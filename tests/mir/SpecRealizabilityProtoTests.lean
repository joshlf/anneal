-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import Lean
import Trusted
import Anneal.SpecRealizabilityPrototype

/-!
# Contract realizability and `ensures`-binding: positive, negative, and audit tests

Exercises `Anneal.SpecRealizabilityPrototype` in three layers.

* **Positive contracts** (`sliceIsEmptyContract`, `checkedAddU32Contract`, and
  the checked-increment refinement): kernel proofs of satisfiability, normal
  realizability, normal and return-value dichotomy, and return determinism,
  together with a passing `ensures`-binding check in every mode.
* **Negative contracts**, one section per vacuity class of *Verified but
  Vacuous* (arXiv:2611.05590): a kernel refutation of the matching semantic
  predicate *and* the expected verdict of the `MetaM` checker.
* **Differential batteries** (`vacuous_case`, `genuine_case`): every disguise
  the checker flags comes with a kernel proof that the postcondition is
  output-insensitive, and every postcondition it accepts comes with a kernel
  dichotomy witness, so the syntactic verdict is validated against the
  semantics entry by entry in both directions.

The file ends with an axiom audit over every theorem of the prototype and of
this file.
-/

namespace SpecRealizabilityProtoTests

open Lean Meta Elab Command
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult
open Anneal.SpecRealizabilityPrototype

/-! ## Harness -/

/-- `#expect_binds c`: the checker must report that `c` binds its output. -/
elab "#expect_binds " id:ident : command => liftTermElabM do
  assertEnsuresBindsOutput (← realizeGlobalConstNoOverloadWithInfo id)

/--
`#expect_vacuous c reason`: the checker must flag `c` as vacuous, for the
`EnsuresVacuityReason` constructor named `reason`.
-/
elab "#expect_vacuous " id:ident reason:ident : command => liftTermElabM do
  let declName ← realizeGlobalConstNoOverloadWithInfo id
  let r ← checkDeclEnsuresBindsOutput declName
  match r.reason? with
  | none =>
    throwError "`{declName}` was expected to be flagged as vacuous \
      ({reason.getId}), but the checker reports that it binds its output.\
      \n{r.describe}"
  | some got =>
    unless toString got == reason.getId.toString do
      throwError "`{declName}` is vacuous for reason `{got}`, but \
        `{reason.getId}` was expected.\n{r.describe}"

/--
`vacuous_case n reason := post by tac` declares the postcondition
`n : Nat → Nat → Prop`, proves by `tac` that it cannot tell two outputs apart,
derives that it has no dichotomy under any precondition, and requires the
checker to flag it for `reason`.
-/
macro "vacuous_case " n:ident reason:ident " := " post:term " by " tac:tacticSeq :
    command => do
  let insensitive := mkIdent (n.getId ++ `insensitive)
  let notDichotomy := mkIdent (n.getId ++ `not_dichotomy)
  `(def $n : Nat → Nat → Prop := $post
    theorem $insensitive : ∀ x r₁ r₂ : Nat, $n x r₁ ↔ $n x r₂ := by $tac
    theorem $notDichotomy (pre : Nat → Prop) :
        ¬ PostconditionDichotomy pre $n :=
      not_dichotomy_of_input_only fun x r₁ r₂ _ => $insensitive x r₁ r₂
    #expect_vacuous $n $reason)

/--
`genuine_case n := post witness x ok bad by tac` declares the postcondition
`n : Nat → Nat → Prop`, proves by `tac` that it accepts `ok` and rejects `bad`
on input `x`, and requires the checker to report that it binds its output.
-/
macro "genuine_case " n:ident " := " post:term " witness " x:term:max
    ok:term:max bad:term:max " by " tac:tacticSeq : command => do
  let dichotomy := mkIdent (n.getId ++ `dichotomy)
  `(def $n : Nat → Nat → Prop := $post
    theorem $dichotomy : PostconditionDichotomy (fun _ => True) $n :=
      ⟨$x, $ok, $bad, trivial, by $tac⟩
    #expect_binds $n)

/-- The report for `declName` under `cfg`, for assertions on its fields. -/
def reportOf (declName : Name) (outputs : Option (Array Nat) := none)
    (cfg : EnsuresCheckConfig := {}) : MetaM EnsuresCheckReport :=
  checkDeclEnsuresBindsOutput declName outputs cfg

/-- Fail unless `declName` is flagged for exactly `reason` under `cfg`. -/
def expectReason (declName : Name) (reason : EnsuresVacuityReason)
    (outputs : Option (Array Nat) := none) (cfg : EnsuresCheckConfig := {}) :
    MetaM Unit :=
  assertEnsuresVacuous declName (some reason) outputs cfg

/-- Elaborate `stx` and run the checker on the resulting `Expr`. -/
def reportOfTerm (stx : Term) (outputs : Option (Array Nat) := none)
    (cfg : EnsuresCheckConfig := {}) : MetaM EnsuresCheckReport := do
  let e ← Term.TermElabM.run' do
    let e ← Term.elabTerm stx none
    Term.synthesizeSyntheticMVarsNoPostponing
    instantiateMVars e
  checkEnsuresBindsOutput e outputs cfg

/-! ## Shared MIR vocabulary -/

/-- A `u32` argument or return value. -/
def u32Arg (n : Nat) : Value := .scalar ⟨n, 4⟩

/-- Rust `Option::<u32>::None`. -/
def optionNone : Value := .aggregate 0 []

/-- Rust `Option::<u32>::Some(n)`. -/
def optionSomeU32 (n : Nat) : Value := .aggregate 1 [.scalar ⟨n, 4⟩]

/-- The wide pointer of a `&[T]` of length `len`. -/
def sliceArg (ptr : ProvenancePtr) (sz len : Nat) : Value :=
  .aggregate 0 [.ptr ptr sz, .scalar ⟨len, 8⟩]

def nullPtr : ProvenancePtr := ⟨0, 0⟩

/-- The length metadata of a single wide-pointer argument. -/
def sliceLen? : List Value → Option Nat
  | [.aggregate _ [_, .scalar s]] => some s.bits
  | _ => none

/-- The bit patterns of two scalar arguments. -/
def scalarPair? : List Value → Option (Nat × Nat)
  | [.scalar a, .scalar b] => some (a.bits, b.bits)
  | _ => none

/-- The bit pattern of a single scalar argument. -/
def scalarArg? : List Value → Option Nat
  | [.scalar a] => some a.bits
  | _ => none

theorem sliceArg_len_inj {args : List Value} {p p' : ProvenancePtr}
    {s s' l l' : Nat} (h : args = [sliceArg p s l])
    (h' : args = [sliceArg p' s' l']) : l = l' :=
  Option.some.inj (congrArg sliceLen? (h.symm.trans h'))

theorem u32Pair_inj {args : List Value} {a b a' b' : Nat}
    (h : args = [u32Arg a, u32Arg b]) (h' : args = [u32Arg a', u32Arg b']) :
    a = a' ∧ b = b' :=
  have := Option.some.inj (congrArg scalarPair? (h.symm.trans h'))
  ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩

theorem u32Single_inj {args : List Value} {a a' : Nat}
    (h : args = [u32Arg a]) (h' : args = [u32Arg a']) : a = a' :=
  Option.some.inj (congrArg scalarArg? (h.symm.trans h'))

theorem u32Arg_inj {a b : Nat} (h : u32Arg a = u32Arg b) : a = b :=
  u32Single_inj (args := [u32Arg a]) rfl (congrArg (fun v => [v]) h)

theorem optionNone_ne_some (n : Nat) : optionNone ≠ optionSomeU32 n :=
  fun h => by cases h

/-! ## Positive contract 1: `core::slice::<impl [T]>::is_empty` -/

namespace SliceIsEmpty

/--
`<[T]>::is_empty(&self) -> bool`: on a wide pointer of length `len`, a normal
return yields the boolean `len == 0` and preserves the call frame; the callee
neither unwinds nor aborts.
-/
def sliceIsEmptyContract : MirCallContract where
  pre req :=
    ∃ ptr sz len, req.args = [sliceArg ptr sz len] ∧ len < scalarModulus 8
  post req ans :=
    match ans with
    | .returned retVal memAfter =>
      callFramePreserved req.memory memAfter ∧
        ∃ ptr sz len b,
          req.args = [sliceArg ptr sz len] ∧ retVal = .scalar ⟨b, 1⟩ ∧
            ((b = 1 ∧ len = 0) ∨ (b = 0 ∧ len ≠ 0))
    | .panicked _ => False
    | .aborted => False

def req (len : Nat) : MirCallReq :=
  { defPath := "core::slice::<impl [T]>::is_empty"
    args := [sliceArg nullPtr 0 len]
    memory := emptyMemory }

theorem pre_req (len : Nat) (h : len < scalarModulus 8) :
    sliceIsEmptyContract.pre (req len) :=
  ⟨nullPtr, 0, len, rfl, h⟩

theorem preSatisfiable : MirCallContractPreSatisfiable sliceIsEmptyContract :=
  ⟨req 0, pre_req 0 (by decide)⟩

/-- An empty slice returns `true`. -/
theorem post_empty_true :
    sliceIsEmptyContract.post (req 0) (.returned (.scalar ⟨1, 1⟩) emptyMemory) :=
  ⟨callFramePreserved_refl _, nullPtr, 0, 0, 1, rfl, rfl, .inl ⟨rfl, rfl⟩⟩

/-- A slice of length three returns `false`. -/
theorem post_nonempty_false :
    sliceIsEmptyContract.post (req 3) (.returned (.scalar ⟨0, 1⟩) emptyMemory) :=
  ⟨callFramePreserved_refl _, nullPtr, 0, 3, 0, rfl, rfl,
    .inr ⟨rfl, by decide⟩⟩

/-- The mutant answer `false` on an empty slice is rejected. -/
theorem rejects_false_on_empty :
    ¬ sliceIsEmptyContract.post (req 0)
      (.returned (.scalar ⟨0, 1⟩) emptyMemory) := by
  rintro ⟨_, ptr, sz, len, b, hargs, hret, h⟩
  have hlen : 0 = len := sliceArg_len_inj rfl hargs
  cases hret
  omega

/-- The mutant answer `true` on a non-empty slice is rejected. -/
theorem rejects_true_on_nonempty :
    ¬ sliceIsEmptyContract.post (req 3)
      (.returned (.scalar ⟨1, 1⟩) emptyMemory) := by
  rintro ⟨_, ptr, sz, len, b, hargs, hret, h⟩
  have hlen : 3 = len := sliceArg_len_inj rfl hargs
  cases hret
  omega

theorem normalRealizable : MirCallContractNormalRealizable sliceIsEmptyContract :=
  ⟨req 0, _, _, pre_req 0 (by decide), post_empty_true⟩

theorem realizable : MirCallContractRealizable sliceIsEmptyContract :=
  normalRealizable.toRealizable

/-- Two returned values are separated in one post-call memory (empty slice). -/
theorem returnValueDichotomy :
    MirCallContractReturnValueDichotomy sliceIsEmptyContract :=
  ⟨req 0, .scalar ⟨1, 1⟩, .scalar ⟨0, 1⟩, emptyMemory, pre_req 0 (by decide),
    post_empty_true, rejects_false_on_empty⟩

theorem normalDichotomy : MirCallContractNormalDichotomy sliceIsEmptyContract :=
  returnValueDichotomy.toNormalDichotomy

/-- The same on a non-empty slice, with the roles of the booleans swapped. -/
theorem normalDichotomy_nonempty :
    MirCallContractNormalDichotomy sliceIsEmptyContract :=
  ⟨req 3, .scalar ⟨0, 1⟩, emptyMemory, .scalar ⟨1, 1⟩, emptyMemory,
    pre_req 3 (by decide), post_nonempty_false, rejects_true_on_nonempty⟩

theorem dichotomy : MirCallContractDichotomy sliceIsEmptyContract :=
  normalDichotomy.toDichotomy

/-- The returned value is a function of the request, over all answers. -/
theorem retVal_deterministic :
    ContractDeterministicOn mirCallRetVal? sliceIsEmptyContract.pre
      sliceIsEmptyContract.post := by
  intro req ans₁ ans₂ _ h₁ h₂
  cases ans₁ with
  | returned v₁ m₁ =>
    cases ans₂ with
    | returned v₂ m₂ =>
      obtain ⟨_, p₁, s₁, l₁, b₁, ha₁, hv₁, hd₁⟩ := h₁
      obtain ⟨_, p₂, s₂, l₂, b₂, ha₂, hv₂, hd₂⟩ := h₂
      have hl : l₁ = l₂ := sliceArg_len_inj ha₁ ha₂
      have hb : b₁ = b₂ := by omega
      subst hl hb hv₁ hv₂
      rfl
    | panicked _ => exact False.elim h₂
    | aborted => exact False.elim h₂
  | panicked _ => exact False.elim h₁
  | aborted => exact False.elim h₁

theorem return_deterministic :
    ContractDeterministicOn Prod.fst sliceIsEmptyContract.pre
      (mirCallNormalPost sliceIsEmptyContract) :=
  returnDeterministic_of_deterministicOn_retVal retVal_deterministic

/-- Dichotomy re-derived from realizability and determinism alone. -/
theorem returnValueDichotomy_of_determinism :
    MirCallContractReturnValueDichotomy sliceIsEmptyContract :=
  mirCallContractReturnValueDichotomy_of_return_deterministic normalRealizable
    return_deterministic

/-- Every admissible request has an accepted normal return. -/
theorem universalRealizable :
    UniversalContractRealizable sliceIsEmptyContract.pre
      (mirCallNormalPost sliceIsEmptyContract) :=
  ⟨preSatisfiable, fun req ⟨ptr, sz, len, hargs, _⟩ =>
    ⟨(.scalar ⟨if len = 0 then 1 else 0, 1⟩, req.memory),
      callFramePreserved_refl _, ptr, sz, len, _, hargs, rfl, by
        split <;> omega⟩⟩

/-- The strongest certificate: implementable, separating, and pinned everywhere. -/
theorem pointwiseCertificate :
    PointwiseDichotomyCertificate Prod.fst sliceIsEmptyContract.pre
      (mirCallNormalPost sliceIsEmptyContract) where
  universal := universalRealizable
  pointwise :=
    pointwiseDichotomy_of_universal_and_deterministicOn universalRealizable
      return_deterministic fun out =>
        let ⟨v, hv⟩ := exists_value_ne out.1
        ⟨(v, out.2), hv⟩
  deterministicOn := return_deterministic

#expect_binds sliceIsEmptyContract

run_meta do
  assertRequiresNotRefuted ``sliceIsEmptyContract
  -- The return is bound by the user clause itself, and it is the *value*.
  assertEnsuresBindsOutput ``sliceIsEmptyContract
    (cfg := { strictReturnValue := true, userEnsuresOnly := true })
  let r ← reportOf ``sliceIsEmptyContract
  unless r.kind == "MirCallContract" && r.arity == 2 && r.outputIdxs == #[1] &&
      r.boundOutputIdxs == #[1] && r.bindsBeyondBoilerplate do
    throwError "unexpected report: {r.describe}"

end SliceIsEmpty

/-! ## Positive contract 2: `core::num::<impl u32>::checked_add` -/

namespace CheckedAdd

/--
`u32::checked_add(self, rhs) -> Option<u32>`: `None` exactly when the
mathematical sum overflows `u32`, `Some(sum)` otherwise.
-/
def checkedAddU32Contract : MirCallContract where
  pre req :=
    ∃ a b, req.args = [u32Arg a, u32Arg b] ∧
      a < scalarModulus 4 ∧ b < scalarModulus 4
  post req ans :=
    match ans with
    | .returned retVal memAfter =>
      callFramePreserved req.memory memAfter ∧
        ∃ a b, req.args = [u32Arg a, u32Arg b] ∧
          ((scalarModulus 4 ≤ a + b ∧ retVal = optionNone) ∨
            (a + b < scalarModulus 4 ∧ retVal = optionSomeU32 (a + b)))
    | .panicked _ => False
    | .aborted => False

def req (a b : Nat) : MirCallReq :=
  { defPath := "core::num::<impl u32>::checked_add"
    args := [u32Arg a, u32Arg b]
    memory := emptyMemory }

theorem pre_req (a b : Nat) (ha : a < scalarModulus 4)
    (hb : b < scalarModulus 4) : checkedAddU32Contract.pre (req a b) :=
  ⟨a, b, rfl, ha, hb⟩

theorem preSatisfiable : MirCallContractPreSatisfiable checkedAddU32Contract :=
  ⟨req 1 2, pre_req 1 2 (by decide) (by decide)⟩

theorem post_some (a b : Nat) (h : a + b < scalarModulus 4) :
    checkedAddU32Contract.post (req a b)
      (.returned (optionSomeU32 (a + b)) emptyMemory) :=
  ⟨callFramePreserved_refl _, a, b, rfl, .inr ⟨h, rfl⟩⟩

theorem post_none (a b : Nat) (h : scalarModulus 4 ≤ a + b) :
    checkedAddU32Contract.post (req a b) (.returned optionNone emptyMemory) :=
  ⟨callFramePreserved_refl _, a, b, rfl, .inl ⟨h, rfl⟩⟩

/-- Inversion of an accepted return on the concrete request `req a b`. -/
theorem post_inv {a b : Nat} {v : Value} {m : Memory}
    (h : checkedAddU32Contract.post (req a b) (.returned v m)) :
    (scalarModulus 4 ≤ a + b ∧ v = optionNone) ∨
      (a + b < scalarModulus 4 ∧ v = optionSomeU32 (a + b)) := by
  obtain ⟨_, a', b', hargs, h⟩ := h
  obtain ⟨rfl, rfl⟩ := u32Pair_inj hargs rfl
  exact h

/-- In range (`1 + 2`): `None` is rejected. -/
theorem rejects_none_in_range :
    ¬ checkedAddU32Contract.post (req 1 2) (.returned optionNone emptyMemory) := by
  intro h
  rcases post_inv h with ⟨hov, _⟩ | ⟨_, hret⟩
  · exact absurd hov (by decide)
  · exact optionNone_ne_some _ hret

/-- In range (`1 + 2`): the off-by-one `Some(4)` is rejected. -/
theorem rejects_off_by_one_in_range :
    ¬ checkedAddU32Contract.post (req 1 2)
      (.returned (optionSomeU32 4) emptyMemory) := by
  intro h
  rcases post_inv h with ⟨hov, _⟩ | ⟨_, hret⟩
  · exact absurd hov (by decide)
  · cases hret

/-- Overflow (`u32::MAX + 1`): the wrapped `Some(0)` is rejected. -/
theorem rejects_wrapped_on_overflow :
    ¬ checkedAddU32Contract.post (req 4294967295 1)
      (.returned (optionSomeU32 0) emptyMemory) := by
  intro h
  rcases post_inv h with ⟨_, hret⟩ | ⟨hin, _⟩
  · exact optionNone_ne_some _ hret.symm
  · exact absurd hin (by decide)

theorem normalRealizable : MirCallContractNormalRealizable checkedAddU32Contract :=
  ⟨req 1 2, _, _, pre_req 1 2 (by decide) (by decide), post_some 1 2 (by decide)⟩

/-- The overflow branch is realizable too. -/
theorem normalRealizable_overflow :
    ∃ m, checkedAddU32Contract.pre (req 4294967295 1) ∧
      checkedAddU32Contract.post (req 4294967295 1) (.returned optionNone m) :=
  ⟨emptyMemory, pre_req _ _ (by decide) (by decide), post_none _ _ (by decide)⟩

/-- In-range dichotomy: `Some(3)` accepted, `None` rejected, in one memory. -/
theorem returnValueDichotomy_in_range :
    MirCallContractReturnValueDichotomy checkedAddU32Contract :=
  ⟨req 1 2, optionSomeU32 3, optionNone, emptyMemory,
    pre_req 1 2 (by decide) (by decide), post_some 1 2 (by decide),
    rejects_none_in_range⟩

/-- Overflow dichotomy: `None` accepted, the wrapped `Some(0)` rejected. -/
theorem returnValueDichotomy_overflow :
    MirCallContractReturnValueDichotomy checkedAddU32Contract :=
  ⟨req 4294967295 1, optionNone, optionSomeU32 0, emptyMemory,
    pre_req _ _ (by decide) (by decide), post_none _ _ (by decide),
    rejects_wrapped_on_overflow⟩

theorem normalDichotomy : MirCallContractNormalDichotomy checkedAddU32Contract :=
  returnValueDichotomy_in_range.toNormalDichotomy

theorem normalDichotomy_overflow :
    MirCallContractNormalDichotomy checkedAddU32Contract :=
  returnValueDichotomy_overflow.toNormalDichotomy

theorem dichotomy : MirCallContractDichotomy checkedAddU32Contract :=
  normalDichotomy.toDichotomy

theorem retVal_deterministic :
    ContractDeterministicOn mirCallRetVal? checkedAddU32Contract.pre
      checkedAddU32Contract.post := by
  intro req ans₁ ans₂ _ h₁ h₂
  cases ans₁ with
  | returned v₁ m₁ =>
    cases ans₂ with
    | returned v₂ m₂ =>
      obtain ⟨_, a₁, b₁, ha₁, hd₁⟩ := h₁
      obtain ⟨_, a₂, b₂, ha₂, hd₂⟩ := h₂
      obtain ⟨rfl, rfl⟩ := u32Pair_inj ha₁ ha₂
      rcases hd₁ with ⟨ho₁, rfl⟩ | ⟨hi₁, rfl⟩ <;>
        rcases hd₂ with ⟨ho₂, rfl⟩ | ⟨hi₂, rfl⟩
      · rfl
      · exact absurd ho₁ (by omega)
      · exact absurd ho₂ (by omega)
      · rfl
    | panicked _ => exact False.elim h₂
    | aborted => exact False.elim h₂
  | panicked _ => exact False.elim h₁
  | aborted => exact False.elim h₁

theorem return_deterministic :
    ContractDeterministicOn Prod.fst checkedAddU32Contract.pre
      (mirCallNormalPost checkedAddU32Contract) :=
  returnDeterministic_of_deterministicOn_retVal retVal_deterministic

theorem universalRealizable :
    UniversalContractRealizable checkedAddU32Contract.pre
      (mirCallNormalPost checkedAddU32Contract) :=
  ⟨preSatisfiable, fun req ⟨a, b, hargs, _, _⟩ =>
    ⟨(if a + b < scalarModulus 4 then optionSomeU32 (a + b) else optionNone,
        req.memory),
      callFramePreserved_refl _, a, b, hargs, by
        by_cases h : a + b < scalarModulus 4
        · exact .inr ⟨h, by simp [h]⟩
        · exact .inl ⟨Nat.le_of_not_lt h, by simp [h]⟩⟩⟩

theorem pointwiseCertificate :
    PointwiseDichotomyCertificate Prod.fst checkedAddU32Contract.pre
      (mirCallNormalPost checkedAddU32Contract) where
  universal := universalRealizable
  pointwise :=
    pointwiseDichotomy_of_universal_and_deterministicOn universalRealizable
      return_deterministic fun out =>
        let ⟨v, hv⟩ := exists_value_ne out.1
        ⟨(v, out.2), hv⟩
  deterministicOn := return_deterministic

#expect_binds checkedAddU32Contract

run_meta do
  assertRequiresNotRefuted ``checkedAddU32Contract
  assertEnsuresBindsOutput ``checkedAddU32Contract
    (cfg := { strictReturnValue := true, userEnsuresOnly := true })

end CheckedAdd

/-! ## Positive contract 3: refinement strengthening and killed mutants -/

namespace Refinement

def incPre (x : Nat) : Prop := x < 100

/-- The weak specification `ensures(ret >= x)`. -/
def geSpec (x ret : Nat) : Prop := ret ≥ x

/-- The strengthened specification `ensures(ret == x + 1)`. -/
def incSpec (x ret : Nat) : Prop := ret = x + 1

theorem incSpec_strengthens_geSpec :
    ∀ x ret, incPre x → incSpec x ret → geSpec x ret := by
  intro x ret _ h
  unfold incSpec at h
  unfold geSpec
  omega

theorem incPre_five : incPre 5 := show 5 < 100 by omega

theorem geSpec_dichotomy : PostconditionDichotomy incPre geSpec :=
  ⟨5, 5, 0, incPre_five, show 5 ≥ 5 by omega, show ¬ 0 ≥ 5 by omega⟩

/--
Dichotomy of the strengthened specification, obtained from the refinement
theorem: `incSpec` is still realizable at `5`, where `geSpec` rejects `0`.
-/
theorem incSpec_dichotomy : PostconditionDichotomy incPre incSpec :=
  dichotomy_preserved_under_strengthening_of_nonvacuous_refinement
    (pre := incPre) (post := geSpec) incSpec_strengthens_geSpec
    ⟨5, incPre_five, incPre_five, ⟨6, rfl⟩, ⟨0, show ¬ 0 ≥ 5 by omega⟩⟩

/-- A data-carrying witness and its certificate. -/
def incSpecWitness : StrongContractWitness incPre incSpec where
  inp := 5
  outOk := 6
  outBad := 0
  pre_inp := show 5 < 100 by omega
  post_ok := rfl
  post_bad := show ¬ 0 = 5 + 1 by omega

theorem incSpec_certificate : DichotomyCertificate incPre incSpec :=
  .ofWitness incSpecWitness

theorem incSpec_deterministic : ContractDeterministic incPre incSpec := by
  intro x r₁ r₂ _ h₁ h₂
  unfold incSpec at h₁ h₂
  omega

theorem geSpec_not_deterministic : ¬ ContractDeterministic incPre geSpec :=
  fun h => absurd (h 5 5 6 (show 5 < 100 by omega) (show 5 ≥ 5 by omega)
    (show 6 ≥ 5 by omega)) (by decide)

/-- The off-by-one mutant `ret + 1`. -/
def offByOne : OutputMutant Nat Nat := fun _ ret => ret + 1

/-- The constant mutant `0`. -/
def constZero : OutputMutant Nat Nat := fun _ _ => 0

/-- The identity-on-input mutant `x`. -/
def echoInput : OutputMutant Nat Nat := fun x _ => x

theorem incSpec_kills_offByOne : MutantKilledBySpec incPre incSpec offByOne :=
  ⟨5, 6, show 5 < 100 by omega, rfl, show ¬ 6 + 1 = 5 + 1 by omega⟩

theorem incSpec_kills_constZero : MutantKilledBySpec incPre incSpec constZero :=
  ⟨5, 6, show 5 < 100 by omega, rfl, show ¬ 0 = 5 + 1 by omega⟩

theorem incSpec_kills_echoInput : MutantKilledBySpec incPre incSpec echoInput :=
  ⟨5, 6, show 5 < 100 by omega, rfl, show ¬ 5 = 5 + 1 by omega⟩

/-- The strengthened specification kills every non-equivalent mutant. -/
theorem incSpec_kills_every_nonequivalent_mutant
    (mutant : OutputMutant Nat Nat) (x ret : Nat) (h_pre : incPre x)
    (h_post : incSpec x ret) (h_ne : mutant x ret ≠ ret) :
    KillsMutantAt incPre incSpec mutant x ret :=
  contractDeterministic_iff_kills_every_nonequivalent_mutant.mp
    incSpec_deterministic mutant x ret h_pre h_post h_ne

/-- The weak specification still kills the constant mutant ... -/
theorem geSpec_kills_constZero : MutantKilledBySpec incPre geSpec constZero :=
  ⟨5, 5, show 5 < 100 by omega, show 5 ≥ 5 by omega, show ¬ 0 ≥ 5 by omega⟩

/-- ... but the off-by-one mutant survives it on every valid execution ... -/
theorem geSpec_survives_offByOne : ¬ MutantKilledBySpec incPre geSpec offByOne := by
  rintro ⟨x, ret, _, hok, hbad⟩
  have hok' : ret ≥ x := hok
  exact hbad (show ret + 1 ≥ x by omega)

/-- ... and so does the identity-on-input mutant. -/
theorem geSpec_survives_echoInput :
    ¬ MutantKilledBySpec incPre geSpec echoInput :=
  fun ⟨x, _, _, _, hbad⟩ => hbad (Nat.le_refl x)

#expect_binds geSpec
#expect_binds incSpec

/-! ### The same refinement as a `StatefulClaim` -/

/-- `ensures(ret >= x)` with the frame condition `mem' = mem`. -/
def checkedIncWeakClaim (body : CapturedMir) : StatefulClaim where
  body := body
  pre args _ := ∃ x, args = [u32Arg x] ∧ x + 1 < scalarModulus 4
  post args mem ret mem' :=
    mem' = mem ∧ ∃ x y, args = [u32Arg x] ∧ ret = u32Arg y ∧ x ≤ y

/-- `ensures(ret == x + 1)` with the frame condition `mem' = mem`. -/
def checkedIncClaim (body : CapturedMir) : StatefulClaim where
  body := body
  pre args _ := ∃ x, args = [u32Arg x] ∧ x + 1 < scalarModulus 4
  post args mem ret mem' :=
    mem' = mem ∧ ∃ x, args = [u32Arg x] ∧ ret = u32Arg (x + 1)

variable (body : CapturedMir)

/-- The witness state: the argument `5` in the empty memory. -/
def incInput : List Value × Memory := ([u32Arg 5], emptyMemory)

theorem incInput_pre : statefulClaimPre (checkedIncClaim body) incInput :=
  ⟨5, rfl, by decide⟩

theorem incInput_pre_weak :
    statefulClaimPre (checkedIncWeakClaim body) incInput :=
  ⟨5, rfl, by decide⟩

theorem incInput_post :
    statefulClaimPost (checkedIncClaim body) incInput (u32Arg 6, emptyMemory) :=
  ⟨rfl, 5, rfl, rfl⟩

theorem checkedInc_strengthens :
    ∀ inp out, statefulClaimPre (checkedIncClaim body) inp →
      statefulClaimPost (checkedIncClaim body) inp out →
      statefulClaimPost (checkedIncWeakClaim body) inp out := by
  rintro ⟨args, mem⟩ ⟨ret, mem'⟩ _ ⟨hmem, x, hargs, hret⟩
  exact ⟨hmem, x, x + 1, hargs, hret, by omega⟩

/-- The weak claim rejects the return `0` on the witness state. -/
theorem checkedIncWeak_rejects_zero :
    ¬ statefulClaimPost (checkedIncWeakClaim body) incInput
      (u32Arg 0, emptyMemory) := by
  rintro ⟨_, x, y, hargs, hret, hle⟩
  have hx : 5 = x := u32Single_inj rfl hargs
  have hy : 0 = y := u32Arg_inj hret
  omega

/-- Stateful dichotomy of the strengthened claim, by the refinement theorem. -/
theorem checkedInc_dichotomy : StatefulClaimDichotomy (checkedIncClaim body) :=
  statefulClaimDichotomy_iff.mpr <|
    dichotomy_preserved_under_strengthening_of_nonvacuous_refinement
      (pre := statefulClaimPre (checkedIncWeakClaim body))
      (post := statefulClaimPost (checkedIncWeakClaim body))
      (checkedInc_strengthens body)
      ⟨incInput, incInput_pre body, incInput_pre_weak body,
        ⟨_, incInput_post body⟩, ⟨_, checkedIncWeak_rejects_zero body⟩⟩

theorem checkedInc_return_deterministic :
    ContractDeterministicOn Prod.fst (statefulClaimPre (checkedIncClaim body))
      (statefulClaimPost (checkedIncClaim body)) := by
  rintro ⟨args, mem⟩ ⟨r₁, m₁⟩ ⟨r₂, m₂⟩ _ ⟨_, x₁, ha₁, hr₁⟩ ⟨_, x₂, ha₂, hr₂⟩
  have hx : x₁ = x₂ := u32Single_inj ha₁ ha₂
  subst hx
  exact hr₁.trans hr₂.symm

/-- The returned value itself is bound, not only the post-memory. -/
theorem checkedInc_returnDichotomy :
    StatefulClaimReturnDichotomy (checkedIncClaim body) :=
  statefulClaimReturnDichotomy_of_realizable_and_return_deterministic
    ⟨_, _, _, _, incInput_pre body, incInput_post body⟩
    (checkedInc_return_deterministic body)

/-- Return-value mutant `ret + 1` on the paired output. -/
def bumpRet : OutputMutant (List Value × Memory) (Value × Memory) :=
  fun _ out =>
    (match out.1 with
      | .scalar s => .scalar ⟨s.bits + 1, s.sizeBytes⟩
      | v => v,
      out.2)

/-- Return-value mutant `0` on the paired output. -/
def zeroRet : OutputMutant (List Value × Memory) (Value × Memory) :=
  fun _ out => (u32Arg 0, out.2)

/-- Return-value mutant "echo the argument" on the paired output. -/
def echoArg : OutputMutant (List Value × Memory) (Value × Memory) :=
  fun inp out => (inp.1.headD out.1, out.2)

/-- On the witness execution every mutant that changes the return is killed. -/
theorem checkedInc_kills (mutant : OutputMutant (List Value × Memory) (Value × Memory))
    (h_ne : (mutant incInput (u32Arg 6, emptyMemory)).1 ≠ u32Arg 6) :
    MutantKilledBySpec (statefulClaimPre (checkedIncClaim body))
      (statefulClaimPost (checkedIncClaim body)) mutant :=
  ⟨incInput, (u32Arg 6, emptyMemory),
    killsMutantAt_of_deterministicOn (checkedInc_return_deterministic body)
      (incInput_pre body) (incInput_post body) h_ne⟩

theorem checkedInc_kills_bumpRet :
    MutantKilledBySpec (statefulClaimPre (checkedIncClaim body))
      (statefulClaimPost (checkedIncClaim body)) bumpRet :=
  checkedInc_kills body bumpRet fun h => absurd (u32Arg_inj h) (by decide)

theorem checkedInc_kills_zeroRet :
    MutantKilledBySpec (statefulClaimPre (checkedIncClaim body))
      (statefulClaimPost (checkedIncClaim body)) zeroRet :=
  checkedInc_kills body zeroRet fun h => absurd (u32Arg_inj h) (by decide)

theorem checkedInc_kills_echoArg :
    MutantKilledBySpec (statefulClaimPre (checkedIncClaim body))
      (statefulClaimPost (checkedIncClaim body)) echoArg :=
  checkedInc_kills body echoArg fun h => absurd (u32Arg_inj h) (by decide)

/-- The weak claim lets the "echo the argument" mutant survive everywhere. -/
theorem checkedIncWeak_survives_echoArg :
    ¬ MutantKilledBySpec (statefulClaimPre (checkedIncWeakClaim body))
      (statefulClaimPost (checkedIncWeakClaim body)) echoArg := by
  rintro ⟨⟨args, mem⟩, ⟨ret, mem'⟩, _, ⟨hmem, x, y, hargs, _, _⟩, hbad⟩
  subst hargs
  exact hbad ⟨hmem, x, x, rfl, rfl, Nat.le_refl x⟩

#expect_binds checkedIncClaim
#expect_binds checkedIncWeakClaim

run_meta do
  -- Strict mode: the returned value (binder 2) is bound, not only `mem'`.
  assertEnsuresBindsOutput ``checkedIncClaim (cfg := { strictReturnValue := true })
  let r ← reportOf ``checkedIncClaim
  unless r.kind == "StatefulClaim" && r.arity == 4 && r.outputIdxs == #[2, 3] &&
      r.boundOutputIdxs == #[2, 3] do
    throwError "unexpected report: {r.describe}"

end Refinement

/-! ## Class 1 — unsatisfiable `requires` -/

namespace Class1

/-- (1a) The literal `requires(false)`. -/
def falsePre (_x : Nat) : Prop := False

theorem falsePre_not_satisfiable : ¬ PreconditionSatisfiable falsePre :=
  not_preconditionSatisfiable_of_unsat fun _ h => h

theorem falsePre_not_realizable (post : Nat → Nat → Prop) :
    ¬ ContractRealizable falsePre post :=
  not_realizable_of_unsat_pre falsePre_not_satisfiable

theorem falsePre_not_dichotomy (post : Nat → Nat → Prop) :
    ¬ PostconditionDichotomy falsePre post :=
  not_dichotomy_of_unsat_pre falsePre_not_satisfiable

/-- The trap: `pre → post` nevertheless holds, for every postcondition. -/
theorem falsePre_implies_every_post (post : Nat → Nat → Prop) :
    ∀ x ret, falsePre x → post x ret :=
  fun _ _ h => h.elim

/-- (1b) A contradictory arithmetic `requires(a < 10 && a > 20)` on a `u32`. -/
def contradictoryPreContract : MirCallContract where
  pre req := ∃ a, req.args = [u32Arg a] ∧ a < 10 ∧ a > 20
  post := CheckedAdd.checkedAddU32Contract.post

theorem contradictoryPre_not_preSatisfiable :
    ¬ MirCallContractPreSatisfiable contradictoryPreContract := by
  rintro ⟨_, a, _, h₁, h₂⟩
  omega

theorem contradictoryPre_not_realizable :
    ¬ MirCallContractRealizable contradictoryPreContract :=
  not_realizable_of_unsat_pre contradictoryPre_not_preSatisfiable

theorem contradictoryPre_not_normalRealizable :
    ¬ MirCallContractNormalRealizable contradictoryPreContract :=
  fun h => contradictoryPre_not_realizable h.toRealizable

theorem contradictoryPre_not_dichotomy :
    ¬ MirCallContractDichotomy contradictoryPreContract :=
  not_dichotomy_of_unsat_pre contradictoryPre_not_preSatisfiable

/-- The same `requires` on a `Claim` with a perfectly binding `ensures`. -/
def contradictoryClaim (body : CapturedMir) : Claim where
  body := body
  pre args := ∃ a, args = [u32Arg a] ∧ a < 10 ∧ a > 20
  post _ ret := ret = u32Arg 42

theorem contradictoryClaim_not_preSatisfiable (body : CapturedMir) :
    ¬ ClaimPreSatisfiable (contradictoryClaim body) := by
  rintro ⟨_, a, _, h₁, h₂⟩
  omega

/--
*Verified but vacuous*: the trusted gate certifies the claim for **every** MIR
body, although nothing satisfies its precondition.
-/
theorem contradictoryClaim_verified (body : CapturedMir) :
    VerificationResult (contradictoryClaim body) :=
  verificationResult_of_not_preSatisfiable
    (contradictoryClaim_not_preSatisfiable body)

theorem contradictoryClaim_not_realizable (body : CapturedMir) :
    ¬ ClaimRealizable (contradictoryClaim body) :=
  not_realizable_of_unsat_pre (contradictoryClaim_not_preSatisfiable body)

run_meta do
  assertRequiresRefuted ``falsePre
  assertRequiresRefuted ``contradictoryPreContract
  assertRequiresRefuted ``contradictoryClaim
  -- An unsatisfiable `requires` is invisible to the `ensures` check: the
  -- postcondition of `contradictoryClaim` binds its output.
  assertEnsuresBindsOutput ``contradictoryClaim
  -- A satisfiable `requires` is not refuted.
  assertRequiresNotRefuted ``Refinement.incPre
  assertRequiresNotRefuted ``Refinement.checkedIncClaim

end Class1

/-! ## Class 2 — constant `True` postcondition -/

namespace Class2

def constTruePost (_x _ret : Nat) : Prop := True

theorem constTruePost_not_dichotomy (pre : Nat → Prop) :
    ¬ PostconditionDichotomy pre constTruePost :=
  not_dichotomy_of_const_true fun _ _ _ => trivial

/-- It is nevertheless realizable: realizability alone does not see class 2. -/
theorem constTruePost_realizable :
    ContractRealizable (fun _ => True) constTruePost :=
  ⟨0, 0, trivial, trivial⟩

def constTrueClaim (body : CapturedMir) : Claim where
  body := body
  pre _ := True
  post _ _ := True

theorem constTrueClaim_not_dichotomy (body : CapturedMir) :
    ¬ ClaimDichotomy (constTrueClaim body) :=
  not_claimDichotomy_of_return_blind fun _ _ _ _ => Iff.rfl

def constTrueStatefulClaim (body : CapturedMir) : StatefulClaim where
  body := body
  pre _ _ := True
  post _ _ _ _ := True

theorem constTrueStatefulClaim_not_dichotomy (body : CapturedMir) :
    ¬ StatefulClaimDichotomy (constTrueStatefulClaim body) :=
  not_statefulClaimDichotomy_of_output_blind fun _ _ _ _ _ _ _ => Iff.rfl

#expect_vacuous constTruePost constTrue
#expect_vacuous constTrueClaim constTrue
#expect_vacuous constTrueStatefulClaim constTrue

end Class2

/-! ## Class 3 — reflexivity and tautology wrappers -/

namespace Class3

/-- (3a) `ensures(ret == ret)`. -/
def reflPost (_x ret : Nat) : Prop := ret = ret

theorem reflPost_not_dichotomy (pre : Nat → Prop) :
    ¬ PostconditionDichotomy pre reflPost :=
  not_dichotomy_of_refl_tautology (fun _ ret => ret) fun _ _ _ => Iff.rfl

/-- (3b) `let y := ret; y = y`. -/
def letReflPost (_x ret : Nat) : Prop := let y := ret; y = y

theorem letReflPost_not_dichotomy (pre : Nat → Prop) :
    ¬ PostconditionDichotomy pre letReflPost :=
  not_dichotomy_of_refl_tautology (fun _ ret => ret) fun _ _ _ => Iff.rfl

/-- (3b) `(ret == ret) = true` through `BEq`. -/
def beqReflPost (_x ret : Nat) : Prop := (ret == ret) = true

theorem beqReflPost_not_dichotomy (pre : Nat → Prop) :
    ¬ PostconditionDichotomy pre beqReflPost :=
  not_dichotomy_of_universal_post fun _ ret _ =>
    show (ret == ret) = true by simp

/-- (3b) `Nat.ble n n = true`. -/
def bleReflPost (_x ret : Nat) : Prop := Nat.ble ret ret = true

theorem bleReflPost_not_dichotomy (pre : Nat → Prop) :
    ¬ PostconditionDichotomy pre bleReflPost :=
  not_dichotomy_of_universal_post fun _ ret _ =>
    show Nat.ble ret ret = true by simp

/--
(3b) The compound `(ret = ret) ∧ (x < 100)`: `ret` occurs, and `x` is
genuinely constrained, yet nothing is said about `ret`.
-/
def compoundReflPost (x ret : Nat) : Prop := (ret = ret) ∧ (x < 100)

theorem compoundReflPost_not_dichotomy (pre : Nat → Prop) :
    ¬ PostconditionDichotomy pre compoundReflPost :=
  not_dichotomy_of_input_predicate (fun x => x < 100) fun _ _ _ =>
    ⟨fun h => h.2, fun h => ⟨rfl, h⟩⟩

/-- The compound is not universally true: it does constrain the input. -/
theorem compoundReflPost_not_universal : ¬ ∀ x ret, compoundReflPost x ret :=
  fun h => absurd (h 100 0).2 (by decide)

#expect_vacuous reflPost reflexiveTautology
#expect_vacuous letReflPost reflexiveTautology
#expect_vacuous beqReflPost reflexiveTautology
#expect_vacuous bleReflPost reflexiveTautology
#expect_vacuous compoundReflPost reflexiveTautology

/-- A reflexive `ensures` on a `Claim` over `Value`s. -/
def reflClaim (body : CapturedMir) : Claim where
  body := body
  pre _ := True
  post _ ret := ret = ret

theorem reflClaim_not_dichotomy (body : CapturedMir) :
    ¬ ClaimDichotomy (reflClaim body) :=
  not_dichotomy_of_refl_tautology (fun _ ret => ret) fun _ _ _ => Iff.rfl

#expect_vacuous reflClaim reflexiveTautology

end Class3

/-! ## Class 4 — input-only postconditions -/

namespace Class4

/-- Tautological and input-only: `ensures(x == x)`. -/
def inputReflPost (x _ret : Nat) : Prop := x = x

theorem inputReflPost_not_dichotomy (pre : Nat → Prop) :
    ¬ PostconditionDichotomy pre inputReflPost :=
  not_dichotomy_of_refl_tautology (fun x _ => x) fun _ _ _ => Iff.rfl

/-- Not a tautology, but input-only: `ensures(x < 100)`. -/
def inputBoundPost (x _ret : Nat) : Prop := x < 100

theorem inputBoundPost_not_dichotomy (pre : Nat → Prop) :
    ¬ PostconditionDichotomy pre inputBoundPost :=
  not_dichotomy_of_input_predicate (fun x => x < 100) fun _ _ _ => Iff.rfl

/-- It genuinely constrains `x`: it is not `ensures(true)` in disguise ... -/
theorem inputBoundPost_not_universal : ¬ ∀ x ret, inputBoundPost x ret :=
  fun h => absurd (h 100 0) (show ¬ 100 < 100 by omega)

/-- ... and it is realizable, yet every output of an accepted input is accepted. -/
theorem inputBoundPost_realizable :
    ContractRealizable (fun _ => True) inputBoundPost :=
  ⟨0, 0, trivial, show 0 < 100 by omega⟩

theorem inputBoundPost_outputInsensitive :
    OutputInsensitive (fun _ => True) inputBoundPost :=
  fun _ _ _ _ h => h

#expect_vacuous inputReflPost inputOnly
#expect_vacuous inputBoundPost inputOnly

/-- The input-only shape on a `Claim`: `ensures(args == args)`. -/
def inputOnlyClaim (body : CapturedMir) : Claim where
  body := body
  pre _ := True
  post args _ := args.length < 3

theorem inputOnlyClaim_not_dichotomy (body : CapturedMir) :
    ¬ ClaimDichotomy (inputOnlyClaim body) :=
  not_claimDichotomy_of_return_blind fun _ _ _ _ => Iff.rfl

#expect_vacuous inputOnlyClaim inputOnly

end Class4

/-! ## Class 5 — outcome-blind and return-blind `MirCallContract`s -/

namespace Class5

/-- (5a) `post := fun _ _ => True`. -/
def outcomeBlindConst : MirCallContract where
  pre _ := True
  post _ _ := True

/-- (5a) The explicit three-arm `match` with `True` in every arm. -/
def outcomeBlindMatch : MirCallContract where
  pre _ := True
  post _ ans :=
    match ans with
    | .returned _ _ => True
    | .panicked _ => True
    | .aborted => True

theorem outcomeBlindConst_not_dichotomy :
    ¬ MirCallContractDichotomy outcomeBlindConst :=
  not_mirCallContractDichotomy_of_outcome_blind fun _ _ _ _ => Iff.rfl

theorem outcomeBlindMatch_not_dichotomy :
    ¬ MirCallContractDichotomy outcomeBlindMatch :=
  not_dichotomy_of_universal_post fun _ ans _ => by cases ans <;> trivial

/-- The default `MirCallContract` is outcome-blind too. -/
theorem default_not_dichotomy : ¬ MirCallContractDichotomy {} :=
  not_mirCallContractDichotomy_of_outcome_blind fun _ _ _ _ => Iff.rfl

#expect_vacuous outcomeBlindConst outcomeBlind
#expect_vacuous outcomeBlindMatch outcomeBlind

/--
(5b) The return-blind nounwind contract: every normal return is accepted,
unwinding is forbidden, aborting is permitted.
-/
def returnBlindNounwind : MirCallContract where
  pre := CheckedAdd.checkedAddU32Contract.pre
  post _ ans :=
    match ans with
    | .returned _ _ => True
    | .panicked _ => False
    | .aborted => True

theorem returnBlindNounwind_normalRealizable :
    MirCallContractNormalRealizable returnBlindNounwind :=
  ⟨CheckedAdd.req 1 2, .unit, emptyMemory,
    CheckedAdd.pre_req 1 2 (by decide) (by decide), trivial⟩

/-- The naive dichotomy *holds*: the forbidden unwind is the rejected answer. -/
theorem returnBlindNounwind_dichotomy :
    MirCallContractDichotomy returnBlindNounwind :=
  mirCallContractDichotomy_of_normalRealizable_of_panic_forbidden
    returnBlindNounwind_normalRealizable fun _ _ _ h => h

/-- The normal dichotomy *fails*: no two returns are told apart. -/
theorem returnBlindNounwind_not_normalDichotomy :
    ¬ MirCallContractNormalDichotomy returnBlindNounwind :=
  not_mirCallContractNormalDichotomy_of_return_blind
    fun _ _ _ _ _ _ => Iff.rfl

#expect_vacuous returnBlindNounwind returnBlind

/--
(5c) The abort-only trap: no return and no unwind is accepted, only an abort.
-/
def abortOnlyTrap : MirCallContract where
  pre := CheckedAdd.checkedAddU32Contract.pre
  post _ ans :=
    match ans with
    | .returned _ _ => False
    | .panicked _ => False
    | .aborted => True

/-- It is "realizable" ... -/
theorem abortOnlyTrap_realizable : MirCallContractRealizable abortOnlyTrap :=
  ⟨CheckedAdd.req 1 2, .aborted,
    CheckedAdd.pre_req 1 2 (by decide) (by decide), trivial⟩

/-- ... and even has the naive dichotomy ... -/
theorem abortOnlyTrap_dichotomy : MirCallContractDichotomy abortOnlyTrap :=
  ⟨CheckedAdd.req 1 2, .aborted, .returned .unit emptyMemory,
    CheckedAdd.pre_req 1 2 (by decide) (by decide), trivial, id⟩

/-- ... but no normal return realises it. -/
theorem abortOnlyTrap_not_normalRealizable :
    ¬ MirCallContractNormalRealizable abortOnlyTrap :=
  not_mirCallContractNormalRealizable_of_no_normal_return fun _ _ _ _ h => h

theorem abortOnlyTrap_not_normalDichotomy :
    ¬ MirCallContractNormalDichotomy abortOnlyTrap :=
  not_mirCallContractNormalDichotomy_of_not_normalRealizable
    abortOnlyTrap_not_normalRealizable

#expect_vacuous abortOnlyTrap normalReturnUnsatisfiable

/-! ### Disguised return-blind contracts -/

/-- The `.returned` arm mentions both fields, in reflexive equations only. -/
def returnBlindRefl : MirCallContract where
  pre _ := True
  post _ ans :=
    match ans with
    | .returned retVal memAfter => retVal = retVal ∧ memAfter = memAfter
    | .panicked _ => False
    | .aborted => True

theorem returnBlindRefl_not_normalDichotomy :
    ¬ MirCallContractNormalDichotomy returnBlindRefl :=
  not_mirCallContractNormalDichotomy_of_return_blind fun _ _ _ _ _ _ =>
    ⟨fun _ => ⟨rfl, rfl⟩, fun _ => ⟨rfl, rfl⟩⟩

/-- No `match` at all: "the answer is some return". -/
def returnBlindExists : MirCallContract where
  pre _ := True
  post _ ans := ∃ retVal memAfter, ans = .returned retVal memAfter

theorem returnBlindExists_not_normalDichotomy :
    ¬ MirCallContractNormalDichotomy returnBlindExists :=
  not_mirCallContractNormalDichotomy_of_return_blind fun _ v₁ m₁ v₂ m₂ _ =>
    ⟨fun _ => ⟨v₂, m₂, rfl⟩, fun _ => ⟨v₁, m₁, rfl⟩⟩

/-- A Boolean helper hides the outcome test. -/
def isReturn : MirCallAns → Bool
  | .returned _ _ => true
  | .panicked _ => false
  | .aborted => false

def returnBlindHelper : MirCallContract where
  pre _ := True
  post _ ans := isReturn ans = true

theorem returnBlindHelper_not_normalDichotomy :
    ¬ MirCallContractNormalDichotomy returnBlindHelper :=
  not_mirCallContractNormalDichotomy_of_return_blind fun _ _ _ _ _ _ => Iff.rfl

/-- The `.returned` arm constrains the *request* only. -/
def returnBlindInputOnly : MirCallContract where
  pre _ := True
  post req ans :=
    match ans with
    | .returned _ _ => req.args = []
    | .panicked _ => False
    | .aborted => True

theorem returnBlindInputOnly_not_normalDichotomy :
    ¬ MirCallContractNormalDichotomy returnBlindInputOnly :=
  not_mirCallContractNormalDichotomy_of_return_blind fun _ _ _ _ _ _ => Iff.rfl

/-- Reflexivity at the level of the whole answer. -/
def outcomeBlindRefl : MirCallContract where
  pre _ := True
  post _ ans := ans = ans

theorem outcomeBlindRefl_not_dichotomy :
    ¬ MirCallContractDichotomy outcomeBlindRefl :=
  not_dichotomy_of_refl_tautology (fun _ ans => ans) fun _ _ _ => Iff.rfl

#expect_vacuous returnBlindRefl returnBlind
#expect_vacuous returnBlindExists returnBlind
#expect_vacuous returnBlindHelper returnBlind
#expect_vacuous returnBlindInputOnly returnBlind
#expect_vacuous outcomeBlindRefl outcomeBlind

/-! ### `externalSpecCallContract`: boilerplate versus the user `ensures` -/

/-- An external spec with the default (`True`) `ensures` clause. -/
def extSpecDefault (target : DefPath) (sidecar : CapturedMir) : MirCallContract :=
  externalSpecCallContract target sidecar

/-- An external spec whose `ensures` clause is reflexive. -/
def extSpecRefl (target : DefPath) (sidecar : CapturedMir) : MirCallContract :=
  externalSpecCallContract target sidecar (fun _ => True) (fun _ ret => ret = ret)

/-- An external spec whose `ensures` clause pins the returned value. -/
def extSpecGenuine (target : DefPath) (sidecar : CapturedMir) : MirCallContract :=
  externalSpecCallContract target sidecar (fun _ => True)
    (fun _ ret => ret = u32Arg 7)

theorem extSpecDefault_not_ensuresDichotomy (target : DefPath)
    (sidecar : CapturedMir) :
    ¬ ExternalSpecEnsuresDichotomy target sidecar (fun _ => True)
      (fun _ _ => True) :=
  not_externalSpecEnsuresDichotomy_default target sidecar _

theorem extSpecRefl_not_ensuresDichotomy (target : DefPath)
    (sidecar : CapturedMir) :
    ¬ ExternalSpecEnsuresDichotomy target sidecar (fun _ => True)
      (fun _ ret => ret = ret) :=
  not_externalSpecEnsuresDichotomy_of_return_blind target sidecar _ _
    fun _ _ _ _ => ⟨fun _ => rfl, fun _ => rfl⟩

/--
Yet both have a *normal* dichotomy as soon as they are normal-realizable: the
frame conjunct separates memories. Only the user-`ensures` mode sees them.
-/
theorem extSpecDefault_normalDichotomy_of_normalRealizable (target : DefPath)
    (sidecar : CapturedMir)
    (h : MirCallContractNormalRealizable (extSpecDefault target sidecar)) :
    MirCallContractNormalDichotomy (extSpecDefault target sidecar) :=
  externalSpecCallContract_normalDichotomy_of_normalRealizable _ _ _ _ h

def trivialExtraPost (_args : List Value) (_ret : Value) : Prop := True

def genuineExtraPost (args : List Value) (ret : Value) : Prop := [ret] = args

#expect_vacuous trivialExtraPost constTrue
#expect_binds genuineExtraPost
#expect_binds extSpecGenuine

run_meta do
  let user : EnsuresCheckConfig := { userEnsuresOnly := true }
  let strictUser : EnsuresCheckConfig :=
    { userEnsuresOnly := true, strictReturnValue := true }
  -- Default mode: frame and return-type conjuncts do bind `(retVal, memAfter)`,
  -- and the report says that nothing else does.
  for n in #[``extSpecDefault, ``extSpecRefl] do
    let r ← reportOf n
    unless r.bindsOutput && !r.bindsBeyondBoilerplate do
      throwError "{n}: expected binding by boilerplate only\n{r.describe}"
    -- User-`ensures` mode: flagged.
    expectReason n .boilerplateOnly (cfg := user)
    expectReason n .boilerplateOnly (cfg := strictUser)
  -- A genuine `ensures` clause passes in every mode.
  let r ← reportOf ``extSpecGenuine
  unless r.bindsOutput && r.bindsBeyondBoilerplate do
    throwError "extSpecGenuine: expected binding beyond boilerplate\n{r.describe}"
  assertEnsuresBindsOutput ``extSpecGenuine (cfg := user)
  assertEnsuresBindsOutput ``extSpecGenuine (cfg := strictUser)

end Class5

/-! ## `StatefulClaim`: post-memory versus returned value -/

namespace Stateful

/-- A reflexive stateful postcondition: neither output is bound. -/
def reflStatefulClaim (body : CapturedMir) : StatefulClaim where
  body := body
  pre _ _ := True
  post _ _ ret mem' := ret = ret ∧ mem' = mem'

theorem reflStatefulClaim_not_dichotomy (body : CapturedMir) :
    ¬ StatefulClaimDichotomy (reflStatefulClaim body) :=
  not_statefulClaimDichotomy_of_output_blind fun _ _ _ _ _ _ _ =>
    ⟨fun _ => ⟨rfl, rfl⟩, fun _ => ⟨rfl, rfl⟩⟩

/-- A raw 4-ary postcondition of the `StatefulClaim` shape. -/
def rawFramePost (_args : List Value) (mem : Memory) (_ret : Value)
    (mem' : Memory) : Prop :=
  mem' = mem

#expect_vacuous reflStatefulClaim reflexiveTautology
#expect_binds frameOnlyStatefulClaim
#expect_binds rawFramePost

run_meta do
  let strict : EnsuresCheckConfig := { strictReturnValue := true }
  -- The frame-only claim binds `mem'` (binder 3) and leaves `retVal` (binder 2)
  -- free: accepted when either output may be bound, flagged in strict mode,
  -- matching `frameOnlyStatefulClaim_not_returnDichotomy`.
  for n in #[``frameOnlyStatefulClaim, ``rawFramePost] do
    let r ← reportOf n
    unless r.arity == 4 && r.outputIdxs == #[2, 3] &&
        r.boundOutputIdxs == #[3] do
      throwError "{n}: unexpected report\n{r.describe}"
    expectReason n .returnValueUnconstrained (cfg := strict)
    -- Designating `retVal` alone: nothing designated is bound.
    expectReason n .inputOnly (outputs := some #[2])
    -- Designating `mem'` alone: bound.
    assertEnsuresBindsOutput n (outputParamIdxs := some #[3])

end Stateful

/-! ## Differential battery: disguises the checker must flag -/

namespace Disguises

/-- A user predicate that is a tautology of its argument. -/
def trivialOn (r : Nat) : Prop := r = r

vacuous_case heqRefl reflexiveTautology := fun _ r => HEq r r
  by intros; simp [heqRefl]
vacuous_case leRefl reflexiveTautology := fun _ r => r ≤ r
  by intros; simp [leRefl]
vacuous_case geRefl reflexiveTautology := fun _ r => r ≥ r
  by intros; simp [geRefl]
vacuous_case ltIrrefl reflexiveTautology := fun _ r => ¬ (r < r)
  by intros; simp [ltIrrefl]
vacuous_case notNe reflexiveTautology := fun _ r => ¬ (r ≠ r)
  by intros; simp [notNe]
vacuous_case neImpFalse reflexiveTautology := fun _ r => r ≠ r → False
  by intros; simp [neImpFalse]
vacuous_case eqTrue reflexiveTautology := fun _ r => (r = r) = True
  by intros; simp [eqTrue]
vacuous_case iffTrue reflexiveTautology := fun _ r => (r = r) ↔ True
  by intros; simp [iffTrue]
vacuous_case forallOnePoint reflexiveTautology :=
  fun _ r => ∀ y : Nat, y = r → y = r
  by intros; simp [forallOnePoint]
vacuous_case existsOnePoint reflexiveTautology := fun _ r => ∃ y : Nat, y = r
  by intros; simp [existsOnePoint]
vacuous_case existsOnePointSym reflexiveTautology :=
  fun x r => ∃ y : Nat, r = y ∧ x = x
  by intros; simp [existsOnePointSym]
vacuous_case iteRefl reflexiveTautology :=
  fun _ r => if r = r then True else False
  by intros; simp [iteRefl]
vacuous_case matchAllTrue reflexiveTautology :=
  fun _ r => match r with
    | 0 => True
    | _ + 1 => True
  by intro _ r₁ r₂; cases r₁ <;> cases r₂ <;> simp [matchAllTrue]
vacuous_case projRefl reflexiveTautology := fun x r => (r, x).1 = (x, r).2
  by intros; simp [projRefl]
vacuous_case matchNested reflexiveTautology :=
  fun x r => match r with
    | 0 => (match x with
      | 0 => True
      | _ + 1 => r = r)
    | n + 1 => n = n
  by intro x r₁ r₂; cases r₁ <;> cases r₂ <;> cases x <;> simp [matchNested]
vacuous_case matchOnProjection inputOnly :=
  fun x r => match (x, r).1 with
    | 0 => x < 9
    | _ + 1 => x < 9
  by intro x r₁ r₂; cases x <;> simp [matchOnProjection]
vacuous_case decideRefl reflexiveTautology := fun _ r => decide (r = r) = true
  by intros; simp [decideRefl]
vacuous_case bneFalse reflexiveTautology := fun _ r => (r != r) = false
  by intros; simp [bneFalse]
vacuous_case natBeqRefl reflexiveTautology := fun _ r => Nat.beq r r = true
  by intros; simp [natBeqRefl]
vacuous_case boolAnd reflexiveTautology := fun _ r => (r == r && true) = true
  by intros; simp [boolAnd]
vacuous_case excludedMiddle reflexiveTautology := fun _ r => r = 0 ∨ r ≠ 0
  by intro _ r₁ r₂; simp only [excludedMiddle]; omega
vacuous_case betaRefl reflexiveTautology := fun _ r => (fun y : Nat => y = y) r
  by intros; simp [betaRefl]
vacuous_case idWrap reflexiveTautology := fun _ r => id (r = r)
  by intros; simp [idWrap]
vacuous_case userWrapper reflexiveTautology := fun _ r => trivialOn r
  by intros; simp [userWrapper, trivialOn]
vacuous_case orTrue reflexiveTautology := fun x r => r = x + 1 ∨ True
  by intros; simp [orTrue]
vacuous_case impTrue reflexiveTautology := fun x r => r = x → True
  by intros; simp [impTrue]
vacuous_case falseImp reflexiveTautology := fun x r => False → r = x
  by intros; simp [falseImp]
vacuous_case selfImp reflexiveTautology := fun x r => r = x → r = x
  by intros; simp [selfImp]
vacuous_case selfIff reflexiveTautology := fun x r => r = x ↔ r = x
  by intros; simp [selfIff]
vacuous_case nestedConj reflexiveTautology :=
  fun x r => True ∧ ((r = r) ∧ (x = x ∨ r = 5))
  by intros; simp [nestedConj]
vacuous_case reflThenInput reflexiveTautology := fun x r => r = r → x < 7
  by intros; simp [reflThenInput]
vacuous_case iteSameBranches reflexiveTautology :=
  fun x r => if r = 3 then x < 7 else x < 7
  by intros; simp [iteSameBranches]
vacuous_case fnRefl reflexiveTautology := fun x r => r + x = r + x
  by intros; simp [fnRefl]
vacuous_case trueOr reflexiveTautology := fun x r => True ∨ r = x
  by intros; simp [trueOr]
vacuous_case andTrue reflexiveTautology := fun x r => (r = r ∧ True) ∧ x < 3
  by intros; simp [andTrue]
vacuous_case pprodProj reflexiveTautology :=
  fun x r => (PProd.mk r x).1 = (PProd.mk x r).2
  by intros; simp [pprodProj]
vacuous_case eqSymmIff reflexiveTautology := fun x r => r = x ↔ x = r
  by intro x r₁ r₂; simp only [eqSymmIff]; omega
vacuous_case eqSymmEm reflexiveTautology := fun x r => r = x ∨ x ≠ r
  by intro x r₁ r₂; simp only [eqSymmEm]; omega
vacuous_case conjCommIff reflexiveTautology :=
  fun x r => (r = x ∧ x < 5) ↔ (x < 5 ∧ r = x)
  by intro x r₁ r₂; simp only [conjCommIff]; omega
vacuous_case conjProjection reflexiveTautology :=
  fun x r => r = x ∧ x < 5 → r = x
  by intro x r₁ r₂; simp only [conjProjection]; omega

-- Erased by beta or zeta before any tautology is met: constant or input-only.
vacuous_case betaConst constTrue := fun _ r => (fun _ : Nat => True) r
  by intros; simp [betaConst]
vacuous_case letUnused inputOnly := fun x r => let _unused := r; x < 100
  by intros; simp [letUnused]
vacuous_case letInputRefl inputOnly := fun x r => let _y := r; x = x
  by intros; simp [letInputRefl]
vacuous_case betaInput inputOnly := fun x r => (fun _ : Nat => x < 100) r
  by intros; simp [betaInput]
vacuous_case projInput inputOnly := fun x r => (x, r).1 < 100
  by intros; simp [projInput]

-- Unsatisfiable postconditions: no output is accepted at all.
vacuous_case neSelf unsatisfiable := fun _ r => r ≠ r
  by intros; simp [neSelf]
vacuous_case ltSelf unsatisfiable := fun _ r => r < r
  by intros; simp [ltSelf]
vacuous_case andFalse unsatisfiable := fun x r => r = x ∧ False
  by intros; simp [andFalse]
vacuous_case contradiction unsatisfiable := fun x r => r = x ∧ ¬ (r = x)
  by intros; simp [contradiction]

-- Not syntactic tautologies: discharged by the bounded proof search.
vacuous_case zeroLe semanticallyInsensitive := fun _ r => 0 ≤ r
  by intros; simp [zeroLe]
vacuous_case ltSucc semanticallyInsensitive := fun _ r => r < r + 1
  by intros; simp [ltSucc]
vacuous_case subSelf semanticallyInsensitive := fun x r => r - r = 0 ∧ x < 5
  by intros; simp [subSelf]
vacuous_case arithEm semanticallyInsensitive := fun x r => x ≤ r ∨ r < x
  by intro x r₁ r₂; simp only [arithEm]; omega
vacuous_case mulZero semanticallyInsensitive := fun x r => r * 0 = x
  by intros; simp [mulZero]

end Disguises

/-! ## Differential battery: genuine postconditions the checker must accept -/

namespace Genuine

genuine_case eqSucc := fun x r => r = x + 1
  witness 0 1 0 by simp [eqSucc]
genuine_case leInput := fun x r => r ≤ x
  witness 0 0 1 by simp [leInput]
genuine_case neInput := fun x r => r ≠ x
  witness 0 1 0 by simp [neInput]
genuine_case guarded := fun x r => x = 0 → r = 1
  witness 0 1 0 by simp [guarded]
genuine_case onePointBinding := fun x r => ∃ y, y = r ∧ y < x
  witness 1 0 1 by simp [onePointBinding]
genuine_case forallOnePointBinding := fun x r => ∀ y, y = r → y ≤ x
  witness 0 0 1 by simp [forallOnePointBinding]
genuine_case matchShape := fun _ r => match r with
    | 0 => True
    | _ + 1 => False
  witness 0 0 1 by simp [matchShape]
genuine_case beqInput := fun x r => (r == x) = true
  witness 0 0 1 by simp [beqInput]
genuine_case bleInput := fun x r => Nat.ble r x = true
  witness 0 0 1 by simp [bleInput]
genuine_case decideInput := fun x r => decide (r = x) = true
  witness 0 0 1 by simp [decideInput]
genuine_case reflAndGenuine := fun x r => r = r ∧ r = x
  witness 0 0 1 by simp [reflAndGenuine]
genuine_case genuineOrInput := fun x r => r = x ∨ x = 5
  witness 0 0 1 by simp [genuineOrInput]
genuine_case iteGuarded := fun x r => if x = 0 then r = 1 else True
  witness 0 1 0 by simp [iteGuarded]
genuine_case impFalse := fun x r => r < x → False
  witness 1 1 0 by simp [impFalse]
genuine_case boundedAndNonneg := fun _ r => r ≤ 5 ∧ 0 ≤ r
  witness 0 0 6 by simp [boundedAndNonneg]
genuine_case projBinding := fun x r => (x, r).2 = x
  witness 0 0 1 by simp [projBinding]
genuine_case outputAsHypothesis := fun x r => r = 5 → x > 0
  witness 0 0 5 by simp [outputAsHypothesis]
genuine_case leSucc := fun x r => r ≤ x + 1
  witness 0 1 2 by simp [leSucc]
-- A `match` whose alternatives differ, or use the pattern variable, stays.
genuine_case matchPatternVar := fun x r => match r with
    | 0 => x = 0
    | n + 1 => x = n
  witness 0 0 2 by simp [matchPatternVar]
-- A discriminant that normalises to the input: the alternatives still differ.
genuine_case matchOnProjectionBinding := fun x r => match (x, r).1 with
    | 0 => r = 1
    | _ + 1 => r = 2
  witness 0 1 2 by simp [matchOnProjectionBinding]
-- The one-point rule needs the bound variable not to occur in the term:
-- `∃ y, y = r + y` says `r = 0`.
genuine_case onePointSelf := fun _ r => ∃ y, y = r + y
  witness 0 0 1 by
    unfold onePointSelf
    exact ⟨⟨0, rfl⟩, by rintro ⟨y, h⟩; omega⟩
-- A binder whose *type* mentions the output: `∃ _ : Fin r, True` says `0 < r`.
genuine_case existsFin := fun _ r => ∃ _y : Fin r, True
  witness 0 1 0 by
    unfold existsFin
    exact ⟨⟨⟨0, by omega⟩, trivial⟩, fun ⟨y, _⟩ => y.elim0⟩
-- ... and `∀ _ : Fin r, False` says `r = 0`.
genuine_case forallFin := fun _ r => ∀ _y : Fin r, False
  witness 0 0 1 by
    unfold forallFin
    exact ⟨fun y => y.elim0, fun h => h ⟨0, by omega⟩⟩
-- Distinct numerals may denote one element: `(5 : Fin 3) = 2` is *true*, so
-- the guarded equation binds `r`. Comparing the literals would call it vacuous.
genuine_case finLiteralGuard := fun x r => (5 : Fin 3) = 2 → r = x
  witness 0 0 1 by
    unfold finLiteralGuard
    exact ⟨fun _ => rfl, fun h => absurd (h (by decide)) (by decide)⟩

end Genuine

/-! ## Soundness traps: reflexive-looking postconditions that are genuine -/

namespace SoundnessTraps

/-- A carrier with a non-reflexive `==` and a non-reflexive `≤`. -/
structure Weird where
  n : Nat

/-- `a == a` holds only away from zero (compare `NaN != NaN` on floats). -/
instance : BEq Weird := ⟨fun a b => a.n == b.n && a.n != 0⟩

/-- `a ≤ a` holds only for `a.n ≤ 1`. -/
instance : LE Weird := ⟨fun a b => a.n + b.n ≤ 2⟩

/-- `(ret == ret) = true` over a non-reflexive `BEq`: it says `ret.n ≠ 0`. -/
def weirdBeqSelf (_x : Nat) (ret : Weird) : Prop := (ret == ret) = true

theorem weirdBeqSelf_dichotomy :
    PostconditionDichotomy (fun _ => True) weirdBeqSelf :=
  ⟨0, ⟨1⟩, ⟨0⟩, trivial, show ((⟨1⟩ : Weird) == ⟨1⟩) = true from rfl,
    show ¬ ((⟨0⟩ : Weird) == ⟨0⟩) = true by decide⟩

/-- `ret ≤ ret` over a non-reflexive `LE`: it says `ret.n ≤ 1`. -/
def weirdLeSelf (_x : Nat) (ret : Weird) : Prop := ret ≤ ret

theorem weirdLeSelf_dichotomy :
    PostconditionDichotomy (fun _ => True) weirdLeSelf :=
  ⟨0, ⟨0⟩, ⟨5⟩, trivial, show 0 + 0 ≤ 2 by omega, show ¬ 5 + 5 ≤ 2 by omega⟩

-- Both look like the class-3 disguises `beqReflPost` and `leRefl`, and both
-- have a kernel dichotomy: the checker must not call them tautologies.
#expect_binds weirdBeqSelf
#expect_binds weirdLeSelf

/-- A contract that pins the return through a helper on the answer. -/
def retValPinned : MirCallContract where
  pre _ := True
  post _ ans := mirCallRetVal? ans = some (u32Arg 1)

theorem retValPinned_returnValueDichotomy :
    MirCallContractReturnValueDichotomy retValPinned :=
  ⟨witnessReq, u32Arg 1, u32Arg 0, emptyMemory, trivial, rfl,
    fun h => absurd (u32Arg_inj (Option.some.inj h)) (by decide)⟩

/-- The same helper, used only to say "the answer is a return". -/
def retValIsSome : MirCallContract where
  pre _ := True
  post _ ans := mirCallRetVal? ans ≠ none

theorem retValIsSome_not_normalDichotomy :
    ¬ MirCallContractNormalDichotomy retValIsSome :=
  not_mirCallContractNormalDichotomy_of_return_blind fun _ _ _ _ _ _ =>
    ⟨fun _ => nofun, fun _ => nofun⟩

/-- ... and its Boolean spelling. -/
def retValIsSomeBool : MirCallContract where
  pre _ := True
  post _ ans := (mirCallRetVal? ans).isSome = true

theorem retValIsSomeBool_not_normalDichotomy :
    ¬ MirCallContractNormalDichotomy retValIsSomeBool :=
  not_mirCallContractNormalDichotomy_of_return_blind fun _ _ _ _ _ _ => Iff.rfl

#expect_binds retValPinned
#expect_vacuous retValIsSome returnBlind
#expect_vacuous retValIsSomeBool returnBlind

run_meta do
  assertEnsuresBindsOutput ``retValPinned (cfg := { strictReturnValue := true })

end SoundnessTraps

/-! ## Entry points, arities, and error paths -/

namespace EntryPoints

/-- A Boolean-valued postcondition. -/
def boolPost (x r : Nat) : Bool := r == x + 1

def boolReflPost (_x r : Nat) : Bool := r == r

/-- A ternary postcondition whose output is the last binder. -/
def sumPost (a b r : Nat) : Prop := r = a + b

/-- A unary postcondition: the only binder is the output. -/
def unaryRefl (r : Nat) : Prop := r = r

/-- A postcondition over an opaque MIR predicate: analysed without unfolding. -/
def mirBoolEnsures (specBody : CapturedMir) (args : List Value) (ret : Value) :
    Prop :=
  MirBoolPredicateHolds specBody (args ++ [ret])

/-- A proposition is not a postcondition. -/
def notAPost : Prop := True

#expect_binds boolPost
#expect_vacuous boolReflPost reflexiveTautology
#expect_binds sumPost
#expect_vacuous unaryRefl reflexiveTautology
#expect_binds mirBoolEnsures

run_meta do
  -- `Expr` entry point on terms that are not constants.
  let r ← reportOfTerm (← `(fun (x r : Nat) => r = x))
  unless r.bindsOutput && r.arity == 2 && r.outputIdxs == #[1] do
    throwError "lambda: {r.describe}"
  let r ← reportOfTerm (← `(fun (_x r : Nat) => r = r))
  unless r.reason? == some .reflexiveTautology do
    throwError "reflexive lambda: {r.describe}"
  -- A `MirCallContract` structure instance given directly as a term.
  let r ← reportOfTerm (← `(({ post := fun _ _ => True } : MirCallContract)))
  unless r.reason? == some .outcomeBlind do
    throwError "structure instance: {r.describe}"
  -- Field projections of a contract are functions like any other.
  let r ← reportOfTerm (← `(SliceIsEmpty.sliceIsEmptyContract.post))
  unless r.bindsOutput do
    throwError "projection: {r.describe}"
  let r ← reportOfTerm (← `(Class5.returnBlindNounwind.post))
  unless r.reason? == some .returnBlind do
    throwError "projection of a return-blind contract: {r.describe}"
  -- A raw `Expr` carrying `mdata` and an unreduced `let`, built by hand:
  -- `fun (x r : Nat) => mdata (let y := r; y = y)`.
  let nat := mkConst ``Nat
  let body := Expr.letE `y nat (.bvar 0)
    (mkApp3 (mkConst ``Eq [Level.one]) nat (.bvar 0) (.bvar 0)) false
  let r ← checkEnsuresBindsOutput
    (.lam `x nat (.lam `r nat (.mdata MData.empty body) .default) .default)
  unless r.reason? == some .reflexiveTautology do
    throwError "mdata and let: {r.describe}"
  -- Caller-designated outputs: in `sumPost a b r`, designating `a` and `b`.
  let r ← reportOf ``sumPost (outputs := some #[0, 1])
  unless r.bindsOutput && r.boundOutputIdxs == #[0, 1] do
    throwError "designated outputs: {r.describe}"
  -- Designating an input of an input-only postcondition makes it the output.
  assertEnsuresBindsOutput ``Class4.inputBoundPost (outputParamIdxs := some #[0])
  -- Without the proof search, `0 ≤ r` is (soundly) reported as binding.
  let r ← reportOf ``Disguises.zeroLe (cfg := { semanticProbe := false })
  unless r.bindsOutput do
    throwError "zeroLe without the proof search: {r.describe}"
  -- Error paths.
  let failed (x : MetaM EnsuresCheckReport) : MetaM Bool := do
    try
      discard x
      return false
    catch _ =>
      return true
  unless ← failed (reportOf ``notAPost) do
    throwError "a proposition was accepted as a postcondition"
  unless ← failed (reportOf ``sumPost (outputs := some #[3])) do
    throwError "an out-of-range output index was accepted"
  unless ← failed (reportOf ``sumPost (outputs := some #[])) do
    throwError "an empty output designation was accepted"
  unless ← failed (reportOf ``u32Arg) do
    throwError "a non-proposition-valued function was accepted"
  -- The assertion helpers fail in the right direction.
  let throws (x : MetaM Unit) : MetaM Bool := do
    try
      x
      return false
    catch _ =>
      return true
  unless ← throws (assertEnsuresBindsOutput ``Class3.reflPost) do
    throwError "assertEnsuresBindsOutput accepted a vacuous postcondition"
  unless ← throws (assertEnsuresVacuous ``Genuine.eqSucc) do
    throwError "assertEnsuresVacuous accepted a binding postcondition"
  unless ← throws (assertEnsuresVacuous ``Class3.reflPost (some .constTrue)) do
    throwError "assertEnsuresVacuous accepted the wrong reason"
  unless ← throws (assertRequiresRefuted ``Refinement.incPre) do
    throwError "assertRequiresRefuted accepted a satisfiable precondition"
  unless ← throws (assertRequiresNotRefuted ``Class1.falsePre) do
    throwError "assertRequiresNotRefuted accepted `False`"

end EntryPoints

/-! ## Axiom and soundness audit -/

namespace Audit

/-- The only axioms a theorem of the prototype or of this file may use. -/
def allowedAxioms : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]

def isAllowedAxiom (n : Name) : Bool := allowedAxioms.contains n

/--
Compiler-generated theorems (equation lemmas, injectivity, `sizeOf`,
constructor-index lemmas of derived instances, and proof-valued structure
projections), excluded from the *authored* counts but audited all the same.
-/
def isGeneratedTheorem (env : Environment) (n : Name) : Bool :=
  n.isInternalDetail || env.isProjectionFn n ||
    match n with
    | .str _ s =>
      s == "injEq" || s == "sizeOf_spec" || s == "inj" || s == "eq_def" ||
        s == "ofNat_ctorIdx" || s.startsWith "eq_" || s.startsWith "match_"
    | _ => false

/-- Whether `e` mentions a constant of the `Lean` namespace (meta-level code). -/
def mentionsLean (e : Expr) : Bool :=
  e.getUsedConstants.any fun n => n.getRoot == `Lean

run_meta do
  let env ← getEnv
  let theoryNs := `Anneal.SpecRealizabilityPrototype
  let testNs := `SpecRealizabilityProtoTests
  -- The allow-list rejects exactly what it must.
  for bad in #[``sorryAx, ``Lean.ofReduceBool, ``Lean.trustCompiler] do
    if isAllowedAxiom bad then
      throwError "audit self-test: `{bad}` is allowed"
  unless (← collectAxioms ``Classical.em).contains ``Classical.choice do
    throwError "audit self-test: `collectAxioms` misses `Classical.choice`"
  let decls := env.constants.fold (init := (#[] : Array (Name × ConstantInfo)))
    fun acc n ci =>
      let user := privateToUserName n
      if theoryNs.isPrefixOf user || testNs.isPrefixOf user then
        acc.push (n, ci)
      else
        acc
  let mut theoryThms := 0
  let mut testThms := 0
  let mut generatedThms := 0
  let mut objectDecls := 0
  for (n, ci) in decls do
    let user := privateToUserName n
    -- No declaration of either namespace, theorem or not, is an axiom or
    -- unsafe (the `partial` functions of the checker are safe opaque constants).
    if ci matches .axiomInfo _ then
      throwError "audit: `{n}` is declared as an axiom"
    if ci.isUnsafe then
      throwError "audit: `{n}` is unsafe"
    match ci with
    | .thmInfo _ =>
      for ax in ← collectAxioms n do
        unless isAllowedAxiom ax do
          throwError "audit: theorem `{n}` depends on the axiom `{ax}`"
      if isGeneratedTheorem env n then
        generatedThms := generatedThms + 1
      else if theoryNs.isPrefixOf user then
        theoryThms := theoryThms + 1
      else
        testThms := testThms + 1
    | _ =>
      -- Object-level definitions (those not written against the `Lean` API)
      -- are held to the same axiom discipline as theorems.
      let usesLean := mentionsLean ci.type ||
        (ci.value?.map mentionsLean).getD false
      unless usesLean do
        for ax in ← collectAxioms n do
          unless isAllowedAxiom ax do
            throwError "audit: definition `{n}` depends on the axiom `{ax}`"
        objectDecls := objectDecls + 1
  unless theoryThms ≥ 15 do
    throwError "audit: only {theoryThms} theorems audited in `{theoryNs}`"
  unless testThms ≥ 15 do
    throwError "audit: only {testThms} theorems audited in `{testNs}`"
  logInfo m!"audit: {decls.size} declarations, none unsafe, none an axiom; \
    {theoryThms} authored theorems in `{theoryNs}`, {testThms} authored \
    theorems in `{testNs}`, {generatedThms} generated theorems, {objectDecls} \
    object-level definitions; axioms ⊆ {allowedAxioms}"

end Audit

end SpecRealizabilityProtoTests
