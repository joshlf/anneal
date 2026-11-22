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
  -- Judged without its `requires`, the postcondition of `contradictoryClaim`
  -- binds its output; judged as a contract, nothing is admissible.
  assertEnsuresBindsOutput ``contradictoryClaim (cfg := { useRequires := false })
  assertEnsuresVacuous ``contradictoryClaim (some .requiresUnsatisfiable)
  assertEnsuresVacuous ``contradictoryPreContract (some .requiresUnsatisfiable)
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

/-! ## Adversarial hardening regressions (Pass B1) -/

namespace HardeningB1

/-! ### Part I bridges, strictness chains, and vacuous-handler theorems -/

theorem claimPre_bridge (body : CapturedMir) :
    ClaimPreSatisfiable (Class1.contradictoryClaim body) ↔
      NonVacuousPre (Class1.contradictoryClaim body).pre :=
  claimPreSatisfiable_iff_nonVacuousPre

theorem statefulPre_bridge (body : CapturedMir) :
    StatefulClaimPreSatisfiable (Refinement.checkedIncClaim body) ↔
      NonVacuousStatefulPre (Refinement.checkedIncClaim body).pre :=
  statefulClaimPreSatisfiable_iff_nonVacuousStatefulPre

/--
An unsatisfiable `MirCallContract` precondition is satisfied even by a handler
that unconditionally triggers undefined behavior (`ITree.fail .ub`).
-/
theorem contradictoryPre_holdsOn_ub_handler :
    Class1.contradictoryPreContract.holdsOn
      (fun _ => Trusted.ITree.ITree.fail Trusted.Effect.FailureKind.ub) :=
  mirCallContract_holdsOn_of_not_preSatisfiable
    Class1.contradictoryPre_not_preSatisfiable _

/--
Every `externalSpecCallContract` (even one with a genuine `extraPost`) is
satisfied by the trivial always-aborting handler, because `.aborted` is `True`.
-/
theorem extSpecGenuine_holdsOn_abort_handler (target : DefPath)
    (sidecar : CapturedMir) :
    (Class5.extSpecGenuine target sidecar).holdsOn (fun _ => .ret .aborted) :=
  mirCallContract_holdsOn_abort_of_abort_permitted fun _ _ => trivial

theorem returnValueDichotomy_strict :
    (∀ c, MirCallContractReturnValueDichotomy c →
      MirCallContractNormalDichotomy c) ∧
      ∃ c, MirCallContractNormalDichotomy c ∧
        ¬ MirCallContractReturnValueDichotomy c :=
  returnValueDichotomy_strictly_stronger_than_normalDichotomy

theorem statefulReturnDichotomy_strict (body : CapturedMir) :
    (∀ c, StatefulClaimReturnDichotomy c → StatefulClaimDichotomy c) ∧
      ∃ c : StatefulClaim, c.body = body ∧
        StatefulClaimDichotomy c ∧ ¬ StatefulClaimReturnDichotomy c :=
  statefulClaimReturnDichotomy_strictly_stronger_than_dichotomy body

/-- An unsatisfiable `TotalClaim` verifies for every MIR body. -/
def unsatTotalClaim (body : CapturedMir) : TotalClaim where
  body := body
  pre args _ := ∃ a, args = [u32Arg a] ∧ a < 10 ∧ a > 20
  post _ _ ret _ := ret = u32Arg 0

theorem unsatTotalClaim_verified (body : CapturedMir) :
    TotalVerificationResult (unsatTotalClaim body) :=
  totalVerificationResult_of_not_preSatisfiable fun ⟨_, _, a, _, h₁, h₂⟩ => by
    omega

/-- An unsatisfiable `ModularClaim` verifies for every MIR body and rely. -/
def unsatModularClaim (body : CapturedMir) : ModularClaim where
  body := body
  envAssumed _ := True
  pre args _ := ∃ a, args = [u32Arg a] ∧ a < 10 ∧ a > 20
  post _ _ ret _ := ret = u32Arg 0

theorem unsatModularClaim_verified (body : CapturedMir) :
    ModularVerificationResult (unsatModularClaim body) :=
  modularVerificationResult_of_not_preSatisfiable fun ⟨_, _, a, _, h₁, h₂⟩ => by
    omega

/-- Observational mutation adequacy applied to `slice::is_empty`. -/
theorem sliceIsEmpty_kills_every_obs_mutant
    (mutant : OutputMutant MirCallReq (Value × Memory))
    (req : MirCallReq) (out : Value × Memory)
    (h_pre : SliceIsEmpty.sliceIsEmptyContract.pre req)
    (h_post : mirCallNormalPost SliceIsEmpty.sliceIsEmptyContract req out)
    (h_ne : (mutant req out).1 ≠ out.1) :
    KillsMutantAt SliceIsEmpty.sliceIsEmptyContract.pre
      (mirCallNormalPost SliceIsEmpty.sliceIsEmptyContract) mutant req out :=
  (contractDeterministicOn_iff_kills_every_obs_nonequivalent_mutant Prod.fst).mp
    SliceIsEmpty.return_deterministic mutant req out h_pre h_post h_ne

/-- `MirCallContractSubsumes` transfers return-value dichotomy in one memory. -/
theorem sliceIsEmpty_subsumes_returnValueDichotomy :
    MirCallContractReturnValueDichotomy SliceIsEmpty.sliceIsEmptyContract ∧
      MirCallContractReturnValueDichotomy SliceIsEmpty.sliceIsEmptyContract :=
  MirCallContractSubsumes.returnValueDichotomy_of_super_ok_sub_bad
    (MirCallContractSubsumes.refl _)
    ⟨SliceIsEmpty.req 0, .scalar ⟨1, 1⟩, .scalar ⟨0, 1⟩, emptyMemory,
      SliceIsEmpty.pre_req 0 (by decide), SliceIsEmpty.post_empty_true,
      SliceIsEmpty.rejects_false_on_empty⟩

/-! ### Soundness bug regressions (no false positives or ill-typed residuals) -/

/--
`collapseMatch?` must peel only `altNumParams` pattern binders, never domain
binders of a function-valued motive (`Nat → Nat`).
-/
def genuineFnMatch (x r : Nat) : Prop :=
  (match x with
   | 0 => fun _ : Nat => 0
   | _ + 1 => fun _ : Nat => 0) = (fun _ : Nat => r)

theorem genuineFnMatch_dichotomy :
    PostconditionDichotomy (fun _ => True) genuineFnMatch :=
  ⟨0, 0, 1, trivial, rfl, fun h => by
    have := congrFun h 0
    exact Nat.zero_ne_one this⟩

/-- Dependent-domain function equality whose RHS collapses via `collapseMatch?`. -/
def genuineFinFnMatch (x r : Nat) : Prop :=
  ∀ f : Fin r → Nat,
    f = match x with
        | 0 => fun _ => 0
        | _ + 1 => fun _ => 0

theorem genuineFinFnMatch_dichotomy :
    PostconditionDichotomy (fun _ => True) genuineFinFnMatch := by
  refine ⟨0, 0, 1, trivial, ?_, ?_⟩
  · intro f
    funext i
    exact i.elim0
  · intro h
    have h1 := congrFun (h (fun _ => 1)) ⟨0, Nat.zero_lt_one⟩
    exact Nat.one_ne_zero h1

/--
Negated boilerplate conjunct paired with a genuine return binding: boilerplate
stripping must stay restricted to positive conjunctive positions so `¬ callFramePreserved`
never collapses to `False` and falsely flags `retVal = u32Arg 1` as vacuous.
-/
def genuineNegBoilerplate : MirCallContract where
  pre _ := True
  post req ans :=
    match ans with
    | .returned retVal memAfter =>
      ¬ callFramePreserved req.memory memAfter ∧ retVal = u32Arg 1
    | .panicked _ => False
    | .aborted => False

theorem genuineNegBoilerplate_returnValueDichotomy :
    MirCallContractReturnValueDichotomy genuineNegBoilerplate :=
  ⟨witnessReq, u32Arg 1, u32Arg 0,
    { emptyMemory with activeProtectors := [0] }, trivial,
    ⟨fun h => List.cons_ne_self 0 _ h.2.2.2.1, rfl⟩,
    fun h => absurd (u32Arg_inj h.2) (by decide)⟩

-- Genuine `Iff` and `Exists` postconditions immune to tactic error recovery.
genuine_case genuineIff := fun x r => (r = 0) ↔ (x = 0)
  witness 0 0 1 by simp [genuineIff]
genuine_case genuineExistsSucc := fun _ r => ∃ y : Nat, r = y + 1
  witness 0 1 0 by
    unfold genuineExistsSucc
    exact ⟨⟨0, rfl⟩, by rintro ⟨y, h⟩; omega⟩

#expect_binds genuineFnMatch
#expect_binds genuineFinFnMatch
#expect_binds genuineNegBoilerplate

run_meta do
  -- `genuineNegBoilerplate` binds beyond boilerplate in every mode.
  let rDef ← reportOf ``genuineNegBoilerplate
  unless rDef.bindsOutput && rDef.bindsBeyondBoilerplate do
    throwError "genuineNegBoilerplate (default): {rDef.describe}"
  assertEnsuresBindsOutput ``genuineNegBoilerplate
    (cfg := { userEnsuresOnly := true })
  assertEnsuresBindsOutput ``genuineNegBoilerplate
    (cfg := { userEnsuresOnly := true, strictReturnValue := true })
  -- `frameOnlyMirCallContract` binds `memAfter` in default mode, fails strict
  -- and user-ensures modes.
  let rFrame ← reportOf ``frameOnlyMirCallContract
  unless rFrame.bindsOutput && !rFrame.bindsBeyondBoilerplate do
    throwError "frameOnlyMirCallContract (default): {rFrame.describe}"
  expectReason ``frameOnlyMirCallContract .returnValueUnconstrained
    (cfg := { strictReturnValue := true })
  expectReason ``frameOnlyMirCallContract .boilerplateOnly
    (cfg := { userEnsuresOnly := true })

/-! ### Closed bypass regressions (each backed by a kernel insensitivity proof) -/

-- 1. Discarded projections distributed through `ite`, `dite`, and `match`.
vacuous_case projOfIte inputOnly :=
  fun x r => (if x = 0 then (x, r) else (x + 1, r)).1 < 100
  by intro x r₁ r₂; simp only [projOfIte]; split <;> rfl
vacuous_case projOfMatch inputOnly :=
  fun x r => (match x with | 0 => (0, r) | n + 1 => (n, r)).1 < 100
  by intro x r₁ r₂; cases x <;> rfl
vacuous_case diteDataTrue reflexiveTautology :=
  fun x r => (if _h : r = r then x else r) < 100
  by intros; simp [diteDataTrue]
vacuous_case diteDataSame reflexiveTautology :=
  fun x r => (if _h : r = 0 then x else x) < 100
  by intros; simp [diteDataSame]

/-- `MirCallContract` hiding `retVal` inside a discarded tuple projection in `ite`. -/
def mirProjIte : MirCallContract where
  pre _ := True
  post req ans :=
    match ans with
    | .returned retVal _ =>
      (if req.args = [] then (req.defPath, retVal) else ("a", retVal)).1 = ""
    | .panicked _ => False
    | .aborted => True

theorem mirProjIte_not_normalDichotomy :
    ¬ MirCallContractNormalDichotomy mirProjIte :=
  not_mirCallContractNormalDichotomy_of_return_blind fun req _ _ _ _ _ => by
    dsimp [mirProjIte]
    split <;> rfl

#expect_vacuous mirProjIte returnBlind

-- 2. Propositional tautologies, absorption, dead branches, and `dite` case splits.
vacuous_case diteSame reflexiveTautology :=
  fun x r => if _h : r = 0 then x < 5 else x < 5
  by intros; simp [diteSame]
vacuous_case diteDependent reflexiveTautology :=
  fun x r => if _h : r = 0 then (r = 0 ∧ x < 5) else (r ≠ 0 ∧ x < 5)
  by intro x r₁ r₂; simp only [diteDependent]; split <;> split <;> omega
vacuous_case caseSplitNat reflexiveTautology :=
  fun x r => (r = 0 → x < 5) ∧ (r ≠ 0 → x < 5)
  by intro x r₁ r₂; simp only [caseSplitNat]; omega
vacuous_case iteReordered reflexiveTautology :=
  fun x r => if r = 0 then (x < 5 ∧ x < 10) else (x < 10 ∧ x < 5)
  by intro x r₁ r₂; simp only [iteReordered]; split <;> split <;> omega
vacuous_case matchReordered reflexiveTautology :=
  fun x r => match r with
    | 0 => x < 5 ∧ x < 10
    | _ + 1 => x < 10 ∧ x < 5
  by intro x r₁ r₂; cases r₁ <;> cases r₂ <;> simp only [matchReordered] <;> omega

-- Non-arithmetic (`Value`) propositional disguises caught by `propSimplify`.
def caseSplitVal (a r : Value) : Prop := (r = a → a = .unit) ∧ (r ≠ a → a = .unit)
def deadBranchVal (a r : Value) : Prop := (a ≠ .unit → r = .unit) ∧ a = .unit
def disjAbsorbVal (a r : Value) : Prop := a = .unit ∨ (a = .unit ∧ r = .unit)
def conjAbsorbVal (a r : Value) : Prop := a = .unit ∧ (a = .unit ∨ r = .unit)
def demorganVal (a r : Value) : Prop := ¬ (r = a ∧ a = .unit) ∨ r = a
def contraposVal (a r : Value) : Prop :=
  (r = a → a = .unit) ↔ (a ≠ .unit → r ≠ a)
def peirceVal (a r : Value) : Prop :=
  ((r = a → a = .unit) → r = a) → r = a

theorem caseSplitVal_not_dichotomy (pre : Value → Prop) :
    ¬ PostconditionDichotomy pre caseSplitVal :=
  not_dichotomy_of_input_predicate (fun a => a = .unit) fun a r _ =>
    ⟨fun h => (Classical.em (r = a)).elim h.1 h.2, fun h => ⟨fun _ => h, fun _ => h⟩⟩

theorem deadBranchVal_not_dichotomy (pre : Value → Prop) :
    ¬ PostconditionDichotomy pre deadBranchVal :=
  not_dichotomy_of_input_predicate (fun a => a = .unit) fun _ _ _ =>
    ⟨fun h => h.2, fun h => ⟨fun hne => absurd h hne, h⟩⟩

theorem disjAbsorbVal_not_dichotomy (pre : Value → Prop) :
    ¬ PostconditionDichotomy pre disjAbsorbVal :=
  not_dichotomy_of_input_predicate (fun a => a = .unit) fun _ _ _ =>
    ⟨fun h => h.elim id And.left, Or.inl⟩

theorem conjAbsorbVal_not_dichotomy (pre : Value → Prop) :
    ¬ PostconditionDichotomy pre conjAbsorbVal :=
  not_dichotomy_of_input_predicate (fun a => a = .unit) fun _ _ _ =>
    ⟨And.left, fun h => ⟨h, Or.inl h⟩⟩

theorem demorganVal_not_dichotomy (pre : Value → Prop) :
    ¬ PostconditionDichotomy pre demorganVal :=
  not_dichotomy_of_universal_post fun a r _ =>
    (Classical.em (r = a)).elim Or.inr fun h => Or.inl fun ⟨hr, _⟩ => h hr

theorem contraposVal_not_dichotomy (pre : Value → Prop) :
    ¬ PostconditionDichotomy pre contraposVal :=
  not_dichotomy_of_universal_post fun _ _ _ =>
    ⟨fun h hne hr => hne (h hr), fun h hr =>
      Classical.byContradiction fun hne => h hne hr⟩

theorem peirceVal_not_dichotomy (pre : Value → Prop) :
    ¬ PostconditionDichotomy pre peirceVal :=
  not_dichotomy_of_universal_post fun _ _ _ h =>
    Classical.byContradiction fun hne => hne (h fun hr => absurd hr hne)

#expect_vacuous caseSplitVal reflexiveTautology
#expect_vacuous deadBranchVal reflexiveTautology
#expect_vacuous disjAbsorbVal reflexiveTautology
#expect_vacuous conjAbsorbVal reflexiveTautology
#expect_vacuous demorganVal reflexiveTautology
#expect_vacuous contraposVal reflexiveTautology
#expect_vacuous peirceVal reflexiveTautology

/-- Reordered conjuncts across all three outcomes remain `outcomeBlind`. -/
def outcomeBlindReordered : MirCallContract where
  pre _ := True
  post req ans :=
    match ans with
    | .returned _ _ => req.args = [] ∧ req.defPath = ""
    | .panicked _ => req.defPath = "" ∧ req.args = []
    | .aborted => req.args = [] ∧ req.defPath = ""

theorem outcomeBlindReordered_not_dichotomy :
    ¬ MirCallContractDichotomy outcomeBlindReordered :=
  not_mirCallContractDichotomy_of_outcome_blind fun _ a₁ a₂ _ => by
    cases a₁ <;> cases a₂ <;> simp [outcomeBlindReordered, and_comm]

#expect_vacuous outcomeBlindReordered outcomeBlind

-- 3. Curried `match` collapse with non-empty `remaining`.
vacuous_case matchCurriedConst reflexiveTautology :=
  fun x r => (match r with | 0 => fun _ : Nat => True | _ + 1 => fun _ : Nat => True) x
  by intro _ r₁ r₂; cases r₁ <;> cases r₂ <;> rfl

-- 4. Existential currying (`Prod`, `Subtype`), case-split one-point, and witness search.
vacuous_case existsPairNat reflexiveTautology :=
  fun _ r => ∃ p : Nat × Nat, p.1 = r
  by intro _ r₁ r₂; exact ⟨fun _ => ⟨(r₂, 0), rfl⟩, fun _ => ⟨(r₁, 0), rfl⟩⟩

vacuous_case existsSubtype reflexiveTautology :=
  fun _ r => ∃ _ : { y : Nat // y = r }, True
  by intro _ r₁ r₂; exact ⟨fun _ => ⟨⟨r₂, rfl⟩, trivial⟩, fun _ => ⟨⟨r₁, rfl⟩, trivial⟩⟩

vacuous_case existsGe semanticallyInsensitive :=
  fun _ r => ∃ y : Nat, r ≤ y
  by intro _ r₁ r₂; exact ⟨fun _ => ⟨r₂, Nat.le_refl _⟩, fun _ => ⟨r₁, Nat.le_refl _⟩⟩

vacuous_case existsGt semanticallyInsensitive :=
  fun _ r => ∃ y : Nat, r < y
  by intro _ r₁ r₂; exact ⟨fun _ => ⟨r₂ + 1, Nat.lt_succ_self _⟩,
    fun _ => ⟨r₁ + 1, Nat.lt_succ_self _⟩⟩

vacuous_case existsFinIteProj inputOnly :=
  fun x r => ∃ _ : Fin (if x = 0 then (x, r) else (x + 1, r)).1, True
  by intro x r₁ r₂; cases x <;> rfl

def existsPairMir : MirCallContract where
  pre _ := True
  post _ ans := ∃ p : Value × Memory, ans = .returned p.1 p.2

theorem existsPairMir_not_normalDichotomy :
    ¬ MirCallContractNormalDichotomy existsPairMir :=
  not_mirCallContractNormalDichotomy_of_return_blind fun _ v₁ m₁ v₂ m₂ _ =>
    ⟨fun _ => ⟨(v₂, m₂), rfl⟩, fun _ => ⟨(v₁, m₁), rfl⟩⟩

def existsImpCaseVal (x : Nat) (r : Value) : Prop :=
  ∃ y : Value, (x < 5 → y = r) ∧ (¬ x < 5 → y = r)

theorem existsImpCaseVal_not_dichotomy (pre : Nat → Prop) :
    ¬ PostconditionDichotomy pre existsImpCaseVal :=
  not_dichotomy_of_universal_post fun _ r _ => ⟨r, fun _ => rfl, fun _ => rfl⟩

#expect_vacuous existsPairMir returnBlind
#expect_vacuous existsImpCaseVal reflexiveTautology

-- 5. Subsingleton outputs and subsingleton equalities.
def subsingletonFin1Pred (p : Fin 1 → Prop) (_x : Nat) (r : Fin 1) : Prop := p r
def emptyOutputPred (p : Empty → Prop) (_x : Nat) (r : Empty) : Prop := p r
def subsingletonFin1Eq (f : Nat → Fin 1) (x r : Nat) : Prop := f r = f x

theorem subsingletonFin1Pred_not_dichotomy (p : Fin 1 → Prop) (pre : Nat → Prop) :
    ¬ PostconditionDichotomy pre (subsingletonFin1Pred p) :=
  not_dichotomy_of_subsingleton

theorem emptyOutputPred_not_dichotomy (p : Empty → Prop) (pre : Nat → Prop) :
    ¬ PostconditionDichotomy pre (emptyOutputPred p) :=
  not_dichotomy_of_subsingleton_output fun a => a.elim

theorem subsingletonFin1Eq_not_dichotomy (f : Nat → Fin 1) (pre : Nat → Prop) :
    ¬ PostconditionDichotomy pre (subsingletonFin1Eq f) :=
  not_dichotomy_of_universal_post fun x r _ => Subsingleton.elim (f r) (f x)

#expect_vacuous subsingletonFin1Pred semanticallyInsensitive
#expect_vacuous emptyOutputPred semanticallyInsensitive
#expect_vacuous subsingletonFin1Eq reflexiveTautology

-- 6. Nested arithmetic subformula probing and small data-helper unfolding.
def mixedValueAndArith (a : Value) (x r : Nat) : Prop :=
  (a = .unit ∧ (x ≤ r ∨ r < x)) ∨ (a = .unit ∧ r = 0)

theorem mixedValueAndArith_not_dichotomy (a : Value) (pre : Nat → Prop) :
    ¬ PostconditionDichotomy pre (mixedValueAndArith a) :=
  not_dichotomy_of_input_predicate (fun _ => a = .unit) fun x r _ =>
    ⟨fun h => h.elim And.left And.left,
      fun h => Or.inl ⟨h, show x ≤ r ∨ r < x by omega⟩⟩

def constZeroHelper (n : Nat) : Nat := n - n

vacuous_case helperSubZero semanticallyInsensitive :=
  fun x r => constZeroHelper r < x
  by intro x r₁ r₂; simp [helperSubZero, constZeroHelper]

#expect_vacuous mixedValueAndArith semanticallyInsensitive

-- 7. `checkRequiresSatisfiable`: Bool preconditions, empty domains, nested And/Or/Exists.
def boolFalsePre (_x : Nat) : Bool := false
def emptyDomainPre (_ : Empty) : Prop := True
def unsatPreAndExists (x : Nat) : Prop := x < 100 ∧ (∃ a : Nat, a < 10 ∧ a > 20)
def unsatExtSpecPre (target : DefPath) (sidecar : CapturedMir) : MirCallContract :=
  externalSpecCallContract target sidecar
    (fun args => ∃ a, args = [u32Arg a] ∧ a < 10 ∧ a > 20)
    (fun _ ret => ret = .unit)
def unsatPreOr (x : Nat) : Prop := (x < 5 ∧ x > 10) ∨ (x < 2 ∧ x > 8)

theorem emptyDomainPre_not_satisfiable :
    ¬ PreconditionSatisfiable emptyDomainPre :=
  fun ⟨e, _⟩ => e.elim

theorem unsatPreAndExists_not_satisfiable :
    ¬ PreconditionSatisfiable unsatPreAndExists := by
  rintro ⟨_, _, a, h₁, h₂⟩
  omega

theorem unsatExtSpecPre_not_satisfiable (target : DefPath)
    (sidecar : CapturedMir) :
    ¬ MirCallContractPreSatisfiable (unsatExtSpecPre target sidecar) := by
  rintro ⟨req, _, _, _, a, _, h₁, h₂⟩
  omega

theorem unsatPreOr_not_satisfiable : ¬ PreconditionSatisfiable unsatPreOr := by
  rintro ⟨x, ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩⟩ <;> omega

run_meta do
  assertRequiresRefuted ``boolFalsePre
  assertRequiresRefuted ``emptyDomainPre
  assertRequiresRefuted ``unsatPreAndExists
  assertRequiresRefuted ``unsatExtSpecPre
  assertRequiresRefuted ``unsatPreOr
  -- Syntactic passes catch projection-distribution and propositional disguises
  -- even with `semanticProbe := false`.
  let noProbe : EnsuresCheckConfig := { semanticProbe := false }
  for n in #[``projOfIte, ``projOfMatch, ``diteDataTrue, ``diteDataSame,
      ``diteSame, ``deadBranchVal, ``disjAbsorbVal, ``conjAbsorbVal,
      ``demorganVal, ``contraposVal, ``peirceVal, ``matchCurriedConst,
      ``existsPairNat, ``existsSubtype, ``existsImpCaseVal, ``subsingletonFin1Eq] do
    assertEnsuresVacuous n (cfg := noProbe)

end HardeningB1

/-! ## Hardening (pass A1): case trees, hypotheses, and the precondition -/

namespace HardeningA1

/-! ### `match` case trees: several discriminants and nested patterns -/

/-- Return-blind behind a `match` on the answer *and* the arguments. -/
def multiDiscrBlind : MirCallContract where
  pre _ := True
  post req ans :=
    match ans, req.args with
    | .returned _ _, [_] => True
    | .returned _ _, _ => True
    | _, _ => False

theorem multiDiscrBlind_post_returned (req : MirCallReq) (v : Value) (m : Memory) :
    multiDiscrBlind.post req (.returned v m) := by
  show (match MirCallAns.returned v m, req.args with
    | .returned _ _, [_] => True
    | .returned _ _, _ => True
    | _, _ => False)
  split <;> first | trivial | simp_all

theorem multiDiscrBlind_not_normalDichotomy :
    ¬ MirCallContractNormalDichotomy multiDiscrBlind :=
  not_mirCallContractNormalDichotomy_of_return_blind fun req _ _ _ _ _ =>
    ⟨fun _ => multiDiscrBlind_post_returned req _ _,
      fun _ => multiDiscrBlind_post_returned req _ _⟩

/-- Return-blind behind nested patterns on the returned value. -/
def nestedPatternBlind : MirCallContract where
  pre _ := True
  post _ ans :=
    match ans with
    | .returned (.scalar _) _ => True
    | .returned (.ptr _ _) _ => True
    | .returned _ _ => True
    | _ => False

theorem nestedPatternBlind_post_returned (req : MirCallReq) (v : Value)
    (m : Memory) : nestedPatternBlind.post req (.returned v m) := by
  cases v <;> trivial

theorem nestedPatternBlind_not_normalDichotomy :
    ¬ MirCallContractNormalDichotomy nestedPatternBlind :=
  not_mirCallContractNormalDichotomy_of_return_blind fun req _ _ _ _ _ =>
    ⟨fun _ => nestedPatternBlind_post_returned req _ _,
      fun _ => nestedPatternBlind_post_returned req _ _⟩

/-- Reflexive equations spread over a two-discriminant `match`. -/
def multiDiscrRefl : MirCallContract where
  pre _ := True
  post req ans :=
    match ans, req.args with
    | .returned v _, [] => v = v
    | .returned _ m, _ :: _ => m = m
    | .panicked _, _ => False
    | .aborted, _ => True

theorem multiDiscrRefl_post_returned (req : MirCallReq) (v : Value) (m : Memory) :
    multiDiscrRefl.post req (.returned v m) := by
  show (match MirCallAns.returned v m, req.args with
    | .returned v _, [] => v = v
    | .returned _ m, _ :: _ => m = m
    | .panicked _, _ => False
    | .aborted, _ => True)
  split <;> first | rfl | simp_all

theorem multiDiscrRefl_not_normalDichotomy :
    ¬ MirCallContractNormalDichotomy multiDiscrRefl :=
  not_mirCallContractNormalDichotomy_of_return_blind fun req _ _ _ _ _ =>
    ⟨fun _ => multiDiscrRefl_post_returned req _ _,
      fun _ => multiDiscrRefl_post_returned req _ _⟩

#expect_vacuous multiDiscrBlind returnBlind
#expect_vacuous nestedPatternBlind returnBlind
#expect_vacuous multiDiscrRefl returnBlind

/-- The same two-discriminant shape with one binding alternative. -/
def multiDiscrGenuine : MirCallContract where
  pre _ := True
  post req ans :=
    match ans, req.args with
    | .returned v _, [x] => v = x
    | .returned _ _, _ => True
    | _, _ => False

theorem multiDiscrGenuine_returnValueDichotomy :
    MirCallContractReturnValueDichotomy multiDiscrGenuine :=
  ⟨{ defPath := "", args := [.unit], memory := emptyMemory }, .unit, .uninit,
    emptyMemory, trivial, rfl, nofun⟩

/-- The same nested-pattern shape with one rejecting alternative. -/
def nestedPatternGenuine : MirCallContract where
  pre _ := True
  post _ ans :=
    match ans with
    | .returned (.scalar _) _ => True
    | .returned _ _ => False
    | _ => False

theorem nestedPatternGenuine_returnValueDichotomy :
    MirCallContractReturnValueDichotomy nestedPatternGenuine :=
  ⟨witnessReq, .scalar ⟨0, 1⟩, .unit, emptyMemory, trivial, trivial, id⟩

#expect_binds multiDiscrGenuine
#expect_binds nestedPatternGenuine

-- Its case tree still scrutinises the input, so the proof search settles it.
vacuous_case pairMatchInput semanticallyInsensitive :=
  fun x r => match x, r with
    | 0, _ => x < 9
    | _ + 1, 0 => x < 7
    | _ + 1, _ + 1 => x < 7
  by intro x r₁ r₂; cases x <;> cases r₁ <;> cases r₂ <;> simp [pairMatchInput]
genuine_case pairMatchGenuine := fun x r => match x, r with
    | 0, _ => True
    | _ + 1, 0 => False
    | _ + 1, _ + 1 => True
  witness 1 1 0 by simp [pairMatchGenuine]

/-! ### Hypotheses that rewrite or contradict -/

/-- An uninterpreted function: only congruence is known of it. -/
opaque opaqueFn : Nat → Nat

vacuous_case congrUnderHyp reflexiveTautology :=
  fun x r => r = x → opaqueFn r = opaqueFn x
  by intro x r₁ r₂; exact ⟨fun _ h => h ▸ rfl, fun _ h => h ▸ rfl⟩
vacuous_case congrUnderIte reflexiveTautology :=
  fun x r => if r = x then opaqueFn r = opaqueFn x else True
  by
    intro x r₁ r₂
    have key : ∀ r, (if r = x then opaqueFn r = opaqueFn x else True) := by
      intro r; split
      · next h => exact h ▸ rfl
      · trivial
    exact ⟨fun _ => key r₂, fun _ => key r₁⟩
genuine_case hypEqGenuine := fun x r => x = 3 → r = x
  witness 3 3 0 by simp [hypEqGenuine]
genuine_case hypEqOutput := fun x r => r = 3 → x = r
  witness 0 0 3 by simp [hypEqOutput]

/-- Premises that contradict each other, over `Value`s (no arithmetic). -/
def contradictoryHypVal (a r : Value) : Prop :=
  (a = .unit ∧ a = .uninit) → r = .unit

theorem contradictoryHypVal_not_dichotomy (pre : Value → Prop) :
    ¬ PostconditionDichotomy pre contradictoryHypVal :=
  not_dichotomy_of_universal_post fun _ _ _ ⟨h₁, h₂⟩ =>
    nomatch h₁.symm.trans h₂

#expect_vacuous contradictoryHypVal semanticallyInsensitive

vacuous_case nonemptyFin semanticallyInsensitive :=
  fun _ r => Nonempty (Fin (r + 1))
  by intro _ r₁ r₂; exact ⟨fun _ => ⟨0⟩, fun _ => ⟨0⟩⟩
vacuous_case nonlinearIdentity semanticallyInsensitive :=
  fun x r => (r + x) * (r + x) = r * r + 2 * r * x + x * x
  by intro x r₁ r₂; simp only [nonlinearIdentity]; constructor <;> intro _ <;> grind

/-! ### Exhaustive constructor disjunctions (case split on the output) -/

def optionExhaustive (_x : Nat) (r : Option Nat) : Prop :=
  r = none ∨ ∃ v, r = some v

theorem optionExhaustive_not_dichotomy (pre : Nat → Prop) :
    ¬ PostconditionDichotomy pre optionExhaustive :=
  not_dichotomy_of_universal_post fun _ r _ => by
    cases r with
    | none => exact .inl rfl
    | some v => exact .inr ⟨v, rfl⟩

def optionGenuine (_x : Nat) (r : Option Nat) : Prop := r = none ∨ r = some 3

theorem optionGenuine_dichotomy :
    PostconditionDichotomy (fun _ => True) optionGenuine :=
  ⟨0, none, some 4, trivial, .inl rfl, fun h => by
    rcases h with h | h <;> cases h⟩

/-- A `Claim` whose `ensures` lists every constructor of `Value`. -/
def valueExhaustiveClaim (body : CapturedMir) : Claim where
  body := body
  pre _ := True
  post _ ret :=
    ret = .unit ∨ ret = .uninit ∨ (∃ s, ret = .scalar s) ∨
      (∃ p n, ret = .ptr p n) ∨ ∃ i fs, ret = .aggregate i fs

theorem valueExhaustiveClaim_not_dichotomy (body : CapturedMir) :
    ¬ ClaimDichotomy (valueExhaustiveClaim body) :=
  not_dichotomy_of_universal_post fun _ ret _ => by
    cases ret with
    | unit => exact .inl rfl
    | uninit => exact .inr (.inl rfl)
    | scalar s => exact .inr (.inr (.inl ⟨s, rfl⟩))
    | ptr p n => exact .inr (.inr (.inr (.inl ⟨p, n, rfl⟩)))
    | aggregate i fs => exact .inr (.inr (.inr (.inr ⟨i, fs, rfl⟩)))

/-- Both Boolean outputs lead to the same input-only condition. -/
def boolSplitVacuous (x : Nat) (r : Bool) : Prop :=
  (r = true ∧ x = 1) ∨ (r = false ∧ x = 1)

theorem boolSplitVacuous_not_dichotomy (pre : Nat → Prop) :
    ¬ PostconditionDichotomy pre boolSplitVacuous :=
  not_dichotomy_of_input_predicate (fun x => x = 1) fun x r _ => by
    cases r <;> simp [boolSplitVacuous]

/-- The two Boolean outputs lead to different conditions: a genuine clause. -/
def boolSplitGenuine (x : Nat) (r : Bool) : Prop :=
  (r = true ∧ x = 1) ∨ (r = false ∧ x = 2)

theorem boolSplitGenuine_dichotomy :
    PostconditionDichotomy (fun _ => True) boolSplitGenuine :=
  ⟨1, true, false, trivial, by simp [boolSplitGenuine],
    by simp [boolSplitGenuine]⟩

#expect_vacuous optionExhaustive reflexiveTautology
#expect_binds optionGenuine
#expect_vacuous valueExhaustiveClaim reflexiveTautology
#expect_vacuous boolSplitVacuous reflexiveTautology
#expect_binds boolSplitGenuine

run_meta do
  -- The case split is syntactic: it does not need the proof search.
  let noProbe : EnsuresCheckConfig := { semanticProbe := false }
  for n in #[``optionExhaustive, ``valueExhaustiveClaim, ``boolSplitVacuous,
      ``multiDiscrBlind, ``nestedPatternBlind, ``multiDiscrRefl,
      ``congrUnderHyp, ``congrUnderIte] do
    assertEnsuresVacuous n (cfg := noProbe)

/-! ### Binding is relative to the precondition -/

def smallPre (x : Nat) : Prop := x < 10

/-- `ensures(x >= 10 ==> ret == 5)`: binding on its own ... -/
def guardedPost (x ret : Nat) : Prop := x ≥ 10 → ret = 5

theorem guardedPost_dichotomy :
    PostconditionDichotomy (fun _ => True) guardedPost :=
  ⟨10, 5, 0, trivial, fun _ => rfl,
    fun h => absurd (h (Nat.le_refl 10)) (by decide)⟩

/-- ... and vacuous under `requires(x < 10)`: its guard is never met. -/
theorem guardedPost_not_dichotomy_under_requires :
    ¬ PostconditionDichotomy smallPre guardedPost :=
  not_dichotomy_of_universal_post fun x _ (hx : x < 10) (h : x ≥ 10) => by
    omega

/-- `ensures(x > 20 && ret == 5)` contradicts `requires(x < 10)`. -/
def contradictedPost (x ret : Nat) : Prop := x > 20 ∧ ret = 5

theorem contradictedPost_not_realizable :
    ¬ ContractRealizable smallPre contradictedPost :=
  not_realizable_of_unsat_post fun x _ (hx : x < 10) (h : x > 20 ∧ _) => by
    omega

/-- The guarded shape on a `Claim`: the `requires` bounds the argument. -/
def guardedClaim (body : CapturedMir) : Claim where
  body := body
  pre args := ∃ a, args = [u32Arg a] ∧ a < 10
  post args ret := ∀ a, args = [u32Arg a] → a ≥ 10 → ret = u32Arg 0

theorem guardedClaim_not_dichotomy (body : CapturedMir) :
    ¬ ClaimDichotomy (guardedClaim body) :=
  not_dichotomy_of_universal_post fun _ _ ⟨a₀, h₀, hlt⟩ a ha hge => by
    have : a₀ = a := u32Single_inj h₀ ha
    omega

/-- The same guard, met by some admissible argument: a genuine `ensures`. -/
def guardedGenuineClaim (body : CapturedMir) : Claim where
  body := body
  pre args := ∃ a, args = [u32Arg a] ∧ a < 10
  post args ret := ∀ a, args = [u32Arg a] → a ≥ 5 → ret = u32Arg 0

theorem guardedGenuineClaim_dichotomy (body : CapturedMir) :
    ClaimDichotomy (guardedGenuineClaim body) :=
  ⟨[u32Arg 7], u32Arg 0, u32Arg 1, ⟨7, rfl, by decide⟩, fun _ _ _ => rfl,
    fun h => absurd (u32Arg_inj (h 7 rfl (by decide))) (by decide)⟩

/-- The guarded shape on a `MirCallContract`. -/
def guardedContract : MirCallContract where
  pre req := ∃ a, req.args = [u32Arg a] ∧ a < 10
  post req ans :=
    match ans with
    | .returned retVal _ => ∀ a, req.args = [u32Arg a] → a ≥ 10 → retVal = u32Arg 0
    | .panicked _ => False
    | .aborted => False

theorem guardedContract_not_normalDichotomy :
    ¬ MirCallContractNormalDichotomy guardedContract :=
  fun ⟨_, _, _, _, _, ⟨a₀, h₀, hlt⟩, _, hbad⟩ =>
    hbad fun a ha hge => by
      have : a₀ = a := u32Single_inj h₀ ha
      omega

/-- The guarded shape on a `StatefulClaim`: the guard needs one argument. -/
def guardedStatefulClaim (body : CapturedMir) : StatefulClaim where
  body := body
  pre args _ := args = []
  post args _ ret mem' := args.length = 1 → (ret = .unit ∧ mem' = emptyMemory)

theorem guardedStatefulClaim_not_dichotomy (body : CapturedMir) :
    ¬ StatefulClaimDichotomy (guardedStatefulClaim body) :=
  not_statefulClaimDichotomy_of_output_blind
    fun args _ _ _ _ _ (h : args = []) => by
      subst h
      exact ⟨fun _ h' => absurd h' (by decide), fun _ h' => absurd h' (by decide)⟩

run_meta do
  assertEnsuresVacuous ``guardedStatefulClaim (some .vacuousUnderRequires)
  -- Judged alone the clause binds; judged against its `requires` it does not.
  assertEnsuresBindsOutput ``guardedPost
  assertEnsuresVacuous ``guardedPost (some .vacuousUnderRequires)
    (preDecl? := some ``smallPre)
  assertEnsuresBindsOutput ``contradictedPost
  assertEnsuresVacuous ``contradictedPost (some .unrealizableUnderRequires)
    (preDecl? := some ``smallPre)
  -- A precondition that leaves the guard reachable does not change the verdict.
  assertEnsuresBindsOutput ``Refinement.incSpec (preDecl? := some ``Refinement.incPre)
  -- Contracts carry their own `requires`.
  assertEnsuresVacuous ``guardedClaim (some .vacuousUnderRequires)
  assertEnsuresVacuous ``guardedContract (some .vacuousUnderRequires)
  assertEnsuresBindsOutput ``guardedClaim (cfg := { useRequires := false })
  assertEnsuresBindsOutput ``guardedContract (cfg := { useRequires := false })
  assertEnsuresBindsOutput ``guardedGenuineClaim
  -- A precondition must be a predicate over leading binders of the postcondition.
  let failed (x : MetaM EnsuresCheckReport) : MetaM Bool := do
    try
      discard x
      return false
    catch _ =>
      return true
  unless ← failed (reportOf ``guardedPost (cfg := {}) |>.bind fun _ =>
      checkDeclEnsuresBindsOutput ``guardedPost (preDecl? := some ``u32Arg)) do
    throwError "a non-predicate precondition was accepted"
  unless ← failed
      (checkDeclEnsuresBindsOutput ``Class3.reflPost
        (preDecl? := some ``Refinement.geSpec)) do
    throwError "a precondition over the output binder was accepted"

/-! ### Boilerplate in disguise (user `ensures` mode) -/

/-- Frame boilerplate behind a vacuous disjunction. -/
def frameOrFalse : MirCallContract where
  pre _ := True
  post req ans :=
    match ans with
    | .returned _ memAfter => callFramePreserved req.memory memAfter ∨ False
    | .panicked _ => False
    | .aborted => True

/-- Frame boilerplate behind a double negation. -/
def frameNotNot : MirCallContract where
  pre _ := True
  post req ans :=
    match ans with
    | .returned _ memAfter => ¬ ¬ callFramePreserved req.memory memAfter
    | .panicked _ => False
    | .aborted => True

/-- Frame boilerplate behind `↔ True`. -/
def frameIffTrue : MirCallContract where
  pre _ := True
  post req ans :=
    match ans with
    | .returned _ memAfter => (callFramePreserved req.memory memAfter ↔ True)
    | .panicked _ => False
    | .aborted => True

/-- Frame boilerplate as a contrapositive. -/
def frameContrapositive : MirCallContract where
  pre _ := True
  post req ans :=
    match ans with
    | .returned _ memAfter => ¬ callFramePreserved req.memory memAfter → False
    | .panicked _ => False
    | .aborted => True

theorem frameOrFalse_not_returnValueDichotomy :
    ¬ MirCallContractReturnValueDichotomy frameOrFalse :=
  not_mirCallContractReturnValueDichotomy_of_value_blind
    fun _ _ _ _ _ => Iff.rfl

theorem frameNotNot_not_returnValueDichotomy :
    ¬ MirCallContractReturnValueDichotomy frameNotNot :=
  not_mirCallContractReturnValueDichotomy_of_value_blind
    fun _ _ _ _ _ => Iff.rfl

theorem frameIffTrue_not_returnValueDichotomy :
    ¬ MirCallContractReturnValueDichotomy frameIffTrue :=
  not_mirCallContractReturnValueDichotomy_of_value_blind
    fun _ _ _ _ _ => Iff.rfl

theorem frameContrapositive_not_returnValueDichotomy :
    ¬ MirCallContractReturnValueDichotomy frameContrapositive :=
  not_mirCallContractReturnValueDichotomy_of_value_blind
    fun _ _ _ _ _ => Iff.rfl

run_meta do
  -- Each says exactly what `frameOnlyMirCallContract` says. A wrapper must not
  -- turn the frame condition into a user constraint, and (as before) a negated
  -- frame condition must not erase a genuine one (`genuineNegBoilerplate`).
  for n in #[``frameOrFalse, ``frameNotNot, ``frameIffTrue,
      ``frameContrapositive] do
    let r ← reportOf n
    unless r.bindsOutput && !r.bindsBeyondBoilerplate do
      throwError "{n}: expected binding by boilerplate only\n{r.describe}"
    expectReason n .boilerplateOnly (cfg := { userEnsuresOnly := true })
    expectReason n .returnValueUnconstrained (cfg := { strictReturnValue := true })
  assertEnsuresBindsOutput ``HardeningB1.genuineNegBoilerplate
    (cfg := { userEnsuresOnly := true, strictReturnValue := true })

/-! ### What an unrealizable call contract does to its caller -/

/-- Under the abort-only trap, no conforming handler ever returns. -/
theorem abortOnlyTrap_handler_never_returns {handler : ExternalCallHandler}
    (h : Class5.abortOnlyTrap.holdsOn handler)
    (tr : List (Trusted.Effect.Event MirClosedEffect)) (v : Value) (m : Memory) :
    ¬ Trusted.ITree.ReachesRet (handler (CheckedAdd.req 1 2)) tr
      (MirCallAns.returned v m) :=
  not_reachesRet_returned_of_holdsOn_of_not_normalRealizable
    Class5.abortOnlyTrap_not_normalRealizable h
    (CheckedAdd.pre_req 1 2 (by decide) (by decide)) tr v m

/-! ### Sequential composition -/

/-- A composite ending in `ensures(true)` binds nothing. -/
theorem seq_then_constTrue_not_dichotomy :
    ¬ PostconditionDichotomy
      (seqPre Refinement.incPre Refinement.incSpec (fun _ => True))
      (seqPost Refinement.incSpec Class2.constTruePost) :=
  not_dichotomy_seq_of_second_outputInsensitive fun _ _ _ _ _ => trivial

/-- `inc ; inc` separates outputs: the first stage is deterministic. -/
theorem seq_inc_inc_dichotomy :
    PostconditionDichotomy
      (seqPre Refinement.incPre Refinement.incSpec Refinement.incPre)
      (seqPost Refinement.incSpec Refinement.incSpec) :=
  dichotomy_seq_of_deterministic_first Refinement.incSpec_deterministic
    ⟨5, 6, 7, 0,
      ⟨Refinement.incPre_five, fun mid (h : mid = 5 + 1) =>
        show mid < 100 by omega⟩,
      rfl, rfl, show ¬ 0 = 6 + 1 by omega⟩

end HardeningA1

/-! ## Adversarial hardening regressions (Pass B2) -/

namespace HardeningB2

/-! ### Part I: Boilerplate cofactoring and sequential composition -/

/--
Frame boilerplate in the antecedent of an implication guarding a genuine return
pin: satisfies `MirCallContractReturnValueDichotomy` and
`DichotomyBeyondPredicate` on `callFramePreserved`. Polarity-only stripping
falsely collapses `callFramePreserved → retVal = 1` to `False → retVal = 1 = True`.
-/
def frameImpGenuine : MirCallContract where
  pre _ := True
  post req ans :=
    match ans with
    | .returned retVal memAfter =>
      callFramePreserved req.memory memAfter → retVal = u32Arg 1
    | .panicked _ => False
    | .aborted => False

theorem frameImpGenuine_returnValueDichotomy :
    MirCallContractReturnValueDichotomy frameImpGenuine :=
  ⟨witnessReq, u32Arg 1, u32Arg 0, emptyMemory, trivial, fun _ => rfl,
    fun h => absurd (u32Arg_inj (h (callFramePreserved_refl _))) (by decide)⟩

theorem frameImpGenuine_dichotomyBeyond_frame :
    DichotomyBeyondPredicate
      (fun req (out : Value × Memory) => callFramePreserved req.memory out.2)
      frameImpGenuine.pre (mirCallNormalPost frameImpGenuine) :=
  (dichotomyBeyondPredicate_iff_cofactors _).mpr <| Or.inl
    ⟨witnessReq, (u32Arg 1, emptyMemory), (u32Arg 0, emptyMemory),
      trivial, callFramePreserved_refl _, callFramePreserved_refl _,
      fun _ => rfl,
      fun h => absurd (u32Arg_inj (h (callFramePreserved_refl _))) (by decide)⟩

section ClassicalBoilerplate

open Classical

/--
Return-deterministic postcondition branching on frame boilerplate: every memory
pins `retVal` to either `1` or `2`, yet polarity-only stripping collapses both
implications to `True`.
-/
def frameIteGenuine : MirCallContract where
  pre _ := True
  post req ans :=
    match ans with
    | .returned retVal memAfter =>
      if callFramePreserved req.memory memAfter then
        retVal = u32Arg 1
      else
        retVal = u32Arg 2
    | .panicked _ => False
    | .aborted => False

theorem frameIteGenuine_returnValueDichotomy :
    MirCallContractReturnValueDichotomy frameIteGenuine :=
  ⟨witnessReq, u32Arg 1, u32Arg 0, emptyMemory, trivial,
    by
      show (if callFramePreserved emptyMemory emptyMemory then u32Arg 1 = u32Arg 1
        else u32Arg 1 = u32Arg 2)
      split
      · rfl
      · exact absurd (callFramePreserved_refl emptyMemory) ‹_›,
    by
      show ¬ (if callFramePreserved emptyMemory emptyMemory then u32Arg 0 = u32Arg 1
        else u32Arg 0 = u32Arg 2)
      split
      · exact fun h => absurd (u32Arg_inj h) (by decide)
      · exact absurd (callFramePreserved_refl emptyMemory) ‹_›⟩

/-- Classical equivalent of `frameImpGenuine` via `¬ (frame ∧ retVal ≠ 1)`. -/
def frameNotAndNotGenuine : MirCallContract where
  pre _ := True
  post req ans :=
    match ans with
    | .returned retVal memAfter =>
      ¬ (callFramePreserved req.memory memAfter ∧ retVal ≠ u32Arg 1)
    | .panicked _ => False
    | .aborted => False

theorem frameNotAndNotGenuine_returnValueDichotomy :
    MirCallContractReturnValueDichotomy frameNotAndNotGenuine :=
  ⟨witnessReq, u32Arg 1, u32Arg 0, emptyMemory, trivial,
    fun ⟨_, hne⟩ => hne rfl,
    fun h => h ⟨callFramePreserved_refl _,
      fun heq => absurd (u32Arg_inj heq) (by decide)⟩⟩

/-- Biconditional coupling frame boilerplate to a genuine return pin. -/
def frameIffGenuine : MirCallContract where
  pre _ := True
  post req ans :=
    match ans with
    | .returned retVal memAfter =>
      callFramePreserved req.memory memAfter ↔ retVal = u32Arg 1
    | .panicked _ => False
    | .aborted => False

theorem frameIffGenuine_returnValueDichotomy :
    MirCallContractReturnValueDichotomy frameIffGenuine :=
  ⟨witnessReq, u32Arg 1, u32Arg 0, emptyMemory, trivial,
    ⟨fun _ => rfl, fun _ => callFramePreserved_refl _⟩,
    fun h => absurd (u32Arg_inj (h.mp (callFramePreserved_refl _))) (by decide)⟩

/-- Data-level `ite` branching on boilerplate while genuinely pinning `retVal`. -/
def dataIteBoilerplateGenuine : MirCallContract where
  pre _ := True
  post req ans :=
    match ans with
    | .returned retVal memAfter =>
      retVal =
        if callFramePreserved req.memory memAfter then u32Arg 1 else u32Arg 2
    | .panicked _ => False
    | .aborted => False

theorem dataIteBoilerplateGenuine_returnValueDichotomy :
    MirCallContractReturnValueDichotomy dataIteBoilerplateGenuine :=
  ⟨witnessReq, u32Arg 1, u32Arg 0, emptyMemory, trivial,
    by
      show u32Arg 1 = if callFramePreserved emptyMemory emptyMemory then u32Arg 1 else u32Arg 2
      split
      · rfl
      · exact absurd (callFramePreserved_refl emptyMemory) ‹_›,
    by
      show u32Arg 0 ≠ if callFramePreserved emptyMemory emptyMemory then u32Arg 1 else u32Arg 2
      split
      · exact fun h => absurd (u32Arg_inj h) (by decide)
      · exact absurd (callFramePreserved_refl emptyMemory) ‹_›⟩

/-- Data-level `ite` encoding pure frame boilerplate with no user constraint. -/
def dataIteBoilerplateOnly : MirCallContract where
  pre _ := True
  post req ans :=
    match ans with
    | .returned _ memAfter =>
      (if callFramePreserved req.memory memAfter then (1 : Nat) else 2) = 1
    | .panicked _ => False
    | .aborted => True

theorem dataIteBoilerplateOnly_not_returnValueDichotomy :
    ¬ MirCallContractReturnValueDichotomy dataIteBoilerplateOnly :=
  not_mirCallContractReturnValueDichotomy_of_value_blind fun _ _ _ _ _ => Iff.rfl

end ClassicalBoilerplate

/--
Pure boilerplate biconditional: polarity-only stripping leaves `↔` untouched,
letting this bypass `userEnsuresOnly`. Cofactoring refutes every assignment.
-/
def boilerplateIffBoilerplate (sidecar : CapturedMir) : MirCallContract where
  pre _ := True
  post req ans :=
    match ans with
    | .returned retVal memAfter =>
      callFramePreserved req.memory memAfter ↔
        retMatchesCalleeReturnTy sidecar retVal
    | .panicked _ => False
    | .aborted => True

theorem boilerplateIffBoilerplate_blind_given_boilerplate (sidecar : CapturedMir)
    (req : MirCallReq) (v₁ v₂ : Value) (m₁ m₂ : Memory)
    (hf : callFramePreserved req.memory m₁ ↔ callFramePreserved req.memory m₂)
    (ht : retMatchesCalleeReturnTy sidecar v₁ ↔
      retMatchesCalleeReturnTy sidecar v₂) :
    (boilerplateIffBoilerplate sidecar).post req (.returned v₁ m₁) ↔
      (boilerplateIffBoilerplate sidecar).post req (.returned v₂ m₂) :=
  ⟨fun h => ⟨fun h₂ => ht.mp (h.mp (hf.mpr h₂)), fun h₂ => hf.mp (h.mpr (ht.mpr h₂))⟩,
    fun h => ⟨fun h₁ => ht.mpr (h.mp (hf.mp h₁)), fun h₁ => hf.mpr (h.mpr (ht.mp h₁))⟩⟩

theorem extSpecDefault_not_dichotomyBeyond_boilerplate (target : DefPath)
    (sidecar : CapturedMir) :
    ¬ DichotomyBeyondPredicate
        (fun req (out : Value × Memory) =>
          callFramePreserved req.memory out.2 ∧
            retMatchesCalleeReturnTy sidecar out.1)
        (Class5.extSpecDefault target sidecar).pre
        (mirCallNormalPost (Class5.extSpecDefault target sidecar)) :=
  not_dichotomyBeyondPredicate_of_boilerplate_only fun _ _ _ _ hiff =>
    ⟨fun ⟨hf, ht, _⟩ => ⟨(hiff.mp ⟨hf, ht⟩).1, (hiff.mp ⟨hf, ht⟩).2, trivial⟩,
      fun ⟨hf, ht, _⟩ => ⟨(hiff.mpr ⟨hf, ht⟩).1, (hiff.mpr ⟨hf, ht⟩).2, trivial⟩⟩

theorem extSpecDefault_bridge (target : DefPath) (sidecar : CapturedMir) :
    ¬ ExternalSpecEnsuresDichotomy target sidecar (fun _ => True)
        (fun _ _ => True) :=
  fun h => extSpecDefault_not_dichotomyBeyond_boilerplate target sidecar
    ((externalSpecEnsuresDichotomy_iff_dichotomyBeyond_boilerplate
      target sidecar (fun _ => True) (fun _ _ => True)).mp h)

/-- Sequential composition into an unsatisfiable second stage is unrealizable. -/
theorem seq_inc_constFalse_not_realizable :
    ¬ ContractRealizable
      (seqPre Refinement.incPre Refinement.incSpec (fun _ => True))
      (seqPost Refinement.incSpec (fun (_ _ : Nat) => False)) :=
  not_realizable_seq_of_second_unrealizable
    (not_realizable_of_unsat_post fun _ _ _ h => h)

/-- `inc ; inc` is deterministic, universally realizable, and pointwise-dichotomous. -/
theorem seq_inc_inc_deterministic :
    ContractDeterministic
      (seqPre Refinement.incPre Refinement.incSpec Refinement.incPre)
      (seqPost Refinement.incSpec Refinement.incSpec) :=
  contractDeterministic_seq Refinement.incSpec_deterministic
    Refinement.incSpec_deterministic

theorem seq_inc_inc_universalRealizable :
    UniversalContractRealizable
      (seqPre Refinement.incPre Refinement.incSpec Refinement.incPre)
      (seqPost Refinement.incSpec Refinement.incSpec) :=
  universalRealizable_seq
    ⟨5, Refinement.incPre_five, fun mid (h : mid = 5 + 1) =>
      show mid < 100 by omega⟩
    ⟨⟨5, Refinement.incPre_five⟩, fun x _ => ⟨x + 1, rfl⟩⟩
    ⟨⟨5, Refinement.incPre_five⟩, fun y _ => ⟨y + 1, rfl⟩⟩

theorem seq_inc_inc_pointwiseDichotomy :
    PointwisePostconditionDichotomy
      (seqPre Refinement.incPre Refinement.incSpec Refinement.incPre)
      (seqPost Refinement.incSpec Refinement.incSpec) :=
  pointwiseDichotomy_seq_of_deterministic_first
    ⟨5, Refinement.incPre_five, fun mid (h : mid = 5 + 1) =>
      show mid < 100 by omega⟩
    ⟨⟨5, Refinement.incPre_five⟩, fun x _ => ⟨x + 1, rfl⟩⟩
    Refinement.incSpec_deterministic
    ⟨⟨5, Refinement.incPre_five⟩, fun y _ =>
      ⟨⟨y + 1, rfl⟩, ⟨y + 2, show ¬ (y + 2 = y + 1) by omega⟩⟩⟩

run_meta do
  let user : EnsuresCheckConfig := { userEnsuresOnly := true }
  let strictUser : EnsuresCheckConfig :=
    { userEnsuresOnly := true, strictReturnValue := true }
  for n in #[``frameImpGenuine, ``frameIteGenuine, ``frameNotAndNotGenuine,
      ``frameIffGenuine, ``dataIteBoilerplateGenuine] do
    let rDef ← reportOf n
    unless rDef.bindsOutput && rDef.bindsBeyondBoilerplate do
      throwError "{n}: expected bindsOutput and bindsBeyondBoilerplate\n{rDef.describe}"
    assertEnsuresBindsOutput n (cfg := user)
    assertEnsuresBindsOutput n (cfg := strictUser)
  for n in #[``dataIteBoilerplateOnly, ``boilerplateIffBoilerplate] do
    let rDef ← reportOf n
    unless rDef.bindsOutput && !rDef.bindsBeyondBoilerplate do
      throwError "{n}: expected binding by boilerplate only\n{rDef.describe}"
    expectReason n .boilerplateOnly (cfg := user)
  expectReason ``dataIteBoilerplateOnly .returnValueUnconstrained
    (cfg := { strictReturnValue := true })

/-! ### Dependent-type soundness in equational rewriting -/

/--
`n = 1` must not blindly substitute `n ↦ 1` into `@Fin.val n v` where `v : Fin n`,
which would corrupt the residual into an ill-typed term.
-/
def depHypEq2 (n : Nat) (v : Fin n) (r : Nat) : Prop :=
  n = 1 → r = v.val

theorem depHypEq2_dichotomy :
    PostconditionDichotomy (fun (_ : (n : Nat) × Fin n) => True)
      (fun p r => depHypEq2 p.1 p.2 r) :=
  ⟨⟨1, ⟨0, by decide⟩⟩, 0, 1, trivial, fun _ => rfl,
    fun h => absurd (h rfl) (by decide)⟩

def depHypVacuous (n : Nat) (_v : Fin n) (r : Nat) : Prop :=
  n = 1 → r = r

theorem depHypVacuous_not_dichotomy (pre : (n : Nat) × Fin n → Prop) :
    ¬ PostconditionDichotomy pre (fun p r => depHypVacuous p.1 p.2 r) :=
  not_dichotomy_of_universal_post fun _ _ _ _ => rfl

def depPre1 (n : Nat) (_v : Fin n) : Prop := n = 1
def depPostVal (n : Nat) (v : Fin n) (r : Nat) : Prop := r = v.val

theorem depPostVal_dichotomy :
    PostconditionDichotomy (fun p : (n : Nat) × Fin n => depPre1 p.1 p.2)
      (fun p r => depPostVal p.1 p.2 r) :=
  ⟨⟨1, ⟨0, by decide⟩⟩, 0, 1, rfl, rfl, show ¬ (1 = 0) by decide⟩

#expect_binds depHypEq2
#expect_vacuous depHypVacuous reflexiveTautology

run_meta do
  -- Directly verify that `simpProp` keeps `depHypEq2` kernel-well-typed.
  withLocalDeclD `n (mkConst ``Nat) fun n =>
  withLocalDeclD `v (mkApp (mkConst ``Fin) n) fun v =>
  withLocalDeclD `r (mkConst ``Nat) fun r => do
    let body := mkApp3 (mkConst ``depHypEq2) n v r
    let ctx : EnsuresCheck.Context :=
      { cfg := {}, outputs := #[r.fvarId!], stripBoilerplate := false }
    let (res, _) ← ((EnsuresCheck.simpProp body).run ctx).run {}
    check res
  -- Rewriting under `requires` must likewise stay well-typed on dependent inputs.
  assertEnsuresBindsOutput ``depPostVal (preDecl? := some ``depPre1)

/-! ### `requires` consistency, `preRefuted` invariant, and existential contracts -/

def unsatPreVal (a : Value) : Prop := a = .unit ∧ a = .uninit
def unsatPreNonlin (x : Nat) : Prop := x * x + 1 = 0

theorem unsatPreVal_not_satisfiable : ¬ PreconditionSatisfiable unsatPreVal :=
  fun ⟨_, h₁, h₂⟩ => nomatch h₁.symm.trans h₂

theorem unsatPreNonlin_not_satisfiable :
    ¬ PreconditionSatisfiable unsatPreNonlin :=
  fun ⟨_, h⟩ => Nat.succ_ne_zero _ h

def unsatPreContract : MirCallContract where
  pre req := req.args = [.unit] ∧ req.args = [.uninit]
  post _ ans :=
    match ans with
    | .returned r _ => r = .unit
    | .panicked _ => False
    | .aborted => False

theorem unsatPreContract_not_preSatisfiable :
    ¬ MirCallContractPreSatisfiable unsatPreContract :=
  fun ⟨_, h₁, h₂⟩ => nomatch h₁.symm.trans h₂

def unsatDisjExistsContract : MirCallContract where
  pre req :=
    (∃ a, req.args = [u32Arg a] ∧ a < 5 ∧ a > 10) ∨
      (∃ b, req.args = [u32Arg b] ∧ b < 2 ∧ b > 8)
  post _ ans :=
    match ans with
    | .returned retVal _ => retVal = u32Arg 0
    | .panicked _ => False
    | .aborted => False

theorem unsatDisjExistsContract_not_preSatisfiable :
    ¬ MirCallContractPreSatisfiable unsatDisjExistsContract := by
  rintro ⟨_, ⟨a, _, h₁, h₂⟩ | ⟨b, _, h₁, h₂⟩⟩ <;> omega

def unsatPreWithGenuinePost : MirCallContract where
  pre _ := False
  post _ ans :=
    match ans with
    | .returned r _ => r = u32Arg 1
    | .panicked _ => False
    | .aborted => False

def emptyInputPost (_ : Empty) (r : Nat) : Prop := r = 0

theorem emptyInputPost_not_dichotomy :
    ¬ PostconditionDichotomy HardeningB1.emptyDomainPre emptyInputPost :=
  fun ⟨e, _, _, _, _, _⟩ => e.elim

def zeroPre (x : Nat) : Prop := x = 0

/-- Exhaustive 5-constructor `Value` disjunction hidden behind `x = 0` from `requires`. -/
def valueExhaustiveUnderPre (x : Nat) (r : Value) : Prop :=
  r = .unit ∨ r = .uninit ∨ (∃ s, r = .scalar s) ∨
    (∃ p n, r = .ptr p n) ∨ (∃ i fs, r = .aggregate i fs ∧ x = 0)

theorem valueExhaustiveUnderPre_not_dichotomy :
    ¬ PostconditionDichotomy zeroPre valueExhaustiveUnderPre :=
  not_dichotomy_of_universal_post fun _ r hx => by
    cases r with
    | unit => exact .inl rfl
    | uninit => exact .inr (.inl rfl)
    | scalar s => exact .inr (.inr (.inl ⟨s, rfl⟩))
    | ptr p n => exact .inr (.inr (.inr (.inl ⟨p, n, rfl⟩)))
    | aggregate i fs => exact .inr (.inr (.inr (.inr ⟨i, fs, rfl, hx⟩)))

/-- Existential MIR contract whose `ensures` guard is dead under `requires`. -/
def vacuousExistsContract : MirCallContract where
  pre req := ∃ a, req.args = [u32Arg a] ∧ a < 10
  post req ans :=
    match ans with
    | .returned retVal _ =>
      ∃ a, req.args = [u32Arg a] ∧ (a ≥ 10 → retVal = u32Arg 0)
    | .panicked _ => False
    | .aborted => False

theorem vacuousExistsContract_not_normalDichotomy :
    ¬ MirCallContractNormalDichotomy vacuousExistsContract :=
  not_mirCallContractNormalDichotomy_of_return_blind
    fun _ _ _ _ _ ⟨a, ha, hlt⟩ =>
      ⟨fun _ => ⟨a, ha, fun hge => absurd hge (by omega)⟩,
        fun _ => ⟨a, ha, fun hge => absurd hge (by omega)⟩⟩

/-- Existential MIR contract whose `ensures` contradicts `requires`. -/
def contradictedExistsContract : MirCallContract where
  pre req := ∃ a, req.args = [u32Arg a] ∧ a < 10
  post req ans :=
    match ans with
    | .returned retVal _ =>
      ∃ a, req.args = [u32Arg a] ∧ a ≥ 10 ∧ retVal = u32Arg 0
    | .panicked _ => False
    | .aborted => False

theorem contradictedExistsContract_not_normalRealizable :
    ¬ MirCallContractNormalRealizable contradictedExistsContract := by
  rintro ⟨_, _, _, ⟨a, ha, hlt⟩, a', ha', hge, _⟩
  have := u32Single_inj ha ha'
  omega

/-- Slice-metadata existential MIR contract whose guard is dead when `len = 0`. -/
def sliceVacuousExistsContract : MirCallContract where
  pre req := ∃ ptr sz len, req.args = [sliceArg ptr sz len] ∧ len = 0
  post req ans :=
    match ans with
    | .returned retVal _ =>
      ∃ ptr sz len, req.args = [sliceArg ptr sz len] ∧
        (len > 0 → retVal = u32Arg 0)
    | .panicked _ => False
    | .aborted => False

theorem sliceVacuousExistsContract_not_normalDichotomy :
    ¬ MirCallContractNormalDichotomy sliceVacuousExistsContract :=
  not_mirCallContractNormalDichotomy_of_return_blind
    fun _ _ _ _ _ ⟨ptr, sz, len, ha, h0⟩ =>
      ⟨fun _ => ⟨ptr, sz, len, ha, fun hgt => absurd hgt (by omega)⟩,
        fun _ => ⟨ptr, sz, len, ha, fun hgt => absurd hgt (by omega)⟩⟩

/-- Length precondition contradicting an empty-list guard. -/
def lenPreContract : MirCallContract where
  pre req := req.args.length = 1
  post req ans :=
    match ans with
    | .returned retVal _ => req.args = [] → retVal = u32Arg 0
    | .panicked _ => False
    | .aborted => False

theorem lenPreContract_not_normalDichotomy :
    ¬ MirCallContractNormalDichotomy lenPreContract :=
  not_mirCallContractNormalDichotomy_of_return_blind
    fun _ _ _ _ _ hlen =>
      ⟨fun _ hnil => by simp [lenPreContract, hnil] at hlen,
        fun _ hnil => by simp [lenPreContract, hnil] at hlen⟩

#expect_vacuous unsatPreContract requiresUnsatisfiable
#expect_vacuous unsatDisjExistsContract requiresUnsatisfiable
#expect_vacuous unsatPreWithGenuinePost requiresUnsatisfiable
#expect_vacuous vacuousExistsContract vacuousUnderRequires
#expect_vacuous contradictedExistsContract unrealizableUnderRequires
#expect_vacuous sliceVacuousExistsContract vacuousUnderRequires
#expect_vacuous lenPreContract vacuousUnderRequires

run_meta do
  -- `checkRequiresSatisfiable` and `checkEnsuresBindsOutput` agree on deep
  -- constructor and nonlinear refutations.
  for n in #[``unsatPreVal, ``unsatPreNonlin, ``unsatPreContract,
      ``unsatDisjExistsContract] do
    assertRequiresRefuted n
  -- When `requiresUnsatisfiable` fires, `boundOutputIdxs` is empty and
  -- `bindsBeyondBoilerplate` must be `false`.
  for n in #[``unsatPreContract, ``unsatDisjExistsContract,
      ``unsatPreWithGenuinePost, ``Class1.contradictoryClaim] do
    let r ← reportOf n
    unless r.reason? == some .requiresUnsatisfiable &&
        r.boundOutputIdxs.isEmpty && !r.bindsBeyondBoilerplate do
      throwError "{n}: inconsistent requiresUnsatisfiable report\n{r.describe}"
  -- Empty input domain is also flagged as `requiresUnsatisfiable`.
  let rEmp ← checkDeclEnsuresBindsOutput ``emptyInputPost
    (preDecl? := some ``HardeningB1.emptyDomainPre)
  unless rEmp.reason? == some .requiresUnsatisfiable &&
      !rEmp.bindsBeyondBoilerplate do
    throwError "emptyInputPost: unexpected report\n{rEmp.describe}"
  -- `caseSplitOutput` re-runs on the precondition-rewritten residual.
  assertEnsuresVacuous ``valueExhaustiveUnderPre (some .vacuousUnderRequires)
    (preDecl? := some ``zeroPre)
  -- Without `requires`, `valueExhaustiveUnderPre` binds (`x` could be nonzero).
  assertEnsuresBindsOutput ``valueExhaustiveUnderPre

/-! ### Disjunctive congruence, existential witnesses, and multi-conjunct unsat -/

vacuous_case disjCongr reflexiveTautology :=
  fun x r => r ≠ x ∨ HardeningA1.opaqueFn r = HardeningA1.opaqueFn x
  by
    intro x r₁ r₂
    have key : ∀ r, r ≠ x ∨ HardeningA1.opaqueFn r = HardeningA1.opaqueFn x :=
      fun r => if h : r = x then .inr (h ▸ rfl) else .inl h
    exact ⟨fun _ => key r₂, fun _ => key r₁⟩

vacuous_case disjCongrAndInput reflexiveTautology :=
  fun x r => (r ≠ x ∨ HardeningA1.opaqueFn r = HardeningA1.opaqueFn x) ∧ x > 0
  by
    intro x r₁ r₂
    have key : ∀ r, r ≠ x ∨ HardeningA1.opaqueFn r = HardeningA1.opaqueFn x :=
      fun r => if h : r = x then .inr (h ▸ rfl) else .inl h
    exact ⟨fun ⟨_, hx⟩ => ⟨key r₂, hx⟩, fun ⟨_, hx⟩ => ⟨key r₁, hx⟩⟩

/--
Non-vacuous twin of disjunctive congruence: `r ≠ x ∨ r ≠ y` rejects `r = 0`
when `x = y = 0`. Guards against circular simultaneous substitution in `Or`.
-/
def disjNonVacuous (x y r : Nat) : Prop := r ≠ x ∨ r ≠ y

theorem disjNonVacuous_dichotomy :
    PostconditionDichotomy (fun _ : Nat × Nat => True)
      (fun p r => disjNonVacuous p.1 p.2 r) :=
  ⟨(0, 0), 1, 0, trivial, .inl (by decide), fun h => h.elim (· rfl) (· rfl)⟩

vacuous_case existsParity semanticallyInsensitive :=
  fun _ r => ∃ y : Nat, r = 2 * y ∨ r = 2 * y + 1
  by
    intro _ r₁ r₂
    exact ⟨fun _ => ⟨r₂ / 2, by omega⟩, fun _ => ⟨r₁ / 2, by omega⟩⟩

vacuous_case existsSumNat semanticallyInsensitive :=
  fun _ r => ∃ a b : Nat, a + b = r
  by
    intro _ r₁ r₂
    exact ⟨fun _ => ⟨0, r₂, by omega⟩, fun _ => ⟨0, r₁, by omega⟩⟩

vacuous_case existsListLen semanticallyInsensitive :=
  fun _ r => ∃ l : List Nat, l.length = r
  by
    intro _ r₁ r₂
    exact ⟨fun _ => ⟨List.replicate r₂ 0, by simp⟩,
      fun _ => ⟨List.replicate r₁ 0, by simp⟩⟩

vacuous_case multiConjUnsat unsatisfiable :=
  fun _ r => r = 0 ∧ r = 1
  by intro _ r₁ r₂; exact ⟨fun ⟨h₁, h₂⟩ => by omega, fun ⟨h₁, h₂⟩ => by omega⟩

def multiConjValUnsat (_x : Nat) (r : Value) : Prop := r = .unit ∧ r = .uninit

theorem multiConjValUnsat_not_dichotomy (pre : Nat → Prop) :
    ¬ PostconditionDichotomy pre multiConjValUnsat :=
  not_dichotomy_of_unsat_post fun _ _ _ ⟨h₁, h₂⟩ => nomatch h₁.symm.trans h₂

#expect_binds disjNonVacuous
#expect_vacuous multiConjValUnsat unsatisfiable

run_meta do
  let noProbe : EnsuresCheckConfig := { semanticProbe := false }
  -- Classical disjunctive congruence is syntactic: needs no proof search.
  assertEnsuresVacuous ``disjCongr (some .reflexiveTautology) (cfg := noProbe)
  assertEnsuresVacuous ``disjCongrAndInput (some .reflexiveTautology) (cfg := noProbe)
  assertEnsuresBindsOutput ``disjNonVacuous (cfg := noProbe)

end HardeningB2

/-! ## Hardening (pass A2): exhaustive cofactors, inhabitants, and witnesses -/

namespace HardeningA2

/-! ### Part I: dichotomy modulo an observation -/

/-- The parity of the output, as an observation. -/
def parityObs (_ : Nat) (r : Nat) : Nat := r % 2

/-- `r = x` separates two outputs of the same parity. -/
theorem eq_dichotomyModuloParity :
    DichotomyModuloObservation parityObs (fun _ => True) (fun x r => r = x) :=
  ⟨0, 0, 2, trivial, rfl, rfl, (by decide : ¬ (2 : Nat) = 0)⟩

/-- The fibre form: both witnesses lie over one observed value. -/
theorem eq_dichotomy_on_a_parity_fibre :
    ∃ b x ok bad, True ∧ parityObs x ok = b ∧ parityObs x bad = b ∧
      ok = x ∧ ¬ bad = x :=
  (dichotomyModuloObservation_iff_fibres parityObs).mp eq_dichotomyModuloParity

/-- "The output is even" has a dichotomy, but none modulo parity. -/
theorem even_dichotomy :
    PostconditionDichotomy (fun (_ : Nat) => True) (fun _ r => r % 2 = 0) :=
  ⟨0, 0, 1, trivial, rfl, (by decide : ¬ (1 % 2 = 0))⟩

theorem even_not_dichotomyModuloParity :
    ¬ DichotomyModuloObservation parityObs (fun _ => True)
      (fun _ r => r % 2 = 0) :=
  not_dichotomyModuloObservation_of_factors (fun _ b => b = 0)
    fun _ _ _ => Iff.rfl

/-- The same fact through the cofactors: each fibre's cofactor is constant. -/
theorem even_not_dichotomyModuloParity_by_cofactors :
    ¬ DichotomyModuloObservation parityObs (fun _ => True)
      (fun _ r => r % 2 = 0) :=
  not_dichotomyModuloObservation_of_cofactors_insensitive
    (fun b _ _ => b = 0) (fun _ _ _ => Iff.rfl) (fun _ _ _ _ _ h => h)

/-- Coarsening parity to evenness, then back to the one-predicate notion. -/
theorem eq_dichotomyBeyond_even :
    DichotomyBeyondPredicate (fun (_ : Nat) r => r % 2 = 0) (fun _ => True)
      (fun x r => r = x) :=
  (dichotomyBeyondPredicate_iff_moduloObservation _).mpr
    (eq_dichotomyModuloParity.of_coarser
      fun _ o₁ o₂ (h : o₁ % 2 = o₂ % 2) => by
        show (o₁ % 2 = 0) = (o₂ % 2 = 0)
        rw [h])

/-- A constant observation is no observation. -/
theorem eq_dichotomyModuloConst :
    DichotomyModuloObservation (fun (_ _ : Nat) => ()) (fun _ => True)
      (fun x r => r = x) :=
  (dichotomyModuloObservation_const_iff ()).mpr
    eq_dichotomyModuloParity.toPostconditionDichotomy

/-- An observation that determines the output leaves nothing to bind. -/
theorem eq_not_dichotomyModuloSucc :
    ¬ DichotomyModuloObservation (fun (_ r : Nat) => r + 1) (fun _ => True)
      (fun x r => r = x) :=
  not_dichotomyModuloObservation_of_injective fun _ _ _ h => Nat.succ.inj h

/-- The exact negation, used as a rewriting rule. -/
theorem even_determined_by_parity (x r₁ r₂ : Nat) (h : r₁ % 2 = r₂ % 2)
    (h₁ : r₁ % 2 = 0) : r₂ % 2 = 0 :=
  (not_dichotomyModuloObservation_iff parityObs).mp
    even_not_dichotomyModuloParity x r₁ r₂ trivial h h₁

/-! ### Cofactoring is exhaustive: the binding assignment may be any of `2 ^ k` -/

/-- A memory whose protector stack is not the empty memory's. -/
def protectedMemory : Memory := { emptyMemory with activeProtectors := [7] }

/-- A memory with yet another protector stack. -/
def otherProtectedMemory : Memory :=
  { emptyMemory with activeProtectors := [8] }

/-- A request issued in `protectedMemory`. -/
def protectedReq : MirCallReq :=
  { defPath := "", args := .nil, memory := protectedMemory }

theorem not_frame_empty_protected :
    ¬ callFramePreserved emptyMemory protectedMemory :=
  fun h => List.cons_ne_nil 7 [] h.2.2.2.1

theorem not_frame_protected_empty :
    ¬ callFramePreserved protectedMemory emptyMemory :=
  fun h => List.cons_ne_nil 7 [] h.2.2.2.1.symm

theorem not_frame_protected_other :
    ¬ callFramePreserved protectedMemory otherProtectedMemory :=
  fun h => absurd (List.cons.inj h.2.2.2.1).1 (by decide)

theorem not_frame_empty_other :
    ¬ callFramePreserved emptyMemory otherProtectedMemory :=
  fun h => List.cons_ne_nil 8 [] h.2.2.2.1

/--
The five frame atoms of `fiveAtomGuard` and `fiveAtomBoilerplate`, as the
observation the checker fixes when it cofactors them.
-/
def fiveFrameObs (req : MirCallReq) (out : Value × Memory) :
    Prop × Prop × Prop × Prop × Prop :=
  (callFramePreserved req.memory out.2, callFramePreserved out.2 req.memory,
    callFramePreserved emptyMemory out.2, callFramePreserved out.2 emptyMemory,
    callFramePreserved out.2 out.2)

/--
Five boilerplate atoms, with the user constraint guarded by the *mixed* truth
assignment `(true, true, false, false, true)`. Sampling the all-true, the
all-false, and the single-flip assignments never reaches it; only an
exhaustive enumeration does.
-/
def fiveAtomGuard : MirCallContract where
  pre _ := True
  post req ans :=
    match ans with
    | .returned retVal memAfter =>
      (callFramePreserved req.memory memAfter ∧
        callFramePreserved memAfter req.memory ∧
        ¬ callFramePreserved emptyMemory memAfter ∧
        ¬ callFramePreserved memAfter emptyMemory ∧
        callFramePreserved memAfter memAfter) → retVal = u32Arg 1
    | .panicked _ => False
    | .aborted => False

theorem fiveAtomGuard_returnValueDichotomy :
    MirCallContractReturnValueDichotomy fiveAtomGuard :=
  ⟨protectedReq, u32Arg 1, u32Arg 2, protectedMemory, trivial, fun _ => rfl,
    fun h => absurd
      (u32Arg_inj (h ⟨callFramePreserved_refl _, callFramePreserved_refl _,
        not_frame_empty_protected, not_frame_protected_empty,
        callFramePreserved_refl _⟩))
      (by decide)⟩

/--
The guard binds beyond its own five atoms: the two returns share the memory,
and the atoms are functions of the memory.
-/
theorem fiveAtomGuard_dichotomyModuloItsAtoms :
    DichotomyModuloObservation fiveFrameObs fiveAtomGuard.pre
      (mirCallNormalPost fiveAtomGuard) :=
  (mirCallContractReturnValueDichotomy_iff_moduloMemory.mp
    fiveAtomGuard_returnValueDichotomy).of_coarser
    fun req o₁ o₂ (h : o₁.2 = o₂.2) => by
      show fiveFrameObs req o₁ = fiveFrameObs req o₂
      simp only [fiveFrameObs, h]

/-- The dichotomy sits in the cofactor of exactly one assignment. -/
theorem fiveAtomGuard_cofactor :
    ∃ b req ok bad, fiveAtomGuard.pre req ∧
      fiveFrameObs req ok = b ∧ fiveFrameObs req bad = b ∧
      ((b.1 ∧ b.2.1 ∧ ¬ b.2.2.1 ∧ ¬ b.2.2.2.1 ∧ b.2.2.2.2) →
        ok.1 = u32Arg 1) ∧
      ¬ ((b.1 ∧ b.2.1 ∧ ¬ b.2.2.1 ∧ ¬ b.2.2.2.1 ∧ b.2.2.2.2) →
        bad.1 = u32Arg 1) :=
  fiveAtomGuard_dichotomyModuloItsAtoms.exists_cofactor_dichotomy
    (fun (b : Prop × Prop × Prop × Prop × Prop) (_ : MirCallReq)
        (out : Value × Memory) =>
      (b.1 ∧ b.2.1 ∧ ¬ b.2.2.1 ∧ ¬ b.2.2.2.1 ∧ b.2.2.2.2) →
        out.1 = u32Arg 1)
    fun _ _ _ => Iff.rfl

/--
Pure boilerplate over the same five atoms (the last disjunct is refuted once
the frame is unfolded, so the full analysis still sees a frame constraint).
-/
def fiveAtomBoilerplate : MirCallContract where
  pre _ := True
  post req ans :=
    match ans with
    | .returned _ memAfter =>
      (callFramePreserved req.memory memAfter ∧
          callFramePreserved memAfter req.memory) ∨
        (¬ callFramePreserved emptyMemory memAfter ∧
          callFramePreserved memAfter emptyMemory) ∨
        ¬ callFramePreserved memAfter memAfter
    | .panicked _ => False
    | .aborted => True

/-- Every one of its 32 cofactors is output-free: no dichotomy modulo the atoms. -/
theorem fiveAtomBoilerplate_not_dichotomyModuloItsAtoms :
    ¬ DichotomyModuloObservation fiveFrameObs fiveAtomBoilerplate.pre
      (mirCallNormalPost fiveAtomBoilerplate) :=
  not_dichotomyModuloObservation_of_cofactors_insensitive
    (fun b _ _ => (b.1 ∧ b.2.1) ∨ (¬ b.2.2.1 ∧ b.2.2.2.1) ∨ ¬ b.2.2.2.2)
    (fun _ _ _ => Iff.rfl) (fun _ _ _ _ _ h => h)

theorem fiveAtomBoilerplate_not_returnValueDichotomy :
    ¬ MirCallContractReturnValueDichotomy fiveAtomBoilerplate :=
  not_mirCallContractReturnValueDichotomy_of_value_blind
    fun _ _ _ _ _ => Iff.rfl

/--
Nine distinct boilerplate atoms and nothing else. Past `maxCofactorAtoms` the
checker does not enumerate; it reports the conservative *binds* together with
a note, although the contract is value-blind (a completeness limit, never a
false positive).
-/
def nineAtomBoilerplate : MirCallContract where
  pre _ := True
  post req ans :=
    match ans with
    | .returned _ memAfter =>
      (callFramePreserved req.memory memAfter ∧
          callFramePreserved memAfter req.memory) ∨
        (¬ callFramePreserved emptyMemory memAfter ∧
          callFramePreserved memAfter emptyMemory) ∨
        (callFramePreserved memAfter memAfter ∧
          ¬ callFramePreserved req.memory req.memory) ∨
        (callFramePreserved emptyMemory req.memory ∧
          ¬ callFramePreserved req.memory emptyMemory) ∨
        ¬ callFramePreserved emptyMemory emptyMemory
    | .panicked _ => False
    | .aborted => True

theorem nineAtomBoilerplate_not_returnValueDichotomy :
    ¬ MirCallContractReturnValueDichotomy nineAtomBoilerplate :=
  not_mirCallContractReturnValueDichotomy_of_value_blind
    fun _ _ _ _ _ => Iff.rfl

/-! ### Boilerplate predicates at other arguments, and under binders -/

/-- Two rejected frames are observed alike by the frame and return-type pair. -/
theorem protected_obs_eq (sidecar : CapturedMir) (v : Value) :
    externalSpecBoilerplateObs sidecar protectedReq (v, emptyMemory) =
      externalSpecBoilerplateObs sidecar protectedReq
        (v, otherProtectedMemory) :=
  congrArg (fun p => (p, retMatchesCalleeReturnTy sidecar v))
    (propext ⟨fun h => absurd h not_frame_protected_empty,
      fun h => absurd h not_frame_protected_other⟩)

/--
A boilerplate predicate applied to a *bound* memory. The clause says that the
protector stack is empty after the call, which the frame of the request does
not determine; the bound atom is not an observation of the output, and treating
it as one (cofactoring it to `True`/`False`) would report `boilerplateOnly`.
-/
def quantifiedFrame : MirCallContract where
  pre _ := True
  post _ ans :=
    match ans with
    | .returned _ memAfter =>
      ∀ m' : Memory, callFramePreserved m' memAfter → m'.activeProtectors = []
    | .panicked _ => False
    | .aborted => False

theorem quantifiedFrame_iff (m : Memory) :
    (∀ m' : Memory, callFramePreserved m' m → m'.activeProtectors = []) ↔
      m.activeProtectors = [] :=
  ⟨fun h => h m (callFramePreserved_refl m),
    fun h _ hf => hf.2.2.2.1.symm.trans h⟩

theorem quantifiedFrame_dichotomyModuloBoilerplate (sidecar : CapturedMir) :
    DichotomyModuloObservation (externalSpecBoilerplateObs sidecar)
      quantifiedFrame.pre (mirCallNormalPost quantifiedFrame) :=
  ⟨protectedReq, (Value.unit, emptyMemory), (Value.unit, otherProtectedMemory),
    trivial, protected_obs_eq sidecar Value.unit,
    (quantifiedFrame_iff emptyMemory).mpr rfl,
    fun h => List.cons_ne_nil 8 [] ((quantifiedFrame_iff _).mp h)⟩

/--
A frame predicate at *other* arguments than the contract's own. By convention
every closed application of a boilerplate predicate is an observation, so the
checker reports `boilerplateOnly`: there is no dichotomy modulo that atom
(`otherFrameInstance_not_dichotomyModuloItsAtom`). The convention is visible,
not hidden: relative to the canonical frame-and-return-type observation the
clause does separate two memories
(`otherFrameInstance_dichotomyModuloBoilerplate`), and the default mode reports
that it binds `memAfter`.
-/
def otherFrameInstance : MirCallContract where
  pre _ := True
  post _ ans :=
    match ans with
    | .returned _ memAfter => callFramePreserved emptyMemory memAfter
    | .panicked _ => False
    | .aborted => False

theorem otherFrameInstance_not_dichotomyModuloItsAtom :
    ¬ DichotomyModuloObservation
      (fun (_ : MirCallReq) (out : Value × Memory) =>
        callFramePreserved emptyMemory out.2)
      otherFrameInstance.pre (mirCallNormalPost otherFrameInstance) :=
  not_dichotomyModuloObservation_of_factors (fun _ b => b) fun _ _ _ => Iff.rfl

theorem otherFrameInstance_dichotomyModuloBoilerplate (sidecar : CapturedMir) :
    DichotomyModuloObservation (externalSpecBoilerplateObs sidecar)
      otherFrameInstance.pre (mirCallNormalPost otherFrameInstance) :=
  ⟨protectedReq, (Value.unit, emptyMemory), (Value.unit, otherProtectedMemory),
    trivial, protected_obs_eq sidecar Value.unit,
    callFramePreserved_refl emptyMemory, not_frame_empty_other⟩

/-- The frame-only contract binds nothing modulo the canonical observation. -/
theorem frameOnly_not_dichotomyModuloBoilerplate (sidecar : CapturedMir) :
    ¬ DichotomyModuloObservation (externalSpecBoilerplateObs sidecar)
      frameOnlyMirCallContract.pre
      (mirCallNormalPost frameOnlyMirCallContract) :=
  frameOnlyMirCallContract_not_dichotomyModuloBoilerplate sidecar

/-- `ensures(true)` on an external spec, through the pair observation. -/
theorem extSpecDefault_not_dichotomyModuloBoilerplate (target : DefPath)
    (sidecar : CapturedMir) :
    ¬ DichotomyModuloObservation (externalSpecBoilerplateObs sidecar)
      (Class5.extSpecDefault target sidecar).pre
      (mirCallNormalPost (Class5.extSpecDefault target sidecar)) :=
  fun h => not_externalSpecEnsuresDichotomy_default target sidecar
    (fun _ => True)
    ((externalSpecEnsuresDichotomy_iff_moduloObservation target sidecar
      (fun _ => True) (fun _ _ => True)).mpr h)

run_meta do
  let user : EnsuresCheckConfig := { userEnsuresOnly := true }
  let strictUser : EnsuresCheckConfig :=
    { userEnsuresOnly := true, strictReturnValue := true }
  -- The guard is one mixed assignment out of 32; it must be found.
  let r ← reportOf ``fiveAtomGuard
  unless r.bindsOutput && r.bindsBeyondBoilerplate do
    throwError "fiveAtomGuard: expected binding beyond boilerplate\n{r.describe}"
  assertEnsuresBindsOutput ``fiveAtomGuard (cfg := user)
  assertEnsuresBindsOutput ``fiveAtomGuard (cfg := strictUser)
  -- Five atoms of pure boilerplate are still recognised as such.
  let r ← reportOf ``fiveAtomBoilerplate
  unless r.bindsOutput && !r.bindsBeyondBoilerplate do
    throwError "fiveAtomBoilerplate: expected boilerplate-only binding\n\
      {r.describe}"
  expectReason ``fiveAtomBoilerplate .boilerplateOnly (cfg := user)
  expectReason ``fiveAtomBoilerplate .returnValueUnconstrained
    (cfg := { strictReturnValue := true })
  -- Past the enumeration bound the verdict is conservative, and says so.
  let r ← reportOf ``nineAtomBoilerplate (cfg := user)
  unless r.bindsOutput && r.bindsBeyondBoilerplate &&
      r.notes.any (fun n => (n.splitOn "cofactoring abandoned").length > 1) do
    throwError "nineAtomBoilerplate: expected a conservative verdict with a \
      note\n{r.describe}"
  expectReason ``nineAtomBoilerplate .returnValueUnconstrained
    (cfg := strictUser)
  -- A boilerplate predicate at a bound argument is not cofactored away.
  let r ← reportOf ``quantifiedFrame
  unless r.bindsOutput && r.bindsBeyondBoilerplate do
    throwError "quantifiedFrame: expected binding beyond boilerplate\n\
      {r.describe}"
  assertEnsuresBindsOutput ``quantifiedFrame (cfg := user)
  -- The stated convention for closed atoms at other arguments.
  let r ← reportOf ``otherFrameInstance
  unless r.bindsOutput && !r.bindsBeyondBoilerplate do
    throwError "otherFrameInstance: expected boilerplate-only binding\n\
      {r.describe}"
  expectReason ``otherFrameInstance .boilerplateOnly (cfg := user)
  expectReason ``frameOnlyMirCallContract .boilerplateOnly (cfg := user)

/-! ### Output types with a single inhabitant in disguise -/

/-- `Option Empty` is inhabited by `none` alone. -/
def optionEmptyNone : Nat → Option Empty → Prop := fun _ r => r = none

theorem optionEmptyNone_not_dichotomy (pre : Nat → Prop) :
    ¬ PostconditionDichotomy pre optionEmptyNone :=
  not_dichotomy_of_const_true fun _ r _ =>
    match r with
    | none => rfl
    | some e => nomatch e

/-- `List Empty` is inhabited by `[]` alone. -/
def listEmptyNil : Nat → List Empty → Prop := fun _ r => r = []

theorem listEmptyNil_not_dichotomy (pre : Nat → Prop) :
    ¬ PostconditionDichotomy pre listEmptyNil :=
  not_dichotomy_of_const_true fun _ r _ =>
    match r with
    | [] => rfl
    | e :: _ => nomatch e

/-- Both sides range over the one inhabitant of `Option PEmpty`. -/
def optionPEmptyEq : Option PEmpty.{1} → Option PEmpty.{1} → Prop :=
  fun x r => r = x

theorem optionPEmptyEq_not_dichotomy (pre : Option PEmpty.{1} → Prop) :
    ¬ PostconditionDichotomy pre optionPEmptyEq :=
  not_dichotomy_of_subsingleton_output fun a b =>
    match a, b with
    | none, none => rfl
    | some e, _ => nomatch e
    | _, some e => nomatch e

/-- Only `Sum.inr` builds a value of `Sum Empty Nat`. -/
def sumEmptyInr : Nat → Sum Empty Nat → Prop := fun _ r => ∃ n, r = Sum.inr n

theorem sumEmptyInr_not_dichotomy (pre : Nat → Prop) :
    ¬ PostconditionDichotomy pre sumEmptyInr :=
  not_dichotomy_of_const_true fun _ r _ =>
    match r with
    | .inr n => ⟨n, rfl⟩
    | .inl e => nomatch e

/-- A structure over a one-inhabitant field has one inhabitant. -/
structure EmptyBox where
  content : Option Empty

def emptyBoxPinned : Nat → EmptyBox → Prop := fun _ r => r = ⟨none⟩

theorem emptyBoxPinned_not_dichotomy (pre : Nat → Prop) :
    ¬ PostconditionDichotomy pre emptyBoxPinned :=
  not_dichotomy_of_const_true fun _ r _ =>
    match r with
    | ⟨none⟩ => rfl
    | ⟨some e⟩ => nomatch e

#expect_vacuous emptyBoxPinned reflexiveTautology
#expect_vacuous optionEmptyNone reflexiveTautology
#expect_vacuous listEmptyNil reflexiveTautology
#expect_vacuous optionPEmptyEq reflexiveTautology
#expect_vacuous sumEmptyInr semanticallyInsensitive

/-- Over an inhabited element type the same equations are genuine. -/
def optionNatNone : Nat → Option Nat → Prop := fun _ r => r = none

theorem optionNatNone_dichotomy :
    PostconditionDichotomy (fun _ => True) optionNatNone :=
  ⟨0, none, some 0, trivial, rfl, fun (h : some 0 = none) => nomatch h⟩

def listOptionEmptyNil : Nat → List (Option Empty) → Prop := fun _ r => r = []

theorem listOptionEmptyNil_dichotomy :
    PostconditionDichotomy (fun _ => True) listOptionEmptyNil :=
  ⟨0, [], [none], trivial, rfl, fun (h : [none] = []) => nomatch h⟩

def sumEmptyPinned : Nat → Sum Empty Nat → Prop := fun _ r => r = Sum.inr 3

theorem sumEmptyPinned_dichotomy :
    PostconditionDichotomy (fun _ => True) sumEmptyPinned :=
  ⟨0, .inr 3, .inr 4, trivial, rfl, fun h => absurd (Sum.inr.inj h) (by decide)⟩

/-- An empty type among the *inputs* does not make the output unbound. -/
def emptyInputPinned : Option Empty → Nat → Prop := fun _ r => r = 0

theorem emptyInputPinned_dichotomy :
    PostconditionDichotomy (fun _ => True) emptyInputPinned :=
  ⟨none, 0, 1, trivial, rfl, (by decide : ¬ (1 : Nat) = 0)⟩

#expect_binds optionNatNone
#expect_binds listOptionEmptyNil
#expect_binds sumEmptyPinned
#expect_binds emptyInputPinned

/-! ### Existential witnesses beyond a leading `∃` -/

vacuous_case forallExistsBound semanticallyInsensitive :=
  fun _ r => ∀ a, ∃ b, a + r ≤ b
  by
    intro _ r₁ r₂
    exact ⟨fun _ a => ⟨a + r₂, Nat.le_refl _⟩,
      fun _ a => ⟨a + r₁, Nat.le_refl _⟩⟩

vacuous_case zeroOrSucc semanticallyInsensitive :=
  fun _ r => r = 0 ∨ ∃ y, r = y + 1
  by
    intro _ r₁ r₂
    have h : ∀ r : Nat, r = 0 ∨ ∃ y, r = y + 1 := fun r =>
      match r with
      | 0 => .inl rfl
      | n + 1 => .inr ⟨n, rfl⟩
    exact ⟨fun _ => h r₂, fun _ => h r₁⟩

vacuous_case evenOrOdd semanticallyInsensitive :=
  fun _ r => (∃ k, r = 2 * k) ∨ (∃ k, r = 2 * k + 1)
  by
    intro _ r₁ r₂
    have h : ∀ r : Nat, (∃ k, r = 2 * k) ∨ (∃ k, r = 2 * k + 1) := fun r =>
      (Nat.mod_two_eq_zero_or_one r).elim
        (fun h => .inl ⟨r / 2, by omega⟩) (fun h => .inr ⟨r / 2, by omega⟩)
    exact ⟨fun _ => h r₂, fun _ => h r₁⟩

vacuous_case forallLeExistsDiff semanticallyInsensitive :=
  fun _ r => ∀ a, a ≤ r → ∃ b, r = a + b
  by
    intro _ r₁ r₂
    exact ⟨fun _ a _ => ⟨r₂ - a, by omega⟩, fun _ a _ => ⟨r₁ - a, by omega⟩⟩

vacuous_case ltExistsGap semanticallyInsensitive :=
  fun x r => x < r → ∃ d, r = x + d + 1
  by
    intro x r₁ r₂
    exact ⟨fun _ _ => ⟨r₂ - x - 1, by omega⟩, fun _ _ => ⟨r₁ - x - 1, by omega⟩⟩

genuine_case forallExistsBelow :=
  fun _ r => ∀ a : Nat, ∃ b, b < r ∧ a = a
  witness 0 1 0 by
    exact ⟨fun _ => ⟨0, by omega, rfl⟩,
      fun h => by obtain ⟨b, hb, _⟩ := h 0; omega⟩

genuine_case zeroOrSuccSucc :=
  fun _ r => r = 0 ∨ ∃ y, r = y + 2
  witness 0 0 1 by
    exact ⟨.inl rfl, fun h => by rcases h with h | ⟨y, h⟩ <;> omega⟩

genuine_case evenOrOneModFour :=
  fun _ r => (∃ k, r = 2 * k) ∨ (∃ k, r = 4 * k + 1)
  witness 0 0 3 by
    exact ⟨.inl ⟨0, rfl⟩, fun h => by rcases h with ⟨k, h⟩ | ⟨k, h⟩ <;> omega⟩

genuine_case forallBelowExistsSum :=
  fun x r => ∀ a, a < x → ∃ b, r = a + b
  witness 2 1 0 by
    exact ⟨fun a _ => ⟨1 - a, by omega⟩,
      fun h => by obtain ⟨b, hb⟩ := h 1 (by omega); omega⟩

genuine_case notSucc :=
  fun _ r => ¬ ∃ y, r = y + 1
  witness 0 0 1 by
    exact ⟨fun ⟨y, h⟩ => by omega, fun h => h ⟨0, rfl⟩⟩

genuine_case existsInHypothesis :=
  fun x r => (∃ y, x = y + 1) → r = x
  witness 1 1 0 by
    exact ⟨fun _ => rfl, fun h => by have := h ⟨0, rfl⟩; omega⟩

end HardeningA2

/-! ## Adversarial hardening regressions (Pass B3) -/

namespace HardeningB3

/-! ### Boilerplate monotonicity, empty fibres, and `.lam` (`match`) substitution -/

/--
Monotonicity regression: `callFramePreserved memAfter memAfter` is always `True`
(`callFramePreserved_refl`), so the guard is dead and `retVal` is unconstrained.
Without empty-fibre elimination and `full.bound` clamping, cofactoring the
impossible `False` assignment falsely reported `retVal` bound under
`userEnsuresOnly := true, strictReturnValue := true` even though plain
`strictReturnValue := true` rejected it.
-/
def tautologicalFrameAtomGuard : MirCallContract where
  pre _ := True
  post req ans :=
    match ans with
    | .returned retVal memAfter =>
      callFramePreserved req.memory memAfter ∧
        (¬ callFramePreserved memAfter memAfter → retVal = u32Arg 1)
    | .panicked _ => False
    | .aborted => True

theorem tautologicalFrameAtomGuard_not_returnValueDichotomy :
    ¬ MirCallContractReturnValueDichotomy tautologicalFrameAtomGuard :=
  not_mirCallContractReturnValueDichotomy_of_value_blind fun _ _ _ m _ =>
    ⟨fun ⟨hf, _⟩ => ⟨hf, fun h => absurd (callFramePreserved_refl m) h⟩,
      fun ⟨hf, _⟩ => ⟨hf, fun h => absurd (callFramePreserved_refl m) h⟩⟩

/--
Empty-fibre soundness in Part I: the `(b₁, False)` fibres of
`(callFramePreserved req.memory memAfter, callFramePreserved memAfter memAfter)`
are uninhabited, so output-insensitivity on inhabited fibres refutes dichotomy.
-/
theorem tautologicalFrameAtomGuard_not_dichotomyModuloObs :
    ¬ DichotomyModuloObservation
        (fun req (out : Value × Memory) =>
          (callFramePreserved req.memory out.2,
            callFramePreserved out.2 out.2))
        tautologicalFrameAtomGuard.pre
        (mirCallNormalPost tautologicalFrameAtomGuard) :=
  not_dichotomyModuloObservation_of_inhabited_cofactors_insensitive
    (fun b _ out => b.1 ∧ (¬ b.2 → out.1 = u32Arg 1))
    (fun _ _ _ => Iff.rfl)
    (fun b ⟨_, out, _, heq⟩ _ _ _ _ ⟨hb1, _⟩ => by
      have hb2 : b.2 := (congrArg Prod.snd heq) ▸ callFramePreserved_refl out.2
      exact ⟨hb1, fun hnb => absurd hb2 hnb⟩)

/-- Impossible-fibre disguise inside `externalSpecCallContract`. -/
def tautologicalFrameAtomGuardExtSpec (target : DefPath) (sidecar : CapturedMir) :
    MirCallContract :=
  externalSpecCallContract target sidecar (fun _ => True)
    (fun _ retVal =>
      ¬ callFramePreserved emptyMemory emptyMemory → retVal = u32Arg 1)

theorem tautologicalFrameAtomGuardExtSpec_not_ensuresDichotomy
    (target : DefPath) (sidecar : CapturedMir) :
    ¬ ExternalSpecEnsuresDichotomy target sidecar (fun _ => True)
        (fun _ retVal =>
          ¬ callFramePreserved emptyMemory emptyMemory → retVal = u32Arg 1) :=
  not_externalSpecEnsuresDichotomy_of_return_blind target sidecar _ _
    fun _ _ _ _ =>
      ⟨fun _ h => absurd (callFramePreserved_refl emptyMemory) h,
        fun _ h => absurd (callFramePreserved_refl emptyMemory) h⟩

section ClassicalB3

open Classical

/-- Impossible `else` branch guarded by `callFramePreserved memAfter memAfter`. -/
def impossibleFrameIte : MirCallContract where
  pre _ := True
  post req ans :=
    match ans with
    | .returned retVal memAfter =>
      callFramePreserved req.memory memAfter ∧
        (if callFramePreserved memAfter memAfter then True else retVal = u32Arg 1)
    | .panicked _ => False
    | .aborted => True

theorem impossibleFrameIte_not_returnValueDichotomy :
    ¬ MirCallContractReturnValueDichotomy impossibleFrameIte :=
  not_mirCallContractReturnValueDichotomy_of_value_blind fun _ _ _ m _ =>
    ⟨fun ⟨hf, _⟩ => ⟨hf, by
        split <;> first | trivial | exact absurd (callFramePreserved_refl m) ‹_›⟩,
      fun ⟨hf, _⟩ => ⟨hf, by
        split <;> first | trivial | exact absurd (callFramePreserved_refl m) ‹_›⟩⟩

end ClassicalB3

/-- Pure boilerplate inside a `match` alternative (`.lam` binder in `List.casesOn`). -/
def matchOnArgsPureBoilerplate : MirCallContract where
  pre _ := True
  post req ans :=
    match ans with
    | .returned _ memAfter =>
      match req.args with
      | [] => True
      | _ :: _ => callFramePreserved req.memory memAfter
    | .panicked _ => False
    | .aborted => True

theorem matchOnArgsPureBoilerplate_not_returnValueDichotomy :
    ¬ MirCallContractReturnValueDichotomy matchOnArgsPureBoilerplate :=
  not_mirCallContractReturnValueDichotomy_of_value_blind fun _ _ _ _ _ => Iff.rfl

/-- Two boilerplate predicates split across `match` alternatives. -/
def matchOnArgsBothBoilerplate (sidecar : CapturedMir) : MirCallContract where
  pre _ := True
  post req ans :=
    match ans with
    | .returned retVal memAfter =>
      match req.args with
      | [] => callFramePreserved req.memory memAfter
      | _ :: _ => retMatchesCalleeReturnTy sidecar retVal
    | .panicked _ => False
    | .aborted => True

theorem matchOnArgsBothBoilerplate_not_dichotomyModuloBoilerplate
    (sidecar : CapturedMir) :
    ¬ DichotomyModuloObservation (externalSpecBoilerplateObs sidecar)
        (matchOnArgsBothBoilerplate sidecar).pre
        (mirCallNormalPost (matchOnArgsBothBoilerplate sidecar)) :=
  not_dichotomyModuloObservation_of_factors
    (fun req b => match req.args with | [] => b.1 | _ :: _ => b.2)
    fun req _ _ => by
      cases h : req.args <;>
        simp [matchOnArgsBothBoilerplate, mirCallNormalPost,
          externalSpecBoilerplateObs, h]

/-- Genuine sibling: one `match` arm binds `retVal` beyond boilerplate. -/
def matchOnArgsMixedBoilerplate : MirCallContract where
  pre _ := True
  post req ans :=
    match ans with
    | .returned retVal memAfter =>
      match req.args with
      | [] => callFramePreserved req.memory memAfter
      | _ :: _ => callFramePreserved req.memory memAfter → retVal = u32Arg 1
    | .panicked _ => False
    | .aborted => False

theorem matchOnArgsMixedBoilerplate_returnValueDichotomy :
    MirCallContractReturnValueDichotomy matchOnArgsMixedBoilerplate :=
  ⟨{ defPath := "", args := [.unit], memory := emptyMemory },
    u32Arg 1, u32Arg 0, emptyMemory, trivial, fun _ => rfl,
    fun h => absurd (u32Arg_inj (h (callFramePreserved_refl _))) (by decide)⟩

/-- Strengthening preserves `DichotomyModuloObservation` (Part I theorem test). -/
theorem strengthening_moduloObservation :
    DichotomyModuloObservation (fun (_ _ : Nat) => ())
      Refinement.incPre Refinement.incSpec :=
  dichotomyModuloObservation_preserved_under_strengthening
    (post := Refinement.geSpec)
    (fun x r _ (h : r = x + 1) => show x ≤ r by omega)
    ⟨5, 6, 4, Refinement.incPre_five, rfl, rfl, show ¬ (5 ≤ 4) by omega⟩

run_meta do
  let user : EnsuresCheckConfig := { userEnsuresOnly := true }
  let strict : EnsuresCheckConfig := { strictReturnValue := true }
  let strictUser : EnsuresCheckConfig :=
    { userEnsuresOnly := true, strictReturnValue := true }
  -- Monotonicity: strict fails, user fails, and strict+user fails alike.
  let r1 ← reportOf ``tautologicalFrameAtomGuard
  unless r1.bindsOutput && !r1.bindsBeyondBoilerplate do
    throwError "tautologicalFrameAtomGuard: expected boilerplate-only\n{r1.describe}"
  expectReason ``tautologicalFrameAtomGuard .returnValueUnconstrained (cfg := strict)
  expectReason ``tautologicalFrameAtomGuard .boilerplateOnly (cfg := user)
  expectReason ``tautologicalFrameAtomGuard .boilerplateOnly (cfg := strictUser)
  for n in #[``tautologicalFrameAtomGuardExtSpec, ``impossibleFrameIte,
      ``matchOnArgsPureBoilerplate, ``matchOnArgsBothBoilerplate] do
    let r ← reportOf n
    unless r.bindsOutput && !r.bindsBeyondBoilerplate do
      throwError "{n}: expected boilerplate-only binding\n{r.describe}"
    expectReason n .boilerplateOnly (cfg := user)
  -- Genuine match arm with boilerplate still passes every mode.
  let rMix ← reportOf ``matchOnArgsMixedBoilerplate
  unless rMix.bindsOutput && rMix.bindsBeyondBoilerplate do
    throwError "matchOnArgsMixedBoilerplate: expected beyond-boilerplate\n{rMix.describe}"
  assertEnsuresBindsOutput ``matchOnArgsMixedBoilerplate (cfg := user)
  assertEnsuresBindsOutput ``matchOnArgsMixedBoilerplate (cfg := strictUser)

/-! ### Multi-output `isBareOutputEq` soundness (`strictReturnValue`) -/

def retBits : Value → Nat
  | .scalar s => s.bits
  | _ => 0

/--
`mem' = { mem with nextTag := retBits ret - retBits ret }` pins `mem'` while
leaving `ret` completely unconstrained (`retBits ret - retBits ret = 0`).
-/
def statefulStrictBypass (body : CapturedMir) : StatefulClaim where
  body := body
  pre _ _ := True
  post _ mem ret mem' := mem' = { mem with nextTag := retBits ret - retBits ret }

theorem statefulStrictBypass_not_returnDichotomy (body : CapturedMir) :
    ¬ StatefulClaimReturnDichotomy (statefulStrictBypass body) :=
  not_statefulClaimReturnDichotomy_of_return_blind fun _ mem r₁ r₂ mem' _ => by
    show (mem' = { mem with nextTag := retBits r₁ - retBits r₁ }) ↔
      (mem' = { mem with nextTag := retBits r₂ - retBits r₂ })
    simp

run_meta do
  let r ← reportOf ``statefulStrictBypass
  unless r.bindsOutput && r.boundOutputIdxs == #[3] do
    throwError "statefulStrictBypass: expected only mem' (idx 3) bound\n{r.describe}"
  expectReason ``statefulStrictBypass .returnValueUnconstrained
    (cfg := { strictReturnValue := true })

/-! ### Recursive emptiness and single-inhabitant outputs -/

def optEmptyProd : Nat → Option (Empty × Nat) → Prop := fun _ r => r = none
def listEmptyProd : Nat → List (Empty × Nat) → Prop := fun _ r => r = []
def optSumEmpty : Nat → Option (Sum Empty Empty) → Prop := fun _ r => r = none
def optFin0 : Nat → Option (Fin 0) → Prop := fun _ r => r = none
def listFin0 : Nat → List (Fin 0) → Prop := fun _ r => r = []
def optUnsatSub : Nat → Option { n : Nat // n < 0 } → Prop := fun _ r => r = none
def sumEmptyProdInr : Nat → Sum (Empty × Nat) Nat → Prop :=
  fun _ r => ∃ n, r = Sum.inr n
def sumFin0Inr : Nat → Sum (Fin 0) Nat → Prop := fun _ r => ∃ n, r = Sum.inr n
def optUnitToEmpty : Nat → Option (Unit → Empty) → Prop := fun _ r => r = none

theorem optEmptyProd_not_dichotomy (pre : Nat → Prop) :
    ¬ PostconditionDichotomy pre optEmptyProd :=
  not_dichotomy_of_option_empty fun p => p.1.elim

theorem listEmptyProd_not_dichotomy (pre : Nat → Prop) :
    ¬ PostconditionDichotomy pre listEmptyProd :=
  not_dichotomy_of_list_empty fun p => p.1.elim

theorem optSumEmpty_not_dichotomy (pre : Nat → Prop) :
    ¬ PostconditionDichotomy pre optSumEmpty :=
  not_dichotomy_of_option_empty fun s => s.elim Empty.elim Empty.elim

theorem optFin0_not_dichotomy (pre : Nat → Prop) :
    ¬ PostconditionDichotomy pre optFin0 :=
  not_dichotomy_of_option_empty Fin.elim0

theorem listFin0_not_dichotomy (pre : Nat → Prop) :
    ¬ PostconditionDichotomy pre listFin0 :=
  not_dichotomy_of_list_empty Fin.elim0

theorem optUnsatSub_not_dichotomy (pre : Nat → Prop) :
    ¬ PostconditionDichotomy pre optUnsatSub :=
  not_dichotomy_of_option_empty fun ⟨_, h⟩ => Nat.not_lt_zero _ h

theorem sumEmptyProdInr_not_dichotomy (pre : Nat → Prop) :
    ¬ PostconditionDichotomy pre sumEmptyProdInr :=
  not_dichotomy_of_sum_empty_left (fun p => p.1.elim)
    fun _ b₁ b₂ _ => ⟨fun _ => ⟨b₂, rfl⟩, fun _ => ⟨b₁, rfl⟩⟩

theorem sumFin0Inr_not_dichotomy (pre : Nat → Prop) :
    ¬ PostconditionDichotomy pre sumFin0Inr :=
  not_dichotomy_of_sum_empty_left Fin.elim0
    fun _ b₁ b₂ _ => ⟨fun _ => ⟨b₂, rfl⟩, fun _ => ⟨b₁, rfl⟩⟩

theorem optUnitToEmpty_not_dichotomy (pre : Nat → Prop) :
    ¬ PostconditionDichotomy pre optUnitToEmpty :=
  not_dichotomy_of_option_empty fun f => (f ()).elim

/-- Soundness guards: genuine two-inhabitant wrappers must still bind. -/
structure PropBox where
  p : Prop

def propBoxTrue : Nat → PropBox → Prop := fun _ r => r = ⟨True⟩
def optFin1 : Nat → Option (Fin 1) → Prop := fun _ r => r = none
def listFin1 : Nat → List (Fin 1) → Prop := fun _ r => r = []

theorem propBoxTrue_dichotomy :
    PostconditionDichotomy (fun _ => True) propBoxTrue :=
  ⟨0, ⟨True⟩, ⟨False⟩, trivial, rfl, fun h =>
    have htf : False = True := congrArg PropBox.p h
    htf.mpr trivial⟩

theorem optFin1_dichotomy : PostconditionDichotomy (fun _ => True) optFin1 :=
  ⟨0, none, some ⟨0, by decide⟩, trivial, rfl, fun h => nomatch h⟩

theorem listFin1_dichotomy : PostconditionDichotomy (fun _ => True) listFin1 :=
  ⟨0, [], [⟨0, by decide⟩], trivial, rfl, fun h => nomatch h⟩

#expect_vacuous optEmptyProd reflexiveTautology
#expect_vacuous listEmptyProd reflexiveTautology
#expect_vacuous optSumEmpty reflexiveTautology
#expect_vacuous optFin0 semanticallyInsensitive
#expect_vacuous listFin0 semanticallyInsensitive
#expect_vacuous optUnsatSub semanticallyInsensitive
#expect_vacuous sumEmptyProdInr semanticallyInsensitive
#expect_vacuous sumFin0Inr reflexiveTautology
#expect_vacuous optUnitToEmpty reflexiveTautology
#expect_binds propBoxTrue
#expect_binds optFin1
#expect_binds listFin1

run_meta do
  -- Purely structural emptiness needs no semantic probe.
  let noProbe : EnsuresCheckConfig := { semanticProbe := false }
  for n in #[``optEmptyProd, ``listEmptyProd, ``optSumEmpty,
      ``optUnitToEmpty] do
    assertEnsuresVacuous n (some .reflexiveTautology) (cfg := noProbe)

/-! ### `Int` existentials, `Iff` insensitivity, and disjunctive/`match` `requires` -/

def existsIntSucc (_x r : Int) : Prop := ∃ y : Int, r = y + 1
def existsIntGt (_x r : Int) : Prop := ∃ y : Int, r < y
def existsIntParity (_x r : Int) : Prop := ∃ y : Int, r = 2 * y ∨ r = 2 * y + 1
def existsIntEvenOrOdd (_x r : Int) : Prop :=
  (∃ k : Int, r = 2 * k) ∨ (∃ k : Int, r = 2 * k + 1)
def existsIntNonneg (_x r : Int) : Prop := ∃ y : Int, y ≥ 0 ∧ r = y

theorem existsIntSucc_not_dichotomy (pre : Int → Prop) :
    ¬ PostconditionDichotomy pre existsIntSucc :=
  not_dichotomy_of_universal_post fun _ r _ => ⟨r - 1, by omega⟩

theorem existsIntGt_not_dichotomy (pre : Int → Prop) :
    ¬ PostconditionDichotomy pre existsIntGt :=
  not_dichotomy_of_universal_post fun _ r _ => ⟨r + 1, by omega⟩

theorem existsIntParity_not_dichotomy (pre : Int → Prop) :
    ¬ PostconditionDichotomy pre existsIntParity :=
  not_dichotomy_of_universal_post fun _ r _ => ⟨r / 2, by omega⟩

theorem existsIntEvenOrOdd_not_dichotomy (pre : Int → Prop) :
    ¬ PostconditionDichotomy pre existsIntEvenOrOdd :=
  not_dichotomy_of_universal_post fun _ r _ => by
    by_cases h : r = 2 * (r / 2)
    · exact .inl ⟨r / 2, h⟩
    · exact .inr ⟨r / 2, by omega⟩

theorem existsIntNonneg_dichotomy :
    PostconditionDichotomy (fun _ => True) existsIntNonneg :=
  ⟨0, 0, -1, trivial, ⟨0, by omega, rfl⟩, fun ⟨_, hy, h⟩ => by omega⟩

#expect_vacuous existsIntSucc semanticallyInsensitive
#expect_vacuous existsIntGt semanticallyInsensitive
#expect_vacuous existsIntParity semanticallyInsensitive
#expect_vacuous existsIntEvenOrOdd semanticallyInsensitive
#expect_binds existsIntNonneg

-- Existentials equivalent to an input-only predicate (`Iff` witness search).
vacuous_case existsArithEquivInput semanticallyInsensitive :=
  fun x r => ∃ y : Nat, y ≥ r ∧ x < 5
  by
    intro x r₁ r₂
    exact ⟨fun ⟨_, _, hx⟩ => ⟨r₂, Nat.le_refl _, hx⟩,
      fun ⟨_, _, hx⟩ => ⟨r₁, Nat.le_refl _, hx⟩⟩

vacuous_case existsSubEquivInput semanticallyInsensitive :=
  fun x r => ∃ y : Nat, y + x ≥ r ∧ x < 5
  by
    intro x r₁ r₂
    exact ⟨fun ⟨_, _, hx⟩ => ⟨r₂, by omega, hx⟩,
      fun ⟨_, _, hx⟩ => ⟨r₁, by omega, hx⟩⟩

-- Existentials that become vacuous only under `requires`.
def existsVacuousUnderPre (x r : Nat) : Prop :=
  (r = 0 ∧ x ≥ 10) ∨ ∃ y : Nat, r ≤ y ∧ x < 10

theorem existsVacuousUnderPre_dichotomy :
    PostconditionDichotomy (fun _ => True) existsVacuousUnderPre :=
  ⟨10, 0, 1, trivial, .inl ⟨rfl, Nat.le_refl _⟩, by
    rintro (⟨h, _⟩ | ⟨_, _, h⟩) <;> omega⟩

theorem existsVacuousUnderPre_not_dichotomy_under_pre :
    ¬ PostconditionDichotomy HardeningA1.smallPre existsVacuousUnderPre :=
  not_dichotomy_of_universal_post fun _ r hx => .inr ⟨r, Nat.le_refl _, hx⟩

def tenPre (x : Nat) : Prop := x = 10
def existsGapUnderPre (x r : Nat) : Prop := r < 10 ∨ ∃ y : Nat, r = y + x

theorem existsGapUnderPre_dichotomy :
    PostconditionDichotomy (fun _ => True) existsGapUnderPre :=
  ⟨100, 0, 50, trivial, .inl (by decide), by
    rintro (h | ⟨y, h⟩) <;> omega⟩

theorem existsGapUnderPre_not_dichotomy_under_pre :
    ¬ PostconditionDichotomy tenPre existsGapUnderPre :=
  not_dichotomy_of_universal_post fun _ r (hx : _ = 10) => by
    by_cases h : r < 10
    · exact .inl h
    · exact .inr ⟨r - 10, by omega⟩

/-- Disjunctive `requires`: both disjuncts contradict the guard in `post`. -/
def disjPreContract : MirCallContract where
  pre req := req.args = [u32Arg 0] ∨ req.args = [u32Arg 1]
  post req ans :=
    match ans with
    | .returned r _ => req.args = [u32Arg 2] → r = u32Arg 0
    | .panicked _ => False
    | .aborted => False

theorem disjPreContract_not_normalDichotomy :
    ¬ MirCallContractNormalDichotomy disjPreContract := by
  have h0 : ¬ PostconditionDichotomy (fun req : MirCallReq => req.args = [u32Arg 0])
      (mirCallNormalPost disjPreContract) :=
    not_dichotomy_of_universal_post fun _ _ h h2 =>
      absurd (u32Single_inj h h2) (by decide)
  have h1 : ¬ PostconditionDichotomy (fun req : MirCallReq => req.args = [u32Arg 1])
      (mirCallNormalPost disjPreContract) :=
    not_dichotomy_of_universal_post fun _ _ h h2 =>
      absurd (u32Single_inj h h2) (by decide)
  exact fun h =>
    ((postconditionDichotomy_or_pre_iff).mp
      (mirCallContractNormalDichotomy_iff.mp h)).elim h0 h1

/-- Genuine disjunctive `requires`: the second disjunct satisfies the guard. -/
def disjPreGenuineContract : MirCallContract where
  pre req := req.args = [u32Arg 0] ∨ req.args = [u32Arg 2]
  post req ans :=
    match ans with
    | .returned r _ => req.args = [u32Arg 2] → r = u32Arg 0
    | .panicked _ => False
    | .aborted => False

theorem disjPreGenuineContract_returnValueDichotomy :
    MirCallContractReturnValueDichotomy disjPreGenuineContract :=
  ⟨{ defPath := "", args := [u32Arg 2], memory := emptyMemory },
    u32Arg 0, u32Arg 1, emptyMemory, .inr rfl, fun _ => rfl,
    fun h => absurd (u32Arg_inj (h rfl)) (by decide)⟩

/-- `match`-shaped `requires` whose pattern contradicts the implication guard. -/
def matchPreContract : MirCallContract where
  pre req :=
    match req.args with
    | [v] => v = u32Arg 0
    | _ => False
  post req ans :=
    match ans with
    | .returned r _ => req.args = [u32Arg 1] → r = u32Arg 0
    | .panicked _ => False
    | .aborted => False

theorem matchPreContract_not_normalDichotomy :
    ¬ MirCallContractNormalDichotomy matchPreContract :=
  not_mirCallContractNormalDichotomy_of_return_blind fun req _ _ _ _ hpre =>
    ⟨fun _ h1 => by
        dsimp only [matchPreContract] at hpre
        rw [h1] at hpre
        exact absurd (u32Arg_inj hpre) (by decide),
      fun _ h1 => by
        dsimp only [matchPreContract] at hpre
        rw [h1] at hpre
        exact absurd (u32Arg_inj hpre) (by decide)⟩

/-- Disjunctive realizability & modulo-observation distribution (Part I tests). -/
theorem disj_realizable_test :
    ContractRealizable (fun x : Nat => x < 10 ∨ x > 20)
      (fun x r => r = x + 1) :=
  (contractRealizable_or_pre_iff).mpr <| .inl ⟨0, 1, by decide, rfl⟩

theorem disj_moduloObservation_test :
    DichotomyModuloObservation (fun (_ _ : Nat) => ())
      (fun x : Nat => x < 10 ∨ x > 20) (fun x r => r = x + 1) :=
  (dichotomyModuloObservation_or_pre_iff).mpr <|
    .inl ⟨0, 1, 2, by decide, rfl, rfl, by decide⟩

#expect_vacuous disjPreContract vacuousUnderRequires
#expect_binds disjPreGenuineContract
#expect_vacuous matchPreContract vacuousUnderRequires

run_meta do
  assertEnsuresBindsOutput ``existsVacuousUnderPre
  assertEnsuresVacuous ``existsVacuousUnderPre (some .vacuousUnderRequires)
    (preDecl? := some ``HardeningA1.smallPre)
  assertEnsuresBindsOutput ``existsGapUnderPre
  assertEnsuresVacuous ``existsGapUnderPre (some .vacuousUnderRequires)
    (preDecl? := some ``tenPre)

end HardeningB3

/-! ## Hardening (pass A3): components, guards, and the analysis budget -/

namespace HardeningA3

/-! ### Componentwise dichotomy of a pair output -/

/-- Binds the first component of its output, and only that. -/
def firstOnly : Nat → Nat × Nat → Prop := fun x out => out.1 = x

theorem firstOnly_dichotomy :
    PostconditionDichotomy (fun _ => True) firstOnly :=
  ⟨0, (0, 0), (1, 0), trivial, rfl, fun (h : (1 : Nat) = 0) => absurd h (by decide)⟩

theorem firstOnly_not_second_component :
    ¬ DichotomyModuloObservation (fun (_ : Nat) (out : Nat × Nat) => out.1)
      (fun _ => True) firstOnly :=
  fun ⟨_, ok, bad, _, heq, hok, hbad⟩ =>
    have heq : ok.1 = bad.1 := heq
    hbad (heq.symm.trans hok)

/-- The decomposition finds the dichotomy in the first component. -/
theorem firstOnly_first_component :
    DichotomyModuloObservation (fun (_ : Nat) (out : Nat × Nat) => out.2)
      (fun _ => True) firstOnly :=
  (postconditionDichotomy_prod_iff.mp firstOnly_dichotomy).resolve_right
    firstOnly_not_second_component

/-- Insensitive to each component separately, hence to the pair. -/
def pairCommutes : Nat → Nat × Nat → Prop :=
  fun x out => out.1 + out.2 = out.2 + out.1 ∧ x = x

theorem pairCommutes_not_dichotomy (pre : Nat → Prop) :
    ¬ PostconditionDichotomy pre pairCommutes :=
  not_dichotomy_prod_of_components
    (fun _ _ _ _ _ _ => ⟨Nat.add_comm _ _, rfl⟩)
    (fun _ _ _ _ _ _ => ⟨Nat.add_comm _ _, rfl⟩)

#expect_binds firstOnly
#expect_vacuous pairCommutes semanticallyInsensitive

/-- The frame-only contract separates memories for a fixed returned value. -/
theorem frameOnly_memoryDichotomy :
    MirCallContractMemoryDichotomy frameOnlyMirCallContract :=
  ⟨witnessReq, .unit, emptyMemory, { emptyMemory with activeProtectors := [0] },
    trivial, callFramePreserved_refl emptyMemory,
    fun h => List.cons_ne_self 0 _ h.2.2.2.1⟩

/-- Its normal dichotomy is the memory disjunct of the decomposition. -/
theorem frameOnly_normalDichotomy_is_memory :
    MirCallContractNormalDichotomy frameOnlyMirCallContract ∧
      ¬ MirCallContractReturnValueDichotomy frameOnlyMirCallContract ∧
      MirCallContractMemoryDichotomy frameOnlyMirCallContract :=
  have hv : ¬ MirCallContractReturnValueDichotomy frameOnlyMirCallContract :=
    not_mirCallContractReturnValueDichotomy_of_value_blind
      fun _ _ _ _ _ => Iff.rfl
  have hn := frameOnly_memoryDichotomy.toNormalDichotomy
  ⟨hn, hv,
    (mirCallContractNormalDichotomy_iff_returnValue_or_memory.mp hn).resolve_left
      hv⟩

/-- The same for the frame-only `StatefulClaim`. -/
theorem frameOnlyStateful_memoryDichotomy (body : CapturedMir) :
    StatefulClaimMemoryDichotomy (frameOnlyStatefulClaim body) :=
  (statefulClaimDichotomy_iff_return_or_memory.mp
    (frameOnlyStatefulClaim_dichotomy body)).resolve_left
    (frameOnlyStatefulClaim_not_returnDichotomy body)

run_meta do
  -- The two disjuncts are the checker's two per-output verdicts.
  let r ← reportOf ``frameOnlyMirCallContract
  unless r.bindsOutput do
    throwError "frameOnlyMirCallContract: expected a (memory) binding\n\
      {r.describe}"
  expectReason ``frameOnlyMirCallContract .returnValueUnconstrained
    (cfg := { strictReturnValue := true })

/-! ### Guarded postconditions -/

/-- `requires(x < 10)`. -/
def belowTen : Nat → Prop := fun x => x < 10

/-- `ensures(x >= 10 ==> ret == 5)`: the guard is an input predicate. -/
def inputGuarded : Nat → Nat → Prop := fun x r => 10 ≤ x → r = 5

/-- The guard moves into the precondition, which then admits no input. -/
theorem inputGuarded_not_dichotomy_under_pre :
    ¬ PostconditionDichotomy belowTen inputGuarded :=
  fun h => not_dichotomy_of_unsat_pre
    (not_preconditionSatisfiable_of_unsat
      fun x (hx : x < 10 ∧ 10 ≤ x) => by omega)
    ((postconditionDichotomy_input_guard_iff (fun x => 10 ≤ x)).mp h)

/-- `ensures(x >= 10 && ret > 0 ==> ret == 5)`: the guard mentions the output. -/
def mixedGuarded : Nat → Nat → Prop := fun x r => 10 ≤ x ∧ 0 < r → r = 5

theorem mixedGuarded_dichotomy :
    PostconditionDichotomy (fun _ => True) mixedGuarded :=
  ⟨10, 5, 1, trivial, fun _ => rfl,
    fun h => absurd (h ⟨Nat.le_refl 10, by decide⟩) (by decide)⟩

theorem mixedGuarded_not_dichotomy_under_pre :
    ¬ PostconditionDichotomy belowTen mixedGuarded :=
  not_dichotomy_of_guard_refuted_by_pre
    (guard := fun x r => 10 ≤ x ∧ 0 < r) (post := fun _ r => r = 5)
    fun x _ (hx : x < 10) (hg : 10 ≤ x ∧ _) => by omega

/--
A guard on the output with a conclusion on the input: `ret == 5 ==> x < 3`.
The conclusion never mentions `ret`, yet the clause binds it; the guard is not
a hypothesis the analysis may assume.
-/
def outputGuarded : Nat → Nat → Prop := fun x r => r = 5 → x < 3

theorem outputGuarded_dichotomy_under_pre :
    PostconditionDichotomy belowTen outputGuarded :=
  ⟨7, 0, 5, (by decide : (7 : Nat) < 10),
    fun (h : (0 : Nat) = 5) => absurd h (by decide),
    fun h => absurd (h rfl) (by decide)⟩

run_meta do
  assertEnsuresBindsOutput ``inputGuarded
  assertEnsuresVacuous ``inputGuarded (some .vacuousUnderRequires)
    (preDecl? := some ``belowTen)
  assertEnsuresBindsOutput ``mixedGuarded
  assertEnsuresVacuous ``mixedGuarded (some .vacuousUnderRequires)
    (preDecl? := some ``belowTen)
  assertEnsuresBindsOutput ``outputGuarded (preDecl? := some ``belowTen)

/-! ### An `ensures` clause the return type implies -/

/-- `ensures` restates the return-type boilerplate. -/
def restatesReturnType (target : DefPath) (sidecar : CapturedMir) :
    MirCallContract :=
  externalSpecCallContract target sidecar (fun _ => True)
    (fun _ ret => retMatchesCalleeReturnTy sidecar ret)

theorem restatesReturnType_not_ensuresDichotomy (target : DefPath)
    (sidecar : CapturedMir) :
    ¬ ExternalSpecEnsuresDichotomy target sidecar (fun _ => True)
      (fun _ ret => retMatchesCalleeReturnTy sidecar ret) :=
  not_externalSpecEnsuresDichotomy_of_implied_by_retTy target sidecar _ _
    fun _ _ _ h => h

run_meta do
  let r ← reportOf ``restatesReturnType
  unless r.bindsOutput && !r.bindsBeyondBoilerplate do
    throwError "restatesReturnType: expected boilerplate-only binding\n\
      {r.describe}"
  expectReason ``restatesReturnType .boilerplateOnly
    (cfg := { userEnsuresOnly := true })

/-! ### Closed numerals behind a definition -/

/-- A reduction modulo `2 ^ 32` is below `2 ^ 32`: says nothing about `r`. -/
def reducedBelowModulus : Nat → Nat → Prop :=
  fun _ r => r % scalarModulus 4 < scalarModulus 4

theorem reducedBelowModulus_not_dichotomy (pre : Nat → Prop) :
    ¬ PostconditionDichotomy pre reducedBelowModulus :=
  not_dichotomy_of_const_true fun _ r _ =>
    Nat.mod_lt r (Nat.pos_of_ne_zero (by decide))

/-- The bound itself is a genuine `u32` range constraint. -/
def belowModulus : Nat → Nat → Prop := fun _ r => r < scalarModulus 4

theorem belowModulus_dichotomy :
    PostconditionDichotomy (fun _ => True) belowModulus :=
  ⟨0, 0, scalarModulus 4, trivial, (by decide : 0 < scalarModulus 4),
    Nat.lt_irrefl _⟩

#expect_vacuous reducedBelowModulus semanticallyInsensitive
#expect_binds belowModulus

/-! ### The analysis budget: the checker never times its caller out -/

/-- Genuine: `r ≥ x` over `Int`, stated with a witness. -/
def intOffsetNonneg : Int → Int → Prop := fun x r => ∃ k : Int, r = x + k ∧ k ≥ 0

theorem intOffsetNonneg_dichotomy :
    PostconditionDichotomy (fun _ => True) intOffsetNonneg :=
  ⟨0, 0, -1, trivial, ⟨0, by omega, by omega⟩, fun ⟨k, h₁, h₂⟩ => by omega⟩

/-- Genuine: residue `0` or `1` modulo `3`, with witnesses bounded by the input. -/
def intThirds : Int → Int → Prop :=
  fun x r => (∃ k : Int, r = 3 * k ∧ k ≥ x) ∨ (∃ k : Int, r = 3 * k + 1 ∧ k ≤ x)

theorem intThirds_dichotomy : PostconditionDichotomy (fun _ => True) intThirds :=
  ⟨0, 0, 2, trivial, .inl ⟨0, by omega, by omega⟩,
    fun h => by rcases h with ⟨k, h₁, h₂⟩ | ⟨k, h₁, h₂⟩ <;> omega⟩

/-- Vacuous, but only the proof search can tell. -/
def leSelfPlus : Nat → Nat → Prop := fun x r => r ≤ r + x

theorem leSelfPlus_not_dichotomy (pre : Nat → Prop) :
    ¬ PostconditionDichotomy pre leSelfPlus :=
  not_dichotomy_of_const_true fun x r _ => Nat.le_add_right r x

-- Both genuine contracts are judged well inside a tenth of the default
-- command budget: a failed witness search is not allowed to be expensive.
set_option maxHeartbeats 20000 in
#expect_binds intOffsetNonneg

set_option maxHeartbeats 20000 in
#expect_binds intThirds

run_meta do
  -- Out of budget, probing stops: the verdict is the conservative one, it is
  -- labelled, and no exception reaches the caller.
  let starved : EnsuresCheckConfig := { maxAnalysisHeartbeats := 1 }
  let r ← reportOf ``leSelfPlus (cfg := starved)
  unless r.bindsOutput && r.notes.contains EnsuresCheck.analysisBudgetNote do
    throwError "leSelfPlus (starved): expected a labelled conservative verdict\n\
      {r.describe}"
  -- A verdict of the syntactic pass needs no probe and survives.
  let r ← reportOf ``Class3.reflPost (cfg := starved)
  unless r.isVacuous || r.notes.contains EnsuresCheck.analysisBudgetNote do
    throwError "reflPost (starved): expected vacuous or labelled\n{r.describe}"
  -- With the default budget the probe runs and no label is attached.
  let r ← reportOf ``leSelfPlus
  unless r.reason? == some .semanticallyInsensitive &&
      !r.notes.contains EnsuresCheck.analysisBudgetNote do
    throwError "leSelfPlus: expected semanticallyInsensitive\n{r.describe}"
  -- A modest budget is respected (up to one probe) and still labelled.
  let before ← IO.getNumHeartbeats
  let r ← reportOf ``intOffsetNonneg (cfg := { maxAnalysisHeartbeats := 500 })
  let used := (← IO.getNumHeartbeats) - before
  unless r.bindsOutput && used ≤ 6000000 do
    throwError "intOffsetNonneg (500k budget): used {used} heartbeats\n\
      {r.describe}"

-- A caller that is itself nearly out of heartbeats gets a labelled verdict
-- rather than a timeout: the analysis takes at most seven eighths of what is
-- left, and `intThirds` would need more.
set_option maxHeartbeats 4000 in
run_meta do
  let r ← reportOf ``intThirds
  unless r.bindsOutput && r.notes.contains EnsuresCheck.analysisBudgetNote do
    throwError "intThirds (starved caller): expected a labelled conservative \
      verdict\n{r.describe}"

end HardeningA3

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
