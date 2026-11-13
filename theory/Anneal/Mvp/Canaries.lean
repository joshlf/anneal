-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Anneal.Mvp.Execution

/-!
These kernel-checked cases distinguish prefix safety from return-only claims,
and exercise the scalar and allocation boundaries used by symbolic execution.
The hand-built bodies use local canary identities. The source-backed identity
regression separately checks that capture binds reviewed contracts to Rust
items; these local labels do not claim the capture scheme's path guarantees.
-/

namespace Anneal.Mvp.Canaries

open Trusted.Mvp

-- The loop never reads its uninitialized return slot. Prefix safety must permit
-- this execution without requiring the slot to acquire a return value.
def spin : Body := ⟨0, false, [.int 64 false], [⟨[], .goto 0⟩], "canary::spin"⟩

theorem spin_step (args : List Word) :
    step spin (initial spin args) = .next (initial spin args) := rfl

theorem spin_safe (args : List Word) : Safe spin args :=
  safeFrom_selfLoop (spin_step args)

theorem spin_noReturn (args : List Word) (value : Word) :
    ¬Returns spin args value := by
  intro returned
  cases returned with
  | intro finish reached =>
      have same := reachable_selfLoop (spin_step args) reached.1
      subst finish
      simp [spin_step] at reached

theorem spin_verified : BodyVerified spin (fun _ => False) := by
  constructor
  · decide
  · intro args valid safety
    exact spin_safe args

-- Both this body and spin have no returns. Requiring safety of all prefixes
-- distinguishes them, while a property only about completed returns would not.
def faultBeforeSpin : Body :=
  ⟨0, false, [.int 64 false],
    [⟨[.assign 0 (.use (.copy 0) true)], .goto 0⟩], "canary::faultBeforeSpin"⟩

theorem faultBeforeSpin_admitted : bodyWF faultBeforeSpin = true := by rfl

theorem faultBeforeSpin_notSafe : ¬Safe faultBeforeSpin [] := by
  intro safe
  exact safe (initial faultBeforeSpin []) .refl .uninitialized rfl

theorem faultBeforeSpin_noReturn (value : Word) :
    ¬Returns faultBeforeSpin [] value := by
  intro returned
  cases returned with
  | intro finish reached =>
      have faulted : step faultBeforeSpin (initial faultBeforeSpin []) =
          .fault .uninitialized := rfl
      have same := reachable_after_fault faulted reached.1
      subst finish
      simp [faulted] at reached

theorem falsePre_doesNotHideFault :
    ¬BodyVerified faultBeforeSpin (fun _ => False) := by
  intro verified
  have valid : argsValid faultBeforeSpin [] := by
    constructor
    · rfl
    · intro index value impossible
      cases impossible
  have safeEntry : faultBeforeSpin.isUnsafe = true → False := by
    simp [faultBeforeSpin]
  exact faultBeforeSpin_notSafe (verified.2 [] valid safeEntry)

theorem falseFunctional_doesNotHideFault :
    ¬CrateTheorem ⟨.crate, [faultBeforeSpin]⟩
      ⟨fun _ _ => False,
        fun _ => ∀ args : List Word, False → Returns faultBeforeSpin args 0⟩ := by
  intro verified
  exact falsePre_doesNotHideFault (verified.2.1 0 faultBeforeSpin rfl)

theorem unit_scope_is_not_crate (specs : Specs) :
    ¬CrateTheorem ⟨.unit, []⟩ specs := by
  intro verified
  cases verified.1

theorem crate_scope_is_not_unit (specs : Specs) :
    ¬UnitTheorem ⟨.crate, []⟩ specs := by
  intro verified
  cases verified.1

-- A false unsafe caller requirement must not hide independent admission duties.
-- This body has malformed locals and control flow even though no allowed caller
-- can enter it under that requirement.
def malformedUnsafe : Body := ⟨0, true, [], [⟨[], .goto 9⟩], "canary::malformedUnsafe"⟩

theorem unsafeFalsePre_stillRequiresAdmission :
    ¬BodyVerified malformedUnsafe (fun _ => False) := by
  intro verified
  have rejected : bodyWF malformedUnsafe = false := by rfl
  have admitted := verified.1
  rw [rejected] at admitted
  cases admitted

theorem shift_modulo :
    evalBinary .shl (.int 64 false) 1 (.int 32 false) 64 =
      .ok (.int 64 false, 1) := by rfl

theorem signed_shift_rhs :
    evalBinary .shl (.int 64 false) 1 (.int 32 true) 4294967295 =
      .ok (.int 64 false, BitVec.ofNat 64 9223372036854775808) := by rfl

theorem signed_shift_lhs :
    evalBinary .shr (.int 8 true) 128 (.int 32 false) 1 =
      .ok (.int 8 true, 192) := by rfl

theorem unsigned_overflow_wraps :
    evalBinary .add (.int 8 false) 255 (.int 8 false) 1 =
      .ok (.int 8 false, 0) := by rfl

theorem signed_overflow_wraps :
    evalBinary .add (.int 8 true) 127 (.int 8 true) 1 =
      .ok (.int 8 true, 128) := by rfl

theorem signed_comparison :
    evalBinary .lt (.int 8 true) 255 (.int 8 true) 1 =
      .ok (.bool, 1) := by rfl

theorem raw_negative_constant :
    evalOperand spin [] (.constant (.int 32 true) 4294967295) =
      .ok (.int 32 true, 4294967295, []) := by rfl

theorem untruncated_constant_rejected :
    evalOperand spin [] (.constant (.int 32 true) 4294967296) =
      .error .invalidValue := by rfl

def enumBody : Body :=
  ⟨1, false, [.int 64 true, .enum 7 [42, 18446744073709551615]], [], "canary::enumBody"⟩

theorem discriminant_is_not_index :
    evalRvalue enumBody [.uninit, .value 1] (.discriminant 1) =
      .ok (.int 64 true, 18446744073709551615, [.uninit, .value 1]) := by rfl

theorem enum_invalid_index_rejected :
    readLocal enumBody [.uninit, .value 2] 1 = .error .invalidValue := by rfl

theorem nominal_enums_distinct :
    writeLocal enumBody [.uninit, .value 1] 1 (.enum 8 [42, 18446744073709551615]) 0 =
      .error .typeMismatch := by rfl

-- Allocation and value initialization are distinct facts. In particular, an
-- unread destination still needs allocated storage before a constant write.
def storageBody : Body :=
  ⟨0, false, [.int 64 false, .bool],
    [⟨[.storageLive 1, .storageDead 1], .goto 0⟩], "canary::storageBody"⟩

theorem initial_storage_states :
    (initial storageBody []).locals = [.uninit, .dead] := rfl

theorem storage_live_resets :
    execStatement storageBody [.uninit, .value 1] (.storageLive 1) =
      .ok [.uninit, .uninit] := rfl

theorem storage_dead_idempotent :
    execStatement storageBody [.uninit, .dead] (.storageDead 1) =
      .ok [.uninit, .dead] := rfl

theorem dead_write_rejected :
    writeLocal storageBody [.uninit, .dead] 1 .bool 0 = .error .deadLocal := rfl

theorem invalid_bool_rejected :
    readLocal storageBody [.uninit, .value 2] 1 = .error .invalidValue := rfl

theorem move_invalidates :
    evalOperand storageBody [.uninit, .value 1] (.move 1) =
      .ok (.bool, 1, [.uninit, .uninit]) := rfl

theorem move_second_load_refused :
    evalRvalue storageBody [.uninit, .value 1]
      (.binary .bitAnd (.move 1) (.copy 1)) = .error .uninitialized := rfl

theorem missing_block_faults :
    step spin ⟨9, 0, [.uninit]⟩ = .fault .badBlock := rfl

theorem missing_statement_faults :
    step spin ⟨0, 1, [.uninit]⟩ = .fault .badPosition := rfl

def returnSeven : Body :=
  ⟨0, false, [.int 64 false],
    [⟨[.assign 0 (.use (.constant (.int 64 false) 7) true)], .ret⟩], "canary::returnSeven"⟩

theorem returnSeven_evaluates :
    run returnSeven 2 (initial returnSeven []) = some 7 := rfl

-- The nonempty segment pays only for reaching the checkpoint. Its suffix must
-- still witness the actual return, preserving both prefix safety and the exact
-- result used by wrong_result_refused below.
theorem returnSeven_safe_and_returns : Safe returnSeven [] ∧ Returns returnSeven [] 7 := by
  have segment : Reach returnSeven (initial returnSeven [])
      ⟨0, 1, [.value 7]⟩ := .next .refl rfl
  have execution : Executes returnSeven (initial returnSeven []) 7 :=
    executes_prepend segment (.ret rfl)
  exact ⟨executes_safe execution, executes_returns execution⟩

theorem wrong_result_refused : ¬Returns returnSeven [] 0 := by
  intro returned
  have equal := run_result_unique returnSeven_evaluates returned
  have unequal : (7 : Word) ≠ 0 := by decide
  exact unequal equal

-- This empty entry domain comes from an uninhabited captured type. It is
-- distinct from narrowing a safe function's domain with an authored predicate.
def neverArgument : Body :=
  ⟨1, false, [.unit, .never], [⟨[.assign 0 .unit], .ret⟩], "canary::neverArgument"⟩

theorem never_argument_has_no_valid_entry (args : List Word) :
    ¬argsValid neverArgument args := by
  intro valid
  cases args with
  | nil => cases valid.1
  | cons value rest =>
      cases valid.2 0 value rfl with
      | intro ty evidence =>
          have same : Ty.never = ty := Option.some.inj evidence.1
          subst ty
          have impossible := evidence.2
          change false = true at impossible
          cases impossible

def returnUnit : Body := ⟨0, false, [.unit], [⟨[.assign 0 .unit], .ret⟩], "canary::returnUnit"⟩

theorem unit_return_safe_and_returns : Safe returnUnit [] ∧ Returns returnUnit [] 0 :=
  run_initial_success (show run returnUnit 2 (initial returnUnit []) = some 0 from rfl)

theorem unit_constant_encoding :
    evalOperand returnUnit [] (.constant .unit 0) = .ok (.unit, 0, []) := rfl

theorem nonzero_unit_rejected : validValue .unit 1 = false := rfl

theorem initialized_never_rejected :
    readLocal neverArgument [.uninit, .value 0] 1 = .error .invalidValue := rfl


def unrestrictedUnsafe : Body :=
  ⟨0, true, [.int 64 false], [⟨[], .unreachable⟩], "rust-path-v1::open"⟩

def namedSafety : Specs :=
  { safety := fun identity _ =>
      if identity = "rust-path-v1::locked" then False else True
    property := fun _ => True }

/--
The only restrictive contract belongs to `locked`. Putting a faulting `open`
body in slot zero must not transfer that restriction and erase its safety duty.
-/
theorem unsafe_contract_does_not_rebind :
    ¬CrateTheorem ⟨.crate, [unrestrictedUnsafe]⟩ namedSafety := by
  intro verified
  have body := verified.2.1 0 unrestrictedUnsafe rfl
  have valid : argsValid unrestrictedUnsafe [] := by
    constructor
    · rfl
    · intro index value impossible
      cases impossible
  have required : unrestrictedUnsafe.isUnsafe = true →
      namedSafety.safety unrestrictedUnsafe.identity [] := by
    intro _
    exact True.intro
  have safe := body.2 [] valid required
  exact safe (initial unrestrictedUnsafe []) .refl .unreachable rfl

end Anneal.Mvp.Canaries
