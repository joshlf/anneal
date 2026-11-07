import Trusted
import Mir.FrameTutor.advance_offset

namespace Obligations.FrameTutor.advance_offset

set_option linter.unusedVariables false

open Trusted.MirAst
open Trusted.MirSemantics
open Trusted.VerificationResult

/-!
Disposable verification obligations for `frame_tutor::advance_offset`.

This file is generated on every `cargo anneal` run. Do not edit it by
hand; declare an `ItemSpec` instance in `Specs.FrameTutor.advance_offset` or discharge the proof in `Proof.FrameTutor.advance_offset`.
-/

/-- Default precondition lowered automatically from Rust `#[spec]` /
    `#[external_spec]` `requires` companions for `frame_tutor::advance_offset` (or `True`
    when no companion contract is present). -/
def defaultPre (args : List Value) : Prop :=
  True

/-- Default postcondition lowered automatically from Rust `#[spec]` /
    `#[external_spec]` `ensures` companions for `frame_tutor::advance_offset` (or `True`
    when no companion contract is present). -/
def defaultPost (args : List Value) (ret : Value) : Prop :=
  True

/-- Trusted `requires` predicate lowered from companion `#[spec]` and
    `#[external_spec]` items for `frame_tutor::advance_offset`. -/
abbrev rustRequires : List Value → Prop := defaultPre

/-- Trusted `ensures` relation lowered from companion `#[spec]` and
    `#[external_spec]` items for `frame_tutor::advance_offset`. -/
abbrev rustEnsures : List Value → Value → Prop := defaultPost

/-- Canonical external call contract for `frame_tutor::advance_offset` lowered from
    `defaultPre` and `defaultPost` so modular callers can assume this
    callee's Rust `#[spec]` contract at `MirCallE` call sites. -/
def defaultCallContract : MirCallContract where
  pre req :=
    And (req.defPath = "frame_tutor::advance_offset") (defaultPre req.args)
  post req ans :=
    ∃ retVal,
      And (ans = .returned retVal req.memory) (defaultPost req.args retVal)

/-- Low-priority default `ItemSpec` instance for `frame_tutor::advance_offset`.
    An authored normal-priority `ItemSpec` instance in `Specs.FrameTutor.advance_offset`
    automatically overrides this instance via Lean typeclass
    synthesis. -/
instance (priority := low) defaultSpec : ItemSpec "frame_tutor::advance_offset" where
  pre := defaultPre
  post := defaultPost

/-- Low-priority default `StatefulItemSpec` instance for `frame_tutor::advance_offset`. -/
instance (priority := low) defaultStatefulSpec :
    StatefulItemSpec "frame_tutor::advance_offset" where
  pre := fun args _ => defaultPre args
  post := fun args _ ret _ => defaultPost args ret

/-- Low-priority default `TotalItemSpec` instance for `frame_tutor::advance_offset`. -/
instance (priority := low) defaultTotalSpec :
    TotalItemSpec "frame_tutor::advance_offset" where
  pre := fun args mem =>
    And (defaultPre args) (mem = (initMachineState Mir.FrameTutor.advance_offset.body args).memory)
  post := fun args _ ret _ => defaultPost args ret

/-- Low-priority default `ModularItemSpec` instance for `frame_tutor::advance_offset`. -/
instance (priority := low) defaultModularSpec :
    ModularItemSpec "frame_tutor::advance_offset" where
  envAssumed := fun _ => True
  pre := fun args mem =>
    And (defaultPre args) (mem = (initMachineState Mir.FrameTutor.advance_offset.body args).memory)
  post := fun args _ ret _ => defaultPost args ret

/-- Low-priority default `UbExceptionItemSpec` instance for `frame_tutor::advance_offset`. -/
instance (priority := low) defaultUbExceptionSpec :
    UbExceptionItemSpec "frame_tutor::advance_offset" where
  pre := fun args _ => defaultPre args
  strictSafetyPre := fun _ _ => False
  post := fun args _ ret _ => defaultPost args ret

/-- Refine `defaultSpec` by conjoining additional Lean `extraPre` and
    `extraPost` clauses while preserving `rustRequires` and `rustEnsures`. -/
@[instance_reducible]
         def refineSpec
    (extraPre : List Value → Prop)
    (extraPost : List Value → Value → Prop) :
    ItemSpec "frame_tutor::advance_offset" where
  pre args := And (rustRequires args) (extraPre args)
  post args ret := And (rustEnsures args ret) (extraPost args ret)

/-- Refine `defaultStatefulSpec` by conjoining additional stateful Lean
    `extraPre` and `extraPost` clauses while preserving `rustRequires` and
    `rustEnsures`. -/
@[instance_reducible]
         def refineStatefulSpec
    (extraPre : List Value → Memory → Prop)
    (extraPost : List Value → Memory → Value → Memory → Prop) :
    StatefulItemSpec "frame_tutor::advance_offset" where
  pre args m := And (rustRequires args) (extraPre args m)
  post args m0 ret m1 := And (rustEnsures args ret) (extraPost args m0 ret m1)

/-- Refine `defaultSpec` for a safe function whose execution is defined
    (`MirNoUB`, `.defined` of `Partial`) across `safetyDomain` while guarding
    `rustEnsures` and `extraPost` behind `rustRequires` and `extraPre` inside
    `.val` (`#125`). -/
@[instance_reducible]
         def refineSafeSpec
    (safetyDomain : List Value → Prop)
    (extraPre : List Value → Prop)
    (extraPost : List Value → Value → Prop) :
    ItemSpec "frame_tutor::advance_offset" where
  pre args := safetyDomain args
  post args ret :=
    And (rustRequires args) (extraPre args) →
      And (rustEnsures args ret) (extraPost args ret)

/-- Refine `defaultStatefulSpec` for a safe stateful function whose execution
    is defined (`MirNoUB`, `.defined` of `Partial`) across `safetyDomain`
    while guarding `rustEnsures` and `extraPost` behind `rustRequires` and
    `extraPre` inside `.val` (`#125`). -/
@[instance_reducible]
         def refineSafeStatefulSpec
    (safetyDomain : List Value → Memory → Prop)
    (extraPre : List Value → Memory → Prop)
    (extraPost : List Value → Memory → Value → Memory → Prop) :
    StatefulItemSpec "frame_tutor::advance_offset" where
  pre args m := safetyDomain args m
  post args m0 ret m1 :=
    And (rustRequires args) (extraPre args m0) →
      And (rustEnsures args ret) (extraPost args m0 ret m1)

/-- Refine `defaultTotalSpec` by conjoining additional stateful Lean
    `extraPre` and `extraPost` clauses while preserving `rustRequires` and
    `rustEnsures`. -/
@[instance_reducible]
         def refineTotalSpec
    (extraPre : List Value → Memory → Prop)
    (extraPost : List Value → Memory → Value → Memory → Prop) :
    TotalItemSpec "frame_tutor::advance_offset" where
  pre args m := And (rustRequires args) (extraPre args m)
  post args m0 ret m1 := And (rustEnsures args ret) (extraPost args m0 ret m1)

/-- Specify program-to-program behavioral equivalence and total correctness
    against reference `specBody` while preserving `rustRequires` and
    `rustEnsures`. -/
@[instance_reducible]
         def refineEquivSpec
    (specBody : CapturedMir)
    (extraPre : List Value → Memory → Prop)
    (extraPost : List Value → Memory → Value → Memory → Prop) :
    StatefulEquivItemSpec "frame_tutor::advance_offset" where
  specBody := specBody
  pre args m := And (rustRequires args) (extraPre args m)
  post args m0 ret m1 := And (rustEnsures args ret) (extraPost args m0 ret m1)

/-- Refine `defaultModularSpec` by supplying `envAssumed` and conjoining
    additional stateful Lean `extraPre` and `extraPost` clauses while
    preserving `rustRequires` and `rustEnsures`. -/
@[instance_reducible]
         def refineModularSpec
    (envAssumed : ExternalCallHandler → Prop)
    (extraPre : List Value → Memory → Prop)
    (extraPost : List Value → Memory → Value → Memory → Prop) :
    ModularItemSpec "frame_tutor::advance_offset" where
  envAssumed := envAssumed
  pre args m := And (rustRequires args) (extraPre args m)
  post args m0 ret m1 := And (rustEnsures args ret) (extraPost args m0 ret m1)

/-- Refine `defaultUbExceptionSpec` by supplying the strict-safety subdomain
    `strictSafetyPre` and conjoining additional stateful Lean `extraPre` and
    `extraPost` clauses while preserving `rustRequires` and `rustEnsures`. -/
@[instance_reducible]
         def refineUbExceptionSpec
    (strictSafetyPre : List Value → Memory → Prop)
    (extraPre : List Value → Memory → Prop)
    (extraPost : List Value → Memory → Value → Memory → Prop) :
    UbExceptionItemSpec "frame_tutor::advance_offset" where
  pre args m := And (rustRequires args) (extraPre args m)
  strictSafetyPre := strictSafetyPre
  post args m0 ret m1 := And (rustEnsures args ret) (extraPost args m0 ret m1)

/-- Canonical verification claim for `frame_tutor::advance_offset` synthesized from
    `ItemSpec "frame_tutor::advance_offset"`. -/
def claim [spec : ItemSpec "frame_tutor::advance_offset"] : Claim :=
  { body := Mir.FrameTutor.advance_offset.body, pre := spec.pre, post := spec.post }

/-- Canonical stateful verification claim for `frame_tutor::advance_offset` synthesized
    from `StatefulItemSpec "frame_tutor::advance_offset"`. -/
def statefulClaim [spec : StatefulItemSpec "frame_tutor::advance_offset"] : StatefulClaim :=
  { body := Mir.FrameTutor.advance_offset.body, pre := spec.pre, post := spec.post }

/-- Canonical total-correctness verification claim for `frame_tutor::advance_offset` synthesized
    from `TotalItemSpec "frame_tutor::advance_offset"`. -/
def totalClaim [spec : TotalItemSpec "frame_tutor::advance_offset"] : TotalClaim :=
  { body := Mir.FrameTutor.advance_offset.body, pre := spec.pre, post := spec.post }

/-- Canonical program-to-program equivalence claim for `frame_tutor::advance_offset` synthesized
    from `StatefulEquivItemSpec "frame_tutor::advance_offset"`. -/
def equivClaim [spec : StatefulEquivItemSpec "frame_tutor::advance_offset"] : StatefulEquivClaim :=
  { implBody := Mir.FrameTutor.advance_offset.body, specBody := spec.specBody, pre := spec.pre, post := spec.post }

/-- Canonical modular verification claim for `frame_tutor::advance_offset` synthesized
    from `ModularItemSpec "frame_tutor::advance_offset"`. -/
def modularClaim [spec : ModularItemSpec "frame_tutor::advance_offset"] : ModularClaim :=
  { body := Mir.FrameTutor.advance_offset.body, envAssumed := spec.envAssumed, pre := spec.pre, post := spec.post }

/-- Canonical scoped UB-exception verification claim for `frame_tutor::advance_offset` synthesized
    from `UbExceptionItemSpec "frame_tutor::advance_offset"`. -/
def ubExceptionClaim [spec : UbExceptionItemSpec "frame_tutor::advance_offset"] : UbExceptionClaim :=
  { body := Mir.FrameTutor.advance_offset.body, pre := spec.pre, strictSafetyPre := spec.strictSafetyPre, post := spec.post }

end Obligations.FrameTutor.advance_offset
