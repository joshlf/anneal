import Trusted
import Mir.FrameTutor.magic_version

namespace Obligations.FrameTutor.magic_version

set_option linter.unusedVariables false

open Trusted.MirAst
open Trusted.MirSemantics
open Trusted.VerificationResult

/-!
Disposable verification obligations for `frame_tutor::magic_version`.

This file is generated on every `cargo anneal` run. Do not edit it by
hand; declare an `ItemSpec` instance in `Specs.FrameTutor.magic_version` or discharge the proof in `Proof.FrameTutor.magic_version`.
-/

/-- Default precondition lowered automatically from Rust `#[spec]` /
    `#[external_spec]` `requires` companions for `frame_tutor::magic_version` (or `True`
    when no companion contract is present). -/
def defaultPre (args : List Value) : Prop :=
  True

/-- Default postcondition lowered automatically from Rust `#[spec]` /
    `#[external_spec]` `ensures` companions for `frame_tutor::magic_version` (or `True`
    when no companion contract is present). -/
def defaultPost (args : List Value) (ret : Value) : Prop :=
  True

/-- Trusted `requires` predicate lowered from companion `#[spec]` and
    `#[external_spec]` items for `frame_tutor::magic_version`. -/
abbrev rustRequires : List Value → Prop := defaultPre

/-- Trusted `ensures` relation lowered from companion `#[spec]` and
    `#[external_spec]` items for `frame_tutor::magic_version`. -/
abbrev rustEnsures : List Value → Value → Prop := defaultPost

/-- Canonical external call contract for `frame_tutor::magic_version` lowered from
    `defaultPre` and `defaultPost` so modular callers can assume this
    callee's Rust `#[spec]` contract at `MirCallE` call sites. -/
def defaultCallContract : MirCallContract where
  pre req :=
    And (req.defPath = "frame_tutor::magic_version") (defaultPre req.args)
  post req ans :=
    ∃ retVal,
      And (ans = .returned retVal req.memory) (defaultPost req.args retVal)

/-- Low-priority default `ItemSpec` instance for `frame_tutor::magic_version`.
    An authored normal-priority `ItemSpec` instance in `Specs.FrameTutor.magic_version`
    automatically overrides this instance via Lean typeclass
    synthesis. -/
instance (priority := low) defaultSpec : ItemSpec "frame_tutor::magic_version" where
  pre := defaultPre
  post := defaultPost

/-- Low-priority default `StatefulItemSpec` instance for `frame_tutor::magic_version`. -/
instance (priority := low) defaultStatefulSpec :
    StatefulItemSpec "frame_tutor::magic_version" where
  pre := fun args _ => defaultPre args
  post := fun args _ ret _ => defaultPost args ret

/-- Low-priority default `TotalItemSpec` instance for `frame_tutor::magic_version`. -/
instance (priority := low) defaultTotalSpec :
    TotalItemSpec "frame_tutor::magic_version" where
  pre := fun args mem =>
    And (defaultPre args) (mem = (initMachineState Mir.FrameTutor.magic_version.body args).memory)
  post := fun args _ ret _ => defaultPost args ret

/-- Low-priority default `ModularItemSpec` instance for `frame_tutor::magic_version`. -/
instance (priority := low) defaultModularSpec :
    ModularItemSpec "frame_tutor::magic_version" where
  envAssumed := fun _ => True
  pre := fun args mem =>
    And (defaultPre args) (mem = (initMachineState Mir.FrameTutor.magic_version.body args).memory)
  post := fun args _ ret _ => defaultPost args ret

/-- Low-priority default `UbExceptionItemSpec` instance for `frame_tutor::magic_version`. -/
instance (priority := low) defaultUbExceptionSpec :
    UbExceptionItemSpec "frame_tutor::magic_version" where
  pre := fun args _ => defaultPre args
  strictSafetyPre := fun _ _ => False
  post := fun args _ ret _ => defaultPost args ret

/-- Refine `defaultSpec` by conjoining additional Lean `extraPre` and
    `extraPost` clauses while preserving `rustRequires` and `rustEnsures`. -/
@[instance_reducible]
         def refineSpec
    (extraPre : List Value → Prop)
    (extraPost : List Value → Value → Prop) :
    ItemSpec "frame_tutor::magic_version" where
  pre args := And (rustRequires args) (extraPre args)
  post args ret := And (rustEnsures args ret) (extraPost args ret)

/-- Refine `defaultStatefulSpec` by conjoining additional stateful Lean
    `extraPre` and `extraPost` clauses while preserving `rustRequires` and
    `rustEnsures`. -/
@[instance_reducible]
         def refineStatefulSpec
    (extraPre : List Value → Memory → Prop)
    (extraPost : List Value → Memory → Value → Memory → Prop) :
    StatefulItemSpec "frame_tutor::magic_version" where
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
    ItemSpec "frame_tutor::magic_version" where
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
    StatefulItemSpec "frame_tutor::magic_version" where
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
    TotalItemSpec "frame_tutor::magic_version" where
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
    StatefulEquivItemSpec "frame_tutor::magic_version" where
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
    ModularItemSpec "frame_tutor::magic_version" where
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
    UbExceptionItemSpec "frame_tutor::magic_version" where
  pre args m := And (rustRequires args) (extraPre args m)
  strictSafetyPre := strictSafetyPre
  post args m0 ret m1 := And (rustEnsures args ret) (extraPost args m0 ret m1)

/-- Canonical verification claim for `frame_tutor::magic_version` synthesized from
    `ItemSpec "frame_tutor::magic_version"`. -/
def claim [spec : ItemSpec "frame_tutor::magic_version"] : Claim :=
  { body := Mir.FrameTutor.magic_version.body, pre := spec.pre, post := spec.post }

/-- Canonical stateful verification claim for `frame_tutor::magic_version` synthesized
    from `StatefulItemSpec "frame_tutor::magic_version"`. -/
def statefulClaim [spec : StatefulItemSpec "frame_tutor::magic_version"] : StatefulClaim :=
  { body := Mir.FrameTutor.magic_version.body, pre := spec.pre, post := spec.post }

/-- Canonical total-correctness verification claim for `frame_tutor::magic_version` synthesized
    from `TotalItemSpec "frame_tutor::magic_version"`. -/
def totalClaim [spec : TotalItemSpec "frame_tutor::magic_version"] : TotalClaim :=
  { body := Mir.FrameTutor.magic_version.body, pre := spec.pre, post := spec.post }

/-- Canonical program-to-program equivalence claim for `frame_tutor::magic_version` synthesized
    from `StatefulEquivItemSpec "frame_tutor::magic_version"`. -/
def equivClaim [spec : StatefulEquivItemSpec "frame_tutor::magic_version"] : StatefulEquivClaim :=
  { implBody := Mir.FrameTutor.magic_version.body, specBody := spec.specBody, pre := spec.pre, post := spec.post }

/-- Canonical modular verification claim for `frame_tutor::magic_version` synthesized
    from `ModularItemSpec "frame_tutor::magic_version"`. -/
def modularClaim [spec : ModularItemSpec "frame_tutor::magic_version"] : ModularClaim :=
  { body := Mir.FrameTutor.magic_version.body, envAssumed := spec.envAssumed, pre := spec.pre, post := spec.post }

/-- Canonical scoped UB-exception verification claim for `frame_tutor::magic_version` synthesized
    from `UbExceptionItemSpec "frame_tutor::magic_version"`. -/
def ubExceptionClaim [spec : UbExceptionItemSpec "frame_tutor::magic_version"] : UbExceptionClaim :=
  { body := Mir.FrameTutor.magic_version.body, pre := spec.pre, strictSafetyPre := spec.strictSafetyPre, post := spec.post }

end Obligations.FrameTutor.magic_version
