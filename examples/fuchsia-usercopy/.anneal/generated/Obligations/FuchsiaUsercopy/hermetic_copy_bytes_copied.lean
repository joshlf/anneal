import Trusted
import Mir.FuchsiaUsercopy.hermetic_copy_bytes_copied
import Mir.FuchsiaUsercopy.__anodized_fn_requires_hermetic_copy_bytes_copied
import Mir.FuchsiaUsercopy.__anodized_fn_ensures_hermetic_copy_bytes_copied

namespace Obligations.FuchsiaUsercopy.hermetic_copy_bytes_copied

set_option linter.unusedVariables false

open Trusted.MirAst
open Trusted.MirSemantics
open Trusted.VerificationResult

/-!
Disposable verification obligations for `fuchsia_usercopy::hermetic_copy_bytes_copied`.

This file is generated on every `cargo anneal` run. Do not edit it by
hand; declare an `ItemSpec` instance in `Specs.FuchsiaUsercopy.hermetic_copy_bytes_copied` or discharge the proof in `Proof.FuchsiaUsercopy.hermetic_copy_bytes_copied`.

Linked specification companion items:
- Inline requires: `fuchsia_usercopy::__anodized_fn_requires_hermetic_copy_bytes_copied` (`Mir.FuchsiaUsercopy.__anodized_fn_requires_hermetic_copy_bytes_copied`)
- Inline ensures: `fuchsia_usercopy::__anodized_fn_ensures_hermetic_copy_bytes_copied` (`Mir.FuchsiaUsercopy.__anodized_fn_ensures_hermetic_copy_bytes_copied`)
-/

/-- Default precondition lowered automatically from Rust `#[spec]` /
    `#[external_spec]` `requires` companions for `fuchsia_usercopy::hermetic_copy_bytes_copied` (or `True`
    when no companion contract is present). -/
def defaultPre (args : List Value) : Prop :=
  And (Trusted.Sequence.length args = Mir.FuchsiaUsercopy.hermetic_copy_bytes_copied.body.argCount) (MirBoolPredicateHolds Mir.FuchsiaUsercopy.__anodized_fn_requires_hermetic_copy_bytes_copied.body args)

/-- Default postcondition lowered automatically from Rust `#[spec]` /
    `#[external_spec]` `ensures` companions for `fuchsia_usercopy::hermetic_copy_bytes_copied` (or `True`
    when no companion contract is present). -/
def defaultPost (args : List Value) (ret : Value) : Prop :=
  MirBoolPredicateHolds Mir.FuchsiaUsercopy.__anodized_fn_ensures_hermetic_copy_bytes_copied.body (List.append args (List.cons ret List.nil))

/-- Polymorphic default precondition for `fuchsia_usercopy::hermetic_copy_bytes_copied` instantiated at
    `typeArgs : Trusted.MirAst.TypeSubst`. -/
@[reducible, simp]
def defaultPreFor
    (typeArgs : Trusted.MirAst.TypeSubst)
    (args : List Value) : Prop :=
  And (Trusted.Sequence.length args = (Mir.FuchsiaUsercopy.hermetic_copy_bytes_copied.body.instantiate typeArgs).argCount) (MirBoolPredicateHolds (Mir.FuchsiaUsercopy.__anodized_fn_requires_hermetic_copy_bytes_copied.body.instantiate typeArgs) args)

/-- Polymorphic default postcondition for `fuchsia_usercopy::hermetic_copy_bytes_copied` instantiated at
    `typeArgs : Trusted.MirAst.TypeSubst`. -/
@[reducible, simp]
def defaultPostFor
    (typeArgs : Trusted.MirAst.TypeSubst)
    (args : List Value)
    (ret : Value) : Prop :=
  MirBoolPredicateHolds (Mir.FuchsiaUsercopy.__anodized_fn_ensures_hermetic_copy_bytes_copied.body.instantiate typeArgs) (List.append args (List.cons ret List.nil))

/-- Trusted `requires` predicate lowered from companion `#[spec]` and
    `#[external_spec]` items for `fuchsia_usercopy::hermetic_copy_bytes_copied`. -/
abbrev rustRequires : List Value → Prop := defaultPre

/-- Trusted `ensures` relation lowered from companion `#[spec]` and
    `#[external_spec]` items for `fuchsia_usercopy::hermetic_copy_bytes_copied`. -/
abbrev rustEnsures : List Value → Value → Prop := defaultPost

/-- Canonical external call contract for `fuchsia_usercopy::hermetic_copy_bytes_copied` lowered from
    `defaultPre` and `defaultPost` so modular callers can assume this
    callee's Rust `#[spec]` contract at `MirCallE` call sites. -/
def defaultCallContract : MirCallContract where
  pre req :=
    And (req.defPath = "fuchsia_usercopy::hermetic_copy_bytes_copied") (defaultPre req.args)
  post req ans :=
    ∃ retVal,
      And (ans = .returned retVal req.memory) (defaultPost req.args retVal)

/-- Low-priority default `ItemSpec` instance for `fuchsia_usercopy::hermetic_copy_bytes_copied`.
    An authored normal-priority `ItemSpec` instance in `Specs.FuchsiaUsercopy.hermetic_copy_bytes_copied`
    automatically overrides this instance via Lean typeclass
    synthesis. -/
instance (priority := low) defaultSpec : ItemSpec "fuchsia_usercopy::hermetic_copy_bytes_copied" where
  pre := defaultPre
  post := defaultPost

/-- Signature-typed stateful precondition for `fuchsia_usercopy::hermetic_copy_bytes_copied` instantiated at
    `typeArgs : Trusted.MirAst.TypeSubst`. -/
@[reducible, simp]
def sigPre
    (typeArgs : Trusted.MirAst.TypeSubst)
    (args : List Value)
    (mem : Memory) : Prop :=
  And (defaultPreFor typeArgs args)
      (Trusted.VerificationResult.argsMatchSignature
        (Mir.FuchsiaUsercopy.hermetic_copy_bytes_copied.body.instantiate typeArgs) args mem)

/-- Signature-typed stateful postcondition for `fuchsia_usercopy::hermetic_copy_bytes_copied` instantiated at
    `typeArgs : Trusted.MirAst.TypeSubst`. -/
@[reducible, simp]
def sigPost
    (typeArgs : Trusted.MirAst.TypeSubst)
    (args : List Value)
    (ret : Value)
    (mem : Memory) : Prop :=
  And (defaultPostFor typeArgs args ret)
      (Trusted.VerificationResult.retMatchesSignature
        (Mir.FuchsiaUsercopy.hermetic_copy_bytes_copied.body.instantiate typeArgs) ret mem)

/-- Low-priority default `StatefulItemSpec` instance for `fuchsia_usercopy::hermetic_copy_bytes_copied`. -/
instance (priority := low) defaultStatefulSpec :
    StatefulItemSpec "fuchsia_usercopy::hermetic_copy_bytes_copied" where
  pre := fun args mem => sigPre List.nil args mem
  post := fun args _ ret mem => sigPost List.nil args ret mem

/-- Low-priority default `TotalItemSpec` instance for `fuchsia_usercopy::hermetic_copy_bytes_copied`. -/
instance (priority := low) defaultTotalSpec :
    TotalItemSpec "fuchsia_usercopy::hermetic_copy_bytes_copied" where
  pre := fun args mem =>
    And (And (defaultPre args) (mem = (initMachineState Mir.FuchsiaUsercopy.hermetic_copy_bytes_copied.body args).memory))
    (Trusted.VerificationResult.argsMatchSignature (Mir.FuchsiaUsercopy.hermetic_copy_bytes_copied.body.instantiate List.nil) args mem)
  post := fun args _ ret _ => defaultPost args ret

/-- Default transitive callee table (`s.memory.callees`) for `fuchsia_usercopy::hermetic_copy_bytes_copied`,
    containing all reachable captured MIR bodies without an explicit
    `#[external_spec]` override. -/
def defaultCallees : List CapturedMir :=
  .nil

/-- Low-priority default `ModularItemSpec` instance for `fuchsia_usercopy::hermetic_copy_bytes_copied`. -/
instance (priority := low) defaultModularSpec :
    ModularItemSpec "fuchsia_usercopy::hermetic_copy_bytes_copied" where
  envAssumed := fun _ => True
  pre := fun args mem =>
    And (And (defaultPre args) (mem = (initMachineState Mir.FuchsiaUsercopy.hermetic_copy_bytes_copied.body args).memory))
    (Trusted.VerificationResult.argsMatchSignature (Mir.FuchsiaUsercopy.hermetic_copy_bytes_copied.body.instantiate List.nil) args mem)
  post := fun args _ ret _ => defaultPost args ret

/-- Low-priority default `UbExceptionItemSpec` instance for `fuchsia_usercopy::hermetic_copy_bytes_copied`. -/
instance (priority := low) defaultUbExceptionSpec :
    UbExceptionItemSpec "fuchsia_usercopy::hermetic_copy_bytes_copied" where
  pre := fun args mem => sigPre List.nil args mem
  strictSafetyPre := fun _ _ => False
  post := fun args _ ret mem => sigPost List.nil args ret mem

/-- Refine `defaultSpec` by conjoining additional Lean `extraPre` and
    `extraPost` clauses while preserving `rustRequires` and `rustEnsures`. -/
@[instance_reducible]
         def refineSpec
    (extraPre : List Value → Prop)
    (extraPost : List Value → Value → Prop) :
    ItemSpec "fuchsia_usercopy::hermetic_copy_bytes_copied" where
  pre args := And (rustRequires args) (extraPre args)
  post args ret := And (rustEnsures args ret) (extraPost args ret)

/-- Refine `defaultStatefulSpec` by conjoining additional stateful Lean
    `extraPre` and `extraPost` clauses while preserving `rustRequires` and
    `rustEnsures`. -/
@[instance_reducible]
         def refineStatefulSpec
    (extraPre : List Value → Memory → Prop)
    (extraPost : List Value → Memory → Value → Memory → Prop) :
    StatefulItemSpec "fuchsia_usercopy::hermetic_copy_bytes_copied" where
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
    ItemSpec "fuchsia_usercopy::hermetic_copy_bytes_copied" where
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
    StatefulItemSpec "fuchsia_usercopy::hermetic_copy_bytes_copied" where
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
    TotalItemSpec "fuchsia_usercopy::hermetic_copy_bytes_copied" where
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
    StatefulEquivItemSpec "fuchsia_usercopy::hermetic_copy_bytes_copied" where
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
    ModularItemSpec "fuchsia_usercopy::hermetic_copy_bytes_copied" where
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
    UbExceptionItemSpec "fuchsia_usercopy::hermetic_copy_bytes_copied" where
  pre args m := And (rustRequires args) (extraPre args m)
  strictSafetyPre := strictSafetyPre
  post args m0 ret m1 := And (rustEnsures args ret) (extraPost args m0 ret m1)

/-- Canonical verification claim for `fuchsia_usercopy::hermetic_copy_bytes_copied` synthesized from
    `ItemSpec "fuchsia_usercopy::hermetic_copy_bytes_copied"`. -/
def claim [spec : ItemSpec "fuchsia_usercopy::hermetic_copy_bytes_copied"] : Claim :=
  { body := Mir.FuchsiaUsercopy.hermetic_copy_bytes_copied.body, pre := spec.pre, post := spec.post, callees := defaultCallees }

/-- Canonical stateful verification claim for `fuchsia_usercopy::hermetic_copy_bytes_copied` synthesized
    from `StatefulItemSpec "fuchsia_usercopy::hermetic_copy_bytes_copied"`. -/
def statefulClaim [spec : StatefulItemSpec "fuchsia_usercopy::hermetic_copy_bytes_copied"] : StatefulClaim :=
  { body := Mir.FuchsiaUsercopy.hermetic_copy_bytes_copied.body, pre := spec.pre, post := spec.post, callees := defaultCallees }

/-- Canonical total-correctness verification claim for `fuchsia_usercopy::hermetic_copy_bytes_copied` synthesized
    from `TotalItemSpec "fuchsia_usercopy::hermetic_copy_bytes_copied"`. -/
def totalClaim [spec : TotalItemSpec "fuchsia_usercopy::hermetic_copy_bytes_copied"] : TotalClaim :=
  { body := Mir.FuchsiaUsercopy.hermetic_copy_bytes_copied.body, pre := spec.pre, post := spec.post, callees := defaultCallees }

/-- Canonical program-to-program equivalence claim for `fuchsia_usercopy::hermetic_copy_bytes_copied` synthesized
    from `StatefulEquivItemSpec "fuchsia_usercopy::hermetic_copy_bytes_copied"`. -/
def equivClaim [spec : StatefulEquivItemSpec "fuchsia_usercopy::hermetic_copy_bytes_copied"] : StatefulEquivClaim :=
  { implBody := Mir.FuchsiaUsercopy.hermetic_copy_bytes_copied.body, specBody := spec.specBody, pre := spec.pre, post := spec.post, implCallees := defaultCallees, specCallees := defaultCallees }

/-- Canonical modular verification claim for `fuchsia_usercopy::hermetic_copy_bytes_copied` synthesized
    from `ModularItemSpec "fuchsia_usercopy::hermetic_copy_bytes_copied"`. -/
def modularClaim [spec : ModularItemSpec "fuchsia_usercopy::hermetic_copy_bytes_copied"] : ModularClaim :=
  { body := Mir.FuchsiaUsercopy.hermetic_copy_bytes_copied.body, envAssumed := spec.envAssumed, pre := spec.pre, post := spec.post, callees := defaultCallees }

/-- Canonical scoped UB-exception verification claim for `fuchsia_usercopy::hermetic_copy_bytes_copied` synthesized
    from `UbExceptionItemSpec "fuchsia_usercopy::hermetic_copy_bytes_copied"`. -/
def ubExceptionClaim [spec : UbExceptionItemSpec "fuchsia_usercopy::hermetic_copy_bytes_copied"] : UbExceptionClaim :=
  { body := Mir.FuchsiaUsercopy.hermetic_copy_bytes_copied.body, pre := spec.pre, strictSafetyPre := spec.strictSafetyPre, post := spec.post, callees := defaultCallees }

/-- Verification claim for `fuchsia_usercopy::hermetic_copy_bytes_copied` instantiated at `typeArgs`. -/
def claimFor
    [spec : ItemSpec "fuchsia_usercopy::hermetic_copy_bytes_copied"]
    (typeArgs : Trusted.MirAst.TypeSubst) : Claim :=
  { body := Mir.FuchsiaUsercopy.hermetic_copy_bytes_copied.body.instantiate typeArgs
    pre := fun args =>
      And (spec.pre args)
          (Trusted.VerificationResult.argsMatchSignature
            (Mir.FuchsiaUsercopy.hermetic_copy_bytes_copied.body.instantiate typeArgs)
            args
            (initMachineState (Mir.FuchsiaUsercopy.hermetic_copy_bytes_copied.body.instantiate typeArgs) args).memory)
    post := fun args ret =>
      And (spec.post args ret)
          (Trusted.VerificationResult.retMatchesSignature
            (Mir.FuchsiaUsercopy.hermetic_copy_bytes_copied.body.instantiate typeArgs)
            ret
            (initMachineState (Mir.FuchsiaUsercopy.hermetic_copy_bytes_copied.body.instantiate typeArgs) args).memory)
    callees := defaultCallees }

/-- Universally quantified polymorphic verification proposition for `fuchsia_usercopy::hermetic_copy_bytes_copied`
    over all `typeArgs : Trusted.MirAst.TypeSubst` of length
    `Mir.FuchsiaUsercopy.hermetic_copy_bytes_copied.body.typeParamCount`. -/
def polyClaim [spec : ItemSpec "fuchsia_usercopy::hermetic_copy_bytes_copied"] : Prop :=
  ∀ (typeArgs : Trusted.MirAst.TypeSubst),
    typeArgs.length = Mir.FuchsiaUsercopy.hermetic_copy_bytes_copied.body.typeParamCount →
      VerificationResult (claimFor typeArgs)

/-- Stateful verification claim for `fuchsia_usercopy::hermetic_copy_bytes_copied` instantiated at `typeArgs`. -/
def statefulClaimFor (typeArgs : Trusted.MirAst.TypeSubst) : StatefulClaim :=
  { body := Mir.FuchsiaUsercopy.hermetic_copy_bytes_copied.body.instantiate typeArgs
    pre := fun args mem => sigPre typeArgs args mem
    post := fun args _ ret mem => sigPost typeArgs args ret mem
    callees := defaultCallees }

/-- Universally quantified polymorphic stateful verification proposition for
    `fuchsia_usercopy::hermetic_copy_bytes_copied` over all `typeArgs : Trusted.MirAst.TypeSubst` of length
    `Mir.FuchsiaUsercopy.hermetic_copy_bytes_copied.body.typeParamCount`. -/
def polyStatefulClaim : Prop :=
  ∀ (typeArgs : Trusted.MirAst.TypeSubst),
    typeArgs.length = Mir.FuchsiaUsercopy.hermetic_copy_bytes_copied.body.typeParamCount →
      StatefulVerificationResult (statefulClaimFor typeArgs)

/-- Total-correctness verification claim for `fuchsia_usercopy::hermetic_copy_bytes_copied` instantiated at
    `typeArgs`. -/
def totalClaimFor (typeArgs : Trusted.MirAst.TypeSubst) : TotalClaim :=
  { body := Mir.FuchsiaUsercopy.hermetic_copy_bytes_copied.body.instantiate typeArgs
    pre := fun args mem =>
      And (And (defaultPreFor typeArgs args)
                (mem = (initMachineState (Mir.FuchsiaUsercopy.hermetic_copy_bytes_copied.body.instantiate typeArgs) args).memory))
          (Trusted.VerificationResult.argsMatchSignature
            (Mir.FuchsiaUsercopy.hermetic_copy_bytes_copied.body.instantiate typeArgs) args mem)
    post := fun args _ ret mem => sigPost typeArgs args ret mem
    callees := defaultCallees }

/-- Universally quantified polymorphic total-correctness verification
    proposition for `fuchsia_usercopy::hermetic_copy_bytes_copied` over all `typeArgs : Trusted.MirAst.TypeSubst`
    of length `Mir.FuchsiaUsercopy.hermetic_copy_bytes_copied.body.typeParamCount`. -/
def polyTotalClaim : Prop :=
  ∀ (typeArgs : Trusted.MirAst.TypeSubst),
    typeArgs.length = Mir.FuchsiaUsercopy.hermetic_copy_bytes_copied.body.typeParamCount →
      TotalVerificationResult (totalClaimFor typeArgs)

/-- Modular verification claim for `fuchsia_usercopy::hermetic_copy_bytes_copied` instantiated at `typeArgs`. -/
def modularClaimFor
    [spec : ModularItemSpec "fuchsia_usercopy::hermetic_copy_bytes_copied"]
    (typeArgs : Trusted.MirAst.TypeSubst) : ModularClaim :=
  { body := Mir.FuchsiaUsercopy.hermetic_copy_bytes_copied.body.instantiate typeArgs
    envAssumed := spec.envAssumed
    pre := fun args mem => sigPre typeArgs args mem
    post := fun args _ ret m1 => sigPost typeArgs args ret m1
    callees := defaultCallees }

/-- Universally quantified polymorphic modular verification proposition for
    `fuchsia_usercopy::hermetic_copy_bytes_copied` over all `typeArgs : Trusted.MirAst.TypeSubst` of length
    `Mir.FuchsiaUsercopy.hermetic_copy_bytes_copied.body.typeParamCount`. -/
def polyModularClaim [spec : ModularItemSpec "fuchsia_usercopy::hermetic_copy_bytes_copied"] : Prop :=
  ∀ (typeArgs : Trusted.MirAst.TypeSubst),
    typeArgs.length = Mir.FuchsiaUsercopy.hermetic_copy_bytes_copied.body.typeParamCount →
      ModularVerificationResult (modularClaimFor typeArgs)

/-- Scoped UB-exception verification claim for `fuchsia_usercopy::hermetic_copy_bytes_copied` instantiated at
    `typeArgs`. -/
def ubExceptionClaimFor
    [spec : UbExceptionItemSpec "fuchsia_usercopy::hermetic_copy_bytes_copied"]
    (typeArgs : Trusted.MirAst.TypeSubst) : UbExceptionClaim :=
  { body := Mir.FuchsiaUsercopy.hermetic_copy_bytes_copied.body.instantiate typeArgs
    pre := fun args mem => sigPre typeArgs args mem
    strictSafetyPre := spec.strictSafetyPre
    post := fun args _ ret m1 => sigPost typeArgs args ret m1
    callees := defaultCallees }

/-- Universally quantified polymorphic UB-exception verification proposition
    for `fuchsia_usercopy::hermetic_copy_bytes_copied` over all `typeArgs : Trusted.MirAst.TypeSubst` of length
    `Mir.FuchsiaUsercopy.hermetic_copy_bytes_copied.body.typeParamCount`. -/
def polyUbExceptionClaim [spec : UbExceptionItemSpec "fuchsia_usercopy::hermetic_copy_bytes_copied"] : Prop :=
  ∀ (typeArgs : Trusted.MirAst.TypeSubst),
    typeArgs.length = Mir.FuchsiaUsercopy.hermetic_copy_bytes_copied.body.typeParamCount →
      UbExceptionVerificationResult (ubExceptionClaimFor typeArgs)

/-- Audited artifact identity for `fuchsia_usercopy::hermetic_copy_bytes_copied`. -/
def artifactIdentity : ArtifactIdentity where
  defPath := "fuchsia_usercopy::hermetic_copy_bytes_copied"
  mirDialect := "V2026_06_01"
  mirModuleSha256 := "0f1dfe1ad297e374dba6dfde9107983ed93e5c514e8102fcfabda01b83ffa64d"

/-- Package a polymorphic item proposition `P` into a single-item
    `CrateClaim` for `Verify.FuchsiaUsercopy.hermetic_copy_bytes_copied.verified` auditing. -/
def polyCertificate (P : Prop) : CrateClaim where
  crateName := "fuchsia_usercopy::hermetic_copy_bytes_copied"
  mirDialect := "V2026_06_01"
  items := [{ identity := artifactIdentity, certificate := P }]

end Obligations.FuchsiaUsercopy.hermetic_copy_bytes_copied
