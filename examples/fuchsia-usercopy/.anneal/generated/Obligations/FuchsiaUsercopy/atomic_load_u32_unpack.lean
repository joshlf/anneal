import Trusted
import Mir.FuchsiaUsercopy.atomic_load_u32_unpack
import Mir.FuchsiaUsercopy.__anodized_fn_requires_atomic_load_u32_unpack
import Mir.FuchsiaUsercopy.__anodized_fn_ensures_atomic_load_u32_unpack

namespace Obligations.FuchsiaUsercopy.atomic_load_u32_unpack

set_option linter.unusedVariables false

open Trusted.MirAst
open Trusted.MirSemantics
open Trusted.VerificationResult

/-!
Disposable verification obligations for `fuchsia_usercopy::atomic_load_u32_unpack`.

This file is generated on every `cargo anneal` run. Do not edit it by
hand; declare an `ItemSpec` instance in `Specs.FuchsiaUsercopy.atomic_load_u32_unpack` or discharge the proof in `Proof.FuchsiaUsercopy.atomic_load_u32_unpack`.

Linked specification companion items:
- Inline requires: `fuchsia_usercopy::__anodized_fn_requires_atomic_load_u32_unpack` (`Mir.FuchsiaUsercopy.__anodized_fn_requires_atomic_load_u32_unpack`)
- Inline ensures: `fuchsia_usercopy::__anodized_fn_ensures_atomic_load_u32_unpack` (`Mir.FuchsiaUsercopy.__anodized_fn_ensures_atomic_load_u32_unpack`)
-/

/-- Default precondition lowered automatically from Rust `#[spec]` /
    `#[external_spec]` `requires` companions for `fuchsia_usercopy::atomic_load_u32_unpack` (or `True`
    when no companion contract is present). -/
def defaultPre (args : List Value) : Prop :=
  And (Trusted.Sequence.length args = Mir.FuchsiaUsercopy.atomic_load_u32_unpack.body.argCount) (MirBoolPredicateHolds Mir.FuchsiaUsercopy.__anodized_fn_requires_atomic_load_u32_unpack.body args)

/-- Default postcondition lowered automatically from Rust `#[spec]` /
    `#[external_spec]` `ensures` companions for `fuchsia_usercopy::atomic_load_u32_unpack` (or `True`
    when no companion contract is present). -/
def defaultPost (args : List Value) (ret : Value) : Prop :=
  MirBoolPredicateHolds Mir.FuchsiaUsercopy.__anodized_fn_ensures_atomic_load_u32_unpack.body (List.append args (List.cons ret List.nil))

/-- Polymorphic default precondition for `fuchsia_usercopy::atomic_load_u32_unpack` instantiated at
    `typeArgs : Trusted.MirAst.TypeSubst`. -/
@[reducible, simp]
def defaultPreFor
    (typeArgs : Trusted.MirAst.TypeSubst)
    (args : List Value) : Prop :=
  And (Trusted.Sequence.length args = (Mir.FuchsiaUsercopy.atomic_load_u32_unpack.body.instantiate typeArgs).argCount) (MirBoolPredicateHolds (Mir.FuchsiaUsercopy.__anodized_fn_requires_atomic_load_u32_unpack.body.instantiate typeArgs) args)

/-- Polymorphic default postcondition for `fuchsia_usercopy::atomic_load_u32_unpack` instantiated at
    `typeArgs : Trusted.MirAst.TypeSubst`. -/
@[reducible, simp]
def defaultPostFor
    (typeArgs : Trusted.MirAst.TypeSubst)
    (args : List Value)
    (ret : Value) : Prop :=
  MirBoolPredicateHolds (Mir.FuchsiaUsercopy.__anodized_fn_ensures_atomic_load_u32_unpack.body.instantiate typeArgs) (List.append args (List.cons ret List.nil))

/-- Trusted `requires` predicate lowered from companion `#[spec]` and
    `#[external_spec]` items for `fuchsia_usercopy::atomic_load_u32_unpack`. -/
abbrev rustRequires : List Value → Prop := defaultPre

/-- Trusted `ensures` relation lowered from companion `#[spec]` and
    `#[external_spec]` items for `fuchsia_usercopy::atomic_load_u32_unpack`. -/
abbrev rustEnsures : List Value → Value → Prop := defaultPost

/-- Canonical external call contract for `fuchsia_usercopy::atomic_load_u32_unpack` lowered from
    `defaultPre` and `defaultPost` so modular callers can assume this
    callee's Rust `#[spec]` contract at `MirCallE` call sites. -/
def defaultCallContract : MirCallContract where
  pre req :=
    And (req.defPath = "fuchsia_usercopy::atomic_load_u32_unpack") (defaultPre req.args)
  post req ans :=
    ∃ retVal,
      And (ans = .returned retVal req.memory) (defaultPost req.args retVal)

/-- Low-priority default `ItemSpec` instance for `fuchsia_usercopy::atomic_load_u32_unpack`.
    An authored normal-priority `ItemSpec` instance in `Specs.FuchsiaUsercopy.atomic_load_u32_unpack`
    automatically overrides this instance via Lean typeclass
    synthesis. -/
instance (priority := low) defaultSpec : ItemSpec "fuchsia_usercopy::atomic_load_u32_unpack" where
  pre := defaultPre
  post := defaultPost

/-- Signature-typed stateful precondition for `fuchsia_usercopy::atomic_load_u32_unpack` instantiated at
    `typeArgs : Trusted.MirAst.TypeSubst`. -/
@[reducible, simp]
def sigPre
    (typeArgs : Trusted.MirAst.TypeSubst)
    (args : List Value)
    (mem : Memory) : Prop :=
  And (defaultPreFor typeArgs args)
      (Trusted.VerificationResult.argsMatchSignature
        (Mir.FuchsiaUsercopy.atomic_load_u32_unpack.body.instantiate typeArgs) args mem)

/-- Signature-typed stateful postcondition for `fuchsia_usercopy::atomic_load_u32_unpack` instantiated at
    `typeArgs : Trusted.MirAst.TypeSubst`. -/
@[reducible, simp]
def sigPost
    (typeArgs : Trusted.MirAst.TypeSubst)
    (args : List Value)
    (ret : Value)
    (mem : Memory) : Prop :=
  And (defaultPostFor typeArgs args ret)
      (Trusted.VerificationResult.retMatchesSignature
        (Mir.FuchsiaUsercopy.atomic_load_u32_unpack.body.instantiate typeArgs) ret mem)

/-- Low-priority default `StatefulItemSpec` instance for `fuchsia_usercopy::atomic_load_u32_unpack`. -/
instance (priority := low) defaultStatefulSpec :
    StatefulItemSpec "fuchsia_usercopy::atomic_load_u32_unpack" where
  pre := fun args mem => sigPre List.nil args mem
  post := fun args _ ret mem => sigPost List.nil args ret mem

/-- Low-priority default `TotalItemSpec` instance for `fuchsia_usercopy::atomic_load_u32_unpack`. -/
instance (priority := low) defaultTotalSpec :
    TotalItemSpec "fuchsia_usercopy::atomic_load_u32_unpack" where
  pre := fun args mem =>
    And (And (defaultPre args) (mem = (initMachineState Mir.FuchsiaUsercopy.atomic_load_u32_unpack.body args).memory))
    (Trusted.VerificationResult.argsMatchSignature (Mir.FuchsiaUsercopy.atomic_load_u32_unpack.body.instantiate List.nil) args mem)
  post := fun args _ ret _ => defaultPost args ret

/-- Default transitive callee table (`s.memory.callees`) for `fuchsia_usercopy::atomic_load_u32_unpack`,
    containing all reachable captured MIR bodies without an explicit
    `#[external_spec]` override. -/
def defaultCallees : List CapturedMir :=
  .nil

/-- Low-priority default `ModularItemSpec` instance for `fuchsia_usercopy::atomic_load_u32_unpack`. -/
instance (priority := low) defaultModularSpec :
    ModularItemSpec "fuchsia_usercopy::atomic_load_u32_unpack" where
  envAssumed := fun _ => True
  pre := fun args mem =>
    And (And (defaultPre args) (mem = (initMachineState Mir.FuchsiaUsercopy.atomic_load_u32_unpack.body args).memory))
    (Trusted.VerificationResult.argsMatchSignature (Mir.FuchsiaUsercopy.atomic_load_u32_unpack.body.instantiate List.nil) args mem)
  post := fun args _ ret _ => defaultPost args ret

/-- Low-priority default `UbExceptionItemSpec` instance for `fuchsia_usercopy::atomic_load_u32_unpack`. -/
instance (priority := low) defaultUbExceptionSpec :
    UbExceptionItemSpec "fuchsia_usercopy::atomic_load_u32_unpack" where
  pre := fun args mem => sigPre List.nil args mem
  strictSafetyPre := fun _ _ => False
  post := fun args _ ret mem => sigPost List.nil args ret mem

/-- Refine `defaultSpec` by conjoining additional Lean `extraPre` and
    `extraPost` clauses while preserving `rustRequires` and `rustEnsures`. -/
@[instance_reducible]
         def refineSpec
    (extraPre : List Value → Prop)
    (extraPost : List Value → Value → Prop) :
    ItemSpec "fuchsia_usercopy::atomic_load_u32_unpack" where
  pre args := And (rustRequires args) (extraPre args)
  post args ret := And (rustEnsures args ret) (extraPost args ret)

/-- Refine `defaultStatefulSpec` by conjoining additional stateful Lean
    `extraPre` and `extraPost` clauses while preserving `rustRequires` and
    `rustEnsures`. -/
@[instance_reducible]
         def refineStatefulSpec
    (extraPre : List Value → Memory → Prop)
    (extraPost : List Value → Memory → Value → Memory → Prop) :
    StatefulItemSpec "fuchsia_usercopy::atomic_load_u32_unpack" where
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
    ItemSpec "fuchsia_usercopy::atomic_load_u32_unpack" where
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
    StatefulItemSpec "fuchsia_usercopy::atomic_load_u32_unpack" where
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
    TotalItemSpec "fuchsia_usercopy::atomic_load_u32_unpack" where
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
    StatefulEquivItemSpec "fuchsia_usercopy::atomic_load_u32_unpack" where
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
    ModularItemSpec "fuchsia_usercopy::atomic_load_u32_unpack" where
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
    UbExceptionItemSpec "fuchsia_usercopy::atomic_load_u32_unpack" where
  pre args m := And (rustRequires args) (extraPre args m)
  strictSafetyPre := strictSafetyPre
  post args m0 ret m1 := And (rustEnsures args ret) (extraPost args m0 ret m1)

/-- Canonical verification claim for `fuchsia_usercopy::atomic_load_u32_unpack` synthesized from
    `ItemSpec "fuchsia_usercopy::atomic_load_u32_unpack"`. -/
def claim [spec : ItemSpec "fuchsia_usercopy::atomic_load_u32_unpack"] : Claim :=
  { body := Mir.FuchsiaUsercopy.atomic_load_u32_unpack.body, pre := spec.pre, post := spec.post, callees := defaultCallees }

/-- Canonical stateful verification claim for `fuchsia_usercopy::atomic_load_u32_unpack` synthesized
    from `StatefulItemSpec "fuchsia_usercopy::atomic_load_u32_unpack"`. -/
def statefulClaim [spec : StatefulItemSpec "fuchsia_usercopy::atomic_load_u32_unpack"] : StatefulClaim :=
  { body := Mir.FuchsiaUsercopy.atomic_load_u32_unpack.body, pre := spec.pre, post := spec.post, callees := defaultCallees }

/-- Canonical total-correctness verification claim for `fuchsia_usercopy::atomic_load_u32_unpack` synthesized
    from `TotalItemSpec "fuchsia_usercopy::atomic_load_u32_unpack"`. -/
def totalClaim [spec : TotalItemSpec "fuchsia_usercopy::atomic_load_u32_unpack"] : TotalClaim :=
  { body := Mir.FuchsiaUsercopy.atomic_load_u32_unpack.body, pre := spec.pre, post := spec.post, callees := defaultCallees }

/-- Canonical program-to-program equivalence claim for `fuchsia_usercopy::atomic_load_u32_unpack` synthesized
    from `StatefulEquivItemSpec "fuchsia_usercopy::atomic_load_u32_unpack"`. -/
def equivClaim [spec : StatefulEquivItemSpec "fuchsia_usercopy::atomic_load_u32_unpack"] : StatefulEquivClaim :=
  { implBody := Mir.FuchsiaUsercopy.atomic_load_u32_unpack.body, specBody := spec.specBody, pre := spec.pre, post := spec.post, implCallees := defaultCallees, specCallees := defaultCallees }

/-- Canonical modular verification claim for `fuchsia_usercopy::atomic_load_u32_unpack` synthesized
    from `ModularItemSpec "fuchsia_usercopy::atomic_load_u32_unpack"`. -/
def modularClaim [spec : ModularItemSpec "fuchsia_usercopy::atomic_load_u32_unpack"] : ModularClaim :=
  { body := Mir.FuchsiaUsercopy.atomic_load_u32_unpack.body, envAssumed := spec.envAssumed, pre := spec.pre, post := spec.post, callees := defaultCallees }

/-- Canonical scoped UB-exception verification claim for `fuchsia_usercopy::atomic_load_u32_unpack` synthesized
    from `UbExceptionItemSpec "fuchsia_usercopy::atomic_load_u32_unpack"`. -/
def ubExceptionClaim [spec : UbExceptionItemSpec "fuchsia_usercopy::atomic_load_u32_unpack"] : UbExceptionClaim :=
  { body := Mir.FuchsiaUsercopy.atomic_load_u32_unpack.body, pre := spec.pre, strictSafetyPre := spec.strictSafetyPre, post := spec.post, callees := defaultCallees }

/-- Verification claim for `fuchsia_usercopy::atomic_load_u32_unpack` instantiated at `typeArgs`. -/
def claimFor
    [spec : ItemSpec "fuchsia_usercopy::atomic_load_u32_unpack"]
    (typeArgs : Trusted.MirAst.TypeSubst) : Claim :=
  { body := Mir.FuchsiaUsercopy.atomic_load_u32_unpack.body.instantiate typeArgs
    pre := fun args =>
      And (spec.pre args)
          (Trusted.VerificationResult.argsMatchSignature
            (Mir.FuchsiaUsercopy.atomic_load_u32_unpack.body.instantiate typeArgs)
            args
            (initMachineState (Mir.FuchsiaUsercopy.atomic_load_u32_unpack.body.instantiate typeArgs) args).memory)
    post := fun args ret =>
      And (spec.post args ret)
          (Trusted.VerificationResult.retMatchesSignature
            (Mir.FuchsiaUsercopy.atomic_load_u32_unpack.body.instantiate typeArgs)
            ret
            (initMachineState (Mir.FuchsiaUsercopy.atomic_load_u32_unpack.body.instantiate typeArgs) args).memory)
    callees := defaultCallees }

/-- Universally quantified polymorphic verification proposition for `fuchsia_usercopy::atomic_load_u32_unpack`
    over all `typeArgs : Trusted.MirAst.TypeSubst` of length
    `Mir.FuchsiaUsercopy.atomic_load_u32_unpack.body.typeParamCount`. -/
def polyClaim [spec : ItemSpec "fuchsia_usercopy::atomic_load_u32_unpack"] : Prop :=
  ∀ (typeArgs : Trusted.MirAst.TypeSubst),
    typeArgs.length = Mir.FuchsiaUsercopy.atomic_load_u32_unpack.body.typeParamCount →
      VerificationResult (claimFor typeArgs)

/-- Stateful verification claim for `fuchsia_usercopy::atomic_load_u32_unpack` instantiated at `typeArgs`. -/
def statefulClaimFor (typeArgs : Trusted.MirAst.TypeSubst) : StatefulClaim :=
  { body := Mir.FuchsiaUsercopy.atomic_load_u32_unpack.body.instantiate typeArgs
    pre := fun args mem => sigPre typeArgs args mem
    post := fun args _ ret mem => sigPost typeArgs args ret mem
    callees := defaultCallees }

/-- Universally quantified polymorphic stateful verification proposition for
    `fuchsia_usercopy::atomic_load_u32_unpack` over all `typeArgs : Trusted.MirAst.TypeSubst` of length
    `Mir.FuchsiaUsercopy.atomic_load_u32_unpack.body.typeParamCount`. -/
def polyStatefulClaim : Prop :=
  ∀ (typeArgs : Trusted.MirAst.TypeSubst),
    typeArgs.length = Mir.FuchsiaUsercopy.atomic_load_u32_unpack.body.typeParamCount →
      StatefulVerificationResult (statefulClaimFor typeArgs)

/-- Total-correctness verification claim for `fuchsia_usercopy::atomic_load_u32_unpack` instantiated at
    `typeArgs`. -/
def totalClaimFor (typeArgs : Trusted.MirAst.TypeSubst) : TotalClaim :=
  { body := Mir.FuchsiaUsercopy.atomic_load_u32_unpack.body.instantiate typeArgs
    pre := fun args mem =>
      And (And (defaultPreFor typeArgs args)
                (mem = (initMachineState (Mir.FuchsiaUsercopy.atomic_load_u32_unpack.body.instantiate typeArgs) args).memory))
          (Trusted.VerificationResult.argsMatchSignature
            (Mir.FuchsiaUsercopy.atomic_load_u32_unpack.body.instantiate typeArgs) args mem)
    post := fun args _ ret mem => sigPost typeArgs args ret mem
    callees := defaultCallees }

/-- Universally quantified polymorphic total-correctness verification
    proposition for `fuchsia_usercopy::atomic_load_u32_unpack` over all `typeArgs : Trusted.MirAst.TypeSubst`
    of length `Mir.FuchsiaUsercopy.atomic_load_u32_unpack.body.typeParamCount`. -/
def polyTotalClaim : Prop :=
  ∀ (typeArgs : Trusted.MirAst.TypeSubst),
    typeArgs.length = Mir.FuchsiaUsercopy.atomic_load_u32_unpack.body.typeParamCount →
      TotalVerificationResult (totalClaimFor typeArgs)

/-- Modular verification claim for `fuchsia_usercopy::atomic_load_u32_unpack` instantiated at `typeArgs`. -/
def modularClaimFor
    [spec : ModularItemSpec "fuchsia_usercopy::atomic_load_u32_unpack"]
    (typeArgs : Trusted.MirAst.TypeSubst) : ModularClaim :=
  { body := Mir.FuchsiaUsercopy.atomic_load_u32_unpack.body.instantiate typeArgs
    envAssumed := spec.envAssumed
    pre := fun args mem => sigPre typeArgs args mem
    post := fun args _ ret m1 => sigPost typeArgs args ret m1
    callees := defaultCallees }

/-- Universally quantified polymorphic modular verification proposition for
    `fuchsia_usercopy::atomic_load_u32_unpack` over all `typeArgs : Trusted.MirAst.TypeSubst` of length
    `Mir.FuchsiaUsercopy.atomic_load_u32_unpack.body.typeParamCount`. -/
def polyModularClaim [spec : ModularItemSpec "fuchsia_usercopy::atomic_load_u32_unpack"] : Prop :=
  ∀ (typeArgs : Trusted.MirAst.TypeSubst),
    typeArgs.length = Mir.FuchsiaUsercopy.atomic_load_u32_unpack.body.typeParamCount →
      ModularVerificationResult (modularClaimFor typeArgs)

/-- Scoped UB-exception verification claim for `fuchsia_usercopy::atomic_load_u32_unpack` instantiated at
    `typeArgs`. -/
def ubExceptionClaimFor
    [spec : UbExceptionItemSpec "fuchsia_usercopy::atomic_load_u32_unpack"]
    (typeArgs : Trusted.MirAst.TypeSubst) : UbExceptionClaim :=
  { body := Mir.FuchsiaUsercopy.atomic_load_u32_unpack.body.instantiate typeArgs
    pre := fun args mem => sigPre typeArgs args mem
    strictSafetyPre := spec.strictSafetyPre
    post := fun args _ ret m1 => sigPost typeArgs args ret m1
    callees := defaultCallees }

/-- Universally quantified polymorphic UB-exception verification proposition
    for `fuchsia_usercopy::atomic_load_u32_unpack` over all `typeArgs : Trusted.MirAst.TypeSubst` of length
    `Mir.FuchsiaUsercopy.atomic_load_u32_unpack.body.typeParamCount`. -/
def polyUbExceptionClaim [spec : UbExceptionItemSpec "fuchsia_usercopy::atomic_load_u32_unpack"] : Prop :=
  ∀ (typeArgs : Trusted.MirAst.TypeSubst),
    typeArgs.length = Mir.FuchsiaUsercopy.atomic_load_u32_unpack.body.typeParamCount →
      UbExceptionVerificationResult (ubExceptionClaimFor typeArgs)

/-- Audited artifact identity for `fuchsia_usercopy::atomic_load_u32_unpack`. -/
def artifactIdentity : ArtifactIdentity where
  defPath := "fuchsia_usercopy::atomic_load_u32_unpack"
  mirDialect := "V2026_06_01"
  mirModuleSha256 := "6bd09bd4b438c72708fd720556651681ecffef2bf9c600d2fbafa7f0df7b5f7a"

/-- Package a polymorphic item proposition `P` into a single-item
    `CrateClaim` for `Verify.FuchsiaUsercopy.atomic_load_u32_unpack.verified` auditing. -/
def polyCertificate (P : Prop) : CrateClaim where
  crateName := "fuchsia_usercopy::atomic_load_u32_unpack"
  mirDialect := "V2026_06_01"
  items := [{ identity := artifactIdentity, certificate := P }]

end Obligations.FuchsiaUsercopy.atomic_load_u32_unpack
