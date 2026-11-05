import Trusted
import Mir.WireframeDemo.wire_protocol_version

namespace Obligations.WireframeDemo.wire_protocol_version

set_option linter.unusedVariables false

open Trusted.MirAst
open Trusted.MirSemantics
open Trusted.VerificationResult

/-!
Disposable verification obligations for `wireframe_demo::wire_protocol_version`.

This file is generated on every `cargo anneal` run. Do not edit it by
hand; declare an `ItemSpec` instance in `Specs.WireframeDemo.wire_protocol_version` or discharge the proof in `Proof.WireframeDemo.wire_protocol_version`.
-/

/-- Default precondition lowered automatically from Rust `#[spec]` /
    `#[external_spec]` `requires` companions for `wireframe_demo::wire_protocol_version` (or `True`
    when no companion contract is present). -/
def defaultPre (args : List Value) : Prop :=
  True

/-- Default postcondition lowered automatically from Rust `#[spec]` /
    `#[external_spec]` `ensures` companions for `wireframe_demo::wire_protocol_version` (or `True`
    when no companion contract is present). -/
def defaultPost (args : List Value) (ret : Value) : Prop :=
  True

/-- Polymorphic default precondition for `wireframe_demo::wire_protocol_version` instantiated at
    `typeArgs : Trusted.MirAst.TypeSubst`. -/
@[reducible, simp]
def defaultPreFor
    (typeArgs : Trusted.MirAst.TypeSubst)
    (args : List Value) : Prop :=
  True

/-- Polymorphic default postcondition for `wireframe_demo::wire_protocol_version` instantiated at
    `typeArgs : Trusted.MirAst.TypeSubst`. -/
@[reducible, simp]
def defaultPostFor
    (typeArgs : Trusted.MirAst.TypeSubst)
    (args : List Value)
    (ret : Value) : Prop :=
  True

/-- Trusted `requires` predicate lowered from companion `#[spec]` and
    `#[external_spec]` items for `wireframe_demo::wire_protocol_version`. -/
abbrev rustRequires : List Value → Prop := defaultPre

/-- Trusted `ensures` relation lowered from companion `#[spec]` and
    `#[external_spec]` items for `wireframe_demo::wire_protocol_version`. -/
abbrev rustEnsures : List Value → Value → Prop := defaultPost

/-- Canonical external call contract for `wireframe_demo::wire_protocol_version` lowered from
    `defaultPre` and `defaultPost` so modular callers can assume this
    callee's Rust `#[spec]` contract at `MirCallE` call sites. -/
def defaultCallContract : MirCallContract where
  pre req :=
    And (req.defPath = "wireframe_demo::wire_protocol_version") (defaultPre req.args)
  post req ans :=
    ∃ retVal,
      And (ans = .returned retVal req.memory) (defaultPost req.args retVal)

/-- Low-priority default `ItemSpec` instance for `wireframe_demo::wire_protocol_version`.
    An authored normal-priority `ItemSpec` instance in `Specs.WireframeDemo.wire_protocol_version`
    automatically overrides this instance via Lean typeclass
    synthesis. -/
instance (priority := low) defaultSpec : ItemSpec "wireframe_demo::wire_protocol_version" where
  pre := defaultPre
  post := defaultPost

/-- Signature-typed stateful precondition for `wireframe_demo::wire_protocol_version` instantiated at
    `typeArgs : Trusted.MirAst.TypeSubst`. -/
@[reducible, simp]
def sigPre
    (typeArgs : Trusted.MirAst.TypeSubst)
    (args : List Value)
    (mem : Memory) : Prop :=
  And (defaultPreFor typeArgs args)
      (Trusted.VerificationResult.argsMatchSignature
        (Mir.WireframeDemo.wire_protocol_version.body.instantiate typeArgs) args mem)

/-- Signature-typed stateful postcondition for `wireframe_demo::wire_protocol_version` instantiated at
    `typeArgs : Trusted.MirAst.TypeSubst`. -/
@[reducible, simp]
def sigPost
    (typeArgs : Trusted.MirAst.TypeSubst)
    (args : List Value)
    (ret : Value)
    (mem : Memory) : Prop :=
  And (defaultPostFor typeArgs args ret)
      (Trusted.VerificationResult.retMatchesSignature
        (Mir.WireframeDemo.wire_protocol_version.body.instantiate typeArgs) ret mem)

/-- Low-priority default `StatefulItemSpec` instance for `wireframe_demo::wire_protocol_version`. -/
instance (priority := low) defaultStatefulSpec :
    StatefulItemSpec "wireframe_demo::wire_protocol_version" where
  pre := fun args mem => sigPre List.nil args mem
  post := fun args _ ret mem => sigPost List.nil args ret mem

/-- Low-priority default `TotalItemSpec` instance for `wireframe_demo::wire_protocol_version`. -/
instance (priority := low) defaultTotalSpec :
    TotalItemSpec "wireframe_demo::wire_protocol_version" where
  pre := fun args mem =>
    And (And (defaultPre args) (mem = (initMachineState Mir.WireframeDemo.wire_protocol_version.body args).memory))
    (Trusted.VerificationResult.argsMatchSignature (Mir.WireframeDemo.wire_protocol_version.body.instantiate List.nil) args mem)
  post := fun args _ ret _ => defaultPost args ret

/-- Default transitive callee table (`s.memory.callees`) for `wireframe_demo::wire_protocol_version`,
    containing all reachable captured MIR bodies without an explicit
    `#[external_spec]` override. -/
def defaultCallees : List CapturedMir :=
  .nil

/-- Low-priority default `ModularItemSpec` instance for `wireframe_demo::wire_protocol_version`. -/
instance (priority := low) defaultModularSpec :
    ModularItemSpec "wireframe_demo::wire_protocol_version" where
  envAssumed := fun _ => True
  pre := fun args mem =>
    And (And (defaultPre args) (mem = (initMachineState Mir.WireframeDemo.wire_protocol_version.body args).memory))
    (Trusted.VerificationResult.argsMatchSignature (Mir.WireframeDemo.wire_protocol_version.body.instantiate List.nil) args mem)
  post := fun args _ ret _ => defaultPost args ret

/-- Low-priority default `UbExceptionItemSpec` instance for `wireframe_demo::wire_protocol_version`. -/
instance (priority := low) defaultUbExceptionSpec :
    UbExceptionItemSpec "wireframe_demo::wire_protocol_version" where
  pre := fun args mem => sigPre List.nil args mem
  strictSafetyPre := fun _ _ => False
  post := fun args _ ret mem => sigPost List.nil args ret mem

/-- Refine `defaultSpec` by conjoining additional Lean `extraPre` and
    `extraPost` clauses while preserving `rustRequires` and `rustEnsures`. -/
@[instance_reducible]
         def refineSpec
    (extraPre : List Value → Prop)
    (extraPost : List Value → Value → Prop) :
    ItemSpec "wireframe_demo::wire_protocol_version" where
  pre args := And (rustRequires args) (extraPre args)
  post args ret := And (rustEnsures args ret) (extraPost args ret)

/-- Refine `defaultStatefulSpec` by conjoining additional stateful Lean
    `extraPre` and `extraPost` clauses while preserving `rustRequires` and
    `rustEnsures`. -/
@[instance_reducible]
         def refineStatefulSpec
    (extraPre : List Value → Memory → Prop)
    (extraPost : List Value → Memory → Value → Memory → Prop) :
    StatefulItemSpec "wireframe_demo::wire_protocol_version" where
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
    ItemSpec "wireframe_demo::wire_protocol_version" where
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
    StatefulItemSpec "wireframe_demo::wire_protocol_version" where
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
    TotalItemSpec "wireframe_demo::wire_protocol_version" where
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
    StatefulEquivItemSpec "wireframe_demo::wire_protocol_version" where
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
    ModularItemSpec "wireframe_demo::wire_protocol_version" where
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
    UbExceptionItemSpec "wireframe_demo::wire_protocol_version" where
  pre args m := And (rustRequires args) (extraPre args m)
  strictSafetyPre := strictSafetyPre
  post args m0 ret m1 := And (rustEnsures args ret) (extraPost args m0 ret m1)

/-- Canonical verification claim for `wireframe_demo::wire_protocol_version` synthesized from
    `ItemSpec "wireframe_demo::wire_protocol_version"`. -/
def claim [spec : ItemSpec "wireframe_demo::wire_protocol_version"] : Claim :=
  { body := Mir.WireframeDemo.wire_protocol_version.body, pre := spec.pre, post := spec.post, callees := defaultCallees }

/-- Canonical stateful verification claim for `wireframe_demo::wire_protocol_version` synthesized
    from `StatefulItemSpec "wireframe_demo::wire_protocol_version"`. -/
def statefulClaim [spec : StatefulItemSpec "wireframe_demo::wire_protocol_version"] : StatefulClaim :=
  { body := Mir.WireframeDemo.wire_protocol_version.body, pre := spec.pre, post := spec.post, callees := defaultCallees }

/-- Canonical total-correctness verification claim for `wireframe_demo::wire_protocol_version` synthesized
    from `TotalItemSpec "wireframe_demo::wire_protocol_version"`. -/
def totalClaim [spec : TotalItemSpec "wireframe_demo::wire_protocol_version"] : TotalClaim :=
  { body := Mir.WireframeDemo.wire_protocol_version.body, pre := spec.pre, post := spec.post, callees := defaultCallees }

/-- Canonical program-to-program equivalence claim for `wireframe_demo::wire_protocol_version` synthesized
    from `StatefulEquivItemSpec "wireframe_demo::wire_protocol_version"`. -/
def equivClaim [spec : StatefulEquivItemSpec "wireframe_demo::wire_protocol_version"] : StatefulEquivClaim :=
  { implBody := Mir.WireframeDemo.wire_protocol_version.body, specBody := spec.specBody, pre := spec.pre, post := spec.post, implCallees := defaultCallees, specCallees := defaultCallees }

/-- Canonical modular verification claim for `wireframe_demo::wire_protocol_version` synthesized
    from `ModularItemSpec "wireframe_demo::wire_protocol_version"`. -/
def modularClaim [spec : ModularItemSpec "wireframe_demo::wire_protocol_version"] : ModularClaim :=
  { body := Mir.WireframeDemo.wire_protocol_version.body, envAssumed := spec.envAssumed, pre := spec.pre, post := spec.post, callees := defaultCallees }

/-- Canonical scoped UB-exception verification claim for `wireframe_demo::wire_protocol_version` synthesized
    from `UbExceptionItemSpec "wireframe_demo::wire_protocol_version"`. -/
def ubExceptionClaim [spec : UbExceptionItemSpec "wireframe_demo::wire_protocol_version"] : UbExceptionClaim :=
  { body := Mir.WireframeDemo.wire_protocol_version.body, pre := spec.pre, strictSafetyPre := spec.strictSafetyPre, post := spec.post, callees := defaultCallees }

/-- Verification claim for `wireframe_demo::wire_protocol_version` instantiated at `typeArgs`. -/
def claimFor
    [spec : ItemSpec "wireframe_demo::wire_protocol_version"]
    (typeArgs : Trusted.MirAst.TypeSubst) : Claim :=
  { body := Mir.WireframeDemo.wire_protocol_version.body.instantiate typeArgs
    pre := fun args =>
      And (spec.pre args)
          (Trusted.VerificationResult.argsMatchSignature
            (Mir.WireframeDemo.wire_protocol_version.body.instantiate typeArgs)
            args
            (initMachineState (Mir.WireframeDemo.wire_protocol_version.body.instantiate typeArgs) args).memory)
    post := fun args ret =>
      And (spec.post args ret)
          (Trusted.VerificationResult.retMatchesSignature
            (Mir.WireframeDemo.wire_protocol_version.body.instantiate typeArgs)
            ret
            (initMachineState (Mir.WireframeDemo.wire_protocol_version.body.instantiate typeArgs) args).memory)
    callees := defaultCallees }

/-- Universally quantified polymorphic verification proposition for `wireframe_demo::wire_protocol_version`
    over all `typeArgs : Trusted.MirAst.TypeSubst` of length
    `Mir.WireframeDemo.wire_protocol_version.body.typeParamCount`. -/
def polyClaim [spec : ItemSpec "wireframe_demo::wire_protocol_version"] : Prop :=
  ∀ (typeArgs : Trusted.MirAst.TypeSubst),
    typeArgs.length = Mir.WireframeDemo.wire_protocol_version.body.typeParamCount →
      VerificationResult (claimFor typeArgs)

/-- Stateful verification claim for `wireframe_demo::wire_protocol_version` instantiated at `typeArgs`. -/
def statefulClaimFor (typeArgs : Trusted.MirAst.TypeSubst) : StatefulClaim :=
  { body := Mir.WireframeDemo.wire_protocol_version.body.instantiate typeArgs
    pre := fun args mem => sigPre typeArgs args mem
    post := fun args _ ret mem => sigPost typeArgs args ret mem
    callees := defaultCallees }

/-- Universally quantified polymorphic stateful verification proposition for
    `wireframe_demo::wire_protocol_version` over all `typeArgs : Trusted.MirAst.TypeSubst` of length
    `Mir.WireframeDemo.wire_protocol_version.body.typeParamCount`. -/
def polyStatefulClaim : Prop :=
  ∀ (typeArgs : Trusted.MirAst.TypeSubst),
    typeArgs.length = Mir.WireframeDemo.wire_protocol_version.body.typeParamCount →
      StatefulVerificationResult (statefulClaimFor typeArgs)

/-- Total-correctness verification claim for `wireframe_demo::wire_protocol_version` instantiated at
    `typeArgs`. -/
def totalClaimFor (typeArgs : Trusted.MirAst.TypeSubst) : TotalClaim :=
  { body := Mir.WireframeDemo.wire_protocol_version.body.instantiate typeArgs
    pre := fun args mem =>
      And (And (defaultPreFor typeArgs args)
                (mem = (initMachineState (Mir.WireframeDemo.wire_protocol_version.body.instantiate typeArgs) args).memory))
          (Trusted.VerificationResult.argsMatchSignature
            (Mir.WireframeDemo.wire_protocol_version.body.instantiate typeArgs) args mem)
    post := fun args _ ret mem => sigPost typeArgs args ret mem
    callees := defaultCallees }

/-- Universally quantified polymorphic total-correctness verification
    proposition for `wireframe_demo::wire_protocol_version` over all `typeArgs : Trusted.MirAst.TypeSubst`
    of length `Mir.WireframeDemo.wire_protocol_version.body.typeParamCount`. -/
def polyTotalClaim : Prop :=
  ∀ (typeArgs : Trusted.MirAst.TypeSubst),
    typeArgs.length = Mir.WireframeDemo.wire_protocol_version.body.typeParamCount →
      TotalVerificationResult (totalClaimFor typeArgs)

/-- Modular verification claim for `wireframe_demo::wire_protocol_version` instantiated at `typeArgs`. -/
def modularClaimFor
    [spec : ModularItemSpec "wireframe_demo::wire_protocol_version"]
    (typeArgs : Trusted.MirAst.TypeSubst) : ModularClaim :=
  { body := Mir.WireframeDemo.wire_protocol_version.body.instantiate typeArgs
    envAssumed := spec.envAssumed
    pre := fun args mem => sigPre typeArgs args mem
    post := fun args _ ret m1 => sigPost typeArgs args ret m1
    callees := defaultCallees }

/-- Universally quantified polymorphic modular verification proposition for
    `wireframe_demo::wire_protocol_version` over all `typeArgs : Trusted.MirAst.TypeSubst` of length
    `Mir.WireframeDemo.wire_protocol_version.body.typeParamCount`. -/
def polyModularClaim [spec : ModularItemSpec "wireframe_demo::wire_protocol_version"] : Prop :=
  ∀ (typeArgs : Trusted.MirAst.TypeSubst),
    typeArgs.length = Mir.WireframeDemo.wire_protocol_version.body.typeParamCount →
      ModularVerificationResult (modularClaimFor typeArgs)

/-- Scoped UB-exception verification claim for `wireframe_demo::wire_protocol_version` instantiated at
    `typeArgs`. -/
def ubExceptionClaimFor
    [spec : UbExceptionItemSpec "wireframe_demo::wire_protocol_version"]
    (typeArgs : Trusted.MirAst.TypeSubst) : UbExceptionClaim :=
  { body := Mir.WireframeDemo.wire_protocol_version.body.instantiate typeArgs
    pre := fun args mem => sigPre typeArgs args mem
    strictSafetyPre := spec.strictSafetyPre
    post := fun args _ ret m1 => sigPost typeArgs args ret m1
    callees := defaultCallees }

/-- Universally quantified polymorphic UB-exception verification proposition
    for `wireframe_demo::wire_protocol_version` over all `typeArgs : Trusted.MirAst.TypeSubst` of length
    `Mir.WireframeDemo.wire_protocol_version.body.typeParamCount`. -/
def polyUbExceptionClaim [spec : UbExceptionItemSpec "wireframe_demo::wire_protocol_version"] : Prop :=
  ∀ (typeArgs : Trusted.MirAst.TypeSubst),
    typeArgs.length = Mir.WireframeDemo.wire_protocol_version.body.typeParamCount →
      UbExceptionVerificationResult (ubExceptionClaimFor typeArgs)

/-- Audited artifact identity for `wireframe_demo::wire_protocol_version`. -/
def artifactIdentity : ArtifactIdentity where
  defPath := "wireframe_demo::wire_protocol_version"
  mirDialect := "V2026_06_01"
  mirModuleSha256 := "a8db7ee2b93488797d7066b1aeaf28bd5a9c5d8832fe02e38c0f3fe7a906e0dd"

/-- Package a polymorphic item proposition `P` into a single-item
    `CrateClaim` for `Verify.WireframeDemo.wire_protocol_version.verified` auditing. -/
def polyCertificate (P : Prop) : CrateClaim where
  crateName := "wireframe_demo::wire_protocol_version"
  mirDialect := "V2026_06_01"
  items := [{ identity := artifactIdentity, certificate := P }]

end Obligations.WireframeDemo.wire_protocol_version
