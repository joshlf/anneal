-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import Anneal.OleanSpecStrengthAuditor

/-!
# Tests for the V1–V4 audit models of `Anneal.OleanSpecStrengthAuditor` (§8–§11)

1. **V1** (§1): strict `_private.<mod>.0.<user>` de-mangling, reserved-root and foreign-module
   spoofing, the closed realized-auxiliary allowlist, and positive controls.
2. **V2** (§2): the unreferenced top-level axiom that reachability-only auditing misses, live
   second-stage axioms, foundational re-declarations, foreign `Assumptions.*` axioms, transitive
   imports, and clean foundational positive controls.
3. **V3** (§3): prefix-confusion and symlinked paths, and one hand-built compacted region mutated
   into every rejected shape (truncation, forged tag, non-zero reference count, short root,
   out-of-bounds array / big integer, zero-size scalar array, unterminated string, self-loop,
   three-node cycle), plus valid acyclic and 96-byte empty-delta positive controls.
4. **V4** (§4): the structural-sharing ban across imports, kernel terms, LCNF, IR, and native
   symbols; IR-only and forged `ctorIdx` compiler hooks; phase-return consistency; and the
   non-blocking `leanprover/lean4#14896` readiness scanner (positive and negative).
5. **Axiom pins** (§5): `#print axioms` on every theorem of §8–§11, each at most
   `[propext, Quot.sound]`.
-/

namespace Anneal.OleanShadowAndOverrideAuditTests

open Anneal.OleanSpecStrengthAuditor

/-! ## 1. V1 — private-name de-mangling and namespace spoofing -/

/-- `_private.<pre>.0.<post>` with arbitrary raw components after the separator. -/
def rawPrivate (pre : List String) (post : AuditName) : AuditName :=
  .str "_private" :: (AuditName.ofStrings pre ++ .num 0 :: post)

/-- Loaded world: audited modules `M`, `Other`, `Trusted.Core`; `Other` owns a private helper with
its first two equation lemmas, a matcher, and a proof realized downstream. -/
def v1Env : PrivateAuditEnv where
  loadedModules := [["M"], ["Other"], ["Trusted"], ["Trusted", "Core"], ["Init", "Prelude"]]
  toolchainModules := [["Init", "Prelude"]]
  toolchainNames := [["Nat", "add"]]
  compilerReservedNames := [["lcUnreachable"], ["Eq", "rec"]]
  decls := [
    { name := mkPrivateName ["Other"] ["helper"], kind := .defnDecl, origin := ["Other"] },
    { name := mkPrivateName ["Other"] ["helper", "eq_1"], kind := .thmDecl, origin := ["M"] },
    { name := mkPrivateName ["Other"] ["helper", "proof_1"], kind := .thmDecl, origin := ["M"] },
    { name := mkPrivateName ["Other"] ["opq"], kind := .opaqueDecl, origin := ["Other"] }]

/-- Verdict for `n` of kind `k` stored by module `M`. -/
def inM (n : AuditName) (k : DeclKindModel) (evidence : Bool := true) : PrivateVerdict :=
  checkPrivateNameModel v1Env
    { declaringMod := ["M"], name := n, kind := some k, shapeEvidence := evidence }

-- Strict shape: positive controls.
example : parseStrictPrivateName (mkPrivateName ["M"] ["Outside", "helper"]) =
    some ⟨["M"], ["Outside", "helper"]⟩ := by decide
example : parseStrictPrivateName (mkPrivateName ["Trusted", "Core"] ["x"]) =
    some ⟨["Trusted", "Core"], ["x"]⟩ := by decide
example : parseStrictPrivateName (mkPrivateName ["M"] ["Outside", "helper"]) =
    some ⟨["M"], ["Outside", "helper"]⟩ :=
  parseStrictPrivate_roundtrip ["M"] ["Outside", "helper"] (by decide) (by decide) (by decide)
    (by decide)

-- Strict shape: every malformed variant fails to de-mangle.
example : parseStrictPrivateName
    (rawPrivate ["M"] [.str "Innocent", .num 0, .str "Trusted", .str "foo"]) = none := by decide
example : parseStrictPrivateName
    (rawPrivate ["M"] [.str "Innocent", .num 0, .str "Trusted", .str "foo"]) = none :=
  parseStrictPrivate_rejects_embedded_num ["M"] [.str "Innocent"] 0 [.str "Trusted", .str "foo"]
example : parseStrictPrivateName (rawPrivate ["M"] [.str "x", .num 7]) = none := by decide
example : parseStrictPrivateName (rawPrivate ["M"] [.str "_private", .str "nest"]) = none := by
  decide
example : parseStrictPrivateName (rawPrivate ["M"] [.str "_private", .str "nest"]) = none :=
  parseStrictPrivate_rejects_nested ["M"] [.str "_private", .str "nest"] (by decide)
example : parseStrictPrivateName (rawPrivate ["M"] [.str "_private.Evil"]) = none := by decide
example : parseStrictPrivateName (rawPrivate ["M"] [.str "a._private.b"]) = none := by decide
example : parseStrictPrivateName (rawPrivate ["M"] [.num 0, .str "dbl"]) = none := by decide
example : parseStrictPrivateName (rawPrivate ["M"] []) = none := by decide
example : parseStrictPrivateName (rawPrivate [] [.str "x"]) = none := by decide
example : parseStrictPrivateName (rawPrivate ["a/b"] [.str "x"]) = none := by decide
example : parseStrictPrivateName (rawPrivate [".."] [.str "x"]) = none := by decide
example : parseStrictPrivateName [.str "_private", .str "M", .num 1, .str "nonzero"] = none := by
  decide
example : parseStrictPrivateName [.str "_private", .str "M", .str "helper"] = none := by decide
example : parseStrictPrivateName [.str "_private", .num 0, .str "x"] = none := by decide
example : parseStrictPrivateName [.str "Lead", .str "_private", .str "M", .num 0, .str "x"] =
    none := by decide
example : parseStrictPrivateName [.str "Lead", .str "_private", .str "M", .num 0, .str "x"] =
    none :=
  parseStrictPrivate_rejects_nonleading _ _ (by decide)
example : parseStrictPrivateName [.num 0, .str "_private", .str "M", .num 0, .str "x"] = none := by
  decide
example : parseStrictPrivateName [] = none := by decide

-- A malformed name that mentions the marker is a violation, not "not private".
example : inM (rawPrivate ["M"] [.str "Innocent", .num 0, .str "Trusted", .str "foo"]) .defnDecl =
    .malformedShape := by decide
example : inM [.str "Lead", .str "_private", .str "nonlead"] .defnDecl = .malformedShape := by
  decide
example : inM (rawPrivate ["M"] [.str "_private", .str "nest"]) .defnDecl = .malformedShape := by
  decide
example : inM [.str "a._private.b"] .defnDecl = .malformedShape := by decide

-- `_private.Trusted.0.fake` stored by `M`: never accepted, as a definition, axiom, or with the
-- claimed module unloaded.
example : inM (mkPrivateName ["Trusted"] ["fake"]) .defnDecl = .foreignOutsideRealizedAux := by
  decide
example : inM (mkPrivateName ["Trusted"] ["fake"]) .axiomDecl = .foreignAxiomOrOpaque := by decide
example : inM (mkPrivateName ["Ghost"] ["fake"]) .defnDecl = .unloadedModule := by decide

-- `_private.M.0.Trusted.foo`: reserved domain root claimed from a foreign-root module.
example : inM (mkPrivateName ["M"] ["Trusted", "foo"]) .defnDecl = .reservedUserSpoof := by decide
example : inM (mkPrivateName ["M"] ["Trusted", "foo"]) .defnDecl = .reservedUserSpoof :=
  checkPrivateName_rejects_reserved_user_spoof v1Env _ ⟨["M"], ["Trusted", "foo"]⟩ (by decide)
    (by decide)
    (privateUserForbidden_reserved_domain_root v1Env ["M"] "Trusted" ["foo"] (by decide)
      (by decide))
example : inM (mkPrivateName ["M"] ["Assumptions", "ax"]) .axiomDecl = .reservedUserSpoof := by
  decide
example : inM (mkPrivateName ["M"] ["Verify", "claim"]) .thmDecl = .reservedUserSpoof := by decide
example : inM (mkPrivateName ["M"] ["sorryAx"]) .defnDecl = .reservedUserSpoof := by decide
example : inM (mkPrivateName ["M"] ["Init", "x"]) .defnDecl = .reservedUserSpoof := by decide
example : inM (mkPrivateName ["M"] ["Lean", "Elab", "x"]) .defnDecl = .reservedUserSpoof := by
  decide
example : inM (mkPrivateName ["M"] ["Classical", "choice"]) .axiomDecl = .reservedUserSpoof := by
  decide
example : inM (mkPrivateName ["M"] ["ShareCommon", "x"]) .defnDecl = .reservedUserSpoof := by
  decide
example : inM (mkPrivateName ["M"] ["wrap", "StateFactoryBuilder"]) .defnDecl =
    .reservedUserSpoof := by decide
example : inM (mkPrivateName ["M"] ["Nat", "add"]) .defnDecl = .reservedUserSpoof := by decide
-- Positive control: the same domain root is legitimate inside a module of that root.
example : checkPrivateNameModel v1Env
    { declaringMod := ["Trusted", "Core"],
      name := mkPrivateName ["Trusted", "Core"] ["Trusted", "foo"], kind := some .defnDecl } =
    .accepted := by decide

-- Foreign private axioms and opaque constants are refused whatever their suffix.
example : inM (mkPrivateName ["Other"] ["cheat"]) .axiomDecl = .foreignAxiomOrOpaque := by decide
example : inM (mkPrivateName ["Other"] ["helper", "eq_1"]) .axiomDecl = .foreignAxiomOrOpaque := by
  decide
example : inM (mkPrivateName ["Other"] ["helper", "match_1"]) .opaqueDecl =
    .foreignAxiomOrOpaque := by decide
example : (inM (mkPrivateName ["Other"] ["cheat"]) .axiomDecl).isRejection = true :=
  checkPrivateName_rejects_foreign_axiom v1Env _ ⟨["Other"], ["cheat"]⟩ (by decide) (by decide)
    (by decide) (Or.inl rfl)

-- Phantom `eq_999` (no `eq_998`), `eq_0`, phantom `match_999` as a non-definition, a base the
-- claimed module does not own, missing kernel evidence, and an IR-only foreign symbol.
example : inM (mkPrivateName ["Other"] ["helper", "eq_999"]) .thmDecl =
    .foreignOutsideRealizedAux := by decide
example : inM (mkPrivateName ["Other"] ["helper", "eq_0"]) .thmDecl =
    .foreignOutsideRealizedAux := by decide
example : inM (mkPrivateName ["Other"] ["helper", "eq_3"]) .thmDecl =
    .foreignOutsideRealizedAux := by decide
example : inM (mkPrivateName ["Other"] ["helper", "proof_999"]) .thmDecl =
    .foreignOutsideRealizedAux := by decide
example : inM (mkPrivateName ["Other"] ["helper", "match_999"]) .thmDecl =
    .foreignOutsideRealizedAux := by decide
example : inM (mkPrivateName ["Other"] ["helper", "eq_1"]) .defnDecl =
    .foreignOutsideRealizedAux := by decide
example : inM (mkPrivateName ["Other"] ["ghost", "eq_1"]) .thmDecl =
    .foreignOutsideRealizedAux := by decide
example : inM (mkPrivateName ["Other"] ["opq", "eq_1"]) .thmDecl =
    .foreignOutsideRealizedAux := by decide
example : inM (mkPrivateName ["Other"] ["helper", "eq_1"]) .thmDecl (evidence := false) =
    .foreignOutsideRealizedAux := by decide
example : inM (mkPrivateName ["Other"] ["helper", "eq_1x"]) .thmDecl =
    .foreignOutsideRealizedAux := by decide
example : inM (mkPrivateName ["Other"] ["helper", "spoof"]) .defnDecl =
    .foreignOutsideRealizedAux := by decide
example : checkPrivateNameModel v1Env
    { declaringMod := ["M"], name := mkPrivateName ["Other"] ["helper", "eq_1"], kind := none } =
    .foreignOutsideRealizedAux := by decide

-- Positive controls: a same-module helper and genuine realized auxiliaries of a foreign helper.
example : inM (mkPrivateName ["M"] ["Outside", "helper"]) .defnDecl = .accepted := by decide
example : inM (mkPrivateName ["M"] ["Outside", "helper"]) .defnDecl = .accepted :=
  checkPrivateName_accepts_same_module_helper v1Env _ ⟨["M"], ["Outside", "helper"]⟩ (by decide)
    (by decide) (by decide) (by decide)
example : inM (mkPrivateName ["M"] ["localAx"]) .axiomDecl = .accepted := by decide
example : inM (mkPrivateName ["Other"] ["helper", "eq_1"]) .thmDecl = .accepted := by decide
example : inM (mkPrivateName ["Other"] ["helper", "eq_2"]) .thmDecl = .accepted := by decide
example : inM (mkPrivateName ["Other"] ["helper", "eq_def"]) .thmDecl = .accepted := by decide
example : inM (mkPrivateName ["Other"] ["helper", "match_1"]) .defnDecl = .accepted := by decide
example : inM (mkPrivateName ["Other"] ["helper", "proof_1"]) .thmDecl = .accepted := by decide
example : inM (mkPrivateName ["Other"] ["helper", "proof_2"]) .thmDecl = .accepted := by decide
example : inM (mkPrivateName ["Other"] ["helper", "_sparseCasesOn_3"]) .defnDecl = .accepted := by
  decide

-- Names outside the check: no marker, or stored by a pinned toolchain module.
example : inM (AuditName.ofStrings ["Outside", "helper"]) .defnDecl = .notPrivate := by decide
example : checkPrivateNameModel v1Env
    { declaringMod := ["Init", "Prelude"],
      name := mkPrivateName ["Init", "Prelude"] ["Init", "x"], kind := some .defnDecl } =
    .notPrivate := by decide

-- Acceptance soundness instantiated: the accepted foreign `eq_1` is a non-axiom realized auxiliary.
example : ∃ r, parseStrictPrivateName (mkPrivateName ["Other"] ["helper", "eq_1"]) = some r ∧
    privateUserForbiddenModel v1Env r.moduleSegs r.userComps = false :=
  let ⟨r, hp, _, hf, _⟩ := checkPrivateName_accepted_sound v1Env
    { declaringMod := ["M"], name := mkPrivateName ["Other"] ["helper", "eq_1"],
      kind := some .thmDecl } (by decide)
  ⟨r, hp, hf⟩

-- Batch summary: 6 names carry the marker, 4 of them are violations, in input order.
example : auditPrivateNamesModel v1Env [
    { declaringMod := ["M"], name := AuditName.ofStrings ["pub"], kind := some .defnDecl },
    { declaringMod := ["M"], name := mkPrivateName ["M"] ["helper"], kind := some .defnDecl },
    { declaringMod := ["M"], name := mkPrivateName ["Trusted"] ["fake"], kind := some .defnDecl },
    { declaringMod := ["M"], name := mkPrivateName ["M"] ["Trusted", "foo"],
      kind := some .defnDecl },
    { declaringMod := ["M"], name := mkPrivateName ["Other"] ["helper", "eq_999"],
      kind := some .thmDecl },
    { declaringMod := ["M"], name := mkPrivateName ["Other"] ["helper", "eq_1"],
      kind := some .thmDecl },
    { declaringMod := ["M"], name := mkPrivateName ["Other"] ["cheat"], kind := some .axiomDecl }] =
    { privateNamesAudited := 6,
      violations := [mkPrivateName ["Trusted"] ["fake"], mkPrivateName ["M"] ["Trusted", "foo"],
        mkPrivateName ["Other"] ["helper", "eq_999"], mkPrivateName ["Other"] ["cheat"]] } := by
  decide

-- Realized-auxiliary suffix classification is exact (no trailing junk, at least one digit).
example : classifyRealizedAuxSuffix "eq_12" = some (.eqn 12) := by decide
example : classifyRealizedAuxSuffix "match_1" = some (.matcher 1) := by decide
example : classifyRealizedAuxSuffix "eq_def" = some .eqDef := by decide
example : classifyRealizedAuxSuffix "proof_7" = some (.proof 7) := by decide
example : classifyRealizedAuxSuffix "_sparseCasesOn_2" = some (.sparseCasesOn 2) := by decide
example : classifyRealizedAuxSuffix "eq_" = none := by decide
example : classifyRealizedAuxSuffix "eq_01" = none := by decide
example : classifyRealizedAuxSuffix "match_001" = none := by decide
example : classifyRealizedAuxSuffix "proof_01" = none := by decide
example : classifyRealizedAuxSuffix "eq_1a" = none := by decide
example : classifyRealizedAuxSuffix "xeq_1" = none := by decide
example : classifyRealizedAuxSuffix "helper" = none := by decide
-- Compiler-reserved name spoofing inside a private user suffix.
example : inM (mkPrivateName ["M"] ["lcUnreachable"]) .defnDecl = .reservedUserSpoof := by decide
example : inM (mkPrivateName ["M"] ["lcUnreachable"]) .defnDecl = .reservedUserSpoof :=
  checkPrivateName_rejects_reserved_user_spoof v1Env _ ⟨["M"], ["lcUnreachable"]⟩ (by decide)
    (by decide) (privateUserForbidden_compiler_reserved v1Env ["M"] "lcUnreachable" [] (by decide))
-- Leading-zero sibling `eq_01` cannot authorize `eq_2`.
example : checkPrivateNameModel
    { v1Env with decls := [
        { name := mkPrivateName ["Other"] ["helper"], kind := .defnDecl, origin := ["Other"] },
        { name := mkPrivateName ["Other"] ["helper", "eq_01"], kind := .thmDecl, origin := ["M"] }] }
    { declaringMod := ["M"], name := mkPrivateName ["Other"] ["helper", "eq_2"],
      kind := some .thmDecl } = .foreignOutsideRealizedAux := by decide
-- IR `_at_` specialization names: valid positive control vs forged `Trusted` site and foreign final site.
example : checkIRAtSpecModel v1Env ["M"]
    (mkPrivateName ["Init", "Prelude"] ["Array", "fold"] ++
      [.str "_at_", .str "M", .str "pubFn", .str "spec_0"]) = true := by decide
example : checkIRAtSpecModel v1Env ["M"]
    (mkPrivateName ["Init", "Prelude"] ["Array", "fold"] ++
      [.str "_at_", .str "Trusted", .str "forged_site", .str "spec_0"]) = false :=
  checkIRAtSpec_rejects_forged_site v1Env ["M"] _
    (mkPrivateName ["Init", "Prelude"] ["Array", "fold"]) []
    [.str "Trusted", .str "forged_site", .str "spec_0"] ["Trusted", "forged_site"] 1
    (by decide) (by decide) (by decide)
    (privateUserForbidden_reserved_domain_root v1Env ["M"] "Trusted" ["forged_site"] (by decide)
      (by decide))
example : checkIRAtSpecModel v1Env ["M"]
    (mkPrivateName ["Init", "Prelude"] ["Array", "fold"] ++
      [.str "_at_"] ++ mkPrivateName ["Other"] ["site", "spec_0"]) = false := by decide
example : checkIRAtSpecModel v1Env ["M"]
    (mkPrivateName ["Init", "Prelude"] ["Array", "fold"] ++
      [.str "_at_", .str "M", .str "noSpec"]) = false := by decide

/-! ## 2. V2 — whole-module unreferenced axiom sweep -/

/-- A clean stored declaration of module `M`. -/
def declM (kind : DeclKindModel) (name : String) (deps : List String := []) : DeclEntryModel :=
  { kind := kind, name := name, declaringMod := "M", originMod := "M", deps := deps }

/-- A foundational axiom stored by the pinned toolchain. -/
def toolchainAxiom (name : String) (choice : Bool := false) : DeclEntryModel :=
  { kind := .axiomDecl, name := name, declaringMod := "Init.Core", originMod := "Init.Core",
    isFoundational := true, isToolchainMod := true, isClassicalChoice := choice }

-- The unreferenced `axiom unused_cheat : False`: reachability-only auditing reports nothing; the
-- sweep reports it and counts it.
example : reachabilityOnlyAxioms false unusedCheatInventory ["claim"] = [] := by decide
example : (wholeModuleAxiomSweep false unusedCheatInventory).violations = ["unused_cheat"] := by
  decide
example : (wholeModuleAxiomSweep false unusedCheatInventory).sweptAxioms = 1 := by decide
example : (wholeModuleAxiomSweep false unusedCheatInventory).ok = false := by decide
example : "unused_cheat" ∈ (wholeModuleAxiomSweep false unusedCheatInventory).violations :=
  wholeModuleAxiomSweep_complete false unusedCheatInventory (declM .axiomDecl "unused_cheat")
    (by decide) rfl (by decide)

/-- The same axiom, but referenced by the claim. -/
def usedCheatInventory : ModuleInventoryModel where
  constants := [declM .axiomDecl "used_cheat", declM .defnDecl "helper" ["used_cheat"],
    declM .thmDecl "claim" ["helper"]]

-- Once referenced (transitively), reachability-only auditing reports it too; both policies agree.
example : reachabilityOnlyAxioms false usedCheatInventory ["claim"] = ["used_cheat"] := by decide
example : (wholeModuleAxiomSweep false usedCheatInventory).violations = ["used_cheat"] := by decide
example : reachabilityOnlyAxioms false usedCheatInventory ["helper"] = ["used_cheat"] := by decide
example : reachabilityOnlyAxioms false usedCheatInventory [] = [] := by decide

/-- Adversarial inventory: a live second-stage axiom, a `propext` re-declaration and a foreign
`Assumptions.*` axiom inside a file-local test-axiom module, a masked re-declaration, an
unreferenced axiom of a transitive import, a legitimate file-local test axiom, and clean
toolchain foundational axioms. -/
def adversarialInventory : ModuleInventoryModel where
  constants := [
    declM .thmDecl "claim",
    { kind := .axiomDecl, name := "propext", declaringMod := "T", originMod := "T",
      isLocalAxiomMod := true, isFoundational := true },
    { kind := .axiomDecl, name := "Assumptions.Other.ax", declaringMod := "T", originMod := "T",
      isLocalAxiomMod := true, isAssumptionsPrefix := true },
    { kind := .axiomDecl, name := "masked", declaringMod := "T", originMod := "Elsewhere",
      isLocalAxiomMod := true },
    { kind := .axiomDecl, name := "test_ax", declaringMod := "T", originMod := "T",
      isLocalAxiomMod := true }]
  stage2 := [
    { kind := .axiomDecl, name := "live_stage2_ax", declaringMod := "T", originMod := "T",
      isLocalAxiomMod := true },
    declM .defnDecl "live_stage2_def"]
  transitiveDeps := [
    { kind := .axiomDecl, name := "dep_cheat", declaringMod := "Dep", originMod := "Dep" },
    { kind := .defnDecl, name := "dep_def", declaringMod := "Dep", originMod := "Dep" },
    toolchainAxiom "propext", toolchainAxiom "Quot.sound", toolchainAxiom "Classical.choice" true]

-- Exactly the five adversarial axioms are reported under the classical policy; the file-local
-- `test_ax`, the second-stage definition, and the toolchain axioms are not.
example : (wholeModuleAxiomSweep true adversarialInventory).violations =
    ["propext", "Assumptions.Other.ax", "masked", "live_stage2_ax", "dep_cheat"] := by decide
example : (wholeModuleAxiomSweep true adversarialInventory).sweptAxioms = 9 := by decide
-- Under the constructive policy the toolchain `Classical.choice` is additionally reported.
example : (wholeModuleAxiomSweep false adversarialInventory).violations =
    ["propext", "Assumptions.Other.ax", "masked", "live_stage2_ax", "dep_cheat",
      "Classical.choice"] := by decide
-- None of them is referenced by the claim: reachability-only auditing reports nothing.
example : reachabilityOnlyAxioms true adversarialInventory ["claim"] = [] := by decide

-- The general theorems instantiated on the adversarial entries.
example : "propext" ∈ (wholeModuleAxiomSweep true adversarialInventory).violations :=
  wholeModuleAxiomSweep_rejects_foundational_redecl true adversarialInventory
    { kind := .axiomDecl, name := "propext", declaringMod := "T", originMod := "T",
      isLocalAxiomMod := true, isFoundational := true } (by decide) rfl rfl rfl
example : "Assumptions.Other.ax" ∈ (wholeModuleAxiomSweep true adversarialInventory).violations :=
  wholeModuleAxiomSweep_rejects_foreign_assumptions true adversarialInventory
    { kind := .axiomDecl, name := "Assumptions.Other.ax", declaringMod := "T", originMod := "T",
      isLocalAxiomMod := true, isAssumptionsPrefix := true } (by decide) rfl rfl rfl rfl
example : "live_stage2_ax" ∈ (wholeModuleAxiomSweep true adversarialInventory).violations :=
  wholeModuleAxiomSweep_flags_stage2_axiom true adversarialInventory
    { kind := .axiomDecl, name := "live_stage2_ax", declaringMod := "T", originMod := "T",
      isLocalAxiomMod := true } (by decide) rfl
example : "masked" ∈ (wholeModuleAxiomSweep true adversarialInventory).violations :=
  wholeModuleAxiomSweep_rejects_masked_redecl true adversarialInventory
    { kind := .axiomDecl, name := "masked", declaringMod := "T", originMod := "Elsewhere",
      isLocalAxiomMod := true } (by decide) rfl (by decide)
-- `sorryAx` and native-evaluation axioms are rejected even inside `localAxiomModules`.
def localSorryAndNativeInventory : ModuleInventoryModel where
  constants := [
    { kind := .axiomDecl, name := "sorryAx", declaringMod := "T", originMod := "T",
      isLocalAxiomMod := true, isSorry := true },
    { kind := .axiomDecl, name := "_native.ax_0", declaringMod := "T", originMod := "T",
      isLocalAxiomMod := true, isNative := true }]

example : (wholeModuleAxiomSweep true localSorryAndNativeInventory).violations =
    ["sorryAx", "_native.ax_0"] := by decide
example : "sorryAx" ∈ (wholeModuleAxiomSweep true localSorryAndNativeInventory).violations :=
  wholeModuleAxiomSweep_rejects_sorry_in_local_mod true localSorryAndNativeInventory
    { kind := .axiomDecl, name := "sorryAx", declaringMod := "T", originMod := "T",
      isLocalAxiomMod := true, isSorry := true } (by decide) rfl rfl
example : "_native.ax_0" ∈ (wholeModuleAxiomSweep true localSorryAndNativeInventory).violations :=
  wholeModuleAxiomSweep_rejects_native_in_local_mod true localSorryAndNativeInventory
    { kind := .axiomDecl, name := "_native.ax_0", declaringMod := "T", originMod := "T",
      isLocalAxiomMod := true, isNative := true } (by decide) rfl rfl

/-- Positive control: toolchain foundational axioms, a file-local test axiom, and an
`Assumptions.*` axiom inside an `Assumptions.*` test module. -/
def cleanInventory : ModuleInventoryModel where
  constants := [
    declM .thmDecl "claim" ["helper"], declM .defnDecl "helper",
    { kind := .axiomDecl, name := "test_ax", declaringMod := "T", originMod := "T",
      isLocalAxiomMod := true },
    { kind := .axiomDecl, name := "Assumptions.T.ax", declaringMod := "Assumptions.T",
      originMod := "Assumptions.T", isLocalAxiomMod := true, isAssumptionsPrefix := true,
      inAssumptionsMod := true }]
  transitiveDeps := [toolchainAxiom "propext", toolchainAxiom "Quot.sound"]

example : wholeModuleAxiomSweep false cleanInventory = { sweptAxioms := 4, violations := [] } := by
  decide
example : (wholeModuleAxiomSweep false cleanInventory).ok = true := by decide
example : ∀ e, e ∈ cleanInventory.allEntries → e.kind = .axiomDecl →
    AxiomEntryAuthorized false e :=
  (wholeModuleAxiomSweep_ok_sound false cleanInventory (by decide)).1
-- The same test axiom outside a file-local test-axiom module is a violation.
example : (wholeModuleAxiomSweep false
    { constants :=
        [{ kind := .axiomDecl, name := "test_ax", declaringMod := "T", originMod := "T" }] }).violations = ["test_ax"] := by decide
-- Toolchain modules may not declare non-foundational axioms either.
example : (wholeModuleAxiomSweep true
    { constants := [],
      transitiveDeps := [
        { kind := .axiomDecl, name := "Lean.trustMe", declaringMod := "Lean", originMod := "Lean",
          isToolchainMod := true }] }).violations =
    ["Lean.trustMe"] := by decide

/-! ## 3. V3 — root containment and compacted-region bounds -/

/-- Path of plain (non-symlink) components. -/
def plainPath (names : List String) : List PathCompModel := names.map (⟨·, false⟩)

-- Prefix confusion: the string-prefix test accepts the sibling, the component test rejects it.
example : naivePrefixWithinModel "/tmp/root" "/tmp/root_evil/Evil.olean" = true := by decide
example : pathWithinRootModel (plainPath ["tmp", "root"])
    (plainPath ["tmp", "root_evil", "Evil.olean"]) = false := by decide
example : pathWithinRootModel (plainPath ["tmp", "root"])
    (plainPath ["tmp", "root_evil", "Evil.olean"]) = false :=
  pathWithinRoot_rejects_prefix_confusion (plainPath ["tmp"]) ⟨"root", false⟩
    ⟨"root_evil", false⟩ (plainPath ["Evil.olean"]) (by decide)
-- `..` traversal, a symlinked ancestor, a symlinked artifact, a symlinked root, an unrelated
-- directory, and the parent of the root.
example : pathWithinRootModel (plainPath ["tmp", "root"])
    (plainPath ["tmp", "root", "..", "root_evil", "Evil.olean"]) = false := by decide
example : pathWithinRootModel (plainPath ["tmp", "root"])
    [⟨"tmp", false⟩, ⟨"root", false⟩, ⟨"link", true⟩, ⟨"M.olean", false⟩] = false := by decide
example : pathWithinRootModel (plainPath ["tmp", "root"])
    [⟨"tmp", false⟩, ⟨"root", false⟩, ⟨"M.olean", true⟩] = false := by decide
example : pathWithinRootModel [⟨"tmp", false⟩, ⟨"root", true⟩]
    (plainPath ["tmp", "root", "M.olean"]) = false := by decide
example : pathWithinRootModel (plainPath ["tmp", "root"]) (plainPath ["var", "root", "M.olean"]) =
    false := by decide
example : pathWithinRootModel (plainPath ["tmp", "root"]) (plainPath ["tmp"]) = false := by decide
example : pathWithinRootModel (plainPath ["tmp", "root"])
    (plainPath ["tmp", "root", "sub/evil"]) = false := by decide
-- Positive controls: a nested artifact and the root itself.
example : pathWithinRootModel (plainPath ["tmp", "root"])
    (plainPath ["tmp", "root", "Sub", "M.olean"]) = true := by decide
example : pathWithinRootModel (plainPath ["tmp", "root"]) (plainPath ["tmp", "root"]) = true := by
  decide

-- Tag classification.
example : CompactedTag.ofByte? 0 = some (.ctor 0) := by decide
example : CompactedTag.ofByte? 243 = some (.ctor 243) := by decide
example : CompactedTag.ofByte? 246 = some .array := by decide
example : CompactedTag.ofByte? 248 = some .scalarArray := by decide
example : CompactedTag.ofByte? 249 = some .string := by decide
example : CompactedTag.ofByte? 250 = some .mpz := by decide
example : [244, 245, 247, 251, 252, 253, 254, 255].map CompactedTag.ofByte? =
    [none, none, none, none, none, none, none, none] := by decide

/-- Mapping address of the test region. -/
def rb : Nat := 4096

/-- A big integer with two limbs stored right behind its header. -/
def mpzObj : CompactedObjModel :=
  { off := 96, tag := 250, size := 1, capacity := 2, dataPtr := rb + 120 }
/-- A one-character string with its NUL terminator. -/
def strObj : CompactedObjModel := { off := 136, tag := 249, size := 2, capacity := 2, strLen := 1 }
/-- A four-byte scalar array. -/
def sarrObj : CompactedObjModel := { off := 176, tag := 248, other := 1, size := 4, capacity := 4 }
/-- An `Import`-like constructor pointing down at the string, big integer, and scalar array. -/
def impObj : CompactedObjModel :=
  { off := 208, tag := 0, other := 3, csSz := 32, fields := [rb + 136, rb + 96, rb + 176] }
/-- The `imports` array holding the constructor. -/
def arr0 : CompactedObjModel :=
  { off := 240, tag := 246, size := 1, capacity := 1, fields := [rb + 208] }
/-- An empty array at `off`. -/
def emptyArr (off : Nat) : CompactedObjModel := { off := off, tag := 246 }
/-- The 56-byte module-data root with its five array slots. -/
def rootObj : CompactedObjModel :=
  { off := 368, tag := 0, other := 5, csSz := 56,
    fields := [rb + 240, rb + 272, rb + 296, rb + 320, rb + 344] }

/-- Build a 424-byte region rooted at offset 368 from the given objects. -/
def regionOf (objs : List CompactedObjModel) (fileSize : Nat := 424) : CompactedRegionModel :=
  { header := { base := rb, rootPtr := rb + 368 }, fileSize := fileSize, objs := objs }

/-- The four empty root arrays. -/
def emptyArrs : List CompactedObjModel := [emptyArr 272, emptyArr 296, emptyArr 320, emptyArr 344]

/-- Positive control: a valid acyclic region (root → imports → Import → string / mpz / bytes). -/
def validRegion : CompactedRegionModel :=
  regionOf ([mpzObj, strObj, sarrObj, impObj, arr0] ++ emptyArrs ++ [rootObj])

/-- Replace the big integer, string, scalar array, constructor, imports array, and root. -/
def mutated (m s b i a r : CompactedObjModel) (fileSize : Nat := 424) : CompactedRegionModel :=
  regionOf ([m, s, b, i, a] ++ emptyArrs ++ [r]) fileSize

example : validateOleanRegionModel validRegion = true := by decide
example : mutated mpzObj strObj sarrObj impObj arr0 rootObj = validRegion := by decide

-- Header-level rejections: truncated below 96 bytes, bad magic/version, unaligned or zero base,
-- address overflow, oversize.
example : validateOleanRegionModel (regionOf [] 95) = false := by decide
example : validateOleanRegionModel (regionOf [] 95) = false :=
  validateOleanRegion_rejects_truncated _ (by decide)
example : validateOleanRegionModel { validRegion with fileSize := 95 } = false := by decide
example : validateOleanRegionModel
    { validRegion with header := { validRegion.header with headerOk := false } } = false := by
  decide
example : validateOleanRegionModel
    { validRegion with header := { base := rb + 4, rootPtr := rb + 368 } } = false := by decide
example : validateOleanRegionModel
    { validRegion with header := { base := 0, rootPtr := 368 } } = false := by decide
example : validateOleanRegionModel
    { header := { base := 18446744073709551608, rootPtr := 18446744073709551608 + 368 },
      fileSize := 424 } = false := by decide
example : validateOleanRegionModel { validRegion with fileSize := 268435457 } = false := by decide

-- Forged kind tag `244` (and every other non-compactable tag) on a reachable object.
example : validateOleanRegionModel
    (mutated mpzObj strObj sarrObj { impObj with tag := 244 } arr0 rootObj) = false := by decide
example : validateOleanRegionModel
    (mutated mpzObj strObj sarrObj { impObj with tag := 244 } arr0 rootObj) = false :=
  validateOleanRegion_rejects_forged_tag _ { impObj with tag := 244 } (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
example : [245, 247, 251, 252, 253, 254, 255].map (fun t => validateOleanRegionModel
    (mutated mpzObj strObj sarrObj { impObj with tag := t } arr0 rootObj)) =
    [false, false, false, false, false, false, false] := by decide

-- Non-zero reference count on an inner object and on the root.
example : validateOleanRegionModel
    (mutated mpzObj strObj sarrObj { impObj with rc := 1 } arr0 rootObj) = false := by decide
example : validateOleanRegionModel
    (mutated mpzObj strObj sarrObj { impObj with rc := 1 } arr0 rootObj) = false :=
  validateOleanRegion_rejects_nonzero_rc _ { impObj with rc := 1 } (by decide) (by decide)
example : validateOleanRegionModel
    (mutated mpzObj strObj sarrObj impObj arr0 { rootObj with rc := 1 }) = false := by decide

-- Short or misshapen root: 48 bytes, four fields, wrong tag, unaligned, past the end, a slot
-- that is not an `Array`, and an out-of-bounds slot.
example : validateOleanRegionModel
    (mutated mpzObj strObj sarrObj impObj arr0 { rootObj with csSz := 48 }) = false := by decide
example : validateOleanRegionModel
    (mutated mpzObj strObj sarrObj impObj arr0
      { rootObj with other := 4, fields := [rb + 240, rb + 272, rb + 296, rb + 320] }) = false := by
  decide
example : validateOleanRegionModel
    (mutated mpzObj strObj sarrObj impObj arr0 { rootObj with tag := 1 }) = false := by decide
example : validateOleanRegionModel
    (mutated mpzObj strObj sarrObj impObj arr0 rootObj 416) = false := by decide
example : validateOleanRegionModel
    (mutated mpzObj strObj sarrObj impObj arr0
      { rootObj with fields := [rb + 208, rb + 272, rb + 296, rb + 320, rb + 344] }) = false := by
  decide
example : validateOleanRegionModel
    (mutated mpzObj strObj sarrObj impObj arr0
      { rootObj with fields := [rb + 240, rb + 272, rb + 296, rb + 320, 4702111234474983744] }) =
    false := by decide
example : validateOleanRegionModel
    { validRegion with header := { base := rb, rootPtr := rb + 372 } } = false := by decide

-- Out-of-bounds `Array` capacity, size above capacity, and an out-of-bounds element pointer.
example : validateOleanRegionModel
    (mutated mpzObj strObj sarrObj impObj { arr0 with capacity := 1000 } rootObj) = false := by
  decide
example : validateOleanRegionModel
    (mutated mpzObj strObj sarrObj impObj { arr0 with capacity := 1000 } rootObj) = false :=
  validateOleanRegion_rejects_oob_array _ { arr0 with capacity := 1000 } (by decide) rfl
    (Or.inl (by decide))
example : validateOleanRegionModel
    (mutated mpzObj strObj sarrObj impObj
      { arr0 with size := 2, fields := [rb + 208, rb + 208] } rootObj) = false := by decide
example : validateOleanRegionModel
    (mutated mpzObj strObj sarrObj impObj { arr0 with fields := [4702111234474983744] } rootObj) =
    false := by decide
-- A two-hop constructor field pointing outside every region, and at a non-object address.
example : validateOleanRegionModel
    (mutated mpzObj strObj sarrObj
      { impObj with fields := [4702111234474983744, rb + 96, rb + 176] } arr0 rootObj) = false := by
  decide
example : validateOleanRegionModel
    (mutated mpzObj strObj sarrObj
      { impObj with fields := [rb + 144, rb + 96, rb + 176] } arr0 rootObj) = false := by decide

-- Big integer: forged limb pointer, limbs past the end, limb count above allocation.
example : validateOleanRegionModel
    (mutated { mpzObj with dataPtr := 4702111234474983744 } strObj sarrObj impObj arr0 rootObj) =
    false := by decide
example : validateOleanRegionModel
    (mutated { mpzObj with dataPtr := 4702111234474983744 } strObj sarrObj impObj arr0 rootObj) =
    false :=
  validateOleanRegion_rejects_oob_mpz _ { mpzObj with dataPtr := 4702111234474983744 } (by decide)
    rfl (by decide) (Or.inr (by decide))
example : validateOleanRegionModel
    (mutated { mpzObj with dataPtr := rb + 416 } strObj sarrObj impObj arr0 rootObj) = false := by
  decide
example : validateOleanRegionModel
    (mutated { mpzObj with dataPtr := rb + 8 } strObj sarrObj impObj arr0 rootObj) = false := by
  decide
example : validateOleanRegionModel
    (mutated { mpzObj with size := 3 } strObj sarrObj impObj arr0 rootObj) = false := by decide
-- Negative signed `int32` `_mp_alloc` (`≥ 2^31`) is rejected even if size ≤ capacity.
example : validateOleanRegionModel
    (mutated { mpzObj with capacity := 2147483648 } strObj sarrObj impObj arr0 rootObj) = false :=
  validateOleanRegion_rejects_negative_mpz_alloc _ { mpzObj with capacity := 2147483648 }
    (by decide) rfl (by decide)
-- Short root and invalid empty delta theorem instantiations.
example : validateOleanRegionModel
    (mutated mpzObj strObj sarrObj impObj arr0 { rootObj with csSz := 48 }) = false :=
  validateOleanRegion_rejects_short_root _ (by decide) (by decide)

-- Scalar array with element size `0`; string without its NUL, with zero size, and with a
-- code-point length that is not below its byte size.
example : validateOleanRegionModel
    (mutated mpzObj strObj { sarrObj with other := 0 } impObj arr0 rootObj) = false := by decide
example : validateOleanRegionModel
    (mutated mpzObj strObj { sarrObj with other := 0 } impObj arr0 rootObj) = false :=
  validateOleanRegion_rejects_zero_elem_scalarArray _ { sarrObj with other := 0 } (by decide) rfl
    rfl
example : validateOleanRegionModel
    (mutated mpzObj { strObj with strNulOk := false } sarrObj impObj arr0 rootObj) = false := by
  decide
example : validateOleanRegionModel
    (mutated mpzObj { strObj with strNulOk := false } sarrObj impObj arr0 rootObj) = false :=
  validateOleanRegion_rejects_string_without_nul _ { strObj with strNulOk := false } (by decide)
    rfl rfl
example : validateOleanRegionModel
    (mutated mpzObj { strObj with size := 0 } sarrObj impObj arr0 rootObj) = false := by decide
example : validateOleanRegionModel
    (mutated mpzObj { strObj with strLen := 2 } sarrObj impObj arr0 rootObj) = false := by decide

/-- Self-loop: the `Import` constructor's first field points at itself. -/
def selfLoopRegion : CompactedRegionModel :=
  mutated mpzObj strObj sarrObj { impObj with fields := [rb + 208, rb + 96, rb + 176] } arr0
    rootObj

/-- Three-node cycle `root → imports → Import → root`. -/
def cycle3Region : CompactedRegionModel :=
  mutated mpzObj strObj sarrObj { impObj with fields := [rb + 368, rb + 96, rb + 176] } arr0
    rootObj

example : validateOleanRegionModel selfLoopRegion = false := by decide
example : validateOleanRegionModel cycle3Region = false := by decide
-- A forward (upward) pointer that closes no cycle is rejected as well.
example : validateOleanRegionModel
    (mutated mpzObj strObj sarrObj { impObj with fields := [rb + 240, rb + 96, rb + 176] } arr0
      rootObj) = false := by decide

/-- The self-loop is a one-edge own-region cycle. -/
theorem selfLoop_path : OwnPath selfLoopRegion (rb + 208) (rb + 208) :=
  .single ⟨{ impObj with fields := [rb + 208, rb + 96, rb + 176] }, by decide, rfl, by decide,
    by decide, by decide, by decide⟩

/-- The three-node cycle is a three-edge own-region cycle through the root. -/
theorem cycle3_path : OwnPath cycle3Region (rb + 368) (rb + 368) :=
  .cons ⟨rootObj, by decide, rfl, by decide, by decide, by decide, by decide⟩
    (.cons ⟨arr0, by decide, rfl, by decide, by decide, by decide, by decide⟩
      (.single ⟨{ impObj with fields := [rb + 368, rb + 96, rb + 176] }, by decide, rfl,
        by decide, by decide, by decide, by decide⟩))

example : validateOleanRegionModel selfLoopRegion = false :=
  validateOleanRegion_rejects_cycle _ _ selfLoop_path
example : validateOleanRegionModel cycle3Region = false :=
  validateOleanRegion_rejects_cycle _ _ cycle3_path
example : validateOleanRegionModel selfLoopRegion = false :=
  validateOleanRegion_rejects_non_downward _ { impObj with fields := [rb + 208, rb + 96, rb + 176] }
    (by decide) (rb + 208) (by decide) (by decide) (by decide) (by decide)
-- The valid region has a genuine own-region path (root → imports → Import) and no cycle.
example : OwnPath validRegion (rb + 368) (rb + 208) :=
  .cons ⟨rootObj, by decide, rfl, by decide, by decide, by decide, by decide⟩
    (.single ⟨arr0, by decide, rfl, by decide, by decide, by decide, by decide⟩)
example : ∀ a, ¬ OwnPath validRegion a a := downwardPointers_no_cycle validRegion (by decide)

/-- The valid region as a validated parent layer. -/
def parentLayer : ParentLayerModel :=
  { base := rb, size := 424, rootPtr := rb + 368,
    rootKids := [rb + 240, rb + 272, rb + 296, rb + 320, rb + 344],
    reachable := [rb + 96, rb + 136, rb + 176, rb + 208, rb + 240, rb + 272, rb + 296, rb + 320,
      rb + 344, rb + 368] }

/-- Positive control: a 96-byte empty delta layer re-exporting the parent's root. -/
def emptyDelta : CompactedRegionModel :=
  { header := { base := 8192, rootPtr := rb + 368 }, fileSize := 96, parents := [parentLayer] }

example : validateOleanRegionModel emptyDelta = true := by decide
-- A delta with no parent, a wrong root, extra bytes, smuggled objects, or overlapping its parent.
example : validateOleanRegionModel { emptyDelta with parents := [] } = false := by decide
example : validateOleanRegionModel
    { emptyDelta with header := { base := 8192, rootPtr := rb + 376 } } = false := by decide
example : validateOleanRegionModel { emptyDelta with fileSize := 104 } = false := by decide
example : validateOleanRegionModel { emptyDelta with objs := [emptyArr 96] } = false := by decide
example : validateOleanRegionModel
    { emptyDelta with header := { base := rb + 200, rootPtr := rb + 368 } } = false := by decide
example : validateOleanRegionModel
    { emptyDelta with header := { base := rb + 200, rootPtr := rb + 368 } } = false :=
  validateOleanRegion_rejects_overlap _ parentLayer (by decide) (by decide) (by decide)
example : validateOleanRegionModel { emptyDelta with parents := [] } = false :=
  validateOleanRegion_rejects_bad_empty_delta _ (by decide) (Or.inl rfl)
example : validateOleanRegionModel { emptyDelta with fileSize := 104 } = false :=
  validateOleanRegion_rejects_bad_empty_delta _ (by decide) (Or.inr (by decide))

-- Separate-chain disjoint layers (`.ir` vs `.olean`): disjoint is accepted, overlapping is
-- rejected, and `.ir` cannot re-export or point into a disjoint `.olean` layer.
def irLayerClean : CompactedRegionModel :=
  { header := { base := 8192, rootPtr := 8192 + 368 }, fileSize := 424,
    objs := ([mpzObj, strObj, sarrObj, impObj, arr0] ++ emptyArrs ++ [rootObj]).map (fun o =>
      { o with
        dataPtr := if o.dataPtr ≥ rb then o.dataPtr - rb + 8192 else o.dataPtr
        fields := o.fields.map (fun f => if f ≥ rb then f - rb + 8192 else f) }),
    disjointLayers := [parentLayer] }

example : validateOleanRegionModel irLayerClean = true := by decide
example : validateOleanRegionModel
    { irLayerClean with header := { base := rb + 200, rootPtr := rb + 200 + 368 } } = false :=
  validateOleanRegion_rejects_disjoint_overlap _ parentLayer (by decide) (by decide) (by decide)
example : validateOleanRegionModel
    { header := { base := 8192, rootPtr := rb + 368 }, fileSize := 96,
      disjointLayers := [parentLayer] } = false := by decide

/-- Positive control: a non-empty upper layer whose root re-uses four parent slots and whose own
array points at a validated parent object. -/
def upperLayer : CompactedRegionModel :=
  { header := { base := 8192, rootPtr := 8192 + 128 }, fileSize := 184,
    objs := [{ off := 96, tag := 246, size := 1, capacity := 1, fields := [rb + 208] },
      { off := 128, tag := 0, other := 5, csSz := 56,
        fields := [8192 + 96, rb + 272, rb + 296, rb + 320, rb + 344] }],
    parents := [parentLayer] }

example : validateOleanRegionModel upperLayer = true := by decide
-- A parent pointer to an address the parent walk never validated, and a parent slot re-used in
-- the wrong position.
example : validateOleanRegionModel { upperLayer with
    objs := [{ off := 96, tag := 246, size := 1, capacity := 1, fields := [rb + 216] },
      { off := 128, tag := 0, other := 5, csSz := 56,
        fields := [8192 + 96, rb + 272, rb + 296, rb + 320, rb + 344] }] } = false := by decide
example : validateOleanRegionModel { upperLayer with
    objs := [{ off := 96, tag := 246, size := 1, capacity := 1, fields := [rb + 208] },
      { off := 128, tag := 0, other := 5, csSz := 56,
        fields := [8192 + 96, rb + 296, rb + 272, rb + 320, rb + 344] }] } = false := by decide
-- Boxed scalars (odd words) are not pointers and are accepted.
example : validateOleanRegionModel
    (mutated mpzObj strObj sarrObj { impObj with fields := [rb + 136, 85, rb + 176] } arr0
      rootObj) = true := by decide

/-! ## 4. V4 — structural-sharing ban, compiler hooks, and readiness scanner -/

-- Forbidden references in every layer.
example : isShareCommonRef (.directImport ["Init", "ShareCommon"]) = true := by decide
example : isShareCommonRef (.directImport ["Init", "ShareCommon", "Basic"]) = true :=
  isShareCommonRef_direct_import ["Basic"]
example : isShareCommonRef (.kernelConst ["ShareCommon", "StateFactoryBuilder"]) = true := by
  decide
example : isShareCommonRef (.kernelConst ["ShareCommon", "shareCommon'"]) = true := by decide
example : isShareCommonRef (.lcnfConst ["ShareCommon", "Object", "eq"]) = true := by decide
example : isShareCommonRef (.lcnfProj ["ShareCommon", "StateFactory"]) = true := by decide
example : isShareCommonRef (.lcnfCases ["ShareCommon", "StateFactoryBuilder"]) = true := by decide
example : isShareCommonRef (.irBody ["ShareCommon", "mkStateImpl"]) = true := by decide
example : isShareCommonRef (.kernelConst ["wrap", "StateFactoryBuilder"]) = true := by decide
example : isShareCommonRef (.externSymbol "lean_sharecommon_mk") = true := by decide
example : isShareCommonRef (.externSymbol "lean_state_sharecommon") = true := by decide
example : isShareCommonRef (.externSymbol "x_lean_sharecommon_quick") = true := by decide
-- Positive controls: `import Init` alone and ordinary references are allowed.
example : isShareCommonRef (.directImport ["Init"]) = false := by decide
example : isShareCommonRef (.directImport ["Init", "Core"]) = false := by decide
example : isShareCommonRef (.directImport ["Init", "ShareCommonX"]) = false := by decide
example : isShareCommonRef (.kernelConst ["Nat", "add"]) = false := by decide
example : isShareCommonRef (.lcnfProj ["Prod"]) = false := by decide
example : isShareCommonRef (.externSymbol "lean_io_prim_put_str") = false := by decide
example : isShareCommonRef (.externSymbol "lean_share") = false := by decide

/-- A module that imports only `Init` yet reaches the library through a kernel constant, an LCNF
projection, an LCNF `cases`, an IR body, and a native symbol. -/
def shareCommonAttack : ShareCommonAuditModel where
  refs := [.directImport ["Init"], .kernelConst ["Nat", "succ"],
    .kernelConst ["ShareCommon", "StateFactoryBuilder"], .lcnfProj ["ShareCommon", "StateFactory"],
    .lcnfCases ["ShareCommon", "Object"], .lcnfConst ["List", "map"],
    .irBody ["ShareCommon", "shareCommon'"], .externSymbol "lean_sharecommon_mk"]

example : auditShareCommonModel shareCommonAttack =
    [.kernelConst ["ShareCommon", "StateFactoryBuilder"], .lcnfProj ["ShareCommon", "StateFactory"],
      .lcnfCases ["ShareCommon", "Object"], .irBody ["ShareCommon", "shareCommon'"],
      .externSymbol "lean_sharecommon_mk"] := by decide
example : shareCommonAttack.ok = false := by decide
example : (ShareCommonAuditModel.mk [.directImport ["Init.ShareCommon"]]).ok = true := by decide
example : (ShareCommonAuditModel.mk [.directImport ["Init", "ShareCommon"]]).ok = false := by
  decide
example : (ShareCommonAuditModel.mk
    [.directImport ["Init"], .kernelConst ["Nat", "add"], .externSymbol "lean_nat_add"]).ok =
    true := by decide
example : ShareCommonRef.lcnfProj ["ShareCommon", "StateFactory"] ∈
    auditShareCommonModel shareCommonAttack :=
  auditShareCommon_complete shareCommonAttack _ (by decide) (by decide)

/-- A non-toolchain hook of `kind` on `decl`. -/
def hook (kind : CompilerHookKind) (decl : String) : CompilerHookEntry :=
  { kind := kind, decl := decl }

/-- Hooks recorded only in the `.ir` companion, a forged three-constructor `Tri.ctorIdx`, a
one-constructor `ctorIdx` with a non-literal body, a live specialization-cache entry, and a
declaration whose IR returns a different literal than its kernel term. -/
def hookAttack : CompilerHookSummary where
  oleanHooks := [
    { kind := .macroInline, decl := "Tri.ctorIdx", isCtorIdxOfLocalInductive := true,
      numCtors := 3, bodyIsRawZero := true },
    { kind := .macroInline, decl := "One.ctorIdx", isCtorIdxOfLocalInductive := true,
      numCtors := 1, bodyIsRawZero := false },
    { kind := .macroInline, decl := "notCtorIdx", numCtors := 1, bodyIsRawZero := true },
    hook .extern "ffi", hook .export "exported", hook .init "initFn",
    hook .builtinInit "builtinInitFn", hook .csimp "csimpThm", hook .cpass "pass",
    hook .folder "fold"]
  irHooks := [hook .implementedBy "irImpl", hook .unbox "UBox", hook .neverExtract "neFn",
    hook .taggedReturn "trFn"]
  specCacheEntries := ["specGhost"]
  phaseReturns := [
    { decl := "retMismatch", kernel := .natLit 0, base := .natLit 0, mono := .natLit 0,
      ir := .natLit 1 },
    { decl := "retOk", kernel := .natLit 0, base := .other, mono := .natLit 0, ir := .natLit 0 }]

example : hookAttack.violations =
    ["Tri.ctorIdx", "One.ctorIdx", "notCtorIdx", "ffi", "exported", "initFn", "builtinInitFn",
      "csimpThm", "pass", "fold", "irImpl", "UBox", "neFn", "trFn", "specGhost",
      "retMismatch"] := by decide
example : hookAttack.ok = false := by decide
example : "UBox" ∈ hookAttack.violations :=
  compilerHookSummary_flags_ir_only_hook hookAttack (hook .unbox "UBox") (by decide) rfl
    (by decide)
example : "Tri.ctorIdx" ∈ hookAttack.violations :=
  compilerHookSummary_rejects_forged_ctorIdx hookAttack
    { kind := .macroInline, decl := "Tri.ctorIdx", isCtorIdxOfLocalInductive := true,
      numCtors := 3, bodyIsRawZero := true } (by decide) rfl (Or.inl (by decide))
example : "retMismatch" ∈ hookAttack.violations :=
  compilerHookSummary_flags_phase_mismatch hookAttack
    { decl := "retMismatch", kernel := .natLit 0, base := .natLit 0, mono := .natLit 0,
      ir := .natLit 1 } (by decide) (by decide)

/-- Positive control: the genuine one-constructor raw-`0` `I.ctorIdx`, toolchain-owned hooks in
both artifacts, and consistent phase returns. -/
def hookClean : CompilerHookSummary where
  oleanHooks := [
    { kind := .macroInline, decl := "I.ctorIdx", isCtorIdxOfLocalInductive := true, numCtors := 1,
      bodyIsRawZero := true },
    { kind := .extern, decl := "Nat.add", isToolchainOwned := true }]
  irHooks := [{ kind := .implementedBy, decl := "Array.foldl", isToolchainOwned := true }]
  phaseReturns := [
    { decl := "k", kernel := .natLit 7, base := .natLit 7, mono := .natLit 7, ir := .natLit 7 },
    { decl := "c", kernel := .ctor "Bool.true", base := .other, mono := .ctor "Bool.true",
      ir := .natLit 1 },
    { decl := "p", kernel := .param 0, base := .param 0, mono := .param 1, ir := .other }]

example : hookClean.violations = [] := by decide
example : hookClean.ok = true := by decide
example : ∀ e, e ∈ hookClean.oleanHooks ++ hookClean.irHooks → HookEntryAdmitted e :=
  (compilerHookSummary_ok_sound hookClean (by decide)).1
example : ∀ p, p ∈ hookClean.phaseReturns → p.consistent = true :=
  (compilerHookSummary_ok_sound hookClean (by decide)).2.2
-- Phase-return compatibility table.
example : simpleRetCompatModel (.natLit 0) (.natLit 1) = false := by decide
example : simpleRetCompatModel (.strLit "a") (.strLit "b") = false := by decide
example : simpleRetCompatModel (.natLit 0) (.strLit "0") = false := by decide
example : simpleRetCompatModel (.param 0) (.natLit 0) = false := by decide
example : simpleRetCompatModel (.natLit 3) (.natLit 3) = true := by decide
example : simpleRetCompatModel .other (.natLit 3) = true := by decide
example : simpleRetCompatModel (.ctor "C") (.strLit "s") = true := by decide

/-- `Eq.rec (motive := fun _ _ => Nat) 7 myEq`: a theorem as the recursor's major premise. -/
def majorPremiseUse : ReadinessExpr := .recursorApp (.const "seven" false) (.const "myEq" true)

/-- The same with the major premise wrapped as `@id (1 = 1) myEq`. -/
def idWrappedUse : ReadinessExpr :=
  .recursorApp (.const "seven" false)
    (.app (.app (.const "id" false) (.const "ty" false)) (.const "myEq" true))

/-- `(andThm).1`: a theorem as a projection scrutinee. -/
def projUse : ReadinessExpr := .proj (.const "andThm" true)

/-- Theorems used only as ordinary arguments, with a recursor and projection on plain data. -/
def cleanUse : ReadinessExpr :=
  .app (.app (.const "congrArg" true) (.lam (.const "f" false)))
    (.letE (.const "someThm" true)
      (.recursorApp (.const "otherThm" true) (.proj (.const "pair" false))))

example : majorPremiseUse.flagged = true := by decide
example : idWrappedUse.flagged = true := by decide
example : projUse.flagged = true := by decide
example : (ReadinessExpr.proj (.app (.const "id" false) (.const "andThm" true))).flagged = true := by
  decide
-- Hidden under binders, `let`s, and applications, at any depth.
example : (ReadinessExpr.lam (.letE (.const "x" false)
    (.app (.const "g" false) (.lam majorPremiseUse)))).flagged = true := by decide
example : (ReadinessExpr.recursorApp projUse (.const "n" false)).flagged = true := by decide
example : (ReadinessExpr.lam majorPremiseUse).flagged = true :=
  readinessScanner_flag_propagates (.lamBody _) (by decide)
example : majorPremiseUse.flagged = true :=
  readinessScanner_flags_major_premise_theorem _ _ rfl
example : projUse.flagged = true := readinessScanner_flags_proj_scrutinee_theorem _ rfl
-- The direct head test sees the direct form but not the wrapper; the model sees both.
example : (ReadinessExpr.const "myEq" true).headIsTheorem = true := by decide
example : (ReadinessExpr.app (.app (.const "id" false) (.const "ty" false))
    (.const "myEq" true)).headIsTheorem = false := by decide
example : (ReadinessExpr.app (.app (.const "id" false) (.const "ty" false))
    (.const "myEq" true)).carriesTheorem = true := by decide
-- `let`-bound theorem placed in a recursor major premise or `.proj` scrutinee (direct or wrapped).
def letBoundRecUse : ReadinessExpr :=
  .letE (.const "myEq" true) (.recursorApp (.const "seven" false) (.bvar 0))
def letBoundWrappedRecUse : ReadinessExpr :=
  .letE (.const "myEq" true)
    (.recursorApp (.const "seven" false) (.app (.const "wrap" false) (.bvar 0)))
def letBoundProjUse : ReadinessExpr := .letE (.const "andThm" true) (.proj (.bvar 0))
def letBoundArgOnly : ReadinessExpr :=
  .letE (.const "myEq" true) (.app (.lam (.const "three" false)) (.bvar 0))

example : letBoundRecUse.flagged = true :=
  readinessScanner_flags_let_bound_theorem _ _ rfl
example : letBoundWrappedRecUse.flagged = true := by decide
example : letBoundProjUse.flagged = true :=
  readinessScanner_flags_let_bound_proj _ rfl
example : letBoundArgOnly.flagged = false := by decide
example : letBoundArgOnly.scrutineesTheoremFree = true := by decide
-- Positive control: `0` flags.
example : cleanUse.flagged = false := by decide
example : cleanUse.scrutineesTheoremFree = true := by decide
example : cleanUse.flagged = false := readinessScanner_clean_zero_flags cleanUse (by decide)
-- A theorem under a binder inside a scrutinee is a function body, not a carried proof.
example : (ReadinessExpr.proj (.lam (.const "thm" true))).flagged = false := by decide

/-- A module with two flagged declarations and two clean ones. -/
def readinessModule : List ReadinessDecl := [
  { name := "usesThmInRec", type := .const "Nat" false, value := some majorPremiseUse },
  { name := "cleanDef", type := .const "Nat" false, value := some cleanUse },
  { name := "projInType", type := projUse },
  { name := "cleanAxiom", type := .const "Prop" false }]

-- Negative: both flagged declarations are reported, and the report is not blocking.
example : scanModuleOpaqueTheoremReadiness true readinessModule =
    { scannedDecls := 4, flaggedDecls := ["usesThmInRec", "projInType"], blocking := false } := by
  decide
example : (scanModuleOpaqueTheoremReadiness true readinessModule).flagCount = 2 := by decide
example : (scanModuleOpaqueTheoremReadiness true readinessModule).isBlocking = false :=
  OpaqueTheoremReadinessSummary.isBlocking_eq_false true readinessModule
-- The audit still accepts a module with flags and no blocking violation, and still rejects one
-- with a blocking violation and no flags.
example : auditVerdictWithReadiness [] (scanModuleOpaqueTheoremReadiness true readinessModule) =
    true := by decide
example : auditVerdictWithReadiness ["unapprovedAxiom"]
    (scanModuleOpaqueTheoremReadiness true []) = false := by decide
-- Disabled: nothing scanned, `0` flags, even on the flagged module.
example : scanModuleOpaqueTheoremReadiness false readinessModule =
    { scannedDecls := 0, flaggedDecls := [], blocking := false } := by decide
example : (scanModuleOpaqueTheoremReadiness false readinessModule).flagCount = 0 :=
  readinessScanner_disabled_zero_flags readinessModule
-- Positive: a clean module reports `0` flags with the check enabled.
example : (scanModuleOpaqueTheoremReadiness true
    [{ name := "cleanDef", type := .const "Nat" false, value := some cleanUse }]).flagCount = 0 := by
  decide

/-- `accWrap accZero` with `accWrap h := Acc.rec f h`: the surface value applies a definition to a
theorem argument, so no recursor is visible; its head-normal form is `Acc.rec f accZero`, a theorem
in a major premise. -/
def accWrapDecl : ReadinessDecl :=
  { name := "usesAccWrap", type := .const "Nat" false,
    value := some (.app (.const "accWrap" false) (.const "accZero" true)),
    unfolded := [.recursorApp (.const "f" false) (.const "accZero" true)] }

-- The surface value alone is clean; the unfolded form flags the declaration.
example : (accWrapDecl.value.map ReadinessExpr.flagged) = some false := by decide
example : scanDeclOpaqueTheoremReadiness accWrapDecl = true := by decide
example : scanDeclOpaqueTheoremReadiness accWrapDecl = true :=
  readinessScanner_flags_delta_wrapped_recursor accWrapDecl (.const "f" false) (.const "accZero" true)
    (by decide) rfl
-- A definition whose unfolding scrutinizes plain data stays clean.
example : scanDeclOpaqueTheoremReadiness
    { accWrapDecl with unfolded := [.recursorApp (.const "f" false) (.const "pair" false)] } =
    false := by decide
example : (scanModuleOpaqueTheoremReadiness true (accWrapDecl :: readinessModule)).flagCount = 3 := by
  decide
example : (scanModuleOpaqueTheoremReadiness true (accWrapDecl :: readinessModule)).isBlocking =
    false := rfl

/-- info: 'Anneal.OleanSpecStrengthAuditor.readinessScanner_flags_delta_wrapped_recursor' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms readinessScanner_flags_delta_wrapped_recursor

/-! ## 5. Axiom pins

Every theorem of §8–§11 and the decidable checkers they are about: at most `[propext, Quot.sound]`,
never `Classical.choice`, `sorryAx`, or a native-evaluation axiom.
-/

/-- info: 'Anneal.OleanSpecStrengthAuditor.band_elim_left' does not depend on any axioms -/
#guard_msgs in
#print axioms band_elim_left

/-- info: 'Anneal.OleanSpecStrengthAuditor.band_elim_right' does not depend on any axioms -/
#guard_msgs in
#print axioms band_elim_right

/-- info: 'Anneal.OleanSpecStrengthAuditor.bor_intro_left' does not depend on any axioms -/
#guard_msgs in
#print axioms bor_intro_left

/-- info: 'Anneal.OleanSpecStrengthAuditor.bor_intro_right' does not depend on any axioms -/
#guard_msgs in
#print axioms bor_intro_right

/-- info: 'Anneal.OleanSpecStrengthAuditor.splitPrivateModule_ofStrings' does not depend on any axioms -/
#guard_msgs in
#print axioms splitPrivateModule_ofStrings

/-- info: 'Anneal.OleanSpecStrengthAuditor.allStrComps_ofStrings' does not depend on any axioms -/
#guard_msgs in
#print axioms allStrComps_ofStrings

/-- info: 'Anneal.OleanSpecStrengthAuditor.allStrComps_embedded_num' does not depend on any axioms -/
#guard_msgs in
#print axioms allStrComps_embedded_num

/-- info: 'Anneal.OleanSpecStrengthAuditor.splitPrivateModule_some_inv' does not depend on any axioms -/
#guard_msgs in
#print axioms splitPrivateModule_some_inv

/-- info: 'Anneal.OleanSpecStrengthAuditor.allStrComps_some_inv' does not depend on any axioms -/
#guard_msgs in
#print axioms allStrComps_some_inv

/-- info: 'Anneal.OleanSpecStrengthAuditor.parsePrivateBody_eq_of' does not depend on any axioms -/
#guard_msgs in
#print axioms parsePrivateBody_eq_of

/-- info: 'Anneal.OleanSpecStrengthAuditor.parsePrivateBody_none_of_tail' does not depend on any axioms -/
#guard_msgs in
#print axioms parsePrivateBody_none_of_tail

/-- info: 'Anneal.OleanSpecStrengthAuditor.parseStrictPrivateName_marker' depends on axioms: [propext] -/
#guard_msgs in
#print axioms parseStrictPrivateName_marker

/-- info: 'Anneal.OleanSpecStrengthAuditor.parseStrictPrivate_roundtrip' depends on axioms: [propext] -/
#guard_msgs in
#print axioms parseStrictPrivate_roundtrip

/-- info: 'Anneal.OleanSpecStrengthAuditor.parseStrictPrivate_some_inv' depends on axioms: [propext] -/
#guard_msgs in
#print axioms parseStrictPrivate_some_inv

/-- info: 'Anneal.OleanSpecStrengthAuditor.parseStrictPrivate_rejects_embedded_num' depends on axioms: [propext] -/
#guard_msgs in
#print axioms parseStrictPrivate_rejects_embedded_num

/-- info: 'Anneal.OleanSpecStrengthAuditor.parseStrictPrivate_rejects_nested' depends on axioms: [propext] -/
#guard_msgs in
#print axioms parseStrictPrivate_rejects_nested

/-- info: 'Anneal.OleanSpecStrengthAuditor.parseStrictPrivate_rejects_nonleading' depends on axioms: [propext] -/
#guard_msgs in
#print axioms parseStrictPrivate_rejects_nonleading

/-- info: 'Anneal.OleanSpecStrengthAuditor.checkPrivateNameModel_of_parse' depends on axioms: [propext] -/
#guard_msgs in
#print axioms checkPrivateNameModel_of_parse

/-- info: 'Anneal.OleanSpecStrengthAuditor.parseStrictPrivate_some_mentions' depends on axioms: [propext] -/
#guard_msgs in
#print axioms parseStrictPrivate_some_mentions

/-- info: 'Anneal.OleanSpecStrengthAuditor.checkPrivateName_rejects_reserved_user_spoof' depends on axioms: [propext] -/
#guard_msgs in
#print axioms checkPrivateName_rejects_reserved_user_spoof

/-- info: 'Anneal.OleanSpecStrengthAuditor.privateUserForbidden_reserved_domain_root' does not depend on any axioms -/
#guard_msgs in
#print axioms privateUserForbidden_reserved_domain_root

/-- info: 'Anneal.OleanSpecStrengthAuditor.privateUserForbidden_reserved_always_root' does not depend on any axioms -/
#guard_msgs in
#print axioms privateUserForbidden_reserved_always_root

/-- info: 'Anneal.OleanSpecStrengthAuditor.checkPrivateName_rejects_foreign_axiom' depends on axioms: [propext] -/
#guard_msgs in
#print axioms checkPrivateName_rejects_foreign_axiom

/-- info: 'Anneal.OleanSpecStrengthAuditor.checkPrivateName_accepts_same_module_helper' depends on axioms: [propext] -/
#guard_msgs in
#print axioms checkPrivateName_accepts_same_module_helper

/-- info: 'Anneal.OleanSpecStrengthAuditor.checkParsedPrivate_accepted_inv' depends on axioms: [propext] -/
#guard_msgs in
#print axioms checkParsedPrivate_accepted_inv

/-- info: 'Anneal.OleanSpecStrengthAuditor.checkForeignPrivate_accepted_inv' depends on axioms: [propext] -/
#guard_msgs in
#print axioms checkForeignPrivate_accepted_inv

/-- info: 'Anneal.OleanSpecStrengthAuditor.foreignKindVerdict_accepted_inv' depends on axioms: [propext] -/
#guard_msgs in
#print axioms foreignKindVerdict_accepted_inv

/-- info: 'Anneal.OleanSpecStrengthAuditor.checkPrivateName_accepted_sound' depends on axioms: [propext] -/
#guard_msgs in
#print axioms checkPrivateName_accepted_sound

/-- info: 'Anneal.OleanSpecStrengthAuditor.mem_sweepViolations' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms mem_sweepViolations

/-- info: 'Anneal.OleanSpecStrengthAuditor.sweepViolations_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms sweepViolations_sound

/-- info: 'Anneal.OleanSpecStrengthAuditor.reachabilityOnly_misses_unreferenced_axiom' does not depend on any axioms -/
#guard_msgs in
#print axioms reachabilityOnly_misses_unreferenced_axiom

/-- info: 'Anneal.OleanSpecStrengthAuditor.wholeModuleAxiomSweep_complete' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms wholeModuleAxiomSweep_complete

/-- info: 'Anneal.OleanSpecStrengthAuditor.wholeModuleAxiomSweep_flags_stage2_axiom' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms wholeModuleAxiomSweep_flags_stage2_axiom

/-- info: 'Anneal.OleanSpecStrengthAuditor.wholeModuleAxiomSweep_ok_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms wholeModuleAxiomSweep_ok_sound

/-- info: 'Anneal.OleanSpecStrengthAuditor.wholeModuleAxiomSweep_subsumes_reachability' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms wholeModuleAxiomSweep_subsumes_reachability

/-- info: 'Anneal.OleanSpecStrengthAuditor.axiomEntry_foundational_redecl_unauthorized' does not depend on any axioms -/
#guard_msgs in
#print axioms axiomEntry_foundational_redecl_unauthorized

/-- info: 'Anneal.OleanSpecStrengthAuditor.axiomEntry_foreign_assumptions_unauthorized' does not depend on any axioms -/
#guard_msgs in
#print axioms axiomEntry_foreign_assumptions_unauthorized

/-- info: 'Anneal.OleanSpecStrengthAuditor.wholeModuleAxiomSweep_rejects_foundational_redecl' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms wholeModuleAxiomSweep_rejects_foundational_redecl

/-- info: 'Anneal.OleanSpecStrengthAuditor.wholeModuleAxiomSweep_rejects_foreign_assumptions' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms wholeModuleAxiomSweep_rejects_foreign_assumptions

/-- info: 'Anneal.OleanSpecStrengthAuditor.segsPrefixOf_sibling' does not depend on any axioms -/
#guard_msgs in
#print axioms segsPrefixOf_sibling

/-- info: 'Anneal.OleanSpecStrengthAuditor.segsPrefixOf_sound' does not depend on any axioms -/
#guard_msgs in
#print axioms segsPrefixOf_sound

/-- info: 'Anneal.OleanSpecStrengthAuditor.pathWithinRoot_rejects_prefix_confusion' depends on axioms: [propext] -/
#guard_msgs in
#print axioms pathWithinRoot_rejects_prefix_confusion

/-- info: 'Anneal.OleanSpecStrengthAuditor.naivePrefix_accepts_prefix_confusion' does not depend on any axioms -/
#guard_msgs in
#print axioms naivePrefix_accepts_prefix_confusion

/-- info: 'Anneal.OleanSpecStrengthAuditor.pathWithinRoot_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms pathWithinRoot_sound

/-- info: 'Anneal.OleanSpecStrengthAuditor.validateOleanRegion_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms validateOleanRegion_iff

/-- info: 'Anneal.OleanSpecStrengthAuditor.validateOleanRegion_false' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms validateOleanRegion_false

/-- info: 'Anneal.OleanSpecStrengthAuditor.regionWF_objs' depends on axioms: [propext] -/
#guard_msgs in
#print axioms regionWF_objs

/-- info: 'Anneal.OleanSpecStrengthAuditor.parentPtr_not_own' depends on axioms: [propext] -/
#guard_msgs in
#print axioms parentPtr_not_own

/-- info: 'Anneal.OleanSpecStrengthAuditor.regionWF_own_field_downward' depends on axioms: [propext] -/
#guard_msgs in
#print axioms regionWF_own_field_downward

/-- info: 'Anneal.OleanSpecStrengthAuditor.ownEdge_lt' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ownEdge_lt

/-- info: 'Anneal.OleanSpecStrengthAuditor.ownPath_lt' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ownPath_lt

/-- info: 'Anneal.OleanSpecStrengthAuditor.downwardPointers_no_cycle' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms downwardPointers_no_cycle

/-- info: 'Anneal.OleanSpecStrengthAuditor.validateOleanRegion_rejects_cycle' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms validateOleanRegion_rejects_cycle

/-- info: 'Anneal.OleanSpecStrengthAuditor.validateOleanRegion_rejects_non_downward' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms validateOleanRegion_rejects_non_downward

/-- info: 'Anneal.OleanSpecStrengthAuditor.validateOleanRegion_rejects_nonzero_rc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms validateOleanRegion_rejects_nonzero_rc

/-- info: 'Anneal.OleanSpecStrengthAuditor.validateOleanRegion_rejects_forged_tag' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms validateOleanRegion_rejects_forged_tag

/-- info: 'Anneal.OleanSpecStrengthAuditor.validateOleanRegion_rejects_oob_array' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms validateOleanRegion_rejects_oob_array

/-- info: 'Anneal.OleanSpecStrengthAuditor.validateOleanRegion_rejects_oob_mpz' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms validateOleanRegion_rejects_oob_mpz

/-- info: 'Anneal.OleanSpecStrengthAuditor.validateOleanRegion_rejects_zero_elem_scalarArray' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms validateOleanRegion_rejects_zero_elem_scalarArray

/-- info: 'Anneal.OleanSpecStrengthAuditor.validateOleanRegion_rejects_string_without_nul' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms validateOleanRegion_rejects_string_without_nul

/-- info: 'Anneal.OleanSpecStrengthAuditor.validateOleanRegion_rejects_truncated' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms validateOleanRegion_rejects_truncated

/-- info: 'Anneal.OleanSpecStrengthAuditor.validateOleanRegion_rejects_overlap' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms validateOleanRegion_rejects_overlap

/-- info: 'Anneal.OleanSpecStrengthAuditor.auditShareCommon_complete' depends on axioms: [propext] -/
#guard_msgs in
#print axioms auditShareCommon_complete

/-- info: 'Anneal.OleanSpecStrengthAuditor.auditShareCommon_ok_sound' depends on axioms: [propext] -/
#guard_msgs in
#print axioms auditShareCommon_ok_sound

/-- info: 'Anneal.OleanSpecStrengthAuditor.isShareCommonRef_direct_import' does not depend on any axioms -/
#guard_msgs in
#print axioms isShareCommonRef_direct_import

/-- info: 'Anneal.OleanSpecStrengthAuditor.compilerHookSummary_flags' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms compilerHookSummary_flags

/-- info: 'Anneal.OleanSpecStrengthAuditor.compilerHookSummary_flags_ir_only_hook' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms compilerHookSummary_flags_ir_only_hook

/-- info: 'Anneal.OleanSpecStrengthAuditor.compilerHookSummary_rejects_forged_ctorIdx' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms compilerHookSummary_rejects_forged_ctorIdx

/-- info: 'Anneal.OleanSpecStrengthAuditor.compilerHookSummary_flags_phase_mismatch' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms compilerHookSummary_flags_phase_mismatch

/-- info: 'Anneal.OleanSpecStrengthAuditor.compilerHookSummary_ok_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms compilerHookSummary_ok_sound

/-- info: 'Anneal.OleanSpecStrengthAuditor.OpaqueTheoremReadinessSummary.isBlocking_eq_false' does not depend on any axioms -/
#guard_msgs in
#print axioms OpaqueTheoremReadinessSummary.isBlocking_eq_false

/-- info: 'Anneal.OleanSpecStrengthAuditor.readinessScanner_never_changes_verdict' does not depend on any axioms -/
#guard_msgs in
#print axioms readinessScanner_never_changes_verdict

/-- info: 'Anneal.OleanSpecStrengthAuditor.readinessScanner_disabled_zero_flags' does not depend on any axioms -/
#guard_msgs in
#print axioms readinessScanner_disabled_zero_flags

/-- info: 'Anneal.OleanSpecStrengthAuditor.ReadinessExpr.carriesTheorem_of_headIsTheorem' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ReadinessExpr.carriesTheorem_of_headIsTheorem

/-- info: 'Anneal.OleanSpecStrengthAuditor.readinessScanner_flags_major_premise_theorem' does not depend on any axioms -/
#guard_msgs in
#print axioms readinessScanner_flags_major_premise_theorem

/-- info: 'Anneal.OleanSpecStrengthAuditor.readinessScanner_flags_proj_scrutinee_theorem' does not depend on any axioms -/
#guard_msgs in
#print axioms readinessScanner_flags_proj_scrutinee_theorem

/-- info: 'Anneal.OleanSpecStrengthAuditor.readinessScanner_flags_direct_and_id_wrapped' does not depend on any axioms -/
#guard_msgs in
#print axioms readinessScanner_flags_direct_and_id_wrapped

/-- info: 'Anneal.OleanSpecStrengthAuditor.readinessScanner_flag_propagates' does not depend on any axioms -/
#guard_msgs in
#print axioms readinessScanner_flag_propagates

/-- info: 'Anneal.OleanSpecStrengthAuditor.readinessScanner_clean_zero_flags' does not depend on any axioms -/
#guard_msgs in
#print axioms readinessScanner_clean_zero_flags

/-- info: 'Anneal.OleanSpecStrengthAuditor.filter_nil_of_all_false' depends on axioms: [propext] -/
#guard_msgs in
#print axioms filter_nil_of_all_false

/-- info: 'Anneal.OleanSpecStrengthAuditor.readinessScanner_clean_module_zero_flags' depends on axioms: [propext] -/
#guard_msgs in
#print axioms readinessScanner_clean_module_zero_flags

/-- info: 'Anneal.OleanSpecStrengthAuditor.unusedCheatInventory' does not depend on any axioms -/
#guard_msgs in
#print axioms unusedCheatInventory

/-- info: 'Anneal.OleanSpecStrengthAuditor.validateOleanRegionModel' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms validateOleanRegionModel

/-- info: 'Anneal.OleanSpecStrengthAuditor.checkPrivateNameModel' depends on axioms: [propext] -/
#guard_msgs in
#print axioms checkPrivateNameModel

/-- info: 'Anneal.OleanSpecStrengthAuditor.wholeModuleAxiomSweep' does not depend on any axioms -/
#guard_msgs in
#print axioms wholeModuleAxiomSweep

/-- info: 'Anneal.OleanSpecStrengthAuditor.auditShareCommonModel' does not depend on any axioms -/
#guard_msgs in
#print axioms auditShareCommonModel

/-- info: 'Anneal.OleanSpecStrengthAuditor.CompilerHookSummary.violations' depends on axioms: [propext] -/
#guard_msgs in
#print axioms CompilerHookSummary.violations

/-- info: 'Anneal.OleanSpecStrengthAuditor.scanModuleOpaqueTheoremReadiness' does not depend on any axioms -/
#guard_msgs in
#print axioms scanModuleOpaqueTheoremReadiness

/-- info: 'Anneal.OleanSpecStrengthAuditor.parseStrictPrivateName' depends on axioms: [propext] -/
#guard_msgs in
#print axioms parseStrictPrivateName

/-- info: 'Anneal.OleanSpecStrengthAuditor.pathWithinRootModel' does not depend on any axioms -/
#guard_msgs in
#print axioms pathWithinRootModel

/-- info: 'Anneal.OleanShadowAndOverrideAuditTests.selfLoop_path' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms selfLoop_path

/-- info: 'Anneal.OleanShadowAndOverrideAuditTests.cycle3_path' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms cycle3_path

/-- info: 'Anneal.OleanSpecStrengthAuditor.privateUserForbidden_compiler_reserved' does not depend on any axioms -/
#guard_msgs in
#print axioms privateUserForbidden_compiler_reserved

/-- info: 'Anneal.OleanSpecStrengthAuditor.checkIRAtSiteModel_none_of_forbidden_last' depends on axioms: [propext] -/
#guard_msgs in
#print axioms checkIRAtSiteModel_none_of_forbidden_last

/-- info: 'Anneal.OleanSpecStrengthAuditor.checkIRAtTailsModel_none_of_last' depends on axioms: [propext] -/
#guard_msgs in
#print axioms checkIRAtTailsModel_none_of_last

/-- info: 'Anneal.OleanSpecStrengthAuditor.checkIRAtSpec_rejects_forged_site' depends on axioms: [propext] -/
#guard_msgs in
#print axioms checkIRAtSpec_rejects_forged_site

/-- info: 'Anneal.OleanSpecStrengthAuditor.checkIRAtSpecModel' depends on axioms: [propext] -/
#guard_msgs in
#print axioms checkIRAtSpecModel

/-- info: 'Anneal.OleanSpecStrengthAuditor.wholeModuleAxiomSweep_rejects_sorry_in_local_mod' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms wholeModuleAxiomSweep_rejects_sorry_in_local_mod

/-- info: 'Anneal.OleanSpecStrengthAuditor.wholeModuleAxiomSweep_rejects_native_in_local_mod' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms wholeModuleAxiomSweep_rejects_native_in_local_mod

/-- info: 'Anneal.OleanSpecStrengthAuditor.wholeModuleAxiomSweep_rejects_masked_redecl' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms wholeModuleAxiomSweep_rejects_masked_redecl

/-- info: 'Anneal.OleanSpecStrengthAuditor.validateOleanRegion_rejects_negative_mpz_alloc' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms validateOleanRegion_rejects_negative_mpz_alloc

/-- info: 'Anneal.OleanSpecStrengthAuditor.validateOleanRegion_rejects_disjoint_overlap' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms validateOleanRegion_rejects_disjoint_overlap

/-- info: 'Anneal.OleanSpecStrengthAuditor.validateOleanRegion_rejects_short_root' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms validateOleanRegion_rejects_short_root

/-- info: 'Anneal.OleanSpecStrengthAuditor.validateOleanRegion_rejects_bad_empty_delta' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms validateOleanRegion_rejects_bad_empty_delta

/-- info: 'Anneal.OleanSpecStrengthAuditor.bmLe_nil' does not depend on any axioms -/
#guard_msgs in
#print axioms bmLe_nil

/-- info: 'Anneal.OleanSpecStrengthAuditor.bmLe_cons' does not depend on any axioms -/
#guard_msgs in
#print axioms bmLe_cons

/-- info: 'Anneal.OleanSpecStrengthAuditor.carriesTheoremAt_mono' does not depend on any axioms -/
#guard_msgs in
#print axioms carriesTheoremAt_mono

/-- info: 'Anneal.OleanSpecStrengthAuditor.flaggedAt_mono' does not depend on any axioms -/
#guard_msgs in
#print axioms flaggedAt_mono

/-- info: 'Anneal.OleanSpecStrengthAuditor.readinessScanner_flags_let_bound_theorem' does not depend on any axioms -/
#guard_msgs in
#print axioms readinessScanner_flags_let_bound_theorem

/-- info: 'Anneal.OleanSpecStrengthAuditor.readinessScanner_flags_let_bound_proj' does not depend on any axioms -/
#guard_msgs in
#print axioms readinessScanner_flags_let_bound_proj

/-- info: 'Anneal.OleanSpecStrengthAuditor.readinessScanner_clean_zero_flags_at' does not depend on any axioms -/
#guard_msgs in
#print axioms readinessScanner_clean_zero_flags_at

end Anneal.OleanShadowAndOverrideAuditTests
