import Anneal.Proto.OleanShadowAndOverrideAuditProto

/-!
# Regression suite: `.olean` private-name, unreferenced-axiom, shadowing, and override audits

Exercises `Anneal.Proto.OleanShadowAndOverrideAuditProto` against the live elaboration
environment of this file, against `.olean` files compiled on the fly into unique `/tmp`
directories (removed in `finally`), against the real toolchain and build `.olean` files, and
against the compiled build library of this checkout.

Every check prints an explicit `PASS` line pinned by `#guard_msgs`; a failed expectation throws,
which changes the message and fails the build.
-/

open Lean Elab Command Meta
open Anneal.Proto.OleanShadowAndOverrideAuditProto

namespace OleanShadowAndOverrideAuditProtoTests

/-! ## Harness -/

def sysLib : IO System.FilePath := return (← findSysroot) / "lib" / "lean"

def expect (label : String) (ok : Bool) (why : String := "") : IO Unit :=
  if ok then IO.println s!"PASS {label}" else throw (IO.userError s!"FAIL {label} {why}")

def nameHas (n : Name) (needle : String) : Bool := (n.toString.splitOn needle).length > 1

def hits (s : AuditSummary) (k : ViolationKind) (needle : String) : Array AuditViolation :=
  s.violations.filter fun v => v.kind == k && (nameHas v.decl needle || nameHas v.module needle)

def anyHits (s : AuditSummary) (needle : String) : Array AuditViolation :=
  s.violations.filter fun v => nameHas v.decl needle || nameHas v.module needle

def renderAll (vs : Array AuditViolation) : String := toString (vs.map (·.render)).toList

/-- All four vectors (minus Vector 3, which has its own tests) over the live environment. -/
def liveAudit (cfg : FourVectorConfig := {}) : CoreM AuditSummary := do
  let env ← getEnv
  let lib ← sysLib
  let ((), s) ← AuditM.run' do
    let ctx ← mkAuditContext env lib (some env.mainModule)
    runAllFourVectorAudits ctx cfg
  return s

/-- Forge a kernel-checked definition `name : Nat := 0` with an arbitrary (possibly malformed) name. -/
def forgeDef (name : Name) : CoreM Unit :=
  addDecl (.defnDecl { name, levelParams := [], type := mkConst ``Nat, value := mkNatLit 0,
                       hints := .abbrev, safety := .safe })

/-- Forge an axiom `name : False`. -/
def forgeAxiom (name : Name) : CoreM Unit :=
  addDecl (.axiomDecl { name, levelParams := [], type := mkConst ``False, isUnsafe := false })

def privName (mod user : Name) : Name := Name.mkNum (`_private ++ mod) 0 ++ user

/-- This file's namespace (declarations below are elaborated inside it). -/
def ns : Name := `OleanShadowAndOverrideAuditProtoTests

def parsesTo (n : Name) (r : Except PrivateNameError (Option PrivateNameView)) : Bool :=
  match parsePrivateName n, r with
  | .ok a, .ok b => a == b
  | .error a, .error b => a == b
  | _, _ => false

/-- Run `k` with a fresh unique directory under `/tmp`, removed afterwards. -/
def withTmpDir (k : System.FilePath → IO α) : IO α := do
  let stamp ← IO.monoNanosNow
  let rnd ← IO.rand 0 1000000000
  let dir : System.FilePath := s!"/tmp/olean_shadow_audit_proto_{stamp}_{rnd}"
  IO.FS.createDirAll dir
  try k dir finally IO.FS.removeDirAll dir

/-- Compile `src` as module `mod` rooted at `root` with the toolchain `lean`, producing its
`.olean` parts next to the source. -/
def compileModule (root : System.FilePath) (mod : Name) (src : String) (leanPath? : Option String := none) :
    IO System.FilePath := do
  let rel := modRelPath mod
  let leanFile := root / (rel ++ ".lean")
  if let some p := leanFile.parent then IO.FS.createDirAll p
  IO.FS.writeFile leanFile src
  let olean := root / (rel ++ ".olean")
  let leanBin := (← findSysroot) / "bin" / "lean"
  let leanPath := leanPath?.getD (root.toString ++ ":" ++ (← sysLib).toString)
  let out ← IO.Process.output {
    cmd := leanBin.toString
    args := #["-R", root.toString, "-o", olean.toString, leanFile.toString]
    env := #[("LEAN_PATH", some leanPath)] }
  unless out.exitCode == 0 do throw (IO.userError s!"compiling {mod} failed: {out.stdout} {out.stderr}")
  return olean

/-- Import `mods` with search path `[root, sysroot]` (restoring the previous search path). -/
def importWith (root : System.FilePath) (mods : Array Name) (level : OLeanLevel := .private) : IO Environment := do
  let saved ← searchPathRef.get
  searchPathRef.set [root, ← sysLib]
  try importModules (mods.map ({ module := · })) {} (loadExts := false) (level := level)
  finally searchPathRef.set saved

def auditImported (env : Environment) (cfg : FourVectorConfig := {}) (root? : Option System.FilePath := none) :
    IO AuditSummary := do
  let lib ← sysLib
  let saved ← searchPathRef.get
  if let some r := root? then searchPathRef.set [r, lib]
  try
    let ((), s) ← AuditM.run' do
      let ctx ← mkAuditContext env lib
      runAllFourVectorAudits ctx cfg
    return s
  finally searchPathRef.set saved

/-! ## T20: real sweep over the compiled build library of this checkout

The swept library roots are the `lean_lib` roots that build on this base (`lake build Trusted
Anneal MiniRust Correspondence`); `MiniRustSpec` currently fails to build on the base (two of its
imports realize the same equation lemma differently), so its artifacts are validated by Vector 3
but not loaded. -/

def libraryRoots : Array Name := #[`Trusted, `Anneal, `MiniRust, `Correspondence]

/-- Run the build-library sweep and print its measurements; fails unless there are zero findings
and (when `budgetMs?` is set) the sweep finishes within the budget. -/
def sweep (label : String) (cfg : FourVectorConfig) (budgetMs? : Option Nat) : IO Unit := do
  let buildLib := (← IO.currentDir) / ".lake" / "build" / "lib" / "lean"
  let ((), s) ← AuditM.run' (auditBuildLibrary buildLib (← sysLib) cfg (some libraryRoots))
  IO.println s!"{label}: modules_checked={s.modulesChecked} decls_checked={s.declsChecked} oleans_checked={s.oleansChecked} axioms_swept={s.axiomsSwept} hook_entries={s.hookEntriesChecked} false_positives={s.violations.size} structural_flags={s.policyFlags.size} stray_artifacts={s.strayArtifacts} elapsed_ms={s.elapsedMs} import_ms={s.importMs}"
  expect s!"{label} zero false positives on the base build" s.violations.isEmpty (renderAll s.violations)
  expect s!"{label} audited every library-root module" (s.modulesChecked ≥ 100) s!"{s.modulesChecked}"
  if let some b := budgetMs? then
    expect s!"{label} finished within {b} ms" (s.elapsedMs < b) s!"{s.elapsedMs}"



/-! ## Vector 1 — `_private` namespace spoofing -/

/-! ### T1: structural parser (pure) -/

/--
info: PASS T1 genuine private name parses to (module, user)
PASS T1 non-private name is not private
PASS T1 missing separator rejected
PASS T1 non-zero separator rejected
PASS T1 empty module rejected
PASS T1 empty user suffix rejected
PASS T1 numeric segment inside module rejected
PASS T1 nested _private rejected
PASS T1 non-leading _private rejected
PASS T1 double-zero separator (_private.M.0.0.foo) rejected
PASS T1 empty user component (_private.M.0."") rejected
-/
#guard_msgs in
#eval show IO Unit from do
  expect "T1 genuine private name parses to (module, user)"
    (parsesTo (privName `Anneal.Foo `Anneal.Foo.helper) (.ok (some { module := `Anneal.Foo, user := `Anneal.Foo.helper })))
  expect "T1 non-private name is not private" (parsesTo `Anneal.Foo.helper (.ok none))
  expect "T1 missing separator rejected" (parsesTo `_private.M.foo (.error .missingSeparator))
  expect "T1 non-zero separator rejected" (parsesTo (Name.mkNum `_private.M 1 ++ `foo) (.error (.nonZeroSeparator 1)))
  expect "T1 empty module rejected" (parsesTo (Name.mkNum `_private 0 ++ `foo) (.error .emptyModule))
  expect "T1 empty user suffix rejected" (parsesTo (Name.mkNum `_private.M 0) (.error .emptyUser))
  expect "T1 numeric segment inside module rejected"
    (parsesTo (Name.mkNum (Name.mkNum `_private.A 3 ++ `B) 0 ++ `x) (.error (.numericModuleSegment 3)))
  expect "T1 nested _private rejected" (parsesTo (privName `A (privName `B `x)) (.error .nestedPrivate))
  expect "T1 non-leading _private rejected" (parsesTo (`Foo ++ privName `Bar `baz) (.error .nonLeadingPrivate))
  expect "T1 double-zero separator (_private.M.0.0.foo) rejected"
    (parsesTo (Name.mkNum (Name.mkNum `_private.M 0) 0 ++ `foo) (.error (.leadingNumericUser 0)))
  expect "T1 empty user component (_private.M.0.\"\") rejected"
    (parsesTo ((Name.mkNum `_private.M 0).str "") (.error .emptyUserComponent))

/-! ### T2: genuine private declarations and compiler auxiliaries (control) -/

namespace V1Ctl
private def helper (n : Nat) : Nat := match n with | 0 => 1 | k + 1 => k
private theorem helper_zero : helper 0 = 1 := rfl
private structure PrivState where
  x : Nat
  deriving Repr
end V1Ctl

/--
info: PASS T2 genuine private declarations are encoded with the live module
PASS T2 zero Vector 1 findings on genuine private declarations and auxiliaries
-/
#guard_msgs in
#eval show CoreM Unit from do
  let env ← getEnv
  let privs := env.constants.map₂.toList.map (·.1) |>.filter fun n => nameHas n "V1Ctl"
  let privs := privs.filter fun n => nameHas n "_private"
  expect "T2 genuine private declarations are encoded with the live module"
    (privs.length ≥ 10 && privs.all fun n =>
      match parsePrivateName n with
      | .ok (some v) => v.module == env.mainModule
      | _ => false) (toString privs)
  let s ← liveAudit
  let v1 := (anyHits s "V1Ctl").filter fun v =>
    v.kind == .malformedPrivateName || v.kind == .privateModuleMismatch || v.kind == .privateUserSuffixSpoof
  expect "T2 zero Vector 1 findings on genuine private declarations and auxiliaries" v1.isEmpty (renderAll v1)

/-! ### T3: forged foreign `_private.<Trusted|Init|Assumptions>.0.*` prefixes -/

run_cmd liftCoreM do
  forgeDef (privName `Trusted.VerificationResult `V1Forge.foo)
  forgeDef (privName `Init.Core `V1Forge.bar)
  forgeAxiom (privName `Assumptions.Ok `V1Forge.ax)

/--
info: PASS T3 forged Trusted prefix rejected
PASS T3 forged Init prefix rejected
PASS T3 forged Assumptions prefix rejected
PASS T3 forged Assumptions axiom never admitted by the assumption allowlist
-/
#guard_msgs in
#eval show CoreM Unit from do
  let s ← liveAudit { axioms := { allowAssumptions := true, allowedAssumptionModules := NameSet.empty.insert `Assumptions.Ok
                                  allowedAssumptions := NameSet.empty.insert (privName `Assumptions.Ok `V1Forge.ax) } }
  let mm := s.violations.filter (·.kind == .privateModuleMismatch)
  expect "T3 forged Trusted prefix rejected" (mm.any (·.decl == privName `Trusted.VerificationResult `V1Forge.foo))
  expect "T3 forged Init prefix rejected" (mm.any (·.decl == privName `Init.Core `V1Forge.bar))
  expect "T3 forged Assumptions prefix rejected" (mm.any (·.decl == privName `Assumptions.Ok `V1Forge.ax))
  expect "T3 forged Assumptions axiom never admitted by the assumption allowlist"
    (s.violations.any fun v => v.decl == privName `Assumptions.Ok `V1Forge.ax &&
      (v.kind == .unreferencedSorryOrNativeAxiom || v.kind == .unreferencedTopLevelAxiom))
    (renderAll (anyHits s "V1Forge"))

/-! ### T4: user-suffix spoofing (`Init.*`, `sorryAx`, `Trusted.*`, wildcard `._spoof`, `ShareCommon.*`, `_at_`) -/

private def _root_.Init.V1Spoof.x : Nat := 0
private def _root_.Trusted.V1Spoof.y : Nat := 0
private def _root_.Lean.V1Spoof.z : Nat := 0

run_cmd liftCoreM do
  let env ← getEnv
  forgeDef (privName env.mainModule `sorryAx)
  forgeDef (privName env.mainModule `Lean.ofReduceBool)
  -- B1 regression: underscore-suffixed spoof extending an imported `Lean.*` constant (`Lean.Name.mkStr1._spoof`)
  forgeDef (privName env.mainModule `Lean.Name.mkStr1._spoof)
  -- B1 regression: axiom spoofing realized `.eq_1` suffix on an imported `Lean.*` constant
  forgeAxiom (privName env.mainModule `Lean.Name.mkStr1.eq_99)
  -- B1 regression: `ShareCommon.*`, `Classical.*`, and `_native` user-suffix spoofs
  forgeDef (privName env.mainModule `ShareCommon.StateFactory.mk)
  forgeDef (privName env.mainModule `Classical.some)
  forgeDef (privName env.mainModule `_native.native_decide.ax_9)

/--
info: PASS T4 Init.* user suffix rejected
PASS T4 Trusted.* user suffix rejected
PASS T4 Lean.* user suffix rejected
PASS T4 sorryAx user suffix rejected
PASS T4 Lean.ofReduceBool user suffix rejected
PASS T4 underscore-wildcard spoof on existing Lean constant rejected
PASS T4 axiom spoofing realized .eq_99 suffix rejected
PASS T4 ShareCommon / Classical / _native user suffixes rejected
PASS T4 forged _at_ specialization context in extraConstNames rejected
-/
#guard_msgs in
#eval show CoreM Unit from do
  let env ← getEnv
  let main := env.mainModule
  let s ← liveAudit
  let sp := s.violations.filter (·.kind == .privateUserSuffixSpoof)
  expect "T4 Init.* user suffix rejected" (sp.any (·.decl == privName main `Init.V1Spoof.x))
  expect "T4 Trusted.* user suffix rejected" (sp.any (·.decl == privName main `Trusted.V1Spoof.y))
  expect "T4 Lean.* user suffix rejected" (sp.any (·.decl == privName main `Lean.V1Spoof.z))
  expect "T4 sorryAx user suffix rejected" (sp.any (·.decl == privName main `sorryAx))
  expect "T4 Lean.ofReduceBool user suffix rejected" (sp.any (·.decl == privName main `Lean.ofReduceBool))
  expect "T4 underscore-wildcard spoof on existing Lean constant rejected"
    (sp.any (·.decl == privName main `Lean.Name.mkStr1._spoof))
  expect "T4 axiom spoofing realized .eq_99 suffix rejected"
    (sp.any (·.decl == privName main `Lean.Name.mkStr1.eq_99))
  expect "T4 ShareCommon / Classical / _native user suffixes rejected"
    (sp.any (·.decl == privName main `ShareCommon.StateFactory.mk) &&
     sp.any (·.decl == privName main `Classical.some) &&
     sp.any (·.decl == privName main `_native.native_decide.ax_9))
  -- B1 regression: forged `_at_` specialization name in `extraConstNames` whose context is foreign
  let lib ← sysLib
  let (ctx, _) ← AuditM.run' (mkAuditContext env lib (some main))
  let spoofSpec := (privName `Init.Data.Nat.Basic `Nat.repeatTR.loop) ++ `_at_ ++ `Trusted.Spoof.spec_0
  let ((), specSummary) := (checkPrivateName ctx main spoofSpec true).run {}
  expect "T4 forged _at_ specialization context in extraConstNames rejected"
    (specSummary.violations.any (·.kind == .privateModuleMismatch)) (renderAll specSummary.violations)

/-! ### T5: malformed, nested and non-leading `_private` declarations and extension targets -/

run_cmd liftCoreM do
  let env ← getEnv
  forgeDef (`V1Bad ++ privName env.mainModule `nonLeading)
  forgeDef (privName env.mainModule (privName env.mainModule `V1Bad.nested))
  forgeDef (Name.mkNum (`_private ++ env.mainModule) 1 ++ `V1Bad.nonZero)
  forgeDef (`_private ++ env.mainModule ++ `V1Bad.noSeparator)

/--
info: PASS T5 non-leading _private declaration rejected
PASS T5 nested _private declaration rejected
PASS T5 non-zero separator declaration rejected
PASS T5 missing separator declaration rejected
PASS T5 malformed and foreign _private extension targets rejected
-/
#guard_msgs in
#eval show CoreM Unit from do
  let env ← getEnv
  let main := env.mainModule
  let s ← liveAudit
  let bad := s.violations.filter (·.kind == .malformedPrivateName)
  expect "T5 non-leading _private declaration rejected" (bad.any (·.decl == `V1Bad ++ privName main `nonLeading))
  expect "T5 nested _private declaration rejected" (bad.any (·.decl == privName main (privName main `V1Bad.nested)))
  expect "T5 non-zero separator declaration rejected" (bad.any (·.decl == Name.mkNum (`_private ++ main) 1 ++ `V1Bad.nonZero))
  expect "T5 missing separator declaration rejected" (bad.any (·.decl == `_private ++ main ++ `V1Bad.noSeparator))
  let lib ← sysLib
  let (ctx, _) ← AuditM.run' (mkAuditContext env lib (some main))
  let ((), extS) := (do
    checkExtensionRefName ctx main `_private.MalformedExtTarget false
    checkExtensionRefName ctx main (privName `Trusted.Foreign `ghostTarget) false : PureAuditM Unit).run {}
  expect "T5 malformed and foreign _private extension targets rejected"
    (extS.violations.any (·.kind == .malformedPrivateName) &&
     extS.violations.any (·.kind == .privateModuleMismatch))
    (renderAll extS.violations)

/-! ## Vector 2 — unreferenced top-level axioms (`leanprover/lean4#16781`) -/

/-! ### T6: foundational control + B1 non-toolchain re-declaration anti-spoofing -/

theorem V2Ctl.claim (p q : Prop) (h : p ↔ q) : p = q := propext h
theorem V2Ctl.choice (α : Type) (h : Nonempty α) : ∃ _ : α, True := ⟨Classical.choice h, trivial⟩

/--
info: PASS T6 propext / Classical.choice admitted with their toolchain modules
PASS T6 Classical.choice rejected when allowClassicalChoice = false
PASS T6 non-toolchain re-declaration of propext or foreign Assumptions axiom rejected
-/
#guard_msgs in
#eval show CoreM Unit from do
  let s ← liveAudit { axiomRoots? := some #[``V2Ctl.claim, ``V2Ctl.choice] }
  expect "T6 propext / Classical.choice admitted with their toolchain modules"
    (!s.violations.any (·.kind == .referencedUnapprovedAxiom)) (renderAll (s.violations.filter (·.kind == .referencedUnapprovedAxiom)))
  let s ← liveAudit { axioms := { allowClassicalChoice := false }, axiomRoots? := some #[``V2Ctl.choice] }
  expect "T6 Classical.choice rejected when allowClassicalChoice = false"
    (s.violations.any fun v => v.kind == .referencedUnapprovedAxiom && v.decl == ``Classical.choice)
  -- B1 regression: untrusted module `Evil` re-declaring `Assumptions.Ok.ax` alongside `Assumptions.Ok`
  withTmpDir fun dir => do
    let _ ← compileModule dir `Assumptions.Ok "axiom Assumptions.Ok.ax : True\n"
    let _ ← compileModule dir `Evil "import Assumptions.Ok\n"
    let env ← importWith dir #[`Evil]
    -- Inject a forged `Assumptions.Ok.ax` and `propext` into a synthetic `ModuleView` for `Evil`
    let some axCi := env.find? `Assumptions.Ok.ax | throw (IO.userError "missing ax")
    let some propCi := env.find? ``propext | throw (IO.userError "missing propext")
    let lib ← sysLib
    let ((), spoofS) ← AuditM.run' do
      let ctx ← mkAuditContext env lib
      let evilView : ModuleView := {
        module := `Evil, idx? := none,
        data := { (default : ModuleData) with constants := #[axCi, propCi], constNames := #[`Assumptions.Ok.ax, ``propext] } }
      auditUnreferencedAxioms ctx #[evilView]
        { allowAssumptions := true, allowedAssumptions := NameSet.empty.insert `Assumptions.Ok.ax }
        (some #[``propext])
    expect "T6 non-toolchain re-declaration of propext or foreign Assumptions axiom rejected"
      (spoofS.violations.any (fun v => v.decl == ``propext && v.module == `Evil) &&
       spoofS.violations.any (fun v => v.decl == `Assumptions.Ok.ax && v.module == `Evil))
      (renderAll spoofS.violations)

/-! ### T7: unreferenced public `axiom : False` (missed by `collectAxioms`) -/

axiom V2Dead.bogus : False
theorem V2Dead.claim : True := trivial

/--
info: PASS T7 reachability-only collectAxioms misses the dangling axiom
PASS T7 auditUnreferencedAxioms reports it as unreferencedTopLevelAxiom
-/
#guard_msgs in
#eval show CoreM Unit from do
  let axs ← collectAxioms ``V2Dead.claim
  expect "T7 reachability-only collectAxioms misses the dangling axiom" (axs.isEmpty) (toString axs)
  let s ← liveAudit { axiomRoots? := some #[``V2Dead.claim] }
  expect "T7 auditUnreferencedAxioms reports it as unreferencedTopLevelAxiom"
    (s.violations.any fun v => v.kind == .unreferencedTopLevelAxiom && v.decl == ``V2Dead.bogus)

/-! ### T8: unreferenced `private axiom` in live `map₂` and in a compiled `.olean.private` -/

private axiom V2Priv.hidden : False

def hiddenAxSrc : String := "module\n\nprivate axiom hiddenAx : False\npublic theorem pubThm : True := trivial\n"

/--
info: PASS T8 live private axiom in env.constants.map₂ reported
PASS T8 compiled module-system file has .olean/.olean.server/.olean.private
PASS T8 private axiom stored only in .olean.private reported
-/
#guard_msgs in
#eval show CoreM Unit from do
  let main := (← getEnv).mainModule
  let s ← liveAudit
  expect "T8 live private axiom in env.constants.map₂ reported"
    (s.violations.any fun v => v.kind == .unreferencedTopLevelAxiom && v.decl == privName main (ns ++ `V2Priv.hidden))
  withTmpDir fun dir => do
    let olean ← compileModule dir `HiddenAx hiddenAxSrc
    let parts ← #["olean", "olean.server", "olean.private"].filterM fun e => entryExists ⟨olean.toString.dropEnd 5 |>.toString |> (· ++ e)⟩
    expect "T8 compiled module-system file has .olean/.olean.server/.olean.private" (parts.size == 3)
    let env ← importWith dir #[`HiddenAx]
    let s ← auditImported env { axiomRoots? := some #[`pubThm] } dir
    expect "T8 private axiom stored only in .olean.private reported"
      (s.violations.any fun v => v.kind == .unreferencedTopLevelAxiom && v.decl == privName `HiddenAx `hiddenAx) (renderAll s.violations)

/-! ### T9: unreferenced `Assumptions.*` axiom, dead `sorryAx` / `_native` axioms -/

def assumptionSrc : String := "axiom Assumptions.Extra.ax : False\ntheorem Assumptions.Extra.ok : True := trivial\n"

run_cmd liftCoreM do
  forgeAxiom `V2Native._native.native_decide.ax_1

/-- warning: declaration uses `sorry` -/
#guard_msgs in
set_option warningAsError false in
run_cmd liftCoreM do
  addDecl (.thmDecl { name := `V2Sorry.claim, levelParams := [], type := mkConst ``True,
                      value := mkApp2 (mkConst `sorryAx [.zero]) (mkConst ``True) (mkConst ``true) })

/--
info: PASS T9 unreferenced Assumptions axiom rejected when allowAssumptions = false
PASS T9 Assumptions axiom admitted only when allowAssumptions = true and allowlisted
PASS T9 reachable sorryAx rejected
PASS T9 dead _native axiom reported as sorryAx-class / native
PASS T9 whole-module audit (axiomRoots? = none) also catches reachable sorryAx
PASS T9 shadowed mergeableDuplicate theorem proof smuggling sorryAx caught
-/
#guard_msgs in
#eval show CoreM Unit from do
  let (sDup, sDupImplicit) ← withTmpDir fun dir => do
    let _ ← compileModule dir `Assumptions.Extra assumptionSrc
    let env ← importWith dir #[`Assumptions.Extra]
    let s ← auditImported env {} dir
    expect "T9 unreferenced Assumptions axiom rejected when allowAssumptions = false"
      (s.violations.any fun v => v.kind == .unreferencedAssumptionAxiom && v.decl == `Assumptions.Extra.ax) (renderAll s.violations)
    let s ← auditImported env { axioms := { allowAssumptions := true, allowedAssumptions := NameSet.empty.insert `Assumptions.Extra.ax } } dir
    expect "T9 Assumptions axiom admitted only when allowAssumptions = true and allowlisted"
      (!s.violations.any fun v => v.decl == `Assumptions.Extra.ax) (renderAll s.violations)
    -- B2 regression: two co-imported modules declaring mergeableDuplicate `Shared.dupThm` where
    -- the first copy is clean (`trivial`) and the second shadowed copy uses `sorryAx`!
    let _ ← compileModule dir `DupClean "theorem Shared.dupThm : True := trivial\n"
    let _ ← compileModule dir `DupDirty "theorem Shared.dupThm : True := sorryAx True true\n"
    let _ ← compileModule dir `DupRoot "import DupClean\nimport DupDirty\ntheorem useDup : True := Shared.dupThm\n"
    let envDup ← importWith dir #[`DupRoot]
    let sDup ← auditImported envDup { axiomRoots? := some #[`useDup] } dir
    let sDupImplicit ← auditImported envDup {} dir
    return (sDup, sDupImplicit)
  expect "T9 reachable sorryAx rejected"
    ((← liveAudit { axiomRoots? := some #[`V2Sorry.claim] }).violations.any fun v => v.kind == .referencedUnapprovedAxiom && v.decl == `sorryAx)
  let sImplicit ← liveAudit {}
  expect "T9 dead _native axiom reported as sorryAx-class / native"
    (sImplicit.violations.any fun v => v.kind == .unreferencedSorryOrNativeAxiom && v.decl == `V2Native._native.native_decide.ax_1)
  expect "T9 whole-module audit (axiomRoots? = none) also catches reachable sorryAx"
    (sImplicit.violations.any fun v => v.kind == .referencedUnapprovedAxiom && v.decl == `sorryAx)
    (renderAll sImplicit.violations)
  expect "T9 shadowed mergeableDuplicate theorem proof smuggling sorryAx caught"
    (sDup.violations.any (fun v => v.kind == .referencedUnapprovedAxiom && v.decl == `sorryAx) &&
     sDupImplicit.violations.any (fun v => v.kind == .referencedUnapprovedAxiom && v.decl == `sorryAx))
    (renderAll sDup.violations)

/-! ### T10: exported-only (`isModule`) environments fail closed even after `setExporting false` -/

/--
info: PASS T10 exported-level import is a module-system environment
PASS T10 the exported view hides the private axiom
PASS T10 auditUnreferencedAxioms fails closed on the exported-only view
PASS T10 exported-level isModule env still fails closed even if caller calls setExporting false
-/
#guard_msgs in
#eval show IO Unit from do
  withTmpDir fun dir => do
    let _ ← compileModule dir `HiddenAx hiddenAxSrc
    let env ← importWith dir #[`HiddenAx] (level := .exported)
    expect "T10 exported-level import is a module-system environment" env.header.isModule
    let hidden := env.header.moduleData.any fun d => d.constNames.contains (privName `HiddenAx `hiddenAx)
    expect "T10 the exported view hides the private axiom" (!hidden)
    let s ← auditImported env {} dir
    expect "T10 auditUnreferencedAxioms fails closed on the exported-only view"
      (s.violations.any (·.kind == .exportedOnlyEnvironment)) (renderAll s.violations)
    -- B1 regression: calling `env.setExporting false` on an `.exported` import (where `.olean.private`
    -- was never loaded and `importAll` is `false`) must STILL fail closed!
    let envUnmasked := env.setExporting false
    let sUnmasked ← auditImported envUnmasked {} dir
    expect "T10 exported-level isModule env still fails closed even if caller calls setExporting false"
      (!envUnmasked.isExporting && sUnmasked.violations.any (·.kind == .exportedOnlyEnvironment))
      (renderAll sUnmasked.violations)

/-! ## Vector 3 — `Lean.findOLean`, shadowing, symlinks, binary headers (`leanprover/lean4#16737`) -/

/-! ### T11: real `Lean.findOLean` + header checks on toolchain and build artifacts -/

/--
info: PASS T11 Init.Prelude resolves inside the sysroot
PASS T11 all 5 Init.Prelude parts pass the pinned 4.34.1 header / root-object checks
PASS T11 the prototype's own build .olean passes
PASS T11 resolution + shadowing audit is clean on the real search path
-/
#guard_msgs in
#eval show IO Unit from do
  let lib ← sysLib
  let p ← findOLean `Init.Prelude
  expect "T11 Init.Prelude resolves inside the sysroot" ((← pathWithinRoot lib p) matches .ok _)
  let base := (p.toString.dropEnd 6).toString
  let mut ok := 0
  for ext in partExts do
    if let .ok i ← validateOleanFile ⟨base ++ "." ++ ext⟩ then
      if i.version == "4.34.1" && i.rootOffset + i.rootSize ≤ i.fileSize then ok := ok + 1
  expect "T11 all 5 Init.Prelude parts pass the pinned 4.34.1 header / root-object checks" (ok == 5) s!"{ok}"
  let own ← findOLean `Anneal.Proto.OleanShadowAndOverrideAuditProto
  expect "T11 the prototype's own build .olean passes" ((← validateOleanFile own) matches .ok _)
  let buildLib := (← IO.currentDir) / ".lake" / "build" / "lib" / "lean"
  let ((), s) ← AuditM.run' (auditOleanResolutionAndShadowing #[`Init.Prelude, `Init.Core, `Anneal.Proto.OleanShadowAndOverrideAuditProto]
    { sysrootLibDir := lib, approvedBuildRoots := #[buildLib], searchPath? := some [buildLib, lib, lib], validateToolchainBinaries := true })
  expect "T11 resolution + shadowing audit is clean on the real search path"
    (s.violations.isEmpty && s.oleansChecked == 11) s!"{renderAll s.violations} {s.oleansChecked}"

/-! ### T12: multi-root shadowing, toolchain shadowing, and incomplete/orphan companion parts -/

/--
info: PASS T12 module present in two search-path roots is reported as shadowed
PASS T12 toolchain module copied into a non-sysroot root is reported
PASS T12 stripped .olean.private companion (with .olean.server remaining) is reported
PASS T12 orphan .ir companion without .ir.sig is reported
-/
#guard_msgs in
#eval show IO Unit from do
  let lib ← sysLib
  withTmpDir fun dir => do
    let rootA := dir / "rootA"
    let rootB := dir / "rootB"
    let olean ← compileModule rootA `Shadowed "def shadowedVal : Nat := 1\n"
    IO.FS.createDirAll rootB
    IO.FS.writeBinFile (rootB / "Shadowed.olean") (← IO.FS.readBinFile olean)
    let ((), s) ← AuditM.run' (auditOleanResolutionAndShadowing #[`Shadowed]
      { sysrootLibDir := lib, approvedBuildRoots := #[rootA, rootB], searchPath? := some [rootA, rootB, lib] })
    expect "T12 module present in two search-path roots is reported as shadowed"
      (s.violations.any (·.kind == .oleanShadowed)) (renderAll s.violations)
    IO.FS.createDirAll (rootB / "Init")
    IO.FS.writeBinFile (rootB / "Init" / "Prelude.olean") (← IO.FS.readBinFile (lib / "Init" / "Prelude.olean"))
    let ((), s) ← AuditM.run' (auditOleanResolutionAndShadowing #[`Init.Prelude]
      { sysrootLibDir := lib, approvedBuildRoots := #[rootB], searchPath? := some [rootB, lib] })
    expect "T12 toolchain module copied into a non-sysroot root is reported"
      (s.violations.any (·.kind == .toolchainShadowed) && s.violations.any (·.kind == .oleanOutsideApprovedRoot))
      (renderAll s.violations)
    -- B1 regression: module-system file with `.olean.private` deleted while `.olean.server` remains
    let rootC := dir / "rootC"
    let modOlean ← compileModule rootC `StrippedMod hiddenAxSrc
    IO.FS.removeFile ⟨modOlean.toString ++ ".private"⟩
    let ((), sStrip) ← AuditM.run' (auditOleanResolutionAndShadowing #[`StrippedMod]
      { sysrootLibDir := lib, approvedBuildRoots := #[rootC], searchPath? := some [rootC, lib] })
    expect "T12 stripped .olean.private companion (with .olean.server remaining) is reported"
      (sStrip.violations.any (·.kind == .oleanOutsideApprovedRoot)) (renderAll sStrip.violations)
    -- B1 regression: incomplete `.ir` without `.ir.sig`
    IO.FS.writeBinFile (rootA / "Shadowed.ir") (← IO.FS.readBinFile olean)
    let ((), sIr) ← AuditM.run' (auditOleanResolutionAndShadowing #[`Shadowed]
      { sysrootLibDir := lib, approvedBuildRoots := #[rootA], searchPath? := some [rootA, lib] })
    expect "T12 orphan .ir companion without .ir.sig is reported"
      (sIr.violations.any (·.kind == .oleanOutsideApprovedRoot)) (renderAll sIr.violations)

/-! ### T13: symlink escape, symlinked root, symlink inside buildLib, path-prefix confusion and `..` -/

/--
info: PASS T13 regular file inside the root accepted
PASS T13 prefix-confused sibling root (root_evil vs root) rejected
PASS T13 symlinked artifact escaping the root rejected
PASS T13 symlinked directory component rejected
PASS T13 symlinked approved root itself rejected
PASS T13 symlinked ancestor of approved root rejected
PASS T13 dot-dot component rejected
PASS T13 resolution through root_evil is outside the approved root
PASS T13 listOleanModules flags symlinked .olean inside buildLib immediately
-/
#guard_msgs in
#eval show IO Unit from do
  let lib ← sysLib
  withTmpDir fun dir => do
    let root := dir / "root"
    let evil := dir / "root_evil"
    let outside := dir / "outside"
    for d in [root, evil, outside, root / "Sub", outside / "nested"] do IO.FS.createDirAll d
    let bytes ← IO.FS.readBinFile (lib / "Init" / "Prelude.olean")
    IO.FS.writeBinFile (root / "Good.olean") bytes
    IO.FS.writeBinFile (evil / "Evil.olean") bytes
    IO.FS.writeBinFile (outside / "Esc.olean") bytes
    IO.FS.writeBinFile (outside / "nested" / "Sneak.olean") bytes
    let ln (target link : System.FilePath) : IO Unit := do
      let out ← IO.Process.output { cmd := "ln", args := #["-s", target.toString, link.toString] }
      unless out.exitCode == 0 do throw (IO.userError out.stderr)
    ln (outside / "Esc.olean") (root / "Esc.olean")
    ln outside (root / "Link")
    ln outside (dir / "sym_root")
    expect "T13 regular file inside the root accepted" ((← pathWithinRoot root (root / "Good.olean")) matches .ok _)
    expect "T13 prefix-confused sibling root (root_evil vs root) rejected"
      ((← pathWithinRoot root (evil / "Evil.olean")) matches .error _)
    expect "T13 symlinked artifact escaping the root rejected" ((← pathWithinRoot root (root / "Esc.olean")) matches .error _)
    expect "T13 symlinked directory component rejected" ((← pathWithinRoot root (root / "Link" / "Esc.olean")) matches .error _)
    expect "T13 symlinked approved root itself rejected"
      ((← pathWithinRoot (dir / "sym_root") (dir / "sym_root" / "Esc.olean")) matches .error _)
    expect "T13 symlinked ancestor of approved root rejected"
      ((← pathWithinRoot (dir / "sym_root" / "nested") (dir / "sym_root" / "nested" / "Sneak.olean")) matches .error _)
    expect "T13 dot-dot component rejected" ((← pathWithinRoot root (root / "Sub" / ".." / "Good.olean")) matches .error _)
    let ((), s) ← AuditM.run' (auditOleanResolutionAndShadowing #[`Evil]
      { sysrootLibDir := lib, approvedBuildRoots := #[root], searchPath? := some [evil, lib] })
    expect "T13 resolution through root_evil is outside the approved root"
      (s.violations.any (·.kind == .oleanOutsideApprovedRoot)) (renderAll s.violations)
    let (foundMods, sWalk) ← AuditM.run' (listOleanModules root)
    expect "T13 listOleanModules flags symlinked .olean inside buildLib immediately"
      (foundMods.contains `Esc && sWalk.violations.any fun v => v.kind == .oleanOutsideApprovedRoot && v.decl == `Esc)
      (renderAll sWalk.violations)

/-! ### T14: truncated and misaligned bytes (`leanprover/lean4#16737`) -/

def realOleanBytes : IO ByteArray := do IO.FS.readBinFile ((← sysLib) / "Init" / "Prelude.olean")

def isErr (r : Except OleanHeaderError OleanHeaderInfo) (p : OleanHeaderError → Bool) : Bool :=
  match r with | .error e => p e | .ok _ => false

/--
info: PASS T14 control: unmodified bytes validate
PASS T14 truncated below the header rejected
PASS T14 misaligned data size rejected
PASS T14 truncated so that the root pointer is past EOF rejected
PASS T14 file over the size limit rejected before parsing
-/
#guard_msgs in
#eval show IO Unit from do
  let bs ← realOleanBytes
  expect "T14 control: unmodified bytes validate" ((validateOleanBinaryBytes bs) matches .ok _)
  expect "T14 truncated below the header rejected" (isErr (validateOleanBinaryBytes (bs.extract 0 50)) (· matches .tooShort _))
  expect "T14 misaligned data size rejected"
    (isErr (validateOleanBinaryBytes (bs ++ ByteArray.mk #[0, 0, 0])) (· matches .misalignedDataSize _))
  let cut := ((bs.size / 2) / 8) * 8
  expect "T14 truncated so that the root pointer is past EOF rejected"
    (isErr (validateOleanBinaryBytes (bs.extract 0 cut)) (· matches .rootOutOfBounds _))
  expect "T14 file over the size limit rejected before parsing"
    (isErr (validateOleanBinaryBytes bs { maxBytes := 1024 }) (· matches .tooLarge _ _))

/-! ### T15: corrupted magic / version / githash / baseAddr wrap / root tag 244 / root child ptrs -/

def setByte (bs : ByteArray) (i : Nat) (b : UInt8) : ByteArray := bs.set! i b

def setLE64 (bs : ByteArray) (off v : Nat) : ByteArray :=
  (List.range 8).foldl (fun acc i => acc.set! (off + i) ((v / 256 ^ i) % 256).toUInt8) bs

/--
info: PASS T15 bad magic rejected
PASS T15 bad format version rejected
PASS T15 unknown flag bits rejected
PASS T15 garbage after the version terminator rejected
PASS T15 version mismatch rejected
PASS T15 non-hex githash rejected
PASS T15 githash mismatch rejected
PASS T15 zero / misaligned / wrapping base address rejected
PASS T15 scalar / misaligned / out-of-bounds root pointer rejected
PASS T15 nonzero root m_rc and non-ctor tag 244 (LeanPromise) rejected
PASS T15 oversized root m_cs_sz and corrupted root field pointers rejected
PASS T15 overlapping parent region and out-of-parent-bounds child pointer rejected
PASS T15 standalone validateOleanFile rejects symlinked .olean via lstat
-/
#guard_msgs in
#eval show IO Unit from do
  let bs ← realOleanBytes
  let some info := (validateOleanBinaryBytes bs).toOption | throw (IO.userError "control failed")
  let v := fun b => validateOleanBinaryBytes b
  expect "T15 bad magic rejected" (isErr (v (setByte bs 0 0x4f)) (· matches .badMagic))
  expect "T15 bad format version rejected" (isErr (v (setByte bs 5 3)) (· matches .badFormatVersion 3))
  expect "T15 unknown flag bits rejected" (isErr (v (setByte bs 6 0x03)) (· matches .badFlags _))
  expect "T15 garbage after the version terminator rejected" (isErr (v (setByte bs 30 0x41)) (· matches .badVersionString _))
  expect "T15 version mismatch rejected" (isErr (v (setByte bs 11 0x39)) (· matches .versionMismatch ..))
  expect "T15 non-hex githash rejected" (isErr (v (setByte bs 41 0x47)) (· matches .badGithash))
  expect "T15 githash mismatch rejected" (isErr (v (setByte bs 41 0x61)) (· matches .githashMismatch ..))
  expect "T15 zero / misaligned / wrapping base address rejected"
    (isErr (v (setLE64 bs 80 0)) (· matches .zeroBaseAddr) &&
     isErr (v (setLE64 bs 80 (info.baseAddr + 4))) (· matches .misalignedBaseAddr _) &&
     isErr (v (setLE64 bs 80 (2 ^ 64 - 8))) (· matches .baseAddrWraps))
  expect "T15 scalar / misaligned / out-of-bounds root pointer rejected"
    (isErr (v (setLE64 bs 88 (info.rootPtr + 1))) (· matches .scalarRootPtr _) &&
     isErr (v (setLE64 bs 88 (info.rootPtr + 4))) (· matches .misalignedRootPtr _) &&
     isErr (v (setLE64 bs 88 (info.baseAddr + info.fileSize))) (· matches .rootOutOfBounds _) &&
     isErr (v (setLE64 bs 88 info.baseAddr)) (· matches .rootOutOfBounds _))
  expect "T15 nonzero root m_rc and non-ctor tag 244 (LeanPromise) rejected"
    (isErr (v (setByte bs info.rootOffset 1)) (· matches .rootRcNonzero _) &&
     isErr (v (setByte bs (info.rootOffset + 7) 244)) (· matches .rootNotConstructor 244))
  expect "T15 oversized root m_cs_sz and corrupted root field pointers rejected"
    (isErr (v (setByte (setByte bs (info.rootOffset + 4) 0xff) (info.rootOffset + 5) 0xff)) (· matches .rootSizeInvalid _) &&
     isErr (v (setLE64 bs (info.rootOffset + 8) 0)) (· matches .rootChildInvalid 0 _) &&
     isErr (v (setLE64 bs (info.rootOffset + 8) (info.baseAddr + info.fileSize + 64))) (· matches .rootChildInvalid 0 _))
  -- B2 regression: overlapping parent region and `< baseAddr` pointer outside parent bounds rejected
  let overlapCfg : OleanHeaderConfig := { allowParentRegionPtrs := true, parentRegions := #[(info.baseAddr + 8, 1024)] }
  let parentCfg : OleanHeaderConfig := { allowParentRegionPtrs := true, parentRegions := #[(info.baseAddr - 4096, 2048)] }
  expect "T15 overlapping parent region and out-of-parent-bounds child pointer rejected"
    (isErr (validateOleanBinaryBytes bs overlapCfg) (· matches .overlappingParentRegion ..) &&
     isErr (validateOleanBinaryBytes (setLE64 bs (info.rootOffset + 8) 64) parentCfg) (· matches .rootChildInvalid 0 _))
  withTmpDir fun dir => do
    let realF := dir / "Real.olean"
    let symF := dir / "Sym.olean"
    IO.FS.writeBinFile realF bs
    let out ← IO.Process.output { cmd := "ln", args := #["-s", realF.toString, symF.toString] }
    unless out.exitCode == 0 do throw (IO.userError out.stderr)
    expect "T15 standalone validateOleanFile rejects symlinked .olean via lstat"
      ((← validateOleanFile symF) matches .error _)

/-! ## Vector 4 — `Init.ShareCommon`, compiler overrides, opaque-theorem readiness -/

/-! ### T16: clean control -/

namespace V4Ctl
@[inline] def inc (n : Nat) : Nat := n + 1
@[always_inline] def fastInc (n : Nat) : Nat := n + 2
@[noinline] def dec (n : Nat) : Nat := n - 1
inductive Color where | red | green
def pick : Color → Nat | .red => 0 | .green => 1
end V4Ctl

/--
info: PASS T16 benign @[inline]/@[always_inline]/@[noinline]/generated ctorIdx produce no Vector 4 findings
-/
#guard_msgs in
#eval show CoreM Unit from do
  let s ← liveAudit
  let hs := anyHits s "V4Ctl"
  expect "T16 benign @[inline]/@[always_inline]/@[noinline]/generated ctorIdx produce no Vector 4 findings" hs.isEmpty (renderAll hs)

/-! ### T17: 100%-safe `Init.ShareCommon` exploit witness (`leanprover/lean4#16779`) -/

namespace V4Share
/-- A builder written in total, safe code whose map ignores keys: the runtime's max-sharing
primitive trusts it, so `StateFactory.mk` bypasses every safety / `implemented_by` check on
user declarations. -/
def evilBuilder : ShareCommon.StateFactoryBuilder where
  Map := fun α β _ _ => List (α × β)
  mkMap := fun _ => []
  mapFind? := fun m _ => m.head?.map (·.2)
  mapInsert := fun m k v => (k, v) :: m
  Set := fun α _ _ => List α
  mkSet := fun _ => []
  setFind? := fun s _ => s.head?
  setInsert := fun s a => a :: s

def exploit : Nat :=
  let σ := ShareCommon.StateFactory.mk evilBuilder
  ((ShareCommon.State.mk σ : ShareCommon.State.{0} σ).shareCommon (5 : Nat)).1

/-- B1 regression: theorem proof body referencing `ShareCommon.shareCommon'` (erased from LCNF/IR
and absent from `ci.type`, testing that even `kernelScanTheoremBodies = false` catches it). -/
theorem proofBodyShareCommon : True :=
  let _ := ShareCommon.shareCommon' (0 : Nat)
  trivial
end V4Share

def shareImportSrc : String := "import Init.ShareCommon\ndef usesNothing : Nat := 0\n"
def shareCompiledThmSrc : String := "theorem sneakShare : True := let _ := ShareCommon.shareCommon' (0 : Nat); trivial\n"

/--
info: PASS T17 StateFactoryBuilder / StateFactory.mk / State.shareCommon references rejected
PASS T17 theorem proof-body ShareCommon reference caught even when kernelScanTheoremBodies = false
PASS T17 compiled IR / LCNF references rejected
PASS T17 direct import of Init.ShareCommon rejected
PASS T17 compiled .olean theorem-body ShareCommon caught with kernelScanTheoremBodies = false
-/
#guard_msgs in
#eval show CoreM Unit from do
  let s ← liveAudit { kernelScanTheoremBodies := false }
  let sc := hits s .shareCommonReference "V4Share"
  expect "T17 StateFactoryBuilder / StateFactory.mk / State.shareCommon references rejected"
    (sc.any (fun v => nameHas v.decl "evilBuilder") && sc.any (fun v => v.decl == `OleanShadowAndOverrideAuditProtoTests.V4Share.exploit))
    (renderAll sc)
  expect "T17 theorem proof-body ShareCommon reference caught even when kernelScanTheoremBodies = false"
    (sc.any fun v => v.decl == ``V4Share.proofBodyShareCommon) (renderAll sc)
  expect "T17 compiled IR / LCNF references rejected"
    (sc.any fun v => (v.detail.splitOn "IR").length > 1 || (v.detail.splitOn "LCNF").length > 1) (renderAll sc)
  withTmpDir fun dir => do
    let _ ← compileModule dir `ShareImp shareImportSrc
    let env ← importWith dir #[`ShareImp]
    let s ← auditImported env {} dir
    expect "T17 direct import of Init.ShareCommon rejected"
      (s.violations.any fun v => v.kind == .shareCommonImport && v.module == `ShareImp) (renderAll s.violations)
    -- B2 regression: compiled `.olean` with NO direct `import Init.ShareCommon` (`Init` imports it
    -- transitively) and `ShareCommon.shareCommon'` ONLY inside a theorem proof body under fast-sweep
    -- `kernelScanTheoremBodies = false`!
    let _ ← compileModule dir `ShareThmOnly shareCompiledThmSrc
    let envThm ← importWith dir #[`ShareThmOnly]
    let sThm ← auditImported envThm { kernelScanTheoremBodies := false } dir
    expect "T17 compiled .olean theorem-body ShareCommon caught with kernelScanTheoremBodies = false"
      (sThm.violations.any fun v => v.kind == .shareCommonReference && v.decl == `sneakShare)
      (renderAll sThm.violations)

/-! ### T18: compiler-override hooks (`google/zerocopy#4321`) + B1 custom `ctorIdx` & foreign tags -/

namespace V4Hook
@[extern "v4_hook_c_fn"] opaque externFn : Nat → Nat
def fastF (n : Nat) : Nat := n
@[implemented_by fastF] def slowF (n : Nat) : Nat := n + 0
@[export v4_hook_export_sym] def exportedF (n : Nat) : Nat := n
initialize initRef : IO.Ref Nat ← IO.mkRef 0
builtin_initialize builtinRef : IO.Ref Nat ← IO.mkRef 0
def csimpSlow (n : Nat) : Nat := n
def csimpFast (n : Nat) : Nat := n
@[csimp] theorem csimpSlow_eq : @csimpSlow = @csimpFast := rfl
@[macro_inline] def macroInlined (b : Bool) (x y : Nat) : Nat := if b then x else y
@[never_extract] def neverExtracted (n : Nat) : Nat := n
@[unbox] structure Unboxed where x : Nat
@[tagged_return, extern "v4_hook_tagged"] opaque taggedFn : Nat → Nat
end V4Hook

-- B1 regression: add a bare inductive via `addDecl` (no generated `ctorIdx`) and author a custom
-- `@[macro_inline] def BareInd.ctorIdx` with lazy multi-arg signature; also mark a foreign decl in
-- `noConfusionExt` and a custom pass in `passManagerExt` on cloned environments!
run_cmd liftCoreM do
  let indName := `OleanShadowAndOverrideAuditProtoTests.V4Hook.BareInd
  addDecl (.inductDecl [] 0 [{
    name := indName, type := mkSort .one,
    ctors := [{ name := indName.str "mk", type := mkConst indName }] }] false)

@[macro_inline] def V4Hook.BareInd.ctorIdx (b : Bool) (x y : Nat) : Nat := if b then x else y

/--
info: PASS T18 hook implemented_by
PASS T18 hook extern
PASS T18 hook export
PASS T18 hook init
PASS T18 hook builtin_init
PASS T18 hook csimp
PASS T18 hook macro_inline
PASS T18 hook never_extract
PASS T18 hook unbox
PASS T18 hook tagged_return
PASS T18 custom @[macro_inline] BareInd.ctorIdx is not exempted
PASS T18 live foreign noConfusion tag, scoped csimp, and tampered PassManager caught
-/
#guard_msgs in
#eval show CoreM Unit from do
  let s ← liveAudit
  let env ← getEnv
  let main := env.mainModule
  let hs := s.violations.filter (·.kind == .compilerOverrideHook)
  for label in ["implemented_by", "extern", "export", "init", "builtin_init", "csimp", "macro_inline",
                "never_extract", "unbox", "tagged_return"] do
    expect s!"T18 hook {label}"
      (hs.any fun v => v.detail.startsWith label && (nameHas v.decl "V4Hook" || v.decl == main))
      (renderAll hs)
  expect "T18 custom @[macro_inline] BareInd.ctorIdx is not exempted"
    (hs.any fun v => v.decl == `OleanShadowAndOverrideAuditProtoTests.V4Hook.BareInd.ctorIdx && v.detail == "macro_inline")
    (renderAll hs)
  -- B1 regression: test live foreign `noConfusionExt` tag + non-recursor `auxRecExt` tag + live
  -- `PassManager` modification without triggering `MapDeclarationExtension.insert`'s stderr panic
  let envTampered := noConfusionExt.modifyState env (·.insert ``Nat.add (.regular 4 1 2))
  let envTampered := markAuxRecursor envTampered ``V4Hook.fastF
  let envTampered := Compiler.LCNF.passManagerExt.modifyState envTampered fun (ps, pm) =>
    (ps, { pm with basePasses := #[] })
  let lib ← sysLib
  let ((), sTamp) ← AuditM.run' do
    let ctx ← mkAuditContext envTampered lib (some main)
    let views ← nonToolchainViews ctx
    auditCompilerHooks ctx views
  expect "T18 live foreign noConfusion tag, scoped csimp, and tampered PassManager caught"
    (sTamp.violations.any (fun v => v.kind == .foreignCompilerTag && v.decl == ``Nat.add) &&
     sTamp.violations.any (fun v => v.kind == .compilerOverrideHook && v.decl == ``V4Hook.fastF) &&
     sTamp.violations.any (fun v => v.kind == .compilerOverrideHook && v.decl == `compiler_pipeline))
    (renderAll sTamp.violations)

/-! ### T19: `leanprover/lean4#14896` opaque-theorem witness (Layer A + Layer B + B1 `opaque` & stmt-type) -/

namespace V4Opaque
theorem accZeroThm : Acc (fun _ _ : Nat => False) 0 := Acc.intro 0 (fun _ h => h.elim)
/-- `Acc.rec` whose major premise is a *theorem*: reducing it needs the theorem's body. -/
def accViaThm : Nat := @Acc.rec Nat (fun _ _ => False) (fun _ _ => Nat) (fun _ _ _ => 42) 0 accZeroThm
set_option linter.defProp false in
def accZeroDef : Acc (fun _ _ : Nat => False) 0 := Acc.intro 0 (fun _ h => h.elim)
/-- Contrast: the same elimination over a *definition*. -/
def accViaDef : Nat := @Acc.rec Nat (fun _ _ => False) (fun _ _ => Nat) (fun _ _ _ => 42) 0 accZeroDef
theorem accViaDef_eq : accViaDef = 42 := rfl
set_option linter.deprecated false in
/-- Native-evaluator guard target. -/
def viaReduceBool : Bool := Lean.reduceBool true
end V4Opaque

/- `accViaThm = 42` proved by `rfl` (kernel-checked directly; the elaborator does not reduce
`Acc.rec`), plus B1 regressions: an `opaque` relying on δ-reducing `accZeroThm`, and a theorem
whose *dependency theorem statement* relies on δ-reducing `accZeroThm`. -/
/- A1 regression: `accViaId` is `accViaThm` with its major premise *wrapped* as
`@id (Acc _ 0) accZeroThm` (built directly: the elaborator would abstract the wrapped proof into
an auxiliary `_proof_1` theorem). The kernel unfolds `id` and then still needs the theorem's body,
so a head-only structural test misses it. -/
run_cmd liftCoreM do
  let env ← getEnv
  let some (.defnInfo dv) := env.find? ``V4Opaque.accViaThm | throwError "missing accViaThm"
  let some tci := env.find? ``V4Opaque.accZeroThm | throwError "missing accZeroThm"
  let wrapped := dv.value.replace fun e =>
    if e.isConstOf ``V4Opaque.accZeroThm then some (mkApp2 (mkConst ``id [.zero]) tci.type e) else none
  let n := `OleanShadowAndOverrideAuditProtoTests.V4Opaque.accViaId
  addDecl (.defnDecl { dv with name := n, value := wrapped, all := [n] })
  -- B2 regression (Layer A): wrap `accZeroThm` in a separate `Prop`-valued `def wrapAcc := accZeroThm`
  -- so `Expr.find?` on `accViaWrapDef` sees NO `.thmInfo` constant directly in the major premise!
  let wrapName := `OleanShadowAndOverrideAuditProtoTests.V4Opaque.wrapAcc
  addDecl (.defnDecl {
    name := wrapName, levelParams := [], type := tci.type,
    value := mkConst ``V4Opaque.accZeroThm, hints := .regular 1, safety := .safe, all := [wrapName] })
  let wrappedViaDef := dv.value.replace fun e =>
    if e.isConstOf ``V4Opaque.accZeroThm then some (mkConst wrapName) else none
  let n2 := `OleanShadowAndOverrideAuditProtoTests.V4Opaque.accViaWrapDef
  addDecl (.defnDecl { dv with name := n2, value := wrappedViaDef, all := [n2] })

run_cmd liftCoreM do
  let n42 := mkNatLit 42
  let eqTy := mkApp3 (mkConst ``Eq [1]) (mkConst ``Nat) (mkConst ``V4Opaque.accViaThm) n42
  let eqRefl := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Nat) n42
  addDecl (.thmDecl { name := `OleanShadowAndOverrideAuditProtoTests.V4Opaque.accViaThm_eq,
                      levelParams := [], type := eqTy, value := eqRefl })
  addDecl (.opaqueDecl { name := `OleanShadowAndOverrideAuditProtoTests.V4Opaque.opaqueViaThm,
                         levelParams := [], type := eqTy, value := eqRefl, isUnsafe := false })
  let stmtNeedsDeltaTy := Expr.letE `h eqTy eqRefl (mkConst ``True) false
  addDecl (.thmDecl { name := `OleanShadowAndOverrideAuditProtoTests.V4Opaque.depStmtNeedsDelta,
                      levelParams := [], type := stmtNeedsDeltaTy, value := mkConst ``True.intro })
  addDecl (.thmDecl { name := `OleanShadowAndOverrideAuditProtoTests.V4Opaque.accViaId_eq, levelParams := [],
                      type := mkApp3 (mkConst ``Eq [1]) (mkConst ``Nat) (mkConst `OleanShadowAndOverrideAuditProtoTests.V4Opaque.accViaId) n42,
                      value := eqRefl })
  addDecl (.thmDecl { name := `OleanShadowAndOverrideAuditProtoTests.V4Opaque.viaDepStmt,
                      levelParams := [], type := mkConst ``True,
                      value := mkConst `OleanShadowAndOverrideAuditProtoTests.V4Opaque.depStmtNeedsDelta })
  -- B2 regression (Layer B): inductive constructor index `SneakyWitness.mk : SneakyWitness accViaThm`
  -- + `theorem exploitViaInduct : SneakyWitness 42 := SneakyWitness.mk`, and `WellFounded.fix` over a theorem!
  let indName := `OleanShadowAndOverrideAuditProtoTests.V4Opaque.SneakyWitness
  let ctorName := indName.str "mk"
  addDecl (.inductDecl [] 0 [{
    name := indName, type := mkForall `n .default (mkConst ``Nat) (mkSort .zero),
    ctors := [{ name := ctorName, type := mkApp (mkConst indName) (mkConst ``V4Opaque.accViaThm) }] }] false)
  addDecl (.thmDecl {
    name := `OleanShadowAndOverrideAuditProtoTests.V4Opaque.exploitViaInduct,
    levelParams := [],
    type := mkApp (mkConst indName) n42,
    value := mkConst ctorName })

theorem V4Opaque.wfEmptyThm : WellFounded (fun _ _ : Nat => False) :=
  WellFounded.intro fun x => Acc.intro x (fun _ h => False.elim h)

def V4Opaque.wfFixViaThm : Nat :=
  @WellFounded.fix Nat (fun _ => Nat) (fun _ _ => False) V4Opaque.wfEmptyThm (fun _ _ => 42) 0

run_cmd liftCoreM do
  let n42 := mkNatLit 42
  addDecl (.thmDecl {
    name := `OleanShadowAndOverrideAuditProtoTests.V4Opaque.wfFixViaThm_eq,
    levelParams := [],
    type := mkApp3 (mkConst ``Eq [1]) (mkConst ``Nat) (mkConst ``V4Opaque.wfFixViaThm) n42,
    value := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Nat) n42 })

/--
info: PASS T19 Layer A flags the theorem in the Acc.rec major premise
PASS T19 Layer A does not flag the definition contrast
PASS T19 Layer B: rfl theorem accepted, rejected once theorems are kernel-opaque
PASS T19 Layer B: opaque declaration relying on theorem body caught
PASS T19 Layer B: dependency theorem whose statement relies on theorem body caught
PASS T19 Layer B: definition contrast replays cleanly
PASS T19 Layer B refuses to run the kernel when a native evaluator is reachable
PASS T19 live audit reports opaqueTheoremDeltaReliance for the replay target
PASS T19 Layer A flags a theorem wrapped in `id` inside the major premise
PASS T19 head-only test alone misses the `id`-wrapped theorem
PASS T19 Layer B catches the `id`-wrapped theorem reliance
PASS T19 Layer A flags a theorem aliased behind a Prop definition in the major premise
PASS T19 Layer B catches inductive-constructor and WellFounded.fix theorem δ-reliance
-/
#guard_msgs in
#eval show CoreM Unit from do
  let env ← getEnv
  let some thmCi := env.find? ``V4Opaque.accViaThm | throwError "missing"
  let some defCi := env.find? ``V4Opaque.accViaDef | throwError "missing"
  expect "T19 Layer A flags the theorem in the Acc.rec major premise"
    ((scanOpaqueTheoremReliance env thmCi) matches .ok #[(``V4Opaque.accZeroThm, _)])
  expect "T19 Layer A does not flag the definition contrast" ((scanOpaqueTheoremReliance env defCi) matches .ok #[])
  let r ← checkOpaqueTheoremReplay env `OleanShadowAndOverrideAuditProtoTests.V4Opaque.accViaThm_eq
  expect "T19 Layer B: rfl theorem accepted, rejected once theorems are kernel-opaque" (r matches .deltaReliance ..) (repr r |>.pretty)
  let rOp ← checkOpaqueTheoremReplay env `OleanShadowAndOverrideAuditProtoTests.V4Opaque.opaqueViaThm
  expect "T19 Layer B: opaque declaration relying on theorem body caught" (rOp matches .deltaReliance ..) (repr rOp |>.pretty)
  let rDep ← checkOpaqueTheoremReplay env `OleanShadowAndOverrideAuditProtoTests.V4Opaque.viaDepStmt
  expect "T19 Layer B: dependency theorem whose statement relies on theorem body caught" (rDep matches .deltaReliance ..) (repr rDep |>.pretty)
  let r ← checkOpaqueTheoremReplay env ``V4Opaque.accViaDef_eq
  expect "T19 Layer B: definition contrast replays cleanly" (r matches .clean .. || r matches .noTheoremDependencies) (repr r |>.pretty)
  let r ← checkOpaqueTheoremReplay env ``V4Opaque.viaReduceBool
  expect "T19 Layer B refuses to run the kernel when a native evaluator is reachable" (r matches .refusedNativeEvaluator)
  let s ← liveAudit { replayTargets := #[`OleanShadowAndOverrideAuditProtoTests.V4Opaque.accViaThm_eq, ``V4Opaque.accViaDef_eq] }
  expect "T19 live audit reports opaqueTheoremDeltaReliance for the replay target"
    ((s.violations.filter (·.kind == .opaqueTheoremDeltaReliance)).map (·.decl) == #[`OleanShadowAndOverrideAuditProtoTests.V4Opaque.accViaThm_eq] &&
      s.policyFlags.any fun v => v.decl == ``V4Opaque.accViaThm) (renderAll s.violations)
  let some idCi := env.find? `OleanShadowAndOverrideAuditProtoTests.V4Opaque.accViaId | throwError "missing"
  expect "T19 Layer A flags a theorem wrapped in `id` inside the major premise"
    ((scanOpaqueTheoremReliance env idCi) matches .ok #[(``V4Opaque.accZeroThm, _)])
  expect "T19 head-only test alone misses the `id`-wrapped theorem"
    (match idCi.value? with
     | some v => (v.find? fun e => (e.isAppOfArity ``Acc.rec 6) && (isTheoremHead env (e.getArg! 5)).isSome).isNone
     | none => false)
  let rId ← checkOpaqueTheoremReplay env `OleanShadowAndOverrideAuditProtoTests.V4Opaque.accViaId_eq
  expect "T19 Layer B catches the `id`-wrapped theorem reliance" (rId matches .deltaReliance ..) (repr rId |>.pretty)
  let some wrapDefCi := env.find? `OleanShadowAndOverrideAuditProtoTests.V4Opaque.accViaWrapDef | throwError "missing wrapDef"
  expect "T19 Layer A flags a theorem aliased behind a Prop definition in the major premise"
    ((scanOpaqueTheoremReliance env wrapDefCi) matches .ok #[(``V4Opaque.accZeroThm, _)])
  let rInd ← checkOpaqueTheoremReplay env `OleanShadowAndOverrideAuditProtoTests.V4Opaque.exploitViaInduct
  let rWf ← checkOpaqueTheoremReplay env `OleanShadowAndOverrideAuditProtoTests.V4Opaque.wfFixViaThm_eq
  expect "T19 Layer B catches inductive-constructor and WellFounded.fix theorem δ-reliance"
    ((rInd matches .deltaReliance ..) && (rWf matches .deltaReliance ..))
    s!"ind={repr rInd |>.pretty} wf={repr rWf |>.pretty}"

/-! ## T21: non-toolchain module planted next to the toolchain library + B2 diamond-DAG & sysroot-bridge regressions

A build-library sweep imports through `[buildLib, sysroot]`. A module that is *not* toolchain-named
but sits in the sysroot directory resolves there and was loaded by `importModules` without ever
passing Vector 3. Also tests B2 regressions: a 6-module diamond DAG (`D1..D6 -> Planted`) that
previously starved an undeduplicated `todo` queue, a tampered-githash `Init.Fake` in `sysroot`
rejected *before* `importModules`, and a toolchain-named `Init.Bridge` in `sysroot` transitively
importing `Planted`. -/

def plantedSrc : String := "prelude\nimport Init.Prelude\ndef plantedVal : Nat := 7\n"
def plantRootSrc : String := "prelude\nimport Init.Prelude\nimport Planted\ndef usesPlanted : Nat := plantedVal\n"

/--
info: PASS T21 planted non-toolchain sysroot module rejected before import
PASS T21 its importer is not loaded
PASS T21 nothing was audited from the planted closure
PASS T21 6-module diamond DAG does not starve pre-import boundary queue
PASS T21 tampered-githash toolchain boundary import rejected before importModules
PASS T21 transitive Init.Bridge -> Planted sysroot escape caught
-/
#guard_msgs in
#eval show IO Unit from do
  let lib ← sysLib
  withTmpDir fun dir => do
    let fakeSys := dir / "sys"
    let build := dir / "build"
    IO.FS.createDirAll (fakeSys / "Init")
    IO.FS.createDirAll build
    for ext in partExts do
      let src := lib / "Init" / s!"Prelude.{ext}"
      if ← entryExists src then IO.FS.writeBinFile (fakeSys / "Init" / s!"Prelude.{ext}") (← IO.FS.readBinFile src)
    let _ ← compileModule fakeSys `Planted plantedSrc (some s!"{fakeSys}:{lib}")
    IO.FS.removeFile (fakeSys / "Planted.lean")
    let _ ← compileModule build `PlantRoot plantRootSrc (some s!"{build}:{fakeSys}:{lib}")
    IO.FS.removeFile (build / "PlantRoot.lean")
    let ((), s) ← AuditM.run' (auditBuildLibrary build fakeSys {} (some #[`PlantRoot]))
    expect "T21 planted non-toolchain sysroot module rejected before import"
      (s.violations.any fun v => v.kind == .oleanOutsideApprovedRoot && v.decl == `Planted) (renderAll s.violations)
    expect "T21 its importer is not loaded"
      (s.violations.any fun v => v.kind == .environmentLoadFailed && v.decl == `PlantRoot) (renderAll s.violations)
    expect "T21 nothing was audited from the planted closure" (s.modulesChecked == 0 && s.importMs == 0) s!"{s.modulesChecked}"
    -- B2-1 regression: 6-module diamond DAG `D1 -> D2..D6`, `D2 -> D3..D6`, ..., `D6 -> Planted`
    let buildDag := dir / "buildDag"
    IO.FS.createDirAll buildDag
    let _ ← compileModule buildDag `D6 "prelude\nimport Init.Prelude\nimport Planted\ndef d6 : Nat := plantedVal\n" (some s!"{buildDag}:{fakeSys}:{lib}")
    let _ ← compileModule buildDag `D5 "prelude\nimport Init.Prelude\nimport D6\ndef d5 : Nat := d6\n" (some s!"{buildDag}:{fakeSys}:{lib}")
    let _ ← compileModule buildDag `D4 "prelude\nimport Init.Prelude\nimport D5\nimport D6\ndef d4 : Nat := Nat.add d5 d6\n" (some s!"{buildDag}:{fakeSys}:{lib}")
    let _ ← compileModule buildDag `D3 "prelude\nimport Init.Prelude\nimport D4\nimport D5\nimport D6\ndef d3 : Nat := d4\n" (some s!"{buildDag}:{fakeSys}:{lib}")
    let _ ← compileModule buildDag `D2 "prelude\nimport Init.Prelude\nimport D3\nimport D4\nimport D5\nimport D6\ndef d2 : Nat := d3\n" (some s!"{buildDag}:{fakeSys}:{lib}")
    let _ ← compileModule buildDag `D1 "prelude\nimport Init.Prelude\nimport D2\nimport D3\nimport D4\nimport D5\nimport D6\ndef d1 : Nat := d2\n" (some s!"{buildDag}:{fakeSys}:{lib}")
    for nm in ["D1", "D2", "D3", "D4", "D5", "D6"] do IO.FS.removeFile (buildDag / s!"{nm}.lean")
    let ((), sDag) ← AuditM.run' (auditBuildLibrary buildDag fakeSys {} (some #[`D1]))
    expect "T21 6-module diamond DAG does not starve pre-import boundary queue"
      (sDag.importMs == 0 && sDag.violations.any fun v => v.kind == .oleanOutsideApprovedRoot && v.decl == `Planted)
      (renderAll sDag.violations)
    -- B2-2a regression: forged-githash `Init.Fake` in `fakeSys` caught *before* `importModules`
    let fakeOlean ← compileModule fakeSys `Init.Fake "prelude\nimport Init.Prelude\ndef fakeTc : Nat := 1\n" (some s!"{fakeSys}:{lib}")
    IO.FS.removeFile (fakeSys / "Init" / "Fake.lean")
    let buildBadHdr := dir / "buildBadHdr"
    IO.FS.createDirAll buildBadHdr
    let _ ← compileModule buildBadHdr `UseFake "prelude\nimport Init.Prelude\nimport Init.Fake\ndef u : Nat := fakeTc\n" (some s!"{buildBadHdr}:{fakeSys}:{lib}")
    IO.FS.removeFile (buildBadHdr / "UseFake.lean")
    let rawFake ← IO.FS.readBinFile fakeOlean
    IO.FS.writeBinFile fakeOlean (setByte rawFake 41 0x61)
    let ((), sHdr) ← AuditM.run' (auditBuildLibrary buildBadHdr fakeSys {} (some #[`UseFake]))
    expect "T21 tampered-githash toolchain boundary import rejected before importModules"
      (sHdr.importMs == 0 && sHdr.violations.any fun v => v.kind == .oleanHeaderInvalid && v.decl == `Init.Fake)
      (renderAll sHdr.violations)
    -- B2-2b regression: valid-header `Init.Bridge` in `fakeSys` transitively importing `Planted`
    let _ ← compileModule fakeSys `Init.Bridge "prelude\nimport Init.Prelude\nimport Planted\ndef br : Nat := plantedVal\n" (some s!"{fakeSys}:{lib}")
    IO.FS.removeFile (fakeSys / "Init" / "Bridge.lean")
    let buildBr := dir / "buildBr"
    IO.FS.createDirAll buildBr
    let _ ← compileModule buildBr `UseBridge "prelude\nimport Init.Prelude\nimport Init.Bridge\ndef ub : Nat := br\n" (some s!"{buildBr}:{fakeSys}:{lib}")
    IO.FS.removeFile (buildBr / "UseBridge.lean")
    let ((), sBr) ← AuditM.run' (auditBuildLibrary buildBr fakeSys {} (some #[`UseBridge]))
    expect "T21 transitive Init.Bridge -> Planted sysroot escape caught"
      (sBr.violations.any fun v => v.kind == .oleanOutsideApprovedRoot && v.decl == `Planted)
      (renderAll sBr.violations)

/-! ## T22: large whole-module audits screen theorem bodies in every mode (A2 regression)

Above `implicitClosureMaxConsts` a whole-module audit no longer computes the exact closure and
relies on the shared kernel traversal to find direct `sorryAx` references. That traversal must see
compiled theorem bodies in both the structural and the constant-only (fast) configuration. The
threshold is lowered to `0` so a small compiled module takes the large-audit path. -/

def sorryThmSrc : String := "theorem smuggled : 1 = 2 := sorryAx _ true\ndef benign : Nat := 3\n"

/--
info: PASS T22 large-audit path, structural scan on: sorryAx in a compiled theorem body caught
PASS T22 large-audit path, constant-only screen: sorryAx in a compiled theorem body caught
PASS T22 large-audit path, theorem bodies excluded from find?: still caught by the constant screen
-/
#guard_msgs in
#eval show IO Unit from do
  withTmpDir fun dir => do
    let _ ← compileModule dir `SorryThm sorryThmSrc
    let env ← importWith dir #[`SorryThm]
    let big : AxiomPolicy := { implicitClosureMaxConsts := 0 }
    let caught (s : AuditSummary) : Bool :=
      s.violations.any fun v => v.kind == .referencedUnapprovedAxiom && v.decl == `sorryAx
    let s ← auditImported env { axioms := big } dir
    expect "T22 large-audit path, structural scan on: sorryAx in a compiled theorem body caught" (caught s) (renderAll s.violations)
    let s ← auditImported env { axioms := big, runStructuralOpaqueScan := false } dir
    expect "T22 large-audit path, constant-only screen: sorryAx in a compiled theorem body caught" (caught s) (renderAll s.violations)
    let s ← auditImported env { axioms := big, kernelScanTheoremBodies := false } dir
    expect "T22 large-audit path, theorem bodies excluded from find?: still caught by the constant screen"
      (caught s) (renderAll s.violations)

-- Deep sweep (full Layer A + every expression via `find?`): zero findings, time reported.
#eval sweep "T20 deep sweep" {} none

-- Fast sweep, deliberately the last command of the file: the frontend elaborates later commands
-- concurrently with a running `#eval`, which would otherwise inflate the measured wall time. Every
-- type, value and theorem body is screened for `Init.ShareCommon` / forbidden-axiom constants by
-- one C++ `getUsedConstants` pass per module; the Layer A walk runs in the deep sweep above.
-- Timed against 5 s.
#eval sweep "T20 fast sweep" { runStructuralOpaqueScan := false } (some 5000)

end OleanShadowAndOverrideAuditProtoTests
