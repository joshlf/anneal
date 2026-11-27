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
def compileModule (root : System.FilePath) (mod : Name) (src : String) : IO System.FilePath := do
  let rel := modRelPath mod
  let leanFile := root / (rel ++ ".lean")
  if let some p := leanFile.parent then IO.FS.createDirAll p
  IO.FS.writeFile leanFile src
  let olean := root / (rel ++ ".olean")
  let leanBin := (← findSysroot) / "bin" / "lean"
  let out ← IO.Process.output { cmd := leanBin.toString, args := #["-R", root.toString, "-o", olean.toString, leanFile.toString] }
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
    (s.violations.any fun v => v.decl == privName `Assumptions.Ok `V1Forge.ax && v.kind == .unreferencedSorryOrNativeAxiom ||
      v.decl == privName `Assumptions.Ok `V1Forge.ax && v.kind == .unreferencedTopLevelAxiom)
    (renderAll (anyHits s "V1Forge"))

/-! ### T4: user-suffix spoofing (`Init.*`, `sorryAx`, `Trusted.*`) -/

private def _root_.Init.V1Spoof.x : Nat := 0
private def _root_.Trusted.V1Spoof.y : Nat := 0
private def _root_.Lean.V1Spoof.z : Nat := 0

run_cmd liftCoreM do
  let env ← getEnv
  forgeDef (privName env.mainModule `sorryAx)
  forgeDef (privName env.mainModule `Lean.ofReduceBool)

/--
info: PASS T4 Init.* user suffix rejected
PASS T4 Trusted.* user suffix rejected
PASS T4 Lean.* user suffix rejected
PASS T4 sorryAx user suffix rejected
PASS T4 Lean.ofReduceBool user suffix rejected
-/
#guard_msgs in
#eval show CoreM Unit from do
  let main := (← getEnv).mainModule
  let s ← liveAudit
  let sp := s.violations.filter (·.kind == .privateUserSuffixSpoof)
  expect "T4 Init.* user suffix rejected" (sp.any (·.decl == privName main `Init.V1Spoof.x))
  expect "T4 Trusted.* user suffix rejected" (sp.any (·.decl == privName main `Trusted.V1Spoof.y))
  expect "T4 Lean.* user suffix rejected" (sp.any (·.decl == privName main `Lean.V1Spoof.z))
  expect "T4 sorryAx user suffix rejected" (sp.any (·.decl == privName main `sorryAx))
  expect "T4 Lean.ofReduceBool user suffix rejected" (sp.any (·.decl == privName main `Lean.ofReduceBool))

/-! ### T5: malformed, nested and non-leading `_private` declarations in the live environment -/

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
-/
#guard_msgs in
#eval show CoreM Unit from do
  let main := (← getEnv).mainModule
  let s ← liveAudit
  let bad := s.violations.filter (·.kind == .malformedPrivateName)
  expect "T5 non-leading _private declaration rejected" (bad.any (·.decl == `V1Bad ++ privName main `nonLeading))
  expect "T5 nested _private declaration rejected" (bad.any (·.decl == privName main (privName main `V1Bad.nested)))
  expect "T5 non-zero separator declaration rejected" (bad.any (·.decl == Name.mkNum (`_private ++ main) 1 ++ `V1Bad.nonZero))
  expect "T5 missing separator declaration rejected" (bad.any (·.decl == `_private ++ main ++ `V1Bad.noSeparator))

/-! ## Vector 2 — unreferenced top-level axioms (`leanprover/lean4#16781`) -/

/-! ### T6: foundational control -/

theorem V2Ctl.claim (p q : Prop) (h : p ↔ q) : p = q := propext h
theorem V2Ctl.choice (α : Type) (h : Nonempty α) : ∃ _ : α, True := ⟨Classical.choice h, trivial⟩

/--
info: PASS T6 propext / Classical.choice admitted with their toolchain modules
PASS T6 Classical.choice rejected when allowClassicalChoice = false
-/
#guard_msgs in
#eval show CoreM Unit from do
  let s ← liveAudit { axiomRoots? := some #[``V2Ctl.claim, ``V2Ctl.choice] }
  expect "T6 propext / Classical.choice admitted with their toolchain modules"
    (!s.violations.any (·.kind == .referencedUnapprovedAxiom)) (renderAll (s.violations.filter (·.kind == .referencedUnapprovedAxiom)))
  let s ← liveAudit { axioms := { allowClassicalChoice := false }, axiomRoots? := some #[``V2Ctl.choice] }
  expect "T6 Classical.choice rejected when allowClassicalChoice = false"
    (s.violations.any fun v => v.kind == .referencedUnapprovedAxiom && v.decl == ``Classical.choice)

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
PASS T9 dead _native axiom reported as sorryAx-class / native
PASS T9 reachable sorryAx rejected
-/
#guard_msgs in
#eval show CoreM Unit from do
  withTmpDir fun dir => do
    let _ ← compileModule dir `Assumptions.Extra assumptionSrc
    let env ← importWith dir #[`Assumptions.Extra]
    let s ← auditImported env {} dir
    expect "T9 unreferenced Assumptions axiom rejected when allowAssumptions = false"
      (s.violations.any fun v => v.kind == .unreferencedAssumptionAxiom && v.decl == `Assumptions.Extra.ax) (renderAll s.violations)
    let s ← auditImported env { axioms := { allowAssumptions := true, allowedAssumptions := NameSet.empty.insert `Assumptions.Extra.ax } } dir
    expect "T9 Assumptions axiom admitted only when allowAssumptions = true and allowlisted"
      (!s.violations.any fun v => v.decl == `Assumptions.Extra.ax) (renderAll s.violations)
  let s ← liveAudit { axiomRoots? := some #[`V2Sorry.claim] }
  expect "T9 dead _native axiom reported as sorryAx-class / native"
    (s.violations.any fun v => v.kind == .unreferencedSorryOrNativeAxiom && v.decl == `V2Native._native.native_decide.ax_1)
  expect "T9 reachable sorryAx rejected"
    (s.violations.any fun v => v.kind == .referencedUnapprovedAxiom && v.decl == `sorryAx)

/-! ### T10: exported-only (`isModule`) environments fail closed -/

/--
info: PASS T10 exported-level import is a module-system environment
PASS T10 the exported view hides the private axiom
PASS T10 auditUnreferencedAxioms fails closed on the exported-only view
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

/-! ### T12: multi-root shadowing and toolchain shadowing -/

/--
info: PASS T12 module present in two search-path roots is reported as shadowed
PASS T12 toolchain module copied into a non-sysroot root is reported
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

/-! ### T13: symlink escape, path-prefix confusion and `..` -/

/--
info: PASS T13 regular file inside the root accepted
PASS T13 prefix-confused sibling root (root_evil vs root) rejected
PASS T13 symlinked artifact escaping the root rejected
PASS T13 symlinked directory component rejected
PASS T13 dot-dot component rejected
PASS T13 resolution through root_evil is outside the approved root
-/
#guard_msgs in
#eval show IO Unit from do
  let lib ← sysLib
  withTmpDir fun dir => do
    let root := dir / "root"
    let evil := dir / "root_evil"
    let outside := dir / "outside"
    for d in [root, evil, outside, root / "Sub"] do IO.FS.createDirAll d
    let bytes ← IO.FS.readBinFile (lib / "Init" / "Prelude.olean")
    IO.FS.writeBinFile (root / "Good.olean") bytes
    IO.FS.writeBinFile (evil / "Evil.olean") bytes
    IO.FS.writeBinFile (outside / "Esc.olean") bytes
    let ln (target link : System.FilePath) : IO Unit := do
      let out ← IO.Process.output { cmd := "ln", args := #["-s", target.toString, link.toString] }
      unless out.exitCode == 0 do throw (IO.userError out.stderr)
    ln (outside / "Esc.olean") (root / "Esc.olean")
    ln outside (root / "Link")
    expect "T13 regular file inside the root accepted" ((← pathWithinRoot root (root / "Good.olean")) matches .ok _)
    expect "T13 prefix-confused sibling root (root_evil vs root) rejected"
      ((← pathWithinRoot root (evil / "Evil.olean")) matches .error _)
    expect "T13 symlinked artifact escaping the root rejected" ((← pathWithinRoot root (root / "Esc.olean")) matches .error _)
    expect "T13 symlinked directory component rejected" ((← pathWithinRoot root (root / "Link" / "Esc.olean")) matches .error _)
    expect "T13 dot-dot component rejected" ((← pathWithinRoot root (root / "Sub" / ".." / "Good.olean")) matches .error _)
    let ((), s) ← AuditM.run' (auditOleanResolutionAndShadowing #[`Evil]
      { sysrootLibDir := lib, approvedBuildRoots := #[root], searchPath? := some [evil, lib] })
    expect "T13 resolution through root_evil is outside the approved root"
      (s.violations.any (·.kind == .oleanOutsideApprovedRoot)) (renderAll s.violations)

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

/-! ### T15: corrupted magic / version / githash / root pointer / `m_rc` -/

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
PASS T15 zero / misaligned base address rejected
PASS T15 scalar / misaligned / out-of-bounds root pointer rejected
PASS T15 nonzero root m_rc rejected
PASS T15 oversized root m_cs_sz rejected
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
  expect "T15 zero / misaligned base address rejected"
    (isErr (v (setLE64 bs 80 0)) (· matches .zeroBaseAddr) && isErr (v (setLE64 bs 80 (info.baseAddr + 4))) (· matches .misalignedBaseAddr _))
  expect "T15 scalar / misaligned / out-of-bounds root pointer rejected"
    (isErr (v (setLE64 bs 88 (info.rootPtr + 1))) (· matches .scalarRootPtr _) &&
     isErr (v (setLE64 bs 88 (info.rootPtr + 4))) (· matches .misalignedRootPtr _) &&
     isErr (v (setLE64 bs 88 (info.baseAddr + info.fileSize))) (· matches .rootOutOfBounds _) &&
     isErr (v (setLE64 bs 88 info.baseAddr)) (· matches .rootOutOfBounds _))
  expect "T15 nonzero root m_rc rejected" (isErr (v (setByte bs info.rootOffset 1)) (· matches .rootRcNonzero _))
  expect "T15 oversized root m_cs_sz rejected"
    (isErr (v (setByte (setByte bs (info.rootOffset + 4) 0xff) (info.rootOffset + 5) 0xff)) (· matches .rootSizeInvalid _))

/-! ## Vector 4 — `Init.ShareCommon`, compiler overrides, opaque-theorem readiness -/

/-! ### T16: clean control -/

namespace V4Ctl
@[inline] def inc (n : Nat) : Nat := n + 1
@[noinline] def dec (n : Nat) : Nat := n - 1
inductive Color where | red | green
def pick : Color → Nat | .red => 0 | .green => 1
end V4Ctl

/--
info: PASS T16 benign @[inline]/@[noinline]/generated ctorIdx produce no Vector 4 findings
-/
#guard_msgs in
#eval show CoreM Unit from do
  let s ← liveAudit
  let hs := anyHits s "V4Ctl"
  expect "T16 benign @[inline]/@[noinline]/generated ctorIdx produce no Vector 4 findings" hs.isEmpty (renderAll hs)

/-! ### T17: 100%-safe `Init.ShareCommon` exploit witness (`leanprover/lean4#16779`) -/

namespace V4Share
/-- A builder written in total, safe code whose map ignores keys: the runtime's max-sharing
primitive trusts it, so `StateFactory.mk` bypasses every `unsafe` / `implemented_by` check on
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
end V4Share

def shareImportSrc : String := "import Init.ShareCommon\ndef usesNothing : Nat := 0\n"

/--
info: PASS T17 StateFactoryBuilder / StateFactory.mk / State.shareCommon references rejected
PASS T17 compiled IR / LCNF references rejected
PASS T17 direct import of Init.ShareCommon rejected
-/
#guard_msgs in
#eval show CoreM Unit from do
  let s ← liveAudit
  let sc := hits s .shareCommonReference "V4Share"
  expect "T17 StateFactoryBuilder / StateFactory.mk / State.shareCommon references rejected"
    (sc.any (fun v => nameHas v.decl "evilBuilder") && sc.any (fun v => v.decl == `OleanShadowAndOverrideAuditProtoTests.V4Share.exploit))
    (renderAll sc)
  expect "T17 compiled IR / LCNF references rejected"
    (sc.any fun v => (v.detail.splitOn "IR").length > 1 || (v.detail.splitOn "LCNF").length > 1) (renderAll sc)
  withTmpDir fun dir => do
    let _ ← compileModule dir `ShareImp shareImportSrc
    let env ← importWith dir #[`ShareImp]
    let s ← auditImported env {} dir
    expect "T17 direct import of Init.ShareCommon rejected"
      (s.violations.any fun v => v.kind == .shareCommonImport && v.module == `ShareImp) (renderAll s.violations)

/-! ### T18: compiler-override hooks (`google/zerocopy#4321`) -/

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
-/
#guard_msgs in
#eval show CoreM Unit from do
  let s ← liveAudit
  let main := (← getEnv).mainModule
  let hs := s.violations.filter (·.kind == .compilerOverrideHook)
  for label in ["implemented_by", "extern", "export", "init", "builtin_init", "csimp", "macro_inline",
                "never_extract", "unbox", "tagged_return"] do
    expect s!"T18 hook {label}"
      (hs.any fun v => v.detail.startsWith label && (nameHas v.decl "V4Hook" || v.decl == main))
      (renderAll hs)

/-! ### T19: `leanprover/lean4#14896` opaque-theorem witness (Layer A + Layer B) -/

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
`Acc.rec`). -/
run_cmd liftCoreM do
  let n42 := mkNatLit 42
  addDecl (.thmDecl { name := `OleanShadowAndOverrideAuditProtoTests.V4Opaque.accViaThm_eq, levelParams := []
                      type := mkApp3 (mkConst ``Eq [1]) (mkConst ``Nat) (mkConst ``V4Opaque.accViaThm) n42
                      value := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Nat) n42 })

/--
info: PASS T19 Layer A flags the theorem in the Acc.rec major premise
PASS T19 Layer A does not flag the definition contrast
PASS T19 Layer B: rfl theorem accepted, rejected once theorems are kernel-opaque
PASS T19 Layer B: definition contrast replays cleanly
PASS T19 Layer B refuses to run the kernel when a native evaluator is reachable
PASS T19 live audit reports opaqueTheoremDeltaReliance for the replay target
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
  let r ← checkOpaqueTheoremReplay env ``V4Opaque.accViaDef_eq
  expect "T19 Layer B: definition contrast replays cleanly" (r matches .clean .. || r matches .noTheoremDependencies) (repr r |>.pretty)
  let r ← checkOpaqueTheoremReplay env ``V4Opaque.viaReduceBool
  expect "T19 Layer B refuses to run the kernel when a native evaluator is reachable" (r matches .refusedNativeEvaluator)
  let s ← liveAudit { replayTargets := #[`OleanShadowAndOverrideAuditProtoTests.V4Opaque.accViaThm_eq, ``V4Opaque.accViaDef_eq] }
  expect "T19 live audit reports opaqueTheoremDeltaReliance for the replay target"
    ((s.violations.filter (·.kind == .opaqueTheoremDeltaReliance)).map (·.decl) == #[`OleanShadowAndOverrideAuditProtoTests.V4Opaque.accViaThm_eq] &&
     s.policyFlags.any fun v => v.decl == ``V4Opaque.accViaThm) (renderAll s.violations)

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

-- Fast sweep (theorem bodies are not screened; everything else is): timed against 5 s.
#eval sweep "T20 fast sweep" { runStructuralOpaqueScan := false, kernelScanTheoremBodies := false } (some 5000)

-- Deep sweep (theorem bodies screened, Layer A structural scan on): zero findings, time reported.
#eval sweep "T20 deep sweep" {} none

end OleanShadowAndOverrideAuditProtoTests
