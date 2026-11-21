import Lean.Replay
import Lean.Compiler.IR.CompilerM
import Lean.Compiler.IR.EmitUtil
import Lean.Compiler.ImplementedByAttr
import Lean.Compiler.ExternAttr
import Lean.Compiler.ExportAttr
import Lean.Compiler.InitAttr
import Lean.Compiler.CSimpAttr
import Lean.Compiler.LCNF.PhaseExt
import Lean.Compiler.LCNF.Main
import Lean.Compiler.LCNF.Passes
import Lean.Compiler.LCNF.Simp.ConstantFold
import Lean.Compiler.LCNF.ElimDeadBranches
import Lean.Compiler.LCNF.Util
import Lean.AuxRecursor
import Lean.Meta.Basic
import Lean.Meta.InferType
import Lean.Meta.CasesInfo
import Lean.Meta.Constructions.CasesOn
import Lean.Meta.Constructions.SparseCasesOn
import Lean.Util.Path

/-!
Compiled `.olean` / `.olean.private` / `.ir` environment auditor, pinned to Lean 4.34.1.

The auditor is a standalone program (`OleanEnvAuditor <request.json> <result.json>`) that loads
one module set exactly once at `OLeanLevel.private` with `loadExts := false`, `trustLevel := 0`
and no plugins, and then audits what the compiled artifacts actually contain:

* provenance of every loaded module and of every companion artifact part (`.olean`,
  `.olean.server`, `.olean.private`, `.ir.sig`, `.ir`), by canonical path, never by name;
* the complete constant inventory of every non-toolchain module (all of its declarations are
  roots), including the kernel dependency closure through toolchain modules;
* the axiom policy (locked foundational axioms by name *and* toolchain origin, `sorryAx`,
  native-evaluation axioms, file-local test axioms);
* `unsafe` / `partial` declarations and forged `_unsafe_rec` code-generation companions;
* compiler overrides that make compiled code disagree with the kernel: `@[implemented_by]`,
  `@[extern]`, `@[export]`, `@[init]` / `@[builtin_init]`, `@[csimp]`, `@[cpass]`,
  `ConstantFold` folders, and the three `ToLCNF.visitApp` compiler-intrinsic tags (`casesOn`,
  `sparseCasesOn`, `noConfusion`), which are validated structurally and confirmed by the kernel;
* compiled code that exists but was not loaded (signatures or LCNF bodies without IR, opaque IR
  stubs, postponed compilation), IR callee resolution and IR helper ownership;
* statement-origin separation for claim modules, and a full kernel replay of every
  non-toolchain declaration on top of the toolchain-only environment.

Native-evaluation axioms are never accepted by a trust-gating request. When a diagnostic request
sets `allowProvisionalNative`, well-formed native axioms are re-checked by a bounded `Meta.whnf`
cost gate followed by the kernel on both polarities; an axiom that stays provisional is reported
and the verdict is still a policy failure.

Every traversal is total: structural recursion or an explicit fuel bound that fails closed with
`auditFuelExhausted`. This file contains no `partial`, `unsafe`, or `sorry`.
-/

open Lean

namespace OleanEnvAuditor

/-! ## Protocol helpers -/

def fail (message : String) : IO α := throw <| IO.userError s!"policy:{message}"

def operational (message : String) : IO α := throw <| IO.userError message

structure Violation where
  tag : String
  decl : Name
  module : Name
  detail : String
  deriving Inhabited, BEq

def Violation.render (v : Violation) : String :=
  s!"[{v.tag}] {v.decl} ({v.module}): {v.detail}"

def Violation.toJson (v : Violation) : Json :=
  Json.mkObj [("tag", Lean.toJson v.tag), ("declaration", Lean.toJson v.decl.toString),
    ("module", Lean.toJson v.module.toString), ("detail", Lean.toJson v.detail)]

/-- Mutable audit state shared by all checks. -/
structure AuditState where
  violations : Array Violation := #[]
  seen : Std.HashSet (String × Name) := {}
  reachedAxioms : NameSet := {}
  localAxioms : NameSet := {}
  nativeAxioms : NameSet := {}
  provisionalNative : NameSet := {}
  kernelConfirmedNative : NameSet := {}
  reachable : Nat := 0
  irDecls : Nat := 0
  tagChecks : Nat := 0
  kernelTagConfirmations : Nat := 0
  companions : Nat := 0

abbrev AuditM := StateRefT AuditState IO

def report (tag : String) (decl : Name) (module : Name) (detail : String) : AuditM Unit := do
  let key := (tag, decl)
  if (← get).seen.contains key then return
  modify fun (s : AuditState) => { s with
    violations := s.violations.push { tag, decl, module, detail }
    seen := s.seen.insert key }

/-! ## Request -/

structure Request where
  sysroot : System.FilePath
  artifacts : Array (Name × Array System.FilePath × Array System.FilePath)
  foundation : Array Name
  roots : Array Name
  modules : Array Name
  graph : Option Json
  axioms : Array (String × String)
  localAxiomModules : Array Name
  claimModules : Array Name
  statementForbidden : Array Name
  statementUnfold : Array Name
  sources : Array (Name × System.FilePath)
  allowProvisionalNative : Bool
  toolchainRoots : Array Name
  scope : String
  nativeHeartbeats : Nat
  maxReported : Nat

def allowedRequestKeys : List String := [
  "mode", "sysroot", "artifacts", "foundation", "graph", "axioms", "roots", "modules",
  "localAxiomModules", "claimModules", "statementForbidden", "statementUnfold", "sources",
  "allowProvisionalNative", "toolchainRoots", "scope", "nativeHeartbeats", "maxReportedViolations"]

def reqField [FromJson α] (j : Json) (key : String) : IO α :=
  match j.getObjValAs? α key with
  | .ok v => pure v
  | .error e => fail s!"malformed olean-audit request field {key}: {e}"

def optField [FromJson α] (j : Json) (key : String) (default : α) : IO α :=
  match j.getObjVal? key with
  | .error _ => pure default
  | .ok v => match fromJson? v with
    | .ok r => pure r
    | .error e => fail s!"malformed olean-audit request field {key}: {e}"

def toNames (xs : Array String) : Array Name := xs.map String.toName

def validModuleName (n : Name) : Bool :=
  !n.isAnonymous && n.components.all fun c =>
    match c with
    | .str .anonymous s =>
      !s.isEmpty && s != "." && s != ".." && !s.contains '/' && !s.contains '\\'
    | _ => false

def parseRequest (j : Json) : IO Request := do
  let .ok obj := j.getObj? | fail "olean-audit request must be a JSON object"
  for (k, _) in obj.toArray do
    unless allowedRequestKeys.contains k do fail s!"unknown olean-audit request field {k}"
  let mode ← reqField (α := String) j "mode"
  unless mode == "olean-audit" || mode == "olean-downstream-audit" do
    fail s!"unsupported olean-audit mode {mode}"
  let rawArts ← reqField (α := Array (String × Array (Array String))) j "artifacts"
  let mut arts := #[]
  for (m, parts) in rawArts do
    let mName := m.toName
    unless validModuleName mName do fail s!"invalid artifact module name {m}"
    unless parts.size == 2 do fail s!"artifact entry for {m} must have exactly olean and IR part lists"
    arts := arts.push (mName, parts[0]!.map System.FilePath.mk, parts[1]!.map System.FilePath.mk)
  let roots := toNames (← reqField (α := Array String) j "roots")
  if roots.isEmpty then fail "olean-audit request has no root modules"
  for r in roots do
    unless validModuleName r do fail s!"invalid root module name {r}"
  let modules := toNames (← reqField (α := Array String) j "modules")
  if modules.isEmpty then fail "olean-audit request has no audited modules"
  let mut seenMods : NameSet := {}
  for m in modules do
    unless validModuleName m do fail s!"invalid audited module name {m}"
    if seenMods.contains m then fail s!"duplicate audited module {m}"
    seenMods := seenMods.insert m
  let toolchainRoots := toNames (← optField (α := Array String) j "toolchainRoots" #["Init", "Std"])
  for r in toolchainRoots do
    unless r == `Init || r == `Std || r == `Lean do
      fail s!"unsupported toolchain root {r}"
  for m in modules do
    if toolchainRoots.contains m.getRoot then
      fail s!"[moduleProvenanceSpoofed] toolchain-named module {m} listed in audited modules"
  let foundation := toNames (← optField (α := Array String) j "foundation" #[])
  for f in foundation do
    unless validModuleName f do fail s!"invalid foundation module name {f}"
  let claimModules := toNames (← optField (α := Array String) j "claimModules" #[])
  for cm in claimModules do
    unless validModuleName cm && seenMods.contains cm do
      fail s!"[missingDeclaration] claim module {cm} is not in the audited module set"
  let localAxiomModules := toNames (← optField (α := Array String) j "localAxiomModules" #[])
  for lm in localAxiomModules do
    unless validModuleName lm && seenMods.contains lm do
      fail s!"invalid localAxiomModules entry {lm}"
  let statementForbidden := toNames (← optField (α := Array String) j "statementForbidden" #[])
  for sf in statementForbidden do
    unless validModuleName sf do fail s!"invalid statementForbidden entry {sf}"
  let statementUnfold := toNames (← optField (α := Array String) j "statementUnfold" #[])
  for su in statementUnfold do
    unless validModuleName su do fail s!"invalid statementUnfold entry {su}"
  let rawSources ← optField (α := Array (String × String)) j "sources" #[]
  let mut sources := #[]
  for (m, p) in rawSources do
    let mName := m.toName
    unless validModuleName mName do fail s!"invalid source module name {m}"
    sources := sources.push (mName, System.FilePath.mk p)
  let graph := match j.getObjVal? "graph" with | .ok g => some g | .error _ => none
  return {
    sysroot := ⟨← reqField (α := String) j "sysroot"⟩
    artifacts := arts
    foundation
    roots
    modules
    graph
    axioms := ← reqField (α := Array (String × String)) j "axioms"
    localAxiomModules
    claimModules
    statementForbidden
    statementUnfold
    sources
    allowProvisionalNative := ← optField (α := Bool) j "allowProvisionalNative" false
    toolchainRoots
    scope := ← optField (α := String) j "scope" "modules"
    nativeHeartbeats := ← optField (α := Nat) j "nativeHeartbeats" 200
    maxReported := ← optField (α := Nat) j "maxReportedViolations" 12
  }

/-! ## Module classification and provenance -/

def isToolchainName (roots : Array Name) (m : Name) : Bool :=
  roots.contains m.getRoot

def partNames : Array String := #["olean", "olean.server", "olean.private", "ir.sig", "ir"]

def modRelPath (m : Name) : String :=
  "/".intercalate (m.components.map (·.toString (escape := false)))

def realPathOrEmpty (p : System.FilePath) : IO System.FilePath := do
  try IO.FS.realPath p catch _ => pure (System.FilePath.mk "")

/-- Canonical-path check of one artifact part: the path must be absolute, must be a regular file
whose `realPath` is the path itself, and its directory must canonicalize to itself. -/
def checkCanonicalPart (m : Name) (expected : System.FilePath) : AuditM Bool := do
  let pathStr := expected.toString
  unless expected.isAbsolute do
    report "moduleProvenanceSpoofed" m m s!"artifact path is not absolute: {pathStr}"
    return false
  let kind ← (show IO (Option IO.FS.FileType) from do
      try
        let md ← expected.symlinkMetadata
        pure (some md.type)
      catch _ => pure none)
  if kind == some .symlink then
    let real ← realPathOrEmpty expected
    report "moduleProvenanceSpoofed" m m s!"artifact part {pathStr} is a symlink and resolves to {real}"
    return false
  unless kind == some .file do
    report "missingPrivateArtifact" m m s!"missing or non-regular artifact part {pathStr}"
    return false
  let real ← realPathOrEmpty expected
  unless real == expected do
    report "moduleProvenanceSpoofed" m m s!"artifact part {pathStr} resolves to {real}"
    return false
  let some dir := expected.parent
    | report "moduleProvenanceSpoofed" m m s!"artifact part {pathStr} has no directory"; return false
  let realDir ← realPathOrEmpty dir
  unless realDir == dir do
    report "moduleProvenanceSpoofed" m m s!"artifact directory {dir} resolves to {realDir}"
    return false
  return true

/-- Verify the companion parts that `importModules` read for module `m`.
`isModuleFile` is the module-system flag of the loaded data. Module-system files need all three
`.olean` parts and, because their compiled code lives only there, both IR parts; a non-module
file is exactly one `.olean` whose compiled code is stored in the `.olean` itself. -/
def checkModuleParts (m : Name) (base : System.FilePath) (oleanParts irParts : Array System.FilePath)
    (isModuleFile : Bool) : AuditM Nat := do
  let expectedOlean :=
    if isModuleFile then #["olean", "olean.server", "olean.private"] else #["olean"]
  let mut checked := 0
  unless oleanParts.size == expectedOlean.size do
    report "missingPrivateArtifact" m m
      s!"expected olean parts {expectedOlean} for {if isModuleFile then "module" else "non-module"} file, got {oleanParts.size}"
    return checked
  for p in oleanParts, ext in expectedOlean do
    let expected : System.FilePath := ⟨base.toString ++ "." ++ ext⟩
    unless p == expected do
      report "moduleProvenanceSpoofed" m m s!"artifact part {p} is not the canonical {expected}"
      return checked
    if ← checkCanonicalPart m expected then checked := checked + 1
  if isModuleFile then
    unless irParts.size == 2 do
      report "missingPrivateArtifact" m m "module-system file without both .ir.sig and .ir"
      return checked
  else
    unless irParts.isEmpty || irParts.size == 2 do
      report "missingPrivateArtifact" m m "incomplete IR companion parts"
      return checked
  for p in irParts, ext in #["ir.sig", "ir"] do
    let expected : System.FilePath := ⟨base.toString ++ "." ++ ext⟩
    unless p == expected do
      report "moduleProvenanceSpoofed" m m s!"IR part {p} is not the canonical {expected}"
      return checked
    if ← checkCanonicalPart m expected then checked := checked + 1
  return checked

/-- Existing-part list for a toolchain module resolved through the pinned library directory. -/
def sysrootParts (libDir : System.FilePath) (m : Name) : IO (Array System.FilePath × Array System.FilePath) := do
  let base := libDir / modRelPath m
  let mut olean := #[]
  for ext in #["olean", "olean.server", "olean.private"] do
    let p : System.FilePath := ⟨base.toString ++ "." ++ ext⟩
    if ← p.pathExists then olean := olean.push p
  let mut ir := #[]
  for ext in #["ir.sig", "ir"] do
    let p : System.FilePath := ⟨base.toString ++ "." ++ ext⟩
    if ← p.pathExists then ir := ir.push p
  return (olean, ir)

/-- Artifact checks that need no loaded environment and therefore run before `importModules`
reads a single byte: shape, canonical names, canonical paths, and companion parts that exist on
disk but were omitted from the artifact list (selective omission hides private data or IR). -/
def preloadArtifactChecks (req : Request) : AuditM Nat := do
  let mut checked := 0
  let mut seen : NameSet := {}
  for (m, olean, ir) in req.artifacts do
    if seen.contains m then
      report "moduleProvenanceSpoofed" m m "duplicate artifact entry"
      continue
    seen := seen.insert m
    if isToolchainName req.toolchainRoots m && !req.foundation.contains m then
      report "moduleProvenanceSpoofed" m m "toolchain-named module supplied as an untrusted artifact"
      continue
    let some first := olean[0]? | report "missingPrivateArtifact" m m "no .olean part"; continue
    let firstStr := first.toString
    unless firstStr.endsWith ("/" ++ modRelPath m ++ ".olean") do
      report "moduleProvenanceSpoofed" m m s!"artifact {firstStr} does not match the module name"
      continue
    let base : String := (firstStr.dropEnd 6).toString
    let oleanExts : Array String :=
      if olean.size == 3 then #["olean", "olean.server", "olean.private"]
      else if olean.size == 1 then #["olean"] else #[]
    if oleanExts.isEmpty then
      report "missingPrivateArtifact" m m s!"expected .olean or .olean/.olean.server/.olean.private, got {olean.size} parts"
      continue
    unless ir.size == 0 || ir.size == 2 do
      report "missingPrivateArtifact" m m "incomplete IR companion parts (.ir.sig and .ir go together)"
      continue
    let mut shapeOk := true
    for p in olean, ext in oleanExts do
      unless p.toString == base ++ "." ++ ext do shapeOk := false
    for p in ir, ext in #["ir.sig", "ir"] do
      unless p.toString == base ++ "." ++ ext do shapeOk := false
    unless shapeOk do
      report "moduleProvenanceSpoofed" m m "artifact parts are not the canonical companions of one base path"
      continue
    for p in olean ++ ir do
      if ← checkCanonicalPart m p then checked := checked + 1
    for ext in partNames do
      let p : System.FilePath := ⟨base ++ "." ++ ext⟩
      let listed := (olean ++ ir).contains p
      if !listed && (← p.pathExists) then
        report "missingPrivateArtifact" m m s!"companion part {p} exists but was omitted from the artifacts"
  return checked

/-! ## Environment -/

structure Loaded where
  env : Environment
  req : Request
  libDir : System.FilePath
  artMap : Std.HashMap Name (Array System.FilePath × Array System.FilePath)
  modIdx : Std.HashMap Name Nat
  toolchainProv : Std.HashSet Name
  nonToolchain : Array Name

def loadEnvironment (req : Request) (roots : Array Name) : IO Environment := do
  -- The search path is exactly the pinned toolchain library; `LEAN_PATH` is ignored so that an
  -- inherited environment variable cannot add a directory that shadows a toolchain module.
  let libDir := req.sysroot / "lib" / "lean"
  searchPathRef.set [libDir]
  let mut arts : NameMap ImportArtifacts := {}
  for (m, olean, ir) in req.artifacts do
    if (arts.find? m).isSome then fail s!"duplicate artifact module {m}"
    arts := arts.insert m (.ofArrays #[olean, ir])
  let env ← try
      importModules (roots.map fun n => { module := n }) {} (trustLevel := 0) (plugins := #[])
        (loadExts := false) (level := .private) (arts := arts)
    catch e => fail s!"[environmentLoadFailed] importModules failed: {e}"
  unless env.header.modules.size == env.header.moduleData.size do
    fail "[environmentLoadFailed] module/data array alignment failure"
  if env.header.isModule then
    fail "[environmentLoadFailed] refusing an exported-level (module-system) environment"
  return env.setExporting false

/-- Every module the pinned toolchain ships under the admitted toolchain roots, found by a bounded
walk of `<sysroot>/lib/lean/<root>`. -/
def listToolchainModules (libDir : System.FilePath) (roots : Array Name) : IO (Array Name) := do
  let mut result : Array Name := #[]
  let mut pending : List (System.FilePath × Name) := []
  for r in roots do
    let rs := r.toString (escape := false)
    if ← (libDir / (rs ++ ".olean")).pathExists then result := result.push r
    pending := (libDir / rs, r) :: pending
  let mut done := false
  for _ in [0:100000] do
    match pending with
    | [] => done := true; break
    | (dir, pre) :: rest =>
      pending := rest
      unless ← dir.isDir do continue
      for entry in ← dir.readDir do
        let md ← entry.path.symlinkMetadata
        if md.type == .symlink then
          fail s!"[moduleProvenanceSpoofed] symlink inside toolchain library: {entry.path}"
        if md.type == .dir then
          pending := (entry.path, pre.str entry.fileName) :: pending
        else if entry.fileName.endsWith ".olean" then
          result := result.push (pre.str (entry.fileName.dropEnd 6).toString)
  unless done do operational "toolchain module walk exhausted its fuel"
  return result

/-- Names of every constant (and IR-only helper) the pinned toolchain declares under the admitted
toolchain roots, whether or not the audited modules import the declaring module. The code generator
special-cases many of these by name alone (`ConstantFold.builtinFolders`, `builtinRuntimeTypes`,
`ToLCNF.visitApp`, `ExtractClosed`, `SimpleGroundExpr`, `ToImpureType`, ...), so a non-toolchain
module that declares one of them, while not importing the toolchain module that owns it, gets
compiler semantics that its kernel definition does not have. -/
def toolchainNameInventory (req : Request) : IO (Std.HashSet Name) := do
  let libDir := req.sysroot / "lib" / "lean"
  searchPathRef.set [libDir]
  let mods ← listToolchainModules libDir req.toolchainRoots
  if mods.isEmpty then fail "[environmentLoadFailed] the pinned toolchain ships no modules"
  let env ← try
      importModules (mods.map fun n => { module := n }) {} (trustLevel := 0) (plugins := #[])
        (loadExts := false) (level := .exported)
    catch e => fail s!"[environmentLoadFailed] cannot load the toolchain name inventory: {e}"
  let mut names : Std.HashSet Name := {}
  for data in env.header.moduleData do
    for n in data.constNames do names := names.insert n
    for n in data.extraConstNames do names := names.insert n
  return names

def origin? (env : Environment) (n : Name) : Option Name := do
  let idx ← env.getModuleIdxFor? n
  let m ← env.header.modules[idx.toNat]?
  return m.module

/-! ## Expression edges -/

def literalEdges (e : Expr) (acc : NameSet) : NameSet :=
  let acc := if (e.find? fun | .lit (.natVal _) => true | _ => false).isSome then acc.insert `Nat else acc
  if (e.find? fun | .lit (.strVal _) => true | _ => false).isSome then acc.insert `String else acc

def exprEdges (e : Expr) (acc : NameSet) : NameSet :=
  literalEdges e (e.getUsedConstants.foldl (·.insert ·) acc)

def isClosedExpr (e : Expr) : Bool := !(e.hasFVar || e.hasMVar || e.hasLooseBVars || e.hasLevelMVar)

/-- All constants a stored declaration mentions: type, value (including opaque and theorem
bodies), mutual blocks, constructors, parent inductive, recursor rules, literal types. -/
def declEdges (ci : ConstantInfo) : NameSet := Id.run do
  let mut acc := exprEdges ci.type {}
  if let some v := ci.value? (allowOpaque := true) then acc := exprEdges v acc
  match ci with
  | .defnInfo v => acc := v.all.foldl (·.insert ·) acc
  | .thmInfo v => acc := v.all.foldl (·.insert ·) acc
  | .opaqueInfo v => acc := v.all.foldl (·.insert ·) acc
  | .inductInfo v => acc := (v.all ++ v.ctors).foldl (·.insert ·) acc
  | .ctorInfo v => acc := acc.insert v.induct
  | .recInfo v =>
    acc := v.all.foldl (·.insert ·) acc
    for r in v.rules do
      acc := exprEdges r.rhs (acc.insert r.ctor)
  | _ => pure ()
  return acc

def declIsClosed (ci : ConstantInfo) : Bool :=
  isClosedExpr ci.type && (ci.value? (allowOpaque := true)).all isClosedExpr &&
  (match ci with
   | .recInfo v => v.rules.all (isClosedExpr ·.rhs)
   | _ => true)

def kindOf (ci : ConstantInfo) : String :=
  match ci with
  | .axiomInfo _ => "axiom" | .defnInfo _ => "definition" | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque" | .quotInfo _ => "quotient" | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor" | .recInfo _ => "recursor"

/-! ## Kernel helpers -/

/-- Absolute kernel heartbeat threshold for a relative budget, clamped into `[1, USize.size - 1]`
so that it can neither wrap around nor become `0` (= unlimited). -/
def kernelHeartbeatThreshold (budget : Nat) : IO USize := do
  let now ← IO.getNumHeartbeats
  let raw := now + 1000 * (max budget 1)
  let clamped := min (max raw 1) (USize.size - 1)
  return clamped.toUSize

def freshName (env : Environment) (base : Name) : Name := Id.run do
  let mut candidate := base
  for i in [0:1000] do
    if (env.find? candidate).isNone && (env.getModuleIdxFor? candidate).isNone then
      return candidate
    candidate := base.appendIndexAfter i
  return base.str "olean_auditor_fresh_exhausted"

/-- Ask the kernel to type check `theorem _ : type := value` against `env`. -/
def kernelAccepts (env : Environment) (lparams : List Name) (type value : Expr) (budget : Nat) :
    IO Bool := do
  unless isClosedExpr type && isClosedExpr value do return false
  let name := freshName env `_olean_auditor_kernel_check
  let decl := Declaration.thmDecl { name, levelParams := lparams, type, value }
  let threshold ← kernelHeartbeatThreshold budget
  match env.toKernelEnv.addDeclCore threshold 0 decl none with
  | .ok _ => return true
  | .error _ => return false

def runMeta (env : Environment) (x : MetaM α) (heartbeats : Nat := 200000) : IO α := do
  let opts : Options := ({} : Options)
    |>.set `smartUnfolding false
    |>.set `maxHeartbeats heartbeats
  let ctx : Core.Context := {
    fileName := "<olean-env-auditor>", fileMap := default, options := opts,
    maxHeartbeats := heartbeats * 1000, maxRecDepth := 4096 }
  let st : Core.State := { env }
  let (a, _, _) ← (Meta.withTransparency .all x).toIO ctx st
  return a

/-! ## Compiler-intrinsic tag validators -/

/-- `I.casesOn` must be exactly what `Lean.mkCasesOnImp` produces for `I`. -/
def genuineCasesOn (env : Environment) (n : Name) : Except String Unit := do
  let .str ind "casesOn" := n | throw "auxiliary-recursor tag on a non-casesOn name with casesOn semantics"
  let some (.inductInfo _) := env.find? ind | throw s!"{ind} is not an inductive type"
  unless origin? env ind == origin? env n do throw s!"{n} is not declared in the module of {ind}"
  let some ci := env.find? n | throw "missing declaration"
  match mkCasesOnImp env.toKernelEnv ind with
  | .error _ => throw "mkCasesOnImp failed"
  | .ok (.defnDecl d) =>
    unless d.name == n && d.levelParams == ci.levelParams && d.type == ci.type &&
        some d.value == ci.value? (allowOpaque := true) && ci matches .defnInfo _ do
      throw "declaration differs from the casesOn recursor Lean generates"
  | .ok _ => throw "mkCasesOnImp produced an unexpected declaration"

/-- `(∀ fvars, lhs = rhs, fun fvars => Eq.refl lhs)`: the kernel accepts the pair iff `lhs` and
`rhs` are definitionally equal for all values of `fvars`. -/
def mkEqObligation (fvars : Array Expr) (lhs rhs : Expr) : MetaM (Expr × Expr) := do
  let ty ← Meta.inferType lhs
  let lvl ← Meta.getLevel ty
  let eqTy := mkApp3 (mkConst ``Eq [lvl]) ty lhs rhs
  let thmTy ← Meta.mkForallFVars fvars eqTy
  let pf ← Meta.mkLambdaFVars fvars (mkApp2 (mkConst ``Eq.refl [lvl]) ty lhs)
  return (thmTy, pf)

def isToolchainConst (env : Environment) (toolchainProv : Std.HashSet Name) (c : Name) : Bool :=
  match origin? env c with
  | some m => toolchainProv.contains m
  | none => false

def natLitExact? (e : Expr) : Option Nat :=
  match e.rawNatLit? with
  | some k => some k
  | none =>
    match e with
    | .app (.app (.app (.const ``OfNat.ofNat _) ty) (.lit (.natVal k))) _ =>
      if ty == mkConst ``Nat then some k else none
    | _ => none

/-- Kernel confirmation that a `casesOn`-like declaration computes the way `ToLCNF.visitCases`
compiles it: alternatives have unique constructors with at most one trailing default, every default
hypothesis is a `Prop`, and for every constructor of the inductive type either the declaration
reduces to the selected alternative in the kernel or the kernel certifies that the side condition
reduces to a `Nat` literal disequality `x = y` (`x ≠ y`). Returns the number of kernel-confirmed
equations or an error. -/
def casesLikeSemantics (env : Environment) (toolchainProv : Std.HashSet Name) (n : Name) (budget : Nat) :
    IO (Except String Nat) := do
  let some ci := env.find? n | return .error "missing declaration"
  unless isToolchainConst env toolchainProv ``Eq do
    return .error "Eq does not originate from a verified toolchain module"
  let lparams := ci.levelParams
  let res ← (runMeta env (do
    let some cinfo ← liftM (m := CoreM) (getCasesInfo? n) | return Except.error "not casesOn-like"
    let some (.inductInfo indVal) := (← getEnv).find? cinfo.indName
      | return .error s!"{cinfo.indName} is not an inductive type"
    if let .str _ "elim" := n then
      unless origin? (← getEnv) cinfo.indName == origin? (← getEnv) n &&
          ((← getEnv).find? n.getPrefix matches some (.ctorInfo _)) do
        return .error "constructor eliminator and inductive type live in different modules"
    -- Validate alternative structure before checking semantics: LCNF/IR evaluates case branches
    -- in order, so a `.default` before a `.ctor` short-circuits that constructor, and duplicate
    -- constructors or defaults make the compiled branch ambiguous.
    let mut seenCtors : NameSet := {}
    let mut seenDefault := false
    for info in cinfo.altNumParams do
      match info with
      | .ctor c _ =>
        if seenDefault then
          return .error "constructor alternative appears after default alternative"
        if seenCtors.contains c then
          return .error s!"duplicate alternative for constructor {c}"
        unless indVal.ctors.contains c do
          return .error s!"alternative constructor {c} does not belong to {cinfo.indName}"
        seenCtors := seenCtors.insert c
      | .default _ =>
        if seenDefault then
          return .error "duplicate default alternative"
        seenDefault := true
    let np := indVal.numParams
    let ni := indVal.numIndices
    unless cinfo.discrPos == np + 1 + ni do return .error "unexpected major premise position"
    let hasSide := cinfo.altsRange.lower == cinfo.discrPos + 2
    unless cinfo.altsRange.lower == cinfo.discrPos + (if hasSide then 2 else 1) &&
        cinfo.altsRange.upper == cinfo.arity &&
        cinfo.altsRange.upper - cinfo.altsRange.lower == cinfo.altNumParams.size do
      return .error "unexpected alternatives range in casesInfo"
    let mut obligations : Array (Expr × Expr) := #[]
    for ctor in indVal.ctors do
      let some (.ctorInfo ctorVal) := (← getEnv).find? ctor | return .error s!"missing constructor {ctor}"
      let r ← Meta.forallBoundedTelescope ci.type (some (np + 1)) fun pm rest => do
        unless pm.size == np + 1 do return Except.error "too few binders"
        let ps := pm.extract 0 np
        -- The universe instantiation of the inductive type, read from the major premise type.
        let majorTy ← Meta.forallBoundedTelescope rest (some (ni + 1)) fun ism _ => do
          if ism.size != ni + 1 then return none
          return some (← Meta.inferType ism[ni]!)
        let some majorTy := majorTy | return .error "too few binders before the major premise"
        let .const indName ls := majorTy.getAppFn | return .error "major premise is not an inductive application"
        unless indName == cinfo.indName do return .error "major premise has an unexpected type"
        let ctorTy ← Meta.instantiateForall (ctorVal.type.instantiateLevelParams ctorVal.levelParams ls) ps
        Meta.forallBoundedTelescope ctorTy (some ctorVal.numFields) fun fs ctorRes => do
          unless fs.size == ctorVal.numFields do return .error "constructor arity mismatch"
          let is' := ctorRes.getAppArgs.extract np (np + ni)
          let major := mkAppN (mkConst ctor ls) (ps ++ fs)
          let rest' ← Meta.instantiateForall rest (is'.push major)
          let continueWith (side : Array Expr) (rest'' : Expr) : MetaM (Except String (Option (Expr × Expr))) := do
            Meta.forallTelescope rest'' fun alts _ => do
              unless alts.size == cinfo.altNumParams.size do
                return .error "alternative binder count differs from casesInfo"
              let lhs := mkAppN (mkConst n (lparams.map mkLevelParam)) (pm ++ is' ++ #[major] ++ side ++ alts)
              let mut chosen : Option (Expr × Nat) := none
              let mut dflt : Option (Expr × Nat) := none
              for info in cinfo.altNumParams, alt in alts do
                match info with
                | .ctor c k => if c == ctor && chosen.isNone then chosen := some (alt, k)
                | .default h => if dflt.isNone then dflt := some (alt, h)
              match chosen, dflt with
              | some (alt, k), _ =>
                unless k == fs.size do return .error "alternative arity differs from constructor fields"
                return .ok (some (← mkEqObligation (pm ++ fs ++ side ++ alts) lhs (mkAppN alt fs)))
              | none, some (alt, h) =>
                Meta.forallBoundedTelescope (← Meta.inferType alt) (some h) fun hs _ => do
                  unless hs.size == h do return .error "default alternative arity mismatch"
                  for hv in hs do
                    unless ← Meta.isProp (← Meta.inferType hv) do
                      return .error "default alternative hypothesis is not a Prop"
                  return .ok (some (← mkEqObligation (pm ++ fs ++ side ++ alts ++ hs) lhs (mkAppN alt hs)))
              | none, none =>
                if side.isEmpty then return .error s!"no alternative for constructor {ctor}"
                return .ok none
          if hasSide then
            Meta.forallBoundedTelescope rest' (some 1) fun hs rest'' => do
              unless hs.size == 1 do return .error "missing side condition"
              let rawSideTy ← Meta.inferType hs[0]!
              unless ← Meta.isProp rawSideTy do
                return .error "side condition is not a Prop"
              let r ← continueWith hs rest''
              match r with
              | .ok none =>
                -- Unreachable alternative: require a toolchain `Nat` literal disequality and
                -- confirm directly in the kernel that the side condition reduces to `x = y` (`x ≠ y`).
                unless isToolchainConst (← getEnv) toolchainProv ``Nat do
                  return .error "Nat does not originate from a verified toolchain module"
                let hTy ← Meta.whnf rawSideTy
                match hTy.eq? with
                | some (eqTy, a, b) =>
                  let eqTy ← Meta.whnf eqTy
                  unless eqTy == mkConst ``Nat do
                    return .error "side condition equality is not over Nat"
                  let a ← Meta.whnf a
                  let b ← Meta.whnf b
                  match natLitExact? a, natLitExact? b with
                  | some x, some y =>
                    if x != y then
                      let litEqTy := mkApp3 (mkConst ``Eq [Level.one]) (mkConst ``Nat)
                        (.lit (.natVal x)) (.lit (.natVal y))
                      let propSort := mkSort Level.zero
                      let checkEq := mkApp3 (mkConst ``Eq [Level.one]) propSort rawSideTy litEqTy
                      let thmTy ← Meta.mkForallFVars (pm ++ fs) checkEq
                      let pf ← Meta.mkLambdaFVars (pm ++ fs)
                        (mkApp2 (mkConst ``Eq.refl [Level.one]) propSort litEqTy)
                      return .ok (some (thmTy, pf))
                    else
                      return .error "side condition does not exclude constructor"
                  | _, _ => return .error "side condition is not a Nat literal disequality"
                | none => return .error "side condition is not an equation"
              | other => return other
          else
            continueWith #[] rest'
      match r with
      | .error e => return .error e
      | .ok none => pure ()
      | .ok (some ob) => obligations := obligations.push ob
    return .ok obligations) (heartbeats := 400000)) <|> pure (.error "meta-level construction failed")
  match res with
  | .error e => return .error e
  | .ok obligations =>
    let mut confirmed := 0
    for (ty, pf) in obligations do
      unless ← kernelAccepts env lparams ty pf budget do
        return .error "kernel refuses a constructor equation of the compiled casesOn semantics"
      confirmed := confirmed + 1
    return .ok confirmed

/-- Kernel confirmation for `noConfusion`-tagged declarations (`ToLCNF.visitNoConfusion`): for
each constructor, equal constructor applications make the declaration reduce to its continuation
applied to the `Prop`-typed field equations; distinct constructors/arguments are excluded by a
toolchain `Eq`/`HEq` hypothesis between the compared arguments. -/
def noConfusionSemantics (env : Environment) (toolchainProv : Std.HashSet Name) (n : Name)
    (info : NoConfusionInfo) (budget : Nat) : IO (Except String Nat) := do
  let some ci := env.find? n | return .error "missing declaration"
  unless isToolchainConst env toolchainProv ``Eq do
    return .error "Eq does not originate from a verified toolchain module"
  let lparams := ci.levelParams
  let us := lparams.map mkLevelParam
  let res ← (runMeta env (do
    match info with
    | .perCtor arity fields =>
      let .str ctorName "noConfusion" := n | return Except.error "per-constructor noConfusion tag on a non-noConfusion name"
      let some (.ctorInfo ctorVal) := (← getEnv).find? ctorName | return .error s!"{ctorName} is not a constructor"
      unless origin? (← getEnv) ctorName == origin? (← getEnv) n do return .error "constructor declared in another module"
      let np := ctorVal.numParams
      let nf := ctorVal.numFields
      unless arity ≥ np + 1 + 2 * nf do return .error "arity smaller than the constructor telescope"
      let neq := arity - (np + 1 + 2 * nf)
      unless neq ≥ 1 do return .error "per-constructor noConfusion has no equation hypothesis"
      -- Verify on distinct field telescopes that the equation binders are Props and include an
      -- Eq/HEq between the two constructor applications.
      let perCtorGuard ← Meta.forallBoundedTelescope ci.type (some (np + 1 + 2 * nf + neq)) fun allEq _ => do
        if allEq.size != np + 1 + 2 * nf + neq then return false
        let ps := allEq.extract 0 np
        let f1 := allEq.extract (np + 1) (np + 1 + nf)
        let f2 := allEq.extract (np + 1 + nf) (np + 1 + 2 * nf)
        let mut found := false
        for i in [np + 1 + 2 * nf : allEq.size] do
          let ty ← Meta.inferType allEq[i]!
          unless ← Meta.isProp ty do return false
          let t ← Meta.whnf ty
          let checkPair (x y : Expr) : Bool :=
            x.isAppOf ctorName && y.isAppOf ctorName &&
            x.getAppArgs == ps ++ f1 && y.getAppArgs == ps ++ f2
          if let some (_, x, y) := t.eq? then
            if checkPair x y then found := true
          if let some (_, x, _, y) := t.heq? then
            if isToolchainConst (← getEnv) toolchainProv ``HEq && checkPair x y then found := true
        return found
      unless perCtorGuard do
        return .error "per-constructor noConfusion lacks a Prop equation hypothesis between the compared constructor applications"
      Meta.forallBoundedTelescope ci.type (some (np + 1 + nf)) fun xs rest => do
        unless xs.size == np + 1 + nf do return .error "too few binders"
        let fs := xs.extract (np + 1) (np + 1 + nf)
        let rest' ← Meta.instantiateForall rest fs
        Meta.forallBoundedTelescope rest' (some (neq + 1)) fun eqk res => do
          unless eqk.size == neq + 1 do return .error "too few equation binders"
          let k := eqk[neq]!
          unless ← Meta.isDefEq res xs[np]! do return .error "result type is not the motive"
          let kTy ← Meta.inferType k
          Meta.forallBoundedTelescope kTy (some fields) fun qs kRes => do
            unless qs.size == fields do return .error "continuation arity differs from the tag"
            for q in qs do
              unless ← Meta.isProp (← Meta.inferType q) do
                return .error "continuation argument is not a Prop"
            unless ← Meta.isDefEq kRes xs[np]! do return .error "continuation does not return the motive"
            let lhs := mkAppN (mkConst n us) (xs ++ fs ++ eqk)
            let rhs := mkAppN k qs
            let ty ← Meta.inferType lhs
            let lvl ← Meta.getLevel ty
            let allFvars := xs ++ eqk ++ qs
            let eqTy := mkApp3 (mkConst ``Eq [lvl]) ty lhs rhs
            let thmTy ← Meta.mkForallFVars allFvars eqTy
            let pf ← Meta.mkLambdaFVars allFvars (mkApp2 (mkConst ``Eq.refl [lvl]) ty lhs)
            return .ok #[(thmTy, pf)]
    | .regular arity lhsPos rhsPos =>
      let .str indName "noConfusion" := n | return Except.error "noConfusion tag on a non-noConfusion name"
      let some (.inductInfo indVal) := (← getEnv).find? indName | return .error s!"{indName} is not an inductive type"
      unless origin? (← getEnv) indName == origin? (← getEnv) n do return .error "inductive type declared in another module"
      let np := indVal.numParams
      let ni := indVal.numIndices
      let w := np + ni + 1
      unless arity == 1 + 3 * w && lhsPos == 1 + np + ni && rhsPos == 1 + 2 * np + 2 * ni + 1 do
        return .error "noConfusion shape information differs from the inductive type"
      -- Distinct constructors are unreachable only if a toolchain equation hypothesis between the
      -- two compared arguments is among the hypotheses.
      let guardOk ← Meta.forallBoundedTelescope ci.type (some arity) fun xs _ => do
        if xs.size != arity then return false
        let a := xs[lhsPos]!
        let b := xs[rhsPos]!
        let mut found := false
        for i in [1 + 2 * w : arity] do
          let ty ← Meta.inferType xs[i]!
          unless ← Meta.isProp ty do return false
          let t ← Meta.whnf ty
          if let some (_, x, y) := t.eq? then
            if x == a && y == b then found := true
          if let some (_, x, _, y) := t.heq? then
            if isToolchainConst (← getEnv) toolchainProv ``HEq && x == a && y == b then found := true
        return found
      unless guardOk do return .error "no equation hypothesis between the compared arguments"
      let mut obligations := #[]
      for ctor in indVal.ctors do
        let some (.ctorInfo ctorVal) := (← getEnv).find? ctor | return .error s!"missing constructor {ctor}"
        let r ← Meta.forallBoundedTelescope ci.type (some 1) fun pP rest => do
          unless pP.size == 1 do return Except.error "missing motive"
          let majorTy ← Meta.forallBoundedTelescope rest (some w) fun xs1 _ => do
            if xs1.size != w then return none
            return some (← Meta.inferType xs1[w - 1]!)
          let some majorTy := majorTy | return .error "too few binders"
          let .const iName ls := majorTy.getAppFn | return .error "compared argument is not an inductive application"
          unless iName == indName do return .error "compared argument has an unexpected type"
          Meta.forallBoundedTelescope rest (some np) fun ps _ => do
            unless ps.size == np do return .error "too few parameters"
            let ctorTy ← Meta.instantiateForall (ctorVal.type.instantiateLevelParams ctorVal.levelParams ls) ps
            Meta.forallBoundedTelescope ctorTy (some ctorVal.numFields) fun fs ctorRes => do
              unless fs.size == ctorVal.numFields do return .error "constructor arity mismatch"
              let is' := ctorRes.getAppArgs.extract np (np + ni)
              let major := mkAppN (mkConst ctor ls) (ps ++ fs)
              let xsVal := ps ++ is' ++ #[major]
              let rest' ← Meta.instantiateForall rest (xsVal ++ xsVal)
              let neq := arity - 1 - 2 * w
              Meta.forallBoundedTelescope rest' (some (neq + 1)) fun eqk res => do
                unless eqk.size == neq + 1 do return .error "too few equation binders"
                let k := eqk[neq]!
                let nonProp ← fs.foldlM (init := 0) fun c f => do
                  return if ← Meta.isProp (← Meta.inferType f) then c else c + 1
                let kTy ← Meta.inferType k
                Meta.forallBoundedTelescope kTy (some nonProp) fun qs kRes => do
                  unless qs.size == nonProp do return .error "continuation arity differs from the non-Prop fields"
                  for q in qs do
                    unless ← Meta.isProp (← Meta.inferType q) do
                      return .error "continuation argument is not a Prop"
                  unless ← Meta.isDefEq kRes pP[0]! do return .error "continuation does not return the motive"
                  unless ← Meta.isDefEq res pP[0]! do return .error "result type is not the motive"
                  let lhs := mkAppN (mkConst n us) (pP ++ xsVal ++ xsVal ++ eqk)
                  let rhs := mkAppN k qs
                  let ty ← Meta.inferType lhs
                  let lvl ← Meta.getLevel ty
                  let allFvars := pP ++ ps ++ fs ++ eqk ++ qs
                  let eqTy := mkApp3 (mkConst ``Eq [lvl]) ty lhs rhs
                  let thmTy ← Meta.mkForallFVars allFvars eqTy
                  let pf ← Meta.mkLambdaFVars allFvars (mkApp2 (mkConst ``Eq.refl [lvl]) ty lhs)
                  return .ok (thmTy, pf)
        match r with
        | .error e => return .error e
        | .ok ob => obligations := obligations.push ob
      return .ok obligations) (heartbeats := 400000)) <|> pure (.error "meta-level construction failed")
  match res with
  | .error e => return .error e
  | .ok obligations =>
    let mut confirmed := 0
    for (ty, pf) in obligations do
      unless ← kernelAccepts env lparams ty pf budget do
        return .error "kernel refuses a constructor equation of the compiled noConfusion semantics"
      confirmed := confirmed + 1
    return .ok confirmed

/-- Names that `sparseCasesOn` tags legitimately: `<Ctor>.elim` constructor eliminators and
`_sparseCasesOn_<i>` auxiliary declarations, both in the module of their inductive type. -/
def sparseCasesOnNameOk (env : Environment) (n : Name) : Bool :=
  match n with
  | .str ctor "elim" =>
    match env.find? ctor with
    | some (.ctorInfo _) => true
    | _ => false
  | .str _ s => s.startsWith "_sparseCasesOn"
  | _ => false

/-! ## Hardcoded compiler-intrinsic names and pipeline fingerprints -/

/-- Constant names whose semantics are hardcoded in Lean 4.34.1's LCNF/IR compiler
(`ConstantFold.builtinFolders`, `builtinRuntimeTypes`, `ToLCNF.visitApp`, `ToMono`, `ExplicitRC`,
`ToImpureType`, `AuxRecursor`, and foundational/native axioms) by name alone without checking
defining-module provenance. No non-toolchain module may declare any of these names. -/
def compilerReservedNames : NameSet := Id.run do
  let mut s : NameSet := {}
  for (k, _) in Compiler.LCNF.Simp.ConstantFold.builtinFolders.toList do
    s := s.insert k
  for k in Compiler.LCNF.builtinRuntimeTypes do
    s := s.insert k
  let extras : Array Name := #[
    ``Quot, ``Quot.mk, ``Quot.lift, ``Quot.ind, ``Quot.lcInv,
    ``Eq, ``Eq.refl, ``Eq.rec, ``Eq.recOn, ``Eq.ndrec, ``Eq.ndrec_symm, ``Eq.ndrecOn,
    ``HEq, ``HEq.refl, ``HEq.rec, ``HEq.ndrec,
    ``And, ``And.rec, ``Iff, ``Iff.rec, ``False, ``False.rec, ``Empty, ``Empty.rec,
    ``lcUnreachable, ``lcProof, ``lcCast, ``lcErased, ``lcAny, ``lcVoid,
    ``Decidable, ``Decidable.isTrue, ``Decidable.isFalse, ``Decidable.decide,
    ``Bool, ``Bool.true, ``Bool.false,
    ``Nat.zero, ``Nat.succ, ``Int.ofNat, ``Int.negSucc, ``Int.natAbs, ``Int.decLt,
    ``List, ``List.nil, ``List.cons,
    ``Array.mkEmpty, ``Array.push, ``Array.toList,
    ``Array.getInternal, ``Array.getInternalBorrowed,
    ``Array.get!Internal, ``Array.get!InternalBorrowed,
    ``Array.uget, ``Array.ugetBorrowed,
    ``ByteArray.data, ``FloatArray.data, ``String.toByteArray,
    ``Float.toModel, ``Float32.toModel,
    ``Thunk.get, ``Task.pure, ``Task.get,
    ``Char, ``Char.ofNat, ``Char.toNat,
    ``UInt8.toBitVec, ``UInt16.toBitVec, ``UInt32.toBitVec, ``UInt64.toBitVec, ``USize.toBitVec,
    ``OfNat, ``OfNat.ofNat,
    ``sorryAx, ``propext, ``Quot.sound, ``Classical.choice,
    ``Lean.ofReduceBool, ``Lean.ofReduceNat, ``Lean.trustCompiler
  ]
  for k in extras do s := s.insert k
  return s

/-- The three toolchain `unsafe` borrowed-array helpers emitted directly by `LCNF.ExplicitRC`. -/
def compilerBorrowedUnsafeIntrinsics : NameSet :=
  NameSet.empty
    |>.insert ``Array.getInternalBorrowed
    |>.insert ``Array.get!InternalBorrowed
    |>.insert ``Array.ugetBorrowed

/-- Order-sensitive structural fingerprint of a `PassManager` (phase lists, names, occurrences, phases). -/
def passManagerFingerprint (pm : Compiler.LCNF.PassManager) :
    Array (Array (Name × Nat × Nat × Nat)) :=
  let phaseTag : Compiler.LCNF.Phase → Nat
    | .base => 0 | .mono => 1 | .impure => 2
  let fp (ps : Array Compiler.LCNF.Pass) :=
    ps.map fun p => (p.name, p.occurrence, phaseTag p.phase, phaseTag p.phaseOut)
  #[fp pm.basePasses, fp pm.monoPasses, fp pm.monoPassesNoLambda, fp pm.impurePasses]

def builtinFolderKeySet : NameSet :=
  Compiler.LCNF.Simp.ConstantFold.builtinFolders.toList.foldl (fun s (k, _) => s.insert k) {}

/-! ## Native-evaluation axioms -/

def nativeBuiltinAxioms : List Name := [``Lean.ofReduceBool, ``Lean.ofReduceNat, ``Lean.trustCompiler]

def hasNativeComponent (n : Name) : Bool :=
  n.components.any (· == `_native)

/-! ## Source scan -/

def isIdentChar (c : Char) : Bool := c.isAlphanum || c == '_' || c == '\'' || c == '!' || c == '?' || c == '.'

/-- Try to skip a Lean `Char` literal starting at index `i` (where `cs[i] == '\''`).
Returns the index immediately past the closing quote, or `none` if no valid char literal starts here. -/
def skipCharLit (cs : Array Char) (i : Nat) : Option Nat := Id.run do
  if i + 2 >= cs.size then return none
  let c1 := cs[i + 1]!
  if c1 == '\n' || c1 == '\'' then return none
  if c1 == '\\' then
    -- Escaped char literal: `'\''`, `'\"'`, `'\\'`, `'\n'`, `'\xNN'`, `'\uNNNN'` (bounded length).
    let mut j := i + 3
    for _ in [0:10] do
      if h : j < cs.size then
        let cj := cs[j]
        if cj == '\'' then return some (j + 1)
        if cj == '\n' then return none
        j := j + 1
      else return none
    return none
  else
    if cs[i + 2]! == '\'' then return some (i + 3) else return none

/-- Try to match a raw string opening `r#*"` starting at index `i` (where `cs[i] == 'r'` and
preceded by a non-identifier boundary). Returns `(numHashes, nextIndex)` if matched. -/
def matchRawStrStart (cs : Array Char) (i : Nat) : Option (Nat × Nat) := Id.run do
  let mut j := i + 1
  let mut hashes := 0
  for _ in [0:cs.size] do
    if h : j < cs.size then
      if cs[j] == '#' then
        hashes := hashes + 1
        j := j + 1
      else break
    else break
  -- `r"..."` (no hashes) is a raw string too: no escapes, so `r"\"` ends at its second quote.
  if h : j < cs.size then
    if cs[j] == '"' then return some (hashes, j + 1)
  return none

/-- Check whether `cs` at index `i` has `"` followed by `hashes` `#` characters. -/
def matchRawStrEnd (cs : Array Char) (i hashes : Nat) : Bool := Id.run do
  if i + hashes >= cs.size then return false
  if cs[i]! != '"' then return false
  for k in [0:hashes] do
    if cs[i + 1 + k]! != '#' then return false
  return true

/-- Identifier tokens of Lean source text outside comments and plain/raw string literals, while
handling single-quoted `Char` literals and descending into `{...}` expressions inside Lean's
built-in interpolated strings (`s!"..."`, `m!"..."`, `f!"..."`). Returns `(tokens, balanced)` where
`balanced` is `false` if scanning reached EOF inside an unclosed string, raw string, comment,
guillemet, or interpolation state (fail-closed guard against lexer desynchronization). -/
def scanIdents (text : String) : Array String × Bool := Id.run do
  let cs := text.toList.toArray
  let mut acc : Array String := #[]
  let mut cur : List Char := []
  let mut i := 0
  let mut depth := 0
  let mut inLine := false
  let mut inStr := false
  let mut inInterpStr := false
  let mut interpStack : List Nat := []
  let mut rawHashes : Option Nat := none
  let mut inGuil := false
  for _ in [0:cs.size + 1] do
    if h : i < cs.size then
      let c := cs[i]
      let d? := cs[i + 1]?
      if inLine then
        if c == '\n' then inLine := false
        i := i + 1
      else if depth > 0 then
        if c == '/' && d? == some '-' then depth := depth + 1; i := i + 2
        else if c == '-' && d? == some '/' then depth := depth - 1; i := i + 2
        else i := i + 1
      else if let some nh := rawHashes then
        if matchRawStrEnd cs i nh then
          rawHashes := none
          i := i + 1 + nh
        else
          i := i + 1
      else if inStr then
        if c == '\\' then i := i + 2
        else if c == '"' then
          inStr := false
          inInterpStr := false
          i := i + 1
        else if inInterpStr && c == '{' then
          inStr := false
          inInterpStr := false
          interpStack := 0 :: interpStack
          i := i + 1
        else
          i := i + 1
      else if inGuil then
        if c == '»' then inGuil := false else cur := c :: cur
        i := i + 1
      else
        -- Check raw string `r#*"..."#*` at token boundary.
        if cur.isEmpty && c == 'r' then
          if let some (nh, nextI) := matchRawStrStart cs i then
            rawHashes := some nh
            i := nextI
            continue
        -- Check `Char` literal `'c'` / `'\...'` at token boundary (never breaks `foo'`).
        if cur.isEmpty && c == '\'' then
          if let some nextI := skipCharLit cs i then
            i := nextI
            continue
        let isStart := (c == '-' && d? == some '-') || (c == '/' && d? == some '-') || c == '"'
        let isInterpOpen := c == '"' && (cur == ['!', 's'] || cur == ['!', 'm'] || cur == ['!', 'f'])
        if isStart || !(isIdentChar c || c == '«') then
          if !cur.isEmpty then acc := acc.push (String.ofList cur.reverse)
          cur := []
        if c == '-' && d? == some '-' then inLine := true; i := i + 2
        else if c == '/' && d? == some '-' then depth := 1; i := i + 2
        else if c == '"' then
          inStr := true
          inInterpStr := isInterpOpen
          i := i + 1
        else if c == '«' then inGuil := true; i := i + 1
        else if c == '{' && !interpStack.isEmpty then
          match interpStack with
          | d :: rest => interpStack := (d + 1) :: rest
          | [] => pure ()
          i := i + 1
        else if c == '}' && !interpStack.isEmpty then
          match interpStack with
          | 0 :: rest =>
            interpStack := rest
            inStr := true
            inInterpStr := true
          | (d + 1) :: rest =>
            interpStack := d :: rest
          | [] => pure ()
          i := i + 1
        else
          if isIdentChar c then cur := c :: cur
          i := i + 1
    else break
  if !cur.isEmpty then acc := acc.push (String.ofList cur.reverse)
  let balanced := !inStr && rawHashes.isNone && depth == 0 && !inGuil && interpStack.isEmpty
  return (acc, balanced)

def forbiddenSourceIdentifier (tok : String) : Bool :=
  (tok.splitOn "_unsafe_rec").length > 1

/-! ## The audit -/

def toolchainAllowedAxiom (L : Loaded) (n m : Name) : Bool :=
  L.toolchainProv.contains m && L.req.axioms.contains (n.toString, m.toString)

/-- Well-formed native-evaluation axiom: generated name shape and type exactly
`@Eq.{1} Bool e Bool.true` with `Eq`, `Bool`, `Bool.true` from verified toolchain modules and a
closed `e` that is not the literal `Bool.false`. -/
def wellFormedNativeAxiom (L : Loaded) (ci : ConstantInfo) : Option Expr := do
  guard (hasNativeComponent ci.name)
  let .str _ last := ci.name | none
  guard (last.startsWith "ax_")
  guard ci.levelParams.isEmpty
  let ty := ci.type
  guard (ty.isAppOfArity ``Eq 3)
  let .const _ [lvl] := ty.getAppFn | none
  guard (lvl == Level.one)
  let args := ty.getAppArgs
  guard (args[0]! == mkConst ``Bool)
  guard (args[2]! == mkConst ``Bool.true)
  for c in [``Eq, ``Bool, ``Bool.true] do
    let m ← origin? L.env c
    guard (L.toolchainProv.contains m)
  let e := args[1]!
  guard (isClosedExpr e)
  guard (e != mkConst ``Bool.false)
  return e

/-- Bounded `Meta.whnf` cost gate (all transparency, no smart unfolding, fresh caches), then the
kernel on both polarities. -/
def recheckNative (L : Loaded) (n : Name) (e : Expr) : AuditM Unit := do
  let hb := L.req.nativeHeartbeats
  let value ← (show IO (Option Expr) from do
    try
      runMeta L.env (do
        let r ← Meta.withTransparency .all (Meta.whnf e)
        return some r) (heartbeats := hb)
    catch _ => pure none)
  let litTrue := mkConst ``Bool.true
  let litFalse := mkConst ``Bool.false
  match value with
  | some v =>
    if v == litTrue || v == litFalse then
      let mkEqTy (b : Expr) := mkApp3 (mkConst ``Eq [Level.one]) (mkConst ``Bool) e b
      let refl (b : Expr) := mkApp2 (mkConst ``Eq.refl [Level.one]) (mkConst ``Bool) b
      if ← kernelAccepts L.env [] (mkEqTy litFalse) (refl litFalse) hb then
        report "unapprovedAxiom" n ((origin? L.env n).getD .anonymous)
          "forged native-evaluation axiom: the kernel proves the opposite polarity"
        return
      if ← kernelAccepts L.env [] (mkEqTy litTrue) (refl litTrue) hb then
        modify fun (s : AuditState) => { s with kernelConfirmedNative := s.kernelConfirmedNative.insert n }
        return
  | none => pure ()
  modify fun (s : AuditState) => { s with provisionalNative := s.provisionalNative.insert n }

/-- Axiom policy for one reached axiom. `localOk` admits file-local test axioms. -/
def checkAxiom (L : Loaded) (ci : ConstantInfo) (m : Name) (localOk : Name → Bool) : AuditM Unit := do
  let n := ci.name
  if n == ``sorryAx then
    report "sorryAxiomReached" n m "incomplete proof (sorryAx)"
    return
  if toolchainAllowedAxiom L n m then
    modify fun (s : AuditState) => { s with reachedAxioms := s.reachedAxioms.insert n }
    return
  if nativeBuiltinAxioms.contains n then
    if L.toolchainProv.contains m then
      if L.req.allowProvisionalNative then
        modify fun (s : AuditState) => { s with provisionalNative := s.provisionalNative.insert n }
      else
        report "nativeDecideReached" n m "native evaluation axiom (trust-gating audits reject native evaluation)"
    else
      report "unapprovedAxiom" n m "native-evaluation axiom name declared outside the toolchain"
    return
  if hasNativeComponent n then
    match wellFormedNativeAxiom L ci with
    | some e =>
      modify fun (s : AuditState) => { s with nativeAxioms := s.nativeAxioms.insert n }
      if L.req.allowProvisionalNative then
        recheckNative L n e
      else
        report "nativeDecideReached" n m "native_decide axiom (trust-gating audits reject native evaluation)"
    | none => report "unapprovedAxiom" n m "malformed or spoofed native-evaluation axiom"
    return
  if localOk m then
    modify fun (s : AuditState) => { s with localAxioms := s.localAxioms.insert n }
    return
  report "unapprovedAxiom" n m "axiom outside the locked toolchain policy"

/-- Does `c` name a recursion/fixpoint combinator emitted by Lean's equation compiler? -/
def isRecursionCombinator (env : Environment) (c : Name) : Bool :=
  c == ``WellFounded.fix || c == ``WellFounded.Nat.fix || c == ``WellFounded.fixF ||
  c == ``Acc.rec || (`Lean.Order).isPrefixOf c ||
  (match c with
   | .str p s =>
     -- Structural recursion is encoded through the inductive type's `brecOn`/`binductionOn`; a
     -- bare recursor (`T.rec`) in a parent is not something the equation compiler emits.
     (s == "brecOn" || s.startsWith "brecOn_" || s == "binductionOn") &&
       (env.find? p matches some (.inductInfo _))
   | _ => false)

/-- Does `parentCi`'s body (or its same-module `_unary` / `_mutual` helper) use a recursion
combinator, as every equation-compiler parent of a genuine `_unsafe_rec` companion does? -/
def parentUsesRecursionCombinator (env : Environment) (parent : Name) (parentCi : ConstantInfo)
    (recMod : Option Name) : Bool := Id.run do
  let checkCi (ci : ConstantInfo) : Bool :=
    match ci.value? (allowOpaque := true) with
    | some v => v.getUsedConstants.any (isRecursionCombinator env)
    | none => false
  if checkCi parentCi then return true
  for suffix in #["_unary", "_mutual"] do
    let helper := parent.str suffix
    if origin? env helper == recMod then
      if let some hci := env.find? helper then
        if checkCi hci then return true
  return false

/-- Is `ci` a genuine equation-compiler code-generation companion `p._unsafe_rec`? -/
def genuineCompanion (L : Loaded) (ci : ConstantInfo) : Except String Unit := do
  let .str parent "_unsafe_rec" := ci.name | throw "not a companion name"
  if (match parent with | .str _ "_unsafe_rec" => true | _ => false) then
    throw "nested _unsafe_rec companion"
  unless ci.isPartial && !ci.isUnsafe do throw "companion is not a safe partial definition"
  let some parentCi := L.env.find? parent | throw s!"companion without parent {parent}"
  unless parentCi matches .defnInfo _ do
    throw s!"companion parent {parent} is not a definition (partial def or forged sibling)"
  if parentCi.isUnsafe || parentCi.isPartial then throw s!"companion parent {parent} is unsafe/partial"
  unless ci.type == parentCi.type && ci.levelParams == parentCi.levelParams do
    throw "companion type/universe parameters differ from its parent"
  let recMod := origin? L.env ci.name
  unless recMod.isSome && origin? L.env parent == recMod do
    throw "companion and parent are declared in different modules"
  unless parentUsesRecursionCombinator L.env parent parentCi recMod do
    throw s!"companion parent {parent} does not use a recursion combinator"
  let body := (ci.value? (allowOpaque := true)).getD (mkConst ``True)
  unless body.getUsedConstants.any (fun c =>
      (match c with | .str _ "_unsafe_rec" => true | _ => false) &&
      origin? L.env c == recMod) do
    throw "companion body is not recursive through a same-module _unsafe_rec"

/-- A lazily realized reserved theorem (`.eq_def`, `.eq_1`, ...) may be stored by several audited
modules with different proofs of the same statement; the environment keeps one of them. Another
copy is accepted only if it is a theorem with the same statement and universe parameters whose own
proof the kernel accepts; its proof's dependencies are then audited as additional roots. -/
def reservedTheoremCopyOk (env : Environment) (n : Name) (stored ci : ConstantInfo) : IO Bool := do
  unless isReservedName env n do return false
  let .thmInfo sv := stored | return false
  let .thmInfo cv := ci | return false
  unless sv.type == cv.type && sv.levelParams == cv.levelParams && declIsClosed ci do return false
  kernelAccepts env cv.levelParams cv.type cv.value 100000

/-- Compiler-override attributes on one declaration (lookups by defining module). -/
def overrideKinds (env : Environment) (n : Name) : Array String := Id.run do
  let mut kinds := #[]
  if (Compiler.getImplementedBy? env n).isSome then kinds := kinds.push "implemented_by"
  if isExtern env n || isExternC env n then kinds := kinds.push "extern"
  if (getExportNameFor? env n).isSome then kinds := kinds.push "export"
  if (getRegularInitFnNameFor? env n).isSome || isIOUnitRegularInitFn env n then kinds := kinds.push "init"
  if (getBuiltinInitFnNameFor? env n).isSome || isIOUnitBuiltinInitFn env n then kinds := kinds.push "builtin_init"
  return kinds

/-- Validate the compiler-intrinsic tags of one non-toolchain declaration. -/
def checkIntrinsicTags (L : Loaded) (n : Name) (m : Name) (budget : Nat) : AuditM Unit := do
  let env := L.env
  if isAuxRecursor env n then
    modify fun (s : AuditState) => { s with tagChecks := s.tagChecks + 1 }
    match n with
    | .str _ s =>
      if s == "casesOn" then
        match genuineCasesOn env n with
        | .ok () => pure ()
        | .error e => report "compilerOverrideAttribute" n m s!"casesOn_tag: {e}"
      else if s.startsWith "casesOn_" then
        report "compilerOverrideAttribute" n m "casesOn_tag: casesOn_* auxiliary-recursor name"
    -- `isAuxRecursorWithSuffix` only matches a final string component, so the code generator
    -- never treats a name ending in a number (hygienic `match_on_same_ctor` helpers) as casesOn.
    | _ => pure ()
  if isSparseCasesOn env n then
    modify fun (s : AuditState) => { s with tagChecks := s.tagChecks + 1 }
    if !sparseCasesOnNameOk env n then
      report "compilerOverrideAttribute" n m "sparse_casesOn_tag: name is neither <Ctor>.elim nor _sparseCasesOn"
    else
      match ← casesLikeSemantics env L.toolchainProv n budget with
      | .ok k => modify fun (s : AuditState) => { s with kernelTagConfirmations := s.kernelTagConfirmations + k }
      | .error e => report "compilerOverrideAttribute" n m s!"sparse_casesOn_tag: {e}"
  if let some info := noConfusionExt.find? env n then
    modify fun (s : AuditState) => { s with tagChecks := s.tagChecks + 1 }
    match ← noConfusionSemantics env L.toolchainProv n info budget with
    | .ok k => modify fun (s : AuditState) => { s with kernelTagConfirmations := s.kernelTagConfirmations + k }
    | .error e => report "compilerOverrideAttribute" n m s!"noConfusion_tag: {e}"

/-- Module-entry scans: every attribute, tag, compiler-pipeline and postponed-compilation entry
stored by a module, judged by the module that stores it (never by the name it mentions). -/
def scanModuleEntries (L : Loaded) : AuditM (Std.HashSet (Name × Name × Name) × NameSet) := do
  let env := L.env
  let mut toolchainCSimp : Std.HashSet (Name × Name × Name) := {}
  let mut toolchainImplByTargets : NameSet := {}
  for h : i in [0:env.header.modules.size] do
    let m := env.header.modules[i].module
    let isTool := L.toolchainProv.contains m
    -- Foreign or spoofed modules are already rejected; their entries add only noise.
    unless isTool || L.nonToolchain.contains m do continue
    for e in Compiler.CSimp.ext.ext.getModuleEntries env i do
      let ent := match e with | .global a => a | .scoped _ a => a
      if isTool then
        toolchainCSimp := toolchainCSimp.insert (ent.fromDeclName, ent.toDeclName, ent.thmName)
      else
        report "compilerOverrideAttribute" ent.fromDeclName m s!"csimp: {ent.fromDeclName} ↦ {ent.toDeclName} via {ent.thmName}"
    for installer in Compiler.LCNF.passManagerExt.getModuleEntries env i do
      report "compilerOverrideAttribute" installer m "cpass: compiler pass installer registered"
    for fe in Compiler.LCNF.Simp.ConstantFold.folderExt.getModuleEntries env i do
      report "compilerOverrideAttribute" fe.declName m s!"constant_fold: folder {fe.folderDeclName}"
    if isTool then
      for (_, tgt) in Compiler.implementedByAttr.ext.getModuleEntries env i do
        toolchainImplByTargets := toolchainImplByTargets.insert tgt
      continue
    for (n, _) in Compiler.implementedByAttr.ext.getModuleEntries env i do
      report "compilerOverrideAttribute" n m "implemented_by"
    for (n, _) in externAttr.ext.getModuleEntries env i do
      report "compilerOverrideAttribute" n m "extern"
    for (n, _) in exportAttr.ext.getModuleEntries env i do
      report "compilerOverrideAttribute" n m "export"
    for (n, _) in regularInitAttr.ext.getModuleEntries env i do
      report "compilerOverrideAttribute" n m "init"
    for (n, _) in regularInitAttr.ext.getModuleIREntries env i do
      report "compilerOverrideAttribute" n m "init"
    for (n, _) in builtinInitAttr.ext.getModuleEntries env i do
      report "compilerOverrideAttribute" n m "builtin_init"
    for entry in Compiler.LCNF.postponedCompileDeclsExt.getModuleEntries env i do
      for n in entry.declNames do
        report "environmentLoadFailed" n m "compilation postponed (separate compilation without IR)"
    for n in auxRecExt.getModuleEntries env i do
      unless origin? env n == some m do
        report "compilerOverrideAttribute" n m "casesOn_tag: auxiliary-recursor tag on a foreign declaration"
    for (n, _) in noConfusionExt.getModuleEntries env i do
      unless origin? env n == some m do
        report "compilerOverrideAttribute" n m "noConfusion_tag: tag on a foreign declaration"
  -- Live state across all `stateStack` frames, `newEntries`, and `scopedEntries`: only genuine
  -- toolchain triples, keyed by their own source constant.
  let csimpStack := Compiler.CSimp.ext.ext.getState env
  for frame in csimpStack.stateStack do
    for (k, ent) in frame.state.map.toList do
      unless k == ent.fromDeclName && toolchainCSimp.contains (k, ent.toDeclName, ent.thmName) do
        report "compilerOverrideAttribute" k .anonymous "csimp: live csimp entry is not a toolchain triple"
  for e in csimpStack.newEntries do
    let ent := match e with | .global a => a | .scoped _ a => a
    unless toolchainCSimp.contains (ent.fromDeclName, ent.toDeclName, ent.thmName) do
      report "compilerOverrideAttribute" ent.fromDeclName .anonymous "csimp: live newEntries entry is not a toolchain triple"
  for (_, entries) in csimpStack.scopedEntries.map.toList do
    for ent in entries.toArray do
      unless toolchainCSimp.contains (ent.fromDeclName, ent.toDeclName, ent.thmName) do
        report "compilerOverrideAttribute" ent.fromDeclName .anonymous "csimp: live scopedEntries entry is not a toolchain triple"
  let (livePasses, livePM) := Compiler.LCNF.passManagerExt.getState env
  unless livePasses.isEmpty do
    report "compilerOverrideAttribute" `cpass .anonymous "cpass: live compiler pass registration"
  unless passManagerFingerprint livePM == passManagerFingerprint Compiler.LCNF.builtinPassManager do
    report "compilerOverrideAttribute" `compiler_pipeline .anonymous "compiler_pipeline: live PassManager differs from builtinPassManager"
  let (liveFolders, liveFolderMap) := Compiler.LCNF.Simp.ConstantFold.folderExt.getState env
  unless liveFolders.isEmpty do
    report "compilerOverrideAttribute" `constant_fold .anonymous "constant_fold: live folder registration"
  let mut liveFolderKeys : NameSet := {}
  for (k, _) in liveFolderMap.toList do
    liveFolderKeys := liveFolderKeys.insert k
    unless builtinFolderKeySet.contains k do
      report "compilerOverrideAttribute" k .anonymous "constant_fold: live folder key not in builtinFolders"
  unless liveFolderKeys.size == builtinFolderKeySet.size do
    report "compilerOverrideAttribute" `constant_fold .anonymous "constant_fold: live folder table differs from builtinFolders"
  return (toolchainCSimp, toolchainImplByTargets)

/-- Lightweight summary of a trivial direct-return body across LCNF and IR phases, used to detect
cross-phase forgery (`baseExt` vs `monoExt` vs `IR.declMapExt`) and forged `ElimDeadBranches`
function summaries. -/
inductive SimpleRet where
  | param (idx : Nat)
  | natLit (v : Nat)
  | strLit (v : String)
  | ctor (c : Name)
  | other
  deriving BEq

def classifyLCNF (env : Environment) (d : Compiler.LCNF.Decl .pure) : SimpleRet :=
  match d.value with
  | .extern .. => .other
  | .code code =>
    let paramIdx (fv : FVarId) : Option Nat := d.params.findIdx? (·.fvarId == fv)
    match code with
    | .return fv =>
      match paramIdx fv with
      | some i => .param i
      | none => .other
    | .let ld (.return fv) =>
      if ld.fvarId == fv then
        match ld.value with
        | .lit (.nat v) => .natLit v
        | .lit (.str v) => .strLit v
        | .fvar fv2 #[] =>
          match paramIdx fv2 with
          | some i => .param i
          | none => .other
        | .const c _ _ =>
          if env.find? c matches some (.ctorInfo _) then .ctor c else .other
        | _ => .other
      else .other
    | _ => .other

def classifyIR (d : IR.Decl) : SimpleRet :=
  match d with
  | .extern .. => .other
  | .fdecl _ xs _ body _ =>
    let paramIdx (v : IR.VarId) : Option Nat := xs.findIdx? (·.x == v)
    let rec stripRC (b : IR.FnBody) (fuel : Nat) : IR.FnBody :=
      match fuel, b with
      | 0, _ => b
      | fuel + 1, .inc _ _ _ _ rest => stripRC rest fuel
      | fuel + 1, .dec _ _ _ _ rest => stripRC rest fuel
      | _, _ => b
    match stripRC body 16 with
    | .ret (.var v) =>
      match paramIdx v with
      | some i => .param i
      | none => .other
    | .vdecl x _ (.lit (.num v)) rest =>
      match stripRC rest 16 with
      | .ret (.var y) => if x == y then .natLit v else .other
      | _ => .other
    | .vdecl x _ (.lit (.str v)) rest =>
      match stripRC rest 16 with
      | .ret (.var y) => if x == y then .strLit v else .other
      | _ => .other
    | _ => .other

/-- Cross-phase compatibility: ignore `.other` and `.ctor` (trivial structures erase `.ctor` to
`.param` in `mono`, and enums lower `.ctor` to `.natLit` in `IR`), while rejecting direct
contradictions between `.param`, `.natLit`, and `.strLit`. -/
def simpleRetCompat (a b : SimpleRet) : Bool :=
  match a, b with
  | .other, _ | _, .other | .ctor _, _ | _, .ctor _ => true
  | .natLit x, .natLit y => x == y
  | .strLit x, .strLit y => x == y
  | .param _, .param _ => true
  | _, _ => false

/-- Check whether an `ElimDeadBranches` summary value is consistent with a trivial `mono` body. -/
def summaryCompatWithMono (ret : SimpleRet)
    (val : Compiler.LCNF.UnreachableBranches.Value) : Bool :=
  match val with
  | .top => true
  | .bot =>
    match ret with
    | .other => true
    | _ => false
  | .ctor c _ =>
    match ret with
    | .param _ => false
    | .ctor c' => c == c'
    | _ => true
  | .choice vs =>
    match ret with
    | .param _ => false
    | .ctor c' => vs.any fun | .ctor c _ => c == c' | _ => true
    | _ => true

/-- Collect constant callees directly mentioned in an LCNF pure `Code` tree (total bounded walk;
returns `none` on fuel exhaustion so callers fail closed with `auditFuelExhausted`). -/
def collectLCNFCodeConsts (code : Compiler.LCNF.Code .pure) (acc : NameSet) (fuel : Nat) :
    Option NameSet :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match code with
    | .let ld k =>
      let acc := match ld.value with
        | .const c _ _ => acc.insert c
        | _ => acc
      collectLCNFCodeConsts k acc fuel
    | .fun fd k | .jp fd k => do
      let acc ← collectLCNFCodeConsts fd.value acc fuel
      collectLCNFCodeConsts k acc fuel
    | .cases cs =>
      cs.alts.foldlM (init := acc) fun a alt =>
        collectLCNFCodeConsts alt.getCode a fuel
    | .jmp .. | .return .. | .unreach .. => some acc

/-- Check callees of a pure LCNF declaration (base/mono) for unsafe or partial targets. -/
def checkLCNFDeclCallees (L : Loaded) (m : Name) (phaseLabel : String)
    (toolchainImplByTargets : NameSet) (d : Compiler.LCNF.Decl .pure) : AuditM Unit := do
  let env := L.env
  let n := d.name
  let .code code := d.value | return
  let some consts := collectLCNFCodeConsts code {} 16384
    | report "auditFuelExhausted" n m s!"{phaseLabel} LCNF callee scan exhausted its fuel"; return
  for c in consts do
    if c == n then continue
    if let some cm := origin? env c then
      if let some cci := env.find? c then
        if cci.isUnsafe then
          unless L.toolchainProv.contains cm &&
              (compilerBorrowedUnsafeIntrinsics.contains c || toolchainImplByTargets.contains c) do
            report "unsafeDeclaration" c m s!"{phaseLabel} LCNF callee of {n} invokes unsafe declaration {c} from {cm}"
        else if cci.isPartial then
          unless (match c with | .str _ "_unsafe_rec" => true | _ => false) do
            report "partialOrUnsafeRecDependency" c m s!"{phaseLabel} LCNF callee of {n} invokes partial declaration {c} from {cm}"
        if let .opaqueInfo _ := cci then
          if let some sib := env.find? (c.str "_unsafe_rec") then
            if sib.isPartial || sib.isUnsafe then
              report "partialOrUnsafeRecDependency" c m s!"{phaseLabel} LCNF callee of {n} invokes partial def {c} from {cm}"

/-- Audit `sorryDep?` and every callee of a concrete IR declaration `d`. -/
def checkIRDeclBody (L : Loaded) (m : Name) (toolchainImplByTargets : NameSet) (d : IR.Decl) :
    AuditM Unit := do
  let env := L.env
  let n := d.name
  match d with
  | .fdecl _ _ _ _ info =>
    if let some dep := info.sorryDep? then
      report "sorryOrUnproved" n m s!"IR declaration records sorry dependency {dep}"
  | .extern .. => return
  for c in IR.collectUsedDecls env [d] do
    if c == n then continue
    match origin? env c with
    | none =>
      if (IR.findEnvDecl env c).isNone then
        report "environmentLoadFailed" c m s!"IR callee of {n} is unknown"
    | some cm =>
      if let some cci := env.find? c then
        if cci.isUnsafe then
          unless L.toolchainProv.contains cm &&
              (compilerBorrowedUnsafeIntrinsics.contains c || toolchainImplByTargets.contains c) do
            report "unsafeDeclaration" c m s!"IR callee of {n} invokes unsafe declaration {c} from {cm}"
        else if cci.isPartial then
          unless (match c with | .str _ "_unsafe_rec" => true | _ => false) do
            report "partialOrUnsafeRecDependency" c m s!"IR callee of {n} invokes partial declaration {c} from {cm}"
        if let .opaqueInfo _ := cci then
          if let some sib := env.find? (c.str "_unsafe_rec") then
            if sib.isPartial || sib.isUnsafe then
              report "partialOrUnsafeRecDependency" c m s!"IR callee of {n} invokes partial def {c} from {cm}"

/-- IR checks for one non-toolchain module. Audits every entry in both module and `.ir` tables
directly (preventing duplicate-entry `binSearch` shadowing in `IR.findEnvDecl`). -/
def checkModuleIR (L : Loaded) (i : Nat) (m : Name) (data : ModuleData)
    (toolchainImplByTargets : NameSet) : AuditM Unit := do
  let env := L.env
  let mut irNames : NameSet := {}
  let mut seenMod : NameSet := {}
  for d in IR.declMapExt.getModuleEntries env i do
    let n := d.name
    if seenMod.contains n then
      report "environmentLoadFailed" n m "duplicate IR declaration entry in module table"
    seenMod := seenMod.insert n
    irNames := irNames.insert n
    checkIRDeclBody L m toolchainImplByTargets d
  let mut seenIR : NameSet := {}
  for d in IR.declMapExt.getModuleIREntries env i do
    let n := d.name
    if seenIR.contains n then
      report "environmentLoadFailed" n m "duplicate IR declaration entry in IR table"
    seenIR := seenIR.insert n
    irNames := irNames.insert n
    match d with
    | .extern f .. =>
      unless isExtern env f || isExternC env f do
        report "environmentLoadFailed" f m "opaque IR stub in IR table without @[extern]"
    | .fdecl .. => pure ()
    checkIRDeclBody L m toolchainImplByTargets d
  let kernelNames : NameSet := data.constNames.foldl (·.insert ·) {}
  let extraNames : NameSet := data.extraConstNames.foldl (·.insert ·) {}
  for n in irNames do
    unless kernelNames.contains n || extraNames.contains n do
      report "environmentLoadFailed" n m "IR declaration not owned by its module"
    unless origin? env n == some m do
      report "environmentLoadFailed" n m "IR declaration provenance mismatch"
    let some d := IR.findEnvDecl env n
      | report "environmentLoadFailed" n m "IR declaration not resolvable"; continue
    modify fun (s : AuditState) => { s with irDecls := s.irDecls + 1 }
    match d with
    | .extern f .. =>
      unless isExtern env f || isExternC env f do
        report "environmentLoadFailed" f m "opaque IR stub without @[extern] (compiled code not loaded)"
    | .fdecl .. => pure ()
  for n in data.extraConstNames do
    unless origin? env n == some m do
      report "environmentLoadFailed" n m "IR helper provenance mismatch"
  -- Compiled code that exists but was not loaded, plus duplicate/provenance checks on LCNF
  -- phase tables and dead-branch summaries, and cross-phase consistency for compiled definitions.
  let mut seenSig : NameSet := {}
  for sig in Compiler.LCNF.impureSigExt.getModuleEntries env i do
    let sn := sig.name
    if seenSig.contains sn then
      report "environmentLoadFailed" sn m "duplicate impure signature entry in module table"
    seenSig := seenSig.insert sn
    unless kernelNames.contains sn || extraNames.contains sn do
      report "environmentLoadFailed" sn m "impure signature not owned by its module"
    unless origin? env sn == some m do
      report "environmentLoadFailed" sn m "impure signature provenance mismatch"
    if (IR.findEnvDecl env sn).isNone then
      report "environmentLoadFailed" sn m "compiled signature without IR body"
  let mut seenSigIR : NameSet := {}
  for sig in Compiler.LCNF.impureSigExt.getModuleIREntries env i do
    let sn := sig.name
    if seenSigIR.contains sn then
      report "environmentLoadFailed" sn m "duplicate impure signature entry in IR table"
    seenSigIR := seenSigIR.insert sn
    unless kernelNames.contains sn || extraNames.contains sn do
      report "environmentLoadFailed" sn m "impure IR signature not owned by its module"
    unless origin? env sn == some m do
      report "environmentLoadFailed" sn m "impure IR signature provenance mismatch"
    if (IR.findEnvDecl env sn).isNone then
      report "environmentLoadFailed" sn m "compiled signature without IR body"
  let mut seenBase : NameSet := {}
  for bd in Compiler.LCNF.baseExt.getModuleEntries env i do
    let bn := bd.name
    if seenBase.contains bn then
      report "environmentLoadFailed" bn m "duplicate base-phase LCNF declaration entry"
    seenBase := seenBase.insert bn
    unless kernelNames.contains bn || extraNames.contains bn do
      report "environmentLoadFailed" bn m "base-phase LCNF declaration not owned by its module"
    unless origin? env bn == some m do
      report "environmentLoadFailed" bn m "base-phase LCNF declaration provenance mismatch"
    if (IR.findEnvDecl env bn).isNone then
      report "environmentLoadFailed" bn m "base-phase LCNF body without IR body"
    checkLCNFDeclCallees L m "base" toolchainImplByTargets bd
  let mut seenMono : NameSet := {}
  for md in Compiler.LCNF.monoExt.getModuleEntries env i do
    let mn := md.name
    if seenMono.contains mn then
      report "environmentLoadFailed" mn m "duplicate mono-phase LCNF declaration entry"
    seenMono := seenMono.insert mn
    unless kernelNames.contains mn || extraNames.contains mn do
      report "environmentLoadFailed" mn m "mono-phase LCNF declaration not owned by its module"
    unless origin? env mn == some m do
      report "environmentLoadFailed" mn m "mono-phase LCNF declaration provenance mismatch"
    if (IR.findEnvDecl env mn).isNone then
      report "environmentLoadFailed" mn m "mono-phase LCNF body without IR body"
    checkLCNFDeclCallees L m "mono" toolchainImplByTargets md
  let mut seenSumm : NameSet := {}
  for (dn, val) in Compiler.LCNF.UnreachableBranches.functionSummariesExt.getModuleEntries env i do
    if seenSumm.contains dn then
      report "environmentLoadFailed" dn m "duplicate dead-branch function summary entry"
    seenSumm := seenSumm.insert dn
    unless kernelNames.contains dn || extraNames.contains dn do
      report "environmentLoadFailed" dn m "dead-branch function summary not owned by its module"
    unless origin? env dn == some m do
      report "environmentLoadFailed" dn m "dead-branch function summary provenance mismatch"
    if let some md := Compiler.LCNF.getDeclCore? env Compiler.LCNF.monoExt dn then
      unless summaryCompatWithMono (classifyLCNF env md) val do
        report "compilerOverrideAttribute" dn m "dead_branch_summary: function summary contradicts mono LCNF body"
  for ci in data.constants do
    let n := ci.name
    if let some irDecl := IR.findEnvDecl env n then
      if (ci matches .defnInfo _) && !(isExtern env n || isExternC env n) then
        let bd? := Compiler.LCNF.getDeclCore? env Compiler.LCNF.baseExt n
        let md? := Compiler.LCNF.getDeclCore? env Compiler.LCNF.monoExt n
        if !seenBase.contains n && bd?.isNone then
          report "environmentLoadFailed" n m "IR body for definition without base-phase LCNF declaration"
        if !seenMono.contains n && md?.isNone then
          report "environmentLoadFailed" n m "IR body for definition without mono-phase LCNF declaration"
        if let (some bd, some md) := (bd?, md?) then
          let cb := classifyLCNF env bd
          let cm := classifyLCNF env md
          let ciR := classifyIR irDecl
          unless simpleRetCompat cb cm && simpleRetCompat cm ciR && simpleRetCompat cb ciR do
            report "compilerOverrideAttribute" n m "lcnf_ir_mismatch: base/mono LCNF and IR return values contradict each other"
      continue
    if (Compiler.LCNF.getSigCore? env Compiler.LCNF.impureSigExt n).isSome then
      report "environmentLoadFailed" n m "compiled signature without IR body"
    if (Compiler.LCNF.getDeclCore? env Compiler.LCNF.baseExt n).isSome then
      report "environmentLoadFailed" n m "base-phase LCNF body without IR body"
    if (Compiler.LCNF.getDeclCore? env Compiler.LCNF.monoExt n).isSome then
      report "environmentLoadFailed" n m "mono-phase LCNF body without IR body"

/-- Statement-origin separation: walking a claim theorem's statement (unfolding declarations of
`statementUnfold`) must never reach a module of `statementForbidden`. -/
def checkStatementOrigin (L : Loaded) (thm : Name) (m : Name) (fuel : Nat) : AuditM Unit := do
  let env := L.env
  let some ci := env.find? thm | report "missingDeclaration" thm m "claim theorem not found"; return
  let mut pending : List Name := (exprEdges ci.type {}).toList
  let mut visited : NameSet := pending.foldl (·.insert ·) {}
  let mut done := false
  for _ in [0:fuel] do
    match pending with
    | [] => done := true; break
    | n :: rest =>
      pending := rest
      let some nm := origin? env n
        | report "missingDeclaration" n m s!"statement of {thm} mentions an unknown constant"; continue
      if L.req.statementForbidden.contains nm then
        report "statementOriginLeak" thm m s!"theorem statement of {thm} depends on untrusted theory declaration {n} from {nm}"
      if L.req.statementUnfold.contains nm then
        let some dci := env.find? n
          | report "missingDeclaration" n nm "statement dependency not found"; continue
        for d in declEdges dci do
          unless visited.contains d do
            visited := visited.insert d
            pending := d :: pending
  unless done do report "auditFuelExhausted" thm m "statement-origin walk exhausted its fuel"

/-- Kernel dependency closure from `roots` (visited-at-push, so iterations are bounded by the
number of constants). -/
def closure (L : Loaded) (roots : Array Name) (visited0 : NameSet) (genuine : NameSet)
    (localOk : Name → Bool) (fuel : Nat) (label : Name) : AuditM NameSet := do
  let env := L.env
  let mut visited := visited0
  let mut pending : List Name := []
  for r in roots do
    unless visited.contains r do
      visited := visited.insert r
      pending := r :: pending
  let mut done := false
  for _ in [0:fuel] do
    match pending with
    | [] => done := true; break
    | n :: rest =>
      pending := rest
      modify fun (s : AuditState) => { s with reachable := s.reachable + 1 }
      let some ci := env.find? n
        | report "missingDeclaration" n ((origin? env n).getD .anonymous) "dependency not found"; continue
      let some m := origin? env n
        | report "missingDeclaration" n .anonymous "dependency without module origin"; continue
      unless declIsClosed ci do
        report "openExpression" n m "open expression in stored declaration"
      if ci.isUnsafe then
        report "unsafeDeclaration" n m "unsafe declaration reached"
      else if ci.isPartial && !genuine.contains n then
        report "partialOrUnsafeRecDependency" n m "partial declaration reached"
      if let .opaqueInfo _ := ci then
        if let some sib := env.find? (n.str "_unsafe_rec") then
          if sib.isPartial || sib.isUnsafe then
            report "partialOrUnsafeRecDependency" n m "partial def (opaque with _unsafe_rec) reached"
      if ci matches .axiomInfo _ then
        checkAxiom L ci m localOk
      for d in declEdges ci do
        unless visited.contains d do
          visited := visited.insert d
          pending := d :: pending
  unless done do report "auditFuelExhausted" label label "dependency closure exhausted its fuel"
  return visited

def graphFor (env : Environment) (tracked : Array Name) : Json :=
  Json.mkObj <| (env.header.modules.zip env.header.moduleData).toList.filterMap fun (m, d) =>
    if tracked.contains m.module then some (m.module.toString, Lean.toJson d.imports) else none

def failWithViolations (req : Request) (violations : Array Violation) : IO α := do
  let k := max req.maxReported 1
  let shown := (violations.extract 0 k).toList.map Violation.render
  let more := if violations.size > k then s!" (+{violations.size - k} more)" else ""
  let tags := (violations.foldl (fun (acc : Std.HashMap String Nat) v => acc.insert v.tag (acc.getD v.tag 0 + 1)) {}).toList
  let tagSummary := ",".intercalate ((tags.toArray.qsort (fun a b => a.1 < b.1)).toList.map fun (t, c) => s!"{t}={c}")
  fail s!"olean-audit rejected ({violations.size} violation(s); {tagSummary}): {"; ".intercalate shown}{more}"

/-- Provenance, inventory, policy and replay checks over one loaded environment. -/
def auditCore (req : Request) (env : Environment) (libDir : System.FilePath)
    (artMap : Std.HashMap Name (Array System.FilePath × Array System.FilePath))
    (modIdx : Std.HashMap Name Nat) (preloaded : Nat) (toolchainNames : Std.HashSet Name) :
    AuditM (Loaded × Nat × Nat × Bool × Nat) := do
  -- Provenance of every loaded module.
  let mut toolchainProv : Std.HashSet Name := {}
  let mut nonToolchain : Array Name := #[]
  let mut partsChecked := preloaded
  for h : idx in [0:env.header.modules.size] do
    let mod := env.header.modules[idx].module
    let data := env.header.moduleData[idx]!
    let tool := isToolchainName req.toolchainRoots mod
    let base := (libDir / modRelPath mod)
    match artMap[mod]? with
    | some (olean, ir) =>
      -- Shape, names and canonical paths were verified before loading; what needs the loaded
      -- data is the module-system flag: a `module` file keeps private data in `.olean.private`
      -- and its compiled code only in `.ir`.
      if data.isModule && (olean.size != 3 || ir.size != 2) then
        report "missingPrivateArtifact" mod mod "module-system file without all of .olean.server, .olean.private, .ir.sig and .ir"
      if tool then toolchainProv := toolchainProv.insert mod
      else
        unless req.modules.contains mod do
          report "foreignModule" mod mod "module outside the admitted module set"
        nonToolchain := nonToolchain.push mod
    | none =>
      if !tool then
        report "foreignModule" mod mod "non-toolchain module resolved outside the admitted artifacts"
        continue
      let (olean, ir) ← sysrootParts libDir mod
      partsChecked := partsChecked + (← checkModuleParts mod base olean ir data.isModule)
      toolchainProv := toolchainProv.insert mod
  for m in req.modules do
    unless modIdx.contains m do
      report "missingDeclaration" m m "admitted module missing from the loaded environment"
  if nonToolchain.isEmpty then
    report "noAuditTargets" .anonymous .anonymous "no non-toolchain modules to audit"
  let L : Loaded := { env, req, libDir, artMap, modIdx, toolchainProv, nonToolchain }
  -- Admitted import DAG.
  if let some expected := req.graph then
    let tracked := env.header.modules.filterMap fun (m : EffectiveImport) =>
      match expected.getObjVal? m.module.toString with
      | .ok _ => some m.module
      | .error _ => none
    for m in nonToolchain do
      unless tracked.contains m do
        report "graphMismatch" m m "module missing from the admitted import DAG"
    for m in tracked do
      let some i := modIdx[m]? | continue
      let actual := Lean.toJson env.header.moduleData[i]!.imports
      let same := match expected.getObjVal? m.toString with
        | .ok e => e == actual
        | .error _ => false
      unless same do
        report "graphMismatch" m m "compiled imports differ from the admitted import DAG"
  let (_toolchainCSimp, toolchainImplByTargets) ← scanModuleEntries L
  -- Inventory consistency, companions, overrides, tags and IR of every non-toolchain module.
  let mut genuine : NameSet := {}
  let mut strictRoots : Array Name := #[]
  let mut localRoots : Std.HashMap Name (Array Name) := {}
  let mut companionRoots : Array (Name × Name) := #[]
  let mut replayLocals : Std.HashMap Name ConstantInfo := {}
  let mut allNames : NameSet := {}
  let mut extraEdges : Array (Name × NameSet) := #[]
  let mut audited := 0
  let budget := 400
  for m in nonToolchain do
    let some i := modIdx[m]? | continue
    let data := env.header.moduleData[i]!
    unless data.constNames == data.constants.map ConstantInfo.name do
      report "inventoryMismatch" m m "constNames differ from stored constants"
    for ci in data.constants do
      let n := ci.name
      let some om := origin? env n | report "inventoryMismatch" n m "declaration without origin"; continue
      if om != m then
        -- A lazily realized reserved declaration (`.eq_1`, `.congr_simp`, ...) may be stored by
        -- several audited modules; it is audited once, in the module the environment attributes
        -- it to, and every other copy must be identical to the stored declaration.
        unless req.modules.contains om && nonToolchain.contains om && isReservedName env n do
          report "inventoryMismatch" n m s!"declaration attributed to {om}"
        match env.checked.get.find? n with
        | some stored =>
          unless stored.type == ci.type && stored.value? true == ci.value? true &&
              stored.levelParams == ci.levelParams && stored.isUnsafe == ci.isUnsafe &&
              stored.isPartial == ci.isPartial && kindOf stored == kindOf ci do
            if ← reservedTheoremCopyOk env n stored ci then
              extraEdges := extraEdges.push (m, declEdges ci)
            else
              report "inventoryMismatch" n m "reserved declaration copy differs from the stored declaration"
        | none => report "inventoryMismatch" n m "declaration missing from the kernel environment"
        continue
      audited := audited + 1
      if allNames.contains n then report "inventoryMismatch" n m "duplicate declaration"
      allNames := allNames.insert n
      if compilerReservedNames.contains n then
        report "compilerOverrideAttribute" n m
          "compiler_intrinsic_name: non-toolchain declaration shadows compiler-builtin constant"
      if toolchainNames.contains n || n.getRoot == `Init || n.getRoot == `Std || n.getRoot == `Lean then
        report "compilerOverrideAttribute" n m
          "toolchain_name: non-toolchain declaration reuses a name or namespace reserved by the pinned toolchain"
      match env.checked.get.find? n with
      | none => report "inventoryMismatch" n m "declaration missing from the kernel environment"
      | some stored =>
        unless stored.type == ci.type && stored.value? true == ci.value? true &&
            stored.levelParams == ci.levelParams && stored.isUnsafe == ci.isUnsafe &&
            stored.isPartial == ci.isPartial && kindOf stored == kindOf ci do
          if ← reservedTheoremCopyOk env n stored ci then
            extraEdges := extraEdges.push (m, declEdges ci)
          else
            report "inventoryMismatch" n m "kernel environment differs from the module inventory"
      if !declIsClosed ci then report "openExpression" n m "open expression in stored declaration"
      if ci.hasValue true && (ci.value? true).isNone then
        report "inventoryMismatch" n m "missing stored body"
      let mut isCompanion := false
      match n with
      | .str _ "_unsafe_rec" =>
        match genuineCompanion L ci with
        | .ok () =>
          genuine := genuine.insert n
          isCompanion := true
          modify fun (s : AuditState) => { s with companions := s.companions + 1 }
        | .error e => report "compilerOverrideAttribute" n m s!"unsafe_rec_sibling: {e}"
      | _ =>
        if forbiddenSourceIdentifier n.toString then
          report "sourceForbiddenIdentifier" n m "non-companion declaration name mentions _unsafe_rec"
      if ci.isUnsafe then report "unsafeDeclaration" n m "unsafe declaration"
      else if ci.isPartial && !isCompanion then
        report "partialOrUnsafeRecDependency" n m "partial declaration"
      if let .opaqueInfo _ := ci then
        if let some sib := env.find? (n.str "_unsafe_rec") then
          if sib.isPartial || sib.isUnsafe then
            report "partialOrUnsafeRecDependency" n m "partial def (opaque with _unsafe_rec)"
      for k in overrideKinds env n do
        report "compilerOverrideAttribute" n m k
      checkIntrinsicTags L n m budget
      if isCompanion then
        companionRoots := companionRoots.push (m, n)
      else if req.localAxiomModules.contains m then
        localRoots := localRoots.insert m ((localRoots.getD m #[]).push n)
      else
        strictRoots := strictRoots.push n
      unless isCompanion do replayLocals := replayLocals.insert n ci
    for n in data.extraConstNames do
      if toolchainNames.contains n then
        report "compilerOverrideAttribute" n m
          "toolchain_name: IR helper reuses a name the pinned toolchain declares"
    checkModuleIR L i m data toolchainImplByTargets
  -- Uninventoried kernel constants attributed to an audited module.
  for (n, _) in env.checked.get.constants do
    if let some om := origin? env n then
      if nonToolchain.contains om && !allNames.contains n then
        report "inventoryMismatch" n om "uninventoried kernel constant"
  -- Closures: strict roots first, then each file-local-axiom test module separately.
  let totalConsts := env.header.moduleData.foldl (fun a d => a + d.constants.size + d.extraConstNames.size) 0
  let fuel := totalConsts + allNames.size + 16
  -- Reserved theorem copies whose proofs differ from the stored one: their proofs are audited too.
  for (m, edges) in extraEdges do
    if req.localAxiomModules.contains m then
      localRoots := localRoots.insert m ((localRoots.getD m #[]) ++ edges.toArray)
    else
      strictRoots := strictRoots ++ edges.toArray
  -- Kernel closures never admit a code-generation companion: the kernel forbids safe declarations
  -- from mentioning `partial` ones, so a companion reached from a kernel root is a forgery.
  let strictVisited ← closure L strictRoots {} {} (fun _ => false) fuel `strict
  let mut localVisited : Std.HashMap Name NameSet := {}
  for (m, rs) in localRoots.toList do
    let v ← closure L rs strictVisited {} (fun om => om == m) fuel m
    localVisited := localVisited.insert m v
  -- Companion bodies are compiled code only; their dependencies are audited under the policy of
  -- the module that stores them, admitting (other) genuine companions.
  for (m, c) in companionRoots do
    if req.localAxiomModules.contains m then
      let _ ← closure L #[c] (localVisited.getD m strictVisited) genuine (fun om => om == m) fuel m
    else
      let _ ← closure L #[c] strictVisited genuine (fun _ => false) fuel `companions
  -- Statement origins of claim theorems.
  for m in req.claimModules do
    let some i := modIdx[m]?
      | report "missingDeclaration" m m "claim module missing from the loaded environment"; continue
    for ci in env.header.moduleData[i]!.constants do
      if ci matches .thmInfo _ then
        checkStatementOrigin L ci.name m fuel
  -- Source-level rule: no user identifier may mention `_unsafe_rec`.
  for (m, path) in req.sources do
    let okPath ← checkCanonicalPart m path
    unless okPath do continue
    let text? ← (show IO (Option String) from do
      try pure (some (← IO.FS.readFile path)) catch _ => pure none)
    let some text := text?
      | report "environmentLoadFailed" m m s!"cannot read source {path}"; continue
    let (toks, balanced) := scanIdents text
    unless balanced do
      report "sourceForbiddenIdentifier" m m "source scan ended with unclosed string, comment, guillemet, or interpolation state"
    for tok in toks do
      if forbiddenSourceIdentifier tok then
        report "sourceForbiddenIdentifier" tok.toName m "user identifiers must not mention _unsafe_rec"
  -- Kernel replay of every non-toolchain declaration on the toolchain-only environment.
  let baseRoots := env.header.modules.filterMap fun (m : EffectiveImport) =>
    if toolchainProv.contains m.module then some m.module else none
  let mut replayed := false
  if (← get).violations.isEmpty then
    let base ← loadEnvironment req baseRoots
    match ← (EIO.toBaseIO (base.toKernelEnv.replay replayLocals)) with
    | .ok _ => replayed := true
    | .error e => report "kernelReplayFailed" .anonymous .anonymous s!"kernel replay failed: {e}"
  return (L, partsChecked, audited, replayed, replayLocals.size)

/-- Load, check provenance, and audit. -/
def audit (req : Request) : IO Json := do
  let startUs ← IO.monoNanosNow
  let realSys ← (IO.FS.realPath req.sysroot) <|> fail s!"cannot resolve sysroot {req.sysroot}"
  unless realSys == req.sysroot do fail s!"[moduleProvenanceSpoofed] sysroot is not canonical: {req.sysroot}"
  let libDir := req.sysroot / "lib" / "lean"
  let (preloaded, preSt) ← (preloadArtifactChecks req).run {}
  if !preSt.violations.isEmpty then failWithViolations req preSt.violations
  let toolchainNames ← toolchainNameInventory req
  let env ← loadEnvironment req req.roots
  let importUs ← IO.monoNanosNow
  let mut artMap : Std.HashMap Name (Array System.FilePath × Array System.FilePath) := {}
  for (m, o, i) in req.artifacts do artMap := artMap.insert m (o, i)
  let mut modIdx : Std.HashMap Name Nat := {}
  for h : i in [0:env.header.modules.size] do
    modIdx := modIdx.insert env.header.modules[i].module i
  let (result, st) ← (auditCore req env libDir artMap modIdx preloaded toolchainNames).run {}
  let (L, partsChecked, audited, replayed, replayedCount) := result
  let endUs ← IO.monoNanosNow
  if !st.violations.isEmpty then failWithViolations req st.violations
  let sortNames (s : NameSet) : Array String := (s.toArray.map Name.toString).qsort (· < ·)
  if !st.provisionalNative.isEmpty then
    fail s!"olean-audit [provisionalNative] native-evaluation axioms stay provisional and never pass: {sortNames st.provisionalNative}"
  unless replayed do fail "[kernelReplayFailed] kernel replay did not run"
  return Json.mkObj [
    ("auditor", Lean.toJson "OleanEnvAuditor"),
    ("schema", Lean.toJson (1 : Nat)),
    ("scope", Lean.toJson req.scope),
    ("modules", Lean.toJson ((L.nonToolchain.map Name.toString).qsort (· < ·))),
    ("loadedModules", Lean.toJson env.header.modules.size),
    ("artifactPartsChecked", Lean.toJson partsChecked),
    ("auditedDeclarations", Lean.toJson audited),
    ("reachableDeclarations", Lean.toJson st.reachable),
    ("codegenCompanions", Lean.toJson st.companions),
    ("irDeclarationsChecked", Lean.toJson st.irDecls),
    ("intrinsicTagsChecked", Lean.toJson st.tagChecks),
    ("kernelTagConfirmations", Lean.toJson st.kernelTagConfirmations),
    ("axioms", Lean.toJson (sortNames st.reachedAxioms)),
    ("localTestAxioms", Lean.toJson st.localAxioms.size),
    ("kernelConfirmedNativeAxioms", Lean.toJson (sortNames st.kernelConfirmedNative)),
    ("provisionalNativeAxioms", Lean.toJson (sortNames st.provisionalNative)),
    ("replayedDeclarations", Lean.toJson replayedCount),
    ("replay", Lean.toJson true),
    ("importMicros", Lean.toJson ((importUs - startUs) / 1000)),
    ("elapsedMicros", Lean.toJson ((endUs - startUs) / 1000))]

def run (j : Json) : IO Json := do
  let req ← parseRequest j
  audit req

end OleanEnvAuditor

def main (args : List String) : IO UInt32 := do
  match args with
  | [request, output] =>
    try
      let j ← IO.ofExcept <| Json.parse (← IO.FS.readFile request)
      let result ← OleanEnvAuditor.run j
      IO.FS.writeFile output <| (Json.mkObj [("ok", toJson true), ("result", result)]).pretty
      return 0
    catch error =>
      let message := error.toString
      let category := if message.startsWith "policy:" then "policy" else "operational"
      IO.FS.writeFile output <| (Json.mkObj [
        ("ok", toJson false), ("category", toJson category), ("message", toJson message)]).pretty
      IO.eprintln message
      return if category == "policy" then 1 else 2
  | _ =>
    IO.eprintln "usage: OleanEnvAuditor <request.json> <result.json>"
    return 2
