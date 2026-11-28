module

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
import all Lean.Compiler.LCNF.Specialize
import all Lean.Compiler.LCNF.ToImpure
import all Lean.Compiler.IR.UnboxResult
import Lean.Compiler.NeverExtractAttr
import Lean.Compiler.InlineAttrs
import all Lean.AuxRecursor
public import Lean.Meta.Basic
import Lean.Meta.InferType
import Lean.Meta.WHNF
import Lean.Meta.ExprDefEq
import Lean.Meta.SynthInstance
import Lean.Meta.Instances
import Lean.Meta.CasesInfo
import Lean.Meta.Match.MatcherInfo
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

public structure Violation where
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
  constructiveModulesChecked : Nat := 0
  specStrengthChecksPassed : Nat := 0
  oleanFilesValidated : Nat := 0
  privateNamesAudited : Nat := 0
  moduleConstantsAxiomSwept : Nat := 0
  opaqueTheoremReadinessFlags : Nat := 0

abbrev AuditM := StateRefT AuditState IO

def report (tag : String) (decl : Name) (module : Name) (detail : String) : AuditM Unit := do
  let key := (tag, decl)
  if (← get).seen.contains key then return
  modify fun (s : AuditState) => { s with
    violations := s.violations.push { tag, decl, module, detail }
    seen := s.seen.insert key }

/-! ## Request -/

public inductive SpecClassKind where
  | item
  | statefulItem
  | totalItem
  | modularItem
  deriving BEq, Repr

inductive SpecStrengthCheckKind where
  | claim (thmName : Name)
  | synth (kind : SpecClassKind) (defId : String)
  deriving BEq, Repr

structure SpecStrengthCheckReq where
  target : SpecStrengthCheckKind
  certName : Name
  requiredCategories : Array String
  requireDeterministic : Bool
  requireInputSensitive : Bool
  deriving BEq

structure Request where
  sysroot : System.FilePath
  artifacts : Array (Name × Array System.FilePath × Array System.FilePath)
  foundation : Array Name
  roots : Array Name
  modules : Array Name
  graph : Option Json
  axioms : Array (String × String)
  allowClassicalChoice : Bool
  constructiveModules : Array Name
  specStrengthChecks : Array SpecStrengthCheckReq
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
  approvedBuildRoots : Array System.FilePath
  checkOpaqueTheoremReadiness : Bool

def allowedRequestKeys : List String := [
  "mode", "sysroot", "artifacts", "foundation", "graph", "axioms", "roots", "modules",
  "allowClassicalChoice", "constructiveModules", "specStrengthChecks",
  "localAxiomModules", "claimModules", "statementForbidden", "statementUnfold", "sources",
  "allowProvisionalNative", "toolchainRoots", "scope", "nativeHeartbeats", "maxReportedViolations",
  "approvedBuildRoots", "checkOpaqueTheoremReadiness"]

def allowedSpecCheckKeys : List String := [
  "kind", "claim", "defId", "cert", "requiredCategories", "requireDeterministic", "requireInputSensitive"]

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
  if toolchainRoots.isEmpty then fail "olean-audit request has no toolchainRoots"
  let mut seenToolRoots : NameSet := {}
  for r in toolchainRoots do
    unless r == `Init || r == `Std || r == `Lean do
      fail s!"unsupported toolchain root {r}"
    if seenToolRoots.contains r then fail s!"duplicate toolchain root {r}"
    seenToolRoots := seenToolRoots.insert r
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
  let mut seenSrcMods : NameSet := {}
  for (m, p) in rawSources do
    let mName := m.toName
    unless validModuleName mName do fail s!"invalid source module name {m}"
    if seenSrcMods.contains mName then fail s!"duplicate source entry for module {m}"
    seenSrcMods := seenSrcMods.insert mName
    sources := sources.push (mName, System.FilePath.mk p)
  let graph ← match j.getObjVal? "graph" with
    | .ok g =>
      match g.getObj? with
      | .ok _ => pure (some g)
      | .error _ => fail "malformed olean-audit request field graph: expected JSON object"
    | .error _ => pure none
  let nativeHeartbeats ← optField (α := Nat) j "nativeHeartbeats" 200
  if nativeHeartbeats == 0 then fail "malformed olean-audit request field nativeHeartbeats: must be positive"
  let allowClassicalChoice ← optField (α := Bool) j "allowClassicalChoice" true
  let constructiveModules := toNames (← optField (α := Array String) j "constructiveModules" #[])
  let mut seenConstructive : NameSet := {}
  for cm in constructiveModules do
    unless validModuleName cm && seenMods.contains cm do
      fail s!"invalid constructiveModules entry {cm}"
    if seenConstructive.contains cm then
      fail s!"duplicate constructiveModules entry {cm}"
    seenConstructive := seenConstructive.insert cm
  let rawSpecChecks ← optField (α := Array Json) j "specStrengthChecks" #[]
  let mut specStrengthChecks : Array SpecStrengthCheckReq := #[]
  for entry in rawSpecChecks do
    let .ok eObj := entry.getObj? | fail "malformed specStrengthChecks entry: expected JSON object"
    for (ek, _) in eObj.toArray do
      unless allowedSpecCheckKeys.contains ek do
        fail s!"unknown specStrengthChecks entry field {ek}"
    let kindStr ← reqField (α := String) entry "kind"
    let certStr ← reqField (α := String) entry "cert"
    let certName := certStr.toName
    unless validModuleName certName do fail s!"invalid specStrengthChecks cert name {certStr}"
    let requiredCategories ← optField (α := Array String) entry "requiredCategories" #[]
    let requireDeterministic ← optField (α := Bool) entry "requireDeterministic" false
    let requireInputSensitive ← optField (α := Bool) entry "requireInputSensitive" false
    let target ← match kindStr with
      | "claim" =>
        if (entry.getObjVal? "defId").isOk then
          fail "specStrengthChecks claim entry must not set defId"
        let claimStr ← reqField (α := String) entry "claim"
        let thmName := claimStr.toName
        unless validModuleName thmName do fail s!"invalid specStrengthChecks claim name {claimStr}"
        pure (.claim thmName)
      | "itemSynth" | "statefulItemSynth" | "totalItemSynth" | "modularItemSynth" =>
        if (entry.getObjVal? "claim").isOk then
          fail "specStrengthChecks synth entry must not set claim"
        let defId ← reqField (α := String) entry "defId"
        if defId.isEmpty then fail "specStrengthChecks defId must be non-empty"
        let clsKind := match kindStr with
          | "itemSynth" => SpecClassKind.item
          | "statefulItemSynth" => SpecClassKind.statefulItem
          | "totalItemSynth" => SpecClassKind.totalItem
          | _ => SpecClassKind.modularItem
        pure (.synth clsKind defId)
      | _ => fail s!"unsupported specStrengthChecks kind {kindStr}"
    specStrengthChecks := specStrengthChecks.push {
      target, certName, requiredCategories, requireDeterministic, requireInputSensitive
    }
  let approvedBuildRoots := (← optField (α := Array String) j "approvedBuildRoots" #[]).map System.FilePath.mk
  for br in approvedBuildRoots do
    unless br.isAbsolute do fail s!"invalid approvedBuildRoots entry {br}"
  let checkOpaqueTheoremReadiness ← optField (α := Bool) j "checkOpaqueTheoremReadiness" false
  return {
    sysroot := ⟨← reqField (α := String) j "sysroot"⟩
    artifacts := arts
    foundation
    roots
    modules
    graph
    axioms := ← reqField (α := Array (String × String)) j "axioms"
    allowClassicalChoice
    constructiveModules
    specStrengthChecks
    localAxiomModules
    claimModules
    statementForbidden
    statementUnfold
    sources
    allowProvisionalNative := ← optField (α := Bool) j "allowProvisionalNative" false
    toolchainRoots
    scope := ← optField (α := String) j "scope" "modules"
    nativeHeartbeats
    maxReported := ← optField (α := Nat) j "maxReportedViolations" 12
    approvedBuildRoots
    checkOpaqueTheoremReadiness
  }

/-! ## Module classification and provenance -/

def isToolchainName (roots : Array Name) (m : Name) : Bool :=
  roots.contains m.getRoot

def partNames : Array String := #["olean", "olean.server", "olean.private", "ir.sig", "ir"]

def modRelPath (m : Name) : String :=
  "/".intercalate (m.components.map (·.toString (escape := false)))

def realPathOrEmpty (p : System.FilePath) : IO System.FilePath := do
  try IO.FS.realPath p catch _ => pure (System.FilePath.mk "")

def pathWithinRoot (root target : System.FilePath) : Bool :=
  let rs := root.toString; let ts := target.toString
  let rn := if rs.endsWith "/" && rs.length > 1 then (rs.dropEnd 1).toString else rs
  ts == rn || ts.startsWith (if rn == "/" then "/" else rn ++ "/")

def readU16LE (b : ByteArray) (o : Nat) : Nat := (b.get! o).toNat ||| ((b.get! (o + 1)).toNat <<< 8)
def readU32LE (b : ByteArray) (o : Nat) : Nat := readU16LE b o ||| (readU16LE b (o + 2) <<< 16)
def readU64LE (b : ByteArray) (o : Nat) : Nat := readU32LE b o ||| (readU32LE b (o + 4) <<< 32)

def oleanMagicBytes : ByteArray := "olean".toUTF8
def oleanVerBytes : ByteArray := "4.34.1".toUTF8
def oleanGitBytes : ByteArray := "5045d0056413266e57c625dcd7c365b10e377c52".toUTF8

/-- Pre-`importModules` binary validation of one `.olean*` or `.ir*` layer (`leanprover/lean4#16737`). -/
def validateOleanBytes (b : ByteArray) (parents disjoint : Array (Nat × Nat × Nat)) :
    Except String (Nat × Nat × Nat) := do
  let sz := b.size
  unless sz >= 96 do throw s!"file smaller than 96-byte header ({sz})"
  unless b.extract 0 5 == oleanMagicBytes && b.get! 5 == 2 && b.get! 6 <= 1 &&
      b.extract 7 13 == oleanVerBytes && b.extract 40 80 == oleanGitBytes do
    throw "invalid .olean header magic/version/flags/githash"
  for idx in [13:40] do unless b.get! idx == 0 do throw "non-NUL padding in .olean version field"
  let (baseAddr, rootPtr) := (readU64LE b 80, readU64LE b 88)
  unless baseAddr > 0 && baseAddr % 8 == 0 && baseAddr + sz < 18446744073709551616 do
    throw "invalid, unaligned, or overflowing .olean baseAddr"
  for (pb, ps, _) in parents ++ disjoint do
    unless baseAddr + sz <= pb || pb + ps <= baseAddr do throw "overlapping compacted-region layer"
  if baseAddr + 96 <= rootPtr && rootPtr <= baseAddr + sz - 8 then
    unless rootPtr % 8 == 0 do throw "unaligned .olean rootPtr"
    let off := rootPtr - baseAddr
    let (rc, csSz, mOther, mTag) := (readU32LE b off, readU16LE b (off + 4), (b.get! (off + 6)).toNat, (b.get! (off + 7)).toNat)
    let minSz := 8 + 8 * mOther; let objSz := if csSz > 0 then csSz else minSz
    unless rc == 0 && mTag <= 243 && (csSz == 0 || csSz >= minSz) && off + objSz <= sz do
      throw s!"invalid root object header (rc={rc}, tag={mTag}, cs_sz={csSz}, other={mOther})"
    for k in [0:mOther] do
      let c := readU64LE b (off + 8 + 8 * k)
      if c % 2 == 1 then continue
      let inOwn := c % 8 == 0 && baseAddr + 96 <= c && c <= baseAddr + sz - 8
      let inPar := c % 8 == 0 && parents.any fun (pb, ps, _) => pb + 96 <= c && c <= pb + ps - 8
      unless inOwn || inPar do throw s!"out-of-bounds root child pointer at slot {k}"
      if inOwn then
        let co := c - baseAddr
        unless readU32LE b co == 0 && (b.get! (co + 7)).toNat <= 249 do
          throw s!"invalid root child object header at slot {k}"
  else unless !parents.isEmpty && sz == 96 && parents.any fun (_, _, pr) => pr == rootPtr do
    throw "out-of-region rootPtr is not a valid 96-byte empty delta layer"
  return (baseAddr, sz, rootPtr)

def validateOleanParts (m : Name) (oleanParts : Array System.FilePath)
    (disjoint : Array (Nat × Nat × Nat) := #[]) : AuditM (Array (Nat × Nat × Nat)) := do
  let mut parents : Array (Nat × Nat × Nat) := #[]
  for p in oleanParts do
    let sz? ← (show IO (Option Nat) from do try pure (some (← p.metadata).byteSize.toNat) catch _ => pure none)
    let some sz := sz? | report "oleanBinaryInvalid" m m s!"cannot stat {p}"; return parents
    unless sz >= 96 && sz <= 256 * 1024 * 1024 do
      report "oleanBinaryInvalid" m m s!"{p} byte size {sz} outside [96, 256 MiB]"; return parents
    let some bytes ← (show IO (Option ByteArray) from do try pure (some (← IO.FS.readBinFile p)) catch _ => pure none)
      | report "oleanBinaryInvalid" m m s!"cannot read {p}"; return parents
    match validateOleanBytes bytes parents disjoint with
    | .ok layer => parents := parents.push layer; modify fun s => { s with oleanFilesValidated := s.oleanFilesValidated + 1 }
    | .error e => report "oleanBinaryInvalid" m m s!"{p}: {e}"; return parents
  return parents

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

def entryExistsOnDisk (p : System.FilePath) : IO Bool := do
  try
    let _ ← p.symlinkMetadata
    pure true
  catch _ => pure false

/-- Existing-part list for a toolchain module resolved through the pinned library directory. -/
def sysrootParts (libDir : System.FilePath) (m : Name) : IO (Array System.FilePath × Array System.FilePath) := do
  let base := libDir / modRelPath m
  let mut olean := #[]
  for ext in #["olean", "olean.server", "olean.private"] do
    let p : System.FilePath := ⟨base.toString ++ "." ++ ext⟩
    if ← entryExistsOnDisk p then olean := olean.push p
  let mut ir := #[]
  for ext in #["ir.sig", "ir"] do
    let p : System.FilePath := ⟨base.toString ++ "." ++ ext⟩
    if ← entryExistsOnDisk p then ir := ir.push p
  return (olean, ir)

def checkNoToolchainShadow (m : Name) (artRoot : System.FilePath) : AuditM Unit := do
  for r in #["Init", "Std", "Lean"] do
    for ext in partNames do
      let f := artRoot / (r ++ "." ++ ext)
      if ← entryExistsOnDisk f then report "moduleProvenanceSpoofed" m m s!"artifact root shadows toolchain file {f}"
    let sub := artRoot / r
    if let some md ← (show IO (Option IO.FS.Metadata) from do try pure (some (← sub.symlinkMetadata)) catch _ => pure none) then
      if md.type == .symlink then report "moduleProvenanceSpoofed" m m s!"artifact root has symlinked toolchain dir {sub}"
      else if md.type == .dir then
        let mut pending : List System.FilePath := [sub]; let mut done := false
        for _ in [0:4096] do
          match pending with
          | [] => done := true; break
          | d :: rest =>
            pending := rest
            for e in ← (show IO (Array IO.FS.DirEntry) from do try d.readDir catch _ => pure #[]) do
              if let some emd ← (show IO (Option IO.FS.Metadata) from do try pure (some (← e.path.symlinkMetadata)) catch _ => pure none) then
                if emd.type == .symlink then report "moduleProvenanceSpoofed" m m s!"symlink under shadowed toolchain dir {e.path}"
                else if emd.type == .dir then pending := e.path :: pending
                else if partNames.any (fun ext => e.fileName.endsWith ("." ++ ext)) then
                  report "moduleProvenanceSpoofed" m m s!"artifact root shadows toolchain artifact {e.path}"
        unless done do report "auditFuelExhausted" m m s!"shadow scan under {sub} exhausted its fuel"

/-- Artifact checks that need no loaded environment and therefore run before `importModules`
reads a single byte: shape, canonical names, canonical paths, binary `.olean*` bounds, shadowing &
`approvedBuildRoots` containment, byte-for-byte pinned-sysroot identity for staged foundation
modules, and omitted companion parts. -/
def preloadArtifactChecks (req : Request) (sysMods : Array Name) : AuditM Nat := do
  let libDir := req.sysroot / "lib" / "lean"
  for br in req.approvedBuildRoots do
    let isSym ← (show IO Bool from do try pure ((← br.symlinkMetadata).type == .symlink) catch _ => pure true)
    if isSym || (← realPathOrEmpty br) != br then
      report "moduleProvenanceSpoofed" .anonymous .anonymous s!"approvedBuildRoots entry {br} is non-canonical or symlink"
  let mut checked := 0; let mut seen : NameSet := {}; let mut checkedRoots : Std.HashSet String := {}
  for (m, olean, ir) in req.artifacts do
    if seen.contains m then report "moduleProvenanceSpoofed" m m "duplicate artifact entry"; continue
    seen := seen.insert m
    let isTool := isToolchainName req.toolchainRoots m
    if isTool && !req.foundation.contains m then report "moduleProvenanceSpoofed" m m "toolchain-named module supplied as an untrusted artifact"; continue
    let some first := olean[0]? | report "missingPrivateArtifact" m m "no .olean part"; continue
    let firstStr := first.toString; let relSuffix := "/" ++ modRelPath m ++ ".olean"
    unless firstStr.endsWith relSuffix do report "moduleProvenanceSpoofed" m m s!"artifact {firstStr} does not match the module name"; continue
    let base : String := (firstStr.dropEnd 6).toString
    let oleanExts : Array String := if olean.size == 3 then #["olean", "olean.server", "olean.private"] else if olean.size == 1 then #["olean"] else #[]
    if oleanExts.isEmpty then report "missingPrivateArtifact" m m s!"expected .olean or .olean/.olean.server/.olean.private, got {olean.size} parts"; continue
    unless ir.size == 0 || ir.size == 2 do report "missingPrivateArtifact" m m "incomplete IR companion parts (.ir.sig and .ir go together)"; continue
    let mut shapeOk := true
    for p in olean, ext in oleanExts do unless p.toString == base ++ "." ++ ext do shapeOk := false
    for p in ir, ext in #["ir.sig", "ir"] do unless p.toString == base ++ "." ++ ext do shapeOk := false
    unless shapeOk do report "moduleProvenanceSpoofed" m m "artifact parts are not the canonical companions of one base path"; continue
    let mut allCanon := true
    for p in olean ++ ir do if ← checkCanonicalPart m p then checked := checked + 1 else allCanon := false
    for ext in partNames do
      let p : System.FilePath := ⟨base ++ "." ++ ext⟩
      if !(olean ++ ir).contains p && (← entryExistsOnDisk p) then
        report "missingPrivateArtifact" m m s!"companion part {p} exists but was omitted from the artifacts"
    if allCanon then
      -- `.ir.sig`/`.ir` are compacted regions in the same format and must stay disjoint from `.olean*`.
      let olLayers ← validateOleanParts m olean; let _ ← validateOleanParts m ir olLayers
      if !isTool then
        let rootStr := (firstStr.dropEnd relSuffix.length).toString
        let artRoot : System.FilePath := ⟨if rootStr.isEmpty then "/" else rootStr⟩
        unless (← realPathOrEmpty artRoot) == artRoot do
          report "moduleProvenanceSpoofed" m m s!"artifact root {artRoot} is not canonical"
        unless checkedRoots.contains artRoot.toString do
          checkedRoots := checkedRoots.insert artRoot.toString; checkNoToolchainShadow m artRoot
        if !req.approvedBuildRoots.isEmpty then
          for p in olean ++ ir do
            unless req.approvedBuildRoots.any (pathWithinRoot · p) do
              report "moduleProvenanceSpoofed" m m s!"artifact part {p} escapes approvedBuildRoots"
    if isTool && allCanon then
      let (sysOlean, sysIR) ← sysrootParts libDir m
      if olean.size != sysOlean.size || ir.size != sysIR.size then
        report "moduleProvenanceSpoofed" m m "foundation artifact part set differs from pinned sysroot"
      else
        for (stagedP, sysP) in (olean.zip sysOlean) ++ (ir.zip sysIR) do
          if ← checkCanonicalPart m sysP then
            let sameBytes ← (show IO Bool from do try pure ((← IO.FS.readBinFile stagedP) == (← IO.FS.readBinFile sysP)) catch _ => pure false)
            unless sameBytes do report "moduleProvenanceSpoofed" m m s!"foundation artifact {stagedP} bytes differ from pinned sysroot {sysP}"
  for sm in sysMods do
    let (sysOlean, sysIR) ← sysrootParts libDir sm
    if sysOlean.isEmpty then report "missingPrivateArtifact" sm sm "sysroot module has no .olean parts"
    else
      let mut okAll := true
      for sp in sysOlean ++ sysIR do unless (← checkCanonicalPart sm sp) && pathWithinRoot libDir sp do okAll := false
      if okAll then
        let olLayers ← validateOleanParts sm sysOlean; let _ ← validateOleanParts sm sysIR olLayers
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
  /-- `false` when a declaration of an audited module can reach a kernel-native evaluator: the
  audit then performs no kernel or `MetaM` evaluation at all (see `reachesNativeEvaluator`). -/
  dynamicOk : Bool := true

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
    let rootOlean := libDir / (rs ++ ".olean")
    if ← entryExistsOnDisk rootOlean then
      let md ← rootOlean.symlinkMetadata
      if md.type == .symlink then
        fail s!"[moduleProvenanceSpoofed] symlink inside toolchain library: {rootOlean}"
      if md.type == .file then
        result := result.push r
    let rootDir := libDir / rs
    if ← entryExistsOnDisk rootDir then
      let md ← rootDir.symlinkMetadata
      if md.type == .symlink then
        fail s!"[moduleProvenanceSpoofed] symlink inside toolchain library: {rootDir}"
      if md.type == .dir then
        pending := (rootDir, r) :: pending
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
def toolchainNameInventory (req : Request) (mods : Array Name) : IO (Std.HashSet Name) := do
  let libDir := req.sysroot / "lib" / "lean"
  searchPathRef.set [libDir]
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

/-! ## Kernel-native evaluators

`Lean.reduceBool c` and `Lean.reduceNat c` are the two terms Lean's kernel (`reduce_native`) and
`Meta.whnf` (`reduceNative?`) reduce by *running the compiled code* of `c`. The IR interpreter finds
that code in the loaded artifacts even under `loadExts := false`, so type checking, replaying or
normalizing any term that can reach one of them executes code of the audited modules inside the
auditor (measured: an instance type `Bool.rec _ _ (Lean.reduceBool flag)` in an audited module wrote
a file from within `OleanEnvAuditor` during the instance scan). An auditor that runs the code it
judges can be made to write its own verdict, so no kernel or `MetaM` evaluation is performed on
anything whose dependency closure reaches a native evaluator. -/

def kernelNativeEvaluators : List Name := [``Lean.reduceBool, ``Lean.reduceNat]

/-- Whether the dependency closure of `roots` (types, values, theorem and opaque bodies, recursor
rules) reaches a kernel-native evaluator. `clean` memoizes constants whose whole closure is known
to be free of them, so repeated queries over one environment stay linear in its size. Fails closed
(`true`) when the fuel runs out. -/
def reachesNativeEvaluator (env : Environment) (roots : Array Name) (clean : NameSet) (fuel : Nat) :
    Bool × NameSet := Id.run do
  let mut visited : NameSet := {}
  let mut pending : List Name := []
  for r in roots do
    unless clean.contains r || visited.contains r do
      visited := visited.insert r
      pending := r :: pending
  for _ in [0:fuel] do
    match pending with
    | [] => return (false, clean ++ visited)
    | n :: rest =>
      pending := rest
      if kernelNativeEvaluators.contains n then return (true, clean)
      let some ci := env.find? n | continue
      for d in declEdges ci do
        unless clean.contains d || visited.contains d do
          visited := visited.insert d
          pending := d :: pending
  if pending.isEmpty then return (false, clean ++ visited)
  return (true, clean)

def envConstantCount (env : Environment) : Nat :=
  env.header.moduleData.foldl (fun a d => a + d.constants.size) 0 + env.constants.map₂.toList.length

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

/-- Ask the kernel to type check a partial companion body `value : type` against `env`. -/
def kernelAcceptsPartial (env : Environment) (lparams : List Name) (type value : Expr) (budget : Nat) :
    IO Bool := do
  unless isClosedExpr type && isClosedExpr value do return false
  let name := freshName env `_olean_auditor_companion_check
  let decl := Declaration.mutualDefnDecl [{
    name, levelParams := lparams, type, value, hints := .opaque, safety := .partial
  }]
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

/-- Strip line (`--`) and nested block (`/- ... -/`) comments from Lean source text, preserving
everything else. Used as a fail-closed fallback when a file declares custom `interpolatedStr` syntax. -/
def stripComments (text : String) : String := Id.run do
  let cs := text.toList.toArray
  let mut out : Array Char := #[]
  let mut i := 0
  let mut depth := 0
  let mut inLine := false
  for _ in [0:cs.size + 1] do
    if h : i < cs.size then
      let c := cs[i]
      let d? := cs[i + 1]?
      if inLine then
        if c == '\n' then inLine := false; out := out.push '\n'
        i := i + 1
      else if depth > 0 then
        if c == '/' && d? == some '-' then depth := depth + 1; i := i + 2
        else if c == '-' && d? == some '/' then depth := depth - 1; i := i + 2
        else i := i + 1
      else
        if c == '-' && d? == some '-' then inLine := true; i := i + 2
        else if c == '/' && d? == some '-' then depth := 1; i := i + 2
        else out := out.push c; i := i + 1
    else break
  return String.ofList out.toList

/-- Identifier tokens of Lean source text outside comments and plain/raw string literals, while
handling single-quoted `Char` literals and descending into `{...}` expressions inside Lean's
interpolated strings (`s!"..."`, `s! "..."`, `m!"..."`, `f!"..."`, `println! "..."`,
`Macro.trace[...] "..."`, and any `<ident>!"..."` macro). Returns `(tokens, balanced)` where
`balanced` is `false` if scanning reached EOF inside an unclosed string, raw string, comment,
guillemet, or interpolation state (fail-closed guard against lexer desynchronization). -/
def scanIdents (text : String) : Array String × Bool := Id.run do
  let cs := text.toList.toArray
  let mut acc : Array String := #[]
  let mut cur : List Char := []
  let mut lastTok : String := ""
  let mut inMacroTrace := false
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
          lastTok := "\""
          inMacroTrace := false
          i := i + 1 + nh
        else
          i := i + 1
      else if inStr then
        if c == '\\' then i := i + 2
        else if c == '"' then
          inStr := false
          inInterpStr := false
          lastTok := "\""
          inMacroTrace := false
          i := i + 1
        else if inInterpStr && c == '{' then
          inStr := false
          inInterpStr := false
          lastTok := "{"
          inMacroTrace := false
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
            lastTok := "'"
            inMacroTrace := false
            i := nextI
            continue
        let isCommentStart := (c == '-' && d? == some '-') || (c == '/' && d? == some '-')
        let isStart := isCommentStart || c == '"'
        if isStart || !(isIdentChar c || c == '«') then
          if !cur.isEmpty then
            let tok := String.ofList cur.reverse
            acc := acc.push tok
            lastTok := tok
            if tok == "Macro.trace" then inMacroTrace := true
            else if !inMacroTrace then inMacroTrace := false
            cur := []
        if c == '-' && d? == some '-' then inLine := true; i := i + 2
        else if c == '/' && d? == some '-' then depth := 1; i := i + 2
        else if c == '"' then
          let isInterpOpen :=
            (lastTok.endsWith "!" && lastTok.length > 1) ||
            (lastTok == "]" && inMacroTrace)
          inStr := true
          inInterpStr := isInterpOpen
          inMacroTrace := false
          i := i + 1
        else if c == '«' then inGuil := true; i := i + 1
        else if c == '{' && !interpStack.isEmpty then
          match interpStack with
          | d :: rest => interpStack := (d + 1) :: rest
          | [] => pure ()
          lastTok := "{"
          inMacroTrace := false
          i := i + 1
        else if c == '}' && !interpStack.isEmpty then
          match interpStack with
          | 0 :: rest =>
            interpStack := rest
            inStr := true
            inInterpStr := true
            lastTok := "}"
            inMacroTrace := false
          | (d + 1) :: rest =>
            interpStack := d :: rest
            lastTok := "}"
            inMacroTrace := false
          | [] => pure ()
          i := i + 1
        else
          if isIdentChar c then
            cur := c :: cur
          else if !c.isWhitespace then
            let cs1 := String.singleton c
            if c == '[' then
              inMacroTrace := (lastTok == "Macro.trace")
            else if c != ']' then
              inMacroTrace := false
            lastTok := cs1
          i := i + 1
    else break
  if !cur.isEmpty then acc := acc.push (String.ofList cur.reverse)
  let balanced := !inStr && rawHashes.isNone && depth == 0 && !inGuil && interpStack.isEmpty
  return (acc, balanced)

def forbiddenSourceIdentifier (tok : String) : Bool :=
  (tok.splitOn "_unsafe_rec").length > 1

/-! ## The audit -/

def toolchainAllowedAxiom (L : Loaded) (n m : Name)
    (allowClassical : Bool := L.req.allowClassicalChoice) : Bool :=
  L.toolchainProv.contains m && L.req.axioms.contains (n.toString, m.toString) &&
    (allowClassical || n == ``propext || n == ``Quot.sound)

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
  unless L.dynamicOk do
    modify fun (s : AuditState) => { s with provisionalNative := s.provisionalNative.insert n }
    return
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

def isFoundationalAxiomName (n : Name) : Bool :=
  n == ``propext || n == ``Quot.sound || n == ``Classical.choice

/-- Axiom policy for one reached axiom. `localOk` admits file-local test axioms. -/
def checkAxiom (L : Loaded) (ci : ConstantInfo) (m : Name) (localOk : Name → Bool)
    (allowClassical : Bool := L.req.allowClassicalChoice) : AuditM Unit := do
  let n := ci.name
  if n == ``sorryAx then
    report "sorryAxiomReached" n m "incomplete proof (sorryAx)"
    return
  if toolchainAllowedAxiom L n m allowClassical then
    modify fun (s : AuditState) => { s with reachedAxioms := s.reachedAxioms.insert n }
    return
  if isFoundationalAxiomName n && !L.toolchainProv.contains m then
    report "unapprovedAxiom" n m "non-toolchain re-declaration of foundational axiom"
    return
  if n == ``Classical.choice && !allowClassical then
    report "unapprovedAxiom" n m "Classical.choice is forbidden under constructive policy"
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
  if n.getRoot == `Assumptions && m.getRoot != `Assumptions then
    report "unapprovedAxiom" n m "foreign Assumptions.* axiom declared outside Assumptions.* module"
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

/-- Memoized DAG collector of all `Nat`/`String` literals occurring in `e` (total, fuel-bounded;
returns `none` on fuel exhaustion so callers fail closed). -/
def exprLiterals (e : Expr) (acc : Std.HashSet Literal) (seen0 : Std.HashSet Expr)
    (fuel : Nat := 200000) : Option (Std.HashSet Literal × Std.HashSet Expr) := Id.run do
  let mut lits := acc
  let mut seen := seen0
  let mut stack : List Expr := [e]
  let mut done := false
  for _ in [0:fuel] do
    match stack with
    | [] => done := true; break
    | x :: rest =>
      stack := rest
      if seen.contains x then continue
      seen := seen.insert x
      match x with
      | .lit l => lits := lits.insert l
      | .app f a => stack := f :: a :: stack
      | .lam _ t b _ | .forallE _ t b _ => stack := t :: b :: stack
      | .letE _ t v b _ => stack := t :: v :: b :: stack
      | .mdata _ b | .proj _ _ b => stack := b :: stack
      | _ => pure ()
  if done then return some (lits, seen) else return none

/-- Strip leading lambdas from an expression (total, fuel-bounded). -/
def stripLeadingLams (e : Expr) (fuel : Nat := 256) : Expr × Nat :=
  let rec go (cur : Expr) (n : Nat) : Nat → Expr × Nat
    | 0 => (cur, n)
    | k + 1 =>
      match cur with
      | .lam _ _ b _ => go b (n + 1) k
      | _ => (cur, n)
  go e 0 fuel

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
  let some body := ci.value? (allowOpaque := true) | throw "companion has no body"
  unless body.getUsedConstants.any (fun c =>
      (match c with | .str _ "_unsafe_rec" => true | _ => false) &&
      origin? L.env c == recMod) do
    throw "companion body is not recursive through a same-module _unsafe_rec"
  -- Every non-companion constant and literal in the companion's body must already occur in the
  -- parent's same-module transitive kernel closure (preventing forged companions on a parent
  -- that merely invokes a recursion combinator with a different RHS).
  let mut visited : NameSet := NameSet.empty.insert parent
  let mut pending : List Name := [parent]
  let mut pConsts : NameSet := NameSet.empty.insert parent
  let mut pLits : Std.HashSet Literal := {}
  let mut litSeen : Std.HashSet Expr := {}
  let mut bfsDone := false
  for _ in [0:16384] do
    match pending with
    | [] => bfsDone := true; break
    | cur :: rest =>
      pending := rest
      if let some xci := L.env.find? cur then
        if let some xv := xci.value? (allowOpaque := true) then
          match exprLiterals xv pLits litSeen with
          | some (l', s') => pLits := l'; litSeen := s'
          | none => throw "companion parent literal scan exhausted its fuel"
          for c in xv.getUsedConstants do
            pConsts := pConsts.insert c
            if !visited.contains c && origin? L.env c == recMod then
              visited := visited.insert c
              pending := c :: pending
  unless bfsDone do throw "companion parent closure scan exhausted its fuel"
  for c in body.getUsedConstants do
    unless pConsts.contains c || (match c with | .str _ "_unsafe_rec" => true | _ => false) do
      throw s!"companion introduces constant {c} absent from parent closure"
  let some (cLits, _) := exprLiterals body {} {}
    | throw "companion body literal scan exhausted its fuel"
  for l in cLits do
    unless pLits.contains l do
      throw s!"companion introduces literal {reprStr l} absent from parent closure"

/-- A lazily realized reserved theorem (`.eq_def`, `.eq_1`, ...) may be stored by several audited
modules with different proofs of the same statement; the environment keeps one of them. Another
copy is accepted only if it is a theorem with the same statement and universe parameters whose own
proof the kernel accepts; its proof's dependencies are then audited as additional roots. -/
def reservedTheoremCopyOk (env : Environment) (n : Name) (stored ci : ConstantInfo) : IO Bool := do
  unless isReservedName env n do return false
  let .thmInfo sv := stored | return false
  let .thmInfo cv := ci | return false
  unless sv.type == cv.type && sv.levelParams == cv.levelParams && declIsClosed ci do return false
  -- Refuse circular self-proofs (`n` is already in `env`).
  if (exprEdges cv.value {}).contains n then return false
  -- Defense-in-depth (`A1-1`): never hand a duplicate reserved theorem copy reaching a
  -- kernel-native evaluator (`Lean.reduceBool` / `Lean.reduceNat`) to `kernelAccepts`.
  let (nativeReach, _) := reachesNativeEvaluator env (declEdges ci).toArray {} (envConstantCount env + 64)
  if nativeReach then return false
  kernelAccepts env cv.levelParams cv.type cv.value 100000

def shareCommonRoots : NameSet :=
  [`ShareCommon, `MonadShareCommon, `withShareCommon, `shareCommonM,
   `ShareCommonT, `ShareCommonM, `StateFactoryBuilder, `StateFactory].foldl (·.insert ·) {}

def hasShareCommonExternSym (s : String) : Bool :=
  (s.splitOn "lean_sharecommon").length > 1 || (s.splitOn "lean_state_sharecommon").length > 1

def externDataMentionsShareCommon (d : ExternAttrData) : Bool :=
  d.entries.any fun | .standard _ fn | .inline _ fn => hasShareCommonExternSym fn | _ => false

def isShareCommonNamePure (n : Name) : Bool :=
  n == `Init.ShareCommon || (`Init.ShareCommon).isPrefixOf n || shareCommonRoots.contains n.getRoot ||
  n.components.any fun | .str .anonymous s => shareCommonRoots.contains (Name.mkSimple s) || hasShareCommonExternSym s | _ => false

def isShareCommonName (env : Environment) (n : Name) : Bool :=
  origin? env n == some `Init.ShareCommon || isShareCommonNamePure n

def namePartsAcc : Name → List (String ⊕ Nat) → List (String ⊕ Nat)
  | .anonymous, acc => acc | .str p s, acc => namePartsAcc p (.inl s :: acc) | .num p k, acc => namePartsAcc p (.inr k :: acc)

def partsToName (ps : List (String ⊕ Nat)) : Name :=
  ps.foldl (fun acc x => match x with | .inl s => acc.str s | .inr k => acc.num k) .anonymous

def hasPrivateMention (ps : List (String ⊕ Nat)) : Bool :=
  ps.any fun | .inl s => s == "_private" || s.startsWith "_private." || (s.splitOn "._private").length > 1 | .inr _ => false

def parseStrictPrivate (ps : List (String ⊕ Nat)) : Option (Name × Name) := do
  let .inl "_private" :: rest := ps | none
  let rec splitMod (ms : List String) : List (String ⊕ Nat) → Option (List String × List (String ⊕ Nat))
    | .inl s :: xs => splitMod (s :: ms) xs | .inr 0 :: xs => some (ms.reverse, xs) | _ => none
  let (ms, tail) ← splitMod [] rest
  guard (!ms.isEmpty && !tail.isEmpty && !hasPrivateMention tail && tail.all Sum.isLeft)
  let modName := ms.foldl Name.str .anonymous
  guard (validModuleName modName)
  return (modName, partsToName tail)

def parseDecSuffix? (s pfx : String) : Option Nat :=
  if s.startsWith pfx then
    let t := (s.drop pfx.length).toString
    if !t.isEmpty && t.toList.all Char.isDigit then t.toNat? else none
  else none

def isIRAuxSuffix (s : String) : Bool :=
  s == "_redArg" || s == "_cstage1" || s == "_cstage2" || (parseDecSuffix? s "_boxed_const_").isSome

def stripSpecTail? (seg : List (String ⊕ Nat)) : Option (List (String ⊕ Nat) × Nat) := Id.run do
  let mut rev := seg.reverse; let mut specs := 0
  for _ in [0:6] do
    match rev with
    | .inl s :: r =>
      if isIRAuxSuffix s || s == "_boxed" then rev := r
      else if (parseDecSuffix? s "spec_").isSome then specs := specs + 1; rev := r
      else break
    | _ => break
  if rev.isEmpty then none else some (rev.reverse, specs)

def conclIsEqOf (base : Name) (ty : Expr) : Bool := Id.run do
  let mut cur := ty
  for _ in [0:128] do match cur with | .forallE _ _ b _ => cur := b | _ => break
  cur.isAppOfArity ``Eq 3 && cur.getAppArgs[1]!.getAppFn.isConstOf base

def reservedAlwaysRoots : NameSet := [`Init, `Std, `Lean, `ShareCommon, `Classical, `Quot, `sorryAx].foldl (·.insert ·) {}
def reservedDomainRoots : NameSet := [`Trusted, `Assumptions, `Verify, `CrateVerify].foldl (·.insert ·) {}

def privateUserForbidden (m user : Name) (toolchainNames : Std.HashSet Name) : Bool :=
  let r := user.getRoot
  reservedAlwaysRoots.contains r || (reservedDomainRoots.contains r && m.getRoot != r) ||
  compilerReservedNames.contains user || toolchainNames.contains user || isShareCommonNamePure user

def matcherInfo? (env : Environment) (n : Name) : Option Meta.MatcherInfo :=
  match env.getModuleIdxFor? n with
  | some i => (Meta.Match.Extension.extension.getModuleEntries env i).findSome? fun e => if e.name == n then some e.info else none
  | none => Meta.getMatcherInfoCore? env n

def splitterTypeMatches (mi : Meta.MatcherInfo) (mTy sTy : Expr) : Bool := Id.run do
  let mut (mt, st) := (mTy, sTy)
  for i in [0:mi.numParams + 1 + mi.numDiscrs + mi.altInfos.size] do
    match mt, st with
    | .forallE _ md mb _, .forallE _ sd sb _ =>
      if i < mi.numParams + 1 + mi.numDiscrs && md != sd then return false
      mt := mb; st := sb
    | _, _ => return false
  return mt == st

def isVerifiedTrustedMatchRealization (env : Environment) (m n user : Name) (ci? : Option ConstantInfo) (isIRHelper : Bool) : Bool := Id.run do
  if user.getRoot != `Trusted then return false
  let trustedM? : Name → Option (Meta.MatcherInfo × ConstantInfo)
    | mt@(.str _ ms) => if (parseDecSuffix? ms "match_").any (· >= 1) && (origin? env mt).any (·.getRoot == `Trusted) then
        match matcherInfo? env mt, env.find? mt with | some mi, some mci@(.defnInfo _) => some (mi, mci) | _, _ => none else none
    | _ => none
  match ci?, user, n with
  | some (.axiomInfo _), _, _ | some (.opaqueInfo _), _, _ => return false
  | some ci, .str mt "splitter", _ =>
    return (trustedM? mt).any fun (mi, mci) => (ci matches .defnInfo _) && ci.levelParams == mci.levelParams && splitterTypeMatches mi mci.type ci.type
  | some ci, .str mt last, .str privBase _ =>
    if let some k := parseDecSuffix? last "eq_" then
      return (k >= 1 && (ci matches .thmInfo _) && (trustedM? mt).isSome && (k == 1 || (env.find? (privBase.str s!"eq_{k - 1}")).isSome) && conclIsEqOf mt ci.type)
    else if (parseDecSuffix? last "_sparseCasesOn_").isSome then
      match mt with
      | .str mBase "splitter" => return ((ci matches .defnInfo _) && isSparseCasesOn env n && (trustedM? mBase).isSome && origin? env privBase == some m && (env.find? privBase matches some (.defnInfo _)))
      | _ => return false
    else return false
  | none, _, _ =>
    if !isIRHelper || (IR.findEnvDecl env n).isNone || origin? env n != some m then return false
    let mut (curU, curN, stripped) := (user, n, false)
    for _ in [0:4] do
      match curU, curN with
      | .str pu su, .str pn sn => if su == sn && (isIRAuxSuffix su || su == "_boxed") then curU := pu; curN := pn; stripped := true else break
      | _, _ => break
    match curU with
    | .str mt "splitter" => return (stripped && (trustedM? mt).isSome && origin? env curN == some m && (env.find? curN matches some (.defnInfo _)))
    | _ => return false
  | _, _, _ => return false

def irAuxBaseOwned (env : Environment) (n pMod : Name) (allowSelf : Bool) : Bool := Id.run do
  let owned (x : Name) := origin? env x == some pMod && ((env.find? x).isSome || (IR.findEnvDecl env x).isSome)
  if allowSelf && owned n then return true
  let mut cur := n
  for _ in [0:4] do match cur with | .str p s => if isIRAuxSuffix s then cur := p; if owned cur then return true else break | _ => break
  return false

/-- Structural `_private.<mod>.0.<user>` de-mangling, provenance binding, reserved-root guard, and
closed-set foreign realized-auxiliary check. -/
def checkPrivateName (L : Loaded) (toolchainNames : Std.HashSet Name) (m n : Name)
    (ci? : Option ConstantInfo) (isIRHelper : Bool := false) : AuditM Unit := do
  let parts := namePartsAcc n []
  -- Toolchain-owned names (e.g. private constants in specialization keys) are pinned, not audited.
  unless hasPrivateMention parts && !L.toolchainProv.contains m do return
  modify fun s => { s with privateNamesAudited := s.privateNamesAudited + 1 }
  let env := L.env
  if isIRHelper && parts.contains (.inl "_at_") && (IR.findEnvDecl env n).isSome && origin? env n == some m then
    let (cur, acc) := parts.foldl (init := ([], [])) fun (c, a) x => if x == .inl "_at_" then ([], c.reverse :: a) else (x :: c, a)
    match (cur.reverse :: acc).reverse with
    | head :: tails =>
      if !tails.isEmpty && !head.isEmpty then
        let mut ok := true
        if hasPrivateMention head then
          match parseStrictPrivate head with
          | some (hMod, hUser) =>
            let hName := partsToName head
            let hOk := L.modIdx.contains hMod && !isShareCommonName env hName &&
              (L.toolchainProv.contains hMod || !privateUserForbidden hMod hUser toolchainNames) &&
              irAuxBaseOwned env hName hMod true
            if !hOk then ok := false
          | none => ok := false
        let lastIdx := tails.length - 1; let mut totalSpecs := 0
        for h : idx in [0:tails.length] do
          match stripSpecTail? tails[idx] with
          | none => ok := false
          | some (site, sp) =>
            totalSpecs := totalSpecs + sp
            if idx == lastIdx && sp == 0 then ok := false
            if hasPrivateMention site then
              match parseStrictPrivate site with
              | some (sMod, sUser) => if !L.modIdx.contains sMod || privateUserForbidden sMod sUser toolchainNames || (idx == lastIdx && sMod != m) then ok := false
              | none => ok := false
        if ok && totalSpecs == tails.length then return
    | _ => pure ()
    report "privateNamespaceSpoofed" n m "malformed or spoofed _private _at_ specialization name"; return
  let some (pMod, pUser) := parseStrictPrivate parts | report "privateNamespaceSpoofed" n m "malformed _private name shape"; return
  if pMod == m && isVerifiedTrustedMatchRealization env m n pUser ci? isIRHelper then return
  if privateUserForbidden pMod pUser toolchainNames then report "privateNamespaceSpoofed" n m s!"_private user suffix {pUser} spoofs reserved/toolchain namespace"; return
  if pMod == m then return
  unless L.modIdx.contains pMod do report "privateNamespaceSpoofed" n m s!"_private module {pMod} is not a loaded module"; return
  match ci? with
  | some (.axiomInfo _) | some (.opaqueInfo _) => report "privateNamespaceSpoofed" n m s!"foreign _private axiom/opaque claiming module {pMod}"
  | some ci =>
    let ok := match n with
      | .str base last =>
        origin? env base == some pMod &&
        if let some k := parseDecSuffix? last "match_" then k >= 1 && (ci matches .defnInfo _) && (matcherInfo? env n).isSome && (env.find? base).isSome
        else if let some k := parseDecSuffix? last "eq_" then
          k >= 1 && (ci matches .thmInfo _) && (env.find? base matches some (.defnInfo _)) &&
          (k == 1 || (env.find? (base.str s!"eq_{k - 1}")).isSome) && conclIsEqOf base ci.type
        else if last == "eq_def" then (ci matches .thmInfo _) && (env.find? base matches some (.defnInfo _)) && conclIsEqOf base ci.type
        else if let some k := parseDecSuffix? last "proof_" then
          k >= 1 && (ci matches .thmInfo _) && (k == 1 || (env.find? (base.str s!"proof_{k - 1}")).isSome) &&
          (env.find? base).any fun bci => (declEdges bci).contains n
        else if (parseDecSuffix? last "_sparseCasesOn_").isSome then (ci matches .defnInfo _) && isSparseCasesOn env n && (env.find? base).isSome
        else false
      | _ => false
    unless ok do report "privateNamespaceSpoofed" n m s!"foreign _private declaration claiming module {pMod} outside verified realized-aux set"
  | none =>
    unless isIRHelper && (IR.findEnvDecl env n).isSome && origin? env n == some m && irAuxBaseOwned env n pMod false do
      report "privateNamespaceSpoofed" n m s!"foreign _private IR/extension symbol claiming module {pMod}"

def genuineCtorIdxMacroInline (env : Environment) (toolchainProv : Std.HashSet Name) (m n : Name) : Bool := Id.run do
  let .str indName "ctorIdx" := n | return false
  unless origin? env n == some m && origin? env indName == some m && isToolchainConst env toolchainProv ``Nat do return false
  let some (.inductInfo iv) := env.find? indName | return false
  let some (.defnInfo dv) := env.find? n | return false
  unless !iv.isUnsafe && dv.safety == .safe && dv.levelParams == iv.levelParams do return false
  let nb := iv.numParams + iv.numIndices + 1
  let mut ty := dv.type; let mut lastDom : Expr := default
  for _ in [0:nb] do match ty with | .forallE _ d b _ => lastDom := d; ty := b | _ => return false
  unless ty == mkConst ``Nat && lastDom.getAppFn.isConstOf indName do return false
  let (valBody, nLams) := stripLeadingLams dv.value (nb + 1)
  unless nLams == nb && (dv.value.find? fun | .letE .. => true | _ => false).isNone do return false
  -- `mkCtorIdx` sets `@[macro_inline]` only for single-constructor types, whose body is raw `0`.
  unless iv.numCtors == 1 && valBody == .lit (.natVal 0) do return false
  let allowed := (exprEdges iv.type {}).insert indName |>.insert ``Nat
  return (exprEdges dv.value {}).all allowed.contains

def overrideKinds (env : Environment) (toolchainProv : Std.HashSet Name) (n : Name) : Array String := Id.run do
  let mut kinds := #[]
  if (Compiler.getImplementedBy? env n).isSome then kinds := kinds.push "implemented_by"
  if isExtern env n || isExternC env n then kinds := kinds.push "extern"
  if (getExportNameFor? env n).isSome then kinds := kinds.push "export"
  if (getRegularInitFnNameFor? env n).isSome || isIOUnitRegularInitFn env n then kinds := kinds.push "init"
  if (getBuiltinInitFnNameFor? env n).isSome || isIOUnitBuiltinInitFn env n then kinds := kinds.push "builtin_init"
  if Compiler.LCNF.taggedReturnAttr.hasTag env n then kinds := kinds.push "tagged_return"
  if IR.UnboxResult.unboxAttr.hasTag env n then kinds := kinds.push "unbox"
  if neverExtractAttr.hasTag env n then kinds := kinds.push "never_extract"
  if Compiler.hasMacroInlineAttribute env n && !genuineCtorIdxMacroInline env toolchainProv ((origin? env n).getD .anonymous) n then
    kinds := kinds.push "macro_inline"
  return kinds

/-- Validate the compiler-intrinsic tags of one non-toolchain declaration. -/
def checkIntrinsicTags (L : Loaded) (n : Name) (m : Name) (budget : Nat) : AuditM Unit := do
  -- Tag validation type checks terms of the audited module; never on a native-reaching environment.
  unless L.dynamicOk do return
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

inductive SimpleRet where | param (idx : Nat) | natLit (v : Nat) | strLit (v : String) | ctor (c : Name) | other deriving BEq

def classifyLCNF (env : Environment) (d : Compiler.LCNF.Decl .pure) : SimpleRet :=
  match d.value with
  | .extern .. => .other
  | .code code =>
    let pIdx (fv : FVarId) := d.params.findIdx? (·.fvarId == fv)
    match code with
    | .return fv => (pIdx fv).map .param |>.getD .other
    | .let ld (.return fv) =>
      if ld.fvarId != fv then .other else match ld.value with
        | .lit (.nat v) => .natLit v | .lit (.str v) => .strLit v
        | .fvar fv2 #[] => (pIdx fv2).map .param |>.getD .other
        | .const c _ _ => if env.find? c matches some (.ctorInfo _) then .ctor c else .other
        | _ => .other
    | _ => .other

def classifyIR : IR.Decl → SimpleRet
  | .extern .. => .other
  | .fdecl _ xs _ body _ =>
    let rec stripRC : Nat → IR.FnBody → IR.FnBody
      | 0, b => b | f + 1, .inc _ _ _ _ r | f + 1, .dec _ _ _ _ r => stripRC f r | _, b => b
    match stripRC 16 body with
    | .ret (.var v) => (xs.findIdx? (·.x == v)).map .param |>.getD .other
    | .vdecl x _ (.lit (.num v)) r => match stripRC 16 r with | .ret (.var y) => if x == y then .natLit v else .other | _ => .other
    | .vdecl x _ (.lit (.str v)) r => match stripRC 16 r with | .ret (.var y) => if x == y then .strLit v else .other | _ => .other
    | _ => .other

def classifyKernel (env : Environment) (ci : ConstantInfo) : SimpleRet :=
  match ci.value? (allowOpaque := true) with
  | none => .other
  | some v =>
    let (body, nLams) := stripLeadingLams v 256
    match body with
    | .bvar i => if i < nLams then .param (nLams - 1 - i) else .other
    | .lit (.natVal k) => .natLit k | .lit (.strVal s) => .strLit s
    | .app (.app (.app (.const ``OfNat.ofNat _) ty) (.lit (.natVal k))) _ => if ty == mkConst ``Nat then .natLit k else .other
    | _ => match body.getAppFn with | .const c _ => if env.find? c matches some (.ctorInfo _) then .ctor c else .other | _ => .other

def simpleRetCompat : SimpleRet → SimpleRet → Bool
  | .other, _ | _, .other | .ctor _, _ | _, .ctor _ => true
  | .natLit x, .natLit y => x == y | .strLit x, .strLit y => x == y | .param _, .param _ => true | _, _ => false

/-- Module-entry scans: every attribute, tag, compiler-pipeline and postponed-compilation entry
stored by a module (both `.olean` and `.ir` tables), judged by the module that stores it. -/
def scanModuleEntries (L : Loaded) (toolchainNames : Std.HashSet Name) :
    AuditM (Std.HashSet (Name × Name × Name) × NameSet) := do
  let env := L.env
  let mut toolchainCSimp : Std.HashSet (Name × Name × Name) := {}
  let mut toolchainImplByTargets : NameSet := {}
  let checkExtTarget (m n : Name) : AuditM Unit := do
    checkPrivateName L toolchainNames m n (env.find? n) ((env.find? n).isNone && (IR.findEnvDecl env n).isSome)
    if isShareCommonName env n then report "shareCommonForbidden" n m "Init.ShareCommon referenced in compiler extension"
  for h : i in [0:env.header.modules.size] do
    let m := env.header.modules[i].module
    let isTool := L.toolchainProv.contains m
    unless isTool || L.nonToolchain.contains m do continue
    for e in Compiler.CSimp.ext.ext.getModuleEntries env i ++ Compiler.CSimp.ext.ext.getModuleIREntries env i do
      let ent := match e with | .global a => a | .scoped _ a => a
      if isTool then toolchainCSimp := toolchainCSimp.insert (ent.fromDeclName, ent.toDeclName, ent.thmName)
      else
        checkExtTarget m ent.fromDeclName; checkExtTarget m ent.toDeclName
        report "compilerOverrideAttribute" ent.fromDeclName m s!"csimp: {ent.fromDeclName} ↦ {ent.toDeclName} via {ent.thmName}"
    for installer in Compiler.LCNF.passManagerExt.getModuleEntries env i ++ Compiler.LCNF.passManagerExt.getModuleIREntries env i do
      if !isTool then checkExtTarget m installer
      report "compilerOverrideAttribute" installer m "cpass: compiler pass installer registered"
    for fe in Compiler.LCNF.Simp.ConstantFold.folderExt.getModuleEntries env i ++ Compiler.LCNF.Simp.ConstantFold.folderExt.getModuleIREntries env i do
      if !isTool then checkExtTarget m fe.declName; checkExtTarget m fe.folderDeclName
      report "compilerOverrideAttribute" fe.declName m s!"constant_fold: folder {fe.folderDeclName}"
    if isTool then
      for (_, tgt) in Compiler.implementedByAttr.ext.getModuleEntries env i ++ Compiler.implementedByAttr.ext.getModuleIREntries env i do
        toolchainImplByTargets := toolchainImplByTargets.insert tgt
      continue
    for (n, tgt) in Compiler.implementedByAttr.ext.getModuleEntries env i ++ Compiler.implementedByAttr.ext.getModuleIREntries env i do
      checkExtTarget m n; checkExtTarget m tgt; report "compilerOverrideAttribute" n m "implemented_by"
    for (n, ed) in externAttr.ext.getModuleEntries env i ++ externAttr.ext.getModuleIREntries env i do
      checkExtTarget m n; report "compilerOverrideAttribute" n m "extern"
      if externDataMentionsShareCommon ed then report "shareCommonForbidden" n m "@[extern] targets lean_sharecommon_*"
    for (lbl, ext) in #[("export", exportAttr.ext), ("init", regularInitAttr.ext), ("builtin_init", builtinInitAttr.ext)] do
      for (n, _) in ext.getModuleEntries env i ++ ext.getModuleIREntries env i do
        checkExtTarget m n; report "compilerOverrideAttribute" n m lbl
    for (lbl, ext) in #[("tagged_return", Compiler.LCNF.taggedReturnAttr.ext), ("unbox", IR.UnboxResult.unboxAttr.ext), ("never_extract", neverExtractAttr.ext)] do
      for n in ext.getModuleEntries env i ++ ext.getModuleIREntries env i do
        checkExtTarget m n; report "compilerOverrideAttribute" n m lbl
    for (n, kind) in Compiler.inlineAttrs.ext.getModuleEntries env i ++ Compiler.inlineAttrs.ext.getModuleIREntries env i do
      checkExtTarget m n
      if kind == .macroInline && !genuineCtorIdxMacroInline env L.toolchainProv m n then
        report "compilerOverrideAttribute" n m "macro_inline: non-toolchain @[macro_inline] outside verified I.ctorIdx shape"
    for entry in Compiler.LCNF.postponedCompileDeclsExt.getModuleEntries env i ++ Compiler.LCNF.postponedCompileDeclsExt.getModuleIREntries env i do
      for n in entry.declNames do checkExtTarget m n; report "environmentLoadFailed" n m "compilation postponed (separate compilation without IR)"
    for (lbl, ns) in #[("casesOn_tag", auxRecExt.getModuleEntries env i ++ auxRecExt.getModuleIREntries env i),
        ("sparse_casesOn_tag", sparseCasesOnExt.getModuleEntries env i ++ sparseCasesOnExt.getModuleIREntries env i),
        ("noConfusion_tag", (noConfusionExt.getModuleEntries env i ++ noConfusionExt.getModuleIREntries env i).map Prod.fst)] do
      for n in ns do
        checkExtTarget m n
        unless origin? env n == some m do report "compilerOverrideAttribute" n m s!"{lbl}: tag on a foreign declaration"
    let modData := env.header.moduleData[i]!
    let modKernelNames : NameSet := modData.constNames.foldl (·.insert ·) {}
    let modExtraNames : NameSet := modData.extraConstNames.foldl (·.insert ·) {}
    let checkSpecEntry (e : Compiler.LCNF.Specialize.CacheEntry) : AuditM Unit := do
      let dn := e.declName
      checkExtTarget m dn
      unless isClosedExpr e.key do report "openExpression" dn m "specialize_cache: open expression in specialization key"; return
      if compilerReservedNames.contains dn || toolchainNames.contains dn then
        report "compilerOverrideAttribute" dn m "specialize_cache: entry target spoofs reserved/toolchain name"; return
      for kc in exprEdges e.key {} do
        if isShareCommonName env kc then report "shareCommonForbidden" dn m s!"specialize_cache: key references Init.ShareCommon ({kc})"
        checkPrivateName L toolchainNames ((origin? env kc).getD m) kc (env.find? kc)
      if modKernelNames.contains dn || (env.find? dn).isSome then report "compilerOverrideAttribute" dn m "specialize_cache: entry targets a kernel declaration"; return
      unless modExtraNames.contains dn && origin? env dn == some m do report "compilerOverrideAttribute" dn m "specialize_cache: entry target not owned by module"; return
      let some irDecl := IR.findEnvDecl env dn | report "compilerOverrideAttribute" dn m "specialize_cache: entry target has no compiled IR body"; return
      let some bd := Compiler.LCNF.getDeclCore? env Compiler.LCNF.baseExt dn | report "compilerOverrideAttribute" dn m "specialize_cache: entry target missing base-phase LCNF"; return
      let some md := Compiler.LCNF.getDeclCore? env Compiler.LCNF.monoExt dn | report "compilerOverrideAttribute" dn m "specialize_cache: entry target missing mono-phase LCNF"; return
      let (cb, cm, ciR) := (classifyLCNF env bd, classifyLCNF env md, classifyIR irDecl)
      unless simpleRetCompat cb cm && simpleRetCompat cm ciR && simpleRetCompat cb ciR do
        report "compilerOverrideAttribute" dn m "specialize_cache: base/mono LCNF and IR return values contradict each other"
      match (stripLeadingLams e.key 256).1.getAppFn with
      | .const kfn _ =>
        let dnStr := dn.toString
        unless dnStr.startsWith (kfn.toString ++ "._at_.") && (dnStr.splitOn ".spec_").length > 1 do
          report "compilerOverrideAttribute" dn m s!"specialize_cache: target {dn} does not match specialization key head {kfn}"
      | _ => report "compilerOverrideAttribute" dn m "specialize_cache: malformed specialization key"
    for e in Compiler.LCNF.Specialize.specCacheExt.getModuleEntries env i ++ Compiler.LCNF.Specialize.specCacheExt.getModuleIREntries env i do
      checkSpecEntry e
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
  unless livePasses.isEmpty do report "compilerOverrideAttribute" `cpass .anonymous "cpass: live compiler pass registration"
  unless passManagerFingerprint livePM == passManagerFingerprint Compiler.LCNF.builtinPassManager do
    report "compilerOverrideAttribute" `compiler_pipeline .anonymous "compiler_pipeline: live PassManager differs from builtinPassManager"
  let (liveFolders, liveFolderMap) := Compiler.LCNF.Simp.ConstantFold.folderExt.getState env
  unless liveFolders.isEmpty do report "compilerOverrideAttribute" `constant_fold .anonymous "constant_fold: live folder registration"
  let mut liveFolderKeys : NameSet := {}
  for (k, _) in liveFolderMap.toList do
    liveFolderKeys := liveFolderKeys.insert k
    unless builtinFolderKeySet.contains k do report "compilerOverrideAttribute" k .anonymous "constant_fold: live folder key not in builtinFolders"
  unless liveFolderKeys.size == builtinFolderKeySet.size do
    report "compilerOverrideAttribute" `constant_fold .anonymous "constant_fold: live folder table differs from builtinFolders"
  for (_, dn) in (Compiler.LCNF.Specialize.specCacheExt.getState env).toList do
    report "compilerOverrideAttribute" dn .anonymous "specialize_cache: live specialization cache entry"
  for (lbl, st) in #[("tagged_return", Compiler.LCNF.taggedReturnAttr.ext.getState env),
      ("unbox", IR.UnboxResult.unboxAttr.ext.getState env), ("never_extract", neverExtractAttr.ext.getState env)] do
    for n in st do report "compilerOverrideAttribute" n .anonymous s!"{lbl}: live {lbl} entry"
  for (n, kind) in (Compiler.inlineAttrs.ext.getState env).toList do
    if kind == .macroInline then
      let om := (origin? env n).getD .anonymous
      unless L.toolchainProv.contains om || genuineCtorIdxMacroInline env L.toolchainProv om n do
        report "compilerOverrideAttribute" n om "macro_inline: live @[macro_inline] outside verified I.ctorIdx shape"
  return (toolchainCSimp, toolchainImplByTargets)

/-- Value-preserving, total, fuel-bounded lattice operations for validating
`ElimDeadBranches.functionSummariesExt` against `monoExt` in linear time (0 `partial`, 0 `unsafe`). -/
abbrev SummaryVal := Compiler.LCNF.UnreachableBranches.Value

def summaryJoin (v1 v2 : SummaryVal) (fuel : Nat) : SummaryVal :=
  match fuel with
  | 0 => .top
  | fuel + 1 =>
    match v1, v2 with
    | .bot, v | v, .bot => v
    | .top, _ | _, .top => .top
    | .ctor c1 a1, .ctor c2 a2 =>
      if c1 == c2 then
        let n := max a1.size a2.size
        let merged := (Array.range n).map fun i => summaryJoin (a1.getD i .top) (a2.getD i .top) fuel
        .ctor c1 merged
      else .choice [.ctor c1 a1, .ctor c2 a2]
    | .choice vs, v | v, .choice vs =>
      let list := match v with | .choice ws => ws | _ => [v]
      if list.any (· == .top) || vs.any (· == .top) then .top
      else
        let addOne (acc : List SummaryVal) (x : SummaryVal) : List SummaryVal :=
          match x with
          | .ctor cx ax =>
            if acc.any fun | .ctor c _ => c == cx | _ => false then
              acc.map fun
                | .ctor c a =>
                  if c == cx then
                    let n := max a.size ax.size
                    .ctor c ((Array.range n).map fun i => summaryJoin (a.getD i .top) (ax.getD i .top) fuel)
                  else .ctor c a
                | o => o
            else x :: acc
          | _ => acc
        .choice (list.foldl addOne vs)

def summaryCtorArgs (v : SummaryVal) (ctor : Name) : Option (Array SummaryVal) :=
  match v with
  | .bot => none
  | .top => some #[]
  | .ctor c args => if c == ctor then some args else none
  | .choice vs =>
    vs.findSome? fun
      | .ctor c args => if c == ctor then some args else none
      | .top => some #[]
      | _ => none

def summaryProj (v : SummaryVal) (idx : Nat) (fuel : Nat) : SummaryVal :=
  match fuel, v with
  | 0, _ => .top
  | _, .bot => .bot
  | _, .top => .top
  | _, .ctor _ args => args.getD idx .top
  | f + 1, .choice vs => vs.foldl (fun acc x => summaryJoin acc (summaryProj x idx f) f) .bot

def summaryTopCtors (v : SummaryVal) (fuel : Nat) : Option NameSet :=
  match fuel, v with
  | 0, _ => none
  | _, .bot => some {}
  | _, .top => none
  | _, .ctor c _ => some (NameSet.empty.insert c)
  | f + 1, .choice vs =>
    vs.foldlM (init := {}) fun acc x => do
      let s ← summaryTopCtors x f
      pure (s.foldl (·.insert ·) acc)

def isExhaustiveCtorSet (env : Environment) (cs : NameSet) : Bool := Id.run do
  let mut indOpt : Option Name := none
  for c in cs do
    match env.find? c with
    | some (.ctorInfo cv) =>
      match indOpt with
      | none => indOpt := some cv.induct
      | some ind => if ind != cv.induct then return false
    | _ => return false
  match indOpt with
  | none => false
  | some ind =>
    match env.find? ind with
    | some (.inductInfo iv) => iv.numCtors >= 1 && iv.ctors.all cs.contains
    | _ => false

def summarySubsumes (env : Environment) (actual claimed : SummaryVal) : Bool :=
  match summaryTopCtors claimed 16 with
  | none => true
  | some allowed =>
    match summaryTopCtors actual 16 with
    | none => isExhaustiveCtorSet env allowed
    | some got => got.all allowed.contains

/-- Linear-time abstract evaluation of a `mono`-phase LCNF `Code .pure` body preserving constructor
field summaries across `.proj` and `.cases` alt parameters: walks the AST at most once (evaluating
join-point continuation `k` first to collect joined `.jmp` arguments, then evaluating `fd.value`
once), returning `none` on fuel exhaustion so callers fail closed. -/
def absEvalMono (env : Environment) (selfName : Name)
    (code : Compiler.LCNF.Code .pure) (vars : Std.HashMap FVarId SummaryVal)
    (jpArgs : Std.HashMap FVarId (Array SummaryVal))
    (fuel : Nat) : Option (SummaryVal × Std.HashMap FVarId (Array SummaryVal)) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    let argVal : Compiler.LCNF.Arg .pure → SummaryVal
      | .fvar fv => vars.getD fv .top
      | _ => .top
    match code with
    | .unreach _ => some (.bot, jpArgs)
    | .return fv => some (vars.getD fv .top, jpArgs)
    | .jmp fn args =>
      let cur := jpArgs.getD fn #[]
      let avs := args.map argVal
      let merged := if cur.isEmpty then avs
        else (cur.zip avs).map fun (a, b) => summaryJoin a b 8
      some (.bot, jpArgs.insert fn merged)
    | .fun fd k =>
      absEvalMono env selfName k (vars.insert fd.fvarId .top) jpArgs fuel
    | .jp fd k => do
      let (r2, jpArgs') ← absEvalMono env selfName k vars jpArgs fuel
      let passed := jpArgs'.getD fd.fvarId #[]
      if passed.isEmpty && !fd.params.isEmpty && !jpArgs'.contains fd.fvarId then
        return (r2, jpArgs')
      let mut jpVars := vars
      for h : idx in [0:fd.params.size] do
        let p := fd.params[idx]
        jpVars := jpVars.insert p.fvarId (passed.getD idx .top)
      let (r1, jpArgs'') ← absEvalMono env selfName fd.value jpVars jpArgs' fuel
      pure (summaryJoin r1 r2 8, jpArgs'')
    | .let ld k =>
      let lv : SummaryVal := match ld.value with
        | .lit (.nat n) =>
          if n == 0 then .ctor ``Nat.zero #[] else .ctor ``Nat.succ #[.top]
        | .proj _ idx fv => summaryProj (vars.getD fv .top) idx 8
        | .fvar fv args =>
          if args.isEmpty then vars.getD fv .top else .top
        | .const c _ args =>
          if env.find? c matches some (.ctorInfo _) then
            .ctor c (args.map argVal)
          else if c == selfName then
            .bot
          else
            match Compiler.LCNF.UnreachableBranches.getFunctionSummary? env c with
            | some sv =>
              match Compiler.LCNF.getDeclCore? env Compiler.LCNF.monoExt c with
              | some cd => if args.size == cd.params.size then sv else .top
              | none => .top
            | none => .top
        | _ => .top
      absEvalMono env selfName k (vars.insert ld.fvarId lv) jpArgs fuel
    | .cases cs =>
      let dv := vars.getD cs.discr .top
      cs.alts.foldlM (init := (.bot, jpArgs)) fun (acc, jpa) alt => do
        match alt with
        | .alt ctor ps body =>
          match summaryCtorArgs dv ctor with
          | none => pure (acc, jpa)
          | some argVals =>
            let mut vars' := vars
            for h : idx in [0:ps.size] do
              vars' := vars'.insert ps[idx].fvarId (argVals.getD idx .top)
            let (r, jpa') ← absEvalMono env selfName body vars' jpa fuel
            pure (summaryJoin acc r 8, jpa')
        | .default body =>
          if dv == .bot then pure (acc, jpa)
          else
            let (r, jpa') ← absEvalMono env selfName body vars jpa fuel
            pure (summaryJoin acc r 8, jpa')

/-- Validate a non-`.top` `ElimDeadBranches` summary against the function's `mono` LCNF body. -/
def checkFunctionSummary (env : Environment) (m dn : Name)
    (val : SummaryVal) : AuditM Unit := do
  if val == .top then return
  if let some md := Compiler.LCNF.getDeclCore? env Compiler.LCNF.monoExt dn then
    match md.value with
    | .extern .. => pure ()
    | .code code =>
      let vars0 := md.params.foldl (init := ({} : Std.HashMap FVarId SummaryVal)) fun a p => a.insert p.fvarId .top
      match absEvalMono env dn code vars0 {} 8192 with
      | none =>
        report "auditFuelExhausted" dn m "dead_branch_summary: mono summary validation exhausted its fuel"
      | some (av, _) =>
        unless summarySubsumes env av val do
          report "compilerOverrideAttribute" dn m "dead_branch_summary: function summary contradicts mono LCNF body"

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

def checkCompiledCallee (L : Loaded) (m n c : Name) (label : String)
    (toolchainImplByTargets : NameSet) (requireKnown : Bool) : AuditM Unit := do
  let env := L.env
  if isShareCommonName env c then report "shareCommonForbidden" c m s!"{label} callee of {n} references Init.ShareCommon"
  if c == n then return
  match origin? env c with
  | none => if requireKnown && (IR.findEnvDecl env c).isNone then report "environmentLoadFailed" c m s!"{label} callee of {n} is unknown"
  | some cm =>
    if let some cci := env.find? c then
      if cci.isUnsafe then
        unless L.toolchainProv.contains cm && (compilerBorrowedUnsafeIntrinsics.contains c || toolchainImplByTargets.contains c) do
          report "unsafeDeclaration" c m s!"{label} callee of {n} invokes unsafe declaration {c} from {cm}"
      else if cci.isPartial then
        unless (match c with | .str _ "_unsafe_rec" => true | _ => false) do
          report "partialOrUnsafeRecDependency" c m s!"{label} callee of {n} invokes partial declaration {c} from {cm}"
      if let .opaqueInfo _ := cci then
        if let some sib := env.find? (c.str "_unsafe_rec") then
          if sib.isPartial || sib.isUnsafe then
            report "partialOrUnsafeRecDependency" c m s!"{label} callee of {n} invokes partial def {c} from {cm}"

def checkLCNFDeclCallees (L : Loaded) (m : Name) (phaseLabel : String)
    (toolchainImplByTargets : NameSet) (d : Compiler.LCNF.Decl .pure) : AuditM Unit := do
  match d.value with
  | .extern ed => if externDataMentionsShareCommon ed then report "shareCommonForbidden" d.name m s!"{phaseLabel} LCNF extern targets lean_sharecommon_*"
  | .code code =>
    let some consts := collectLCNFCodeConsts code {} 16384
      | report "auditFuelExhausted" d.name m s!"{phaseLabel} LCNF callee scan exhausted its fuel"; return
    for c in consts do checkCompiledCallee L m d.name c s!"{phaseLabel} LCNF" toolchainImplByTargets false

def checkIRDeclBody (L : Loaded) (m : Name) (toolchainImplByTargets : NameSet) (d : IR.Decl) : AuditM Unit := do
  match d with
  | .fdecl _ _ _ _ info => if let some dep := info.sorryDep? then report "sorryOrUnproved" d.name m s!"IR declaration records sorry dependency {dep}"
  | .extern _ _ _ ed =>
    if externDataMentionsShareCommon ed then report "shareCommonForbidden" d.name m "IR extern targets lean_sharecommon_*"
    return
  for c in IR.collectUsedDecls L.env [d] do checkCompiledCallee L m d.name c "IR" toolchainImplByTargets true

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
  let checkOwned (label : String) (needIR : Bool) (n : Name) (seen : NameSet) : AuditM NameSet := do
    if seen.contains n then report "environmentLoadFailed" n m s!"duplicate {label} entry"
    unless kernelNames.contains n || extraNames.contains n do report "environmentLoadFailed" n m s!"{label} not owned by its module"
    unless origin? env n == some m do report "environmentLoadFailed" n m s!"{label} provenance mismatch"
    if needIR && (IR.findEnvDecl env n).isNone then report "environmentLoadFailed" n m s!"{label} without IR body"
    return seen.insert n
  let mut seenSig : NameSet := {}; let mut seenSigIR : NameSet := {}
  for sig in Compiler.LCNF.impureSigExt.getModuleEntries env i do seenSig ← checkOwned "impure signature" true sig.name seenSig
  for sig in Compiler.LCNF.impureSigExt.getModuleIREntries env i do seenSigIR ← checkOwned "impure IR signature" true sig.name seenSigIR
  let mut seenBase : NameSet := {}; let mut seenBaseIR : NameSet := {}
  for bd in Compiler.LCNF.baseExt.getModuleEntries env i do
    seenBase ← checkOwned "base-phase LCNF declaration" true bd.name seenBase
    checkLCNFDeclCallees L m "base" toolchainImplByTargets bd
  for bd in Compiler.LCNF.baseExt.getModuleIREntries env i do
    seenBaseIR ← checkOwned "base-phase LCNF IR declaration" true bd.name seenBaseIR
    checkLCNFDeclCallees L m "base-ir" toolchainImplByTargets bd
  let mut seenMono : NameSet := {}; let mut seenMonoIR : NameSet := {}
  for md in Compiler.LCNF.monoExt.getModuleEntries env i do
    seenMono ← checkOwned "mono-phase LCNF declaration" true md.name seenMono
    checkLCNFDeclCallees L m "mono" toolchainImplByTargets md
  for md in Compiler.LCNF.monoExt.getModuleIREntries env i do
    seenMonoIR ← checkOwned "mono-phase LCNF IR declaration" true md.name seenMonoIR
    checkLCNFDeclCallees L m "mono-ir" toolchainImplByTargets md
  let mut seenSumm : NameSet := {}; let mut seenSummIR : NameSet := {}
  for (dn, val) in Compiler.LCNF.UnreachableBranches.functionSummariesExt.getModuleEntries env i do
    seenSumm ← checkOwned "dead-branch function summary" false dn seenSumm
    checkFunctionSummary env m dn val
  for (dn, val) in Compiler.LCNF.UnreachableBranches.functionSummariesExt.getModuleIREntries env i do
    seenSummIR ← checkOwned "dead-branch IR function summary" false dn seenSummIR
    checkFunctionSummary env m dn val
  for ci in data.constants do
    let n := ci.name
    if let some irDecl := IR.findEnvDecl env n then
      if (ci matches .defnInfo _) && !(isExtern env n || isExternC env n) then
        let bd? := Compiler.LCNF.getDeclCore? env Compiler.LCNF.baseExt n
        let md? := Compiler.LCNF.getDeclCore? env Compiler.LCNF.monoExt n
        if !seenBase.contains n && !seenBaseIR.contains n && bd?.isNone then
          report "environmentLoadFailed" n m "IR body for definition without base-phase LCNF declaration"
        if !seenMono.contains n && !seenMonoIR.contains n && md?.isNone then
          report "environmentLoadFailed" n m "IR body for definition without mono-phase LCNF declaration"
        if let (some bd, some md) := (bd?, md?) then
          let ck := classifyKernel env ci
          let cb := classifyLCNF env bd
          let cm := classifyLCNF env md
          let ciR := classifyIR irDecl
          unless simpleRetCompat ck cb && simpleRetCompat ck cm && simpleRetCompat ck ciR &&
              simpleRetCompat cb cm && simpleRetCompat cm ciR && simpleRetCompat cb ciR do
            report "compilerOverrideAttribute" n m "lcnf_ir_mismatch: kernel, base/mono LCNF, and IR return values contradict each other"
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
    (localOk : Name → Bool) (fuel : Nat) (label : Name)
    (allowClassical : Bool := L.req.allowClassicalChoice) : AuditM NameSet := do
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
        checkAxiom L ci m localOk allowClassical
      for d in declEdges ci do
        unless visited.contains d do
          visited := visited.insert d
          pending := d :: pending
  unless done do report "auditFuelExhausted" label label "dependency closure exhausted its fuel"
  return visited

/-! ## Hardened Spec-Strength & Mutant-Kill Verification Gates -/

public def trustedVerifModName : Name := `Trusted.VerificationResult
public def specLibModName : Name := `Anneal.OleanSpecStrengthAuditor

def claimVerificationResultName : Name := `Trusted.VerificationResult.VerificationResult
def claimStatefulVerificationResultName : Name := `Trusted.VerificationResult.StatefulVerificationResult
def claimTotalVerificationResultName : Name := `Trusted.VerificationResult.TotalVerificationResult
def claimModularVerificationResultName : Name := `Trusted.VerificationResult.ModularVerificationResult

def mirValueName : Name := `Trusted.Rustc.V2026_06_01.MirSemantics.Value
def mirMemoryName : Name := `Trusted.Rustc.V2026_06_01.MirSemantics.Memory

def certSpecStrengthName : Name := `Anneal.OleanSpecStrengthAuditor.SpecStrengthCert
def certMultiMutantName : Name := `Anneal.OleanSpecStrengthAuditor.MultiMutantSpecCert
def certDeterministicName : Name := `Anneal.OleanSpecStrengthAuditor.DeterministicSpecCert
def certInputSensitiveName : Name := `Anneal.OleanSpecStrengthAuditor.InputSensitiveSpecCert

def certModularSpecStrengthName : Name := `Anneal.OleanSpecStrengthAuditor.ModularSpecStrengthCert
def certModularMultiMutantName : Name := `Anneal.OleanSpecStrengthAuditor.ModularMultiMutantSpecCert
def certModularDeterministicName : Name := `Anneal.OleanSpecStrengthAuditor.ModularDeterministicSpecCert
def certModularInputSensitiveName : Name := `Anneal.OleanSpecStrengthAuditor.ModularInputSensitiveSpecCert

def mutantCategoryPrefix : Name := `Anneal.OleanSpecStrengthAuditor.MutantCategory
def directCoversCategoryName : Name := `Anneal.OleanSpecStrengthAuditor.MultiMutantSpecCert.coversCategory
def modularCoversCategoryName : Name := `Anneal.OleanSpecStrengthAuditor.ModularMultiMutantSpecCert.coversCategory

def SpecClassKind.className : SpecClassKind → Name
  | .item => `Trusted.VerificationResult.ItemSpec
  | .statefulItem => `Trusted.VerificationResult.StatefulItemSpec
  | .totalItem => `Trusted.VerificationResult.TotalItemSpec
  | .modularItem => `Trusted.VerificationResult.ModularItemSpec

/-- Replace the active `Core.Context` with clean options and bounded heartbeat/recursion limits. -/
def withCleanCoreContext (cleanOpts : Options) (nowHb hb : Nat) (x : MetaM α) : MetaM α :=
  fun metaCtx metaSt =>
    withReader (m := CoreM) (fun coreCtx => { coreCtx with
      options := cleanOpts
      diag := false
      initHeartbeats := nowHb
      maxHeartbeats := hb * 1000
      currRecDepth := 0
      maxRecDepth := 4096 }) (x metaCtx metaSt)

/-- Execute `x` inside an isolated, kernel-faithful `CoreM` + `MetaM` context:
- clears and restores `Core.State.cache` (`instLevelType` and `instLevelValue`),
- resets `Core.Context` options (`smartUnfolding := false`, clean defaults, bounded heartbeats),
- wraps in `Lean.withoutExporting` so private instances/aliases cannot be hidden by export mode,
- clears and restores `Meta.State.cache` via `Meta.withFreshCache`,
- replaces `Meta.Context` with default `Config` (no `customCanUnfoldPredicate?`, empty `lctx`,
  empty `localInstances`, default `iota`/`beta`/`zeta`/`proj`/`etaStruct`), and
- runs inside `Meta.withNewMCtxDepth` (`allowLevelAssignments := false`). -/
public def withKernelFaithfulMeta (x : MetaM α) (heartbeats : Nat := 400000) : MetaM α := do
  let savedCoreCache := (← getThe Core.State).cache
  modifyThe Core.State fun s => { s with cache := {} }
  try
    let curOpts ← getOptions
    let hb := min (max (maxHeartbeats.get curOpts) heartbeats) 2000000
    let cleanOpts : Options := ({} : Options)
      |>.set `smartUnfolding false
      |>.set `maxHeartbeats hb
      |>.set `maxRecDepth 4096
    let nowHb ← IO.getNumHeartbeats
    withCleanCoreContext cleanOpts nowHb hb do
      Lean.withoutExporting do
        Meta.withFreshCache do
          withReader (fun (_ : Meta.Context) => ({} : Meta.Context)) do
            Meta.withNewMCtxDepth do
              x
  finally
    modifyThe Core.State fun s => { s with cache := savedCoreCache }

/-- Ask Lean's kernel directly to confirm `val : expectedTy` (both closed) under a clamped
heartbeat threshold `[1, USize.size - 1]`. -/
def kernelConfirmsHasType (env : Environment) (val expectedTy : Expr) (budget : Nat := 400) :
    IO Bool := do
  unless isClosedExpr val && isClosedExpr expectedTy do return false
  let name := freshName env `_olean_auditor_spec_type_check
  let decl := Declaration.defnDecl {
    name, levelParams := [], type := expectedTy, value := val, hints := .opaque, safety := .safe
  }
  let threshold ← kernelHeartbeatThreshold budget
  match env.toKernelEnv.addDeclCore threshold 0 decl none with
  | .ok _ => return true
  | .error _ => return false

/-- Ask Lean's kernel directly to confirm `e = Bool.true` via `Eq.refl Bool.true`. -/
def kernelConfirmsBoolTrue (env : Environment) (e : Expr) (budget : Nat := 400) : IO Bool := do
  unless isClosedExpr e do return false
  let ty := mkApp3 (mkConst ``Eq [Level.one]) (mkConst ``Bool) e (mkConst ``Bool.true)
  let pf := mkApp2 (mkConst ``Eq.refl [Level.one]) (mkConst ``Bool) (mkConst ``Bool.true)
  kernelAccepts env [] ty pf budget

/-- Result of one global-linear-budget pure head normalization step sequence. -/
public structure HeadNormResult (fuel : Nat) where
  expr : Expr
  certainWhnf : Bool
  rem : { r : Nat // r ≤ fuel }

def natLitToCtor? : Expr → Option Expr
  | .lit (.natVal 0) => some (mkConst ``Nat.zero)
  | .lit (.natVal (n + 1)) => some (mkApp (mkConst ``Nat.succ) (.lit (.natVal n)))
  | _ => none

/-- `"abc"` as the kernel sees it under a projection or a recursor: `String.ofList ['a', 'b', 'c']`. -/
def strLitToOfList? : Expr → Option Expr
  | .lit (.strVal s) => some (mkApp (mkConst ``String.ofList) (toExpr s.toList))
  | _ => none

/-- `Nat` functions the kernel evaluates natively (GMP) when their arguments are literals. -/
def kernelNatAcceleratedOps : List Name :=
  [``Nat.add, ``Nat.sub, ``Nat.mul, ``Nat.div, ``Nat.mod, ``Nat.gcd, ``Nat.beq, ``Nat.ble,
   ``Nat.bitwise, ``Nat.land, ``Nat.lor, ``Nat.xor, ``Nat.shiftLeft, ``Nat.shiftRight,
   ``Nat.pow, ``Nat.log2]

def isCtorOrLitHead (env : Environment) (e : Expr) : Bool :=
  match e.getAppFn with
  | .lit _ => true
  | .const c _ =>
    match env.find? c with
    | some (.ctorInfo _) => true
    | _ => false
  | _ => false

def isStructureLikeInduct (env : Environment) (indName : Name) : Option (InductiveVal × ConstructorVal) := do
  let .inductInfo iv ← env.find? indName | none
  guard (iv.ctors.length == 1 && iv.numIndices == 0 && !iv.isRec && !iv.isReflexive && !iv.isUnsafe)
  let ctorName ← iv.ctors.head?
  let .ctorInfo cv ← env.find? ctorName | none
  return (iv, cv)

/-- Total, global-linear-budget pure kernel-faithful weak-head normalizer (`0 partial`, `0 unsafe`).
Threads a single remaining-step budget `{ r : Nat // r ≤ fuel }` across every sub-reduction so
worst-case work is strictly `O(fuel)` even on exponentially branching types (`A4-7`).
Marks `.opaqueInfo` native evaluators `Lean.reduceBool` and `Lean.reduceNat` as undecided
(`certainWhnf := false`) so pure scanning fails closed (`A4-5a`), while stuck variables,
constructors, and stuck recursors on variables return `certainWhnf := true` (`0` false candidates). -/
public def headNormalizeBudget (env : Environment) (e : Expr) (fuel : Nat) : HeadNormResult fuel :=
  match fuel with
  | 0 => { expr := e, certainWhnf := false, rem := ⟨0, Nat.le_refl 0⟩ }
  | fuel' + 1 =>
    let liftRes {k : Nat} (hk : k ≤ fuel') (r : HeadNormResult k) : HeadNormResult (fuel' + 1) :=
      { expr := r.expr
        certainWhnf := r.certainWhnf
        rem := ⟨r.rem.1, Nat.le_trans r.rem.2 (Nat.le_trans hk (Nat.le_succ _))⟩ }
    let liftRem {k : Nat} (hk : k ≤ fuel') (r : { x : Nat // x ≤ k }) : { x : Nat // x ≤ fuel' + 1 } :=
      ⟨r.1, Nat.le_trans r.2 (Nat.le_trans hk (Nat.le_succ _))⟩
    match e with
    | .mdata _ b => liftRes (Nat.le_refl _) (headNormalizeBudget env b fuel')
    | .letE _ _ v b _ => liftRes (Nat.le_refl _) (headNormalizeBudget env (b.instantiate1 v) fuel')
    | _ =>
      let fn := e.getAppFn
      let args := e.getAppArgs
      match fn with
      | .mdata _ inner =>
        liftRes (Nat.le_refl _) (headNormalizeBudget env (mkAppN inner args) fuel')
      | .letE _ _ v b _ =>
        liftRes (Nat.le_refl _) (headNormalizeBudget env (mkAppN (b.instantiate1 v) args) fuel')
      | .lam _ _ body _ =>
        if hEmpty : args.isEmpty then
          { expr := e, certainWhnf := true, rem := ⟨fuel', Nat.le_succ _⟩ }
        else
          let next := mkAppN (body.instantiate1 args[0]!) (args.extract 1 args.size)
          liftRes (Nat.le_refl _) (headNormalizeBudget env next fuel')
      | .proj structName idx s =>
        let sRes := headNormalizeBudget env s fuel'
        match env.find? structName with
        | some (.inductInfo iv) =>
          match iv.ctors with
          | [ctorName] =>
            match env.find? ctorName with
            | some (.ctorInfo cv) =>
              if sRes.expr.isAppOf ctorName then
                let sArgs := sRes.expr.getAppArgs
                let fieldIdx := cv.numParams + idx
                if hF : fieldIdx < sArgs.size then
                  have : sRes.rem.1 < fuel' + 1 := Nat.lt_succ_of_le sRes.rem.2
                  liftRes sRes.rem.2 (headNormalizeBudget env (mkAppN sArgs[fieldIdx] args) sRes.rem.1)
                else
                  { expr := mkAppN (.proj structName idx sRes.expr) args
                    certainWhnf := false
                    rem := liftRem (Nat.le_refl _) sRes.rem }
              else
                match strLitToOfList? sRes.expr with
                | some ofList =>
                  -- The kernel converts a string literal under a projection to `String.ofList [..]`
                  -- and keeps reducing; a literal is never a certain stuck structure value.
                  have : sRes.rem.1 < fuel' + 1 := Nat.lt_succ_of_le sRes.rem.2
                  liftRes sRes.rem.2
                    (headNormalizeBudget env (mkAppN (.proj structName idx ofList) args) sRes.rem.1)
                | none =>
                  { expr := mkAppN (.proj structName idx sRes.expr) args
                    certainWhnf := sRes.certainWhnf
                    rem := liftRem (Nat.le_refl _) sRes.rem }
            | _ =>
              { expr := e, certainWhnf := false, rem := liftRem (Nat.le_refl _) sRes.rem }
          | _ =>
            { expr := e, certainWhnf := false, rem := liftRem (Nat.le_refl _) sRes.rem }
        | _ =>
          { expr := e, certainWhnf := false, rem := liftRem (Nat.le_refl _) sRes.rem }
      | .const c us =>
        if c == ``Lean.reduceBool || c == ``Lean.reduceNat then
          { expr := e, certainWhnf := false, rem := ⟨fuel', Nat.le_succ _⟩ }
        else
          match env.find? c with
          | none => { expr := e, certainWhnf := false, rem := ⟨fuel', Nat.le_succ _⟩ }
          | some (.defnInfo dv) =>
            if dv.levelParams.length == us.length then
              let body := dv.value.instantiateLevelParams dv.levelParams us
              let r := liftRes (Nat.le_refl _) (headNormalizeBudget env (mkAppN body args) fuel')
              -- The kernel evaluates these `Nat` functions on literals with GMP and never looks at
              -- their bodies, so a body that is stuck (on an axiom inside a well-foundedness proof,
              -- say) proves nothing about the kernel: only a constructor or literal result is certain.
              if kernelNatAcceleratedOps.contains c && !isCtorOrLitHead env r.expr then
                { r with certainWhnf := false }
              else r
            else
              { expr := e, certainWhnf := false, rem := ⟨fuel', Nat.le_succ _⟩ }
          | some (.thmInfo tv) =>
            -- Lean's kernel δ-unfolds theorems exactly like definitions (`is_delta` tests
            -- `has_value`), while `Meta.whnf` never does (`getUnfoldableConst?` answers `none` for
            -- `.thm` at every transparency): a recursor whose major premise is a theorem (`Acc.rec`,
            -- any subsingleton eliminator) reduces in the kernel and is stuck in `MetaM`.
            if tv.levelParams.length == us.length then
              let body := tv.value.instantiateLevelParams tv.levelParams us
              liftRes (Nat.le_refl _) (headNormalizeBudget env (mkAppN body args) fuel')
            else
              { expr := e, certainWhnf := false, rem := ⟨fuel', Nat.le_succ _⟩ }
          | some (.recInfo rv) =>
            let majorIdx := rv.getMajorIdx
            if hMaj : majorIdx < args.size then
              let pmmEnd := rv.numParams + rv.numMotives + rv.numMinors
              let pmm := args.extract 0 pmmEnd
              let extra := args.extract (majorIdx + 1) args.size
              if rv.k then
                match rv.rules with
                | [r] =>
                  if r.nfields == 0 && rv.levelParams.length == us.length then
                    let next := mkAppN (r.rhs.instantiateLevelParams rv.levelParams us) (pmm ++ extra)
                    liftRes (Nat.le_refl _) (headNormalizeBudget env next fuel')
                  else
                    { expr := e, certainWhnf := false, rem := ⟨fuel', Nat.le_succ _⟩ }
                | _ =>
                  { expr := e, certainWhnf := false, rem := ⟨fuel', Nat.le_succ _⟩ }
              else
                let majRes := headNormalizeBudget env args[majorIdx] fuel'
                let majExpr := (natLitToCtor? majRes.expr).getD majRes.expr
                let majFn := majExpr.getAppFn
                let majArgs := majExpr.getAppArgs
                let rule? := match majFn with
                  | .const ctorName _ => rv.rules.find? (fun (r : RecursorRule) => r.ctor == ctorName)
                  | _ => none
                match rule? with
                | some r =>
                  if r.nfields ≤ majArgs.size && rv.levelParams.length == us.length then
                    let fields := majArgs.extract (majArgs.size - r.nfields) majArgs.size
                    let next := mkAppN (r.rhs.instantiateLevelParams rv.levelParams us) (pmm ++ fields ++ extra)
                    have : majRes.rem.1 < fuel' + 1 := Nat.lt_succ_of_le majRes.rem.2
                    liftRes majRes.rem.2 (headNormalizeBudget env next majRes.rem.1)
                  else
                    { expr := e, certainWhnf := false, rem := liftRem (Nat.le_refl _) majRes.rem }
                | none =>
                  match strLitToOfList? majRes.expr with
                  | some ofList =>
                    -- The kernel turns a string literal major premise into `String.ofList [..]`
                    -- before applying recursor rules (`A1-4`).
                    let nextArgs := args.set! majorIdx ofList
                    have : majRes.rem.1 < fuel' + 1 := Nat.lt_succ_of_le majRes.rem.2
                    liftRes majRes.rem.2 (headNormalizeBudget env (mkAppN fn nextArgs) majRes.rem.1)
                  | none =>
                    let etaNext? : Option Expr := do
                      guard (rv.levelParams.length == us.length)
                      let [r] := rv.rules | none
                      let .ctorInfo cv ← env.find? r.ctor | none
                      let (iv, _) ← isStructureLikeInduct env cv.induct
                      let fields := (Array.range r.nfields).map fun idx => Expr.proj iv.name idx majExpr
                      return mkAppN (r.rhs.instantiateLevelParams rv.levelParams us) (pmm ++ fields ++ extra)
                    match etaNext? with
                    | some next =>
                      have : majRes.rem.1 < fuel' + 1 := Nat.lt_succ_of_le majRes.rem.2
                      liftRes majRes.rem.2 (headNormalizeBudget env next majRes.rem.1)
                    | none =>
                      { expr := e, certainWhnf := majRes.certainWhnf, rem := liftRem (Nat.le_refl _) majRes.rem }
            else
              { expr := e, certainWhnf := true, rem := ⟨fuel', Nat.le_succ _⟩ }
          | some (.quotInfo qv) =>
            match qv.kind with
            | .lift =>
              if hMaj : 5 < args.size then
                let qRes := headNormalizeBudget env args[5] fuel'
                if qRes.expr.isAppOf ``Quot.mk && qRes.expr.getAppArgs.size ≥ 3 then
                  let a := qRes.expr.getAppArgs[2]!
                  let f := args[3]!
                  let extra := args.extract 6 args.size
                  have : qRes.rem.1 < fuel' + 1 := Nat.lt_succ_of_le qRes.rem.2
                  liftRes qRes.rem.2 (headNormalizeBudget env (mkAppN f (#[a] ++ extra)) qRes.rem.1)
                else
                  { expr := e, certainWhnf := qRes.certainWhnf, rem := liftRem (Nat.le_refl _) qRes.rem }
              else
                { expr := e, certainWhnf := true, rem := ⟨fuel', Nat.le_succ _⟩ }
            | .ind =>
              if hMaj : 4 < args.size then
                let qRes := headNormalizeBudget env args[4] fuel'
                if qRes.expr.isAppOf ``Quot.mk && qRes.expr.getAppArgs.size ≥ 3 then
                  let a := qRes.expr.getAppArgs[2]!
                  let f := args[3]!
                  let extra := args.extract 5 args.size
                  have : qRes.rem.1 < fuel' + 1 := Nat.lt_succ_of_le qRes.rem.2
                  liftRes qRes.rem.2 (headNormalizeBudget env (mkAppN f (#[a] ++ extra)) qRes.rem.1)
                else
                  { expr := e, certainWhnf := qRes.certainWhnf, rem := liftRem (Nat.le_refl _) qRes.rem }
              else
                { expr := e, certainWhnf := true, rem := ⟨fuel', Nat.le_succ _⟩ }
            | .type | .ctor =>
              { expr := e, certainWhnf := true, rem := ⟨fuel', Nat.le_succ _⟩ }
          | some (.inductInfo _) | some (.ctorInfo _) | some (.axiomInfo _) | some (.opaqueInfo _) =>
            { expr := e, certainWhnf := true, rem := ⟨fuel', Nat.le_succ _⟩ }
      | .mvar _ =>
        { expr := e, certainWhnf := false, rem := ⟨fuel', Nat.le_succ _⟩ }
      | _ =>
        { expr := e, certainWhnf := true, rem := ⟨fuel', Nat.le_succ _⟩ }
termination_by fuel

public inductive SpecClassMatch where
  | matched
  | notMatched
  | undecided
  deriving BEq, Repr

/-- Whether an expression still mentions any constant that can transitively reach `specClass`. -/
def exprCanReachSpecClass (specClass : Name) (reach? : Option NameSet) (e : Expr) : Bool :=
  match reach? with
  | some reach => e.getUsedConstants.any reach.contains
  | none => e.getUsedConstants.contains specClass

/-- Pure, total, global-linear-budget conclusion matcher for `specClass targetDefId`.
Shares the single global budget `fuel` across `forallE` stripping, head normalization, and
`defId` argument normalization. When the head is a stuck eliminator (`recInfo`/`quotInfo`),
projection, or bound/free variable whose term can still reach `specClass`, instantiating a binder
could reduce it to `specClass targetDefId`, so this returns `.undecided` (`A1-3`). -/
def specClassConclusionMatchBudget (env : Environment) (specClass : Name) (targetDefId : String)
    (e : Expr) (fuel : Nat) (reach? : Option NameSet := none) (varHeadIsCandidate : Bool := false) :
    SpecClassMatch :=
  match fuel with
  | 0 => .undecided
  | fuel' + 1 =>
    let res := headNormalizeBudget env e (fuel' + 1)
    match res.expr with
    | .forallE _ _ body _ =>
      if _ : res.rem.1 < fuel' + 1 then
        specClassConclusionMatchBudget env specClass targetDefId body res.rem.1 reach? varHeadIsCandidate
      else
        specClassConclusionMatchBudget env specClass targetDefId body fuel' reach? varHeadIsCandidate
    | e' =>
      if !res.certainWhnf then .undecided
      else
        match e'.getAppFn with
        | .const c _ =>
          if c == specClass then
            let args := e'.getAppArgs
            if args.size == 1 then
              let argRes := headNormalizeBudget env args[0]! res.rem.1
              match argRes.expr with
              | .lit (.strVal s) => if s == targetDefId then .matched else .notMatched
              | _ => .undecided
            else .undecided
          else
            let isElim := match env.find? c with
              | some (.recInfo _) | some (.quotInfo _) => true
              | _ => false
            if isElim && (varHeadIsCandidate || exprCanReachSpecClass specClass reach? e') then
              .undecided
            else
              .notMatched
        | .bvar _ | .fvar _ =>
          -- A variable conclusion (`{T : Type 1} → [h : Holder T] → T`) unifies with every goal:
          -- for a *registered instance* that is a candidate whatever constants it mentions.
          if varHeadIsCandidate || exprCanReachSpecClass specClass reach? e' then .undecided else .notMatched
        | .proj _ _ _ =>
          -- A stuck projection conclusion (`[c : Carrier] → c.ty`) can equally instantiate to any
          -- `specClass targetDefId` when registered via a forged `Meta.instanceExtension` entry (`A2-1a`).
          if varHeadIsCandidate || exprCanReachSpecClass specClass reach? e' then .undecided else .notMatched
        | _ => .notMatched
termination_by fuel

public def specClassConclusionMatch (env : Environment) (specClass : Name) (targetDefId : String)
    (ty : Expr) (fuel : Nat := 256) : SpecClassMatch :=
  specClassConclusionMatchBudget env specClass targetDefId ty fuel none

/-- Module-reachability filter: indices of imported modules that transitively depend on `targetMod`. -/
def reachingModuleIndices (env : Environment) (targetMod : Name) : Array Nat := Id.run do
  let n := env.header.modules.size
  let mut reach : Std.HashSet Name := ({} : Std.HashSet Name).insert targetMod
  let mut changed := true
  for _ in [0:n + 1] do
    if !changed then break
    changed := false
    for h : i in [0:n] do
      let m := env.header.modules[i].module
      if !reach.contains m then
        let data := env.header.moduleData[i]!
        if data.imports.any (fun imp => reach.contains imp.module) then
          reach := reach.insert m
          changed := true
  let mut idxs : Array Nat := #[]
  for h : i in [0:n] do
    if reach.contains env.header.modules[i].module then
      idxs := idxs.push i
  return idxs

/-- Reverse-BFS over all constants in modules that import `specClass`'s defining module (plus live
local constants in `env.constants.map₂`) to find the sound over-approximation of constants whose
transitive `declEdges` can ever mention `specClass`. Returns `none` on fuel exhaustion so callers
fail closed and inspect every eligible declaration. -/
def constsReachingSpecClass (env : Environment) (specClass : Name) (modIdxs : Array Nat) :
    Option NameSet := Id.run do
  let mut rev : Std.HashMap Name (Array Name) := {}
  let mut total := 0
  let addEdges (ci : ConstantInfo) (r : Std.HashMap Name (Array Name)) :
      Std.HashMap Name (Array Name) :=
    (declEdges ci).foldl (init := r) fun acc dep =>
      acc.insert dep ((acc.getD dep #[]).push ci.name)
  for i in modIdxs do
    for ci in env.header.moduleData[i]!.constants do
      total := total + 1
      rev := addEdges ci rev
  for (_, ci) in env.constants.map₂.toList do
    total := total + 1
    rev := addEdges ci rev
  let mut reach : NameSet := NameSet.empty.insert specClass
  let mut pending : List Name := [specClass]
  let mut done := false
  for _ in [0:total + 64] do
    match pending with
    | [] => done := true; break
    | cur :: rest =>
      pending := rest
      for parent in rev.getD cur #[] do
        unless reach.contains parent do
          reach := reach.insert parent
          pending := parent :: pending
  if done then return some reach else return none

/-- Collect candidate declarations (`.defnInfo`, `.opaqueInfo`, `.axiomInfo`) in modules that can
reach `specClass` (plus live local constants in `env.constants.map₂`), along with the reverse-BFS
`reach?` set, excluding only Lean's compiler-generated `<SpecClass>.mk._flat_ctor` constructor
wrapper in `specClass`'s own defining module and declarations whose type's transitive constant
closure cannot mention `specClass`. -/
def candidateDeclsForSpecClassWithReach (env : Environment) (specClass : Name) :
    Array (Name × ConstantInfo) × Option NameSet := Id.run do
  let specOrigin := origin? env specClass
  let flatCtorName := (specClass.str "mk").str "_flat_ctor"
  let modIdxs := match specOrigin with
    | some targetMod => reachingModuleIndices env targetMod
    | none => #[]
  let reach? := constsReachingSpecClass env specClass modIdxs
  let isEligible (ci : ConstantInfo) : Bool :=
    match ci with
    | .defnInfo _ | .opaqueInfo _ | .axiomInfo _ =>
      if ci.name == flatCtorName && origin? env ci.name == specOrigin then
        false
      else
        match reach? with
        | none => true
        | some reach => ci.type.getUsedConstants.any reach.contains
    | _ => false
  let mut out : Array (Name × ConstantInfo) := #[]
  for i in modIdxs do
    let data := env.header.moduleData[i]!
    for ci in data.constants do
      if isEligible ci then
        out := out.push (ci.name, ci)
  for (n, ci) in env.constants.map₂.toList do
    if isEligible ci then
      out := out.push (n, ci)
  return (out, reach?)

/-- Pure global-linear-budget uniqueness scan for `(specClass, targetDefId)`. -/
public def specInstanceCandidates (env : Environment) (specClass : Name) (targetDefId : String)
    (fuel : Nat := 256) : Array Name := Id.run do
  let (decls, reach?) := candidateDeclsForSpecClassWithReach env specClass
  let mut cands : Array Name := #[]
  let mut seen : NameSet := {}
  for (n, ci) in decls do
    if seen.contains n then continue
    match specClassConclusionMatchBudget env specClass targetDefId ci.type fuel reach? with
    | .matched | .undecided =>
      seen := seen.insert n
      cands := cands.push n
    | .notMatched => pure ()
  return cands.qsort (fun a b => a.toString < b.toString)

/-- `MetaM` uniqueness scan for `(specClass, targetDefId)` running inside `withKernelFaithfulMeta`
with `Meta.withTransparency .all`.

`Meta.whnf` is strictly weaker than the kernel in two measured ways: it never δ-unfolds theorems
(`getUnfoldableConst?` answers `none` for `.thm` at every transparency, so `Acc.rec … thm` is stuck
where the kernel reduces it), and it leaves the result of `Lean.reduceNat` unnormalized (`A4-5b`).
A "not the specification class" answer is therefore believed only when the kernel-faithful pure
normalizer (`specClassConclusionMatchBudget`) is certain of it as well, whatever head `Meta.whnf`
stopped at (including dependent stuck eliminators/projections/variables reaching `specClass`,
`A1-3`). A type whose dependency closure reaches a kernel-native evaluator is never normalized at
all (that would run audited code inside the auditor): it is a candidate. -/
public def specInstanceCandidatesMeta (specClass : Name) (targetDefId : String) (fuel : Nat := 256) :
    MetaM (Array Name) :=
  withKernelFaithfulMeta do
    let env ← getEnv
    let (decls, reach?) := candidateDeclsForSpecClassWithReach env specClass
    let nativeFuel := envConstantCount env + 64
    let (specNative, clean0) := reachesNativeEvaluator env #[specClass] {} nativeFuel
    let specIsProp ← if specNative then pure true else try
        Meta.withTransparency .all (Meta.isProp (mkApp (mkConst specClass []) (mkStrLit targetDefId)))
      catch _ => pure true
    let mut cands : Array Name := #[]
    let mut seen : NameSet := {}
    let mut clean : NameSet := clean0
    for (n, ci) in decls do
      if seen.contains n then continue
      let (native, clean') := reachesNativeEvaluator env ci.type.getUsedConstants clean nativeFuel
      clean := clean'
      let isCand ← if native then pure true else try
          Meta.withTransparency .all do
            if !specIsProp then
              if ← Meta.isProp ci.type then
                return false
            Meta.forallTelescopeReducing ci.type fun _ body => do
              let body ← Meta.whnf body
              let fn := body.getAppFn
              let args := body.getAppArgs
              if fn.isConstOf specClass then
                if args.size == 1 then
                  let arg ← Meta.whnf args[0]!
                  match arg with
                  | .lit (.strVal s) => return s == targetDefId
                  | _ => return true
                else
                  return true
              else
                match specClassConclusionMatchBudget env specClass targetDefId ci.type fuel reach? with
                | .matched | .undecided => return true
                | .notMatched => return false
        catch _ =>
          pure true
      if isCand then
        seen := seen.insert n
        cands := cands.push n
    return cands.qsort (fun a b => a.toString < b.toString)

public inductive ExpectedSpec where
  | direct (req ens : Expr)
  | modular (envAssumed pre post : Expr)

public structure SpecAuditCtx where
  toolchainProv : Std.HashSet Name
  allowedAxioms : Array (String × String)
  trustedOriginMod : Name := trustedVerifModName
  specLibOriginMod : Name := specLibModName
  allowLocalDecls : Bool := false
  useSynthInstance : Bool := false
  budget : Nat := 400

def SpecAuditCtx.forLoaded (L : Loaded) (budget : Nat := 400) : SpecAuditCtx where
  toolchainProv := L.toolchainProv
  allowedAxioms := L.req.axioms
  allowLocalDecls := false
  useSynthInstance := false
  budget := budget

public def SpecAuditCtx.forLiveMeta (env : Environment) (budget : Nat := 400) : SpecAuditCtx := Id.run do
  let mut toolProv : Std.HashSet Name := {}
  for m in env.header.modules do
    if m.module.getRoot == `Init || m.module.getRoot == `Std || m.module.getRoot == `Lean then
      toolProv := toolProv.insert m.module
  return {
    toolchainProv := toolProv
    allowedAxioms := #[("propext", "Init.Core"), ("Quot.sound", "Init.Prelude"), ("Classical.choice", "Init.Prelude")]
    allowLocalDecls := true
    useSynthInstance := true
    budget := budget
  }

def effectiveOrigin? (env : Environment) (ctx : SpecAuditCtx) (n : Name) : Option Name :=
  match origin? env n with
  | some m => some m
  | none => if ctx.allowLocalDecls && (env.find? n).isSome then some env.header.mainModule else none

/-- Build a set of non-toolchain `@[csimp]` target names (both module entries and live state)
for single-declaration closure checks in spec-strength gates. -/
def nonToolchainCSimpTargets (env : Environment) (toolchainProv : Std.HashSet Name) : NameSet := Id.run do
  let mut toolTriples : Std.HashSet (Name × Name × Name) := {}
  let mut bad : NameSet := {}
  for h : i in [0:env.header.modules.size] do
    let m := env.header.modules[i].module
    let isTool := toolchainProv.contains m
    for e in Compiler.CSimp.ext.ext.getModuleEntries env i ++ Compiler.CSimp.ext.ext.getModuleIREntries env i do
      let ent := match e with | .global a => a | .scoped _ a => a
      if isTool then
        toolTriples := toolTriples.insert (ent.fromDeclName, ent.toDeclName, ent.thmName)
      else
        bad := bad.insert ent.fromDeclName
  let st := Compiler.CSimp.ext.ext.getState env
  for frame in st.stateStack do
    for (k, ent) in frame.state.map.toList do
      unless k == ent.fromDeclName && toolTriples.contains (k, ent.toDeclName, ent.thmName) do
        bad := bad.insert k
  for e in st.newEntries do
    let ent := match e with | .global a => a | .scoped _ a => a
    unless toolTriples.contains (ent.fromDeclName, ent.toDeclName, ent.thmName) do
      bad := bad.insert ent.fromDeclName
  for (_, entries) in st.scopedEntries.map.toList do
    for ent in entries.toArray do
      unless toolTriples.contains (ent.fromDeclName, ent.toDeclName, ent.thmName) do
        bad := bad.insert ent.fromDeclName
  return bad

/-- Standalone bounded kernel-dependency audit of `roots` returning a fresh `Array Violation`
(never reusing an outer `seen` set so audit-before-coverage `A1-4` is never masked), plus a
whole-module + live `env.constants.map₂` unreferenced-axiom sweep (`leanprover/lean4#16781`). -/
public def auditDeclsForSpec (env : Environment) (ctx : SpecAuditCtx) (roots : Array Name)
    (constructive : Bool) : Array Violation :=
  (StateT.run (m := Id) (s := (#[], ({} : Std.HashSet (String × Name)))) do
    let addV (tag : String) (decl mod : Name) (detail : String) : StateM (Array Violation × Std.HashSet (String × Name)) Unit :=
      modify fun (vs, sv) => if sv.contains (tag, decl) then (vs, sv) else (vs.push { tag, decl, module := mod, detail }, sv.insert (tag, decl))
    let checkSpecAx (ci : ConstantInfo) (m : Name) : StateM (Array Violation × Std.HashSet (String × Name)) Unit := do
      let n := ci.name; let isTool := ctx.toolchainProv.contains m
      if n == ``sorryAx then addV "sorryAxiomReached" n m "incomplete proof (sorryAx)"
      else if isTool && ctx.allowedAxioms.contains (n.toString, m.toString) && (!constructive || n == ``propext || n == ``Quot.sound) then pure ()
      else if isFoundationalAxiomName n && !isTool then addV "unapprovedAxiom" n m "non-toolchain re-declaration of foundational axiom"
      else if n == ``Classical.choice && constructive then addV "unapprovedAxiom" n m "Classical.choice is forbidden under constructive policy"
      else if nativeBuiltinAxioms.contains n then addV (if isTool then "nativeDecideReached" else "unapprovedAxiom") n m "native evaluation axiom"
      else if hasNativeComponent n then
        let wellFormed := match n with
          | .str _ last =>
            last.startsWith "ax_" && ci.levelParams.isEmpty && ci.type.isAppOfArity ``Eq 3 &&
            (match ci.type.getAppFn with | .const _ [lvl] => lvl == Level.one | _ => false) &&
            ci.type.getAppArgs[0]! == mkConst ``Bool && ci.type.getAppArgs[2]! == mkConst ``Bool.true &&
            ci.type.getAppArgs[1]! != mkConst ``Bool.false && isClosedExpr ci.type.getAppArgs[1]! &&
            ([``Eq, ``Bool, ``Bool.true].all fun c => (origin? env c).any (ctx.toolchainProv.contains ·))
          | _ => false
        addV (if wellFormed then "nativeDecideReached" else "unapprovedAxiom") n m "native_decide axiom"
      else addV "unapprovedAxiom" n m "axiom outside locked policy"
    let badCSimp := nonToolchainCSimpTargets env ctx.toolchainProv
    let fuel := env.header.moduleData.foldl (fun a d => a + d.constants.size) 0 + env.constants.map₂.toList.length + 64
    let mut visited : NameSet := {}; let mut pending : List Name := []; let mut rootMods : NameSet := {}
    for r in roots do
      if let some m := effectiveOrigin? env ctx r then
        if !ctx.toolchainProv.contains m then rootMods := rootMods.insert m
      unless visited.contains r do visited := visited.insert r; pending := r :: pending
    let mut done := false
    for _ in [0:fuel] do
      match pending with
      | [] => done := true; break
      | n :: rest =>
        pending := rest
        let some ci := env.find? n
          | addV "missingDeclaration" n ((effectiveOrigin? env ctx n).getD .anonymous) "dependency not found"; continue
        let some m := effectiveOrigin? env ctx n
          | addV "missingDeclaration" n .anonymous "dependency without module origin"; continue
        let isTool := ctx.toolchainProv.contains m
        if !isTool then rootMods := rootMods.insert m
        unless declIsClosed ci do addV "openExpression" n m "open expression in stored declaration"
        if ci.isUnsafe then addV "unsafeDeclaration" n m "unsafe declaration reached"
        else if ci.isPartial then addV "partialOrUnsafeRecDependency" n m "partial declaration reached"
        if kernelNativeEvaluators.contains n then addV "nativeDecideReached" n m "kernel-native evaluator (Lean.reduceBool / Lean.reduceNat) reached"
        if isShareCommonName env n then addV "shareCommonForbidden" n m "Init.ShareCommon reached"
        if let .opaqueInfo _ := ci then
          if let some sib := env.find? (n.str "_unsafe_rec") then
            if sib.isPartial || sib.isUnsafe then addV "partialOrUnsafeRecDependency" n m "partial def (opaque with _unsafe_rec) reached"
        if !isTool then
          for k in overrideKinds env ctx.toolchainProv n do addV "compilerOverrideAttribute" n m k
        if badCSimp.contains n then addV "compilerOverrideAttribute" n m "csimp_target"
        if ci matches .axiomInfo _ then checkSpecAx ci m
        for d in declEdges ci do
          unless visited.contains d do visited := visited.insert d; pending := d :: pending
    unless done do addV "auditFuelExhausted" (roots.getD 0 .anonymous) .anonymous "spec-strength dependency closure exhausted its fuel"
    -- Vector 2 sweep: declaring modules of `roots` + live `env.constants.map₂` for unreferenced axioms.
    for h : i in [0:env.header.modules.size] do
      let m := env.header.modules[i].module
      if rootMods.contains m then
        for ci in env.header.moduleData[i]!.constants do
          if ci matches .axiomInfo _ then checkSpecAx ci m
    for (n, ci) in env.constants.map₂.toList do
      if ci matches .axiomInfo _ then checkSpecAx ci ((effectiveOrigin? env ctx n).getD env.header.mainModule)).2.1

def parseMutantCategoryExpr? (cat : String) : Option Expr :=
  match cat with
  | "wrongReturn" => some (mkConst (mutantCategoryPrefix.str "wrongReturn"))
  | "wrapOverflow" => some (mkConst (mutantCategoryPrefix.str "wrapOverflow"))
  | "truncatedLength" => some (mkConst (mutantCategoryPrefix.str "truncatedLength"))
  | "swappedByteOrder" => some (mkConst (mutantCategoryPrefix.str "swappedByteOrder"))
  | "offByOneScalar" => some (mkConst (mutantCategoryPrefix.str "offByOneScalar"))
  | "wrongBranchTag" => some (mkConst (mutantCategoryPrefix.str "wrongBranchTag"))
  | "unpreservedFrame" => some (mkConst (mutantCategoryPrefix.str "unpreservedFrame"))
  | _ =>
    if cat.startsWith "custom:" then
      some (mkApp (mkConst (mutantCategoryPrefix.str "custom")) (mkStrLit (cat.drop 7).toString))
    else
      none

def mkUncurryPre (rawPre : Expr) : Expr :=
  let valTy := mkConst mirValueName
  let memTy := mkConst mirMemoryName
  let listValTy := mkApp (mkConst ``List [Level.zero]) valTy
  let inTy := mkApp2 (mkConst ``Prod [Level.zero, Level.zero]) listValTy memTy
  Expr.lam `p inTy
    (mkApp2 rawPre (Expr.proj ``Prod 0 (.bvar 0)) (Expr.proj ``Prod 1 (.bvar 0)))
    .default

def mkUncurryPost (rawPost : Expr) : Expr :=
  let valTy := mkConst mirValueName
  let memTy := mkConst mirMemoryName
  let listValTy := mkApp (mkConst ``List [Level.zero]) valTy
  let inTy := mkApp2 (mkConst ``Prod [Level.zero, Level.zero]) listValTy memTy
  let outTy := mkApp2 (mkConst ``Prod [Level.zero, Level.zero]) valTy memTy
  Expr.lam `p inTy
    (Expr.lam `q outTy
      (mkApp4 rawPost
        (Expr.proj ``Prod 0 (.bvar 1)) (Expr.proj ``Prod 1 (.bvar 1))
        (Expr.proj ``Prod 0 (.bvar 0)) (Expr.proj ``Prod 1 (.bvar 0)))
      .default)
    .default

def directCertHeads : Array Name := #[
  certSpecStrengthName, certMultiMutantName, certDeterministicName, certInputSensitiveName]

def modularCertHeads : Array Name := #[
  certModularSpecStrengthName, certModularMultiMutantName,
  certModularDeterministicName, certModularInputSensitiveName]

def typeLevelOf? (ty : Expr) : MetaM (Option Level) := do
  let lvl ← Meta.getLevel ty
  match lvl.normalize with
  | .succ u => return some u
  | _ => return none

/-- Direct cert-bound spec-strength gate (`R6`, `R8`, `A1-4`, `A3-3a/b/d`, `B4-5`, `W6`):
1. Resolves caller-assigned mvars (`instantiateMVars`) and requires all expected expressions to be
   closed (`isClosedExpr`, rejecting unassigned mvars/fvars/loose bvars as `specStrengthCertInvalidType`).
2. Audits `certName` under **constructive** policy (`[propext, Quot.sound]`, zero `Classical.choice`,
   zero `sorryAx`, zero overrides/unsafe/partial) **BEFORE** evaluating `coversCategory` (`A1-4`).
3. Checks certificate head provenance (`Anneal.OleanSpecStrengthAuditor`), required tier flags, and
   confirms `certName : boundTy` directly in Lean's kernel (`kernelConfirmsHasType`, `A3-3a/d`).
4. For each `cat ∈ requiredCategories`, checks `coversCategory cert cat` under `withKernelFaithfulMeta`
   and confirms `coversCategory cert cat = Bool.true` directly in Lean's kernel (`A3-3b`). -/
def auditSpecStrengthCertCore (ctx : SpecAuditCtx) (certName : Name) (expected : ExpectedSpec)
    (requiredCategories : Array String := #[])
    (requireDeterministic : Bool := false)
    (requireInputSensitive : Bool := false) : MetaM (Array Violation) := do
  -- Substitute caller-assigned metavariables BEFORE entering `withNewMCtxDepth` (`W6`), then
  -- verify strict closedness (`B4-5`).
  let expectedInst ← match expected with
    | .direct req ens =>
      pure (ExpectedSpec.direct (← instantiateMVars req) (← instantiateMVars ens))
    | .modular envA pre post =>
      pure (ExpectedSpec.modular (← instantiateMVars envA) (← instantiateMVars pre) (← instantiateMVars post))
  withKernelFaithfulMeta (heartbeats := max (ctx.budget * 1000) 400000) do
    let env ← getEnv
    let certMod := (effectiveOrigin? env ctx certName).getD .anonymous
    let singleV (tag : String) (detail : String) : Array Violation :=
      #[{ tag, decl := certName, module := certMod, detail }]
    -- Step 1: closedness & native-evaluator pre-pass on expected specification expressions (`B4-5`, `A1-2a`).
    let expectedClosed := match expectedInst with
      | .direct req ens => isClosedExpr req && isClosedExpr ens
      | .modular envA pre post => isClosedExpr envA && isClosedExpr pre && isClosedExpr post
    unless expectedClosed do
      return singleV "specStrengthCertInvalidType"
        "expected specification expression is not closed (contains fvar, mvar, level mvar, or loose bvar)"
    let expectedConsts : Array Name := match expectedInst with
      | .direct req ens => req.getUsedConstants ++ ens.getUsedConstants
      | .modular envA pre post => envA.getUsedConstants ++ pre.getUsedConstants ++ post.getUsedConstants
    let (expNative, _) := reachesNativeEvaluator env expectedConsts {} (envConstantCount env + 64)
    if expNative then
      return singleV "nativeDecideReached"
        "kernel-native evaluator (Lean.reduceBool / Lean.reduceNat) reachable from expected specification expression"
    -- Step 2: existence & constructive audit BEFORE coverage (`A1-4`).
    let some certCi := env.find? certName
      | return singleV "specStrengthCertMissing" s!"spec-strength certificate {certName} not found"
    let certViolations := auditDeclsForSpec env ctx #[certName] (constructive := true)
    if !certViolations.isEmpty then
      return certViolations
    unless certCi.levelParams.isEmpty do
      return singleV "specStrengthCertInvalidType"
        s!"spec-strength certificate {certName} must be monomorphic (got universe params {certCi.levelParams})"
    -- Step 3: verify head type provenance and confirm binding in Lean's kernel (`A3-3a/d`).
    let certTy ← try Meta.withTransparency .all (Meta.whnf certCi.type) catch _ => pure certCi.type
    let .const headName _ := certTy.getAppFn
      | return singleV "specStrengthCertInvalidType"
          s!"certificate {certName} type does not reduce to a recognized certificate head"
    unless origin? env headName == some ctx.specLibOriginMod do
      return singleV "specStrengthCertInvalidType"
        s!"certificate head {headName} does not originate from {ctx.specLibOriginMod}"
    match expectedInst with
    | .direct req ens =>
      unless directCertHeads.contains headName do
        return singleV "specStrengthCertInvalidType"
          s!"expected direct certificate head, got {headName}"
      if requireDeterministic && headName != certDeterministicName then
        return singleV "specStrengthCertInvalidType"
          s!"deterministic certificate required, got {headName}"
      if requireInputSensitive && headName != certInputSensitiveName then
        return singleV "specStrengthCertInvalidType"
          s!"input-sensitive certificate required, got {headName}"
      if !requiredCategories.isEmpty && headName != certMultiMutantName then
        return singleV "specStrengthCoverageGap"
          s!"required mutant categories {requiredCategories} need MultiMutantSpecCert, got {headName}"
      let αβ? ← try
          Meta.withTransparency .all do
            let reqTy ← Meta.whnf (← Meta.inferType req)
            let ensTy ← Meta.whnf (← Meta.inferType ens)
            match reqTy, ensTy with
            | .forallE _ α _ _, .forallE _ _ ensCod _ =>
              let ensCod' ← Meta.whnf ensCod
              match ensCod' with
              | .forallE _ β _ _ =>
                let α ← instantiateMVars α
                let β ← instantiateMVars β
                if !isClosedExpr α || !isClosedExpr β then return none
                let some u ← typeLevelOf? α | return none
                let some v ← typeLevelOf? β | return none
                return some (α, β, u, v)
              | _ => return none
            | _, _ => return none
        catch _ => pure none
      let some (α, β, u, v) := αβ?
        | return singleV "specStrengthCertInvalidType"
            "cannot infer closed domain/codomain types from expected (req, ens)"
      let boundTy := mkApp4 (mkConst headName [u, v]) α β req ens
      let metaOk ← try Meta.withTransparency .all (Meta.isDefEq certTy boundTy) catch _ => pure false
      unless metaOk do
        return singleV "specStrengthCertInvalidType"
          s!"certificate {certName} does not match expected specification"
      let kernOk ← liftM (m := IO) (kernelConfirmsHasType env (mkConst certName []) boundTy ctx.budget)
      unless kernOk do
        return singleV "specStrengthCertInvalidType"
          s!"kernel rejected certificate binding for {certName}"
      -- Step 4: verify required mutant categories in Lean's kernel (`R8`, `A3-3b`).
      if !requiredCategories.isEmpty then
        unless origin? env directCoversCategoryName == some ctx.specLibOriginMod &&
            [``Eq, ``Bool, ``Bool.true].all (fun c => (origin? env c).any (ctx.toolchainProv.contains ·)) do
          return singleV "specStrengthCoverageGap" "coversCategory or Bool/Eq provenance check failed"
        let mut missing : Array String := #[]
        for catStr in requiredCategories do
          match parseMutantCategoryExpr? catStr with
          | none => missing := missing.push catStr
          | some catExpr =>
            let covExpr := mkApp6 (mkConst directCoversCategoryName [u, v]) α β req ens (mkConst certName []) catExpr
            let metaTrue ← try
                let v ← Meta.withTransparency .all (Meta.whnf covExpr)
                pure (v == mkConst ``Bool.true)
              catch _ => pure false
            let kernTrue ← if metaTrue then
                liftM (m := IO) (kernelConfirmsBoolTrue env covExpr ctx.budget)
              else pure false
            unless kernTrue do
              missing := missing.push catStr
        if !missing.isEmpty then
          return singleV "specStrengthCoverageGap"
            s!"certificate {certName} missing required mutant categories: {missing}"
      return #[]
    | .modular envA pre post =>
      unless modularCertHeads.contains headName do
        return singleV "specStrengthCertInvalidType"
          s!"expected modular certificate head, got {headName}"
      if requireDeterministic && headName != certModularDeterministicName then
        return singleV "specStrengthCertInvalidType"
          s!"modular deterministic certificate required, got {headName}"
      if requireInputSensitive && headName != certModularInputSensitiveName then
        return singleV "specStrengthCertInvalidType"
          s!"modular input-sensitive certificate required, got {headName}"
      if !requiredCategories.isEmpty && headName != certModularMultiMutantName then
        return singleV "specStrengthCoverageGap"
          s!"required mutant categories {requiredCategories} need ModularMultiMutantSpecCert, got {headName}"
      let boundTy := mkApp3 (mkConst headName []) envA pre post
      let metaOk ← try Meta.withTransparency .all (Meta.isDefEq certTy boundTy) catch _ => pure false
      unless metaOk do
        return singleV "specStrengthCertInvalidType"
          s!"modular certificate {certName} does not match expected (envAssumed, pre, post)"
      let kernOk ← liftM (m := IO) (kernelConfirmsHasType env (mkConst certName []) boundTy ctx.budget)
      unless kernOk do
        return singleV "specStrengthCertInvalidType"
          s!"kernel rejected modular certificate binding for {certName}"
      if !requiredCategories.isEmpty then
        unless origin? env modularCoversCategoryName == some ctx.specLibOriginMod &&
            [``Eq, ``Bool, ``Bool.true].all (fun c => (origin? env c).any (ctx.toolchainProv.contains ·)) do
          return singleV "specStrengthCoverageGap" "modular coversCategory or Bool/Eq provenance check failed"
        let mut missing : Array String := #[]
        for catStr in requiredCategories do
          match parseMutantCategoryExpr? catStr with
          | none => missing := missing.push catStr
          | some catExpr =>
            let covExpr := mkApp5 (mkConst modularCoversCategoryName []) envA pre post (mkConst certName []) catExpr
            let metaTrue ← try
                let v ← Meta.withTransparency .all (Meta.whnf covExpr)
                pure (v == mkConst ``Bool.true)
              catch _ => pure false
            let kernTrue ← if metaTrue then
                liftM (m := IO) (kernelConfirmsBoolTrue env covExpr ctx.budget)
              else pure false
            unless kernTrue do
              missing := missing.push catStr
        if !missing.isEmpty then
          return singleV "specStrengthCoverageGap"
            s!"modular certificate {certName} missing required mutant categories: {missing}"
      return #[]

/-- Live `MetaM` convenience wrapper for `auditSpecStrengthCertCore`. -/
public def auditSpecStrengthCert (certName : Name) (expected : ExpectedSpec)
    (requiredCategories : Array String := #[])
    (requireDeterministic : Bool := false)
    (requireInputSensitive : Bool := false)
    (budget : Nat := 400) : MetaM (Array Violation) := do
  let ctx := SpecAuditCtx.forLiveMeta (← getEnv) budget
  auditSpecStrengthCertCore ctx certName expected requiredCategories requireDeterministic requireInputSensitive

/-- Claim-bound spec-strength gate (`R11`, `A1-6`, `A2-4b`, `A3-3a/e`):
requires `thmName` to be a `.thmInfo` (`requireClaimTheorem := true`), audits `thmName` under
strict standard policy, extracts `(envAssumed,) pre, post` from `VerificationResult` /
`StatefulVerificationResult` / `TotalVerificationResult` / `ModularVerificationResult`
(provenance-verified + kernel-confirmed via `kernelConfirmsHasType`), and validates `certName`
against the exact extracted contract under constructive policy. -/
def auditClaimSpecStrengthCore (ctx : SpecAuditCtx) (thmName certName : Name)
    (requiredCategories : Array String := #[])
    (requireDeterministic : Bool := false)
    (requireInputSensitive : Bool := false) : MetaM (Array Violation) :=
  withKernelFaithfulMeta (heartbeats := max (ctx.budget * 1000) 400000) do
    let env ← getEnv
    let thmMod := (effectiveOrigin? env ctx thmName).getD .anonymous
    let singleV (tag : String) (detail : String) : Array Violation :=
      #[{ tag, decl := thmName, module := thmMod, detail }]
    let some thmCi := env.find? thmName
      | return singleV "missingDeclaration" s!"claim declaration {thmName} not found"
    unless thmCi matches .thmInfo _ do
      return singleV "specStrengthCertInvalidType"
        s!"claim {thmName} must be a theorem (.thmInfo), got {kindOf thmCi}"
    -- Audit the claim theorem BEFORE structural/levelParam checks (`A1-2b`, mirroring `B1-6`),
    -- so a universe-polymorphic `sorry`/axiom/native claim is never masked as `specStrengthCertInvalidType`.
    let thmViolations := auditDeclsForSpec env ctx #[thmName] (constructive := false)
    if !thmViolations.isEmpty then
      return thmViolations
    unless thmCi.levelParams.isEmpty do
      return singleV "specStrengthCertInvalidType"
        s!"claim theorem {thmName} must be monomorphic"
    let thmTy ← try Meta.withTransparency .all (Meta.whnf thmCi.type) catch _ => pure thmCi.type
    let .const headName [] := thmTy.getAppFn
      | return singleV "specStrengthCertInvalidType"
          s!"claim {thmName} type does not reduce to a recognized VerificationResult head"
    let args := thmTy.getAppArgs
    unless args.size == 1 do
      return singleV "specStrengthCertInvalidType"
        s!"claim {thmName} head {headName} expected 1 argument, got {args.size}"
    unless origin? env headName == some ctx.trustedOriginMod do
      return singleV "specStrengthCertInvalidType"
        s!"claim head {headName} does not originate from {ctx.trustedOriginMod}"
    let c ← instantiateMVars args[0]!
    unless isClosedExpr c do
      return singleV "specStrengthCertInvalidType"
        s!"extracted claim argument of {thmName} is not closed"
    -- Kernel confirmation that `thmName` genuinely has type `headName c` (`A3-3e`).
    let claimKernOk ← liftM (m := IO)
      (kernelConfirmsHasType env (mkConst thmName []) (mkApp (mkConst headName []) c) ctx.budget)
    unless claimKernOk do
      return singleV "specStrengthCertInvalidType"
        s!"kernel rejected claim type {headName} for {thmName}"
    let expected? : Option ExpectedSpec :=
      if headName == claimVerificationResultName then
        let pre := mkApp (mkConst `Trusted.VerificationResult.Claim.pre) c
        let post := mkApp (mkConst `Trusted.VerificationResult.Claim.post) c
        some (.direct pre post)
      else if headName == claimStatefulVerificationResultName then
        let rawPre := mkApp (mkConst `Trusted.VerificationResult.StatefulClaim.pre) c
        let rawPost := mkApp (mkConst `Trusted.VerificationResult.StatefulClaim.post) c
        some (.direct (mkUncurryPre rawPre) (mkUncurryPost rawPost))
      else if headName == claimTotalVerificationResultName then
        let rawPre := mkApp (mkConst `Trusted.VerificationResult.TotalClaim.pre) c
        let rawPost := mkApp (mkConst `Trusted.VerificationResult.TotalClaim.post) c
        some (.direct (mkUncurryPre rawPre) (mkUncurryPost rawPost))
      else if headName == claimModularVerificationResultName then
        let envA := mkApp (mkConst `Trusted.VerificationResult.ModularClaim.envAssumed) c
        let pre := mkApp (mkConst `Trusted.VerificationResult.ModularClaim.pre) c
        let post := mkApp (mkConst `Trusted.VerificationResult.ModularClaim.post) c
        some (.modular envA pre post)
      else
        none
    let some expected := expected?
      | return singleV "specStrengthCertInvalidType"
          s!"unsupported claim head {headName} on {thmName}"
    auditSpecStrengthCertCore ctx certName expected requiredCategories requireDeterministic requireInputSensitive

/-- Live `MetaM` convenience wrapper for `auditClaimSpecStrengthCore`. -/
public def auditClaimSpecStrength (thmName certName : Name)
    (requiredCategories : Array String := #[])
    (requireDeterministic : Bool := false)
    (requireInputSensitive : Bool := false)
    (budget : Nat := 400) : MetaM (Array Violation) := do
  let ctx := SpecAuditCtx.forLiveMeta (← getEnv) budget
  auditClaimSpecStrengthCore ctx thmName certName requiredCategories requireDeterministic requireInputSensitive

/-- Whether a `Meta.DiscrTree` key path stored in a `Meta.instanceExtension` entry could match
a typeclass lookup for `specClass targetDefId` (`A2-1`). -/
def keysCanMatchSpecClass (keys : Array Meta.DiscrTree.Key) (specClass : Name)
    (targetDefId : String) : Bool :=
  match keys.toList with
  | [] => true
  | .star :: _ | .other :: _ => true
  | .const c _ :: rest =>
    if c != specClass then false
    else
      match rest with
      | .lit (.strVal s) :: _ => s == targetDefId
      | _ => true
  | _ => false

/-- Total fold over all values stored in a `Meta.DiscrTree`. -/
def discrTreeFold {α σ : Type} (f : σ → α → σ) (init : σ) (d : Meta.DiscrTree α) : σ :=
  let rec goTrie (acc : σ) (t : Meta.DiscrTree.Trie α) : σ :=
    match t with
    | .node vs children =>
      let acc := vs.foldl f acc
      children.attach.foldl (fun a ⟨(_, child), hmem⟩ =>
        have : sizeOf child < 1 + sizeOf vs + sizeOf children := by
          have h1 := Array.sizeOf_lt_of_mem hmem
          simp only [Prod.mk.sizeOf_spec] at h1
          omega
        goTrie a child) acc
  termination_by sizeOf t
  d.root.foldl (fun acc _ trie => goTrie acc trie) init

/-- Check whether `declName` is registered as an active, exported `.global` zero-argument
`@[instance]` keyed for `specClass targetDefId` (`A1-6`, `A2-2`, `A2-7`, `A3-1`).
In a `module` file, `Meta.instanceExtension`'s `exportEntry?` withholds any entry with
`isPrivateName declName` from `.olean` (`exported := none`), so `module` importers cannot
synthesize it; reject unexported private instances in `module` files here as well. -/
def isGlobalInstanceRegistered (env : Environment) (declName specClass : Name)
    (targetDefId : String) (allowLocalDecls : Bool := false) : Bool := Id.run do
  let target := mkConst declName []
  let expectedKeys : Array Meta.DiscrTree.Key := #[.const specClass 1, .lit (.strVal targetDefId)]
  let matchesEntry (ent : Meta.InstanceEntry) : Bool :=
    ent.attrKind == .global && ent.val == target && ent.globalName? == some declName &&
      ent.synthOrder.isEmpty && ent.keys == expectedKeys
  if allowLocalDecls then
    if (Meta.instanceExtension.getState env).erased.contains declName then
      return false
    if !(env.header.isModule && isPrivateName declName) then
      for e in (Meta.instanceExtension.ext.getState env).newEntries do
        match e with
        | .global ent => if matchesEntry ent then return true
        | .scoped _ _ => pure ()
  for i in [0:env.header.modules.size] do
    if env.header.moduleData[i]!.isModule && isPrivateName declName then
      continue
    for e in Meta.instanceExtension.ext.getModuleEntries env i do
      match e with
      | .global ent => if matchesEntry ent then return true
      | .scoped _ _ => pure ()
  return false

/-- Collect non-toolchain (or `specClass`-key-matching) `Meta.InstanceEntry` records across
serialized non-toolchain modules plus live `newEntries`, `scopedEntries`, and `stateStack`
(capturing `.local` forged instances in live `MetaM`, `A2-3`). -/
def collectRelevantInstanceEntries (env : Environment) (toolchainProv : Std.HashSet Name)
    (specClass : Name) (targetDefId : String) : Array Meta.InstanceEntry := Id.run do
  let mut entries : Array Meta.InstanceEntry := #[]
  for h : i in [0:env.header.modules.size] do
    if toolchainProv.contains env.header.modules[i].module then continue
    for e in Meta.instanceExtension.ext.getModuleEntries env i do
      entries := entries.push (match e with | .global a => a | .scoped _ a => a)
  let st := Meta.instanceExtension.ext.getState env
  let isToolchainVal (ent : Meta.InstanceEntry) : Bool :=
    match ent.val with
    | .const n _ => (origin? env n).any toolchainProv.contains
    | _ => false
  for e in st.newEntries do
    entries := entries.push (match e with | .global a => a | .scoped _ a => a)
  for (_, es) in st.scopedEntries.map.toList do
    for ent in es.toArray do
      if keysCanMatchSpecClass ent.keys specClass targetDefId || !isToolchainVal ent then
        entries := entries.push ent
  for frame in st.stateStack do
    entries := discrTreeFold (init := entries) (fun acc ent =>
      if keysCanMatchSpecClass ent.keys specClass targetDefId || !isToolchainVal ent then
        acc.push ent
      else acc) frame.state.discrTree
  return entries

/-- Collect non-toolchain `Meta.DefaultInstanceEntry` records from serialized non-toolchain modules
and live `defaultInstanceExtension` state (`A2-6`, `A3-2`). -/
def collectRelevantDefaultInstances (env : Environment) (toolchainProv : Std.HashSet Name) :
    Array Name := Id.run do
  let mut toolDefInsts : Std.HashSet (Name × Name) := {}
  let mut out : Array Name := #[]
  for h : i in [0:env.header.modules.size] do
    let m := env.header.modules[i].module
    let isTool := toolchainProv.contains m
    for d in Meta.defaultInstanceExtension.getModuleEntries env i do
      if isTool then
        toolDefInsts := toolDefInsts.insert (d.className, d.instanceName)
      else if !out.contains d.instanceName then
        out := out.push d.instanceName
  let liveMap := (Meta.defaultInstanceExtension.getState env).defaultInstances
  for (clsName, defs) in liveMap.toList do
    for (instName, _) in defs do
      unless toolDefInsts.contains (clsName, instName) do
        if !out.contains instName then
          out := out.push instName
  return out

/-- Registered-instance scan (`B2-1`, `A2-1`, `A2-3`, `A2-6`). Type class resolution retrieves an
instance through the discrimination-tree `keys` stored in its `Meta.instanceExtension` entry (or via
`Meta.defaultInstanceExtension`) and then unifies the goal with the *declared type of the entry's
constant*; the keys need not describe that type. A metaprogram can store an entry directly
(`instanceExtension.add`), bypassing `addInstance`'s "return type is a class" check, so an entry
whose constant concludes in a variable (`T`), stuck projection (`c.ty`), or stuck eliminator
(`Bool.rec _ s.a s.b s.tag`) keyed like `ItemSpec d` makes resolution of `ItemSpec d` return a weak
specification no declaration-type scan sees. Every relevant registered entry (global, scoped, local
in `stateStack`, or default instance) is therefore a candidate if either its `keys` can match
`specClass targetDefId` or the pure normalizer is not certain its conclusion is unrelated (with
variable, projection, and eliminator conclusions always candidates); an entry whose value is not a
constant, or names a missing constant, is a candidate as well. -/
public def instanceEntryCandidates (env : Environment) (toolchainProv : Std.HashSet Name)
    (specClass : Name) (targetDefId : String) (fuel : Nat := 256) : Array Name := Id.run do
  let entries := collectRelevantInstanceEntries env toolchainProv specClass targetDefId
  let mut out : Array Name := #[]
  for ent in entries do
    let label := match ent.val with
      | .const n _ => n
      | _ => (ent.globalName?.getD `_forged_instance_entry).str "_non_constant_instance_value"
    let isCand :=
      keysCanMatchSpecClass ent.keys specClass targetDefId ||
      match ent.val with
      | .const n _ =>
        match env.find? n with
        | some ci =>
          match specClassConclusionMatchBudget env specClass targetDefId ci.type fuel none
              (varHeadIsCandidate := true) with
          | .notMatched => false
          | _ => true
        | none => true
      | _ => true
    if isCand && !out.contains label then
      out := out.push label
  for instName in collectRelevantDefaultInstances env toolchainProv do
    let isCand := match env.find? instName with
      | some ci =>
        match specClassConclusionMatchBudget env specClass targetDefId ci.type fuel none
            (varHeadIsCandidate := true) with
        | .notMatched => false
        | _ => true
      | none => true
    if isCand && !out.contains instName then
      out := out.push instName
  return out

/-- Whether any relevant registered `Meta.instanceExtension` or `Meta.defaultInstanceExtension`
entry transitively reaches a kernel-native evaluator (`A2-5`), checked before calling
`Meta.synthInstance?` in live `MetaM`. -/
def instanceEntriesReachNative (env : Environment) (toolchainProv : Std.HashSet Name)
    (specClass : Name) (targetDefId : String) : Bool := Id.run do
  let mut roots : Array Name := #[]
  let mut seen : NameSet := {}
  for ent in collectRelevantInstanceEntries env toolchainProv specClass targetDefId do
    for c in ent.val.getUsedConstants do
      unless seen.contains c do
        seen := seen.insert c
        roots := roots.push c
  for instName in collectRelevantDefaultInstances env toolchainProv do
    unless seen.contains instName do
      seen := seen.insert instName
      roots := roots.push instName
  (reachesNativeEvaluator env roots {} (envConstantCount env + 64)).1

/-- Unique-instance synthesis spec-strength gate (`R7`, `A1-2`, `S3a/b`, `B4-3/4/6`, `A3-3c`,
`A4-3`, `A4-5`, `A4-7`):
requires a globally unique candidate for `(specClass, defId)` across BOTH pure linear-budget
`specInstanceCandidates` and kernel-faithful `specInstanceCandidatesMeta`, requires the resolved
instance to be that bare zero-argument constant (rejecting instance chains `S3a/b`) and registered
as a global typeclass `@[instance]` (`A1-6`), confirms `soleCand : specClass defId` in Lean's
kernel, and audits `certName` against its contract. -/
def auditItemSpecStrengthBySynthCore (ctx : SpecAuditCtx) (kind : SpecClassKind)
    (defId : String) (certName : Name)
    (requiredCategories : Array String := #[])
    (requireDeterministic : Bool := false)
    (requireInputSensitive : Bool := false) : MetaM (Array Violation) :=
  withKernelFaithfulMeta (heartbeats := max (ctx.budget * 1000) 400000) do
    let env ← getEnv
    let specClass := kind.className
    let certMod := (effectiveOrigin? env ctx certName).getD .anonymous
    let singleV (tag : String) (decl : Name) (detail : String) : Array Violation :=
      #[{ tag, decl, module := certMod, detail }]
    unless origin? env specClass == some ctx.trustedOriginMod do
      return singleV "specStrengthCertInvalidType" specClass
        s!"spec class {specClass} does not originate from {ctx.trustedOriginMod}"
    let pureCands := specInstanceCandidates env specClass defId 256
    let metaCands ← specInstanceCandidatesMeta specClass defId 256
    let entryCands := instanceEntryCandidates env ctx.toolchainProv specClass defId 256
    let mut unionSet : NameSet := {}
    let mut allCands : Array Name := #[]
    for c in pureCands ++ metaCands ++ entryCands do
      unless unionSet.contains c do
        unionSet := unionSet.insert c
        allCands := allCands.push c
    allCands := allCands.qsort (fun a b => a.toString < b.toString)
    if allCands.isEmpty then
      return singleV "specStrengthCertMissing" certName
        s!"no {specClass} instance candidate found for {defId}"
    if allCands.size > 1 then
      return singleV "specInstanceAmbiguous" certName
        s!"multiple {specClass} instance candidates for {defId}: {allCands}"
    let soleCand := allCands[0]!
    -- The specification instance is audited (standard policy) before anything unfolds it: an
    -- instance built from `sorryAx`, an unapproved axiom, or a kernel-native evaluator is rejected
    -- here, never normalized or type checked.
    let instViolations := auditDeclsForSpec env ctx #[soleCand] (constructive := false)
    if !instViolations.isEmpty then
      return instViolations
    let expectedInstTy := mkApp (mkConst specClass []) (mkStrLit defId)
    -- Always confirm in Lean's kernel that the bare constant `soleCand` has type `specClass defId`
    -- (rejects parameterized instance-chain functions `S3a/b` as `specInstanceAmbiguous` before
    -- checking global `@[instance]` registration).
    let instKernOk ← liftM (m := IO)
      (kernelConfirmsHasType env (mkConst soleCand []) expectedInstTy ctx.budget)
    unless instKernOk do
      return singleV "specInstanceAmbiguous" soleCand
        s!"unique candidate {soleCand} is not a bare zero-argument constant of type {specClass} \"{defId}\""
    if ctx.useSynthInstance then
      if instanceEntriesReachNative env ctx.toolchainProv specClass defId then
        return singleV "nativeDecideReached" soleCand
          "kernel-native evaluator (Lean.reduceBool / Lean.reduceNat) reachable from a registered instance entry"
      let synth? ← try Meta.synthInstance? expectedInstTy catch _ => pure none
      match synth? with
      | none =>
        return singleV "specStrengthCertMissing" soleCand
          s!"typeclass synthesis failed for {specClass} \"{defId}\" (sole candidate {soleCand})"
      | some instExpr =>
        let instExpr ← instantiateMVars instExpr
        unless isClosedExpr instExpr do
          return singleV "specInstanceAmbiguous" soleCand
            s!"synthesized instance for {specClass} \"{defId}\" is not closed"
        match instExpr with
        | .const synthName [] =>
          unless synthName == soleCand do
            return singleV "specInstanceAmbiguous" synthName
              s!"synthesized instance {synthName} differs from unique candidate {soleCand}"
        | _ =>
          return singleV "specInstanceAmbiguous" soleCand
            s!"synthesized instance for {specClass} \"{defId}\" is not a bare zero-argument constant (instance chain rejected)"
    else
      -- Confirm `soleCand` is actually registered as an active `.global` zero-argument `@[instance]`
      -- keyed for `specClass defId` so a plain non-instance `def`, forged wrong-key entry, or
      -- erased instance cannot pass `itemSynth` (`A1-6`, `A2-2`, `A2-7`).
      unless isGlobalInstanceRegistered env soleCand specClass defId ctx.allowLocalDecls do
        return singleV "specStrengthCertMissing" soleCand
          s!"sole candidate {soleCand} for {specClass} \"{defId}\" is not registered as a global @[instance] keyed for {specClass} \"{defId}\""
    let instConst := mkConst soleCand []
    let defLit := mkStrLit defId
    let expected : ExpectedSpec := match kind with
      | .item =>
        let pre := mkApp2 (mkConst `Trusted.VerificationResult.ItemSpec.pre) defLit instConst
        let post := mkApp2 (mkConst `Trusted.VerificationResult.ItemSpec.post) defLit instConst
        .direct pre post
      | .statefulItem =>
        let rawPre := mkApp2 (mkConst `Trusted.VerificationResult.StatefulItemSpec.pre) defLit instConst
        let rawPost := mkApp2 (mkConst `Trusted.VerificationResult.StatefulItemSpec.post) defLit instConst
        .direct (mkUncurryPre rawPre) (mkUncurryPost rawPost)
      | .totalItem =>
        let rawPre := mkApp2 (mkConst `Trusted.VerificationResult.TotalItemSpec.pre) defLit instConst
        let rawPost := mkApp2 (mkConst `Trusted.VerificationResult.TotalItemSpec.post) defLit instConst
        .direct (mkUncurryPre rawPre) (mkUncurryPost rawPost)
      | .modularItem =>
        let envA := mkApp2 (mkConst `Trusted.VerificationResult.ModularItemSpec.envAssumed) defLit instConst
        let pre := mkApp2 (mkConst `Trusted.VerificationResult.ModularItemSpec.pre) defLit instConst
        let post := mkApp2 (mkConst `Trusted.VerificationResult.ModularItemSpec.post) defLit instConst
        .modular envA pre post
    auditSpecStrengthCertCore ctx certName expected requiredCategories requireDeterministic requireInputSensitive

/-- Live `MetaM` convenience wrapper for `auditItemSpecStrengthBySynthCore`. -/
public def auditItemSpecStrengthBySynth (kind : SpecClassKind) (defId : String) (certName : Name)
    (requiredCategories : Array String := #[])
    (requireDeterministic : Bool := false)
    (requireInputSensitive : Bool := false)
    (useSynthInstance : Bool := true)
    (budget : Nat := 400) : MetaM (Array Violation) := do
  let ctx := { SpecAuditCtx.forLiveMeta (← getEnv) budget with useSynthInstance }
  auditItemSpecStrengthBySynthCore ctx kind defId certName requiredCategories requireDeterministic requireInputSensitive

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

/-- Non-blocking `leanprover/lean4#14896` readiness check: does `e` place a theorem constant in a
δ-reducible recursor/quotient major-premise or `.proj` scrutinee position? Total, fuel-bounded. -/
def exprUsesOpaqueTheorem (env : Environment) (e : Expr) (fuel : Nat := 100000) : Bool := Id.run do
  let headIsThm (x : Expr) : Bool :=
    match x.getAppFn with | .const c _ => (env.find? c matches some (.thmInfo _)) | _ => false
  let mut seen : Std.HashSet Expr := {}; let mut stack : List Expr := [e]
  for _ in [0:fuel] do
    match stack with
    | [] => return false
    | x :: rest =>
      stack := rest
      if seen.contains x then continue
      seen := seen.insert x
      match x with
      | .proj _ _ s => if headIsThm s then return true else stack := s :: stack
      | .app f a =>
        if let .const c _ := x.getAppFn then
          let args := x.getAppArgs
          match env.find? c with
          | some (.recInfo rv) => if h : rv.getMajorIdx < args.size then if headIsThm args[rv.getMajorIdx] then return true
          | some (.quotInfo qv) =>
            let mi := match qv.kind with | .lift => 5 | .ind => 4 | _ => args.size
            if h : mi < args.size then if headIsThm args[mi] then return true
          | _ => pure ()
        stack := f :: a :: stack
      | .lam _ t b _ | .forallE _ t b _ => stack := t :: b :: stack
      | .letE _ t v b _ => stack := t :: v :: b :: stack
      | .mdata _ b => stack := b :: stack
      | _ => pure ()
  return false

/-- Provenance, inventory, policy and replay checks over one loaded environment. -/
def auditCore (req : Request) (env : Environment) (libDir : System.FilePath)
    (artMap : Std.HashMap Name (Array System.FilePath × Array System.FilePath))
    (modIdx : Std.HashMap Name Nat) (preloaded : Nat) (toolchainNames : Std.HashSet Name) :
    AuditM (Loaded × Nat × Nat × Bool × Nat) := do
  -- Provenance of every loaded module, including `Lean.findOLean` root containment for toolchain modules.
  let mut toolchainProv : Std.HashSet Name := {}
  let mut nonToolchain : Array Name := #[]
  let mut partsChecked := preloaded
  for h : idx in [0:env.header.modules.size] do
    let mod := env.header.modules[idx].module
    let data := env.header.moduleData[idx]!
    let tool := isToolchainName req.toolchainRoots mod
    let base := (libDir / modRelPath mod)
    if tool then
      let found? ← (show IO (Option System.FilePath) from do try pure (some (← Lean.findOLean mod)) catch _ => pure none)
      match found? with
      | some found =>
        let expectedOlean : System.FilePath := ⟨base.toString ++ ".olean"⟩
        unless found == expectedOlean && pathWithinRoot libDir found && (← checkCanonicalPart mod found) do
          report "moduleProvenanceSpoofed" mod mod s!"Lean.findOLean resolved {mod} to {found} outside {libDir}"
      | none => report "moduleProvenanceSpoofed" mod mod s!"Lean.findOLean failed for toolchain module {mod}"
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
  -- Kernel-native evaluators: decide once, before anything is type checked or normalized,
  -- whether in-process kernel / `MetaM` evaluation is safe on this environment. Seed directly
  -- from `declEdges ci` of EVERY stored declaration in every non-toolchain module (not only
  -- `env.find? ci.name`), so shadowed duplicate reserved-theorem copies cannot bypass `B1-4` (`A1-1`).
  let mut nativeRoots : Array Name := #[]
  let mut nativeRootSet : NameSet := {}
  for m in nonToolchain do
    if let some i := modIdx[m]? then
      for ci in env.header.moduleData[i]!.constants do
        unless nativeRootSet.contains ci.name do
          nativeRootSet := nativeRootSet.insert ci.name
          nativeRoots := nativeRoots.push ci.name
        for d in declEdges ci do
          unless nativeRootSet.contains d do
            nativeRootSet := nativeRootSet.insert d
            nativeRoots := nativeRoots.push d
      -- Also seed from registered instance entries (`ent.val`) and default instances (`A2-5`) so
      -- a forged `Meta.instanceExtension` entry carrying `Lean.reduceBool`/`Lean.reduceNat` is
      -- caught before any kernel or `MetaM` evaluation runs.
      for e in Meta.instanceExtension.ext.getModuleEntries env i do
        let ent := match e with | .global a => a | .scoped _ a => a
        for d in ent.val.getUsedConstants do
          unless nativeRootSet.contains d do
            nativeRootSet := nativeRootSet.insert d
            nativeRoots := nativeRoots.push d
      for d in Meta.defaultInstanceExtension.getModuleEntries env i do
        unless nativeRootSet.contains d.instanceName do
          nativeRootSet := nativeRootSet.insert d.instanceName
          nativeRoots := nativeRoots.push d.instanceName
  let (nativeReach, _) := reachesNativeEvaluator env nativeRoots {} (envConstantCount env + 64)
  if nativeReach then
    report "nativeDecideReached" ``Lean.reduceBool ((origin? env ``Lean.reduceBool).getD .anonymous)
      "kernel-native evaluator (Lean.reduceBool / Lean.reduceNat) reachable from an audited declaration: evaluating it would run audited code inside the auditor, so no kernel or MetaM evaluation is performed"
  let L : Loaded := {
    env, req, libDir, artMap, modIdx, toolchainProv, nonToolchain, dynamicOk := !nativeReach }
  -- Admitted import DAG.
  if let some expected := req.graph then
    let tracked := env.header.modules.filterMap fun (m : EffectiveImport) =>
      match expected.getObjVal? m.module.toString with
      | .ok _ => some m.module
      | .error _ => none
    for m in nonToolchain do
      unless tracked.contains m do
        report "graphMismatch" m m "module missing from the admitted import DAG"
    for f in req.foundation do
      if modIdx.contains f && !tracked.contains f then
        report "graphMismatch" f f "loaded foundation module missing from the admitted import DAG"
    for m in tracked do
      let some i := modIdx[m]? | continue
      let actual := Lean.toJson env.header.moduleData[i]!.imports
      let same := match expected.getObjVal? m.toString with
        | .ok e => e == actual
        | .error _ => false
      unless same do
        report "graphMismatch" m m "compiled imports differ from the admitted import DAG"
  let (_toolchainCSimp, toolchainImplByTargets) ← scanModuleEntries L toolchainNames
  -- Inventory consistency, companions, overrides, tags, ShareCommon ban, _private audit, axiom sweep, and IR.
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
    for imp in data.imports do
      if imp.module == `Init.ShareCommon || (`Init.ShareCommon).isPrefixOf imp.module then
        report "shareCommonForbidden" imp.module m "direct import of Init.ShareCommon is forbidden"
    unless data.constNames == data.constants.map ConstantInfo.name do
      report "inventoryMismatch" m m "constNames differ from stored constants"
    for ci in data.constants do
      let n := ci.name
      if isShareCommonName env n || (declEdges ci).any (isShareCommonName env) then
        report "shareCommonForbidden" n m "declaration references Init.ShareCommon"
      if ci matches .axiomInfo _ then
        modify fun s => { s with moduleConstantsAxiomSwept := s.moduleConstantsAxiomSwept + 1 }
        if origin? env n != some m then
          report "unapprovedAxiom" n m s!"masked top-level axiom re-declaration (origin={(origin? env n).getD .anonymous})"
        else
          checkAxiom L ci m (fun om => om == m && req.localAxiomModules.contains m)
      let some om := origin? env n | report "inventoryMismatch" n m "declaration without origin"; continue
      checkPrivateName L toolchainNames om n (some ci)
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
            if ← (if L.dynamicOk then reservedTheoremCopyOk env n stored ci else pure false) then
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
          if ← (if L.dynamicOk then reservedTheoremCopyOk env n stored ci else pure false) then
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
          let bodyOk ← match ci.value? (allowOpaque := true) with
            | some v =>
              if L.dynamicOk then kernelAcceptsPartial env ci.levelParams ci.type v budget else pure false
            | none => pure false
          if bodyOk then
            genuine := genuine.insert n
            isCompanion := true
            modify fun (s : AuditState) => { s with companions := s.companions + 1 }
          else
            report "compilerOverrideAttribute" n m "unsafe_rec_sibling: kernel rejected partial companion body"
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
      for k in overrideKinds env L.toolchainProv n do
        report "compilerOverrideAttribute" n m k
      checkIntrinsicTags L n m budget
      if req.checkOpaqueTheoremReadiness then
        let rhsFlag := match ci with | .recInfo rv => rv.rules.any (exprUsesOpaqueTheorem env ·.rhs) | _ => false
        if exprUsesOpaqueTheorem env ci.type || (ci.value? true).any (exprUsesOpaqueTheorem env) || rhsFlag then
          modify fun s => { s with opaqueTheoremReadinessFlags := s.opaqueTheoremReadinessFlags + 1 }
      if isCompanion then
        companionRoots := companionRoots.push (m, n)
      else if req.localAxiomModules.contains m then
        localRoots := localRoots.insert m ((localRoots.getD m #[]).push n)
      else
        strictRoots := strictRoots.push n
      unless isCompanion do replayLocals := replayLocals.insert n ci
    for n in data.extraConstNames do
      checkPrivateName L toolchainNames m n none (isIRHelper := true)
      if isShareCommonName env n then report "shareCommonForbidden" n m "IR helper references Init.ShareCommon"
      if toolchainNames.contains n || compilerReservedNames.contains n then
        report "compilerOverrideAttribute" n m
          "toolchain_name: IR helper reuses a name the pinned toolchain declares"
    checkModuleIR L i m data toolchainImplByTargets
  -- Stage-2 (`env.constants.map₂`) + full kernel constant sweep (Vector 1, 2, 4).
  for (n, ci) in env.constants.map₂.toList do
    let om := (origin? env n).getD env.header.mainModule
    checkPrivateName L toolchainNames om n (some ci)
    if isShareCommonName env n || (declEdges ci).any (isShareCommonName env) then
      report "shareCommonForbidden" n om "stage-2 constant references Init.ShareCommon"
    if ci matches .axiomInfo _ then
      modify fun s => { s with moduleConstantsAxiomSwept := s.moduleConstantsAxiomSwept + 1 }
      report "unapprovedAxiom" n om "unreferenced/live stage-2 axiom in env.constants.map₂"
  for (n, ci) in env.checked.get.constants do
    if ci matches .axiomInfo _ then
      match origin? env n with
      | none => report "unapprovedAxiom" n .anonymous "unattributed kernel axiom"
      | some om =>
        unless toolchainProv.contains om do
          modify fun s => { s with moduleConstantsAxiomSwept := s.moduleConstantsAxiomSwept + 1 }
          checkAxiom L ci om (fun m' => m' == om && req.localAxiomModules.contains om)
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
  -- Constructive module policy: every declaration (and genuine companion) in `constructiveModules`
  -- is audited freshly from `visited0 := {}` with `allowClassical := false` (`[propext, Quot.sound]`).
  for cm in req.constructiveModules do
    let some i := modIdx[cm]?
      | report "missingDeclaration" cm cm "constructive module missing from the loaded environment"; continue
    let mut cRoots : Array Name := #[]
    let mut cCompRoots : Array Name := #[]
    for ci in env.header.moduleData[i]!.constants do
      if origin? env ci.name == some cm then
        if genuine.contains ci.name then
          cCompRoots := cCompRoots.push ci.name
        else
          cRoots := cRoots.push ci.name
      else
        -- A duplicate reserved theorem copy stored by a constructive module (`A2-4`) must also
        -- have its own stored proof dependencies audited under `allowClassical := false`.
        for d in declEdges ci do
          cRoots := cRoots.push d
    for (em, edges) in extraEdges do
      if em == cm then
        cRoots := cRoots ++ edges.toArray
    let _ ← closure L cRoots {} {} (fun _ => false) fuel cm (allowClassical := false)
    for c in cCompRoots do
      let _ ← closure L #[c] {} genuine (fun _ => false) fuel cm (allowClassical := false)
    modify fun (s : AuditState) => { s with constructiveModulesChecked := s.constructiveModulesChecked + 1 }
  -- Hardened spec-strength & mutant-kill verification gates.
  -- (Skipped on a native-reaching environment: the gates normalize and type check audited terms.)
  if !req.specStrengthChecks.isEmpty && L.dynamicOk then
    let specCtx := SpecAuditCtx.forLoaded L budget
    for sc in req.specStrengthChecks do
      let vs ← (show IO (Array Violation) from do
        try
          runMeta env (do
            match sc.target with
            | .claim thmName =>
              auditClaimSpecStrengthCore specCtx thmName sc.certName
                sc.requiredCategories sc.requireDeterministic sc.requireInputSensitive
            | .synth clsKind defId =>
              auditItemSpecStrengthBySynthCore specCtx clsKind defId sc.certName
                sc.requiredCategories sc.requireDeterministic sc.requireInputSensitive) (heartbeats := 600000)
        catch e =>
          pure #[{ tag := "specStrengthCertInvalidType", decl := sc.certName, module := .anonymous,
                   detail := s!"spec-strength gate error: {e}" }])
      if vs.isEmpty then
        modify fun (s : AuditState) => { s with specStrengthChecksPassed := s.specStrengthChecksPassed + 1 }
      else
        for v in vs do
          report v.tag v.decl v.module v.detail
  -- Statement origins of claim theorems (and Prop-typed defs/opaques in claim modules).
  for m in req.claimModules do
    let some i := modIdx[m]?
      | report "missingDeclaration" m m "claim module missing from the loaded environment"; continue
    for ci in env.header.moduleData[i]!.constants do
      match ci with
      | .thmInfo _ =>
        checkStatementOrigin L ci.name m fuel
      | .defnInfo _ | .opaqueInfo _ =>
        let isPropTy ← if L.dynamicOk then (show IO Bool from do
            try runMeta env (Meta.isProp ci.type) (heartbeats := 50000) catch _ => pure true)
          else pure true
        if isPropTy then
          checkStatementOrigin L ci.name m fuel
      | _ => pure ()
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
    -- Second, independent layer that guesses nothing about strings: `_unsafe_rec` anywhere outside
    -- comments (string literals included) is rejected. Deciding which `"` opens an interpolated
    -- string needs Lean's parser (`panic! "{"` is a plain string, `s! "{"` is not), so the
    -- string-aware token scan can be desynchronized; this string-unaware pass cannot. A string
    -- containing `--` or `/-` only makes it treat more text as a comment, and that text is
    -- still covered by the token scan, so an identifier is missed only if both layers miss it.
    if forbiddenSourceIdentifier (stripComments text) then
      report "sourceForbiddenIdentifier" m m "_unsafe_rec appears outside comments"
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
  let realLib ← realPathOrEmpty libDir
  unless realLib == libDir && pathWithinRoot realSys realLib do
    fail s!"[moduleProvenanceSpoofed] toolchain libDir is not canonical within sysroot: {libDir}"
  let sysMods ← listToolchainModules libDir req.toolchainRoots
  let (preloaded, preSt) ← (preloadArtifactChecks req sysMods).run {}
  if !preSt.violations.isEmpty then failWithViolations req preSt.violations
  let toolchainNames ← toolchainNameInventory req sysMods
  let env ← loadEnvironment req req.roots
  let importUs ← IO.monoNanosNow
  let mut artMap : Std.HashMap Name (Array System.FilePath × Array System.FilePath) := {}
  for (m, o, i) in req.artifacts do artMap := artMap.insert m (o, i)
  let mut modIdx : Std.HashMap Name Nat := {}
  for h : i in [0:env.header.modules.size] do
    modIdx := modIdx.insert env.header.modules[i].module i
  let (result, st) ← (auditCore req env libDir artMap modIdx preloaded toolchainNames).run
    { oleanFilesValidated := preSt.oleanFilesValidated }
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
    ("oleanFilesValidated", Lean.toJson st.oleanFilesValidated),
    ("privateNamesAudited", Lean.toJson st.privateNamesAudited),
    ("moduleConstantsAxiomSwept", Lean.toJson st.moduleConstantsAxiomSwept),
    ("opaqueTheoremReadinessFlags", Lean.toJson st.opaqueTheoremReadinessFlags),
    ("auditedDeclarations", Lean.toJson audited),
    ("reachableDeclarations", Lean.toJson st.reachable),
    ("codegenCompanions", Lean.toJson st.companions),
    ("irDeclarationsChecked", Lean.toJson st.irDecls),
    ("intrinsicTagsChecked", Lean.toJson st.tagChecks),
    ("kernelTagConfirmations", Lean.toJson st.kernelTagConfirmations),
    ("constructiveModulesChecked", Lean.toJson st.constructiveModulesChecked),
    ("specStrengthChecksPassed", Lean.toJson st.specStrengthChecksPassed),
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

public def main (args : List String) : IO UInt32 := do
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
