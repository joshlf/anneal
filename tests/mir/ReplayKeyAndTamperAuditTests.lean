import Anneal.ReplayKeyAndTamperAudit

namespace Anneal.ReplayKeyAndTamperAuditTests

open Anneal.ReplayKeyAndTamperAudit

/-!
# Regression and Axiom-Audit Suite for `Anneal.ReplayKeyAndTamperAudit`

Every `theorem` below is checked by the kernel (`decide +kernel` evaluates the audit on a
concrete package), and every soundness theorem of the module is pinned to its exact axiom
footprint with `#guard_msgs in #print axioms`.

Contents:
1. Fixtures: a clean four-module package (`Topic.Defs`, `Anneal.TheoryHelper`,
   `Topic.Proofs`, `Verify.Topic`) over `standardBaseDecls`.
2. Operational models of the unpatched behaviours (`naiveLean434Replay`,
   `naiveInsertByCiNameAudit`, `finalizeImport434`, `naiveCachedClosureMultiItemAudit`,
   `naiveSingleAllCheck`). They live here, not in `theory/`: they exist only to show that
   each exploit is accepted by the unpatched logic and rejected by the audit.
3. `lean4#16677` replay-key bypasses, the `replayLocals` overwrite, the `subsumesInfo`
   body swap, and the multi-item cache poisoning.
4. Mutual `.all` blocks, the `pillar_1` native-reduction bans, the tamper vectors
   `V01`-`V18`, and the hardening regressions (lexer, extensions, imports, roles, roots).
5. Axiom audit of the module's theorems.
-/

/-! ## Helpers and fixtures -/

open Lean in
/-- `chars! "abc"` is the character list `['a', 'b', 'c']`, built at elaboration time: the
kernel never has to convert a `String`. -/
macro "chars!" s:str : term => do
  let elems : Array (TSyntax `term) :=
    s.getString.toList.toArray.map (fun c => ⟨(Syntax.mkCharLit c).raw⟩)
  `(([$elems,*] : List Char))

open Lean in
/-- `sn! "Topic.Proofs.lemma"` is the name with components `Topic`, `Proofs`, `lemma`. -/
macro "sn!" s:str : term => do
  let parts := (s.getString.splitOn ".").filter (fun part => part != "")
  let partStx : Array (TSyntax `term) ← parts.toArray.mapM fun part => do
    let elems : Array (TSyntax `term) :=
      part.toList.toArray.map (fun c => ⟨(Syntax.mkCharLit c).raw⟩)
    `(([$elems,*] : List Char))
  `(SymName.mk [$partStx,*])

/-- `c! "Nat.zero"` is the constant expression of that name. -/
macro "c!" s:str : term => `(ExprSkeleton.const (sn! $s))

def trueE : ExprSkeleton := c! "True"
def falseE : ExprSkeleton := c! "False"
def natE : ExprSkeleton := c! "Nat"
def boolE : ExprSkeleton := c! "Bool"
def trueIntroE : ExprSkeleton := c! "True.intro"
def sorryE : ExprSkeleton := c! "sorryAx"

/-- `Trusted.VerificationResult e`. -/
def vr (e : ExprSkeleton) : ExprSkeleton := .app (c! "Trusted.VerificationResult") e

/-- `Trusted.VerificationResult.intro e`. -/
def vrIntro (e : ExprSkeleton) : ExprSkeleton := .app (c! "Trusted.VerificationResult.intro") e

/-- `EqBool e Bool.true`. -/
def eqBoolTrue (e : ExprSkeleton) : ExprSkeleton := .app (.app (c! "EqBool") e) (c! "Bool.true")

def mkThm (n : SymName) (ty val : ExprSkeleton) : ConstantRecord :=
  { name := n, kind := .thmDecl, type := ty, value? := some val, all := [n] }

def mkDef (n : SymName) (ty val : ExprSkeleton) : ConstantRecord :=
  { name := n, kind := .defnDecl, type := ty, value? := some val, all := [n] }

def mkOpaque (n : SymName) (ty val : ExprSkeleton) : ConstantRecord :=
  { name := n, kind := .opaqueDecl, type := ty, value? := some val, all := [n] }

def mkAxiom (n : SymName) (ty : ExprSkeleton) : ConstantRecord :=
  { name := n, kind := .axiomDecl, type := ty }

/-- A module whose keys are exactly its record names. -/
def mkModule (name : SymName) (role : ModuleRole) (consts : List ConstantRecord)
    (imports : List SymName) : ModuleInventory :=
  { moduleName := name, role := role, constNames := consts.map (·.name), constants := consts,
    imports := imports.map (fun m => { module := m }) }

def addConsts (m : ModuleInventory) (cs : List ConstantRecord) : ModuleInventory :=
  { m with constNames := m.constNames ++ cs.map (·.name), constants := m.constants ++ cs }

def addExts (m : ModuleInventory) (es : List EnvExtEntry) : ModuleInventory :=
  { m with extEntries := m.extEntries ++ es }

def withSource (m : ModuleInventory) (src : List Char) : ModuleInventory :=
  { m with sourceText? := some src }

/-- `r` failed with exactly the diagnostic `e`. -/
def failsWith {α : Type} (r : Except AuditFailure α) (e : AuditFailure) : Bool :=
  match r with
  | .error e' => decide (e' = e)
  | .ok _ => false

def isOk {α : Type} (r : Except AuditFailure α) : Bool :=
  match r with
  | .ok _ => true
  | .error _ => false

/-- Configuration for tests that are not about source text. -/
def noSourceConfig : AuditConfig := { requireSources := false }

def colorName : SymName := sn! "Topic.Defs.Color"
def redName : SymName := sn! "Topic.Defs.Color.red"
def blueName : SymName := sn! "Topic.Defs.Color.blue"

def colorDecls : List ConstantRecord := [
  { name := colorName, kind := .inductDecl [redName, blueName], type := .sort 1,
    all := [colorName] },
  { name := redName, kind := .ctorDecl colorName, type := .const colorName },
  { name := blueName, kind := .ctorDecl colorName, type := .const colorName },
  { name := sn! "Topic.Defs.Color.rec",
    kind := .recDecl (canonicalRecRules colorName [redName, blueName]),
    type := canonicalRecType colorName [redName, blueName], all := [colorName] }]

def defsModule : ModuleInventory :=
  addExts (mkModule (sn! "Topic.Defs") .defsExempt
    (colorDecls ++ [mkDef (sn! "Topic.Defs.claimIdx") natE (.natLit 0),
      mkDef (sn! "Topic.Defs.instColor") (.const colorName) (.const redName)]) [sn! "Init"])
    [.instanceEntry (sn! "Topic.Defs.instColor") (sn! "Inhabited") false]

def theoryModule : ModuleInventory :=
  mkModule (sn! "Anneal.TheoryHelper") .theory
    [mkDef (sn! "Anneal.TheoryHelper.theoryIdx") natE (.natLit 5),
     mkThm (sn! "Anneal.TheoryHelper.helperLemma") trueE trueIntroE] [sn! "Init"]

def mutAName : SymName := sn! "Topic.Proofs.mutA"
def mutBName : SymName := sn! "Topic.Proofs.mutB"

def proofsModule : ModuleInventory :=
  { mkModule (sn! "Topic.Proofs") .proof
      [mkThm (sn! "Topic.Proofs.cleanLemma") trueE trueIntroE,
       { mkThm (sn! "Topic.Proofs.mutA") trueE trueIntroE with all := [mutAName, mutBName] },
       { mkThm (sn! "Topic.Proofs.mutB") trueE (c! "Topic.Proofs.cleanLemma") with
           all := [mutAName, mutBName] },
       mkThm (sn! "Topic.Proofs.usesTheory") trueE (c! "Anneal.TheoryHelper.helperLemma"),
       mkThm (sn! "Topic.Proofs.forallRed") (.pi (.const colorName) trueE) (.lam (.const colorName) trueIntroE),
       mkDef (sn! "Topic.Proofs.safeRecFn") natE (.natLit 0),
       { mkDef (sn! "Topic.Proofs.safeRecFn._unsafe_rec") natE (c! "Topic.Proofs.safeRecFn._unsafe_rec")
           with safety := .partialDecl }]
      [sn! "Init", sn! "Topic.Defs", sn! "Anneal.TheoryHelper"] with
    oleanParts := { isModuleMode := true, hasServer := true, hasPrivate := true } }

def verifiedName : SymName := sn! "Verify.Topic.verified"

def verifyModule : ModuleInventory :=
  mkModule (sn! "Verify.Topic") .verify
    [mkThm (sn! "Verify.Topic.verified") (vr (c! "Topic.Defs.claimIdx")) (vrIntro (c! "Topic.Defs.claimIdx"))]
    [sn! "Init", sn! "Trusted.Core", sn! "Topic.Defs", sn! "Topic.Proofs"]

/-- A package with the given replacement for the proof module. -/
def pkgWithProofs (m : ModuleInventory) : PackageAuditInput :=
  { baseEnv := standardBaseDecls, modules := [defsModule, theoryModule, m, verifyModule],
    verifyRoots := [verifiedName] }

/-- The clean package without source texts. -/
def corePkg : PackageAuditInput := pkgWithProofs proofsModule

def defsSrc : List Char :=
  chars! "namespace Topic.Defs\ninductive Color where\n  | red\n  | blue\ndef claimIdx : Nat := 0\ninstance instColor : Inhabited Color := ⟨.red⟩\nend Topic.Defs\n"

def theorySrc : List Char :=
  chars! "namespace Anneal.TheoryHelper\ndef theoryIdx : Nat := 5\ntheorem helperLemma : True := True.intro\nend Anneal.TheoryHelper\n"

def proofsSrc : List Char :=
  chars! "namespace Topic.Proofs\n-- a comment may mention set_option debug.skipKernelTC true or native_decide\n/- block /- nested unsafe -/ still a comment: run_cmd -/\ndef msg : String := \"an escaped \\\" quote and the word unsafe\"\ndef quoteChar : Char := '\"'\ndef x' : Nat := 0\ntheorem cleanLemma : True := by decide +kernel\nmutual\ntheorem mutA : True := True.intro\ntheorem mutB : True := cleanLemma\nend\nend Topic.Proofs\n"

def verifySrc : List Char :=
  chars! "import Topic.Proofs\nnamespace Verify.Topic\ntheorem verified : Trusted.VerificationResult Topic.Defs.claimIdx := .intro _\nend Verify.Topic\n"

/-- The clean package as production sees it: every module with its source text. -/
def validBaselinePackage : PackageAuditInput :=
  { baseEnv := standardBaseDecls,
    modules := [withSource defsModule defsSrc, withSource theoryModule theorySrc,
      withSource proofsModule proofsSrc, withSource verifyModule verifySrc],
    verifyRoots := [verifiedName] }

def audit (cfg : AuditConfig) (pkg : PackageAuditInput) : Except AuditFailure AuditCertificate :=
  auditAndReplayPackage cfg pkg

def initPrelude : SymName := SymName.initPreludeModuleName
def initCore : SymName := SymName.initCoreModuleName
def proofsMod : SymName := sn! "Topic.Proofs"

/-! ## Positive baseline -/

theorem validBaselinePackage_accepted :
    isOk (audit defaultStrictConfig validBaselinePackage) = true ∧
    isOk (audit noSourceConfig corePkg) = true := by decide +kernel

/-- The JSON report of the clean package, byte for byte. -/
theorem validBaselinePackage_json :
    renderAuditJsonChars defaultStrictConfig validBaselinePackage =
      chars! "{\"ok\":true,\"violations\":[],\"modules\":4,\"replayed\":15,\"reachedAxioms\":[],\"items\":[{\"root\":\"Verify.Topic.verified\",\"status\":\"VerifiedUnconditional\",\"provisional\":[],\"assumptions\":[]}]}" := by
  decide +kernel

/-- Source withholding is rejected by the production configuration: a package that omits
its source texts is refused outright, and the JSON report says why. -/
theorem source_withholding_rejected_by_default :
    failsWith (audit defaultStrictConfig corePkg) (.missingSourceText (sn! "Topic.Defs")) = true ∧
    renderAuditJsonChars defaultStrictConfig corePkg =
      chars! "{\"ok\":false,\"violations\":[{\"code\":\"missingSourceText\",\"names\":[\"Topic.Defs\"],\"detail\":\"\"}]}" ∧
    defaultStrictConfig.requireSources = true := by decide +kernel

/-- A hash-map order is not a dependency order: the same declarations reversed still
replay, and the certificate holds every declaration under its own name. -/
theorem baseline_replays_in_any_order :
    isOk (replayCleanEnvOrdered (fun _ => false) standardBaseEnv (collectReplayDecls corePkg).reverse)
      = true ∧
    failsWith (replayCleanEnv (fun _ => false) standardBaseEnv (collectReplayDecls corePkg).reverse)
      (.unknownConstant (sn! "Topic.Defs.claimIdx")) = true := by decide +kernel

/-! ## Operational models of the unpatched behaviours -/

/-- `addDecl` unless a declaration of that name is already present. -/
def naiveAdd (env : KernelEnv) (ci : ConstantRecord) : Except AuditFailure KernelEnv :=
  if env.contains ci.name then .ok env else kernelCheckDecl env true ci

/-- Add the records found under the given names: lookups are by name, as in `Replay.lean`. -/
def naiveAddByName (m : KernelEnv) : KernelEnv → List SymName → Except AuditFailure KernelEnv
  | env, [] => .ok env
  | env, n :: rest =>
    match m.lookup n with
    | none => .error (.unknownConstant n)
    | some ci =>
      match naiveAdd env ci with
      | .error e => .error e
      | .ok env' => naiveAddByName m env' rest

/-- One pass of Lean 4.34.1 `replayConstant` over the entries of a key → record map `m`.
Each branch reproduces what the code does with the *key* and with the record's *name*:
quotients are added without reading the stored record; constructors and recursors are
postponed under `ci.name`; an inductive is rebuilt from `ci.all` by name, so the record
stored under the key is never checked; a theorem whose name and type are already present
is skipped. -/
def naiveReplayPass (m : KernelEnv) :
    KernelEnv → List (SymName × ConstantRecord) → List SymName →
      Except AuditFailure (KernelEnv × List SymName)
  | env, [], postponed => .ok (env, postponed.reverse)
  | env, (_, ci) :: rest, postponed =>
    match ci.kind with
    | .quotDecl => naiveReplayPass m env rest postponed
    | .ctorDecl _ => naiveReplayPass m env rest (ci.name :: postponed)
    | .recDecl _ => naiveReplayPass m env rest (ci.name :: postponed)
    | .inductDecl _ =>
      match naiveAddByName m env ci.all with
      | .error e => .error e
      | .ok env' => naiveReplayPass m env' rest postponed
    | .thmDecl =>
      match env.lookup ci.name with
      | some prev =>
        if prev.type = ci.type then naiveReplayPass m env rest postponed
        else .error (.kernelTypeError ci.name "already declared")
      | none =>
        match kernelCheckDecl env true ci with
        | .error e => .error e
        | .ok env' => naiveReplayPass m env' rest postponed
    | _ =>
      match naiveAdd env ci with
      | .error e => .error e
      | .ok env' => naiveReplayPass m env' rest postponed

/-- Unpatched replay: one pass, then the postponed constructors and recursors by name. -/
def naiveLean434Replay (base m : KernelEnv) : Except AuditFailure KernelEnv :=
  match naiveReplayPass m base m [] with
  | .error e => .error e
  | .ok (env, postponed) => naiveAddByName m env postponed

/-- What import leaves under a key. -/
def importedType (inv : ModuleInventory) (key : SymName) : Option ExprSkeleton :=
  (inv.replayMap.lookup key).map (·.type)

def exploitMod : SymName := sn! "Proof.Exploit"
def tName : SymName := sn! "Proof.Exploit.T"
def tMkName : SymName := sn! "Proof.Exploit.T.mk"
def tRecName : SymName := sn! "Proof.Exploit.T.rec"
def renamedKey : SymName := sn! "Proof.Exploit.forgedFalse"

def tDecl : ConstantRecord :=
  { name := tName, kind := .inductDecl [tMkName], type := .sort 1, all := [tName] }
def tMkDecl : ConstantRecord := { name := tMkName, kind := .ctorDecl tName, type := .const tName }
def tRecDecl : ConstantRecord :=
  { name := tRecName, kind := .recDecl (canonicalRecRules tName [tMkName]),
    type := canonicalRecType tName [tMkName], all := [tName] }
def validThm : ConstantRecord := mkThm (sn! "Proof.Exploit.valid") trueE trueIntroE

/-- An exploit inventory: the honest records plus `forged` stored under `key`. -/
def forgedInv (key : SymName) (forged : ConstantRecord) (first : Bool := false) : ModuleInventory :=
  if first then
    { moduleName := exploitMod, role := .proof,
      constNames := [key, tName, tMkName, tRecName, validThm.name],
      constants := [forged, tDecl, tMkDecl, tRecDecl, validThm] }
  else
    { moduleName := exploitMod, role := .proof,
      constNames := [tName, tMkName, tRecName, validThm.name, key],
      constants := [tDecl, tMkDecl, tRecDecl, validThm, forged] }

def forgedRec : ConstantRecord := { tRecDecl with type := falseE }
def forgedCtor : ConstantRecord := { tMkDecl with type := falseE }
def forgedQuot : ConstantRecord := { name := sn! "Quot", kind := .quotDecl, type := falseE }
def forgedThm : ConstantRecord := { validThm with value? := some sorryE }
def forgedInduct : ConstantRecord := { tDecl with type := falseE }
def alignedFakeInd : ConstantRecord :=
  { name := sn! "Proof.Exploit.FakeInd", kind := .inductDecl [], type := falseE, all := [tName] }
def alignedFakeQuot : ConstantRecord :=
  { name := sn! "Proof.Exploit.fakeQuot", kind := .quotDecl, type := falseE }

/-- The honest inventory replays under both the unpatched model and the audit. -/
theorem honest_inventory_accepted :
    isOk (validateReplayInventory (mkModule (sn! "Proof.Exploit") .proof [tDecl, tMkDecl, tRecDecl, validThm] []))
      = true ∧
    isOk (naiveLean434Replay standardBaseEnv
      (mkModule (sn! "Proof.Exploit") .proof [tDecl, tMkDecl, tRecDecl, validThm] []).replayMap) = true ∧
    isOk (replayCleanEnvOrdered (fun _ => false) standardBaseEnv [tRecDecl, tMkDecl, tDecl]) = true := by
  decide +kernel

/-! ## `lean4#16677`: the seven replay-key bypasses -/

/-- Bypass 1, `.recInfo`: a record named `T.rec` of type `False` stored under another key.
Replay postpones `T.rec`, later checks the honest record of that name, and never looks at
the forged one, which import nevertheless binds under the key. -/
theorem issue16675_recursor_bypass :
    isOk (naiveLean434Replay standardBaseEnv (forgedInv renamedKey forgedRec).replayMap) = true ∧
    importedType (forgedInv renamedKey forgedRec) renamedKey = some falseE ∧
    failsWith (validateReplayInventory (forgedInv renamedKey forgedRec))
      (.keyNameMismatch exploitMod renamedKey tRecName) = true := by decide +kernel

/-- Bypass 2, `.ctorInfo`: the same through `postponedConstructors`. -/
theorem issue16675_ctor_bypass :
    isOk (naiveLean434Replay standardBaseEnv (forgedInv renamedKey forgedCtor).replayMap) = true ∧
    importedType (forgedInv renamedKey forgedCtor) renamedKey = some falseE ∧
    failsWith (validateReplayInventory (forgedInv renamedKey forgedCtor))
      (.keyNameMismatch exploitMod renamedKey tMkName) = true := by decide +kernel

/-- Bypass 3, `.quotInfo`: `addDecl quotDecl` never reads the stored record. -/
theorem issue16675_quot_bypass :
    isOk (naiveLean434Replay standardBaseEnv (forgedInv renamedKey forgedQuot).replayMap) = true ∧
    importedType (forgedInv renamedKey forgedQuot) renamedKey = some falseE ∧
    failsWith (validateReplayInventory (forgedInv renamedKey forgedQuot))
      (.keyNameMismatch exploitMod renamedKey (sn! "Quot")) = true := by decide +kernel

/-- Bypass 4, `.thmInfo` duplicate short-circuit: an aliased entry with the header of a
checked theorem and a `sorryAx` body is skipped. -/
theorem issue16675_thm_dup_bypass :
    isOk (naiveLean434Replay standardBaseEnv (forgedInv renamedKey forgedThm).replayMap) = true ∧
    ((forgedInv renamedKey forgedThm).replayMap.lookup renamedKey).bind (·.value?) = some sorryE ∧
    failsWith (validateReplayInventory (forgedInv renamedKey forgedThm))
      (.keyNameMismatch exploitMod renamedKey validThm.name) = true := by decide +kernel

/-- Bypass 5, `.inductInfo` by-name rebuild: the kernel declaration is rebuilt from the
records named in `.all`, so a record named `T` of type `False` under another key is
accepted when it is replayed before `T`. -/
theorem issue16675_induct_bypass :
    isOk (naiveLean434Replay standardBaseEnv (forgedInv renamedKey forgedInduct true).replayMap)
      = true ∧
    importedType (forgedInv renamedKey forgedInduct true) renamedKey = some falseE ∧
    failsWith (validateReplayInventory (forgedInv renamedKey forgedInduct true))
      (.keyNameMismatch exploitMod renamedKey tName) = true := by decide +kernel

/-- Bypass 6, key-ALIGNED inductive: key equals name and `constNames = constants.map name`,
yet `.all` omits the record itself, so replay adds `T` and never checks `FakeInd : False`.
Only `ci.name ∈ ci.all` rejects it. -/
theorem issue16675_induct_all_aligned_key_bypass :
    isOk (naiveLean434Replay standardBaseEnv
      (forgedInv alignedFakeInd.name alignedFakeInd true).replayMap) = true ∧
    importedType (forgedInv alignedFakeInd.name alignedFakeInd true) alignedFakeInd.name
      = some falseE ∧
    isOk (validateModuleDataKeys (forgedInv alignedFakeInd.name alignedFakeInd true)) = true ∧
    failsWith (validateReplayInventory (forgedInv alignedFakeInd.name alignedFakeInd true))
      (.invalidMutualAll exploitMod alignedFakeInd.name "ci.name missing from .all") = true := by
  decide +kernel

/-- Bypass 7, key-ALIGNED quotient outside `Init`: accepted by unpatched replay with an
aligned key; rejected by the inventory check, and independently by the clean kernel. -/
theorem issue16675_quot_aligned_key_bypass :
    isOk (naiveLean434Replay standardBaseEnv
      (forgedInv alignedFakeQuot.name alignedFakeQuot).replayMap) = true ∧
    importedType (forgedInv alignedFakeQuot.name alignedFakeQuot) alignedFakeQuot.name
      = some falseE ∧
    isOk (validateModuleDataKeys (forgedInv alignedFakeQuot.name alignedFakeQuot)) = true ∧
    failsWith (validateReplayInventory (forgedInv alignedFakeQuot.name alignedFakeQuot))
      (.foreignQuotDecl exploitMod alignedFakeQuot.name) = true ∧
    failsWith (replayCleanEnv (fun _ => false) standardBaseEnv [alignedFakeQuot])
      (.kernelTypeError alignedFakeQuot.name "non-canonical quotient declaration") = true := by
  decide +kernel

/-- Length mismatch, duplicate keys, and anonymous keys are explicit errors (Lean's
parallel insertion loop silently truncates at the shorter array). -/
theorem inventory_key_hygiene_rejected :
    failsWith (validateReplayInventory
      { moduleName := exploitMod, role := .proof, constNames := [validThm.name, tName],
        constants := [validThm] }) (.lengthMismatch exploitMod 2 1) = true ∧
    failsWith (validateReplayInventory
      { moduleName := exploitMod, role := .proof, constNames := [validThm.name, validThm.name],
        constants := [validThm, validThm] }) (.duplicateConstName exploitMod validThm.name) = true ∧
    failsWith (validateReplayInventory
      { moduleName := exploitMod, role := .proof, constNames := [.anonymous],
        constants := [{ validThm with name := .anonymous }] })
      (.anonymousConstantName exploitMod) = true := by decide +kernel

/-! ## `TrustedBoundary` `replayLocals` overwrite, `subsumesInfo` body swap -/

/-- `replayLocals := replayLocals.insert ci.name ci`: the last record of a name wins. -/
def naiveReplayLocals (cs : List ConstantRecord) : KernelEnv :=
  cs.foldl (fun acc ci => (ci.name, ci) :: acc.filter (fun p => decide (p.1 ≠ ci.name))) []

/-- `verifyAudit` before the patch: the header check reads the imported map by key, the
kernel replays `replayLocals`, and nothing compares the two. -/
def naiveInsertByCiNameAudit (base : KernelEnv) (inv : ModuleInventory) (root : SymName) : Bool :=
  (match inv.replayMap.lookup root with
   | some ci =>
     decide (ci.kind = .thmDecl ∧ ci.type.getAppFn = .const SymName.verificationResultName)
   | none => false) &&
  isOk (replayCleanEnvOrdered (fun _ => false) base ((naiveReplayLocals inv.constants).map (·.2)))

def verifyFooMod : SymName := sn! "Verify.Foo"
def verifyFooThm : SymName := sn! "Verify.Foo.verified"
def verifyFooHelperKey : SymName := sn! "Verify.Foo.helper"

/-- Under the key `verified`: a `VerificationResult 0` "proved" by `True.intro`. Under the
key `helper`: a benign theorem that is also *named* `verified`. -/
def overwriteInv : ModuleInventory :=
  { moduleName := verifyFooMod, role := .verify, constNames := [verifyFooThm, verifyFooHelperKey],
    constants := [mkThm (sn! "Verify.Foo.verified") (vr (.natLit 0)) trueIntroE,
      mkThm (sn! "Verify.Foo.verified") trueE trueIntroE] }

theorem trustedBoundary_overwrite_bypass :
    naiveInsertByCiNameAudit standardBaseEnv overwriteInv verifyFooThm = true ∧
    importedType overwriteInv verifyFooThm = some (vr (.natLit 0)) ∧
    failsWith (replayCleanEnv (fun _ => false) standardBaseEnv
      [mkThm (sn! "Verify.Foo.verified") (vr (.natLit 0)) trueIntroE])
      (.kernelTypeError verifyFooThm "theorem proof term type mismatch") = true ∧
    failsWith (validateReplayInventory overwriteInv)
      (.keyNameMismatch verifyFooMod verifyFooHelperKey verifyFooThm) = true := by decide +kernel

/-- `subsumesInfo` of `Environment.lean`: same name and type, and for two theorems the
same `.all`; the proof body is not compared. -/
def subsumes434 (new old : ConstantRecord) : Bool :=
  decide (new.name = old.name ∧ new.type = old.type) &&
    match new.kind, old.kind with
    | .thmDecl, .thmDecl => decide (new.all = old.all)
    | _, _ => false

/-- `finalizeImport`: a later record that subsumes the stored one REPLACES it, while
`const2ModIdx.insertIfNew` keeps the first module as the origin. -/
def finalizeImport434 :
    List (SymName × SymName × ConstantRecord) → KernelEnv → List (SymName × SymName) →
      Option (KernelEnv × List (SymName × SymName))
  | [], m, origins => some (m, origins)
  | (modName, key, ci) :: rest, m, origins =>
    match m.lookup key with
    | none => finalizeImport434 rest (m ++ [(key, ci)]) (origins ++ [(key, modName)])
    | some prev =>
      if subsumes434 ci prev then
        finalizeImport434 rest (m.map (fun p => if p.1 = key then (key, ci) else p)) origins
      else if subsumes434 prev ci then finalizeImport434 rest m origins
      else none

def importEntries (mods : List ModuleInventory) : List (SymName × SymName × ConstantRecord) :=
  mods.flatMap (fun inv => inv.replayMap.map (fun p => (inv.moduleName, p.1, p.2)))

def sharedThmName : SymName := sn! "Proof.Shared.thm"
def modA : ModuleInventory :=
  mkModule (sn! "Proof.ModA") .proof [{ mkThm (sn! "Proof.Shared.thm") trueE trueIntroE with name := sharedThmName }] [sn! "Init"]
def modB : ModuleInventory :=
  mkModule (sn! "Proof.ModB") .proof [mkThm (sn! "Proof.Shared.thm") trueE sorryE] [sn! "Init"]
def bodySwapPkg : PackageAuditInput := { baseEnv := standardBaseDecls, modules := [modA, modB] }

/-- Two modules declare `Proof.Shared.thm : True` with different bodies. Import keeps the
LATER module's `sorryAx` body and attributes it to the FIRST module. The audit refuses
every cross-module duplicate name. -/
theorem finalizeImport_subsumes_body_swap_bypass :
    ((finalizeImport434 (importEntries [modA, modB]) [] []).map
      (fun r => ((r.1.lookup sharedThmName).bind (·.value?), r.2))) =
      some (some sorryE, [(sharedThmName, sn! "Proof.ModA")]) ∧
    failsWith (audit noSourceConfig bodySwapPkg)
      (.duplicateConstName (sn! "Proof.ModA") sharedThmName) = true := by decide +kernel

/-! ## `cleanNonWorkspace` multi-item cache poisoning -/

def provisionalNoSource : AuditConfig := { allowProvisionalNative := true, requireSources := false }

def nativeAxName : SymName := sn! "Proof.Native.f._native.native_decide.ax_1"
def usesNativeName : SymName := sn! "Proof.Native.usesNative"
def usesProvName : SymName := sn! "Anneal.TheoryHelper.usesProv"

def nativeModule : ModuleInventory :=
  mkModule (sn! "Proof.Native") .proof
    [mkAxiom (sn! "Proof.Native.f._native.native_decide.ax_1") (eqBoolTrue (c! "Bool.true")),
     mkThm (sn! "Proof.Native.usesNative") (eqBoolTrue (c! "Bool.true")) (.const nativeAxName)] [sn! "Init"]

/-- A `VerificationResult 0` whose proof term mentions `dep : EqBool Bool.true Bool.true`. -/
def verifiedVia (dep : SymName) : ExprSkeleton :=
  .app (.lam (eqBoolTrue (c! "Bool.true")) (vrIntro (.natLit 0))) (.const dep)

def itemModule (name : SymName) (dep : SymName) (imports : List SymName) : ModuleInventory :=
  mkModule name .verify [mkThm name.verifiedRoot (vr (.natLit 0)) (verifiedVia dep)] imports

/-- Two verify items reach the native axiom through a helper outside the workspace. -/
def cachePoisonPkg : PackageAuditInput :=
  { baseEnv := standardBaseDecls,
    modules := [nativeModule,
      mkModule (sn! "Anneal.TheoryHelper") .theory
        [mkThm (sn! "Anneal.TheoryHelper.usesProv") (eqBoolTrue (c! "Bool.true")) (.const usesNativeName)]
        [sn! "Init"],
      itemModule (sn! "Verify.Item1") usesProvName [sn! "Init", sn! "Trusted.Core", sn! "Anneal.TheoryHelper"],
      itemModule (sn! "Verify.Item2") usesProvName [sn! "Init", sn! "Trusted.Core", sn! "Anneal.TheoryHelper"]],
    verifyRoots := [sn! "Verify.Item1.verified", sn! "Verify.Item2.verified"] }

/-- The same items with the dependency on the proof module declared and direct. -/
def cachePoisonDeclaredPkg : PackageAuditInput :=
  { baseEnv := standardBaseDecls,
    modules := [nativeModule,
      itemModule (sn! "Verify.Item1") usesNativeName [sn! "Init", sn! "Trusted.Core", sn! "Proof.Native"],
      itemModule (sn! "Verify.Item2") usesNativeName [sn! "Init", sn! "Trusted.Core", sn! "Proof.Native"]],
    verifyRoots := [sn! "Verify.Item1.verified", sn! "Verify.Item2.verified"] }

/-- One item of `verifyAudit` before the patch: nodes in the shared cache are not expanded,
and afterwards EVERY visited non-workspace node joins the cache, whatever lay below it. -/
def naiveCachedItem (pkg : PackageAuditInput) (cache : List SymName) (root : SymName) :
    Option (String × List SymName) :=
  match walkGraph (packageEnv pkg) root
      (fun n ci => if n ∈ cache then .ok [] else ci.declarationEdges)
      (closureFuel (packageEnv pkg)) [root] [] with
  | .error _ => none
  | .ok visited =>
    some (if visited.any (·.isNativeReductionAxiom) then "ProvisionalNative"
          else "VerifiedUnconditional",
      cache ++ visited.filter (fun n =>
        !n.isNativeReductionAxiom &&
        match (packageEnv pkg).lookup n with
        | some ci => decide (roleOfConst pkg n ci ≠ .proof ∧ roleOfConst pkg n ci ≠ .verify)
        | none => false))

def naiveCachedClosureMultiItemAudit (pkg : PackageAuditInput) :
    List SymName → List SymName → List String
  | [], _ => []
  | root :: rest, cache =>
    match naiveCachedItem pkg cache root with
    | none => ["error"]
    | some (status, cache') => status :: naiveCachedClosureMultiItemAudit pkg rest cache'

def itemStatuses (cfg : AuditConfig) (pkg : PackageAuditInput) : Option (List VerifyItemStatus) :=
  match audit cfg pkg with
  | .ok cert => some (cert.itemReports.map (·.status))
  | .error _ => none

/-- The shared cache certifies the second item `VerifiedUnconditional` although it depends
on the same native axiom as the first. The audit classifies every root from its own walk:
both items are `provisionalNative` under `--provisional` and rejected without it; and the
undeclared theory-to-proof dependency of the first package is itself rejected. -/
theorem cleanNonWorkspace_cache_poisoning_bypass :
    naiveCachedClosureMultiItemAudit cachePoisonPkg cachePoisonPkg.verifyRoots [] =
      ["ProvisionalNative", "VerifiedUnconditional"] ∧
    failsWith (audit provisionalNoSource cachePoisonPkg)
      (.referenceOutsideImportClosure (sn! "Anneal.TheoryHelper") usesProvName usesNativeName
        (sn! "Proof.Native")) = true ∧
    itemStatuses provisionalNoSource cachePoisonDeclaredPkg =
      some [.provisionalNative, .provisionalNative] ∧
    failsWith (audit noSourceConfig cachePoisonDeclaredPkg)
      (.forbiddenNativeReductionAxiom nativeAxName nativeAxName) = true := by decide +kernel

/-! ## `lowmem_lean`: multi-element mutual `.all` blocks -/

/-- The over-strict check that rejects every multi-element block. -/
def naiveSingleAllCheck (inv : ModuleInventory) : Bool :=
  inv.constants.all (fun ci => !ci.kind.hasMutualAll || decide (ci.all = [ci.name]))

def opA : SymName := sn! "Topic.Proofs.opA"
def opB : SymName := sn! "Topic.Proofs.opB"

def mutualOpaqueModule : ModuleInventory :=
  addConsts proofsModule
    [{ mkOpaque (sn! "Topic.Proofs.opA") natE (.natLit 1) with all := [opA, opB] },
     { mkOpaque (sn! "Topic.Proofs.opB") natE (.natLit 2) with all := [opA, opB] }]

/-- Valid two-element mutual theorem and opaque blocks: the naive single-`.all` check
rejects them, the audit accepts them. -/
theorem mutual_thm_and_opaque_blocks_accepted :
    naiveSingleAllCheck proofsModule = false ∧
    naiveSingleAllCheck mutualOpaqueModule = false ∧
    isOk (validateReplayInventory proofsModule) = true ∧
    isOk (audit noSourceConfig (pkgWithProofs mutualOpaqueModule)) = true := by decide +kernel

def allMod (cs : List ConstantRecord) : ModuleInventory := mkModule (sn! "Proof.Exploit") .proof cs []
def mA : SymName := sn! "Proof.Exploit.a"
def mB : SymName := sn! "Proof.Exploit.b"
def thmA (all : List SymName) : ConstantRecord := { mkThm (sn! "Proof.Exploit.a") trueE trueIntroE with all := all }
def thmB (all : List SymName) : ConstantRecord := { mkThm (sn! "Proof.Exploit.b") trueE trueIntroE with all := all }

/-- The seven malformed `.all` shapes, each with its own diagnostic. -/
theorem malformedAll_all_seven_rejected :
    failsWith (validateReplayInventory (allMod [thmA []]))
      (.invalidMutualAll exploitMod mA "empty .all") = true ∧
    failsWith (validateReplayInventory (allMod [thmA [mA, mA]]))
      (.invalidMutualAll exploitMod mA "duplicate entry in .all") = true ∧
    failsWith (validateReplayInventory (allMod [thmA [mA, .anonymous]]))
      (.invalidMutualAll exploitMod mA "anonymous entry in .all") = true ∧
    failsWith (validateReplayInventory (allMod [thmA [mB], thmB [mB]]))
      (.invalidMutualAll exploitMod mA "ci.name missing from .all") = true ∧
    failsWith (validateReplayInventory (allMod [thmA [mA, mB], thmB [mB]]))
      (.invalidMutualAll exploitMod mA "asymmetric mutual .all") = true ∧
    failsWith (validateReplayInventory (allMod [thmA [mA, mB]]))
      (.invalidMutualAll exploitMod mA "missing mutual peer") = true ∧
    failsWith (validateReplayInventory
        (allMod [thmA [mA, mB], { mkDef (sn! "Proof.Exploit.b") trueE trueIntroE with all := [mA, mB] }]))
      (.invalidMutualAll exploitMod mA "incompatible mutual peer kind") = true := by decide +kernel

/-- Recursor targets, constructor links, and stray `.all` fields. -/
theorem all_field_structure_rejected :
    failsWith (validateReplayInventory (allMod [tMkDecl, tRecDecl]))
      (.invalidMutualAll exploitMod tMkName "constructor of a missing inductive") = true ∧
    failsWith (validateReplayInventory (allMod [{ tRecDecl with all := [validThm.name] }, validThm]))
      (.invalidMutualAll exploitMod tRecName "recursor .all target is not an inductive") = true ∧
    failsWith (validateReplayInventory (allMod [{ tRecDecl with all := [tName] }]))
      (.invalidMutualAll exploitMod tRecName "missing inductive target of recursor .all") = true ∧
    failsWith (validateReplayInventory (allMod [tDecl]))
      (.invalidMutualAll exploitMod tName "inductive lists a missing constructor") = true ∧
    failsWith (validateReplayInventory (allMod [{ tDecl with kind := .inductDecl [] }, tMkDecl]))
      (.invalidMutualAll exploitMod tMkName "constructor is not listed by its inductive") = true ∧
    failsWith (validateReplayInventory (allMod [{ mkAxiom (sn! "Proof.Exploit.ax") trueE with all := [mA] }]))
      (.invalidMutualAll exploitMod (sn! "Proof.Exploit.ax")
        "unexpected .all on a declaration without one") = true := by decide +kernel

def hiddenSorryModule : ModuleInventory :=
  addConsts proofsModule
    [{ mkThm (sn! "Topic.Proofs.front") trueE trueIntroE with
        all := [sn! "Topic.Proofs.front", sn! "Topic.Proofs.hidden"] },
     { mkThm (sn! "Topic.Proofs.hidden") trueE sorryE with
        all := [sn! "Topic.Proofs.front", sn! "Topic.Proofs.hidden"] }]

/-- `sorryAx` in a mutual sibling: the clean-looking front theorem never mentions the
sibling in its type or value, and the walk still reaches it through `.all`. -/
theorem mutual_sibling_hidden_sorry_rejected :
    failsWith (audit noSourceConfig (pkgWithProofs hiddenSorryModule))
      (.forbiddenAxiom (sn! "Topic.Proofs.front") SymName.sorryAxName initPrelude) = true := by
  decide +kernel

/-! ## `pillar_1`: native reduction and compiler trust -/

def withProofThm (n : SymName) (ty val : ExprSkeleton) : PackageAuditInput :=
  pkgWithProofs (addConsts proofsModule [mkThm n ty val])

def pillarUser : SymName := sn! "Topic.Proofs.pillar"

/-- The deprecated reduction axioms and `Lean.trustCompiler` are banned in every mode,
`--provisional` included. -/
theorem pillar1_native_reduction_all_rejected :
    failsWith (audit noSourceConfig (withProofThm (sn! "Topic.Proofs.pillar") trueE (c! "Lean.ofReduceNat")))
      (.forbiddenNativeReductionAxiom pillarUser SymName.ofReduceNatName) = true ∧
    failsWith (audit noSourceConfig (withProofThm (sn! "Topic.Proofs.pillar") trueE (c! "Lean.ofReduceBool")))
      (.forbiddenNativeReductionAxiom pillarUser SymName.ofReduceBoolName) = true ∧
    failsWith (audit noSourceConfig (withProofThm (sn! "Topic.Proofs.pillar") trueE (c! "Lean.trustCompiler")))
      (.forbiddenNativeReductionAxiom pillarUser SymName.trustCompilerName) = true ∧
    failsWith (audit provisionalNoSource
        (withProofThm (sn! "Topic.Proofs.pillar") trueE (c! "Lean.ofReduceNat")))
      (.forbiddenNativeReductionAxiom pillarUser SymName.ofReduceNatName) = true ∧
    failsWith (audit provisionalNoSource
        (withProofThm (sn! "Topic.Proofs.pillar") trueE (c! "Lean.ofReduceBool")))
      (.forbiddenNativeReductionAxiom pillarUser SymName.ofReduceBoolName) = true ∧
    failsWith (audit provisionalNoSource
        (withProofThm (sn! "Topic.Proofs.pillar") trueE (c! "Lean.trustCompiler")))
      (.forbiddenNativeReductionAxiom pillarUser SymName.trustCompilerName) = true := by
  decide +kernel

def provAx : SymName := sn! "Topic.Proofs.f._native.native_decide.ax_1"

/-- A proof module with one compiler-generated native axiom of the given type, used by a
theorem, plus extra declarations the axiom may mention. -/
def nativeProofs (axType : ExprSkeleton) (extra : List ConstantRecord := []) : PackageAuditInput :=
  pkgWithProofs (addConsts proofsModule (extra ++
    [mkAxiom (sn! "Topic.Proofs.f._native.native_decide.ax_1") axType,
     mkThm (sn! "Topic.Proofs.usesAx") axType (.const provAx)]))

def reachedAxiomsOfAudit (cfg : AuditConfig) (pkg : PackageAuditInput) : Option (List SymName) :=
  match audit cfg pkg with
  | .ok cert => some cert.reachedAxioms
  | .error _ => none

/-- `--provisional` admits a well-shaped `_native` axiom of a proof module and reports it;
without the flag it is rejected; in a specification module, or under a name that merely
imitates `Lean.ofReduceBool`, it is rejected even with the flag. -/
theorem pillar1_provisional_scoping :
    reachedAxiomsOfAudit provisionalNoSource (nativeProofs (eqBoolTrue (c! "Bool.true"))) =
      some [provAx] ∧
    failsWith (audit noSourceConfig (nativeProofs (eqBoolTrue (c! "Bool.true"))))
      (.forbiddenNativeReductionAxiom provAx provAx) = true ∧
    failsWith (audit provisionalNoSource
        { corePkg with modules := corePkg.modules ++
            [mkModule (sn! "Topic.Spec") .spec
              [mkAxiom (sn! "Topic.Spec.g._native.native_decide.ax_1") (eqBoolTrue (c! "Bool.true"))]
              [sn! "Init"]] })
      (.forbiddenNativeReductionAxiom (sn! "Topic.Spec.g._native.native_decide.ax_1")
        (sn! "Topic.Spec.g._native.native_decide.ax_1")) = true ∧
    failsWith (audit provisionalNoSource
        { baseEnv := standardBaseDecls.filter (fun ci => decide (ci.name ≠ SymName.ofReduceBoolName)),
          modules := [mkModule (sn! "Proof.Native") .proof [mkAxiom (sn! "Lean.ofReduceBool") falseE] [sn! "Init"]] })
      (.forbiddenNativeReductionAxiom SymName.ofReduceBoolName SymName.ofReduceBoolName) = true := by
  decide +kernel

/-- The shape `EqBool e Bool.true` is required, and an axiom whose left-hand side evaluates
to `Bool.false` is refused: literally, through a definition, through an `opaque` constant
(compiled code runs opaque bodies), and through an opaque function applied to an argument. -/
theorem pillar1_native_axiom_shape_and_refutation :
    failsWith (audit provisionalNoSource (nativeProofs falseE))
      (.invalidNativeAxiomType provAx provAx) = true ∧
    failsWith (audit provisionalNoSource (nativeProofs (eqBoolTrue (c! "Bool.false"))))
      (.invalidNativeAxiomType provAx provAx) = true ∧
    failsWith (audit provisionalNoSource (nativeProofs (eqBoolTrue (c! "Topic.Proofs.alwaysFalse"))
        [mkDef (sn! "Topic.Proofs.alwaysFalse") boolE (c! "Bool.false")]))
      (.invalidNativeAxiomType provAx provAx) = true ∧
    failsWith (audit provisionalNoSource (nativeProofs (eqBoolTrue (c! "Topic.Proofs.opaqueFalse"))
        [mkOpaque (sn! "Topic.Proofs.opaqueFalse") boolE (c! "Bool.false")]))
      (.invalidNativeAxiomType provAx provAx) = true ∧
    failsWith (audit provisionalNoSource
        (nativeProofs (eqBoolTrue (.app (c! "Topic.Proofs.opaqueFn") (c! "Bool.true")))
          [mkOpaque (sn! "Topic.Proofs.opaqueFn") (.pi boolE boolE) (.lam boolE (c! "Bool.false"))]))
      (.invalidNativeAxiomType provAx provAx) = true ∧
    isOk (audit provisionalNoSource (nativeProofs (eqBoolTrue (c! "Topic.Proofs.alwaysTrue"))
        [mkDef (sn! "Topic.Proofs.alwaysTrue") boolE (c! "Bool.true")])) = true := by decide +kernel

/-! ## Tamper vectors `V01`–`V18` -/

def lemmaName : SymName := sn! "Topic.Proofs.cleanLemma"
def verifyMod : SymName := sn! "Verify.Topic"
def defsMod : SymName := sn! "Topic.Defs"
def theoryMod : SymName := sn! "Anneal.TheoryHelper"
def instColorName : SymName := sn! "Topic.Defs.instColor"

def extPkg (e : EnvExtEntry) : PackageAuditInput := pkgWithProofs (addExts proofsModule [e])

def addImports (m : ModuleInventory) (imps : List ImportSpec) : ModuleInventory :=
  { m with imports := m.imports ++ imps }

/-- The strict baseline with another source text for the proof module. -/
def srcPkg (src : List Char) : PackageAuditInput :=
  { validBaselinePackage with
    modules := [withSource defsModule defsSrc, withSource theoryModule theorySrc,
      withSource proofsModule src, withSource verifyModule verifySrc] }

theorem V01_hijack_macro_rejected :
    failsWith (audit noSourceConfig (extPkg (.macroEntry lemmaName)))
      (.forbiddenMacroOrElab proofsMod "macro" lemmaName) = true ∧
    failsWith (audit noSourceConfig (extPkg (.syntaxEntry lemmaName)))
      (.forbiddenMacroOrElab proofsMod "syntax" lemmaName) = true := by decide +kernel

theorem V02_hijack_elab_rejected :
    failsWith (audit noSourceConfig
        { corePkg with modules := [defsModule, theoryModule, proofsModule,
            addExts verifyModule [.commandElabEntry verifiedName]] })
      (.forbiddenMacroOrElab verifyMod "command_elab" verifiedName) = true := by decide +kernel

def badThmName : SymName := sn! "Topic.Proofs.bad"

/-- `debug.skipKernelTC` is caught twice, independently: by the source scanner, and (with
the source scan out of the picture) by clean-environment replay of the ill-typed proof. -/
theorem V03_skip_kernel_tc_rejected_both_layers :
    failsWith (audit defaultStrictConfig
        (srcPkg (chars! "set_option debug.skipKernelTC true in\ntheorem bad : False := trivial\n")))
      (.forbiddenSourceOption proofsMod "debug.skipKernelTC") = true ∧
    failsWith (audit noSourceConfig (withProofThm badThmName falseE trueIntroE))
      (.kernelTypeError badThmName "theorem proof term type mismatch") = true := by decide +kernel

def specMod : SymName := sn! "Topic.Spec"
def unrefAxName : SymName := sn! "Topic.Spec.unrefAxiom"

def withSpec (consts : List ConstantRecord) (imports : List SymName := [sn! "Init"]) :
    PackageAuditInput :=
  { corePkg with modules := corePkg.modules ++ [mkModule specMod .spec consts imports] }

/-- An axiom nobody references is still rejected: every declaration is audited. -/
theorem V04_unref_axiom_rejected :
    failsWith (audit noSourceConfig (withSpec [mkAxiom unrefAxName trueE]))
      (.forbiddenAxiom unrefAxName unrefAxName specMod) = true := by decide +kernel

def opaqueHelperName : SymName := sn! "Topic.Proofs.opaqueHelper"

/-- `sorryAx` inside an `opaque` body: the walk reads opaque values. -/
theorem V05_shadow_sorry_rejected :
    failsWith (audit noSourceConfig
        (pkgWithProofs (addConsts proofsModule [mkOpaque opaqueHelperName trueE sorryE])))
      (.forbiddenAxiom opaqueHelperName SymName.sorryAxName initPrelude) = true := by decide +kernel

def sorryThmName : SymName := sn! "Topic.Proofs.sorryThm"

def v06Pkg (cache : List SymName) : PackageAuditInput :=
  pkgWithProofs (addConsts proofsModule
    [{ mkThm sorryThmName trueE sorryE with cachedExportedAxioms := cache }])

/-- The artifact's own axiom cache is never consulted. Whatever it claims (nothing, only
`propext`, or the truth), structure, extensions, imports, and shadowing all pass, and the
direct closure walk finds `sorryAx`. -/
theorem V06_tamper_ext_isolated_rejection :
    isOk (validatePackageStructure (v06Pkg [])) = true ∧
    (v06Pkg []).modules.all (fun inv =>
      isOk (validateModuleExtensions inv) && isOk (validateImports (v06Pkg []) inv) &&
        isOk (auditShadowing (v06Pkg []) inv)) = true ∧
    failsWith (audit noSourceConfig (v06Pkg []))
      (.forbiddenAxiom sorryThmName SymName.sorryAxName initPrelude) = true ∧
    failsWith (audit noSourceConfig (v06Pkg [SymName.propextName]))
      (.forbiddenAxiom sorryThmName SymName.sorryAxName initPrelude) = true ∧
    failsWith (audit noSourceConfig (v06Pkg [SymName.sorryAxName]))
      (.forbiddenAxiom sorryThmName SymName.sorryAxName initPrelude) = true := by decide +kernel

theorem V07_local_elab_bad_rejected :
    failsWith (audit noSourceConfig (extPkg (.localCommandElabEntry lemmaName true)))
      (.forbiddenMacroOrElab proofsMod "local_command_elab_global" lemmaName) = true ∧
    failsWith (audit noSourceConfig (extPkg (.localCommandElabEntry lemmaName false)))
      (.forbiddenMacroOrElab proofsMod "local_command_elab" lemmaName) = true := by decide +kernel

theorem V08_nonlocal_elab_bad_rejected :
    failsWith (audit noSourceConfig (extPkg (.commandElabEntry lemmaName)))
      (.forbiddenMacroOrElab proofsMod "command_elab" lemmaName) = true := by decide +kernel

def illTypedName : SymName := sn! "Topic.Proofs.illTyped"

/-- An ill-typed theorem injected without any source or extension trace passes structure
and the whole policy stage, and fails only at clean-environment replay. -/
theorem V09_replay_only_isolated_rejection :
    isOk (validatePackageStructure (withProofThm illTypedName falseE trueIntroE)) = true ∧
    isOk (validateAxiomAndTamperPolicy noSourceConfig
      (withProofThm illTypedName falseE trueIntroE)) = true ∧
    failsWith (audit noSourceConfig (withProofThm illTypedName falseE trueIntroE))
      (.kernelTypeError illTypedName "theorem proof term type mismatch") = true := by decide +kernel

theorem V10_hooks_bad_all_four_rejected :
    failsWith (audit noSourceConfig (extPkg (.initializeEntry lemmaName false)))
      (.forbiddenInitOrCodegenHook proofsMod "initialize" lemmaName) = true ∧
    failsWith (audit noSourceConfig (extPkg (.initializeEntry lemmaName true)))
      (.forbiddenInitOrCodegenHook proofsMod "meta_initialize" lemmaName) = true ∧
    failsWith (audit noSourceConfig (extPkg (.implementedByEntry lemmaName mutAName)))
      (.forbiddenInitOrCodegenHook proofsMod "implemented_by" lemmaName) = true ∧
    failsWith (audit noSourceConfig (extPkg (.externEntry lemmaName)))
      (.forbiddenInitOrCodegenHook proofsMod "extern" lemmaName) = true := by decide +kernel

theorem V11_scoped_attrs_bad_all_three_rejected :
    failsWith (audit noSourceConfig (extPkg (.scopedElabEntry lemmaName proofsMod)))
      (.forbiddenMacroOrElab proofsMod "scoped_elab" lemmaName) = true ∧
    failsWith (audit noSourceConfig (extPkg (.scopedMacroEntry lemmaName proofsMod)))
      (.forbiddenMacroOrElab proofsMod "scoped_macro" lemmaName) = true ∧
    failsWith (audit noSourceConfig (extPkg (.scopedInstanceEntry lemmaName mutAName proofsMod)))
      (.forbiddenInstanceOrCoe proofsMod "scoped_instance" lemmaName) = true := by decide +kernel

/-- Instances: an imported declaration, a default instance, and a coercion are rejected in
a proof module; a local instance of a local class there, and the definitions module's
local instance of an imported class, are accepted. -/
theorem V12_inst_and_coe_bad_and_benign_ok :
    failsWith (audit noSourceConfig (extPkg (.instanceEntry instColorName colorName false)))
      (.forbiddenInstanceOrCoe proofsMod "imported_instance" instColorName) = true ∧
    failsWith (audit noSourceConfig (extPkg (.instanceEntry lemmaName colorName false)))
      (.forbiddenInstanceOrCoe proofsMod "instance_of_imported_class" lemmaName) = true ∧
    failsWith (audit noSourceConfig (extPkg (.defaultInstanceEntry lemmaName mutAName)))
      (.forbiddenInstanceOrCoe proofsMod "default_instance" lemmaName) = true ∧
    failsWith (audit noSourceConfig (extPkg (.coeEntry lemmaName mutAName mutBName)))
      (.forbiddenInstanceOrCoe proofsMod "coe" lemmaName) = true ∧
    isOk (audit noSourceConfig (extPkg (.instanceEntry lemmaName mutAName false))) = true ∧
    defsModule.extEntries = [.instanceEntry instColorName (sn! "Inhabited") false] := by
  decide +kernel

theorem V13_reducibility_bad_both_layers_rejected :
    failsWith (SourceScanner.scanSourceChars defaultStrictConfig proofsMod .proof
        (chars! "set_option allowUnsafeReducibility true in\nattribute [reducible] Nat.add\n"))
      (.forbiddenSourceOption proofsMod "allowUnsafeReducibility") = true ∧
    failsWith (audit noSourceConfig (extPkg (.reducibilityOverride SymName.natSuccName)))
      (.forbiddenReducibilityOverride proofsMod SymName.natSuccName) = true ∧
    isOk (audit noSourceConfig (extPkg (.reducibilityOverride lemmaName))) = true := by
  decide +kernel

def privInstName : SymName := sn! "_private.Topic.Defs.0.instPriv"

/-- `import all`, alone and with a private instance it would expose: flagged by the flag,
and by the `_private` name when the flag lies. -/
theorem V14_import_all_and_private_instance_rejected :
    failsWith (audit noSourceConfig
        (pkgWithProofs (addImports proofsModule [{ module := defsMod, importAll := true }])))
      (.forbiddenImportAll proofsMod defsMod) = true ∧
    failsWith (audit noSourceConfig
        { corePkg with modules :=
            [{ defsModule with extEntries := [.instanceEntry instColorName (sn! "Inhabited") true] },
             theoryModule, addImports proofsModule [{ module := defsMod, importAll := true }],
             verifyModule] })
      (.privateInstanceLeakViaImportAll proofsMod defsMod instColorName) = true ∧
    failsWith (audit noSourceConfig
        { corePkg with modules :=
            [addExts (addConsts defsModule
                [{ mkDef privInstName (.const colorName) (.const redName) with isPrivate := true }])
                [.instanceEntry privInstName (sn! "Inhabited") false],
             theoryModule, addImports proofsModule [{ module := defsMod, importAll := true }],
             verifyModule] })
      (.privateInstanceLeakViaImportAll proofsMod defsMod privInstName) = true := by decide +kernel

def shadowNat : SymName := sn! "Topic.Proofs.Nat.succ"
def shadowDefs : SymName := sn! "Topic.Proofs.Topic.Defs.claimIdx"
def shadowInternal : SymName := sn! "Topic.Proofs._x.Nat.succ"
def pubName : SymName := sn! "Topic.Proofs.pub"

/-- `export`, namespace-suffix shadowing of `Init` and of a definitions module, a spoofed
`Defs` exemption, and the flag shortcuts around them. -/
theorem V15_export_shadow_and_spoofed_defs_rejected :
    failsWith (audit noSourceConfig (extPkg (.exportAlias (sn! "add") SymName.natSuccName)))
      (.forbiddenShadowingOrExport proofsMod "export" (sn! "add")) = true ∧
    failsWith (audit noSourceConfig (withProofThm shadowNat trueE trueIntroE))
      (.forbiddenShadowingOrExport proofsMod "namespace_shadow" shadowNat) = true ∧
    failsWith (audit noSourceConfig (withProofThm shadowDefs trueE trueIntroE))
      (.forbiddenShadowingOrExport proofsMod "namespace_shadow" shadowDefs) = true ∧
    failsWith (audit noSourceConfig (withProofThm shadowInternal trueE trueIntroE))
      (.forbiddenShadowingOrExport proofsMod "namespace_shadow" shadowInternal) = true ∧
    failsWith (audit noSourceConfig
        (pkgWithProofs (addConsts proofsModule
          [{ mkThm pubName trueE trueIntroE with isPrivate := true }])))
      (.privateFlagMismatch proofsMod pubName) = true ∧
    failsWith (audit noSourceConfig
        { corePkg with modules := corePkg.modules ++
            [mkModule (sn! "Topic.Proofs.Defs") .defsExempt [] [sn! "Init"]] })
      (.spoofedExemptModule (sn! "Topic.Proofs.Defs")) = true := by decide +kernel

theorem V16_term_delab_bad_all_three_rejected :
    failsWith (audit noSourceConfig (extPkg (.termElabEntry lemmaName)))
      (.forbiddenMacroOrElab proofsMod "term_elab" lemmaName) = true ∧
    failsWith (audit noSourceConfig (extPkg (.delabEntry lemmaName)))
      (.forbiddenMacroOrElab proofsMod "delab" lemmaName) = true ∧
    failsWith (audit noSourceConfig (extPkg (.appUnexpanderEntry lemmaName)))
      (.forbiddenMacroOrElab proofsMod "app_unexpander" lemmaName) = true := by decide +kernel

theorem V17_missing_olean_server_rejected :
    failsWith (audit noSourceConfig (pkgWithProofs
        { proofsModule with oleanParts := { isModuleMode := true, hasServer := false, hasPrivate := true } }))
      (.missingOleanServer proofsMod) = true := by decide +kernel

theorem V18_missing_olean_private_rejected :
    failsWith (audit noSourceConfig (pkgWithProofs
        { proofsModule with oleanParts := { isModuleMode := true, hasServer := true, hasPrivate := false } }))
      (.missingOleanPrivate proofsMod) = true := by decide +kernel

/-! ## Source scanner: lexer desynchronisation, token glue, fail-closed lexing -/

def scan (src : List Char) : Except AuditFailure Unit :=
  SourceScanner.scanSourceChars defaultStrictConfig proofsMod .proof src

/-- The scan rejects the source for the given reason. -/
def flags (src : List Char) (what : String) : Bool :=
  failsWith (scan src) (.forbiddenSourceOption proofsMod what)

def lexFails (src : List Char) : Bool :=
  match scan src with
  | .error (.unsupportedSourceLexing _ _) => true
  | _ => false

/-- Sources in which a naive stripper loses track of where a literal or comment ends and
hides an active `set_option debug.skipKernelTC true`. Each is lexed as Lean lexes it. -/
theorem sourceScanner_lexer_desync_rejected :
    -- primed identifier directly before a string
    flags (chars! "def g := f'\"\"\nset_option debug.skipKernelTC true in\ndef h := 1 --\"")
      "debug.skipKernelTC" = true ∧
    flags (chars! "def y := (x', \"'\")\nset_option debug.skipKernelTC true in\ndef h := 1")
      "debug.skipKernelTC" = true ∧
    -- raw strings: no escapes, optional hashes
    flags (chars! "def s := r\"\\\"\nset_option debug.skipKernelTC true in\ndef t := \"\"")
      "debug.skipKernelTC" = true ∧
    flags (chars! "def s := r#\"a\"b\"#\nset_option debug.skipKernelTC true in\ndef t := 1")
      "debug.skipKernelTC" = true ∧
    -- the documentation-comment opener consumes three characters
    flags (chars! "/--/ -/-- x\nset_option debug.skipKernelTC true in\ntheorem t : True := trivial\n-- -/\n")
      "debug.skipKernelTC" = true ∧
    -- escaped identifier components
    flags (chars! "set_option «debug».skipKernelTC true in\ndef a := 1") "debug.skipKernelTC" = true ∧
    -- a backtick name literal is not a raw-string prefix
    flags (chars! "def n := g `r\"\\\"\"\nset_option debug.skipKernelTC true in\ndef a := 1")
      "debug.skipKernelTC" = true ∧
    -- `ident.r` and `«x».r` are identifiers
    flags (chars! "def a := «x».r\"\\\"\"\nset_option debug.skipKernelTC true in\ndef b := 1")
      "debug.skipKernelTC" = true ∧
    -- the token `]'`
    flags (chars! "def a := xs[i]'\"proof\"\nset_option debug.skipKernelTC true in\ndef b := 1")
      "debug.skipKernelTC" = true ∧
    -- non-ASCII identifier characters carry primes too
    flags (chars! "def β' := 1\ndef s := β'\"\"\nset_option debug.skipKernelTC true in\ndef b := 1 --\"")
      "debug.skipKernelTC" = true := by decide +kernel

/-- Numeric literals and field indices end a token: a raw string or character literal may
follow immediately (valid after a precedence, `prefix:0x1r"\"" => id`). -/
theorem sourceScanner_numeric_literal_desync_rejected :
    flags (chars! "prefix:0x1r\"\\\" => id\nset_option debug.skipKernelTC true in\ndef a := \"\"")
      "debug.skipKernelTC" = true ∧
    flags (chars! "infixl:0b1r\"\\\" => Nat.add\nset_option debug.skipKernelTC true in\ndef a := \"\"")
      "debug.skipKernelTC" = true ∧
    flags (chars! "notation:0o7r\"\\\" => 1\nset_option debug.skipKernelTC true in\ndef a := \"\"")
      "debug.skipKernelTC" = true ∧
    flags (chars! "prefix:1_0r\"\\\" => id\nset_option debug.skipKernelTC true in\ndef a := \"\"")
      "debug.skipKernelTC" = true ∧
    flags (chars! "prefix:1e+0r\"\\\" => id\nset_option debug.skipKernelTC true in\ndef a := \"\"")
      "debug.skipKernelTC" = true ∧
    flags (chars! "def c := 0x1'\"'\nset_option debug.skipKernelTC true in\ndef a := 1")
      "debug.skipKernelTC" = true ∧
    -- `p.1e5r` is a field index followed by the identifier `e5r`, not `1e5` and a raw string
    flags (chars! "def a := p.1e5r\"\\\"\"\nset_option debug.skipKernelTC true in\ndef b := 1")
      "debug.skipKernelTC" = true := by decide +kernel

/-- Native evaluation hidden from a whitespace tokenizer, and every spelling of it. -/
theorem sourceScanner_token_glue_and_native_rejected :
    flags (chars! "example : True := ⟨by native_decide⟩") "native_decide" = true ∧
    flags (chars! "example : True := by skip<;>native_decide") "native_decide" = true ∧
    flags (chars! "example : True := by first|native_decide|skip") "native_decide" = true ∧
    flags (chars! "example : True := by iterate 1native_decide") "native_decide" = true ∧
    flags (chars! "example : True := by iterate 0x1native_decide") "native_decide" = true ∧
    flags (chars! "def s := s!\"{by native_decide}\"") "native_decide" = true ∧
    flags (chars! "example : True := by bv_decide") "bv_decide" = true ∧
    flags (chars! "example : True := by bv_decide?") "bv_decide" = true ∧
    flags (chars! "example : True := by bv_check \"t.lrat\"") "bv_check" = true ∧
    flags (chars! "example : True := by decide+native") "decide with a configuration" = true ∧
    flags (chars! "example : True := by decide\n  +native") "decide with a configuration" = true ∧
    flags (chars! "example : True := by decide (config := { native := true })")
      "decide with a configuration" = true ∧
    flags (chars! "example : True := by decide (config := ⟨false, true, true, false⟩)")
      "decide with a configuration" = true ∧
    flags (chars! "example : True := by decide (config := .mk false true true false)")
      "decide with a configuration" = true ∧
    flags (chars! "example : True := by decide? (config := myCfg)")
      "decide with a configuration" = true ∧
    flags (chars! "theorem t : True := _root_.Lean.ofReduceBool") "ofReduceBool" = true ∧
    flags (chars! "theorem t : True := Lean.trustCompiler") "trustCompiler" = true := by
  decide +kernel

/-- Metaprogram execution, `unsafe`, `partial`, code-generation hooks, and options. -/
theorem sourceScanner_meta_exec_unsafe_and_options_rejected :
    flags (chars! "example : True := by_elab pure ()") "by_elab" = true ∧
    flags (chars! "example : True := by run_tac pure ()") "run_tac" = true ∧
    flags (chars! "run_cmd pure ()") "run_cmd" = true ∧
    flags (chars! "run_meta pure ()") "run_meta" = true ∧
    flags (chars! "run_elab do pure ()") "run_elab" = true ∧
    flags (chars! "def x : Nat := unsafe (0 : Nat)") "unsafe" = true ∧
    flags (chars! "unsafe def y : Nat := 1") "unsafe" = true ∧
    flags (chars! "def «unsafe» : Nat := 1") "unsafe" = true ∧
    flags (chars! "partial def loop : Nat := loop") "partial" = true ∧
    flags (chars! "@[implemented_by g] def f : Nat := 1") "implemented_by" = true ∧
    flags (chars! "@[extern \"c_f\"] def f : Nat := 1") "extern" = true ∧
    flags (chars! "set_option hygiene false") "hygiene" = true ∧
    flags (chars! "set_option quotPrecheck false") "quotPrecheck" = true ∧
    flags (chars! "set_option backward.privateInPublic true") "backward.privateInPublic" = true ∧
    flags (chars! "set_option debug.byAsSorry true") "debug.byAsSorry" = true ∧
    flags (chars! "open Lean in\nset_option\n  debug.skipKernelTC true") "debug.skipKernelTC" = true := by
  decide +kernel

/-- What cannot be delimited with certainty is an error, never a pass. -/
theorem sourceScanner_ambiguous_lexing_fails_closed :
    lexFails (chars! "def s := s!\"{«}\"»}\"") = true ∧
    lexFails (chars! "def s := s!\"{\"a\"}\"") = true ∧
    lexFails (chars! "def s := s!\"{x -- y}\"") = true ∧
    lexFails (chars! "def s := s!\"{'a'}\"") = true ∧
    lexFails (chars! "def s := \"unterminated") = true ∧
    lexFails (chars! "/- never closed") = true ∧
    lexFails (chars! "def r := r#\"never closed\"") = true ∧
    lexFails (chars! "def c := ''") = true ∧
    lexFails (chars! "def n := 2else 3") = true ∧
    lexFails (chars! "def a := «unterminated") = true := by decide +kernel

/-- No false positives on ordinary proofs: keywords in comments, strings, raw strings, and
longer identifiers; kernel `decide`; every numeric literal form; character escapes; primed
identifiers next to literals and inside interpolation holes; allowed options. -/
theorem sourceScanner_hardened_lexer_no_false_positive :
    isOk (scan (chars! "theorem t : True := by decide +kernel")) = true ∧
    isOk (scan (chars! "def isUnsafeFlag := 1\ndef f._unsafe_rec := 2\ndef run_command_name := 3\ndef partialSum := 4\ndef run_elaborate := 5")) = true ∧
    isOk (scan (chars! "-- native_decide unsafe set_option debug.skipKernelTC true\n/- bv_decide /- nested -/ run_cmd -/ def a := \"run_cmd unsafe\"")) = true ∧
    isOk (scan (chars! "def a := 0x1a + 1_000 + 1.5e-3 + 0b101 + 0o17 + 2.")) = true ∧
    isOk (scan (chars! "example : True := by iterate 2 decide")) = true ∧
    isOk (scan (chars! "example : True := by simp?")) = true ∧
    isOk (scan (chars! "def f' := 1\ndef g := (f', \"x\", 'c', '\\'', '\\x41', '\\u0041', '\\\\', '\"')")) = true ∧
    isOk (scan (chars! "def s := s!\"{x'} and {y.1}\"")) = true ∧
    isOk (scan (chars! "def r := r\"mentions native_decide\" ++ r#\"set_option debug.skipKernelTC true\"#")) = true ∧
    isOk (scan (chars! "def a := xs[i]'h + (p, q).1.2 + [0..1e5].length")) = true ∧
    isOk (scan (chars! "set_option maxHeartbeats 400000 in\nset_option pp.all true in\nset_option linter.unusedVariables false in\ntheorem t : True := trivial")) = true := by
  decide +kernel

/-- `--provisional` allows native tactics in proof modules only, and never the compiler-trust
or reduction primitives. -/
theorem sourceScanner_provisional_scoping :
    isOk (SourceScanner.scanSourceChars provisionalConfig proofsMod .proof
      (chars! "example : True := by native_decide")) = true ∧
    failsWith (SourceScanner.scanSourceChars provisionalConfig specMod .spec
        (chars! "example : True := by native_decide"))
      (.forbiddenSourceOption specMod "native_decide") = true ∧
    failsWith (SourceScanner.scanSourceChars provisionalConfig proofsMod .proof
        (chars! "theorem t : True := Lean.trustCompiler"))
      (.forbiddenSourceOption proofsMod "trustCompiler") = true ∧
    failsWith (SourceScanner.scanSourceChars provisionalConfig proofsMod .proof
        (chars! "def x : Nat := unsafe (0 : Nat)"))
      (.forbiddenSourceOption proofsMod "unsafe") = true := by decide +kernel

/-- Segment matching: suffix `?`/`!`, numeric glue, dotted qualification. -/
theorem sourceScanner_segment_matching_edges :
    SourceScanner.tokenHasKeyword Chars.kwBvDecide (chars! "bv_decide?") = true ∧
    SourceScanner.tokenHasKeyword Chars.kwNativeDecide (chars! "1native_decide") = true ∧
    SourceScanner.tokenHasKeyword Chars.kwNativeDecide (chars! "Foo.native_decide!") = true ∧
    SourceScanner.tokenHasKeyword Chars.kwNativeDecide (chars! "xnative_decide") = false ∧
    SourceScanner.tokenHasKeyword Chars.kwUnsafe (chars! "_unsafe_rec") = false ∧
    SourceScanner.tokenizeChars (chars! "a  b.c d'") = [chars! "a", chars! "b.c", chars! "d'"] := by
  decide +kernel

/-! ## Roles and package-name spoofing -/

def plusModule (m : ModuleInventory) : PackageAuditInput :=
  { corePkg with modules := corePkg.modules ++ [m] }

/-- A role label must be the one the module name justifies. -/
theorem roleSpoof_labels_rejected :
    failsWith (audit noSourceConfig (pkgWithProofs { proofsModule with role := .foundation }))
      (.moduleRoleMismatch proofsMod "foundation") = true ∧
    failsWith (audit noSourceConfig (pkgWithProofs { proofsModule with role := .test }))
      (.moduleRoleMismatch proofsMod "test") = true ∧
    failsWith (audit noSourceConfig
        { corePkg with modules := [defsModule, { theoryModule with role := .spec }, proofsModule,
            verifyModule] })
      (.moduleRoleMismatch theoryMod "spec") = true ∧
    failsWith (audit noSourceConfig (plusModule (mkModule (sn! "Verify") .verify [] [])))
      (.moduleRoleMismatch (sn! "Verify") "verify") = true ∧
    failsWith (audit noSourceConfig (plusModule (mkModule (sn! "Topic.Proofs.Tests") .proof [] [])))
      (.moduleRoleMismatch (sn! "Topic.Proofs.Tests") "proof") = true ∧
    failsWith (audit noSourceConfig (plusModule (mkModule .anonymous .spec [] [])))
      (.moduleRoleMismatch .anonymous "spec") = true ∧
    failsWith (audit noSourceConfig (plusModule proofsModule))
      (.duplicateModuleName proofsMod) = true := by decide +kernel

/-- A package cannot supply its own standard library, compiler, or trusted modules. -/
theorem stdlib_trusted_lean_named_package_modules_rejected :
    failsWith (audit noSourceConfig (plusModule (mkModule (sn! "Std.Evil") .foundation
        [mkThm (sn! "Std.Evil.oops") falseE trueIntroE] [])))
      (.stdlibNamedPackageModule (sn! "Std.Evil")) = true ∧
    failsWith (audit noSourceConfig (plusModule (mkModule (sn! "Init.Evil") .foundation [] [])))
      (.stdlibNamedPackageModule (sn! "Init.Evil")) = true ∧
    failsWith (audit noSourceConfig (plusModule (mkModule (sn! "Lean.Evil") .spec [] [])))
      (.stdlibNamedPackageModule (sn! "Lean.Evil")) = true ∧
    failsWith (audit noSourceConfig (plusModule (mkModule (sn! "Trusted.Evil") .trusted [] [])))
      (.trustedNamedPackageModule (sn! "Trusted.Evil")) = true := by decide +kernel

/-- The role table: one role per name, none for hybrids, bare reserved roots, or `Lean.*`. -/
theorem roleMatchesModuleName_table :
    classifyModuleName (sn! "Topic.Proofs.Tests") = none ∧
    classifyModuleName (sn! "Tests.Proofs") = none ∧
    classifyModuleName (sn! "Verify") = none ∧
    classifyModuleName (sn! "Assumptions") = none ∧
    classifyModuleName (sn! "Lean.Evil") = none ∧
    classifyModuleName .anonymous = none ∧
    classifyModuleName (sn! "Topic.Proofs.Defs") = some .proof ∧
    classifyModuleName (sn! "Topic.Defs") = some .defsExempt ∧
    classifyModuleName (sn! "Topic.Spec") = some .spec ∧
    classifyModuleName (sn! "CrateVerify") = some .verify ∧
    classifyModuleName (sn! "Verify.Topic") = some .verify ∧
    classifyModuleName (sn! "Assumptions.Hw") = some .assumptions ∧
    classifyModuleName (sn! "Anneal.Proofs") = some .theory ∧
    classifyModuleName (sn! "Std.Data") = some .foundation ∧
    SymName.isStdlibModule (sn! "Lean.Evil") = false ∧
    SymName.isLeanCompilerModule (sn! "Lean.Evil") = true ∧
    roleOfModule corePkg (sn! "Lean.Evil") = .theory := by decide +kernel

/-! ## Statement origins, verify roots, claim roots -/

def theoryIdxName : SymName := sn! "Anneal.TheoryHelper.theoryIdx"

def verifyWith (stmtArg : ExprSkeleton) (imports : List SymName) : ModuleInventory :=
  mkModule verifyMod .verify [mkThm verifiedName (vr stmtArg) (vrIntro stmtArg)] imports

def allImports : List SymName :=
  [sn! "Init", sn! "Trusted.Core", sn! "Topic.Defs", sn! "Topic.Proofs", sn! "Anneal.TheoryHelper"]

/-- The verified statement mentions a theory definition directly. -/
def statementLeakPkg : PackageAuditInput :=
  { corePkg with modules := [defsModule, theoryModule, proofsModule,
      verifyWith (.const theoryIdxName) allImports] }

def aliasName : SymName := sn! "Topic.Proofs.claimAlias"

/-- The verified statement mentions a proof-module alias of a theory definition. -/
def launderedLeakPkg : PackageAuditInput :=
  { corePkg with modules := [defsModule, theoryModule,
      addConsts proofsModule [mkDef aliasName natE (.const theoryIdxName)],
      verifyWith (.const aliasName) allImports] }

theorem statementTheoryLeak_rejected :
    failsWith (audit noSourceConfig statementLeakPkg)
      (.statementTheoryLeak verifiedName theoryIdxName theoryMod) = true ∧
    failsWith (audit noSourceConfig launderedLeakPkg)
      (.statementTheoryLeak verifiedName theoryIdxName theoryMod) = true := by decide +kernel

/-- A verify module is audited whether or not its root is listed: leaving the root out is
itself the failure. Roots are unique, are theorems, state a `VerificationResult`, and sit
in their verify module. -/
theorem verifyRoot_coverage_and_shape_rejected :
    failsWith (audit noSourceConfig { statementLeakPkg with verifyRoots := [] })
      (.invalidVerifyRoot verifiedName "verify module root is not listed in verifyRoots") = true ∧
    failsWith (audit noSourceConfig { corePkg with verifyRoots := [verifiedName, verifiedName] })
      (.invalidVerifyRoot verifiedName "duplicate verify root") = true ∧
    failsWith (audit noSourceConfig { corePkg with claimRoots := [lemmaName, lemmaName] })
      (.invalidVerifyRoot lemmaName "duplicate claim root") = true ∧
    failsWith (audit noSourceConfig { corePkg with verifyRoots := [verifiedName, lemmaName] })
      (.invalidVerifyRoot lemmaName "verify root statement must be a Trusted.VerificationResult")
      = true ∧
    failsWith (audit noSourceConfig
        { (withProofThm (sn! "Topic.Proofs.verified") (vr (.natLit 0)) (vrIntro (.natLit 0))) with
          verifyRoots := [verifiedName, sn! "Topic.Proofs.verified"] })
      (.invalidVerifyRoot (sn! "Topic.Proofs.verified")
        "verify root must be <Verify module>.verified") = true ∧
    failsWith (audit noSourceConfig { corePkg with verifyRoots := [verifiedName, instColorName] })
      (.invalidVerifyRoot instColorName "verify root must be a theorem") = true ∧
    failsWith (audit noSourceConfig { corePkg with verifyRoots := [verifiedName, sn! "Ghost.root"] })
      (.unknownConstant (sn! "Ghost.root")) = true := by decide +kernel

theorem claimRoot_rules :
    isOk (audit noSourceConfig { corePkg with claimRoots := [lemmaName] }) = true ∧
    failsWith (audit noSourceConfig
        { corePkg with claimRoots := [sn! "Anneal.TheoryHelper.helperLemma"] })
      (.invalidVerifyRoot (sn! "Anneal.TheoryHelper.helperLemma")
        "claim root declared in a theory or test module") = true := by decide +kernel

/-! ## Imports: provenance, modifiers, direction, cycles, closure -/

def importPkg (imp : ImportSpec) : PackageAuditInput :=
  pkgWithProofs (addImports proofsModule [imp])

theorem foreign_and_modified_imports_rejected :
    failsWith (audit noSourceConfig (importPkg { module := sn! "Evil.Mod" }))
      (.foreignImport proofsMod (sn! "Evil.Mod")) = true ∧
    failsWith (audit noSourceConfig (importPkg { module := sn! "Lean.Elab.Command" }))
      (.foreignImport proofsMod (sn! "Lean.Elab.Command")) = true ∧
    failsWith (audit noSourceConfig (importPkg { module := sn! "Lean" }))
      (.foreignImport proofsMod (sn! "Lean")) = true ∧
    isOk (audit noSourceConfig (importPkg { module := sn! "Std.Data.HashMap" })) = true ∧
    failsWith (audit noSourceConfig (importPkg { module := defsMod, isExported := false }))
      (.forbiddenImportModifier proofsMod defsMod "private") = true ∧
    failsWith (audit noSourceConfig (importPkg { module := sn! "Init", isExported := false }))
      (.forbiddenImportModifier proofsMod (sn! "Init") "private") = true ∧
    failsWith (audit noSourceConfig (importPkg { module := defsMod, isMeta := true }))
      (.forbiddenImportModifier proofsMod defsMod "meta") = true ∧
    isOk (audit noSourceConfig (importPkg { module := sn! "Init", isMeta := true })) = true := by
  decide +kernel

def testsMod : SymName := sn! "Topic.Tests"

theorem import_cycles_and_role_direction_rejected :
    failsWith (audit noSourceConfig (importPkg { module := proofsMod }))
      (.importCycle proofsMod) = true ∧
    failsWith (audit noSourceConfig
        { baseEnv := standardBaseDecls,
          modules := [mkModule (sn! "Proof.A") .proof [] [sn! "Proof.B"],
            mkModule (sn! "Proof.B") .proof [] [sn! "Proof.A"]] })
      (.importCycle (sn! "Proof.A")) = true ∧
    failsWith (audit noSourceConfig
        { corePkg with modules := [defsModule, addImports theoryModule [{ module := proofsMod }],
            proofsModule, verifyModule] })
      (.forbiddenImportDirection theoryMod "theory" proofsMod "proof") = true ∧
    failsWith (audit noSourceConfig
        { corePkg with modules := [defsModule, theoryModule, proofsModule,
            addImports verifyModule [{ module := testsMod }],
            mkModule testsMod .test [] [sn! "Init"]] })
      (.forbiddenImportDirection verifyMod "verify" testsMod "test") = true ∧
    failsWith (audit noSourceConfig
        { corePkg with modules := [addImports defsModule [{ module := theoryMod }], theoryModule,
            proofsModule, verifyModule] })
      (.forbiddenImportDirection defsMod "defsExempt" theoryMod "theory") = true := by
  decide +kernel

def specLemma : SymName := sn! "Topic.Spec.usesProof"

/-- The import rules bind what declarations mention, not only what headers declare. -/
theorem reference_outside_import_closure_rejected :
    failsWith (audit noSourceConfig (withSpec [mkThm specLemma trueE (.const lemmaName)]))
      (.referenceOutsideImportClosure specMod specLemma lemmaName proofsMod) = true ∧
    failsWith (audit noSourceConfig
        (withSpec [mkThm specLemma trueE (.const lemmaName)] [sn! "Init", sn! "Topic.Proofs"]))
      (.forbiddenImportDirection specMod "spec" proofsMod "proof") = true ∧
    failsWith (audit noSourceConfig
        { corePkg with modules := [defsModule,
            addConsts theoryModule [mkThm (sn! "Anneal.TheoryHelper.peek") trueE (.const lemmaName)],
            proofsModule, verifyModule] })
      (.referenceOutsideImportClosure theoryMod (sn! "Anneal.TheoryHelper.peek") lemmaName
        proofsMod) = true ∧
    importClosureContains corePkg verifyMod defsMod = true ∧
    importClosureContains corePkg verifyMod theoryMod = true ∧
    importClosureContains corePkg defsMod proofsMod = false := by decide +kernel

/-! ## Extension entries: foreign targets, dangling and borrowed declarations, scopes -/

def defsPkg (es : List EnvExtEntry) : PackageAuditInput :=
  { corePkg with modules := [addExts defsModule es, theoryModule, proofsModule, verifyModule] }

def subFn : SymName := sn! "Topic.Proofs.Sub.fn"

theorem extension_entry_hardening :
    -- a definitions module may not touch imported classes or types beyond plain instances
    failsWith (audit noSourceConfig (defsPkg [.defaultInstanceEntry instColorName (sn! "Inhabited")]))
      (.forbiddenInstanceOrCoe defsMod "default_instance_of_imported_target" instColorName) = true ∧
    failsWith (audit noSourceConfig
        (defsPkg [.scopedInstanceEntry instColorName (sn! "Inhabited") defsMod]))
      (.forbiddenInstanceOrCoe defsMod "scoped_instance_of_imported_target" instColorName) = true ∧
    failsWith (audit noSourceConfig
        (defsPkg [.coeEntry instColorName SymName.natName SymName.boolName]))
      (.forbiddenInstanceOrCoe defsMod "coe_between_imported_types" instColorName) = true ∧
    isOk (audit noSourceConfig (defsPkg [.coeEntry instColorName colorName SymName.natName,
      .defaultInstanceEntry instColorName colorName,
      .scopedInstanceEntry instColorName colorName defsMod])) = true ∧
    -- hooks and macros are refused in a definitions module too
    failsWith (audit noSourceConfig (defsPkg [.initializeEntry instColorName false]))
      (.forbiddenInitOrCodegenHook defsMod "initialize" instColorName) = true ∧
    failsWith (audit noSourceConfig (defsPkg [.macroEntry instColorName]))
      (.forbiddenMacroOrElab defsMod "macro" instColorName) = true ∧
    failsWith (audit noSourceConfig (defsPkg [.reducibilityOverride SymName.natSuccName]))
      (.forbiddenReducibilityOverride defsMod SymName.natSuccName) = true ∧
    -- a dangling declaration, and a declaration borrowed from a child-namespace module
    failsWith (audit noSourceConfig (extPkg (.instanceEntry (sn! "Topic.Proofs.ghost") mutAName false)))
      (.forbiddenInstanceOrCoe proofsMod "imported_instance" (sn! "Topic.Proofs.ghost")) = true ∧
    failsWith (audit noSourceConfig
        { corePkg with modules := [defsModule, theoryModule,
            addExts proofsModule [.instanceEntry subFn mutAName false], verifyModule,
            mkModule (sn! "Topic.Proofs.Sub") .proof [mkDef subFn natE (.natLit 0)] [sn! "Init"]] })
      (.forbiddenInstanceOrCoe proofsMod "imported_instance" subFn) = true ∧
    -- a scope namespace that is a package module outside the import closure
    failsWith (audit noSourceConfig
        (defsPkg [.scopedInstanceEntry instColorName colorName proofsMod]))
      (.referenceOutsideImportClosure defsMod instColorName instColorName proofsMod) = true := by
  decide +kernel

theorem extraConstNames_hygiene_rejected :
    failsWith (audit noSourceConfig (pkgWithProofs { proofsModule with extraConstNames := [.anonymous] }))
      (.anonymousConstantName proofsMod) = true ∧
    failsWith (audit noSourceConfig
        (pkgWithProofs { proofsModule with extraConstNames := [sn! "Topic.Proofs.x", sn! "Topic.Proofs.x"] }))
      (.duplicateConstName proofsMod (sn! "Topic.Proofs.x")) = true ∧
    failsWith (audit noSourceConfig
        (pkgWithProofs { proofsModule with extraConstNames := [lemmaName] }))
      (.duplicateConstName proofsMod lemmaName) = true ∧
    failsWith (audit noSourceConfig
        (pkgWithProofs { proofsModule with extraConstNames := [sn! "Topic.Defs.claimIdx"] }))
      (.extraConstNameProvenance proofsMod (sn! "Topic.Defs.claimIdx") "claims a declared constant")
      = true ∧
    isOk (audit noSourceConfig
      (pkgWithProofs { proofsModule with extraConstNames := [sn! "Topic.Proofs._cstage1"] })) = true := by
  decide +kernel

/-! ## `_unsafe_rec` companions -/

def recName : SymName := sn! "Topic.Proofs.safeRecFn._unsafe_rec"

/-- The proof module with another record in place of the `_unsafe_rec` companion. -/
def recPkg (rec : ConstantRecord) : PackageAuditInput :=
  pkgWithProofs { proofsModule with constants := proofsModule.constants.dropLast ++ [rec] }

def recWith (val : ExprSkeleton) : ConstantRecord :=
  { mkDef recName natE val with safety := .partialDecl }

/-- A companion must be a `partial` definition with its parent's type, and its body obeys
the dependency rules even though it is never replayed. -/
theorem unsafeRec_companion_sanitized :
    failsWith (audit noSourceConfig (recPkg { mkDef recName falseE (.const recName) with safety := .partialDecl }))
      (.unsafeOrPartialDecl proofsMod recName) = true ∧
    failsWith (audit noSourceConfig
        (recPkg { name := recName, kind := .axiomDecl, type := natE, safety := .partialDecl }))
      (.unsafeOrPartialDecl proofsMod recName) = true ∧
    failsWith (audit noSourceConfig (recPkg { mkDef recName natE (.const recName) with safety := .unsafeDecl }))
      (.unsafeOrPartialDecl proofsMod recName) = true ∧
    failsWith (audit noSourceConfig (recPkg (recWith sorryE)))
      (.forbiddenAxiom recName SymName.sorryAxName initPrelude) = true ∧
    failsWith (audit noSourceConfig (recPkg (recWith (c! "Lean.trustCompiler"))))
      (.forbiddenNativeReductionAxiom recName SymName.trustCompilerName) = true ∧
    failsWith (audit provisionalNoSource (recPkg (recWith (c! "Lean.trustCompiler"))))
      (.forbiddenNativeReductionAxiom recName SymName.trustCompilerName) = true ∧
    failsWith (audit noSourceConfig (recPkg (recWith (c! "Ghost.DoesNotExist"))))
      (.unknownConstant (sn! "Ghost.DoesNotExist")) = true ∧
    isCodegenUnsafeRecInMod proofsModule (recWith (.const recName)) = true := by decide +kernel

/-! ## Test modules, assumptions, and per-item status -/

def localAxName : SymName := sn! "Topic.Tests.localAx"
def testThmName : SymName := sn! "Topic.Tests.check"
def testAxiomsConfig : AuditConfig := { allowLocalTestAxioms := true, requireSources := false }

def testPkg (consts : List ConstantRecord) : PackageAuditInput :=
  plusModule (mkModule testsMod .test consts [sn! "Init", sn! "Topic.Proofs"])

theorem test_module_closures_and_axioms :
    failsWith (audit noSourceConfig (testPkg [mkThm testThmName trueE sorryE]))
      (.forbiddenAxiom testThmName SymName.sorryAxName initPrelude) = true ∧
    failsWith (audit noSourceConfig (testPkg [mkAxiom localAxName trueE]))
      (.forbiddenAxiom localAxName localAxName testsMod) = true ∧
    isOk (audit testAxiomsConfig
      (testPkg [mkAxiom localAxName trueE, mkThm testThmName trueE (.const localAxName)])) = true ∧
    failsWith (audit testAxiomsConfig (testPkg [mkThm testThmName trueE (c! "Lean.ofReduceBool")]))
      (.forbiddenNativeReductionAxiom testThmName SymName.ofReduceBoolName) = true := by
  decide +kernel

def hwMod : SymName := sn! "Assumptions.Hw"
def mmioName : SymName := sn! "Assumptions.Hw.mmioOk"
def mixedConfig : AuditConfig :=
  { allowAssumptions := true, allowProvisionalNative := true, allowLocalTestAxioms := true,
    requireSources := false }

/-- `(fun _ : ty => body) dep`: a proof term that mentions `dep`. -/
def viaProof (ty : ExprSkeleton) (dep : SymName) (body : ExprSkeleton) : ExprSkeleton :=
  .app (.lam ty body) (.const dep)

def verifyItem (name : SymName) (proof : ExprSkeleton) (imports : List SymName) : ModuleInventory :=
  mkModule name .verify [mkThm name.verifiedRoot (vr (.natLit 0)) proof]
    ([sn! "Init", sn! "Trusted.Core"] ++ imports)

/-- One clean item, one that uses an assumption, one native, one both; plus a test that
leans on the assumption module. -/
def mixedPkg (withTest : Bool) : PackageAuditInput :=
  { baseEnv := standardBaseDecls,
    modules := [mkModule hwMod .assumptions [mkAxiom mmioName trueE] [sn! "Init"], nativeModule,
      verifyItem (sn! "Verify.Clean") (vrIntro (.natLit 0)) [],
      verifyItem (sn! "Verify.Cond") (viaProof trueE mmioName (vrIntro (.natLit 0))) [hwMod],
      verifyItem (sn! "Verify.Native") (verifiedVia usesNativeName) [sn! "Proof.Native"],
      verifyItem (sn! "Verify.Both")
        (viaProof trueE mmioName (verifiedVia usesNativeName)) [hwMod, sn! "Proof.Native"]] ++
      (if withTest then
        [mkModule testsMod .test [mkThm testThmName trueE (.const mmioName)] [sn! "Init", hwMod]]
       else []),
    verifyRoots := [sn! "Verify.Clean.verified", sn! "Verify.Cond.verified",
      sn! "Verify.Native.verified", sn! "Verify.Both.verified"] }

/-- Per-item status in a mixed package: the clean item stays unconditional, and an item
that reaches both a native axiom and an assumption reports both. A test module may not
use another module's assumption axiom. -/
theorem mixed_package_per_item_status_and_isolation :
    itemStatuses mixedConfig (mixedPkg false) =
      some [.verifiedUnconditional, .verifiedConditional, .provisionalNative,
        .provisionalNativeConditional] ∧
    reachedAxiomsOfAudit mixedConfig (mixedPkg false) = some [mmioName, nativeAxName] ∧
    failsWith (audit mixedConfig (mixedPkg true))
      (.testModuleForeignAxiom testsMod testThmName mmioName) = true ∧
    failsWith (audit { mixedConfig with allowAssumptions := false } (mixedPkg false))
      (.forbiddenAxiom mmioName mmioName hwMod) = true := by decide +kernel

/-! ## Reserved origins, padded closures, fail-closed walks, kernel edges -/

def eqAuxName : SymName := sn! "Topic.Proofs.fn.eq_1"

theorem reserved_origin_claims_rejected :
    failsWith (audit noSourceConfig (pkgWithProofs (addConsts proofsModule
        [{ mkThm eqAuxName trueE trueIntroE with originModule := some (sn! "Ghost.Mod") }])))
      (.reservedOriginMissingSibling proofsMod eqAuxName (sn! "Ghost.Mod")) = true ∧
    failsWith (audit noSourceConfig (pkgWithProofs (addConsts proofsModule
        [{ mkThm pubName trueE trueIntroE with originModule := some defsMod }])))
      (.reservedOriginMissingSibling proofsMod pubName defsMod) = true ∧
    failsWith (audit noSourceConfig (withSpec
        [{ mkThm (sn! "Topic.Spec.fn.eq_1") trueE trueIntroE with originModule := some theoryMod }]))
      (.referenceOutsideImportClosure specMod (sn! "Topic.Spec.fn.eq_1") (sn! "Topic.Spec.fn.eq_1")
        theoryMod) = true ∧
    isOk (audit noSourceConfig (pkgWithProofs (addConsts proofsModule
      [{ mkThm eqAuxName trueE trueIntroE with originModule := some defsMod }]))) = true := by
  decide +kernel

def padType : Nat → ExprSkeleton
  | 0 => trueE
  | n + 1 => .pi trueE (padType n)

def padProof : Nat → ExprSkeleton
  | 0 => sorryE
  | n + 1 => .lam trueE (padProof n)

def paddedName : SymName := sn! "Topic.Proofs.padded"

/-- A well-typed theorem `True → … → True` (24 binders) ending in `sorryAx`: replay accepts
it, a walk that stops after a fixed number of steps would miss it, and the fail-closed walk
reports `sorryAx`. With too little fuel the walk errors instead of returning a partial set. -/
theorem padded_closure_and_fuel_exhaustion_fail_closed :
    isOk (replayCleanEnv (fun _ => false) standardBaseEnv [mkThm paddedName (padType 24) (padProof 24)])
      = true ∧
    failsWith (audit noSourceConfig (withProofThm paddedName (padType 24) (padProof 24)))
      (.forbiddenAxiom paddedName SymName.sorryAxName initPrelude) = true ∧
    failsWith (walkGraph (packageEnv corePkg) verifiedName closureExpand 1 [verifiedName] [])
      (.closureFuelExhausted verifiedName SymName.verificationResultName) = true ∧
    isOk (walkGraph (packageEnv corePkg) verifiedName closureExpand
      (closureFuel (packageEnv corePkg)) [verifiedName] []) = true := by decide +kernel

def kA : SymName := sn! "Topic.K.a"
def kB : SymName := sn! "Topic.K.b"
def kF : SymName := sn! "Topic.K.f"
def eqNat (a b : ExprSkeleton) : ExprSkeleton := .app (.app (c! "Eq") a) b

/-- The kernel model: dependency cycles and missing dependencies are diagnosed; a data
function is typed and its application to a literal reduces; ill-typed terms, functions
over non-data domains, projections, and oversized universes are rejected; a recursor is
admitted only in canonical form. -/
theorem kernel_model_edges :
    failsWith (replayCleanEnvOrdered (fun _ => false) standardBaseEnv
        [mkDef kA natE (.const kB), mkDef kB natE (.const kA)]) (.cyclicDependency kA) = true ∧
    failsWith (replayCleanEnvOrdered (fun _ => false) standardBaseEnv
        [mkDef kA natE (c! "Ghost.missing")]) (.unknownConstant (sn! "Ghost.missing")) = true ∧
    isOk (replayCleanEnvOrdered (fun _ => false) standardBaseEnv
      [mkThm kA (eqNat (.app (.const kF) (.natLit 3)) (.natLit 3)) (.app (c! "Eq.refl") (.natLit 3)),
       mkDef kF (.pi natE natE) (.lam natE (.bvar 0))]) = true ∧
    failsWith (replayCleanEnvOrdered (fun _ => false) standardBaseEnv
        [mkDef kF (.pi natE natE) (.lam natE (.bvar 0)),
         mkThm kA (eqNat (.app (.const kF) (.natLit 3)) (.natLit 4)) (.app (c! "Eq.refl") (.natLit 3))])
      (.kernelTypeError kA "theorem proof term type mismatch") = true ∧
    failsWith (replayCleanEnv (fun _ => false) standardBaseEnv
        [mkDef kF natE (.lam (.pi natE natE) (.natLit 0))])
      (.kernelTypeError kF "abstraction over a non-data binder must produce a proof") = true ∧
    failsWith (replayCleanEnv (fun _ => false) standardBaseEnv
        [mkDef kF (.pi (.pi natE natE) natE) (.lam (.pi natE natE) (.natLit 0))])
      (.kernelTypeError kF "function type over a non-data domain must be a proposition") = true ∧
    failsWith (replayCleanEnv (fun _ => false) standardBaseEnv
        [mkThm kA (.pi (.pi natE natE) natE) trueIntroE])
      (.kernelTypeError kA "function type over a non-data domain must be a proposition") = true ∧
    failsWith (replayCleanEnv (fun _ => false) standardBaseEnv
        [mkDef kA natE (.proj SymName.natName 0 (.natLit 0))])
      (.kernelTypeError kA "projections are outside the modeled kernel fragment") = true ∧
    failsWith (replayCleanEnv (fun _ => false) standardBaseEnv [mkAxiom kA trueE])
      (.forbiddenAxiom kA kA .anonymous) = true ∧
    failsWith (replayCleanEnv (fun _ => false) standardBaseEnv
        [tDecl, tMkDecl, { tRecDecl with type := .pi (.const tName) trueE }])
      (.kernelTypeError tRecName "non-canonical recursor") = true ∧
    failsWith (replayCleanEnv (fun _ => false) standardBaseEnv [mkThm SymName.falseName trueE trueIntroE])
      (.kernelTypeError SymName.falseName "declaration already present in the replay environment")
      = true := by decide +kernel

/-! ## Pass `B1` hardening regressions -/

/-- Core token `/\` before a block comment and token boundaries around `«...»` escaped
identifiers. (`.r` before a string moved to `passA1_token_boundary_desync_fails_closed`.) -/
theorem passB1_lexer_and_guillemet_desync_rejected :
    flags (chars! "theorem t : True/\\/- \" -/True := ⟨trivial, trivial⟩\nset_option debug.skipKernelTC true in\ntheorem bad : False := trivial -- \"")
      "debug.skipKernelTC" = true ∧
    flags (chars! "section «Foo»set_option debug.byAsSorry true in\ntheorem bad : False := by skip\nend «Foo»")
      "debug.byAsSorry" = true ∧
    flags (chars! "namespace «Foo»unsafe def evil : Nat := 0\nend «Foo»")
      "unsafe" = true ∧
    flags (chars! "open «Nat»partial def loop (x : Nat) : Nat := loop x")
      "partial" = true ∧
    flags (chars! "section «Foo»run_cmd pure ()\nend «Foo»")
      "run_cmd" = true ∧
    flags (chars! "def a := f«unsafe»") "unsafe" = true ∧
    flags (chars! "def a := r«unsafe»") "unsafe" = true ∧
    flags (chars! "set_option «debug».«skipKernelTC» true in\ntheorem bad : False := trivial")
      "debug.skipKernelTC" = true ∧
    isOk (scan (chars! "theorem t : True/\\/- comment -/True := ⟨trivial, trivial⟩")) = true ∧
    isOk (scan (chars! "set_option «pp».«all» true in\ndef x := 1")) = true ∧
    isOk (scan (chars! "def a := «x»r\"\\\"\ndef b := 1")) = true := by decide +kernel

/-- Definitions and opaque declarations must have a well-typed sort annotation (`kernelSortOf`),
not merely a type whose β-reduction ignores an ill-typed binder domain. -/
theorem passB1_kernel_defn_opaque_ill_typed_type_rejected :
    let illType : ExprSkeleton := .app (.lam (.natLit 0) natE) (.natLit 0)
    failsWith (audit noSourceConfig
        (pkgWithProofs (addConsts proofsModule [mkDef (sn! "Topic.Proofs.badDef") illType (.natLit 0)])))
      (.kernelTypeError (sn! "Topic.Proofs.badDef") "type expected") = true ∧
    failsWith (audit noSourceConfig
        (pkgWithProofs (addConsts proofsModule [mkOpaque (sn! "Topic.Proofs.badOp") illType (.natLit 0)])))
      (.kernelTypeError (sn! "Topic.Proofs.badOp") "type expected") = true := by decide +kernel

def testRecParentName : SymName := sn! "Topic.Tests.testRec"
def testRecCompName : SymName := sn! "Topic.Tests.testRec._unsafe_rec"

def testRecMod (val : ExprSkeleton) (imports : List SymName) (extra : List ConstantRecord := []) :
    ModuleInventory :=
  mkModule testsMod .test
    (extra ++ [mkDef testRecParentName natE (.natLit 0),
      { mkDef testRecCompName natE val with safety := .partialDecl }])
    ([sn! "Init"] ++ imports)

/-- `_unsafe_rec` companions are checked over their entire transitive `DepReaches` closure
(catching `sorryAx` hidden behind a `baseEnv` helper) and obey the `.test`-module policy
(blocking foreign `Assumptions.*` and `Proof.Native` axioms in test companions while still
admitting local test axioms when `allowLocalTestAxioms = true`). -/
theorem passB1_unsafeRec_transitive_and_test_policy_rejected :
    let baseWithWrapper := standardBaseDecls ++ [
      { name := sn! "Trusted.BaseHelper", kind := .defnDecl, type := natE,
        value? := some (.app (.lam trueE (.natLit 0)) sorryE),
        originModule := some (sn! "Trusted.Core") }]
    failsWith (audit noSourceConfig
        { corePkg with
          baseEnv := baseWithWrapper,
          modules := [defsModule, theoryModule,
            { proofsModule with
              constants := proofsModule.constants.dropLast ++
                [recWith (c! "Trusted.BaseHelper")] },
            verifyModule] })
      (.forbiddenAxiom recName SymName.sorryAxName initPrelude) = true ∧
    failsWith (audit { conditionalConfig with requireSources := false }
        { baseEnv := standardBaseDecls,
          modules := [mkModule hwMod .assumptions [mkAxiom mmioName trueE] [sn! "Init"],
            testRecMod (viaProof trueE mmioName (.natLit 0)) [hwMod]] })
      (.testModuleForeignAxiom testsMod testRecCompName mmioName) = true ∧
    failsWith (audit provisionalNoSource
        { baseEnv := standardBaseDecls,
          modules := [nativeModule,
            testRecMod (viaProof (eqBoolTrue (c! "Bool.true")) nativeAxName (.natLit 0))
              [sn! "Proof.Native"]] })
      (.forbiddenNativeReductionAxiom testRecCompName nativeAxName) = true ∧
    isOk (audit testAxiomsConfig
        { baseEnv := standardBaseDecls,
          modules := [testRecMod (viaProof trueE localAxName (.natLit 0)) []
            [mkAxiom localAxName trueE]] }) = true := by decide +kernel

/-- Extension entries may not attach to an un-replayed `partial` `_unsafe_rec` companion,
and `extraConstNames` must be distinct across modules. -/
theorem passB1_unsafeRec_ext_target_and_cross_module_extraConstNames_rejected :
    failsWith (audit noSourceConfig (extPkg (.instanceEntry recName mutAName false)))
      (.forbiddenInstanceOrCoe proofsMod "imported_instance" recName) = true ∧
    failsWith (audit noSourceConfig (extPkg (.reducibilityOverride recName)))
      (.forbiddenReducibilityOverride proofsMod recName) = true ∧
    failsWith (audit noSourceConfig
        { corePkg with
          modules := [{ defsModule with extraConstNames := [sn! "Shared._cstage1"] },
            theoryModule,
            { proofsModule with extraConstNames := [sn! "Shared._cstage1"] },
            verifyModule] })
      (.extraConstNameProvenance defsMod (sn! "Shared._cstage1")
        "duplicate extraConstName across modules") = true := by decide +kernel

def nestedBetaFalse : Nat → ExprSkeleton
  | 0 => c! "Bool.false"
  | n + 1 => .app (.lam boolE (nestedBetaFalse n)) (c! "Bool.true")

/-- Provisional native refutation scales its fuel with the expression's size (refuting deep
β-redex chains), provisional admission requires a strictly interior `._native.` name, and
`allowReplayAxiom` enforces those same guards independently. -/
theorem passB1_provisional_native_fuel_and_interior_name_hardened :
    failsWith (audit provisionalNoSource (nativeProofs (eqBoolTrue (nestedBetaFalse 130))))
      (.invalidNativeAxiomType provAx provAx) = true ∧
    failsWith (audit provisionalNoSource
        (pkgWithProofs (addConsts proofsModule
          [mkAxiom (sn! "_native") (eqBoolTrue (c! "Bool.true"))])))
      (.forbiddenNativeReductionAxiom (sn! "_native") (sn! "_native")) = true ∧
    failsWith (audit provisionalNoSource
        (pkgWithProofs (addConsts proofsModule
          [mkAxiom (sn! "_native.ax") (eqBoolTrue (c! "Bool.true"))])))
      (.forbiddenNativeReductionAxiom (sn! "_native.ax") (sn! "_native.ax")) = true ∧
    failsWith (audit provisionalNoSource
        (pkgWithProofs (addConsts proofsModule
          [mkAxiom (sn! "Topic.Proofs._native") (eqBoolTrue (c! "Bool.true"))])))
      (.forbiddenNativeReductionAxiom (sn! "Topic.Proofs._native") (sn! "Topic.Proofs._native"))
      = true ∧
    allowReplayAxiom provisionalNoSource corePkg (mkAxiom (sn! "Topic.Proofs.sneaky") trueE)
      = false ∧
    allowReplayAxiom provisionalNoSource corePkg
      (mkAxiom (sn! "_native") (eqBoolTrue (c! "Bool.true"))) = false := by decide +kernel

/-! ## Pass `A1` hardening regressions -/

/-- Token boundaries the scanner cannot decide are errors. Every source that hides
`set_option debug.skipKernelTC true` here was accepted by the scanner before this pass, and
Lean 4.34.1 compiles the declaration after it as live code. `=` and `!=` never absorb a
slash, so there the block comment is real and the option stays visible. -/
theorem passA1_token_boundary_desync_fails_closed :
    -- `<<<` or `=<<` and then a line comment, against `<`, `<-`, `-`: Lean 4.34.1 accepts both
    lexFails (chars! "def f (a b : Nat) : Nat := a <<<-- \"\n  b\nset_option debug.skipKernelTC true in\ntheorem bad : True := trivial -- \"") = true ∧
    lexFails (chars! "def h (f : Nat → Option Nat) (x : Option Nat) : Option Nat := f =<<-- \"\n  x\nset_option debug.skipKernelTC true in\ntheorem bad : True := trivial -- \"") = true ∧
    lexFails (chars! "def f := x <-- set_option debug.skipKernelTC true\n") = true ∧
    lexFails (chars! "def T := { x : Int //-2 < x }\nset_option debug.skipKernelTC true in\ndef b := 1 -- -/") = true ∧
    lexFails (chars! "theorem t : a \\/- b\nset_option debug.skipKernelTC true in\ndef b := 1 -- -/") = true ∧
    -- `#check` ends without a boundary, so a raw string or character literal may follow
    lexFails (chars! "#checkr\"\\\" \nset_option debug.skipKernelTC true in\ntheorem bad : True := trivial -- \"") = true ∧
    lexFails (chars! "#check'\"'\nset_option debug.skipKernelTC true in\ntheorem bad : True := trivial -- \"") = true ∧
    lexFails (chars! "#checkr#\"x\"#") = true ∧
    lexFails (chars! "#eval2 + 2") = true ∧
    lexFails (chars! "def r := 1\ndef a := r#check'\"'\nset_option debug.skipKernelTC true in\ntheorem bad : True := trivial -- \"") = true ∧
    -- scoped tokens of opened core namespaces: `#'`, `/.`, `~m`, `+1]`, `\math`, three backticks
    lexFails (chars! "open BitVec\ntheorem t1 : True := by first | exact absurd (3#'\"' \") | trivial\nset_option debug.skipKernelTC true in\ntheorem bad : True := trivial -- \"") = true ∧
    lexFails (chars! "open Rat\ntheorem t1 : True := by first | exact absurd (1 /.r\"\\\") | trivial\nset_option debug.skipKernelTC true in\ntheorem bad : True := trivial -- \"") = true ∧
    lexFails (chars! "import Std\nopen Std.HashMap\ntheorem t1 : True := by first | exact absurd (a ~mr\"\\\") | trivial\nset_option debug.skipKernelTC true in\ntheorem bad : True := trivial -- \"") = true ∧
    lexFails (chars! "open Int\ndef a := -[0+1]'x'") = true ∧
    lexFails (chars! "def a := s \\math") = true ∧
    lexFails (chars! "def a := ```x") = true ∧
    -- after a dot, `r"` is raw (`1...r"…"`) or not (`(.r"…")`) depending on the parser
    lexFails (chars! "theorem t1 : True := by first | exact absurd (1...r\"\\\") | trivial\nset_option debug.skipKernelTC true in\ntheorem bad : True := trivial -- \"") = true ∧
    lexFails (chars! "def x := .r\"\\\"\"\nset_option debug.skipKernelTC true in\ntheorem bad : True := trivial -- \"") = true ∧
    lexFails (chars! "def f (s : S) := (s).r\"\\\"\"\nset_option debug.skipKernelTC true in\ntheorem bad : True := trivial -- \"") = true ∧
    lexFails (chars! "def f (p : S × Nat) := p.1.r\"\\\"\"\nset_option debug.skipKernelTC true in\ntheorem bad : True := trivial -- \"") = true ∧
    lexFails (chars! "def x := .r#\"x\"#") = true ∧
    lexFails (chars! "def x := y //.r") = true ∧
    flags (chars! "def k (a b : Nat) : Prop := a =/- \" -/ b\nset_option debug.skipKernelTC true in\ntheorem bad : True := trivial -- \"")
      "debug.skipKernelTC" = true ∧
    flags (chars! "def k (a b : Nat) : Bool := a !=/- \" -/ b\nset_option debug.skipKernelTC true in\ntheorem bad : True := trivial -- \"")
      "debug.skipKernelTC" = true := by decide +kernel

/-- Commands and attributes that add syntax, tokens, or macros are rejected even when
`local`: `local notation "x\""` leaves no extension entry, yet makes `x"` a token, so the
string that seems to follow it hides live code from the scanner. -/
theorem passA1_syntax_extension_commands_rejected :
    flags (chars! "local notation \"x\\\"\" => (0 : Nat)\ndef a : Nat := x\"\nset_option debug.skipKernelTC true in\ntheorem bad : True := trivial -- \"") "notation" = true ∧
    flags (chars! "local infixl:65 \" +/- \" => Nat.add\ndef b : Nat := 1 +/- 2\nset_option debug.skipKernelTC true in\ntheorem bad : True := trivial -- -/") "infixl" = true ∧
    flags (chars! "infix:50 \" ≈≈ \" => Eq") "infix" = true ∧
    flags (chars! "scoped infixr:67 \" ::: \" => List.cons") "infixr" = true ∧
    flags (chars! "prefix:max \"√\" => id") "prefix" = true ∧
    flags (chars! "postfix:max \"!!\" => id") "postfix" = true ∧
    flags (chars! "local syntax \"quux\" : term") "syntax" = true ∧
    flags (chars! "local macro \"quux\" : term => `(0)") "macro" = true ∧
    flags (chars! "macro_rules | `(quux) => `(0)") "macro_rules" = true ∧
    flags (chars! "elab \"quux\" : term => pure x") "elab" = true ∧
    flags (chars! "elab_rules : term | `(quux) => pure x") "elab_rules" = true ∧
    flags (chars! "declare_syntax_cat quux") "declare_syntax_cat" = true ∧
    flags (chars! "binder_predicate x \" ≺ \" y:term => `($x ≺ $y)") "binder_predicate" = true ∧
    flags (chars! "@[local term_parser] def p := q") "term_parser" = true ∧
    flags (chars! "attribute [local builtin_command_parser] p") "builtin_command_parser" = true ∧
    flags (chars! "@[local macro k] def m := n") "macro" = true := by decide +kernel

/-- No false positives from the new rules on ordinary code. -/
theorem passA1_no_false_positive :
    isOk (scan (chars! "#check Nat.succ\n#print axioms foo'\n#guard_msgs in\n#check! f x\ndef v := #[1, 2] ++ #v[3].toArray")) = true ∧
    isOk (scan (chars! "def a := x <<< 2 + (y >>> 1) - z\ndef f := do let x <- g; let y ← h x; pure (x, y) -- done")) = true ∧
    isOk (scan (chars! "theorem t : (a <-> b) /\\ (c \\/ d) /\\ { x : Nat // x < 2 } = T := h -- note")) = true ∧
    isOk (scan (chars! "def a := x.r + p.1.r + (· + ·) 1 2 + ~~~m + 5#8 + s \\ t + a / b /- c -/ + `Nat.succ")) = true ∧
    isOk (scan (chars! "def prefixLen := 1\ndef x := xs.isPrefixOf ys && macroScopes.notations.syntaxTree.parser_state")) = true := by
  decide +kernel

/-! ## Pass `B2` hardening regressions -/

def smuggledStdMod : SymName := SymName.mk [chars! "Std.Evil"]
def smuggledShadowNat : SymName := SymName.mk [chars! "Topic.Proofs.Nat.succ"]
def emptyPartName : SymName := SymName.mk [[]]
def smuggledA : SymName := SymName.mk [chars! "Topic.Proofs.a"]
def normalA : SymName := sn! "Topic.Proofs.a"
def smuggledBaseNat : SymName := SymName.mk [chars! "Nat.evil"]
def smuggledExtra : SymName := SymName.mk [chars! "Topic.Proofs.x"]
def smuggledPeer : SymName := SymName.mk [chars! "Proof.Exploit.b"]

/-- Malformed `SymName` components (empty parts or embedded `.`) cannot spoof module roles,
evade shadowing checks, collide under `toChars`, or smuggle into `baseEnv`, `.all`, or
`extraConstNames`. -/
theorem passB2_symname_component_smuggling_rejected :
    smuggledA ≠ normalA ∧
    smuggledA.toChars = normalA.toChars ∧
    failsWith (audit noSourceConfig (plusModule (mkModule smuggledStdMod .spec [] [sn! "Init"])))
      (.moduleRoleMismatch smuggledStdMod "spec") = true ∧
    failsWith (audit noSourceConfig (withProofThm smuggledShadowNat trueE trueIntroE))
      (.anonymousConstantName proofsMod) = true ∧
    failsWith (audit noSourceConfig (withProofThm emptyPartName trueE trueIntroE))
      (.anonymousConstantName proofsMod) = true ∧
    failsWith (audit noSourceConfig
        (pkgWithProofs (addConsts proofsModule
          [mkThm normalA trueE trueIntroE, mkThm smuggledA trueE trueIntroE])))
      (.anonymousConstantName proofsMod) = true ∧
    failsWith (audit noSourceConfig
        (pkgWithProofs { proofsModule with extraConstNames := [smuggledExtra] }))
      (.anonymousConstantName proofsMod) = true ∧
    failsWith (audit noSourceConfig
        { corePkg with
          baseEnv := corePkg.baseEnv ++ [baseDecl smuggledBaseNat .axiomDecl trueE initCore] })
      (.anonymousConstantName .anonymous) = true ∧
    failsWith (validateReplayInventory (allMod [thmA [mA, smuggledPeer]]))
      (.invalidMutualAll exploitMod mA "malformed entry in .all") = true := by decide +kernel

def uName : SymName := sn! "Proof.Exploit.U"
def uMkName : SymName := sn! "Proof.Exploit.U.mk"
def mutIndT : ConstantRecord := { tDecl with all := [tName, uName] }
def mutIndU : ConstantRecord :=
  { name := uName, kind := .inductDecl [uMkName], type := .sort 1, all := [tName, uName] }
def mutIndUMk : ConstantRecord := { name := uMkName, kind := .ctorDecl uName, type := .const uName }

/-- `Topic.Defs` may not register orphan instances of imported classes (whose type mentions
zero local declarations), and a recursor's `.all` must match its mutual inductive's `.all`. -/
theorem passB2_defs_orphan_instance_and_rec_all_mismatch_rejected :
    failsWith (audit noSourceConfig
        (defsPkg [.instanceEntry (sn! "Topic.Defs.claimIdx") (sn! "OfNat") false]))
      (.forbiddenInstanceOrCoe defsMod "orphan_instance_of_imported_class"
        (sn! "Topic.Defs.claimIdx")) = true ∧
    isOk (audit noSourceConfig corePkg) = true ∧
    failsWith (validateReplayInventory (allMod [mutIndT, tMkDecl, mutIndU, mutIndUMk, tRecDecl]))
      (.invalidMutualAll exploitMod tRecName "recursor .all differs from inductive .all") = true := by
  decide +kernel

def baseGhostAx : SymName := sn! "Topic.Tests.baseGhostAx"

def baseCollisionPkg : PackageAuditInput :=
  { baseEnv := standardBaseDecls ++ [baseDecl baseGhostAx .axiomDecl trueE testsMod],
    modules := corePkg.modules ++
      [mkModule testsMod .test [mkThm testThmName trueE (.const baseGhostAx)] [sn! "Init"]],
    verifyRoots := [verifiedName] }

/-- A `baseEnv` declaration cannot claim the module name of an audited package module, and
`checkTestDep` independently enforces `cfg.allowLocalTestAxioms = true` before admitting any
local test axiom. -/
theorem passB2_baseEnv_module_collision_and_test_axiom_flag_rejected :
    failsWith (audit noSourceConfig baseCollisionPkg) (.duplicateModuleName testsMod) = true ∧
    failsWith (checkTestDep noSourceConfig baseCollisionPkg (packageEnv baseCollisionPkg)
        testsMod testThmName baseGhostAx)
      (.testModuleForeignAxiom testsMod testThmName baseGhostAx) = true ∧
    isOk (checkTestDep testAxiomsConfig (testPkg [mkAxiom localAxName trueE])
      (packageEnv (testPkg [mkAxiom localAxName trueE])) testsMod testThmName localAxName) = true := by
  decide +kernel

def specReqName : SymName := sn! "Topic.Spec.Req"
def shadowSpec : SymName := sn! "Topic.Proofs.Topic.Spec.Req"
def shadowAssump : SymName := sn! "Topic.Proofs.Assumptions.Hw.mmioOk"

/-- `V15` namespace-suffix shadowing protects every statement-side module (`Defs`, `Spec`,
and `Assumptions`), not only `Defs`. -/
theorem passB2_v15_spec_and_assumptions_shadowing_rejected :
    failsWith (audit noSourceConfig
        { corePkg with
          modules := [defsModule, theoryModule,
            mkModule specMod .spec [mkDef specReqName natE (.natLit 0)] [sn! "Init"],
            addConsts proofsModule [mkThm shadowSpec trueE trueIntroE],
            verifyModule] })
      (.forbiddenShadowingOrExport proofsMod "namespace_shadow" shadowSpec) = true ∧
    failsWith (audit { noSourceConfig with allowAssumptions := true }
        { corePkg with
          modules := [defsModule, theoryModule,
            mkModule hwMod .assumptions [mkAxiom mmioName trueE] [sn! "Init"],
            addConsts proofsModule [mkThm shadowAssump trueE trueIntroE],
            verifyModule] })
      (.forbiddenShadowingOrExport proofsMod "namespace_shadow" shadowAssump) = true := by
  decide +kernel

def nestedBetaWrap : Nat → ExprSkeleton → ExprSkeleton
  | 0, body => body
  | n + 1, body => .app (.lam boolE (nestedBetaWrap n body)) (c! "Bool.true")

def chainDefName (k : Nat) : SymName :=
  SymName.mk [chars! "Topic", chars! "Proofs", ['d', Char.ofNat (48 + k)]]

def chainedBoolDefs (leaf : ExprSkeleton) : Nat → List ConstantRecord
  | 0 => [mkDef (chainDefName 0) boolE (nestedBetaWrap 15 leaf)]
  | k + 1 =>
    chainedBoolDefs leaf k ++
      [mkDef (chainDefName (k + 1)) boolE (nestedBetaWrap 15 (.const (chainDefName k)))]

def cycDef : ConstantRecord := mkDef (sn! "Topic.Proofs.cyc") boolE (c! "Topic.Proofs.cyc")

/-- Chained helper definitions (tiny root `e.size = 1`, >150 total β+δ steps) still refute a
false provisional native axiom, accept an honest true chain, and fail closed if reduction
exhausts fuel (e.g. a cyclic definition). -/
theorem passB2_provisional_native_chained_defs_refuted_and_fail_closed :
    failsWith (audit provisionalNoSource
        (nativeProofs (eqBoolTrue (.const (chainDefName 9))) (chainedBoolDefs (c! "Bool.false") 9)))
      (.invalidNativeAxiomType provAx provAx) = true ∧
    isOk (audit provisionalNoSource
        (nativeProofs (eqBoolTrue (.const (chainDefName 9))) (chainedBoolDefs (c! "Bool.true") 9)))
      = true ∧
    nativeAxiomRefutedByKernel ((sn! "Topic.Proofs.cyc", cycDef) :: standardBaseEnv)
      (eqBoolTrue (c! "Topic.Proofs.cyc")) = true := by decide +kernel

/-- Source scanner catches initializers, elaborator/delaborator/unexpander/simproc/unif_hint/
csimp/cpass/export hooks and all `builtin_*` variants, without false positives on ordinary
identifiers like `init` or `builtin_helper`. -/
theorem passB2_sourceScanner_ext_hooks_and_builtin_variants_rejected :
    flags (chars! "initialize pure ()") "initialize" = true ∧
    flags (chars! "builtin_initialize pure ()") "builtin_initialize" = true ∧
    flags (chars! "@[builtin_init myInit] def x : Unit := ()") "builtin_init" = true ∧
    flags (chars! "@[command_elab myCmd] def e := 0") "command_elab" = true ∧
    flags (chars! "@[builtin_command_elab myCmd] def e := 0") "builtin_command_elab" = true ∧
    flags (chars! "@[term_elab myTerm] def e := 0") "term_elab" = true ∧
    flags (chars! "@[tactic_elab myTac] def e := 0") "tactic_elab" = true ∧
    flags (chars! "@[doElem_elab myDo] def e := 0") "doElem_elab" = true ∧
    flags (chars! "@[inductive_elab myInd] def e := 0") "inductive_elab" = true ∧
    flags (chars! "@[delab myApp] def d := 0") "delab" = true ∧
    flags (chars! "@[app_unexpander myApp] def u := 0") "app_unexpander" = true ∧
    flags (chars! "simproc mySimp (0) := f") "simproc" = true ∧
    flags (chars! "dsimproc myDSimp (0) := f") "dsimproc" = true ∧
    flags (chars! "cbv_simproc myCbv (0) := f") "cbv_simproc" = true ∧
    flags (chars! "builtin_simproc mySimp (0) := f") "builtin_simproc" = true ∧
    flags (chars! "simproc_decl mySimp (0)") "simproc_decl" = true ∧
    flags (chars! "unif_hint (x : Nat) where x =?= x |- x =?= x") "unif_hint" = true ∧
    flags (chars! "@[unification_hint] def h := 0") "unification_hint" = true ∧
    flags (chars! "export Nat (add)") "export" = true ∧
    flags (chars! "@[csimp] theorem fg : f = g := rfl") "csimp" = true ∧
    flags (chars! "@[cpass] def p := 0") "cpass" = true ∧
    flags (chars! "declare_simp_like_tactic my_simp") "declare_simp_like_tactic" = true ∧
    flags (chars! "builtin_macro \"foo\" : term => 0") "builtin_macro" = true ∧
    flags (chars! "builtin_syntax \"foo\" : term") "builtin_syntax" = true ∧
    isOk (scan (chars! "def init := 0\ndef initial_value := 1\ndef builtin_helper := 2\ndef exported_flag := 3\ndef unif_helper := 4"))
      = true := by decide +kernel

/-! ## Pass `A2` hardening regressions -/

def premInstName : SymName := sn! "Topic.Defs.premInst"

/-- `Topic.Defs` with one more instance declaration of the given type and value. -/
def defsInstPkg (ty val : ExprSkeleton) : PackageAuditInput :=
  { corePkg with modules :=
      [addExts (addConsts defsModule [mkDef premInstName ty val])
         [.instanceEntry premInstName (sn! "Inhabited") false],
       theoryModule, proofsModule, verifyModule] }

/-- What ties an instance to its module is a local name that is not a reducible alias: the
class itself, or for an imported class a name in the conclusion of the instance's type.
Lean 4.34.1 compiles `theorem hijacked : (0 : Nat) = 1 := rfl` after each rejected shape:
`instance (priority := high) [Marker α] : OfNat α 0` beside a local `Marker Nat` instance,
`abbrev N := Nat` with `instance : OfNat N 0`, and `abbrev C := OfNat Nat 0` with
`instance : C`. -/
theorem passA2_instance_anchor_in_conclusion_and_not_reducible :
    -- a local name among the premises only
    failsWith (audit noSourceConfig (defsInstPkg (.pi (.const colorName) natE)
        (.lam (.const colorName) (.natLit 0))))
      (.forbiddenInstanceOrCoe defsMod "orphan_instance_of_imported_class" premInstName) = true ∧
    -- the only local name in the conclusion is a reducible alias
    failsWith (audit noSourceConfig (defsPkg [.reducibilityOverride colorName]))
      (.forbiddenInstanceOrCoe defsMod "orphan_instance_of_imported_class" instColorName) = true ∧
    -- a reducible alias as the class, outside and inside a definitions module
    failsWith (audit noSourceConfig (pkgWithProofs (addExts proofsModule
        [.instanceEntry lemmaName mutAName false, .reducibilityOverride mutAName])))
      (.forbiddenInstanceOrCoe proofsMod "instance_of_imported_class" lemmaName) = true ∧
    failsWith (audit noSourceConfig (defsPkg [.reducibilityOverride (sn! "Topic.Defs.claimIdx"),
        .scopedInstanceEntry instColorName (sn! "Topic.Defs.claimIdx") defsMod]))
      (.forbiddenInstanceOrCoe defsMod "scoped_instance_of_imported_target" instColorName) = true ∧
    failsWith (audit noSourceConfig (defsPkg [.reducibilityOverride (sn! "Topic.Defs.claimIdx"),
        .defaultInstanceEntry instColorName (sn! "Topic.Defs.claimIdx")]))
      (.forbiddenInstanceOrCoe defsMod "default_instance_of_imported_target" instColorName) = true ∧
    -- a reducibility attribute on the instance itself, as `instance` adds, changes nothing
    isOk (audit noSourceConfig (defsPkg [.reducibilityOverride instColorName])) = true ∧
    isOk (audit noSourceConfig (extPkg (.instanceEntry lemmaName mutAName false))) = true ∧
    -- premises do not hide a local name in the conclusion
    isOk (audit noSourceConfig (defsInstPkg (.pi natE (.const colorName))
        (.lam natE (.const redName)))) = true := by
  decide +kernel

/-! ## Pass `B3` hardening regressions -/

def haddName : SymName := sn! "HAdd"
def haddMkName : SymName := sn! "HAdd.mk"
def haddBaseDecls : List ConstantRecord :=
  standardBaseDecls ++ [
    baseDecl haddName (.inductDecl [haddMkName])
      (.pi natE (.pi natE (.pi natE (.sort 0)))) initCore,
    baseDecl haddMkName (.ctorDecl haddName)
      (.pi natE (.pi natE (.pi natE (.app (.app (.app (.const haddName) (.bvar 2)) (.bvar 1)) (.bvar 0)))))
      initCore]

def haddApp (a b c : ExprSkeleton) : ExprSkeleton :=
  .app (.app (.app (.const haddName) a) b) c

def haddMkApp (a b c : ExprSkeleton) : ExprSkeleton :=
  .app (.app (.app (.const haddMkName) a) b) c

def localOutName : SymName := sn! "Topic.Defs.localOut"
def localOutDecl : ConstantRecord := mkOpaque localOutName natE (.natLit 0)
def aliasPremName : SymName := sn! "Topic.Defs.AliasPrem"
def aliasNatName : SymName := sn! "Topic.Defs.AliasNat"
def aliasColorName : SymName := sn! "Topic.Defs.AliasColor"
def evilCoeName : SymName := sn! "Topic.Defs.evilCoe"

/-- Instance anchor checks β/δ-normalize instance types before extracting the conclusion,
exclude `outParam` slots of core `Init` classes (`HAdd Nat Nat Color`), and require
`isInstanceAnchor` on `coeEntry` endpoints (closing `abbrev N' := Nat` coercions as well as
un-annotated `def` aliases). -/
theorem passB3_instance_beta_alias_and_outparam_rejected :
    -- β-redex hiding a premise `(fun _ : Nat => Color → True) 0` (rc=0 hijack in Lean 4.34.1)
    failsWith (audit noSourceConfig (defsInstPkg
        (.app (.lam natE (.pi (.const colorName) trueE)) (.natLit 0))
        (.lam (.const colorName) trueIntroE)))
      (.forbiddenInstanceOrCoe defsMod "orphan_instance_of_imported_class" premInstName) = true ∧
    -- dead β-redex `(fun _ : Color => True) Color.red` in conclusion
    failsWith (validateModuleExtensions (addExts (addConsts defsModule
        [mkDef premInstName (.app (.lam (.const colorName) trueE) (.const redName)) trueIntroE])
        [.instanceEntry premInstName (sn! "OfNat") false]))
      (.forbiddenInstanceOrCoe defsMod "orphan_instance_of_imported_class" premInstName) = true ∧
    -- inner β-redex `Eq ((fun _ : Color => 0) Color.red) 0`
    failsWith (validateModuleExtensions (addExts (addConsts defsModule
        [mkDef premInstName
          (eqNat (.app (.lam (.const colorName) (.natLit 0)) (.const redName)) (.natLit 0))
          (.app (c! "Eq.refl") (.natLit 0))])
        [.instanceEntry premInstName (sn! "OfNat") false]))
      (.forbiddenInstanceOrCoe defsMod "orphan_instance_of_imported_class" premInstName) = true ∧
    -- un-annotated `def AliasPrem := Color → True` hiding premise (no reducibilityOverride)
    failsWith (audit noSourceConfig
        { corePkg with modules :=
            [addExts (addConsts defsModule
                [mkDef aliasPremName (.sort 0) (.pi (.const colorName) trueE),
                 mkDef premInstName (.const aliasPremName) (.lam (.const colorName) trueIntroE)])
               [.instanceEntry premInstName (sn! "OfNat") false],
             theoryModule, proofsModule, verifyModule] })
      (.forbiddenInstanceOrCoe defsMod "orphan_instance_of_imported_class" premInstName) = true ∧
    -- un-annotated `def AliasNat := Nat` used as instance anchor (no reducibilityOverride)
    failsWith (audit noSourceConfig
        { corePkg with modules :=
            [addExts (addConsts defsModule
                [mkDef aliasNatName (.sort 1) natE,
                 mkDef premInstName (.const aliasNatName) (.natLit 0)])
               [.instanceEntry premInstName (sn! "OfNat") false],
             theoryModule, proofsModule, verifyModule] })
      (.forbiddenInstanceOrCoe defsMod "orphan_instance_of_imported_class" premInstName) = true ∧
    -- `coeEntry` with reducible alias `abbrev AliasNat := Nat` (rc=0 hijack in Lean 4.34.1)
    failsWith (audit noSourceConfig
        { corePkg with modules :=
            [addExts (addConsts defsModule
                [mkDef aliasNatName (.sort 1) natE,
                 mkDef evilCoeName (.pi (.const aliasNatName) boolE)
                   (.lam (.const aliasNatName) (c! "Bool.true"))])
               [.reducibilityOverride aliasNatName,
                .coeEntry evilCoeName aliasNatName SymName.boolName],
             theoryModule, proofsModule, verifyModule] })
      (.forbiddenInstanceOrCoe defsMod "coe_between_imported_types" evilCoeName) = true ∧
    -- `coeEntry` with un-annotated `def AliasNat := Nat`
    failsWith (audit noSourceConfig
        { corePkg with modules :=
            [addExts (addConsts defsModule
                [mkDef aliasNatName (.sort 1) natE,
                 mkDef evilCoeName (.pi (.const aliasNatName) boolE)
                   (.lam (.const aliasNatName) (c! "Bool.true"))])
               [.coeEntry evilCoeName aliasNatName SymName.boolName],
             theoryModule, proofsModule, verifyModule] })
      (.forbiddenInstanceOrCoe defsMod "coe_between_imported_types" evilCoeName) = true ∧
    -- `outParam` hijack: `HAdd 0 0 localOut` anchors only in trailing `outParam` (rejected)
    failsWith (audit noSourceConfig
        { baseEnv := haddBaseDecls,
          modules :=
            [addExts (addConsts defsModule
                [localOutDecl,
                 mkDef premInstName (haddApp (.natLit 0) (.natLit 0) (.const localOutName))
                   (haddMkApp (.natLit 0) (.natLit 0) (.const localOutName))])
               [.instanceEntry premInstName haddName false],
             theoryModule, proofsModule, verifyModule],
          verifyRoots := [verifiedName] })
      (.forbiddenInstanceOrCoe defsMod "orphan_instance_of_imported_class" premInstName) = true ∧
    -- positive: `HAdd localOut 0 0` anchors in input param 1 (accepted)
    isOk (audit noSourceConfig
        { baseEnv := haddBaseDecls,
          modules :=
            [addExts (addConsts defsModule
                [localOutDecl,
                 mkDef premInstName (haddApp (.const localOutName) (.natLit 0) (.natLit 0))
                   (haddMkApp (.const localOutName) (.natLit 0) (.natLit 0))])
               [.instanceEntry premInstName haddName false],
             theoryModule, proofsModule, verifyModule],
          verifyRoots := [verifiedName] }) = true ∧
    -- positive: non-reducible `def AliasColor := Color` still anchors on local `Color`
    isOk (audit noSourceConfig
        { corePkg with modules :=
            [addExts (addConsts defsModule
                [mkDef aliasColorName (.sort 1) (.const colorName),
                 mkDef premInstName (.const aliasColorName) (.const redName)])
               [.instanceEntry premInstName (sn! "Inhabited") false],
             theoryModule, proofsModule, verifyModule] }) = true := by decide +kernel

/-- A bodyless `.defnDecl` `_unsafe_rec` companion (`value? := none`) is never excused from
kernel replay. -/
theorem passB3_bodyless_unsafeRec_rejected :
    let bodyless : ConstantRecord :=
      { name := recName, kind := .defnDecl, type := natE, value? := none,
        safety := .partialDecl, all := [recName] }
    isCodegenUnsafeRecInMod proofsModule bodyless = false ∧
    failsWith (audit noSourceConfig (recPkg bodyless))
      (.unsafeOrPartialDecl proofsMod recName) = true := by decide +kernel

/-- Source scanner rejects `#eval`/`#eval!`/`#reduce` (compile-time IO/reduction),
`@[init ...]`/`attribute [init ...]` attribute forms, `@[cbv_eval]`/`@[cbv_opaque]`,
`coinductive`, and hex/sci-literal quotes inside interpolation holes, while accepting
`s!"{xs[0]'h}"`, `def eval := 0`, `def init := 0`, and `[init]`. -/
theorem passB3_sourceScanner_eval_init_and_hole_hardened :
    flags (chars! "#eval IO.println \"pwned\"") "#eval" = true ∧
    flags (chars! "#eval! f x") "#eval" = true ∧
    flags (chars! "#reduce (1 + 1)") "#reduce" = true ∧
    flags (chars! "def a := r#eval 1") "#eval" = true ∧
    flags (chars! "def s := s!\"{#eval 1}\"") "#eval" = true ∧
    flags (chars! "def myInit : IO Unit := pure ()\n@[init myInit] def x : Unit := ()") "init" = true ∧
    flags (chars! "@[simp, local init myInit] def x : Unit := ()") "init" = true ∧
    flags (chars! "attribute [init myInit] x") "init" = true ∧
    flags (chars! "local attribute [init myInit] x") "init" = true ∧
    flags (chars! "attribute [simp, «init» myInit] x") "init" = true ∧
    flags (chars! "@[cbv_eval] theorem f_eq : f = g := rfl") "cbv_eval" = true ∧
    flags (chars! "@[cbv_opaque] def f := 0") "cbv_opaque" = true ∧
    flags (chars! "coinductive Stream' (α : Type) where") "coinductive" = true ∧
    lexFails (chars! "def s := s!\"{0x1'a'}\"") = true ∧
    lexFails (chars! "def s := s!\"{1e0'a'}\"") = true ∧
    -- no false positives on valid Lean 4 array indexing in holes or ordinary identifiers
    isOk (scan (chars! "def f (xs : Array Nat) (h : 0 < xs.size) := s!\"{xs[0]'h} and {xs[0]'(by exact h)}\"")) = true ∧
    isOk (scan (chars! "def s := s!\"{x1'}\"")) = true ∧
    isOk (scan (chars! "def eval := 0\ndef reduce := 1\ndef init := 2\ndef xs := [init]\n@[simp] def init2 := 3\nattribute [simp] init")) = true := by
  decide +kernel

/-! ## End-to-end instantiation on the clean package -/

/-- The semantic soundness theorem applied to the clean package over the standard base
environment: whatever certificate the audit returns, its replayed environment has a model
in which every proposition-typed constant, replayed or imported, is true. Together with
`validBaselinePackage_accepted` this is a concrete, axiom-free consistency statement. -/
theorem validBaselinePackage_semantic_sound (cert : AuditCertificate)
    (h : auditAndReplayPackage noSourceConfig corePkg = .ok cert) :
    ∃ M', EnvSound cert.replayedEnv M' ∧
      (∀ n ci, cert.replayedEnv.lookup n = some ci →
        ∀ P : Prop, evalExpr M' [] ci.type = .prop P → P) ∧
      (∀ n ci, cert.importedEnv.lookup n = some ci →
        ∀ P : Prop, evalExpr M' [] ci.type = .prop P → P) :=
  auditAndReplayPackage_semantic_sound h ⟨rfl, rfl, rfl⟩ standardBaseEnv_sound

/-- No constant of the audited clean package has type `False`. -/
theorem validBaselinePackage_no_false (cert : AuditCertificate)
    (h : auditAndReplayPackage noSourceConfig corePkg = .ok cert) :
    ∀ n ci, cert.importedEnv.lookup n = some ci → ci.type ≠ .const SymName.falseName :=
  ((auditAndReplayPackage_sound h).2.2 ⟨rfl, rfl, rfl⟩ standardBaseModel standardBaseEnv_sound).2

/-- The verified root of the clean package has a clean dependency closure. -/
theorem validBaselinePackage_verifyRoot_closure_clean (cert : AuditCertificate)
    (h : auditAndReplayPackage noSourceConfig corePkg = .ok cert) :
    ∀ dep, DepReaches (packageEnv corePkg) verifiedName dep →
      CleanDep corePkg (packageEnv corePkg) dep :=
  auditAndReplayPackage_closure_sound h rfl rfl verifiedName
    (Or.inr (Or.inl (by simp [corePkg, pkgWithProofs])))

/-! ## Axiom audit

Every theorem of the module, pinned to its exact axiom footprint. All are within
`[propext, Classical.choice, Quot.sound]`: no `sorryAx`, no `Lean.ofReduceBool`, no
`Lean.ofReduceNat`, no `Lean.trustCompiler`, no custom axiom. -/

/-- info: 'Anneal.ReplayKeyAndTamperAudit.validInventory_length_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms validInventory_length_eq

/-- info: 'Anneal.ReplayKeyAndTamperAudit.validInventory_constNames_nodup' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms validInventory_constNames_nodup

/-- info: 'Anneal.ReplayKeyAndTamperAudit.validInventory_key_eq_ci_name' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms validInventory_key_eq_ci_name

/-- info: 'Anneal.ReplayKeyAndTamperAudit.validInventory_lookup_bijection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms validInventory_lookup_bijection

/-- info: 'Anneal.ReplayKeyAndTamperAudit.validInventory_mutual_all_wf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms validInventory_mutual_all_wf

/-- info: 'Anneal.ReplayKeyAndTamperAudit.validInventory_rec_all_targets_induct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms validInventory_rec_all_targets_induct

/-- info: 'Anneal.ReplayKeyAndTamperAudit.walkGraph_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms walkGraph_sound

/-- info: 'Anneal.ReplayKeyAndTamperAudit.walkGraph_reaches_subset' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms walkGraph_reaches_subset

/-- info: 'Anneal.ReplayKeyAndTamperAudit.walkGraph_never_exhausts_fuel' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms walkGraph_never_exhausts_fuel

/-- info: 'Anneal.ReplayKeyAndTamperAudit.closureExpand_never_exhausts_fuel' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms closureExpand_never_exhausts_fuel

/-- info: 'Anneal.ReplayKeyAndTamperAudit.walkStatementOrigins_never_exhausts_fuel' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms walkStatementOrigins_never_exhausts_fuel

/-- info: 'Anneal.ReplayKeyAndTamperAudit.worklist_closed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms worklist_closed

/-- info: 'Anneal.ReplayKeyAndTamperAudit.worklist_origin' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms worklist_origin

/-- info: 'Anneal.ReplayKeyAndTamperAudit.worklist_error_of_fuel' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms worklist_error_of_fuel

/-- info: 'Anneal.ReplayKeyAndTamperAudit.validPackage_axiom_closure_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms validPackage_axiom_closure_sound

/-- info: 'Anneal.ReplayKeyAndTamperAudit.statementOrigins_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms statementOrigins_sound

/-- info: 'Anneal.ReplayKeyAndTamperAudit.roleMatchesModuleName_unique' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms roleMatchesModuleName_unique

/-- info: 'Anneal.ReplayKeyAndTamperAudit.importClosureCheck_exact' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms importClosureCheck_exact

/-- info: 'Anneal.ReplayKeyAndTamperAudit.auditAndReplayPackage_modules_nodup' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms auditAndReplayPackage_modules_nodup

/-- info: 'Anneal.ReplayKeyAndTamperAudit.auditAndReplayPackage_global_names_nodup' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms auditAndReplayPackage_global_names_nodup

/-- info: 'Anneal.ReplayKeyAndTamperAudit.auditAndReplayPackage_extraConstNames_nodup' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms auditAndReplayPackage_extraConstNames_nodup

/-- info: 'Anneal.ReplayKeyAndTamperAudit.auditAndReplayPackage_no_lean_modules' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms auditAndReplayPackage_no_lean_modules

/-- info: 'Anneal.ReplayKeyAndTamperAudit.auditAndReplayPackage_roots_nodup' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms auditAndReplayPackage_roots_nodup

/-- info: 'Anneal.ReplayKeyAndTamperAudit.auditAndReplayPackage_verify_modules_covered' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms auditAndReplayPackage_verify_modules_covered

/-- info: 'Anneal.ReplayKeyAndTamperAudit.auditAndReplayPackage_imports_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms auditAndReplayPackage_imports_sound

/-- info: 'Anneal.ReplayKeyAndTamperAudit.auditAndReplayPackage_references_within_imports' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms auditAndReplayPackage_references_within_imports

/-- info: 'Anneal.ReplayKeyAndTamperAudit.auditAndReplayPackage_statement_side_dependencies' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms auditAndReplayPackage_statement_side_dependencies

/-- info: 'Anneal.ReplayKeyAndTamperAudit.auditAndReplayPackage_ext_refs_within_imports' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms auditAndReplayPackage_ext_refs_within_imports

/-- info: 'Anneal.ReplayKeyAndTamperAudit.auditAndReplayPackage_reserved_origins_within_imports' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms auditAndReplayPackage_reserved_origins_within_imports

/-- info: 'Anneal.ReplayKeyAndTamperAudit.auditAndReplayPackage_ext_decls_declared' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms auditAndReplayPackage_ext_decls_declared

/-- info: 'Anneal.ReplayKeyAndTamperAudit.auditAndReplayPackage_unsafeRec_sanitized' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms auditAndReplayPackage_unsafeRec_sanitized

/-- info: 'Anneal.ReplayKeyAndTamperAudit.auditAndReplayPackage_sources_covered' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms auditAndReplayPackage_sources_covered

/-- info: 'Anneal.ReplayKeyAndTamperAudit.auditAndReplayPackage_test_closures_clean' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms auditAndReplayPackage_test_closures_clean

/-- info: 'Anneal.ReplayKeyAndTamperAudit.auditAndReplayPackage_closure_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms auditAndReplayPackage_closure_sound

/-- info: 'Anneal.ReplayKeyAndTamperAudit.auditAndReplayPackage_verifyRoots_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms auditAndReplayPackage_verifyRoots_sound

/-- info: 'Anneal.ReplayKeyAndTamperAudit.auditAndReplayPackage_itemReports_cover_roots' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms auditAndReplayPackage_itemReports_cover_roots

/-- info: 'Anneal.ReplayKeyAndTamperAudit.auditAndReplayPackage_item_status_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms auditAndReplayPackage_item_status_sound

/-- info: 'Anneal.ReplayKeyAndTamperAudit.auditAndReplayPackage_item_status_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms auditAndReplayPackage_item_status_complete

/-- info: 'Anneal.ReplayKeyAndTamperAudit.whnf_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms whnf_sound

/-- info: 'Anneal.ReplayKeyAndTamperAudit.isDefEq_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms isDefEq_sound

/-- info: 'Anneal.ReplayKeyAndTamperAudit.inferType_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms inferType_sound

/-- info: 'Anneal.ReplayKeyAndTamperAudit.kernel_sound_at_fuel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms kernel_sound_at_fuel

/-- info: 'Anneal.ReplayKeyAndTamperAudit.canonicalRecType_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms canonicalRecType_holds

/-- info: 'Anneal.ReplayKeyAndTamperAudit.kernelCheckDecl_preserves_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms kernelCheckDecl_preserves_sound

/-- info: 'Anneal.ReplayKeyAndTamperAudit.replayCleanEnv_preserves_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms replayCleanEnv_preserves_sound

/-- info: 'Anneal.ReplayKeyAndTamperAudit.replayCleanEnvOrdered_preserves_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms replayCleanEnvOrdered_preserves_sound

/-- info: 'Anneal.ReplayKeyAndTamperAudit.replayCleanEnvOrdered_contains_decl' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms replayCleanEnvOrdered_contains_decl

/-- info: 'Anneal.ReplayKeyAndTamperAudit.standardBaseEnv_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms standardBaseEnv_sound

/-- info: 'Anneal.ReplayKeyAndTamperAudit.kernelEnv_no_false' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms kernelEnv_no_false

/-- info: 'Anneal.ReplayKeyAndTamperAudit.kernelEnv_prop_types_true' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms kernelEnv_prop_types_true

/-- info: 'Anneal.ReplayKeyAndTamperAudit.imported_record_replayed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms imported_record_replayed

/-- info: 'Anneal.ReplayKeyAndTamperAudit.auditAndReplayPackage_semantic_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms auditAndReplayPackage_semantic_sound

/-- info: 'Anneal.ReplayKeyAndTamperAudit.auditAndReplayPackage_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms auditAndReplayPackage_sound

/-- info: 'Anneal.ReplayKeyAndTamperAudit.collectViolations_nil' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms collectViolations_nil

/-! The regression theorems above are kernel evaluations (`decide +kernel`): they add no
axiom beyond the same three. -/

/-- info: 'Anneal.ReplayKeyAndTamperAuditTests.validBaselinePackage_accepted' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms validBaselinePackage_accepted

/-- info: 'Anneal.ReplayKeyAndTamperAuditTests.validBaselinePackage_json' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms validBaselinePackage_json

/-- info: 'Anneal.ReplayKeyAndTamperAuditTests.issue16675_recursor_bypass' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms issue16675_recursor_bypass

/-- info: 'Anneal.ReplayKeyAndTamperAuditTests.issue16675_induct_all_aligned_key_bypass' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms issue16675_induct_all_aligned_key_bypass

/-- info: 'Anneal.ReplayKeyAndTamperAuditTests.trustedBoundary_overwrite_bypass' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms trustedBoundary_overwrite_bypass

/-- info: 'Anneal.ReplayKeyAndTamperAuditTests.finalizeImport_subsumes_body_swap_bypass' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms finalizeImport_subsumes_body_swap_bypass

/-- info: 'Anneal.ReplayKeyAndTamperAuditTests.cleanNonWorkspace_cache_poisoning_bypass' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms cleanNonWorkspace_cache_poisoning_bypass

/-- info: 'Anneal.ReplayKeyAndTamperAuditTests.pillar1_native_reduction_all_rejected' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms pillar1_native_reduction_all_rejected

/-- info: 'Anneal.ReplayKeyAndTamperAuditTests.V06_tamper_ext_isolated_rejection' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms V06_tamper_ext_isolated_rejection

/-- info: 'Anneal.ReplayKeyAndTamperAuditTests.V09_replay_only_isolated_rejection' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms V09_replay_only_isolated_rejection

/-- info: 'Anneal.ReplayKeyAndTamperAuditTests.sourceScanner_lexer_desync_rejected' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms sourceScanner_lexer_desync_rejected

/-- info: 'Anneal.ReplayKeyAndTamperAuditTests.kernel_model_edges' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms kernel_model_edges

/-- info: 'Anneal.ReplayKeyAndTamperAuditTests.validBaselinePackage_semantic_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms validBaselinePackage_semantic_sound

/-- info: 'Anneal.ReplayKeyAndTamperAuditTests.validBaselinePackage_no_false' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms validBaselinePackage_no_false

/-- info: 'Anneal.ReplayKeyAndTamperAuditTests.validBaselinePackage_verifyRoot_closure_clean' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms validBaselinePackage_verifyRoot_closure_clean

/-- info: 'Anneal.ReplayKeyAndTamperAuditTests.passB1_lexer_and_guillemet_desync_rejected' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms passB1_lexer_and_guillemet_desync_rejected

/-- info: 'Anneal.ReplayKeyAndTamperAuditTests.passB1_kernel_defn_opaque_ill_typed_type_rejected' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms passB1_kernel_defn_opaque_ill_typed_type_rejected

/-- info: 'Anneal.ReplayKeyAndTamperAuditTests.passB1_unsafeRec_transitive_and_test_policy_rejected' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms passB1_unsafeRec_transitive_and_test_policy_rejected

/-- info: 'Anneal.ReplayKeyAndTamperAuditTests.passB1_unsafeRec_ext_target_and_cross_module_extraConstNames_rejected' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms passB1_unsafeRec_ext_target_and_cross_module_extraConstNames_rejected

/-- info: 'Anneal.ReplayKeyAndTamperAuditTests.passB1_provisional_native_fuel_and_interior_name_hardened' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms passB1_provisional_native_fuel_and_interior_name_hardened

/-- info: 'Anneal.ReplayKeyAndTamperAuditTests.passA1_token_boundary_desync_fails_closed' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms passA1_token_boundary_desync_fails_closed

/-- info: 'Anneal.ReplayKeyAndTamperAuditTests.passA1_syntax_extension_commands_rejected' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms passA1_syntax_extension_commands_rejected

/-- info: 'Anneal.ReplayKeyAndTamperAuditTests.passA1_no_false_positive' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms passA1_no_false_positive

/-- info: 'Anneal.ReplayKeyAndTamperAudit.SymName.toChars_inj' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SymName.toChars_inj

/-- info: 'Anneal.ReplayKeyAndTamperAudit.auditAndReplayPackage_global_toChars_nodup' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms auditAndReplayPackage_global_toChars_nodup

/-- info: 'Anneal.ReplayKeyAndTamperAudit.auditAndReplayPackage_no_orphan_instances' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms auditAndReplayPackage_no_orphan_instances

/-- info: 'Anneal.ReplayKeyAndTamperAuditTests.passB2_symname_component_smuggling_rejected' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms passB2_symname_component_smuggling_rejected

/-- info: 'Anneal.ReplayKeyAndTamperAuditTests.passB2_defs_orphan_instance_and_rec_all_mismatch_rejected' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms passB2_defs_orphan_instance_and_rec_all_mismatch_rejected

/-- info: 'Anneal.ReplayKeyAndTamperAuditTests.passB2_baseEnv_module_collision_and_test_axiom_flag_rejected' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms passB2_baseEnv_module_collision_and_test_axiom_flag_rejected

/-- info: 'Anneal.ReplayKeyAndTamperAuditTests.passB2_v15_spec_and_assumptions_shadowing_rejected' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms passB2_v15_spec_and_assumptions_shadowing_rejected

/-- info: 'Anneal.ReplayKeyAndTamperAuditTests.passB2_provisional_native_chained_defs_refuted_and_fail_closed' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms passB2_provisional_native_chained_defs_refuted_and_fail_closed

/-- info: 'Anneal.ReplayKeyAndTamperAuditTests.passB2_sourceScanner_ext_hooks_and_builtin_variants_rejected' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms passB2_sourceScanner_ext_hooks_and_builtin_variants_rejected

/-- info: 'Anneal.ReplayKeyAndTamperAuditTests.passA2_instance_anchor_in_conclusion_and_not_reducible' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms passA2_instance_anchor_in_conclusion_and_not_reducible

/-- info: 'Anneal.ReplayKeyAndTamperAudit.auditAndReplayPackage_coe_anchored' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms auditAndReplayPackage_coe_anchored

/-- info: 'Anneal.ReplayKeyAndTamperAuditTests.passB3_instance_beta_alias_and_outparam_rejected' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms passB3_instance_beta_alias_and_outparam_rejected

/-- info: 'Anneal.ReplayKeyAndTamperAuditTests.passB3_bodyless_unsafeRec_rejected' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms passB3_bodyless_unsafeRec_rejected

/-- info: 'Anneal.ReplayKeyAndTamperAuditTests.passB3_sourceScanner_eval_init_and_hole_hardened' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms passB3_sourceScanner_eval_init_and_hole_hardened

end Anneal.ReplayKeyAndTamperAuditTests
