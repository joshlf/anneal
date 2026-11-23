-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

namespace Anneal.ReplayKeyAndTamperAudit

/-!
# `.olean` Replay-Key, Mutual-`.all`, Axiom-Policy, and Tamper Audit

A kernel-checked model of the checks an `.olean` inspector must make before it
trusts a compiled Lean package on the pinned toolchain `leanprover/lean4:v4.34.1`.

On that toolchain an imported module is a pair of parallel arrays, `constNames` and
`constants`. `finalizeImport` inserts `constants[i]` under the key `constNames[i]`
without comparing the key with `constants[i].name`, stops silently at the shorter
array, and lets a later record replace an earlier one that it "subsumes".
`Kernel.Environment.replay` then follows record *names*, so a record stored under a
foreign key is never type-checked (`leanprover/lean4#16677`). This module states the
checks that close that gap and the ones around it, and proves what they guarantee:

1. **Inventory** (`validateModuleDataKeys`, `validateReplayInventory`): equal array
   lengths, duplicate-free non-anonymous keys, `key = record.name` for every entry,
   well-formed mutual `.all` blocks, recursor targets, constructor/inductive links,
   private-name flags, `extraConstNames` hygiene, and no quotient declaration outside
   the standard library.
2. **Policy** (`validateAxiomAndTamperPolicy`): module roles justified by module names,
   multi-part `.olean` presence, persistent environment extensions, imports (modifiers,
   provenance, role direction, acyclicity), source text scanning, `unsafe`/`partial`
   declarations and their `_unsafe_rec` companions, the direct constant-closure walk
   with the `sorryAx` / native-reduction / compiler-trust bans, test-module closures,
   verify-root coverage, and statement/proof origin separation.
3. **Replay** (`replayCleanEnv`, `replayCleanEnvOrdered`): every package declaration is
   re-checked by a small kernel (`whnf`, `isDefEq`, `inferType`, `kernelCheckDecl`)
   on top of the pinned base environment, in dependency order.

`auditAndReplayPackage` runs the three stages and returns an `AuditCertificate`;
`renderAuditJson` renders the outcome as deterministic JSON.

The kernel is a model, not Lean's kernel: it covers a first-order fragment (sorts
`Prop`, `Type`, and one universe above them; functions out of data types; impredicative
`Prop`; enumeration inductives with their `Prop` recursors) and is proved sound against
the set-theoretic model `SemVal`. Everything outside the fragment is rejected, never
assumed. The file imports nothing beyond `Init` and runs no code at elaboration time.
-/

/-! ## Character-list constants

Every name component and keyword the audit compares against, spelled out as a character
list. Converting a `String` literal to characters is quadratic under kernel reduction, so
nothing on the audit's evaluation path does it: names and source texts are character
lists throughout, and `String` appears only in diagnostics and convenience constructors. -/

namespace Chars

def init : List Char := ['I', 'n', 'i', 't']
def std : List Char := ['S', 't', 'd']
def lean : List Char := ['L', 'e', 'a', 'n']
def trusted : List Char := ['T', 'r', 'u', 's', 't', 'e', 'd']
def verify : List Char := ['V', 'e', 'r', 'i', 'f', 'y']
def crateVerify : List Char := ['C', 'r', 'a', 't', 'e', 'V', 'e', 'r', 'i', 'f', 'y']
def privatePrefix : List Char := ['_', 'p', 'r', 'i', 'v', 'a', 't', 'e']
def anneal : List Char := ['A', 'n', 'n', 'e', 'a', 'l']
def assumptions : List Char := ['A', 's', 's', 'u', 'm', 'p', 't', 'i', 'o', 'n', 's']
def proof : List Char := ['P', 'r', 'o', 'o', 'f']
def proofs : List Char := ['P', 'r', 'o', 'o', 'f', 's']
def test : List Char := ['T', 'e', 's', 't']
def tests : List Char := ['T', 'e', 's', 't', 's']
def defs : List Char := ['D', 'e', 'f', 's']
def verified : List Char := ['v', 'e', 'r', 'i', 'f', 'i', 'e', 'd']
def unsafeRec : List Char := ['_', 'u', 'n', 's', 'a', 'f', 'e', '_', 'r', 'e', 'c']
def nativeMarker : List Char := ['_', 'n', 'a', 't', 'i', 'v', 'e']
def eqDef : List Char := ['e', 'q', '_', 'd', 'e', 'f']
def congrSimp : List Char := ['c', 'o', 'n', 'g', 'r', '_', 's', 'i', 'm', 'p']
def elim : List Char := ['e', 'l', 'i', 'm']
def splitter : List Char := ['s', 'p', 'l', 'i', 't', 't', 'e', 'r']
def injEq : List Char := ['i', 'n', 'j', 'E', 'q']
def sizeOfSpec : List Char := ['s', 'i', 'z', 'e', 'O', 'f', '_', 's', 'p', 'e', 'c']
def noConfusion : List Char := ['n', 'o', 'C', 'o', 'n', 'f', 'u', 's', 'i', 'o', 'n']
def induct : List Char := ['i', 'n', 'd', 'u', 'c', 't']
def eqPrefix : List Char := ['e', 'q', '_']
def matchPrefix : List Char := ['m', 'a', 't', 'c', 'h', '_']
def proofPrefix : List Char := ['p', 'r', 'o', 'o', 'f', '_']
def sorryAx : List Char := ['s', 'o', 'r', 'r', 'y', 'A', 'x']
def propext : List Char := ['p', 'r', 'o', 'p', 'e', 'x', 't']
def classical : List Char := ['C', 'l', 'a', 's', 's', 'i', 'c', 'a', 'l']
def choice : List Char := ['c', 'h', 'o', 'i', 'c', 'e']
def quot : List Char := ['Q', 'u', 'o', 't']
def sound : List Char := ['s', 'o', 'u', 'n', 'd']
def ofReduceBool : List Char := ['o', 'f', 'R', 'e', 'd', 'u', 'c', 'e', 'B', 'o', 'o', 'l']
def ofReduceNat : List Char := ['o', 'f', 'R', 'e', 'd', 'u', 'c', 'e', 'N', 'a', 't']
def reduceBool : List Char := ['r', 'e', 'd', 'u', 'c', 'e', 'B', 'o', 'o', 'l']
def reduceNat : List Char := ['r', 'e', 'd', 'u', 'c', 'e', 'N', 'a', 't']
def trustCompiler : List Char := ['t', 'r', 'u', 's', 't', 'C', 'o', 'm', 'p', 'i', 'l', 'e', 'r']
def nat : List Char := ['N', 'a', 't']
def zero : List Char := ['z', 'e', 'r', 'o']
def succ : List Char := ['s', 'u', 'c', 'c']
def string : List Char := ['S', 't', 'r', 'i', 'n', 'g']
def bool : List Char := ['B', 'o', 'o', 'l']
def boolFalse : List Char := ['f', 'a', 'l', 's', 'e']
def boolTrue : List Char := ['t', 'r', 'u', 'e']
def trueProp : List Char := ['T', 'r', 'u', 'e']
def intro : List Char := ['i', 'n', 't', 'r', 'o']
def falseProp : List Char := ['F', 'a', 'l', 's', 'e']
def eq : List Char := ['E', 'q']
def refl : List Char := ['r', 'e', 'f', 'l']
def eqBool : List Char := ['E', 'q', 'B', 'o', 'o', 'l']
def verificationResult : List Char := ['V', 'e', 'r', 'i', 'f', 'i', 'c', 'a', 't', 'i', 'o', 'n', 'R', 'e', 's', 'u', 'l', 't']
def prelude : List Char := ['P', 'r', 'e', 'l', 'u', 'd', 'e']
def core : List Char := ['C', 'o', 'r', 'e']
def kwSetOption : List Char := ['s', 'e', 't', '_', 'o', 'p', 't', 'i', 'o', 'n']
def maxHeartbeats : List Char := ['m', 'a', 'x', 'H', 'e', 'a', 'r', 't', 'b', 'e', 'a', 't', 's']
def maxRecDepth : List Char := ['m', 'a', 'x', 'R', 'e', 'c', 'D', 'e', 'p', 't', 'h']
def ppPrefix : List Char := ['p', 'p', '.']
def linterPrefix : List Char := ['l', 'i', 'n', 't', 'e', 'r', '.']
def kwSkipKernelTC : List Char := ['s', 'k', 'i', 'p', 'K', 'e', 'r', 'n', 'e', 'l', 'T', 'C']
def kwAllowUnsafeReducibility : List Char := ['a', 'l', 'l', 'o', 'w', 'U', 'n', 's', 'a', 'f', 'e', 'R', 'e', 'd', 'u', 'c', 'i', 'b', 'i', 'l', 'i', 't', 'y']
def kwPrivateInPublic : List Char := ['p', 'r', 'i', 'v', 'a', 't', 'e', 'I', 'n', 'P', 'u', 'b', 'l', 'i', 'c']
def kwQuotPrecheck : List Char := ['q', 'u', 'o', 't', 'P', 'r', 'e', 'c', 'h', 'e', 'c', 'k']
def kwHygiene : List Char := ['h', 'y', 'g', 'i', 'e', 'n', 'e']
def kwNativeEqTrue : List Char := ['n', 'a', 't', 'i', 'v', 'e', 'E', 'q', 'T', 'r', 'u', 'e']
def kwImplementedBy : List Char := ['i', 'm', 'p', 'l', 'e', 'm', 'e', 'n', 't', 'e', 'd', '_', 'b', 'y']
def kwExtern : List Char := ['e', 'x', 't', 'e', 'r', 'n']
def kwUnsafe : List Char := ['u', 'n', 's', 'a', 'f', 'e']
def kwPartial : List Char := ['p', 'a', 'r', 't', 'i', 'a', 'l']
def kwByElab : List Char := ['b', 'y', '_', 'e', 'l', 'a', 'b']
def kwRunTac : List Char := ['r', 'u', 'n', '_', 't', 'a', 'c']
def kwRunCmd : List Char := ['r', 'u', 'n', '_', 'c', 'm', 'd']
def kwRunMeta : List Char := ['r', 'u', 'n', '_', 'm', 'e', 't', 'a']
def kwRunElab : List Char := ['r', 'u', 'n', '_', 'e', 'l', 'a', 'b']
def kwNativeDecide : List Char := ['n', 'a', 't', 'i', 'v', 'e', '_', 'd', 'e', 'c', 'i', 'd', 'e']
def kwBvDecide : List Char := ['b', 'v', '_', 'd', 'e', 'c', 'i', 'd', 'e']
def kwBvCheck : List Char := ['b', 'v', '_', 'c', 'h', 'e', 'c', 'k']
def kwDecide : List Char := ['d', 'e', 'c', 'i', 'd', 'e']
def kwNative : List Char := ['n', 'a', 't', 'i', 'v', 'e']
def kwConfig : List Char := ['c', 'o', 'n', 'f', 'i', 'g']
def kwDecideConfig : List Char := ['D', 'e', 'c', 'i', 'd', 'e', 'C', 'o', 'n', 'f', 'i', 'g']
def kwNotation : List Char := ['n', 'o', 't', 'a', 't', 'i', 'o', 'n']
def kwInfix : List Char := ['i', 'n', 'f', 'i', 'x']
def kwInfixl : List Char := ['i', 'n', 'f', 'i', 'x', 'l']
def kwInfixr : List Char := ['i', 'n', 'f', 'i', 'x', 'r']
def kwPrefix : List Char := ['p', 'r', 'e', 'f', 'i', 'x']
def kwPostfix : List Char := ['p', 'o', 's', 't', 'f', 'i', 'x']
def kwSyntax : List Char := ['s', 'y', 'n', 't', 'a', 'x']
def kwMacro : List Char := ['m', 'a', 'c', 'r', 'o']
def kwMacroRules : List Char := ['m', 'a', 'c', 'r', 'o', '_', 'r', 'u', 'l', 'e', 's']
def kwElab : List Char := ['e', 'l', 'a', 'b']
def kwElabRules : List Char := ['e', 'l', 'a', 'b', '_', 'r', 'u', 'l', 'e', 's']
def kwDeclareSyntaxCat : List Char := ['d', 'e', 'c', 'l', 'a', 'r', 'e', '_', 's', 'y', 'n', 't', 'a', 'x', '_', 'c', 'a', 't']
def kwBinderPredicate : List Char := ['b', 'i', 'n', 'd', 'e', 'r', '_', 'p', 'r', 'e', 'd', 'i', 'c', 'a', 't', 'e']
def kwInitialize : List Char := ['i', 'n', 'i', 't', 'i', 'a', 'l', 'i', 'z', 'e']
def kwBuiltinInit : List Char := ['b', 'u', 'i', 'l', 't', 'i', 'n', '_', 'i', 'n', 'i', 't']
def kwCommandElab : List Char := ['c', 'o', 'm', 'm', 'a', 'n', 'd', '_', 'e', 'l', 'a', 'b']
def kwTermElab : List Char := ['t', 'e', 'r', 'm', '_', 'e', 'l', 'a', 'b']
def kwTacticElab : List Char := ['t', 'a', 'c', 't', 'i', 'c', '_', 'e', 'l', 'a', 'b']
def kwDelab : List Char := ['d', 'e', 'l', 'a', 'b']
def kwAppUnexpander : List Char := ['a', 'p', 'p', '_', 'u', 'n', 'e', 'x', 'p', 'a', 'n', 'd', 'e', 'r']
def kwSimproc : List Char := ['s', 'i', 'm', 'p', 'r', 'o', 'c']
def kwDSimproc : List Char := ['d', 's', 'i', 'm', 'p', 'r', 'o', 'c']
def kwCbvSimproc : List Char := ['c', 'b', 'v', '_', 's', 'i', 'm', 'p', 'r', 'o', 'c']
def kwSimprocDecl : List Char := ['s', 'i', 'm', 'p', 'r', 'o', 'c', '_', 'd', 'e', 'c', 'l']
def kwDSimprocDecl : List Char := ['d', 's', 'i', 'm', 'p', 'r', 'o', 'c', '_', 'd', 'e', 'c', 'l']
def kwCbvSimprocDecl : List Char := ['c', 'b', 'v', '_', 's', 'i', 'm', 'p', 'r', 'o', 'c', '_', 'd', 'e', 'c', 'l']
def kwUnifHint : List Char := ['u', 'n', 'i', 'f', '_', 'h', 'i', 'n', 't']
def kwUnificationHint : List Char := ['u', 'n', 'i', 'f', 'i', 'c', 'a', 't', 'i', 'o', 'n', '_', 'h', 'i', 'n', 't']
def kwExport : List Char := ['e', 'x', 'p', 'o', 'r', 't']
def kwCsimp : List Char := ['c', 's', 'i', 'm', 'p']
def kwCpass : List Char := ['c', 'p', 'a', 's', 's']
def kwDeclareSimpLikeTactic : List Char := ['d', 'e', 'c', 'l', 'a', 'r', 'e', '_', 's', 'i', 'm', 'p', '_', 'l', 'i', 'k', 'e', '_', 't', 'a', 'c', 't', 'i', 'c']
def kwDoElemElab : List Char := ['d', 'o', 'E', 'l', 'e', 'm', '_', 'e', 'l', 'a', 'b']
def kwInductiveElab : List Char := ['i', 'n', 'd', 'u', 'c', 't', 'i', 'v', 'e', '_', 'e', 'l', 'a', 'b']
def kwBuiltinTactic : List Char := ['b', 'u', 'i', 'l', 't', 'i', 'n', '_', 't', 'a', 'c', 't', 'i', 'c']
def kwGrindTactic : List Char := ['g', 'r', 'i', 'n', 'd', '_', 't', 'a', 'c', 't', 'i', 'c']
def kwTryTactic : List Char := ['t', 'r', 'y', '_', 't', 'a', 'c', 't', 'i', 'c']
def kwSymSimproc : List Char := ['s', 'y', 'm', '_', 's', 'i', 'm', 'p', 'r', 'o', 'c']
def kwSymDSimproc : List Char := ['s', 'y', 'm', '_', 'd', 's', 'i', 'm', 'p', 'r', 'o', 'c']
def kwSymDischarger : List Char := ['s', 'y', 'm', '_', 'd', 'i', 's', 'c', 'h', 'a', 'r', 'g', 'e', 'r']
def kwRunParserAttrHooks : List Char := ['r', 'u', 'n', '_', 'p', 'a', 'r', 's', 'e', 'r', '_', 'a', 't', 't', 'r', 'i', 'b', 'u', 't', 'e', '_', 'h', 'o', 'o', 'k', 's']
def kwRunBuiltinParserAttrHooks : List Char := ['r', 'u', 'n', '_', 'b', 'u', 'i', 'l', 't', 'i', 'n', '_', 'p', 'a', 'r', 's', 'e', 'r', '_', 'a', 't', 't', 'r', 'i', 'b', 'u', 't', 'e', '_', 'h', 'o', 'o', 'k', 's']
def kwInit : List Char := ['i', 'n', 'i', 't']
def kwAttribute : List Char := ['a', 't', 't', 'r', 'i', 'b', 'u', 't', 'e']
def kwHashEval : List Char := ['#', 'e', 'v', 'a', 'l']
def kwHashReduce : List Char := ['#', 'r', 'e', 'd', 'u', 'c', 'e']
def kwCbvEval : List Char := ['c', 'b', 'v', '_', 'e', 'v', 'a', 'l']
def kwCbvOpaque : List Char := ['c', 'b', 'v', '_', 'o', 'p', 'a', 'q', 'u', 'e']
def kwCoinductive : List Char := ['c', 'o', 'i', 'n', 'd', 'u', 'c', 't', 'i', 'v', 'e']
def clsHAdd : List Char := ['H', 'A', 'd', 'd']
def clsHSub : List Char := ['H', 'S', 'u', 'b']
def clsHMul : List Char := ['H', 'M', 'u', 'l']
def clsHDiv : List Char := ['H', 'D', 'i', 'v']
def clsHMod : List Char := ['H', 'M', 'o', 'd']
def clsHPow : List Char := ['H', 'P', 'o', 'w']
def clsHAppend : List Char := ['H', 'A', 'p', 'p', 'e', 'n', 'd']
def clsHAnd : List Char := ['H', 'A', 'n', 'd']
def clsHOr : List Char := ['H', 'O', 'r']
def clsHXor : List Char := ['H', 'X', 'o', 'r']
def clsHShiftLeft : List Char := ['H', 'S', 'h', 'i', 'f', 't', 'L', 'e', 'f', 't']
def clsHShiftRight : List Char := ['H', 'S', 'h', 'i', 'f', 't', 'R', 'i', 'g', 'h', 't']
def clsHSMul : List Char := ['H', 'S', 'M', 'u', 'l']
def clsHAndThen : List Char := ['H', 'A', 'n', 'd', 'T', 'h', 'e', 'n']
def clsHOrElse : List Char := ['H', 'O', 'r', 'E', 'l', 's', 'e']
def clsGetElem : List Char := ['G', 'e', 't', 'E', 'l', 'e', 'm']
def clsGetElemQ : List Char := ['G', 'e', 't', 'E', 'l', 'e', 'm', '?']
def clsTrans : List Char := ['T', 'r', 'a', 'n', 's']
def clsCoeOut : List Char := ['C', 'o', 'e', 'O', 'u', 't']
def clsCoeTail : List Char := ['C', 'o', 'e', 'T', 'a', 'i', 'l']
def clsCoeFun : List Char := ['C', 'o', 'e', 'F', 'u', 'n']
def clsCoeSort : List Char := ['C', 'o', 'e', 'S', 'o', 'r', 't']
def clsCoeHead : List Char := ['C', 'o', 'e', 'H', 'e', 'a', 'd']
def builtinPrefix : List Char := ['b', 'u', 'i', 'l', 't', 'i', 'n', '_']
def parserSuffix : List Char := ['_', 'p', 'a', 'r', 's', 'e', 'r']
def plusOneBracketTick : List Char := ['+', '1', ']', '\'']

end Chars

/-! ## Names -/

/-- A hierarchical name as its list of components. Components are character lists so that
every name test reduces in the kernel without touching `String`. `[]` is the anonymous name. -/
structure SymName where
  parts : List (List Char)
  deriving DecidableEq

namespace SymName

def anonymous : SymName := ⟨[]⟩

def isAnonymous (n : SymName) : Bool := n.parts.isEmpty

/-- A name is well formed when it is non-anonymous, every component is non-empty, and no
component contains a `.` (preventing dotted-string collisions and component-smuggling
bypasses of root, suffix, private, or native checks). -/
def isWellFormed (n : SymName) : Bool :=
  !n.parts.isEmpty && n.parts.all (fun p => !p.isEmpty && decide ('.' ∉ p))

theorem ne_anonymous_of_isWellFormed {n : SymName} (h : n.isWellFormed = true) :
    n ≠ anonymous := by
  intro heq
  subst heq
  simp [isWellFormed, anonymous] at h

/-- Convenience constructors from `String`s, for drivers. The audit itself never uses them. -/
def mkSimple (s : String) : SymName := ⟨[s.toList]⟩

def ofList (l : List String) : SymName := ⟨l.map String.toList⟩

/-- Parse a dotted name such as `"Topic.Proofs.lemma"`. Empty components are dropped. -/
def ofString (s : String) : SymName := ⟨(s.toList.splitOn '.').filter (fun p => !p.isEmpty)⟩

def str (n : SymName) (s : String) : SymName := ⟨n.parts ++ [s.toList]⟩

/-- Append one component. -/
def child (n : SymName) (part : List Char) : SymName := ⟨n.parts ++ [part]⟩

def toChars (n : SymName) : List Char := List.intercalate ['.'] n.parts

theorem append_dot_inj {p q r s : List Char} (hp : '.' ∉ p) (hq : '.' ∉ q)
    (h : p ++ '.' :: r = q ++ '.' :: s) : p = q ∧ r = s := by
  induction p generalizing q with
  | nil =>
    cases q with
    | nil => simp only [List.nil_append, List.cons.injEq] at h; exact ⟨rfl, h.2⟩
    | cons b bs =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      exact absurd (h.1 ▸ List.mem_cons_self) hq
  | cons a as ih =>
    cases q with
    | nil =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      exact absurd (h.1.symm ▸ List.mem_cons_self) hp
    | cons b bs =>
      simp only [List.cons_append, List.cons.injEq] at h
      have hpa : '.' ∉ as := fun hm => hp (List.mem_cons_of_mem _ hm)
      have hqb : '.' ∉ bs := fun hm => hq (List.mem_cons_of_mem _ hm)
      obtain ⟨heq, hrs⟩ := ih hpa hqb h.2
      exact ⟨by rw [h.1, heq], hrs⟩

theorem intercalate_dot_inj : ∀ {ps qs : List (List Char)},
    (∀ p ∈ ps, p ≠ [] ∧ '.' ∉ p) → (∀ q ∈ qs, q ≠ [] ∧ '.' ∉ q) →
    List.intercalate ['.'] ps = List.intercalate ['.'] qs → ps = qs
  | [], [], _, _, _ => rfl
  | [], q :: qs, _, hq, heq => by
    have hqne := (hq q List.mem_cons_self).1
    cases qs with
    | nil => simp [List.intercalate] at heq; exact absurd heq hqne
    | cons q' qs' =>
      simp [List.intercalate] at heq
  | p :: ps, [], hp, _, heq => by
    have hpne := (hp p List.mem_cons_self).1
    cases ps with
    | nil => simp [List.intercalate] at heq; exact absurd heq hpne
    | cons p' ps' =>
      simp [List.intercalate] at heq
  | [p], [q], _, _, heq => by
    simp [List.intercalate] at heq
    rw [heq]
  | [p], q :: q' :: qs, hp, _, heq => by
    have h1 : List.intercalate ['.'] [p] = p := List.append_nil p
    have h2 : List.intercalate ['.'] (q :: q' :: qs) =
        q ++ '.' :: List.intercalate ['.'] (q' :: qs) := rfl
    rw [h1, h2] at heq
    have hdot : '.' ∈ p := by
      rw [heq]
      exact List.mem_append_right _ List.mem_cons_self
    exact absurd hdot (hp p List.mem_cons_self).2
  | p :: p' :: ps, [q], _, hq, heq => by
    have h1 : List.intercalate ['.'] (p :: p' :: ps) =
        p ++ '.' :: List.intercalate ['.'] (p' :: ps) := rfl
    have h2 : List.intercalate ['.'] [q] = q := List.append_nil q
    rw [h1, h2] at heq
    have hdot : '.' ∈ q := by
      rw [← heq]
      exact List.mem_append_right _ List.mem_cons_self
    exact absurd hdot (hq q List.mem_cons_self).2
  | p :: p' :: ps, q :: q' :: qs, hp, hq, heq => by
    have h1 : List.intercalate ['.'] (p :: p' :: ps) =
        p ++ '.' :: List.intercalate ['.'] (p' :: ps) := rfl
    have h2 : List.intercalate ['.'] (q :: q' :: qs) =
        q ++ '.' :: List.intercalate ['.'] (q' :: qs) := rfl
    rw [h1, h2] at heq
    obtain ⟨hpq, hrest⟩ := append_dot_inj (hp p List.mem_cons_self).2
      (hq q List.mem_cons_self).2 heq
    have htail := intercalate_dot_inj
      (fun x hx => hp x (List.mem_cons_of_mem _ hx))
      (fun x hx => hq x (List.mem_cons_of_mem _ hx)) hrest
    rw [hpq, htail]

/-- Dotted character rendering is injective on well-formed names: distinct well-formed names
always produce distinct dotted strings. -/
theorem toChars_inj {n1 n2 : SymName} (h1 : n1.isWellFormed = true)
    (h2 : n2.isWellFormed = true) (heq : n1.toChars = n2.toChars) : n1 = n2 := by
  cases n1 with | mk ps =>
  cases n2 with | mk qs =>
  simp only [isWellFormed, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true',
    List.isEmpty_eq_false_iff, decide_eq_true_eq] at h1 h2
  congr 1
  exact intercalate_dot_inj (fun p hp => h1.2 p hp) (fun q hq => h2.2 q hq) heq

def hasRoot (n : SymName) (part : List Char) : Bool := decide (n.parts.head? = some part)

def hasPart (n : SymName) (part : List Char) : Bool := decide (part ∈ n.parts)

def lastIs (n : SymName) (part : List Char) : Bool := decide (n.parts.getLast? = some part)

/-- `Init` and `Std` only, as `TrustedBoundary.isStdlibMod`. -/
def isStdlibModule (n : SymName) : Bool := n.hasRoot Chars.init || n.hasRoot Chars.std

/-- The compiler's own namespace. It is neither standard library nor importable. -/
def isLeanCompilerModule (n : SymName) : Bool := n.hasRoot Chars.lean

def isTrustedModule (n : SymName) : Bool := n.hasRoot Chars.trusted

/-- `Verify.<Item>` (at least two components) or `CrateVerify` / `CrateVerify.*`. -/
def isVerifyModuleName (n : SymName) : Bool :=
  (n.hasRoot Chars.verify && decide (2 ≤ n.parts.length)) || n.hasRoot Chars.crateVerify

/-- The root `M.verified` of a verify module `M`. -/
def verifiedRoot (n : SymName) : SymName := n.child Chars.verified

/-- Private names carry the `_private` prefix of Lean's name mangling. -/
def isPrivateName (n : SymName) : Bool := n.hasRoot Chars.privatePrefix

def isInternalPart (p : List Char) : Bool :=
  decide (p.head? = some '_') || (!p.isEmpty && p.all Char.isDigit)

def hasInternalPart (n : SymName) : Bool := n.parts.any isInternalPart

/-- Names of auxiliary declarations Lean realizes on demand (`f.eq_1`, `f.congr_simp`, ...). -/
def isReservedAuxName (n : SymName) : Bool :=
  decide (2 ≤ n.parts.length) &&
  match n.parts.getLast? with
  | some l =>
    decide (l ∈ [Chars.eqDef, Chars.congrSimp, Chars.elim, Chars.splitter, Chars.injEq,
      Chars.sizeOfSpec, Chars.noConfusion, Chars.induct]) ||
    Chars.eqPrefix.isPrefixOf l || Chars.matchPrefix.isPrefixOf l ||
    Chars.proofPrefix.isPrefixOf l
  | none => false

/-- `some parent` when the name is `parent._unsafe_rec`. -/
def unsafeRecParent? (n : SymName) : Option SymName :=
  if n.lastIs Chars.unsafeRec ∧ 2 ≤ n.parts.length then some ⟨n.parts.dropLast⟩ else none

def suffixesAux : List (List Char) → List SymName
  | [] => []
  | _ :: rest => (if rest.isEmpty then [] else [⟨rest⟩]) ++ suffixesAux rest

/-- Proper, non-empty suffixes: `A.B.c` has `B.c` and `c`. -/
def properSuffixes (n : SymName) : List SymName := suffixesAux n.parts

def sorryAxName : SymName := ⟨[Chars.sorryAx]⟩
def propextName : SymName := ⟨[Chars.propext]⟩
def choiceName : SymName := ⟨[Chars.classical, Chars.choice]⟩
def quotSoundName : SymName := ⟨[Chars.quot, Chars.sound]⟩
def ofReduceBoolName : SymName := ⟨[Chars.lean, Chars.ofReduceBool]⟩
def ofReduceNatName : SymName := ⟨[Chars.lean, Chars.ofReduceNat]⟩
def reduceBoolName : SymName := ⟨[Chars.lean, Chars.reduceBool]⟩
def reduceNatName : SymName := ⟨[Chars.lean, Chars.reduceNat]⟩
def trustCompilerName : SymName := ⟨[Chars.lean, Chars.trustCompiler]⟩
def natName : SymName := ⟨[Chars.nat]⟩
def natZeroName : SymName := ⟨[Chars.nat, Chars.zero]⟩
def natSuccName : SymName := ⟨[Chars.nat, Chars.succ]⟩
def stringName : SymName := ⟨[Chars.string]⟩
def boolName : SymName := ⟨[Chars.bool]⟩
def boolFalseName : SymName := ⟨[Chars.bool, Chars.boolFalse]⟩
def boolTrueName : SymName := ⟨[Chars.bool, Chars.boolTrue]⟩
def trueName : SymName := ⟨[Chars.trueProp]⟩
def trueIntroName : SymName := ⟨[Chars.trueProp, Chars.intro]⟩
def falseName : SymName := ⟨[Chars.falseProp]⟩
def eqName : SymName := ⟨[Chars.eq]⟩
def eqReflName : SymName := ⟨[Chars.eq, Chars.refl]⟩
def eqBoolName : SymName := ⟨[Chars.eqBool]⟩
def eqBoolReflName : SymName := ⟨[Chars.eqBool, Chars.refl]⟩
def verificationResultName : SymName := ⟨[Chars.trusted, Chars.verificationResult]⟩
def verificationResultIntroName : SymName :=
  ⟨[Chars.trusted, Chars.verificationResult, Chars.intro]⟩
def initModuleName : SymName := ⟨[Chars.init]⟩
def initPreludeModuleName : SymName := ⟨[Chars.init, Chars.prelude]⟩
def initCoreModuleName : SymName := ⟨[Chars.init, Chars.core]⟩
def trustedCoreModuleName : SymName := ⟨[Chars.trusted, Chars.core]⟩

def isFoundationalAxiom (n : SymName) : Bool :=
  decide (n = propextName) || decide (n = choiceName) || decide (n = quotSoundName)

/-- The compiler-generated native marker (`_native` anywhere in the name). -/
def hasNativeMarker (n : SymName) : Bool := n.hasPart Chars.nativeMarker

/-- Strictly interior `._native.` form `<decl>._native.<tactic>.ax_<n>` that
`Lean.Meta.nativeEqTrue` emits: never bare `_native`, `_native.*`, or `*._native`. -/
def isProvisionalNativeName (n : SymName) : Bool :=
  n.hasNativeMarker && decide (3 ≤ n.parts.length) &&
    decide (n.parts.head? ≠ some Chars.nativeMarker) &&
    decide (n.parts.getLast? ≠ some Chars.nativeMarker)

/-- Native-reduction trust: the deprecated `Lean.ofReduceBool` / `Lean.ofReduceNat` axioms,
the `Lean.reduceBool` / `Lean.reduceNat` primitives they justify, and every name with a
`_native` component (the `<decl>._native.<tactic>.ax_<n>` axioms that `native_decide` and
`bv_decide` add on Lean 4.34.1). -/
def isNativeReductionAxiom (n : SymName) : Bool :=
  decide (n = ofReduceBoolName) || decide (n = ofReduceNatName) ||
  decide (n = reduceBoolName) || decide (n = reduceNatName) || n.hasNativeMarker

/-- `Lean.trustCompiler`: banned in every mode. -/
def isCompilerTrustAxiom (n : SymName) : Bool := decide (n = trustCompilerName)

/-- Names whose interpretation the kernel model fixes; packages may not redeclare them. -/
def isBuiltinName (n : SymName) : Bool :=
  decide (n = natName) || decide (n = stringName) || decide (n = falseName)

end SymName

/-! ## Expressions and declarations -/

/-- Kernel expressions with de Bruijn indices. `sort 0` is `Prop`, `sort 1` is `Type`.
There are no free variables, metavariables, `let`, or metadata nodes: a stored
declaration that contains any of them is not representable and so not accepted. -/
inductive ExprSkeleton where
  | bvar (idx : Nat)
  | sort (level : Nat)
  | const (name : SymName)
  | app (fn arg : ExprSkeleton)
  | lam (binderType body : ExprSkeleton)
  | pi (binderType body : ExprSkeleton)
  | natLit (n : Nat)
  | strLit (s : List Char)
  | proj (structName : SymName) (idx : Nat) (struct : ExprSkeleton)
  deriving DecidableEq

namespace ExprSkeleton

/-- Constants an expression mentions. Literals mention their type and projections their
structure, as `TrustedBoundary.expressionEdges` requires. -/
def usedConstants : ExprSkeleton → List SymName
  | bvar _ => []
  | sort _ => []
  | const n => [n]
  | app f a => f.usedConstants ++ a.usedConstants
  | lam t b => t.usedConstants ++ b.usedConstants
  | pi t b => t.usedConstants ++ b.usedConstants
  | natLit _ => [SymName.natName]
  | strLit _ => [SymName.stringName]
  | proj s _ e => s :: e.usedConstants

/-- The conclusion of a function type: what remains under its leading binders. -/
def piTarget : ExprSkeleton → ExprSkeleton
  | pi _ b => b.piTarget
  | e => e

/-- No bound variable escapes `k` enclosing binders. -/
def closedBelow : Nat → ExprSkeleton → Bool
  | k, bvar i => decide (i < k)
  | _, sort _ => true
  | _, const _ => true
  | k, app f a => closedBelow k f && closedBelow k a
  | k, lam t b => closedBelow k t && closedBelow (k + 1) b
  | k, pi t b => closedBelow k t && closedBelow (k + 1) b
  | _, natLit _ => true
  | _, strLit _ => true
  | k, proj _ _ e => closedBelow k e

/-- Shift the variables at or above the cutoff `c` up by `k`. -/
def liftFrom (c k : Nat) : ExprSkeleton → ExprSkeleton
  | bvar i => if i < c then bvar i else bvar (i + k)
  | sort l => sort l
  | const n => const n
  | app f a => app (liftFrom c k f) (liftFrom c k a)
  | lam t b => lam (liftFrom c k t) (liftFrom (c + 1) k b)
  | pi t b => pi (liftFrom c k t) (liftFrom (c + 1) k b)
  | natLit n => natLit n
  | strLit s => strLit s
  | proj s i e => proj s i (liftFrom c k e)

/-- Substitute `a` for variable `c` and lower the variables above it. -/
def instAt (c : Nat) (a : ExprSkeleton) : ExprSkeleton → ExprSkeleton
  | bvar i => if i < c then bvar i else if i = c then liftFrom 0 c a else bvar (i - 1)
  | sort l => sort l
  | const n => const n
  | app f x => app (instAt c a f) (instAt c a x)
  | lam t b => lam (instAt c a t) (instAt (c + 1) a b)
  | pi t b => pi (instAt c a t) (instAt (c + 1) a b)
  | natLit n => natLit n
  | strLit s => strLit s
  | proj s i e => proj s i (instAt c a e)

/-- `body[arg/0]`. -/
def instantiate (body arg : ExprSkeleton) : ExprSkeleton := instAt 0 arg body

def getAppFn : ExprSkeleton → ExprSkeleton
  | app f _ => getAppFn f
  | e => e

def getAppArgsRev : ExprSkeleton → List ExprSkeleton
  | app f a => a :: getAppArgsRev f
  | _ => []

def getAppArgs (e : ExprSkeleton) : List ExprSkeleton :=
  (getAppArgsRev e).reverse

def isLiteral : ExprSkeleton → Bool
  | natLit _ => true
  | strLit _ => true
  | _ => false

def size : ExprSkeleton → Nat
  | app f a => f.size + a.size + 1
  | lam t b => t.size + b.size + 1
  | pi t b => t.size + b.size + 1
  | proj _ _ e => e.size + 1
  | _ => 1

end ExprSkeleton

inductive DeclSafety where
  | safe
  | unsafeDecl
  | partialDecl
  deriving DecidableEq

structure RecRule where
  ctor : SymName
  nfields : Nat
  rhs : ExprSkeleton
  deriving DecidableEq

inductive DeclKind where
  | axiomDecl
  | defnDecl
  | thmDecl
  | opaqueDecl
  | quotDecl
  | inductDecl (ctors : List SymName)
  | ctorDecl (induct : SymName)
  | recDecl (rules : List RecRule)
  deriving DecidableEq

inductive DeclTag where
  | axiomTag | defnTag | thmTag | opaqueTag | quotTag | inductTag | ctorTag | recTag
  deriving DecidableEq

namespace DeclKind

def tag : DeclKind → DeclTag
  | axiomDecl => .axiomTag
  | defnDecl => .defnTag
  | thmDecl => .thmTag
  | opaqueDecl => .opaqueTag
  | quotDecl => .quotTag
  | inductDecl _ => .inductTag
  | ctorDecl _ => .ctorTag
  | recDecl _ => .recTag

/-- Kinds whose `.all` lists the members of their own mutual block. -/
def hasMutualAll : DeclKind → Bool
  | defnDecl => true
  | thmDecl => true
  | opaqueDecl => true
  | inductDecl _ => true
  | _ => false

def render : DeclKind → String
  | axiomDecl => "axiom"
  | defnDecl => "definition"
  | thmDecl => "theorem"
  | opaqueDecl => "opaque"
  | quotDecl => "quotient"
  | inductDecl _ => "inductive"
  | ctorDecl _ => "constructor"
  | recDecl _ => "recursor"

end DeclKind

/-- One stored declaration. `isPrivate`, `originModule`, and `cachedExportedAxioms` are
claims made by the artifact: the first two are checked against computed facts and the
last is never read by any check. -/
structure ConstantRecord where
  name : SymName
  kind : DeclKind
  type : ExprSkeleton
  value? : Option ExprSkeleton := none
  all : List SymName := []
  safety : DeclSafety := .safe
  isPrivate : Bool := false
  originModule : Option SymName := none
  cachedExportedAxioms : List SymName := []
  deriving DecidableEq

namespace ConstantRecord

/-- Every expression stored in the record: type, value (also of `opaque`), recursor rules. -/
def exprs (ci : ConstantRecord) : List ExprSkeleton :=
  ci.type :: (ci.value?.toList ++
    match ci.kind with
    | .recDecl rules => rules.map (·.rhs)
    | _ => [])

/-- Names the record depends on outside its expressions: mutual peers, constructors,
the parent inductive, and recursor-rule constructors. -/
def structuralEdges (ci : ConstantRecord) : List SymName :=
  ci.all ++
    match ci.kind with
    | .inductDecl ctors => ctors
    | .ctorDecl induct => [induct]
    | .recDecl rules => rules.map (·.ctor)
    | _ => []

def edgeList (ci : ConstantRecord) : List SymName :=
  ci.exprs.flatMap ExprSkeleton.usedConstants ++ ci.structuralEdges

/-- Constants referenced by expressions only (what kernel checking needs in scope). -/
def exprConstants (ci : ConstantRecord) : List SymName :=
  ci.exprs.flatMap ExprSkeleton.usedConstants

def isClosed (ci : ConstantRecord) : Bool := ci.exprs.all (ExprSkeleton.closedBelow 0)

end ConstantRecord

/-! ## Diagnostics -/

/-- Every way the audit can fail. Each constructor carries the module or declaration at
fault and the offending names, so the first failure can be reported precisely. -/
inductive AuditFailure where
  | lengthMismatch (mod : SymName) (numNames numConstants : Nat)
  | anonymousConstantName (mod : SymName)
  | keyNameMismatch (mod key recordName : SymName)
  | duplicateConstName (mod name : SymName)
  | duplicateModuleName (mod : SymName)
  | invalidMutualAll (mod decl : SymName) (reason : String)
  | foreignQuotDecl (mod decl : SymName)
  | privateFlagMismatch (mod decl : SymName)
  | extraConstNameProvenance (mod name : SymName) (reason : String)
  | missingOleanServer (mod : SymName)
  | missingOleanPrivate (mod : SymName)
  | moduleRoleMismatch (mod : SymName) (role : String)
  | stdlibNamedPackageModule (mod : SymName)
  | trustedNamedPackageModule (mod : SymName)
  | spoofedExemptModule (mod : SymName)
  | forbiddenImportAll (mod imported : SymName)
  | forbiddenImportModifier (mod imported : SymName) (modifier : String)
  | privateInstanceLeakViaImportAll (mod imported inst : SymName)
  | foreignImport (mod imported : SymName)
  | importCycle (mod : SymName)
  | forbiddenImportDirection (mod : SymName) (role : String) (imported : SymName)
      (importedRole : String)
  | referenceOutsideImportClosure (mod decl dep depMod : SymName)
  | reservedOriginMissingSibling (mod decl origin : SymName)
  | missingSourceText (mod : SymName)
  | unsupportedSourceLexing (mod : SymName) (reason : String)
  | forbiddenSourceOption (mod : SymName) (what : String)
  | forbiddenMacroOrElab (mod : SymName) (kind : String) (decl : SymName)
  | forbiddenInitOrCodegenHook (mod : SymName) (kind : String) (decl : SymName)
  | forbiddenInstanceOrCoe (mod : SymName) (kind : String) (decl : SymName)
  | forbiddenReducibilityOverride (mod target : SymName)
  | forbiddenShadowingOrExport (mod : SymName) (kind : String) (name : SymName)
  | unsafeOrPartialDecl (mod decl : SymName)
  | forbiddenAxiom (user axiomName declaringMod : SymName)
  | forbiddenNativeReductionAxiom (user axiomName : SymName)
  | invalidNativeAxiomType (user axiomName : SymName)
  | testModuleForeignAxiom (mod user axiomName : SymName)
  | invalidVerifyRoot (root : SymName) (reason : String)
  | statementTheoryLeak (root dep depMod : SymName)
  | closureFuelExhausted (root pending : SymName)
  | unknownConstant (name : SymName)
  | cyclicDependency (name : SymName)
  | kernelTypeError (decl : SymName) (reason : String)
  deriving DecidableEq

/-- The replay-key checks report through the same diagnostic type. -/
abbrev ReplayKeyViolation := AuditFailure

/-! ## Check combinators -/

/-- Succeed exactly when `p` holds. -/
def ensure {ε : Type} (p : Prop) [Decidable p] (e : ε) : Except ε Unit :=
  if p then .ok () else .error e

theorem ensure_ok_iff {ε : Type} {p : Prop} [Decidable p] {e : ε} :
    ensure p e = .ok () ↔ p := by
  unfold ensure
  split <;> simp_all

/-- Run a check on every element, stopping at the first failure. -/
def checkAll {ε α : Type} : List α → (α → Except ε Unit) → Except ε Unit
  | [], _ => .ok ()
  | x :: xs, f =>
    match f x with
    | .ok _ => checkAll xs f
    | .error e => .error e

theorem checkAll_ok_iff {ε α : Type} {l : List α} {f : α → Except ε Unit} :
    checkAll l f = .ok () ↔ ∀ x ∈ l, f x = .ok () := by
  induction l with
  | nil => simp [checkAll]
  | cons x xs ih =>
    simp only [checkAll, List.forall_mem_cons]
    cases hfx : f x with
    | ok u => simp [ih]
    | error e => simp

/-- Run a computation on every element and collect the results in order. -/
def collectEach {ε α β : Type} : List α → (α → Except ε β) → Except ε (List β)
  | [], _ => .ok []
  | x :: xs, f =>
    match f x with
    | .error e => .error e
    | .ok y =>
      match collectEach xs f with
      | .error e => .error e
      | .ok ys => .ok (y :: ys)

theorem collectEach_mem {ε α β : Type} {f : α → Except ε β} :
    ∀ {l : List α} {ys : List β}, collectEach l f = .ok ys →
      ∀ y ∈ ys, ∃ x ∈ l, f x = .ok y := by
  intro l
  induction l with
  | nil => intro ys h y hy; simp [collectEach] at h; subst h; simp at hy
  | cons x xs ih =>
    intro ys h y hy
    simp only [collectEach] at h
    cases hfx : f x with
    | error e => simp [hfx] at h
    | ok y0 =>
      cases hrest : collectEach xs f with
      | error e => simp [hfx, hrest] at h
      | ok ys0 =>
        simp [hfx, hrest] at h
        subst h
        rcases List.mem_cons.mp hy with rfl | hy'
        · exact ⟨x, List.mem_cons_self, hfx⟩
        · obtain ⟨x', hx', hf'⟩ := ih hrest y hy'
          exact ⟨x', List.mem_cons_of_mem _ hx', hf'⟩

theorem collectEach_forall {ε α β : Type} {f : α → Except ε β} :
    ∀ {l : List α} {ys : List β}, collectEach l f = .ok ys →
      ∀ x ∈ l, ∃ y ∈ ys, f x = .ok y := by
  intro l
  induction l with
  | nil => intro ys _ x hx; simp at hx
  | cons x xs ih =>
    intro ys h x' hx'
    simp only [collectEach] at h
    cases hfx : f x with
    | error e => simp [hfx] at h
    | ok y0 =>
      cases hrest : collectEach xs f with
      | error e => simp [hfx, hrest] at h
      | ok ys0 =>
        simp [hfx, hrest] at h
        subst h
        rcases List.mem_cons.mp hx' with rfl | hx''
        · exact ⟨y0, List.mem_cons_self, hfx⟩
        · obtain ⟨y, hy, hf'⟩ := ih hrest x' hx''
          exact ⟨y, List.mem_cons_of_mem _ hy, hf'⟩

theorem collectEach_map {ε α β : Type} {f : α → Except ε β} (g : β → α)
    (hg : ∀ x y, f x = .ok y → g y = x) :
    ∀ {l : List α} {ys : List β}, collectEach l f = .ok ys → ys.map g = l := by
  intro l
  induction l with
  | nil => intro ys h; simp [collectEach] at h; subst h; rfl
  | cons x xs ih =>
    intro ys h
    simp only [collectEach] at h
    cases hfx : f x with
    | error e => simp [hfx] at h
    | ok y0 =>
      cases hrest : collectEach xs f with
      | error e => simp [hfx, hrest] at h
      | ok ys0 =>
        simp [hfx, hrest] at h
        subst h
        simp [hg x y0 hfx, ih hrest]

theorem bind_ok_iff {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β} :
    (x >>= f) = .ok b ↔ ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x <;> simp [bind, Except.bind]

theorem bindUnit_ok_iff {ε β : Type} {x : Except ε Unit} {f : Unit → Except ε β} {b : β} :
    (x >>= f) = .ok b ↔ x = .ok () ∧ f () = .ok b := by
  cases x <;> simp [bind, Except.bind]

/-- The first element that occurs again later in the list. -/
def firstDuplicate? : List SymName → Option SymName
  | [] => none
  | x :: xs => if x ∈ xs then some x else firstDuplicate? xs

theorem firstDuplicate?_eq_none_iff (l : List SymName) : firstDuplicate? l = none ↔ l.Nodup := by
  induction l with
  | nil => simp [firstDuplicate?]
  | cons x xs ih =>
    simp only [firstDuplicate?, List.nodup_cons]
    by_cases hx : x ∈ xs
    · simp [hx]
    · simp [hx, ih]

theorem firstDuplicate?_mem {l : List SymName} {d : SymName} (h : firstDuplicate? l = some d) :
    d ∈ l := by
  induction l with
  | nil => simp [firstDuplicate?] at h
  | cons x xs ih =>
    simp only [firstDuplicate?] at h
    split at h
    · cases h; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih h)

/-- Fail with `mkErr d` on the first duplicate `d`. -/
def ensureNodup {ε : Type} (l : List SymName) (mkErr : SymName → ε) : Except ε Unit :=
  match firstDuplicate? l with
  | some d => .error (mkErr d)
  | none => .ok ()

theorem ensureNodup_ok_iff {ε : Type} {l : List SymName} {mkErr : SymName → ε} :
    ensureNodup l mkErr = .ok () ↔ l.Nodup := by
  unfold ensureNodup
  rw [← firstDuplicate?_eq_none_iff]
  split <;> simp_all

/-! ## Environments -/

/-- An environment as an association list; the first entry for a key wins. -/
abbrev KernelEnv := List (SymName × ConstantRecord)

namespace KernelEnv

def lookup : KernelEnv → SymName → Option ConstantRecord
  | [], _ => none
  | (k, ci) :: rest, n => if k = n then some ci else lookup rest n

def contains (env : KernelEnv) (n : SymName) : Bool := (env.lookup n).isSome

theorem lookup_mem {env : KernelEnv} {n : SymName} {ci : ConstantRecord}
    (h : env.lookup n = some ci) : (n, ci) ∈ env := by
  induction env with
  | nil => simp [lookup] at h
  | cons p rest ih =>
    obtain ⟨k, c⟩ := p
    simp only [lookup] at h
    split at h
    · cases h; subst_vars; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih h)

theorem lookup_append {env₁ env₂ : KernelEnv} {n : SymName} :
    lookup (env₁ ++ env₂) n = (lookup env₁ n).or (lookup env₂ n) := by
  induction env₁ with
  | nil => simp [lookup]
  | cons p rest ih =>
    obtain ⟨k, c⟩ := p
    simp only [List.cons_append, lookup]
    split <;> simp_all

theorem lookup_isSome_of_mem {env : KernelEnv} {n : SymName} {ci : ConstantRecord}
    (h : (n, ci) ∈ env) : (env.lookup n).isSome = true := by
  induction env with
  | nil => simp at h
  | cons p rest ih =>
    obtain ⟨k, c⟩ := p
    simp only [lookup]
    split
    · rfl
    · rename_i hne
      rcases List.mem_cons.mp h with heq | hmem
      · cases heq; exact absurd rfl hne
      · exact ih hmem

/-- With duplicate-free keys, membership determines lookup. -/
theorem lookup_of_mem_nodup {env : KernelEnv} {n : SymName} {ci : ConstantRecord}
    (hnd : (env.map Prod.fst).Nodup) (h : (n, ci) ∈ env) : env.lookup n = some ci := by
  induction env with
  | nil => simp at h
  | cons p rest ih =>
    obtain ⟨k, c⟩ := p
    simp only [List.map_cons, List.nodup_cons] at hnd
    simp only [lookup]
    rcases List.mem_cons.mp h with heq | hmem
    · cases heq; simp
    · split
      · rename_i hk
        subst hk
        exact absurd (List.mem_map.mpr ⟨(k, ci), hmem, rfl⟩) hnd.1
      · exact ih hnd.2 hmem

end KernelEnv

/-- The first record with the given name. -/
def findConstByName : List ConstantRecord → SymName → Option ConstantRecord
  | [], _ => none
  | ci :: rest, n => if ci.name = n then some ci else findConstByName rest n

theorem findConstByName_mem {cs : List ConstantRecord} {n : SymName} {ci : ConstantRecord}
    (h : findConstByName cs n = some ci) : ci ∈ cs ∧ ci.name = n := by
  induction cs with
  | nil => simp [findConstByName] at h
  | cons c rest ih =>
    simp only [findConstByName] at h
    split at h
    · cases h; exact ⟨List.mem_cons_self, by assumption⟩
    · exact ⟨List.mem_cons_of_mem _ (ih h).1, (ih h).2⟩

/-- The pinned base environment keyed by record name. -/
def mkBaseKernelEnv (base : List ConstantRecord) : KernelEnv := base.map (fun ci => (ci.name, ci))

theorem lookup_mkBaseKernelEnv (cs : List ConstantRecord) (n : SymName) :
    KernelEnv.lookup (mkBaseKernelEnv cs) n = findConstByName cs n := by
  induction cs with
  | nil => rfl
  | cons c rest ih =>
    simp only [mkBaseKernelEnv, List.map_cons, KernelEnv.lookup, findConstByName]
    split
    · rfl
    · exact ih

namespace ConstantRecord

/-- All dependency edges of a declaration, or an error if it stores an open expression
(`TrustedBoundary.expressionEdges` fails the same way). -/
def declarationEdges (ci : ConstantRecord) : Except AuditFailure (List SymName) :=
  if ci.isClosed then .ok ci.edgeList
  else .error (.kernelTypeError ci.name "open expression in stored declaration")

theorem declarationEdges_ok {ci : ConstantRecord} {edges : List SymName}
    (h : ci.declarationEdges = .ok edges) : edges = ci.edgeList ∧ ci.isClosed = true := by
  unfold declarationEdges at h
  split at h
  · cases h; exact ⟨rfl, by assumption⟩
  · cases h

theorem all_subset_edgeList (ci : ConstantRecord) : ∀ p ∈ ci.all, p ∈ ci.edgeList := by
  intro p hp
  simp only [edgeList, structuralEdges, List.mem_append]
  exact Or.inr (Or.inl hp)

end ConstantRecord

/-- An upper bound on the number of edges `declarationEdges` can emit. -/
def edgeCount (ci : ConstantRecord) : Nat := ci.edgeList.length

/-! ## Modules, roles, and packages -/

inductive ModuleRole where
  | foundation
  | trusted
  | theory
  | spec
  | defsExempt
  | assumptions
  | proof
  | verify
  | test
  deriving DecidableEq

namespace ModuleRole

def render : ModuleRole → String
  | foundation => "foundation"
  | trusted => "trusted"
  | theory => "theory"
  | spec => "spec"
  | defsExempt => "defsExempt"
  | assumptions => "assumptions"
  | proof => "proof"
  | verify => "verify"
  | test => "test"

end ModuleRole

/-- Roles whose declarations may appear in a verified statement. -/
def isStatementSideRole : ModuleRole → Bool
  | .foundation => true
  | .trusted => true
  | .spec => true
  | .defsExempt => true
  | .assumptions => true
  | _ => false

/-- The one role a module name can justify. Reserved roots (`Init`, `Std`, `Trusted`,
`Anneal`, `Assumptions`, `Verify`, `CrateVerify`) admit only their own role; `Lean.*`,
the anonymous name, bare `Assumptions` / `Verify`, and names with both a proof and a
test segment justify none. Elsewhere a `Proof`/`Proofs` segment means proof, a
`Test`/`Tests` segment means test, a final `Defs` means definitions, and anything
else is a specification module. -/
def classifyModuleName (m : SymName) : Option ModuleRole :=
  if !m.isWellFormed then none
  else if m.isLeanCompilerModule then none
  else if m.isStdlibModule then some .foundation
  else if m.isTrustedModule then some .trusted
  else if m.hasRoot Chars.anneal then some .theory
  else if m.hasRoot Chars.assumptions then
    (if 2 ≤ m.parts.length then some .assumptions else none)
  else if m.hasRoot Chars.verify || m.hasRoot Chars.crateVerify then
    (if m.isVerifyModuleName then some .verify else none)
  else if (m.hasPart Chars.proof || m.hasPart Chars.proofs) &&
      (m.hasPart Chars.test || m.hasPart Chars.tests) then
    none
  else if m.hasPart Chars.proof || m.hasPart Chars.proofs then some .proof
  else if m.hasPart Chars.test || m.hasPart Chars.tests then some .test
  else if m.lastIs Chars.defs then some .defsExempt
  else some .spec

/-- A role label is acceptable only if the module name justifies exactly that role. -/
def roleMatchesModuleName (r : ModuleRole) (m : SymName) : Bool :=
  decide (classifyModuleName m = some r)

/-- A module name matches at most one role. -/
theorem roleMatchesModuleName_unique {r1 r2 : ModuleRole} {m : SymName}
    (h1 : roleMatchesModuleName r1 m = true) (h2 : roleMatchesModuleName r2 m = true) :
    r1 = r2 := by
  simp only [roleMatchesModuleName, decide_eq_true_eq] at h1 h2
  rw [h1] at h2
  exact Option.some.inj h2

/-- Only a name that classifies as a definitions module may claim the `Defs` exemption
(`Topic.Proofs.Defs` is a proof module). -/
def SymName.isStrictExemptModuleName (m : SymName) : Bool :=
  decide (classifyModuleName m = some .defsExempt)

/-- The role of a module that is not part of the audited package. Names that justify no
role get `theory`, the role with no privileges that statements may not mention. -/
def baseRoleOfModuleName (m : SymName) : ModuleRole := (classifyModuleName m).getD .theory

structure ImportSpec where
  module : SymName
  importAll : Bool := false
  isExported : Bool := true
  isMeta : Bool := false
  deriving DecidableEq

/-- Which files of a module's compiled artifact are present on disk. -/
structure OleanArtifactParts where
  isModuleMode : Bool := false
  hasServer : Bool := false
  hasPrivate : Bool := false
  deriving DecidableEq

/-- One entry of a persistent environment extension table, as read from the `.olean`.
Entries name declarations only; whether a declaration is local is always computed from
the module's inventory, never stored. -/
inductive EnvExtEntry where
  | macroEntry (decl : SymName)
  | syntaxEntry (decl : SymName)
  | commandElabEntry (decl : SymName)
  | localCommandElabEntry (decl : SymName) (persistedGlobal : Bool)
  | termElabEntry (decl : SymName)
  | delabEntry (decl : SymName)
  | appUnexpanderEntry (decl : SymName)
  | scopedMacroEntry (decl scopeNs : SymName)
  | scopedElabEntry (decl scopeNs : SymName)
  | initializeEntry (decl : SymName) (isMeta : Bool)
  | implementedByEntry (decl impl : SymName)
  | externEntry (decl : SymName)
  | instanceEntry (decl targetClass : SymName) (isPrivateInst : Bool)
  | scopedInstanceEntry (decl targetClass scopeNs : SymName)
  | defaultInstanceEntry (decl targetClass : SymName)
  | coeEntry (decl srcType tgtType : SymName)
  | reducibilityOverride (target : SymName)
  | exportAlias (aliasName target : SymName)
  deriving DecidableEq

namespace EnvExtEntry

/-- The declaration an entry must own: instance-like entries and reducibility targets. -/
def localDecl? : EnvExtEntry → Option SymName
  | instanceEntry d _ _ => some d
  | scopedInstanceEntry d _ _ => some d
  | defaultInstanceEntry d _ => some d
  | coeEntry d _ _ => some d
  | reducibilityOverride t => some t
  | _ => none

/-- Constants an entry makes visible to elaboration. -/
def referencedConstants : EnvExtEntry → List SymName
  | instanceEntry d c _ => [d, c]
  | scopedInstanceEntry d c _ => [d, c]
  | defaultInstanceEntry d c => [d, c]
  | coeEntry d s t => [d, s, t]
  | reducibilityOverride t => [t]
  | implementedByEntry d i => [d, i]
  | exportAlias _ t => [t]
  | macroEntry d => [d]
  | syntaxEntry d => [d]
  | commandElabEntry d => [d]
  | localCommandElabEntry d _ => [d]
  | termElabEntry d => [d]
  | delabEntry d => [d]
  | appUnexpanderEntry d => [d]
  | scopedMacroEntry d _ => [d]
  | scopedElabEntry d _ => [d]
  | initializeEntry d _ => [d]
  | externEntry d => [d]

/-- Namespaces an entry is scoped to; each must be a module the entry's module can see. -/
def referencedModules : EnvExtEntry → List SymName
  | scopedInstanceEntry _ _ ns => [ns]
  | scopedMacroEntry _ ns => [ns]
  | scopedElabEntry _ ns => [ns]
  | _ => []

end EnvExtEntry

/-- What the inspector reads from one compiled module. -/
structure ModuleInventory where
  moduleName : SymName
  role : ModuleRole
  constNames : List SymName
  constants : List ConstantRecord
  extraConstNames : List SymName := []
  imports : List ImportSpec := []
  extEntries : List EnvExtEntry := []
  oleanParts : OleanArtifactParts := {}
  sourceText? : Option (List Char) := none
  deriving DecidableEq

/-- Attach a source text given as a `String` (for drivers; tests give characters). -/
def ModuleInventory.withSourceText (inv : ModuleInventory) (src : String) : ModuleInventory :=
  { inv with sourceText? := some src.toList }

/-- The map Lean builds on import: `constNames[i] ↦ constants[i]`, truncated at the
shorter array. -/
def ModuleInventory.replayMap (inv : ModuleInventory) : KernelEnv :=
  inv.constNames.zip inv.constants

/-- The environment after importing the given modules (first insertion wins). -/
def KernelEnv.finalizeImportedEnv (invs : List ModuleInventory) : KernelEnv :=
  invs.flatMap ModuleInventory.replayMap

/-- Audit modes. The default is the strict production mode: no assumption axioms, no
provisional native axioms, no test-local axioms, and a source text for every module. -/
structure AuditConfig where
  allowAssumptions : Bool := false
  allowProvisionalNative : Bool := false
  allowLocalTestAxioms : Bool := false
  requireSources : Bool := true
  deriving DecidableEq

/-- The production configuration. -/
def defaultStrictConfig : AuditConfig := {}

/-- `--provisional`: additionally admit compiler-generated `_native` axioms of proof modules. -/
def provisionalConfig : AuditConfig := { allowProvisionalNative := true }

/-- Conditional verification: additionally admit axioms of `Assumptions.*` modules. -/
def conditionalConfig : AuditConfig := { allowAssumptions := true }

/-- No axiom of any kind is admitted. -/
def AuditConfig.admitsNoAxioms (cfg : AuditConfig) : Prop :=
  cfg.allowAssumptions = false ∧ cfg.allowProvisionalNative = false ∧
    cfg.allowLocalTestAxioms = false

/-- A package: the pinned, separately audited base environment and the modules to audit. -/
structure PackageAuditInput where
  baseEnv : List ConstantRecord
  modules : List ModuleInventory
  verifyRoots : List SymName := []
  claimRoots : List SymName := []
  deriving DecidableEq

inductive VerifyItemStatus where
  | verifiedUnconditional
  | verifiedConditional
  | provisionalNative
  | provisionalNativeConditional
  deriving DecidableEq

structure VerifyItemReport where
  root : SymName
  status : VerifyItemStatus
  reachedProvisional : List SymName
  reachedAssumptions : List SymName
  deriving DecidableEq

structure AuditCertificate where
  importedEnv : KernelEnv
  replayedEnv : KernelEnv
  reachedAxioms : List SymName
  itemReports : List VerifyItemReport
  deriving DecidableEq

/-! ## Inventory validation: replay keys and mutual blocks -/

/-- The `lean4#16677` checks. Lean inserts `constants[i]` under `constNames[i]` and
replays by record name; the two agree only if the arrays have equal length, the keys
are distinct and well-formed (non-anonymous, non-empty dot-free components), and every
key equals its record's name. -/
def validateModuleDataKeys (inv : ModuleInventory) : Except ReplayKeyViolation Unit := do
  ensure (inv.constNames.length = inv.constants.length)
    (.lengthMismatch inv.moduleName inv.constNames.length inv.constants.length)
  ensure (inv.constNames.all SymName.isWellFormed = true) (.anonymousConstantName inv.moduleName)
  ensureNodup inv.constNames (.duplicateConstName inv.moduleName)
  checkAll inv.replayMap
    (fun p => ensure (p.1 = p.2.name) (.keyNameMismatch inv.moduleName p.1 p.2.name))

theorem validateModuleDataKeys_ok_iff {inv : ModuleInventory} :
    validateModuleDataKeys inv = .ok () ↔
      inv.constNames.length = inv.constants.length ∧
      (∀ n ∈ inv.constNames, n.isWellFormed = true) ∧
      inv.constNames.Nodup ∧ ∀ p ∈ inv.replayMap, p.1 = p.2.name := by
  simp only [validateModuleDataKeys, bindUnit_ok_iff, ensure_ok_iff, ensureNodup_ok_iff,
    checkAll_ok_iff, List.all_eq_true]

def validateAllHygiene (inv : ModuleInventory) (ci : ConstantRecord) : Except AuditFailure Unit := do
  ensure (ci.all ≠ []) (.invalidMutualAll inv.moduleName ci.name "empty .all")
  ensureNodup ci.all (fun _ => .invalidMutualAll inv.moduleName ci.name "duplicate entry in .all")
  ensure (SymName.anonymous ∉ ci.all)
    (.invalidMutualAll inv.moduleName ci.name "anonymous entry in .all")
  ensure (ci.all.all SymName.isWellFormed = true)
    (.invalidMutualAll inv.moduleName ci.name "malformed entry in .all")

def validateMutualPeer (inv : ModuleInventory) (ci : ConstantRecord) (peer : SymName) :
    Except AuditFailure Unit :=
  match findConstByName inv.constants peer with
  | none => .error (.invalidMutualAll inv.moduleName ci.name "missing mutual peer")
  | some pc => do
    ensure (pc.kind.tag = ci.kind.tag)
      (.invalidMutualAll inv.moduleName ci.name "incompatible mutual peer kind")
    ensure (pc.all = ci.all) (.invalidMutualAll inv.moduleName ci.name "asymmetric mutual .all")

/-- A mutual block is well formed: non-empty, duplicate-free, non-anonymous, contains the
declaration itself, and every peer is a same-kind declaration of this module with the
same `.all`. Lean 4.34.1 replay rebuilds an inductive block from `.all` by name, so
`ci.name ∈ ci.all` is a soundness check, not hygiene. -/
def validateMutualBlock (inv : ModuleInventory) (ci : ConstantRecord) : Except AuditFailure Unit := do
  validateAllHygiene inv ci
  ensure (ci.name ∈ ci.all) (.invalidMutualAll inv.moduleName ci.name "ci.name missing from .all")
  checkAll ci.all (validateMutualPeer inv ci)

/-- Every name in a recursor's `.all` is an inductive type of this module whose own `.all`
matches the recursor's mutual block. -/
def validateRecAllTarget (inv : ModuleInventory) (ci : ConstantRecord) (target : SymName) :
    Except AuditFailure Unit :=
  match findConstByName inv.constants target with
  | none =>
    .error (.invalidMutualAll inv.moduleName ci.name "missing inductive target of recursor .all")
  | some ic => do
    ensure (ic.kind.tag = .inductTag)
      (.invalidMutualAll inv.moduleName ci.name "recursor .all target is not an inductive")
    ensure (ic.all = ci.all)
      (.invalidMutualAll inv.moduleName ci.name "recursor .all differs from inductive .all")

def validateNonBlockAll (inv : ModuleInventory) (ci : ConstantRecord) : Except AuditFailure Unit :=
  match ci.kind with
  | .recDecl _ => do
    validateAllHygiene inv ci
    checkAll ci.all (validateRecAllTarget inv ci)
  | _ =>
    ensure (ci.all = [])
      (.invalidMutualAll inv.moduleName ci.name "unexpected .all on a declaration without one")

def validateCtorOfInduct (inv : ModuleInventory) (ci : ConstantRecord) (ctor : SymName) :
    Except AuditFailure Unit :=
  match findConstByName inv.constants ctor with
  | none => .error (.invalidMutualAll inv.moduleName ci.name "inductive lists a missing constructor")
  | some cc =>
    ensure (cc.kind = .ctorDecl ci.name)
      (.invalidMutualAll inv.moduleName ci.name "inductive lists a constructor of another type")

/-- Constructors and inductives must point at each other within the module. -/
def validateKindLinks (inv : ModuleInventory) (ci : ConstantRecord) : Except AuditFailure Unit :=
  match ci.kind with
  | .ctorDecl induct =>
    match findConstByName inv.constants induct with
    | none =>
      .error (.invalidMutualAll inv.moduleName ci.name "constructor of a missing inductive")
    | some ic =>
      match ic.kind with
      | .inductDecl ctors =>
        ensure (ci.name ∈ ctors)
          (.invalidMutualAll inv.moduleName ci.name "constructor is not listed by its inductive")
      | _ => .error (.invalidMutualAll inv.moduleName ci.name "constructor parent is not an inductive")
  | .inductDecl ctors => do
    ensureNodup ctors
      (fun _ => .invalidMutualAll inv.moduleName ci.name "duplicate constructor name")
    checkAll ctors (validateCtorOfInduct inv ci)
  | _ => .ok ()

def validateAllField (inv : ModuleInventory) (ci : ConstantRecord) : Except AuditFailure Unit :=
  if ci.kind.hasMutualAll then validateMutualBlock inv ci else validateNonBlockAll inv ci

def validateMutualAll (inv : ModuleInventory) (ci : ConstantRecord) : Except AuditFailure Unit := do
  validateAllField inv ci
  validateKindLinks inv ci

def validateConstantRecord (inv : ModuleInventory) (ci : ConstantRecord) :
    Except AuditFailure Unit := do
  ensure (ci.isPrivate = ci.name.isPrivateName) (.privateFlagMismatch inv.moduleName ci.name)
  ensure (ci.kind ≠ .quotDecl ∨ inv.moduleName.isStdlibModule = true)
    (.foreignQuotDecl inv.moduleName ci.name)
  validateMutualAll inv ci

/-- `extraConstNames` extends the module's claim on names without storing records. The
names must be well-formed (non-anonymous, non-empty dot-free components) and distinct
from each other and from the declared names. -/
def validateExtraConstNames (inv : ModuleInventory) : Except AuditFailure Unit := do
  ensure (inv.extraConstNames.all SymName.isWellFormed = true)
    (.anonymousConstantName inv.moduleName)
  ensureNodup (inv.constNames ++ inv.extraConstNames) (.duplicateConstName inv.moduleName)

/-- Complete per-module inventory validation. -/
def validateReplayInventory (inv : ModuleInventory) : Except AuditFailure Unit := do
  validateModuleDataKeys inv
  validateExtraConstNames inv
  checkAll inv.constants (validateConstantRecord inv)

theorem validateReplayInventory_ok {inv : ModuleInventory}
    (h : validateReplayInventory inv = .ok ()) :
    validateModuleDataKeys inv = .ok () ∧ validateExtraConstNames inv = .ok () ∧
      ∀ ci ∈ inv.constants, validateConstantRecord inv ci = .ok () := by
  simpa only [validateReplayInventory, bindUnit_ok_iff, checkAll_ok_iff] using h

theorem zip_keys_eq_map {ks : List SymName} {cs : List ConstantRecord}
    (hlen : ks.length = cs.length) (h : ∀ p ∈ ks.zip cs, p.1 = p.2.name) :
    ks = cs.map ConstantRecord.name := by
  induction ks generalizing cs with
  | nil => cases cs with
    | nil => rfl
    | cons c cs => simp at hlen
  | cons k ks ih =>
    cases cs with
    | nil => simp at hlen
    | cons c cs =>
      simp only [List.zip_cons_cons, List.forall_mem_cons] at h
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      simp only [List.map_cons]
      rw [h.1, ← ih hlen h.2]

theorem map_name_zip (cs : List ConstantRecord) :
    (cs.map ConstantRecord.name).zip cs = mkBaseKernelEnv cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp only [List.map_cons, List.zip_cons_cons, mkBaseKernelEnv] at ih ⊢; rw [ih]

/-- An accepted inventory has as many keys as records, so Lean's parallel insertion loop
truncates nothing. -/
theorem validInventory_length_eq {inv : ModuleInventory}
    (h : validateReplayInventory inv = .ok ()) :
    inv.constNames.length = inv.constants.length ∧
      inv.replayMap = inv.constNames.zip inv.constants :=
  ⟨(validateModuleDataKeys_ok_iff.mp (validateReplayInventory_ok h).1).1, rfl⟩

theorem validInventory_constNames_nodup {inv : ModuleInventory}
    (h : validateReplayInventory inv = .ok ()) : inv.constNames.Nodup :=
  (validateModuleDataKeys_ok_iff.mp (validateReplayInventory_ok h).1).2.2.1

/-- Every map key is the name of the record stored under it. -/
theorem validInventory_key_eq_ci_name {inv : ModuleInventory}
    (h : validateReplayInventory inv = .ok ()) :
    (∀ p ∈ inv.replayMap, p.1 = p.2.name) ∧
      inv.constNames = inv.constants.map ConstantRecord.name := by
  have hk := validateModuleDataKeys_ok_iff.mp (validateReplayInventory_ok h).1
  exact ⟨hk.2.2.2, zip_keys_eq_map hk.1 hk.2.2.2⟩

theorem validInventory_replayMap_eq {inv : ModuleInventory}
    (h : validateReplayInventory inv = .ok ()) : inv.replayMap = mkBaseKernelEnv inv.constants := by
  have hk := (validInventory_key_eq_ci_name h).2
  unfold ModuleInventory.replayMap
  rw [hk, map_name_zip]

/-- Lookup by key (what import does) and lookup by record name (what replay does) agree. -/
theorem validInventory_lookup_bijection {inv : ModuleInventory}
    (h : validateReplayInventory inv = .ok ()) :
    ∀ n, KernelEnv.lookup inv.replayMap n = findConstByName inv.constants n ∧
      KernelEnv.lookup (KernelEnv.finalizeImportedEnv [inv]) n =
        findConstByName inv.constants n := by
  intro n
  have hmap := validInventory_replayMap_eq h
  refine ⟨by rw [hmap, lookup_mkBaseKernelEnv], ?_⟩
  simp only [KernelEnv.finalizeImportedEnv, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [hmap, lookup_mkBaseKernelEnv]

theorem validateMutualPeer_ok {inv : ModuleInventory} {ci : ConstantRecord} {peer : SymName}
    (h : validateMutualPeer inv ci peer = .ok ()) :
    ∃ pc, findConstByName inv.constants peer = some pc ∧ pc.kind.tag = ci.kind.tag ∧
      pc.all = ci.all := by
  unfold validateMutualPeer at h
  split at h
  · cases h
  · rename_i pc hpc
    simp only [bindUnit_ok_iff, ensure_ok_iff] at h
    exact ⟨pc, hpc, h.1, h.2⟩

/-- Mutual `.all` blocks of an accepted inventory are well formed, and every peer is a
dependency edge, so nothing hides in a mutual sibling. -/
theorem validInventory_mutual_all_wf {inv : ModuleInventory}
    (h : validateReplayInventory inv = .ok ()) :
    ∀ ci ∈ inv.constants, ci.kind.hasMutualAll = true →
      ci.all ≠ [] ∧ ci.all.Nodup ∧ SymName.anonymous ∉ ci.all ∧ ci.name ∈ ci.all ∧
      (∀ peer ∈ ci.all, ∃ pc, findConstByName inv.constants peer = some pc ∧
        pc.kind.tag = ci.kind.tag ∧ pc.all = ci.all) ∧
      (∀ edges, ci.declarationEdges = .ok edges → ∀ peer ∈ ci.all, peer ∈ edges) := by
  intro ci hci hkind
  have hrec := (validateReplayInventory_ok h).2.2 ci hci
  simp only [validateConstantRecord, validateMutualAll, bindUnit_ok_iff] at hrec
  have hall := hrec.2.2.1
  simp only [validateAllField, hkind, ↓reduceIte, validateMutualBlock, validateAllHygiene,
    bindUnit_ok_iff, ensure_ok_iff, ensureNodup_ok_iff, checkAll_ok_iff] at hall
  obtain ⟨⟨hne, hnd, hanon, _⟩, hself, hpeers⟩ := hall
  refine ⟨hne, hnd, hanon, hself, fun peer hp => validateMutualPeer_ok (hpeers peer hp), ?_⟩
  intro edges hedges peer hp
  rw [(ConstantRecord.declarationEdges_ok hedges).1]
  exact ci.all_subset_edgeList peer hp

/-- Every name in a recursor's `.all` resolves to an inductive type of the same module
whose mutual `.all` block matches the recursor's `.all`. -/
theorem validInventory_rec_all_targets_induct {inv : ModuleInventory}
    (h : validateReplayInventory inv = .ok ()) :
    ∀ ci ∈ inv.constants, ∀ rules, ci.kind = .recDecl rules →
      ∀ target ∈ ci.all, ∃ ic, findConstByName inv.constants target = some ic ∧
        ic.kind.tag = .inductTag ∧ ic.all = ci.all := by
  intro ci hci rules hkind target ht
  have hrec := (validateReplayInventory_ok h).2.2 ci hci
  simp only [validateConstantRecord, validateMutualAll, bindUnit_ok_iff] at hrec
  have hall := hrec.2.2.1
  simp only [validateAllField, hkind, DeclKind.hasMutualAll, Bool.false_eq_true, ↓reduceIte,
    validateNonBlockAll, bindUnit_ok_iff, checkAll_ok_iff] at hall
  have htarget := hall.2 target ht
  unfold validateRecAllTarget at htarget
  split at htarget
  · cases htarget
  · rename_i ic hic
    simp only [bindUnit_ok_iff, ensure_ok_iff] at htarget
    exact ⟨ic, hic, htarget.1, htarget.2⟩

/-! ## Worklist closure -/

/-- Depth-first worklist closure with a visited set. It fails closed: when the fuel runs
out with a name still pending it reports `exhausted`, never a partial result. -/
def worklist {α ε : Type} [DecidableEq α] (expand : α → Except ε (List α)) (exhausted : α → ε) :
    Nat → List α → List α → Except ε (List α)
  | _, [], visited => .ok visited
  | 0, p :: _, _ => .error (exhausted p)
  | fuel + 1, p :: pending, visited =>
    if p ∈ visited then worklist expand exhausted fuel pending visited
    else
      match expand p with
      | .error e => .error e
      | .ok edges => worklist expand exhausted fuel (edges ++ pending) (p :: visited)

/-- Reflexive-transitive reachability along successfully expanded edges. -/
inductive Reach {α ε : Type} (expand : α → Except ε (List α)) : α → α → Prop where
  | refl (a : α) : Reach expand a a
  | step {a b c : α} {edges : List α} :
      expand a = .ok edges → b ∈ edges → Reach expand b c → Reach expand a c

/-- A successful walk keeps everything visited and pending, and every name it adds
expands with all its edges inside the result. -/
theorem worklist_closed {α ε : Type} [DecidableEq α] {expand : α → Except ε (List α)}
    {exhausted : α → ε} :
    ∀ (fuel : Nat) (pending visited result : List α),
      worklist expand exhausted fuel pending visited = .ok result →
      (∀ v ∈ visited, v ∈ result) ∧ (∀ p ∈ pending, p ∈ result) ∧
      (∀ n ∈ result, n ∈ visited ∨
        ∃ edges, expand n = .ok edges ∧ ∀ e ∈ edges, e ∈ result) := by
  intro fuel
  induction fuel with
  | zero =>
    intro pending visited result h
    cases pending with
    | nil =>
      simp only [worklist, Except.ok.injEq] at h
      subst h
      exact ⟨fun _ hv => hv, by simp, fun _ hn => Or.inl hn⟩
    | cons p rest => simp [worklist] at h
  | succ fuel ih =>
    intro pending visited result h
    cases pending with
    | nil =>
      simp only [worklist, Except.ok.injEq] at h
      subst h
      exact ⟨fun _ hv => hv, by simp, fun _ hn => Or.inl hn⟩
    | cons p rest =>
      simp only [worklist] at h
      split at h
      · rename_i hp
        obtain ⟨hv, hpd, hcl⟩ := ih rest visited result h
        refine ⟨hv, ?_, hcl⟩
        intro q hq
        rcases List.mem_cons.mp hq with rfl | hq'
        · exact hv _ hp
        · exact hpd _ hq'
      · rename_i hp
        split at h
        · cases h
        · rename_i edges hedges
          obtain ⟨hv, hpd, hcl⟩ := ih (edges ++ rest) (p :: visited) result h
          refine ⟨fun v hv' => hv v (List.mem_cons_of_mem _ hv'), ?_, ?_⟩
          · intro q hq
            rcases List.mem_cons.mp hq with rfl | hq'
            · exact hv _ List.mem_cons_self
            · exact hpd _ (List.mem_append_right _ hq')
          · intro n hn
            rcases hcl n hn with hnv | hne
            · rcases List.mem_cons.mp hnv with rfl | hnv'
              · exact Or.inr ⟨edges, hedges, fun e he => hpd e (List.mem_append_left _ he)⟩
              · exact Or.inl hnv'
            · exact Or.inr hne

/-- Everything a successful walk returns was already visited or is reachable from a
pending name. -/
theorem worklist_origin {α ε : Type} [DecidableEq α] {expand : α → Except ε (List α)}
    {exhausted : α → ε} :
    ∀ (fuel : Nat) (pending visited result : List α),
      worklist expand exhausted fuel pending visited = .ok result →
      ∀ n ∈ result, n ∈ visited ∨ ∃ p ∈ pending, Reach expand p n := by
  intro fuel
  induction fuel with
  | zero =>
    intro pending visited result h
    cases pending with
    | nil =>
      simp only [worklist, Except.ok.injEq] at h
      subst h
      exact fun _ hn => Or.inl hn
    | cons p rest => simp [worklist] at h
  | succ fuel ih =>
    intro pending visited result h
    cases pending with
    | nil =>
      simp only [worklist, Except.ok.injEq] at h
      subst h
      exact fun _ hn => Or.inl hn
    | cons p rest =>
      simp only [worklist] at h
      split at h
      · intro n hn
        rcases ih rest visited result h n hn with hv | ⟨q, hq, hr⟩
        · exact Or.inl hv
        · exact Or.inr ⟨q, List.mem_cons_of_mem _ hq, hr⟩
      · split at h
        · cases h
        · rename_i edges hedges
          intro n hn
          rcases ih (edges ++ rest) (p :: visited) result h n hn with hv | ⟨q, hq, hr⟩
          · rcases List.mem_cons.mp hv with rfl | hv'
            · exact Or.inr ⟨n, List.mem_cons_self, Reach.refl n⟩
            · exact Or.inl hv'
          · rcases List.mem_append.mp hq with hqe | hqr
            · exact Or.inr ⟨p, List.mem_cons_self, Reach.step hedges hqe hr⟩
            · exact Or.inr ⟨q, List.mem_cons_of_mem _ hqr, hr⟩

/-- A set closed under expansion contains everything reachable from its members. -/
theorem reach_mem_of_closed {α ε : Type} {expand : α → Except ε (List α)} {result : List α}
    (hcl : ∀ n ∈ result, ∃ edges, expand n = .ok edges ∧ ∀ e ∈ edges, e ∈ result)
    {a d : α} (hr : Reach expand a d) (ha : a ∈ result) : d ∈ result := by
  induction hr with
  | refl a => exact ha
  | step hexp hb _ ih =>
    obtain ⟨edges', hexp', hsub⟩ := hcl _ ha
    rw [hexp] at hexp'
    cases hexp'
    exact ih (hsub _ hb)

/-- Budget of unvisited work: one step plus its edge bound for every universe entry whose
key has not been visited. -/
def worklistBudget {α : Type} [DecidableEq α] (visited : List α) : List (α × Nat) → Nat
  | [] => 0
  | (u, c) :: rest => (if u ∈ visited then 0 else 1 + c) + worklistBudget visited rest

theorem worklistBudget_mono {α : Type} [DecidableEq α] (a : α) (visited : List α)
    (univ : List (α × Nat)) :
    worklistBudget (a :: visited) univ ≤ worklistBudget visited univ := by
  induction univ with
  | nil => simp [worklistBudget]
  | cons p rest ih =>
    obtain ⟨u, c⟩ := p
    simp only [worklistBudget, List.mem_cons]
    by_cases hu : u ∈ visited
    · simp [hu]; exact ih
    · by_cases hua : u = a
      · simp [hua]; omega
      · simp [hu, hua]; omega

theorem worklistBudget_visit {α : Type} [DecidableEq α] {a : α} {c : Nat} {visited : List α}
    {univ : List (α × Nat)} (hmem : (a, c) ∈ univ) (hnv : a ∉ visited) :
    worklistBudget (a :: visited) univ + (1 + c) ≤ worklistBudget visited univ := by
  induction univ with
  | nil => simp at hmem
  | cons p rest ih =>
    obtain ⟨u, c'⟩ := p
    simp only [worklistBudget, List.mem_cons]
    rcases List.mem_cons.mp hmem with heq | hrest
    · cases heq
      have := worklistBudget_mono a visited rest
      simp [hnv]
      omega
    · have := ih hrest
      by_cases hu : u ∈ visited
      · simp [hu]; omega
      · by_cases hua : u = a
        · simp [hua, hnv]; omega
        · simp [hu, hua]; omega

/-- Liveness: with fuel at least `pending.length + worklistBudget visited univ`, where
every expansion is either empty or bounded by a universe entry of the expanded name,
the walk never reports exhaustion; any error comes from `expand` itself. -/
theorem worklist_error_of_fuel {α ε : Type} [DecidableEq α] {expand : α → Except ε (List α)}
    {exhausted : α → ε} {univ : List (α × Nat)}
    (hb : ∀ a edges, expand a = .ok edges →
      edges = [] ∨ ∃ c, (a, c) ∈ univ ∧ edges.length ≤ c) :
    ∀ (fuel : Nat) (pending visited : List α) (e : ε),
      pending.length + worklistBudget visited univ ≤ fuel →
      worklist expand exhausted fuel pending visited = .error e →
      ∃ a, expand a = .error e := by
  intro fuel
  induction fuel with
  | zero =>
    intro pending visited e hfuel h
    cases pending with
    | nil => simp [worklist] at h
    | cons p rest => simp at hfuel
  | succ fuel ih =>
    intro pending visited e hfuel h
    cases pending with
    | nil => simp [worklist] at h
    | cons p rest =>
      simp only [worklist] at h
      simp only [List.length_cons] at hfuel
      split at h
      · exact ih rest visited e (by omega) h
      · rename_i hp
        split at h
        · rename_i e' he'
          cases h
          exact ⟨p, he'⟩
        · rename_i edges hedges
          refine ih (edges ++ rest) (p :: visited) e ?_ h
          simp only [List.length_append]
          rcases hb p edges hedges with hnil | ⟨c, hc, hle⟩
          · subst hnil
            have := worklistBudget_mono p visited univ
            simp
            omega
          · have := worklistBudget_visit hc hp
            omega

/-! ## Constant-dependency graphs -/

/-- Expansion of a name in an environment: unknown names are errors. -/
def graphExpand (env : KernelEnv)
    (expand : SymName → ConstantRecord → Except AuditFailure (List SymName)) (n : SymName) :
    Except AuditFailure (List SymName) :=
  match env.lookup n with
  | none => .error (.unknownConstant n)
  | some ci => expand n ci

/-- Fail-closed closure walk over the constants of `env`. -/
def walkGraph (env : KernelEnv) (root : SymName)
    (expand : SymName → ConstantRecord → Except AuditFailure (List SymName))
    (fuel : Nat) (pending visited : List SymName) : Except AuditFailure (List SymName) :=
  worklist (graphExpand env expand) (.closureFuelExhausted root) fuel pending visited

/-- Reachability in `env` along `expand`. -/
abbrev GraphReaches (env : KernelEnv)
    (expand : SymName → ConstantRecord → Except AuditFailure (List SymName)) :
    SymName → SymName → Prop :=
  Reach (graphExpand env expand)

/-- Work left for a walk of `env`: one step and `edgeCount` edges per unvisited entry. -/
def unvisitedBudget (visited : List SymName) (env : KernelEnv) : Nat :=
  worklistBudget visited (env.map (fun p => (p.1, edgeCount p.2)))

/-- Fuel that provably suffices for a walk from one root. -/
def closureFuel (env : KernelEnv) : Nat := 1 + unvisitedBudget [] env

/-- Worklist invariant of a successful walk. -/
theorem walkGraph_sound {env : KernelEnv} {root : SymName}
    {expand : SymName → ConstantRecord → Except AuditFailure (List SymName)}
    {fuel : Nat} {pending visited result : List SymName}
    (h : walkGraph env root expand fuel pending visited = .ok result) :
    (∀ v ∈ visited, v ∈ result) ∧ (∀ p ∈ pending, p ∈ result) ∧
    (∀ n ∈ result, n ∈ visited ∨ ∃ ci edges, env.lookup n = some ci ∧
      expand n ci = .ok edges ∧ ∀ e ∈ edges, e ∈ result) := by
  obtain ⟨hv, hp, hcl⟩ := worklist_closed fuel pending visited result h
  refine ⟨hv, hp, fun n hn => ?_⟩
  rcases hcl n hn with hnv | ⟨edges, hexp, hsub⟩
  · exact Or.inl hnv
  · unfold graphExpand at hexp
    split at hexp
    · cases hexp
    · rename_i ci hci
      exact Or.inr ⟨ci, edges, hci, hexp, hsub⟩

/-- Completeness of a successful walk from scratch: it contains everything reachable from
the pending roots, and every returned name resolves and expands. -/
theorem walkGraph_reaches_subset {env : KernelEnv} {root : SymName}
    {expand : SymName → ConstantRecord → Except AuditFailure (List SymName)}
    {fuel : Nat} {pending result : List SymName}
    (h : walkGraph env root expand fuel pending [] = .ok result) :
    (∀ p ∈ pending, ∀ d, GraphReaches env expand p d → d ∈ result) ∧
    (∀ n ∈ result, ∃ ci edges, env.lookup n = some ci ∧ expand n ci = .ok edges ∧
      ∀ e ∈ edges, e ∈ result) := by
  obtain ⟨_, hp, hcl⟩ := worklist_closed fuel pending [] result h
  have hcl' : ∀ n ∈ result, ∃ edges, graphExpand env expand n = .ok edges ∧
      ∀ e ∈ edges, e ∈ result := by
    intro n hn
    rcases hcl n hn with hnv | hne
    · simp at hnv
    · exact hne
  refine ⟨fun p hpp d hr => reach_mem_of_closed hcl' hr (hp p hpp), fun n hn => ?_⟩
  rcases (walkGraph_sound h).2.2 n hn with hnv | hne
  · simp at hnv
  · exact hne

/-- Liveness: if `expand` emits at most `edgeCount ci` edges and never itself reports
fuel exhaustion, a walk with fuel `≥ pending.length + unvisitedBudget visited env` never
fails with `closureFuelExhausted`. -/
theorem walkGraph_never_exhausts_fuel {env : KernelEnv} {root : SymName}
    {expand : SymName → ConstantRecord → Except AuditFailure (List SymName)}
    (hbound : ∀ n ci edges, expand n ci = .ok edges → edges.length ≤ edgeCount ci)
    (hnoexh : ∀ n ci r p, expand n ci ≠ .error (.closureFuelExhausted r p))
    {fuel : Nat} {pending visited : List SymName}
    (hfuel : pending.length + unvisitedBudget visited env ≤ fuel) (r p : SymName) :
    walkGraph env root expand fuel pending visited ≠ .error (.closureFuelExhausted r p) := by
  intro h
  have hb : ∀ a edges, graphExpand env expand a = .ok edges →
      edges = [] ∨ ∃ c, (a, c) ∈ env.map (fun q => (q.1, edgeCount q.2)) ∧ edges.length ≤ c := by
    intro a edges hexp
    unfold graphExpand at hexp
    split at hexp
    · cases hexp
    · rename_i ci hci
      exact Or.inr ⟨edgeCount ci, List.mem_map.mpr ⟨(a, ci), KernelEnv.lookup_mem hci, rfl⟩,
        hbound a ci edges hexp⟩
  obtain ⟨a, ha⟩ := worklist_error_of_fuel hb fuel pending visited _ hfuel h
  unfold graphExpand at ha
  split at ha
  · cases ha
  · exact hnoexh _ _ _ _ ha

/-- The dependency expansion of the closure walk: all declaration edges. -/
def closureExpand (_ : SymName) (ci : ConstantRecord) : Except AuditFailure (List SymName) :=
  ci.declarationEdges

/-- Genuine transitive dependency in `env` through `declarationEdges`. -/
abbrev DepReaches (env : KernelEnv) : SymName → SymName → Prop := GraphReaches env closureExpand

theorem closureExpand_bound (n : SymName) (ci : ConstantRecord) (edges : List SymName)
    (h : closureExpand n ci = .ok edges) : edges.length ≤ edgeCount ci := by
  rw [(ConstantRecord.declarationEdges_ok h).1]
  exact Nat.le_refl _

theorem closureExpand_no_exhaust (n : SymName) (ci : ConstantRecord) (r p : SymName) :
    closureExpand n ci ≠ .error (.closureFuelExhausted r p) := by
  unfold closureExpand ConstantRecord.declarationEdges
  split <;> simp

/-- The closure walk from a single root never runs out of `closureFuel`. -/
theorem closureExpand_never_exhausts_fuel (env : KernelEnv) (root r p : SymName) :
    walkGraph env root closureExpand (closureFuel env) [root] [] ≠
      .error (.closureFuelExhausted r p) :=
  walkGraph_never_exhausts_fuel closureExpand_bound closureExpand_no_exhaust
    (by simp [closureFuel]) r p

/-! ## Kernel model: reduction, conversion, and type inference

The fragment: `sort 0` (`Prop`), `sort 1` (data types), and `sort 2` for everything else
that is a type (`Prop` itself, function and predicate types). A dependent function type
`pi A B` is a proposition when `B` is (impredicative, any `A`); otherwise `A` must be a data
type. Applications, abstractions, constants, and `Nat`/`String` literals are typed as in
Lean; projections are rejected. `whnf` unfolds definitions at the head and β-reduces a
literal argument: the semantics below validates β exactly for data arguments, and literals
are the arguments whose data-hood needs no typing derivation. -/

def whnf (env : KernelEnv) : Nat → ExprSkeleton → ExprSkeleton
  | 0, e => e
  | fuel + 1, .const c =>
    match env.lookup c with
    | some ci =>
      if ci.kind = .defnDecl then
        match ci.value? with
        | some v => whnf env fuel v
        | none => .const c
      else .const c
    | none => .const c
  | fuel + 1, .app f a =>
    match whnf env fuel f with
    | .lam t b => if a.isLiteral then whnf env fuel (b.instantiate a) else .app (.lam t b) a
    | f' => .app f' a
  | _, e => e

/-- Definitional equality: syntactic equality, or congruence of weak head normal forms. -/
def isDefEq (env : KernelEnv) : Nat → ExprSkeleton → ExprSkeleton → Bool
  | 0, a, b => decide (a = b)
  | fuel + 1, a, b =>
    decide (a = b) ||
    match whnf env fuel a, whnf env fuel b with
    | .app f x, .app g y => isDefEq env fuel f g && isDefEq env fuel x y
    | .lam s t, .lam u v => isDefEq env fuel s u && isDefEq env fuel t v
    | .pi s t, .pi u v => isDefEq env fuel s u && isDefEq env fuel t v
    | a', b' => decide (a' = b')

/-- The universe level of a type expression's sort. -/
def asSort (env : KernelEnv) (fuel : Nat) (t : ExprSkeleton) : Except String Nat :=
  match whnf env fuel t with
  | .sort l => .ok l
  | _ => .error "type expected"

def inferType (env : KernelEnv) : Nat → List ExprSkeleton → ExprSkeleton → Except String ExprSkeleton
  | 0, _, _ => .error "kernel fuel exhausted"
  | _ + 1, ctx, .bvar i =>
    match ctx[i]? with
    | some t => .ok (t.liftFrom 0 (i + 1))
    | none => .error "loose bound variable"
  | _ + 1, _, .sort l => if l ≤ 1 then .ok (.sort 2) else .error "universe level out of range"
  | _ + 1, _, .const c =>
    match env.lookup c with
    | some ci => .ok ci.type
    | none => .error "unknown constant"
  | fuel + 1, ctx, .app f a => do
    let tf ← inferType env fuel ctx f
    match whnf env fuel tf with
    | .pi dom cod => do
      let ta ← inferType env fuel ctx a
      if isDefEq env fuel dom ta then .ok (cod.instantiate a)
      else .error "application argument type mismatch"
    | _ => .error "function expected"
  | fuel + 1, ctx, .lam t b => do
    let st ← inferType env fuel ctx t
    let sA ← asSort env fuel st
    let tb ← inferType env fuel (t :: ctx) b
    let stb ← inferType env fuel (t :: ctx) tb
    let sB ← asSort env fuel stb
    if sB = 0 ∨ sA = 1 then .ok (.pi t tb)
    else .error "abstraction over a non-data binder must produce a proof"
  | fuel + 1, ctx, .pi t b => do
    let st ← inferType env fuel ctx t
    let sA ← asSort env fuel st
    let sb ← inferType env fuel (t :: ctx) b
    let sB ← asSort env fuel sb
    if sB = 0 then .ok (.sort 0)
    else if sA = 1 then .ok (.sort 2)
    else .error "function type over a non-data domain must be a proposition"
  | _ + 1, _, .natLit _ =>
    if env.contains SymName.natName then .ok (.const SymName.natName)
    else .error "Nat literal without Nat"
  | _ + 1, _, .strLit _ =>
    if env.contains SymName.stringName then .ok (.const SymName.stringName)
    else .error "String literal without String"
  | _ + 1, _, .proj _ _ _ => .error "projections are outside the modeled kernel fragment"

/-! ## Semantic model -/

/-- First-order data: the elements of data types. -/
inductive Dom where
  | nat (n : Nat)
  | str (s : List Char)
  | enum (ty ctor : SymName)

inductive DataTag where
  | nat
  | str
  | enum (ty : SymName) (ctors : List SymName)

def DataTag.carrier : DataTag → Dom → Prop
  | .nat, .nat _ => True
  | .str, .str _ => True
  | .enum ty ctors, .enum ty' c => ty' = ty ∧ c ∈ ctors
  | _, _ => False

/-- Semantic values: propositions, sorts, data and data types, functions out of data, and
function types with a data domain. Functions take `Dom` arguments, which keeps the type
strictly positive; propositions quantify over all of `SemVal`. -/
inductive SemVal where
  | junk
  | prop (P : Prop)
  | sort (level : Nat)
  | elem (d : Dom)
  | dataTy (t : DataTag)
  | fn (f : Dom → SemVal)
  | piTy (dom : SemVal) (cod : Dom → SemVal)

namespace SemVal

def holds : SemVal → Prop
  | prop P => P
  | _ => False

def isTypeVal : SemVal → Prop
  | prop _ => True
  | sort _ => True
  | dataTy _ => True
  | piTy _ _ => True
  | _ => False

end SemVal

def sortMem : Nat → SemVal → Prop
  | 0, v => ∃ P, v = .prop P
  | 1, v => ∃ t, v = .dataTy t
  | _ + 2, v => v.isTypeVal

/-- `Mem v T`: the value `v` inhabits the type value `T`. Membership in a proposition is
its truth, whatever the proof value. -/
def Mem : SemVal → SemVal → Prop
  | _, .prop P => P
  | v, .sort l => sortMem l v
  | v, .dataTy t => ∃ d, v = .elem d ∧ t.carrier d
  | v, .piTy A B => ∃ g, v = .fn g ∧ ∀ d, Mem (.elem d) A → Mem (g d) (B d)
  | _, .junk => False
  | _, .elem _ => False
  | _, .fn _ => False

def applyVal : SemVal → SemVal → SemVal
  | .fn g, .elem d => g d
  | _, _ => .junk

/-- The function type over a data domain; junk for any other domain. -/
def semPiData (A : SemVal) (B : SemVal → SemVal) : SemVal :=
  match A with
  | .dataTy t => .piTy (.dataTy t) (fun d => B (.elem d))
  | _ => .junk

open Classical in
/-- The value of `pi A B`: the proposition `∀ v ∈ A, B v` when `B` is a family of
propositions, a function type when `A` is a data type, and junk otherwise. -/
noncomputable def semPi (A : SemVal) (B : SemVal → SemVal) : SemVal :=
  if (∀ v, Mem v A → ∃ P, B v = .prop P) then .prop (∀ v, Mem v A → (B v).holds)
  else semPiData A B

theorem semPi_of_prop {A : SemVal} {B : SemVal → SemVal}
    (hp : ∀ v, Mem v A → ∃ P, B v = .prop P) :
    semPi A B = .prop (∀ v, Mem v A → (B v).holds) := by
  unfold semPi
  split
  · rfl
  · contradiction

theorem semPi_of_not_prop {A : SemVal} {B : SemVal → SemVal}
    (hp : ¬ ∀ v, Mem v A → ∃ P, B v = .prop P) : semPi A B = semPiData A B := by
  unfold semPi
  split
  · contradiction
  · rfl

abbrev Model := SymName → SemVal

abbrev Valuation := Nat → SemVal

def Valuation.cons (v : SemVal) (ρ : Valuation) : Valuation
  | 0 => v
  | i + 1 => ρ i

def Valuation.ofList (l : List SemVal) : Valuation := fun i => l.getD i .junk

/-- Denotation of an expression under a model of the constants and a valuation of the
bound variables. -/
noncomputable def evalIn (M : Model) : Valuation → ExprSkeleton → SemVal
  | ρ, .bvar i => ρ i
  | _, .sort l => .sort l
  | _, .const n => M n
  | ρ, .app f a => applyVal (evalIn M ρ f) (evalIn M ρ a)
  | ρ, .lam _ b => .fn (fun d => evalIn M (Valuation.cons (.elem d) ρ) b)
  | ρ, .pi t b => semPi (evalIn M ρ t) (fun v => evalIn M (Valuation.cons v ρ) b)
  | _, .natLit n => .elem (.nat n)
  | _, .strLit s => .elem (.str s)
  | _, .proj _ _ _ => .junk

/-- Denotation under a list of values for the bound variables. -/
noncomputable def evalExpr (M : Model) (ρ : List SemVal) (e : ExprSkeleton) : SemVal :=
  evalIn M (Valuation.ofList ρ) e

theorem cons_lift (v : SemVal) (ρ : Valuation) (c k : Nat) :
    (fun i => if i < c + 1 then Valuation.cons v ρ i else Valuation.cons v ρ (i + k)) =
      Valuation.cons v (fun i => if i < c then ρ i else ρ (i + k)) := by
  funext i
  cases i with
  | zero => simp [Valuation.cons]
  | succ j =>
    simp only [Valuation.cons, Nat.add_lt_add_iff_right]
    split
    · rfl
    · rw [Nat.add_right_comm]

theorem evalIn_liftFrom (M : Model) (k : Nat) :
    ∀ (e : ExprSkeleton) (c : Nat) (ρ : Valuation),
      evalIn M ρ (e.liftFrom c k) = evalIn M (fun i => if i < c then ρ i else ρ (i + k)) e := by
  intro e
  induction e with
  | bvar i =>
    intro c ρ
    simp only [ExprSkeleton.liftFrom]
    by_cases h : i < c
    · simp [h, evalIn]
    · simp [h, evalIn]
  | sort l => intro c ρ; rfl
  | const n => intro c ρ; rfl
  | app f a ihf iha => intro c ρ; simp only [ExprSkeleton.liftFrom, evalIn, ihf, iha]
  | lam t b _ ihb =>
    intro c ρ
    simp only [ExprSkeleton.liftFrom, evalIn]
    congr 1
    funext d
    rw [ihb (c + 1), cons_lift]
  | pi t b iht ihb =>
    intro c ρ
    simp only [ExprSkeleton.liftFrom, evalIn]
    rw [iht c ρ]
    congr 1
    funext v
    rw [ihb (c + 1), cons_lift]
  | natLit n => intro c ρ; rfl
  | strLit s => intro c ρ; rfl
  | proj s i e _ => intro c ρ; rfl

theorem cons_inst (M : Model) (a : ExprSkeleton) (v : SemVal) (ρ : Valuation) (c : Nat) :
    (fun i => if i < c + 1 then Valuation.cons v ρ i
      else if i = c + 1 then evalIn M (fun j => Valuation.cons v ρ (j + (c + 1))) a
      else Valuation.cons v ρ (i - 1)) =
    Valuation.cons v (fun i => if i < c then ρ i
      else if i = c then evalIn M (fun j => ρ (j + c)) a else ρ (i - 1)) := by
  funext i
  cases i with
  | zero => simp [Valuation.cons]
  | succ j =>
    simp only [Valuation.cons, Nat.add_lt_add_iff_right, Nat.add_right_cancel_iff,
      Nat.add_sub_cancel]
    split
    · rfl
    · split
      · rfl
      · cases j with
        | zero => omega
        | succ j' => rfl

theorem evalIn_instAt (M : Model) (a : ExprSkeleton) :
    ∀ (e : ExprSkeleton) (c : Nat) (ρ : Valuation),
      evalIn M ρ (ExprSkeleton.instAt c a e) =
        evalIn M (fun i => if i < c then ρ i
          else if i = c then evalIn M (fun j => ρ (j + c)) a else ρ (i - 1)) e := by
  intro e
  induction e with
  | bvar i =>
    intro c ρ
    simp only [ExprSkeleton.instAt]
    by_cases h1 : i < c
    · simp [h1, evalIn]
    · by_cases h2 : i = c
      · subst h2
        simp only [Nat.lt_irrefl, ↓reduceIte, evalIn]
        rw [evalIn_liftFrom]
        simp
      · simp [h1, h2, evalIn]
  | sort l => intro c ρ; rfl
  | const n => intro c ρ; rfl
  | app f x ihf ihx => intro c ρ; simp only [ExprSkeleton.instAt, evalIn, ihf, ihx]
  | lam t b _ ihb =>
    intro c ρ
    simp only [ExprSkeleton.instAt, evalIn]
    congr 1
    funext d
    rw [ihb (c + 1), cons_inst]
  | pi t b iht ihb =>
    intro c ρ
    simp only [ExprSkeleton.instAt, evalIn]
    rw [iht c ρ]
    congr 1
    funext v
    rw [ihb (c + 1), cons_inst]
  | natLit n => intro c ρ; rfl
  | strLit s => intro c ρ; rfl
  | proj s i e _ => intro c ρ; rfl

/-- Substitution lemma: instantiating the body is evaluating it with the argument's value. -/
theorem evalIn_instantiate (M : Model) (b a : ExprSkeleton) (ρ : Valuation) :
    evalIn M ρ (b.instantiate a) = evalIn M (Valuation.cons (evalIn M ρ a) ρ) b := by
  unfold ExprSkeleton.instantiate
  rw [evalIn_instAt]
  congr 1
  funext i
  cases i with
  | zero => simp [Valuation.cons]
  | succ j => simp [Valuation.cons]

/-- The denotation depends on the model only at the constants the expression mentions. -/
theorem evalIn_model_congr {M M' : Model} :
    ∀ (e : ExprSkeleton) (ρ : Valuation), (∀ c ∈ e.usedConstants, M c = M' c) →
      evalIn M ρ e = evalIn M' ρ e := by
  intro e
  induction e with
  | bvar i => intro ρ _; rfl
  | sort l => intro ρ _; rfl
  | const n => intro ρ h; exact h n (by simp [ExprSkeleton.usedConstants])
  | app f a ihf iha =>
    intro ρ h
    simp only [ExprSkeleton.usedConstants, List.mem_append] at h
    simp only [evalIn, ihf ρ (fun c hc => h c (Or.inl hc)), iha ρ (fun c hc => h c (Or.inr hc))]
  | lam t b _ ihb =>
    intro ρ h
    simp only [ExprSkeleton.usedConstants, List.mem_append] at h
    simp only [evalIn]
    congr 1
    funext d
    exact ihb _ (fun c hc => h c (Or.inr hc))
  | pi t b iht ihb =>
    intro ρ h
    simp only [ExprSkeleton.usedConstants, List.mem_append] at h
    simp only [evalIn]
    rw [iht ρ (fun c hc => h c (Or.inl hc))]
    congr 1
    funext v
    exact ihb _ (fun c hc => h c (Or.inr hc))
  | natLit n => intro ρ _; rfl
  | strLit s => intro ρ _; rfl
  | proj s i e _ => intro ρ _; rfl

/-- A closed expression denotes the same value under every valuation. -/
theorem evalIn_closedBelow (M : Model) :
    ∀ (e : ExprSkeleton) (k : Nat) (ρ ρ' : Valuation), e.closedBelow k = true →
      (∀ i, i < k → ρ i = ρ' i) → evalIn M ρ e = evalIn M ρ' e := by
  intro e
  induction e with
  | bvar i =>
    intro k ρ ρ' hc h
    simp only [ExprSkeleton.closedBelow, decide_eq_true_eq] at hc
    exact h i hc
  | sort l => intros; rfl
  | const n => intros; rfl
  | app f a ihf iha =>
    intro k ρ ρ' hc h
    simp only [ExprSkeleton.closedBelow, Bool.and_eq_true] at hc
    simp only [evalIn, ihf k ρ ρ' hc.1 h, iha k ρ ρ' hc.2 h]
  | lam t b _ ihb =>
    intro k ρ ρ' hc h
    simp only [ExprSkeleton.closedBelow, Bool.and_eq_true] at hc
    simp only [evalIn]
    congr 1
    funext d
    refine ihb (k + 1) _ _ hc.2 (fun i hi => ?_)
    cases i with
    | zero => rfl
    | succ j => exact h j (by omega)
  | pi t b iht ihb =>
    intro k ρ ρ' hc h
    simp only [ExprSkeleton.closedBelow, Bool.and_eq_true] at hc
    simp only [evalIn]
    rw [iht k ρ ρ' hc.1 h]
    congr 1
    funext v
    refine ihb (k + 1) _ _ hc.2 (fun i hi => ?_)
    cases i with
    | zero => rfl
    | succ j => exact h j (by omega)
  | natLit n => intros; rfl
  | strLit s => intros; rfl
  | proj s i e _ => intros; rfl

theorem evalIn_closed (M : Model) {e : ExprSkeleton} (hc : e.closedBelow 0 = true)
    (ρ ρ' : Valuation) : evalIn M ρ e = evalIn M ρ' e :=
  evalIn_closedBelow M e 0 ρ ρ' hc (fun _ hi => absurd hi (Nat.not_lt_zero _))

/-- A model of an environment: every constant inhabits its type, definitions denote their
values, and the builtin types and enumeration types have their standard meaning. `inScope`
records that stored expressions only mention constants of the environment, so extending
the model at a fresh name changes none of the facts. -/
structure EnvSound (env : KernelEnv) (M : Model) : Prop where
  typed : ∀ c ci, env.lookup c = some ci → ∀ ρ, Mem (M c) (evalIn M ρ ci.type)
  defn : ∀ c ci v, env.lookup c = some ci → ci.kind = .defnDecl → ci.value? = some v →
    ∀ ρ, evalIn M ρ v = M c
  natTy : env.contains SymName.natName = true → M SymName.natName = .dataTy .nat
  strTy : env.contains SymName.stringName = true → M SymName.stringName = .dataTy .str
  falseTy : env.contains SymName.falseName = true → M SymName.falseName = .prop False
  enumTy : ∀ c ci ctors, env.lookup c = some ci → ci.kind = .inductDecl ctors →
    ci.type = .sort 1 → c.isBuiltinName = false → M c = .dataTy (.enum c ctors)
  enumCtor : ∀ c ci T, env.lookup c = some ci → ci.kind = .ctorDecl T → ci.type = .const T →
    T.isBuiltinName = false → M c = .elem (.enum T c)
  inScope : ∀ c ci, env.lookup c = some ci → ∀ d ∈ ci.exprConstants, env.contains d = true

theorem whnf_sound {env : KernelEnv} {M : Model} (hs : EnvSound env M) :
    ∀ (fuel : Nat) (e : ExprSkeleton) (ρ : Valuation),
      evalIn M ρ (whnf env fuel e) = evalIn M ρ e := by
  intro fuel
  induction fuel with
  | zero => intro e ρ; rfl
  | succ fuel ih =>
    intro e ρ
    cases e with
    | const c =>
      simp only [whnf]
      split
      · rename_i ci hci
        split
        · rename_i hk
          split
          · rename_i v hv
            rw [ih v ρ]
            exact hs.defn c ci v hci hk hv ρ
          · rfl
        · rfl
      · rfl
    | app f a =>
      simp only [whnf]
      have hf := ih f ρ
      split
      · rename_i t b hw
        rw [hw] at hf
        split
        · rename_i hlit
          rw [ih, evalIn_instantiate]
          simp only [evalIn] at hf ⊢
          rw [← hf]
          cases a with
          | natLit n => simp only [evalIn, applyVal]
          | strLit s => simp only [evalIn, applyVal]
          | _ => simp [ExprSkeleton.isLiteral] at hlit
        · simp only [evalIn] at hf ⊢
          rw [hf]
      · simp only [evalIn]
        rw [hf]
    | bvar i => rfl
    | sort l => rfl
    | lam t b => rfl
    | pi t b => rfl
    | natLit n => rfl
    | strLit s => rfl
    | proj s i e => rfl

theorem isDefEq_sound {env : KernelEnv} {M : Model} (hs : EnvSound env M) :
    ∀ (fuel : Nat) (a b : ExprSkeleton), isDefEq env fuel a b = true →
      ∀ ρ, evalIn M ρ a = evalIn M ρ b := by
  intro fuel
  induction fuel with
  | zero =>
    intro a b h ρ
    simp only [isDefEq, decide_eq_true_eq] at h
    rw [h]
  | succ fuel ih =>
    intro a b h ρ
    simp only [isDefEq, Bool.or_eq_true, decide_eq_true_eq] at h
    rcases h with rfl | h
    · rfl
    · rw [← whnf_sound hs fuel a ρ, ← whnf_sound hs fuel b ρ]
      revert h
      generalize whnf env fuel a = a'
      generalize whnf env fuel b = b'
      intro h
      split at h
      · simp only [Bool.and_eq_true] at h
        simp only [evalIn, ih _ _ h.1 ρ, ih _ _ h.2 ρ]
      · simp only [Bool.and_eq_true] at h
        simp only [evalIn]
        congr 1
        funext d
        exact ih _ _ h.2 _
      · simp only [Bool.and_eq_true] at h
        simp only [evalIn]
        rw [ih _ _ h.1 ρ]
        congr 1
        funext v
        exact ih _ _ h.2 _
      · simp only [decide_eq_true_eq] at h
        rw [h]

theorem asSort_sound {env : KernelEnv} {M : Model} (hs : EnvSound env M) {fuel : Nat}
    {t : ExprSkeleton} {l : Nat} (h : asSort env fuel t = .ok l) (ρ : Valuation) :
    evalIn M ρ t = .sort l := by
  unfold asSort at h
  split at h
  · rename_i l' hw
    cases h
    rw [← whnf_sound hs fuel t ρ, hw]
    rfl
  · cases h

/-- A valuation satisfies a typing context. -/
def CtxOK (M : Model) (ctx : List ExprSkeleton) (ρ : Valuation) : Prop :=
  ∀ i t, ctx[i]? = some t → Mem (ρ i) (evalIn M (fun j => ρ (j + (i + 1))) t)

theorem ctxOK_nil (M : Model) (ρ : Valuation) : CtxOK M [] ρ := by
  intro i t h
  simp at h

theorem ctxOK_cons {M : Model} {ctx : List ExprSkeleton} {ρ : Valuation} {t : ExprSkeleton}
    {v : SemVal} (hρ : CtxOK M ctx ρ) (hv : Mem v (evalIn M ρ t)) :
    CtxOK M (t :: ctx) (Valuation.cons v ρ) := by
  intro i t' h
  cases i with
  | zero =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    exact hv
  | succ k =>
    simp only [List.getElem?_cons_succ] at h
    exact hρ k t' h

theorem mem_dataTy_of_sort_one {v : SemVal} (h : Mem v (.sort 1)) : ∃ t, v = .dataTy t := h

theorem inferType_sound {env : KernelEnv} {M : Model} (hs : EnvSound env M) :
    ∀ (fuel : Nat) (ctx : List ExprSkeleton) (e T : ExprSkeleton),
      inferType env fuel ctx e = .ok T →
      ∀ ρ, CtxOK M ctx ρ → Mem (evalIn M ρ e) (evalIn M ρ T) := by
  intro fuel
  induction fuel with
  | zero => intro ctx e T h; simp [inferType] at h
  | succ fuel ih =>
    intro ctx e T h ρ hρ
    cases e with
    | bvar i =>
      simp only [inferType] at h
      split at h
      · rename_i t ht
        cases h
        rw [evalIn_liftFrom]
        simp only [evalIn, Nat.not_lt_zero, ↓reduceIte]
        exact hρ i t ht
      · cases h
    | sort l =>
      simp only [inferType] at h
      split at h
      · cases h
        simp [evalIn, Mem, sortMem, SemVal.isTypeVal]
      · cases h
    | const c =>
      simp only [inferType] at h
      split at h
      · rename_i ci hci
        cases h
        exact hs.typed c ci hci ρ
      · cases h
    | app f a =>
      simp only [inferType, bind_ok_iff] at h
      obtain ⟨tf, htf, h⟩ := h
      split at h
      · rename_i dom cod hw
        simp only [bind_ok_iff] at h
        obtain ⟨ta, hta, h⟩ := h
        split at h
        · rename_i hdef
          cases h
          have h1 := ih ctx f tf htf ρ hρ
          rw [← whnf_sound hs fuel tf ρ, hw] at h1
          have h2 := ih ctx a ta hta ρ hρ
          rw [← isDefEq_sound hs fuel dom ta hdef ρ] at h2
          rw [evalIn_instantiate]
          simp only [evalIn] at h1 ⊢
          by_cases hp : ∀ v, Mem v (evalIn M ρ dom) →
              ∃ P, evalIn M (Valuation.cons v ρ) cod = .prop P
          · rw [semPi_of_prop hp] at h1
            simp only [Mem] at h1
            obtain ⟨P, hP⟩ := hp _ h2
            have h3 := h1 _ h2
            rw [hP] at h3 ⊢
            exact h3
          · rw [semPi_of_not_prop hp] at h1
            revert h1 h2
            generalize evalIn M ρ dom = A
            intro h1 h2
            cases A with
            | dataTy tg =>
              simp only [semPiData, Mem] at h1 h2
              obtain ⟨g, hg, hall⟩ := h1
              obtain ⟨d, hd, hcar⟩ := h2
              rw [hg, hd]
              simp only [applyVal]
              exact hall d ⟨d, rfl, hcar⟩
            | junk => simp only [semPiData, Mem] at h1
            | prop P => simp only [semPiData, Mem] at h1
            | sort l => simp only [semPiData, Mem] at h1
            | elem d => simp only [semPiData, Mem] at h1
            | fn g => simp only [semPiData, Mem] at h1
            | piTy A' B' => simp only [semPiData, Mem] at h1
        · cases h
      · cases h
    | lam t b =>
      simp only [inferType, bind_ok_iff] at h
      obtain ⟨st, hst, sA, hsA, tb, htb, stb, hstb, sB, hsB, h⟩ := h
      split at h
      · rename_i hcond
        cases h
        simp only [evalIn]
        have hbody : ∀ v, Mem v (evalIn M ρ t) →
            Mem (evalIn M (Valuation.cons v ρ) b) (evalIn M (Valuation.cons v ρ) tb) :=
          fun v hv => ih (t :: ctx) b tb htb _ (ctxOK_cons hρ hv)
        by_cases hp : ∀ v, Mem v (evalIn M ρ t) →
            ∃ P, evalIn M (Valuation.cons v ρ) tb = .prop P
        · rw [semPi_of_prop hp]
          simp only [Mem]
          intro v hv
          obtain ⟨P, hP⟩ := hp v hv
          have h3 := hbody v hv
          rw [hP] at h3 ⊢
          exact h3
        · have hA : ∃ tg, evalIn M ρ t = .dataTy tg := by
            rcases hcond with hz | ho
            · exfalso
              apply hp
              intro v hv
              have h3 := ih (t :: ctx) tb stb hstb _ (ctxOK_cons hρ hv)
              rw [asSort_sound hs hsB, hz] at h3
              exact h3
            · have h3 := ih ctx t st hst ρ hρ
              rw [asSort_sound hs hsA, ho] at h3
              exact h3
          obtain ⟨tg, hAeq⟩ := hA
          rw [semPi_of_not_prop hp]
          rw [hAeq] at hbody ⊢
          simp only [semPiData, Mem]
          exact ⟨_, rfl, fun d hd => hbody (.elem d) hd⟩
      · cases h
    | pi t b =>
      simp only [inferType, bind_ok_iff] at h
      obtain ⟨st, hst, sA, hsA, sb, hsb, sB, hsB, h⟩ := h
      simp only [evalIn]
      split at h
      · rename_i hz
        cases h
        have hp : ∀ v, Mem v (evalIn M ρ t) →
            ∃ P, evalIn M (Valuation.cons v ρ) b = .prop P := by
          intro v hv
          have h3 := ih (t :: ctx) b sb hsb _ (ctxOK_cons hρ hv)
          rw [asSort_sound hs hsB, hz] at h3
          exact h3
        rw [semPi_of_prop hp]
        exact ⟨_, rfl⟩
      · split at h
        · rename_i ho
          cases h
          by_cases hp : ∀ v, Mem v (evalIn M ρ t) →
              ∃ P, evalIn M (Valuation.cons v ρ) b = .prop P
          · rw [semPi_of_prop hp]
            simp [evalIn, Mem, sortMem, SemVal.isTypeVal]
          · have h3 := ih ctx t st hst ρ hρ
            rw [asSort_sound hs hsA, ho] at h3
            obtain ⟨tg, hAeq⟩ := mem_dataTy_of_sort_one h3
            rw [semPi_of_not_prop hp, hAeq]
            simp [evalIn, semPiData, Mem, sortMem, SemVal.isTypeVal]
        · cases h
    | natLit n =>
      simp only [inferType] at h
      split at h
      · rename_i hc
        cases h
        simp only [evalIn, hs.natTy hc, Mem]
        exact ⟨_, rfl, trivial⟩
      · cases h
    | strLit s =>
      simp only [inferType] at h
      split at h
      · rename_i hc
        cases h
        simp only [evalIn, hs.strTy hc, Mem]
        exact ⟨_, rfl, trivial⟩
      · cases h
    | proj s i e => simp [inferType] at h

/-- Soundness of the kernel's three judgments against the model, at every fuel. -/
theorem kernel_sound_at_fuel {env : KernelEnv} {M : Model} (hs : EnvSound env M) (fuel : Nat) :
    (∀ e ρ, evalIn M ρ (whnf env fuel e) = evalIn M ρ e) ∧
    (∀ a b, isDefEq env fuel a b = true → ∀ ρ, evalIn M ρ a = evalIn M ρ b) ∧
    (∀ ctx e T, inferType env fuel ctx e = .ok T →
      ∀ ρ, CtxOK M ctx ρ → Mem (evalIn M ρ e) (evalIn M ρ T)) :=
  ⟨whnf_sound hs fuel, isDefEq_sound hs fuel, inferType_sound hs fuel⟩

/-- In a sound environment, a constant whose type denotes a proposition makes it true. -/
theorem kernelEnv_prop_types_true {env : KernelEnv} {M : Model} (hs : EnvSound env M)
    {n : SymName} {ci : ConstantRecord} (h : env.lookup n = some ci) (P : Prop)
    (hP : evalExpr M [] ci.type = .prop P) : P := by
  have hm := hs.typed n ci h (Valuation.ofList [])
  unfold evalExpr at hP
  rw [hP] at hm
  exact hm

/-- No constant of a sound environment has type `False`. -/
theorem kernelEnv_no_false {env : KernelEnv} {M : Model} (hs : EnvSound env M)
    {n : SymName} {ci : ConstantRecord} (h : env.lookup n = some ci) :
    ci.type ≠ .const SymName.falseName := by
  intro hty
  have hin : env.contains SymName.falseName = true :=
    hs.inScope n ci h SymName.falseName (by
      simp [ConstantRecord.exprConstants, ConstantRecord.exprs, hty,
        ExprSkeleton.usedConstants])
  have hm := hs.typed n ci h (Valuation.ofList [])
  rw [hty] at hm
  simp only [evalIn, hs.falseTy hin, Mem] at hm

/-! ## Declaration checking

`kernelCheckDecl` admits one declaration into an environment. Definitions, theorems, and
opaque constants must have a value whose inferred type is definitionally the declared
type. Inductive types are enumerations: a data type whose constructors are constants of
that type, with the `Prop`-eliminating recursor of exactly the canonical shape. Quotient
declarations are never admitted: the four `Quot` constants belong to the pinned base
environment, and Lean 4.34.1 replay does not compare a stored quotient record with them.
Axioms are admitted only when the caller's policy allows that one declaration. -/

theorem contains_cons (k : SymName) (c : ConstantRecord) (env : KernelEnv) (n : SymName) :
    KernelEnv.contains ((k, c) :: env) n = (decide (k = n) || env.contains n) := by
  simp only [KernelEnv.contains, KernelEnv.lookup]
  split <;> simp_all

/-- `motive c₁ → … → motive cₙ → ∀ t : T, motive t` below `k` minor premises. -/
def canonicalRecMinors (T : SymName) : Nat → List SymName → ExprSkeleton
  | k, [] => .pi (.const T) (.app (.bvar (k + 1)) (.bvar 0))
  | k, c :: cs => .pi (.app (.bvar k) (.const c)) (canonicalRecMinors T (k + 1) cs)

/-- `∀ motive : T → Prop, motive c₁ → … → motive cₙ → ∀ t : T, motive t`. -/
def canonicalRecType (T : SymName) (ctors : List SymName) : ExprSkeleton :=
  .pi (.pi (.const T) (.sort 0)) (canonicalRecMinors T 0 ctors)

def canonicalRecRuleLams (body : ExprSkeleton) : Nat → List SymName → ExprSkeleton
  | _, [] => body
  | k, c :: cs => .lam (.app (.bvar k) (.const c)) (canonicalRecRuleLams body (k + 1) cs)

/-- Rule `i` returns the `i`-th minor premise: `fun motive m₁ … mₙ => mᵢ`. -/
def canonicalRecRules (T : SymName) (ctors : List SymName) : List RecRule :=
  ((List.range ctors.length).zip ctors).map fun p =>
    { ctor := p.2, nfields := 0,
      rhs := .lam (.pi (.const T) (.sort 0))
        (canonicalRecRuleLams (.bvar (ctors.length - 1 - p.1)) 0 ctors) }

/-- The constructor list of `T` when `T` is an enumeration data type of the environment. -/
def enumInductive? (env : KernelEnv) (T : SymName) : Option (List SymName) :=
  match env.lookup T with
  | some ic =>
    match ic.kind with
    | .inductDecl ctors =>
      if ic.type = .sort 1 ∧ T.isBuiltinName = false then some ctors else none
    | _ => none
  | none => none

theorem enumInductive?_spec {env : KernelEnv} {T : SymName} {ctors : List SymName}
    (h : enumInductive? env T = some ctors) :
    ∃ ic, env.lookup T = some ic ∧ ic.kind = .inductDecl ctors ∧ ic.type = .sort 1 ∧
      T.isBuiltinName = false := by
  unfold enumInductive? at h
  split at h
  · rename_i ic hic
    split at h
    · rename_i ctors' hk
      split at h
      · rename_i hc
        cases h
        exact ⟨ic, hic, hk, hc.1, hc.2⟩
      · cases h
    · cases h
  · cases h

def isEnumCtorOf (env : KernelEnv) (T c : SymName) : Bool :=
  match env.lookup c with
  | some cc => decide (cc.kind = .ctorDecl T ∧ cc.type = .const T)
  | none => false

theorem isEnumCtorOf_spec {env : KernelEnv} {T c : SymName} (h : isEnumCtorOf env T c = true) :
    ∃ cc, env.lookup c = some cc ∧ cc.kind = .ctorDecl T ∧ cc.type = .const T := by
  unfold isEnumCtorOf at h
  split at h
  · rename_i cc hcc
    simp only [decide_eq_true_eq] at h
    exact ⟨cc, hcc, h.1, h.2⟩
  · cases h

/-- A recursor is admitted only for an enumeration whose constructors are all present,
with exactly the canonical type and rules. -/
def isCanonicalRecDecl (env : KernelEnv) (ci : ConstantRecord) (rules : List RecRule) : Bool :=
  match ci.all with
  | [T] =>
    match enumInductive? env T with
    | some ctors =>
      ctors.all (isEnumCtorOf env T) && decide (ci.type = canonicalRecType T ctors) &&
        decide (rules = canonicalRecRules T ctors) && decide (ci.value? = none)
    | none => false
  | _ => false

theorem isCanonicalRecDecl_spec {env : KernelEnv} {ci : ConstantRecord} {rules : List RecRule}
    (h : isCanonicalRecDecl env ci rules = true) :
    ∃ T ctors, enumInductive? env T = some ctors ∧
      (∀ c ∈ ctors, isEnumCtorOf env T c = true) ∧ ci.type = canonicalRecType T ctors := by
  unfold isCanonicalRecDecl at h
  split at h
  · rename_i T _
    split at h
    · rename_i ctors hctors
      simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
      exact ⟨T, ctors, hctors, h.1.1.1, h.1.1.2⟩
    · cases h
  · cases h

/-- Fuel for checking one declaration: proportional to its size and the environment's. -/
def kernelFuel (env : KernelEnv) (ci : ConstantRecord) : Nat :=
  64 + 4 * (ci.exprs.map ExprSkeleton.size).sum + 2 * env.length

def kernelInfer (env : KernelEnv) (ci : ConstantRecord) (e : ExprSkeleton) :
    Except AuditFailure ExprSkeleton :=
  match inferType env (kernelFuel env ci) [] e with
  | .ok t => .ok t
  | .error msg => .error (.kernelTypeError ci.name msg)

def kernelSortOf (env : KernelEnv) (ci : ConstantRecord) (e : ExprSkeleton) :
    Except AuditFailure Nat :=
  match kernelInfer env ci e with
  | .error err => .error err
  | .ok t =>
    match asSort env (kernelFuel env ci) t with
    | .ok l => .ok l
    | .error msg => .error (.kernelTypeError ci.name msg)

/-- The stored value exists and its inferred type converts to the declared type. -/
def checkDeclValue (env : KernelEnv) (ci : ConstantRecord) (missing mismatch : String) :
    Except AuditFailure Unit :=
  match ci.value? with
  | none => .error (.kernelTypeError ci.name missing)
  | some v =>
    match kernelInfer env ci v with
    | .error err => .error err
    | .ok tv =>
      ensure (isDefEq env (kernelFuel env ci) tv ci.type = true)
        (.kernelTypeError ci.name mismatch)

def kernelCheckKind (env : KernelEnv) (allowAxiom : Bool) (ci : ConstantRecord) :
    Except AuditFailure Unit :=
  match ci.kind with
  | .axiomDecl => do
    ensure (allowAxiom = true) (.forbiddenAxiom ci.name ci.name .anonymous)
    ensure (ci.value? = none) (.kernelTypeError ci.name "axiom with a value")
    match kernelSortOf env ci ci.type with
    | .ok _ => .ok ()
    | .error err => .error err
  | .defnDecl => do
    let _ ← kernelSortOf env ci ci.type
    checkDeclValue env ci "definition without a value" "definition value type mismatch"
  | .opaqueDecl => do
    let _ ← kernelSortOf env ci ci.type
    checkDeclValue env ci "opaque without a value" "opaque value type mismatch"
  | .thmDecl =>
    match kernelSortOf env ci ci.type with
    | .error err => .error err
    | .ok l => do
      ensure (l = 0) (.kernelTypeError ci.name "theorem statement is not a proposition")
      checkDeclValue env ci "theorem without a proof" "theorem proof term type mismatch"
  | .quotDecl => .error (.kernelTypeError ci.name "non-canonical quotient declaration")
  | .inductDecl _ => do
    ensure (ci.type = .sort 1)
      (.kernelTypeError ci.name "only enumeration data types are modeled")
    ensure (ci.value? = none) (.kernelTypeError ci.name "inductive type with a value")
  | .ctorDecl T => do
    ensure (ci.value? = none) (.kernelTypeError ci.name "constructor with a value")
    ensure (ci.type = .const T)
      (.kernelTypeError ci.name "only constant constructors are modeled")
    match enumInductive? env T with
    | some ctors =>
      ensure (ci.name ∈ ctors)
        (.kernelTypeError ci.name "constructor is not listed by its inductive")
    | none =>
      .error (.kernelTypeError ci.name "constructor of an unknown or unsupported inductive")
  | .recDecl rules =>
    ensure (isCanonicalRecDecl env ci rules = true)
      (.kernelTypeError ci.name "non-canonical recursor")

/-- Check one declaration and add it under its own name. The name must be fresh, the
stored expressions closed, and every constant they mention already present. -/
def kernelCheckDecl (env : KernelEnv) (allowAxiom : Bool) (ci : ConstantRecord) :
    Except AuditFailure KernelEnv := do
  ensure (ci.name.isAnonymous = false) (.anonymousConstantName ci.name)
  ensure (env.contains ci.name = false)
    (.kernelTypeError ci.name "declaration already present in the replay environment")
  ensure (ci.name.isBuiltinName = false)
    (.kernelTypeError ci.name "builtin name is reserved for the base environment")
  ensure (ci.safety = .safe)
    (.kernelTypeError ci.name "unsafe or partial declaration cannot be replayed")
  ensure (ci.isClosed = true)
    (.kernelTypeError ci.name "open expression in stored declaration")
  checkAll ci.exprConstants (fun d => ensure (env.contains d = true) (.unknownConstant d))
  kernelCheckKind env allowAxiom ci
  .ok ((ci.name, ci) :: env)

theorem kernelCheckDecl_ok {env env' : KernelEnv} {allowAxiom : Bool} {ci : ConstantRecord}
    (h : kernelCheckDecl env allowAxiom ci = .ok env') :
    env' = (ci.name, ci) :: env ∧ env.contains ci.name = false ∧
      ci.name.isBuiltinName = false ∧ ci.isClosed = true ∧
      (∀ d ∈ ci.exprConstants, env.contains d = true) ∧
      kernelCheckKind env allowAxiom ci = .ok () := by
  simp only [kernelCheckDecl, bindUnit_ok_iff, ensure_ok_iff, checkAll_ok_iff,
    Except.ok.injEq] at h
  exact ⟨h.2.2.2.2.2.2.2.symm, h.2.1, h.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1⟩

theorem kernelCheckDecl_lookup {env env' : KernelEnv} {allowAxiom : Bool} {ci : ConstantRecord}
    (h : kernelCheckDecl env allowAxiom ci = .ok env') :
    env'.lookup ci.name = some ci ∧ ∀ n x, env.lookup n = some x → env'.lookup n = some x := by
  obtain ⟨rfl, hfresh, _⟩ := kernelCheckDecl_ok h
  refine ⟨by simp [KernelEnv.lookup], fun n x hx => ?_⟩
  simp only [KernelEnv.lookup]
  split
  · rename_i heq
    subst heq
    simp [KernelEnv.contains, hx] at hfresh
  · exact hx

theorem type_mem_exprs (ci : ConstantRecord) : ci.type ∈ ci.exprs := by
  simp [ConstantRecord.exprs]

theorem value_mem_exprs {ci : ConstantRecord} {v : ExprSkeleton} (h : ci.value? = some v) :
    v ∈ ci.exprs := by
  simp [ConstantRecord.exprs, h]

theorem closed_of_mem_exprs {ci : ConstantRecord} (hc : ci.isClosed = true) {e : ExprSkeleton}
    (he : e ∈ ci.exprs) : e.closedBelow 0 = true := by
  simp only [ConstantRecord.isClosed, List.all_eq_true] at hc
  exact hc e he

theorem consts_mem_exprConstants {ci : ConstantRecord} {e : ExprSkeleton} (he : e ∈ ci.exprs)
    {d : SymName} (hd : d ∈ e.usedConstants) : d ∈ ci.exprConstants :=
  List.mem_flatMap.mpr ⟨e, he, hd⟩

/-- Extending a sound environment with a fresh, scoped declaration and a value for it. -/
theorem envSound_extend {env : KernelEnv} {M : Model} {ci : ConstantRecord}
    (hs : EnvSound env M) (x : SemVal)
    (hfresh : env.contains ci.name = false) (hbuiltin : ci.name.isBuiltinName = false)
    (hscoped : ∀ d ∈ ci.exprConstants, env.contains d = true)
    (htyped : ∀ ρ, Mem x (evalIn M ρ ci.type))
    (hdefn : ci.kind = .defnDecl → ∀ v, ci.value? = some v → ∀ ρ, evalIn M ρ v = x)
    (henum : ∀ ctors, ci.kind = .inductDecl ctors → ci.type = .sort 1 →
      x = .dataTy (.enum ci.name ctors))
    (hctor : ∀ T, ci.kind = .ctorDecl T → ci.type = .const T → T.isBuiltinName = false →
      x = .elem (.enum T ci.name)) :
    EnvSound ((ci.name, ci) :: env) (fun c => if c = ci.name then x else M c) := by
  have hne : ∀ d, env.contains d = true → d ≠ ci.name := by
    intro d hd he
    rw [he, hfresh] at hd
    cases hd
  have hagree : ∀ (e : ExprSkeleton) (ρ : Valuation),
      (∀ d ∈ e.usedConstants, env.contains d = true) →
      evalIn (fun c => if c = ci.name then x else M c) ρ e = evalIn M ρ e := by
    intro e ρ he
    exact evalIn_model_congr e ρ (fun c hc => by simp [hne c (he c hc)])
  have hlk : ∀ c ci', KernelEnv.lookup ((ci.name, ci) :: env) c = some ci' →
      (c = ci.name ∧ ci' = ci) ∨ (c ≠ ci.name ∧ env.lookup c = some ci') := by
    intro c ci' h
    simp only [KernelEnv.lookup] at h
    split at h
    · rename_i heq
      cases h
      exact Or.inl ⟨heq.symm, rfl⟩
    · rename_i hneq
      exact Or.inr ⟨fun h' => hneq h'.symm, h⟩
  have hold : ∀ c ci', env.lookup c = some ci' → ∀ e ∈ ci'.exprs, ∀ ρ,
      evalIn (fun c => if c = ci.name then x else M c) ρ e = evalIn M ρ e :=
    fun c ci' hl e he ρ =>
      hagree e ρ (fun d hd => hs.inScope c ci' hl d (consts_mem_exprConstants he hd))
  have hnew : ∀ e ∈ ci.exprs, ∀ ρ,
      evalIn (fun c => if c = ci.name then x else M c) ρ e = evalIn M ρ e :=
    fun e he ρ => hagree e ρ (fun d hd => hscoped d (consts_mem_exprConstants he hd))
  have hin : ∀ d, env.contains d = true → KernelEnv.contains ((ci.name, ci) :: env) d = true := by
    intro d hd
    rw [contains_cons, hd, Bool.or_true]
  have hbase : ∀ n : SymName, n.isBuiltinName = true →
      KernelEnv.contains ((ci.name, ci) :: env) n = true →
      env.contains n = true ∧ (if n = ci.name then x else M n) = M n := by
    intro n hn hc
    have hneq : n ≠ ci.name := by
      intro he
      rw [he, hbuiltin] at hn
      cases hn
    rw [contains_cons] at hc
    simp only [Bool.or_eq_true, decide_eq_true_eq] at hc
    rcases hc with hc | hc
    · exact absurd hc.symm hneq
    · exact ⟨hc, by simp [hneq]⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c ci' h ρ
    rcases hlk c ci' h with ⟨rfl, rfl⟩ | ⟨hc, hl⟩
    · simp only [↓reduceIte]
      rw [hnew _ (type_mem_exprs _)]
      exact htyped ρ
    · simp only [hc, ↓reduceIte]
      rw [hold c ci' hl _ (type_mem_exprs _)]
      exact hs.typed c ci' hl ρ
  · intro c ci' v h hk hv ρ
    rcases hlk c ci' h with ⟨rfl, rfl⟩ | ⟨hc, hl⟩
    · simp only [↓reduceIte]
      rw [hnew _ (value_mem_exprs hv)]
      exact hdefn hk v hv ρ
    · simp only [hc, ↓reduceIte]
      rw [hold c ci' hl _ (value_mem_exprs hv)]
      exact hs.defn c ci' v hl hk hv ρ
  · intro hc
    obtain ⟨hc', heq⟩ := hbase SymName.natName (by decide) hc
    rw [heq]
    exact hs.natTy hc'
  · intro hc
    obtain ⟨hc', heq⟩ := hbase SymName.stringName (by decide) hc
    rw [heq]
    exact hs.strTy hc'
  · intro hc
    obtain ⟨hc', heq⟩ := hbase SymName.falseName (by decide) hc
    rw [heq]
    exact hs.falseTy hc'
  · intro c ci' ctors h hk ht hb
    rcases hlk c ci' h with ⟨rfl, rfl⟩ | ⟨hc, hl⟩
    · simp only [↓reduceIte]
      exact henum ctors hk ht
    · simp only [hc, ↓reduceIte]
      exact hs.enumTy c ci' ctors hl hk ht hb
  · intro c ci' T h hk ht hb
    rcases hlk c ci' h with ⟨rfl, rfl⟩ | ⟨hc, hl⟩
    · simp only [↓reduceIte]
      exact hctor T hk ht hb
    · simp only [hc, ↓reduceIte]
      exact hs.enumCtor c ci' T hl hk ht hb
  · intro c ci' h d hd
    rcases hlk c ci' h with ⟨rfl, rfl⟩ | ⟨_, hl⟩
    · exact hin d (hscoped d hd)
    · exact hin d (hs.inScope c ci' hl d hd)

theorem carrier_enum {T : SymName} {ctors : List SymName} {d : Dom}
    (h : (DataTag.enum T ctors).carrier d) : ∃ c, d = .enum T c ∧ c ∈ ctors := by
  cases d with
  | nat n => simp [DataTag.carrier] at h
  | str s => simp [DataTag.carrier] at h
  | enum ty c =>
    simp only [DataTag.carrier] at h
    exact ⟨c, by rw [h.1], h.2⟩

theorem mem_enum {T : SymName} {ctors : List SymName} {c : SymName} (hc : c ∈ ctors) :
    Mem (.elem (.enum T c)) (.dataTy (.enum T ctors)) := by
  simp only [Mem]
  exact ⟨_, rfl, rfl, hc⟩

/-- The minor premises and conclusion of the canonical recursor hold once the motive
holds at every constructor not still awaited. -/
theorem recMinors_holds {M : Model} {T : SymName} {ctors : List SymName}
    (hT : M T = .dataTy (.enum T ctors)) (hctors : ∀ c ∈ ctors, M c = .elem (.enum T c))
    (m : SemVal) :
    ∀ (cs : List SymName) (k : Nat) (ρ : Valuation), ρ k = m → (∀ c ∈ cs, c ∈ ctors) →
      (∀ c ∈ ctors, c ∉ cs → (applyVal m (.elem (.enum T c))).holds) →
      (∀ c ∈ cs, ∃ P, applyVal m (.elem (.enum T c)) = .prop P) →
      ∃ P, evalIn M ρ (canonicalRecMinors T k cs) = .prop P ∧ P := by
  intro cs
  induction cs with
  | nil =>
    intro k ρ hk _ hdone _
    simp only [canonicalRecMinors, evalIn, hT, Valuation.cons, hk]
    have hfact : ∀ v, Mem v (.dataTy (.enum T ctors)) → (applyVal m v).holds := by
      intro v hv
      simp only [Mem] at hv
      obtain ⟨d, rfl, hd⟩ := hv
      obtain ⟨c, rfl, hc⟩ := carrier_enum hd
      exact hdone c hc (by simp)
    have hp : ∀ v, Mem v (.dataTy (.enum T ctors)) → ∃ P, applyVal m v = .prop P := by
      intro v hv
      have h1 := hfact v hv
      cases happ : applyVal m v with
      | prop P => exact ⟨P, rfl⟩
      | _ => simp [SemVal.holds, happ] at h1
    rw [semPi_of_prop hp]
    exact ⟨_, rfl, hfact⟩
  | cons c cs ih =>
    intro k ρ hk hsub hdone hprop
    simp only [canonicalRecMinors, evalIn]
    rw [hk, hctors c (hsub c List.mem_cons_self)]
    obtain ⟨Pc, hPc⟩ := hprop c List.mem_cons_self
    rw [hPc]
    have hstep : ∀ v, Mem v (.prop Pc) →
        ∃ P, evalIn M (Valuation.cons v ρ) (canonicalRecMinors T (k + 1) cs) = .prop P ∧ P := by
      intro v hv
      refine ih (k + 1) (Valuation.cons v ρ) hk
        (fun c' hc' => hsub c' (List.mem_cons_of_mem _ hc')) ?_
        (fun c' hc' => hprop c' (List.mem_cons_of_mem _ hc'))
      intro c' hc' hnot
      by_cases hcc : c' = c
      · subst hcc
        rw [hPc]
        exact hv
      · exact hdone c' hc' (by simp [hcc, hnot])
    rw [semPi_of_prop (fun v hv => (hstep v hv).imp (fun _ h => h.1))]
    refine ⟨_, rfl, fun v hv => ?_⟩
    obtain ⟨P, hP, hPt⟩ := hstep v hv
    rw [hP]
    exact hPt

theorem mem_predTy {T : SymName} {ctors : List SymName} {m : SemVal}
    (hm : Mem m (semPi (.dataTy (.enum T ctors)) (fun _ => .sort 0))) :
    ∀ c ∈ ctors, ∃ P, applyVal m (.elem (.enum T c)) = .prop P := by
  intro c hc
  have hnp : ¬ ∀ v, Mem v (.dataTy (.enum T ctors)) →
      ∃ P, (fun _ : SemVal => SemVal.sort 0) v = .prop P := by
    intro hp
    obtain ⟨P, hP⟩ := hp _ (mem_enum hc)
    cases hP
  rw [semPi_of_not_prop hnp] at hm
  simp only [semPiData, Mem] at hm
  obtain ⟨g, rfl, hg⟩ := hm
  have h1 := hg (.enum T c) ⟨_, rfl, rfl, hc⟩
  simpa [applyVal, sortMem] using h1

/-- The canonical recursor type of an enumeration is a true proposition. -/
theorem canonicalRecType_holds {M : Model} {T : SymName} {ctors : List SymName}
    (hT : M T = .dataTy (.enum T ctors)) (hctors : ∀ c ∈ ctors, M c = .elem (.enum T c))
    (ρ : Valuation) : ∃ P, evalIn M ρ (canonicalRecType T ctors) = .prop P ∧ P := by
  simp only [canonicalRecType, evalIn, hT]
  have hstep : ∀ m, Mem m (semPi (.dataTy (.enum T ctors)) (fun _ => .sort 0)) →
      ∃ P, evalIn M (Valuation.cons m ρ) (canonicalRecMinors T 0 ctors) = .prop P ∧ P := by
    intro m hm
    exact recMinors_holds hT hctors m ctors 0 (Valuation.cons m ρ) rfl (fun _ h => h)
      (fun c hc hn => absurd hc hn) (mem_predTy hm)
  rw [semPi_of_prop (fun m hm => (hstep m hm).imp (fun _ h => h.1))]
  refine ⟨_, rfl, fun m hm => ?_⟩
  obtain ⟨P, hP, hPt⟩ := hstep m hm
  rw [hP]
  exact hPt

theorem checkDeclValue_sound {env : KernelEnv} {M : Model} {ci : ConstantRecord}
    {m1 m2 : String} (hs : EnvSound env M) (h : checkDeclValue env ci m1 m2 = .ok ()) :
    ∃ v, ci.value? = some v ∧ ∀ ρ, Mem (evalIn M ρ v) (evalIn M ρ ci.type) := by
  unfold checkDeclValue at h
  split at h
  · cases h
  · rename_i v hv
    split at h
    · cases h
    · rename_i tv htv
      refine ⟨v, hv, fun ρ => ?_⟩
      unfold kernelInfer at htv
      split at htv
      · rename_i t ht
        cases htv
        have h1 := inferType_sound hs _ [] v _ ht ρ (ctxOK_nil M ρ)
        rw [isDefEq_sound hs _ _ _ (ensure_ok_iff.mp h) ρ] at h1
        exact h1
      · cases htv

/-- What a successful kind check provides: a value for the new constant that inhabits its
type and satisfies the kind-specific clauses of `EnvSound`. -/
theorem kernelCheckKind_model {env : KernelEnv} {M : Model} {ci : ConstantRecord}
    (hs : EnvSound env M) (hclosed : ci.isClosed = true)
    (h : kernelCheckKind env false ci = .ok ()) :
    ∃ x : SemVal, (∀ ρ, Mem x (evalIn M ρ ci.type)) ∧
      (ci.kind = .defnDecl → ∀ v, ci.value? = some v → ∀ ρ, evalIn M ρ v = x) ∧
      (∀ ctors, ci.kind = .inductDecl ctors → ci.type = .sort 1 →
        x = .dataTy (.enum ci.name ctors)) ∧
      (∀ T, ci.kind = .ctorDecl T → ci.type = .const T → T.isBuiltinName = false →
        x = .elem (.enum T ci.name)) := by
  have hval : ∀ {m1 m2 : String}, checkDeclValue env ci m1 m2 = .ok () →
      ∃ x : SemVal, (∀ ρ, Mem x (evalIn M ρ ci.type)) ∧
        (∀ v, ci.value? = some v → ∀ ρ, evalIn M ρ v = x) := by
    intro m1 m2 hv
    obtain ⟨v, hv1, hv2⟩ := checkDeclValue_sound hs hv
    have hcv := closed_of_mem_exprs hclosed (value_mem_exprs hv1)
    refine ⟨evalIn M (fun _ => .junk) v, fun ρ => ?_, fun v' hv' ρ => ?_⟩
    · rw [evalIn_closed M hcv _ ρ]
      exact hv2 ρ
    · rw [hv1] at hv'
      cases hv'
      exact evalIn_closed M hcv _ _
  unfold kernelCheckKind at h
  split at h
  · simp [bindUnit_ok_iff, ensure_ok_iff] at h
  · rename_i hk
    simp only [bind_ok_iff] at h
    obtain ⟨_, _, hvalOk⟩ := h
    obtain ⟨x, hx1, hx2⟩ := hval hvalOk
    exact ⟨x, hx1, fun _ => hx2, fun ctors hk' => (by rw [hk] at hk'; cases hk'),
      fun T hk' => (by rw [hk] at hk'; cases hk')⟩
  · rename_i hk
    simp only [bind_ok_iff] at h
    obtain ⟨_, _, hvalOk⟩ := h
    obtain ⟨x, hx1, _⟩ := hval hvalOk
    exact ⟨x, hx1, fun hk' => (by rw [hk] at hk'; cases hk'),
      fun ctors hk' => (by rw [hk] at hk'; cases hk'), fun T hk' => (by rw [hk] at hk'; cases hk')⟩
  · rename_i hk
    split at h
    · cases h
    · simp only [bindUnit_ok_iff] at h
      obtain ⟨x, hx1, _⟩ := hval h.2
      exact ⟨x, hx1, fun hk' => (by rw [hk] at hk'; cases hk'),
        fun ctors hk' => (by rw [hk] at hk'; cases hk'), fun T hk' => (by rw [hk] at hk'; cases hk')⟩
  · cases h
  · rename_i ctors hk
    simp only [bindUnit_ok_iff, ensure_ok_iff] at h
    refine ⟨.dataTy (.enum ci.name ctors), fun ρ => ?_, fun hk' => (by rw [hk] at hk'; cases hk'),
      fun ctors' hk' _ => (by rw [hk] at hk'; cases hk'; rfl),
      fun T hk' => (by rw [hk] at hk'; cases hk')⟩
    rw [h.1]
    exact ⟨_, rfl⟩
  · rename_i T hk
    simp only [bindUnit_ok_iff, ensure_ok_iff] at h
    obtain ⟨_, hty, h⟩ := h
    split at h
    · rename_i ctors hctors
      obtain ⟨ic, hic, hick, hict, hTb⟩ := enumInductive?_spec hctors
      refine ⟨.elem (.enum T ci.name), fun ρ => ?_, fun hk' => (by rw [hk] at hk'; cases hk'),
        fun ctors' hk' => (by rw [hk] at hk'; cases hk'),
        fun T' hk' _ _ => (by rw [hk] at hk'; cases hk'; rfl)⟩
      rw [hty]
      simp only [evalIn, hs.enumTy T ic ctors hic hick hict hTb]
      exact mem_enum (ensure_ok_iff.mp h)
    · cases h
  · rename_i rules hk
    obtain ⟨T, ctors, hctors, hall, hty⟩ := isCanonicalRecDecl_spec (ensure_ok_iff.mp h)
    obtain ⟨ic, hic, hick, hict, hTb⟩ := enumInductive?_spec hctors
    have hT := hs.enumTy T ic ctors hic hick hict hTb
    have hcs : ∀ c ∈ ctors, M c = .elem (.enum T c) := by
      intro c hc
      obtain ⟨cc, hcc, hcck, hcct⟩ := isEnumCtorOf_spec (hall c hc)
      exact hs.enumCtor c cc T hcc hcck hcct hTb
    refine ⟨.junk, fun ρ => ?_, fun hk' => (by rw [hk] at hk'; cases hk'),
      fun ctors' hk' => (by rw [hk] at hk'; cases hk'), fun T' hk' => (by rw [hk] at hk'; cases hk')⟩
    obtain ⟨P, hP, hPt⟩ := canonicalRecType_holds hT hcs ρ
    rw [hty, hP]
    exact hPt

/-- Checking a declaration with axioms disallowed preserves soundness: the extended
environment has a model that agrees with the old one on the old constants. -/
theorem kernelCheckDecl_preserves_sound {env env' : KernelEnv} {M : Model} {ci : ConstantRecord}
    (hs : EnvSound env M) (h : kernelCheckDecl env false ci = .ok env') :
    ∃ M', EnvSound env' M' ∧ ∀ c, env.contains c = true → M' c = M c := by
  obtain ⟨rfl, hfresh, hbuiltin, hclosed, hscoped, hkind⟩ := kernelCheckDecl_ok h
  obtain ⟨x, hx1, hx2, hx3, hx4⟩ := kernelCheckKind_model hs hclosed hkind
  refine ⟨fun c => if c = ci.name then x else M c,
    envSound_extend hs x hfresh hbuiltin hscoped hx1 hx2 hx3 hx4, fun c hc => ?_⟩
  have hne : c ≠ ci.name := by
    intro he
    rw [he, hfresh] at hc
    cases hc
  simp [hne]

/-! ## Clean-environment replay -/

/-- Replay declarations in the given order on top of `env`. `allow ci` says whether the
policy admits `ci` if it is an axiom. -/
def replayCleanEnv (allow : ConstantRecord → Bool) :
    KernelEnv → List ConstantRecord → Except AuditFailure KernelEnv
  | env, [] => .ok env
  | env, ci :: rest =>
    match kernelCheckDecl env (allow ci) ci with
    | .ok env' => replayCleanEnv allow env' rest
    | .error e => .error e

theorem replayCleanEnv_preserves_sound {allow : ConstantRecord → Bool} :
    ∀ (decls : List ConstantRecord) (env env' : KernelEnv) (M : Model), EnvSound env M →
      (∀ ci ∈ decls, allow ci = false) → replayCleanEnv allow env decls = .ok env' →
      ∃ M', EnvSound env' M' := by
  intro decls
  induction decls with
  | nil =>
    intro env env' M hs _ h
    simp only [replayCleanEnv, Except.ok.injEq] at h
    exact ⟨M, h ▸ hs⟩
  | cons ci rest ih =>
    intro env env' M hs hallow h
    simp only [replayCleanEnv] at h
    split at h
    · rename_i env1 h1
      rw [hallow ci List.mem_cons_self] at h1
      obtain ⟨M1, hs1, _⟩ := kernelCheckDecl_preserves_sound hs h1
      exact ih env1 env' M1 hs1 (fun c hc => hallow c (List.mem_cons_of_mem _ hc)) h
    · cases h

/-- A declaration can be checked once every constant its expressions mention is present. -/
def declDepsReady (env : KernelEnv) (ci : ConstantRecord) : Bool :=
  ci.exprConstants.all (fun d => env.contains d)

/-- One pass over the pending declarations: check the ready ones, defer the rest. -/
def replayReadyPass (allow : ConstantRecord → Bool) :
    KernelEnv → List ConstantRecord → Except AuditFailure (KernelEnv × List ConstantRecord)
  | env, [] => .ok (env, [])
  | env, ci :: rest =>
    if declDepsReady env ci then
      match kernelCheckDecl env (allow ci) ci with
      | .error e => .error e
      | .ok env' => replayReadyPass allow env' rest
    else
      match replayReadyPass allow env rest with
      | .error e => .error e
      | .ok (env', deferred) => .ok (env', ci :: deferred)

/-- Why no pending declaration is ready: a dependency declared nowhere, or a cycle. -/
def diagnoseReplayStuck (env : KernelEnv) (pending : List ConstantRecord) : AuditFailure :=
  match pending.findSome? (fun ci =>
      ci.exprConstants.find? (fun d =>
        !env.contains d && !pending.any (fun p => decide (p.name = d)))) with
  | some d => .unknownConstant d
  | none =>
    match pending with
    | ci :: _ => .cyclicDependency ci.name
    | [] => .cyclicDependency .anonymous

def replayOrderedLoop (allow : ConstantRecord → Bool) :
    Nat → KernelEnv → List ConstantRecord → Except AuditFailure KernelEnv
  | _, env, [] => .ok env
  | 0, env, ci :: rest => .error (diagnoseReplayStuck env (ci :: rest))
  | fuel + 1, env, ci :: rest =>
    match replayReadyPass allow env (ci :: rest) with
    | .error e => .error e
    | .ok (env', deferred) =>
      if deferred.length < (ci :: rest).length then replayOrderedLoop allow fuel env' deferred
      else .error (diagnoseReplayStuck env (ci :: rest))

/-- Dependency-ordered replay: the order of the inventory (a hash-map order in real
artifacts) does not matter, every declaration still passes `kernelCheckDecl`, and a
dependency cycle or a missing dependency is reported instead of looping. -/
def replayCleanEnvOrdered (allow : ConstantRecord → Bool) (env : KernelEnv)
    (decls : List ConstantRecord) : Except AuditFailure KernelEnv :=
  replayOrderedLoop allow decls.length env decls

theorem replayReadyPass_spec {allow : ConstantRecord → Bool} :
    ∀ (pending : List ConstantRecord) (env env' : KernelEnv) (deferred : List ConstantRecord),
      replayReadyPass allow env pending = .ok (env', deferred) →
      (∀ d ∈ deferred, d ∈ pending) ∧
      (∀ n x, env.lookup n = some x → env'.lookup n = some x) ∧
      (∀ ci ∈ pending, ci ∈ deferred ∨ env'.lookup ci.name = some ci) := by
  intro pending
  induction pending with
  | nil =>
    intro env env' deferred h
    simp only [replayReadyPass, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨by simp, fun _ _ hx => hx, by simp⟩
  | cons ci rest ih =>
    intro env env' deferred h
    simp only [replayReadyPass] at h
    split at h
    · split at h
      · cases h
      · rename_i env1 h1
        obtain ⟨hsub, hmono, hall⟩ := ih env1 env' deferred h
        obtain ⟨hself, hmono1⟩ := kernelCheckDecl_lookup h1
        refine ⟨fun d hd => List.mem_cons_of_mem _ (hsub d hd),
          fun n x hx => hmono n x (hmono1 n x hx), fun c hc => ?_⟩
        rcases List.mem_cons.mp hc with rfl | hc'
        · exact Or.inr (hmono _ _ hself)
        · exact hall c hc'
    · split at h
      · cases h
      · rename_i env1 deferred1 h1
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨hsub, hmono, hall⟩ := ih env env1 deferred1 h1
        refine ⟨fun d hd => ?_, hmono, fun c hc => ?_⟩
        · rcases List.mem_cons.mp hd with rfl | hd'
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ (hsub d hd')
        · rcases List.mem_cons.mp hc with rfl | hc'
          · exact Or.inl List.mem_cons_self
          · rcases hall c hc' with hdef | hlk
            · exact Or.inl (List.mem_cons_of_mem _ hdef)
            · exact Or.inr hlk

theorem replayReadyPass_sound {allow : ConstantRecord → Bool} :
    ∀ (pending : List ConstantRecord) (env env' : KernelEnv) (deferred : List ConstantRecord)
      (M : Model), EnvSound env M → (∀ ci ∈ pending, allow ci = false) →
      replayReadyPass allow env pending = .ok (env', deferred) → ∃ M', EnvSound env' M' := by
  intro pending
  induction pending with
  | nil =>
    intro env env' deferred M hs _ h
    simp only [replayReadyPass, Except.ok.injEq, Prod.mk.injEq] at h
    exact ⟨M, h.1 ▸ hs⟩
  | cons ci rest ih =>
    intro env env' deferred M hs hallow h
    simp only [replayReadyPass] at h
    have hrest : ∀ c ∈ rest, allow c = false := fun c hc => hallow c (List.mem_cons_of_mem _ hc)
    split at h
    · split at h
      · cases h
      · rename_i env1 h1
        rw [hallow ci List.mem_cons_self] at h1
        obtain ⟨M1, hs1, _⟩ := kernelCheckDecl_preserves_sound hs h1
        exact ih env1 env' deferred M1 hs1 hrest h
    · split at h
      · cases h
      · rename_i env1 deferred1 h1
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        exact h.1 ▸ ih env env1 deferred1 M hs hrest h1

theorem replayOrderedLoop_spec {allow : ConstantRecord → Bool} :
    ∀ (fuel : Nat) (env env' : KernelEnv) (pending : List ConstantRecord),
      replayOrderedLoop allow fuel env pending = .ok env' →
      (∀ n x, env.lookup n = some x → env'.lookup n = some x) ∧
      (∀ ci ∈ pending, env'.lookup ci.name = some ci) := by
  intro fuel
  induction fuel with
  | zero =>
    intro env env' pending h
    cases pending with
    | nil =>
      simp only [replayOrderedLoop, Except.ok.injEq] at h
      subst h
      exact ⟨fun _ _ hx => hx, by simp⟩
    | cons ci rest => simp [replayOrderedLoop] at h
  | succ fuel ih =>
    intro env env' pending h
    cases pending with
    | nil =>
      simp only [replayOrderedLoop, Except.ok.injEq] at h
      subst h
      exact ⟨fun _ _ hx => hx, by simp⟩
    | cons ci rest =>
      simp only [replayOrderedLoop] at h
      split at h
      · cases h
      · rename_i env1 deferred h1
        split at h
        · obtain ⟨_, hmono1, hall1⟩ := replayReadyPass_spec _ _ _ _ h1
          obtain ⟨hmono, hall⟩ := ih env1 env' deferred h
          refine ⟨fun n x hx => hmono n x (hmono1 n x hx), fun c hc => ?_⟩
          rcases hall1 c hc with hdef | hlk
          · exact hall c hdef
          · exact hmono _ _ hlk
        · cases h

theorem replayOrderedLoop_sound {allow : ConstantRecord → Bool} :
    ∀ (fuel : Nat) (env env' : KernelEnv) (pending : List ConstantRecord) (M : Model),
      EnvSound env M → (∀ ci ∈ pending, allow ci = false) →
      replayOrderedLoop allow fuel env pending = .ok env' → ∃ M', EnvSound env' M' := by
  intro fuel
  induction fuel with
  | zero =>
    intro env env' pending M hs _ h
    cases pending with
    | nil =>
      simp only [replayOrderedLoop, Except.ok.injEq] at h
      exact ⟨M, h ▸ hs⟩
    | cons ci rest => simp [replayOrderedLoop] at h
  | succ fuel ih =>
    intro env env' pending M hs hallow h
    cases pending with
    | nil =>
      simp only [replayOrderedLoop, Except.ok.injEq] at h
      exact ⟨M, h ▸ hs⟩
    | cons ci rest =>
      simp only [replayOrderedLoop] at h
      split at h
      · cases h
      · rename_i env1 deferred h1
        split at h
        · obtain ⟨M1, hs1⟩ := replayReadyPass_sound _ _ _ _ M hs hallow h1
          obtain ⟨hsub, _, _⟩ := replayReadyPass_spec _ _ _ _ h1
          exact ih env1 env' deferred M1 hs1 (fun c hc => hallow c (hsub c hc)) h
        · cases h

/-- Dependency-ordered replay preserves soundness when no axiom is admitted. -/
theorem replayCleanEnvOrdered_preserves_sound {allow : ConstantRecord → Bool} {env env' : KernelEnv}
    {decls : List ConstantRecord} {M : Model} (hs : EnvSound env M)
    (hallow : ∀ ci ∈ decls, allow ci = false)
    (h : replayCleanEnvOrdered allow env decls = .ok env') : ∃ M', EnvSound env' M' :=
  replayOrderedLoop_sound _ _ _ _ M hs hallow h

/-- Every submitted declaration is in the replayed environment under its own name, and
nothing that was in the base environment changed. -/
theorem replayCleanEnvOrdered_contains_decl {allow : ConstantRecord → Bool} {env env' : KernelEnv}
    {decls : List ConstantRecord} (h : replayCleanEnvOrdered allow env decls = .ok env') :
    (∀ ci ∈ decls, env'.lookup ci.name = some ci) ∧
      (∀ n x, env.lookup n = some x → env'.lookup n = some x) :=
  ⟨(replayOrderedLoop_spec _ _ _ _ h).2, (replayOrderedLoop_spec _ _ _ _ h).1⟩

/-! ## The standard base environment

The pinned environment below the audited package, restricted to what the kernel model
can state: `Nat`, `Bool`, `String`, `True`, `False`, equality on `Nat` (`Eq`) and on `Bool`
(`EqBool`, the model's instance of `@Eq Bool`), `Trusted.VerificationResult`, and the
axioms of `Init`. The statements of `propext`, `Classical.choice`, `Quot.sound`, `sorryAx`,
and the native-reduction axioms lie outside the fragment, so each is recorded at the type
`True`: the audit recognizes them by name and declaring module, never by their type. -/

def baseDecl (n : SymName) (k : DeclKind) (t : ExprSkeleton) (origin : SymName) : ConstantRecord :=
  { name := n, kind := k, type := t, originModule := some origin }

open SymName in
def standardBaseDecls : List ConstantRecord := [
  baseDecl natName (.inductDecl [natZeroName, natSuccName]) (.sort 1) initPreludeModuleName,
  baseDecl natZeroName (.ctorDecl natName) (.const natName) initPreludeModuleName,
  baseDecl natSuccName (.ctorDecl natName) (.pi (.const natName) (.const natName))
    initPreludeModuleName,
  baseDecl boolName (.inductDecl [boolFalseName, boolTrueName]) (.sort 1) initPreludeModuleName,
  baseDecl boolFalseName (.ctorDecl boolName) (.const boolName) initPreludeModuleName,
  baseDecl boolTrueName (.ctorDecl boolName) (.const boolName) initPreludeModuleName,
  baseDecl stringName (.inductDecl []) (.sort 1) initPreludeModuleName,
  baseDecl trueName (.inductDecl [trueIntroName]) (.sort 0) initPreludeModuleName,
  baseDecl trueIntroName (.ctorDecl trueName) (.const trueName) initPreludeModuleName,
  baseDecl falseName (.inductDecl []) (.sort 0) initPreludeModuleName,
  baseDecl eqName (.inductDecl [eqReflName])
    (.pi (.const natName) (.pi (.const natName) (.sort 0))) initPreludeModuleName,
  baseDecl eqReflName (.ctorDecl eqName)
    (.pi (.const natName) (.app (.app (.const eqName) (.bvar 0)) (.bvar 0))) initPreludeModuleName,
  baseDecl eqBoolName (.inductDecl [eqBoolReflName])
    (.pi (.const boolName) (.pi (.const boolName) (.sort 0))) initPreludeModuleName,
  baseDecl eqBoolReflName (.ctorDecl eqBoolName)
    (.pi (.const boolName) (.app (.app (.const eqBoolName) (.bvar 0)) (.bvar 0)))
    initPreludeModuleName,
  baseDecl verificationResultName (.inductDecl [verificationResultIntroName])
    (.pi (.const natName) (.sort 0)) trustedCoreModuleName,
  baseDecl verificationResultIntroName (.ctorDecl verificationResultName)
    (.pi (.const natName) (.app (.const verificationResultName) (.bvar 0))) trustedCoreModuleName,
  baseDecl propextName .axiomDecl (.const trueName) initCoreModuleName,
  baseDecl choiceName .axiomDecl (.const trueName) initCoreModuleName,
  baseDecl quotSoundName .axiomDecl (.const trueName) initCoreModuleName,
  baseDecl sorryAxName .axiomDecl (.const trueName) initPreludeModuleName,
  baseDecl ofReduceBoolName .axiomDecl (.const trueName) initCoreModuleName,
  baseDecl ofReduceNatName .axiomDecl (.const trueName) initCoreModuleName,
  baseDecl trustCompilerName .axiomDecl (.const trueName) initCoreModuleName]

def standardBaseEnv : KernelEnv := mkBaseKernelEnv standardBaseDecls

open SymName in
/-- The intended interpretation of the standard base environment. -/
def standardBaseModel : Model := fun c =>
  if c = natName then .dataTy .nat
  else if c = natZeroName then .elem (.nat 0)
  else if c = natSuccName then
    .fn (fun d => match d with
      | .nat n => .elem (.nat (n + 1))
      | _ => .junk)
  else if c = boolName then .dataTy (.enum boolName [boolFalseName, boolTrueName])
  else if c = boolFalseName then .elem (.enum boolName boolFalseName)
  else if c = boolTrueName then .elem (.enum boolName boolTrueName)
  else if c = stringName then .dataTy .str
  else if c = trueName then .prop True
  else if c = trueIntroName then .elem (.enum trueName trueIntroName)
  else if c = falseName then .prop False
  else if c = eqName then .fn (fun a => .fn (fun b => .prop (a = b)))
  else if c = eqBoolName then .fn (fun a => .fn (fun b => .prop (a = b)))
  else if c = verificationResultName then .fn (fun _ => .prop True)
  else .junk

theorem sbm_nat : standardBaseModel SymName.natName = .dataTy .nat := rfl
theorem sbm_zero : standardBaseModel SymName.natZeroName = .elem (.nat 0) := rfl
theorem sbm_succ : standardBaseModel SymName.natSuccName =
    .fn (fun d => match d with
      | .nat n => .elem (.nat (n + 1))
      | _ => .junk) := rfl
theorem sbm_bool : standardBaseModel SymName.boolName =
    .dataTy (.enum SymName.boolName [SymName.boolFalseName, SymName.boolTrueName]) := rfl
theorem sbm_boolFalse : standardBaseModel SymName.boolFalseName =
    .elem (.enum SymName.boolName SymName.boolFalseName) := rfl
theorem sbm_boolTrue : standardBaseModel SymName.boolTrueName =
    .elem (.enum SymName.boolName SymName.boolTrueName) := rfl
theorem sbm_string : standardBaseModel SymName.stringName = .dataTy .str := rfl
theorem sbm_true : standardBaseModel SymName.trueName = .prop True := rfl
theorem sbm_trueIntro : standardBaseModel SymName.trueIntroName =
    .elem (.enum SymName.trueName SymName.trueIntroName) := rfl
theorem sbm_false : standardBaseModel SymName.falseName = .prop False := rfl
theorem sbm_eq : standardBaseModel SymName.eqName =
    .fn (fun a => .fn (fun b => .prop (a = b))) := rfl
theorem sbm_eqBool : standardBaseModel SymName.eqBoolName =
    .fn (fun a => .fn (fun b => .prop (a = b))) := rfl
theorem sbm_verificationResult : standardBaseModel SymName.verificationResultName =
    .fn (fun _ => .prop True) := rfl

theorem forall_lookup_base {P : SymName → ConstantRecord → Prop} {decls : List ConstantRecord}
    (h : ∀ ci ∈ decls, P ci.name ci) :
    ∀ c ci, KernelEnv.lookup (mkBaseKernelEnv decls) c = some ci → P c ci := by
  intro c ci hl
  rw [lookup_mkBaseKernelEnv] at hl
  obtain ⟨hm, hn⟩ := findConstByName_mem hl
  exact hn ▸ h ci hm

/-- A function type over an inhabited data type whose codomain is not a proposition. -/
theorem semPi_dataTy_fn {t : DataTag} {B : SemVal → SemVal} (d : Dom) (hd : t.carrier d)
    (hnp : ∀ P, B (.elem d) ≠ .prop P) :
    semPi (.dataTy t) B = .piTy (.dataTy t) (fun d => B (.elem d)) := by
  have hnot : ¬ ∀ v, Mem v (.dataTy t) → ∃ P, B v = .prop P := by
    intro hp
    obtain ⟨P, hP⟩ := hp (.elem d) ⟨d, rfl, hd⟩
    exact hnp P hP
  rw [semPi_of_not_prop hnot]
  rfl

/-- A universally quantified proposition over a data type that holds pointwise. -/
theorem semPi_dataTy_prop {t : DataTag} {B : SemVal → SemVal}
    (h : ∀ d, t.carrier d → (B (.elem d)).holds) : ∃ Q, semPi (.dataTy t) B = .prop Q ∧ Q := by
  have hfact : ∀ v, Mem v (.dataTy t) → (B v).holds := by
    intro v hv
    simp only [Mem] at hv
    obtain ⟨d, rfl, hd⟩ := hv
    exact h d hd
  have hp : ∀ v, Mem v (.dataTy t) → ∃ P, B v = .prop P := by
    intro v hv
    have h1 := hfact v hv
    cases hB : B v with
    | prop P => exact ⟨P, rfl⟩
    | _ => simp [SemVal.holds, hB] at h1
  rw [semPi_of_prop hp]
  exact ⟨_, rfl, hfact⟩

theorem standardBase_typed : ∀ ci ∈ standardBaseDecls, ∀ ρ,
    Mem (standardBaseModel ci.name) (evalIn standardBaseModel ρ ci.type) := by
  intro ci hci ρ
  simp only [standardBaseDecls, List.mem_cons, List.mem_nil_iff, or_false] at hci
  rcases hci with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, rfl⟩
  · simp only [baseDecl, evalIn, sbm_nat, sbm_zero, Mem]
    exact ⟨_, rfl, trivial⟩
  · simp only [baseDecl, evalIn, sbm_nat, sbm_succ]
    rw [semPi_dataTy_fn (.nat 0) (by simp [DataTag.carrier]) (by intro P h; cases h)]
    simp only [Mem]
    refine ⟨_, rfl, fun d hd => ?_⟩
    obtain ⟨d', hd', hcar⟩ := hd
    cases hd'
    cases d with
    | nat n => exact ⟨_, rfl, trivial⟩
    | str s => exact hcar.elim
    | enum ty c => exact hcar.elim
  · exact ⟨_, rfl⟩
  · simp only [baseDecl, evalIn, sbm_bool, sbm_boolFalse]
    exact mem_enum (by simp)
  · simp only [baseDecl, evalIn, sbm_bool, sbm_boolTrue]
    exact mem_enum (by simp)
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩
  · simp only [baseDecl, evalIn, sbm_true, Mem]
  · exact ⟨_, rfl⟩
  · simp only [baseDecl, evalIn, sbm_nat, sbm_eq]
    have hinner : semPi (.dataTy .nat) (fun _ => SemVal.sort 0) =
        .piTy (.dataTy .nat) (fun _ => .sort 0) :=
      semPi_dataTy_fn (.nat 0) (by simp [DataTag.carrier]) (by intro P h; cases h)
    rw [hinner, semPi_dataTy_fn (.nat 0) (by simp [DataTag.carrier]) (by intro P h; cases h)]
    simp only [Mem]
    exact ⟨_, rfl, fun a _ => ⟨_, rfl, fun b _ => ⟨_, rfl⟩⟩⟩
  · simp only [baseDecl, evalIn, sbm_nat, sbm_eq, Valuation.cons]
    obtain ⟨Q, hQ, hQt⟩ := semPi_dataTy_prop (t := .nat)
      (B := fun v => applyVal (applyVal (.fn (fun a => .fn (fun b => .prop (a = b)))) v) v)
      (fun d _ => by simp [applyVal, SemVal.holds])
    rw [hQ]
    exact hQt
  · simp only [baseDecl, evalIn, sbm_bool, sbm_eqBool]
    have hinner : semPi (.dataTy (.enum SymName.boolName
          [SymName.boolFalseName, SymName.boolTrueName])) (fun _ => SemVal.sort 0) =
        .piTy (.dataTy (.enum SymName.boolName [SymName.boolFalseName, SymName.boolTrueName]))
          (fun _ => .sort 0) :=
      semPi_dataTy_fn (.enum SymName.boolName SymName.boolTrueName)
        (by simp [DataTag.carrier]) (by intro P h; cases h)
    rw [hinner, semPi_dataTy_fn (.enum SymName.boolName SymName.boolTrueName)
      (by simp [DataTag.carrier]) (by intro P h; cases h)]
    simp only [Mem]
    exact ⟨_, rfl, fun a _ => ⟨_, rfl, fun b _ => ⟨_, rfl⟩⟩⟩
  · simp only [baseDecl, evalIn, sbm_bool, sbm_eqBool, Valuation.cons]
    obtain ⟨Q, hQ, hQt⟩ := semPi_dataTy_prop
      (t := .enum SymName.boolName [SymName.boolFalseName, SymName.boolTrueName])
      (B := fun v => applyVal (applyVal (.fn (fun a => .fn (fun b => .prop (a = b)))) v) v)
      (fun d _ => by simp [applyVal, SemVal.holds])
    rw [hQ]
    exact hQt
  · simp only [baseDecl, evalIn, sbm_nat, sbm_verificationResult]
    rw [semPi_dataTy_fn (.nat 0) (by simp [DataTag.carrier]) (by intro P h; cases h)]
    simp only [Mem]
    exact ⟨_, rfl, fun a _ => ⟨_, rfl⟩⟩
  · simp only [baseDecl, evalIn, sbm_nat, sbm_verificationResult, Valuation.cons]
    obtain ⟨Q, hQ, hQt⟩ := semPi_dataTy_prop (t := .nat)
      (B := fun v => applyVal (.fn (fun _ => .prop True)) v)
      (fun d _ => by simp [applyVal, SemVal.holds])
    rw [hQ]
    exact hQt
  all_goals simp only [baseDecl, evalIn, sbm_true, Mem]

/-- Records the model interprets as enumeration types or enumeration constructors. -/
def isEnumIndRecord (ci : ConstantRecord) : Bool :=
  match ci.kind with
  | .inductDecl _ => decide (ci.type = .sort 1) && !ci.name.isBuiltinName
  | _ => false

def isEnumCtorRecord (ci : ConstantRecord) : Bool :=
  match ci.kind with
  | .ctorDecl T => decide (ci.type = .const T) && !T.isBuiltinName
  | _ => false

/-- The standard base environment is sound for its intended model, hence consistent. -/
theorem standardBaseEnv_sound : EnvSound standardBaseEnv standardBaseModel := by
  have hdefn : ∀ ci ∈ standardBaseDecls, ci.kind ≠ .defnDecl := by decide +kernel
  have hscope : ∀ ci ∈ standardBaseDecls, ∀ d ∈ ci.exprConstants,
      standardBaseEnv.contains d = true := by decide +kernel
  have hind : ∀ ci ∈ standardBaseDecls, isEnumIndRecord ci = true →
      ci = baseDecl SymName.boolName (.inductDecl [SymName.boolFalseName, SymName.boolTrueName])
        (.sort 1) SymName.initPreludeModuleName := by decide +kernel
  have hctor : ∀ ci ∈ standardBaseDecls, isEnumCtorRecord ci = true →
      ci.name = SymName.boolFalseName ∨ ci.name = SymName.boolTrueName ∨
        ci.name = SymName.trueIntroName := by decide +kernel
  have hctorT : ∀ ci ∈ standardBaseDecls, ∀ T, ci.kind = .ctorDecl T →
      (ci.name = SymName.boolFalseName ∨ ci.name = SymName.boolTrueName → T = SymName.boolName) ∧
      (ci.name = SymName.trueIntroName → T = SymName.trueName) := by
    intro ci hci T hk
    have hall : ∀ ci ∈ standardBaseDecls,
        (ci.name = SymName.boolFalseName ∨ ci.name = SymName.boolTrueName →
          ci.kind = .ctorDecl SymName.boolName) ∧
        (ci.name = SymName.trueIntroName → ci.kind = .ctorDecl SymName.trueName) := by
      decide +kernel
    refine ⟨fun h => ?_, fun h => ?_⟩
    · have h1 := (hall ci hci).1 h
      rw [hk] at h1
      cases h1
      rfl
    · have h1 := (hall ci hci).2 h
      rw [hk] at h1
      cases h1
      rfl
  refine ⟨forall_lookup_base standardBase_typed, ?_, fun _ => sbm_nat, fun _ => sbm_string,
    fun _ => sbm_false, ?_, ?_, forall_lookup_base hscope⟩
  · intro c ci v hl hk
    rw [standardBaseEnv, lookup_mkBaseKernelEnv] at hl
    exact absurd hk (hdefn ci (findConstByName_mem hl).1)
  · intro c ci ctors hl
    refine forall_lookup_base (P := fun c ci => ∀ ctors, ci.kind = .inductDecl ctors →
      ci.type = .sort 1 → c.isBuiltinName = false →
      standardBaseModel c = .dataTy (.enum c ctors)) ?_ c ci hl ctors
    intro ci hci ctors hk ht hb
    have hrec := hind ci hci (by simp [isEnumIndRecord, hk, ht, hb])
    subst hrec
    simp only [baseDecl, DeclKind.inductDecl.injEq] at hk
    subst hk
    exact sbm_bool
  · intro c ci T hl
    refine forall_lookup_base (P := fun c ci => ∀ T, ci.kind = .ctorDecl T →
      ci.type = .const T → T.isBuiltinName = false →
      standardBaseModel c = .elem (.enum T c)) ?_ c ci hl T
    intro ci hci T hk ht hb
    have hrec := hctor ci hci (by simp [isEnumCtorRecord, hk, ht, hb])
    have hT := hctorT ci hci T hk
    rcases hrec with h | h | h
    · rw [h, hT.1 (Or.inl h)]
      exact sbm_boolFalse
    · rw [h, hT.1 (Or.inr h)]
      exact sbm_boolTrue
    · rw [h, hT.2 h]
      exact sbm_trueIntro

/-! ## Source scanner (defense in depth)

A text-level second line behind syntax-tree inspection and the artifact checks. It strips
comments and literals the way the Lean 4.34.1 lexer delimits them, then looks for
forbidden options and keywords among the remaining tokens. The lexer rules it follows
(`Lean/Parser/Basic.lean`: `whitespace`, `tokenFnAux`, `identFnAux`, `numberFnAux`,
`charLitFnAux`, `strLitFnAux`, `rawStrLitFnAux`, `fieldIdxFn`):

* A line comment (two dashes) or block comment (slash, dash) starts only at a token
  boundary; the documentation-comment openers (slash, dash, then a dash or `!`) consume
  three characters; block comments nest. Only the tokens `<-`, `//`, and `\/` end in the
  first character of a comment opener, and whether one of them is the token there depends
  on the tokens before it (`<<<` then a comment, but `<` `<-` `-`), so a comment opener
  glued to `<`, `//`, or `\/` is an error.
* `'` continues an identifier, belongs to the tokens `]'`, `×'`, `Σ'`, `⊕'`, or opens a
  character literal `'c'` / `'\…'`.
* `r"…"` and `r#"…"#` are raw strings only at a token start: not inside an identifier or
  after a name-literal backtick. After `.` it depends on the parser (`x...r"…"` is raw,
  `(.r"…")` is not), so that is an error.
* A token that starts with a symbol may continue with letters and end without a boundary
  (`#check`, and in an opened core namespace `~m`, `#'`, `/.`, `\math`, `+1]`): letters
  glued to `#` or `~` may not contain `'` or a digit or touch a string, and `#'`, `/.`,
  `+1]'`, a letter glued to `\`, and a doubled backtick are errors.
* Numeric literals (`0x`, `0b`, `0o`, decimal, `_` separators, fractions, exponents) and
  field indices (`x.1`) end a token, so a raw string or character literal may follow.
* `«…»` is an identifier component: delimiters dropped, content kept, and token
  boundaries preserved on both sides unless adjacent to `.`.
* A non-raw string may be interpolated. Text inside `{…}` stays visible to the token
  scan, and anything there that could open another literal or comment is rejected.

Whatever cannot be delimited with certainty is an error, never a pass, and so is input
that ends inside a literal or block comment. The scanner assumes the token table of
`Init`, `Std`, and `Lean` with any of their namespaces opened: commands and attributes
that add tokens or macros, even locally, are rejected by the token scan, and persisted
ones by the extension audit as well. -/

namespace SourceScanner

def inRange (c : Char) (lo hi : Nat) : Bool := decide (lo ≤ c.toNat) && decide (c.toNat ≤ hi)

/-- `Lean.isLetterLike`. -/
def isLetterLike (c : Char) : Bool :=
  decide (0xc0 ≤ c.toNat) &&
  ((inRange c 0x3b1 0x3c9 && decide (c.toNat ≠ 0x3bb)) ||
   (inRange c 0x391 0x3a9 && decide (c.toNat ≠ 0x3a0) && decide (c.toNat ≠ 0x3a3)) ||
   inRange c 0x3ca 0x3fb || inRange c 0x1f00 0x1ffe || inRange c 0x2100 0x214f ||
   inRange c 0x1d49c 0x1d59f ||
   (inRange c 0xc0 0xff && decide (c.toNat ≠ 0xd7) && decide (c.toNat ≠ 0xf7)) ||
   inRange c 0x100 0x17f)

/-- `Lean.isSubScriptAlnum`. -/
def isSubScriptAlnum (c : Char) : Bool :=
  decide (0x1d62 ≤ c.toNat) &&
  (inRange c 0x2080 0x2089 || inRange c 0x2090 0x209c || inRange c 0x1d62 0x1d6a ||
   decide (c.toNat = 0x2c7c))

def isIdFirst (c : Char) : Bool := c.isAlpha || c == '_' || isLetterLike c

def isIdRest (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == '\'' || c == '!' || c == '?' || isLetterLike c ||
    isSubScriptAlnum c

/-- Characters of the tokens the keyword scan looks at. -/
def isTokenChar (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == '.' || c == '\'' || c == '!' || c == '?'

/-- What an identifier character contributes to the visible code: itself when it can be
part of a keyword, `_` otherwise (a non-ASCII letter can never be part of one). -/
def visible (c : Char) : Char := if isTokenChar c then c else '_'

def isHexDigit (c : Char) : Bool :=
  c.isDigit || (decide ('a' ≤ c) && decide (c ≤ 'f')) || (decide ('A' ≤ c) && decide (c ≤ 'F'))

/-- What precedes the current character in code. -/
inductive Prev where
  | other | ident | identDot | dot | tick | escIdent | quoteTok | sym | symIdent
  deriving DecidableEq

inductive Radix where
  | bin
  | oct
  | hex
  deriving DecidableEq

def Radix.isDigit : Radix → Char → Bool
  | .bin, c => c == '0' || c == '1'
  | .oct, c => decide ('0' ≤ c) && decide (c ≤ '7')
  | .hex, c => isHexDigit c

/-- What precedes the current character inside a string interpolation hole. -/
inductive HolePrev where
  | other | ident | num | quoteTok
  deriving DecidableEq

inductive ScanState where
  | code (prev : Prev)
  | dash | slash | slashAmb | lt | ltDash | bslash | dotR | lineComment
  | blockStart (depth : Nat) | block (depth : Nat) | blockDash (depth : Nat)
  | blockSlash (depth : Nat)
  | str | strEsc
  | hole (depth : Nat) (prev : HolePrev) | holeDash (depth : Nat) | holeSlash (depth : Nat)
  | chrOpen | chrEsc | chrEscN (remaining : Nat) | chrEnd
  | rawR | rawHash (hashes : Nat) | raw (hashes : Nat) | rawEnd (hashes seen : Nat)
  | guillemet
  | numZero | numRadix (r : Radix) | numDec | numDot | numFrac | numExpStart | numExpSign
  | numExp | fieldIdx
  deriving DecidableEq

/-- One lexer step: the next state and the characters it makes visible. -/
abbrev StepResult := Except String (ScanState × List Char)

/-- A character at a position where a token may start or an identifier may continue. -/
def stepCode (prev : Prev) (c : Char) : StepResult :=
  let sep : List Char := if prev = .escIdent then [' '] else []
  if prev = .ident && isIdRest c then .ok (.code .ident, [visible c])
  else if prev = .symIdent ∧ (isIdRest c ∨ c = '"' ∨ c = '#') then
    if c = '\'' ∨ c = '"' ∨ c = '#' ∨ c.isDigit then .error "literal glued to a symbol keyword"
    else .ok (.code .symIdent, [visible c])
  else if prev = .sym ∧ c = '\'' then .error "quote glued to a symbol that may absorb it"
  else if isIdFirst c then
    if prev = .sym then .ok (.code .symIdent, [visible c])
    else if c = 'r' ∧ (prev = .other ∨ prev = .escIdent ∨ prev = .quoteTok) then
      .ok (.rawR, sep)
    else if c = 'r' ∧ prev = .dot then .ok (.dotR, [])
    else .ok (.code .ident, sep ++ [visible c])
  else if c = '.' then
    .ok (.code (if prev = .ident ∨ prev = .escIdent then .identDot else .dot), ['.'])
  else if c.isDigit then
    if prev = .identDot ∨ prev = .dot then .ok (.fieldIdx, [c])
    else if c = '0' then .ok (.numZero, sep ++ [c])
    else .ok (.numDec, sep ++ [c])
  else if c = '"' then .ok (.str, [' '])
  else if c = '\'' then
    if prev = .quoteTok then .ok (.code .other, [' ']) else .ok (.chrOpen, [' '])
  else if c = '`' then
    if prev = .tick then .error "doubled backtick" else .ok (.code .tick, [' '])
  else if c = '«' then .ok (.guillemet, if prev = .identDot ∨ prev = .dot then [] else [' '])
  else if c = '»' then .error "unmatched identifier escape"
  else if c = '-' then .ok (.dash, [' '])
  else if c = '/' then .ok (.slash, [' '])
  else if c = '<' then .ok (.lt, [' '])
  else if c = '\\' then .ok (.bslash, [' '])
  else if c = '@' then .ok (.code .other, [' ', '@', ' '])
  else if c = '[' then .ok (.code .other, [' ', '[', ' '])
  else if c = ']' then .ok (.code .quoteTok, [' ', ']', ' '])
  else if c = '×' ∨ c = 'Σ' ∨ c = '⊕' then .ok (.code .quoteTok, [' '])
  else if c = '#' then .ok (.code .sym, [' ', '#'])
  else if c = '~' then .ok (.code .sym, [' '])
  else .ok (.code .other, [' '])

/-- A character inside a block comment at nesting `depth`. -/
def stepBlock (depth : Nat) (c : Char) : ScanState :=
  if c = '-' then .blockDash depth else if c = '/' then .blockSlash depth else .block depth

/-- A character inside an interpolation hole. -/
def stepHole (depth : Nat) (prev : HolePrev) (c : Char) : StepResult :=
  if c = '{' then .ok (.hole (depth + 1) .other, [' '])
  else if c = '}' then
    if depth ≤ 1 then .ok (.str, [' ']) else .ok (.hole (depth - 1) .other, [' '])
  else if c = '"' ∨ c = '\\' ∨ c = '«' ∨ c = '»' then
    .error "literal or escape inside an interpolation hole"
  else if c = '\'' then
    if prev = .ident then .ok (.hole depth .ident, ['\''])
    else if prev = .quoteTok then .ok (.hole depth .other, [' '])
    else .error "character literal inside an interpolation hole"
  else if c = '-' then .ok (.holeDash depth, [' '])
  else if c = '/' then .ok (.holeSlash depth, [' '])
  else if c = '@' then .ok (.hole depth .other, [' ', '@', ' '])
  else if c = '[' then .ok (.hole depth .other, [' ', '[', ' '])
  else if c = ']' then .ok (.hole depth .quoteTok, [' ', ']', ' '])
  else if c = '×' ∨ c = 'Σ' ∨ c = '⊕' then .ok (.hole depth .quoteTok, [' '])
  else if c = '#' then .ok (.hole depth .other, [' ', '#'])
  else if c.isDigit then
    .ok (.hole depth (if prev = .ident then .ident else .num), [c])
  else if isIdFirst c then
    .ok (.hole depth (if prev = .num then .num else .ident), [visible c])
  else if isIdRest c then .ok (.hole depth prev, [visible c])
  else if c = '.' then .ok (.hole depth .other, ['.'])
  else .ok (.hole depth .other, [' '])

def stepOne (st : ScanState) (c : Char) : StepResult :=
  match st with
  | .code prev => stepCode prev c
  | .dash => if c = '-' then .ok (.lineComment, []) else stepCode .other c
  | .slash =>
    if c = '-' then .ok (.blockStart 1, [])
    else if c = '/' then .ok (.slashAmb, [])
    else if c = '\\' then .ok (.code .other, [])
    else if c = '.' then .error "slash glued to a dot"
    else stepCode .other c
  | .slashAmb =>
    if c = '-' ∨ c = '.' then .error "comment opener or dot glued to a slash token"
    else if c = '/' then .ok (.slashAmb, [])
    else stepCode .other c
  | .lt => if c = '-' then .ok (.ltDash, []) else stepCode .other c
  | .ltDash =>
    if c = '-' then .error "line comment opener glued to a left arrow" else stepCode .other c
  | .bslash =>
    if c = '/' then .ok (.slashAmb, [])
    else if isIdFirst c then .error "identifier glued to a backslash"
    else stepCode .other c
  | .dotR =>
    if c = '"' ∨ c = '#' then .error "raw string prefix after a dot"
    else (stepCode .ident c).map (fun r => (r.1, 'r' :: r.2))
  | .lineComment => if c = '\n' then .ok (.code .other, []) else .ok (.lineComment, [])
  | .blockStart d => if c = '-' ∨ c = '!' then .ok (.block d, []) else .ok (stepBlock d c, [])
  | .block d => .ok (stepBlock d c, [])
  | .blockDash d =>
    if c = '/' then (if d ≤ 1 then .ok (.code .other, []) else .ok (.block (d - 1), []))
    else .ok (stepBlock d c, [])
  | .blockSlash d => if c = '-' then .ok (.block (d + 1), []) else .ok (stepBlock d c, [])
  | .str =>
    if c = '"' then .ok (.code .other, [])
    else if c = '\\' then .ok (.strEsc, [])
    else if c = '{' then .ok (.hole 1 .other, [' '])
    else .ok (.str, [])
  | .strEsc => .ok (.str, [])
  | .hole d p => stepHole d p c
  | .holeDash d =>
    if c = '-' then .error "comment inside an interpolation hole" else stepHole d .other c
  | .holeSlash d =>
    if c = '-' then .error "comment inside an interpolation hole" else stepHole d .other c
  | .chrOpen =>
    if c = '\\' then .ok (.chrEsc, [])
    else if c = '\'' then .error "empty character literal"
    else .ok (.chrEnd, [])
  | .chrEsc =>
    if c = 'x' then .ok (.chrEscN 2, [])
    else if c = 'u' then .ok (.chrEscN 4, [])
    else .ok (.chrEnd, [])
  | .chrEscN k => if k ≤ 1 then .ok (.chrEnd, []) else .ok (.chrEscN (k - 1), [])
  | .chrEnd =>
    if c = '\'' then .ok (.code .other, []) else .error "missing end of character literal"
  | .rawR =>
    if c = '"' then .ok (.raw 0, [' '])
    else if c = '#' then .ok (.rawHash 1, [])
    else (stepCode .ident c).map (fun r => (r.1, 'r' :: r.2))
  | .rawHash n =>
    if c = '#' then .ok (.rawHash (n + 1), [])
    else if c = '"' then .ok (.raw n, [' '])
    else (stepCode .sym c).map (fun r => (r.1, 'r' :: ' ' :: '#' :: r.2))
  | .raw n =>
    if c = '"' then (if n = 0 then .ok (.code .other, []) else .ok (.rawEnd n 0, []))
    else .ok (.raw n, [])
  | .rawEnd n k =>
    if c = '#' then (if k + 1 = n then .ok (.code .other, []) else .ok (.rawEnd n (k + 1), []))
    else if c = '"' then .ok (.rawEnd n 0, [])
    else .ok (.raw n, [])
  | .guillemet => if c = '»' then .ok (.code .escIdent, []) else .ok (.guillemet, [visible c])
  | .numZero =>
    if c = 'b' ∨ c = 'B' then .ok (.numRadix .bin, [c])
    else if c = 'o' ∨ c = 'O' then .ok (.numRadix .oct, [c])
    else if c = 'x' ∨ c = 'X' then .ok (.numRadix .hex, [c])
    else if c.isDigit ∨ c = '_' then .ok (.numDec, [c])
    else if c = '.' then .ok (.numDot, [])
    else if c = 'e' ∨ c = 'E' then .ok (.numExpStart, [c])
    else (stepCode .other c).map (fun r => (r.1, ' ' :: r.2))
  | .numRadix r =>
    if c = '_' ∨ r.isDigit c = true then .ok (.numRadix r, [c])
    else (stepCode .other c).map (fun r => (r.1, ' ' :: r.2))
  | .numDec =>
    if c.isDigit ∨ c = '_' then .ok (.numDec, [c])
    else if c = '.' then .ok (.numDot, [])
    else if c = 'e' ∨ c = 'E' then .ok (.numExpStart, [c])
    else (stepCode .other c).map (fun r => (r.1, ' ' :: r.2))
  | .numDot =>
    if c.isDigit then .ok (.numFrac, ['.', c])
    else if c = '.' then .ok (.code .other, [' '])
    else if c = 'e' ∨ c = 'E' then .ok (.numExpStart, ['.', c])
    else if isIdFirst c ∨ c = '«' then .error "identifier after a decimal point"
    else (stepCode .other c).map (fun r => (r.1, ' ' :: r.2))
  | .numFrac =>
    if c.isDigit ∨ c = '_' then .ok (.numFrac, [c])
    else if c = 'e' ∨ c = 'E' then .ok (.numExpStart, [c])
    else (stepCode .other c).map (fun r => (r.1, ' ' :: r.2))
  | .numExpStart =>
    if c = '+' ∨ c = '-' then .ok (.numExpSign, [])
    else if c.isDigit then .ok (.numExp, [c])
    else .error "missing exponent digits in a scientific literal"
  | .numExpSign =>
    if c.isDigit then .ok (.numExp, [c])
    else .error "missing exponent digits in a scientific literal"
  | .numExp =>
    if c.isDigit ∨ c = '_' then .ok (.numExp, [c])
    else (stepCode .other c).map (fun r => (r.1, ' ' :: r.2))
  | .fieldIdx =>
    if c.isDigit then .ok (.fieldIdx, [c])
    else (stepCode .other c).map (fun r => (r.1, ' ' :: r.2))

/-- May the input end in this state? Never inside a literal, block comment, or escape. -/
def lexTerminalOk : ScanState → Bool
  | .code _ | .dash | .slash | .slashAmb | .lt | .ltDash | .bslash | .dotR | .lineComment
  | .rawR | .rawHash _ | .numZero | .numRadix _ | .numDec | .numDot | .numFrac | .numExp
  | .fieldIdx => true
  | _ => false

/-- States that hold back an `r` not yet known to start a raw string. -/
def holdsPendingR : ScanState → Bool
  | .rawR | .dotR | .rawHash _ => true
  | _ => false

/-- Run the lexer; `acc` holds the visible code in reverse. -/
def lexAux : ScanState → List Char → List Char → Except String (List Char)
  | st, [], acc =>
    if lexTerminalOk st then
      .ok (if holdsPendingR st then ('r' :: acc).reverse else acc.reverse)
    else .error "input ends inside a literal, comment, or escape"
  | st, c :: rest, acc =>
    match stepOne st c with
    | .error msg => .error msg
    | .ok (st', out) => lexAux st' rest (out.reverse ++ acc)

/-- `pat` occurs somewhere in the text. -/
def hasInfix (pat : List Char) : List Char → Bool
  | [] => pat.isEmpty
  | c :: rest => pat.isPrefixOf (c :: rest) || hasInfix pat rest

/-- The code of a source text with comments and literal contents blanked out. -/
def lexSource (src : List Char) : Except String (List Char) :=
  if hasInfix Chars.plusOneBracketTick src then .error "quote glued to a successor bracket"
  else lexAux (.code .other) src []

def stripChars (src : List Char) : Except String (List Char) := lexSource src

def stripCommentsAndStrings (src : String) : Except String String :=
  (lexSource src.toList).map String.ofList

/-- Maximal runs of token characters. -/
def tokenizeChars (code : List Char) : List (List Char) :=
  (code.splitOn ' ').filter (fun t => !t.isEmpty)

def dotSegments (tok : List Char) : List (List Char) := tok.splitOn '.'

def lastDotSegment (tok : List Char) : List Char := (dotSegments tok).getLast?.getD []

/-- Drop one trailing `?` or `!`: `bv_decide?` and `decide!` are their base keyword. -/
def stripTacticSuffix (seg : List Char) : List Char :=
  match seg.getLast? with
  | some '?' => seg.dropLast
  | some '!' => seg.dropLast
  | _ => seg

/-- A segment is the keyword, or a numeric literal glued in front of it (`1native_decide`). -/
def segmentIsKeyword (kw seg : List Char) : Bool :=
  let s := stripTacticSuffix seg
  decide (s = kw) ||
    match s with
    | c :: _ => c.isDigit && kw.isSuffixOf s
    | [] => false

def tokenHasKeyword (kw : List Char) (tok : List Char) : Bool :=
  (dotSegments tok).any (segmentIsKeyword kw)

/-- The first of the keywords that occurs in some token. -/
def firstKeyword? (kws : List (List Char)) (toks : List (List Char)) : Option (List Char) :=
  kws.find? (fun kw => toks.any (tokenHasKeyword kw))

/-- Options a source may set, as `TrustedBoundary.isAllowedOptionName`. -/
def isAllowedOptionName (opt : List Char) : Bool :=
  decide (opt = Chars.maxHeartbeats) || decide (opt = Chars.maxRecDepth) ||
    Chars.ppPrefix.isPrefixOf opt || Chars.linterPrefix.isPrefixOf opt

/-- The first option set by `set_option` that is not on the allow-list. -/
def optionViolation? : List (List Char) → Option (List Char)
  | [] => none
  | t :: rest =>
    if tokenHasKeyword Chars.kwSetOption t then
      match rest with
      | [] => some Chars.kwSetOption
      | opt :: _ => if isAllowedOptionName opt then optionViolation? rest else some opt
    else optionViolation? rest

/-- Option names that are rejected wherever they appear, with or without `set_option`. -/
def forbiddenOptionTokens : List (List Char) :=
  [Chars.kwSkipKernelTC, Chars.kwAllowUnsafeReducibility, Chars.kwPrivateInPublic,
   Chars.kwQuotPrecheck, Chars.kwHygiene]

/-- Banned in every mode: native-reduction primitives, code-generation hooks, `unsafe` and
`partial`, and commands or tactics that run metaprograms or compile-time evaluation. -/
def metaExecTokens : List (List Char) :=
  [Chars.kwByElab, Chars.kwRunTac, Chars.kwRunCmd, Chars.kwRunMeta, Chars.kwRunElab,
   Chars.kwHashEval, Chars.kwHashReduce]

/-- Commands and attributes that add syntax, tokens, or macros, even `local` ones that
leave no extension entry: the lexer rules above hold only for the core token table. -/
def syntaxExtensionTokens : List (List Char) :=
  [Chars.kwNotation, Chars.kwInfix, Chars.kwInfixl, Chars.kwInfixr, Chars.kwPrefix,
   Chars.kwPostfix, Chars.kwSyntax, Chars.kwMacro, Chars.kwMacroRules, Chars.kwElab,
   Chars.kwElabRules, Chars.kwDeclareSyntaxCat, Chars.kwBinderPredicate,
   Chars.kwDeclareSimpLikeTactic]

/-- Extension-hook commands and attributes (initializers, elaborators, delaborators,
unexpanders, simprocs, unification hints, compiler passes/rewrites, `cbv_eval`,
`coinductive`, and `export` aliases), banned in every mode as defense in depth behind
the `.olean` extension audit. -/
def extHookTokens : List (List Char) :=
  [Chars.kwInitialize, Chars.kwBuiltinInit, Chars.kwCommandElab, Chars.kwTermElab,
   Chars.kwTacticElab, Chars.kwDoElemElab, Chars.kwInductiveElab, Chars.kwDelab,
   Chars.kwAppUnexpander, Chars.kwSimproc, Chars.kwDSimproc, Chars.kwCbvSimproc,
   Chars.kwSimprocDecl, Chars.kwDSimprocDecl, Chars.kwCbvSimprocDecl, Chars.kwUnifHint,
   Chars.kwUnificationHint, Chars.kwExport, Chars.kwCsimp, Chars.kwCpass, Chars.kwCbvEval,
   Chars.kwCbvOpaque, Chars.kwCoinductive, Chars.kwBuiltinTactic, Chars.kwGrindTactic,
   Chars.kwTryTactic, Chars.kwSymSimproc, Chars.kwSymDSimproc, Chars.kwSymDischarger,
   Chars.kwRunParserAttrHooks, Chars.kwRunBuiltinParserAttrHooks]

def alwaysForbiddenTokens : List (List Char) :=
  [Chars.ofReduceBool, Chars.ofReduceNat, Chars.trustCompiler, Chars.reduceBool,
   Chars.reduceNat, Chars.kwNativeEqTrue, Chars.kwImplementedBy, Chars.kwExtern,
   Chars.kwUnsafe, Chars.kwPartial] ++ metaExecTokens ++ syntaxExtensionTokens ++ extHookTokens

/-- Detect `init` inside an attribute block (`@[... init ...]` or `attribute [... init ...]`)
without flagging ordinary identifiers such as `def init := 0` or list literals `[init]`. -/
def initAttributeAux : Nat → List (List Char) → Option (List Char)
  | _, [] => none
  | 0, t1 :: t2 :: rest =>
    if (t1 = ['@'] ∨ tokenHasKeyword Chars.kwAttribute t1) ∧ t2 = ['['] then
      initAttributeAux 1 rest
    else initAttributeAux 0 (t2 :: rest)
  | 0, [_] => none
  | depth + 1, t :: rest =>
    if t = ['['] then initAttributeAux (depth + 2) rest
    else if t = [']'] then initAttributeAux depth rest
    else if tokenHasKeyword Chars.kwInit t then some Chars.kwInit
    else initAttributeAux (depth + 1) rest

def initAttribute? (toks : List (List Char)) : Option (List Char) :=
  initAttributeAux 0 toks

def stripLeadingDigits : List Char → List Char
  | c :: rest => if c.isDigit then stripLeadingDigits rest else c :: rest
  | [] => []

/-- A token naming a `builtin_<kw>` variant of any always-forbidden keyword or attribute. -/
def builtinForbidden? (toks : List (List Char)) : Option (List Char) :=
  toks.find? (fun t =>
    (dotSegments t).any (fun seg =>
      let s := stripLeadingDigits (stripTacticSuffix seg)
      Chars.builtinPrefix.isPrefixOf s &&
        alwaysForbiddenTokens.any (fun kw => decide (s.drop Chars.builtinPrefix.length = kw))))

/-- A token naming a parser attribute (`term_parser`, `builtin_command_parser`, …). -/
def parserAttribute? (toks : List (List Char)) : Option (List Char) :=
  toks.find? (fun t => (dotSegments t).any (fun seg => Chars.parserSuffix.isSuffixOf seg))

/-- Tactics that add a `_native` axiom. -/
def nativeTacticTokens : List (List Char) :=
  [Chars.kwNativeDecide, Chars.kwBvDecide, Chars.kwBvCheck]

/-- `decide` together with any way of passing it a configuration. A positional
`DecideConfig` (`decide (config := ⟨false, true, true, false⟩)`) selects native evaluation
without the word `native`, so every `config` is refused; `decide +kernel` is not. -/
def hasNativeDecideConfig (toks : List (List Char)) : Bool :=
  toks.any (tokenHasKeyword Chars.kwDecide) &&
    toks.any (fun t => tokenHasKeyword Chars.kwNative t || tokenHasKeyword Chars.kwConfig t ||
      tokenHasKeyword Chars.kwDecideConfig t)

def hasNativeDecideTokensChars (toks : List (List Char)) : Bool :=
  (firstKeyword? nativeTacticTokens toks).isSome || hasNativeDecideConfig toks

def hasMetaExecTokensChars (toks : List (List Char)) : Bool :=
  (firstKeyword? metaExecTokens toks).isSome

def hasUnsafeTokenChars (toks : List (List Char)) : Bool :=
  toks.any (tokenHasKeyword Chars.kwUnsafe)

def checkTokens (cfg : AuditConfig) (modName : SymName) (role : ModuleRole)
    (toks : List (List Char)) : Except AuditFailure Unit :=
  match optionViolation? toks with
  | some opt => .error (.forbiddenSourceOption modName (String.ofList opt))
  | none =>
    match firstKeyword? forbiddenOptionTokens toks with
    | some kw => .error (.forbiddenSourceOption modName (String.ofList kw))
    | none =>
      match (((firstKeyword? alwaysForbiddenTokens toks).or (builtinForbidden? toks)).or
          (parserAttribute? toks)).or (initAttribute? toks) with
      | some kw => .error (.forbiddenSourceOption modName (String.ofList kw))
      | none =>
        if cfg.allowProvisionalNative = true ∧ role = .proof then .ok ()
        else
          match firstKeyword? nativeTacticTokens toks with
          | some kw => .error (.forbiddenSourceOption modName (String.ofList kw))
          | none =>
            ensure (hasNativeDecideConfig toks = false)
              (.forbiddenSourceOption modName "decide with a configuration")

def scanSourceChars (cfg : AuditConfig) (modName : SymName) (role : ModuleRole)
    (src : List Char) : Except AuditFailure Unit :=
  match lexSource src with
  | .error msg => .error (.unsupportedSourceLexing modName msg)
  | .ok code => checkTokens cfg modName role (tokenizeChars code)

/-- Scan one module's source text. -/
def scanSourceDefenseInDepth (cfg : AuditConfig) (modName : SymName) (role : ModuleRole)
    (src : String) : Except AuditFailure Unit :=
  scanSourceChars cfg modName role src.toList

end SourceScanner

/-! ## Package lookups and structure -/

def findModuleIn : List ModuleInventory → SymName → Option ModuleInventory
  | [], _ => none
  | inv :: rest, m => if inv.moduleName = m then some inv else findModuleIn rest m

theorem findModuleIn_spec {mods : List ModuleInventory} {m : SymName} {inv : ModuleInventory}
    (h : findModuleIn mods m = some inv) : inv ∈ mods ∧ inv.moduleName = m := by
  induction mods with
  | nil => simp [findModuleIn] at h
  | cons x rest ih =>
    simp only [findModuleIn] at h
    split at h
    · cases h; exact ⟨List.mem_cons_self, by assumption⟩
    · exact ⟨List.mem_cons_of_mem _ (ih h).1, (ih h).2⟩

theorem findModuleIn_of_mem_nodup {mods : List ModuleInventory}
    (hnd : (mods.map ModuleInventory.moduleName).Nodup) {inv : ModuleInventory}
    (h : inv ∈ mods) : findModuleIn mods inv.moduleName = some inv := by
  induction mods with
  | nil => simp at h
  | cons x rest ih =>
    simp only [List.map_cons, List.nodup_cons] at hnd
    simp only [findModuleIn]
    rcases List.mem_cons.mp h with rfl | hmem
    · simp
    · split
      · rename_i heq
        exact absurd (List.mem_map.mpr ⟨inv, hmem, heq.symm⟩) hnd.1
      · exact ih hnd.2 hmem

/-- The first module whose inventory declares the name (Lean's `const2ModIdx`). -/
def moduleOfConstIn : List ModuleInventory → SymName → Option ModuleInventory
  | [], _ => none
  | inv :: rest, n => if n ∈ inv.constNames then some inv else moduleOfConstIn rest n

theorem moduleOfConstIn_spec {mods : List ModuleInventory} {n : SymName} {inv : ModuleInventory}
    (h : moduleOfConstIn mods n = some inv) : inv ∈ mods ∧ n ∈ inv.constNames := by
  induction mods with
  | nil => simp [moduleOfConstIn] at h
  | cons x rest ih =>
    simp only [moduleOfConstIn] at h
    split at h
    · cases h; exact ⟨List.mem_cons_self, by assumption⟩
    · exact ⟨List.mem_cons_of_mem _ (ih h).1, (ih h).2⟩

def findModule? (pkg : PackageAuditInput) (m : SymName) : Option ModuleInventory :=
  findModuleIn pkg.modules m

def moduleOfConst? (pkg : PackageAuditInput) (n : SymName) : Option ModuleInventory :=
  moduleOfConstIn pkg.modules n

/-- The role of any module name: the audited module's validated role, or the role its
name justifies when it lies outside the package. -/
def roleOfModule (pkg : PackageAuditInput) (m : SymName) : ModuleRole :=
  match findModule? pkg m with
  | some inv => inv.role
  | none => baseRoleOfModuleName m

/-- The module that declares a constant: computed from the inventories for package
constants, read from the pinned record for base constants. Never read from a package
record's own `originModule` claim. -/
def declaringModuleName (pkg : PackageAuditInput) (n : SymName) (ci : ConstantRecord) : SymName :=
  match moduleOfConst? pkg n with
  | some inv => inv.moduleName
  | none => ci.originModule.getD .anonymous

def roleOfConst (pkg : PackageAuditInput) (n : SymName) (ci : ConstantRecord) : ModuleRole :=
  match moduleOfConst? pkg n with
  | some inv => inv.role
  | none => baseRoleOfModuleName (ci.originModule.getD .anonymous)

/-- Everything the package's modules see: the base environment, then every module's map. -/
def packageEnv (pkg : PackageAuditInput) : KernelEnv :=
  mkBaseKernelEnv pkg.baseEnv ++ KernelEnv.finalizeImportedEnv pkg.modules

def baseModuleNames (pkg : PackageAuditInput) : List SymName :=
  pkg.baseEnv.filterMap (·.originModule)

/-- In module mode every part of the artifact must exist: Lean silently falls back from a
missing `.olean.server` or `.olean.private` to the plain `.olean`. -/
def validateOleanParts (inv : ModuleInventory) : Except AuditFailure Unit := do
  ensure (inv.oleanParts.isModuleMode = false ∨ inv.oleanParts.hasServer = true)
    (.missingOleanServer inv.moduleName)
  ensure (inv.oleanParts.isModuleMode = false ∨ inv.oleanParts.hasPrivate = true)
    (.missingOleanPrivate inv.moduleName)

/-- The role label must be the one the module name justifies, and no audited module may
carry a standard-library, compiler, or `Trusted` name: those are the pinned base
environment, never artifacts under audit. -/
def validateModuleRole (inv : ModuleInventory) : Except AuditFailure Unit := do
  ensure (inv.moduleName.isStdlibModule = false ∧ inv.moduleName.isLeanCompilerModule = false)
    (.stdlibNamedPackageModule inv.moduleName)
  ensure (inv.moduleName.isTrustedModule = false) (.trustedNamedPackageModule inv.moduleName)
  ensure (inv.role ≠ .defsExempt ∨ inv.moduleName.isStrictExemptModuleName = true)
    (.spoofedExemptModule inv.moduleName)
  ensure (roleMatchesModuleName inv.role inv.moduleName = true)
    (.moduleRoleMismatch inv.moduleName inv.role.render)

def validateModuleStructure (inv : ModuleInventory) : Except AuditFailure Unit := do
  validateModuleRole inv
  validateOleanParts inv
  validateReplayInventory inv

def allDeclaredNames (pkg : PackageAuditInput) : List SymName :=
  pkg.baseEnv.map (·.name) ++ pkg.modules.flatMap (·.constNames)

def allExtraConstNames (pkg : PackageAuditInput) : List SymName :=
  pkg.modules.flatMap (·.extraConstNames)

/-- Module names are unique (and disjoint from base-environment module origins), every
base and package declaration name is well-formed, every module is structurally valid,
constant names are unique across the base environment and all modules, and
`extraConstNames` are distinct across all modules and never claim a declared name. -/
def validatePackageStructure (pkg : PackageAuditInput) : Except AuditFailure Unit := do
  ensureNodup (pkg.modules.map (·.moduleName)) .duplicateModuleName
  ensure (pkg.baseEnv.all (fun ci => ci.name.isWellFormed) = true)
    (.anonymousConstantName .anonymous)
  checkAll pkg.modules validateModuleStructure
  checkAll pkg.modules (fun inv =>
    ensure (inv.moduleName ∉ baseModuleNames pkg) (.duplicateModuleName inv.moduleName))
  ensureNodup (allDeclaredNames pkg)
    (fun d => .duplicateConstName ((moduleOfConst? pkg d).map (·.moduleName) |>.getD .anonymous) d)
  checkAll pkg.modules (fun inv => checkAll inv.extraConstNames (fun n =>
    ensure (n ∉ allDeclaredNames pkg)
      (.extraConstNameProvenance inv.moduleName n "claims a declared constant")))
  ensureNodup (allExtraConstNames pkg)
    (fun n =>
      let owner := (pkg.modules.find? (fun m => decide (n ∈ m.extraConstNames))).map (·.moduleName)
      .extraConstNameProvenance (owner.getD .anonymous) n "duplicate extraConstName across modules")

theorem validatePackageStructure_ok {pkg : PackageAuditInput}
    (h : validatePackageStructure pkg = .ok ()) :
    (pkg.modules.map (·.moduleName)).Nodup ∧
    (∀ ci ∈ pkg.baseEnv, ci.name.isWellFormed = true) ∧
    (∀ inv ∈ pkg.modules, validateModuleRole inv = .ok () ∧ validateOleanParts inv = .ok () ∧
      validateReplayInventory inv = .ok () ∧ inv.moduleName ∉ baseModuleNames pkg) ∧
    (allDeclaredNames pkg).Nodup ∧
    (allExtraConstNames pkg).Nodup ∧
    (∀ inv ∈ pkg.modules, ∀ n ∈ inv.extraConstNames, n ∉ allDeclaredNames pkg) := by
  simp only [validatePackageStructure, bindUnit_ok_iff, ensureNodup_ok_iff, checkAll_ok_iff,
    ensure_ok_iff, List.all_eq_true] at h
  refine ⟨h.1, h.2.1, fun inv hinv => ?_, h.2.2.2.2.1, h.2.2.2.2.2.2, h.2.2.2.2.2.1⟩
  have h1 := h.2.2.1 inv hinv
  have h2 := h.2.2.2.1 inv hinv
  simp only [validateModuleStructure, bindUnit_ok_iff] at h1
  exact ⟨h1.1, h1.2.1, h1.2.2, h2⟩

/-! ## Codegen `_unsafe_rec` companions -/

/-- The equation compiler's `parent._unsafe_rec` companion of a safe definition of the
same module: a `partial` definition with a stored body and the parent's type. -/
def isCodegenUnsafeRecInMod (inv : ModuleInventory) (ci : ConstantRecord) : Bool :=
  decide (ci.safety = .partialDecl ∧ ci.kind = .defnDecl ∧ ci.value?.isSome = true) &&
  match ci.name.unsafeRecParent? with
  | some p =>
    match findConstByName inv.constants p with
    | some pc => decide (pc.kind = .defnDecl ∧ pc.safety = .safe ∧ pc.type = ci.type)
    | none => false
  | none => false

theorem isCodegenUnsafeRecInMod_parent {inv : ModuleInventory} {ci : ConstantRecord}
    (h : isCodegenUnsafeRecInMod inv ci = true) :
    ∃ pc ∈ inv.constants, pc.safety = .safe ∧ pc.type = ci.type := by
  unfold isCodegenUnsafeRecInMod at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨_, h⟩ := h
  split at h
  · split at h
    · rename_i pc hpc
      simp only [decide_eq_true_eq] at h
      exact ⟨pc, (findConstByName_mem hpc).1, h.2.1, h.2.2⟩
    · cases h
  · cases h

def replayableConstants (inv : ModuleInventory) : List ConstantRecord :=
  inv.constants.filter (fun ci => !isCodegenUnsafeRecInMod inv ci)

/-! ## Persistent environment extensions -/

/-- A declaration belongs locally to `inv` for extension purposes only if it is both
declared in `inv` and kernel-replayed (never a dangling name, borrowed name, or
un-replayed `partial` `_unsafe_rec` companion). -/
def isLocalExtDecl (inv : ModuleInventory) (d : SymName) : Bool :=
  decide (d ∈ inv.constNames) && decide (d ∈ (replayableConstants inv).map (·.name))

/-- Full β-reduction and local-definition unfolding used to normalize instance and alias
types before checking local anchoring. Returns `none` on fuel exhaustion (fail-closed). -/
def normInstanceExprOpt (inv : ModuleInventory) : Nat → ExprSkeleton → Option ExprSkeleton
  | 0, _ => none
  | fuel + 1, .const c =>
    match findConstByName inv.constants c with
    | some ci =>
      if ci.kind = .defnDecl then
        match ci.value? with
        | some v => normInstanceExprOpt inv fuel v
        | none => none
      else some (.const c)
    | none => some (.const c)
  | fuel + 1, .app f a =>
    match normInstanceExprOpt inv fuel f with
    | none => none
    | some (.lam _ b) =>
      match normInstanceExprOpt inv fuel a with
      | none => none
      | some a' => normInstanceExprOpt inv fuel (b.instantiate a')
    | some f' =>
      match normInstanceExprOpt inv fuel a with
      | none => none
      | some a' => some (.app f' a')
  | fuel + 1, .lam t b =>
    match normInstanceExprOpt inv fuel t, normInstanceExprOpt inv fuel b with
    | some t', some b' => some (.lam t' b')
    | _, _ => none
  | fuel + 1, .pi t b =>
    match normInstanceExprOpt inv fuel t, normInstanceExprOpt inv fuel b with
    | some t', some b' => some (.pi t' b')
    | _, _ => none
  | fuel + 1, .proj s i e =>
    match normInstanceExprOpt inv fuel e with
    | some e' => some (.proj s i e')
    | none => none
  | _ + 1, e => some e

def invDefnBodySize (inv : ModuleInventory) : Nat :=
  (inv.constants.map (fun ci =>
    if ci.kind = .defnDecl then (ci.value?.map ExprSkeleton.size).getD 0 else 0)).sum

def instanceNormFuel (inv : ModuleInventory) (e : ExprSkeleton) : Nat :=
  64 + 4 * e.size + 2 * inv.constants.length + 2 * invDefnBodySize inv

/-- Normalize an instance or alias type under β-reduction and local-definition unfolding,
then extract the conclusion under all leading `pi` binders (even binders revealed only
after β/δ-reduction). -/
def normInstanceTargetOpt (inv : ModuleInventory) (e : ExprSkeleton) : Option ExprSkeleton :=
  (normInstanceExprOpt inv (instanceNormFuel inv e) e).map ExprSkeleton.piTarget

/-- Non-definition local declaration without a reducibility attribute: cannot silently
unfold to an imported type or class during instance synthesis. -/
def isBaseInstanceAnchor (inv : ModuleInventory) (d : SymName) : Bool :=
  isLocalExtDecl inv d && decide (EnvExtEntry.reducibilityOverride d ∉ inv.extEntries) &&
    match findConstByName inv.constants d with
    | some ci => decide (ci.kind ≠ .defnDecl)
    | none => false

/-- Core `Init` typeclasses whose trailing arguments are `outParam`s: anchoring solely in an
`outParam` (e.g. `HAdd Nat Nat Color`) still matches every imported-type query (`Nat + Nat`). -/
def outParamAfter2Classes : List (List Char) :=
  [Chars.clsHAdd, Chars.clsHSub, Chars.clsHMul, Chars.clsHDiv, Chars.clsHMod, Chars.clsHPow,
   Chars.clsHAppend, Chars.clsHAnd, Chars.clsHOr, Chars.clsHXor, Chars.clsHShiftLeft,
   Chars.clsHShiftRight, Chars.clsHSMul, Chars.clsHAndThen, Chars.clsHOrElse,
   Chars.clsGetElem, Chars.clsGetElemQ, Chars.clsTrans]

def outParamAfter1Classes : List (List Char) :=
  [Chars.clsCoeOut, Chars.clsCoeTail, Chars.clsCoeFun, Chars.clsCoeSort]

/-- Input expressions of a normalized instance conclusion, excluding `outParam` slots of
known `Init` classes so an instance cannot anchor solely on an output parameter. -/
def instanceInputExprs (target : ExprSkeleton) : List ExprSkeleton :=
  match target.getAppFn with
  | .const cls =>
    match cls.parts with
    | [seg] =>
      let args := target.getAppArgs
      if seg ∈ outParamAfter2Classes then args.take 2
      else if seg ∈ outParamAfter1Classes then args.take 1
      else if seg = Chars.clsCoeHead then args.drop 1
      else [target]
    | _ => [target]
  | _ => [target]

/-- A local declaration that can own an instance or coercion: a non-reducible local
declaration that is either non-definitional (`inductive`/`opaque`/...) or a non-reducible
definition whose normalized conclusion still names a non-reducible local base anchor
(closing both `abbrev N := Nat` and un-annotated `def N := Nat` / `def C := OfNat Nat 0`). -/
def isInstanceAnchor (inv : ModuleInventory) (d : SymName) : Bool :=
  isLocalExtDecl inv d && decide (EnvExtEntry.reducibilityOverride d ∉ inv.extEntries) &&
    match findConstByName inv.constants d with
    | some ci =>
      if ci.kind = .defnDecl then
        match ci.value? with
        | some v =>
          match normInstanceTargetOpt inv v with
          | some target =>
            (instanceInputExprs target).any (fun a => a.usedConstants.any (isBaseInstanceAnchor inv))
          | none => false
        | none => false
      else true
    | none => false

/-- Policy for one persisted extension entry. An entry found in a persisted table is
persisted, whatever scope it was declared with. No audited module may register macros,
syntax, elaborators, delaborators, unexpanders, initializers, `implemented_by` / `extern`
hooks, or `export` aliases. A reducibility attribute must target a local declaration. An
instance must be a local declaration of a local anchor class (`isInstanceAnchor`), except
that a definitions module may instantiate an imported class when the β/δ-normalized
conclusion's non-`outParam` input expressions name a local base anchor, and may also
register scoped/default instances of local anchor classes and coercions involving a local
anchor type. -/
def validateSingleExtEntry (inv : ModuleInventory) (ext : EnvExtEntry) : Except AuditFailure Unit :=
  match ext with
  | .macroEntry d => .error (.forbiddenMacroOrElab inv.moduleName "macro" d)
  | .syntaxEntry d => .error (.forbiddenMacroOrElab inv.moduleName "syntax" d)
  | .commandElabEntry d => .error (.forbiddenMacroOrElab inv.moduleName "command_elab" d)
  | .localCommandElabEntry d persistedGlobal =>
    .error (.forbiddenMacroOrElab inv.moduleName
      (if persistedGlobal then "local_command_elab_global" else "local_command_elab") d)
  | .termElabEntry d => .error (.forbiddenMacroOrElab inv.moduleName "term_elab" d)
  | .delabEntry d => .error (.forbiddenMacroOrElab inv.moduleName "delab" d)
  | .appUnexpanderEntry d => .error (.forbiddenMacroOrElab inv.moduleName "app_unexpander" d)
  | .scopedMacroEntry d _ => .error (.forbiddenMacroOrElab inv.moduleName "scoped_macro" d)
  | .scopedElabEntry d _ => .error (.forbiddenMacroOrElab inv.moduleName "scoped_elab" d)
  | .initializeEntry d isMeta =>
    .error (.forbiddenInitOrCodegenHook inv.moduleName
      (if isMeta then "meta_initialize" else "initialize") d)
  | .implementedByEntry d _ =>
    .error (.forbiddenInitOrCodegenHook inv.moduleName "implemented_by" d)
  | .externEntry d => .error (.forbiddenInitOrCodegenHook inv.moduleName "extern" d)
  | .instanceEntry d cls _ => do
    ensure (isLocalExtDecl inv d = true)
      (.forbiddenInstanceOrCoe inv.moduleName "imported_instance" d)
    if isInstanceAnchor inv cls then .ok ()
    else do
      ensure (inv.role = .defsExempt)
        (.forbiddenInstanceOrCoe inv.moduleName "instance_of_imported_class" d)
      match findConstByName inv.constants d with
      | some ci =>
        match normInstanceTargetOpt inv ci.type with
        | some target =>
          ensure ((instanceInputExprs target).any
              (fun a => a.usedConstants.any (isBaseInstanceAnchor inv)) = true)
            (.forbiddenInstanceOrCoe inv.moduleName "orphan_instance_of_imported_class" d)
        | none =>
          .error (.forbiddenInstanceOrCoe inv.moduleName "orphan_instance_of_imported_class" d)
      | none =>
        .error (.forbiddenInstanceOrCoe inv.moduleName "imported_instance" d)
  | .scopedInstanceEntry d cls _ => do
    ensure (inv.role = .defsExempt) (.forbiddenInstanceOrCoe inv.moduleName "scoped_instance" d)
    ensure (isLocalExtDecl inv d = true ∧ isInstanceAnchor inv cls = true)
      (.forbiddenInstanceOrCoe inv.moduleName "scoped_instance_of_imported_target" d)
  | .defaultInstanceEntry d cls => do
    ensure (inv.role = .defsExempt) (.forbiddenInstanceOrCoe inv.moduleName "default_instance" d)
    ensure (isLocalExtDecl inv d = true ∧ isInstanceAnchor inv cls = true)
      (.forbiddenInstanceOrCoe inv.moduleName "default_instance_of_imported_target" d)
  | .coeEntry d src tgt => do
    ensure (inv.role = .defsExempt) (.forbiddenInstanceOrCoe inv.moduleName "coe" d)
    ensure (isLocalExtDecl inv d = true ∧
        (isInstanceAnchor inv src = true ∨ isInstanceAnchor inv tgt = true))
      (.forbiddenInstanceOrCoe inv.moduleName "coe_between_imported_types" d)
  | .reducibilityOverride t =>
    ensure (isLocalExtDecl inv t = true) (.forbiddenReducibilityOverride inv.moduleName t)
  | .exportAlias a _ => .error (.forbiddenShadowingOrExport inv.moduleName "export" a)

def validateModuleExtensions (inv : ModuleInventory) : Except AuditFailure Unit :=
  checkAll inv.extEntries (validateSingleExtEntry inv)

/-- An accepted entry owns its declaration: it is declared, audited, and kernel-replayed
in the same module. -/
theorem validateSingleExtEntry_localDecl {inv : ModuleInventory} {ext : EnvExtEntry}
    (h : validateSingleExtEntry inv ext = .ok ()) :
    ∀ d, ext.localDecl? = some d →
      d ∈ inv.constNames ∧ d ∈ (replayableConstants inv).map (·.name) := by
  intro d hd
  cases ext with
  | instanceEntry d' cls isPriv =>
    simp only [EnvExtEntry.localDecl?, Option.some.injEq] at hd
    subst hd
    simp only [validateSingleExtEntry, bindUnit_ok_iff, ensure_ok_iff] at h
    simpa [isLocalExtDecl] using h.1
  | _ =>
    simp_all [validateSingleExtEntry, EnvExtEntry.localDecl?, bindUnit_ok_iff, ensure_ok_iff,
      isLocalExtDecl]

/-- Names a public declaration may not shadow by namespace suffix: everything in the base
environment and everything declared by another statement-side module (`Defs`, `Spec`, or
`Assumptions`). -/
def protectedNames (pkg : PackageAuditInput) (inv : ModuleInventory) : List SymName :=
  pkg.baseEnv.map (·.name) ++
    (pkg.modules.filter (fun m =>
      isStatementSideRole m.role && decide (m.moduleName ≠ inv.moduleName))).flatMap (·.constNames)

/-- `Pkg.Nat.add` shadows `Nat.add` for any reader with `Pkg` open. Private names cannot
be opened; a suffix with an internal component cannot be written by a user. -/
def shadowsProtected (prot : List SymName) (n : SymName) : Bool :=
  !n.isPrivateName && n.properSuffixes.any (fun s => !s.hasInternalPart && decide (s ∈ prot))

def auditShadowing (pkg : PackageAuditInput) (inv : ModuleInventory) : Except AuditFailure Unit :=
  checkAll inv.constants (fun ci =>
    ensure (shadowsProtected (protectedNames pkg inv) ci.name = false)
      (.forbiddenShadowingOrExport inv.moduleName "namespace_shadow" ci.name))

/-! ## Imports -/

/-- May a module of role `importer` import a module of role `imported`? Statement-side
modules import only statement-side modules; theory adds theory; proofs add proofs; verify
modules add verify modules; only tests import tests. -/
def importRoleAllowed (importer imported : ModuleRole) : Bool :=
  match importer, imported with
  | _, .foundation => true
  | _, .trusted => true
  | .test, _ => true
  | _, .test => false
  | .verify, _ => true
  | _, .verify => false
  | .proof, _ => true
  | _, .proof => false
  | .theory, _ => true
  | _, .theory => false
  | _, _ => true

theorem importRoleAllowed_statementSide {r r' : ModuleRole} (hr : isStatementSideRole r = true)
    (h : importRoleAllowed r r' = true) : isStatementSideRole r' = true := by
  cases r <;> cases r' <;> simp_all [importRoleAllowed, isStatementSideRole]

def directImportsOf (pkg : PackageAuditInput) (m : SymName) : List SymName :=
  match findModule? pkg m with
  | some inv => inv.imports.map (·.module)
  | none => []

/-- `b` is reachable from `a` through one or more declared imports of package modules. -/
inductive ImportReaches (pkg : PackageAuditInput) : SymName → SymName → Prop where
  | direct {a b : SymName} : b ∈ directImportsOf pkg a → ImportReaches pkg a b
  | step {a c b : SymName} : c ∈ directImportsOf pkg a → ImportReaches pkg c b →
      ImportReaches pkg a b

def importExpand (pkg : PackageAuditInput) (m : SymName) : Except AuditFailure (List SymName) :=
  .ok (directImportsOf pkg m)

def importGraphFuel (pkg : PackageAuditInput) : Nat :=
  1 + worklistBudget [] (pkg.modules.map (fun inv => (inv.moduleName, inv.imports.length)))

/-- Is `target` among `pending` or reachable from it through declared imports? -/
def importReachesAux (pkg : PackageAuditInput) (target : SymName) (fuel : Nat)
    (pending visited : List SymName) : Bool :=
  match worklist (importExpand pkg) AuditFailure.importCycle fuel pending visited with
  | .ok result => decide (target ∈ result)
  | .error _ => false

theorem reach_import_iff {pkg : PackageAuditInput} {a b : SymName} :
    Reach (importExpand pkg) a b ↔ a = b ∨ ImportReaches pkg a b := by
  constructor
  · intro h
    induction h with
    | refl a => exact Or.inl rfl
    | step hexp hb _ ih =>
      simp only [importExpand, Except.ok.injEq] at hexp
      subst hexp
      rcases ih with rfl | hr
      · exact Or.inr (.direct hb)
      · exact Or.inr (.step hb hr)
  · intro h
    rcases h with rfl | h
    · exact Reach.refl _
    · induction h with
      | direct hb => exact Reach.step rfl hb (Reach.refl _)
      | step hc _ ih => exact Reach.step rfl hc ih

theorem importExpand_bound (pkg : PackageAuditInput) (a : SymName) (edges : List SymName)
    (h : importExpand pkg a = .ok edges) :
    edges = [] ∨ ∃ c, (a, c) ∈ pkg.modules.map (fun inv => (inv.moduleName, inv.imports.length)) ∧
      edges.length ≤ c := by
  simp only [importExpand, Except.ok.injEq] at h
  subst h
  unfold directImportsOf findModule?
  split
  · rename_i inv hinv
    obtain ⟨hmem, hname⟩ := findModuleIn_spec hinv
    exact Or.inr ⟨inv.imports.length, List.mem_map.mpr ⟨inv, hmem, by rw [hname]⟩, by simp⟩
  · exact Or.inl rfl

/-- The executable import-closure search is exact: it neither over- nor under-approximates
reachability through declared imports. -/
theorem importClosureCheck_exact (pkg : PackageAuditInput) (target : SymName)
    (pending : List SymName) :
    importReachesAux pkg target (importGraphFuel pkg + pending.length) pending [] = true ↔
      ∃ p ∈ pending, p = target ∨ ImportReaches pkg p target := by
  unfold importReachesAux
  cases hw : worklist (importExpand pkg) AuditFailure.importCycle
      (importGraphFuel pkg + pending.length) pending [] with
  | error e =>
    exfalso
    obtain ⟨a, ha⟩ := worklist_error_of_fuel (importExpand_bound pkg) _ pending [] e
      (by simp [importGraphFuel]; omega) hw
    simp [importExpand] at ha
  | ok result =>
    simp only [decide_eq_true_eq]
    constructor
    · intro ht
      rcases worklist_origin _ pending [] result hw target ht with hv | ⟨p, hp, hr⟩
      · simp at hv
      · exact ⟨p, hp, reach_import_iff.mp hr⟩
    · rintro ⟨p, hp, hr⟩
      obtain ⟨_, hpend, hcl⟩ := worklist_closed _ pending [] result hw
      have hcl' : ∀ n ∈ result, ∃ edges, importExpand pkg n = .ok edges ∧
          ∀ e ∈ edges, e ∈ result := by
        intro n hn
        rcases hcl n hn with hnv | hne
        · simp at hnv
        · exact hne
      exact reach_mem_of_closed hcl' (reach_import_iff.mpr hr) (hpend p hp)

theorem importReaches_iff_direct {pkg : PackageAuditInput} {a b : SymName} :
    ImportReaches pkg a b ↔ ∃ p ∈ directImportsOf pkg a, p = b ∨ ImportReaches pkg p b := by
  constructor
  · intro h
    cases h with
    | direct hb => exact ⟨b, hb, Or.inl rfl⟩
    | step hc hr => exact ⟨_, hc, Or.inr hr⟩
  · rintro ⟨p, hp, rfl | hr⟩
    · exact .direct hp
    · exact .step hp hr

/-- Does the import closure of `m` contain `target`? -/
def importClosureContains (pkg : PackageAuditInput) (m target : SymName) : Bool :=
  importReachesAux pkg target (importGraphFuel pkg + (directImportsOf pkg m).length)
    (directImportsOf pkg m) []

theorem importClosureContains_iff {pkg : PackageAuditInput} {m target : SymName} :
    importClosureContains pkg m target = true ↔ ImportReaches pkg m target := by
  unfold importClosureContains
  rw [importClosureCheck_exact, importReaches_iff_direct]

/-- A module sees itself and its import closure. -/
def moduleVisibleFrom (pkg : PackageAuditInput) (inv : ModuleInventory) (target : SymName) : Bool :=
  decide (target = inv.moduleName) || importClosureContains pkg inv.moduleName target

theorem moduleVisibleFrom_iff {pkg : PackageAuditInput} {inv : ModuleInventory} {target : SymName} :
    moduleVisibleFrom pkg inv target = true ↔
      target = inv.moduleName ∨ ImportReaches pkg inv.moduleName target := by
  simp only [moduleVisibleFrom, Bool.or_eq_true, decide_eq_true_eq, importClosureContains_iff]

/-- A private instance of the imported module, which `import all` would expose. -/
def privateInstanceOf (pkg : PackageAuditInput) (m : SymName) : Option SymName :=
  match findModule? pkg m with
  | some inv =>
    inv.extEntries.findSome? (fun e =>
      match e with
      | .instanceEntry d _ isPrivateInst =>
        if isPrivateInst || d.isPrivateName then some d else none
      | _ => none)
  | none => none

def importAllFailure (pkg : PackageAuditInput) (inv : ModuleInventory) (imp : ImportSpec) :
    AuditFailure :=
  match privateInstanceOf pkg imp.module with
  | some d => .privateInstanceLeakViaImportAll inv.moduleName imp.module d
  | none => .forbiddenImportAll inv.moduleName imp.module

/-- Is the module part of the package, the pinned base environment, or the standard library? -/
def isKnownModule (pkg : PackageAuditInput) (m : SymName) : Bool :=
  (findModule? pkg m).isSome || decide (m ∈ baseModuleNames pkg) || m.isStdlibModule

/-- One import: no `import all`, no `private import` (not even of `Init`), no `meta import`
except the implicit one of `Init`, no `Lean.*`, nothing outside the package, the base
environment, and the standard library, and only in an allowed role direction. -/
def validateSingleImport (pkg : PackageAuditInput) (inv : ModuleInventory) (imp : ImportSpec) :
    Except AuditFailure Unit := do
  ensure (imp.importAll = false) (importAllFailure pkg inv imp)
  ensure (imp.isExported = true) (.forbiddenImportModifier inv.moduleName imp.module "private")
  ensure (imp.isMeta = false ∨ imp.module = SymName.initModuleName)
    (.forbiddenImportModifier inv.moduleName imp.module "meta")
  ensure (imp.module.isLeanCompilerModule = false ∧ isKnownModule pkg imp.module = true)
    (.foreignImport inv.moduleName imp.module)
  ensure (importRoleAllowed inv.role (roleOfModule pkg imp.module) = true)
    (.forbiddenImportDirection inv.moduleName inv.role.render imp.module
      (roleOfModule pkg imp.module).render)

def validateImports (pkg : PackageAuditInput) (inv : ModuleInventory) : Except AuditFailure Unit := do
  checkAll inv.imports (validateSingleImport pkg inv)
  ensure (importClosureContains pkg inv.moduleName inv.moduleName = false)
    (.importCycle inv.moduleName)

/-! ## Dependency policy: `sorryAx`, native reduction, compiler trust, axioms -/

/-- `EqBool e Bool.true` with closed `e`: the only statement shape of the axioms that
`Lean.Meta.nativeEqTrue` adds for `native_decide` and `bv_decide`. -/
def isValidNativeAxiomType (t : ExprSkeleton) : Bool :=
  match t with
  | .app (.app (.const f) e) (.const b) =>
    decide (f = SymName.eqBoolName ∧ b = SymName.boolTrueName) && e.closedBelow 0
  | _ => false

/-- Evaluation as compiled code would do it: unfold definitions *and* opaque constants
and β-reduce every redex. Returns `none` when fuel runs out so that native-axiom
refutation fails closed instead of silently passing a deep or cyclic chain. -/
def whnfAllowOpaqueOpt (env : KernelEnv) : Nat → ExprSkeleton → Option ExprSkeleton
  | 0, _ => none
  | fuel + 1, .const c =>
    match env.lookup c with
    | some ci =>
      if ci.kind = .defnDecl ∨ ci.kind = .opaqueDecl then
        match ci.value? with
        | some v => whnfAllowOpaqueOpt env fuel v
        | none => some (.const c)
      else some (.const c)
    | none => some (.const c)
  | fuel + 1, .app f a =>
    match whnfAllowOpaqueOpt env fuel f with
    | none => none
    | some (.lam _ b) => whnfAllowOpaqueOpt env fuel (b.instantiate a)
    | some f' => some (.app f' a)
  | _ + 1, e => some e

/-- Total AST size of definition and opaque bodies in an environment, used to scale
runtime-faithful reduction fuel across chained helper definitions. -/
def envBodySize (env : KernelEnv) : Nat :=
  (env.map (fun p =>
    if p.2.kind = .defnDecl ∨ p.2.kind = .opaqueDecl then
      (p.2.value?.map ExprSkeleton.size).getD 0
    else 0)).sum

/-- Total evaluation wrapper returning the weak head normal form, or `e` on fuel exhaustion. -/
def whnfAllowOpaque (env : KernelEnv) (fuel : Nat) (e : ExprSkeleton) : ExprSkeleton :=
  (whnfAllowOpaqueOpt env fuel e).getD e

/-- A native axiom whose left-hand side evaluates to `Bool.false` — or fails to reach
weak head normal form within the scaled budget — is rejected (fail-closed). -/
def nativeAxiomRefutedByKernel (env : KernelEnv) (t : ExprSkeleton) : Bool :=
  match t with
  | .app (.app _ e) _ =>
    match whnfAllowOpaqueOpt env (64 + 4 * e.size + 2 * env.length + 2 * envBodySize env) e with
    | none => true
    | some (.const b) => decide (b = SymName.boolFalseName)
    | some _ => false
  | _ => false

/-- `--provisional` admits a native axiom only if it has the strictly interior `._native.`
shape `<decl>._native.<tactic>.ax_<n>`, is an axiom of a proof module, has the closed
`EqBool e Bool.true` type shape, and is not refuted by runtime-faithful reduction. -/
def checkNativeDep (cfg : AuditConfig) (pkg : PackageAuditInput) (env : KernelEnv)
    (user dep : SymName) (dci : ConstantRecord) : Except AuditFailure Unit := do
  ensure (cfg.allowProvisionalNative = true ∧ dep.isProvisionalNativeName = true ∧
      dci.kind = .axiomDecl ∧ roleOfConst pkg dep dci = .proof)
    (.forbiddenNativeReductionAxiom user dep)
  ensure (isValidNativeAxiomType dci.type = true ∧ nativeAxiomRefutedByKernel env dci.type = false)
    (.invalidNativeAxiomType user dep)

/-- Any other axiom must be foundational and declared by the foundation, or, in
conditional mode, declared by an `Assumptions.*` module. -/
def checkAxiomDep (cfg : AuditConfig) (pkg : PackageAuditInput) (user dep : SymName)
    (dci : ConstantRecord) : Except AuditFailure Unit :=
  ensure (dci.kind ≠ .axiomDecl ∨
      (dep.isFoundationalAxiom = true ∧ roleOfConst pkg dep dci = .foundation) ∨
      (cfg.allowAssumptions = true ∧ roleOfConst pkg dep dci = .assumptions))
    (.forbiddenAxiom user dep (declaringModuleName pkg dep dci))

/-- Policy for one dependency. `sorryAx` and `Lean.trustCompiler` are banned in every mode. -/
def checkDepPolicy (cfg : AuditConfig) (pkg : PackageAuditInput) (env : KernelEnv)
    (user dep : SymName) (dci : ConstantRecord) : Except AuditFailure Unit := do
  ensure (dep ≠ SymName.sorryAxName) (.forbiddenAxiom user dep (declaringModuleName pkg dep dci))
  ensure (dep.isCompilerTrustAxiom = false) (.forbiddenNativeReductionAxiom user dep)
  if dep.isNativeReductionAxiom then checkNativeDep cfg pkg env user dep dci
  else checkAxiomDep cfg pkg user dep dci

theorem checkDepPolicy_ok {cfg : AuditConfig} {pkg : PackageAuditInput} {env : KernelEnv}
    {user dep : SymName} {dci : ConstantRecord}
    (h : checkDepPolicy cfg pkg env user dep dci = .ok ()) :
    dep ≠ SymName.sorryAxName ∧ dep.isCompilerTrustAxiom = false ∧
    (dep.isNativeReductionAxiom = true → cfg.allowProvisionalNative = true) ∧
    (dep.isNativeReductionAxiom = false → dci.kind = .axiomDecl →
      (dep.isFoundationalAxiom = true ∧ roleOfConst pkg dep dci = .foundation) ∨
      (cfg.allowAssumptions = true ∧ roleOfConst pkg dep dci = .assumptions)) := by
  simp only [checkDepPolicy, bindUnit_ok_iff, ensure_ok_iff] at h
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, h2, ?_, ?_⟩
  · intro hn
    simp only [hn, ↓reduceIte, checkNativeDep, bindUnit_ok_iff, ensure_ok_iff] at h3
    exact h3.1.1
  · intro hn hk
    simp only [hn, Bool.false_eq_true, ↓reduceIte, checkAxiomDep, ensure_ok_iff] at h3
    rcases h3 with h3 | h3
    · exact absurd hk h3
    · exact h3

/-- A clean dependency: resolved, safe, not `sorryAx`, not native reduction or compiler
trust, and if an axiom then a foundational one declared by the foundation. -/
def CleanDep (pkg : PackageAuditInput) (env : KernelEnv) (dep : SymName) : Prop :=
  ∃ ci, env.lookup dep = some ci ∧ ci.safety = .safe ∧ dep ≠ SymName.sorryAxName ∧
    dep.isCompilerTrustAxiom = false ∧ dep.isNativeReductionAxiom = false ∧
    (ci.kind = .axiomDecl → dep.isFoundationalAxiom = true ∧ roleOfConst pkg dep ci = .foundation)

def checkClosureDep (cfg : AuditConfig) (pkg : PackageAuditInput) (env : KernelEnv)
    (user dep : SymName) : Except AuditFailure Unit :=
  match env.lookup dep with
  | none => .error (.unknownConstant dep)
  | some dci => do
    ensure (dci.safety = .safe) (.unsafeOrPartialDecl (declaringModuleName pkg dep dci) dep)
    checkDepPolicy cfg pkg env user dep dci

theorem checkClosureDep_ok {cfg : AuditConfig} {pkg : PackageAuditInput} {env : KernelEnv}
    {user dep : SymName} (h : checkClosureDep cfg pkg env user dep = .ok ()) :
    ∃ ci, env.lookup dep = some ci ∧ ci.safety = .safe ∧
      checkDepPolicy cfg pkg env user dep ci = .ok () := by
  unfold checkClosureDep at h
  split at h
  · cases h
  · rename_i dci hdci
    simp only [bindUnit_ok_iff, ensure_ok_iff] at h
    exact ⟨dci, hdci, h.1, h.2⟩

/-- An axiom that is neither native nor a foundational axiom of the foundation. -/
def isAssumptionDep (pkg : PackageAuditInput) (env : KernelEnv) (dep : SymName) : Bool :=
  match env.lookup dep with
  | some ci =>
    decide (ci.kind = .axiomDecl) && !dep.isNativeReductionAxiom &&
      !(dep.isFoundationalAxiom && decide (roleOfConst pkg dep ci = .foundation))
  | none => false

/-- An accepted dependency is clean, or it is recorded as provisional or as an assumption. -/
theorem cleanDep_or_recorded {cfg : AuditConfig} {pkg : PackageAuditInput} {env : KernelEnv}
    {user dep : SymName} (h : checkClosureDep cfg pkg env user dep = .ok ()) :
    CleanDep pkg env dep ∨ dep.isNativeReductionAxiom = true ∨ isAssumptionDep pkg env dep = true := by
  obtain ⟨ci, hci, hsafe, hpol⟩ := checkClosureDep_ok h
  obtain ⟨h1, h2, _, h4⟩ := checkDepPolicy_ok hpol
  cases hn : dep.isNativeReductionAxiom with
  | true => exact Or.inr (Or.inl rfl)
  | false =>
    by_cases hclean : ci.kind = .axiomDecl →
        dep.isFoundationalAxiom = true ∧ roleOfConst pkg dep ci = .foundation
    · exact Or.inl ⟨ci, hci, hsafe, h1, h2, hn, hclean⟩
    · refine Or.inr (Or.inr ?_)
      have hk : ci.kind = .axiomDecl := Classical.byContradiction (fun hk => hclean (fun h => absurd h hk))
      have hnf : ¬ (dep.isFoundationalAxiom = true ∧ roleOfConst pkg dep ci = .foundation) :=
        fun hf => hclean (fun _ => hf)
      simp only [isAssumptionDep, hci, hk, hn, decide_true, Bool.not_false, Bool.true_and,
        Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not]
      by_cases hf : dep.isFoundationalAxiom = true
      · exact Or.inr (fun hr => hnf ⟨hf, hr⟩)
      · exact Or.inl (by simpa using hf)

theorem cleanDep_of_unconditional {cfg : AuditConfig} {pkg : PackageAuditInput} {env : KernelEnv}
    {user dep : SymName} (ha : cfg.allowAssumptions = false) (hp : cfg.allowProvisionalNative = false)
    (h : checkClosureDep cfg pkg env user dep = .ok ()) : CleanDep pkg env dep := by
  obtain ⟨ci, hci, hsafe, hpol⟩ := checkClosureDep_ok h
  obtain ⟨h1, h2, h3, h4⟩ := checkDepPolicy_ok hpol
  have hn : dep.isNativeReductionAxiom = false := by
    cases hn : dep.isNativeReductionAxiom with
    | false => rfl
    | true => rw [h3 hn] at hp; cases hp
  refine ⟨ci, hci, hsafe, h1, h2, hn, fun hk => ?_⟩
  rcases h4 hn hk with hf | hf
  · exact hf
  · rw [ha] at hf
    cases hf.1

/-- The direct closure audit of one root: walk every declaration edge (the artifact's
`cachedExportedAxioms` is never consulted), then check every name reached. -/
def auditDirectClosure (cfg : AuditConfig) (pkg : PackageAuditInput) (env : KernelEnv)
    (root : SymName) : Except AuditFailure (List SymName) := do
  let visited ← walkGraph env root closureExpand (closureFuel env) [root] []
  checkAll visited (checkClosureDep cfg pkg env root)
  .ok visited

theorem auditDirectClosure_ok {cfg : AuditConfig} {pkg : PackageAuditInput} {env : KernelEnv}
    {root : SymName} {visited : List SymName}
    (h : auditDirectClosure cfg pkg env root = .ok visited) :
    (∀ dep, DepReaches env root dep → dep ∈ visited) ∧
      (∀ dep ∈ visited, checkClosureDep cfg pkg env root dep = .ok ()) := by
  simp only [auditDirectClosure, bind_ok_iff, Except.ok.injEq] at h
  obtain ⟨v, hw, u, hall, rfl⟩ := h
  exact ⟨fun dep hr => (walkGraph_reaches_subset hw).1 root List.mem_cons_self dep hr,
    checkAll_ok_iff.mp hall⟩

/-- Closure soundness over genuine reachability: in unconditional mode, everything a root
transitively depends on is clean. -/
theorem validPackage_axiom_closure_sound {cfg : AuditConfig} {pkg : PackageAuditInput}
    {allEnv : KernelEnv} {root : SymName} {reached : List SymName}
    (ha : cfg.allowAssumptions = false) (hp : cfg.allowProvisionalNative = false)
    (h : auditDirectClosure cfg pkg allEnv root = .ok reached) :
    ∀ dep, DepReaches allEnv root dep → CleanDep pkg allEnv dep := by
  intro dep hr
  obtain ⟨hreach, hall⟩ := auditDirectClosure_ok h
  exact cleanDep_of_unconditional ha hp (hall dep (hreach dep hr))

def classifyVerifyItem (provisional assumptions : List SymName) : VerifyItemStatus :=
  match provisional, assumptions with
  | [], [] => .verifiedUnconditional
  | [], _ :: _ => .verifiedConditional
  | _ :: _, [] => .provisionalNative
  | _ :: _, _ :: _ => .provisionalNativeConditional

theorem classifyVerifyItem_unconditional {p a : List SymName} :
    classifyVerifyItem p a = .verifiedUnconditional ↔ p = [] ∧ a = [] := by
  cases p <;> cases a <;> simp [classifyVerifyItem]

/-- Classify one verify root from its own closure walk: no state is shared between roots. -/
def buildVerifyItemReport (cfg : AuditConfig) (pkg : PackageAuditInput) (env : KernelEnv)
    (root : SymName) : Except AuditFailure VerifyItemReport :=
  match auditDirectClosure cfg pkg env root with
  | .error e => .error e
  | .ok visited =>
    .ok { root := root
          status := classifyVerifyItem (visited.filter (fun d => d.isNativeReductionAxiom))
            (visited.filter (isAssumptionDep pkg env))
          reachedProvisional := visited.filter (fun d => d.isNativeReductionAxiom)
          reachedAssumptions := visited.filter (isAssumptionDep pkg env) }

theorem buildVerifyItemReport_ok {cfg : AuditConfig} {pkg : PackageAuditInput} {env : KernelEnv}
    {root : SymName} {rep : VerifyItemReport}
    (h : buildVerifyItemReport cfg pkg env root = .ok rep) :
    rep.root = root ∧ ∃ visited, auditDirectClosure cfg pkg env root = .ok visited ∧
      rep.reachedProvisional = visited.filter (fun d => d.isNativeReductionAxiom) ∧
      rep.reachedAssumptions = visited.filter (isAssumptionDep pkg env) ∧
      rep.status = classifyVerifyItem rep.reachedProvisional rep.reachedAssumptions := by
  unfold buildVerifyItemReport at h
  split at h
  · cases h
  · rename_i visited hv
    cases h
    exact ⟨rfl, visited, hv, rfl, rfl, rfl⟩

/-! ## Module declarations: `unsafe`, `partial`, `_unsafe_rec`, declared axioms -/

/-- An `_unsafe_rec` companion is excused from replay only: every declaration in its
transitive dependency closure must resolve, must not be `unsafe`, may be `partial` only
if it is the companion itself, and obeys the same axiom policy as everything else. -/
def checkUnsafeRecEdge (cfg : AuditConfig) (pkg : PackageAuditInput) (env : KernelEnv)
    (user dep : SymName) : Except AuditFailure Unit :=
  match env.lookup dep with
  | none => .error (.unknownConstant dep)
  | some dci => do
    ensure (dci.safety ≠ .unsafeDecl ∧ (dci.safety = .safe ∨ dep = user))
      (.unsafeOrPartialDecl (declaringModuleName pkg dep dci) dep)
    checkDepPolicy cfg pkg env user dep dci

/-- An `_unsafe_rec` companion in a `.test` module must additionally obey the test-module
closure policy (no `sorryAx`, no native or compiler-trust axioms, no foreign assumptions). -/
def checkUnsafeRecTestEdge (cfg : AuditConfig) (pkg : PackageAuditInput) (env : KernelEnv)
    (testMod user dep : SymName) : Except AuditFailure Unit :=
  match env.lookup dep with
  | none => .error (.unknownConstant dep)
  | some dci => do
    ensure (dci.safety ≠ .unsafeDecl ∧ (dci.safety = .safe ∨ dep = user))
      (.unsafeOrPartialDecl (declaringModuleName pkg dep dci) dep)
    ensure (dep ≠ SymName.sorryAxName)
      (.forbiddenAxiom user dep (declaringModuleName pkg dep dci))
    ensure (dep.isCompilerTrustAxiom = false ∧ dep.isNativeReductionAxiom = false)
      (.forbiddenNativeReductionAxiom user dep)
    ensure (dci.kind ≠ .axiomDecl ∨
        (dep.isFoundationalAxiom = true ∧ roleOfConst pkg dep dci = .foundation) ∨
        (cfg.allowLocalTestAxioms = true ∧ declaringModuleName pkg dep dci = testMod))
      (.testModuleForeignAxiom testMod user dep)

def auditDeclSafety (cfg : AuditConfig) (pkg : PackageAuditInput) (env : KernelEnv)
    (inv : ModuleInventory) (ci : ConstantRecord) : Except AuditFailure Unit :=
  if isCodegenUnsafeRecInMod inv ci then
    match walkGraph env ci.name closureExpand (closureFuel env) [ci.name] [] with
    | .error e => .error e
    | .ok visited =>
      if inv.role = .test then
        checkAll visited (checkUnsafeRecTestEdge cfg pkg env inv.moduleName ci.name)
      else
        checkAll visited (checkUnsafeRecEdge cfg pkg env ci.name)
  else ensure (ci.safety = .safe) (.unsafeOrPartialDecl inv.moduleName ci.name)

/-- Every axiom a module declares is checked, referenced or not. A test module may keep
ordinary local axioms when the configuration allows them. -/
def checkDeclaredAxiom (cfg : AuditConfig) (pkg : PackageAuditInput) (env : KernelEnv)
    (inv : ModuleInventory) (ci : ConstantRecord) : Except AuditFailure Unit :=
  if ci.kind = .axiomDecl ∧ ¬ (inv.role = .test ∧ cfg.allowLocalTestAxioms = true ∧
      ci.name.isNativeReductionAxiom = false ∧ ci.name.isCompilerTrustAxiom = false ∧
      ci.name ≠ SymName.sorryAxName) then
    checkDepPolicy cfg pkg env ci.name ci.name ci
  else .ok ()

def auditModuleDecl (cfg : AuditConfig) (pkg : PackageAuditInput) (env : KernelEnv)
    (inv : ModuleInventory) (ci : ConstantRecord) : Except AuditFailure Unit := do
  auditDeclSafety cfg pkg env inv ci
  checkDeclaredAxiom cfg pkg env inv ci

/-! ## References, extension entries, and reserved origins stay inside the import closure -/

/-- A reference to a constant of another package module needs that module in the
referring module's import closure. -/
def checkReference (pkg : PackageAuditInput) (inv : ModuleInventory) (user dep : SymName) :
    Except AuditFailure Unit :=
  match moduleOfConst? pkg dep with
  | some target =>
    ensure (moduleVisibleFrom pkg inv target.moduleName = true)
      (.referenceOutsideImportClosure inv.moduleName user dep target.moduleName)
  | none => .ok ()

def auditDeclReferences (pkg : PackageAuditInput) (inv : ModuleInventory) (ci : ConstantRecord) :
    Except AuditFailure Unit :=
  match ci.declarationEdges with
  | .error e => .error e
  | .ok edges => checkAll edges (checkReference pkg inv ci.name)

def auditReferenceImports (pkg : PackageAuditInput) (inv : ModuleInventory) :
    Except AuditFailure Unit :=
  checkAll inv.constants (auditDeclReferences pkg inv)

/-- A scope namespace that names a package module must be visible. -/
def checkScopeModule (pkg : PackageAuditInput) (inv : ModuleInventory) (user ns : SymName) :
    Except AuditFailure Unit :=
  ensure ((findModule? pkg ns).isNone = true ∨ moduleVisibleFrom pkg inv ns = true)
    (.referenceOutsideImportClosure inv.moduleName user user ns)

def auditExtReferences (pkg : PackageAuditInput) (inv : ModuleInventory) (ext : EnvExtEntry) :
    Except AuditFailure Unit := do
  checkAll ext.referencedConstants
    (checkReference pkg inv (ext.referencedConstants.headD .anonymous))
  checkAll ext.referencedModules
    (checkScopeModule pkg inv (ext.referencedConstants.headD .anonymous))

def auditExtReferenceImports (pkg : PackageAuditInput) (inv : ModuleInventory) :
    Except AuditFailure Unit :=
  checkAll inv.extEntries (auditExtReferences pkg inv)

/-- A record may claim another origin module only as a reserved auxiliary declaration of
a known module, and a package module it names must be visible. -/
def auditReservedOrigin (pkg : PackageAuditInput) (inv : ModuleInventory) (ci : ConstantRecord) :
    Except AuditFailure Unit :=
  match ci.originModule with
  | none => .ok ()
  | some o =>
    if o = inv.moduleName then .ok ()
    else do
      ensure (ci.name.isReservedAuxName = true ∧
          ((findModule? pkg o).isSome = true ∨ o ∈ baseModuleNames pkg))
        (.reservedOriginMissingSibling inv.moduleName ci.name o)
      ensure ((findModule? pkg o).isNone = true ∨ moduleVisibleFrom pkg inv o = true)
        (.referenceOutsideImportClosure inv.moduleName ci.name ci.name o)

/-! ## Verify roots, claim roots, and statement origins -/

/-- Roots are listed once, and every verify module's `verified` theorem is listed: a
verify module that is merely loaded is not allowed to ride along unaudited. -/
def auditVerifyModuleCoverage (pkg : PackageAuditInput) : Except AuditFailure Unit := do
  ensureNodup pkg.verifyRoots (fun d => .invalidVerifyRoot d "duplicate verify root")
  ensureNodup pkg.claimRoots (fun d => .invalidVerifyRoot d "duplicate claim root")
  checkAll pkg.modules (fun inv =>
    ensure (inv.role ≠ .verify ∨ inv.moduleName.verifiedRoot ∈ pkg.verifyRoots)
      (.invalidVerifyRoot inv.moduleName.verifiedRoot
        "verify module root is not listed in verifyRoots"))

def stopsStatementUnfolding : ModuleRole → Bool
  | .foundation => true
  | .trusted => true
  | _ => false

/-- Statement walk: a theory declaration is a leak; foundation and trusted declarations
are opaque vocabulary; everything else, definitions modules included, is unfolded. -/
def statementExpand (pkg : PackageAuditInput) (root n : SymName) (ci : ConstantRecord) :
    Except AuditFailure (List SymName) :=
  if roleOfConst pkg n ci = .theory then
    .error (.statementTheoryLeak root n (declaringModuleName pkg n ci))
  else if stopsStatementUnfolding (roleOfConst pkg n ci) then .ok []
  else ci.declarationEdges

def walkStatementOrigins (pkg : PackageAuditInput) (env : KernelEnv) (root : SymName)
    (typeEdges : List SymName) : Except AuditFailure (List SymName) :=
  walkGraph env root (statementExpand pkg root) (typeEdges.length + closureFuel env) typeEdges []

/-- The statement walk never runs out of its budget. -/
theorem walkStatementOrigins_never_exhausts_fuel (pkg : PackageAuditInput) (allEnv : KernelEnv)
    (rootName : SymName) (typeEdges : List SymName) (r p : SymName) :
    walkStatementOrigins pkg allEnv rootName typeEdges ≠ .error (.closureFuelExhausted r p) := by
  refine walkGraph_never_exhausts_fuel ?_ ?_ (by simp [closureFuel]) r p
  · intro n ci edges h
    unfold statementExpand at h
    split at h
    · cases h
    · split at h
      · cases h; simp
      · exact closureExpand_bound n ci edges h
  · intro n ci r p h
    unfold statementExpand at h
    split at h
    · cases h
    · split at h
      · cases h
      · exact closureExpand_no_exhaust n ci r p h

/-- Nothing reachable from a statement's constants by unfolding non-foundation,
non-trusted declarations is declared by a theory module. -/
theorem statementOrigins_sound {pkg : PackageAuditInput} {allEnv : KernelEnv} {root : SymName}
    {typeEdges visited : List SymName}
    (h : walkStatementOrigins pkg allEnv root typeEdges = .ok visited) :
    ∀ r ∈ typeEdges, ∀ d, GraphReaches allEnv (statementExpand pkg root) r d →
      ∃ dCi, allEnv.lookup d = some dCi ∧ roleOfConst pkg d dCi ≠ .theory := by
  intro r hr d hreach
  obtain ⟨hsub, hcl⟩ := walkGraph_reaches_subset h
  obtain ⟨ci, edges, hci, hexp, _⟩ := hcl d (hsub r hr d hreach)
  refine ⟨ci, hci, fun hth => ?_⟩
  simp [statementExpand, hth] at hexp

def isVerifyRootLocation (pkg : PackageAuditInput) (root : SymName) : Bool :=
  pkg.modules.any (fun inv =>
    decide (inv.role = .verify ∧ root = inv.moduleName.verifiedRoot ∧ root ∈ inv.constNames))

def auditStatement (pkg : PackageAuditInput) (env : KernelEnv) (root : SymName)
    (ci : ConstantRecord) : Except AuditFailure Unit :=
  match walkStatementOrigins pkg env root ci.type.usedConstants with
  | .ok _ => .ok ()
  | .error e => .error e

/-- A verify root is the theorem `<Verify module>.verified`, declared there, stating a
`Trusted.VerificationResult`, with no theory declaration behind its statement. -/
def auditVerifyRoot (pkg : PackageAuditInput) (env : KernelEnv) (root : SymName) :
    Except AuditFailure Unit :=
  match env.lookup root with
  | none => .error (.unknownConstant root)
  | some ci => do
    ensure (ci.kind = .thmDecl) (.invalidVerifyRoot root "verify root must be a theorem")
    ensure (ci.type.getAppFn = .const SymName.verificationResultName)
      (.invalidVerifyRoot root "verify root statement must be a Trusted.VerificationResult")
    ensure (isVerifyRootLocation pkg root = true)
      (.invalidVerifyRoot root "verify root must be <Verify module>.verified")
    auditStatement pkg env root ci

/-- A claim root is a theorem outside theory and test modules with a clean statement. -/
def auditClaimRoot (pkg : PackageAuditInput) (env : KernelEnv) (root : SymName) :
    Except AuditFailure Unit :=
  match env.lookup root with
  | none => .error (.unknownConstant root)
  | some ci => do
    ensure (ci.kind = .thmDecl) (.invalidVerifyRoot root "claim root must be a theorem")
    ensure (roleOfConst pkg root ci ≠ .theory ∧ roleOfConst pkg root ci ≠ .test)
      (.invalidVerifyRoot root "claim root declared in a theory or test module")
    auditStatement pkg env root ci

/-! ## Closure roots and test modules -/

/-- Every declaration of a non-test module is a closure root, referenced or not. -/
def closureRootsOfModule (inv : ModuleInventory) : List SymName :=
  if inv.role = .test then [] else (replayableConstants inv).map (·.name)

def closureRootsOfPackage (pkg : PackageAuditInput) : List SymName :=
  pkg.modules.flatMap closureRootsOfModule

def reachedAxiomsOf (env : KernelEnv) (names : List SymName) : List SymName :=
  (names.filter (fun n =>
    match env.lookup n with
    | some ci => decide (ci.kind = .axiomDecl)
    | none => false)).eraseDups

def auditPackageClosures (cfg : AuditConfig) (pkg : PackageAuditInput) (env : KernelEnv) :
    Except AuditFailure (List SymName) :=
  match collectEach (closureRootsOfPackage pkg ++ pkg.verifyRoots ++ pkg.claimRoots)
      (auditDirectClosure cfg pkg env) with
  | .ok visitedLists => .ok (reachedAxiomsOf env visitedLists.flatten)
  | .error e => .error e

/-- A clean dependency of a test module: as `CleanDep`, except that an axiom may also be
one the test module itself declares. -/
def CleanTestDep (pkg : PackageAuditInput) (env : KernelEnv) (testMod dep : SymName) : Prop :=
  ∃ ci, env.lookup dep = some ci ∧ ci.safety = .safe ∧ dep ≠ SymName.sorryAxName ∧
    dep.isCompilerTrustAxiom = false ∧ dep.isNativeReductionAxiom = false ∧
    (ci.kind = .axiomDecl →
      (dep.isFoundationalAxiom = true ∧ roleOfConst pkg dep ci = .foundation) ∨
      declaringModuleName pkg dep ci = testMod)

/-- Stricter than `TrustedBoundary.downstreamAudit`: native axioms are refused in tests too,
and local test axioms are admitted only when `cfg.allowLocalTestAxioms = true`. -/
def checkTestDep (cfg : AuditConfig) (pkg : PackageAuditInput) (env : KernelEnv)
    (testMod user dep : SymName) : Except AuditFailure Unit :=
  match env.lookup dep with
  | none => .error (.unknownConstant dep)
  | some dci => do
    ensure (dci.safety = .safe) (.unsafeOrPartialDecl (declaringModuleName pkg dep dci) dep)
    ensure (dep ≠ SymName.sorryAxName)
      (.forbiddenAxiom user dep (declaringModuleName pkg dep dci))
    ensure (dep.isCompilerTrustAxiom = false ∧ dep.isNativeReductionAxiom = false)
      (.forbiddenNativeReductionAxiom user dep)
    ensure (dci.kind ≠ .axiomDecl ∨
        (dep.isFoundationalAxiom = true ∧ roleOfConst pkg dep dci = .foundation) ∨
        (cfg.allowLocalTestAxioms = true ∧ declaringModuleName pkg dep dci = testMod))
      (.testModuleForeignAxiom testMod user dep)

def auditTestDecl (cfg : AuditConfig) (pkg : PackageAuditInput) (env : KernelEnv)
    (inv : ModuleInventory) (ci : ConstantRecord) : Except AuditFailure Unit :=
  match walkGraph env ci.name closureExpand (closureFuel env) [ci.name] [] with
  | .error e => .error e
  | .ok visited => checkAll visited (checkTestDep cfg pkg env inv.moduleName ci.name)

def auditTestModule (cfg : AuditConfig) (pkg : PackageAuditInput) (env : KernelEnv)
    (inv : ModuleInventory) : Except AuditFailure Unit :=
  if inv.role = .test then checkAll (replayableConstants inv) (auditTestDecl cfg pkg env inv)
  else .ok ()

def auditTestModuleClosures (cfg : AuditConfig) (pkg : PackageAuditInput) (env : KernelEnv) :
    Except AuditFailure Unit :=
  checkAll pkg.modules (auditTestModule cfg pkg env)

/-! ## The policy stage and the pipeline -/

/-- With `requireSources` (the default) every module must supply its source text. -/
def auditModuleSource (cfg : AuditConfig) (inv : ModuleInventory) : Except AuditFailure Unit :=
  match inv.sourceText? with
  | none => ensure (cfg.requireSources = false) (.missingSourceText inv.moduleName)
  | some src => SourceScanner.scanSourceChars cfg inv.moduleName inv.role src

def auditModulePolicy (cfg : AuditConfig) (pkg : PackageAuditInput) (env : KernelEnv)
    (inv : ModuleInventory) : Except AuditFailure Unit := do
  validateModuleExtensions inv
  auditShadowing pkg inv
  validateImports pkg inv
  auditModuleSource cfg inv
  checkAll inv.constants (auditModuleDecl cfg pkg env inv)
  auditReferenceImports pkg inv
  auditExtReferenceImports pkg inv
  checkAll inv.constants (auditReservedOrigin pkg inv)

structure PolicyOutcome where
  reachedAxioms : List SymName
  itemReports : List VerifyItemReport

/-- The axiom and tamper policy over a structurally valid package. -/
def validateAxiomAndTamperPolicy (cfg : AuditConfig) (pkg : PackageAuditInput) :
    Except AuditFailure PolicyOutcome := do
  checkAll pkg.modules (auditModulePolicy cfg pkg (packageEnv pkg))
  auditVerifyModuleCoverage pkg
  let reached ← auditPackageClosures cfg pkg (packageEnv pkg)
  auditTestModuleClosures cfg pkg (packageEnv pkg)
  checkAll pkg.verifyRoots (auditVerifyRoot pkg (packageEnv pkg))
  checkAll pkg.claimRoots (auditClaimRoot pkg (packageEnv pkg))
  let reports ← collectEach pkg.verifyRoots (buildVerifyItemReport cfg pkg (packageEnv pkg))
  .ok { reachedAxioms := reached, itemReports := reports }

/-- May replay admit this declaration if it is an axiom? Only what the policy admits
(never `sorryAx`, never `Lean.trustCompiler`, and only strictly interior `._native.`
names for provisional proof axioms). -/
def allowReplayAxiom (cfg : AuditConfig) (pkg : PackageAuditInput) (ci : ConstantRecord) : Bool :=
  decide (ci.name ≠ SymName.sorryAxName) && !ci.name.isCompilerTrustAxiom &&
  ((cfg.allowAssumptions && !ci.name.isNativeReductionAxiom &&
      decide (roleOfConst pkg ci.name ci = .assumptions)) ||
   (cfg.allowProvisionalNative && ci.name.isProvisionalNativeName &&
      decide (roleOfConst pkg ci.name ci = .proof)) ||
   (cfg.allowLocalTestAxioms && !ci.name.isNativeReductionAxiom &&
      decide (roleOfConst pkg ci.name ci = .test)))

/-- Declarations to replay: everything except `_unsafe_rec` companions. -/
def collectReplayDecls (pkg : PackageAuditInput) : List ConstantRecord :=
  pkg.modules.flatMap replayableConstants

/-- The audit: structure, policy, then clean-environment replay of every declaration. -/
def auditAndReplayPackage (cfg : AuditConfig) (pkg : PackageAuditInput) :
    Except AuditFailure AuditCertificate := do
  validatePackageStructure pkg
  let outcome ← validateAxiomAndTamperPolicy cfg pkg
  let replayed ← replayCleanEnvOrdered (allowReplayAxiom cfg pkg) (mkBaseKernelEnv pkg.baseEnv)
    (collectReplayDecls pkg)
  .ok { importedEnv := packageEnv pkg, replayedEnv := replayed,
        reachedAxioms := outcome.reachedAxioms, itemReports := outcome.itemReports }

/-! ## What an accepted package guarantees -/

/-- The individual checks behind a successful policy stage. -/
structure PolicyFacts (cfg : AuditConfig) (pkg : PackageAuditInput)
    (reports : List VerifyItemReport) : Prop where
  modules : ∀ inv ∈ pkg.modules, auditModulePolicy cfg pkg (packageEnv pkg) inv = .ok ()
  coverage : auditVerifyModuleCoverage pkg = .ok ()
  closures : ∀ root ∈ closureRootsOfPackage pkg ++ pkg.verifyRoots ++ pkg.claimRoots,
    ∃ visited, auditDirectClosure cfg pkg (packageEnv pkg) root = .ok visited
  tests : ∀ inv ∈ pkg.modules, auditTestModule cfg pkg (packageEnv pkg) inv = .ok ()
  verifyRoots : ∀ r ∈ pkg.verifyRoots, auditVerifyRoot pkg (packageEnv pkg) r = .ok ()
  claimRoots : ∀ r ∈ pkg.claimRoots, auditClaimRoot pkg (packageEnv pkg) r = .ok ()
  reports : collectEach pkg.verifyRoots (buildVerifyItemReport cfg pkg (packageEnv pkg)) =
    .ok reports

theorem policy_facts {cfg : AuditConfig} {pkg : PackageAuditInput} {outcome : PolicyOutcome}
    (h : validateAxiomAndTamperPolicy cfg pkg = .ok outcome) :
    PolicyFacts cfg pkg outcome.itemReports := by
  simp only [validateAxiomAndTamperPolicy, bind_ok_iff, Except.ok.injEq] at h
  obtain ⟨u1, hmods, u2, hcov, reached, hclos, u3, htests, u4, hvr, u5, hcr, reports, hrep, rfl⟩ := h
  refine ⟨checkAll_ok_iff.mp hmods, hcov, ?_, checkAll_ok_iff.mp htests, checkAll_ok_iff.mp hvr,
    checkAll_ok_iff.mp hcr, hrep⟩
  intro root hroot
  unfold auditPackageClosures at hclos
  split at hclos
  · rename_i lists hl
    obtain ⟨visited, _, hv⟩ := collectEach_forall hl root hroot
    exact ⟨visited, hv⟩
  · cases hclos

theorem auditModulePolicy_ok {cfg : AuditConfig} {pkg : PackageAuditInput} {env : KernelEnv}
    {inv : ModuleInventory} (h : auditModulePolicy cfg pkg env inv = .ok ()) :
    validateModuleExtensions inv = .ok () ∧ auditShadowing pkg inv = .ok () ∧
    validateImports pkg inv = .ok () ∧ auditModuleSource cfg inv = .ok () ∧
    (∀ ci ∈ inv.constants, auditModuleDecl cfg pkg env inv ci = .ok ()) ∧
    auditReferenceImports pkg inv = .ok () ∧ auditExtReferenceImports pkg inv = .ok () ∧
    (∀ ci ∈ inv.constants, auditReservedOrigin pkg inv ci = .ok ()) := by
  simpa only [auditModulePolicy, bindUnit_ok_iff, checkAll_ok_iff] using h

/-- Everything a successful audit established, stage by stage. -/
theorem auditAndReplayPackage_facts {cfg : AuditConfig} {pkg : PackageAuditInput}
    {cert : AuditCertificate} (h : auditAndReplayPackage cfg pkg = .ok cert) :
    ((pkg.modules.map (·.moduleName)).Nodup ∧
      (∀ ci ∈ pkg.baseEnv, ci.name.isWellFormed = true) ∧
      (∀ inv ∈ pkg.modules, validateModuleRole inv = .ok () ∧ validateOleanParts inv = .ok () ∧
        validateReplayInventory inv = .ok () ∧ inv.moduleName ∉ baseModuleNames pkg) ∧
      (allDeclaredNames pkg).Nodup ∧
      (allExtraConstNames pkg).Nodup ∧
      (∀ inv ∈ pkg.modules, ∀ n ∈ inv.extraConstNames, n ∉ allDeclaredNames pkg)) ∧
    PolicyFacts cfg pkg cert.itemReports ∧
    replayCleanEnvOrdered (allowReplayAxiom cfg pkg) (mkBaseKernelEnv pkg.baseEnv)
      (collectReplayDecls pkg) = .ok cert.replayedEnv ∧
    cert.importedEnv = packageEnv pkg := by
  simp only [auditAndReplayPackage, bind_ok_iff, Except.ok.injEq] at h
  obtain ⟨u, hs, outcome, hp, replayed, hr, rfl⟩ := h
  exact ⟨validatePackageStructure_ok hs, policy_facts hp, hr, rfl⟩

/-- Module names are unique across the package. -/
theorem auditAndReplayPackage_modules_nodup {cfg : AuditConfig} {pkg : PackageAuditInput}
    {cert : AuditCertificate} (h : auditAndReplayPackage cfg pkg = .ok cert) :
    (pkg.modules.map ModuleInventory.moduleName).Nodup :=
  (auditAndReplayPackage_facts h).1.1

/-- Constant names are unique across the base environment and all modules: no import can
overwrite, subsume, or shadow another record. -/
theorem auditAndReplayPackage_global_names_nodup {cfg : AuditConfig} {pkg : PackageAuditInput}
    {cert : AuditCertificate} (h : auditAndReplayPackage cfg pkg = .ok cert) :
    (pkg.baseEnv.map ConstantRecord.name ++
      pkg.modules.flatMap ModuleInventory.constNames).Nodup :=
  (auditAndReplayPackage_facts h).1.2.2.2.1

theorem nodup_map_on {α β : Type} {f : α → β} {l : List α}
    (hnd : l.Nodup) (hinj : ∀ a ∈ l, ∀ b ∈ l, f a = f b → a = b) : (l.map f).Nodup := by
  induction l with
  | nil => exact List.nodup_nil
  | cons x xs ih =>
    simp only [List.nodup_cons] at hnd
    simp only [List.map_cons, List.nodup_cons]
    refine ⟨fun hm => ?_, ih hnd.2 (fun a ha b hb =>
      hinj a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb))⟩
    obtain ⟨y, hy, hfx⟩ := List.mem_map.mp hm
    have hxy := hinj x List.mem_cons_self y (List.mem_cons_of_mem _ hy) hfx.symm
    exact hnd.1 (hxy ▸ hy)

/-- Rendered dotted names are globally duplicate-free across the base environment and all
audited modules: no component-smuggling name can collide with another constant when
serialized or looked up by string. -/
theorem auditAndReplayPackage_global_toChars_nodup {cfg : AuditConfig}
    {pkg : PackageAuditInput} {cert : AuditCertificate}
    (h : auditAndReplayPackage cfg pkg = .ok cert) :
    ((pkg.baseEnv.map ConstantRecord.name ++
      pkg.modules.flatMap ModuleInventory.constNames).map SymName.toChars).Nodup := by
  obtain ⟨_, hbaseWf, hmods, hnd, _, _⟩ := (auditAndReplayPackage_facts h).1
  have hwf : ∀ n ∈ pkg.baseEnv.map ConstantRecord.name ++
      pkg.modules.flatMap ModuleInventory.constNames, n.isWellFormed = true := by
    intro n hn
    rcases List.mem_append.mp hn with hb | hm
    · obtain ⟨ci, hci, rfl⟩ := List.mem_map.mp hb
      exact hbaseWf ci hci
    · obtain ⟨inv, hinv, hni⟩ := List.mem_flatMap.mp hm
      exact (validateModuleDataKeys_ok_iff.mp (validateReplayInventory_ok (hmods inv hinv).2.2.1).1).2.1 n hni
  exact nodup_map_on hnd (fun a ha b hb heq => SymName.toChars_inj (hwf a ha) (hwf b hb) heq)

/-- `extraConstNames` are distinct across all modules and disjoint from every declared constant. -/
theorem auditAndReplayPackage_extraConstNames_nodup {cfg : AuditConfig} {pkg : PackageAuditInput}
    {cert : AuditCertificate} (h : auditAndReplayPackage cfg pkg = .ok cert) :
    (allExtraConstNames pkg).Nodup ∧
      ∀ inv ∈ pkg.modules, ∀ n ∈ inv.extraConstNames, n ∉ allDeclaredNames pkg :=
  ⟨(auditAndReplayPackage_facts h).1.2.2.2.2.1, (auditAndReplayPackage_facts h).1.2.2.2.2.2⟩

theorem moduleRole_facts {inv : ModuleInventory} (h : validateModuleRole inv = .ok ()) :
    inv.moduleName.isStdlibModule = false ∧ inv.moduleName.isLeanCompilerModule = false ∧
      inv.moduleName.isTrustedModule = false ∧
      roleMatchesModuleName inv.role inv.moduleName = true := by
  simp only [validateModuleRole, bindUnit_ok_iff, ensure_ok_iff] at h
  exact ⟨h.1.1, h.1.2, h.2.1, h.2.2.2⟩

/-- No audited module lives in the compiler's `Lean` namespace. -/
theorem auditAndReplayPackage_no_lean_modules {cfg : AuditConfig} {pkg : PackageAuditInput}
    {cert : AuditCertificate} (h : auditAndReplayPackage cfg pkg = .ok cert) :
    ∀ inv ∈ pkg.modules, ¬ SymName.isLeanCompilerModule inv.moduleName := by
  intro inv hinv
  simp [(moduleRole_facts ((auditAndReplayPackage_facts h).1.2.2.1 inv hinv).1).2.1]

/-- Verify roots and claim roots are listed once each. -/
theorem auditAndReplayPackage_roots_nodup {cfg : AuditConfig} {pkg : PackageAuditInput}
    {cert : AuditCertificate} (h : auditAndReplayPackage cfg pkg = .ok cert) :
    pkg.verifyRoots.Nodup ∧ pkg.claimRoots.Nodup := by
  have hc := (auditAndReplayPackage_facts h).2.1.coverage
  simp only [auditVerifyModuleCoverage, bindUnit_ok_iff, ensureNodup_ok_iff] at hc
  exact ⟨hc.1, hc.2.1⟩

/-- Every verify module's `verified` theorem is a listed verify root. -/
theorem auditAndReplayPackage_verify_modules_covered {cfg : AuditConfig}
    {pkg : PackageAuditInput} {cert : AuditCertificate}
    (h : auditAndReplayPackage cfg pkg = .ok cert) :
    ∀ inv ∈ pkg.modules, inv.role = .verify →
      inv.moduleName.verifiedRoot ∈ pkg.verifyRoots := by
  intro inv hinv hrole
  have hc := (auditAndReplayPackage_facts h).2.1.coverage
  simp only [auditVerifyModuleCoverage, bindUnit_ok_iff, checkAll_ok_iff, ensure_ok_iff] at hc
  rcases hc.2.2 inv hinv with hne | hmem
  · exact absurd hrole hne
  · exact hmem

/-- Import provenance, modifiers, role stratification, and acyclicity. -/
theorem auditAndReplayPackage_imports_sound {cfg : AuditConfig} {pkg : PackageAuditInput}
    {cert : AuditCertificate} (h : auditAndReplayPackage cfg pkg = .ok cert) :
    ∀ inv ∈ pkg.modules,
      ¬ SymName.isStdlibModule inv.moduleName ∧ ¬ SymName.isTrustedModule inv.moduleName ∧
      (∀ imp ∈ inv.imports, imp.importAll = false ∧ imp.isExported = true ∧
        (imp.isMeta = false ∨ imp.module = SymName.initModuleName) ∧
        imp.module.isLeanCompilerModule = false ∧ isKnownModule pkg imp.module = true ∧
        importRoleAllowed inv.role (roleOfModule pkg imp.module) = true) ∧
      ¬ ImportReaches pkg inv.moduleName inv.moduleName := by
  intro inv hinv
  obtain ⟨hstruct, hpol, _, _⟩ := auditAndReplayPackage_facts h
  have hr := moduleRole_facts (hstruct.2.2.1 inv hinv).1
  have hi := (auditModulePolicy_ok (hpol.modules inv hinv)).2.2.1
  simp only [validateImports, bindUnit_ok_iff, checkAll_ok_iff, ensure_ok_iff] at hi
  refine ⟨by simp [hr.1], by simp [hr.2.2.1], fun imp himp => ?_, fun hreach => ?_⟩
  · have h1 := hi.1 imp himp
    simp only [validateSingleImport, bindUnit_ok_iff, ensure_ok_iff] at h1
    exact ⟨h1.1, h1.2.1, h1.2.2.1, h1.2.2.2.1.1, h1.2.2.2.1.2, h1.2.2.2.2⟩
  · have hc := importClosureContains_iff.mpr hreach
    rw [hi.2] at hc
    cases hc

theorem auditDeclReferences_ok {pkg : PackageAuditInput} {inv : ModuleInventory}
    {ci : ConstantRecord} (h : auditDeclReferences pkg inv ci = .ok ()) :
    ∀ edges, ci.declarationEdges = .ok edges → ∀ dep ∈ edges, ∀ target,
      moduleOfConst? pkg dep = some target →
      target.moduleName = inv.moduleName ∨ ImportReaches pkg inv.moduleName target.moduleName := by
  intro edges he dep hdep target ht
  simp only [auditDeclReferences, he, checkAll_ok_iff] at h
  have h1 := h dep hdep
  simp only [checkReference, ht, ensure_ok_iff] at h1
  exact moduleVisibleFrom_iff.mp h1

/-- Every reference to a constant of another package module goes through the declared
import closure, so the import rules bind dependencies, not just headers. -/
theorem auditAndReplayPackage_references_within_imports {cfg : AuditConfig}
    {pkg : PackageAuditInput} {cert : AuditCertificate}
    (h : auditAndReplayPackage cfg pkg = .ok cert) :
    ∀ inv ∈ pkg.modules, ∀ ci ∈ inv.constants, ∀ edges,
      ConstantRecord.declarationEdges ci = .ok edges → ∀ dep ∈ edges, ∀ target,
      moduleOfConst? pkg dep = some target →
      target.moduleName = inv.moduleName ∨ ImportReaches pkg inv.moduleName target.moduleName := by
  intro inv hinv ci hci
  have hrefs := (auditModulePolicy_ok ((auditAndReplayPackage_facts h).2.1.modules inv hinv)).2.2.2.2.2.1
  exact auditDeclReferences_ok (checkAll_ok_iff.mp hrefs ci hci)

theorem importReaches_statementSide {pkg : PackageAuditInput}
    (himp : ∀ inv ∈ pkg.modules, ∀ imp ∈ inv.imports,
      importRoleAllowed inv.role (roleOfModule pkg imp.module) = true)
    {a b : SymName} (hr : ImportReaches pkg a b) :
    isStatementSideRole (roleOfModule pkg a) = true →
      isStatementSideRole (roleOfModule pkg b) = true := by
  have hstep : ∀ a b, b ∈ directImportsOf pkg a →
      isStatementSideRole (roleOfModule pkg a) = true →
      isStatementSideRole (roleOfModule pkg b) = true := by
    intro a b hb ha
    unfold directImportsOf at hb
    unfold roleOfModule at ha
    split at hb
    · rename_i inv hinv
      simp only [hinv] at ha
      obtain ⟨imp, himpmem, rfl⟩ := List.mem_map.mp hb
      exact importRoleAllowed_statementSide ha (himp inv (findModuleIn_spec hinv).1 imp himpmem)
    · simp at hb
  induction hr with
  | direct hb => exact hstep _ _ hb
  | step hc _ ih => exact fun ha => ih (hstep _ _ hc ha)

theorem roleOfModule_of_mem {pkg : PackageAuditInput}
    (hnd : (pkg.modules.map ModuleInventory.moduleName).Nodup) {inv : ModuleInventory}
    (h : inv ∈ pkg.modules) : roleOfModule pkg inv.moduleName = inv.role := by
  simp [roleOfModule, findModule?, findModuleIn_of_mem_nodup hnd h]

/-- Statement-side modules depend only on statement-side modules: no declaration of a
specification, definitions, or assumptions module mentions a proof, theory, verify, or
test declaration of the package. -/
theorem auditAndReplayPackage_statement_side_dependencies {cfg : AuditConfig}
    {pkg : PackageAuditInput} {cert : AuditCertificate}
    (h : auditAndReplayPackage cfg pkg = .ok cert) :
    ∀ inv ∈ pkg.modules, isStatementSideRole inv.role = true → ∀ ci ∈ inv.constants,
      ∀ edges, ConstantRecord.declarationEdges ci = .ok edges → ∀ dep ∈ edges, ∀ target,
      moduleOfConst? pkg dep = some target → isStatementSideRole target.role = true := by
  intro inv hinv hrole ci hci edges he dep hdep target ht
  have hnd := auditAndReplayPackage_modules_nodup h
  have hrt := roleOfModule_of_mem hnd (moduleOfConstIn_spec ht).1
  have hri := roleOfModule_of_mem hnd hinv
  rcases auditAndReplayPackage_references_within_imports h inv hinv ci hci edges he dep hdep
    target ht with heq | hreach
  · rw [← hrt, heq, hri]
    exact hrole
  · rw [← hrt]
    exact importReaches_statementSide
      (fun inv' hinv' imp himp =>
        ((auditAndReplayPackage_imports_sound h inv' hinv').2.2.1 imp himp).2.2.2.2.2)
      hreach (hri ▸ hrole)

/-- Every persisted extension entry owns its declaration, every constant and scope it names
lies inside the module's import closure, and statement-side modules only reference
statement-side targets and scopes. -/
theorem auditAndReplayPackage_ext_refs_within_imports {cfg : AuditConfig}
    {pkg : PackageAuditInput} {cert : AuditCertificate}
    (h : auditAndReplayPackage cfg pkg = .ok cert) :
    ∀ inv ∈ pkg.modules, ∀ ext ∈ inv.extEntries,
      (∀ d, ext.localDecl? = some d → d ∈ inv.constNames) ∧
      (∀ c ∈ ext.referencedConstants, ∀ target, moduleOfConst? pkg c = some target →
        (target.moduleName = inv.moduleName ∨
          ImportReaches pkg inv.moduleName target.moduleName) ∧
        (isStatementSideRole inv.role = true → isStatementSideRole target.role = true)) ∧
      (∀ ns ∈ ext.referencedModules, ∀ target, findModule? pkg ns = some target →
        (ns = inv.moduleName ∨ ImportReaches pkg inv.moduleName ns) ∧
        (isStatementSideRole inv.role = true → isStatementSideRole target.role = true)) := by
  intro inv hinv ext hext
  have hm := auditModulePolicy_ok ((auditAndReplayPackage_facts h).2.1.modules inv hinv)
  have hval := checkAll_ok_iff.mp hm.1 ext hext
  have href := checkAll_ok_iff.mp hm.2.2.2.2.2.2.1 ext hext
  have hnd := auditAndReplayPackage_modules_nodup h
  have hri := roleOfModule_of_mem hnd hinv
  have himp : ∀ inv' ∈ pkg.modules, ∀ imp ∈ inv'.imports,
      importRoleAllowed inv'.role (roleOfModule pkg imp.module) = true :=
    fun inv' hinv' imp himp =>
      ((auditAndReplayPackage_imports_sound h inv' hinv').2.2.1 imp himp).2.2.2.2.2
  simp only [auditExtReferences, bindUnit_ok_iff, checkAll_ok_iff] at href
  refine ⟨fun d hd => (validateSingleExtEntry_localDecl hval d hd).1, fun c hc target ht => ?_,
    fun ns hns target ht => ?_⟩
  · have h1 := href.1 c hc
    simp only [checkReference, ht, ensure_ok_iff] at h1
    have hvis := moduleVisibleFrom_iff.mp h1
    refine ⟨hvis, fun hrole => ?_⟩
    have hrt := roleOfModule_of_mem hnd (moduleOfConstIn_spec ht).1
    rcases hvis with heq | hreach
    · rw [← hrt, heq, hri]
      exact hrole
    · rw [← hrt]
      exact importReaches_statementSide himp hreach (hri ▸ hrole)
  · have h1 := href.2 ns hns
    simp only [checkScopeModule, ht, ensure_ok_iff] at h1
    have hvis : ns = inv.moduleName ∨ ImportReaches pkg inv.moduleName ns := by
      rcases h1 with h1 | h1
      · simp at h1
      · exact moduleVisibleFrom_iff.mp h1
    refine ⟨hvis, fun hrole => ?_⟩
    have hspec := findModuleIn_spec ht
    have hrt := roleOfModule_of_mem hnd hspec.1
    rcases hvis with heq | hreach
    · rw [← hrt, hspec.2, heq, hri]
      exact hrole
    · rw [← hrt, hspec.2]
      exact importReaches_statementSide himp hreach (hri ▸ hrole)

/-- Every instance, coercion, and reducibility entry refers to a declaration that the same
module declares, audits, and kernel-replays (never dangling, borrowed, or an un-replayed
`_unsafe_rec` companion). -/
theorem auditAndReplayPackage_ext_decls_declared {cfg : AuditConfig} {pkg : PackageAuditInput}
    {cert : AuditCertificate} (h : auditAndReplayPackage cfg pkg = .ok cert) :
    ∀ inv ∈ pkg.modules, ∀ ext ∈ inv.extEntries, ∀ d, ext.localDecl? = some d →
      d ∈ inv.constNames ∧
        ∃ ci ∈ inv.constants, ci.name = d ∧ cert.replayedEnv.lookup d = some ci := by
  intro inv hinv ext hext d hd
  have hfacts := auditAndReplayPackage_facts h
  have hm := auditModulePolicy_ok (hfacts.2.1.modules inv hinv)
  have hval := checkAll_ok_iff.mp hm.1 ext hext
  obtain ⟨hmem, hrep⟩ := validateSingleExtEntry_localDecl hval d hd
  obtain ⟨ci, hciRep, hname⟩ := List.mem_map.mp hrep
  have hci : ci ∈ inv.constants := (List.mem_filter.mp hciRep).1
  have hdecls := (replayCleanEnvOrdered_contains_decl hfacts.2.2.1).1
  have hlk := hdecls ci (List.mem_flatMap.mpr ⟨inv, hinv, hciRep⟩)
  exact ⟨hmem, ci, hci, hname, hname ▸ hlk⟩

/-- A record that claims a foreign origin is a reserved auxiliary declaration, and a
package module it names is in the claiming module's import closure. -/
theorem auditAndReplayPackage_reserved_origins_within_imports {cfg : AuditConfig}
    {pkg : PackageAuditInput} {cert : AuditCertificate}
    (h : auditAndReplayPackage cfg pkg = .ok cert) :
    ∀ inv ∈ pkg.modules, ∀ ci ∈ inv.constants, ∀ o, ci.originModule = some o →
      o ≠ inv.moduleName →
      ci.name.isReservedAuxName = true ∧
        ∀ originMod, findModule? pkg o = some originMod → ImportReaches pkg inv.moduleName o := by
  intro inv hinv ci hci o ho hne
  have hm := auditModulePolicy_ok ((auditAndReplayPackage_facts h).2.1.modules inv hinv)
  have h1 := hm.2.2.2.2.2.2.2 ci hci
  simp only [auditReservedOrigin, ho, hne, ↓reduceIte, bindUnit_ok_iff, ensure_ok_iff] at h1
  refine ⟨h1.1.1, fun originMod hom => ?_⟩
  rcases h1.2 with h2 | h2
  · simp [hom] at h2
  · rcases moduleVisibleFrom_iff.mp h2 with h3 | h3
    · exact absurd h3 hne
    · exact h3

/-- `_unsafe_rec` companions are excused from replay only: every declaration in their
entire transitive `DepReaches` closure resolves, is not `unsafe`, is not any other
`partial` declaration, is not `sorryAx` or `Lean.trustCompiler`, obeys the test-module
closure policy when declared in a `.test` module, and in unconditional mode for non-test
modules is not native reduction and is an axiom only if foundational. -/
theorem auditAndReplayPackage_unsafeRec_sanitized {cfg : AuditConfig} {pkg : PackageAuditInput}
    {cert : AuditCertificate} (h : auditAndReplayPackage cfg pkg = .ok cert) :
    ∀ inv ∈ pkg.modules, ∀ ci ∈ inv.constants, isCodegenUnsafeRecInMod inv ci = true →
      ∀ dep, DepReaches (packageEnv pkg) ci.name dep →
      ∃ dci, (packageEnv pkg).lookup dep = some dci ∧ dci.safety ≠ .unsafeDecl ∧
        (dci.safety = .safe ∨ dep = ci.name) ∧
        dep ≠ SymName.sorryAxName ∧ dep.isCompilerTrustAxiom = false ∧
        (inv.role = .test →
          dep.isNativeReductionAxiom = false ∧
          (dci.kind = .axiomDecl →
            (dep.isFoundationalAxiom = true ∧ roleOfConst pkg dep dci = .foundation) ∨
            (cfg.allowLocalTestAxioms = true ∧ declaringModuleName pkg dep dci = inv.moduleName))) ∧
        (inv.role ≠ .test → cfg.allowAssumptions = false → cfg.allowProvisionalNative = false →
          dep.isNativeReductionAxiom = false ∧
          (dci.kind = .axiomDecl →
            dep.isFoundationalAxiom = true ∧ roleOfConst pkg dep dci = .foundation)) := by
  intro inv hinv ci hci hcomp dep hreach
  have hm := auditModulePolicy_ok ((auditAndReplayPackage_facts h).2.1.modules inv hinv)
  have h1 := (hm.2.2.2.2.1 ci hci)
  simp only [auditModuleDecl, bindUnit_ok_iff, auditDeclSafety, hcomp, ↓reduceIte] at h1
  have hs := h1.1
  split at hs
  · cases hs
  · rename_i visited hw
    have hmem : dep ∈ visited :=
      (walkGraph_reaches_subset hw).1 ci.name List.mem_cons_self dep hreach
    split at hs
    · rename_i htest
      have h2 := checkAll_ok_iff.mp hs dep hmem
      unfold checkUnsafeRecTestEdge at h2
      split at h2
      · cases h2
      · rename_i dci hdci
        simp only [bindUnit_ok_iff, ensure_ok_iff] at h2
        refine ⟨dci, hdci, h2.1.1, h2.1.2, h2.2.1, h2.2.2.1.1, fun _ => ?_,
          fun hne => absurd htest hne⟩
        refine ⟨h2.2.2.1.2, fun hk => ?_⟩
        rcases h2.2.2.2 with h3 | h3
        · exact absurd hk h3
        · exact h3
    · rename_i hnotTest
      have h2 := checkAll_ok_iff.mp hs dep hmem
      unfold checkUnsafeRecEdge at h2
      split at h2
      · cases h2
      · rename_i dci hdci
        simp only [bindUnit_ok_iff, ensure_ok_iff] at h2
        obtain ⟨p1, p2, p3, p4⟩ := checkDepPolicy_ok h2.2
        refine ⟨dci, hdci, h2.1.1, h2.1.2, p1, p2, fun ht => absurd ht hnotTest,
          fun _ ha hp => ?_⟩
        have hn : dep.isNativeReductionAxiom = false := by
          cases hn : dep.isNativeReductionAxiom with
          | false => rfl
          | true => rw [p3 hn] at hp; cases hp
        refine ⟨hn, fun hk => ?_⟩
        rcases p4 hn hk with hf | hf
        · exact hf
        · rw [ha] at hf
          cases hf.1

/-- With `requireSources`, every module supplied a source text and it passed the scanner. -/
theorem auditAndReplayPackage_sources_covered {cfg : AuditConfig} {pkg : PackageAuditInput}
    {cert : AuditCertificate} (h : auditAndReplayPackage cfg pkg = .ok cert)
    (hreq : cfg.requireSources = true) :
    ∀ inv ∈ pkg.modules, ∃ src, inv.sourceText? = some src ∧
      SourceScanner.scanSourceChars cfg inv.moduleName inv.role src = .ok () := by
  intro inv hinv
  have hm := auditModulePolicy_ok ((auditAndReplayPackage_facts h).2.1.modules inv hinv)
  have h1 := hm.2.2.2.1
  unfold auditModuleSource at h1
  split at h1
  · rw [ensure_ok_iff, hreq] at h1
    cases h1
  · rename_i src hsrc
    exact ⟨src, hsrc, h1⟩

/-- No audited module registers an orphan instance of an imported class: an accepted
instance of an imported class belongs to a `Defs` module, its type normalizes under
β-reduction and local-definition unfolding to a conclusion whose non-`outParam` input
expressions name a local replayed non-definition declaration with no reducibility
attribute. -/
theorem auditAndReplayPackage_no_orphan_instances {cfg : AuditConfig} {pkg : PackageAuditInput}
    {cert : AuditCertificate} (h : auditAndReplayPackage cfg pkg = .ok cert) :
    ∀ inv ∈ pkg.modules, ∀ d cls isPriv,
      EnvExtEntry.instanceEntry d cls isPriv ∈ inv.extEntries →
      isInstanceAnchor inv cls = false →
      inv.role = .defsExempt ∧
        ∃ ci ∈ inv.constants, ci.name = d ∧
          ∃ target, normInstanceTargetOpt inv ci.type = some target ∧
            ∃ arg ∈ instanceInputExprs target,
              ∃ anchor ∈ arg.usedConstants,
                isLocalExtDecl inv anchor = true ∧
                EnvExtEntry.reducibilityOverride anchor ∉ inv.extEntries := by
  intro inv hinv d cls isPriv hext hcls
  have hm := auditModulePolicy_ok ((auditAndReplayPackage_facts h).2.1.modules inv hinv)
  have hval := checkAll_ok_iff.mp hm.1 _ hext
  simp only [validateSingleExtEntry, bindUnit_ok_iff, ensure_ok_iff, hcls, Bool.false_eq_true,
    ↓reduceIte] at hval
  obtain ⟨_, hrole, hfind⟩ := hval
  split at hfind
  · rename_i ci hci
    obtain ⟨hmem, hname⟩ := findConstByName_mem hci
    split at hfind
    · rename_i target htarget
      obtain ⟨arg, harg, hused⟩ := List.any_eq_true.mp (ensure_ok_iff.mp hfind)
      obtain ⟨anchor, ha, hanchor⟩ := List.any_eq_true.mp hused
      simp only [isBaseInstanceAnchor, Bool.and_eq_true, decide_eq_true_eq] at hanchor
      exact ⟨hrole, ci, hmem, hname, target, htarget, arg, harg, anchor, ha, hanchor.1.1,
        hanchor.1.2⟩
    · cases hfind
  · cases hfind

/-- Every accepted coercion belongs to a `Defs` module and involves at least one local
instance anchor (blocking reducible or transparent aliases such as `abbrev N' := Nat`). -/
theorem auditAndReplayPackage_coe_anchored {cfg : AuditConfig} {pkg : PackageAuditInput}
    {cert : AuditCertificate} (h : auditAndReplayPackage cfg pkg = .ok cert) :
    ∀ inv ∈ pkg.modules, ∀ d src tgt,
      EnvExtEntry.coeEntry d src tgt ∈ inv.extEntries →
      inv.role = .defsExempt ∧ isLocalExtDecl inv d = true ∧
        (isInstanceAnchor inv src = true ∨ isInstanceAnchor inv tgt = true) := by
  intro inv hinv d src tgt hext
  have hm := auditModulePolicy_ok ((auditAndReplayPackage_facts h).2.1.modules inv hinv)
  have hval := checkAll_ok_iff.mp hm.1 _ hext
  simp only [validateSingleExtEntry, bindUnit_ok_iff, ensure_ok_iff] at hval
  exact ⟨hval.1, hval.2.1, hval.2.2⟩

/-- Every declaration of a test module has a clean closure, and when
`cfg.allowLocalTestAxioms = false`, every dependency satisfies `CleanDep` with no local
test axioms admitted. -/
theorem auditAndReplayPackage_test_closures_clean {cfg : AuditConfig} {pkg : PackageAuditInput}
    {cert : AuditCertificate} (h : auditAndReplayPackage cfg pkg = .ok cert) :
    ∀ inv ∈ pkg.modules, inv.role = .test → ∀ ci ∈ inv.constants,
      isCodegenUnsafeRecInMod inv ci = false → ∀ dep,
      DepReaches (packageEnv pkg) ci.name dep →
      CleanTestDep pkg (packageEnv pkg) inv.moduleName dep ∧
        (cfg.allowLocalTestAxioms = false → CleanDep pkg (packageEnv pkg) dep) := by
  intro inv hinv hrole ci hci hcomp dep hreach
  have ht := (auditAndReplayPackage_facts h).2.1.tests inv hinv
  simp only [auditTestModule, hrole, ↓reduceIte, checkAll_ok_iff] at ht
  have h1 := ht ci (by simp [replayableConstants, hci, hcomp])
  unfold auditTestDecl at h1
  split at h1
  · cases h1
  · rename_i visited hw
    have h2 := checkAll_ok_iff.mp h1 dep
      ((walkGraph_reaches_subset hw).1 ci.name List.mem_cons_self dep hreach)
    unfold checkTestDep at h2
    split at h2
    · cases h2
    · rename_i dci hdci
      simp only [bindUnit_ok_iff, ensure_ok_iff] at h2
      refine ⟨⟨dci, hdci, h2.1, h2.2.1, h2.2.2.1.1, h2.2.2.1.2, fun hk => ?_⟩, fun hno => ?_⟩
      · rcases h2.2.2.2 with h3 | h3 | h3
        · exact absurd hk h3
        · exact Or.inl h3
        · exact Or.inr h3.2
      · refine ⟨dci, hdci, h2.1, h2.2.1, h2.2.2.1.1, h2.2.2.1.2, fun hk => ?_⟩
        rcases h2.2.2.2 with h3 | h3 | h3
        · exact absurd hk h3
        · exact h3
        · rw [hno] at h3
          cases h3.1

/-- Pipeline-level closure soundness: in unconditional mode the whole dependency closure
of every declaration, verify root, and claim root is clean. -/
theorem auditAndReplayPackage_closure_sound {cfg : AuditConfig} {pkg : PackageAuditInput}
    {cert : AuditCertificate} (h : auditAndReplayPackage cfg pkg = .ok cert)
    (ha : cfg.allowAssumptions = false) (hp : cfg.allowProvisionalNative = false) :
    ∀ root, (root ∈ closureRootsOfPackage pkg ∨ root ∈ pkg.verifyRoots ∨
        root ∈ pkg.claimRoots) →
      ∀ dep, DepReaches (packageEnv pkg) root dep → CleanDep pkg (packageEnv pkg) dep := by
  intro root hroot
  obtain ⟨visited, hv⟩ := (auditAndReplayPackage_facts h).2.1.closures root
    (by simp only [List.mem_append]; rcases hroot with h1 | h1 | h1 <;> simp [h1])
  exact validPackage_axiom_closure_sound ha hp hv

/-- Every verify root is the theorem `<Verify module>.verified`, states a
`VerificationResult`, and has no theory declaration behind its statement. -/
theorem auditAndReplayPackage_verifyRoots_sound {cfg : AuditConfig} {pkg : PackageAuditInput}
    {cert : AuditCertificate} (h : auditAndReplayPackage cfg pkg = .ok cert) :
    ∀ root ∈ pkg.verifyRoots, ∃ ci, (packageEnv pkg).lookup root = some ci ∧
      ci.kind = .thmDecl ∧ ci.type.getAppFn = .const SymName.verificationResultName ∧
      isVerifyRootLocation pkg root = true ∧
      (∀ r ∈ ci.type.usedConstants, ∀ d,
        GraphReaches (packageEnv pkg) (statementExpand pkg root) r d →
        ∃ dCi, (packageEnv pkg).lookup d = some dCi ∧ roleOfConst pkg d dCi ≠ .theory) := by
  intro root hroot
  have h1 := (auditAndReplayPackage_facts h).2.1.verifyRoots root hroot
  unfold auditVerifyRoot at h1
  split at h1
  · cases h1
  · rename_i ci hci
    simp only [bindUnit_ok_iff, ensure_ok_iff] at h1
    refine ⟨ci, hci, h1.1, h1.2.1, h1.2.2.1, ?_⟩
    have h2 := h1.2.2.2
    unfold auditStatement at h2
    split at h2
    · rename_i visited hw
      exact statementOrigins_sound hw
    · cases h2

/-- Exactly one report per verify root, in order: no root is missing from the classification. -/
theorem auditAndReplayPackage_itemReports_cover_roots {cfg : AuditConfig}
    {pkg : PackageAuditInput} {cert : AuditCertificate}
    (h : auditAndReplayPackage cfg pkg = .ok cert) :
    cert.itemReports.map VerifyItemReport.root = pkg.verifyRoots :=
  collectEach_map VerifyItemReport.root (fun _ _ hx => (buildVerifyItemReport_ok hx).1)
    (auditAndReplayPackage_facts h).2.1.reports

theorem itemReport_closure {cfg : AuditConfig} {pkg : PackageAuditInput}
    {cert : AuditCertificate} (h : auditAndReplayPackage cfg pkg = .ok cert)
    {rep : VerifyItemReport} (hrep : rep ∈ cert.itemReports) :
    ∃ visited, auditDirectClosure cfg pkg (packageEnv pkg) rep.root = .ok visited ∧
      rep.reachedProvisional = visited.filter (fun d => d.isNativeReductionAxiom) ∧
      rep.reachedAssumptions = visited.filter (isAssumptionDep pkg (packageEnv pkg)) ∧
      rep.status = classifyVerifyItem rep.reachedProvisional rep.reachedAssumptions := by
  obtain ⟨root, _, hb⟩ := collectEach_mem (auditAndReplayPackage_facts h).2.1.reports rep hrep
  obtain ⟨hroot, visited, hv, h1, h2, h3⟩ := buildVerifyItemReport_ok hb
  exact ⟨visited, hroot ▸ hv, h1, h2, h3⟩

/-- Per-item completeness, for every configuration: each dependency of a verify root is
clean, or it is listed in that root's report and the root is not unconditional. -/
theorem auditAndReplayPackage_item_status_complete {cfg : AuditConfig} {pkg : PackageAuditInput}
    {cert : AuditCertificate} (h : auditAndReplayPackage cfg pkg = .ok cert) :
    ∀ rep ∈ cert.itemReports, ∀ dep, DepReaches (packageEnv pkg) rep.root dep →
      CleanDep pkg (packageEnv pkg) dep ∨
        ((dep ∈ rep.reachedProvisional ∨ dep ∈ rep.reachedAssumptions) ∧
          rep.status ≠ .verifiedUnconditional) := by
  intro rep hrep dep hreach
  obtain ⟨visited, hv, hprov, hassum, hstatus⟩ := itemReport_closure h hrep
  obtain ⟨hall, hchk⟩ := auditDirectClosure_ok hv
  have hmem := hall dep hreach
  rcases cleanDep_or_recorded (hchk dep hmem) with hc | hn | hasm
  · exact Or.inl hc
  · have hin : dep ∈ rep.reachedProvisional := by
      rw [hprov]
      exact List.mem_filter.mpr ⟨hmem, hn⟩
    refine Or.inr ⟨Or.inl hin, fun hs => ?_⟩
    rw [hstatus, classifyVerifyItem_unconditional] at hs
    rw [hs.1] at hin
    simp at hin
  · have hin : dep ∈ rep.reachedAssumptions := by
      rw [hassum]
      exact List.mem_filter.mpr ⟨hmem, hasm⟩
    refine Or.inr ⟨Or.inr hin, fun hs => ?_⟩
    rw [hstatus, classifyVerifyItem_unconditional] at hs
    rw [hs.2] at hin
    simp at hin

/-- Per-item isolation, for every configuration: an item reported `verifiedUnconditional`
has a clean closure even when other items of the package use assumptions or native axioms. -/
theorem auditAndReplayPackage_item_status_sound {cfg : AuditConfig} {pkg : PackageAuditInput}
    {cert : AuditCertificate} (h : auditAndReplayPackage cfg pkg = .ok cert) :
    ∀ rep ∈ cert.itemReports, rep.status = .verifiedUnconditional → ∀ dep,
      DepReaches (packageEnv pkg) rep.root dep → CleanDep pkg (packageEnv pkg) dep := by
  intro rep hrep hstatus dep hreach
  rcases auditAndReplayPackage_item_status_complete h rep hrep dep hreach with hc | ⟨_, hne⟩
  · exact hc
  · exact absurd hstatus hne

/-- Every imported record sits under its own name, and it was replayed, or it is an
`_unsafe_rec` companion whose type is the type of a replayed declaration. -/
theorem imported_record_replayed {cfg : AuditConfig} {pkg : PackageAuditInput}
    {cert : AuditCertificate} (h : auditAndReplayPackage cfg pkg = .ok cert) :
    ∀ n ci, cert.importedEnv.lookup n = some ci →
      ci.name = n ∧ (cert.replayedEnv.lookup n = some ci ∨
        ∃ pc, cert.replayedEnv.lookup pc.name = some pc ∧ pc.type = ci.type) := by
  intro n ci hl
  obtain ⟨hstruct, _, hreplay, himp⟩ := auditAndReplayPackage_facts h
  obtain ⟨hdecls, hmono⟩ := replayCleanEnvOrdered_contains_decl hreplay
  have hin : ∀ inv ∈ pkg.modules, ∀ c ∈ inv.constants, isCodegenUnsafeRecInMod inv c = false →
      cert.replayedEnv.lookup c.name = some c := by
    intro inv hinv c hc hcomp
    exact hdecls c (List.mem_flatMap.mpr ⟨inv, hinv, by simp [replayableConstants, hc, hcomp]⟩)
  rw [himp, packageEnv, KernelEnv.lookup_append] at hl
  cases hb : KernelEnv.lookup (mkBaseKernelEnv pkg.baseEnv) n with
  | some x =>
    simp only [hb, Option.some_or, Option.some.injEq] at hl
    subst hl
    have hname := hb
    rw [lookup_mkBaseKernelEnv] at hname
    exact ⟨(findConstByName_mem hname).2, Or.inl (hmono n x hb)⟩
  | none =>
    simp only [hb, Option.none_or] at hl
    obtain ⟨inv, hinv, hmem⟩ := List.mem_flatMap.mp (KernelEnv.lookup_mem hl)
    have hvalid := (hstruct.2.2.1 inv hinv).2.2.1
    have hkey := (validInventory_key_eq_ci_name hvalid).1 (n, ci) hmem
    have hci : ci ∈ inv.constants := (List.of_mem_zip hmem).2
    simp only at hkey
    subst hkey
    refine ⟨rfl, ?_⟩
    cases hcomp : isCodegenUnsafeRecInMod inv ci with
    | false => exact Or.inl (hin inv hinv ci hci hcomp)
    | true =>
      obtain ⟨pc, hpc, hsafe, hty⟩ := isCodegenUnsafeRecInMod_parent hcomp
      refine Or.inr ⟨pc, hin inv hinv pc hpc ?_, hty⟩
      cases hpcomp : isCodegenUnsafeRecInMod inv pc with
      | false => rfl
      | true =>
        simp only [isCodegenUnsafeRecInMod, Bool.and_eq_true, decide_eq_true_eq] at hpcomp
        rw [hsafe] at hpcomp
        cases hpcomp.1.1

theorem allowReplayAxiom_false {cfg : AuditConfig} (hcfg : cfg.admitsNoAxioms)
    (pkg : PackageAuditInput) (ci : ConstantRecord) : allowReplayAxiom cfg pkg ci = false := by
  simp [allowReplayAxiom, hcfg.1, hcfg.2.1, hcfg.2.2]

/-- End-to-end semantic soundness: when no axiom is admitted and the base environment has
a model, the replayed environment has one too, and in it every proposition that is the
type of a replayed or imported constant is true. -/
theorem auditAndReplayPackage_semantic_sound {cfg : AuditConfig} {pkg : PackageAuditInput}
    {cert : AuditCertificate} (h : auditAndReplayPackage cfg pkg = .ok cert)
    (hcfg : cfg.admitsNoAxioms) {M : Model} (hbase : EnvSound (mkBaseKernelEnv pkg.baseEnv) M) :
    ∃ M', EnvSound cert.replayedEnv M' ∧
      (∀ n ci, cert.replayedEnv.lookup n = some ci →
        ∀ P : Prop, evalExpr M' [] ci.type = .prop P → P) ∧
      (∀ n ci, cert.importedEnv.lookup n = some ci →
        ∀ P : Prop, evalExpr M' [] ci.type = .prop P → P) := by
  obtain ⟨M', hs⟩ := replayCleanEnvOrdered_preserves_sound hbase
    (fun ci _ => allowReplayAxiom_false hcfg pkg ci) (auditAndReplayPackage_facts h).2.2.1
  refine ⟨M', hs, fun n ci hl P hP => kernelEnv_prop_types_true hs hl P hP,
    fun n ci hl P hP => ?_⟩
  rcases (imported_record_replayed h n ci hl).2 with hr | ⟨pc, hpc, hty⟩
  · exact kernelEnv_prop_types_true hs hr P hP
  · exact kernelEnv_prop_types_true hs hpc P (hty ▸ hP)

/-- End-to-end soundness: every imported record sits under its own name; every module
passed the inventory, extension, import, and source checks; and when no axiom is admitted
over a sound base environment, neither the replayed nor the imported environment
(`_unsafe_rec` companions included) has a constant of type `False`. -/
theorem auditAndReplayPackage_sound {cfg : AuditConfig} {pkg : PackageAuditInput}
    {cert : AuditCertificate} (h : auditAndReplayPackage cfg pkg = .ok cert) :
    (∀ n ci, cert.importedEnv.lookup n = some ci → ci.name = n) ∧
    (∀ inv ∈ pkg.modules, validateReplayInventory inv = .ok () ∧
      validateModuleExtensions inv = .ok () ∧ validateImports pkg inv = .ok () ∧
      auditModuleSource cfg inv = .ok ()) ∧
    (cfg.admitsNoAxioms → ∀ M, EnvSound (mkBaseKernelEnv pkg.baseEnv) M →
      (∀ n ci, cert.replayedEnv.lookup n = some ci → ci.type ≠ .const SymName.falseName) ∧
      (∀ n ci, cert.importedEnv.lookup n = some ci → ci.type ≠ .const SymName.falseName)) := by
  obtain ⟨hstruct, hpol, hreplay, _⟩ := auditAndReplayPackage_facts h
  refine ⟨fun n ci hl => (imported_record_replayed h n ci hl).1, fun inv hinv => ?_,
    fun hcfg M hbase => ?_⟩
  · have hm := auditModulePolicy_ok (hpol.modules inv hinv)
    exact ⟨(hstruct.2.2.1 inv hinv).2.2.1, hm.1, hm.2.2.1, hm.2.2.2.1⟩
  · obtain ⟨M', hs⟩ := replayCleanEnvOrdered_preserves_sound hbase
      (fun ci _ => allowReplayAxiom_false hcfg pkg ci) hreplay
    refine ⟨fun n ci hl => kernelEnv_no_false hs hl, fun n ci hl => ?_⟩
    rcases (imported_record_replayed h n ci hl).2 with hr | ⟨pc, hpc, hty⟩
    · exact kernelEnv_no_false hs hr
    · exact hty ▸ kernelEnv_no_false hs hpc

/-! ## Deterministic JSON report -/

/-- Diagnostic code, the names involved, and a free-text detail. -/
def AuditFailure.fields : AuditFailure → String × List SymName × String
  | .lengthMismatch m a b => ("lengthMismatch", [m], toString a ++ " names, " ++ toString b ++ " records")
  | .anonymousConstantName m => ("anonymousConstantName", [m], "")
  | .keyNameMismatch m k n => ("keyNameMismatch", [m, k, n], "")
  | .duplicateConstName m n => ("duplicateConstName", [m, n], "")
  | .duplicateModuleName m => ("duplicateModuleName", [m], "")
  | .invalidMutualAll m d r => ("invalidMutualAll", [m, d], r)
  | .foreignQuotDecl m d => ("foreignQuotDecl", [m, d], "")
  | .privateFlagMismatch m d => ("privateFlagMismatch", [m, d], "")
  | .extraConstNameProvenance m n r => ("extraConstNameProvenance", [m, n], r)
  | .missingOleanServer m => ("missingOleanServer", [m], "")
  | .missingOleanPrivate m => ("missingOleanPrivate", [m], "")
  | .moduleRoleMismatch m r => ("moduleRoleMismatch", [m], r)
  | .stdlibNamedPackageModule m => ("stdlibNamedPackageModule", [m], "")
  | .trustedNamedPackageModule m => ("trustedNamedPackageModule", [m], "")
  | .spoofedExemptModule m => ("spoofedExemptModule", [m], "")
  | .forbiddenImportAll m i => ("forbiddenImportAll", [m, i], "")
  | .forbiddenImportModifier m i r => ("forbiddenImportModifier", [m, i], r)
  | .privateInstanceLeakViaImportAll m i d => ("privateInstanceLeakViaImportAll", [m, i, d], "")
  | .foreignImport m i => ("foreignImport", [m, i], "")
  | .importCycle m => ("importCycle", [m], "")
  | .forbiddenImportDirection m r i ir => ("forbiddenImportDirection", [m, i], r ++ " -> " ++ ir)
  | .referenceOutsideImportClosure m d dep dm => ("referenceOutsideImportClosure", [m, d, dep, dm], "")
  | .reservedOriginMissingSibling m d o => ("reservedOriginMissingSibling", [m, d, o], "")
  | .missingSourceText m => ("missingSourceText", [m], "")
  | .unsupportedSourceLexing m r => ("unsupportedSourceLexing", [m], r)
  | .forbiddenSourceOption m w => ("forbiddenSourceOption", [m], w)
  | .forbiddenMacroOrElab m k d => ("forbiddenMacroOrElab", [m, d], k)
  | .forbiddenInitOrCodegenHook m k d => ("forbiddenInitOrCodegenHook", [m, d], k)
  | .forbiddenInstanceOrCoe m k d => ("forbiddenInstanceOrCoe", [m, d], k)
  | .forbiddenReducibilityOverride m t => ("forbiddenReducibilityOverride", [m, t], "")
  | .forbiddenShadowingOrExport m k n => ("forbiddenShadowingOrExport", [m, n], k)
  | .unsafeOrPartialDecl m d => ("unsafeOrPartialDecl", [m, d], "")
  | .forbiddenAxiom u a dm => ("forbiddenAxiom", [u, a, dm], "")
  | .forbiddenNativeReductionAxiom u a => ("forbiddenNativeReductionAxiom", [u, a], "")
  | .invalidNativeAxiomType u a => ("invalidNativeAxiomType", [u, a], "")
  | .testModuleForeignAxiom m u a => ("testModuleForeignAxiom", [m, u, a], "")
  | .invalidVerifyRoot r reason => ("invalidVerifyRoot", [r], reason)
  | .statementTheoryLeak r d dm => ("statementTheoryLeak", [r, d, dm], "")
  | .closureFuelExhausted r p => ("closureFuelExhausted", [r, p], "")
  | .unknownConstant n => ("unknownConstant", [n], "")
  | .cyclicDependency n => ("cyclicDependency", [n], "")
  | .kernelTypeError d r => ("kernelTypeError", [d], r)

def hexDigitChar (n : Nat) : Char := if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)

/-- JSON string escaping: quote, backslash, and control characters. -/
def jsonEscape : List Char → List Char
  | [] => []
  | c :: rest =>
    (if c = '"' then ['\\', '"']
     else if c = '\\' then ['\\', '\\']
     else if c = '\n' then ['\\', 'n']
     else if c.toNat < 32 then
       ['\\', 'u', '0', '0', hexDigitChar (c.toNat / 16), hexDigitChar (c.toNat % 16)]
     else [c]) ++ jsonEscape rest

def jsonString (s : List Char) : List Char := '"' :: jsonEscape s ++ ['"']

def jsonArray (items : List (List Char)) : List Char :=
  '[' :: List.intercalate [','] items ++ [']']

def jsonNames (names : List SymName) : List Char :=
  jsonArray (names.map (fun n => jsonString n.toChars))

def renderViolationChars (f : AuditFailure) : List Char :=
  "{\"code\":".toList ++ jsonString f.fields.1.toList ++ ",\"names\":".toList ++
    jsonNames f.fields.2.1 ++ ",\"detail\":".toList ++ jsonString f.fields.2.2.toList ++ ['}']

def VerifyItemStatus.render : VerifyItemStatus → String
  | .verifiedUnconditional => "VerifiedUnconditional"
  | .verifiedConditional => "VerifiedConditional"
  | .provisionalNative => "ProvisionalNative"
  | .provisionalNativeConditional => "ProvisionalNativeConditional"

def renderItemChars (rep : VerifyItemReport) : List Char :=
  "{\"root\":".toList ++ jsonString rep.root.toChars ++ ",\"status\":".toList ++
    jsonString rep.status.render.toList ++ ",\"provisional\":".toList ++
    jsonNames rep.reachedProvisional ++ ",\"assumptions\":".toList ++
    jsonNames rep.reachedAssumptions ++ ['}']

/-- All violations worth reporting: the first structural failure of every module, or,
when every module is structurally valid, the first failure of the whole audit. -/
def collectViolations (cfg : AuditConfig) (pkg : PackageAuditInput) : List AuditFailure :=
  match pkg.modules.filterMap (fun inv =>
      match validateModuleStructure inv with
      | .error e => some e
      | .ok _ => none) with
  | [] =>
    match auditAndReplayPackage cfg pkg with
    | .error e => [e]
    | .ok _ => []
  | structural => structural

/-- The report says `"ok": true` only for a package the audit accepted. -/
theorem collectViolations_nil {cfg : AuditConfig} {pkg : PackageAuditInput}
    (h : collectViolations cfg pkg = []) : ∃ cert, auditAndReplayPackage cfg pkg = .ok cert := by
  unfold collectViolations at h
  split at h
  · split at h
    · cases h
    · rename_i cert hc
      exact ⟨cert, hc⟩
  · rename_i hne
    exact absurd h (hne · )

def renderAuditJsonChars (cfg : AuditConfig) (pkg : PackageAuditInput) : List Char :=
  match pkg.modules.filterMap (fun inv =>
      match validateModuleStructure inv with
      | .error e => some e
      | .ok _ => none) with
  | [] =>
    match auditAndReplayPackage cfg pkg with
    | .ok cert =>
      "{\"ok\":true,\"violations\":[],\"modules\":".toList ++ (toString pkg.modules.length).toList ++
        ",\"replayed\":".toList ++ (toString (collectReplayDecls pkg).length).toList ++
        ",\"reachedAxioms\":".toList ++ jsonNames cert.reachedAxioms ++
        ",\"items\":".toList ++ jsonArray (cert.itemReports.map renderItemChars) ++ ['}']
    | .error e =>
      "{\"ok\":false,\"violations\":".toList ++ jsonArray [renderViolationChars e] ++ ['}']
  | structural =>
    "{\"ok\":false,\"violations\":".toList ++ jsonArray (structural.map renderViolationChars) ++
      ['}']

/-- Deterministic JSON for drivers: `{"ok": …, "violations": [...], ...}`. -/
def renderAuditJson (cfg : AuditConfig) (pkg : PackageAuditInput) : String :=
  String.ofList (renderAuditJsonChars cfg pkg)

end Anneal.ReplayKeyAndTamperAudit
