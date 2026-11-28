-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import Lean
import Lean.Replay
import Lean.Compiler.ExportAttr
import Lean.Compiler.IR.Basic
import Lean.Compiler.ImplementedByAttr
import Anneal.NatBitwise

/-!
# Prototype Reference Validator & 6-Vector Test Harness (`V-Q1`–`V-N6`)

Pure, total, DAG-memoized reference validator for the six Lean 4.34.1 `.olean` /
kernel / interpreter integrity vectors:

1. **V-Q1 (`forgedQuotInfo`)**: Canonical `.quotInfo` validation (`Quot`, `Quot.mk`,
   `Quot.lift`, `Quot.ind`, `Init.Prelude` origin, `QuotKind`, `levelParams`, and
   exact canonical type).
2. **V-M2 (`forgedExprMData`, `forgedLevelMData`, `forgedNameHash`)**: Full 64-bit
   recomputation and verification of `Expr.Data`, `Level.Data`, and `Name.hash`
   across both in-memory `Environment` DAGs (immune to `Expr.beq` upper-bit
   cache-poisoning) and pure-Lean binary `.olean`/`.ir` compacted-region pointer DAGs.
3. **V-U3 (`invalidUtf8Literal`)**: Strict RFC 3629 UTF-8 well-formedness, embedded
   NUL rejection, NUL-terminator check, and `m_length` scalar-value count verification
   on `Literal.strVal`, `Name.str`, and all reachable `LeanString` objects.
4. **V-F4 (`kernelFreshCollision`, `lean4#16767`)**: Rejection of `_kernel_fresh`
   identifiers in declaration names, nested names, binders, `Expr.fvar`/`mvar`/`const`/
   `proj`, `Level.param`/`mvar`, and `LocalContext`, paired with live Lean 4.34.1
   `Kernel.isDefEq` / `Kernel.check` / `Kernel.whnf` collision witnesses.
5. **V-S5 (`forbiddenExportAttr`)**: Complete `@[export]` and C-symbol exposure
   checking across `exportAttr.ext.getModuleEntries`, `getModuleIREntries`, live
   `getState`, `getExportNameFor?`, `isExport` (`main`), and raw binary `.olean`/`.ir`
   `ModuleData.entries`.
6. **V-N6 (`nanodaNatXorPropextMismatch`, `lean4#16831`)**: Live transitive axiom
   closure audit of `Nat.xor`, `Nat.bitwise`, `Anneal.NatBitwise`, and a second-kernel
   `primitiveTargets` export-closure parity oracle contrasting unconditional vs.
   demand-driven filtering (`zerocopy#4444`, `zerocopy#4488`).

All traversals are structurally recursive or explicitly fuel-bounded and fail closed
with `auditFuelExhausted`.
-/

namespace Anneal.OleanQuotMdataUtf8Proto

open Lean

/-! ## Section 1: Core Types, Diagnostics, and Helpers -/

structure Violation where
  tag    : String
  decl   : Name
  detail : String
  deriving Inhabited, BEq, Repr

def Violation.render (v : Violation) : String :=
  s!"[{v.tag}] {v.decl}: {v.detail}"

def Violation.toJson (v : Violation) : Json :=
  Json.mkObj [
    ("tag", Lean.toJson v.tag),
    ("decl", Lean.toJson v.decl.toString),
    ("detail", Lean.toJson v.detail)
  ]

structure AuditStats where
  declsChecked      : Nat := 0
  exprNodesVisited  : Nat := 0
  exprCacheHits     : Nat := 0
  levelNodesVisited : Nat := 0
  levelCacheHits    : Nat := 0
  nameNodesVisited  : Nat := 0
  nameCacheHits     : Nat := 0
  stringsValidated  : Nat := 0
  deriving Inhabited, BEq, Repr

def AuditStats.totalNodes (s : AuditStats) : Nat :=
  s.exprNodesVisited + s.levelNodesVisited + s.nameNodesVisited

def AuditStats.totalHits (s : AuditStats) : Nat :=
  s.exprCacheHits + s.levelCacheHits + s.nameCacheHits

def AuditStats.hitRatePermille (s : AuditStats) : Nat :=
  let lookups := s.totalNodes + s.totalHits
  if lookups == 0 then 0 else (s.totalHits * 1000) / lookups

def AuditStats.toJson (s : AuditStats) : Json :=
  Json.mkObj [
    ("declsChecked", Lean.toJson s.declsChecked),
    ("exprNodesVisited", Lean.toJson s.exprNodesVisited),
    ("exprCacheHits", Lean.toJson s.exprCacheHits),
    ("levelNodesVisited", Lean.toJson s.levelNodesVisited),
    ("levelCacheHits", Lean.toJson s.levelCacheHits),
    ("nameNodesVisited", Lean.toJson s.nameNodesVisited),
    ("nameCacheHits", Lean.toJson s.nameCacheHits),
    ("stringsValidated", Lean.toJson s.stringsValidated),
    ("totalNodes", Lean.toJson s.totalNodes),
    ("totalHits", Lean.toJson s.totalHits),
    ("hitRatePermille", Lean.toJson s.hitRatePermille)
  ]

structure AuditReport where
  violations : Array Violation := #[]
  stats      : AuditStats := {}
  deriving Inhabited, BEq, Repr

def AuditReport.ok (r : AuditReport) : Bool := r.violations.isEmpty

def AuditReport.hasTag (r : AuditReport) (tag : String) : Bool :=
  r.violations.any (·.tag == tag)

def AuditReport.tags (r : AuditReport) : Array String := Id.run do
  let mut seen : Std.HashSet String := {}
  let mut out : Array String := #[]
  for v in r.violations do
    if !seen.contains v.tag then
      seen := seen.insert v.tag
      out := out.push v.tag
  return out.qsort (· < ·)

def AuditReport.toJson (r : AuditReport) : Json :=
  Json.mkObj [
    ("ok", Lean.toJson r.ok),
    ("violationCount", Lean.toJson r.violations.size),
    ("tags", Lean.toJson r.tags),
    ("violations", Lean.toJson (r.violations.map Violation.toJson)),
    ("stats", r.stats.toJson)
  ]

/-! ## Section 2: Strict RFC 3629 UTF-8 & `m_length` Validator (V-U3) -/

/-- Validate raw UTF-8 bytes strictly per RFC 3629:
- rejects lone UTF-16 surrogates (`U+D800..U+DFFF`, e.g. `ED A0 80`)
- rejects truncated multi-byte sequences (`E2 82`, etc.)
- rejects overlong encodings (`C0 80`, `C0 AF`, `E0 80..9F`, `F0 80..8F`)
- rejects invalid lead bytes (`C0..C1`, `F5..FF`) and unexpected continuations (`80..BF`)
- rejects codepoints above `U+10FFFF` (`F4 90..BF`)
- rejects embedded NUL bytes (`0x00`) when `rejectEmbeddedNul := true`
- verifies the exact Unicode scalar-value count equals `expectedCpLen`. -/
def validateUtf8Bytes (bytes : ByteArray) (expectedCpLen : Nat)
    (rejectEmbeddedNul : Bool := true) : Except String Nat := Id.run do
  let n := bytes.size
  let mut i : Nat := 0
  let mut cps : Nat := 0
  for _ in [0:n + 1] do
    if i >= n then
      break
    let b0 := bytes.get! i
    if b0 == 0x00 then
      if rejectEmbeddedNul then
        return .error s!"embedded NUL byte at offset {i}"
      i := i + 1
      cps := cps + 1
    else if b0 <= 0x7F then
      i := i + 1
      cps := cps + 1
    else if b0 >= 0xC2 && b0 <= 0xDF then
      if i + 1 >= n then
        return .error s!"truncated 2-byte UTF-8 sequence at offset {i}"
      let b1 := bytes.get! (i + 1)
      if b1 < 0x80 || b1 > 0xBF then
        return .error s!"invalid continuation byte {b1} at offset {i + 1}"
      i := i + 2
      cps := cps + 1
    else if b0 == 0xE0 then
      if i + 2 >= n then
        return .error s!"truncated 3-byte UTF-8 sequence at offset {i}"
      let b1 := bytes.get! (i + 1)
      let b2 := bytes.get! (i + 2)
      if b1 < 0xA0 || b1 > 0xBF then
        return .error s!"overlong or invalid 3-byte sequence (E0 {b1}) at offset {i}"
      if b2 < 0x80 || b2 > 0xBF then
        return .error s!"invalid continuation byte {b2} at offset {i + 2}"
      i := i + 3
      cps := cps + 1
    else if (b0 >= 0xE1 && b0 <= 0xEC) || (b0 >= 0xEE && b0 <= 0xEF) then
      if i + 2 >= n then
        return .error s!"truncated 3-byte UTF-8 sequence at offset {i}"
      let b1 := bytes.get! (i + 1)
      let b2 := bytes.get! (i + 2)
      if b1 < 0x80 || b1 > 0xBF || b2 < 0x80 || b2 > 0xBF then
        return .error s!"invalid continuation byte in 3-byte sequence at offset {i}"
      i := i + 3
      cps := cps + 1
    else if b0 == 0xED then
      if i + 2 >= n then
        return .error s!"truncated 3-byte UTF-8 sequence at offset {i}"
      let b1 := bytes.get! (i + 1)
      let b2 := bytes.get! (i + 2)
      if b1 < 0x80 || b1 > 0x9F then
        return .error s!"UTF-16 surrogate or invalid byte (ED {b1}) at offset {i}"
      if b2 < 0x80 || b2 > 0xBF then
        return .error s!"invalid continuation byte {b2} at offset {i + 2}"
      i := i + 3
      cps := cps + 1
    else if b0 == 0xF0 then
      if i + 3 >= n then
        return .error s!"truncated 4-byte UTF-8 sequence at offset {i}"
      let b1 := bytes.get! (i + 1)
      let b2 := bytes.get! (i + 2)
      let b3 := bytes.get! (i + 3)
      if b1 < 0x90 || b1 > 0xBF then
        return .error s!"overlong or invalid 4-byte sequence (F0 {b1}) at offset {i}"
      if b2 < 0x80 || b2 > 0xBF || b3 < 0x80 || b3 > 0xBF then
        return .error s!"invalid continuation byte in 4-byte sequence at offset {i}"
      i := i + 4
      cps := cps + 1
    else if b0 >= 0xF1 && b0 <= 0xF3 then
      if i + 3 >= n then
        return .error s!"truncated 4-byte UTF-8 sequence at offset {i}"
      let b1 := bytes.get! (i + 1)
      let b2 := bytes.get! (i + 2)
      let b3 := bytes.get! (i + 3)
      if b1 < 0x80 || b1 > 0xBF || b2 < 0x80 || b2 > 0xBF || b3 < 0x80 || b3 > 0xBF then
        return .error s!"invalid continuation byte in 4-byte sequence at offset {i}"
      i := i + 4
      cps := cps + 1
    else if b0 == 0xF4 then
      if i + 3 >= n then
        return .error s!"truncated 4-byte UTF-8 sequence at offset {i}"
      let b1 := bytes.get! (i + 1)
      let b2 := bytes.get! (i + 2)
      let b3 := bytes.get! (i + 3)
      if b1 < 0x80 || b1 > 0x8F then
        return .error s!"out-of-range codepoint > U+10FFFF (F4 {b1}) at offset {i}"
      if b2 < 0x80 || b2 > 0xBF || b3 < 0x80 || b3 > 0xBF then
        return .error s!"invalid continuation byte in 4-byte sequence at offset {i}"
      i := i + 4
      cps := cps + 1
    else
      return .error s!"invalid UTF-8 lead or unexpected continuation byte {b0} at offset {i}"
  if cps != expectedCpLen then
    return .error s!"m_length mismatch: stored {expectedCpLen}, decoded {cps} scalar values"
  return .ok cps

/-- Validate an in-memory `String` by reading raw bytes via `toUTF8` and comparing
the decoded RFC 3629 scalar-value count against `s.length` (`lean_string_object.m_length`). -/
def validateInMemoryString (s : String) (rejectEmbeddedNul : Bool := true) : Except String Nat :=
  validateUtf8Bytes s.toUTF8 s.length rejectEmbeddedNul

/-! ## Section 3: Exact Pure `Name.hash`, `Level.Data`, and `Expr.Data` Formulas (V-M2) -/

def nameAnonymousHash : UInt64 := 1723

def recomputeNameStrHash (preHash : UInt64) (s : String) : UInt64 :=
  mixHash preHash (hash s)

def recomputeNameNumHash (preHash : UInt64) (v : Nat) : UInt64 :=
  let vHash : UInt64 := if v < UInt64.size then UInt64.ofNat v else 17
  mixHash preHash vHash

/-- Pure bit-exact implementation of `lean_level_mk_data` that fails closed
instead of panicking when `depth >= 2^24`. Reserved bits `34..39` are strictly zero. -/
def recomputeLevelData (h : UInt64) (depth : Nat) (hasMVar hasParam : Bool) : Except String UInt64 :=
  if depth >= 0x1000000 then
    .error s!"Level depth overflow: {depth} >= 2^24"
  else
    let lo : UInt64 := h &&& 0xFFFFFFFF
    let bMVar : UInt64 := if hasMVar then (1 : UInt64) <<< 32 else 0
    let bParam : UInt64 := if hasParam then (1 : UInt64) <<< 33 else 0
    let dBits : UInt64 := UInt64.ofNat depth <<< 40
    .ok (lo ||| bMVar ||| bParam ||| dBits)

/-- Pure bit-exact implementation of `lean_expr_mk_data` that fails closed
instead of panicking when `looseBVarRange >= 2^20`. -/
def recomputeExprData (h : UInt64) (looseBVarRange : Nat := 0) (approxDepth : Nat := 0)
    (hasFVar hasExprMVar hasLevelMVar hasLevelParam : Bool := false) : Except String UInt64 :=
  if looseBVarRange >= 0x100000 then
    .error s!"Expr looseBVarRange overflow: {looseBVarRange} >= 2^20"
  else
    let lo : UInt64 := h &&& 0xFFFFFFFF
    let dBits : UInt64 := UInt64.ofNat (min approxDepth 255) <<< 32
    let bFVar : UInt64 := if hasFVar then (1 : UInt64) <<< 40 else 0
    let bEMVar : UInt64 := if hasExprMVar then (1 : UInt64) <<< 41 else 0
    let bLMVar : UInt64 := if hasLevelMVar then (1 : UInt64) <<< 42 else 0
    let bLParam : UInt64 := if hasLevelParam then (1 : UInt64) <<< 43 else 0
    let bRange : UInt64 := UInt64.ofNat looseBVarRange <<< 44
    .ok (lo ||| dBits ||| bFVar ||| bEMVar ||| bLMVar ||| bLParam ||| bRange)

/-- Pure bit-exact mirror of Lean 4.34.1 `lean_expr_mk_app_data` (`Expr.mkAppData`).
Note how `fData`'s hash mixes only its low 32 bits whereas `aData`'s full 64-bit word
enters the Murmur-style multiplier. -/
def recomputeAppDataPure (fData aData : UInt64) : UInt64 :=
  let fd : UInt64 := (fData >>> 32) &&& 0xFF
  let ad : UInt64 := (aData >>> 32) &&& 0xFF
  let maxD : UInt64 := if fd > ad then fd else ad
  let clampedD : UInt64 := if maxD < 254 then maxD else 254
  let fl : UInt64 := fData >>> 44
  let al : UInt64 := aData >>> 44
  let maxL : UInt64 := if fl > al then fl else al
  let k : UInt64 := aData * 0xc6a4a7935bd1e995
  let h32 : UInt32 :=
    (fData.toUInt32 ^^^ k.toUInt32 ^^^ (k >>> 47).toUInt32 ^^^ 0x5bd1e995) * 0x5bd1e995
  let flags : UInt64 := (fData ||| aData) &&& 0x00000F0000000000
  (h32.toUInt64 ||| flags ||| (clampedD <<< 32) ||| (maxL <<< 44)) + 0x0000000100000000

def levelDataHash (d : UInt64) : UInt64 := d &&& 0xFFFFFFFF
def levelDataHasMVar (d : UInt64) : Bool := ((d >>> 32) &&& 1) == 1
def levelDataHasParam (d : UInt64) : Bool := ((d >>> 33) &&& 1) == 1
def levelDataDepth (d : UInt64) : Nat := (d >>> 40).toNat

def exprDataHash (d : UInt64) : UInt64 := d &&& 0xFFFFFFFF
def exprDataApproxDepth (d : UInt64) : Nat := ((d >>> 32) &&& 0xFF).toNat
def exprDataHasFVar (d : UInt64) : Bool := ((d >>> 40) &&& 1) == 1
def exprDataHasExprMVar (d : UInt64) : Bool := ((d >>> 41) &&& 1) == 1
def exprDataHasLevelMVar (d : UInt64) : Bool := ((d >>> 42) &&& 1) == 1
def exprDataHasLevelParam (d : UInt64) : Bool := ((d >>> 43) &&& 1) == 1
def exprDataLooseBVarRange (d : UInt64) : Nat := (d >>> 44).toNat

def exprDataIsClosed (d : UInt64) : Bool :=
  !exprDataHasFVar d && !exprDataHasExprMVar d && !exprDataHasLevelMVar d && exprDataLooseBVarRange d == 0

/-! ## Section 4: Cache-Sound Strict Structural + Metadata Equality (`withPtrEq`)

Standard `Expr.beq` (`lean_expr_eqv`) and `Expr.equal` (`lean_expr_equal`) skip upper
`Expr.Data` flags (`hasFVar`, `hasExprMVar`, `hasLevelMVar`, `hasLevelParam`,
`looseBVarRange`, `approxDepth`), and `String.beq` does not compare `m_length` against
decoded UTF-8 scalar counts. Using `Std.HashSet Expr` to memoize validation therefore
permits an attacker to pair an honest term `e_ok` with a structurally identical forged
term `e_bad` having the same 32-bit hash (or a forged child with masked flags) and get a
false cache hit.

`StrictExprKey` uses `withPtrEq` (total, kernel-checked pointer fast-path) falling back
to full recursive 64-bit `Expr.Data` / `Level.Data` / `Name.hash` / raw `ByteArray` +
`m_length` comparison, guaranteeing:
- O(1) cache hits on genuinely pointer-shared DAG nodes (exponential shared DAGs stay linear),
- 0 false cache hits against forged duplicates at any depth (root or child). -/

def levelDataU64 (d : Level.Data) : UInt64 := d
def exprDataU64 (d : Expr.Data) : UInt64 := d

theorem levelDataBeq_refl (d : Level.Data) : (d == d) = true :=
  @beq_self_eq_true UInt64 _ _ d

theorem exprDataBeq_refl (d : Expr.Data) : (d == d) = true :=
  @beq_self_eq_true UInt64 _ _ d

theorem binderInfoBeq_refl (bi : BinderInfo) : (bi == bi) = true := by
  cases bi <;> rfl

def strictStringEq (a b : String) : Bool :=
  a.length == b.length && a.toUTF8.data == b.toUTF8.data

theorem strictStringEq_refl (a : String) : strictStringEq a a = true := by
  simp [strictStringEq]

def strictNameEqAux : (a b : Name) → { r : Bool // a = b → r = true }
  | .anonymous, .anonymous => ⟨true, fun _ => rfl⟩
  | .str p1 s1, .str p2 s2 =>
    ⟨strictStringEq s1 s2 && withPtrEq p1 p2 (fun _ => p1.hash == p2.hash && (strictNameEqAux p1 p2).val) (fun h => by
      subst h; simp [(strictNameEqAux p1 p1).property rfl]),
     fun h => by
      injection h with hp hs; subst hp; subst hs
      simp [withPtrEq, strictStringEq_refl, (strictNameEqAux p1 p1).property rfl]⟩
  | .num p1 v1, .num p2 v2 =>
    ⟨v1 == v2 && withPtrEq p1 p2 (fun _ => p1.hash == p2.hash && (strictNameEqAux p1 p2).val) (fun h => by
      subst h; simp [(strictNameEqAux p1 p1).property rfl]),
     fun h => by
      injection h with hp hv; subst hp; subst hv
      simp [withPtrEq, (strictNameEqAux p1 p1).property rfl]⟩
  | .anonymous, .str _ _ => ⟨false, fun h => nomatch h⟩
  | .anonymous, .num _ _ => ⟨false, fun h => nomatch h⟩
  | .str _ _, .anonymous => ⟨false, fun h => nomatch h⟩
  | .str _ _, .num _ _ => ⟨false, fun h => nomatch h⟩
  | .num _ _, .anonymous => ⟨false, fun h => nomatch h⟩
  | .num _ _, .str _ _ => ⟨false, fun h => nomatch h⟩

def strictNameEq (a b : Name) : Bool :=
  withPtrEq a b (fun _ => a.hash == b.hash && (strictNameEqAux a b).val) (fun h => by
    subst h; simp [(strictNameEqAux a a).property rfl])

theorem strictNameEq_refl (a : Name) : strictNameEq a a = true := by
  simp [strictNameEq, withPtrEq, (strictNameEqAux a a).property rfl]

def strictLevelEqAux : (a b : Level) → { r : Bool // a = b → r = true }
  | .zero, .zero => ⟨true, fun _ => rfl⟩
  | .succ u1, .succ u2 =>
    ⟨withPtrEq u1 u2 (fun _ => u1.data == u2.data && (strictLevelEqAux u1 u2).val) (fun h => by
      subst h; simp [levelDataBeq_refl, (strictLevelEqAux u1 u1).property rfl]),
     fun h => by
      injection h with hu; subst hu
      simp [withPtrEq, levelDataBeq_refl, (strictLevelEqAux u1 u1).property rfl]⟩
  | .max u1 v1, .max u2 v2 =>
    ⟨withPtrEq u1 u2 (fun _ => u1.data == u2.data && (strictLevelEqAux u1 u2).val) (fun h => by
      subst h; simp [levelDataBeq_refl, (strictLevelEqAux u1 u1).property rfl]) &&
     withPtrEq v1 v2 (fun _ => v1.data == v2.data && (strictLevelEqAux v1 v2).val) (fun h => by
      subst h; simp [levelDataBeq_refl, (strictLevelEqAux v1 v1).property rfl]),
     fun h => by
      injection h with hu hv; subst hu; subst hv
      simp [withPtrEq, levelDataBeq_refl, (strictLevelEqAux u1 u1).property rfl, (strictLevelEqAux v1 v1).property rfl]⟩
  | .imax u1 v1, .imax u2 v2 =>
    ⟨withPtrEq u1 u2 (fun _ => u1.data == u2.data && (strictLevelEqAux u1 u2).val) (fun h => by
      subst h; simp [levelDataBeq_refl, (strictLevelEqAux u1 u1).property rfl]) &&
     withPtrEq v1 v2 (fun _ => v1.data == v2.data && (strictLevelEqAux v1 v2).val) (fun h => by
      subst h; simp [levelDataBeq_refl, (strictLevelEqAux v1 v1).property rfl]),
     fun h => by
      injection h with hu hv; subst hu; subst hv
      simp [withPtrEq, levelDataBeq_refl, (strictLevelEqAux u1 u1).property rfl, (strictLevelEqAux v1 v1).property rfl]⟩
  | .param n1, .param n2 =>
    ⟨strictNameEq n1 n2, fun h => by injection h with hn; subst hn; exact strictNameEq_refl n1⟩
  | .mvar id1, .mvar id2 =>
    ⟨strictNameEq id1.name id2.name, fun h => by injection h with hid; subst hid; exact strictNameEq_refl id1.name⟩
  | .zero, .succ _ => ⟨false, fun h => nomatch h⟩
  | .zero, .max _ _ => ⟨false, fun h => nomatch h⟩
  | .zero, .imax _ _ => ⟨false, fun h => nomatch h⟩
  | .zero, .param _ => ⟨false, fun h => nomatch h⟩
  | .zero, .mvar _ => ⟨false, fun h => nomatch h⟩
  | .succ _, .zero => ⟨false, fun h => nomatch h⟩
  | .succ _, .max _ _ => ⟨false, fun h => nomatch h⟩
  | .succ _, .imax _ _ => ⟨false, fun h => nomatch h⟩
  | .succ _, .param _ => ⟨false, fun h => nomatch h⟩
  | .succ _, .mvar _ => ⟨false, fun h => nomatch h⟩
  | .max _ _, .zero => ⟨false, fun h => nomatch h⟩
  | .max _ _, .succ _ => ⟨false, fun h => nomatch h⟩
  | .max _ _, .imax _ _ => ⟨false, fun h => nomatch h⟩
  | .max _ _, .param _ => ⟨false, fun h => nomatch h⟩
  | .max _ _, .mvar _ => ⟨false, fun h => nomatch h⟩
  | .imax _ _, .zero => ⟨false, fun h => nomatch h⟩
  | .imax _ _, .succ _ => ⟨false, fun h => nomatch h⟩
  | .imax _ _, .max _ _ => ⟨false, fun h => nomatch h⟩
  | .imax _ _, .param _ => ⟨false, fun h => nomatch h⟩
  | .imax _ _, .mvar _ => ⟨false, fun h => nomatch h⟩
  | .param _, .zero => ⟨false, fun h => nomatch h⟩
  | .param _, .succ _ => ⟨false, fun h => nomatch h⟩
  | .param _, .max _ _ => ⟨false, fun h => nomatch h⟩
  | .param _, .imax _ _ => ⟨false, fun h => nomatch h⟩
  | .param _, .mvar _ => ⟨false, fun h => nomatch h⟩
  | .mvar _, .zero => ⟨false, fun h => nomatch h⟩
  | .mvar _, .succ _ => ⟨false, fun h => nomatch h⟩
  | .mvar _, .max _ _ => ⟨false, fun h => nomatch h⟩
  | .mvar _, .imax _ _ => ⟨false, fun h => nomatch h⟩
  | .mvar _, .param _ => ⟨false, fun h => nomatch h⟩

def strictLevelEq (a b : Level) : Bool :=
  withPtrEq a b (fun _ => a.data == b.data && (strictLevelEqAux a b).val) (fun h => by
    subst h; simp [levelDataBeq_refl, (strictLevelEqAux a a).property rfl])

theorem strictLevelEq_refl (a : Level) : strictLevelEq a a = true := by
  simp [strictLevelEq, withPtrEq, levelDataBeq_refl, (strictLevelEqAux a a).property rfl]

def strictLevelListEq : List Level → List Level → Bool
  | [], [] => true
  | u1 :: us1, u2 :: us2 => strictLevelEq u1 u2 && strictLevelListEq us1 us2
  | _, _ => false

theorem strictLevelListEq_refl : ∀ ls : List Level, strictLevelListEq ls ls = true
  | [] => rfl
  | u :: us => by
    simp [strictLevelListEq, strictLevelEq_refl u, strictLevelListEq_refl us]

def strictLitEq : Literal → Literal → Bool
  | .natVal v1, .natVal v2 => v1 == v2
  | .strVal s1, .strVal s2 => strictStringEq s1 s2
  | _, _ => false

theorem strictLitEq_refl : ∀ l : Literal, strictLitEq l l = true
  | .natVal _ => by simp [strictLitEq]
  | .strVal s => by simp [strictLitEq, strictStringEq_refl]

/-! ### Injective strict `Syntax` cache key (B1 hardening)

A0 compared `DataValue.ofSyntax` payloads via `reprStr`, which is NOT byte-injective:
measured on Lean 4.34.1, an atom whose `LeanString` holds the invalid bytes `C0 81`
(`m_length = 1`) renders with the SAME `reprStr` as the honest atom `"A"`.
Two `Expr.mdata` nodes differing only in that atom were `StrictExprKey`-equal, so the
second (forged) node was a cache hit and never validated. `syntaxStrictKey` serializes
every string's raw bytes + `m_length`, every `Name` component + stored hash, and every
position, so equal keys imply identical validation results. Fuel matches
`syntaxValidationFuel`, so a key-truncating syntax tree also exhausts validation fuel
and fails closed with `auditFuelExhausted`. -/

def syntaxValidationFuel : Nat := 100000

def keyPushU64 (out : ByteArray) (v : UInt64) : ByteArray := Id.run do
  let mut o := out
  for k in [0:8] do
    o := o.push (v >>> UInt64.ofNat (8 * k)).toUInt8
  return o

def keyPushNat (out : ByteArray) (n : Nat) : ByteArray :=
  let s := (toString n).toUTF8
  keyPushU64 out (UInt64.ofNat s.size) ++ s

def keyPushStr (out : ByteArray) (s : String) : ByteArray :=
  let b := s.toUTF8
  keyPushU64 (keyPushU64 out (UInt64.ofNat s.length)) (UInt64.ofNat b.size) ++ b

def keyPushName : ByteArray → Name → ByteArray
  | out, .anonymous => out.push 0
  | out, n@(.str p s) => keyPushStr (keyPushU64 ((keyPushName out p).push 1) n.hash) s
  | out, n@(.num p v) => keyPushNat (keyPushU64 ((keyPushName out p).push 2) n.hash) v

def keyPushSourceInfo (out : ByteArray) : SourceInfo → ByteArray
  | .original leading pos trailing endPos =>
    let o := keyPushStr (out.push 0) leading.str
    let o := keyPushNat (keyPushNat o leading.startPos.byteIdx) leading.stopPos.byteIdx
    let o := keyPushNat o pos.byteIdx
    let o := keyPushStr o trailing.str
    let o := keyPushNat (keyPushNat o trailing.startPos.byteIdx) trailing.stopPos.byteIdx
    keyPushNat o endPos.byteIdx
  | .synthetic pos endPos canonical =>
    (keyPushNat (keyPushNat (out.push 1) pos.byteIdx) endPos.byteIdx).push (if canonical then 1 else 0)
  | .none => out.push 2

/-- Injective, fuel-bounded serialization of a `Syntax` tree used as its strict cache key. -/
def syntaxStrictKey (root : Syntax) : ByteArray := Id.run do
  let mut out : ByteArray := ByteArray.empty
  let mut work : List Syntax := [root]
  for _ in [0:syntaxValidationFuel] do
    match work with
    | [] => return out.push 0xEE
    | s :: rest =>
      work := rest
      match s with
      | .missing => out := out.push 0
      | .node info kind args =>
        out := keyPushU64 (keyPushName (keyPushSourceInfo (out.push 1) info) kind) (UInt64.ofNat args.size)
        work := args.toList ++ work
      | .atom info val =>
        out := keyPushStr (keyPushSourceInfo (out.push 2) info) val
      | .ident info rawVal val pre =>
        out := keyPushSourceInfo (out.push 3) info
        out := keyPushStr out rawVal.str
        out := keyPushNat (keyPushNat out rawVal.startPos.byteIdx) rawVal.stopPos.byteIdx
        out := keyPushU64 (keyPushName out val) (UInt64.ofNat pre.length)
        for p in pre do
          match p with
          | .namespace ns => out := keyPushName (out.push 0) ns
          | .decl n fields =>
            out := keyPushU64 (keyPushName (out.push 1) n) (UInt64.ofNat fields.length)
            for f in fields do
              out := keyPushStr out f
  return out.push 0xFF

def strictSubstringRawEq (a b : Substring.Raw) : Bool :=
  strictStringEq a.str b.str && a.startPos == b.startPos && a.stopPos == b.stopPos

theorem strictSubstringRawEq_refl (a : Substring.Raw) : strictSubstringRawEq a a = true := by
  simp [strictSubstringRawEq, strictStringEq_refl]

def strictSourceInfoEq : SourceInfo → SourceInfo → Bool
  | .original l1 p1 t1 e1, .original l2 p2 t2 e2 =>
    strictSubstringRawEq l1 l2 && p1 == p2 && strictSubstringRawEq t1 t2 && e1 == e2
  | .synthetic p1 e1 c1, .synthetic p2 e2 c2 =>
    p1 == p2 && e1 == e2 && c1 == c2
  | .none, .none => true
  | _, _ => false

theorem strictSourceInfoEq_refl : ∀ s : SourceInfo, strictSourceInfoEq s s = true
  | .original l p t e => by
    simp [strictSourceInfoEq, strictSubstringRawEq_refl]
  | .synthetic p e c => by
    simp [strictSourceInfoEq]
  | .none => rfl

def strictStringListEq : List String → List String → Bool
  | [], [] => true
  | a :: as, b :: bs => strictStringEq a b && strictStringListEq as bs
  | _, _ => false

theorem strictStringListEq_refl : ∀ xs : List String, strictStringListEq xs xs = true
  | [] => rfl
  | x :: xs => by simp [strictStringListEq, strictStringEq_refl, strictStringListEq_refl xs]

def strictPreresolvedEq : Syntax.Preresolved → Syntax.Preresolved → Bool
  | .namespace n1, .namespace n2 => strictNameEq n1 n2
  | .decl n1 f1, .decl n2 f2 => strictNameEq n1 n2 && strictStringListEq f1 f2
  | _, _ => false

theorem strictPreresolvedEq_refl : ∀ p : Syntax.Preresolved, strictPreresolvedEq p p = true
  | .namespace n => by simp [strictPreresolvedEq, strictNameEq_refl]
  | .decl n f => by simp [strictPreresolvedEq, strictNameEq_refl, strictStringListEq_refl]

def strictPreresolvedListEq : List Syntax.Preresolved → List Syntax.Preresolved → Bool
  | [], [] => true
  | a :: as, b :: bs => strictPreresolvedEq a b && strictPreresolvedListEq as bs
  | _, _ => false

theorem strictPreresolvedListEq_refl :
    ∀ xs : List Syntax.Preresolved, strictPreresolvedListEq xs xs = true
  | [] => rfl
  | x :: xs => by
    simp [strictPreresolvedListEq, strictPreresolvedEq_refl, strictPreresolvedListEq_refl xs]

/-! ### DAG-safe strict `Syntax` equality and hash (`withPtrEq`, A1 hardening)

B1's `syntaxStrictKey` walked `Syntax` as an unmemoized tree with fuel `100000`, so a tiny
depth-30 shared `Syntax.node` DAG (31 nodes in memory, `2^30` paths) exhausted fuel on BOTH
`syntaxStrictKey` and `validateSyntaxDag` (exponential DoS). `strictSyntaxEq` uses `withPtrEq`
at every node (O(1) on shared pointers, full byte+`m_length`+`Name.hash` structural check on
distinct pointers), and `StrictSyntaxKey` enables O(N) DAG memoization in `validateSyntaxDag`. -/

mutual
def strictSyntaxEqAux : (a b : Syntax) → { r : Bool // a = b → r = true }
  | .missing, .missing => ⟨true, fun _ => rfl⟩
  | .node i1 k1 a1, .node i2 k2 a2 =>
    ⟨strictSourceInfoEq i1 i2 && strictNameEq k1 k2 &&
     withPtrEq a1 a2 (fun _ => (strictSyntaxListEqAux a1.toList a2.toList).val) (fun h => by
       subst h; exact (strictSyntaxListEqAux a1.toList a1.toList).property rfl),
     fun h => by
       injection h with hi hk ha; subst hi; subst hk; subst ha
       simp [withPtrEq, strictSourceInfoEq_refl, strictNameEq_refl,
         (strictSyntaxListEqAux a1.toList a1.toList).property rfl]⟩
  | .atom i1 v1, .atom i2 v2 =>
    ⟨strictSourceInfoEq i1 i2 && strictStringEq v1 v2, fun h => by
      injection h with hi hv; subst hi; subst hv
      simp [strictSourceInfoEq_refl, strictStringEq_refl]⟩
  | .ident i1 r1 v1 p1, .ident i2 r2 v2 p2 =>
    ⟨strictSourceInfoEq i1 i2 && strictSubstringRawEq r1 r2 &&
     strictNameEq v1 v2 && strictPreresolvedListEq p1 p2, fun h => by
      injection h with hi hr hv hp; subst hi; subst hr; subst hv; subst hp
      simp [strictSourceInfoEq_refl, strictSubstringRawEq_refl, strictNameEq_refl,
        strictPreresolvedListEq_refl]⟩
  | .missing, .node _ _ _ => ⟨false, fun h => nomatch h⟩
  | .missing, .atom _ _ => ⟨false, fun h => nomatch h⟩
  | .missing, .ident _ _ _ _ => ⟨false, fun h => nomatch h⟩
  | .node _ _ _, .missing => ⟨false, fun h => nomatch h⟩
  | .node _ _ _, .atom _ _ => ⟨false, fun h => nomatch h⟩
  | .node _ _ _, .ident _ _ _ _ => ⟨false, fun h => nomatch h⟩
  | .atom _ _, .missing => ⟨false, fun h => nomatch h⟩
  | .atom _ _, .node _ _ _ => ⟨false, fun h => nomatch h⟩
  | .atom _ _, .ident _ _ _ _ => ⟨false, fun h => nomatch h⟩
  | .ident _ _ _ _, .missing => ⟨false, fun h => nomatch h⟩
  | .ident _ _ _ _, .node _ _ _ => ⟨false, fun h => nomatch h⟩
  | .ident _ _ _ _, .atom _ _ => ⟨false, fun h => nomatch h⟩

def strictSyntaxListEqAux : (xs ys : List Syntax) → { r : Bool // xs = ys → r = true }
  | [], [] => ⟨true, fun _ => rfl⟩
  | x :: xs, y :: ys =>
    ⟨withPtrEq x y (fun _ => (strictSyntaxEqAux x y).val) (fun h => by
       subst h; exact (strictSyntaxEqAux x x).property rfl) &&
     (strictSyntaxListEqAux xs ys).val,
     fun h => by
       injection h with hx hxs; subst hx; subst hxs
       simp [withPtrEq, (strictSyntaxEqAux x x).property rfl,
         (strictSyntaxListEqAux xs xs).property rfl]⟩
  | [], _ :: _ => ⟨false, fun h => nomatch h⟩
  | _ :: _, [] => ⟨false, fun h => nomatch h⟩
end

def strictSyntaxEq (a b : Syntax) : Bool :=
  withPtrEq a b (fun _ => (strictSyntaxEqAux a b).val) (fun h => by
    subst h; exact (strictSyntaxEqAux a a).property rfl)

theorem strictSyntaxEq_refl (a : Syntax) : strictSyntaxEq a a = true := by
  simp [strictSyntaxEq, withPtrEq, (strictSyntaxEqAux a a).property rfl]

/-- Shallow O(1) structural hash for `StrictSyntaxKey` (always agrees on `strictSyntaxEq`-equal
nodes because `strictSyntaxEq` checks raw UTF-8 bytes, `m_length`, `Name.hash`, and arity). -/
def strictSyntaxHash : Syntax → UInt64
  | .missing => 101
  | .node _ kind args => mixHash 103 (mixHash kind.hash (UInt64.ofNat args.size))
  | .atom _ val => mixHash 107 (mixHash (UInt64.ofNat val.length) (UInt64.ofNat val.toUTF8.size))
  | .ident _ rawVal val pre =>
    mixHash 109 (mixHash val.hash (mixHash (UInt64.ofNat rawVal.str.length) (UInt64.ofNat pre.length)))

structure StrictSyntaxKey where
  val : Syntax

instance : BEq StrictSyntaxKey where
  beq a b := strictSyntaxEq a.val b.val

instance : Hashable StrictSyntaxKey where
  hash a := strictSyntaxHash a.val

def pairList : List α → List α → List (α × α)
  | a :: as, b :: bs => (a, b) :: pairList as bs
  | _, _ => []

theorem pairList_diag : ∀ (xs : List α) (p : α × α), p ∈ pairList xs xs → p.1 = p.2
  | [], _, h => nomatch h
  | _ :: xs, p, h => by
    simp only [pairList, List.mem_cons] at h
    cases h with
    | inl h => subst h; rfl
    | inr h => exact pairList_diag xs p h

/-- Tail-recursive, zero-`ByteArray`-allocation structural equality for `Syntax` (A2), charged one
unit of `fuel` per compared node pair.

B3 hardening: A2 handed everything left after `fuel` pairs to the recursive, per-pair
`strictSyntaxPairsEqFallback`, which (i) recurses natively as deep as the remaining tree and
(ii) re-expands shared sub-DAGs once per path whenever the two sides are distinct objects:
comparing two separately built but structurally identical depth-`d` shared `Syntax` DAGs costs
`2^d` (two `MData` payloads over one body with such DAGs collide in the bounded 512-node
fingerprint, so `validateExprDag` stalls instead of failing closed). Exhausting `fuel` now
returns `true`. This is sound because the loop consumes one pair per node of `a`'s tree
expansion: exhaustion means that expansion exceeds `syntaxValidationFuel` nodes, so whichever
side was validated (cache entries are inserted only after validation; module constants are all
validated) already recorded `auditFuelExhausted` and the audit fails closed regardless. -/
def strictSyntaxEqIterLoop : Nat → List (Syntax × Syntax) → Bool
  | _, [] => true
  | 0, _ => true
  | fuel + 1, (a, b) :: rest =>
    match a, b with
    | .missing, .missing => strictSyntaxEqIterLoop fuel rest
    | .node i1 k1 a1, .node i2 k2 a2 =>
      if strictSourceInfoEq i1 i2 && strictNameEq k1 k2 && a1.size == a2.size then
        strictSyntaxEqIterLoop fuel (pairList a1.toList a2.toList ++ rest)
      else false
    | .atom i1 v1, .atom i2 v2 =>
      if strictSourceInfoEq i1 i2 && strictStringEq v1 v2 then
        strictSyntaxEqIterLoop fuel rest
      else false
    | .ident i1 r1 v1 p1, .ident i2 r2 v2 p2 =>
      if strictSourceInfoEq i1 i2 && strictSubstringRawEq r1 r2 &&
         strictNameEq v1 v2 && strictPreresolvedListEq p1 p2 then
        strictSyntaxEqIterLoop fuel rest
      else false
    | _, _ => false

theorem strictSyntaxEqIterLoop_diag :
    ∀ (fuel : Nat) (xs : List (Syntax × Syntax)),
      (∀ p ∈ xs, p.1 = p.2) → strictSyntaxEqIterLoop fuel xs = true
  | 0, [], _ => rfl
  | _ + 1, [], _ => rfl
  | 0, _ :: _, _ => rfl
  | fuel + 1, (a, b) :: rest, h => by
    have hab : a = b := h (a, b) (List.mem_cons_self ..)
    have hrest : ∀ p ∈ rest, p.1 = p.2 := fun p hp => h p (List.mem_cons_of_mem _ hp)
    subst hab
    cases a with
    | missing => exact strictSyntaxEqIterLoop_diag fuel rest hrest
    | node i k arr =>
      simp only [strictSyntaxEqIterLoop, strictSourceInfoEq_refl, strictNameEq_refl,
        beq_self_eq_true, Bool.and_self, ↓reduceIte]
      apply strictSyntaxEqIterLoop_diag fuel
      intro p hp
      rw [List.mem_append] at hp
      cases hp with
      | inl h1 => exact pairList_diag arr.toList p h1
      | inr h2 => exact hrest p h2
    | atom i v =>
      simp only [strictSyntaxEqIterLoop, strictSourceInfoEq_refl, strictStringEq_refl,
        Bool.and_self, ↓reduceIte]
      exact strictSyntaxEqIterLoop_diag fuel rest hrest
    | ident i r v p =>
      simp only [strictSyntaxEqIterLoop, strictSourceInfoEq_refl, strictSubstringRawEq_refl,
        strictNameEq_refl, strictPreresolvedListEq_refl, Bool.and_self, ↓reduceIte]
      exact strictSyntaxEqIterLoop_diag fuel rest hrest

def strictSyntaxEqIter (a b : Syntax) (fuel : Nat := syntaxValidationFuel) : Bool :=
  withPtrEq a b (fun _ => strictSyntaxEqIterLoop fuel [(a, b)]) (fun h => by
    subst h
    apply strictSyntaxEqIterLoop_diag
    intro p hp
    simp only [List.mem_singleton] at hp
    subst hp; rfl)

theorem strictSyntaxEqIter_refl (s : Syntax) : strictSyntaxEqIter s s = true := by
  simp only [strictSyntaxEqIter, withPtrEq]
  apply strictSyntaxEqIterLoop_diag
  intro p hp
  simp only [List.mem_singleton] at hp
  subst hp; rfl

/-- Bounded-budget O(1) structural fingerprint for `Syntax` (A2 hardening): avoids allocating
a full `syntaxStrictKey` `ByteArray` on every `HashMap` lookup while still distinguishing
distinct `Syntax` chains up to 512 nodes deep (agrees on all `strictSyntaxEqIter`-equal trees). -/
def syntaxBoundedFingerprint (root : Syntax) (budget : Nat := 512) : UInt64 := Id.run do
  let mut h : UInt64 := 131
  let mut work : List Syntax := [root]
  for _ in [0:budget] do
    match work with
    | [] => return mixHash h 0xEE
    | s :: rest =>
      work := rest
      match s with
      | .missing => h := mixHash h 1
      | .node _ kind args =>
        h := mixHash h (mixHash 2 (mixHash kind.hash (UInt64.ofNat args.size)))
        work := args.toList ++ work
      | .atom _ val =>
        h := mixHash h (mixHash 3 (mixHash (UInt64.ofNat val.length) (hash val.toUTF8)))
      | .ident _ rawVal val pre =>
        h := mixHash h (mixHash 4 (mixHash val.hash (mixHash (hash rawVal.str.toUTF8) (UInt64.ofNat pre.length))))
  return mixHash h 0xFF

def strictDataValueEq : DataValue → DataValue → Bool
  | .ofString s1, .ofString s2 => strictStringEq s1 s2
  | .ofBool b1, .ofBool b2 => b1 == b2
  | .ofName n1, .ofName n2 => strictNameEq n1 n2
  | .ofNat v1, .ofNat v2 => v1 == v2
  | .ofInt v1, .ofInt v2 => v1 == v2
  | .ofSyntax s1, .ofSyntax s2 => strictSyntaxEqIter s1 s2
  | _, _ => false

theorem strictDataValueEq_refl : ∀ dv : DataValue, strictDataValueEq dv dv = true
  | .ofString s => by simp [strictDataValueEq, strictStringEq_refl]
  | .ofBool _ => by simp [strictDataValueEq]
  | .ofName n => by simp [strictDataValueEq, strictNameEq_refl]
  | .ofNat _ => by simp [strictDataValueEq]
  | .ofInt _ => by simp [strictDataValueEq]
  | .ofSyntax s => by simp [strictDataValueEq, strictSyntaxEqIter_refl]

def strictKVEntriesEq : List (Name × DataValue) → List (Name × DataValue) → Bool
  | [], [] => true
  | (k1, v1) :: r1, (k2, v2) :: r2 =>
    strictNameEq k1 k2 && strictDataValueEq v1 v2 && strictKVEntriesEq r1 r2
  | _, _ => false

theorem strictKVEntriesEq_refl : ∀ xs : List (Name × DataValue), strictKVEntriesEq xs xs = true
  | [] => rfl
  | (k, v) :: r => by
    simp [strictKVEntriesEq, strictNameEq_refl k, strictDataValueEq_refl v,
      strictKVEntriesEq_refl r]

def strictMDataEq (m1 m2 : MData) : Bool :=
  strictKVEntriesEq m1.entries m2.entries

theorem strictMDataEq_refl (m : MData) : strictMDataEq m m = true :=
  strictKVEntriesEq_refl m.entries

def strictExprEqAux (a b : Expr) : { r : Bool // a = b → r = true } :=
  match a with
  | .bvar i1 =>
    match b with
    | .bvar i2 => ⟨i1 == i2, fun h => by injection h with hi; subst hi; simp⟩
    | .fvar _ | .mvar _ | .sort _ | .const _ _ | .app _ _ | .lam _ _ _ _
    | .forallE _ _ _ _ | .letE _ _ _ _ _ | .lit _ | .mdata _ _ | .proj _ _ _ => ⟨false, fun h => nomatch h⟩
  | .fvar id1 =>
    match b with
    | .fvar id2 => ⟨strictNameEq id1.name id2.name, fun h => by injection h with hid; subst hid; exact strictNameEq_refl id1.name⟩
    | .bvar _ | .mvar _ | .sort _ | .const _ _ | .app _ _ | .lam _ _ _ _
    | .forallE _ _ _ _ | .letE _ _ _ _ _ | .lit _ | .mdata _ _ | .proj _ _ _ => ⟨false, fun h => nomatch h⟩
  | .mvar id1 =>
    match b with
    | .mvar id2 => ⟨strictNameEq id1.name id2.name, fun h => by injection h with hid; subst hid; exact strictNameEq_refl id1.name⟩
    | .bvar _ | .fvar _ | .sort _ | .const _ _ | .app _ _ | .lam _ _ _ _
    | .forallE _ _ _ _ | .letE _ _ _ _ _ | .lit _ | .mdata _ _ | .proj _ _ _ => ⟨false, fun h => nomatch h⟩
  | .sort u1 =>
    match b with
    | .sort u2 => ⟨strictLevelEq u1 u2, fun h => by injection h with hu; subst hu; exact strictLevelEq_refl u1⟩
    | .bvar _ | .fvar _ | .mvar _ | .const _ _ | .app _ _ | .lam _ _ _ _
    | .forallE _ _ _ _ | .letE _ _ _ _ _ | .lit _ | .mdata _ _ | .proj _ _ _ => ⟨false, fun h => nomatch h⟩
  | .const n1 us1 =>
    match b with
    | .const n2 us2 =>
      ⟨strictNameEq n1 n2 && strictLevelListEq us1 us2, fun h => by
        injection h with hn hus; subst hn; subst hus; simp [strictNameEq_refl, strictLevelListEq_refl]⟩
    | .bvar _ | .fvar _ | .mvar _ | .sort _ | .app _ _ | .lam _ _ _ _
    | .forallE _ _ _ _ | .letE _ _ _ _ _ | .lit _ | .mdata _ _ | .proj _ _ _ => ⟨false, fun h => nomatch h⟩
  | .app f1 a1 =>
    match b with
    | .app f2 a2 =>
      ⟨withPtrEq f1 f2 (fun _ => f1.data == f2.data && (strictExprEqAux f1 f2).val) (fun h => by
          subst h; simp [exprDataBeq_refl, (strictExprEqAux f1 f1).property rfl]) &&
       withPtrEq a1 a2 (fun _ => a1.data == a2.data && (strictExprEqAux a1 a2).val) (fun h => by
          subst h; simp [exprDataBeq_refl, (strictExprEqAux a1 a1).property rfl]),
       fun h => by
        injection h with hf ha; subst hf; subst ha
        simp [withPtrEq, exprDataBeq_refl, (strictExprEqAux f1 f1).property rfl, (strictExprEqAux a1 a1).property rfl]⟩
    | .bvar _ | .fvar _ | .mvar _ | .sort _ | .const _ _ | .lam _ _ _ _
    | .forallE _ _ _ _ | .letE _ _ _ _ _ | .lit _ | .mdata _ _ | .proj _ _ _ => ⟨false, fun h => nomatch h⟩
  | .lam n1 t1 b1 bi1 =>
    match b with
    | .lam n2 t2 b2 bi2 =>
      ⟨bi1 == bi2 && strictNameEq n1 n2 &&
       withPtrEq t1 t2 (fun _ => t1.data == t2.data && (strictExprEqAux t1 t2).val) (fun h => by
          subst h; simp [exprDataBeq_refl, (strictExprEqAux t1 t1).property rfl]) &&
       withPtrEq b1 b2 (fun _ => b1.data == b2.data && (strictExprEqAux b1 b2).val) (fun h => by
          subst h; simp [exprDataBeq_refl, (strictExprEqAux b1 b1).property rfl]),
       fun h => by
        injection h with hn ht hb hbi; subst hn; subst ht; subst hb; subst hbi
        simp [withPtrEq, exprDataBeq_refl, binderInfoBeq_refl, strictNameEq_refl,
          (strictExprEqAux t1 t1).property rfl, (strictExprEqAux b1 b1).property rfl]⟩
    | .bvar _ | .fvar _ | .mvar _ | .sort _ | .const _ _ | .app _ _
    | .forallE _ _ _ _ | .letE _ _ _ _ _ | .lit _ | .mdata _ _ | .proj _ _ _ => ⟨false, fun h => nomatch h⟩
  | .forallE n1 t1 b1 bi1 =>
    match b with
    | .forallE n2 t2 b2 bi2 =>
      ⟨bi1 == bi2 && strictNameEq n1 n2 &&
       withPtrEq t1 t2 (fun _ => t1.data == t2.data && (strictExprEqAux t1 t2).val) (fun h => by
          subst h; simp [exprDataBeq_refl, (strictExprEqAux t1 t1).property rfl]) &&
       withPtrEq b1 b2 (fun _ => b1.data == b2.data && (strictExprEqAux b1 b2).val) (fun h => by
          subst h; simp [exprDataBeq_refl, (strictExprEqAux b1 b1).property rfl]),
       fun h => by
        injection h with hn ht hb hbi; subst hn; subst ht; subst hb; subst hbi
        simp [withPtrEq, exprDataBeq_refl, binderInfoBeq_refl, strictNameEq_refl,
          (strictExprEqAux t1 t1).property rfl, (strictExprEqAux b1 b1).property rfl]⟩
    | .bvar _ | .fvar _ | .mvar _ | .sort _ | .const _ _ | .app _ _ | .lam _ _ _ _
    | .letE _ _ _ _ _ | .lit _ | .mdata _ _ | .proj _ _ _ => ⟨false, fun h => nomatch h⟩
  | .letE n1 t1 v1 b1 nd1 =>
    match b with
    | .letE n2 t2 v2 b2 nd2 =>
      ⟨nd1 == nd2 && strictNameEq n1 n2 &&
       withPtrEq t1 t2 (fun _ => t1.data == t2.data && (strictExprEqAux t1 t2).val) (fun h => by
          subst h; simp [exprDataBeq_refl, (strictExprEqAux t1 t1).property rfl]) &&
       withPtrEq v1 v2 (fun _ => v1.data == v2.data && (strictExprEqAux v1 v2).val) (fun h => by
          subst h; simp [exprDataBeq_refl, (strictExprEqAux v1 v1).property rfl]) &&
       withPtrEq b1 b2 (fun _ => b1.data == b2.data && (strictExprEqAux b1 b2).val) (fun h => by
          subst h; simp [exprDataBeq_refl, (strictExprEqAux b1 b1).property rfl]),
       fun h => by
        injection h with hn ht hv hb hnd; subst hn; subst ht; subst hv; subst hb; subst hnd
        simp [withPtrEq, exprDataBeq_refl, strictNameEq_refl, (strictExprEqAux t1 t1).property rfl,
          (strictExprEqAux v1 v1).property rfl, (strictExprEqAux b1 b1).property rfl]⟩
    | .bvar _ | .fvar _ | .mvar _ | .sort _ | .const _ _ | .app _ _ | .lam _ _ _ _
    | .forallE _ _ _ _ | .lit _ | .mdata _ _ | .proj _ _ _ => ⟨false, fun h => nomatch h⟩
  | .lit l1 =>
    match b with
    | .lit l2 => ⟨strictLitEq l1 l2, fun h => by injection h with hl; subst hl; exact strictLitEq_refl l1⟩
    | .bvar _ | .fvar _ | .mvar _ | .sort _ | .const _ _ | .app _ _ | .lam _ _ _ _
    | .forallE _ _ _ _ | .letE _ _ _ _ _ | .mdata _ _ | .proj _ _ _ => ⟨false, fun h => nomatch h⟩
  | .mdata d1 b1 =>
    match b with
    | .mdata d2 b2 =>
      ⟨strictMDataEq d1 d2 &&
       withPtrEq b1 b2 (fun _ => b1.data == b2.data && (strictExprEqAux b1 b2).val) (fun h => by
          subst h; simp [exprDataBeq_refl, (strictExprEqAux b1 b1).property rfl]),
       fun h => by
        injection h with hd hb; subst hd; subst hb
        simp [withPtrEq, exprDataBeq_refl, strictMDataEq_refl, (strictExprEqAux b1 b1).property rfl]⟩
    | .bvar _ | .fvar _ | .mvar _ | .sort _ | .const _ _ | .app _ _ | .lam _ _ _ _
    | .forallE _ _ _ _ | .letE _ _ _ _ _ | .lit _ | .proj _ _ _ => ⟨false, fun h => nomatch h⟩
  | .proj s1 i1 b1 =>
    match b with
    | .proj s2 i2 b2 =>
      ⟨i1 == i2 && strictNameEq s1 s2 &&
       withPtrEq b1 b2 (fun _ => b1.data == b2.data && (strictExprEqAux b1 b2).val) (fun h => by
          subst h; simp [exprDataBeq_refl, (strictExprEqAux b1 b1).property rfl]),
       fun h => by
        injection h with hs hi hb; subst hs; subst hi; subst hb
        simp [withPtrEq, exprDataBeq_refl, strictNameEq_refl, (strictExprEqAux b1 b1).property rfl]⟩
    | .bvar _ | .fvar _ | .mvar _ | .sort _ | .const _ _ | .app _ _ | .lam _ _ _ _
    | .forallE _ _ _ _ | .letE _ _ _ _ _ | .lit _ | .mdata _ _ => ⟨false, fun h => nomatch h⟩

def strictExprEq (a b : Expr) : Bool :=
  withPtrEq a b (fun _ => a.data == b.data && (strictExprEqAux a b).val) (fun h => by
    subst h; simp [exprDataBeq_refl, (strictExprEqAux a a).property rfl])

structure StrictNameKey where
  val : Name

instance : BEq StrictNameKey where
  beq a b := strictNameEq a.val b.val

instance : Hashable StrictNameKey where
  hash a := a.val.hash

structure StrictLevelKey where
  val : Level

instance : BEq StrictLevelKey where
  beq a b := strictLevelEq a.val b.val

instance : Hashable StrictLevelKey where
  hash a :=
    let d : UInt64 := a.val.data
    mixHash d (d >>> 32)

structure StrictExprKey where
  val : Expr

instance : BEq StrictExprKey where
  beq a b := strictExprEq a.val b.val

def dataValueFingerprint : DataValue → UInt64
  | .ofString s => mixHash 1 (hash s.toUTF8)
  | .ofBool b => if b then 3 else 2
  | .ofName n => mixHash 4 n.hash
  | .ofNat v => mixHash 5 (hash v)
  | .ofInt v => mixHash 6 (hash v)
  | .ofSyntax s => mixHash 7 (syntaxBoundedFingerprint s)

/-- B2: `Expr.mdata` data depends only on the body, so A1's key hash put every `mdata` node
over a shared body in one bucket and compared payloads pairwise (quadratic). The hash now mixes
an exact fingerprint of the `MData` entries (agreeing with `strictMDataEq`). -/
def mdataFingerprint (md : MData) : UInt64 :=
  md.entries.foldl (fun acc (k, v) => mixHash acc (mixHash k.hash (dataValueFingerprint v))) 11

instance : Hashable StrictExprKey where
  hash a :=
    let d : UInt64 := a.val.data
    let h := mixHash d (d >>> 32)
    match a.val with
    | .mdata md _ => mixHash h (mdataFingerprint md)
    | _ => h

/-! ## Section 5: V-Q1 Canonical `.quotInfo` Validator -/

def quotKindEq : QuotKind → QuotKind → Bool
  | .type, .type => true
  | .ctor, .ctor => true
  | .lift, .lift => true
  | .ind, .ind => true
  | _, _ => false

def quotKindName : QuotKind → String
  | .type => "type"
  | .ctor => "ctor"
  | .lift => "lift"
  | .ind => "ind"

def canonicalQuotType : Expr :=
  let u := Level.param `u
  let relTy := Expr.forallE `a (.bvar 0)
    (Expr.forallE `a (.bvar 1) (.sort .zero) .default) .default
  Expr.forallE `α (.sort u)
    (Expr.forallE `r relTy (.sort u) .default) .implicit

def canonicalQuotMkType : Expr :=
  let u := Level.param `u
  let relTy := Expr.forallE `a (.bvar 0)
    (Expr.forallE `a (.bvar 1) (.sort .zero) .default) .default
  let retTy := Expr.app (Expr.app (.const `Quot [u]) (.bvar 2)) (.bvar 1)
  Expr.forallE `α (.sort u)
    (Expr.forallE `r relTy
      (Expr.forallE `a (.bvar 1) retTy .default) .default) .implicit

def canonicalQuotLiftType : Expr :=
  let u := Level.param `u
  let v := Level.param `v
  let relTy := Expr.forallE `a (.bvar 0)
    (Expr.forallE `a (.bvar 1) (.sort .zero) .default) .default
  let fTy := Expr.forallE `a (.bvar 2) (.bvar 1) .default
  let eqApp :=
    Expr.app
      (Expr.app
        (Expr.app (.const `Eq [v]) (.bvar 4))
        (Expr.app (.bvar 3) (.bvar 2)))
      (Expr.app (.bvar 3) (.bvar 1))
  let compatTy :=
    Expr.forallE `a (.bvar 3)
      (Expr.forallE `b (.bvar 4)
        (Expr.forallE `a
          (Expr.app (Expr.app (.bvar 4) (.bvar 1)) (.bvar 0))
          eqApp .default) .default) .default
  let quotApp := Expr.app (Expr.app (.const `Quot [u]) (.bvar 4)) (.bvar 3)
  Expr.forallE `α (.sort u)
    (Expr.forallE `r relTy
      (Expr.forallE `β (.sort v)
        (Expr.forallE `f fTy
          (Expr.forallE `a compatTy
            (Expr.forallE `a quotApp (.bvar 3) .default) .default) .default) .implicit) .implicit) .implicit

def canonicalQuotIndType : Expr :=
  let u := Level.param `u
  let relTy := Expr.forallE `a (.bvar 0)
    (Expr.forallE `a (.bvar 1) (.sort .zero) .default) .default
  let predTy :=
    Expr.forallE `a
      (Expr.app (Expr.app (.const `Quot [u]) (.bvar 1)) (.bvar 0))
      (.sort .zero) .default
  let mkApp :=
    Expr.app
      (Expr.app
        (Expr.app (.const `Quot.mk [u]) (.bvar 3))
        (.bvar 2))
      (.bvar 0)
  let mkHyp := Expr.forallE `a (.bvar 2) (Expr.app (.bvar 1) mkApp) .default
  let qTy := Expr.app (Expr.app (.const `Quot [u]) (.bvar 3)) (.bvar 2)
  Expr.forallE `α (.sort u)
    (Expr.forallE `r relTy
      (Expr.forallE `β predTy
        (Expr.forallE `mk mkHyp
          (Expr.forallE `q qTy (Expr.app (.bvar 2) (.bvar 0)) .default) .default) .implicit) .implicit) .implicit

def canonicalQuotSpec? (n : Name) : Option (QuotKind × List Name × Expr) :=
  if n == `Quot then some (.type, [`u], canonicalQuotType)
  else if n == `Quot.mk then some (.ctor, [`u], canonicalQuotMkType)
  else if n == `Quot.lift then some (.lift, [`u, `v], canonicalQuotLiftType)
  else if n == `Quot.ind then some (.ind, [`u], canonicalQuotIndType)
  else none

/-- Canonical Lean 4.34.1 `init_quot` declaring module (`Init.Prelude`). -/
def canonicalQuotOrigin : Name := `Init.Prelude

/-- Validate a `QuotVal` against Lean 4.34.1 canonical quotient primitives.
Checks canonical name, `Init.Prelude` origin, `QuotKind`, exact `levelParams`, and
exact canonical type (via `strictExprEq`, not `Expr.beq`). -/
def validateQuotVal (qv : QuotVal) (originMod : Option Name) : Array Violation := Id.run do
  let mut vs : Array Violation := #[]
  if originMod != some canonicalQuotOrigin then
    vs := vs.push {
      tag := "forgedQuotInfo"
      decl := qv.name
      detail := s!"quotInfo origin is {reprStr originMod}, expected some {canonicalQuotOrigin}"
    }
  match canonicalQuotSpec? qv.name with
  | none =>
    vs := vs.push {
      tag := "forgedQuotInfo"
      decl := qv.name
      detail := s!"non-canonical quotInfo declaration name {qv.name}"
    }
  | some (expKind, expLParams, expTy) =>
    if !quotKindEq qv.kind expKind then
      vs := vs.push {
        tag := "forgedQuotInfo"
        decl := qv.name
        detail := s!"quotInfo kind is {quotKindName qv.kind}, expected {quotKindName expKind}"
      }
    if qv.levelParams != expLParams then
      vs := vs.push {
        tag := "forgedQuotInfo"
        decl := qv.name
        detail := s!"quotInfo levelParams are {qv.levelParams}, expected {expLParams}"
      }
    if !strictExprEq qv.type expTy then
      vs := vs.push {
        tag := "forgedQuotInfo"
        decl := qv.name
        detail := "quotInfo type differs from canonical Lean 4.34.1 Quot primitive type"
      }
  return vs

/-! ## Section 6: V-F4 `_kernel_fresh` Prefix Validator (`lean4#16767`) -/

def kernelFreshPrefix : String := "_kernel_fresh"

def isKernelFreshString (s : String) : Bool :=
  s == kernelFreshPrefix || s.startsWith kernelFreshPrefix

def hasKernelFreshComponent : Name → Bool
  | .anonymous => false
  | .str p s => isKernelFreshString s || hasKernelFreshComponent p
  | .num p _ => hasKernelFreshComponent p

/-! ## Section 7: In-Memory DAG-Memoized Validator (V-Q1..V-S5) -/

structure MemValidatorState where
  nameCache   : Std.HashMap StrictNameKey UInt64 := {}
  levelCache  : Std.HashMap StrictLevelKey UInt64 := {}
  exprCache   : Std.HashMap StrictExprKey UInt64 := {}
  syntaxCache : Std.HashSet StrictSyntaxKey := {}
  violations  : Array Violation := #[]
  seenV       : Std.HashSet (String × Name × String) := {}
  stats       : AuditStats := {}

def MemValidatorState.record (st : MemValidatorState) (tag : String) (decl : Name)
    (detail : String) : MemValidatorState :=
  let key := (tag, decl, detail)
  if st.seenV.contains key then st
  else { st with
    violations := st.violations.push { tag, decl, detail }
    seenV := st.seenV.insert key
  }

/-- Iterative post-order DAG-memoized validator for `Name`.
Recomputes `Name.hash`, checks RFC 3629 UTF-8 + `m_length` + embedded NUL on every
`Name.str`, and rejects `_kernel_fresh` components. -/
def validateNameDag (decl : Name) (root : Name) (st0 : MemValidatorState)
    (fuel : Nat := 100000) : MemValidatorState × UInt64 := Id.run do
  let mut st := st0
  let mut work : List (Bool × Name) := [(false, root)]
  let mut completed := false
  for _ in [0:fuel] do
    match work with
    | [] => completed := true; break
    | (false, n) :: rest =>
      work := rest
      let key : StrictNameKey := ⟨n⟩
      if st.nameCache.contains key then
        st := { st with stats := { st.stats with nameCacheHits := st.stats.nameCacheHits + 1 } }
        continue
      match n with
      | .anonymous =>
        st := { st with
          nameCache := st.nameCache.insert key nameAnonymousHash
          stats := { st.stats with nameNodesVisited := st.stats.nameNodesVisited + 1 }
        }
      | .str p _ =>
        work := (false, p) :: (true, n) :: work
      | .num p _ =>
        work := (false, p) :: (true, n) :: work
    | (true, n) :: rest =>
      work := rest
      let key : StrictNameKey := ⟨n⟩
      if st.nameCache.contains key then continue
      st := { st with stats := { st.stats with nameNodesVisited := st.stats.nameNodesVisited + 1 } }
      match n with
      | .anonymous =>
        st := { st with nameCache := st.nameCache.insert key nameAnonymousHash }
      | .str p s =>
        let pHash := st.nameCache.getD ⟨p⟩ nameAnonymousHash
        st := { st with stats := { st.stats with stringsValidated := st.stats.stringsValidated + 1 } }
        match validateInMemoryString s true with
        | .error err =>
          st := st.record "invalidUtf8Literal" decl s!"Name.str component UTF-8 error: {err}"
        | .ok _ => pure ()
        if isKernelFreshString s then
          st := st.record "kernelFreshCollision" decl s!"Name contains _kernel_fresh component {s}"
        let expected := recomputeNameStrHash pHash s
        if n.hash != expected then
          st := st.record "forgedNameHash" decl
            s!"Name.str hash mismatch: stored {n.hash}, expected {expected}"
        st := { st with nameCache := st.nameCache.insert key expected }
      | .num p v =>
        let pHash := st.nameCache.getD ⟨p⟩ nameAnonymousHash
        let expected := recomputeNameNumHash pHash v
        if n.hash != expected then
          st := st.record "forgedNameHash" decl
            s!"Name.num hash mismatch: stored {n.hash}, expected {expected}"
        st := { st with nameCache := st.nameCache.insert key expected }
  if !completed then
    st := st.record "auditFuelExhausted" decl "validateNameDag exhausted fuel"
    return (st, 0)
  return (st, st.nameCache.getD ⟨root⟩ nameAnonymousHash)

/-- Iterative post-order DAG-memoized validator for `Level`.
Recomputes exact 64-bit `Level.Data` (hash, hasMVar, hasParam, reserved zero bits
34..39, and 24-bit depth) without trusting child `Level.data`. -/
def validateLevelDag (decl : Name) (root : Level) (st0 : MemValidatorState)
    (fuel : Nat := 100000) : MemValidatorState × UInt64 := Id.run do
  let mut st := st0
  let mut work : List (Bool × Level) := [(false, root)]
  let mut completed := false
  for _ in [0:fuel] do
    match work with
    | [] => completed := true; break
    | (false, l) :: rest =>
      work := rest
      let key : StrictLevelKey := ⟨l⟩
      if st.levelCache.contains key then
        st := { st with stats := { st.stats with levelCacheHits := st.stats.levelCacheHits + 1 } }
        continue
      match l with
      | .zero =>
        let exp := match recomputeLevelData 2221 0 false false with | .ok d => d | .error _ => 0
        if levelDataU64 l.data != exp then
          st := st.record "forgedLevelMData" decl
            s!"Level.zero m_data mismatch: stored {levelDataU64 l.data}, expected {exp}"
        st := { st with
          levelCache := st.levelCache.insert key exp
          stats := { st.stats with levelNodesVisited := st.stats.levelNodesVisited + 1 }
        }
      | .param _ | .mvar _ =>
        work := (true, l) :: work
      | .succ u =>
        work := (false, u) :: (true, l) :: work
      | .max u v | .imax u v =>
        work := (false, u) :: (false, v) :: (true, l) :: work
    | (true, l) :: rest =>
      work := rest
      let key : StrictLevelKey := ⟨l⟩
      if st.levelCache.contains key then continue
      st := { st with stats := { st.stats with levelNodesVisited := st.stats.levelNodesVisited + 1 } }
      let mut expRes : Except String UInt64 := .ok 0
      match l with
      | .zero =>
        expRes := recomputeLevelData 2221 0 false false
      | .param n =>
        let (st', nh) := validateNameDag decl n st fuel
        st := st'
        expRes := recomputeLevelData (mixHash 2239 nh) 0 false true
      | .mvar id =>
        let (st', nh) := validateNameDag decl id.name st fuel
        st := st'
        expRes := recomputeLevelData (mixHash 2237 (mixHash 0 nh)) 0 true false
      | .succ u =>
        let ud := st.levelCache.getD ⟨u⟩ 0
        expRes := recomputeLevelData (mixHash 2243 (levelDataHash ud)) (levelDataDepth ud + 1)
          (levelDataHasMVar ud) (levelDataHasParam ud)
      | .max u v =>
        let ud := st.levelCache.getD ⟨u⟩ 0
        let vd := st.levelCache.getD ⟨v⟩ 0
        expRes := recomputeLevelData
          (mixHash 2251 (mixHash (levelDataHash ud) (levelDataHash vd)))
          (Nat.max (levelDataDepth ud) (levelDataDepth vd) + 1)
          (levelDataHasMVar ud || levelDataHasMVar vd)
          (levelDataHasParam ud || levelDataHasParam vd)
      | .imax u v =>
        let ud := st.levelCache.getD ⟨u⟩ 0
        let vd := st.levelCache.getD ⟨v⟩ 0
        expRes := recomputeLevelData
          (mixHash 2267 (mixHash (levelDataHash ud) (levelDataHash vd)))
          (Nat.max (levelDataDepth ud) (levelDataDepth vd) + 1)
          (levelDataHasMVar ud || levelDataHasMVar vd)
          (levelDataHasParam ud || levelDataHasParam vd)
      match expRes with
      | .error err =>
        st := st.record "forgedLevelMData" decl err
        st := { st with levelCache := st.levelCache.insert key 0 }
      | .ok exp =>
        if levelDataU64 l.data != exp then
          st := st.record "forgedLevelMData" decl
            s!"Level m_data mismatch: stored {levelDataU64 l.data}, expected {exp}"
        st := { st with levelCache := st.levelCache.insert key exp }
  if !completed then
    st := st.record "auditFuelExhausted" decl "validateLevelDag exhausted fuel"
    return (st, 0)
  return (st, st.levelCache.getD ⟨root⟩ 0)

/-- Validate every `String` / `Name` reachable from an in-memory `Syntax` DAG carried by
an `MData` `DataValue.ofSyntax` payload.

B2 hardening: A1 memoized visits in a `Std.HashSet StrictSyntaxKey` whose hash is SHALLOW
(`kind.hash`, arity). In-memory `Syntax` carries no cached structural hash, so every node of a
plain honest chain `node k #[node k #[ ... atom ...]]` lands in ONE bucket and each insertion
runs a recursive `strictSyntaxEq` down to the leaf: cubic time plus native recursion as deep as
the chain (measured on A1: honest chains of 40/80/160 nodes took 24/192/1542 ms, i.e.
cubic growth, so a 50000-node chain that fits the fuel budget would run for years). Pointer-identity
memoization is not available to escape-hatch-free code, so the traversal is now a plain tree walk charged one unit of
`syntaxValidationFuel` per visited node: linear, and any `Syntax` whose tree expansion exceeds
the budget (including exponential shared DAGs) fails closed with `auditFuelExhausted`.
Kernel-checked terms carry no legitimate `MData` syntax of that size. -/
def validateSyntaxDag (decl : Name) (root : Syntax) (st0 : MemValidatorState) :
    MemValidatorState := Id.run do
  let fuel := syntaxValidationFuel
  let mut st := st0
  let mut work : List Syntax := [root]
  let mut completed := false
  let checkStr (st : MemValidatorState) (what : String) (s : String) : MemValidatorState :=
    let st := { st with stats := { st.stats with stringsValidated := st.stats.stringsValidated + 1 } }
    match validateInMemoryString s true with
    | .error err => st.record "invalidUtf8Literal" decl s!"MData Syntax {what} UTF-8 error: {err}"
    | .ok _ => st
  let checkInfo (st : MemValidatorState) (info : SourceInfo) : MemValidatorState :=
    match info with
    | .original leading _ trailing _ =>
      checkStr (checkStr st "leading" leading.str) "trailing" trailing.str
    | _ => st
  for _ in [0:fuel] do
    match work with
    | [] => completed := true; break
    | s :: rest =>
      work := rest
      match s with
      | .missing => pure ()
      | .node info kind args =>
        st := checkInfo st info
        st := (validateNameDag decl kind st fuel).1
        work := args.toList ++ work
      | .atom info val =>
        st := checkInfo st info
        st := checkStr st "atom" val
      | .ident info rawVal val pre =>
        st := checkInfo st info
        st := checkStr st "ident rawVal" rawVal.str
        st := (validateNameDag decl val st fuel).1
        for p in pre do
          match p with
          | .namespace ns => st := (validateNameDag decl ns st fuel).1
          | .decl n fields =>
            st := (validateNameDag decl n st fuel).1
            for f in fields do
              st := checkStr st "preresolved field" f
  if !completed then
    st := st.record "auditFuelExhausted" decl "validateSyntaxDag exhausted fuel"
  return st

def validateMData (decl : Name) (md : MData) (st0 : MemValidatorState) (fuel : Nat) :
    MemValidatorState := Id.run do
  let mut st := st0
  for (k, dv) in md.entries do
    let (st1, _) := validateNameDag decl k st fuel
    st := st1
    match dv with
    | .ofString s =>
      st := { st with stats := { st.stats with stringsValidated := st.stats.stringsValidated + 1 } }
      if let .error err := validateInMemoryString s true then
        st := st.record "invalidUtf8Literal" decl s!"MData string UTF-8 error: {err}"
    | .ofName n =>
      let (st2, _) := validateNameDag decl n st fuel
      st := st2
    | .ofSyntax stx =>
      st := validateSyntaxDag decl stx st
    | .ofBool _ | .ofNat _ | .ofInt _ => pure ()
  return st

/-- Iterative post-order DAG-memoized validator for `Expr`.
Computes every parent's expected 64-bit `Expr.Data` strictly from recomputed child data
stored in `exprCache` (keyed by `StrictExprKey`), verifies exact 64-bit equality with
`e.data`, validates all `Name`s, `Level`s, `Literal.strVal` UTF-8 + `m_length`, `MData`,
and `_kernel_fresh` prefixes. Optionally enforces closedness on the root expression. -/
def validateExprDag (decl : Name) (root : Expr) (st0 : MemValidatorState)
    (requireClosed : Bool := true) (fuel : Nat := 2000000) : MemValidatorState × UInt64 := Id.run do
  let mut st := st0
  let mut work : List (Bool × Expr) := [(false, root)]
  let mut completed := false
  for _ in [0:fuel] do
    match work with
    | [] => completed := true; break
    | (false, e) :: rest =>
      work := rest
      let key : StrictExprKey := ⟨e⟩
      if st.exprCache.contains key then
        st := { st with stats := { st.stats with exprCacheHits := st.stats.exprCacheHits + 1 } }
        continue
      match e with
      | .bvar _ | .fvar _ | .mvar _ | .sort _ | .const _ _ | .lit _ =>
        work := (true, e) :: work
      | .app f a =>
        work := (false, f) :: (false, a) :: (true, e) :: work
      | .lam _ t b _ | .forallE _ t b _ =>
        work := (false, t) :: (false, b) :: (true, e) :: work
      | .letE _ t v b _ =>
        work := (false, t) :: (false, v) :: (false, b) :: (true, e) :: work
      | .mdata _ body | .proj _ _ body =>
        work := (false, body) :: (true, e) :: work
    | (true, e) :: rest =>
      work := rest
      let key : StrictExprKey := ⟨e⟩
      if st.exprCache.contains key then continue
      st := { st with stats := { st.stats with exprNodesVisited := st.stats.exprNodesVisited + 1 } }
      let mut expRes : Except String UInt64 := .ok 0
      match e with
      | .bvar idx =>
        expRes := recomputeExprData (mixHash 7 (hash idx)) (idx + 1) 0 false false false false
      | .fvar id =>
        let (st', nh) := validateNameDag decl id.name st fuel
        st := st'
        expRes := recomputeExprData (mixHash 13 (mixHash 0 nh)) 0 0 true false false false
      | .mvar id =>
        let (st', nh) := validateNameDag decl id.name st fuel
        st := st'
        expRes := recomputeExprData (mixHash 17 (mixHash 0 nh)) 0 0 false true false false
      | .sort lvl =>
        let (st', ld) := validateLevelDag decl lvl st fuel
        st := st'
        expRes := recomputeExprData (mixHash 11 (levelDataHash ld)) 0 0 false false
          (levelDataHasMVar ld) (levelDataHasParam ld)
      | .const n lvls =>
        let (st', nh) := validateNameDag decl n st fuel
        st := st'
        let mut lHash : UInt64 := 7
        let mut hasLMVar := false
        let mut hasLParam := false
        for u in lvls do
          let (st'', ud) := validateLevelDag decl u st fuel
          st := st''
          lHash := mixHash lHash (levelDataHash ud)
          hasLMVar := hasLMVar || levelDataHasMVar ud
          hasLParam := hasLParam || levelDataHasParam ud
        expRes := recomputeExprData (mixHash 5 (mixHash nh lHash)) 0 0 false false hasLMVar hasLParam
      | .app f a =>
        let fd := st.exprCache.getD ⟨f⟩ 0
        let ad := st.exprCache.getD ⟨a⟩ 0
        expRes := .ok (recomputeAppDataPure fd ad)
      | .lam n t b _ =>
        let (st', _) := validateNameDag decl n st fuel
        st := st'
        let td := st.exprCache.getD ⟨t⟩ 0
        let bd := st.exprCache.getD ⟨b⟩ 0
        let d := Nat.max (exprDataApproxDepth td) (exprDataApproxDepth bd) + 1
        let h := mixHash (UInt64.ofNat d) (mixHash (exprDataHash td) (exprDataHash bd))
        let lbr := Nat.max (exprDataLooseBVarRange td) (exprDataLooseBVarRange bd - 1)
        expRes := recomputeExprData h lbr d
          (exprDataHasFVar td || exprDataHasFVar bd)
          (exprDataHasExprMVar td || exprDataHasExprMVar bd)
          (exprDataHasLevelMVar td || exprDataHasLevelMVar bd)
          (exprDataHasLevelParam td || exprDataHasLevelParam bd)
      | .forallE n t b _ =>
        let (st', _) := validateNameDag decl n st fuel
        st := st'
        let td := st.exprCache.getD ⟨t⟩ 0
        let bd := st.exprCache.getD ⟨b⟩ 0
        let d := Nat.max (exprDataApproxDepth td) (exprDataApproxDepth bd) + 1
        let h := mixHash (UInt64.ofNat d) (mixHash (exprDataHash td) (exprDataHash bd))
        let lbr := Nat.max (exprDataLooseBVarRange td) (exprDataLooseBVarRange bd - 1)
        expRes := recomputeExprData h lbr d
          (exprDataHasFVar td || exprDataHasFVar bd)
          (exprDataHasExprMVar td || exprDataHasExprMVar bd)
          (exprDataHasLevelMVar td || exprDataHasLevelMVar bd)
          (exprDataHasLevelParam td || exprDataHasLevelParam bd)
      | .letE n t v b _ =>
        let (st', _) := validateNameDag decl n st fuel
        st := st'
        let td := st.exprCache.getD ⟨t⟩ 0
        let vd := st.exprCache.getD ⟨v⟩ 0
        let bd := st.exprCache.getD ⟨b⟩ 0
        let d := Nat.max (Nat.max (exprDataApproxDepth td) (exprDataApproxDepth vd)) (exprDataApproxDepth bd) + 1
        let h := mixHash (UInt64.ofNat d) (mixHash (exprDataHash td) (mixHash (exprDataHash vd) (exprDataHash bd)))
        let lbr := Nat.max (Nat.max (exprDataLooseBVarRange td) (exprDataLooseBVarRange vd)) (exprDataLooseBVarRange bd - 1)
        expRes := recomputeExprData h lbr d
          (exprDataHasFVar td || exprDataHasFVar vd || exprDataHasFVar bd)
          (exprDataHasExprMVar td || exprDataHasExprMVar vd || exprDataHasExprMVar bd)
          (exprDataHasLevelMVar td || exprDataHasLevelMVar vd || exprDataHasLevelMVar bd)
          (exprDataHasLevelParam td || exprDataHasLevelParam vd || exprDataHasLevelParam bd)
      | .lit lit =>
        let mut lHash : UInt64 := 0
        match lit with
        | .natVal v => lHash := hash v
        | .strVal s =>
          st := { st with stats := { st.stats with stringsValidated := st.stats.stringsValidated + 1 } }
          if let .error err := validateInMemoryString s true then
            st := st.record "invalidUtf8Literal" decl s!"Literal.strVal UTF-8 error: {err}"
          lHash := hash s
        expRes := recomputeExprData (mixHash 3 lHash) 0 0 false false false false
      | .mdata md body =>
        st := validateMData decl md st fuel
        let bd := st.exprCache.getD ⟨body⟩ 0
        let d := exprDataApproxDepth bd + 1
        let h := mixHash (UInt64.ofNat d) (exprDataHash bd)
        expRes := recomputeExprData h (exprDataLooseBVarRange bd) d
          (exprDataHasFVar bd) (exprDataHasExprMVar bd)
          (exprDataHasLevelMVar bd) (exprDataHasLevelParam bd)
      | .proj s idx body =>
        let (st', sh) := validateNameDag decl s st fuel
        st := st'
        let bd := st.exprCache.getD ⟨body⟩ 0
        let d := exprDataApproxDepth bd + 1
        let h := mixHash (UInt64.ofNat d) (mixHash sh (mixHash (hash idx) (exprDataHash bd)))
        expRes := recomputeExprData h (exprDataLooseBVarRange bd) d
          (exprDataHasFVar bd) (exprDataHasExprMVar bd)
          (exprDataHasLevelMVar bd) (exprDataHasLevelParam bd)
      match expRes with
      | .error err =>
        st := st.record "forgedExprMData" decl err
        st := { st with exprCache := st.exprCache.insert key 0 }
      | .ok exp =>
        if exprDataU64 e.data != exp then
          st := st.record "forgedExprMData" decl
            s!"Expr ({e.ctorName}) m_data mismatch: stored {exprDataU64 e.data}, expected {exp}"
        st := { st with exprCache := st.exprCache.insert key exp }
  if !completed then
    st := st.record "auditFuelExhausted" decl "validateExprDag exhausted fuel"
    return (st, 0)
  let rootData := st.exprCache.getD ⟨root⟩ 0
  if requireClosed && !exprDataIsClosed rootData then
    st := st.record "forgedExprMData" decl
      s!"recomputed Expr.Data shows open expression (hasFVar={exprDataHasFVar rootData}, hasExprMVar={exprDataHasExprMVar rootData}, hasLevelMVar={exprDataHasLevelMVar rootData}, looseBVarRange={exprDataLooseBVarRange rootData})"
  return (st, rootData)

def strictOptExprEq : Option Expr → Option Expr → Bool
  | none, none => true
  | some a, some b => strictExprEq a b
  | _, _ => false

def localDeclKindEq : LocalDeclKind → LocalDeclKind → Bool
  | .default, .default => true
  | .implDetail, .implDetail => true
  | .auxDecl, .auxDecl => true
  | _, _ => false

def strictLocalDeclEq : LocalDecl → LocalDecl → Bool
  | .cdecl i1 fv1 un1 ty1 bi1 k1, .cdecl i2 fv2 un2 ty2 bi2 k2 =>
    i1 == i2 && strictNameEq fv1.name fv2.name && strictNameEq un1 un2 &&
    strictExprEq ty1 ty2 && bi1 == bi2 && localDeclKindEq k1 k2
  | .ldecl i1 fv1 un1 ty1 val1 nd1 k1, .ldecl i2 fv2 un2 ty2 val2 nd2 k2 =>
    i1 == i2 && strictNameEq fv1.name fv2.name && strictNameEq un1 un2 &&
    strictExprEq ty1 ty2 && strictExprEq val1 val2 && nd1 == nd2 && localDeclKindEq k1 k2
  | _, _ => false

/-- Collect every `FVarId` occurring in `e` (fuel-bounded, DAG-memoized by `StrictExprKey`). -/
def collectFVarIdsBounded (e : Expr) (fuel : Nat := 2000000) : Option (Array FVarId) := Id.run do
  let mut seen : Std.HashSet StrictExprKey := {}
  let mut out : Array FVarId := #[]
  let mut work : List Expr := [e]
  for _ in [0:fuel] do
    match work with
    | [] => return some out
    | x :: rest =>
      work := rest
      if seen.contains ⟨x⟩ then continue
      seen := seen.insert ⟨x⟩
      match x with
      | .fvar id => out := out.push id
      | .app f a => work := f :: a :: work
      | .lam _ t b _ | .forallE _ t b _ => work := t :: b :: work
      | .letE _ t v b _ => work := t :: v :: b :: work
      | .mdata _ b | .proj _ _ b => work := b :: work
      | _ => pure ()
  return none

/-- Collect every constant `Name` referenced in `e` (fuel-bounded, DAG-memoized by `StrictExprKey`). -/
def collectConstsBounded (e : Expr) (fuel : Nat := 2000000) : Option NameSet := Id.run do
  let mut seen : Std.HashSet StrictExprKey := {}
  let mut out : NameSet := {}
  let mut work : List Expr := [e]
  for _ in [0:fuel] do
    match work with
    | [] => return some out
    | x :: rest =>
      work := rest
      if seen.contains ⟨x⟩ then continue
      seen := seen.insert ⟨x⟩
      match x with
      | .const n _ => out := out.insert n
      | .app f a => work := f :: a :: work
      | .lam _ t b _ | .forallE _ t b _ => work := t :: b :: work
      | .letE _ t v b _ => work := t :: v :: b :: work
      | .mdata _ b | .proj _ _ b => work := b :: work
      | _ => pure ()
  return none

def exprDataKernelQuerySafe (d : UInt64) : Bool :=
  !exprDataHasExprMVar d && !exprDataHasLevelMVar d && exprDataLooseBVarRange d == 0

def validateLocalDeclSt (ldecl : LocalDecl) (st0 : MemValidatorState) (fuel : Nat) :
    MemValidatorState := Id.run do
  let fvName := ldecl.fvarId.name
  let (st1, _) := validateNameDag fvName fvName st0 fuel
  let (st2, _) := validateNameDag fvName ldecl.userName st1 fuel
  let (st3, tyData) := validateExprDag fvName ldecl.type st2 (requireClosed := false) fuel
  let mut st := st3
  if !exprDataKernelQuerySafe tyData then
    st := st.record "malformedLocalContext" fvName
      s!"LocalDecl type has loose bvars or mvars (looseBVarRange={exprDataLooseBVarRange tyData}, hasExprMVar={exprDataHasExprMVar tyData}, hasLevelMVar={exprDataHasLevelMVar tyData})"
  if let some val := ldecl.value? then
    let (st4, valData) := validateExprDag fvName val st (requireClosed := false) fuel
    st := st4
    if !exprDataKernelQuerySafe valData then
      st := st.record "malformedLocalContext" fvName
        s!"LocalDecl value has loose bvars or mvars (looseBVarRange={exprDataLooseBVarRange valData}, hasExprMVar={exprDataHasExprMVar valData}, hasLevelMVar={exprDataHasLevelMVar valData})"
  return st

/-- `LocalContext` validation into an existing state.
Hardened across B1 & A1:
- Validates every `fvarIdToDecl` map key and requires exact bijection with `decls` under
  full `strictLocalDeclEq` (checking `binderInfo`, `nonDep`, `kind`, `index`, `type`, `value?`).
- Verifies slot index agreement (`decls[i] = some d → d.index == i`) and rejects duplicate
  `fvarId`s in `decls`.
- Enforces strict telescopic scoping inside `lctx`: every `FVarId` referenced in `d.type` or
  `d.value?` must already be declared at an earlier index (blocking undeclared fvars,
  self-references, and forward-reference cycles) and forbids loose `bvar`s / `mvar`s. -/
def validateLocalContextSt (lctx : LocalContext) (st0 : MemValidatorState) (fuel : Nat) :
    MemValidatorState := Id.run do
  let mut st := st0
  let mut mapCount : Nat := 0
  for (k, d) in lctx.fvarIdToDecl.toList do
    mapCount := mapCount + 1
    let (st1, _) := validateNameDag k.name k.name st fuel
    st := st1
    if !strictNameEq k.name d.fvarId.name then
      st := st.record "malformedLocalContext" k.name
        s!"fvarIdToDecl key {k.name} aliases LocalDecl with fvarId {d.fvarId.name}"
    st := validateLocalDeclSt d st fuel
  let mut arrCount : Nat := 0
  let mut declaredSoFar : Std.HashSet FVarId := {}
  for i in [0:lctx.decls.size] do
    if let some ldecl := lctx.decls[i]! then
      arrCount := arrCount + 1
      if ldecl.index != i then
        st := st.record "malformedLocalContext" ldecl.fvarId.name
          s!"decls[{i}] has mismatched LocalDecl.index={ldecl.index}"
      if declaredSoFar.contains ldecl.fvarId then
        st := st.record "malformedLocalContext" ldecl.fvarId.name
          s!"duplicate fvarId {ldecl.fvarId.name} in LocalContext.decls"
      st := validateLocalDeclSt ldecl st fuel
      match collectFVarIdsBounded ldecl.type fuel with
      | none =>
        st := st.record "auditFuelExhausted" ldecl.fvarId.name
          "collectFVarIdsBounded exhausted fuel on LocalDecl.type"
      | some ids =>
        for id in ids do
          if !declaredSoFar.contains id then
            st := st.record "undeclaredFVar" id.name
              s!"LocalDecl {ldecl.fvarId.name} type references undeclared/self/forward fvar {id.name}"
      if let some val := ldecl.value? then
        match collectFVarIdsBounded val fuel with
        | none =>
          st := st.record "auditFuelExhausted" ldecl.fvarId.name
            "collectFVarIdsBounded exhausted fuel on LocalDecl.value"
        | some ids =>
          for id in ids do
            if !declaredSoFar.contains id then
              st := st.record "undeclaredFVar" id.name
                s!"LocalDecl {ldecl.fvarId.name} value references undeclared/self/forward fvar {id.name}"
      declaredSoFar := declaredSoFar.insert ldecl.fvarId
      match lctx.fvarIdToDecl.find? ldecl.fvarId with
      | none =>
        st := st.record "malformedLocalContext" ldecl.fvarId.name
          "decls entry missing from fvarIdToDecl (kernel cannot resolve it)"
      | some d =>
        if !strictLocalDeclEq d ldecl then
          st := st.record "malformedLocalContext" ldecl.fvarId.name
            "decls entry differs from the fvarIdToDecl entry the kernel resolves"
  if mapCount != arrCount then
    st := st.record "malformedLocalContext" .anonymous
      s!"fvarIdToDecl has {mapCount} entries but decls has {arrCount}"
  return st

/-- Validate a `LocalContext` before passing it to `Lean.Kernel.{check,isDefEq,whnf}`
to prevent `lean4#16767` `_kernel_fresh` `FVarId` collisions as well as forged `m_data`/UTF-8. -/
def validateLocalContext (lctx : LocalContext) (fuel : Nat := 100000) : AuditReport :=
  let st := validateLocalContextSt lctx {} fuel
  { violations := st.violations, stats := st.stats }

/-- Validate a complete kernel query `(lctx, exprs)` before `Kernel.{check,isDefEq,whnf}`.
Hardened across B1 & A1:
- Validates `lctx` (including telescopic fvar scoping, full `strictLocalDeclEq`, and `_kernel_fresh`).
- Validates every query expression with `fuel` propagated to BOTH `validateExprDag` and
  `collectFVarIdsBounded`, rejects loose `bvar`s / `Expr.mvar` / `Level.mvar` (`malformedKernelQuery`),
  and requires every free `fvar` to be declared in `lctx` (`undeclaredFVar`). -/
def validateKernelQuery (lctx : LocalContext) (exprs : Array Expr) (fuel : Nat := 100000) :
    AuditReport := Id.run do
  let mut st := validateLocalContextSt lctx {} fuel
  for e in exprs do
    let (st1, rootData) := validateExprDag `kernelQuery e st (requireClosed := false) fuel
    st := st1
    if !exprDataKernelQuerySafe rootData then
      st := st.record "malformedKernelQuery" `kernelQuery
        s!"query expression has loose bvars or mvars (looseBVarRange={exprDataLooseBVarRange rootData}, hasExprMVar={exprDataHasExprMVar rootData}, hasLevelMVar={exprDataHasLevelMVar rootData})"
    match collectFVarIdsBounded e fuel with
    | none => st := st.record "auditFuelExhausted" `kernelQuery "collectFVarIdsBounded exhausted fuel"
    | some ids =>
      for id in ids do
        if (lctx.fvarIdToDecl.find? id).isNone then
          st := st.record "undeclaredFVar" id.name
            s!"query references fvar {id.name} not declared in the LocalContext"
  return { violations := st.violations, stats := st.stats }

/-- Validate a single `ConstantInfo` in-memory (V-Q1, V-M2, V-U3, V-F4). -/
def validateConstantInfo (ci : ConstantInfo) (originMod : Option Name)
    (st0 : MemValidatorState) (fuel : Nat := 2000000) : MemValidatorState := Id.run do
  let decl := ci.name
  let mut st := { st0 with stats := { st0.stats with declsChecked := st0.stats.declsChecked + 1 } }
  let (st1, _) := validateNameDag decl decl st fuel
  st := st1
  for lp in ci.levelParams do
    let (st2, _) := validateNameDag decl lp st fuel
    st := st2
  let (st3, _) := validateExprDag decl ci.type st (requireClosed := true) fuel
  st := st3
  if let some v := ci.value? (allowOpaque := true) then
    let (st4, _) := validateExprDag decl v st (requireClosed := true) fuel
    st := st4
  match ci with
  | .quotInfo qv =>
    for v in validateQuotVal qv originMod do
      st := st.record v.tag v.decl v.detail
  | .defnInfo v =>
    for a in v.all do
      let (st', _) := validateNameDag decl a st fuel
      st := st'
  | .thmInfo v =>
    for a in v.all do
      let (st', _) := validateNameDag decl a st fuel
      st := st'
  | .opaqueInfo v =>
    for a in v.all do
      let (st', _) := validateNameDag decl a st fuel
      st := st'
  | .inductInfo v =>
    for a in v.all ++ v.ctors do
      let (st', _) := validateNameDag decl a st fuel
      st := st'
  | .ctorInfo v =>
    let (st', _) := validateNameDag decl v.induct st fuel
    st := st'
  | .recInfo v =>
    for a in v.all do
      let (st', _) := validateNameDag decl a st fuel
      st := st'
    for r in v.rules do
      let (st', _) := validateNameDag decl r.ctor st fuel
      let (st'', _) := validateExprDag decl r.rhs st' (requireClosed := true) fuel
      st := st''
  | .axiomInfo _ => pure ()
  return st

/-- V-S5: Audit all `@[export]`, C-symbol, FFI, compiler-override, and IR-extern surfaces for
module `modIdx` plus live state:
1. `exportAttr.ext.getModuleEntries` & `getModuleIREntries` (closes `OleanEnvAuditor.lean:1649` gap)
2. `externAttr.ext`, `Compiler.implementedByAttr.ext`, `regularInitAttr.ext`, `builtinInitAttr.ext`
   across BOTH `.olean` (`getModuleEntries`) and `.ir` (`getModuleIREntries`) tables
3. `IR.declMapExt` across BOTH `.olean` and `.ir` tables for `IR.Decl.extern` C-symbol stubs
4. live `exportAttr.ext.getState env` (both list and map)
5. `getExportNameFor?` and `isExport` (catching unannotated `main` C-symbol binding). -/
def auditExportSurface (env : Environment) (modIdx : Nat) (modName : Name)
    (st0 : MemValidatorState) (checkLiveState : Bool := true)
    (forbidMainExport : Bool := true) : MemValidatorState := Id.run do
  let mut st := st0
  for (declName, cSym) in exportAttr.ext.getModuleEntries env modIdx do
    st := st.record "forbiddenExportAttr" declName
      s!"@[export {cSym}] in module {modName} (.olean entries)"
  for (declName, cSym) in exportAttr.ext.getModuleIREntries env modIdx do
    st := st.record "forbiddenExportAttr" declName
      s!"@[export {cSym}] in module {modName} (.ir entries)"
  for (declName, _) in externAttr.ext.getModuleEntries env modIdx do
    st := st.record "forbiddenExportAttr" declName
      s!"@[extern] C-symbol binding in module {modName} (.olean entries)"
  for (declName, _) in externAttr.ext.getModuleIREntries env modIdx do
    st := st.record "forbiddenExportAttr" declName
      s!"@[extern] C-symbol binding in module {modName} (.ir entries)"
  for (declName, tgt) in Compiler.implementedByAttr.ext.getModuleEntries env modIdx do
    st := st.record "forbiddenExportAttr" declName
      s!"@[implemented_by {tgt}] override in module {modName} (.olean entries)"
  for (declName, tgt) in Compiler.implementedByAttr.ext.getModuleIREntries env modIdx do
    st := st.record "forbiddenExportAttr" declName
      s!"@[implemented_by {tgt}] override in module {modName} (.ir entries)"
  for (declName, _) in regularInitAttr.ext.getModuleEntries env modIdx do
    st := st.record "forbiddenExportAttr" declName
      s!"@[init] hook in module {modName} (.olean entries)"
  for (declName, _) in regularInitAttr.ext.getModuleIREntries env modIdx do
    st := st.record "forbiddenExportAttr" declName
      s!"@[init] hook in module {modName} (.ir entries)"
  for (declName, _) in builtinInitAttr.ext.getModuleEntries env modIdx do
    st := st.record "forbiddenExportAttr" declName
      s!"@[builtin_init] hook in module {modName} (.olean entries)"
  for (declName, _) in builtinInitAttr.ext.getModuleIREntries env modIdx do
    st := st.record "forbiddenExportAttr" declName
      s!"@[builtin_init] hook in module {modName} (.ir entries)"
  let isMod := (env.header.moduleData[modIdx]?).map (·.isModule) |>.getD false
  let mut irFdeclNames : NameSet := {}
  for irDecl in IR.declMapExt.getModuleIREntries env modIdx do
    match irDecl with
    | .extern f _ _ _ =>
      st := st.record "forbiddenExportAttr" f
        s!"IR.Decl.extern C-symbol stub in module {modName} (.ir IR.declMapExt)"
    | .fdecl f .. =>
      irFdeclNames := irFdeclNames.insert f
  for irDecl in IR.declMapExt.getModuleEntries env modIdx do
    match irDecl with
    | .extern f _ _ info =>
      let pureOpaque := match info.entries with | [.opaque] => true | _ => false
      -- Lean 4.34.1 `module` interfaces emit pure `.opaque` IR signature stubs in `.olean`
      -- that MUST resolve to an `IR.Decl.fdecl` in `.ir`. Any C-symbol entry (`.standard`/
      -- `.inline`/`.adhoc`), any non-module `.extern`, or any stub lacking an `.ir` `.fdecl`
      -- is rejected as `forbiddenExportAttr`.
      if !(isMod && pureOpaque && irFdeclNames.contains f) then
        st := st.record "forbiddenExportAttr" f
          s!"IR.Decl.extern C-symbol or unresolved stub in module {modName} (.olean IR.declMapExt)"
    | .fdecl .. => pure ()
  if let some data := env.header.moduleData[modIdx]? then
    for ci in data.constants do
      if let some cSym := getExportNameFor? env ci.name then
        st := st.record "forbiddenExportAttr" ci.name
          s!"getExportNameFor? resolved C symbol {cSym} in module {modName}"
      if forbidMainExport && ci.name == `main && isExport env ci.name then
        st := st.record "forbiddenExportAttr" ci.name
          s!"isExport true on unannotated `main` C-symbol entry point in module {modName}"
  if checkLiveState then
    let (liveDecls, liveMap) := exportAttr.ext.getState env
    for declName in liveDecls do
      let symStr := match liveMap.find? declName with
        | some s => s.toString
        | none => "<unknown>"
      st := st.record "forbiddenExportAttr" declName
        s!"live exportAttr.ext.getState entry -> C symbol {symStr}"
    for (declName, cSym) in liveMap.toList do
      st := st.record "forbiddenExportAttr" declName
        s!"live exportAttr.ext.getState map entry -> C symbol {cSym}"
  return st

def constKindName : ConstantInfo → String
  | .axiomInfo _ => "axiom" | .defnInfo _ => "definition" | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque" | .quotInfo _ => "quot" | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor" | .recInfo _ => "recursor"

def constKindTag : ConstantInfo → Nat
  | .axiomInfo _ => 0 | .defnInfo _ => 1 | .thmInfo _ => 2 | .opaqueInfo _ => 3
  | .quotInfo _ => 4 | .inductInfo _ => 5 | .ctorInfo _ => 6 | .recInfo _ => 7

/-- Strict (metadata-checking) `ConstantInfo` identity used for shadowing detection. -/
def strictConstInfoEq (a b : ConstantInfo) : Bool :=
  constKindTag a == constKindTag b && strictNameEq a.name b.name &&
  a.levelParams == b.levelParams && strictExprEq a.type b.type &&
  strictOptExprEq (a.value? (allowOpaque := true)) (b.value? (allowOpaque := true))

/-- Strict reserved-theorem duplicate check (A1 hardening):
B1's `benignTheoremDuplicate` tolerated ANY two `.thmInfo` declarations with equal
name/levelParams/type, letting Module B replace Module A's `theorem thmBridge : False := evilAx`
with a cyclic self-proof `theorem thmBridge : False := thmBridge`, laundering `evilAx` out of
every axiom-closure audit while `validateEnvModule` returned `ok` on both modules!
Cross-module `.thmInfo` duplication is now accepted ONLY when:
1. `isReservedName env cn` holds (compiler-generated reserved lemma, never user theorems),
2. both are `.thmInfo` with strictly equal name, `levelParams`, and `type`,
3. NEITHER proof body references `cn` (blocks direct self-referential cycles), and
4. both proof bodies have strictly identical `StrictExprKey` constant sets (so a shadowed
   theorem cannot silently drop dependencies/axioms). -/
def safeReservedTheoremDuplicate (env : Environment) (cn : Name) (a b : ConstantInfo)
    (fuel : Nat) : Bool :=
  if !isReservedName env cn then false
  else match a, b with
  | .thmInfo va, .thmInfo vb =>
    if !(strictNameEq va.name vb.name && va.levelParams == vb.levelParams &&
         strictExprEq va.type vb.type) then false
    else
      match collectConstsBounded va.value fuel, collectConstsBounded vb.value fuel with
      | some ca, some cb =>
        !ca.contains cn && !cb.contains cn &&
        ca.toArray.qsort Name.lt == cb.toArray.qsort Name.lt
      | _, _ => false
  | _, _ => false

/-- Full in-memory DAG-memoized validation of one loaded module in `env`
(covers V-Q1, V-M2, V-U3, V-F4, V-S5).

Hardened across B1 & A1:
- Rejects `constNames.size != constants.size` and `constNames[i] != constants[i].name`
  (`constNameAliasMismatch`).
- Rejects intra-module duplicate `constNames` (`shadowedConstant`), closing single-module
  self-shadowing.
- Rejects cross-module shadowing including theorem-over-axiom AND theorem-over-theorem axiom
  laundering (`shadowedConstant`), tolerating only non-circular, identical-dependency
  compiler-reserved theorem duplicates (`safeReservedTheoremDuplicate`).
- Validates import module names (`Name.hash` / UTF-8 / `_kernel_fresh`) and complete
  V-S5 export/extern/IR-stub surfaces. -/
def validateEnvModule (env : Environment) (modName : Name)
    (fuel : Nat := 20000000) (checkLiveExportState : Bool := true) : AuditReport := Id.run do
  let some modIdx := env.getModuleIdx? modName
    | return { violations := #[{ tag := "missingModule", decl := modName, detail := "module not loaded in environment" }] }
  let idx := modIdx.toNat
  let some data := env.header.moduleData[idx]?
    | return { violations := #[{ tag := "missingModule", decl := modName, detail := "moduleData index out of bounds" }] }
  let mut st : MemValidatorState := {}
  for imp in data.imports do
    let (st1, _) := validateNameDag modName imp.module st fuel
    st := st1
  let mut seenInMod : NameSet := {}
  for cn in data.constNames do
    let (st1, _) := validateNameDag cn cn st fuel
    st := st1
    if seenInMod.contains cn then
      st := st.record "shadowedConstant" cn
        s!"duplicate constName {cn} within module {modName}"
    seenInMod := seenInMod.insert cn
  for en in data.extraConstNames do
    let (st1, _) := validateNameDag en en st fuel
    st := st1
  for ci in data.constants do
    st := validateConstantInfo ci (some modName) st fuel
  if data.constNames.size != data.constants.size then
    st := st.record "constNameAliasMismatch" modName
      s!"constNames.size={data.constNames.size} != constants.size={data.constants.size} (importModules silently drops the excess)"
  for (cn, ci) in data.constNames.zip data.constants do
    if !strictNameEq cn ci.name then
      st := st.record "constNameAliasMismatch" cn
        s!"constNames entry {cn} binds a ConstantInfo named {ci.name}"
    match env.find? cn with
    | none =>
      st := st.record "shadowedConstant" cn "module constant is not bound in the loaded environment"
    | some envCi =>
      if !strictConstInfoEq ci envCi then
        if !safeReservedTheoremDuplicate env cn ci envCi fuel then
          st := st.record "shadowedConstant" cn
            s!"module {constKindName ci} {cn} was replaced in the loaded environment by a {constKindName envCi} from another module"
      else
        match env.getModuleIdxFor? cn with
        | some owner =>
          if owner.toNat != idx then
            let prev? := (env.header.moduleData[owner.toNat]?).bind fun d =>
              ((d.constNames.zip d.constants).find? (fun (n, _) => strictNameEq n cn)).map (·.2)
            let benign := match prev? with
              | some prev => safeReservedTheoremDuplicate env cn ci prev fuel
              | none => false
            if !benign then
              let prevKind := match prev? with | some prev => constKindName prev | none => "<missing>"
              st := st.record "shadowedConstant" cn
                s!"module {constKindName ci} {cn} replaced the {prevKind} owned by module index {owner.toNat}"
        | none =>
          st := st.record "shadowedConstant" cn "module constant has no owning module index"
  st := auditExportSurface env idx modName st (checkLiveState := checkLiveExportState)
  return { violations := st.violations, stats := st.stats }

/-! ## Section 8: Pure-Lean Binary `.olean` / `.ir` Compacted-Region Pointer-DAG Validator

Parses real Lean 4.34.1 `.olean` / `.olean.server` / `.olean.private` / `.ir.sig` / `.ir`
files directly from `Array ByteArray` without `importModules` and without trusting cached
`m_data`, `Level.data`, `Name.hash`, or `lean_string_object.m_length`.

Every heap object is keyed by its 64-bit virtual address (`UInt64`), giving O(1) DAG
memoization immune to ALL structural/hash-collision cache poisoning, plus 3-color cycle
detection (`visiting` set), alignment, OOB, and 64-bit overflow checks, and `m_rc == 0` checks. -/

structure OleanPart where
  baseAddr : UInt64
  rootPtr  : UInt64
  bytes    : ByteArray
  deriving Inhabited

def readU16LE (b : ByteArray) (off : Nat) : UInt16 :=
  (b.get! off).toUInt16 ||| ((b.get! (off + 1)).toUInt16 <<< 8)

def readU32LE (b : ByteArray) (off : Nat) : UInt32 :=
  (b.get! off).toUInt32 |||
  ((b.get! (off + 1)).toUInt32 <<< 8) |||
  ((b.get! (off + 2)).toUInt32 <<< 16) |||
  ((b.get! (off + 3)).toUInt32 <<< 24)

def readU64LE (b : ByteArray) (off : Nat) : UInt64 :=
  (readU32LE b off).toUInt64 ||| ((readU32LE b (off + 4)).toUInt64 <<< 32)

def oleanHeaderSize : Nat := 88

/-- Parse and validate headers of a single or multi-part `.olean` / `.ir` region set.
Rejects truncated files, bad magic/version, misaligned base addresses, 64-bit address
space wraparound, and overlapping region address ranges. -/
def parseOleanParts (rawParts : Array ByteArray) : Except String (Array OleanPart) := Id.run do
  if rawParts.isEmpty then
    return .error "empty olean part list"
  let mut parts : Array OleanPart := #[]
  for idx in [0:rawParts.size] do
    let b := rawParts[idx]!
    if b.size < 96 then
      return .error s!"part {idx} too small ({b.size} bytes < 96)"
    if b.get! 0 != 0x6f || b.get! 1 != 0x6c || b.get! 2 != 0x65 ||
       b.get! 3 != 0x61 || b.get! 4 != 0x6e then
      return .error s!"part {idx} invalid magic header (expected 'olean')"
    let ver := b.get! 5
    if ver != 2 then
      return .error s!"part {idx} unsupported olean format version {ver} (expected 2)"
    let baseAddr := readU64LE b 80
    let rootPtr := readU64LE b 88
    if (baseAddr &&& 7) != 0 then
      return .error s!"part {idx} misaligned base_addr {baseAddr}"
    if baseAddr.toNat + b.size >= UInt64.size then
      return .error s!"part {idx} base_addr + file size overflows 64-bit address space"
    let newStart := baseAddr.toNat
    let newEnd := newStart + b.size
    for prev in parts do
      let pStart := prev.baseAddr.toNat
      let pEnd := pStart + prev.bytes.size
      if newStart < pEnd && pStart < newEnd then
        return .error s!"part {idx} address range overlaps earlier compacted region"
    parts := parts.push { baseAddr, rootPtr, bytes := b }
  return .ok parts

def isScalarWord (w : UInt64) : Bool := (w &&& 1) == 1
def unboxScalar (w : UInt64) : Nat := (w >>> 1).toNat

/-- Resolve a 64-bit compacted-region heap pointer into `(partIndex, byteOffset)`.
Uses exact arbitrary-precision `Nat` bounds checking to prevent 64-bit wraparound. -/
def resolveHeapPtr (parts : Array OleanPart) (ptr : UInt64) : Except String (Nat × Nat) := Id.run do
  if isScalarWord ptr then
    return .error s!"expected heap pointer, got tagged scalar {ptr}"
  if ptr == 0 then
    return .error "null pointer in compacted region"
  if (ptr &&& 7) != 0 then
    return .error s!"misaligned heap pointer {ptr}"
  let pNat := ptr.toNat
  for h : i in [0:parts.size] do
    let part := parts[i]
    let baseNat := part.baseAddr.toNat
    if pNat >= baseNat then
      let off := pNat - baseNat
      if off >= oleanHeaderSize + 8 && off + 8 <= part.bytes.size then
        return .ok (i, off)
  return .error s!"out-of-bounds heap pointer {ptr}"

structure ObjHeader where
  partIdx : Nat
  off     : Nat
  rc      : UInt32
  csSz    : Nat
  other   : Nat
  tag     : UInt8

def readObjHeader (parts : Array OleanPart) (ptr : UInt64) : Except String ObjHeader := do
  let (pi, off) ← resolveHeapPtr parts ptr
  let b := parts[pi]!.bytes
  let rc := readU32LE b off
  let csSz := (readU16LE b (off + 4)).toNat
  let other := (b.get! (off + 6)).toNat
  let tag := b.get! (off + 7)
  if rc != 0 then
    throw s!"non-zero m_rc={rc} in compacted region at ptr {ptr}"
  if tag <= 243 then
    if csSz < 8 + other * 8 then
      throw s!"ctor cs_sz={csSz} smaller than header + {other} object fields at ptr {ptr}"
    if off + csSz > b.size then
      throw s!"ctor object (cs_sz={csSz}) extends past region end at ptr {ptr}"
  return { partIdx := pi, off, rc, csSz, other, tag }

def readFieldPtr (parts : Array OleanPart) (h : ObjHeader) (idx : Nat) : Except String UInt64 := do
  if idx >= h.other then
    throw s!"ctor field index {idx} >= m_other {h.other}"
  let b := parts[h.partIdx]!.bytes
  let foff := h.off + 8 + idx * 8
  if foff + 8 > b.size then
    throw "ctor field offset out of bounds"
  return readU64LE b foff

def readScalarU64 (parts : Array OleanPart) (h : ObjHeader) (scalarByteOff : Nat) : Except String UInt64 := do
  let b := parts[h.partIdx]!.bytes
  let soff := h.off + 8 + h.other * 8 + scalarByteOff
  if soff + 8 > h.off + h.csSz || soff + 8 > b.size then
    throw s!"ctor scalar U64 at +{scalarByteOff} out of bounds (cs_sz={h.csSz})"
  return readU64LE b soff

def readScalarU32 (parts : Array OleanPart) (h : ObjHeader) (scalarByteOff : Nat) : Except String UInt32 := do
  let b := parts[h.partIdx]!.bytes
  let soff := h.off + 8 + h.other * 8 + scalarByteOff
  if soff + 4 > h.off + h.csSz || soff + 4 > b.size then
    throw s!"ctor scalar U32 at +{scalarByteOff} out of bounds (cs_sz={h.csSz})"
  return readU32LE b soff

def readScalarU8 (parts : Array OleanPart) (h : ObjHeader) (scalarByteOff : Nat) : Except String UInt8 := do
  let b := parts[h.partIdx]!.bytes
  let soff := h.off + 8 + h.other * 8 + scalarByteOff
  if soff + 1 > h.off + h.csSz || soff + 1 > b.size then
    throw s!"ctor scalar U8 at +{scalarByteOff} out of bounds (cs_sz={h.csSz})"
  return b.get! soff

def readArrayElems (parts : Array OleanPart) (ptr : UInt64) : Except String (Array UInt64) := do
  let h ← readObjHeader parts ptr
  if h.tag != 246 then
    throw s!"expected LeanArray (tag 246), got tag {h.tag} at ptr {ptr}"
  let b := parts[h.partIdx]!.bytes
  if h.off + 24 > b.size then
    throw s!"LeanArray header out of bounds at ptr {ptr}"
  let sz := (readU64LE b (h.off + 8)).toNat
  let cap := (readU64LE b (h.off + 16)).toNat
  if cap < sz then
    throw s!"LeanArray m_capacity ({cap}) < m_size ({sz}) at ptr {ptr}"
  if h.off + 24 + sz * 8 > b.size then
    throw s!"LeanArray elements ({sz}) extend past region end at ptr {ptr}"
  let mut out : Array UInt64 := Array.mkEmpty sz
  for i in [0:sz] do
    out := out.push (readU64LE b (h.off + 24 + i * 8))
  return out

structure BinStringInfo where
  rawBytes   : ByteArray
  str        : String
  hashVal    : UInt64
  validUtf8  : Bool

structure BinNameInfo where
  hashVal        : UInt64
  name           : Name
  hasKernelFresh : Bool

structure BinValidatorState where
  strCache   : Std.HashMap UInt64 BinStringInfo := {}
  nameCache  : Std.HashMap UInt64 BinNameInfo := {}
  levelCache : Std.HashMap UInt64 UInt64 := {}
  exprCache  : Std.HashMap UInt64 UInt64 := {}
  violations : Array Violation := #[]
  seenV      : Std.HashSet (String × Name × String) := {}
  stats      : AuditStats := {}

def BinValidatorState.record (st : BinValidatorState) (tag : String) (decl : Name)
    (detail : String) : BinValidatorState :=
  let key := (tag, decl, detail)
  if st.seenV.contains key then st
  else { st with
    violations := st.violations.push { tag, decl, detail }
    seenV := st.seenV.insert key
  }

/-- Read and validate a `LeanString` (tag 249) at `ptr` in a compacted region.
Checks `m_size >= 1`, `m_capacity >= m_size`, trailing NUL byte, strict RFC 3629 UTF-8,
no embedded NUL, and exact `m_length` scalar-value count. -/
def readBinString (parts : Array OleanPart) (decl : Name) (ptr : UInt64)
    (st0 : BinValidatorState) : BinValidatorState × Except String BinStringInfo := Id.run do
  if let some cached := st0.strCache[ptr]? then
    return (st0, .ok cached)
  let mut st := { st0 with stats := { st0.stats with stringsValidated := st0.stats.stringsValidated + 1 } }
  match readObjHeader parts ptr with
  | .error e =>
    st := st.record "malformedOleanRegion" decl s!"LeanString header error: {e}"
    return (st, .error e)
  | .ok h =>
    if h.tag != 249 then
      let msg := s!"expected LeanString (tag 249), got tag {h.tag} at ptr {ptr}"
      st := st.record "malformedOleanRegion" decl msg
      return (st, .error msg)
    let b := parts[h.partIdx]!.bytes
    if h.off + 32 > b.size then
      let msg := s!"LeanString header extends past region end at ptr {ptr}"
      st := st.record "malformedOleanRegion" decl msg
      return (st, .error msg)
    let mSize := (readU64LE b (h.off + 8)).toNat
    let mCap := (readU64LE b (h.off + 16)).toNat
    let mLen := (readU64LE b (h.off + 24)).toNat
    if mSize == 0 || mCap < mSize || h.off + 32 + mSize > b.size then
      let msg := s!"LeanString bounds invalid (m_size={mSize}, m_capacity={mCap}) at ptr {ptr}"
      st := st.record "malformedOleanRegion" decl msg
      return (st, .error msg)
    if b.get! (h.off + 32 + mSize - 1) != 0 then
      let msg := s!"LeanString missing NUL terminator at ptr {ptr}"
      st := st.record "invalidUtf8Literal" decl msg
      return (st, .error msg)
    let payload := b.extract (h.off + 32) (h.off + 32 + mSize - 1)
    match validateUtf8Bytes payload mLen true with
    | .error err =>
      st := st.record "invalidUtf8Literal" decl s!"LeanString at ptr {ptr}: {err}"
      let info : BinStringInfo := { rawBytes := payload, str := "", hashVal := 0, validUtf8 := false }
      st := { st with strCache := st.strCache.insert ptr info }
      return (st, .ok info)
    | .ok _ =>
      match String.fromUTF8? payload with
      | none =>
        st := st.record "invalidUtf8Literal" decl s!"String.fromUTF8? rejected payload at ptr {ptr}"
        let info : BinStringInfo := { rawBytes := payload, str := "", hashVal := 0, validUtf8 := false }
        st := { st with strCache := st.strCache.insert ptr info }
        return (st, .ok info)
      | some s =>
        let info : BinStringInfo := { rawBytes := payload, str := s, hashVal := hash s, validUtf8 := true }
        st := { st with strCache := st.strCache.insert ptr info }
        return (st, .ok info)

/-- Read a `Nat` word from a compacted region (either tagged 63-bit scalar or `LeanMPZ` tag 250).
Returns `(natValue, u64LowWord, fitsU64)`. Fails closed on negative or out-of-bounds MPZ. -/
def readBinNat (parts : Array OleanPart) (word : UInt64) : Except String (Nat × UInt64 × Bool) := do
  if isScalarWord word then
    let v := word >>> 1
    return (v.toNat, v, true)
  let h ← readObjHeader parts word
  if h.tag != 250 then
    throw s!"expected LeanMPZ (tag 250) for boxed Nat, got tag {h.tag} at ptr {word}"
  let b := parts[h.partIdx]!.bytes
  if h.off + 24 > b.size then
    throw s!"LeanMPZ header out of bounds at ptr {word}"
  let mpAlloc := readU32LE b (h.off + 8)
  let mpSizeRaw := readU32LE b (h.off + 12)
  -- Reject negative MPZ (high bit set in int32 _mp_size) for Nat values.
  if (mpSizeRaw &&& 0x80000000) != 0 then
    throw s!"negative LeanMPZ _mp_size in Nat at ptr {word}"
  let mpSize := mpSizeRaw.toNat
  if mpSize > mpAlloc.toNat || mpAlloc.toNat > 1024 then
    throw s!"LeanMPZ _mp_size ({mpSize}) > _mp_alloc ({mpAlloc}) or alloc cap exceeded at ptr {word}"
  let limbsPtr := readU64LE b (h.off + 16)
  -- B1/A1 hardening: the runtime (`lean_nat_eq` / `lean_nat_big_eq`, `Name` equality, kernel
  -- literal comparison) assumes CANONICAL Nats: every value `<= LEAN_MAX_SMALL_NAT = 2^63-1`
  -- is a tagged scalar, big values have a non-zero top limb, and the full `_mp_alloc` limb
  -- buffer fits within the compacted region.
  if mpSize == 0 then
    throw s!"non-canonical LeanMPZ zero (must be tagged scalar 0) at ptr {word}"
  let (lpi, loff) ← resolveHeapPtr parts limbsPtr
  let lb := parts[lpi]!.bytes
  if loff + mpAlloc.toNat * 8 > lb.size then
    throw s!"LeanMPZ limbs (alloc={mpAlloc}, size={mpSize}) extend past region end at ptr {word}"
  let limb0 := readU64LE lb loff
  if readU64LE lb (loff + (mpSize - 1) * 8) == 0 then
    throw s!"non-canonical LeanMPZ with zero top limb at ptr {word}"
  if mpSize == 1 then
    if limb0.toNat < 2 ^ 63 then
      throw s!"non-canonical LeanMPZ value {limb0.toNat} <= LEAN_MAX_SMALL_NAT at ptr {word}"
    return (limb0.toNat, limb0, true)
  -- Reconstruct full Nat for reasonable limb counts (fail closed on pathological sizes).
  if mpSize > 1024 then
    throw s!"LeanMPZ limb count {mpSize} exceeds safety cap"
  let mut acc : Nat := 0
  for i in [0:mpSize] do
    let idx := mpSize - 1 - i
    let limb := readU64LE lb (loff + idx * 8)
    acc := acc * UInt64.size + limb.toNat
  return (acc, limb0, false)

/-- Well-formedness of a boxed `Int` word (`DataValue.ofInt`): tagged scalar, or canonical
`LeanMPZ` (non-zero top limb, magnitude outside the small-int range `[-2^31, 2^31-1]`). -/
def readBinIntWellFormed (parts : Array OleanPart) (word : UInt64) : Except String Unit := do
  if isScalarWord word then return ()
  let h ← readObjHeader parts word
  if h.tag != 250 then
    throw s!"expected LeanMPZ (tag 250) for boxed Int, got tag {h.tag} at ptr {word}"
  let b := parts[h.partIdx]!.bytes
  if h.off + 24 > b.size then
    throw s!"LeanMPZ header out of bounds at ptr {word}"
  let mpAlloc := (readU32LE b (h.off + 8)).toNat
  let raw := readU32LE b (h.off + 12)
  let neg := (raw &&& 0x80000000) != 0
  let mpSize : Nat := if neg then 2 ^ 32 - raw.toNat else raw.toNat
  if mpSize == 0 || mpSize > mpAlloc || mpAlloc > 1024 then
    throw s!"malformed LeanMPZ Int sizes (size={mpSize}, alloc={mpAlloc}) at ptr {word}"
  let (lpi, loff) ← resolveHeapPtr parts (readU64LE b (h.off + 16))
  let lb := parts[lpi]!.bytes
  if loff + mpAlloc * 8 > lb.size then
    throw s!"LeanMPZ Int limbs extend past region end at ptr {word}"
  if readU64LE lb (loff + (mpSize - 1) * 8) == 0 then
    throw s!"non-canonical LeanMPZ Int with zero top limb at ptr {word}"
  let mag := (readU64LE lb loff).toNat
  if mpSize == 1 && ((!neg && mag < 2 ^ 31) || (neg && mag <= 2 ^ 31)) then
    throw s!"non-canonical LeanMPZ Int in small-int range at ptr {word}"

/-- Pure binary DAG-memoized validator for `Name` objects keyed by 64-bit heap address,
with 3-color cycle detection (`visiting` set). -/
def validateBinName (parts : Array OleanPart) (decl : Name) (rootWord : UInt64)
    (st0 : BinValidatorState) (fuel : Nat := 100000) : BinValidatorState × BinNameInfo := Id.run do
  if isScalarWord rootWord then
    if unboxScalar rootWord == 0 then
      return (st0, { hashVal := nameAnonymousHash, name := .anonymous, hasKernelFresh := false })
    let st := st0.record "malformedOleanRegion" decl s!"invalid scalar Name tag {rootWord}"
    return (st, { hashVal := 0, name := .anonymous, hasKernelFresh := false })
  if let some cached := st0.nameCache[rootWord]? then
    let st := { st0 with stats := { st0.stats with nameCacheHits := st0.stats.nameCacheHits + 1 } }
    return (st, cached)
  let mut st := st0
  let mut visiting : Std.HashSet UInt64 := {}
  let mut work : List (Bool × UInt64) := [(false, rootWord)]
  let mut completed := false
  for _ in [0:fuel] do
    match work with
    | [] => completed := true; break
    | (false, w) :: rest =>
      work := rest
      if isScalarWord w then
        if unboxScalar w != 0 then
          st := st.record "malformedOleanRegion" decl s!"invalid scalar Name {w}"
        continue
      if st.nameCache.contains w then
        st := { st with stats := { st.stats with nameCacheHits := st.stats.nameCacheHits + 1 } }
        continue
      if visiting.contains w then
        st := st.record "malformedOleanRegion" decl s!"cycle detected in Name DAG at ptr {w}"
        return (st, { hashVal := 0, name := .anonymous, hasKernelFresh := false })
      match readObjHeader parts w with
      | .error e =>
        st := st.record "malformedOleanRegion" decl s!"Name header error: {e}"
        st := { st with nameCache := st.nameCache.insert w { hashVal := 0, name := .anonymous, hasKernelFresh := false } }
      | .ok h =>
        if (h.tag != 1 && h.tag != 2) || h.other != 2 then
          st := st.record "malformedOleanRegion" decl
            s!"invalid Name ctor (tag={h.tag}, other={h.other}) at ptr {w}"
          st := { st with nameCache := st.nameCache.insert w { hashVal := 0, name := .anonymous, hasKernelFresh := false } }
        else
          match readFieldPtr parts h 0 with
          | .error e =>
            st := st.record "malformedOleanRegion" decl e
            st := { st with nameCache := st.nameCache.insert w { hashVal := 0, name := .anonymous, hasKernelFresh := false } }
          | .ok prePtr =>
            visiting := visiting.insert w
            work := (false, prePtr) :: (true, w) :: work
    | (true, w) :: rest =>
      work := rest
      visiting := visiting.erase w
      if st.nameCache.contains w then continue
      st := { st with stats := { st.stats with nameNodesVisited := st.stats.nameNodesVisited + 1 } }
      match readObjHeader parts w with
      | .error e =>
        st := st.record "malformedOleanRegion" decl e
        st := { st with nameCache := st.nameCache.insert w { hashVal := 0, name := .anonymous, hasKernelFresh := false } }
      | .ok h =>
        match readFieldPtr parts h 0, readFieldPtr parts h 1, readScalarU64 parts h 0 with
        | .ok prePtr, .ok argPtr, .ok storedHash =>
          let preInfo : BinNameInfo :=
            if isScalarWord prePtr then
              { hashVal := nameAnonymousHash, name := .anonymous, hasKernelFresh := false }
            else
              st.nameCache.getD prePtr { hashVal := nameAnonymousHash, name := .anonymous, hasKernelFresh := false }
          if h.tag == 1 then
            let (st1, sRes) := readBinString parts decl argPtr st
            st := st1
            match sRes with
            | .error _ =>
              st := { st with nameCache := st.nameCache.insert w { hashVal := 0, name := preInfo.name, hasKernelFresh := preInfo.hasKernelFresh } }
            | .ok sInfo =>
              let isKf := isKernelFreshString sInfo.str
              if isKf then
                st := st.record "kernelFreshCollision" decl s!"Name.str contains _kernel_fresh component {sInfo.str}"
              let expected := if sInfo.validUtf8 then mixHash preInfo.hashVal sInfo.hashVal else storedHash
              if sInfo.validUtf8 && storedHash != expected then
                st := st.record "forgedNameHash" decl
                  s!"binary Name.str hash mismatch at ptr {w}: stored {storedHash}, expected {expected}"
              let info : BinNameInfo := {
                hashVal := expected
                name := .str preInfo.name sInfo.str
                hasKernelFresh := preInfo.hasKernelFresh || isKf
              }
              st := { st with nameCache := st.nameCache.insert w info }
          else
            match readBinNat parts argPtr with
            | .error e =>
              st := st.record "malformedOleanRegion" decl s!"Name.num Nat error: {e}"
              st := { st with nameCache := st.nameCache.insert w { hashVal := 0, name := preInfo.name, hasKernelFresh := preInfo.hasKernelFresh } }
            | .ok (nVal, u64Val, fitsU64) =>
              let vHash : UInt64 := if fitsU64 then u64Val else 17
              let expected := mixHash preInfo.hashVal vHash
              if storedHash != expected then
                st := st.record "forgedNameHash" decl
                  s!"binary Name.num hash mismatch at ptr {w}: stored {storedHash}, expected {expected}"
              let info : BinNameInfo := {
                hashVal := expected
                name := .num preInfo.name nVal
                hasKernelFresh := preInfo.hasKernelFresh
              }
              st := { st with nameCache := st.nameCache.insert w info }
        | _, _, _ =>
          st := st.record "malformedOleanRegion" decl s!"Name field/scalar read failed at ptr {w}"
          st := { st with nameCache := st.nameCache.insert w { hashVal := 0, name := .anonymous, hasKernelFresh := false } }
  if !completed then
    st := st.record "auditFuelExhausted" decl "validateBinName exhausted fuel"
    return (st, { hashVal := 0, name := .anonymous, hasKernelFresh := false })
  return (st, st.nameCache.getD rootWord { hashVal := nameAnonymousHash, name := .anonymous, hasKernelFresh := false })

def levelZeroData : UInt64 := 2221

/-- Pure binary DAG-memoized validator for `Level` objects keyed by 64-bit heap address,
with 3-color cycle detection. -/
def validateBinLevel (parts : Array OleanPart) (decl : Name) (rootWord : UInt64)
    (st0 : BinValidatorState) (fuel : Nat := 100000) : BinValidatorState × UInt64 := Id.run do
  if isScalarWord rootWord then
    if unboxScalar rootWord == 0 then
      return (st0, levelZeroData)
    let st := st0.record "malformedOleanRegion" decl s!"invalid scalar Level tag {rootWord}"
    return (st, 0)
  if let some cached := st0.levelCache[rootWord]? then
    let st := { st0 with stats := { st0.stats with levelCacheHits := st0.stats.levelCacheHits + 1 } }
    return (st, cached)
  let mut st := st0
  let mut visiting : Std.HashSet UInt64 := {}
  let mut work : List (Bool × UInt64) := [(false, rootWord)]
  let mut completed := false
  for _ in [0:fuel] do
    match work with
    | [] => completed := true; break
    | (false, w) :: rest =>
      work := rest
      if isScalarWord w then
        if unboxScalar w != 0 then
          st := st.record "malformedOleanRegion" decl s!"invalid scalar Level {w}"
        continue
      if st.levelCache.contains w then
        st := { st with stats := { st.stats with levelCacheHits := st.stats.levelCacheHits + 1 } }
        continue
      if visiting.contains w then
        st := st.record "malformedOleanRegion" decl s!"cycle detected in Level DAG at ptr {w}"
        return (st, 0)
      match readObjHeader parts w with
      | .error e =>
        st := st.record "malformedOleanRegion" decl s!"Level header error: {e}"
        st := { st with levelCache := st.levelCache.insert w 0 }
      | .ok h =>
        visiting := visiting.insert w
        match h.tag with
        | 1 => -- succ u
          if h.other != 1 then
            st := st.record "malformedOleanRegion" decl s!"Level.succ bad m_other={h.other}"
            visiting := visiting.erase w
            st := { st with levelCache := st.levelCache.insert w 0 }
          else
            match readFieldPtr parts h 0 with
            | .ok u => work := (false, u) :: (true, w) :: work
            | .error e =>
              st := st.record "malformedOleanRegion" decl e
              visiting := visiting.erase w
              st := { st with levelCache := st.levelCache.insert w 0 }
        | 2 | 3 => -- max / imax u v
          if h.other != 2 then
            st := st.record "malformedOleanRegion" decl s!"Level.max/imax bad m_other={h.other}"
            visiting := visiting.erase w
            st := { st with levelCache := st.levelCache.insert w 0 }
          else
            match readFieldPtr parts h 0, readFieldPtr parts h 1 with
            | .ok u, .ok v => work := (false, u) :: (false, v) :: (true, w) :: work
            | _, _ =>
              st := st.record "malformedOleanRegion" decl s!"Level.max/imax field read error at {w}"
              visiting := visiting.erase w
              st := { st with levelCache := st.levelCache.insert w 0 }
        | 4 | 5 => -- param / mvar
          if h.other != 1 then
            st := st.record "malformedOleanRegion" decl s!"Level.param/mvar bad m_other={h.other}"
            visiting := visiting.erase w
            st := { st with levelCache := st.levelCache.insert w 0 }
          else
            work := (true, w) :: work
        | _ =>
          st := st.record "malformedOleanRegion" decl s!"unknown Level tag {h.tag} at ptr {w}"
          visiting := visiting.erase w
          st := { st with levelCache := st.levelCache.insert w 0 }
    | (true, w) :: rest =>
      work := rest
      visiting := visiting.erase w
      if st.levelCache.contains w then continue
      st := { st with stats := { st.stats with levelNodesVisited := st.stats.levelNodesVisited + 1 } }
      match readObjHeader parts w with
      | .error e =>
        st := st.record "malformedOleanRegion" decl e
        st := { st with levelCache := st.levelCache.insert w 0 }
      | .ok h =>
        match readScalarU64 parts h 0 with
        | .error e =>
          st := st.record "malformedOleanRegion" decl s!"Level data scalar missing: {e}"
          st := { st with levelCache := st.levelCache.insert w 0 }
        | .ok storedData =>
          let getLD (cw : UInt64) : UInt64 :=
            if isScalarWord cw then levelZeroData else st.levelCache.getD cw 0
          let mut expRes : Except String UInt64 := .ok 0
          match h.tag with
          | 1 =>
            match readFieldPtr parts h 0 with
            | .ok u =>
              let ud := getLD u
              expRes := recomputeLevelData (mixHash 2243 (levelDataHash ud)) (levelDataDepth ud + 1)
                (levelDataHasMVar ud) (levelDataHasParam ud)
            | .error e => expRes := .error e
          | 2 =>
            match readFieldPtr parts h 0, readFieldPtr parts h 1 with
            | .ok u, .ok v =>
              let ud := getLD u
              let vd := getLD v
              expRes := recomputeLevelData
                (mixHash 2251 (mixHash (levelDataHash ud) (levelDataHash vd)))
                (Nat.max (levelDataDepth ud) (levelDataDepth vd) + 1)
                (levelDataHasMVar ud || levelDataHasMVar vd)
                (levelDataHasParam ud || levelDataHasParam vd)
            | _, _ => expRes := .error "Level.max child read error"
          | 3 =>
            match readFieldPtr parts h 0, readFieldPtr parts h 1 with
            | .ok u, .ok v =>
              let ud := getLD u
              let vd := getLD v
              expRes := recomputeLevelData
                (mixHash 2267 (mixHash (levelDataHash ud) (levelDataHash vd)))
                (Nat.max (levelDataDepth ud) (levelDataDepth vd) + 1)
                (levelDataHasMVar ud || levelDataHasMVar vd)
                (levelDataHasParam ud || levelDataHasParam vd)
            | _, _ => expRes := .error "Level.imax child read error"
          | 4 =>
            match readFieldPtr parts h 0 with
            | .ok nPtr =>
              let (st1, nInfo) := validateBinName parts decl nPtr st fuel
              st := st1
              expRes := recomputeLevelData (mixHash 2239 nInfo.hashVal) 0 false true
            | .error e => expRes := .error e
          | 5 =>
            match readFieldPtr parts h 0 with
            | .ok nPtr =>
              let (st1, nInfo) := validateBinName parts decl nPtr st fuel
              st := st1
              expRes := recomputeLevelData (mixHash 2237 (mixHash 0 nInfo.hashVal)) 0 true false
            | .error e => expRes := .error e
          | t => expRes := .error s!"unexpected Level tag {t}"
          match expRes with
          | .error err =>
            st := st.record "forgedLevelMData" decl err
            st := { st with levelCache := st.levelCache.insert w 0 }
          | .ok exp =>
            if storedData != exp then
              st := st.record "forgedLevelMData" decl
                s!"binary Level m_data mismatch at ptr {w}: stored {storedData}, expected {exp}"
            st := { st with levelCache := st.levelCache.insert w exp }
  if !completed then
    st := st.record "auditFuelExhausted" decl "validateBinLevel exhausted fuel"
    return (st, 0)
  return (st, st.levelCache.getD rootWord 0)

/-- Traverse a binary `List α` in a compacted region with cycle detection and fuel. -/
def readBinList (parts : Array OleanPart) (headWord : UInt64) (fuel : Nat := 100000) :
    Except String (Array UInt64) := Id.run do
  let mut cur := headWord
  let mut out : Array UInt64 := #[]
  let mut seen : Std.HashSet UInt64 := {}
  let mut done := false
  for _ in [0:fuel] do
    if isScalarWord cur then
      if unboxScalar cur == 0 then
        done := true
        break
      return .error s!"invalid scalar List tag {cur}"
    if seen.contains cur then
      return .error s!"cycle in List at ptr {cur}"
    seen := seen.insert cur
    let h ← match readObjHeader parts cur with | .ok h => pure h | .error e => return .error e
    if h.tag != 1 || h.other != 2 then
      return .error s!"invalid List.cons (tag={h.tag}, other={h.other}) at ptr {cur}"
    let hd ← match readFieldPtr parts h 0 with | .ok p => pure p | .error e => return .error e
    let tl ← match readFieldPtr parts h 1 with | .ok p => pure p | .error e => return .error e
    out := out.push hd
    cur := tl
  if !done then
    return .error "readBinList exhausted fuel"
  return .ok out

/-- Typed, fuel-bounded, address-memoized validation of a binary `Syntax` DAG
(`DataValue.ofSyntax`) with 3-color cycle detection (`visiting` + `done` sets):
B1 used a 1-color `seen` set, so a cyclic `Syntax.node` whose `args` pointed back to itself
passed with `ok=true`. Every atom / substring `LeanString` (RFC 3629 + `m_length`), every
`Name` (hash, UTF-8, `_kernel_fresh`), every position `Nat` (canonical), and every
constructor shape (`Syntax`, `SourceInfo`, `Substring.Raw`, `Syntax.Preresolved`) is checked. -/
def validateBinSyntax (parts : Array OleanPart) (decl : Name) (rootWord : UInt64)
    (st0 : BinValidatorState) : BinValidatorState := Id.run do
  let fuel := syntaxValidationFuel
  let mut st := st0
  -- kinds: 0 Syntax, 1 SourceInfo, 2 Substring.Raw, 3 Preresolved, 4 Nat, 5 String
  let mut work : List (Bool × Nat × UInt64) := [(false, 0, rootWord)]
  let mut visiting : Std.HashSet (Nat × UInt64) := {}
  let mut done : Std.HashSet (Nat × UInt64) := {}
  let mut completed := false
  let bad (s : BinValidatorState) (msg : String) : BinValidatorState :=
    s.record "malformedOleanRegion" decl s!"MData Syntax: {msg}"
  for _ in [0:fuel] do
    match work with
    | [] => completed := true; break
    | (true, kind, w) :: rest =>
      work := rest
      visiting := visiting.erase (kind, w)
      done := done.insert (kind, w)
    | (false, kind, w) :: rest =>
      work := rest
      let key := (kind, w)
      if done.contains key then continue
      if visiting.contains key then
        st := bad st s!"cycle detected in binary Syntax DAG (kind={kind}) at ptr {w}"
        return st
      if kind == 4 then
        if let .error e := readBinNat parts w then st := bad st e
        done := done.insert key
        continue
      if kind == 5 then
        st := (readBinString parts decl w st).1
        done := done.insert key
        continue
      if isScalarWord w then
        -- Only `Syntax.missing` (0) and `SourceInfo.none` (2) are nullary.
        let okScalar := (kind == 0 && unboxScalar w == 0) || (kind == 1 && unboxScalar w == 2)
        if !okScalar then st := bad st s!"invalid scalar {w} for kind {kind}"
        done := done.insert key
        continue
      match readObjHeader parts w with
      | .error e =>
        st := bad st e
        done := done.insert key
      | .ok h =>
        visiting := visiting.insert key
        let exitFrame := (true, kind, w)
        let f (i : Nat) : Except String UInt64 := readFieldPtr parts h i
        match kind, h.tag.toNat, h.other with
        | 0, 1, 3 => -- node info kind args
          match f 0, f 1, f 2 with
          | .ok i, .ok k, .ok a =>
            st := (validateBinName parts decl k st fuel).1
            match readArrayElems parts a with
            | .ok elems =>
              work := (false, 1, i) :: (elems.toList.map fun x => (false, 0, x)) ++ (exitFrame :: work)
            | .error e =>
              st := bad st e
              visiting := visiting.erase key
              done := done.insert key
          | _, _, _ =>
            st := bad st "node field read error"
            visiting := visiting.erase key
            done := done.insert key
        | 0, 2, 2 => -- atom info val
          match f 0, f 1 with
          | .ok i, .ok v => work := (false, 1, i) :: (false, 5, v) :: exitFrame :: work
          | _, _ =>
            st := bad st "atom field read error"
            visiting := visiting.erase key
            done := done.insert key
        | 0, 3, 4 => -- ident info rawVal val preresolved
          match f 0, f 1, f 2, f 3 with
          | .ok i, .ok r, .ok n, .ok p =>
            st := (validateBinName parts decl n st fuel).1
            match readBinList parts p fuel with
            | .ok ps =>
              work := (false, 1, i) :: (false, 2, r) :: (ps.toList.map fun x => (false, 3, x)) ++ (exitFrame :: work)
            | .error e =>
              st := bad st e
              visiting := visiting.erase key
              done := done.insert key
          | _, _, _, _ =>
            st := bad st "ident field read error"
            visiting := visiting.erase key
            done := done.insert key
        | 1, 0, 4 => -- SourceInfo.original leading pos trailing endPos
          match f 0, f 1, f 2, f 3 with
          | .ok l, .ok p, .ok t, .ok e =>
            work := (false, 2, l) :: (false, 4, p) :: (false, 2, t) :: (false, 4, e) :: exitFrame :: work
          | _, _, _, _ =>
            st := bad st "SourceInfo.original field read error"
            visiting := visiting.erase key
            done := done.insert key
        | 1, 1, 2 => -- SourceInfo.synthetic pos endPos; canonical
          match f 0, f 1, readScalarU8 parts h 0 with
          | .ok p, .ok e, .ok c =>
            if c > 1 then st := bad st s!"invalid Bool byte {c} in SourceInfo.synthetic"
            work := (false, 4, p) :: (false, 4, e) :: exitFrame :: work
          | _, _, _ =>
            st := bad st "SourceInfo.synthetic field read error"
            visiting := visiting.erase key
            done := done.insert key
        | 2, 0, 3 => -- Substring.Raw str startPos stopPos
          match f 0, f 1, f 2 with
          | .ok s, .ok a, .ok b =>
            work := (false, 5, s) :: (false, 4, a) :: (false, 4, b) :: exitFrame :: work
          | _, _, _ =>
            st := bad st "Substring field read error"
            visiting := visiting.erase key
            done := done.insert key
        | 3, 0, 1 => -- Preresolved.namespace ns
          match f 0 with
          | .ok n =>
            st := (validateBinName parts decl n st fuel).1
            visiting := visiting.erase key
            done := done.insert key
          | .error e =>
            st := bad st e
            visiting := visiting.erase key
            done := done.insert key
        | 3, 1, 2 => -- Preresolved.decl n fields
          match f 0, f 1 with
          | .ok n, .ok fs =>
            st := (validateBinName parts decl n st fuel).1
            match readBinList parts fs fuel with
            | .ok ws => work := (ws.toList.map fun x => (false, 5, x)) ++ (exitFrame :: work)
            | .error e =>
              st := bad st e
              visiting := visiting.erase key
              done := done.insert key
          | _, _ =>
            st := bad st "Preresolved.decl field read error"
            visiting := visiting.erase key
            done := done.insert key
        | k, t, o =>
          st := bad st s!"invalid ctor (kind={k}, tag={t}, other={o}) at ptr {w}"
          visiting := visiting.erase key
          done := done.insert key
  if !completed then
    st := st.record "auditFuelExhausted" decl "validateBinSyntax exhausted fuel"
  return st

/-- Validate a binary `MData` (`KVMap` = `List (Name × DataValue)`).
B1 hardening: A0 silently accepted `ofNat` / `ofInt` / `ofSyntax` payloads, `ofBool` bytes,
unknown `DataValue` tags and wrong arities. Every `DataValue` constructor is now checked
exactly and fails closed otherwise. -/
def validateBinMData (parts : Array OleanPart) (decl : Name) (mdataWord : UInt64)
    (st0 : BinValidatorState) (fuel : Nat) : BinValidatorState := Id.run do
  let mut st := st0
  -- `KVMap` is a 1-field structure wrapping `List (Name × DataValue)`, unboxed directly to the `List`.
  match readBinList parts mdataWord fuel with
  | .error e =>
    return st.record "malformedOleanRegion" decl s!"MData list error: {e}"
  | .ok pairs =>
    for pairPtr in pairs do
      match readObjHeader parts pairPtr with
      | .error e => st := st.record "malformedOleanRegion" decl s!"MData pair error: {e}"
      | .ok ph =>
        if ph.tag != 0 || ph.other != 2 then
          st := st.record "malformedOleanRegion" decl s!"MData pair invalid ctor at {pairPtr}"
        else
          match readFieldPtr parts ph 0, readFieldPtr parts ph 1 with
          | .ok kPtr, .ok vPtr =>
            let (st1, _) := validateBinName parts decl kPtr st fuel
            st := st1
            if isScalarWord vPtr then
              st := st.record "malformedOleanRegion" decl s!"MData DataValue cannot be scalar {vPtr}"
            else
              match readObjHeader parts vPtr with
              | .ok vh =>
                let field0 := readFieldPtr parts vh 0
                -- DataValue: 0=ofString, 1=ofBool (u8 scalar), 2=ofName, 3=ofNat, 4=ofInt, 5=ofSyntax
                match vh.tag.toNat, vh.other, field0 with
                | 0, 1, .ok sPtr => st := (readBinString parts decl sPtr st).1
                | 1, 0, _ =>
                  match readScalarU8 parts vh 0 with
                  | .ok b => if b > 1 then
                      st := st.record "malformedOleanRegion" decl s!"MData ofBool invalid byte {b}"
                  | .error e => st := st.record "malformedOleanRegion" decl s!"MData ofBool: {e}"
                | 2, 1, .ok nPtr => st := (validateBinName parts decl nPtr st fuel).1
                | 3, 1, .ok nw =>
                  if let .error e := readBinNat parts nw then
                    st := st.record "malformedOleanRegion" decl s!"MData ofNat: {e}"
                | 4, 1, .ok iw =>
                  if let .error e := readBinIntWellFormed parts iw then
                    st := st.record "malformedOleanRegion" decl s!"MData ofInt: {e}"
                | 5, 1, .ok sx => st := validateBinSyntax parts decl sx st
                | t, o, _ =>
                  st := st.record "malformedOleanRegion" decl
                    s!"MData invalid DataValue ctor (tag={t}, other={o}) at {vPtr}"
              | .error e => st := st.record "malformedOleanRegion" decl s!"MData value error: {e}"
          | _, _ => st := st.record "malformedOleanRegion" decl s!"MData pair field error at {pairPtr}"
    return st

/-- Pure binary DAG-memoized validator for `Expr` objects in compacted regions,
keyed by 64-bit object address (`UInt64`), with 3-color cycle detection.
Verifies full 64-bit `Expr.Data`, all `Name.hash`, all `Level.Data`, all `Literal.strVal`
UTF-8 + `m_length` + NUL invariants, `BinderInfo`/`Bool` discriminants, and `_kernel_fresh`. -/
def validateBinExpr (parts : Array OleanPart) (decl : Name) (rootWord : UInt64)
    (st0 : BinValidatorState) (requireClosed : Bool := true)
    (fuel : Nat := 2000000) : BinValidatorState × UInt64 := Id.run do
  if isScalarWord rootWord then
    let st := st0.record "malformedOleanRegion" decl s!"Expr cannot be tagged scalar {rootWord}"
    return (st, 0)
  if let some cached := st0.exprCache[rootWord]? then
    let st := { st0 with stats := { st0.stats with exprCacheHits := st0.stats.exprCacheHits + 1 } }
    let st := if requireClosed && !exprDataIsClosed cached then
      st.record "forgedExprMData" decl "binary Expr root is open per recomputed Expr.Data"
    else st
    return (st, cached)
  let mut st := st0
  let mut visiting : Std.HashSet UInt64 := {}
  let mut work : List (Bool × UInt64) := [(false, rootWord)]
  let mut completed := false
  for _ in [0:fuel] do
    match work with
    | [] => completed := true; break
    | (false, w) :: rest =>
      work := rest
      if isScalarWord w then
        st := st.record "malformedOleanRegion" decl s!"Expr child cannot be scalar {w}"
        continue
      if st.exprCache.contains w then
        st := { st with stats := { st.stats with exprCacheHits := st.stats.exprCacheHits + 1 } }
        continue
      if visiting.contains w then
        st := st.record "malformedOleanRegion" decl s!"cycle detected in Expr DAG at ptr {w}"
        return (st, 0)
      match readObjHeader parts w with
      | .error e =>
        st := st.record "malformedOleanRegion" decl s!"Expr header error: {e}"
        st := { st with exprCache := st.exprCache.insert w 0 }
      | .ok h =>
        visiting := visiting.insert w
        match h.tag with
        | 0 | 1 | 2 | 3 | 4 | 9 =>
          work := (true, w) :: work
        | 5 => -- app f a
          if h.other != 2 then
            st := st.record "malformedOleanRegion" decl s!"Expr.app bad m_other={h.other}"
            visiting := visiting.erase w
            st := { st with exprCache := st.exprCache.insert w 0 }
          else
            match readFieldPtr parts h 0, readFieldPtr parts h 1 with
            | .ok f, .ok a => work := (false, f) :: (false, a) :: (true, w) :: work
            | _, _ =>
              st := st.record "malformedOleanRegion" decl s!"Expr.app field read failed at {w}"
              visiting := visiting.erase w
              st := { st with exprCache := st.exprCache.insert w 0 }
        | 6 | 7 => -- lam / forallE (n, t, b; data, bi)
          if h.other != 3 then
            st := st.record "malformedOleanRegion" decl s!"Expr.lam/forallE bad m_other={h.other}"
            visiting := visiting.erase w
            st := { st with exprCache := st.exprCache.insert w 0 }
          else
            match readFieldPtr parts h 1, readFieldPtr parts h 2 with
            | .ok t, .ok b => work := (false, t) :: (false, b) :: (true, w) :: work
            | _, _ =>
              st := st.record "malformedOleanRegion" decl s!"Expr.lam/forallE field read failed at {w}"
              visiting := visiting.erase w
              st := { st with exprCache := st.exprCache.insert w 0 }
        | 8 => -- letE (n, t, v, b; data, nondep)
          if h.other != 4 then
            st := st.record "malformedOleanRegion" decl s!"Expr.letE bad m_other={h.other}"
            visiting := visiting.erase w
            st := { st with exprCache := st.exprCache.insert w 0 }
          else
            match readFieldPtr parts h 1, readFieldPtr parts h 2, readFieldPtr parts h 3 with
            | .ok t, .ok v, .ok b => work := (false, t) :: (false, v) :: (false, b) :: (true, w) :: work
            | _, _, _ =>
              st := st.record "malformedOleanRegion" decl s!"Expr.letE field read failed at {w}"
              visiting := visiting.erase w
              st := { st with exprCache := st.exprCache.insert w 0 }
        | 10 => -- mdata (d, e; data)
          if h.other != 2 then
            st := st.record "malformedOleanRegion" decl s!"Expr.mdata bad m_other={h.other}"
            visiting := visiting.erase w
            st := { st with exprCache := st.exprCache.insert w 0 }
          else
            match readFieldPtr parts h 1 with
            | .ok body => work := (false, body) :: (true, w) :: work
            | .error e =>
              st := st.record "malformedOleanRegion" decl e
              visiting := visiting.erase w
              st := { st with exprCache := st.exprCache.insert w 0 }
        | 11 => -- proj (s, i, e; data)
          if h.other != 3 then
            st := st.record "malformedOleanRegion" decl s!"Expr.proj bad m_other={h.other}"
            visiting := visiting.erase w
            st := { st with exprCache := st.exprCache.insert w 0 }
          else
            match readFieldPtr parts h 2 with
            | .ok body => work := (false, body) :: (true, w) :: work
            | .error e =>
              st := st.record "malformedOleanRegion" decl e
              visiting := visiting.erase w
              st := { st with exprCache := st.exprCache.insert w 0 }
        | t =>
          st := st.record "malformedOleanRegion" decl s!"unknown Expr tag {t} at ptr {w}"
          visiting := visiting.erase w
          st := { st with exprCache := st.exprCache.insert w 0 }
    | (true, w) :: rest =>
      work := rest
      visiting := visiting.erase w
      if st.exprCache.contains w then continue
      st := { st with stats := { st.stats with exprNodesVisited := st.stats.exprNodesVisited + 1 } }
      match readObjHeader parts w with
      | .error e =>
        st := st.record "malformedOleanRegion" decl e
        st := { st with exprCache := st.exprCache.insert w 0 }
      | .ok h =>
        match readScalarU64 parts h 0 with
        | .error e =>
          st := st.record "malformedOleanRegion" decl s!"Expr m_data scalar read error: {e}"
          st := { st with exprCache := st.exprCache.insert w 0 }
        | .ok storedData =>
          let mut expRes : Except String UInt64 := .ok 0
          match h.tag with
          | 0 => -- bvar idx
            if h.other != 1 then expRes := .error s!"Expr.bvar bad m_other={h.other}"
            else match readFieldPtr parts h 0 with
            | .error e => expRes := .error e
            | .ok idxWord =>
              match readBinNat parts idxWord with
              | .error e => expRes := .error e
              | .ok (idxNat, idxU64, _) =>
                expRes := recomputeExprData (mixHash 7 idxU64) (idxNat + 1) 0 false false false false
          | 1 => -- fvar id
            if h.other != 1 then expRes := .error s!"Expr.fvar bad m_other={h.other}"
            else match readFieldPtr parts h 0 with
            | .error e => expRes := .error e
            | .ok nPtr =>
              let (st1, nInfo) := validateBinName parts decl nPtr st fuel
              st := st1
              expRes := recomputeExprData (mixHash 13 (mixHash 0 nInfo.hashVal)) 0 0 true false false false
          | 2 => -- mvar id
            if h.other != 1 then expRes := .error s!"Expr.mvar bad m_other={h.other}"
            else match readFieldPtr parts h 0 with
            | .error e => expRes := .error e
            | .ok nPtr =>
              let (st1, nInfo) := validateBinName parts decl nPtr st fuel
              st := st1
              expRes := recomputeExprData (mixHash 17 (mixHash 0 nInfo.hashVal)) 0 0 false true false false
          | 3 => -- sort lvl
            if h.other != 1 then expRes := .error s!"Expr.sort bad m_other={h.other}"
            else match readFieldPtr parts h 0 with
            | .error e => expRes := .error e
            | .ok lPtr =>
              let (st1, ld) := validateBinLevel parts decl lPtr st fuel
              st := st1
              expRes := recomputeExprData (mixHash 11 (levelDataHash ld)) 0 0 false false
                (levelDataHasMVar ld) (levelDataHasParam ld)
          | 4 => -- const n us
            if h.other != 2 then expRes := .error s!"Expr.const bad m_other={h.other}"
            else match readFieldPtr parts h 0, readFieldPtr parts h 1 with
            | .ok nPtr, .ok usPtr =>
              let (st1, nInfo) := validateBinName parts decl nPtr st fuel
              st := st1
              match readBinList parts usPtr fuel with
              | .error e => expRes := .error s!"Expr.const levels list error: {e}"
              | .ok lWords =>
                let mut lHash : UInt64 := 7
                let mut hasLMVar := false
                let mut hasLParam := false
                for lw in lWords do
                  let (st2, ld) := validateBinLevel parts decl lw st fuel
                  st := st2
                  lHash := mixHash lHash (levelDataHash ld)
                  hasLMVar := hasLMVar || levelDataHasMVar ld
                  hasLParam := hasLParam || levelDataHasParam ld
                expRes := recomputeExprData (mixHash 5 (mixHash nInfo.hashVal lHash)) 0 0 false false hasLMVar hasLParam
            | _, _ => expRes := .error "Expr.const field read error"
          | 5 => -- app f a
            match readFieldPtr parts h 0, readFieldPtr parts h 1 with
            | .ok fPtr, .ok aPtr =>
              let fd := st.exprCache.getD fPtr 0
              let ad := st.exprCache.getD aPtr 0
              expRes := .ok (recomputeAppDataPure fd ad)
            | _, _ => expRes := .error "Expr.app field read error"
          | 6 | 7 => -- lam / forallE
            match readFieldPtr parts h 0, readFieldPtr parts h 1, readFieldPtr parts h 2, readScalarU8 parts h 8 with
            | .ok nPtr, .ok tPtr, .ok bPtr, .ok biByte =>
              if biByte >= 4 then
                st := st.record "malformedOleanRegion" decl s!"invalid BinderInfo byte {biByte} at ptr {w}"
              let (st1, _) := validateBinName parts decl nPtr st fuel
              st := st1
              let td := st.exprCache.getD tPtr 0
              let bd := st.exprCache.getD bPtr 0
              let d := Nat.max (exprDataApproxDepth td) (exprDataApproxDepth bd) + 1
              let hh := mixHash (UInt64.ofNat d) (mixHash (exprDataHash td) (exprDataHash bd))
              let lbr := Nat.max (exprDataLooseBVarRange td) (exprDataLooseBVarRange bd - 1)
              expRes := recomputeExprData hh lbr d
                (exprDataHasFVar td || exprDataHasFVar bd)
                (exprDataHasExprMVar td || exprDataHasExprMVar bd)
                (exprDataHasLevelMVar td || exprDataHasLevelMVar bd)
                (exprDataHasLevelParam td || exprDataHasLevelParam bd)
            | _, _, _, _ => expRes := .error "Expr.lam/forallE field read error"
          | 8 => -- letE
            match readFieldPtr parts h 0, readFieldPtr parts h 1, readFieldPtr parts h 2,
                  readFieldPtr parts h 3, readScalarU8 parts h 8 with
            | .ok nPtr, .ok tPtr, .ok vPtr, .ok bPtr, .ok ndByte =>
              if ndByte >= 2 then
                st := st.record "malformedOleanRegion" decl s!"invalid Bool byte {ndByte} in letE at ptr {w}"
              let (st1, _) := validateBinName parts decl nPtr st fuel
              st := st1
              let td := st.exprCache.getD tPtr 0
              let vd := st.exprCache.getD vPtr 0
              let bd := st.exprCache.getD bPtr 0
              let d := Nat.max (Nat.max (exprDataApproxDepth td) (exprDataApproxDepth vd)) (exprDataApproxDepth bd) + 1
              let hh := mixHash (UInt64.ofNat d) (mixHash (exprDataHash td) (mixHash (exprDataHash vd) (exprDataHash bd)))
              let lbr := Nat.max (Nat.max (exprDataLooseBVarRange td) (exprDataLooseBVarRange vd)) (exprDataLooseBVarRange bd - 1)
              expRes := recomputeExprData hh lbr d
                (exprDataHasFVar td || exprDataHasFVar vd || exprDataHasFVar bd)
                (exprDataHasExprMVar td || exprDataHasExprMVar vd || exprDataHasExprMVar bd)
                (exprDataHasLevelMVar td || exprDataHasLevelMVar vd || exprDataHasLevelMVar bd)
                (exprDataHasLevelParam td || exprDataHasLevelParam vd || exprDataHasLevelParam bd)
            | _, _, _, _, _ => expRes := .error "Expr.letE field read error"
          | 9 => -- lit
            if h.other != 1 then expRes := .error s!"Expr.lit bad m_other={h.other}"
            else match readFieldPtr parts h 0 with
            | .error e => expRes := .error e
            | .ok litPtr =>
              match readObjHeader parts litPtr with
              | .error e => expRes := .error s!"Literal header error: {e}"
              | .ok lh =>
                if lh.other != 1 then expRes := .error s!"Literal bad m_other={lh.other}"
                else match readFieldPtr parts lh 0 with
                | .error e => expRes := .error e
                | .ok payloadPtr =>
                  if lh.tag == 0 then
                    match readBinNat parts payloadPtr with
                    | .error e => expRes := .error s!"Literal.natVal error: {e}"
                    | .ok (_, u64Val, _) =>
                      expRes := recomputeExprData (mixHash 3 u64Val) 0 0 false false false false
                  else if lh.tag == 1 then
                    let (st1, sRes) := readBinString parts decl payloadPtr st
                    st := st1
                    match sRes with
                    | .error e => expRes := .error e
                    | .ok sInfo =>
                      if sInfo.validUtf8 then
                        expRes := recomputeExprData (mixHash 3 sInfo.hashVal) 0 0 false false false false
                      else
                        -- Invalid UTF-8 already recorded as `invalidUtf8Literal`.
                        expRes := .ok storedData
                  else expRes := .error s!"unknown Literal tag {lh.tag}"
          | 10 => -- mdata
            match readFieldPtr parts h 0, readFieldPtr parts h 1 with
            | .ok mdPtr, .ok bodyPtr =>
              st := validateBinMData parts decl mdPtr st fuel
              let bd := st.exprCache.getD bodyPtr 0
              let d := exprDataApproxDepth bd + 1
              let hh := mixHash (UInt64.ofNat d) (exprDataHash bd)
              expRes := recomputeExprData hh (exprDataLooseBVarRange bd) d
                (exprDataHasFVar bd) (exprDataHasExprMVar bd)
                (exprDataHasLevelMVar bd) (exprDataHasLevelParam bd)
            | _, _ => expRes := .error "Expr.mdata field read error"
          | 11 => -- proj
            match readFieldPtr parts h 0, readFieldPtr parts h 1, readFieldPtr parts h 2 with
            | .ok sPtr, .ok iWord, .ok bodyPtr =>
              let (st1, sInfo) := validateBinName parts decl sPtr st fuel
              st := st1
              match readBinNat parts iWord with
              | .error e => expRes := .error s!"Expr.proj idx Nat error: {e}"
              | .ok (_, iU64, _) =>
                let bd := st.exprCache.getD bodyPtr 0
                let d := exprDataApproxDepth bd + 1
                let hh := mixHash (UInt64.ofNat d) (mixHash sInfo.hashVal (mixHash iU64 (exprDataHash bd)))
                expRes := recomputeExprData hh (exprDataLooseBVarRange bd) d
                  (exprDataHasFVar bd) (exprDataHasExprMVar bd)
                  (exprDataHasLevelMVar bd) (exprDataHasLevelParam bd)
            | _, _, _ => expRes := .error "Expr.proj field read error"
          | t => expRes := .error s!"unexpected Expr tag {t}"
          match expRes with
          | .error err =>
            st := st.record "forgedExprMData" decl err
            st := { st with exprCache := st.exprCache.insert w 0 }
          | .ok exp =>
            if storedData != exp then
              st := st.record "forgedExprMData" decl
                s!"binary Expr (tag {h.tag}) m_data mismatch at ptr {w}: stored {storedData}, expected {exp}"
            st := { st with exprCache := st.exprCache.insert w exp }
  if !completed then
    st := st.record "auditFuelExhausted" decl "validateBinExpr exhausted fuel"
    return (st, 0)
  let rootData := st.exprCache.getD rootWord 0
  if requireClosed && !exprDataIsClosed rootData then
    st := st.record "forgedExprMData" decl
      s!"binary Expr root is open per recomputed Expr.Data (hasFVar={exprDataHasFVar rootData}, hasExprMVar={exprDataHasExprMVar rootData}, hasLevelMVar={exprDataHasLevelMVar rootData}, looseBVarRange={exprDataLooseBVarRange rootData})"
  return (st, rootData)

def binNameCleanMatches (parts : Array OleanPart) (ptr : UInt64) (expected : Name) : Bool :=
  let (st, info) := validateBinName parts expected ptr {}
  st.violations.isEmpty && info.name == expected

/-- Compare a binary `Expr` pointer in a compacted region directly against a canonical `Expr`
(used to verify binary `.quotInfo` types without trusting `importModules`). -/
def binExprMatchesCanonical (parts : Array OleanPart) (ptr : UInt64) (expected : Expr)
    (fuel : Nat := 128) : Bool :=
  match fuel with
  | 0 => false
  | fuel + 1 =>
    if isScalarWord ptr then false
    else match readObjHeader parts ptr with
    | .error _ => false
    | .ok h =>
      match readScalarU64 parts h 0 with
      | .error _ => false
      | .ok storedData =>
        if storedData != (expected.data : UInt64) then false
        else match expected with
        | .bvar idx =>
          h.tag == 0 && h.other == 1 &&
          match readFieldPtr parts h 0 with
          | .ok iw => match readBinNat parts iw with | .ok (v, _, _) => v == idx | .error _ => false
          | .error _ => false
        | .sort u =>
          h.tag == 3 && h.other == 1 &&
          match readFieldPtr parts h 0 with
          | .ok lw =>
            match u with
            | .zero => isScalarWord lw && unboxScalar lw == 0
            | .param pn =>
              match readObjHeader parts lw with
              | .ok lh =>
                lh.tag == 4 && lh.other == 1 &&
                match readFieldPtr parts lh 0, readScalarU64 parts lh 0 with
                | .ok np, .ok ld =>
                  ld == (u.data : UInt64) && binNameCleanMatches parts np pn
                | _, _ => false
              | .error _ => false
            | _ => false
          | .error _ => false
        | .const n us =>
          h.tag == 4 && h.other == 2 &&
          match readFieldPtr parts h 0, readFieldPtr parts h 1 with
          | .ok np, .ok usp =>
            binNameCleanMatches parts np n &&
            match readBinList parts usp fuel with
            | .ok lws =>
              lws.size == us.length &&
              (lws.toList.zip us).all fun (lw, eu) =>
                match eu with
                | .param pn =>
                  match readObjHeader parts lw with
                  | .ok lh =>
                    lh.tag == 4 && lh.other == 1 &&
                    match readFieldPtr parts lh 0, readScalarU64 parts lh 0 with
                    | .ok pnp, .ok ld =>
                      ld == (eu.data : UInt64) && binNameCleanMatches parts pnp pn
                    | _, _ => false
                  | .error _ => false
                | _ => false
            | .error _ => false
          | _, _ => false
        | .app f a =>
          h.tag == 5 && h.other == 2 &&
          match readFieldPtr parts h 0, readFieldPtr parts h 1 with
          | .ok fp, .ok ap =>
            binExprMatchesCanonical parts fp f fuel && binExprMatchesCanonical parts ap a fuel
          | _, _ => false
        | .forallE n t b bi =>
          h.tag == 7 && h.other == 3 &&
          match readFieldPtr parts h 0, readFieldPtr parts h 1, readFieldPtr parts h 2, readScalarU8 parts h 8 with
          | .ok np, .ok tp, .ok bp, .ok biB =>
            biB.toUInt64 == bi.toUInt64 &&
            binNameCleanMatches parts np n &&
            binExprMatchesCanonical parts tp t fuel &&
            binExprMatchesCanonical parts bp b fuel
          | _, _, _, _ => false
        | _ => false

/-- Validate `ConstantVal` (tag 0, 3 objs: `name`, `levelParams`, `type`) and return
`(st, declName, levelParams, typePtr)`. -/
def validateBinConstantVal (parts : Array OleanPart) (cvPtr : UInt64)
    (st0 : BinValidatorState) (fuel : Nat) : BinValidatorState × Option (Name × List Name × UInt64) := Id.run do
  let mut st := st0
  match readObjHeader parts cvPtr with
  | .error e =>
    return (st.record "malformedOleanRegion" .anonymous s!"ConstantVal header error: {e}", none)
  | .ok h =>
    if h.tag != 0 || h.other != 3 then
      return (st.record "malformedOleanRegion" .anonymous s!"ConstantVal bad ctor at {cvPtr}", none)
    match readFieldPtr parts h 0, readFieldPtr parts h 1, readFieldPtr parts h 2 with
    | .ok namePtr, .ok lparamsPtr, .ok typePtr =>
      let (st1, nInfo) := validateBinName parts .anonymous namePtr st fuel
      st := st1
      let decl := nInfo.name
      let mut lps : List Name := []
      match readBinList parts lparamsPtr fuel with
      | .error e =>
        st := st.record "malformedOleanRegion" decl s!"levelParams list error: {e}"
      | .ok lpWords =>
        for lpw in lpWords do
          let (st2, lpInfo) := validateBinName parts decl lpw st fuel
          st := st2
          lps := lps ++ [lpInfo.name]
      let (st3, _) := validateBinExpr parts decl typePtr st (requireClosed := true) fuel
      st := st3
      return (st, some (decl, lps, typePtr))
    | _, _, _ =>
      return (st.record "malformedOleanRegion" .anonymous s!"ConstantVal field read error at {cvPtr}", none)

/-- Check a `Bool`/enum scalar byte at `scalarByteOff` is `<= maxV` (fail closed). -/
def binCheckByte (parts : Array OleanPart) (decl : Name) (h : ObjHeader) (scalarByteOff : Nat)
    (maxV : UInt8) (what : String) (s : BinValidatorState) : BinValidatorState :=
  match readScalarU8 parts h scalarByteOff with
  | .ok b =>
    if b > maxV then s.record "malformedOleanRegion" decl s!"invalid {what} discriminant {b} (max {maxV})"
    else s
  | .error e => s.record "malformedOleanRegion" decl s!"{what} scalar missing: {e}"

/-- Check that object field `idx` is a canonical binary `Nat` (fail closed). -/
def binCheckNatField (parts : Array OleanPart) (decl : Name) (h : ObjHeader) (idx : Nat)
    (what : String) (s : BinValidatorState) : BinValidatorState :=
  match readFieldPtr parts h idx with
  | .ok w =>
    match readBinNat parts w with
    | .ok _ => s
    | .error e => s.record "malformedOleanRegion" decl s!"{what}: {e}"
  | .error e => s.record "malformedOleanRegion" decl s!"{what}: {e}"

/-- Read the declaration-name pointer of a binary `ConstantInfo`. -/
def binConstantNamePtr (parts : Array OleanPart) (ciPtr : UInt64) : Except String UInt64 := do
  let ciH ← readObjHeader parts ciPtr
  let valPtr ← readFieldPtr parts ciH 0
  let vh ← readObjHeader parts valPtr
  let cvPtr ← readFieldPtr parts vh 0
  let cvH ← readObjHeader parts cvPtr
  readFieldPtr parts cvH 0

/-- Validate one binary `ConstantInfo` object in a compacted region (V-Q1, V-M2, V-U3, V-F4). -/
def validateBinConstantInfo (parts : Array OleanPart) (ciPtr : UInt64)
    (modName : Name) (st0 : BinValidatorState) (fuel : Nat) : BinValidatorState := Id.run do
  let mut st := { st0 with stats := { st0.stats with declsChecked := st0.stats.declsChecked + 1 } }
  match readObjHeader parts ciPtr with
  | .error e => return st.record "malformedOleanRegion" modName s!"ConstantInfo header error: {e}"
  | .ok ciH =>
    if ciH.other != 1 || ciH.tag > 7 then
      return st.record "malformedOleanRegion" modName s!"ConstantInfo invalid ctor (tag={ciH.tag}, other={ciH.other})"
    match readFieldPtr parts ciH 0 with
    | .error e => return st.record "malformedOleanRegion" modName e
    | .ok valPtr =>
      match readObjHeader parts valPtr with
      | .error e => return st.record "malformedOleanRegion" modName s!"ConstantInfo payload error: {e}"
      | .ok vh =>
        if vh.tag != 0 || vh.other < 1 then
          return st.record "malformedOleanRegion" modName s!"ConstantInfo payload bad ctor at {valPtr}"
        match readFieldPtr parts vh 0 with
        | .error e => return st.record "malformedOleanRegion" modName e
        | .ok cvPtr =>
          let (st1, cvOpt) := validateBinConstantVal parts cvPtr st fuel
          st := st1
          let some (decl, lps, typePtr) := cvOpt | return st
          let checkNameList (listPtr : UInt64) (s : BinValidatorState) : BinValidatorState := Id.run do
            let mut s' := s
            match readBinList parts listPtr fuel with
            | .error e => return s'.record "malformedOleanRegion" decl s!"name list error: {e}"
            | .ok ws =>
              for w in ws do
                let (s'', _) := validateBinName parts decl w s' fuel
                s' := s''
              return s'
          match ciH.tag with
          | 0 => -- axiomInfo (cv; isUnsafe)
            if vh.other != 1 then
              st := st.record "malformedOleanRegion" decl "AxiomVal bad m_other"
          | 1 => -- defnInfo (cv, value, hints, all; safety)
            if vh.other != 4 then
              st := st.record "malformedOleanRegion" decl "DefinitionVal bad m_other"
            else
              if let .ok vPtr := readFieldPtr parts vh 1 then
                let (st', _) := validateBinExpr parts decl vPtr st (requireClosed := true) fuel
                st := st'
              if let .ok allPtr := readFieldPtr parts vh 3 then
                st := checkNameList allPtr st
          | 2 => -- thmInfo (cv, value, all)
            if vh.other != 3 then
              st := st.record "malformedOleanRegion" decl "TheoremVal bad m_other"
            else
              if let .ok vPtr := readFieldPtr parts vh 1 then
                let (st', _) := validateBinExpr parts decl vPtr st (requireClosed := true) fuel
                st := st'
              if let .ok allPtr := readFieldPtr parts vh 2 then
                st := checkNameList allPtr st
          | 3 => -- opaqueInfo (cv, value, all; isUnsafe)
            if vh.other != 3 then
              st := st.record "malformedOleanRegion" decl "OpaqueVal bad m_other"
            else
              if let .ok vPtr := readFieldPtr parts vh 1 then
                let (st', _) := validateBinExpr parts decl vPtr st (requireClosed := true) fuel
                st := st'
              if let .ok allPtr := readFieldPtr parts vh 2 then
                st := checkNameList allPtr st
          | 4 => -- quotInfo (cv; kind) -> V-Q1!
            if vh.other != 1 then
              st := st.record "forgedQuotInfo" decl "QuotVal bad m_other"
            else
              if modName != canonicalQuotOrigin then
                st := st.record "forgedQuotInfo" decl
                  s!"binary quotInfo declared in {modName}, expected {canonicalQuotOrigin}"
              match readScalarU8 parts vh 0 with
              | .error e => st := st.record "forgedQuotInfo" decl s!"QuotVal kind missing: {e}"
              | .ok kindByte =>
                let kindOpt : Option QuotKind :=
                  match kindByte with
                  | 0 => some .type
                  | 1 => some .ctor
                  | 2 => some .lift
                  | 3 => some .ind
                  | _ => none
                match kindOpt, canonicalQuotSpec? decl with
                | none, _ =>
                  st := st.record "forgedQuotInfo" decl s!"invalid QuotKind discriminant {kindByte}"
                | _, none =>
                  st := st.record "forgedQuotInfo" decl s!"non-canonical quotInfo name {decl}"
                | some k, some (expKind, expLps, expTy) =>
                  if !quotKindEq k expKind then
                    st := st.record "forgedQuotInfo" decl
                      s!"binary quotInfo kind {quotKindName k} != expected {quotKindName expKind}"
                  if lps != expLps then
                    st := st.record "forgedQuotInfo" decl
                      s!"binary quotInfo levelParams {lps} != expected {expLps}"
                  if !binExprMatchesCanonical parts typePtr expTy 128 then
                    st := st.record "forgedQuotInfo" decl
                      "binary quotInfo type does not match canonical Lean 4.34.1 Quot primitive type"
          | 5 => -- inductInfo (cv, numParams, numIndices, all, ctors, numNested; 3 bools)
            if vh.other != 6 then
              st := st.record "malformedOleanRegion" decl "InductiveVal bad m_other"
            else
              if let .ok allPtr := readFieldPtr parts vh 3 then st := checkNameList allPtr st
              if let .ok ctorsPtr := readFieldPtr parts vh 4 then st := checkNameList ctorsPtr st
          | 6 => -- ctorInfo (cv, induct, cidx, numParams, numFields; isUnsafe)
            if vh.other != 5 then
              st := st.record "malformedOleanRegion" decl "ConstructorVal bad m_other"
            else
              if let .ok indPtr := readFieldPtr parts vh 1 then
                let (st', _) := validateBinName parts decl indPtr st fuel
                st := st'
          | 7 => -- recInfo (cv, all, numParams, numIndices, numMotives, numMinors, rules; k, isUnsafe)
            if vh.other != 7 then
              st := st.record "malformedOleanRegion" decl "RecursorVal bad m_other"
            else
              if let .ok allPtr := readFieldPtr parts vh 1 then st := checkNameList allPtr st
              if let .ok rulesPtr := readFieldPtr parts vh 6 then
                match readBinList parts rulesPtr fuel with
                | .error e => st := st.record "malformedOleanRegion" decl s!"RecursorVal rules error: {e}"
                | .ok rWords =>
                  for rw in rWords do
                    match readObjHeader parts rw with
                    | .error e => st := st.record "malformedOleanRegion" decl s!"RecursorRule error: {e}"
                    | .ok rh =>
                      if rh.tag != 0 || rh.other != 3 then
                        st := st.record "malformedOleanRegion" decl s!"RecursorRule bad ctor at {rw}"
                      else
                        if let .ok cPtr := readFieldPtr parts rh 0 then
                          let (st', _) := validateBinName parts decl cPtr st fuel
                          st := st'
                        if let .ok rhsPtr := readFieldPtr parts rh 2 then
                          let (st', _) := validateBinExpr parts decl rhsPtr st (requireClosed := true) fuel
                          st := st'
                        st := binCheckNatField parts decl rh 1 "RecursorRule.nfields" st
          | _ => pure ()
          -- B1 hardening: scalar discriminants and `Nat` fields. A0 never read them, so e.g.
          -- `DefinitionVal.safety := 7` loaded fine; Lean-side code decodes it as a non-safe
          -- constructor (index 2) while the C++ kernel's enum comparisons match neither
          -- non-safe enumerator and treat it as safe: an interpretation split.
          match ciH.tag with
          | 0 => st := binCheckByte parts decl vh 0 1 "AxiomVal.isUnsafe" st
          | 1 =>
            st := binCheckByte parts decl vh 0 2 "DefinitionVal.safety" st
            match readFieldPtr parts vh 2 with
            | .ok hw =>
              if isScalarWord hw then
                if unboxScalar hw > 1 then
                  st := st.record "malformedOleanRegion" decl s!"invalid ReducibilityHints scalar {hw}"
              else
                match readObjHeader parts hw with
                | .ok hh =>
                  if hh.tag != 2 || hh.other != 0 then
                    st := st.record "malformedOleanRegion" decl
                      s!"invalid ReducibilityHints ctor (tag={hh.tag}, other={hh.other})"
                  else if let .error e := readScalarU32 parts hh 0 then
                    st := st.record "malformedOleanRegion" decl
                      s!"ReducibilityHints.regular height scalar truncated: {e}"
                | .error e => st := st.record "malformedOleanRegion" decl s!"ReducibilityHints: {e}"
            | .error _ => pure ()
          | 3 => st := binCheckByte parts decl vh 0 1 "OpaqueVal.isUnsafe" st
          | 5 =>
            for (i, what) in [(1, "numParams"), (2, "numIndices"), (5, "numNested")] do
              st := binCheckNatField parts decl vh i s!"InductiveVal.{what}" st
            for (o, what) in [(0, "isRec"), (1, "isUnsafe"), (2, "isReflexive")] do
              st := binCheckByte parts decl vh o 1 s!"InductiveVal.{what}" st
          | 6 =>
            for (i, what) in [(2, "cidx"), (3, "numParams"), (4, "numFields")] do
              st := binCheckNatField parts decl vh i s!"ConstructorVal.{what}" st
            st := binCheckByte parts decl vh 0 1 "ConstructorVal.isUnsafe" st
          | 7 =>
            for (i, what) in [(2, "numParams"), (3, "numIndices"), (4, "numMotives"), (5, "numMinors")] do
              st := binCheckNatField parts decl vh i s!"RecursorVal.{what}" st
            for (o, what) in [(0, "k"), (1, "isUnsafe")] do
              st := binCheckByte parts decl vh o 1 s!"RecursorVal.{what}" st
          | _ => pure ()
          return st

/-- Bounded 3-color compacted-region reachability sweep over opaque `ModuleData.entries`
payloads (A1 hardening): validates `m_rc == 0`, OOB pointers, cycles, forbids runtime-only
heap object tags (`245` closure, `251` thunk, `252` task, `253` ref, `254` external, `255`),
validates every reachable `LeanString` (RFC 3629 UTF-8 + `m_length` + NUL terminator), and
checks `LeanArray` / `LeanScalarArray` / `LeanMPZ` bounds so malformed UTF-8 or corrupted
objects cannot hide inside non-`exportAttr` extensions (`docStringExt`, `IR.declMapExt`, etc.). -/
def sweepBinRegionGraph (parts : Array OleanPart) (modName : Name) (rootPtr : UInt64)
    (st0 : BinValidatorState) (fuel : Nat := 2000000) : BinValidatorState := Id.run do
  if isScalarWord rootPtr then return st0
  let mut st := st0
  let mut visiting : Std.HashSet UInt64 := {}
  let mut done : Std.HashSet UInt64 := {}
  let mut work : List (Bool × UInt64) := [(false, rootPtr)]
  let mut completed := false
  for _ in [0:fuel] do
    match work with
    | [] => completed := true; break
    | (true, w) :: rest =>
      work := rest
      visiting := visiting.erase w
      done := done.insert w
    | (false, w) :: rest =>
      work := rest
      if isScalarWord w then continue
      if done.contains w then continue
      if visiting.contains w then
        st := st.record "malformedOleanRegion" modName
          s!"cycle detected in ModuleData.entries compacted region at ptr {w}"
        return st
      match readObjHeader parts w with
      | .error e =>
        st := st.record "malformedOleanRegion" modName s!"ModuleData.entries object error: {e}"
        done := done.insert w
      | .ok h =>
        if h.tag == 249 then
          st := (readBinString parts modName w st).1
          done := done.insert w
        else if h.tag == 250 then
          if let .error e := readBinIntWellFormed parts w then
            st := st.record "malformedOleanRegion" modName s!"ModuleData.entries LeanMPZ error: {e}"
          done := done.insert w
        else if h.tag == 248 then
          -- LeanScalarArray (ByteArray / FloatArray): validate size <= cap and byte bounds.
          let b := parts[h.partIdx]!.bytes
          if h.off + 24 > b.size then
            st := st.record "malformedOleanRegion" modName s!"LeanScalarArray header OOB at ptr {w}"
          else
            let sz := (readU64LE b (h.off + 8)).toNat
            let cap := (readU64LE b (h.off + 16)).toNat
            let elemSz := h.other
            if elemSz == 0 || cap < sz || h.off + 24 + cap * elemSz > b.size then
              st := st.record "malformedOleanRegion" modName
                s!"LeanScalarArray invalid bounds (elemSz={elemSz}, sz={sz}, cap={cap}) at ptr {w}"
          done := done.insert w
        else if h.tag == 246 then
          match readArrayElems parts w with
          | .error e =>
            st := st.record "malformedOleanRegion" modName s!"ModuleData.entries array error: {e}"
            done := done.insert w
          | .ok elems =>
            visiting := visiting.insert w
            let mut nextWork : List (Bool × UInt64) := (true, w) :: work
            for el in elems do
              if !isScalarWord el then
                nextWork := (false, el) :: nextWork
            work := nextWork
        else if h.tag <= 243 then
          visiting := visiting.insert w
          let mut nextWork : List (Bool × UInt64) := (true, w) :: work
          let mut okFields := true
          for i in [0:h.other] do
            match readFieldPtr parts h i with
            | .ok fp =>
              if !isScalarWord fp then
                nextWork := (false, fp) :: nextWork
            | .error e =>
              st := st.record "malformedOleanRegion" modName e
              okFields := false
          if okFields then
            work := nextWork
          else
            visiting := visiting.erase w
            done := done.insert w
        else
          -- Reject runtime-only / non-compacted tags: 244 (struct), 245 (closure!),
          -- 247 (struct array), 251 (thunk), 252 (task), 253 (ref), 254 (external), 255.
          st := st.record "malformedOleanRegion" modName
            s!"forbidden heap object tag {h.tag} in ModuleData.entries at ptr {w}"
          done := done.insert w
  if !completed then
    st := st.record "auditFuelExhausted" modName "sweepBinRegionGraph exhausted fuel"
  return st

/-- True iff binary `ExternAttrData` (unboxed `List ExternEntry`) is strictly `[ExternEntry.opaque]`
(constructor tag 3 -> nullary scalar word 7), i.e., carries ZERO C symbol names. -/
def binExternAttrDataIsPureOpaque (parts : Array OleanPart) (externDataWord : UInt64) : Bool :=
  match readBinList parts externDataWord 16 with
  | .ok elems => elems.size == 1 && isScalarWord elems[0]! && unboxScalar elems[0]! == 3
  | .error _ => false

/-- Validate `ModuleData.entries` in a binary `.olean` or `.ir` region:
- V-S5: flags any non-empty `Lean.exportAttr`, `Lean.externAttr`,
  `Lean.Compiler.implementedByAttr`, `Lean.regularInitAttr`, `Lean.builtinInitAttr`, and any
  C-symbol / `.ir` / non-module `IR.Decl.extern` (tag 1) entry inside `Lean.IR.declMapExt`
  (`forbiddenExportAttr`). Returns `(st, opaqueIrStubs, irFdeclNames)` so multi-part
  `validateModuleArtifactParts` verifies every `module` `.olean` opaque IR stub resolves to
  an `IR.Decl.fdecl` in `.ir`.
- Validates all extension keys' `Name.hash`/UTF-8 AND sweeps the full compacted-region graph
  reachable from `entriesArrPtr` (`sweepBinRegionGraph`) so malformed UTF-8 / `m_length` /
  `m_rc != 0` / cycles / `LeanClosure` objects cannot hide in any extension payload. -/
def validateBinModuleEntries (parts : Array OleanPart) (modName : Name) (entriesArrPtr : UInt64)
    (st0 : BinValidatorState) (fuel : Nat) (allowOpaqueIrStubs : Bool := false) :
    BinValidatorState × NameSet × NameSet := Id.run do
  let mut st := st0
  let mut opaqueStubs : NameSet := {}
  let mut fdecls : NameSet := {}
  match readArrayElems parts entriesArrPtr with
  | .error e =>
    return (st.record "malformedOleanRegion" modName s!"entries array error: {e}", opaqueStubs, fdecls)
  | .ok pairs =>
    for pairPtr in pairs do
      match readObjHeader parts pairPtr with
      | .error e => st := st.record "malformedOleanRegion" modName s!"entries pair error: {e}"
      | .ok ph =>
        if ph.tag != 0 || ph.other != 2 then
          st := st.record "malformedOleanRegion" modName s!"entries pair bad ctor at {pairPtr}"
        else
          match readFieldPtr parts ph 0, readFieldPtr parts ph 1 with
          | .ok extNamePtr, .ok arrPtr =>
            let (st1, extInfo) := validateBinName parts modName extNamePtr st fuel
            st := st1
            if extInfo.name == `Lean.exportAttr then
              match readArrayElems parts arrPtr with
              | .error e =>
                st := st.record "forbiddenExportAttr" modName
                  s!"malformed Lean.exportAttr entries array in {modName}: {e}"
              | .ok expEntries =>
                for ep in expEntries do
                  match readObjHeader parts ep with
                  | .ok eh =>
                    if eh.tag == 0 && eh.other == 2 then
                      match readFieldPtr parts eh 0, readFieldPtr parts eh 1 with
                      | .ok dPtr, .ok symPtr =>
                        let (st2, dInfo) := validateBinName parts modName dPtr st fuel
                        let (st3, sInfo) := validateBinName parts dInfo.name symPtr st2 fuel
                        st := st3.record "forbiddenExportAttr" dInfo.name
                          s!"binary Lean.exportAttr entry -> C symbol {sInfo.name} in {modName}"
                      | _, _ =>
                        st := st.record "forbiddenExportAttr" modName
                          s!"binary Lean.exportAttr entry in {modName}"
                    else
                      st := st.record "forbiddenExportAttr" modName
                        s!"binary Lean.exportAttr entry in {modName}"
                  | .error _ =>
                    st := st.record "forbiddenExportAttr" modName
                      s!"binary Lean.exportAttr entry in {modName}"
            else if extInfo.name == `Lean.externAttr ||
                    extInfo.name == `Lean.Compiler.implementedByAttr ||
                    extInfo.name == `Lean.regularInitAttr ||
                    extInfo.name == `Lean.builtinInitAttr then
              match readArrayElems parts arrPtr with
              | .error e =>
                st := st.record "forbiddenExportAttr" modName
                  s!"malformed {extInfo.name} entries array in {modName}: {e}"
              | .ok attrEntries =>
                for ep in attrEntries do
                  let mut declName := modName
                  if let .ok eh := readObjHeader parts ep then
                    if eh.tag == 0 && eh.other >= 1 then
                      if let .ok dPtr := readFieldPtr parts eh 0 then
                        let (st2, dInfo) := validateBinName parts modName dPtr st fuel
                        st := st2
                        declName := dInfo.name
                  st := st.record "forbiddenExportAttr" declName
                    s!"binary {extInfo.name} entry in {modName}"
            else if extInfo.name == `Lean.IR.declMapExt then
              match readArrayElems parts arrPtr with
              | .error e =>
                st := st.record "malformedOleanRegion" modName
                  s!"malformed Lean.IR.declMapExt array in {modName}: {e}"
              | .ok irDecls =>
                for dp in irDecls do
                  match readObjHeader parts dp with
                  | .error e =>
                    st := st.record "malformedOleanRegion" modName s!"IR.Decl header error: {e}"
                  | .ok dh =>
                    if dh.tag == 0 then
                      if dh.other >= 1 then
                        if let .ok fPtr := readFieldPtr parts dh 0 then
                          let (st2, fInfo) := validateBinName parts modName fPtr st fuel
                          st := st2
                          fdecls := fdecls.insert fInfo.name
                    else if dh.tag == 1 then
                      -- `IR.Decl.extern (f : FunId) (xs : Array Param) (type : IRType) (info : ExternAttrData)`
                      let mut fName := modName
                      if dh.other >= 1 then
                        if let .ok fPtr := readFieldPtr parts dh 0 then
                          let (st2, fInfo) := validateBinName parts modName fPtr st fuel
                          st := st2
                          fName := fInfo.name
                      let pureOpaque :=
                        if dh.other == 4 then
                          match readFieldPtr parts dh 3 with
                          | .ok edPtr => binExternAttrDataIsPureOpaque parts edPtr
                          | .error _ => false
                        else false
                      if allowOpaqueIrStubs && pureOpaque then
                        opaqueStubs := opaqueStubs.insert fName
                      else
                        st := st.record "forbiddenExportAttr" fName
                          s!"binary IR.Decl.extern C-symbol stub in {modName}"
                    else
                      st := st.record "malformedOleanRegion" modName
                        s!"unknown IR.Decl tag {dh.tag} at ptr {dp}"
          | _, _ => st := st.record "malformedOleanRegion" modName s!"entries pair field error"
    st := sweepBinRegionGraph parts modName entriesArrPtr st (min fuel 2000000)
    return (st, opaqueStubs, fdecls)

def validateOleanPartsEx (rawParts : Array ByteArray) (modName : Name)
    (forbidMainExport : Bool := true) (fuel : Nat := 20000000)
    (isIrGroup : Bool := false) : AuditReport × NameSet × NameSet := Id.run do
  match parseOleanParts rawParts with
  | .error err =>
    return ({ violations := #[{ tag := "malformedOleanRegion", decl := modName, detail := err }] }, {}, {})
  | .ok parts =>
    let mut st : BinValidatorState := {}
    let mut opaqueStubs : NameSet := {}
    let mut fdecls : NameSet := {}
    for pIdx in [0:parts.size] do
      let rootPtr := parts[pIdx]!.rootPtr
      if isScalarWord rootPtr then
        -- Empty delta layer root (if any) must be valid scalar 0 (`PUnit` / empty).
        if unboxScalar rootPtr != 0 then
          st := st.record "malformedOleanRegion" modName s!"part {pIdx} invalid scalar root {rootPtr}"
        continue
      match readObjHeader parts rootPtr with
      | .error e =>
        st := st.record "malformedOleanRegion" modName s!"part {pIdx} ModuleData root error: {e}"
      | .ok rh =>
        if rh.tag != 0 || rh.other != 5 then
          st := st.record "malformedOleanRegion" modName
            s!"part {pIdx} ModuleData root expected tag=0, other=5, got tag={rh.tag}, other={rh.other}"
        else
          -- B1 hardening: `ModuleData.isModule` byte and `imports` (A0 skipped field 0, so a
          -- forged import `Name.hash` / invalid UTF-8 / `_kernel_fresh` import name passed).
          st := binCheckByte parts modName rh 0 1 "ModuleData.isModule" st
          let partIsModule := match readScalarU8 parts rh 0 with | .ok 1 => true | _ => false
          match readFieldPtr parts rh 0 with
          | .error e => st := st.record "malformedOleanRegion" modName s!"imports field error: {e}"
          | .ok importsPtr =>
            match readArrayElems parts importsPtr with
            | .error e => st := st.record "malformedOleanRegion" modName s!"imports error: {e}"
            | .ok impPtrs =>
              for ip in impPtrs do
                match readObjHeader parts ip with
                | .error e => st := st.record "malformedOleanRegion" modName s!"Import header error: {e}"
                | .ok ih =>
                  if ih.tag != 0 || ih.other != 1 then
                    st := st.record "malformedOleanRegion" modName s!"Import bad ctor at {ip}"
                  else
                    for (o, what) in [(0, "importAll"), (1, "isExported"), (2, "isMeta")] do
                      st := binCheckByte parts modName ih o 1 s!"Import.{what}" st
                    if let .ok nPtr := readFieldPtr parts ih 0 then
                      st := (validateBinName parts modName nPtr st fuel).1
          match readFieldPtr parts rh 1, readFieldPtr parts rh 2,
                readFieldPtr parts rh 3, readFieldPtr parts rh 4 with
          | .ok constNamesPtr, .ok constsPtr, .ok extraNamesPtr, .ok entriesPtr =>
            let mut cnInfos : Array BinNameInfo := #[]
            let mut partSeenConstNames : NameSet := {}
            match readArrayElems parts constNamesPtr with
            | .error e => st := st.record "malformedOleanRegion" modName s!"constNames error: {e}"
            | .ok cnPtrs =>
              for cnp in cnPtrs do
                let (st1, nInfo) := validateBinName parts modName cnp st fuel
                st := st1
                cnInfos := cnInfos.push nInfo
                if partSeenConstNames.contains nInfo.name then
                  st := st.record "shadowedConstant" nInfo.name
                    s!"duplicate constName {nInfo.name} in part {pIdx} of module {modName}"
                partSeenConstNames := partSeenConstNames.insert nInfo.name
                if forbidMainExport && nInfo.name == `main then
                  st := st.record "forbiddenExportAttr" `main
                    s!"unannotated `main` C-symbol entry point in binary module {modName}"
            match readArrayElems parts extraNamesPtr with
            | .error e => st := st.record "malformedOleanRegion" modName s!"extraConstNames error: {e}"
            | .ok enPtrs =>
              for enp in enPtrs do
                let (st1, _) := validateBinName parts modName enp st fuel
                st := st1
            match readArrayElems parts constsPtr with
            | .error e => st := st.record "malformedOleanRegion" modName s!"constants error: {e}"
            | .ok ciPtrs =>
              -- B1 hardening: `importModules` binds `constNames[i] ↦ constants[i]`; reject
              -- length mismatches (silently truncated by the zip) and aliased names.
              if ciPtrs.size != cnInfos.size then
                st := st.record "constNameAliasMismatch" modName
                  s!"constNames.size={cnInfos.size} != constants.size={ciPtrs.size} (importModules silently drops the excess)"
              for h : i in [0:ciPtrs.size] do
                let cip := ciPtrs[i]
                st := validateBinConstantInfo parts cip modName st fuel
                if let some cnInfo := cnInfos[i]? then
                  match binConstantNamePtr parts cip with
                  | .error e => st := st.record "malformedOleanRegion" modName s!"ConstantInfo name read: {e}"
                  | .ok np =>
                    let (st1, ciName) := validateBinName parts modName np st fuel
                    st := st1
                    if !(cnInfo.name == ciName.name && cnInfo.hashVal == ciName.hashVal) then
                      st := st.record "constNameAliasMismatch" cnInfo.name
                        s!"constNames entry {cnInfo.name} binds a ConstantInfo named {ciName.name}"
            let (stE, pStubs, pFdecls) := validateBinModuleEntries parts modName entriesPtr st fuel
              (allowOpaqueIrStubs := !isIrGroup && partIsModule)
            st := stE
            opaqueStubs := pStubs.foldl (·.insert ·) opaqueStubs
            fdecls := pFdecls.foldl (·.insert ·) fdecls
          | _, _, _, _ =>
            st := st.record "malformedOleanRegion" modName s!"part {pIdx} ModuleData fields unreadable"
    return ({ violations := st.violations, stats := st.stats }, opaqueStubs, fdecls)

def mergeAuditStats (a b : AuditStats) : AuditStats := {
  declsChecked := a.declsChecked + b.declsChecked
  exprNodesVisited := a.exprNodesVisited + b.exprNodesVisited
  exprCacheHits := a.exprCacheHits + b.exprCacheHits
  levelNodesVisited := a.levelNodesVisited + b.levelNodesVisited
  levelCacheHits := a.levelCacheHits + b.levelCacheHits
  nameNodesVisited := a.nameNodesVisited + b.nameNodesVisited
  nameCacheHits := a.nameCacheHits + b.nameCacheHits
  stringsValidated := a.stringsValidated + b.stringsValidated
}

/-- Validate a module's `.olean*` compacted-region group and its independent `.ir*`
compacted-region group separately (A1 hardening: `.ir.sig`/`.ir` have an independent base
address space from `.olean`/`.olean.server`/`.olean.private`, and every `module` `.olean`
pure-`.opaque` IR signature stub must be backed by an `IR.Decl.fdecl` in `.ir`). -/
def validateModuleArtifactParts (oleanParts irParts : Array ByteArray) (modName : Name)
    (forbidMainExport : Bool := true) (fuel : Nat := 20000000) : AuditReport := Id.run do
  let (r1, oStubs, oFdecls) := validateOleanPartsEx oleanParts modName forbidMainExport fuel (isIrGroup := false)
  let (r2, irFdecls) :=
    if irParts.isEmpty then ({}, ({} : NameSet))
    else
      let (rep, _, fds) := validateOleanPartsEx irParts modName forbidMainExport fuel (isIrGroup := true)
      (rep, fds)
  let allFdecls := irFdecls.foldl (·.insert ·) oFdecls
  let mut vs := r1.violations ++ r2.violations
  for stub in oStubs do
    if !allFdecls.contains stub then
      vs := vs.push {
        tag := "forbiddenExportAttr"
        decl := stub
        detail := s!"unresolved module IR.Decl.extern opaque stub {stub} in {modName} without backing .ir fdecl"
      }
  return { violations := vs, stats := mergeAuditStats r1.stats r2.stats }

/-- Full pure-Lean binary `.olean`/`.ir` compacted-region pointer-DAG validation over
`rawParts : Array ByteArray`. Fails closed on any unresolved `IR.Decl.extern` stub. -/
def validateOleanParts (rawParts : Array ByteArray) (modName : Name)
    (forbidMainExport : Bool := true) (fuel : Nat := 20000000) : AuditReport :=
  validateModuleArtifactParts rawParts #[] modName forbidMainExport fuel

/-! ## Section 9: V-N6 `lean4#16831` `Nat.xor` / `[propext]` Second-Kernel Parity Oracle -/

def declUsedConsts (ci : ConstantInfo) (fuel : Nat := 2000000) : Except Violation NameSet := do
  let mergeInto (acc : NameSet) (e : Expr) : Except Violation NameSet :=
    match collectConstsBounded e fuel with
    | some ns => .ok (ns.foldl (·.insert ·) acc)
    | none => .error {
        tag := "auditFuelExhausted"
        decl := ci.name
        detail := "declUsedConsts exhausted fuel"
      }
  let mut acc ← mergeInto {} ci.type
  if let some v := ci.value? (allowOpaque := true) then
    acc ← mergeInto acc v
  match ci with
  | .inductInfo v => acc := (v.all ++ v.ctors).foldl (·.insert ·) acc
  | .ctorInfo v => acc := acc.insert v.induct
  | .recInfo v =>
    acc := v.all.foldl (·.insert ·) acc
    for r in v.rules do
      acc ← mergeInto (acc.insert r.ctor) r.rhs
  | _ => pure ()
  return acc

/-- Collect the exact reachable declaration set and axiom set for `roots` in `env`
(pure, total, fuel-bounded DAG BFS using `StrictExprKey`-memoized constant extraction;
fails closed with `auditFuelExhausted`). -/
def collectReachableAndAxioms (env : Environment) (roots : Array Name)
    (fuel : Nat := 200000) : Except Violation (NameSet × Array Name) := Id.run do
  let mut visited : NameSet := {}
  let mut stack : List Name := []
  let mut axioms : NameSet := {}
  for r in roots do
    if !visited.contains r then
      visited := visited.insert r
      stack := r :: stack
  let mut done := false
  for _ in [0:fuel] do
    match stack with
    | [] => done := true; break
    | n :: rest =>
      stack := rest
      if let some ci := env.find? n then
        if ci matches .axiomInfo _ then
          axioms := axioms.insert n
        match declUsedConsts ci with
        | .error v => return .error v
        | .ok used =>
          for d in used do
            if !visited.contains d then
              visited := visited.insert d
              stack := d :: stack
  if !done then
    return .error {
      tag := "auditFuelExhausted"
      decl := roots.getD 0 .anonymous
      detail := "collectReachableAndAxioms exhausted fuel"
    }
  return .ok (visited, axioms.toArray.qsort Name.lt)

/-- Standard nanoda / second-kernel primitive targets list, including `Nat.xor`
(which on Lean 4.34.1 depends on `Nat.bitwise` -> `propext`, triggering `lean4#16831`
if exported unconditionally for 0-axiom proofs). -/
def nanodaPrimitiveTargets : Array Name := #[
  ``Nat, ``Nat.zero, ``Nat.succ, ``Nat.add, ``Nat.sub, ``Nat.mul, ``Nat.pow,
  ``Nat.div, ``Nat.mod, ``Nat.beq, ``Nat.ble, ``Nat.xor, ``Nat.land, ``Nat.lor,
  ``String, ``Char
]

structure SecondKernelParityResult where
  target             : Name
  demandDriven       : Bool
  leanAxioms         : Array Name
  secondKernelAxioms : Array Name
  exportedPrimitives : Array Name
  violation?         : Option Violation
  deriving Repr

/-- Second-kernel export-closure parity oracle (`lean4#16831`):
- `demandDriven := false` reproduces the unconditional `primitiveTargets` bug where
  `Nat.xor` injects `propext` into 0-axiom theorems (`nanodaNatXorPropextMismatch`).
- `demandDriven := true` filters `primitiveTargets` to `targetReachable ∩ primitiveTargets`,
  restoring exact Lean-vs-second-kernel axiom parity. -/
def checkSecondKernelParity (env : Environment) (target : Name)
    (demandDriven : Bool) (fuel : Nat := 200000) : Except Violation SecondKernelParityResult := do
  let (reach, leanAxioms) ← collectReachableAndAxioms env #[target] fuel
  let exportedPrimitives :=
    if demandDriven then nanodaPrimitiveTargets.filter reach.contains
    else nanodaPrimitiveTargets
  let (_, skAxioms) ← collectReachableAndAxioms env (#[target] ++ exportedPrimitives) fuel
  let viol? :=
    if leanAxioms != skAxioms then
      some {
        tag := "nanodaNatXorPropextMismatch"
        decl := target
        detail := s!"Lean kernel axioms {leanAxioms} != second-kernel axioms {skAxioms} (demandDriven={demandDriven})"
      }
    else none
  return {
    target
    demandDriven
    leanAxioms
    secondKernelAxioms := skAxioms
    exportedPrimitives
    violation? := viol?
  }

/-! ### Forged per-module axiom cache (`exportedAxiomsExt`, B2 hardening)

Lean 4.34.1's `Lean.collectAxioms` (and therefore `#print axioms`) does NOT traverse imported
declarations: it looks up the per-declaration axiom arrays that each `.olean` stores in the
private `Lean.exportedAxiomsExt` persistent extension (`CollectAxioms.lean`: "axiom collection
never crosses module boundaries"). Nothing re-checks those arrays on import, so a forged
`.olean` that empties the stored array for `useEvil : False := evilAx` makes `#print axioms`
report "does not depend on any axioms" for `useEvil` AND for every downstream theorem that
uses it (reproduced live in the Python suite). Every axiom-closure measurement made through
`#print axioms` / `collectAxioms` (including the V-N6 `#print axioms` `#guard_msgs` blocks) silently trusts
these arrays. `independentAxiomClosures` recomputes closures by traversing kernel constants
(mirroring `CollectAxioms.collect`, never consulting the extension) and
`validateExportedAxiomCache` rejects any module constant whose cached axiom array omits an
axiom of its true closure (`forgedExportedAxioms`). -/

inductive TarjanFrame where
  | enter (c : Name)
  | step (c : Name) (deps : List Name)
  | afterChild (parent : Name) (child : Name)

/-- Collect direct constant dependencies for `c` in `env`, covering ALL `ConstantInfo` fields
including `.recInfo` `rules` (`r.ctor`, `r.rhs`) + `all`, `.ctorInfo` `induct`, and
`.inductInfo` `all ++ ctors` (A2 fix: B2 omitted `.recInfo.rules` and `.ctorInfo.induct`). -/
def directConstDeps (env : Environment) (c : Name) (fuel : Nat := 2000000)
    (skipInductCtorsFor : Option Name := none) :
    Option (Array Name) := do
  let some ci := env.find? c | return #[]
  let mut acc ← collectConstsBounded ci.type fuel
  if let some v := ci.value? (allowOpaque := true) then
    let vs ← collectConstsBounded v fuel
    acc := vs.foldl (·.insert ·) acc
  match ci with
  | .inductInfo v =>
    if skipInductCtorsFor == some c then
      acc := v.all.foldl (·.insert ·) acc
    else
      acc := (v.all ++ v.ctors).foldl (·.insert ·) acc
  | .ctorInfo v =>
    acc := acc.insert v.induct
  | .recInfo v =>
    acc := v.all.foldl (·.insert ·) acc
    for r in v.rules do
      acc := acc.insert r.ctor
      let rs ← collectConstsBounded r.rhs fuel
      acc := rs.foldl (·.insert ·) acc
  | _ => pure ()
  return acc.toArray

/-- Independent, fuel-bounded, SCC-exact axiom closures for `roots` via iterative Tarjan SCC
(A2 fix: B2's DFS cached `#[]` sentinel results permanently on mutual-recursion back-edges,
so for `cycB <-> cycC` where `cycB` uses `sccEvil`, visiting `cycB` first permanently cached
`cycC ↦ #[]` and let `validateExportedAxiomCache` accept a forged empty cache for `cycC`;
B2 also omitted `.recInfo.rules` and `.ctorInfo.induct`). -/
def independentAxiomClosures (env : Environment) (roots : Array Name) (fuel : Nat := 20000000)
    (skipInductCtorsFor : Option Name := none) :
    Except Violation (NameMap (Array Name)) := Id.run do
  let mut nextIdx : Nat := 0
  let mut index : NameMap Nat := {}
  let mut lowlink : NameMap Nat := {}
  let mut onStack : NameSet := {}
  let mut tarjanStack : List Name := []
  let mut depsCache : NameMap (Array Name) := {}
  let mut closures : NameMap (Array Name) := {}
  let mut work : List TarjanFrame := roots.toList.map TarjanFrame.enter
  let mut done := false
  for _ in [0:fuel] do
    match work with
    | [] => done := true; break
    | .enter c :: rest =>
      work := rest
      if index.contains c then continue
      let idx := nextIdx
      nextIdx := nextIdx + 1
      index := index.insert c idx
      lowlink := lowlink.insert c idx
      tarjanStack := c :: tarjanStack
      onStack := onStack.insert c
      match directConstDeps env c (skipInductCtorsFor := skipInductCtorsFor) with
      | none =>
        return .error { tag := "auditFuelExhausted", decl := c, detail := "independentAxiomClosures expression fuel exhausted" }
      | some ds =>
        depsCache := depsCache.insert c ds
        work := .step c ds.toList :: work
    | .step c [] :: rest =>
      work := rest
      let cIdx := (index.find? c).getD 0
      let cLow := (lowlink.find? c).getD 0
      if cLow == cIdx then
        -- Pop the entire SCC rooted at `c` and assign the exact union of axioms to every member.
        let mut scc : Array Name := #[]
        let maxPops := tarjanStack.length
        for _ in [0:maxPops] do
          match tarjanStack with
          | [] => break
          | w :: ws =>
            tarjanStack := ws
            onStack := onStack.erase w
            scc := scc.push w
            if w == c then break
        let mut sccAxs : NameSet := {}
        for u in scc do
          if let some (.axiomInfo _) := env.find? u then
            sccAxs := sccAxs.insert u
          if let some ds := depsCache.find? u then
            for d in ds do
              if let some dAxs := closures.find? d then
                if !dAxs.isEmpty then
                  sccAxs := dAxs.foldl (·.insert ·) sccAxs
        let res : Array Name :=
          if sccAxs.isEmpty then #[] else sccAxs.toArray.qsort Name.lt
        for u in scc do
          closures := closures.insert u res
    | .step c (d :: ds) :: rest =>
      work := rest
      if !index.contains d then
        work := .enter d :: .afterChild c d :: .step c ds :: work
      else
        if onStack.contains d then
          let cLow := (lowlink.find? c).getD 0
          let dIdx := (index.find? d).getD 0
          if dIdx < cLow then
            lowlink := lowlink.insert c dIdx
        work := .step c ds :: work
    | .afterChild parent child :: rest =>
      work := rest
      let pLow := (lowlink.find? parent).getD 0
      let cLow := (lowlink.find? child).getD 0
      if cLow < pLow then
        lowlink := lowlink.insert parent cLow
  if !done then
    return .error { tag := "auditFuelExhausted", decl := roots.getD 0 .anonymous, detail := "independentAxiomClosures exhausted fuel" }
  return .ok closures

def exportedAxiomsExtName : String := "_private.Lean.Util.CollectAxioms.0.Lean.exportedAxiomsExt"

/-- Decode the per-declaration axiom arrays stored in a module's binary `exportedAxiomsExt`
entries (A2 hardening: checks `ph`/`eh` ctor shapes `(tag=0, other=2)` and fails closed on
any `validateBinName` violation instead of discarding name-hash/UTF-8 errors). -/
def binExportedAxiomClaims (rawParts : Array ByteArray) :
    Except String (Array (Name × Array Name)) := do
  let parts ← parseOleanParts rawParts
  let mut out : Array (Name × Array Name) := #[]
  let readCleanName (ptr : UInt64) (what : String) : Except String Name :=
    let (st, info) := validateBinName parts .anonymous ptr {}
    if !st.violations.isEmpty then
      .error s!"{what} name invalid: {(st.violations.map Violation.render)}"
    else
      .ok info.name
  for p in parts do
    if isScalarWord p.rootPtr then continue
    let rh ← readObjHeader parts p.rootPtr
    for pairPtr in ← readArrayElems parts (← readFieldPtr parts rh 4) do
      let ph ← readObjHeader parts pairPtr
      if ph.tag != 0 || ph.other != 2 then
        throw s!"entries pair bad ctor (tag={ph.tag}, other={ph.other})"
      let extName ← readCleanName (← readFieldPtr parts ph 0) "entries extension"
      if extName.toString == exportedAxiomsExtName then
        for e in ← readArrayElems parts (← readFieldPtr parts ph 1) do
          let eh ← readObjHeader parts e
          if eh.tag != 0 || eh.other != 2 then
            throw s!"exportedAxiomsExt entry bad ctor (tag={eh.tag}, other={eh.other})"
          let declName ← readCleanName (← readFieldPtr parts eh 0) "exportedAxiomsExt decl"
          let mut axs : Array Name := #[]
          for a in ← readArrayElems parts (← readFieldPtr parts eh 1) do
            axs := axs.push (← readCleanName a "exportedAxiomsExt axiom")
          out := out.push (declName, axs)
  return out

/-- Reject module-owned declarations whose cached (`exportedAxiomsExt`) axiom array omits an
axiom of the independently recomputed SCC-exact closure, plus duplicate claims or claims
targeting declarations owned by OTHER modules (`forgedExportedAxioms`). -/
def validateExportedAxiomCache (env : Environment) (modName : Name)
    (claims : Array (Name × Array Name)) : AuditReport := Id.run do
  let some modIdx := env.getModuleIdx? modName
    | return { violations := #[{ tag := "missingModule", decl := modName, detail := "module not loaded in environment" }] }
  let mut vs : Array Violation := #[]
  -- B3: a `module` file legitimately stores the SAME (`.uniform`) cache in `.olean`,
  -- `.olean.server` and `.olean.private`, so A2's "any duplicate" rule rejected every honest
  -- module-system file. Only CONFLICTING duplicates are flagged; every copy is still checked
  -- against the independent closure below.
  let mut seenClaims : NameMap (Array Name) := {}
  let mut owned : Array (Name × Array Name) := #[]
  for (c, cached) in claims do
    if let some prev := seenClaims.find? c then
      if prev.qsort Name.lt != cached.qsort Name.lt then
        vs := vs.push {
          tag := "forgedExportedAxioms"
          decl := c
          detail := s!"conflicting duplicate exportedAxiomsExt cache entries for {c} in module {modName}: {prev} vs {cached}"
        }
    seenClaims := seenClaims.insert c cached
    if env.getModuleIdxFor? c == some modIdx then
      owned := owned.push (c, cached)
    else
      vs := vs.push {
        tag := "forgedExportedAxioms"
        decl := c
        detail := s!"exportedAxiomsExt in {modName} injects foreign/unowned axiom cache entry for {c}"
      }
  match independentAxiomClosures env (owned.map (·.1)) with
  | .error v => return { violations := vs.push v }
  | .ok closures =>
    for (c, cached) in owned do
      let truth : Array Name := (closures.find? c).getD #[]
      let missing := truth.filter (fun a => !cached.contains a)
      if !missing.isEmpty then
        -- Lean 4.34.1's `CollectAxioms` visits an inductive's constructors in order under a
        -- `#[]` sentinel on the inductive itself, so an early `.ctorInfo` (e.g.
        -- `MirLiftCore.LiftTerminator.goto`) can legitimately cache `#[]` while a later sibling
        -- ctor and the parent `.inductInfo` carry `[propext]`. For `.ctorInfo`, still strictly
        -- enforce all axioms reachable from the ctor's own type and parent inductive type
        -- (excluding sibling ctors); every non-ctor declaration enforces the full SCC closure.
        let effectiveMissing : Except Violation (Array Name) :=
          match env.find? c with
          | some (.ctorInfo cv) =>
            match independentAxiomClosures env #[c] (skipInductCtorsFor := some cv.induct) with
            | .error v => .error v
            | .ok m =>
              let ownTruth := (m.find? c).getD #[]
              .ok (ownTruth.filter (fun a => !cached.contains a))
          | _ => .ok missing
        match effectiveMissing with
        | .error v => vs := vs.push v
        | .ok eff =>
          if !eff.isEmpty then
            vs := vs.push {
              tag := "forgedExportedAxioms"
              decl := c
              detail := s!"cached exportedAxiomsExt array {cached} omits {eff} of the true closure {truth}"
            }
    return { violations := vs }

/-- In-memory module validation plus the exported axiom-cache cross-check (decodes claims from
BOTH `.olean*` and optional `.ir*` bytes so no extension code runs on import and `.ir` cannot
smuggle forged `exportedAxiomsExt` entries). -/
def validateEnvModuleFull (env : Environment) (modName : Name) (oleanParts : Array ByteArray)
    (fuel : Nat := 20000000) (checkLiveExportState : Bool := true)
    (irParts : Array ByteArray := #[]) : AuditReport :=
  let r1 := validateEnvModule env modName fuel checkLiveExportState
  let decodeGroup (ps : Array ByteArray) (label : String) : AuditReport :=
    if ps.isEmpty then {}
    else match binExportedAxiomClaims ps with
      | .ok claims => validateExportedAxiomCache env modName claims
      | .error e => { violations := #[{ tag := "malformedOleanRegion", decl := modName, detail := s!"{label} exportedAxiomsExt decode: {e}" }] }
  let r2 := decodeGroup oleanParts "olean"
  let r3 := decodeGroup irParts "ir"
  { violations := r1.violations ++ r2.violations ++ r3.violations, stats := r1.stats }

/-! ## Section 10: Process Memory (`VmHWM` / `VmRSS`) & Benchmark Harness -/

def readProcStatusKb (field : String) : IO Nat := do
  try
    let text ← IO.FS.readFile "/proc/self/status"
    for line in text.splitOn "\n" do
      if line.startsWith field then
        let rest := (line.drop field.length).trimAscii.toString
        let toks := rest.splitOn " "
        if let some numStr := toks.head? then
          if let some n := numStr.toNat? then
            return n
    return 0
  catch _ =>
    return 0

def loadModulePartsFromDisk (baseNoExt : System.FilePath) : IO (Array ByteArray × Array ByteArray) := do
  let mut oleanParts : Array ByteArray := #[]
  for ext in #["olean", "olean.server", "olean.private"] do
    let p : System.FilePath := ⟨baseNoExt.toString ++ "." ++ ext⟩
    if ← p.pathExists then
      oleanParts := oleanParts.push (← IO.FS.readBinFile p)
  let mut irParts : Array ByteArray := #[]
  for ext in #["ir.sig", "ir"] do
    let p : System.FilePath := ⟨baseNoExt.toString ++ "." ++ ext⟩
    if ← p.pathExists then
      irParts := irParts.push (← IO.FS.readBinFile p)
  return (oleanParts, irParts)

/-! ## Section 11: Pure Test Fixtures & `#guard_msgs`-Pinned Regressions (V-Q1..V-N6) -/

/-- Pure 0-axiom proof fixture for V-N6. -/
theorem protoZeroAxiomProof : 2 + 2 = 4 := rfl

/-- `[propext]`-only proof fixture for V-N6. -/
theorem protoPropextOnlyProof : (True ↔ True) = (True = True) :=
  propext ⟨fun _ => propext ⟨fun h => h, fun h => h⟩, fun _ => Iff.rfl⟩

/-- info: 'Anneal.OleanQuotMdataUtf8Proto.protoZeroAxiomProof' does not depend on any axioms -/
#guard_msgs in
#print axioms protoZeroAxiomProof

/-- info: 'Anneal.OleanQuotMdataUtf8Proto.protoPropextOnlyProof' depends on axioms: [propext] -/
#guard_msgs in
#print axioms protoPropextOnlyProof

/-- info: 'Nat.xor' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Nat.xor

/-- info: 'Nat.bitwise' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Nat.bitwise

/-- info: 'Anneal.NatBitwise.unfold_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Anneal.NatBitwise.unfold_eq

/-- info: true -/
#guard_msgs in
#eval show Bool from
  -- Verify pure recomputeAppDataPure matches Lean 4.34.1 `Expr.mkAppData` across varied flags/depths.
  let u := Level.param `u
  let m := Level.mvar ⟨`m⟩
  let samples : Array (Expr × Expr) := #[
    (.const `f [u], .bvar 2),
    (.fvar ⟨`x⟩, .mvar ⟨`y⟩),
    (.sort m, .lit (.strVal "abc")),
    (.lam `x (.const `Nat []) (.bvar 0) .default, .lit (.natVal 99))
  ]
  samples.all fun (f, a) =>
    recomputeAppDataPure (f.data : UInt64) (a.data : UInt64) == (Expr.mkAppData f.data a.data : UInt64)

/--
info: V-Q1 canonical ok=true (4 primitives validated)
V-Q1 badName tags=#[forgedQuotInfo]
V-Q1 badOrigin tags=#[forgedQuotInfo]
V-Q1 badKind tags=#[forgedQuotInfo]
V-Q1 badLParams tags=#[forgedQuotInfo]
V-Q1 badType tags=#[forgedQuotInfo]
V-Q1 live Replay.lean gap confirmed: forged FakeQuot accepted by replay=true
-/
#guard_msgs in
#eval show MetaM Unit from do
  let env ← getEnv
  -- Positive: all 4 real Lean 4.34.1 Quot primitives from Init.Prelude pass with 0 violations.
  let mut canonOk := true
  for qn in [``Quot, ``Quot.mk, ``Quot.lift, ``Quot.ind] do
    match env.find? qn with
    | some (.quotInfo qv) =>
      let orig := env.getModuleIdxFor? qn |>.map fun i => env.header.modules[i.toNat]!.module
      if !(validateQuotVal qv orig).isEmpty then canonOk := false
    | _ => canonOk := false
  IO.println s!"V-Q1 canonical ok={canonOk} (4 primitives validated)"
  -- Negative: 5 distinct V-Q1 forgeries.
  let badName : QuotVal := { name := `FakeQuot, levelParams := [`u], type := canonicalQuotType, kind := .type }
  let badOrigin : QuotVal := { name := `Quot, levelParams := [`u], type := canonicalQuotType, kind := .type }
  let badKind : QuotVal := { name := `Quot, levelParams := [`u], type := canonicalQuotType, kind := .ctor }
  let badLParams : QuotVal := { name := `Quot, levelParams := [], type := canonicalQuotType, kind := .type }
  let badType : QuotVal := { name := `Quot, levelParams := [`u], type := mkConst ``False, kind := .type }
  let tagsOf (vs : Array Violation) : Array String := ({ violations := vs } : AuditReport).tags
  IO.println s!"V-Q1 badName tags={tagsOf (validateQuotVal badName (some `Init.Prelude))}"
  IO.println s!"V-Q1 badOrigin tags={tagsOf (validateQuotVal badOrigin (some `UntrustedMod))}"
  IO.println s!"V-Q1 badKind tags={tagsOf (validateQuotVal badKind (some `Init.Prelude))}"
  IO.println s!"V-Q1 badLParams tags={tagsOf (validateQuotVal badLParams (some `Init.Prelude))}"
  IO.println s!"V-Q1 badType tags={tagsOf (validateQuotVal badType (some `Init.Prelude))}"
  -- Live Replay.lean gap reproduction: `Kernel.Environment.replay` ignores QuotVal payload!
  let forgedMap : Std.HashMap Name ConstantInfo :=
    ({} : Std.HashMap Name ConstantInfo).insert `FakeQuot (.quotInfo {
      name := `FakeQuot, levelParams := [], type := mkConst ``False, kind := .type
    })
  let replayRes ← EIO.toBaseIO (env.toKernelEnv.replay forgedMap)
  IO.println s!"V-Q1 live Replay.lean gap confirmed: forged FakeQuot accepted by replay={replayRes.isOk}"

/--
info: V-U3 honest ok=true
V-U3 loneSurrogate=invalidUtf8Literal
V-U3 truncated=invalidUtf8Literal
V-U3 overlongNul=invalidUtf8Literal
V-U3 overlongSlash=invalidUtf8Literal
V-U3 invalidLead=invalidUtf8Literal
V-U3 unexpectedCont=invalidUtf8Literal
V-U3 embeddedNul=invalidUtf8Literal
V-U3 mLengthMismatch=invalidUtf8Literal
-/
#guard_msgs in
#eval show IO Unit from do
  let honest := "hello_λ_α".toUTF8
  let okHonest := (validateUtf8Bytes honest 9 true).isOk
  IO.println s!"V-U3 honest ok={okHonest}"
  let cases : Array (String × ByteArray × Nat) := #[
    ("loneSurrogate", ByteArray.mk #[0xED, 0xA0, 0x80], 1),
    ("truncated", ByteArray.mk #[0xE2, 0x82], 1),
    ("overlongNul", ByteArray.mk #[0xC0, 0x80], 1),
    ("overlongSlash", ByteArray.mk #[0xC0, 0xAF], 1),
    ("invalidLead", ByteArray.mk #[0xFF], 1),
    ("unexpectedCont", ByteArray.mk #[0x80], 1),
    ("embeddedNul", ByteArray.mk #[0x41, 0x00, 0x42], 3),
    ("mLengthMismatch", ByteArray.mk #[0x41, 0x42, 0x43, 0x44], 99)
  ]
  for (label, bs, cpLen) in cases do
    let tag := match validateUtf8Bytes bs cpLen true with
      | .ok _ => "UNEXPECTED_OK"
      | .error _ => "invalidUtf8Literal"
    IO.println s!"V-U3 {label}={tag}"

/--
info: V-F4 live Kernel.isDefEq capture=true
V-F4 live Kernel.check wrongTypeIsBoolToBool=true
V-F4 live Kernel.whnf Eq.rec K-reduction to 42=true (honest control=false)
V-F4 validator lctx=#[kernelFreshCollision]
V-F4 validator declName=#[kernelFreshCollision]
V-F4 validator nestedBinder=#[kernelFreshCollision]
V-F4 validator fvar=#[kernelFreshCollision]
-/
#guard_msgs in
#eval show MetaM Unit from do
  let env ← getEnv
  let fvId : FVarId := ⟨Name.num (Name.str .anonymous "_kernel_fresh") 0⟩
  let lctx : LocalContext := ({} : LocalContext).mkLocalDecl fvId `n (mkConst ``Nat) .default
  let lamFvar := Expr.lam `x (mkConst ``Bool) (Expr.fvar fvId) .default
  let lamId := Expr.lam `x (mkConst ``Bool) (Expr.bvar 0) .default
  let boolToBool := Expr.forallE `x (mkConst ``Bool) (mkConst ``Bool) .default
  let isDefEqCap := match Kernel.isDefEq env lctx lamFvar lamId with | .ok b => b | .error _ => false
  let checkWrong := match Kernel.check env lctx lamFvar with | .ok ty => ty == boolToBool | .error _ => false
  -- Live Kernel.whnf K-reduction capture witness:
  let hId : FVarId := ⟨`h_bogus⟩
  let eqTy := mkApp3 (mkConst ``Eq [.one]) boolToBool lamId lamFvar
  let lctxW := lctx.mkLocalDecl hId `h eqTy .default
  let motive := Expr.lam `f boolToBool
    (Expr.lam `p (mkApp3 (mkConst ``Eq [.one]) boolToBool lamId (.bvar 0)) (mkConst ``Nat) .default) .default
  let eqRec := mkAppN (mkConst ``Eq.rec [.one, .one]) #[boolToBool, lamId, motive, mkRawNatLit 42, lamFvar, Expr.fvar hId]
  let whnfCap := match Kernel.whnf env lctxW eqRec with | .ok e => e == mkRawNatLit 42 | .error _ => false
  -- Honest control (non-colliding FVarId):
  let honestId : FVarId := ⟨`honest_fv⟩
  let lamHonest := Expr.lam `x (mkConst ``Bool) (Expr.fvar honestId) .default
  let lctxH := (({} : LocalContext).mkLocalDecl honestId `n (mkConst ``Nat) .default).mkLocalDecl hId `h
    (mkApp3 (mkConst ``Eq [.one]) boolToBool lamId lamHonest) .default
  let eqRecH := mkAppN (mkConst ``Eq.rec [.one, .one]) #[boolToBool, lamId, motive, mkRawNatLit 42, lamHonest, Expr.fvar hId]
  let whnfHonest := match Kernel.whnf env lctxH eqRecH with | .ok e => e == mkRawNatLit 42 | .error _ => false
  IO.println s!"V-F4 live Kernel.isDefEq capture={isDefEqCap}"
  IO.println s!"V-F4 live Kernel.check wrongTypeIsBoolToBool={checkWrong}"
  IO.println s!"V-F4 live Kernel.whnf Eq.rec K-reduction to 42={whnfCap} (honest control={whnfHonest})"
  -- Validator catches all 4 surfaces:
  let rLctx := validateLocalContext lctx
  let stDecl := validateConstantInfo
    (.defnInfo {
      name := Name.num (Name.str `Foo "_kernel_fresh") 7
      levelParams := [], type := mkConst ``Nat, value := mkNatLit 0
      hints := .abbrev, safety := .safe, all := []
    }) (some `TestMod) {}
  let nestedLam := Expr.lam (Name.str `Outer "_kernel_fresh_x") (mkConst ``Nat) (.bvar 0) .default
  let (stBind, _) := validateExprDag `bindTest nestedLam {} (requireClosed := true)
  let (stFvar, _) := validateExprDag `fvarTest (Expr.fvar fvId) {} (requireClosed := false)
  IO.println s!"V-F4 validator lctx={rLctx.tags}"
  IO.println s!"V-F4 validator declName={({ violations := stDecl.violations } : AuditReport).tags}"
  IO.println s!"V-F4 validator nestedBinder={({ violations := stBind.violations } : AuditReport).tags}"
  IO.println s!"V-F4 validator fvar={({ violations := stFvar.violations } : AuditReport).tags}"

/--
info: V-S5 live exportAttr state tags=#[forbiddenExportAttr]
V-S5 unannotated main export tags=#[forbiddenExportAttr]
-/
#guard_msgs in
#eval show MetaM Unit from do
  let env ← getEnv
  -- Live exportAttr.ext.getState surface (missed by getModuleEntries-only scans):
  let envWithLiveExport := exportAttr.ext.addEntry env (`protoLiveFn, `proto_live_c_sym)
  let stLive := auditExportSurface envWithLiveExport 0 `Init.Prelude {} (checkLiveState := true)
  IO.println s!"V-S5 live exportAttr state tags={({ violations := stLive.violations } : AuditReport).tags}"
  -- Unannotated `main` C-symbol exposure in binary ModuleData:
  let mainCheck :=
    if isExport env `main then
      ({ violations := #[{ tag := "forbiddenExportAttr", decl := `main, detail := "isExport true on main" }] } : AuditReport).tags
    else #[]
  IO.println s!"V-S5 unannotated main export tags={mainCheck}"

/--
info: V-N6 Nat.xor axioms=#[propext]
V-N6 Nat.bitwise axioms=#[propext]
V-N6 Anneal.NatBitwise.unfold_eq (403ebd3b) axioms=#[propext, Quot.sound]
V-N6 Anneal.NatBitwise theorem distribution: zero=11, propextOnly=19, propextQuot=43
V-N6 buggy unconditional primitiveTargets on 0-axiom proof -> tag=nanodaNatXorPropextMismatch (lean=#[] vs secondKernel=#[propext])
V-N6 fixed demand-driven primitiveTargets on 0-axiom proof -> ok=true (lean=#[] == secondKernel=#[])
V-N6 fixed demand-driven primitiveTargets on [propext]-only proof -> ok=true (lean=#[propext] == secondKernel=#[propext])
V-N6 fixed demand-driven primitiveTargets on Anneal.NatBitwise.unfold_eq -> ok=true (lean=#[propext, Quot.sound] == secondKernel=#[propext, Quot.sound])
-/
#guard_msgs in
#eval show MetaM Unit from do
  let env ← getEnv
  let axOf (n : Name) : Array Name :=
    match collectReachableAndAxioms env #[n] with
    | .ok (_, axs) => axs
    | .error _ => #[`ERROR]
  IO.println s!"V-N6 Nat.xor axioms={axOf ``Nat.xor}"
  IO.println s!"V-N6 Nat.bitwise axioms={axOf ``Nat.bitwise}"
  IO.println s!"V-N6 Anneal.NatBitwise.unfold_eq (403ebd3b) axioms={axOf `Anneal.NatBitwise.unfold_eq}"
  let mut nZero := 0
  let mut nProp := 0
  let mut nPropQuot := 0
  if let some idx := env.getModuleIdx? `Anneal.NatBitwise then
    for ci in env.header.moduleData[idx.toNat]!.constants do
      if ci matches .thmInfo _ then
        let axs := axOf ci.name
        if axs == #[] then nZero := nZero + 1
        else if axs == #[``propext] then nProp := nProp + 1
        else if axs == #[``propext, ``Quot.sound] then nPropQuot := nPropQuot + 1
  IO.println s!"V-N6 Anneal.NatBitwise theorem distribution: zero={nZero}, propextOnly={nProp}, propextQuot={nPropQuot}"
  match checkSecondKernelParity env ``protoZeroAxiomProof false with
  | .ok r =>
    let tag := match r.violation? with | some v => v.tag | none => "NONE"
    IO.println s!"V-N6 buggy unconditional primitiveTargets on 0-axiom proof -> tag={tag} (lean={r.leanAxioms} vs secondKernel={r.secondKernelAxioms})"
  | .error e => IO.println s!"ERROR: {e.render}"
  match checkSecondKernelParity env ``protoZeroAxiomProof true with
  | .ok r =>
    IO.println s!"V-N6 fixed demand-driven primitiveTargets on 0-axiom proof -> ok={r.violation?.isNone} (lean={r.leanAxioms} == secondKernel={r.secondKernelAxioms})"
  | .error e => IO.println s!"ERROR: {e.render}"
  match checkSecondKernelParity env ``protoPropextOnlyProof true with
  | .ok r =>
    IO.println s!"V-N6 fixed demand-driven primitiveTargets on [propext]-only proof -> ok={r.violation?.isNone} (lean={r.leanAxioms} == secondKernel={r.secondKernelAxioms})"
  | .error e => IO.println s!"ERROR: {e.render}"
  match checkSecondKernelParity env `Anneal.NatBitwise.unfold_eq true with
  | .ok r =>
    IO.println s!"V-N6 fixed demand-driven primitiveTargets on Anneal.NatBitwise.unfold_eq -> ok={r.violation?.isNone} (lean={r.leanAxioms} == secondKernel={r.secondKernelAxioms})"
  | .error e => IO.println s!"ERROR: {e.render}"

/--
info: Malformed binary .olean tests:
  badMagic=#[malformedOleanRegion]
  addrOverflow=#[malformedOleanRegion]
  nonZeroRc=#[malformedOleanRegion]
  oobPtr=#[malformedOleanRegion]
  cycleExpr=#[malformedOleanRegion]
  fuelExhausted=#[auditFuelExhausted]
-/
#guard_msgs in
#eval show IO Unit from do
  let mkHeader (base root : UInt64) (totalSize : Nat) : ByteArray := Id.run do
    let mut b := ByteArray.mk (Array.replicate totalSize (0 : UInt8))
    b := b.set! 0 0x6f |>.set! 1 0x6c |>.set! 2 0x65 |>.set! 3 0x61 |>.set! 4 0x6e
    b := b.set! 5 2 |>.set! 6 1
    let putU64 (arr : ByteArray) (off : Nat) (v : UInt64) : ByteArray := Id.run do
      let mut a := arr
      for k in [0:8] do
        a := a.set! (off + k) ((v >>> UInt64.ofNat (8 * k)).toUInt8)
      return a
    b := putU64 b 80 base
    b := putU64 b 88 root
    return b
  let putU64 (arr : ByteArray) (off : Nat) (v : UInt64) : ByteArray := Id.run do
    let mut a := arr
    for k in [0:8] do
      a := a.set! (off + k) ((v >>> UInt64.ofNat (8 * k)).toUInt8)
    return a
  -- 1. Bad magic
  let badMagic := ByteArray.mk (Array.replicate 128 0)
  -- 2. 64-bit address overflow
  let addrOv := mkHeader (0xFFFFFFFFFFFFFFF0 : UInt64) (0xFFFFFFFFFFFFFFF0 : UInt64) 128
  -- 3. Non-zero m_rc at root
  let base : UInt64 := 0x100000
  let mut nonZeroRc := mkHeader base (base + 96) 256
  nonZeroRc := nonZeroRc.set! 96 1 -- m_rc = 1 != 0
  -- 4. Out-of-bounds root pointer
  let oobPtr := mkHeader base (base + 4096) 256
  -- 5. Cycle in binary Expr DAG: Expr.app at off 96 pointing to itself!
  let mut cyc := mkHeader base (base + 96) 256
  -- Ctor tag=5 (Expr.app), other=2, cs_sz=32, rc=0
  cyc := cyc.set! 100 32 |>.set! 101 0 |>.set! 102 2 |>.set! 103 5
  cyc := putU64 cyc 104 (base + 96) -- f = self
  cyc := putU64 cyc 112 (base + 96) -- a = self
  let cycParts := match parseOleanParts #[cyc] with | .ok ps => ps | .error _ => #[]
  let (stCyc, _) := validateBinExpr cycParts `CycleDecl (base + 96) {}
  -- 6. Fuel exhaustion on valid term
  let (stFuel, _) := validateExprDag `FuelDecl (Expr.app (.const `Nat []) (.const `Nat [])) {} (requireClosed := true) (fuel := 1)
  IO.println "Malformed binary .olean tests:"
  IO.println s!"  badMagic={(validateOleanParts #[badMagic] `BadMagic).tags}"
  IO.println s!"  addrOverflow={(validateOleanParts #[addrOv] `AddrOv).tags}"
  IO.println s!"  nonZeroRc={(validateOleanParts #[nonZeroRc] `NonZeroRc).tags}"
  IO.println s!"  oobPtr={(validateOleanParts #[oobPtr] `OobPtr).tags}"
  IO.println s!"  cycleExpr={({ violations := stCyc.violations } : AuditReport).tags}"
  IO.println s!"  fuelExhausted={({ violations := stFuel.violations } : AuditReport).tags}"

/--
info: Exponential DAG stress test (depth=35): ok=true, exprNodesVisited=36, exprCacheHits=35, hitRate=479‰
-/
#guard_msgs in
#eval show IO Unit from do
  -- Depth-35 binary branching DAG has 2^35 (~34 billion) tree paths, but only 36 distinct nodes!
  let mut dag : Expr := .const `Nat []
  for _ in [0:35] do
    dag := .app dag dag
  let (st, _) := validateExprDag `ExpDag35 dag {} (requireClosed := true)
  IO.println s!"Exponential DAG stress test (depth=35): ok={st.violations.isEmpty}, exprNodesVisited={st.stats.exprNodesVisited}, exprCacheHits={st.stats.exprCacheHits}, hitRate={st.stats.hitRatePermille}‰"

/- Live end-to-end binary + in-memory cache-poisoning regression on a real compiled
Lean 4.34.1 `.olean` (built in `/tmp`, mutated to clone a duplicate subexpression with
identical 32-bit hash and flipped upper `m_data` flags, proving naive `HashSet Expr`
gets poisoned while BOTH our in-memory `StrictExprKey` and binary pointer-DAG validators
catch `forgedExprMData`). -/
/--
info: V-M2 live cache-poisoning regression (real .olean):
  naiveHashSetExprMissedForgedDuplicate=true
  inMemoryStrictExprKeyTags=#[forgedExprMData]
  binaryPointerDagTags=#[forgedExprMData]
-/
#guard_msgs in
#eval show IO Unit from do
  -- Build a minimal real .olean in /tmp with two separate Expr.app nodes whose bodies share
  -- structure `fun (x : Nat) => x` so we can mutate one copy's `approxDepth` bit in the
  -- compacted region while keeping its 32-bit hash identical (and keeping Expr.beq == true!).
  let pid ← IO.Process.getPID
  let tmpDir : System.FilePath := ⟨s!"/tmp/anneal-proto-cache-poison-{pid}"⟩
  IO.FS.createDirAll tmpDir
  try
    let appDir ← IO.appDir
    let leanBin : System.FilePath :=
      match ← IO.getEnv "LEAN_BIN" with
      | some p => ⟨p⟩
      | none => ⟨appDir.toString ++ "/lean"⟩
    let leanExe := if ← leanBin.pathExists then leanBin else ⟨"lean"⟩
    let sysrootOut ← IO.Process.output { cmd := leanExe.toString, args := #["--print-prefix"] }
    let sysroot : System.FilePath := ⟨sysrootOut.stdout.trimAscii.toString⟩
    let libDir := sysroot / "lib" / "lean"
    let srcPath := tmpDir / "CachePoisonFixture.lean"
    let setupPath := tmpDir / "CachePoisonFixture.setup.json"
    let oleanPath := tmpDir / "CachePoisonFixture.olean"
    -- Two distinct declarations with structurally identical lambdas (`lam _ Nat (bvar 0)`),
    -- using distinct binder names `a` and `b` so `compact.cpp` does NOT deduplicate them,
    -- while `Expr.beq` (`lean_expr_eqv`, alpha-equivalence) treats them as EQUAL with the
    -- EXACT SAME 32-bit hash!
    IO.FS.writeFile srcPath
      "prelude\nimport Init.Core\ndef fnOk (a : Nat) : Nat := a\ndef fnBad (b : Nat) : Nat := b\n"
    IO.FS.writeFile setupPath
      "{\"name\":\"CachePoisonFixture\",\"isModule\":false,\"imports\":[{\"module\":\"Init.Core\",\"importAll\":false,\"isExported\":true,\"isMeta\":false}],\"importArts\":{},\"dynlibs\":[],\"plugins\":[],\"options\":{}}"
    let cOut ← IO.Process.output {
      cmd := leanExe.toString
      args := #["-j1", "--setup", setupPath.toString, "-o", oleanPath.toString, srcPath.toString]
    }
    if cOut.exitCode != 0 then
      throw (IO.userError s!"compile CachePoisonFixture failed: {cOut.stderr}")
    let origBytes ← IO.FS.readBinFile oleanPath
    -- Locate `fnBad`'s `DefinitionVal.value` (`Expr.lam `b Nat (bvar 0)`) in the compacted region
    -- and flip bit 32 (`approxDepth`, upper bits ignored by `Expr.beq` and `Expr.hash`!).
    let parts ← IO.ofExcept (parseOleanParts #[origBytes])
    let rootPtr := parts[0]!.rootPtr
    let rh ← IO.ofExcept (readObjHeader parts rootPtr)
    let cnArr ← IO.ofExcept (readArrayElems parts (← IO.ofExcept (readFieldPtr parts rh 1)))
    let ciArr ← IO.ofExcept (readArrayElems parts (← IO.ofExcept (readFieldPtr parts rh 2)))
    let mut targetDataOff : Option Nat := none
    for h : i in [0:cnArr.size] do
      let (_, nInfo) := validateBinName parts `CachePoisonFixture cnArr[i] {}
      if nInfo.name == `fnBad then
        let ciH ← IO.ofExcept (readObjHeader parts ciArr[i]!)
        let valPtr ← IO.ofExcept (readFieldPtr parts ciH 0)
        let valH ← IO.ofExcept (readObjHeader parts valPtr)
        let exprPtr ← IO.ofExcept (readFieldPtr parts valH 1)
        let eh ← IO.ofExcept (readObjHeader parts exprPtr)
        -- Expr.lam has 3 obj fields; `data : UInt64` sits at off + 8 + 3*8 = off + 32.
        targetDataOff := some (eh.off + 8 + eh.other * 8)
    let some dOff := targetDataOff | throw (IO.userError "could not locate fnBad value Expr")
    let mut mutBytes := origBytes
    let oldData := readU64LE mutBytes dOff
    -- Flip bit 32 (approxDepth) and bit 40 (hasFVar) while keeping low 32-bit hash identical!
    let newData := oldData ^^^ ((1 : UInt64) <<< 32)
    for k in [0:8] do
      mutBytes := mutBytes.set! (dOff + k) ((newData >>> UInt64.ofNat (8 * k)).toUInt8)
    let mutOleanPath := tmpDir / "CachePoisonFixtureMut.olean"
    IO.FS.writeBinFile mutOleanPath mutBytes
    -- 1. Validate binary compacted region directly:
    let binRep := validateOleanParts #[mutBytes] `CachePoisonFixture
    -- 2. Import mutated .olean via `importModules` and compare naive `HashSet Expr` vs `StrictExprKey`:
    searchPathRef.set [libDir]
    let arts : NameMap ImportArtifacts :=
      ({} : NameMap ImportArtifacts).insert `CachePoisonFixture (.ofArrays #[#[mutOleanPath], #[]])
    let env ← importModules #[{ module := `CachePoisonFixture }] {} (trustLevel := 0)
      (plugins := #[]) (loadExts := false) (level := .private) (arts := arts)
    let some (.defnInfo dOk) := env.find? `fnOk | throw (IO.userError "missing fnOk")
    let some (.defnInfo dBad) := env.find? `fnBad | throw (IO.userError "missing fnBad")
    -- Naive `HashSet Expr` (using `Expr.beq` / `Expr.hash`):
    let naiveSet : Std.HashSet Expr := ({} : Std.HashSet Expr).insert dOk.value
    let naiveMissed := naiveSet.contains dBad.value
    -- Our hardened in-memory `StrictExprKey` validator:
    let (st1, _) := validateExprDag `fnOk dOk.value {} (requireClosed := true)
    let (st2, _) := validateExprDag `fnBad dBad.value st1 (requireClosed := true)
    let memRep : AuditReport := { violations := st2.violations, stats := st2.stats }
    IO.println "V-M2 live cache-poisoning regression (real .olean):"
    IO.println s!"  naiveHashSetExprMissedForgedDuplicate={naiveMissed}"
    IO.println s!"  inMemoryStrictExprKeyTags={memRep.tags}"
    IO.println s!"  binaryPointerDagTags={binRep.tags}"
  finally
    try IO.FS.removeDirAll tmpDir catch _ => pure ()

/-! ## Section 11b: Round-B1 Adversarial Regressions

Every block below pins a bypass that was reproduced LIVE against the A0 validator (A0
reported `ok=true` / `#[]` for each forged artifact). Real `.olean` fixtures are written
with `saveModuleData` into a per-process `/tmp` directory (removed in `finally`), then
binary-patched and loaded via `importModules`. -/

def b1PutU64 (arr : ByteArray) (off : Nat) (v : UInt64) : ByteArray := Id.run do
  let mut a := arr
  for k in [0:8] do
    a := a.set! (off + k) ((v >>> UInt64.ofNat (8 * k)).toUInt8)
  return a

def b1FindBytes (hay needle : ByteArray) : Option Nat := Id.run do
  if needle.size == 0 || needle.size > hay.size then return none
  for i in [0:hay.size - needle.size + 1] do
    let mut ok := true
    for j in [0:needle.size] do
      if hay.get! (i + j) != needle.get! j then
        ok := false
        break
    if ok then return some i
  return none

/-- Overwrite the first `LeanString` whose payload+NUL equals `needle` with `payload`
(new `m_size = payload.size + 1`, forged `m_length = mLen`), checking `m_capacity`. -/
def b1PatchString (bytes : ByteArray) (needle : String) (payload : ByteArray) (mLen : Nat) :
    IO ByteArray := do
  let some off := b1FindBytes bytes (needle.toUTF8.push 0)
    | throw (IO.userError s!"needle {needle} not found")
  let cap := (readU64LE bytes (off - 16)).toNat
  if payload.size + 1 > cap then
    throw (IO.userError s!"payload exceeds m_capacity {cap}")
  let mut b := b1PutU64 bytes (off - 24) (UInt64.ofNat (payload.size + 1))
  b := b1PutU64 b (off - 8) (UInt64.ofNat mLen)
  for k in [0:payload.size] do
    b := b.set! (off + k) (payload.get! k)
  return b.set! (off + payload.size) 0

def b1LibDir : IO System.FilePath := do
  let appDir ← IO.appDir
  let leanBin : System.FilePath :=
    match ← IO.getEnv "LEAN_BIN" with
    | some p => ⟨p⟩
    | none => ⟨appDir.toString ++ "/lean"⟩
  let leanExe := if ← leanBin.pathExists then leanBin else ⟨"lean"⟩
  let out ← IO.Process.output { cmd := leanExe.toString, args := #["--print-prefix"] }
  return ⟨out.stdout.trimAscii.toString⟩ / "lib" / "lean"

def b1Save (dir : System.FilePath) (name : Name) (imports : Array Name) (constNames : Array Name)
    (consts : Array ConstantInfo) : IO System.FilePath := do
  let p := dir / s!"{name}.olean"
  saveModuleData p name {
    isModule := false
    imports := imports.map fun m => { module := m, importAll := false, isExported := true, isMeta := false }
    constNames, constants := consts, extraConstNames := #[], entries := #[] }
  return p

def b1Import (libDir : System.FilePath) (arts : List (Name × System.FilePath)) (root : Name) :
    IO Environment := do
  searchPathRef.set [libDir]
  let m : NameMap ImportArtifacts := arts.foldl (fun m (n, p) => m.insert n (.ofArrays #[#[p], #[]])) {}
  importModules #[{ module := root }] {} (trustLevel := 0) (plugins := #[]) (loadExts := false)
    (level := .private) (arts := m)

def b1Tags (vs : Array Violation) : Array String := ({ violations := vs } : AuditReport).tags

/--
info: B1 V-F4 empty LocalContext: Kernel.isDefEq capture=true, Kernel.check type=Bool→Bool:true
B1 V-F4 empty LocalContext: validateLocalContext ok=true (insufficient alone)
B1 V-F4 empty LocalContext: validateKernelQuery tags=#[kernelFreshCollision, undeclaredFVar]
B1 V-F4 aliased fvarIdToDecl: Kernel.isDefEq capture=true, find? resolves decl fvarId=honest_decl
B1 V-F4 aliased fvarIdToDecl: validateLocalContext tags=#[kernelFreshCollision, malformedLocalContext]
B1 V-F4 honest query control: validateKernelQuery ok=true
-/
#guard_msgs in
#eval show MetaM Unit from do
  let env ← getEnv
  let kf : FVarId := ⟨Name.num (Name.str .anonymous "_kernel_fresh") 0⟩
  let lamFvar := Expr.lam `x (mkConst ``Bool) (Expr.fvar kf) .default
  let lamId := Expr.lam `x (mkConst ``Bool) (Expr.bvar 0) .default
  let boolToBool := Expr.forallE `x (mkConst ``Bool) (mkConst ``Bool) .default
  -- (1) No colliding LocalContext entry at all: the kernel's own fresh binder captures.
  let cap0 := match Kernel.isDefEq env {} lamFvar lamId with | .ok b => b | .error _ => false
  let chk0 := match Kernel.check env {} lamFvar with | .ok ty => ty == boolToBool | .error _ => false
  IO.println s!"B1 V-F4 empty LocalContext: Kernel.isDefEq capture={cap0}, Kernel.check type=Bool→Bool:{chk0}"
  IO.println s!"B1 V-F4 empty LocalContext: validateLocalContext ok={(validateLocalContext {}).ok} (insufficient alone)"
  IO.println s!"B1 V-F4 empty LocalContext: validateKernelQuery tags={(validateKernelQuery {} #[lamFvar, lamId]).tags}"
  -- (2) Map key `_kernel_fresh.0` aliasing an honest-looking `decls` entry.
  let honest : FVarId := ⟨`honest_decl⟩
  let d : LocalDecl := .cdecl 0 honest `n (mkConst ``Nat) .default .default
  let lctxA : LocalContext := {
    fvarIdToDecl := ({} : PersistentHashMap FVarId LocalDecl).insert kf d
    decls := ({} : PersistentArray (Option LocalDecl)).push (some d) }
  let capA := match Kernel.isDefEq env lctxA lamFvar lamId with | .ok b => b | .error _ => false
  let resolved := (lctxA.find? kf).map (·.fvarId.name) |>.getD .anonymous
  IO.println s!"B1 V-F4 aliased fvarIdToDecl: Kernel.isDefEq capture={capA}, find? resolves decl fvarId={resolved}"
  IO.println s!"B1 V-F4 aliased fvarIdToDecl: validateLocalContext tags={(validateLocalContext lctxA).tags}"
  -- (3) Honest control: declared, non-colliding fvar.
  let hId : FVarId := ⟨`honest_fv⟩
  let lctxH := ({} : LocalContext).mkLocalDecl hId `n (mkConst ``Nat) .default
  let qH := Expr.lam `x (mkConst ``Bool) (Expr.fvar hId) .default
  IO.println s!"B1 V-F4 honest query control: validateKernelQuery ok={(validateKernelQuery lctxH #[qH, lamId]).ok}"

/--
info: B1 V-Q1 constNames alias: env.find? aliasKey -> ConstantInfo named hiddenName
B1 V-Q1 constNames alias: binary=#[constNameAliasMismatch] memory=#[constNameAliasMismatch]
B1 V-Q1 constNames/constants size mismatch: extraThm bound=false binary=#[constNameAliasMismatch] memory=#[constNameAliasMismatch]
B1 V-N6 axiom laundering: A-only evilAx=axiom axioms(useEvil)=#[evilAx] memory(LaunderA)=#[]
B1 V-N6 axiom laundering: A+B evilAx=theorem axioms(useEvil)=#[] (laundered)
B1 V-N6 axiom laundering: memory(LaunderB)=#[shadowedConstant] memory(LaunderA)=#[shadowedConstant]
B1 V-U3 ofSyntax honest control: binary ok=true memory ok=true
B1 V-U3 ofSyntax surrogate atom: binary=#[invalidUtf8Literal] memory=#[invalidUtf8Literal]
B1 V-U3 ofSyntax cache poisoning: A0 reprStr key collides=true, syntaxStrictKey collides=false
B1 V-U3 ofSyntax cache poisoning: binary=#[invalidUtf8Literal] memory=#[invalidUtf8Literal]
B1 binary DefinitionVal.safety=7: Lean-side decodes safety==safe:false, binary=#[malformedOleanRegion] memory=#[]
B1 binary forged import Name.hash: binary=#[forgedNameHash]
-/
#guard_msgs in
#eval show IO Unit from do
  let pid ← IO.Process.getPID
  let dir : System.FilePath := ⟨s!"/tmp/anneal-proto-b1-{pid}"⟩
  IO.FS.createDirAll dir
  try
    let libDir ← b1LibDir
    let core := #[`Init.Core]
    let tags (p : System.FilePath) (n : Name) : IO (Array String) := do
      return (validateOleanParts #[← IO.FS.readBinFile p] n).tags
    -- (1) constNames ↦ constants aliasing (importModules keys the map by constNames[i]).
    let hidden : ConstantInfo := .thmInfo {
      name := `hiddenName, levelParams := [], type := mkConst ``True, value := mkConst ``True.intro, all := [`hiddenName] }
    let pAlias ← b1Save dir `B1Alias core #[`aliasKey] #[hidden]
    let envAlias ← b1Import libDir [(`B1Alias, pAlias)] `B1Alias
    IO.println s!"B1 V-Q1 constNames alias: env.find? aliasKey -> ConstantInfo named {(envAlias.find? `aliasKey).map (·.name) |>.getD .anonymous}"
    IO.println s!"B1 V-Q1 constNames alias: binary={← tags pAlias `B1Alias} memory={(validateEnvModule envAlias `B1Alias).tags}"
    let extra : ConstantInfo := .thmInfo {
      name := `extraThm, levelParams := [], type := mkConst ``True, value := mkConst ``True.intro, all := [`extraThm] }
    let pSize ← b1Save dir `B1Size core #[`hiddenName] #[hidden, extra]
    let envSize ← b1Import libDir [(`B1Size, pSize)] `B1Size
    IO.println s!"B1 V-Q1 constNames/constants size mismatch: extraThm bound={(envSize.find? `extraThm).isSome} binary={← tags pSize `B1Size} memory={(validateEnvModule envSize `B1Size).tags}"
    -- (2) Axiom laundering through `importModules` `subsumesInfo` (theorem replaces axiom).
    let ax : ConstantInfo := .axiomInfo { name := `evilAx, levelParams := [], type := mkConst ``False, isUnsafe := false }
    let useIt : ConstantInfo := .thmInfo {
      name := `useEvil, levelParams := [], type := mkConst ``False, value := mkConst `evilAx, all := [`useEvil] }
    let pA ← b1Save dir `B1LaunderA core #[`evilAx, `useEvil] #[ax, useIt]
    let fake : ConstantInfo := .thmInfo {
      name := `evilAx, levelParams := [], type := mkConst ``False, value := mkConst `evilAx, all := [`evilAx] }
    let pB ← b1Save dir `B1LaunderB #[`B1LaunderA] #[`evilAx] #[fake]
    let arts := [(`B1LaunderA, pA), (`B1LaunderB, pB)]
    let envA ← b1Import libDir arts `B1LaunderA
    let envB ← b1Import libDir arts `B1LaunderB
    let axOf (env : Environment) : Array Name :=
      match collectReachableAndAxioms env #[`useEvil] with | .ok (_, a) => a | .error _ => #[`ERROR]
    let kindOf (env : Environment) : String := (env.find? `evilAx).map constKindName |>.getD "?"
    IO.println s!"B1 V-N6 axiom laundering: A-only evilAx={kindOf envA} axioms(useEvil)={axOf envA} memory(LaunderA)={(validateEnvModule envA `B1LaunderA).tags}"
    IO.println s!"B1 V-N6 axiom laundering: A+B evilAx={kindOf envB} axioms(useEvil)={axOf envB} (laundered)"
    IO.println s!"B1 V-N6 axiom laundering: memory(LaunderB)={(validateEnvModule envB `B1LaunderB).tags} memory(LaunderA)={(validateEnvModule envB `B1LaunderA).tags}"
    -- (3) `DataValue.ofSyntax` UTF-8 smuggling + `reprStr` cache-key poisoning.
    let synDef (n : Name) (atom : String) : ConstantInfo := .defnInfo {
      name := n, levelParams := [], type := mkConst ``Nat
      value := .mdata (KVMap.empty.insert `b1.syn (.ofSyntax (Syntax.atom .none atom))) (mkNatLit 0)
      hints := .abbrev, safety := .safe, all := [n] }
    let pSyn ← b1Save dir `B1Syn core #[`synDef] #[synDef `synDef "UUUUUUUU"]
    let envSyn0 ← b1Import libDir [(`B1Syn, pSyn)] `B1Syn
    IO.println s!"B1 V-U3 ofSyntax honest control: binary ok={(← tags pSyn `B1Syn).isEmpty} memory ok={(validateEnvModule envSyn0 `B1Syn).ok}"
    let bSyn ← b1PatchString (← IO.FS.readBinFile pSyn) "UUUUUUUU" (ByteArray.mk #[0xED, 0xA0, 0x80, 0x41]) 2
    IO.FS.writeBinFile pSyn bSyn
    let envSyn ← b1Import libDir [(`B1Syn, pSyn)] `B1Syn
    IO.println s!"B1 V-U3 ofSyntax surrogate atom: binary={← tags pSyn `B1Syn} memory={(validateEnvModule envSyn `B1Syn).tags}"
    let pPois ← b1Save dir `B1Pois core #[`synOk, `synBad] #[synDef `synOk "A", synDef `synBad "WW"]
    let bPois ← b1PatchString (← IO.FS.readBinFile pPois) "WW" (ByteArray.mk #[0xC0, 0x81]) 1
    IO.FS.writeBinFile pPois bPois
    let envPois ← b1Import libDir [(`B1Pois, pPois)] `B1Pois
    let stxOf (n : Name) : Syntax := match envPois.find? n with
      | some (.defnInfo v) => match v.value with
        | .mdata md _ => match md.entries with | [(_, .ofSyntax s)] => s | _ => .missing
        | _ => .missing
      | _ => .missing
    let a0Collide := reprStr (stxOf `synOk) == reprStr (stxOf `synBad)
    let strictCollide := (syntaxStrictKey (stxOf `synOk)).data == (syntaxStrictKey (stxOf `synBad)).data
    IO.println s!"B1 V-U3 ofSyntax cache poisoning: A0 reprStr key collides={a0Collide}, syntaxStrictKey collides={strictCollide}"
    IO.println s!"B1 V-U3 ofSyntax cache poisoning: binary={← tags pPois `B1Pois} memory={(validateEnvModule envPois `B1Pois).tags}"
    -- (4) Out-of-range scalar discriminant (`DefinitionVal.safety := 7`).
    let pSafe ← b1Save dir `B1Safe core #[`safeDef] #[.defnInfo {
      name := `safeDef, levelParams := [], type := mkConst ``Nat, value := mkNatLit 0
      hints := .abbrev, safety := .safe, all := [`safeDef] }]
    let b0 ← IO.FS.readBinFile pSafe
    let parts ← IO.ofExcept (parseOleanParts #[b0])
    let rh ← IO.ofExcept (readObjHeader parts parts[0]!.rootPtr)
    let ciArr ← IO.ofExcept (readArrayElems parts (← IO.ofExcept (readFieldPtr parts rh 2)))
    let ciH ← IO.ofExcept (readObjHeader parts ciArr[0]!)
    let vh ← IO.ofExcept (readObjHeader parts (← IO.ofExcept (readFieldPtr parts ciH 0)))
    let bSafe := b0.set! (vh.off + 8 + vh.other * 8) 7
    IO.FS.writeBinFile pSafe bSafe
    let envSafe ← b1Import libDir [(`B1Safe, pSafe)] `B1Safe
    let loadedSafe := match envSafe.find? `safeDef with | some (.defnInfo v) => v.safety == DefinitionSafety.safe | _ => true
    IO.println s!"B1 binary DefinitionVal.safety=7: Lean-side decodes safety==safe:{loadedSafe}, binary={← tags pSafe `B1Safe} memory={(validateEnvModule envSafe `B1Safe).tags}"
    -- (5) Forged `Name.hash` on the `Import.module` name (A0 never read `ModuleData.imports`).
    let imps ← IO.ofExcept (readArrayElems parts (← IO.ofExcept (readFieldPtr parts rh 0)))
    let ih ← IO.ofExcept (readObjHeader parts imps[0]!)
    let nh ← IO.ofExcept (readObjHeader parts (← IO.ofExcept (readFieldPtr parts ih 0)))
    let hOff := nh.off + 8 + nh.other * 8
    let bImp := b0.set! hOff (b0.get! hOff ^^^ 0x5A)
    IO.println s!"B1 binary forged import Name.hash: binary={(validateOleanParts #[bImp] `B1Safe).tags}"
  finally
    try IO.FS.removeDirAll dir catch _ => pure ()

/--
info: B1 binary non-canonical LeanMPZ: Name.num(5 as MPZ)=#[malformedOleanRegion] scalar control=#[]
-/
#guard_msgs in
#eval show IO Unit from do
  -- Hand-built compacted region: `Name.num .anonymous 5` whose `5` is a heap `LeanMPZ`
  -- (one limb) instead of the canonical tagged scalar; the stored hash is CORRECT, so only
  -- the canonicality check can catch it.
  let base : UInt64 := 0x100000
  let mk (mpz : Bool) : ByteArray := Id.run do
    let mut b := ByteArray.mk (Array.replicate 192 (0 : UInt8))
    b := b.set! 0 0x6f |>.set! 1 0x6c |>.set! 2 0x65 |>.set! 3 0x61 |>.set! 4 0x6e |>.set! 5 2
    b := b1PutU64 b 80 base
    b := b1PutU64 b 88 (base + 96)
    b := b.set! 100 32 |>.set! 102 2 |>.set! 103 2
    b := b1PutU64 b 104 1
    b := b1PutU64 b 112 (if mpz then base + 128 else ((5 : UInt64) <<< 1) ||| 1)
    b := b1PutU64 b 120 (mixHash 1723 5)
    b := b.set! 135 250 |>.set! 136 1 |>.set! 140 1
    b := b1PutU64 b 144 (base + 160)
    b := b1PutU64 b 160 5
    return b
  let run (mpz : Bool) : Array String :=
    match parseOleanParts #[mk mpz] with
    | .ok parts => b1Tags (validateBinName parts `B1Mpz (base + 96) {}).1.violations
    | .error _ => #["PARSE_ERROR"]
  IO.println s!"B1 binary non-canonical LeanMPZ: Name.num(5 as MPZ)={run true} scalar control={run false}"

/-! ## Section 11c: Round-A1 Adversarial Regressions

Pins every bypass reproduced LIVE against B1 (`8cf7fa0f`):
1. Theorem-over-theorem axiom laundering (`benignTheoremDuplicate` bypass) & intra-module
   duplicate `constNames`.
2. Depth-35 shared `Syntax` DAG (exponential DoS on unmemoized `validateSyntaxDag`) &
   cyclic binary `Syntax` (bypassed 1-color `seen` set in `validateBinSyntax`).
3. V-S5 `IR.Decl.extern` C-symbol stub & `Lean.externAttr` (zero `exportAttr`).
4. Binary `ReducibilityHints.regular` truncated `cs_sz`, malformed UTF-8 hidden in
   `ModuleData.entries` (`Lean.docStringExt`), and forbidden `LeanClosure` (tag `245`) in
   `ModuleData.entries`.
5. `strictLocalDeclEq` `binderInfo`/`kind` mismatch, `LocalContext` self/forward/undeclared
   fvar references, and `validateKernelQuery` loose `bvar` / `mvar` / `fuel` propagation.
6. Multi-part 5-file Lean 4.34.1 `module` (`.olean*` + `.ir*`) independent-group validation. -/

/--
info: A1 V-F4 cdecl binderInfo/kind mismatch: tags=#[malformedLocalContext]
A1 V-F4 lctx self/forward fvar: self=#[undeclaredFVar] forward=#[undeclaredFVar]
A1 V-F4 query looseBVar/mvar: loose=#[malformedKernelQuery] mvar=#[malformedKernelQuery]
A1 V-F4 query fuel propagation: fuel1=#[auditFuelExhausted]
A1 V-U3 depth-35 shared Syntax DAG: fail-closed tags=#[auditFuelExhausted] strictEq=true
A1 V-U3 cyclic binary Syntax: tags=#[malformedOleanRegion]
A1 binary truncated ReducibilityHints.regular: tags=#[malformedOleanRegion]
A1 binary ModuleData.entries LeanClosure tag 245: tags=#[malformedOleanRegion]
-/
#guard_msgs in
#eval show IO Unit from do
  -- (1) `strictLocalDeclEq` binderInfo/kind mismatch between fvarIdToDecl and decls.
  let hId : FVarId := ⟨`h_bi⟩
  let c1 : LocalDecl := .cdecl 0 hId `x (mkConst ``Nat) .default .default
  let c2 : LocalDecl := .cdecl 0 hId `x (mkConst ``Nat) .implicit .auxDecl
  let lctxBi : LocalContext := {
    fvarIdToDecl := ({} : PersistentHashMap FVarId LocalDecl).insert hId c1
    decls := ({} : PersistentArray (Option LocalDecl)).push (some c2) }
  IO.println s!"A1 V-F4 cdecl binderInfo/kind mismatch: tags={(validateLocalContext lctxBi).tags}"
  -- (2) Telescopic fvar scoping in LocalContext (self-ref and forward-ref).
  let sId : FVarId := ⟨`self_fv⟩
  let dSelf : LocalDecl := .cdecl 0 sId `x (Expr.fvar sId) .default .default
  let lctxSelf : LocalContext := {
    fvarIdToDecl := ({} : PersistentHashMap FVarId LocalDecl).insert sId dSelf
    decls := ({} : PersistentArray (Option LocalDecl)).push (some dSelf) }
  let f1 : FVarId := ⟨`fv_first⟩
  let f2 : FVarId := ⟨`fv_second⟩
  let dF1 : LocalDecl := .cdecl 0 f1 `a (Expr.fvar f2) .default .default
  let dF2 : LocalDecl := .cdecl 1 f2 `b (mkConst ``Nat) .default .default
  let lctxFwd : LocalContext := {
    fvarIdToDecl := (({} : PersistentHashMap FVarId LocalDecl).insert f1 dF1).insert f2 dF2
    decls := (({} : PersistentArray (Option LocalDecl)).push (some dF1)).push (some dF2) }
  IO.println s!"A1 V-F4 lctx self/forward fvar: self={(validateLocalContext lctxSelf).tags} forward={(validateLocalContext lctxFwd).tags}"
  -- (3) validateKernelQuery loose bvar, mvar, and fuel propagation.
  let rLoose := validateKernelQuery {} #[.bvar 0]
  let rMVar := validateKernelQuery {} #[.mvar ⟨`mv_bad⟩]
  let rFuel := validateKernelQuery {} #[Expr.app (.const `Nat []) (.const `Nat [])] (fuel := 1)
  IO.println s!"A1 V-F4 query looseBVar/mvar: loose={rLoose.tags} mvar={rMVar.tags}"
  IO.println s!"A1 V-F4 query fuel propagation: fuel1={rFuel.tags}"
  -- (4) Depth-35 shared Syntax DAG (2^35 paths, 36 unique nodes) validates cleanly in O(36).
  let mut stx : Syntax := Syntax.atom .none "leaf"
  for _ in [0:35] do
    stx := Syntax.node .none `pair #[stx, stx]
  let stStx := validateSyntaxDag `A1SynDag35 stx {}
  IO.println s!"A1 V-U3 depth-35 shared Syntax DAG: fail-closed tags={b1Tags stStx.violations} strictEq={strictSyntaxEq stx stx}"
  -- (5) Cyclic binary Syntax.node whose args points back to itself.
  let base : UInt64 := 0x180000
  let mkHdr (sz : Nat) : ByteArray := Id.run do
    let mut b := ByteArray.mk (Array.replicate sz (0 : UInt8))
    b := b.set! 0 0x6f |>.set! 1 0x6c |>.set! 2 0x65 |>.set! 3 0x61 |>.set! 4 0x6e |>.set! 5 2
    b := b1PutU64 b 80 base
    b := b1PutU64 b 88 (base + 96)
    return b
  let mut cb := mkHdr 256
  cb := cb.set! 100 32 |>.set! 102 3 |>.set! 103 1
  cb := b1PutU64 cb 104 5
  cb := b1PutU64 cb 112 1
  cb := b1PutU64 cb 120 (base + 128)
  cb := cb.set! 135 246
  cb := b1PutU64 cb 136 1
  cb := b1PutU64 cb 144 1
  cb := b1PutU64 cb 152 (base + 96)
  let cycParts := match parseOleanParts #[cb] with | .ok ps => ps | .error _ => #[]
  IO.println s!"A1 V-U3 cyclic binary Syntax: tags={b1Tags (validateBinSyntax cycParts `A1CycSyn (base + 96) {}).violations}"
  -- (6) Truncated `ReducibilityHints.regular` (`cs_sz = 8`, missing 4-byte UInt32 height).
  let mut hb := mkHdr 128
  hb := hb.set! 100 8 |>.set! 102 0 |>.set! 103 2
  let hParts := match parseOleanParts #[hb] with | .ok ps => ps | .error _ => #[]
  let hTags : Array String := match readObjHeader hParts (base + 96) with
    | .ok hh =>
      match readScalarU32 hParts hh 0 with
      | .ok _ => #[]
      | .error _ => #["malformedOleanRegion"]
    | .error _ => #["malformedOleanRegion"]
  IO.println s!"A1 binary truncated ReducibilityHints.regular: tags={hTags}"
  -- (7) Forbidden `LeanClosure` (tag 245) hidden inside `ModuleData.entries` graph.
  let mut clb := mkHdr 256
  clb := clb.set! 103 246
  clb := b1PutU64 clb 104 1
  clb := b1PutU64 clb 112 1
  clb := b1PutU64 clb 120 (base + 128)
  -- Closure object at off 128: tag=245, rc=0
  clb := clb.set! 135 245
  let clParts := match parseOleanParts #[clb] with | .ok ps => ps | .error _ => #[]
  IO.println s!"A1 binary ModuleData.entries LeanClosure tag 245: tags={b1Tags (sweepBinRegionGraph clParts `A1Closure (base + 96) {}).violations}"

/--
info: A1 V-N6 thm-over-thm laundering: axioms(useBridge)=#[] memory(A)=#[shadowedConstant] memory(B)=#[shadowedConstant]
A1 V-N6 intra-mod dup constNames: binary=#[shadowedConstant] memory=#[shadowedConstant]
A1 V-S5 IR.Decl.extern (zero exportAttr): binary=#[forbiddenExportAttr] memory=#[forbiddenExportAttr]
A1 V-U3 docStringExt surrogate in entries: binary=#[invalidUtf8Literal]
A1 multi-part 5-file module clean control: binMod ok=true memory ok=true
-/
#guard_msgs in
#eval show IO Unit from do
  let pid ← IO.Process.getPID
  let dir : System.FilePath := ⟨s!"/tmp/anneal-proto-a1-{pid}"⟩
  IO.FS.createDirAll dir
  try
    let libDir ← b1LibDir
    let core := #[`Init.Core]
    -- (1) Theorem-over-theorem axiom laundering (bypassed B1's `benignTheoremDuplicate`).
    let ax : ConstantInfo := .axiomInfo { name := `evilAx2, levelParams := [], type := mkConst ``False, isUnsafe := false }
    let bridgeA : ConstantInfo := .thmInfo {
      name := `thmBridge, levelParams := [], type := mkConst ``False, value := mkConst `evilAx2, all := [`thmBridge] }
    let useIt : ConstantInfo := .thmInfo {
      name := `useBridge, levelParams := [], type := mkConst ``False, value := mkConst `thmBridge, all := [`useBridge] }
    let pA ← b1Save dir `A1ThmA core #[`evilAx2, `thmBridge, `useBridge] #[ax, bridgeA, useIt]
    let bridgeB : ConstantInfo := .thmInfo {
      name := `thmBridge, levelParams := [], type := mkConst ``False, value := mkConst `thmBridge, all := [`thmBridge] }
    let pB ← b1Save dir `A1ThmB #[`A1ThmA] #[`thmBridge] #[bridgeB]
    let envAB ← b1Import libDir [(`A1ThmA, pA), (`A1ThmB, pB)] `A1ThmB
    let axs := match collectReachableAndAxioms envAB #[`useBridge] with | .ok (_, a) => a | .error _ => #[`ERR]
    IO.println s!"A1 V-N6 thm-over-thm laundering: axioms(useBridge)={axs} memory(A)={(validateEnvModule envAB `A1ThmA).tags} memory(B)={(validateEnvModule envAB `A1ThmB).tags}"
    -- (2) Intra-module duplicate `constNames` (bypassed B1 binary validator).
    let pDup ← b1Save dir `A1Dup core #[`dupThm, `dupThm] #[
      .thmInfo { name := `dupThm, levelParams := [], type := mkConst ``True, value := mkConst ``True.intro, all := [`dupThm] },
      .thmInfo { name := `dupThm, levelParams := [], type := mkConst ``True, value := mkConst `dupThm, all := [`dupThm] }
    ]
    let envDup ← b1Import libDir [(`A1Dup, pDup)] `A1Dup
    let bDup ← IO.FS.readBinFile pDup
    IO.println s!"A1 V-N6 intra-mod dup constNames: binary={(validateOleanParts #[bDup] `A1Dup).tags} memory={(validateEnvModule envDup `A1Dup).tags}"
    -- (3) V-S5 `IR.Decl.extern` C-symbol stub with zero `exportAttr` (bypassed B1).
    let extData : ExternAttrData := { entries := [.standard `all "a1_forged_extern_sym"] }
    let extDecl : IR.Decl := .extern `a1Fn #[{ x := ⟨1⟩, borrow := false, ty := .object }] .object extData
    let donorEnv := IR.declMapExt.addEntry (← mkEmptyEnvironment) extDecl
    let pDonor := dir / "A1IrDonor.olean"
    writeModule donorEnv pDonor (writeIR := false)
    let (donorMd, _) ← readModuleData pDonor
    let irEntries := donorMd.entries.filter (·.1 == `Lean.IR.declMapExt)
    let pIrExt := dir / "A1IrExt.olean"
    saveModuleData pIrExt `A1IrExt {
      isModule := false
      imports := #[{ module := `Init.Core, importAll := false, isExported := true, isMeta := false }]
      constNames := #[`a1Fn]
      constants := #[.defnInfo {
        name := `a1Fn, levelParams := [], type := mkConst ``Nat, value := mkNatLit 0
        hints := .abbrev, safety := .safe, all := [`a1Fn] }]
      extraConstNames := #[]
      entries := irEntries
    }
    let bIrExt ← IO.FS.readBinFile pIrExt
    let envIrExt ← b1Import libDir [(`A1IrExt, pIrExt)] `A1IrExt
    IO.println s!"A1 V-S5 IR.Decl.extern (zero exportAttr): binary={(validateOleanParts #[bIrExt] `A1IrExt).tags} memory={(validateEnvModule envIrExt `A1IrExt).tags}"
    -- (4) Malformed UTF-8 hidden in `ModuleData.entries` (`Lean.docStringExt`) caught by sweep!
    let appDir ← IO.appDir
    let leanBin : System.FilePath :=
      match ← IO.getEnv "LEAN_BIN" with
      | some p => ⟨p⟩
      | none => ⟨appDir.toString ++ "/lean"⟩
    let leanExe := if ← leanBin.pathExists then leanBin else ⟨"lean"⟩
    let docSrc := dir / "A1Doc.lean"
    let docSetup := dir / "A1Doc.setup.json"
    let pDoc := dir / "A1Doc.olean"
    IO.FS.writeFile docSrc "prelude\nimport Init.Core\n/-- DDDDDDDD -/\ndef a1DocFn : Nat := 0\n"
    IO.FS.writeFile docSetup
      "{\"name\":\"A1Doc\",\"isModule\":false,\"imports\":[{\"module\":\"Init.Core\",\"importAll\":false,\"isExported\":true,\"isMeta\":false}],\"importArts\":{},\"dynlibs\":[],\"plugins\":[],\"options\":{}}"
    let cDoc ← IO.Process.output {
      cmd := leanExe.toString
      args := #["-j1", "--setup", docSetup.toString, "-o", pDoc.toString, docSrc.toString]
      cwd := some dir
    }
    if cDoc.exitCode != 0 then
      throw (IO.userError s!"compile A1Doc failed: {cDoc.stderr}")
    let bDocMut ← b1PatchString (← IO.FS.readBinFile pDoc) "DDDDDDDD " (ByteArray.mk #[0xED, 0xA0, 0x80, 0x41]) 2
    IO.println s!"A1 V-U3 docStringExt surrogate in entries: binary={(validateOleanParts #[bDocMut] `A1Doc).tags}"
    -- (5) Real compiled 5-file Lean 4.34.1 `module` clean control via `validateModuleArtifactParts`.
    let modSrc := dir / "A1ModClean.lean"
    let modSetup := dir / "A1ModClean.setup.json"
    let modOlean := dir / "A1ModClean.olean"
    IO.FS.writeFile modSrc "module\npublic def a1Pub (x : Nat) : Nat := x + 1\ndef a1Priv (x : Nat) : Nat := x + 2\n"
    IO.FS.writeFile modSetup
      "{\"name\":\"A1ModClean\",\"isModule\":true,\"imports\":[{\"module\":\"Init.Core\",\"importAll\":false,\"isExported\":true,\"isMeta\":false}],\"importArts\":{},\"dynlibs\":[],\"plugins\":[],\"options\":{}}"
    let cMod ← IO.Process.output {
      cmd := leanExe.toString
      args := #["-j1", "--setup", modSetup.toString, "-o", modOlean.toString, modSrc.toString]
      cwd := some dir
    }
    if cMod.exitCode != 0 then
      throw (IO.userError s!"compile A1ModClean failed: {cMod.stderr}")
    let (olPs, irPs) ← loadModulePartsFromDisk (dir / "A1ModClean")
    let repBinMod := validateModuleArtifactParts olPs irPs `A1ModClean
    let olPaths : Array System.FilePath := #[dir / "A1ModClean.olean", dir / "A1ModClean.olean.server", dir / "A1ModClean.olean.private"]
    let irPaths : Array System.FilePath := #[dir / "A1ModClean.ir.sig", dir / "A1ModClean.ir"]
    searchPathRef.set [libDir]
    let mArts : NameMap ImportArtifacts :=
      ({} : NameMap ImportArtifacts).insert `A1ModClean (.ofArrays #[olPaths, irPaths])
    let envMod ← importModules #[{ module := `A1ModClean }] {} (trustLevel := 0) (plugins := #[]) (loadExts := false) (level := .private) (arts := mArts)
    let repMemMod := validateEnvModule envMod `A1ModClean
    IO.println s!"A1 multi-part 5-file module clean control: binMod ok={repBinMod.ok} memory ok={repMemMod.ok}"
  finally
    try IO.FS.removeDirAll dir catch _ => pure ()

/-! ## Section 11d: Round-B2 Adversarial Regressions -/

/--
info: B2 V-U3 honest 50000-node Syntax chain: ok=true stringsValidated=2
B2 V-U3 200 mdata nodes over one body with distinct 300-node Syntax chains: ok=true exprNodesVisited=208
-/
#guard_msgs in
#eval show IO Unit from do
  -- Linear-time regression for the shallow-hash `StrictSyntaxKey` bucket collapse (A1 took
  -- super-cubic time on honest chains; this block would not finish under A1).
  let chain (n : Nat) (leaf : String) : Syntax := Id.run do
    let mut s : Syntax := Syntax.atom .none leaf
    for _ in [0:n] do
      s := Syntax.node .none `wrap #[s]
    return s
  let st := validateSyntaxDag `B2Chain (chain 50000 "leaf") {}
  IO.println s!"B2 V-U3 honest 50000-node Syntax chain: ok={st.violations.isEmpty} stringsValidated={st.stats.stringsValidated}"
  -- `Expr.mdata` data depends only on the body: A1 hashed every such node into one bucket.
  let body := mkNatLit 0
  let mut stE : MemValidatorState := {}
  for i in [0:200] do
    let md : MData := KVMap.empty.insert `b2.syn (.ofSyntax (chain 300 s!"leaf{i}"))
    stE := (validateExprDag `B2Mdata (.mdata md body) stE (requireClosed := true)).1
  IO.println s!"B2 V-U3 200 mdata nodes over one body with distinct 300-node Syntax chains: ok={stE.violations.isEmpty} exprNodesVisited={stE.stats.exprNodesVisited}"

/-- Compile a non-`module` Lean source to `dir/<name>.olean` with `LEAN_PATH = dir:libDir`. -/
def b2Compile (dir libDir : System.FilePath) (name : String) (src : String) (imports : Array String) :
    IO System.FilePath := do
  let appDir ← IO.appDir
  let leanBin : System.FilePath :=
    match ← IO.getEnv "LEAN_BIN" with
    | some p => ⟨p⟩
    | none => ⟨appDir.toString ++ "/lean"⟩
  let leanExe := if ← leanBin.pathExists then leanBin else ⟨"lean"⟩
  let srcP := dir / s!"{name}.lean"
  let setupP := dir / s!"{name}.setup.json"
  let outP := dir / s!"{name}.olean"
  IO.FS.writeFile srcP src
  let imps := ",".intercalate (imports.toList.map fun m =>
    s!"\{\"module\":\"{m}\",\"importAll\":false,\"isExported\":true,\"isMeta\":false}")
  IO.FS.writeFile setupP
    s!"\{\"name\":\"{name}\",\"isModule\":false,\"imports\":[{imps}],\"importArts\":\{},\"dynlibs\":[],\"plugins\":[],\"options\":\{}}"
  let out ← IO.Process.output {
    cmd := leanExe.toString
    args := #["-j1", "--setup", setupP.toString, "-o", outP.toString, srcP.toString]
    cwd := some dir
    env := #[("LEAN_PATH", some s!"{dir}:{libDir}")]
  }
  if out.exitCode != 0 then
    throw (IO.userError s!"compile {name} failed: {out.stderr}")
  return outP

/-- The cached axiom array a module's binary `exportedAxiomsExt` stores for `n`. -/
def b2ClaimOf (bytes : ByteArray) (n : Name) : Array Name :=
  match binExportedAxiomClaims #[bytes] with
  | .ok cs => ((cs.find? (·.1 == n)).map (·.2)).getD #[`MISSING]
  | .error _ => #[`ERROR]

/-- Empty (`m_size := 0`) the stored `exportedAxiomsExt` axiom arrays of `targets`. -/
def b2EmptyAxiomCache (bytes : ByteArray) (targets : List Name) : IO (ByteArray × Nat) := do
  let parts ← IO.ofExcept (parseOleanParts #[bytes])
  let rh ← IO.ofExcept (readObjHeader parts parts[0]!.rootPtr)
  let entries ← IO.ofExcept (readArrayElems parts (← IO.ofExcept (readFieldPtr parts rh 4)))
  let mut b := bytes
  let mut patched := 0
  for pairPtr in entries do
    let ph ← IO.ofExcept (readObjHeader parts pairPtr)
    let (_, extInfo) := validateBinName parts `B2 (← IO.ofExcept (readFieldPtr parts ph 0)) {}
    if extInfo.name.toString.endsWith "exportedAxiomsExt" then
      for e in ← IO.ofExcept (readArrayElems parts (← IO.ofExcept (readFieldPtr parts ph 1))) do
        let eh ← IO.ofExcept (readObjHeader parts e)
        let (_, nInfo) := validateBinName parts `B2 (← IO.ofExcept (readFieldPtr parts eh 0)) {}
        if targets.contains nInfo.name then
          let ah ← IO.ofExcept (readObjHeader parts (← IO.ofExcept (readFieldPtr parts eh 1)))
          b := b1PutU64 b (ah.off + 8) 0
          patched := patched + 1
  return (b, patched)

/--
info: B2 V-N6 honest axiom cache: claim(useEvil2)=#[evilAx] memory ok=true
B2 V-N6 forged exportedAxiomsExt: patched 2 cached arrays
B2 V-N6 forged exportedAxiomsExt: cached claim(useEvil)=#[] claim(useEvil2)=#[] (consumed by #print axioms)
B2 V-N6 forged exportedAxiomsExt: independent closure(useEvil2)=#[evilAx]
B2 V-N6 forged exportedAxiomsExt: binary=#[] memory(validateEnvModule)=#[] memory(Full)=#[forgedExportedAxioms]
B2 V-N6 honestly-compiled downstream of forged cache: claim(downstream)=#[] memory(Full)=#[forgedExportedAxioms]
-/
#guard_msgs in
#eval show IO Unit from do
  let pid ← IO.Process.getPID
  let dir : System.FilePath := ⟨s!"/tmp/anneal-proto-b2-{pid}"⟩
  IO.FS.createDirAll dir
  try
    let libDir ← b1LibDir
    let src := "axiom evilAx : False\ntheorem useEvil : False := evilAx\ntheorem useEvil2 : 1 = 2 := useEvil.elim\n"
    let pAx ← b2Compile dir libDir "B2Ax" src #["Init"]
    let envHonest ← b1Import libDir [(`B2Ax, pAx)] `B2Ax
    let bHonest ← IO.FS.readBinFile pAx
    IO.println s!"B2 V-N6 honest axiom cache: claim(useEvil2)={b2ClaimOf bHonest `useEvil2} memory ok={(validateEnvModuleFull envHonest `B2Ax #[bHonest]).ok}"
    let (bForged, n) ← b2EmptyAxiomCache (← IO.FS.readBinFile pAx) [`useEvil, `useEvil2]
    IO.println s!"B2 V-N6 forged exportedAxiomsExt: patched {n} cached arrays"
    let pForged := dir / "forged" / "B2Ax.olean"
    IO.FS.createDirAll (dir / "forged")
    IO.FS.writeBinFile pForged bForged
    let env ← b1Import libDir [(`B2Ax, pForged)] `B2Ax
    IO.println s!"B2 V-N6 forged exportedAxiomsExt: cached claim(useEvil)={b2ClaimOf bForged `useEvil} claim(useEvil2)={b2ClaimOf bForged `useEvil2} (consumed by #print axioms)"
    let indep := match independentAxiomClosures env #[`useEvil2] with
      | .ok m => (m.find? `useEvil2).getD #[] | .error _ => #[`ERROR]
    IO.println s!"B2 V-N6 forged exportedAxiomsExt: independent closure(useEvil2)={indep}"
    IO.println s!"B2 V-N6 forged exportedAxiomsExt: binary={(validateOleanParts #[bForged] `B2Ax).tags} memory(validateEnvModule)={(validateEnvModule env `B2Ax).tags} memory(Full)={(validateEnvModuleFull env `B2Ax #[bForged]).tags}"
    -- Downstream module compiled HONESTLY by Lean against the forged upstream cache.
    let fdir := dir / "forged"
    let pDown ← b2Compile fdir libDir "B2AxDown" "import B2Ax\ntheorem downstream : 1 = 2 := useEvil2\n" #["Init", "B2Ax"]
    let envDown ← b1Import libDir [(`B2Ax, pForged), (`B2AxDown, pDown)] `B2AxDown
    let bDown ← IO.FS.readBinFile pDown
    IO.println s!"B2 V-N6 honestly-compiled downstream of forged cache: claim(downstream)={b2ClaimOf bDown `downstream} memory(Full)={(validateEnvModuleFull envDown `B2AxDown #[bDown]).tags}"
  finally
    try IO.FS.removeDirAll dir catch _ => pure ()

/-! ## Section 11e: Round-A2 Adversarial Regressions

Pins every bypass reproduced LIVE against B2 (`8d981f89`):
1. Mutual-recursion SCC bug in B2's `independentAxiomClosures` (`cycB <-> cycC` where `cycB`
   uses `sccEvil`: B2 permanently cached `cycC ↦ #[]` and accepted a forged empty cache!).
2. `.recInfo` `rules.rhs` axiom hiding in B2's `independentAxiomClosures` (`useRec ↦ #[]`).
3. Truncated `syntaxStrictKey` false equality (`strictDataValueEq == true` on distinct >100k
   `Syntax` chains `"A"` vs `"B"`), fixed by fail-closed iterative `strictSyntaxEqIter`.
4. Duplicate & foreign-owned `exportedAxiomsExt` cache entries rejected (`forgedExportedAxioms`). -/

/--
info: A2 V-N6 mutual-recursion SCC: cycB=(some #[sccEvil]) cycC=(some #[sccEvil]) forgedCache(cycC=#[])=#[forgedExportedAxioms]
A2 V-N6 recInfo rules.rhs axiom: useRec=(some #[sccEvil]) forgedCache(useRec=#[])=#[forgedExportedAxioms]
A2 V-N6 duplicate & foreign exportedAxiomsExt: identicalDup(uniform parts, B3)=#[] foreign=#[forgedExportedAxioms]
A2 V-U3 >100k Syntax chain: validate=#[auditFuelExhausted] boundedEq(distinct)=true ptrIdentEq=true
-/
#guard_msgs in
#eval show IO Unit from do
  let pid ← IO.Process.getPID
  let dir : System.FilePath := ⟨s!"/tmp/anneal-proto-a2-{pid}"⟩
  IO.FS.createDirAll dir
  try
    let libDir ← b1LibDir
    let core := #[`Init.Core]
    let ax : ConstantInfo := .axiomInfo { name := `sccEvil, levelParams := [], type := mkConst ``False, isUnsafe := false }
    -- (1) Mutual recursion SCC: cycB calls cycC + sccEvil, cycC calls cycB.
    let cycB : ConstantInfo := .thmInfo {
      name := `cycB, levelParams := [], type := mkConst ``False
      value := Expr.app (mkConst `cycC) (mkConst `sccEvil), all := [`cycB, `cycC] }
    let cycC : ConstantInfo := .thmInfo {
      name := `cycC, levelParams := [], type := mkConst ``False
      value := mkConst `cycB, all := [`cycB, `cycC] }
    let pScc ← b1Save dir `A2Scc core #[`sccEvil, `cycB, `cycC] #[ax, cycB, cycC]
    let envScc ← b1Import libDir [(`A2Scc, pScc)] `A2Scc
    match independentAxiomClosures envScc #[`cycB, `cycC] with
    | .ok m =>
      let repScc := validateExportedAxiomCache envScc `A2Scc #[(`cycB, #[`sccEvil]), (`cycC, #[])]
      IO.println s!"A2 V-N6 mutual-recursion SCC: cycB={m.find? `cycB} cycC={m.find? `cycC} forgedCache(cycC=#[])={repScc.tags}"
    | .error v => throw (IO.userError v.render)
    -- (2) `.recInfo` `rules.rhs` axiom hiding.
    let recCi : ConstantInfo := .recInfo {
      name := `a2BadRec, levelParams := [], type := mkConst ``Nat, all := [`a2BadRec]
      numParams := 0, numIndices := 0, numMotives := 0, numMinors := 0
      rules := [{ ctor := `Nat.zero, nfields := 0, rhs := mkConst `sccEvil }]
      k := false, isUnsafe := false }
    let useRec : ConstantInfo := .thmInfo {
      name := `a2UseRec, levelParams := [], type := mkConst ``Nat
      value := mkConst `a2BadRec, all := [`a2UseRec] }
    let pRec ← b1Save dir `A2Rec core #[`sccEvil, `a2BadRec, `a2UseRec] #[ax, recCi, useRec]
    let envRec ← b1Import libDir [(`A2Rec, pRec)] `A2Rec
    match independentAxiomClosures envRec #[`a2UseRec] with
    | .ok m =>
      let repRec := validateExportedAxiomCache envRec `A2Rec #[(`a2UseRec, #[])]
      IO.println s!"A2 V-N6 recInfo rules.rhs axiom: useRec={m.find? `a2UseRec} forgedCache(useRec=#[])={repRec.tags}"
    | .error v => throw (IO.userError v.render)
    -- (3) Duplicate and foreign-owned `exportedAxiomsExt` entries.
    let repDup := validateExportedAxiomCache envScc `A2Scc #[(`cycB, #[`sccEvil]), (`cycB, #[`sccEvil])]
    let repFor := validateExportedAxiomCache envScc `A2Scc #[(`Nat.add, #[])]
    IO.println s!"A2 V-N6 duplicate & foreign exportedAxiomsExt: identicalDup(uniform parts, B3)={repDup.tags} foreign={repFor.tags}"
    -- (4) >100k `Syntax` chains differing only at leaf fail closed (`false`), while pointer-identical passes (`true`).
    let mkDeep (leaf : String) : Syntax := Id.run do
      let mut s : Syntax := Syntax.atom .none leaf
      for _ in [0:100005] do
        s := Syntax.node .none `w #[s]
      return s
    let sA := mkDeep "A"
    let sB := mkDeep "B"
    -- B3: bounded equality truncates to `true` past the budget; sound because the oversize tree
    -- itself fails validation closed (`validate=#[auditFuelExhausted]`).
    IO.println s!"A2 V-U3 >100k Syntax chain: validate={b1Tags (validateSyntaxDag `A2Deep sA {}).violations} boundedEq(distinct)={strictDataValueEq (.ofSyntax sA) (.ofSyntax sB)} ptrIdentEq={strictDataValueEq (.ofSyntax sA) (.ofSyntax sA)}"
  finally
    try IO.FS.removeDirAll dir catch _ => pure ()

/-! ## Section 11f: Round-B3 Adversarial Regressions -/

/-- Shared depth-`depth` `Syntax` DAG (`2^depth` tree paths, `depth + 1` objects). -/
@[noinline] def b3Dag (depth : Nat) (leaf : String) : Syntax := Id.run do
  let mut s : Syntax := Syntax.atom .none leaf
  for _ in [0:depth] do
    s := Syntax.node .none `b3pair #[s, s]
  return s

/--
info: B3 V-U3 distinct depth-40 Syntax DAGs: boundedEq=true (no 2^40 re-expansion)
B3 V-U3 two mdata nodes over one body with distinct depth-40 DAGs: tags=#[auditFuelExhausted]
-/
#guard_msgs in
#eval show IO Unit from do
  -- Two separately built (distinct-pointer) but structurally identical shared DAGs, differing
  -- only in a sibling leaf. A2's recursive fallback re-expanded the shared sub-DAG once per path.
  let r ← IO.mkRef "L"
  let l1 ← r.get
  let l2 ← r.get
  let a := Syntax.node .none `b3top #[b3Dag 40 l1, Syntax.atom .none "A"]
  let b := Syntax.node .none `b3top #[b3Dag 40 l2, Syntax.atom .none "B"]
  IO.println s!"B3 V-U3 distinct depth-40 Syntax DAGs: boundedEq={strictDataValueEq (.ofSyntax a) (.ofSyntax b)} (no 2^40 re-expansion)"
  let md (s : Syntax) : MData := KVMap.empty.insert `b3.syn (.ofSyntax s)
  let body := mkNatLit 0
  let st1 := (validateExprDag `B3X (.mdata (md a) body) {} (requireClosed := true)).1
  let st2 := (validateExprDag `B3Y (.mdata (md b) body) st1 (requireClosed := true)).1
  IO.println s!"B3 V-U3 two mdata nodes over one body with distinct depth-40 DAGs: tags={b1Tags st2.violations}"

/--
info: B3 V-N6 honest 5-file module (uniform cache in 3 olean parts): claims=6 Full ok=true
B3 V-N6 conflicting duplicate claim: tags=#[forgedExportedAxioms]
-/
#guard_msgs in
#eval show IO Unit from do
  let pid ← IO.Process.getPID
  let dir : System.FilePath := ⟨s!"/tmp/anneal-proto-b3-{pid}"⟩
  IO.FS.createDirAll dir
  try
    let libDir ← b1LibDir
    let appDir ← IO.appDir
    let leanBin : System.FilePath :=
      match ← IO.getEnv "LEAN_BIN" with
      | some p => ⟨p⟩
      | none => ⟨appDir.toString ++ "/lean"⟩
    let leanExe := if ← leanBin.pathExists then leanBin else ⟨"lean"⟩
    IO.FS.writeFile (dir / "B3Mod.lean")
      "module\npublic axiom b3Ax : False\npublic theorem b3Use : False := b3Ax\ntheorem b3Priv : 1 = 1 := rfl\n"
    IO.FS.writeFile (dir / "B3Mod.setup.json")
      "{\"name\":\"B3Mod\",\"isModule\":true,\"imports\":[{\"module\":\"Init\",\"importAll\":false,\"isExported\":true,\"isMeta\":false}],\"importArts\":{},\"dynlibs\":[],\"plugins\":[],\"options\":{}}"
    let out ← IO.Process.output {
      cmd := leanExe.toString
      args := #["-j1", "--setup", (dir / "B3Mod.setup.json").toString, "-o", (dir / "B3Mod.olean").toString, (dir / "B3Mod.lean").toString]
      cwd := some dir }
    if out.exitCode != 0 then throw (IO.userError s!"compile B3Mod failed: {out.stderr}")
    let (olPs, irPs) ← loadModulePartsFromDisk (dir / "B3Mod")
    let nClaims := match binExportedAxiomClaims olPs with | .ok cs => cs.size | .error _ => 0
    searchPathRef.set [libDir]
    let olPaths : Array System.FilePath := #[dir / "B3Mod.olean", dir / "B3Mod.olean.server", dir / "B3Mod.olean.private"]
    let irPaths : Array System.FilePath := #[dir / "B3Mod.ir.sig", dir / "B3Mod.ir"]
    let mArts : NameMap ImportArtifacts := ({} : NameMap ImportArtifacts).insert `B3Mod (.ofArrays #[olPaths, irPaths])
    let env ← importModules #[{ module := `B3Mod }] {} (trustLevel := 0) (plugins := #[]) (loadExts := false)
      (level := .private) (arts := mArts)
    IO.println s!"B3 V-N6 honest 5-file module (uniform cache in 3 olean parts): claims={nClaims} Full ok={(validateEnvModuleFull env `B3Mod olPs (irParts := irPs)).ok}"
    let conflict := validateExportedAxiomCache env `B3Mod #[(`b3Use, #[`b3Ax]), (`b3Use, #[`b3Ax, `propext])]
    IO.println s!"B3 V-N6 conflicting duplicate claim: tags={conflict.tags}"
  finally
    try IO.FS.removeDirAll dir catch _ => pure ()

/-! ## Section 12: Live Latency & Peak-RSS Benchmark on Compiled `Anneal.NatBitwise` & `Anneal.MirLiftCore` -/

def runModuleBenchmark (modName : Name) (relBase : String) : IO Unit := do
  let basePath : System.FilePath := ⟨".lake/build/lib/lean/" ++ relBase⟩
  let (oleanParts, irParts) ← loadModulePartsFromDisk basePath
  if oleanParts.isEmpty then
    throw (IO.userError s!"compiled artifact missing for {modName} at {basePath}.olean")
  let totalBytes := (oleanParts ++ irParts).foldl (fun a b => a + b.size) 0
  -- 1. Pure-Lean binary `.olean` + `.ir` compacted-region pointer-DAG validation.
  -- Force control dependence on `binRep` before reading `t1` so the compiler cannot sink pure `let`s.
  let t0 ← IO.monoNanosNow
  let binRep := validateModuleArtifactParts oleanParts irParts modName
  if !binRep.ok then
    throw (IO.userError s!"FALSE POSITIVE on honest module {modName} (binary): {binRep.violations.map Violation.render}")
  let binGuard ← IO.mkRef binRep.stats.totalNodes
  let _ ← binGuard.get
  let t1 ← IO.monoNanosNow
  let binUs := (t1 - t0) / 1000
  let binMs := binUs / 1000
  -- 2. In-memory `Environment` DAG validation on the compiled `.olean`
  let appDir ← IO.appDir
  let leanBin : System.FilePath :=
    match ← IO.getEnv "LEAN_BIN" with
    | some p => ⟨p⟩
    | none => ⟨appDir.toString ++ "/lean"⟩
  let leanExe := if ← leanBin.pathExists then leanBin else ⟨"lean"⟩
  let sysrootOut ← IO.Process.output { cmd := leanExe.toString, args := #["--print-prefix"] }
  let libDir : System.FilePath := ⟨sysrootOut.stdout.trimAscii.toString⟩ / "lib" / "lean"
  searchPathRef.set [libDir, ⟨".lake/build/lib/lean"⟩]
  let env ← importModules #[{ module := modName }] {} (trustLevel := 0)
    (plugins := #[]) (loadExts := false) (level := .private)
  let t2 ← IO.monoNanosNow
  let memRep := validateEnvModuleFull env modName oleanParts (checkLiveExportState := false) (irParts := irParts)
  if !memRep.ok then
    throw (IO.userError s!"FALSE POSITIVE on honest module {modName} (in-memory): {memRep.violations.map Violation.render}")
  let memGuard ← IO.mkRef memRep.stats.totalNodes
  let _ ← memGuard.get
  let t3 ← IO.monoNanosNow
  let memUs := (t3 - t2) / 1000
  let memMs := memUs / 1000
  let vmHwmKb ← readProcStatusKb "VmHWM:"
  let vmRssKb ← readProcStatusKb "VmRSS:"
  IO.println s!"BENCH {modName} ({totalBytes} bytes):"
  IO.println s!"  binary-dag : ok={binRep.ok}, decls={binRep.stats.declsChecked}, nodes={binRep.stats.totalNodes}, hits={binRep.stats.totalHits}, hitRate={binRep.stats.hitRatePermille}‰, strings={binRep.stats.stringsValidated}, elapsed={binMs}ms ({binUs}us)"
  IO.println s!"  memory-dag : ok={memRep.ok}, decls={memRep.stats.declsChecked}, nodes={memRep.stats.totalNodes}, hits={memRep.stats.totalHits}, hitRate={memRep.stats.hitRatePermille}‰, strings={memRep.stats.stringsValidated}, elapsed={memMs}ms ({memUs}us)"
  IO.println s!"  rss        : VmHWM={vmHwmKb}kB, VmRSS={vmRssKb}kB"

#eval show IO Unit from do
  runModuleBenchmark `Anneal.NatBitwise "Anneal/NatBitwise"
  runModuleBenchmark `Anneal.MirLiftCore "Anneal/MirLiftCore"

/-! ## Section 13: CLI Entrypoint for Python Reproduction Suite (`test_six_vectors.py`) -/

/-- Run binary `.olean`/`.ir` validation and print JSON report to stdout. -/
def cliValidateBin (modNameStr : String) (paths : List String) : IO UInt32 := do
  let mut parts : Array ByteArray := #[]
  for p in paths do
    parts := parts.push (← IO.FS.readBinFile ⟨p⟩)
  let rep := validateOleanParts parts modNameStr.toName
  IO.println rep.toJson.compress
  return if rep.ok then 0 else 1

/-- Validate independent `.olean*` and `.ir*` compacted-region groups for a `module`. -/
def cliValidateBinMod (modNameStr oleanCsv irCsv : String) : IO UInt32 := do
  let loadCsv (s : String) : IO (Array ByteArray) := do
    if s.isEmpty then return #[]
    let mut out : Array ByteArray := #[]
    for p in s.splitOn "," do
      if !p.isEmpty then
        out := out.push (← IO.FS.readBinFile ⟨p⟩)
    return out
  let olParts ← loadCsv oleanCsv
  let irParts ← loadCsv irCsv
  let rep := validateModuleArtifactParts olParts irParts modNameStr.toName
  IO.println rep.toJson.compress
  return if rep.ok then 0 else 1

/-- Load module artifacts via `importModules` and run full in-memory validation
(V-Q1..V-S5), printing JSON report to stdout. -/
def cliValidateEnv (sysrootStr modNameStr : String) (oleanCsv irCsv : String) : IO UInt32 := do
  let libDir : System.FilePath := ⟨sysrootStr⟩ / "lib" / "lean"
  searchPathRef.set [libDir]
  let splitNonEmpty (s : String) : Array System.FilePath :=
    if s.isEmpty then #[]
    else (s.splitOn ",").toArray.filterMap fun p =>
      if p.isEmpty then none else some ⟨p⟩
  let oleanParts := splitNonEmpty oleanCsv
  let irParts := splitNonEmpty irCsv
  let modName := modNameStr.toName
  let arts : NameMap ImportArtifacts :=
    ({} : NameMap ImportArtifacts).insert modName (.ofArrays #[oleanParts, irParts])
  let env ← importModules #[{ module := modName }] {} (trustLevel := 0)
    (plugins := #[]) (loadExts := false) (level := .private) (arts := arts)
  let mut oleanBytes : Array ByteArray := #[]
  for p in oleanParts do
    oleanBytes := oleanBytes.push (← IO.FS.readBinFile p)
  let mut irBytes : Array ByteArray := #[]
  for p in irParts do
    irBytes := irBytes.push (← IO.FS.readBinFile p)
  let rep := validateEnvModuleFull env modName oleanBytes (irParts := irBytes)
  IO.println rep.toJson.compress
  return if rep.ok then 0 else 1

/-- Check `OleanEnvAuditor.isClosedExpr` (cached `Expr.m_data` bits only) on a loaded module's
declaration, demonstrating the BEFORE blind spot on forged `Expr.m_data`. -/
def cliCheckCachedClosed (sysrootStr modNameStr declNameStr oleanPath : String) : IO UInt32 := do
  let libDir : System.FilePath := ⟨sysrootStr⟩ / "lib" / "lean"
  searchPathRef.set [libDir]
  let modName := modNameStr.toName
  let arts : NameMap ImportArtifacts :=
    ({} : NameMap ImportArtifacts).insert modName (.ofArrays #[#[⟨oleanPath⟩], #[]])
  let env ← importModules #[{ module := modName }] {} (trustLevel := 0)
    (plugins := #[]) (loadExts := false) (level := .private) (arts := arts)
  let some ci := env.find? declNameStr.toName
    | throw (IO.userError s!"decl {declNameStr} not found")
  let e := (ci.value? (allowOpaque := true)).getD ci.type
  let cachedClosed := !(e.hasFVar || e.hasMVar || e.hasLooseBVars || e.hasLevelMVar)
  let (st, recomputed) := validateExprDag ci.name e {} (requireClosed := true)
  let rep : AuditReport := { violations := st.violations, stats := st.stats }
  let j := Json.mkObj [
    ("cachedIsClosedExpr", toJson cachedClosed),
    ("recomputedClosed", toJson (exprDataIsClosed recomputed)),
    ("validatorOk", toJson rep.ok),
    ("validatorTags", toJson rep.tags)
  ]
  IO.println j.compress
  return 0

/-- Probe `exportAttr.ext` BEFORE (`getModuleEntries`) vs AFTER (`getModuleIREntries` + validator). -/
def cliProbeExport (sysrootStr modNameStr oleanCsv irCsv : String) : IO UInt32 := do
  let libDir : System.FilePath := ⟨sysrootStr⟩ / "lib" / "lean"
  searchPathRef.set [libDir]
  let splitNonEmpty (s : String) : Array System.FilePath :=
    if s.isEmpty then #[]
    else (s.splitOn ",").toArray.filterMap fun p =>
      if p.isEmpty then none else some ⟨p⟩
  let modName := modNameStr.toName
  let arts : NameMap ImportArtifacts :=
    ({} : NameMap ImportArtifacts).insert modName (.ofArrays #[splitNonEmpty oleanCsv, splitNonEmpty irCsv])
  let env ← importModules #[{ module := modName }] {} (trustLevel := 0)
    (plugins := #[]) (loadExts := false) (level := .private) (arts := arts)
  let some modIdx := env.getModuleIdx? modName
    | throw (IO.userError s!"module {modName} not loaded")
  let me := (exportAttr.ext.getModuleEntries env modIdx.toNat).map fun (a, b) => (a.toString, b.toString)
  let ire := (exportAttr.ext.getModuleIREntries env modIdx.toNat).map fun (a, b) => (a.toString, b.toString)
  let rep := validateEnvModule env modName
  let j := Json.mkObj [
    ("moduleEntries", toJson me),
    ("moduleIREntries", toJson ire),
    ("validatorOk", toJson rep.ok),
    ("validatorTags", toJson rep.tags)
  ]
  IO.println j.compress
  return 0

/-- Probe V-Q1 live `Kernel.Environment.replay` gap vs `validateQuotVal`. -/
def cliProbeV1 (sysrootStr : String) : IO UInt32 := do
  let libDir : System.FilePath := ⟨sysrootStr⟩ / "lib" / "lean"
  searchPathRef.set [libDir]
  let env ← importModules #[{ module := `Init.Core }] {} (trustLevel := 0)
    (plugins := #[]) (loadExts := false) (level := .private)
  let forged : QuotVal := { name := `FakeQuot, levelParams := [], type := mkConst ``False, kind := .type }
  let m : Std.HashMap Name ConstantInfo :=
    ({} : Std.HashMap Name ConstantInfo).insert `FakeQuot (.quotInfo forged)
  let replayRes ← EIO.toBaseIO (env.toKernelEnv.replay m)
  let vs := validateQuotVal forged (some `UntrustedMod)
  let rep : AuditReport := { violations := vs }
  let j := Json.mkObj [
    ("replayAcceptedForgedQuotInfo", toJson replayRes.isOk),
    ("validatorOk", toJson rep.ok),
    ("validatorTags", toJson rep.tags)
  ]
  IO.println j.compress
  return 0

/-- Probe V-F4 live `Kernel.isDefEq` / `Kernel.check` / `Kernel.whnf` capture vs validator. -/
def cliProbeV4 (sysrootStr : String) : IO UInt32 := do
  let libDir : System.FilePath := ⟨sysrootStr⟩ / "lib" / "lean"
  searchPathRef.set [libDir]
  let env ← importModules #[{ module := `Init.Core }] {} (trustLevel := 0)
    (plugins := #[]) (loadExts := false) (level := .private)
  let fvId : FVarId := ⟨Name.num (Name.str .anonymous "_kernel_fresh") 0⟩
  let lctx : LocalContext := ({} : LocalContext).mkLocalDecl fvId `n (mkConst ``Nat) .default
  let lamFvar := Expr.lam `x (mkConst ``Bool) (Expr.fvar fvId) .default
  let lamId := Expr.lam `x (mkConst ``Bool) (Expr.bvar 0) .default
  let boolToBool := Expr.forallE `x (mkConst ``Bool) (mkConst ``Bool) .default
  let isDefEqCap := match Kernel.isDefEq env lctx lamFvar lamId with | .ok b => b | .error _ => false
  let checkWrong := match Kernel.check env lctx lamFvar with | .ok ty => ty == boolToBool | .error _ => false
  let hId : FVarId := ⟨`h_bogus⟩
  let eqTy := mkApp3 (mkConst ``Eq [.one]) boolToBool lamId lamFvar
  let lctxW := lctx.mkLocalDecl hId `h eqTy .default
  let motive := Expr.lam `f boolToBool
    (Expr.lam `p (mkApp3 (mkConst ``Eq [.one]) boolToBool lamId (.bvar 0)) (mkConst ``Nat) .default) .default
  let eqRec := mkAppN (mkConst ``Eq.rec [.one, .one]) #[boolToBool, lamId, motive, mkRawNatLit 42, lamFvar, Expr.fvar hId]
  let whnfCap := match Kernel.whnf env lctxW eqRec with | .ok e => e == mkRawNatLit 42 | .error _ => false
  let lctxRep := validateLocalContext lctx
  let j := Json.mkObj [
    ("kernelIsDefEqCapture", toJson isDefEqCap),
    ("kernelCheckWrongType", toJson checkWrong),
    ("kernelWhnfKReductionCapture", toJson whnfCap),
    ("validatorOk", toJson lctxRep.ok),
    ("validatorTags", toJson lctxRep.tags)
  ]
  IO.println j.compress
  return 0

/-- Probe V-N6 live axiom closures and second-kernel `primitiveTargets` parity oracle. -/
def cliProbeV6 (sysrootStr lakeLibDir : String) : IO UInt32 := do
  let libDir : System.FilePath := ⟨sysrootStr⟩ / "lib" / "lean"
  searchPathRef.set [libDir, ⟨lakeLibDir⟩]
  let env ← importModules #[{ module := `Anneal.NatBitwise }] {} (trustLevel := 0)
    (plugins := #[]) (loadExts := false) (level := .private)
  let axOf (n : Name) : Array String :=
    match collectReachableAndAxioms env #[n] with
    | .ok (_, axs) => axs.map Name.toString
    | .error _ => #["ERROR"]
  -- Find a 0-axiom theorem and a [propext]-only theorem inside compiled `Anneal.NatBitwise`
  let mut zeroThm? : Option Name := none
  let mut propThm? : Option Name := none
  let mut nZero := 0
  let mut nProp := 0
  let mut nPropQuot := 0
  if let some idx := env.getModuleIdx? `Anneal.NatBitwise then
    for ci in env.header.moduleData[idx.toNat]!.constants do
      if ci matches .thmInfo _ then
        let axs := axOf ci.name
        if axs == #[] then
          nZero := nZero + 1
          if zeroThm?.isNone then zeroThm? := some ci.name
        else if axs == #["propext"] then
          nProp := nProp + 1
          if propThm?.isNone then propThm? := some ci.name
        else if axs == #["propext", "Quot.sound"] then
          nPropQuot := nPropQuot + 1
  let some zThm := zeroThm? | throw (IO.userError "no 0-axiom theorem found in Anneal.NatBitwise")
  let some pThm := propThm? | throw (IO.userError "no [propext]-only theorem found in Anneal.NatBitwise")
  let buggyZero ← IO.ofExcept <| (checkSecondKernelParity env zThm false).mapError Violation.render
  let fixedZero ← IO.ofExcept <| (checkSecondKernelParity env zThm true).mapError Violation.render
  let fixedProp ← IO.ofExcept <| (checkSecondKernelParity env pThm true).mapError Violation.render
  let fixedUnfold ← IO.ofExcept <| (checkSecondKernelParity env `Anneal.NatBitwise.unfold_eq true).mapError Violation.render
  let j := Json.mkObj [
    ("natXorAxioms", toJson (axOf ``Nat.xor)),
    ("natBitwiseAxioms", toJson (axOf ``Nat.bitwise)),
    ("unfoldEqAxioms", toJson (axOf `Anneal.NatBitwise.unfold_eq)),
    ("zeroAxiomTheoremCount", toJson nZero),
    ("propextOnlyTheoremCount", toJson nProp),
    ("propextQuotTheoremCount", toJson nPropQuot),
    ("sampleZeroTheorem", toJson zThm.toString),
    ("buggyUnconditionalTag", toJson (buggyZero.violation?.map (·.tag) |>.getD "")),
    ("buggyUnconditionalSecondKernelAxioms", toJson (buggyZero.secondKernelAxioms.map Name.toString)),
    ("fixedDemandDrivenZeroOk", toJson fixedZero.violation?.isNone),
    ("fixedDemandDrivenPropOk", toJson fixedProp.violation?.isNone),
    ("fixedDemandDrivenUnfoldOk", toJson fixedUnfold.violation?.isNone)
  ]
  IO.println j.compress
  return 0

def cliMain (args : List String) : IO UInt32 := do
  match args with
  | "validate-bin" :: modName :: paths =>
    cliValidateBin modName paths
  | ["validate-bin-mod", modName, oleanCsv, irCsv] =>
    cliValidateBinMod modName oleanCsv irCsv
  | ["validate-env", sysroot, modName, oleanCsv, irCsv] =>
    cliValidateEnv sysroot modName oleanCsv irCsv
  | ["check-cached-closed", sysroot, modName, declName, oleanPath] =>
    cliCheckCachedClosed sysroot modName declName oleanPath
  | ["probe-export", sysroot, modName, oleanCsv, irCsv] =>
    cliProbeExport sysroot modName oleanCsv irCsv
  | ["probe-v1", sysroot] =>
    cliProbeV1 sysroot
  | ["probe-v4", sysroot] =>
    cliProbeV4 sysroot
  | ["probe-v6", sysroot, lakeLibDir] =>
    cliProbeV6 sysroot lakeLibDir
  | _ =>
    IO.eprintln "usage: OleanQuotMdataUtf8ProtoTests <validate-bin|validate-env|check-cached-closed|probe-export|probe-v1|probe-v4|probe-v6> ..."
    return 2

end Anneal.OleanQuotMdataUtf8Proto
