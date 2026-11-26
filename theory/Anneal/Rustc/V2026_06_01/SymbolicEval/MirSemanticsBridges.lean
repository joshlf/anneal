import Anneal.Rustc.V2026_06_01.SymbolicEval.DiffTestingAndSigTests
import Anneal.Rustc.V2026_06_01.SymbolicEval.CfgGvnDriverAndBenchmarks

namespace Anneal.Rustc.V2026_06_01.SymbolicEval

open Trusted.Refinement
open Trusted.Sequence
open Trusted.Effect
open Trusted.ITree
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult
open Anneal.Refinement
open Anneal.Effect
open Anneal.ITree
open Anneal.EffectWP
open Anneal.ITreeWP
open Anneal.Scalars
open Anneal.Memory
open Anneal.UnsafeObligations
open Anneal.SepLogic
open Anneal.Rustc.V2026_06_01.Lower

/-!
Width-aware trusted `MirSemantics` operator bridges and production `DWLP mirDefaultWP` diamond /
triangle / `switchTable` join-cut combinators with `callerLocals` / full-`Memory` merges.
-/

/-!
## Trusted `MirSemantics` Operator Bridges & Production `DWLP mirDefaultWP` Diamond Join-Cut Combinators
-/

/-- Bridge adapter converting a concrete evaluated `SymId` into a trusted `MirSemantics.Value`
    (`8`-byte `u64` scalar). -/
def evalSymIdToMirValue (tbl : SymTable) (env : SymEnv) (id : SymId) :
    Trusted.Rustc.V2026_06_01.MirSemantics.Value :=
  .scalar { bits := evalSymId tbl env id, sizeBytes := 8 }

/-- Monotonicity of `evalSymIdToMirValue` under append-only `SymTable.Extends`. -/
theorem evalSymIdToMirValue_mono {tbl₁ tbl₂ : SymTable}
    (hValid : ValidTable tbl₁) (hExt : tbl₁.Extends tbl₂)
    (env : SymEnv) {id : SymId} (hlt : id < tbl₁.nodes.length) :
    evalSymIdToMirValue tbl₁ env id = evalSymIdToMirValue tbl₂ env id := by
  dsimp [evalSymIdToMirValue]
  rw [evalSymId_mono hValid hExt env hlt]

/-- `evalSymIdToMirValue` after `internTree` produces the exact 8-byte `MirSemantics.Value`
    of `ExprTree.eval`. -/
theorem evalSymIdToMirValue_internTree (tbl : SymTable) (hValid : ValidTable tbl)
    (t : ExprTree) (env : SymEnv) :
    evalSymIdToMirValue (internTree tbl t).2 env (internTree tbl t).1 =
      .scalar { bits := t.eval env, sizeBytes := 8 } := by
  dsimp [evalSymIdToMirValue]
  rw [(internTree_spec t tbl hValid).2.2.2 env]

/-- Universal `u64` range invariant for `evalSymIdToMirValue`: every `SymId` evaluates to a
    canonical 8-byte `MirSemantics.Value` whose scalar bits are `< word64Modulus`. -/
theorem evalSymIdToMirValue_lt_word64 (tbl : SymTable) (env : SymEnv) (id : SymId) :
    ∃ bits : Nat,
      evalSymIdToMirValue tbl env id = .scalar { bits := bits, sizeBytes := 8 } ∧
        bits < word64Modulus :=
  ⟨evalSymId tbl env id, rfl, evalSymId_lt_word64 tbl env id⟩

/-- `evalSymIdToMirValue` after `internNode` agrees with the single-step node evaluation. -/
theorem evalSymIdToMirValue_internNode {tbl : SymTable} {n : SymNode}
    (hValid : ValidTable tbl) (hNode : ValidNode tbl.nodes.length n) (env : SymEnv) :
    evalSymIdToMirValue (internNode tbl n).2 env (internNode tbl n).1 =
      .scalar { bits := evalSymNodeWith (evalSymId tbl env) env n, sizeBytes := 8 } := by
  dsimp [evalSymIdToMirValue]
  rw [internNode_eval hValid hNode env]

/-- `evalSymIdToMirValue` after `internOp2` (including peephole canonicalization) agrees with
    `evalSymOp2` on the operand `SymId`s. -/
theorem evalSymIdToMirValue_internOp2 {tbl : SymTable} {op : SymOp2} {a b : SymId}
    (hValid : ValidTable tbl) (ha : a < tbl.nodes.length) (hb : b < tbl.nodes.length)
    (env : SymEnv) :
    evalSymIdToMirValue (internOp2 tbl op a b).2 env (internOp2 tbl op a b).1 =
      .scalar { bits := evalSymOp2 op (evalSymId tbl env a) (evalSymId tbl env b), sizeBytes := 8 } := by
  dsimp [evalSymIdToMirValue]
  rw [internOp2_eval hValid ⟨ha, hb⟩ env]

theorem bridge_coexistence_rfl :
    evalSymIdToMirValue (buildDiamondGvn 4).2 (fun _ => 7) (buildDiamondGvn 4).1 =
      .scalar { bits := (buildDiamondTree 4).eval (fun _ => 7), sizeBytes := 8 } :=
  rfl

/-- Does `evalSymOp2` on `u64` arithmetic/bitwise/shift operations agree with the trusted
    `MirSemantics.evalScalarBinOp` on 8-byte scalars `a`, `b`? -/
def protoOpAgrees (op : SymOp2) (mop : Trusted.Rustc.V2026_06_01.MirAst.BinOp) (a b : Nat) : Bool :=
  match Trusted.Rustc.V2026_06_01.MirSemantics.evalScalarBinOp mop ⟨a, 8⟩ ⟨b, 8⟩ [] with
  | .ok (.scalar s) _ _ => s.bits == evalSymOp2 op a b && s.sizeBytes == 8
  | _ => false

/-- Does `evalSymOp2` on `u64` comparison operations agree with the trusted
    `MirSemantics.evalScalarBinOp` (which returns a 1-byte `bool` scalar via `boolToScalar`)
    on 8-byte inputs `a`, `b`? -/
def protoCmpAgrees (op : SymOp2) (mop : Trusted.Rustc.V2026_06_01.MirAst.BinOp) (a b : Nat) : Bool :=
  match Trusted.Rustc.V2026_06_01.MirSemantics.evalScalarBinOp mop ⟨a, 8⟩ ⟨b, 8⟩ [] with
  | .ok (.scalar s) _ _ => s.bits == evalSymOp2 op a b && s.sizeBytes == 1
  | _ => false

/-- Does every `SymOp1` unary operator (`id`, `boolNot`, `wrappingNeg64`, `maskLow32`, `xorConst`,
    `addConst`) agree with its trusted `MirSemantics` binary-operator encoding on 8-byte scalar
    `a` and constant `b`? -/
def protoOp1Agrees (a b : Nat) : Bool :=
  let m8 := Trusted.Rustc.V2026_06_01.MirSemantics.scalarModulus 8
  let idOk := Trusted.Rustc.V2026_06_01.MirSemantics.wrapScalarBits a m8 == evalSymOp1 .id a
  let boolNotOk :=
    match Trusted.Rustc.V2026_06_01.MirSemantics.evalScalarBinOp .eq ⟨a, 8⟩ ⟨0, 8⟩ [] with
    | .ok (.scalar s) _ _ => s.bits == evalSymOp1 .boolNot a && s.sizeBytes == 1
    | _ => false
  let negOk :=
    match Trusted.Rustc.V2026_06_01.MirSemantics.evalScalarBinOp .sub ⟨0, 8⟩ ⟨a, 8⟩ [] with
    | .ok (.scalar s) _ _ => s.bits == evalSymOp1 .wrappingNeg64 a && s.sizeBytes == 8
    | _ => false
  let maskOk :=
    match Trusted.Rustc.V2026_06_01.MirSemantics.evalScalarBinOp .bitAnd ⟨a, 8⟩ ⟨0xFFFFFFFF, 8⟩ [] with
    | .ok (.scalar s) _ _ => s.bits == evalSymOp1 .maskLow32 a && s.sizeBytes == 8
    | _ => false
  let xorOk :=
    match Trusted.Rustc.V2026_06_01.MirSemantics.evalScalarBinOp .bitXor ⟨a, 8⟩ ⟨wrap64 b, 8⟩ [] with
    | .ok (.scalar s) _ _ => s.bits == evalSymOp1 (.xorConst b) a && s.sizeBytes == 8
    | _ => false
  let addOk :=
    match Trusted.Rustc.V2026_06_01.MirSemantics.evalScalarBinOp .add ⟨a, 8⟩ ⟨wrap64 b, 8⟩ [] with
    | .ok (.scalar s) _ _ => s.bits == evalSymOp1 (.addConst b) a && s.sizeBytes == 8
    | _ => false
  idOk && boolNotOk && negOk && maskOk && xorOk && addOk

def bridgeSamples : List (Nat × Nat) :=
  [(0, 0), (3, 5), (5, 3), (1, 65), (18446744073709551615, 1),
   (18446744073709551615, 18446744073709551615), (9223372036854775808, 2), (123456789, 987654321)]

/-- MIR `bool` operand type used by the typed `UnOp::Not` bridge (`evalUnaryNot`'s `ty.kind = .bool`
    branch). -/
def bridgeBoolTy : Ty := { kind := .bool, layoutIdx := 0 }

/-- MIR `u64` operand type used by the typed `UnOp::Not` bridge (`evalUnaryNot`'s `ty.kind = .uint _`
    branch). -/
def bridgeU64Ty : Ty := { kind := .uint .u64, layoutIdx := 0 }

/-- MIR `u8` operand type: a `1`-byte **integer**, whose `!0u8 = 255` must not be confused with
    `bool`'s `!false = true` although both operands are `1`-byte scalars with bits `0`. -/
def bridgeU8Ty : Ty := { kind := .uint .u8, layoutIdx := 0 }

/-- MIR `UnOp::Not` as evaluated by the trusted `evalUnaryNot` on a `width`-byte scalar `a` whose
    operand type `ty` is **known** (`some ty`), exactly as the MIR lowering supplies it. The typed
    branches are the ones a lowering exercises; `evalUnaryNot`'s untyped (`none`) fallback guesses
    `bool` for every `1`-byte `0`/`1` operand and is deliberately *not* what this bridge checks. -/
def mirNot (ty : Ty) (a width : Nat) : Option Nat :=
  match Trusted.Rustc.V2026_06_01.MirSemantics.evalUnaryNot ⟨a, width⟩ (some ty) [] emptyMemory with
  | .ok (.scalar s) _ _ => if s.sizeBytes == width then some s.bits else none
  | _ => none

/-- **Trusted `MirSemantics.evalUnaryNot` Bridge (`bridge_unary_not_mapping`)**, on **typed**
    operands (`bool` / `u64` / `u8`):
    1. `boolNot` agrees with MIR `UnOp::Not` on `bool` operands `0`/`1`;
    2. `xorConst (2^64 - 1)` agrees with MIR `UnOp::Not` on `u64` samples (bitwise complement);
    3. `boolNot 5 ≠ MIR Not 5` on `u64`, so lowering integer `!x` to `boolNot` would be unsound;
    4. MIR `!` on an invalid `bool` (bits `5`) is UB (`none`), whereas `boolNot 5 = 0`: `boolNot` is
       only a faithful encoding on valid `0`/`1` booleans;
    5. on `1`-byte operands with bits `0`, `u8` and `bool` disagree (`255` vs `1`): the encoding must
       be chosen from the operand **type**, never from the operand width or value. -/
theorem bridge_unary_not_mapping :
    [0, 1].all (fun b => mirNot bridgeBoolTy b 1 == some (evalSymOp1 .boolNot b)) = true ∧
      bridgeSamples.all (fun p =>
        mirNot bridgeU64Ty p.1 8 == some (evalSymOp1 (.xorConst 18446744073709551615) p.1)) = true ∧
      mirNot bridgeU64Ty 5 8 ≠ some (evalSymOp1 .boolNot 5) ∧
      mirNot bridgeBoolTy 5 1 = none ∧
      mirNot bridgeU8Ty 0 1 = some 255 ∧ mirNot bridgeBoolTy 0 1 = some 1 := by
  decide +kernel

/-- Universal typed-`bool` `UnOp::Not` bridge: on every valid `bool` (`b ≤ 1`), MIR `!b` is
    `boolNot b`. -/
theorem evalUnaryNot_bool_eq_boolNot {b : Nat} (hb : b ≤ 1)
    (locals : List LocalSlot) (mem : Memory) :
    evalUnaryNot ⟨b, 1⟩ (some bridgeBoolTy) locals mem =
      .ok (.scalar ⟨evalSymOp1 .boolNot b, 1⟩) locals mem := by
  match b, hb with
  | 0, _ => rfl
  | 1, _ => rfl

/-- Universal typed-`bool` negative bridge: MIR `!b` on an invalid `bool` (`2 ≤ b`) is UB, although
    `evalSymOp1 .boolNot b = 0` is defined. -/
theorem evalUnaryNot_bool_invalid_ub {b : Nat} (hb : 2 ≤ b)
    (locals : List LocalSlot) (mem : Memory) :
    evalUnaryNot ⟨b, 1⟩ (some bridgeBoolTy) locals mem = .ub := by
  match b, hb with
  | _ + 2, _ => rfl

/-- Universal typed-`u64` `UnOp::Not` bridge: on every `u64` word `a`, MIR `!a` is
    `u64::MAX.wrapping_sub(a)` (`evalSymOp2 .sub (2^64 - 1) a`), i.e. the bitwise complement. -/
theorem evalUnaryNot_u64_eq_wrappingSubMax {a : Nat} (ha : a < word64Modulus)
    (locals : List LocalSlot) (mem : Memory) :
    evalUnaryNot ⟨a, 8⟩ (some bridgeU64Ty) locals mem =
      .ok (.scalar ⟨evalSymOp2 .sub 18446744073709551615 a, 8⟩) locals mem := by
  have ha' : a < 18446744073709551616 := ha
  have hle : a ≤ 18446744073709551615 := Nat.le_of_lt_succ ha'
  have hLt : 18446744073709551615 - a < 18446744073709551616 :=
    Nat.lt_of_le_of_lt (Nat.sub_le _ _) (by decide)
  show RvalueEvalResult.ok (.scalar ⟨Nat.sub (Nat.sub (scalarModulus 8) 1)
      (wrapScalarBits a (scalarModulus 8)), 8⟩) locals mem = _
  rw [scalarModulus_eight, wrapScalarBits_of_lt ha']
  have hSub : evalSymOp2 .sub 18446744073709551615 a = 18446744073709551615 - a := by
    show (18446744073709551615 + (18446744073709551616 - a % 18446744073709551616)) %
        18446744073709551616 = _
    rw [Nat.mod_eq_of_lt ha', ← Nat.add_sub_assoc (Nat.le_of_lt ha'),
      Nat.sub_add_comm hle, Nat.add_mod_right, Nat.mod_eq_of_lt hLt]
  rw [hSub]
  rfl

/-- **Trusted `MirSemantics.evalScalarBinOp` Bridge (`bridge_u64_semantics_agree`)**:
    Kernel-checked agreement with the trusted MIR semantics on boundary, shift-wrap (`65 % 64`),
    and generic `u64` samples across all 11 `SymOp2` binary operators and all 6 `SymOp1` unary
    operators (their binary-operator encodings). The universal counterparts for **every** operand
    pair are `bridge_u64_semantics_agree_universal` (binary) and the `evalUnaryNot_*` lemmas. -/
theorem bridge_u64_semantics_agree :
    bridgeSamples.all (fun p =>
      protoOp1Agrees p.1 p.2 &&
        protoOpAgrees .add .add p.1 p.2 && protoOpAgrees .sub .sub p.1 p.2 &&
        protoOpAgrees .mul .mul p.1 p.2 && protoOpAgrees .bitXor .bitXor p.1 p.2 &&
        protoOpAgrees .bitAnd .bitAnd p.1 p.2 && protoOpAgrees .bitOr .bitOr p.1 p.2 &&
        protoOpAgrees .shl .shl p.1 p.2 && protoOpAgrees .shr .shr p.1 p.2 &&
        protoCmpAgrees .eq .eq p.1 p.2 && protoCmpAgrees .lt .lt p.1 p.2 &&
        protoCmpAgrees .le .le p.1 p.2) = true := by
  decide +kernel

/-- Universal `u64` addition bridge: `evalSymOp2 .add a b` matches `MirSemantics.evalScalarBinOp .add`
    for **all** `a b : Nat`. -/
theorem evalSymOp2_add_eq_evalScalarBinOp
    (a b : Nat) (locals : List LocalSlot) (mem : Memory) :
    evalScalarBinOp .add ⟨a, 8⟩ ⟨b, 8⟩ locals mem false =
      .ok (.scalar ⟨evalSymOp2 .add a b, 8⟩) locals mem := by
  dsimp [evalScalarBinOp, evalSymOp2, wrap64, word64Modulus]
  rw [wrapScalarBits_eq_mod]

/-- Universal `u64` multiplication bridge: `evalSymOp2 .mul a b` matches
    `MirSemantics.evalScalarBinOp .mul` for **all** `a b : Nat`. -/
theorem evalSymOp2_mul_eq_evalScalarBinOp
    (a b : Nat) (locals : List LocalSlot) (mem : Memory) :
    evalScalarBinOp .mul ⟨a, 8⟩ ⟨b, 8⟩ locals mem false =
      .ok (.scalar ⟨evalSymOp2 .mul a b, 8⟩) locals mem := by
  dsimp [evalScalarBinOp, evalSymOp2, wrap64, word64Modulus]
  rw [wrapScalarBits_eq_mod]

/-- Universal `u64` wrapping subtraction bridge: `evalSymOp2 .sub a b` matches
    `MirSemantics.evalScalarBinOp .sub` for **all** `u64` words `a, b < word64Modulus`
    (proved without `omega`). -/
theorem evalSymOp2_sub_eq_evalScalarBinOp
    {a b : Nat} (ha : a < word64Modulus) (hb : b < word64Modulus)
    (locals : List LocalSlot) (mem : Memory) :
    evalScalarBinOp .sub ⟨a, 8⟩ ⟨b, 8⟩ locals mem false =
      .ok (.scalar ⟨evalSymOp2 .sub a b, 8⟩) locals mem := by
  dsimp [evalScalarBinOp, evalSymOp2, wrap64, word64Modulus] at ha hb ⊢
  have hModB : b % 18446744073709551616 = b := Nat.mod_eq_of_lt hb
  rw [hModB]
  cases hBle : Nat.ble b a with
  | true =>
    have hLe : b ≤ a := (nat_ble_eq_true_iff b a).1 hBle
    rw [wrapScalarBits_eq_mod]
    congr 2
    have hSubLt : a - b < 18446744073709551616 := Nat.lt_of_le_of_lt (Nat.sub_le a b) ha
    have hAddEq : a + (18446744073709551616 - b) = (a - b) + 18446744073709551616 := by
      rw [← Nat.add_sub_assoc (Nat.le_of_lt hb), Nat.sub_add_comm hLe]
    rw [hAddEq, Nat.add_mod_right, Nat.mod_eq_of_lt hSubLt]
  | false =>
    dsimp only
    rw [wrapScalarBits_of_lt ha, wrapScalarBits_of_lt hb, wrapScalarBits_eq_mod]
    have hEq : 18446744073709551616 + a - b = a + (18446744073709551616 - b) := by
      rw [Nat.add_comm 18446744073709551616 a, Nat.add_sub_assoc (Nat.le_of_lt hb)]
    rw [hEq]

/-- Universal `u64` equality comparison bridge: `evalSymOp2 .eq a b` matches
    `MirSemantics.evalScalarBinOp .eq` for **all** `a b : Nat`. -/
theorem evalSymOp2_eq_eq_evalScalarBinOp
    (a b : Nat) (locals : List LocalSlot) (mem : Memory) :
    evalScalarBinOp .eq ⟨a, 8⟩ ⟨b, 8⟩ locals mem false =
      .ok (.scalar ⟨evalSymOp2 .eq a b, 1⟩) locals mem := by
  dsimp [evalScalarBinOp, evalSymOp2, boolToScalar]
  by_cases h : a = b
  · subst h
    have hBeq : Nat.beq a a = true := (nat_beq_eq_true_iff a a).2 rfl
    have hBne : (a == a) = true := decide_eq_true rfl
    rw [hBeq, hBne]
    rfl
  · have hBeq : Nat.beq a b = false := (nat_beq_eq_false_iff a b).2 h
    have hBne : (a == b) = false := decide_eq_false h
    rw [hBeq, hBne]
    rfl

/-- Universal unsigned `u64` `<` bridge: `evalSymOp2 .lt a b` matches `MirSemantics.evalScalarBinOp .lt`
    (a `1`-byte `bool`) for **all** `a b : Nat`. -/
theorem evalSymOp2_lt_eq_evalScalarBinOp
    (a b : Nat) (locals : List LocalSlot) (mem : Memory) :
    evalScalarBinOp .lt ⟨a, 8⟩ ⟨b, 8⟩ locals mem false =
      .ok (.scalar ⟨evalSymOp2 .lt a b, 1⟩) locals mem := by
  show RvalueEvalResult.ok (.scalar (boolToScalar (Bool.not (Nat.ble b a)))) locals mem = _
  cases h : Nat.ble b a with
  | true =>
    have hn : decide (a < b) = false := decide_eq_false (Nat.not_lt.2 ((nat_ble_eq_true_iff b a).1 h))
    simp only [evalSymOp2, hn]
    rfl
  | false =>
    have hy : decide (a < b) = true := decide_eq_true ((nat_ble_eq_false_iff b a).1 h)
    simp only [evalSymOp2, hy]
    rfl

/-- Universal unsigned `u64` `≤` bridge: `evalSymOp2 .le a b` matches `MirSemantics.evalScalarBinOp .le`
    (a `1`-byte `bool`) for **all** `a b : Nat`. -/
theorem evalSymOp2_le_eq_evalScalarBinOp
    (a b : Nat) (locals : List LocalSlot) (mem : Memory) :
    evalScalarBinOp .le ⟨a, 8⟩ ⟨b, 8⟩ locals mem false =
      .ok (.scalar ⟨evalSymOp2 .le a b, 1⟩) locals mem := by
  show RvalueEvalResult.ok (.scalar (boolToScalar (Nat.ble a b))) locals mem = _
  cases h : Nat.ble a b with
  | true =>
    have hy : decide (a ≤ b) = true := decide_eq_true ((nat_ble_eq_true_iff a b).1 h)
    simp only [evalSymOp2, hy]
    rfl
  | false =>
    have hn : decide (a ≤ b) = false := decide_eq_false (Nat.not_le.2 ((nat_ble_eq_false_iff a b).1 h))
    simp only [evalSymOp2, hn]
    rfl

/-- Universal `u64` `<<` bridge: `evalSymOp2 .shl a b` (shift amount masked to `b % 64`) matches
    `MirSemantics.evalScalarBinOp .shl` for **all** `a b : Nat`. -/
theorem evalSymOp2_shl_eq_evalScalarBinOp
    (a b : Nat) (locals : List LocalSlot) (mem : Memory) :
    evalScalarBinOp .shl ⟨a, 8⟩ ⟨b, 8⟩ locals mem false =
      .ok (.scalar ⟨evalSymOp2 .shl a b, 8⟩) locals mem := by
  show RvalueEvalResult.ok
    (.scalar ⟨shiftLeftBits a (Nat.mod b (Nat.mul 8 8)) (scalarModulus 8), 8⟩) locals mem = _
  simp only [shiftLeftBits, evalSymOp2, wrap64, word64Modulus, scalarModulus_eight,
    wrapScalarBits_eq_mod, scalarPow2_eq_two_pow, Nat.shiftLeft_eq', Nat.shiftLeft_eq]
  rfl

/-- Universal unsigned `u64` `>>` bridge: `evalSymOp2 .shr a b` (shift amount masked to `b % 64`)
    matches `MirSemantics.evalScalarBinOp .shr` for **all** `a b : Nat`. -/
theorem evalSymOp2_shr_eq_evalScalarBinOp
    (a b : Nat) (locals : List LocalSlot) (mem : Memory) :
    evalScalarBinOp .shr ⟨a, 8⟩ ⟨b, 8⟩ locals mem false =
      .ok (.scalar ⟨evalSymOp2 .shr a b, 8⟩) locals mem := by
  show RvalueEvalResult.ok (.scalar ⟨wrapScalarBits
    (shiftRightUnsignedBits a (Nat.mod b (Nat.mul 8 8))) (scalarModulus 8), 8⟩) locals mem = _
  have hShr : Nat.shiftRight a (b % 64) = a / 2 ^ (b % 64) := Nat.shiftRight_eq_div_pow a (b % 64)
  simp only [shiftRightUnsignedBits, evalSymOp2, wrap64, word64Modulus, scalarModulus_eight,
    wrapScalarBits_eq_mod, scalarPow2_eq_two_pow, hShr]
  rfl

/-- `testBit` of a trusted bit-recursion step `bit + 2 * rest` (`bit < 2`) at bit `0`. -/
theorem testBit_bitStep_zero {bit rest : Nat} (hb : bit < 2) :
    (Nat.add bit (Nat.mul 2 rest)).testBit 0 = decide (bit = 1) := by
  rw [Nat.testBit_zero]
  have h : (Nat.add bit (Nat.mul 2 rest)) % 2 = bit := by
    show (bit + 2 * rest) % 2 = bit
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hb]
  rw [h]

/-- `testBit` of a trusted bit-recursion step `bit + 2 * rest` (`bit < 2`) at bit `j + 1`. -/
theorem testBit_bitStep_succ {bit rest : Nat} (hb : bit < 2) (j : Nat) :
    (Nat.add bit (Nat.mul 2 rest)).testBit (j + 1) = rest.testBit j := by
  rw [Nat.testBit_succ]
  have h : (Nat.add bit (Nat.mul 2 rest)) / 2 = rest := by
    show (bit + 2 * rest) / 2 = rest
    rw [Nat.add_mul_div_left _ _ (by decide : 0 < 2), Nat.div_eq_of_lt hb, Nat.zero_add]
  rw [h]

theorem decide_succ_lt_succ (j k : Nat) : decide (j + 1 < k + 1) = decide (j < k) :=
  decide_eq_decide.mpr Nat.succ_lt_succ_iff

/-- Bitwise characterization of the trusted `bitwiseAndBits` recursion. -/
theorem testBit_bitwiseAndBits :
    ∀ (k a b i : Nat),
      (bitwiseAndBits k a b).testBit i = (decide (i < k) && (a.testBit i && b.testBit i))
  | 0, a, b, i => by
    show (0 : Nat).testBit i = _
    rw [Nat.zero_testBit]
    rfl
  | k + 1, a, b, 0 => by
    refine (testBit_bitStep_zero ?_).trans ?_
    · split <;> decide
    · rw [Nat.testBit_zero a, Nat.testBit_zero b]
      rcases Nat.mod_two_eq_zero_or_one a with ha | ha <;>
        rcases Nat.mod_two_eq_zero_or_one b with hb | hb <;>
        · have ha' : Nat.mod a 2 = _ := ha
          have hb' : Nat.mod b 2 = _ := hb
          simp only [ha, hb, ha', hb']
          all_goals rfl
  | k + 1, a, b, j + 1 => by
    refine (testBit_bitStep_succ ?_ j).trans ((testBit_bitwiseAndBits k (a / 2) (b / 2) j).trans ?_)
    · split <;> decide
    · rw [Nat.testBit_succ a j, Nat.testBit_succ b j, decide_succ_lt_succ]

/-- Bitwise characterization of the trusted `bitwiseOrBits` recursion. -/
theorem testBit_bitwiseOrBits :
    ∀ (k a b i : Nat),
      (bitwiseOrBits k a b).testBit i = (decide (i < k) && (a.testBit i || b.testBit i))
  | 0, a, b, i => by
    show (0 : Nat).testBit i = _
    rw [Nat.zero_testBit]
    rfl
  | k + 1, a, b, 0 => by
    refine (testBit_bitStep_zero ?_).trans ?_
    · split <;> decide
    · rw [Nat.testBit_zero a, Nat.testBit_zero b]
      rcases Nat.mod_two_eq_zero_or_one a with ha | ha <;>
        rcases Nat.mod_two_eq_zero_or_one b with hb | hb <;>
        · have ha' : Nat.mod a 2 = _ := ha
          have hb' : Nat.mod b 2 = _ := hb
          simp only [ha, hb, ha', hb']
          all_goals rfl
  | k + 1, a, b, j + 1 => by
    refine (testBit_bitStep_succ ?_ j).trans ((testBit_bitwiseOrBits k (a / 2) (b / 2) j).trans ?_)
    · split <;> decide
    · rw [Nat.testBit_succ a j, Nat.testBit_succ b j, decide_succ_lt_succ]

/-- Bitwise characterization of the trusted `bitwiseXorBits` recursion. -/
theorem testBit_bitwiseXorBits :
    ∀ (k a b i : Nat),
      (bitwiseXorBits k a b).testBit i = (decide (i < k) && (a.testBit i ^^ b.testBit i))
  | 0, a, b, i => by
    show (0 : Nat).testBit i = _
    rw [Nat.zero_testBit]
    rfl
  | k + 1, a, b, 0 => by
    refine (testBit_bitStep_zero ?_).trans ?_
    · split <;> decide
    · rw [Nat.testBit_zero a, Nat.testBit_zero b]
      rcases Nat.mod_two_eq_zero_or_one a with ha | ha <;>
        rcases Nat.mod_two_eq_zero_or_one b with hb | hb <;>
        · have ha' : Nat.mod a 2 = _ := ha
          have hb' : Nat.mod b 2 = _ := hb
          simp only [ha, hb, ha', hb']
          all_goals rfl
  | k + 1, a, b, j + 1 => by
    refine (testBit_bitStep_succ ?_ j).trans ((testBit_bitwiseXorBits k (a / 2) (b / 2) j).trans ?_)
    · split <;> decide
    · rw [Nat.testBit_succ a j, Nat.testBit_succ b j, decide_succ_lt_succ]

theorem bitwiseAndBits_eq (k a b : Nat) : bitwiseAndBits k a b = (a &&& b) % 2 ^ k := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_bitwiseAndBits, Nat.testBit_mod_two_pow, Nat.testBit_and]

theorem bitwiseOrBits_eq (k a b : Nat) : bitwiseOrBits k a b = (a ||| b) % 2 ^ k := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_bitwiseOrBits, Nat.testBit_mod_two_pow, Nat.testBit_or]

theorem bitwiseXorBits_eq (k a b : Nat) : bitwiseXorBits k a b = (a ^^^ b) % 2 ^ k := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_bitwiseXorBits, Nat.testBit_mod_two_pow, Nat.testBit_xor]

/-- Universal `u64` `&` bridge (trusted `bitwiseAndBits` recursion) for **all** `a b : Nat`. -/
theorem evalSymOp2_bitAnd_eq_evalScalarBinOp
    (a b : Nat) (locals : List LocalSlot) (mem : Memory) :
    evalScalarBinOp .bitAnd ⟨a, 8⟩ ⟨b, 8⟩ locals mem false =
      .ok (.scalar ⟨evalSymOp2 .bitAnd a b, 8⟩) locals mem := by
  show RvalueEvalResult.ok (.scalar ⟨bitwiseAndBits (Nat.mul 8 8) a b, 8⟩) locals mem = _
  rw [bitwiseAndBits_eq]
  rfl

/-- Universal `u64` `|` bridge (trusted `bitwiseOrBits` recursion) for **all** `a b : Nat`. -/
theorem evalSymOp2_bitOr_eq_evalScalarBinOp
    (a b : Nat) (locals : List LocalSlot) (mem : Memory) :
    evalScalarBinOp .bitOr ⟨a, 8⟩ ⟨b, 8⟩ locals mem false =
      .ok (.scalar ⟨evalSymOp2 .bitOr a b, 8⟩) locals mem := by
  show RvalueEvalResult.ok (.scalar ⟨bitwiseOrBits (Nat.mul 8 8) a b, 8⟩) locals mem = _
  rw [bitwiseOrBits_eq]
  rfl

/-- Universal `u64` `^` bridge (trusted `bitwiseXorBits` recursion) for **all** `a b : Nat`. -/
theorem evalSymOp2_bitXor_eq_evalScalarBinOp
    (a b : Nat) (locals : List LocalSlot) (mem : Memory) :
    evalScalarBinOp .bitXor ⟨a, 8⟩ ⟨b, 8⟩ locals mem false =
      .ok (.scalar ⟨evalSymOp2 .bitXor a b, 8⟩) locals mem := by
  show RvalueEvalResult.ok (.scalar ⟨bitwiseXorBits (Nat.mul 8 8) a b, 8⟩) locals mem = _
  rw [bitwiseXorBits_eq]
  rfl

/-- `k`-bit all-ones mask (`2 ^ k - 1`), defined structurally so `testBit`, low-masking, and
    bitwise-complement identities can be proved by elementary bit recursion without
    `Classical.choice` (`Nat.testBit_two_pow_sub_succ` in Lean core depends on `Classical.choice`). -/
def onesBits : Nat → Nat
  | 0 => 0
  | k + 1 => 1 + 2 * onesBits k

theorem testBit_onesBits : ∀ (k i : Nat), (onesBits k).testBit i = decide (i < k)
  | 0, i => by
    show (0 : Nat).testBit i = _
    rw [Nat.zero_testBit]
    rfl
  | k + 1, 0 => by
    refine (testBit_bitStep_zero (by decide : 1 < 2)).trans ?_
    rfl
  | k + 1, j + 1 => by
    refine (testBit_bitStep_succ (by decide : 1 < 2) j).trans ?_
    rw [testBit_onesBits k j, decide_succ_lt_succ]

theorem and_onesBits_eq_mod (k a : Nat) : (a &&& onesBits k) = a % 2 ^ k := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, testBit_onesBits, Nat.testBit_mod_two_pow, Bool.and_comm]

/-- `k`-bit bitwise complement of `a`, defined by the same bit-step recursion as `bitwiseXorBits`. -/
def bitwiseComplementBits : Nat → Nat → Nat
  | 0, _ => 0
  | k + 1, a => (1 - a % 2) + 2 * bitwiseComplementBits k (a / 2)

theorem testBit_bitwiseComplementBits :
    ∀ (k a i : Nat),
      (bitwiseComplementBits k a).testBit i = (decide (i < k) && !a.testBit i)
  | 0, a, i => by
    show (0 : Nat).testBit i = _
    rw [Nat.zero_testBit]
    rfl
  | k + 1, a, 0 => by
    have hb : 1 - a % 2 < 2 := Nat.lt_of_le_of_lt (Nat.sub_le 1 (a % 2)) (by decide)
    refine (testBit_bitStep_zero hb).trans ?_
    rw [Nat.testBit_zero a]
    rcases Nat.mod_two_eq_zero_or_one a with ha | ha <;> simp [ha]
  | k + 1, a, j + 1 => by
    have hb : 1 - a % 2 < 2 := Nat.lt_of_le_of_lt (Nat.sub_le 1 (a % 2)) (by decide)
    refine (testBit_bitStep_succ hb j).trans ?_
    rw [testBit_bitwiseComplementBits k (a / 2) j, Nat.testBit_succ a j, decide_succ_lt_succ]

theorem bitwiseComplementBits_eq_xor_onesBits (k a : Nat) :
    bitwiseComplementBits k a = (a ^^^ onesBits k) % 2 ^ k := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_bitwiseComplementBits, Nat.testBit_mod_two_pow, Nat.testBit_xor, testBit_onesBits]
  cases decide (i < k) <;> cases a.testBit i <;> rfl

private theorem bitStep_add_compl (r c q : Nat) (hr : r = 0 ∨ r = 1) :
    ((1 - r) + 2 * c) + (r + 2 * q) = 1 + 2 * (c + q) := by
  rcases hr with rfl | rfl
  · show (1 + 2 * c) + (0 + 2 * q) = 1 + 2 * (c + q)
    rw [Nat.zero_add, Nat.add_assoc, ← Nat.left_distrib]
  · show (0 + 2 * c) + (1 + 2 * q) = 1 + 2 * (c + q)
    rw [Nat.zero_add, ← Nat.add_assoc, Nat.add_comm (2 * c) 1, Nat.add_assoc, ← Nat.left_distrib]

theorem bitwiseComplementBits_add_eq_onesBits :
    ∀ (k a : Nat), a < 2 ^ k → bitwiseComplementBits k a + a = onesBits k
  | 0, a, ha => by
    match a, ha with
    | 0, _ => rfl
  | k + 1, a, ha => by
    have hDivLt : a / 2 < 2 ^ k :=
      (Nat.div_lt_iff_lt_mul (by decide : 0 < 2)).2 (by rw [← Nat.pow_succ]; exact ha)
    have ih := bitwiseComplementBits_add_eq_onesBits k (a / 2) hDivLt
    have hDecomp : a % 2 + 2 * (a / 2) = a := by
      rw [Nat.add_comm]
      exact Nat.div_add_mod a 2
    show ((1 - a % 2) + 2 * bitwiseComplementBits k (a / 2)) + a = 1 + 2 * onesBits k
    conv => lhs; rhs; rw [← hDecomp]
    rw [bitStep_add_compl (a % 2) (bitwiseComplementBits k (a / 2)) (a / 2)
      (Nat.mod_two_eq_zero_or_one a), ih]

/-- Constructive (`Classical.choice`-free) equivalence between `(2 ^ k - 1) - a` and
    `(a ^^^ (2 ^ k - 1)) % 2 ^ k` for all `a < 2 ^ k`. -/
theorem onesBits_sub_eq_xor {k a : Nat} (ha : a < 2 ^ k) :
    onesBits k - a = (a ^^^ onesBits k) % 2 ^ k := by
  have hSub : onesBits k - a = bitwiseComplementBits k a := by
    rw [← bitwiseComplementBits_add_eq_onesBits k a ha, Nat.add_sub_cancel]
  rw [hSub, bitwiseComplementBits_eq_xor_onesBits]

/-- Equivalence between `evalSymOp2 .sub (2^64 - 1) a` (`u64::MAX.wrapping_sub(a)`) and
    `evalSymOp1 (.xorConst (2^64 - 1)) a` (`a ^ u64::MAX`) for all `a < word64Modulus`
    (proved without `Classical.choice`). -/
theorem evalSymOp2_sub_max_eq_xorConst_max {a : Nat} (ha : a < word64Modulus) :
    evalSymOp2 .sub 18446744073709551615 a = evalSymOp1 (.xorConst 18446744073709551615) a := by
  have ha' : a < 18446744073709551616 := ha
  have hle : a ≤ 18446744073709551615 := Nat.le_of_lt_succ ha'
  have hLt : 18446744073709551615 - a < 18446744073709551616 :=
    Nat.lt_of_le_of_lt (Nat.sub_le _ _) (by decide)
  have hSub : evalSymOp2 .sub 18446744073709551615 a = 18446744073709551615 - a := by
    show (18446744073709551615 + (18446744073709551616 - a % 18446744073709551616)) %
        18446744073709551616 = _
    rw [Nat.mod_eq_of_lt ha', ← Nat.add_sub_assoc (Nat.le_of_lt ha'),
      Nat.sub_add_comm hle, Nat.add_mod_right, Nat.mod_eq_of_lt hLt]
  rw [hSub]
  exact onesBits_sub_eq_xor (k := 64) ha

/-- **Universal typed-`u64` `UnOp::Not` ↔ `xorConst (2^64 - 1)` bridge
    (`evalUnaryNot_u64_eq_xorConst_max`)**: on **every** `u64` word `a < word64Modulus`,
    trusted `MirSemantics.evalUnaryNot` on `u64` equals `evalSymOp1 (.xorConst (2^64 - 1)) a`
    (proved without `Classical.choice`). -/
theorem evalUnaryNot_u64_eq_xorConst_max {a : Nat} (ha : a < word64Modulus)
    (locals : List LocalSlot) (mem : Memory) :
    evalUnaryNot ⟨a, 8⟩ (some bridgeU64Ty) locals mem =
      .ok (.scalar ⟨evalSymOp1 (.xorConst 18446744073709551615) a, 8⟩) locals mem := by
  rw [evalUnaryNot_u64_eq_wrappingSubMax ha, evalSymOp2_sub_max_eq_xorConst_max ha]

/-- Universal typed-`u8` `UnOp::Not` bridge (`evalUnaryNot_u8_eq_xor_255`): on every `u8` byte
    `a < 256`, trusted `MirSemantics.evalUnaryNot` on `u8` computes `(a ^^^ 255) % 256` (`1` byte),
    which disagrees with `boolNot 0 = 1` on `a = 0`. -/
theorem evalUnaryNot_u8_eq_xor_255 {a : Nat} (ha : a < 256)
    (locals : List LocalSlot) (mem : Memory) :
    evalUnaryNot ⟨a, 1⟩ (some bridgeU8Ty) locals mem =
      .ok (.scalar ⟨(a ^^^ 255) % 256, 1⟩) locals mem := by
  have hSubXor : 255 - a = (a ^^^ 255) % 256 := onesBits_sub_eq_xor (k := 8) ha
  show RvalueEvalResult.ok (.scalar ⟨Nat.sub 255 (wrapScalarBits a 256), 1⟩) locals mem = _
  rw [wrapScalarBits_of_lt ha]
  change RvalueEvalResult.ok (.scalar ⟨255 - a, 1⟩) locals mem = _
  rw [hSubXor]

/-- Universal `SymOp1.id` bridge: `wrapScalarBits a (scalarModulus 8)` equals `evalSymOp1 .id a`
    for **all** `a < word64Modulus`. -/
theorem evalSymOp1_id_eq_wrapScalarBits {a : Nat} (ha : a < word64Modulus) :
    wrapScalarBits a (scalarModulus 8) = evalSymOp1 .id a := by
  have ha' : a < 18446744073709551616 := ha
  show wrapScalarBits a 18446744073709551616 = a
  exact wrapScalarBits_of_lt ha'

/-- Universal `SymOp1.boolNot` bridge: `evalScalarBinOp .eq ⟨a, 8⟩ ⟨0, 8⟩` produces
    `evalSymOp1 .boolNot a` (`1`-byte `bool`) for **all** `a : Nat`. -/
theorem evalSymOp1_boolNot_eq_evalScalarBinOp
    (a : Nat) (locals : List LocalSlot) (mem : Memory) :
    evalScalarBinOp .eq ⟨a, 8⟩ ⟨0, 8⟩ locals mem false =
      .ok (.scalar ⟨evalSymOp1 .boolNot a, 1⟩) locals mem :=
  evalSymOp2_eq_eq_evalScalarBinOp a 0 locals mem

/-- Universal `SymOp1.wrappingNeg64` bridge: `evalScalarBinOp .sub ⟨0, 8⟩ ⟨a, 8⟩` produces
    `evalSymOp1 .wrappingNeg64 a` (`8`-byte `u64`) for **all** `a < word64Modulus`. -/
theorem evalSymOp1_wrappingNeg64_eq_evalScalarBinOp
    {a : Nat} (ha : a < word64Modulus) (locals : List LocalSlot) (mem : Memory) :
    evalScalarBinOp .sub ⟨0, 8⟩ ⟨a, 8⟩ locals mem false =
      .ok (.scalar ⟨evalSymOp1 .wrappingNeg64 a, 8⟩) locals mem := by
  have h0 : (0 : Nat) < word64Modulus := by decide
  have hSub := evalSymOp2_sub_eq_evalScalarBinOp h0 ha locals mem
  have hEq : evalSymOp2 .sub 0 a = evalSymOp1 .wrappingNeg64 a := by
    dsimp [evalSymOp2, evalSymOp1, wrap64]
    rw [Nat.zero_add]
  rw [hEq] at hSub
  exact hSub

/-- Universal `SymOp1.maskLow32` bridge: `evalScalarBinOp .bitAnd ⟨a, 8⟩ ⟨0xFFFFFFFF, 8⟩` produces
    `evalSymOp1 .maskLow32 a` (`a % 2^32`, `8` bytes) for **all** `a : Nat` (closing the sampled-only
    gap for `maskLow32` without `Classical.choice`). -/
theorem evalSymOp1_maskLow32_eq_evalScalarBinOp
    (a : Nat) (locals : List LocalSlot) (mem : Memory) :
    evalScalarBinOp .bitAnd ⟨a, 8⟩ ⟨0xFFFFFFFF, 8⟩ locals mem false =
      .ok (.scalar ⟨evalSymOp1 .maskLow32 a, 8⟩) locals mem := by
  rw [evalSymOp2_bitAnd_eq_evalScalarBinOp]
  have hMask : (a &&& 0xFFFFFFFF) % 18446744073709551616 = a % 4294967296 := by
    change (a &&& onesBits 32) % 2 ^ 64 = a % 2 ^ 32
    rw [and_onesBits_eq_mod 32 a]
    exact Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt a (by decide)) (by decide))
  dsimp [evalSymOp2, evalSymOp1, wrap64, word64Modulus]
  rw [hMask]

/-- Universal `SymOp1.xorConst` bridge: `evalScalarBinOp .bitXor ⟨a, 8⟩ ⟨wrap64 b, 8⟩` produces
    `evalSymOp1 (.xorConst b) a` for **all** `a b : Nat`. -/
theorem evalSymOp1_xorConst_eq_evalScalarBinOp
    (a b : Nat) (locals : List LocalSlot) (mem : Memory) :
    evalScalarBinOp .bitXor ⟨a, 8⟩ ⟨wrap64 b, 8⟩ locals mem false =
      .ok (.scalar ⟨evalSymOp1 (.xorConst b) a, 8⟩) locals mem := by
  rw [evalSymOp2_bitXor_eq_evalScalarBinOp]
  have hXor : (a ^^^ (b % 2 ^ 64)) % 2 ^ 64 = (a ^^^ b) % 2 ^ 64 := by
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_mod_two_pow, Nat.testBit_xor, Nat.testBit_mod_two_pow,
      Nat.testBit_mod_two_pow, Nat.testBit_xor]
    cases decide (i < 64) <;> cases a.testBit i <;> cases b.testBit i <;> rfl
  dsimp [evalSymOp2, evalSymOp1, wrap64, word64Modulus]
  exact congrArg (fun v => RvalueEvalResult.ok (.scalar ⟨v, 8⟩) locals mem) hXor

/-- Universal `SymOp1.addConst` bridge: `evalScalarBinOp .add ⟨a, 8⟩ ⟨wrap64 b, 8⟩` produces
    `evalSymOp1 (.addConst b) a` for **all** `a b : Nat`. -/
theorem evalSymOp1_addConst_eq_evalScalarBinOp
    (a b : Nat) (locals : List LocalSlot) (mem : Memory) :
    evalScalarBinOp .add ⟨a, 8⟩ ⟨wrap64 b, 8⟩ locals mem false =
      .ok (.scalar ⟨evalSymOp1 (.addConst b) a, 8⟩) locals mem := by
  rw [evalSymOp2_add_eq_evalScalarBinOp]
  dsimp [evalSymOp2, evalSymOp1, wrap64, word64Modulus]
  rw [Nat.add_mod_mod]

/-- **Universal `SymOp1` unary operator bridge (`bridge_symOp1_semantics_agree_universal`)**:
    for **every** `u64` word `a < word64Modulus` and constant `b : Nat`, all 6 `SymOp1` unary
    operators (`id`, `boolNot`, `wrappingNeg64`, `maskLow32`, `xorConst`, `addConst`) agree with
    their trusted `MirSemantics` encodings, and `xorConst (2^64 - 1)` agrees with typed `u64`
    `MirSemantics.evalUnaryNot`. -/
theorem bridge_symOp1_semantics_agree_universal
    {a : Nat} (ha : a < word64Modulus) (b : Nat)
    (locals : List LocalSlot) (mem : Memory) :
    wrapScalarBits a (scalarModulus 8) = evalSymOp1 .id a ∧
      evalScalarBinOp .eq ⟨a, 8⟩ ⟨0, 8⟩ locals mem false =
        .ok (.scalar ⟨evalSymOp1 .boolNot a, 1⟩) locals mem ∧
      evalScalarBinOp .sub ⟨0, 8⟩ ⟨a, 8⟩ locals mem false =
        .ok (.scalar ⟨evalSymOp1 .wrappingNeg64 a, 8⟩) locals mem ∧
      evalScalarBinOp .bitAnd ⟨a, 8⟩ ⟨0xFFFFFFFF, 8⟩ locals mem false =
        .ok (.scalar ⟨evalSymOp1 .maskLow32 a, 8⟩) locals mem ∧
      evalScalarBinOp .bitXor ⟨a, 8⟩ ⟨wrap64 b, 8⟩ locals mem false =
        .ok (.scalar ⟨evalSymOp1 (.xorConst b) a, 8⟩) locals mem ∧
      evalScalarBinOp .add ⟨a, 8⟩ ⟨wrap64 b, 8⟩ locals mem false =
        .ok (.scalar ⟨evalSymOp1 (.addConst b) a, 8⟩) locals mem ∧
      evalUnaryNot ⟨a, 8⟩ (some bridgeU64Ty) locals mem =
        .ok (.scalar ⟨evalSymOp1 (.xorConst 18446744073709551615) a, 8⟩) locals mem :=
  ⟨evalSymOp1_id_eq_wrapScalarBits ha,
   evalSymOp1_boolNot_eq_evalScalarBinOp a locals mem,
   evalSymOp1_wrappingNeg64_eq_evalScalarBinOp ha locals mem,
   evalSymOp1_maskLow32_eq_evalScalarBinOp a locals mem,
   evalSymOp1_xorConst_eq_evalScalarBinOp a b locals mem,
   evalSymOp1_addConst_eq_evalScalarBinOp a b locals mem,
   evalUnaryNot_u64_eq_xorConst_max ha locals mem⟩

/-- **Universal `u64` operator bridge (`bridge_u64_semantics_agree_universal`)**: for **every** pair
    of `u64` words `a, b` (the canonical-range hypotheses are needed only by `sub`), all 11 `SymOp2`
    operators agree with the trusted `MirSemantics.evalScalarBinOp` (`8`-byte results for
    arithmetic/bitwise/shift operators, `1`-byte `bool` results for comparisons). This upgrades the
    sampled `bridge_u64_semantics_agree` regression test to a theorem over the whole `u64` domain. -/
theorem bridge_u64_semantics_agree_universal
    {a b : Nat} (ha : a < word64Modulus) (hb : b < word64Modulus)
    (locals : List LocalSlot) (mem : Memory) :
    evalScalarBinOp .add ⟨a, 8⟩ ⟨b, 8⟩ locals mem false =
        .ok (.scalar ⟨evalSymOp2 .add a b, 8⟩) locals mem ∧
      evalScalarBinOp .sub ⟨a, 8⟩ ⟨b, 8⟩ locals mem false =
        .ok (.scalar ⟨evalSymOp2 .sub a b, 8⟩) locals mem ∧
      evalScalarBinOp .mul ⟨a, 8⟩ ⟨b, 8⟩ locals mem false =
        .ok (.scalar ⟨evalSymOp2 .mul a b, 8⟩) locals mem ∧
      evalScalarBinOp .bitAnd ⟨a, 8⟩ ⟨b, 8⟩ locals mem false =
        .ok (.scalar ⟨evalSymOp2 .bitAnd a b, 8⟩) locals mem ∧
      evalScalarBinOp .bitOr ⟨a, 8⟩ ⟨b, 8⟩ locals mem false =
        .ok (.scalar ⟨evalSymOp2 .bitOr a b, 8⟩) locals mem ∧
      evalScalarBinOp .bitXor ⟨a, 8⟩ ⟨b, 8⟩ locals mem false =
        .ok (.scalar ⟨evalSymOp2 .bitXor a b, 8⟩) locals mem ∧
      evalScalarBinOp .shl ⟨a, 8⟩ ⟨b, 8⟩ locals mem false =
        .ok (.scalar ⟨evalSymOp2 .shl a b, 8⟩) locals mem ∧
      evalScalarBinOp .shr ⟨a, 8⟩ ⟨b, 8⟩ locals mem false =
        .ok (.scalar ⟨evalSymOp2 .shr a b, 8⟩) locals mem ∧
      evalScalarBinOp .eq ⟨a, 8⟩ ⟨b, 8⟩ locals mem false =
        .ok (.scalar ⟨evalSymOp2 .eq a b, 1⟩) locals mem ∧
      evalScalarBinOp .lt ⟨a, 8⟩ ⟨b, 8⟩ locals mem false =
        .ok (.scalar ⟨evalSymOp2 .lt a b, 1⟩) locals mem ∧
      evalScalarBinOp .le ⟨a, 8⟩ ⟨b, 8⟩ locals mem false =
        .ok (.scalar ⟨evalSymOp2 .le a b, 1⟩) locals mem :=
  ⟨evalSymOp2_add_eq_evalScalarBinOp a b locals mem,
   evalSymOp2_sub_eq_evalScalarBinOp ha hb locals mem,
   evalSymOp2_mul_eq_evalScalarBinOp a b locals mem,
   evalSymOp2_bitAnd_eq_evalScalarBinOp a b locals mem,
   evalSymOp2_bitOr_eq_evalScalarBinOp a b locals mem,
   evalSymOp2_bitXor_eq_evalScalarBinOp a b locals mem,
   evalSymOp2_shl_eq_evalScalarBinOp a b locals mem,
   evalSymOp2_shr_eq_evalScalarBinOp a b locals mem,
   evalSymOp2_eq_eq_evalScalarBinOp a b locals mem,
   evalSymOp2_lt_eq_evalScalarBinOp a b locals mem,
   evalSymOp2_le_eq_evalScalarBinOp a b locals mem⟩

/-- Width-parameterized bridge adapter converting an evaluated `SymId` into a trusted
    `MirSemantics.Value` of `sizeBytes` bytes (`8` for `u64` words, `1` for `bool` comparisons). -/
def evalSymIdToMirValueSized (sizeBytes : Nat) (tbl : SymTable) (env : SymEnv) (id : SymId) :
    Trusted.Rustc.V2026_06_01.MirSemantics.Value :=
  .scalar { bits := evalSymId tbl env id, sizeBytes := sizeBytes }

theorem evalSymIdToMirValue_eq_sized (tbl : SymTable) (env : SymEnv) (id : SymId) :
    evalSymIdToMirValue tbl env id = evalSymIdToMirValueSized 8 tbl env id :=
  rfl

/-- Byte width of a `SymOp1` result in `MirSemantics` (`1` for `boolNot`, `8` for `u64` ops). -/
def SymOp1.resultSizeBytes : SymOp1 → Nat
  | .boolNot => 1
  | _ => 8

/-- Byte width of a `SymOp2` result in `MirSemantics` (`1` for `bool`-valued comparisons
    `eq`/`lt`/`le`, `8` for `u64` arithmetic/bitwise/shift ops). -/
def SymOp2.resultSizeBytes : SymOp2 → Nat
  | .eq | .lt | .le => 1
  | _ => 8

/-- Byte width of a `SymNode` in `MirSemantics` (`1` for boolean-producing `op1`/`op2` nodes,
    `8` otherwise). -/
def SymNode.resultSizeBytes : SymNode → Nat
  | .op1 op _ => op.resultSizeBytes
  | .op2 op _ _ => op.resultSizeBytes
  | _ => 8

/-- **Negative control: a MIR width is a property of the use site, not of the GVN node**
    (`gvn_node_width_is_not_mir_width`). Peephole GVN folds `x == x` to the hash-consed
    `.const 1`, whose node-derived width is `8`, while MIR's `Eq` yields a `1`-byte `bool`; the same
    `.const 1` node is shared with every `u64` constant `1`. Widths must come from the operator or the
    use site (`evalSymIdToMirValueSized op.resultSizeBytes`, as in
    `evalSymIdToMirValueSized_internOp2_eq_evalScalarBinOp`), never from `tbl.nodes[id]?`, which is
    why no node-typed adapter is provided. -/
theorem gvn_node_width_is_not_mir_width :
    let res := internOp2 { nodes := [.var 0] } .eq 0 0
    (res.2.nodes[res.1]?).map SymNode.resultSizeBytes = some 8 ∧
      SymOp2.resultSizeBytes .eq = 1 := by
  decide +kernel

/-- Mapping from `SymOp2` to the corresponding `MirAst.BinOp`. -/
def SymOp2.toMirBinOp : SymOp2 → Trusted.Rustc.V2026_06_01.MirAst.BinOp
  | .add => .add
  | .sub => .sub
  | .mul => .mul
  | .bitAnd => .bitAnd
  | .bitOr => .bitOr
  | .bitXor => .bitXor
  | .shl => .shl
  | .shr => .shr
  | .eq => .eq
  | .lt => .lt
  | .le => .le

/-- Unified width-exact `SymOp2` ↔ `MirSemantics.evalScalarBinOp` theorem across all 11 operators
    (returning `op.resultSizeBytes = 8` for arithmetic/bitwise/shift and `op.resultSizeBytes = 1`
    for `bool` comparisons `eq`/`lt`/`le`). -/
theorem evalSymOp2_eq_evalScalarBinOp_universal (op : SymOp2)
    {a b : Nat} (ha : a < word64Modulus) (hb : b < word64Modulus)
    (locals : List LocalSlot) (mem : Memory) :
    evalScalarBinOp op.toMirBinOp ⟨a, 8⟩ ⟨b, 8⟩ locals mem false =
      .ok (.scalar ⟨evalSymOp2 op a b, op.resultSizeBytes⟩) locals mem := by
  cases op
  · exact evalSymOp2_add_eq_evalScalarBinOp a b locals mem
  · exact evalSymOp2_sub_eq_evalScalarBinOp ha hb locals mem
  · exact evalSymOp2_mul_eq_evalScalarBinOp a b locals mem
  · exact evalSymOp2_bitAnd_eq_evalScalarBinOp a b locals mem
  · exact evalSymOp2_bitOr_eq_evalScalarBinOp a b locals mem
  · exact evalSymOp2_bitXor_eq_evalScalarBinOp a b locals mem
  · exact evalSymOp2_shl_eq_evalScalarBinOp a b locals mem
  · exact evalSymOp2_shr_eq_evalScalarBinOp a b locals mem
  · exact evalSymOp2_eq_eq_evalScalarBinOp a b locals mem
  · exact evalSymOp2_lt_eq_evalScalarBinOp a b locals mem
  · exact evalSymOp2_le_eq_evalScalarBinOp a b locals mem

/-- **Width-Exact GVN `internOp2` ↔ `MirSemantics.evalScalarBinOp` Bridge
    (`evalSymIdToMirValueSized_internOp2_eq_evalScalarBinOp`)**:
    For every `op : SymOp2` and valid child `SymId`s `a, b < tbl.nodes.length`, evaluating
    `MirSemantics.evalScalarBinOp op.toMirBinOp` on the 8-byte values of `a` and `b` produces
    `evalSymIdToMirValueSized op.resultSizeBytes` of the GVN-interned `(internOp2 tbl op a b).1`
    (`8` bytes for `u64` arithmetic/bitwise/shift, `1` byte for `bool` comparisons `eq`/`lt`/`le`). -/
theorem evalSymIdToMirValueSized_internOp2_eq_evalScalarBinOp
    {tbl : SymTable} (hValid : ValidTable tbl)
    (op : SymOp2) {a b : SymId} (ha : a < tbl.nodes.length) (hb : b < tbl.nodes.length)
    (env : SymEnv) (locals : List LocalSlot) (mem : Memory) :
    let res := internOp2 tbl op a b
    evalScalarBinOp op.toMirBinOp ⟨evalSymId tbl env a, 8⟩ ⟨evalSymId tbl env b, 8⟩
        locals mem false =
      .ok (evalSymIdToMirValueSized op.resultSizeBytes res.2 env res.1) locals mem := by
  intro res
  rw [evalSymOp2_eq_evalScalarBinOp_universal op
    (evalSymId_lt_word64 tbl env a) (evalSymId_lt_word64 tbl env b) locals mem]
  dsimp [evalSymIdToMirValueSized, res]
  rw [internOp2_eval hValid ⟨ha, hb⟩ env]

/-!
### Compositional `DWLP mirDefaultWP` / `MirSemantics` Diamond Join-Cut Combinator (`evalJoinDiamondWP`, `wpMirJoinDiamond_sound`)
-/

/-- Check whether `st : MirExecState` is at the entry (`stmtIdx == 0`) of top-level basic block
    `joinBb` (`activeCallee == none`). -/
def isAtJoinBlockEntry (joinBb : BasicBlockIdx) : MirExecState → Option MachineState
  | .running s =>
    if s.memory.activeCallee.isNone && s.frame.blockIdx == joinBb && s.frame.stmtIdx == 0 then
      some s
    else
      none
  | _ => none

theorem isAtJoinBlockEntry_eq_some
    {joinBb : BasicBlockIdx} {st : MirExecState} {sJoin : MachineState}
    (h : isAtJoinBlockEntry joinBb st = some sJoin) :
    st = .running sJoin ∧
      sJoin.memory.activeCallee = none ∧
      sJoin.frame.blockIdx = joinBb ∧
      sJoin.frame.stmtIdx = 0 := by
  cases st with
  | halted _ => cases h
  | faulted _ => cases h
  | running s =>
    dsimp [isAtJoinBlockEntry] at h
    split at h
    · rename_i hCond
      injection h with hEq
      subst hEq
      simp [Bool.and_eq_true, Option.isNone_iff_eq_none] at hCond
      exact ⟨rfl, hCond.1.1, hCond.1.2, hCond.2⟩
    · cases h

/-- Single-pass fuel-bounded symbolic WP with a compositional join-block cut at basic block
    `joinBb`: steps from `st` through prefix statements and branch terminators (`SwitchInt`
    arms), and whenever a transition lands at the entry (`stmtIdx = 0`, `activeCallee = none`)
    of `joinBb`, discharges `cut sJoin` instead of duplicating `joinBb`'s continuation across
    every incoming path. -/
def wpMirUntilJoinSym
    (fuel : Nat) (body : CapturedMir) (joinBb : BasicBlockIdx) (st : MirExecState)
    (cut : MachineState → Prop) (post : MirOutcome → Prop) : Prop :=
  match fuel with
  | 0 => False
  | fuel' + 1 =>
    evalSymNodeTree
      (fun st' =>
        match isAtJoinBlockEntry joinBb st' with
        | some sJoin => cut sJoin
        | none => wpMirUntilJoinSym fuel' body joinBb st' cut post)
      post
      (stepMirExecSymTree body st)

/-- Fuel monotonicity of `wpMirExecSym` (`omega`-free, so it stays within `{propext, Quot.sound}`). -/
theorem wpMirExecSym_mono_fuel
    {f₁ f₂ : Nat} (hle : f₁ ≤ f₂)
    {body : CapturedMir} {st : MirExecState} {post : MirOutcome → Prop}
    (h : wpMirExecSym f₁ body st post) :
    wpMirExecSym f₂ body st post := by
  induction f₁ generalizing f₂ st with
  | zero => exact False.elim h
  | succ f₁' ih =>
    cases f₂ with
    | zero => exact absurd hle (Nat.not_succ_le_zero f₁')
    | succ f₂' =>
      have hle' : f₁' ≤ f₂' := Nat.le_of_succ_le_succ hle
      unfold wpMirExecSym at h ⊢
      rw [evalSymNodeTree_eq, stepMirExecSymTree_eval, evalNodeWP_eq] at h ⊢
      cases h_step : stepMirState body st with
      | ret _ =>
        rw [h_step] at h
        exact h
      | tau st' =>
        rw [h_step] at h
        exact ih hle' h
      | vis i k =>
        rw [h_step] at h
        exact mirDefaultWP.mono (fun _ _ hw => ih hle' hw) h

theorem wpMirSym_mono_fuel
    {f₁ f₂ : Nat} (hle : f₁ ≤ f₂)
    {body : CapturedMir} {s : MachineState} {post : MirOutcome → Prop}
    (h : wpMirSym f₁ body s post) :
    wpMirSym f₂ body s post :=
  wpMirExecSym_mono_fuel hle h

/-- Compositional cut-elimination theorem for `wpMirUntilJoinSym`: combining a prefix execution
    `wpMirUntilJoinSym prefixFuel body joinBb st cut post` with a single suffix proof
    `∀ sJoin, cut sJoin → wpMirSym suffixFuel body sJoin post` yields
    `wpMirExecSym (prefixFuel + suffixFuel) body st post`. -/
theorem wpMirUntilJoinSym_to_wpMirExecSym
    {prefixFuel suffixFuel : Nat}
    {body : CapturedMir}
    {joinBb : BasicBlockIdx}
    {st : MirExecState}
    {cut : MachineState → Prop}
    {post : MirOutcome → Prop}
    (hPrefix : wpMirUntilJoinSym prefixFuel body joinBb st cut post)
    (hJoin : ∀ sJoin : MachineState, cut sJoin → wpMirSym suffixFuel body sJoin post) :
    wpMirExecSym (prefixFuel + suffixFuel) body st post := by
  induction prefixFuel generalizing st with
  | zero => exact False.elim hPrefix
  | succ fuel' ih =>
    rw [Nat.add_right_comm fuel' 1 suffixFuel]
    unfold wpMirUntilJoinSym at hPrefix
    unfold wpMirExecSym
    rw [evalSymNodeTree_eq, stepMirExecSymTree_eval, evalNodeWP_eq] at hPrefix ⊢
    have hStepJoin :
        ∀ st' : MirExecState,
          (match isAtJoinBlockEntry joinBb st' with
           | some sJoin => cut sJoin
           | none => wpMirUntilJoinSym fuel' body joinBb st' cut post) →
          wpMirExecSym (fuel' + suffixFuel) body st' post := by
      intro st' hCont
      cases hAt : isAtJoinBlockEntry joinBb st' with
      | some sJoin =>
        rw [hAt] at hCont
        rcases isAtJoinBlockEntry_eq_some hAt with ⟨rfl, _, _, _⟩
        exact wpMirExecSym_mono_fuel (Nat.le_add_left suffixFuel fuel') (hJoin sJoin hCont)
      | none =>
        rw [hAt] at hCont
        exact ih hCont
    cases h_step : stepMirState body st with
    | ret _ =>
      rw [h_step] at hPrefix
      exact hPrefix
    | tau st' =>
      rw [h_step] at hPrefix
      exact hStepJoin st' hPrefix
    | vis i k =>
      rw [h_step] at hPrefix
      exact mirDefaultWP.mono (fun o _ hw => hStepJoin (k o) hw) hPrefix

/-- Coinductive `DWLP mirDefaultWP` soundness of `wpMirUntilJoinSym`: if `wpMirUntilJoinSym`
    holds up to `joinBb` with cut predicate `cut`, and every `sJoin` satisfying `cut` satisfies
    `DWLP mirDefaultWP (mirTree body sJoin)`, then `DWLP mirDefaultWP` holds from `st`. -/
theorem dwlp_of_wpMirUntilJoinSym
    {fuel : Nat}
    {body : CapturedMir}
    {joinBb : BasicBlockIdx}
    {st : MirExecState}
    {cut : MachineState → Prop}
    {post : MirOutcome → Prop}
    (hPrefix : wpMirUntilJoinSym fuel body joinBb st cut post)
    (hJoin :
      ∀ sJoin : MachineState,
        cut sJoin →
        DWLP mirDefaultWP (mirTree body sJoin) (fun out _ => post out) PUnit.unit) :
    DWLP mirDefaultWP (ITree.cofix (stepMirState body) st) (fun out _ => post out) PUnit.unit := by
  induction fuel generalizing st with
  | zero => exact False.elim hPrefix
  | succ fuel' ih =>
    unfold wpMirUntilJoinSym at hPrefix
    rw [evalSymNodeTree_eq, stepMirExecSymTree_eval, evalNodeWP_eq] at hPrefix
    have hStepJoin :
        ∀ st' : MirExecState,
          (match isAtJoinBlockEntry joinBb st' with
           | some sJoin => cut sJoin
           | none => wpMirUntilJoinSym fuel' body joinBb st' cut post) →
          DWLP mirDefaultWP (ITree.cofix (stepMirState body) st')
            (fun out _ => post out) PUnit.unit := by
      intro st' hCont
      cases hAt : isAtJoinBlockEntry joinBb st' with
      | some sJoin =>
        rw [hAt] at hCont
        rcases isAtJoinBlockEntry_eq_some hAt with ⟨rfl, _, _, _⟩
        exact hJoin sJoin hCont
      | none =>
        rw [hAt] at hCont
        exact ih hCont
    rw [DWLP.unfold_eq, ITree.observe_cofix]
    cases h_step : stepMirState body st with
    | ret out =>
      rw [h_step] at hPrefix
      dsimp only [ITreeF.map]
      exact hPrefix
    | tau st' =>
      rw [h_step] at hPrefix
      dsimp only [ITreeF.map]
      exact hStepJoin st' hPrefix
    | vis i k =>
      rw [h_step] at hPrefix
      dsimp only [ITreeF.map]
      exact mirDefaultWP.mono (fun o _ hw => hStepJoin (k o) hw) hPrefix

/-- Merge two `MirSemantics.LocalSlot`s reaching a join block from the two `SwitchInt` arms, under an
    **untrusted** per-slot hint `differs` (the production-semantics analogue of `JoinHints`):
    - `differs = false`: the arms are expected to agree on this slot, which is kept **verbatim** from
      the `then` arm (no `ite`, so the join continuation sees exactly the shared value);
    - `differs = true`:
      1. when both arms hold initialized scalars of the same width (`Nat.beq scT.sizeBytes scF.sizeBytes`),
         the merged slot pushes `if cond` **inside** `ScalarInt.bits`, so `evalOperand` / `evalRvalue` in
         the join block see a single `.init (.scalar ⟨_, sz⟩)` constructor and never re-split on `cond`;
      2. when the arms differ in slot kind or width (e.g., a branch-local scratch temporary `_3` left
         `.init` or `.uninit` in one arm and `.dead` in the other), the merged slot places
         `if cond then sT else sF` at that slot index. A join block that never reads that slot, or
         overwrites it first, still steps once by `rfl`: `StorageLive`/`StorageDead` only check that
         the slot index exists (`get?`) and never inspect the slot's value. A join block that *reads*
         such a slot cannot be discharged by evaluation for a symbolic `cond` (the read is stuck on
         the `ite`), and faults for every concrete `cond` that selects a dead/uninitialized arm
         (`mirJoinAsymmetricScratch_read_dead_slot3_rejected`).
    The hint is never trusted: `mergeMirJoinState_eq_ite` only fires under `MirArmsAgree`, and the
    join cut (`evalJoinDiamondWP`) independently checks that each arm reaches the merged state. -/
def mergeMirScalarSlot (cond differs : Bool) (sT sF : LocalSlot) : LocalSlot :=
  match differs, sT, sF with
  | false, _, _ => sT
  | true, .init (.scalar scT), .init (.scalar scF) =>
    if Nat.beq scT.sizeBytes scF.sizeBytes then
      .init (.scalar { bits := if cond then scT.bits else scF.bits, sizeBytes := scT.sizeBytes })
    else
      if cond then sT else sF
  | true, _, _ => if cond then sT else sF

/-- Pointwise hint-driven merge of two `List LocalSlot` local stores; slots beyond the hint list
    are kept verbatim from the `then` arm. -/
def mergeMirLocalSlots (cond : Bool) : List Bool → List LocalSlot → List LocalSlot → List LocalSlot
  | d :: ds, sT :: restT, sF :: restF =>
    mergeMirScalarSlot cond d sT sF :: mergeMirLocalSlots cond ds restT restF
  | _, lT, _ => lT

/-- Merge two `MachineState`s `(sT, sF)` arriving at the same join block entry under `cond`. The
    control point (`blockIdx`, `stmtIdx`) and the `Memory` are taken from `sT` **without** an `ite`:
    an `if cond then 3 else 3` block index or an `ite` over memories would block every later
    `stepMirState` reduction on a symbolic `cond`. `MirArmsAgree` is exactly the side condition
    under which the merge is the state-level `if cond then sT else sF` (`mergeMirJoinState_eq_ite`). -/
def mergeMirJoinState (cond : Bool) (differs : List Bool) (sT sF : MachineState) : MachineState :=
  { frame :=
      { blockIdx := sT.frame.blockIdx
        stmtIdx := sT.frame.stmtIdx
        locals := mergeMirLocalSlots cond differs sT.frame.locals sF.frame.locals }
    memory := sT.memory }

/-- Per-slot arm agreement demanded by the `differs` hint: equal slots when `differs = false`,
    unrestricted when `differs = true` (equal-width scalars fold `if cond` into `ScalarInt.bits`;
    diverging dead/scratch slots fold `if cond` into that single `LocalSlot`). -/
def MirArmSlotAgree (differs : Bool) (sT sF : LocalSlot) : Prop :=
  match differs with
  | false => sT = sF
  | true => True

/-- Pointwise `MirArmSlotAgree`; slots beyond the hint list must be equal. -/
def MirArmSlotsAgree : List Bool → List LocalSlot → List LocalSlot → Prop
  | d :: ds, sT :: restT, sF :: restF => MirArmSlotAgree d sT sF ∧ MirArmSlotsAgree ds restT restF
  | _, lT, lF => lT = lF

/-- The two arm states agree on the control point, on the whole `Memory`, and on every local
    outside the hinted `differs` slots. -/
structure MirArmsAgree (differs : List Bool) (sT sF : MachineState) : Prop where
  blockIdx : sT.frame.blockIdx = sF.frame.blockIdx
  stmtIdx : sT.frame.stmtIdx = sF.frame.stmtIdx
  memory : sT.memory = sF.memory
  locals : MirArmSlotsAgree differs sT.frame.locals sF.frame.locals

theorem mergeMirScalarSlot_true (d : Bool) (sT sF : LocalSlot) :
    mergeMirScalarSlot true d sT sF = sT := by
  cases d with
  | false => rfl
  | true =>
    cases sT with
    | dead => rfl
    | uninit => rfl
    | init vT =>
      cases vT with
      | scalar scT =>
        cases sF with
        | dead => rfl
        | uninit => rfl
        | init vF =>
          cases vF with
          | scalar scF =>
            dsimp [mergeMirScalarSlot]
            cases Nat.beq scT.sizeBytes scF.sizeBytes <;> rfl
          | _ => rfl
      | _ => rfl

theorem mergeMirScalarSlot_false {d : Bool} {sT sF : LocalSlot} (h : MirArmSlotAgree d sT sF) :
    mergeMirScalarSlot false d sT sF = sF := by
  cases d with
  | false => exact h
  | true =>
    cases sT with
    | dead => rfl
    | uninit => rfl
    | init vT =>
      cases vT with
      | scalar scT =>
        cases sF with
        | dead => rfl
        | uninit => rfl
        | init vF =>
          cases vF with
          | scalar scF =>
            dsimp [mergeMirScalarSlot]
            cases hSz : Nat.beq scT.sizeBytes scF.sizeBytes with
            | false => rfl
            | true =>
              rcases scF with ⟨bitsF, szF⟩
              have hEq : scT.sizeBytes = szF := (nat_beq_eq_true_iff _ _).1 hSz
              rw [hEq]
              rfl
          | _ => rfl
      | _ => rfl

theorem mergeMirScalarSlot_self (cond d : Bool) (s : LocalSlot) :
    mergeMirScalarSlot cond d s s = s := by
  cases cond with
  | false =>
    cases d with
    | false => rfl
    | true => exact mergeMirScalarSlot_false (d := true) trivial
  | true => exact mergeMirScalarSlot_true d s s

theorem mergeMirLocalSlots_true :
    ∀ (ds : List Bool) (lT lF : List LocalSlot), mergeMirLocalSlots true ds lT lF = lT
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl
  | _ :: _, _ :: _, [] => rfl
  | d :: ds, sT :: restT, sF :: restF => by
    show mergeMirScalarSlot true d sT sF :: mergeMirLocalSlots true ds restT restF = sT :: restT
    rw [mergeMirScalarSlot_true, mergeMirLocalSlots_true ds restT restF]

theorem mergeMirLocalSlots_false :
    ∀ {ds : List Bool} {lT lF : List LocalSlot}, MirArmSlotsAgree ds lT lF →
      mergeMirLocalSlots false ds lT lF = lF
  | [], _, _, h => h
  | _ :: _, [], _, h => h
  | _ :: _, _ :: _, [], h => h
  | _ :: _, _ :: _, _ :: _, h => by
    show mergeMirScalarSlot false _ _ _ :: mergeMirLocalSlots false _ _ _ = _ :: _
    rw [mergeMirScalarSlot_false h.1, mergeMirLocalSlots_false h.2]

theorem mergeMirLocalSlots_self (cond : Bool) :
    ∀ (ds : List Bool) (ls : List LocalSlot), mergeMirLocalSlots cond ds ls ls = ls
  | [], _ => rfl
  | _ :: _, [] => rfl
  | d :: ds, s :: rest => by
    show mergeMirScalarSlot cond d s s :: mergeMirLocalSlots cond ds rest rest = s :: rest
    rw [mergeMirScalarSlot_self, mergeMirLocalSlots_self cond ds rest]

theorem mergeMirJoinState_true (ds : List Bool) (sT sF : MachineState) :
    mergeMirJoinState true ds sT sF = sT := by
  rcases sT with ⟨⟨bbT, stT, locT⟩, memT⟩
  show MachineState.mk ⟨bbT, stT, mergeMirLocalSlots true ds locT sF.frame.locals⟩ memT = _
  rw [mergeMirLocalSlots_true]

theorem mergeMirJoinState_false {ds : List Bool} {sT sF : MachineState}
    (h : MirArmsAgree ds sT sF) :
    mergeMirJoinState false ds sT sF = sF := by
  rcases sT with ⟨⟨bbT, stT, locT⟩, memT⟩
  rcases sF with ⟨⟨bbF, stF, locF⟩, memF⟩
  rcases h with ⟨hBb, hSt, hMem, hLoc⟩
  dsimp only at hBb hSt hMem hLoc
  subst hBb hSt hMem
  show MachineState.mk ⟨bbT, stT, mergeMirLocalSlots false ds locT locF⟩ memT = _
  rw [mergeMirLocalSlots_false hLoc]

/-- Under `MirArmsAgree`, the hint-driven merge **is** the state-level `if cond then sT else sF`
    (for both values of `cond`), yet, unlike that `ite`, it reduces structurally for a symbolic
    `cond`, so a join continuation can be evaluated once on it. -/
theorem mergeMirJoinState_eq_ite {cond : Bool} {ds : List Bool} {sT sF : MachineState}
    (h : MirArmsAgree ds sT sF) :
    mergeMirJoinState cond ds sT sF = if cond then sT else sF := by
  cases cond with
  | false => exact mergeMirJoinState_false h
  | true => exact mergeMirJoinState_true ds sT sF

theorem mergeMirJoinState_self (cond : Bool) (ds : List Bool) (s : MachineState) :
    mergeMirJoinState cond ds s s = s := by
  rcases s with ⟨⟨bb, st, loc⟩, mem⟩
  show MachineState.mk ⟨bb, st, mergeMirLocalSlots cond ds loc loc⟩ mem = _
  rw [mergeMirLocalSlots_self]

/-- Production `MirSemantics` / `DWLP mirDefaultWP` diamond join-cut combinator
    (`evalJoinDiamondWP`):
    1. Steps `body` from `s` up to the join basic block entry `(joinBb, 0)` via
       `wpMirUntilJoinSym prefixFuel body joinBb (.running s) (fun s' => s' = sJoin) post`,
       verifying that both `SwitchInt` branches reach the single merged join state `sJoin`
       (e.g., via canonicalized dead temporaries or `mergeMirJoinState`), and
    2. Proves the continuation from `joinBb` **once** on `sJoin` via
       `wpMirSym suffixFuel body sJoin post`. -/
def evalJoinDiamondWP
    (prefixFuel suffixFuel : Nat)
    (body : CapturedMir)
    (joinBb : BasicBlockIdx)
    (s sJoin : MachineState)
    (post : MirOutcome → Prop) : Prop :=
  wpMirUntilJoinSym prefixFuel body joinBb (.running s) (fun s' => s' = sJoin) post ∧
    wpMirSym suffixFuel body sJoin post

/-- `evalJoinDiamondWP` implies `wpMirSym (prefixFuel + suffixFuel) body s post`. -/
theorem wpMirSym_of_evalJoinDiamondWP
    {prefixFuel suffixFuel : Nat}
    {body : CapturedMir}
    {joinBb : BasicBlockIdx}
    {s sJoin : MachineState}
    {post : MirOutcome → Prop}
    (h : evalJoinDiamondWP prefixFuel suffixFuel body joinBb s sJoin post) :
    wpMirSym (prefixFuel + suffixFuel) body s post :=
  wpMirUntilJoinSym_to_wpMirExecSym h.1 (fun _ hEq => hEq ▸ h.2)

/-- Total-correctness (`DWP mirDefaultWP`) soundness of `evalJoinDiamondWP`. -/
theorem dwpMirJoinDiamond_sound
    {prefixFuel suffixFuel : Nat}
    {body : CapturedMir}
    {joinBb : BasicBlockIdx}
    {s sJoin : MachineState}
    {post : MirOutcome → Prop}
    (h : evalJoinDiamondWP prefixFuel suffixFuel body joinBb s sJoin post) :
    DWP mirDefaultWP (mirTree body s) (fun out _ => post out) PUnit.unit :=
  dwp_of_wpMirSym (wpMirSym_of_evalJoinDiamondWP h)

/-- **Compositional `DWLP mirDefaultWP` Diamond Join-Cut Soundness (`wpMirJoinDiamond_sound`)**:
    When both `SwitchInt` arms step to the join block `joinBb` with states matching `sJoin`,
    proving the suffix `wpMirSym suffixFuel body sJoin post` **once** on `sJoin` discharges
    `DWLP mirDefaultWP (mirTree body s)` without duplicating `joinBb` across branches. -/
theorem wpMirJoinDiamond_sound
    {prefixFuel suffixFuel : Nat}
    {body : CapturedMir}
    {joinBb : BasicBlockIdx}
    {s sJoin : MachineState}
    {post : MirOutcome → Prop}
    (h : evalJoinDiamondWP prefixFuel suffixFuel body joinBb s sJoin post) :
    DWLP mirDefaultWP (mirTree body s) (fun out _ => post out) PUnit.unit :=
  (dwpMirJoinDiamond_sound h).toDWLP

/-- Coinductive `DWLP mirDefaultWP` variant of `wpMirJoinDiamond_sound` taking a direct
    `DWLP mirDefaultWP (mirTree body sJoin)` continuation hypothesis at `joinBb`. -/
theorem wpMirJoinDiamond_dwlp_sound
    {prefixFuel : Nat}
    {body : CapturedMir}
    {joinBb : BasicBlockIdx}
    {s sJoin : MachineState}
    {post : MirOutcome → Prop}
    (hPrefix : wpMirUntilJoinSym prefixFuel body joinBb (.running s) (fun s' => s' = sJoin) post)
    (hJoin : DWLP mirDefaultWP (mirTree body sJoin) (fun out _ => post out) PUnit.unit) :
    DWLP mirDefaultWP (mirTree body s) (fun out _ => post out) PUnit.unit :=
  dwlp_of_wpMirUntilJoinSym hPrefix (fun _ hEq => hEq ▸ hJoin)

/-- **Hint-driven merged diamond join cut (`wpMirJoinDiamond_merge_sound`)**: if the prefix from `s`
    reaches the join entry in the state-level `if cond then sT else sF` (each `SwitchInt` arm reaches
    its own natural arm state), the arms agree outside the untrusted `differs` hint
    (`MirArmsAgree`), and the join continuation holds **once** on the structurally merged state
    `mergeMirJoinState cond differs sT sF` (in which hinted equal-width scalar slots carry
    `if cond then _ else _` bits and hinted dead/scratch slots carry `if cond then sT[i] else sF[i]`),
    then `evalJoinDiamondWP` holds for that merged state; hence
    (`wpMirSym_of_evalJoinDiamondWP` / `wpMirJoinDiamond_sound`) the whole diamond is verified
    without evaluating the join block twice. A wrong hint can only make `MirArmsAgree` or `hJoin`
    unprovable (`mirJoinDiamond_unhinted_merge_rejected`,
    `mirJoinAsymmetricScratch_read_dead_slot3_rejected`), never unsound. -/
theorem wpMirJoinDiamond_merge_sound
    {prefixFuel suffixFuel : Nat} {body : CapturedMir} {joinBb : BasicBlockIdx}
    {s : MachineState} {cond : Bool} {differs : List Bool} {sT sF : MachineState}
    {post : MirOutcome → Prop}
    (hPrefix : wpMirUntilJoinSym prefixFuel body joinBb (.running s)
      (fun s' => s' = if cond then sT else sF) post)
    (hAgree : MirArmsAgree differs sT sF)
    (hJoin : wpMirSym suffixFuel body (mergeMirJoinState cond differs sT sF) post) :
    evalJoinDiamondWP prefixFuel suffixFuel body joinBb s
      (mergeMirJoinState cond differs sT sF) post := by
  rw [mergeMirJoinState_eq_ite hAgree] at hJoin ⊢
  exact ⟨hPrefix, hJoin⟩

/-- Coinductive `DWLP mirDefaultWP` form of `wpMirJoinDiamond_merge_sound`. -/
theorem wpMirJoinDiamond_merge_dwlp_sound
    {prefixFuel : Nat} {body : CapturedMir} {joinBb : BasicBlockIdx}
    {s : MachineState} {cond : Bool} {differs : List Bool} {sT sF : MachineState}
    {post : MirOutcome → Prop}
    (hPrefix : wpMirUntilJoinSym prefixFuel body joinBb (.running s)
      (fun s' => s' = if cond then sT else sF) post)
    (hAgree : MirArmsAgree differs sT sF)
    (hJoin : DWLP mirDefaultWP (mirTree body (mergeMirJoinState cond differs sT sF))
      (fun out _ => post out) PUnit.unit) :
    DWLP mirDefaultWP (mirTree body s) (fun out _ => post out) PUnit.unit := by
  rw [mergeMirJoinState_eq_ite hAgree] at hJoin
  exact wpMirJoinDiamond_dwlp_sound hPrefix hJoin

/-- Hint-driven merge of two `MirSemantics.Memory` states at a join block:
    `callerLocals` (which backs caller-owned `&mut` and `*mut` referents of a root frame) is merged
    pointwise using `mergeMirLocalSlots cond callerDiffers mT.callerLocals mF.callerLocals`,
    pushing `if cond` inside `ScalarInt.bits` of hinted caller-owned scalar referents so dereference
    reads and writes (`*p`) in the join block evaluate once without re-splitting on `cond`. -/
def mergeMirMemory (cond : Bool) (callerDiffers : List Bool) (mT mF : Memory) : Memory :=
  { mT with callerLocals := mergeMirLocalSlots cond callerDiffers mT.callerLocals mF.callerLocals }

/-- Agreement between two `MirSemantics.Memory` states outside the hinted `callerDiffers` slots of
    `callerLocals`. When `callerDiffers = []`, this is equivalent to `mT = mF`. -/
structure MirMemoryAgree (callerDiffers : List Bool) (mT mF : Memory) : Prop where
  nextAllocId : mT.nextAllocId = mF.nextAllocId
  globals : mT.globals = mF.globals
  borrows : mT.borrows = mF.borrows
  nextTag : mT.nextTag = mF.nextTag
  callees : mT.callees = mF.callees
  traitImpls : mT.traitImpls = mF.traitImpls
  callStack : mT.callStack = mF.callStack
  activeCallee : mT.activeCallee = mF.activeCallee
  activeProtectors : mT.activeProtectors = mF.activeProtectors
  nextProtector : mT.nextProtector = mF.nextProtector
  callerLocals : MirArmSlotsAgree callerDiffers mT.callerLocals mF.callerLocals
  fnPtrs : mT.fnPtrs = mF.fnPtrs
  exposedAllocIds : mT.exposedAllocIds = mF.exposedAllocIds
  rootUnwindCeiling : mT.rootUnwindCeiling = mF.rootUnwindCeiling

theorem mergeMirMemory_true (callerDiffers : List Bool) (mT mF : Memory) :
    mergeMirMemory true callerDiffers mT mF = mT := by
  rcases mT with ⟨a, g, b, nt, c, ti, cs, ac, ap, np, cl, fp, ea, ru⟩
  show Memory.mk a g b nt c ti cs ac ap np
    (mergeMirLocalSlots true callerDiffers cl mF.callerLocals) fp ea ru = _
  rw [mergeMirLocalSlots_true]

theorem mergeMirMemory_false {callerDiffers : List Bool} {mT mF : Memory}
    (h : MirMemoryAgree callerDiffers mT mF) :
    mergeMirMemory false callerDiffers mT mF = mF := by
  rcases mT with ⟨aT, gT, bT, ntT, cT, tiT, csT, acT, apT, npT, clT, fpT, eaT, ruT⟩
  rcases mF with ⟨aF, gF, bF, ntF, cF, tiF, csF, acF, apF, npF, clF, fpF, eaF, ruF⟩
  rcases h with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, hCl, h11, h12, h13⟩
  dsimp only at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 hCl h11 h12 h13
  subst h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
  show Memory.mk aT gT bT ntT cT tiT csT acT apT npT
    (mergeMirLocalSlots false callerDiffers clT clF) fpT eaT ruT = _
  rw [mergeMirLocalSlots_false hCl]

/-- Merge two `MachineState`s `(sT, sF)` arriving at the same join block entry when the arms also
    mutate caller-owned `&mut` referents in `Memory.callerLocals` (hinted by `callerDiffers`). -/
def mergeMirJoinStateWithCaller (cond : Bool) (localDiffers callerDiffers : List Bool)
    (sT sF : MachineState) : MachineState :=
  { frame :=
      { blockIdx := sT.frame.blockIdx
        stmtIdx := sT.frame.stmtIdx
        locals := mergeMirLocalSlots cond localDiffers sT.frame.locals sF.frame.locals }
    memory := mergeMirMemory cond callerDiffers sT.memory sF.memory }

/-- Arm agreement for `mergeMirJoinStateWithCaller`: control point, non-hinted frame locals, and
    non-hinted `Memory.callerLocals` (plus shared `Memory` metadata) agree. -/
structure MirArmsAgreeWithCaller (localDiffers callerDiffers : List Bool)
    (sT sF : MachineState) : Prop where
  blockIdx : sT.frame.blockIdx = sF.frame.blockIdx
  stmtIdx : sT.frame.stmtIdx = sF.frame.stmtIdx
  memory : MirMemoryAgree callerDiffers sT.memory sF.memory
  locals : MirArmSlotsAgree localDiffers sT.frame.locals sF.frame.locals

theorem mergeMirJoinStateWithCaller_eq_ite {cond : Bool} {localDiffers callerDiffers : List Bool}
    {sT sF : MachineState} (h : MirArmsAgreeWithCaller localDiffers callerDiffers sT sF) :
    mergeMirJoinStateWithCaller cond localDiffers callerDiffers sT sF =
      if cond then sT else sF := by
  cases cond with
  | true =>
    rcases sT with ⟨⟨bbT, stT, locT⟩, memT⟩
    show MachineState.mk ⟨bbT, stT, mergeMirLocalSlots true localDiffers locT sF.frame.locals⟩
      (mergeMirMemory true callerDiffers memT sF.memory) = _
    rw [mergeMirLocalSlots_true, mergeMirMemory_true]
    rfl
  | false =>
    rcases sT with ⟨⟨bbT, stT, locT⟩, memT⟩
    rcases sF with ⟨⟨bbF, stF, locF⟩, memF⟩
    rcases h with ⟨hBb, hSt, hMem, hLoc⟩
    dsimp only at hBb hSt hMem hLoc
    subst hBb hSt
    show MachineState.mk ⟨bbT, stT, mergeMirLocalSlots false localDiffers locT locF⟩
      (mergeMirMemory false callerDiffers memT memF) = _
    rw [mergeMirLocalSlots_false hLoc, mergeMirMemory_false hMem]
    rfl

/-- **Stateful (`&mut` / `Memory.callerLocals`) Merged Diamond Join Cut
    (`wpMirJoinDiamond_callerMerge_sound`)**: generalizes `wpMirJoinDiamond_merge_sound` to arms
    that write different values through `&mut` references into `Memory.callerLocals`. -/
theorem wpMirJoinDiamond_callerMerge_sound
    {prefixFuel suffixFuel : Nat} {body : CapturedMir} {joinBb : BasicBlockIdx}
    {s : MachineState} {cond : Bool} {localDiffers callerDiffers : List Bool}
    {sT sF : MachineState} {post : MirOutcome → Prop}
    (hPrefix : wpMirUntilJoinSym prefixFuel body joinBb (.running s)
      (fun s' => s' = if cond then sT else sF) post)
    (hAgree : MirArmsAgreeWithCaller localDiffers callerDiffers sT sF)
    (hJoin : wpMirSym suffixFuel body
      (mergeMirJoinStateWithCaller cond localDiffers callerDiffers sT sF) post) :
    evalJoinDiamondWP prefixFuel suffixFuel body joinBb s
      (mergeMirJoinStateWithCaller cond localDiffers callerDiffers sT sF) post := by
  rw [mergeMirJoinStateWithCaller_eq_ite hAgree] at hJoin ⊢
  exact ⟨hPrefix, hJoin⟩

theorem wpMirJoinDiamond_callerMerge_dwlp_sound
    {prefixFuel : Nat} {body : CapturedMir} {joinBb : BasicBlockIdx}
    {s : MachineState} {cond : Bool} {localDiffers callerDiffers : List Bool}
    {sT sF : MachineState} {post : MirOutcome → Prop}
    (hPrefix : wpMirUntilJoinSym prefixFuel body joinBb (.running s)
      (fun s' => s' = if cond then sT else sF) post)
    (hAgree : MirArmsAgreeWithCaller localDiffers callerDiffers sT sF)
    (hJoin : DWLP mirDefaultWP
      (mirTree body (mergeMirJoinStateWithCaller cond localDiffers callerDiffers sT sF))
      (fun out _ => post out) PUnit.unit) :
    DWLP mirDefaultWP (mirTree body s) (fun out _ => post out) PUnit.unit := by
  rw [mergeMirJoinStateWithCaller_eq_ite hAgree] at hJoin
  exact wpMirJoinDiamond_dwlp_sound hPrefix hJoin

/-- Hint-driven merge of a single `Option UInt8` byte inside a `CapturedAllocation`:
    when `differs = true` and both arms are initialized (`.some uT`, `.some uF`), pushes `if cond`
    inside `.some (if cond then uT else uF)` so `readLittleEndianBytes` / `readGlobalScalar` match
    `.some (.some byteVal)` and step through the merged allocation **once** without getting stuck on
    an outer `Option` `ite`. -/
def mergeMirAllocByte (cond differs : Bool) (bT bF : Option UInt8) : Option UInt8 :=
  match differs, bT, bF with
  | false, _, _ => bT
  | true, .some uT, .some uF => .some (if cond then uT else uF)
  | true, _, _ => if cond then bT else bF

def MirAllocByteAgree (differs : Bool) (bT bF : Option UInt8) : Prop :=
  match differs with
  | false => bT = bF
  | true => True

theorem mergeMirAllocByte_true (d : Bool) (bT bF : Option UInt8) :
    mergeMirAllocByte true d bT bF = bT := by
  cases d with
  | false => rfl
  | true =>
    cases bT with
    | none => rfl
    | some uT =>
      cases bF <;> rfl

theorem mergeMirAllocByte_false {d : Bool} {bT bF : Option UInt8} (h : MirAllocByteAgree d bT bF) :
    mergeMirAllocByte false d bT bF = bF := by
  cases d with
  | false => exact h
  | true =>
    cases bT with
    | none => rfl
    | some uT =>
      cases bF <;> rfl

def mergeMirAllocBytes (cond : Bool) :
    List Bool → List (Option UInt8) → List (Option UInt8) → List (Option UInt8)
  | d :: ds, bT :: restT, bF :: restF =>
    mergeMirAllocByte cond d bT bF :: mergeMirAllocBytes cond ds restT restF
  | _, bsT, _ => bsT

def MirAllocBytesAgree : List Bool → List (Option UInt8) → List (Option UInt8) → Prop
  | d :: ds, bT :: restT, bF :: restF =>
    MirAllocByteAgree d bT bF ∧ MirAllocBytesAgree ds restT restF
  | _, bsT, bsF => bsT = bsF

theorem mergeMirAllocBytes_true :
    ∀ (ds : List Bool) (bsT bsF : List (Option UInt8)),
      mergeMirAllocBytes true ds bsT bsF = bsT
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl
  | _ :: _, _ :: _, [] => rfl
  | d :: ds, bT :: restT, bF :: restF => by
    show mergeMirAllocByte true d bT bF :: mergeMirAllocBytes true ds restT restF = bT :: restT
    rw [mergeMirAllocByte_true, mergeMirAllocBytes_true ds restT restF]

theorem mergeMirAllocBytes_false :
    ∀ {ds : List Bool} {bsT bsF : List (Option UInt8)},
      MirAllocBytesAgree ds bsT bsF →
      mergeMirAllocBytes false ds bsT bsF = bsF
  | [], _, _, h => h
  | _ :: _, [], _, h => h
  | _ :: _, _ :: _, [], h => h
  | _ :: _, _ :: _, _ :: _, h => by
    show mergeMirAllocByte false _ _ _ :: mergeMirAllocBytes false _ _ _ = _ :: _
    rw [mergeMirAllocByte_false h.1, mergeMirAllocBytes_false h.2]

/-- Merge two `CapturedAllocation`s in `Memory.globals` using byte-level `byteDiffers` hints while
    keeping `allocId`, `relocations`, `align`, and `mutability` structurally unsplit so
    `lookupGlobalAlloc` and `checkGlobalAllocAlign` reduce by `rfl`. -/
def mergeMirGlobalAlloc (cond : Bool) (byteDiffers : List Bool)
    (aT aF : CapturedAllocation) : CapturedAllocation :=
  { aT with bytes := mergeMirAllocBytes cond byteDiffers aT.bytes aF.bytes }

structure MirGlobalAllocAgree (byteDiffers : List Bool) (aT aF : CapturedAllocation) : Prop where
  allocId : aT.allocId = aF.allocId
  bytes : MirAllocBytesAgree byteDiffers aT.bytes aF.bytes
  relocations : aT.relocations = aF.relocations
  align : aT.align = aF.align
  mutability : aT.mutability = aF.mutability

theorem mergeMirGlobalAlloc_true (byteDiffers : List Bool) (aT aF : CapturedAllocation) :
    mergeMirGlobalAlloc true byteDiffers aT aF = aT := by
  rcases aT with ⟨idT, bsT, relT, alT, mutT⟩
  show CapturedAllocation.mk idT (mergeMirAllocBytes true byteDiffers bsT aF.bytes) relT alT mutT = _
  rw [mergeMirAllocBytes_true]

theorem mergeMirGlobalAlloc_false {byteDiffers : List Bool} {aT aF : CapturedAllocation}
    (h : MirGlobalAllocAgree byteDiffers aT aF) :
    mergeMirGlobalAlloc false byteDiffers aT aF = aF := by
  rcases aT with ⟨idT, bsT, relT, alT, mutT⟩
  rcases aF with ⟨idF, bsF, relF, alF, mutF⟩
  rcases h with ⟨hId, hBs, hRel, hAl, hMut⟩
  dsimp only at hId hBs hRel hAl hMut
  subst hId hRel hAl hMut
  show CapturedAllocation.mk idT (mergeMirAllocBytes false byteDiffers bsT bsF) relT alT mutT = _
  rw [mergeMirAllocBytes_false hBs]

def mergeMirGlobalAllocs (cond : Bool) :
    List (List Bool) → List CapturedAllocation → List CapturedAllocation → List CapturedAllocation
  | ds :: dss, aT :: restT, aF :: restF =>
    mergeMirGlobalAlloc cond ds aT aF :: mergeMirGlobalAllocs cond dss restT restF
  | _, gsT, _ => gsT

def MirGlobalsAgree : List (List Bool) → List CapturedAllocation → List CapturedAllocation → Prop
  | ds :: dss, aT :: restT, aF :: restF =>
    MirGlobalAllocAgree ds aT aF ∧ MirGlobalsAgree dss restT restF
  | _, gsT, gsF => gsT = gsF

theorem mergeMirGlobalAllocs_true :
    ∀ (dss : List (List Bool)) (gsT gsF : List CapturedAllocation),
      mergeMirGlobalAllocs true dss gsT gsF = gsT
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl
  | _ :: _, _ :: _, [] => rfl
  | ds :: dss, aT :: restT, aF :: restF => by
    show mergeMirGlobalAlloc true ds aT aF :: mergeMirGlobalAllocs true dss restT restF = aT :: restT
    rw [mergeMirGlobalAlloc_true, mergeMirGlobalAllocs_true dss restT restF]

theorem mergeMirGlobalAllocs_false :
    ∀ {dss : List (List Bool)} {gsT gsF : List CapturedAllocation},
      MirGlobalsAgree dss gsT gsF →
      mergeMirGlobalAllocs false dss gsT gsF = gsF
  | [], _, _, h => h
  | _ :: _, [], _, h => h
  | _ :: _, _ :: _, [], h => h
  | _ :: _, _ :: _, _ :: _, h => by
    show mergeMirGlobalAlloc false _ _ _ :: mergeMirGlobalAllocs false _ _ _ = _ :: _
    rw [mergeMirGlobalAlloc_false h.1, mergeMirGlobalAllocs_false h.2]

/-- Merge two suspended caller frames in `Memory.callStack` using `slotDiffers` hints on
    `SavedCallerFrame.frame.locals` (for inlined callees that write through `&mut` into a parent
    caller frame on the stack). -/
def mergeMirSavedCallerFrame (cond : Bool) (slotDiffers : List Bool)
    (fT fF : SavedCallerFrame) : SavedCallerFrame :=
  { fT with
    frame :=
      { fT.frame with
        locals := mergeMirLocalSlots cond slotDiffers fT.frame.locals fF.frame.locals } }

structure MirSavedCallerFrameAgree (slotDiffers : List Bool)
    (fT fF : SavedCallerFrame) : Prop where
  callerBody : fT.callerBody = fF.callerBody
  blockIdx : fT.frame.blockIdx = fF.frame.blockIdx
  stmtIdx : fT.frame.stmtIdx = fF.frame.stmtIdx
  locals : MirArmSlotsAgree slotDiffers fT.frame.locals fF.frame.locals
  destination : fT.destination = fF.destination
  returnTarget : fT.returnTarget = fF.returnTarget
  callerProtector : fT.callerProtector = fF.callerProtector
  calleeProtectors : fT.calleeProtectors = fF.calleeProtectors
  returnUnwind : fT.returnUnwind = fF.returnUnwind
  isDiverging : fT.isDiverging = fF.isDiverging

theorem mergeMirSavedCallerFrame_true (slotDiffers : List Bool) (fT fF : SavedCallerFrame) :
    mergeMirSavedCallerFrame true slotDiffers fT fF = fT := by
  rcases fT with ⟨cb, ⟨bb, st, loc⟩, dst, rt, cp, clp, ru, idv⟩
  show SavedCallerFrame.mk cb
    ⟨bb, st, mergeMirLocalSlots true slotDiffers loc fF.frame.locals⟩
    dst rt cp clp ru idv = _
  rw [mergeMirLocalSlots_true]

theorem mergeMirSavedCallerFrame_false {slotDiffers : List Bool} {fT fF : SavedCallerFrame}
    (h : MirSavedCallerFrameAgree slotDiffers fT fF) :
    mergeMirSavedCallerFrame false slotDiffers fT fF = fF := by
  rcases fT with ⟨cbT, ⟨bbT, stT, locT⟩, dstT, rtT, cpT, clpT, ruT, idvT⟩
  rcases fF with ⟨cbF, ⟨bbF, stF, locF⟩, dstF, rtF, cpF, clpF, ruF, idvF⟩
  rcases h with ⟨hCb, hBb, hSt, hLoc, hDst, hRt, hCp, hClp, hRu, hIdv⟩
  dsimp only at hCb hBb hSt hLoc hDst hRt hCp hClp hRu hIdv
  subst hCb hBb hSt hDst hRt hCp hClp hRu hIdv
  show SavedCallerFrame.mk cbT
    ⟨bbT, stT, mergeMirLocalSlots false slotDiffers locT locF⟩
    dstT rtT cpT clpT ruT idvT = _
  rw [mergeMirLocalSlots_false hLoc]

def mergeMirCallStack (cond : Bool) :
    List (List Bool) → List SavedCallerFrame → List SavedCallerFrame → List SavedCallerFrame
  | ds :: dss, fT :: restT, fF :: restF =>
    mergeMirSavedCallerFrame cond ds fT fF :: mergeMirCallStack cond dss restT restF
  | _, csT, _ => csT

def MirCallStackAgree : List (List Bool) → List SavedCallerFrame → List SavedCallerFrame → Prop
  | ds :: dss, fT :: restT, fF :: restF =>
    MirSavedCallerFrameAgree ds fT fF ∧ MirCallStackAgree dss restT restF
  | _, csT, csF => csT = csF

theorem mergeMirCallStack_true :
    ∀ (dss : List (List Bool)) (csT csF : List SavedCallerFrame),
      mergeMirCallStack true dss csT csF = csT
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl
  | _ :: _, _ :: _, [] => rfl
  | ds :: dss, fT :: restT, fF :: restF => by
    show mergeMirSavedCallerFrame true ds fT fF :: mergeMirCallStack true dss restT restF = fT :: restT
    rw [mergeMirSavedCallerFrame_true, mergeMirCallStack_true dss restT restF]

theorem mergeMirCallStack_false :
    ∀ {dss : List (List Bool)} {csT csF : List SavedCallerFrame},
      MirCallStackAgree dss csT csF →
      mergeMirCallStack false dss csT csF = csF
  | [], _, _, h => h
  | _ :: _, [], _, h => h
  | _ :: _, _ :: _, [], h => h
  | _ :: _, _ :: _, _ :: _, h => by
    show mergeMirSavedCallerFrame false _ _ _ :: mergeMirCallStack false _ _ _ = _ :: _
    rw [mergeMirSavedCallerFrame_false h.1, mergeMirCallStack_false h.2]

/-- Unified hint-driven merge of two `MirSemantics.Memory` states covering:
    - `callerLocals` (root-frame caller-owned `&mut` / `*mut` referents),
    - `globals` (global/static/heap `CapturedAllocation` byte arrays), and
    - `callStack` (suspended caller frames during inlined calls). -/
def mergeMirMemoryFull (cond : Bool) (callerDiffers : List Bool)
    (globalDiffers : List (List Bool) := []) (stackDiffers : List (List Bool) := [])
    (mT mF : Memory) : Memory :=
  { mT with
    globals := mergeMirGlobalAllocs cond globalDiffers mT.globals mF.globals
    callStack := mergeMirCallStack cond stackDiffers mT.callStack mF.callStack
    callerLocals := mergeMirLocalSlots cond callerDiffers mT.callerLocals mF.callerLocals }

structure MirMemoryAgreeFull (callerDiffers : List Bool)
    (globalDiffers : List (List Bool) := []) (stackDiffers : List (List Bool) := [])
    (mT mF : Memory) : Prop where
  nextAllocId : mT.nextAllocId = mF.nextAllocId
  globals : MirGlobalsAgree globalDiffers mT.globals mF.globals
  borrows : mT.borrows = mF.borrows
  nextTag : mT.nextTag = mF.nextTag
  callees : mT.callees = mF.callees
  traitImpls : mT.traitImpls = mF.traitImpls
  callStack : MirCallStackAgree stackDiffers mT.callStack mF.callStack
  activeCallee : mT.activeCallee = mF.activeCallee
  activeProtectors : mT.activeProtectors = mF.activeProtectors
  nextProtector : mT.nextProtector = mF.nextProtector
  callerLocals : MirArmSlotsAgree callerDiffers mT.callerLocals mF.callerLocals
  fnPtrs : mT.fnPtrs = mF.fnPtrs
  exposedAllocIds : mT.exposedAllocIds = mF.exposedAllocIds
  rootUnwindCeiling : mT.rootUnwindCeiling = mF.rootUnwindCeiling

theorem mergeMirMemoryFull_true (callerDiffers : List Bool)
    (globalDiffers stackDiffers : List (List Bool)) (mT mF : Memory) :
    mergeMirMemoryFull true callerDiffers globalDiffers stackDiffers mT mF = mT := by
  rcases mT with ⟨a, g, b, nt, c, ti, cs, ac, ap, np, cl, fp, ea, ru⟩
  show Memory.mk a (mergeMirGlobalAllocs true globalDiffers g mF.globals) b nt c ti
    (mergeMirCallStack true stackDiffers cs mF.callStack) ac ap np
    (mergeMirLocalSlots true callerDiffers cl mF.callerLocals) fp ea ru = _
  rw [mergeMirGlobalAllocs_true, mergeMirCallStack_true, mergeMirLocalSlots_true]

theorem mergeMirMemoryFull_false {callerDiffers : List Bool}
    {globalDiffers stackDiffers : List (List Bool)} {mT mF : Memory}
    (h : MirMemoryAgreeFull callerDiffers globalDiffers stackDiffers mT mF) :
    mergeMirMemoryFull false callerDiffers globalDiffers stackDiffers mT mF = mF := by
  rcases mT with ⟨aT, gT, bT, ntT, cT, tiT, csT, acT, apT, npT, clT, fpT, eaT, ruT⟩
  rcases mF with ⟨aF, gF, bF, ntF, cF, tiF, csF, acF, apF, npF, clF, fpF, eaF, ruF⟩
  rcases h with ⟨h1, hG, h3, h4, h5, h6, hCs, h8, h9, h10, hCl, h11, h12, h13⟩
  dsimp only at h1 hG h3 h4 h5 h6 hCs h8 h9 h10 hCl h11 h12 h13
  subst h1 h3 h4 h5 h6 h8 h9 h10 h11 h12 h13
  show Memory.mk aT (mergeMirGlobalAllocs false globalDiffers gT gF) bT ntT cT tiT
    (mergeMirCallStack false stackDiffers csT csF) acT apT npT
    (mergeMirLocalSlots false callerDiffers clT clF) fpT eaT ruT = _
  rw [mergeMirGlobalAllocs_false hG, mergeMirCallStack_false hCs, mergeMirLocalSlots_false hCl]

def mergeMirJoinStateFull (cond : Bool) (localDiffers callerDiffers : List Bool)
    (globalDiffers : List (List Bool) := []) (stackDiffers : List (List Bool) := [])
    (sT sF : MachineState) : MachineState :=
  { frame :=
      { blockIdx := sT.frame.blockIdx
        stmtIdx := sT.frame.stmtIdx
        locals := mergeMirLocalSlots cond localDiffers sT.frame.locals sF.frame.locals }
    memory := mergeMirMemoryFull cond callerDiffers globalDiffers stackDiffers sT.memory sF.memory }

structure MirArmsAgreeFull (localDiffers callerDiffers : List Bool)
    (globalDiffers : List (List Bool) := []) (stackDiffers : List (List Bool) := [])
    (sT sF : MachineState) : Prop where
  blockIdx : sT.frame.blockIdx = sF.frame.blockIdx
  stmtIdx : sT.frame.stmtIdx = sF.frame.stmtIdx
  memory : MirMemoryAgreeFull callerDiffers globalDiffers stackDiffers sT.memory sF.memory
  locals : MirArmSlotsAgree localDiffers sT.frame.locals sF.frame.locals

theorem mergeMirJoinStateFull_eq_ite {cond : Bool} {localDiffers callerDiffers : List Bool}
    {globalDiffers stackDiffers : List (List Bool)} {sT sF : MachineState}
    (h : MirArmsAgreeFull localDiffers callerDiffers globalDiffers stackDiffers sT sF) :
    mergeMirJoinStateFull cond localDiffers callerDiffers globalDiffers stackDiffers sT sF =
      if cond then sT else sF := by
  cases cond with
  | true =>
    rcases sT with ⟨⟨bbT, stT, locT⟩, memT⟩
    show MachineState.mk ⟨bbT, stT, mergeMirLocalSlots true localDiffers locT sF.frame.locals⟩
      (mergeMirMemoryFull true callerDiffers globalDiffers stackDiffers memT sF.memory) = _
    rw [mergeMirLocalSlots_true, mergeMirMemoryFull_true]
    rfl
  | false =>
    rcases sT with ⟨⟨bbT, stT, locT⟩, memT⟩
    rcases sF with ⟨⟨bbF, stF, locF⟩, memF⟩
    rcases h with ⟨hBb, hSt, hMem, hLoc⟩
    dsimp only at hBb hSt hMem hLoc
    subst hBb hSt
    show MachineState.mk ⟨bbT, stT, mergeMirLocalSlots false localDiffers locT locF⟩
      (mergeMirMemoryFull false callerDiffers globalDiffers stackDiffers memT memF) = _
    rw [mergeMirLocalSlots_false hLoc, mergeMirMemoryFull_false hMem]
    rfl

/-- **Full-Memory (`callerLocals` + `globals` + `callStack`) Merged Diamond Join Cut
    (`wpMirJoinDiamond_fullMemoryMerge_sound`)**: generalizes `wpMirJoinDiamond_callerMerge_sound`
    to arms that also diverge in `Memory.globals` (`CapturedAllocation` bytes) and/or
    `Memory.callStack` (`SavedCallerFrame` locals). -/
theorem wpMirJoinDiamond_fullMemoryMerge_sound
    {prefixFuel suffixFuel : Nat} {body : CapturedMir} {joinBb : BasicBlockIdx}
    {s : MachineState} {cond : Bool} {localDiffers callerDiffers : List Bool}
    {globalDiffers stackDiffers : List (List Bool)}
    {sT sF : MachineState} {post : MirOutcome → Prop}
    (hPrefix : wpMirUntilJoinSym prefixFuel body joinBb (.running s)
      (fun s' => s' = if cond then sT else sF) post)
    (hAgree : MirArmsAgreeFull localDiffers callerDiffers globalDiffers stackDiffers sT sF)
    (hJoin : wpMirSym suffixFuel body
      (mergeMirJoinStateFull cond localDiffers callerDiffers globalDiffers stackDiffers sT sF) post) :
    evalJoinDiamondWP prefixFuel suffixFuel body joinBb s
      (mergeMirJoinStateFull cond localDiffers callerDiffers globalDiffers stackDiffers sT sF) post := by
  rw [mergeMirJoinStateFull_eq_ite hAgree] at hJoin ⊢
  exact ⟨hPrefix, hJoin⟩

theorem wpMirJoinDiamond_fullMemoryMerge_dwlp_sound
    {prefixFuel : Nat} {body : CapturedMir} {joinBb : BasicBlockIdx}
    {s : MachineState} {cond : Bool} {localDiffers callerDiffers : List Bool}
    {globalDiffers stackDiffers : List (List Bool)}
    {sT sF : MachineState} {post : MirOutcome → Prop}
    (hPrefix : wpMirUntilJoinSym prefixFuel body joinBb (.running s)
      (fun s' => s' = if cond then sT else sF) post)
    (hAgree : MirArmsAgreeFull localDiffers callerDiffers globalDiffers stackDiffers sT sF)
    (hJoin : DWLP mirDefaultWP
      (mirTree body (mergeMirJoinStateFull cond localDiffers callerDiffers globalDiffers stackDiffers sT sF))
      (fun out _ => post out) PUnit.unit) :
    DWLP mirDefaultWP (mirTree body s) (fun out _ => post out) PUnit.unit := by
  rw [mergeMirJoinStateFull_eq_ite hAgree] at hJoin
  exact wpMirJoinDiamond_dwlp_sound hPrefix hJoin

/-- Right-nested invariance of `MirArmSlotsAgree`: because `mergeMirScalarSlot cond false s1 s2 = s1`
    by `rfl`, agreeing with `mergeMirLocalSlots cond ds l1 l2` is identical to agreeing with `l1`. -/
theorem MirArmSlotsAgree_merge_right (cond : Bool) :
    ∀ (ds : List Bool) (l0 l1 l2 : List LocalSlot),
      MirArmSlotsAgree ds l0 l1 →
      MirArmSlotsAgree ds l0 (mergeMirLocalSlots cond ds l1 l2)
  | [], _, _, _, h => h
  | _ :: _, [], _, _, h => by cases h; rfl
  | _ :: _, _ :: _, [], _, h => h
  | _ :: _, _ :: _, _ :: _, [], h => h
  | false :: ds, s0 :: rest0, s1 :: rest1, s2 :: rest2, ⟨hH, hT⟩ =>
    ⟨hH, MirArmSlotsAgree_merge_right cond ds rest0 rest1 rest2 hT⟩
  | true :: ds, s0 :: rest0, s1 :: rest1, s2 :: rest2, ⟨_, hT⟩ =>
    ⟨trivial, MirArmSlotsAgree_merge_right cond ds rest0 rest1 rest2 hT⟩

/-- Right-nested invariance of `MirArmsAgree`: enables folding `mergeMirJoinState` across $N$-way
    `SwitchInt` tables (`c0 -> s0 | c1 -> s1 | _ -> s2`). -/
theorem MirArmsAgree_merge_right (cond : Bool) {ds : List Bool} {s0 s1 s2 : MachineState}
    (h01 : MirArmsAgree ds s0 s1) :
    MirArmsAgree ds s0 (mergeMirJoinState cond ds s1 s2) :=
  ⟨h01.blockIdx, h01.stmtIdx, h01.memory,
   MirArmSlotsAgree_merge_right cond ds s0.frame.locals s1.frame.locals s2.frame.locals h01.locals⟩

/-- **3-Way `SwitchInt` Merged Join Cut (`wpMirJoinSwitch3_merge_sound`)**:
    When a 3-way `SwitchInt` (`cond0 -> s0 | cond1 -> s1 | otherwise -> s2`) steps to `joinBb`,
    nesting `mergeMirJoinState` twice pushes the entire 3-way `if-else` cascade inside
    `ScalarInt.bits` and evaluates `joinBb` **once**. -/
theorem wpMirJoinSwitch3_merge_sound
    {prefixFuel suffixFuel : Nat} {body : CapturedMir} {joinBb : BasicBlockIdx}
    {s : MachineState} {cond0 cond1 : Bool} {differs : List Bool} {s0 s1 s2 : MachineState}
    {post : MirOutcome → Prop}
    (hPrefix : wpMirUntilJoinSym prefixFuel body joinBb (.running s)
      (fun s' => s' = if cond0 then s0 else if cond1 then s1 else s2) post)
    (hAgree01 : MirArmsAgree differs s0 s1)
    (hAgree12 : MirArmsAgree differs s1 s2)
    (hJoin : wpMirSym suffixFuel body
      (mergeMirJoinState cond0 differs s0 (mergeMirJoinState cond1 differs s1 s2)) post) :
    evalJoinDiamondWP prefixFuel suffixFuel body joinBb s
      (mergeMirJoinState cond0 differs s0 (mergeMirJoinState cond1 differs s1 s2)) post := by
  have hEq0 : mergeMirJoinState cond0 differs s0 (mergeMirJoinState cond1 differs s1 s2) =
      (if cond0 then s0 else if cond1 then s1 else s2) := by
    rw [mergeMirJoinState_eq_ite (MirArmsAgree_merge_right cond1 hAgree01),
      mergeMirJoinState_eq_ite hAgree12]
  rw [hEq0] at hJoin ⊢
  exact ⟨hPrefix, hJoin⟩

end Anneal.Rustc.V2026_06_01.SymbolicEval
