import Anneal.FunctionalTranslation

namespace Anneal.FunctionalTranslationTests

open Trusted.Effect
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult
open Anneal.ITreeWP
open Anneal.UnsafeObligations
open Anneal.SepLogic
open Anneal.Rustc.V2026_06_01.Lower
open Anneal.FunctionalTranslation

/-!
Kernel-checked verification test suites for `Anneal.FunctionalTranslation` over
`V2026_06_01` `CapturedMir` bodies, exercising pillars 1–3 (the Pillar 4
program-to-program refinement suite lives in `FunctionalTranslationEquivTests`):

1. **Suite 1 (Pillar 1 + Pillar 2 Diamond Joining Without Path Splitting)**:
   - Spine-preserving symbolic aggregate merging (`SymVal`, `zipSymVal`,
     `denote_zipSymVal`, `zipSymLocals`, `denote_zipSymLocals`).
   - Multi-diamond `CapturedMir` verification (`twoDiamondTupleBody`) constructing
     and projecting a `(u32, u32)` tuple across two sequential `if/else` diamonds
     over symbolic `c1 c2 : Bool` and `x : Nat` (`x < 1000`), verified via
     `TransPlan.branch` without case-splitting on `c1` or `c2`.
2. **Suite 2 (Pillar 2 Symbolic `while`-Loop Total & Coinductive Partial Verification)**:
   - Symbolic `while i < n` arithmetic-accumulation loop (`sumToNLoopBody`) over
     arbitrary `n : Nat` (`n ≤ 1000`), verified for total correctness
     (`TotalVerificationResult` and `MirTerminatesAndNoUB`) via `TransPlan.loop`
     and for partial correctness (`VerificationResult`) via
     `dwlp_mirTree_while_invariant`.
3. **Suite 3 (Pillar 3 `&mut` Lenses, `ActiveTypedMutBorrow`, and `CapturedMir` `&mut` Body)**:
   - `FrameCursor` (`pos : Nat`, `len : Nat`) pure state-update specification
     `FrameCursor.advancePure`, sub-place field lens composition
     (`LawfulMutLens.comp`), sequential update composition (`MutUpdate.seq`), and
     spatial `ActiveTypedMutBorrow` + `AgreeOnFootprint` disjoint-allocation
     framing via `memoryPtrMutLens`.
   - Symbolic verification of `advanceCursorMutMirBody` (`Rvalue.ref (.mut false)`
     + `(*_ptr).0` / `(*_ptr).1` dereference projections + conditional field
     mutation) via `MutRefLocalSpec`, `verifyMutRefLocalTotalByTransPlan`, and
     `statefulOfTotalMutRefLocal`.
-/

/-! ## Shared `V2026_06_01` `CapturedMir` AST Builders and Scalar Simplification Lemmas -/

@[reducible] private def boolMirTy : Ty := { kind := .bool, layoutIdx := 0 }
@[reducible] private def u32MirTy : Ty := { kind := .uint .u32, layoutIdx := 0 }
@[reducible] private def pairU32MirTy : Ty :=
  { kind := .tuple [.uint .u32, .uint .u32], layoutIdx := 0 }
@[reducible] private def pairU32MutRefMirTy : Ty :=
  { kind := .ref .mut (.tuple [.uint .u32, .uint .u32]), layoutIdx := 0 }
@[reducible] private def cursorRetMirTy : Ty :=
  { kind := .tuple [.tuple [.uint .u32, .uint .u32], .bool], layoutIdx := 0 }

@[reducible] private def u32ConstOp (n : Nat) : Operand :=
  .constant { ty := u32MirTy, val := .scalar (.int { bits := n, sizeBytes := 4 }) }

@[reducible] private def defaultU32Layout : TypeLayout := {
  size := { bytes := 4 }
  align := { bytes := 4 }
  backendRepr := .memory
  fields := .primitive
  variants := .single 0
  isUninhabited := false
}

@[reducible] private def defaultFnAbi : FnAbi := {
  args := []
  ret := { layout := defaultU32Layout, mode := .direct }
  conv := .rust
  canUnwind := false
}

@[reducible] private def mkDecl (mutability : Mutability) (ty : Ty) : LocalDecl :=
  { mutability, ty, debugName := none }

@[reducible] private def mkStmt (kind : StatementKind) : Statement :=
  { kind, span := "FunctionalTranslationTests.lean" }

@[reducible] private def mkTerm (kind : TerminatorKind) : Terminator :=
  { kind, span := "FunctionalTranslationTests.lean" }

@[reducible] private def mkMirBody
    (defPath : DefPath) (argCount : Nat)
    (localDecls : List LocalDecl) (basicBlocks : List BasicBlockData) :
    CapturedMir := {
  defPath, argCount, localDecls, basicBlocks
  phase := .runtimePostCleanup
  role := .subject
  fnAbi := defaultFnAbi
  layouts := emptyLayoutTable
  allocations := []
}

@[reducible] private def locPlace (idx : Local) : Place :=
  { local_ := idx, projection := [] }

/-- In-range `u32` addition: `wrapScalarBits` is the identity below `2^32`. -/
private theorem wrapU32_add {a b : Nat} (h : a + b < 4294967296) :
    wrapScalarBits (a.add b) (scalarModulus 4) = a + b :=
  wrapScalarBits_of_lt h

private theorem boolToScalar_eq (b : Bool) :
    boolToScalar b = ⟨b.toNat, 1⟩ := by
  cases b <;> rfl

private theorem not_beq_toNat_zero (b : Bool) :
    (!b.toNat.beq 0) = b := by
  cases b <;> rfl

/-- Non-dead local slot helper (`none ↦ .uninit`, `some v ↦ .init v`). -/
@[reducible] private def optSlot : Option Value → LocalSlot
  | none => .uninit
  | some v => .init v

/-! ## Suite 1: Pillar 1 Symbolic Value Merging & Multi-Diamond `TransPlan.branch` -/

/--
Direct Pillar 1 test: `zipSymVal` merges nested symbolic aggregates while keeping
every outer `.adt` constructor exposed definitionally (`rfl`), and `SymVal.denote`
commutes with `zipSymVal` without path splitting.
-/
theorem pillar1_nested_agg_zip_spine_and_denote
    (cond : Bool) (a d : Nat) (b₁ b₂ : Bool) (c e : Nat) :
    let vThen : SymVal := .adt 0 [.scalar a 4, .adt 0 [.bool b₁, .scalar c 8]]
    let vElse : SymVal := .adt 0 [.scalar d 4, .adt 0 [.bool b₂, .scalar e 8]]
    zipSymVal cond vThen vElse =
      .adt 0
        [.scalar (if cond then a else d) 4,
         .adt 0 [.bool (if cond then b₁ else b₂), .scalar (if cond then c else e) 8]] ∧
    (zipSymVal cond vThen vElse).denote =
      (if cond then vThen.denote else vElse.denote) :=
  ⟨rfl, denote_zipSymVal cond _ _⟩

/-- Direct Pillar 1 frame-level test for `zipSymLocals` and `denote_zipSymLocals`. -/
theorem pillar1_symLocals_zip_denote
    (cond : Bool) (x y : Nat) :
    let fThen : SymLocals := [.uninit, .init (.scalar (x + 10) 4), .dead]
    let fElse : SymLocals := [.uninit, .init (.scalar (y + 20) 4), .dead]
    (zipSymLocals cond fThen fElse).denote =
      (if cond then fThen.denote else fElse.denote) :=
  denote_zipSymLocals cond rfl

/--
`V2026_06_01` `CapturedMir` body with two sequential `if/else` diamonds:
```rust
fn two_diamond_tuple(c1: bool, c2: bool, x: u32) -> u32 {
    let pair: (u32, u32) = if c1 { (x + 10, x + 20) } else { (x + 1, x + 2) };
    if c2 { pair.0 } else { pair.1 }
}
```
Notice that `pair` (`_4`) is constructed separately in `bb1` and `bb2`, joined
into a single symbolic aggregate at `bb3`, and then field-projected (`_4.0` and
`_4.1`) across the second diamond (`bb4` / `bb5` → `bb6`).
-/
def twoDiamondTupleBody : CapturedMir :=
  mkMirBody "test::two_diamond_tuple" 3
    [mkDecl .mut u32MirTy,
     mkDecl .not boolMirTy,
     mkDecl .not boolMirTy,
     mkDecl .not u32MirTy,
     mkDecl .mut pairU32MirTy,
     mkDecl .mut u32MirTy,
     mkDecl .mut u32MirTy]
    [ -- bb0: switch on c1 (_1)
      { statements := [mkStmt (.storageLive 4), mkStmt (.storageLive 5), mkStmt (.storageLive 6)]
        terminator := mkTerm (.switchInt (.copy (locPlace 1))
          { branches := [(0, 2)], otherwise := 1 })
        isCleanup := false },
      -- bb1 (c1 == true): _4 = (_3 + 10, _3 + 20); goto bb3
      { statements :=
          [mkStmt (.assign (locPlace 5) (.binaryOp .add (.copy (locPlace 3)) (u32ConstOp 10))),
           mkStmt (.assign (locPlace 6) (.binaryOp .add (.copy (locPlace 3)) (u32ConstOp 20))),
           mkStmt (.assign (locPlace 4) (.aggregate .tuple
             [.copy (locPlace 5), .copy (locPlace 6)]))]
        terminator := mkTerm (.goto 3)
        isCleanup := false },
      -- bb2 (c1 == false): _4 = (_3 + 1, _3 + 2); goto bb3
      { statements :=
          [mkStmt (.assign (locPlace 5) (.binaryOp .add (.copy (locPlace 3)) (u32ConstOp 1))),
           mkStmt (.assign (locPlace 6) (.binaryOp .add (.copy (locPlace 3)) (u32ConstOp 2))),
           mkStmt (.assign (locPlace 4) (.aggregate .tuple
             [.copy (locPlace 5), .copy (locPlace 6)]))]
        terminator := mkTerm (.goto 3)
        isCleanup := false },
      -- bb3 (first join): switch on c2 (_2)
      { statements := []
        terminator := mkTerm (.switchInt (.copy (locPlace 2))
          { branches := [(0, 5)], otherwise := 4 })
        isCleanup := false },
      -- bb4 (c2 == true): _0 = _4.0; goto bb6
      { statements :=
          [mkStmt (.assign (locPlace 0)
            (.use (.copy { local_ := 4, projection := [.field 0 u32MirTy] })))]
        terminator := mkTerm (.goto 6)
        isCleanup := false },
      -- bb5 (c2 == false): _0 = _4.1; goto bb6
      { statements :=
          [mkStmt (.assign (locPlace 0)
            (.use (.copy { local_ := 4, projection := [.field 1 u32MirTy] })))]
        terminator := mkTerm (.goto 6)
        isCleanup := false },
      -- bb6 (second join): return
      { statements := []
        terminator := mkTerm .return_
        isCleanup := false } ]

/-- Pure Lean functional specification of `twoDiamondTupleBody`. -/
def twoDiamondPure (c1 c2 : Bool) (x : Nat) : Nat :=
  if c2 then (if c1 then x + 10 else x + 1) else (if c1 then x + 20 else x + 2)

/-- Two-diamond `TransPlan.branch` joining at `bb3` and `bb6`. -/
def twoDiamondPlan : TransPlan :=
  .branch 3 (.jump 3 5) (.jump 3 5)
    (.branch 6 (.jump 6 3) (.jump 6 3) (.ret 1) 1)
    4

def twoDiamondClaim : Claim where
  body := twoDiamondTupleBody
  pre args :=
    ∃ (c1 c2 : Bool) (x : Nat),
      x < 1000 ∧
      args = [.scalar (boolToScalar c1), .scalar (boolToScalar c2), .scalar ⟨x, 4⟩]
  post args retVal :=
    ∀ (c1 c2 : Bool) (x : Nat),
      args = [.scalar (boolToScalar c1), .scalar (boolToScalar c2), .scalar ⟨x, 4⟩] →
      retVal = .scalar ⟨twoDiamondPure c1 c2 x, 4⟩

def twoDiamondTotalClaim : TotalClaim where
  body := twoDiamondTupleBody
  pre args mem :=
    mem = emptyMemory ∧
    ∃ (c1 c2 : Bool) (x : Nat),
      x < 1000 ∧
      args = [.scalar (boolToScalar c1), .scalar (boolToScalar c2), .scalar ⟨x, 4⟩]
  post args _ retVal mem' :=
    mem' = emptyMemory ∧
    ∀ (c1 c2 : Bool) (x : Nat),
      args = [.scalar (boolToScalar c1), .scalar (boolToScalar c2), .scalar ⟨x, 4⟩] →
      retVal = .scalar ⟨twoDiamondPure c1 c2 x, 4⟩

/-- Injectivity of the `(c1, c2, x)` argument encoding. -/
private theorem twoDiamond_args_inj {c1 c2 c1' c2' : Bool} {x x' : Nat}
    (h : [Value.scalar (boolToScalar c1), .scalar (boolToScalar c2), .scalar ⟨x, 4⟩] =
      [.scalar (boolToScalar c1'), .scalar (boolToScalar c2'), .scalar ⟨x', 4⟩]) :
    c1 = c1' ∧ c2 = c2' ∧ x = x' := by
  cases c1 <;> cases c1' <;> cases c2 <;> cases c2' <;> cases h <;> exact ⟨rfl, rfl, rfl⟩

private def twoDiamondPreSwitchState (c1 c2 : Bool) (x : Nat) (bb : BasicBlockIdx) : MachineState :=
  { frame := {
      blockIdx := bb
      stmtIdx := 0
      locals :=
        [.uninit,
         .init (.scalar ⟨c1.toNat, 1⟩),
         .init (.scalar ⟨c2.toNat, 1⟩),
         .init (.scalar ⟨x, 4⟩),
         .uninit, .uninit, .uninit]
    }
    memory := emptyMemory }

private def twoDiamondBb3BranchState (c1 c2 : Bool) (x a b : Nat) : MachineState :=
  { frame := {
      blockIdx := 3
      stmtIdx := 0
      locals :=
        [.uninit,
         .init (.scalar ⟨c1.toNat, 1⟩),
         .init (.scalar ⟨c2.toNat, 1⟩),
         .init (.scalar ⟨x, 4⟩),
         .init (.aggregate 0 [.scalar ⟨a, 4⟩, .scalar ⟨b, 4⟩]),
         .init (.scalar ⟨a, 4⟩),
         .init (.scalar ⟨b, 4⟩)]
    }
    memory := emptyMemory }

private theorem twoDiamond_bb0_switch (c1 c2 : Bool) (x : Nat) :
    runMirToBinarySwitch 4 twoDiamondTupleBody
      (initMachineStateWithMemory twoDiamondTupleBody
        [.scalar ⟨c1.toNat, 1⟩, .scalar ⟨c2.toNat, 1⟩, .scalar ⟨x, 4⟩]
        emptyMemory) =
      some (!c1.toNat.beq 0, c1.toNat,
            twoDiamondPreSwitchState c1 c2 x 1,
            twoDiamondPreSwitchState c1 c2 x 2) :=
  rfl

private theorem twoDiamond_bb1_join (c1 c2 : Bool) (x : Nat) (hx : x < 1000) :
    evalPlanToJoin twoDiamondTupleBody (.jump 3 5)
      (twoDiamondPreSwitchState c1 c2 x 1) =
      some (twoDiamondBb3BranchState c1 c2 x (x + 10) (x + 20)) := by
  rw [← wrapU32_add (by omega : x + 10 < 4294967296),
      ← wrapU32_add (by omega : x + 20 < 4294967296)]
  rfl

private theorem twoDiamond_bb2_join (c1 c2 : Bool) (x : Nat) (hx : x < 1000) :
    evalPlanToJoin twoDiamondTupleBody (.jump 3 5)
      (twoDiamondPreSwitchState c1 c2 x 2) =
      some (twoDiamondBb3BranchState c1 c2 x (x + 1) (x + 2)) := by
  rw [← wrapU32_add (by omega : x + 1 < 4294967296),
      ← wrapU32_add (by omega : x + 2 < 4294967296)]
  rfl

/--
Core `wpTransPlan` proof for `twoDiamondTupleBody` over symbolic `(c1, c2, x)`.
Crucially, this proof NEVER invokes `cases c1` or `cases c2`: `zipLocalSlots`
merges the symbolic `(u32, u32)` aggregate at `bb3` so field projections `.0`
and `.1` in the second diamond evaluate in a single pass.
-/
theorem wpTransPlan_twoDiamondTuple
    (c1 c2 : Bool) (x : Nat) (hx : x < 1000) :
    wpTransPlan mirNoCallWP twoDiamondTupleBody twoDiamondPlan
      (· = .normal (.scalar ⟨twoDiamondPure c1 c2 x, 4⟩, emptyMemory))
      (initMachineStateWithMemory twoDiamondTupleBody
        [.scalar (boolToScalar c1), .scalar (boolToScalar c2), .scalar ⟨x, 4⟩]
        emptyMemory) := by
  rw [boolToScalar_eq c1, boolToScalar_eq c2, twoDiamondPlan, wpTransPlan,
    twoDiamond_bb0_switch c1 c2 x, not_beq_toNat_zero c1]
  dsimp only
  rw [twoDiamond_bb1_join c1 c2 x hx, twoDiamond_bb2_join c1 c2 x hx]
  dsimp only [twoDiamondBb3BranchState, joinPlanMemConsistent]
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, trivial, trivial, ?_⟩
  rw [wpTransPlan]
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, trivial, trivial, ?_⟩
  rw [wpTransPlan]
  change Outcome.normal (Value.scalar
    ⟨if (!(if c1 = true then c2.toNat else c2.toNat).beq 0) = true
      then (if c1 = true then x + 10 else x + 1)
      else (if c1 = true then x + 20 else x + 2), 4⟩, emptyMemory) = _
  rw [ite_self, not_beq_toNat_zero c2]
  rfl

theorem twoDiamondClaim_verified : VerificationResult twoDiamondClaim := by
  refine verifyByTransPlan (ewp := mirNoCallWP)
    twoDiamondClaim (fun _ => twoDiamondPlan) ?_
  rintro args ⟨c1, c2, x, hx, rfl⟩
  exact wpTransPlan_mono
    (fun _ h_eq _ _ h_norm _ _ _ h_args => by
      obtain ⟨rfl, rfl, rfl⟩ := twoDiamond_args_inj h_args
      cases h_eq.symm.trans h_norm
      rfl)
    (wpTransPlan_twoDiamondTuple c1 c2 x hx)

theorem twoDiamondTotalClaim_verified :
    TotalVerificationResult twoDiamondTotalClaim := by
  refine verifyTotalByTransPlan (ewp := mirNoCallWP)
    twoDiamondTotalClaim (fun _ _ => twoDiamondPlan) ?_
  rintro args mem ⟨rfl, c1, c2, x, hx, rfl⟩
  exact wpTransPlan_mono
    (fun _ h_eq => ⟨_, _, h_eq, rfl, fun _ _ _ h_args => by
      obtain ⟨rfl, rfl, rfl⟩ := twoDiamond_args_inj h_args
      rfl⟩)
    (wpTransPlan_twoDiamondTuple c1 c2 x hx)

/-! ## Suite 2: Pillar 2 Symbolic `while`-Loop Total & Coinductive Partial Verification -/

/--
`V2026_06_01` `CapturedMir` body for a symbolic `while i < n` arithmetic-sum loop:
```rust
fn sum_to_n(n: u32) -> u32 {
    let mut i: u32 = 0;
    let mut acc: u32 = 0;
    while i < n {
        acc = acc + i;
        i = i + 1;
    }
    acc
}
```
-/
def sumToNLoopBody : CapturedMir :=
  mkMirBody "test::sum_to_n" 1
    [mkDecl .mut u32MirTy,
     mkDecl .not u32MirTy,
     mkDecl .mut u32MirTy,
     mkDecl .mut u32MirTy,
     mkDecl .mut boolMirTy]
    [ -- bb0 (entry): _2 (i) = 0; _3 (acc) = 0; goto bb1
      { statements :=
          [mkStmt (.storageLive 2),
           mkStmt (.storageLive 3),
           mkStmt (.storageLive 4),
           mkStmt (.assign (locPlace 2) (.use (u32ConstOp 0))),
           mkStmt (.assign (locPlace 3) (.use (u32ConstOp 0)))]
        terminator := mkTerm (.goto 1)
        isCleanup := false },
      -- bb1 (loop header): _4 = (_2 < _1); switchInt(_4) [0 -> bb3, otherwise -> bb2]
      { statements :=
          [mkStmt (.assign (locPlace 4)
            (.binaryOp .lt (.copy (locPlace 2)) (.copy (locPlace 1))))]
        terminator := mkTerm (.switchInt (.copy (locPlace 4))
          { branches := [(0, 3)], otherwise := 2 })
        isCleanup := false },
      -- bb2 (loop body): _3 = _3 + _2; _2 = _2 + 1; goto bb1
      { statements :=
          [mkStmt (.assign (locPlace 3)
            (.binaryOp .add (.copy (locPlace 3)) (.copy (locPlace 2)))),
           mkStmt (.assign (locPlace 2)
            (.binaryOp .add (.copy (locPlace 2)) (u32ConstOp 1)))]
        terminator := mkTerm (.goto 1)
        isCleanup := false },
      -- bb3 (loop exit): _0 = _3; return
      { statements :=
          [mkStmt (.assign (locPlace 0) (.use (.copy (locPlace 3))))]
        terminator := mkTerm .return_
        isCleanup := false } ]

/-- Pure arithmetic sum $\sum_{k=0}^{n-1} k$. -/
def arithSum : Nat → Nat
  | 0 => 0
  | k + 1 => arithSum k + k

private theorem arithSum_le_sq : ∀ k : Nat, arithSum k ≤ k * k
  | 0 => Nat.le_refl 0
  | k + 1 => by
    have ih := arithSum_le_sq k
    calc
      arithSum (k + 1) = arithSum k + k := rfl
      _ ≤ k * k + k := Nat.add_le_add_right ih k
      _ ≤ (k + 1) * (k + 1) := by
        rw [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
        omega

/-- `sumToNLoopBody` state at `(bb, 0)` with counter `i`, accumulator `acc`, and slot `_4`. -/
private def sumToNState (bb n i acc : Nat) (cmp : LocalSlot) : MachineState :=
  { frame := {
      blockIdx := bb
      stmtIdx := 0
      locals :=
        [.uninit,
         .init (.scalar ⟨n, 4⟩),
         .init (.scalar ⟨i, 4⟩),
         .init (.scalar ⟨acc, 4⟩),
         cmp]
    }
    memory := emptyMemory }

/-- Loop header `MachineState` at iteration `i` with `acc = arithSum i`. -/
private abbrev sumToNHeaderState (n i : Nat) (cmpOpt : Option Value) : MachineState :=
  sumToNState 1 n i (arithSum i) (optSlot cmpOpt)

/-- Post-switch `MachineState` at block `bb` holding the comparison scalar `sc`. -/
private abbrev sumToNBranchState (bb n i : Nat) (sc : ScalarInt) : MachineState :=
  sumToNState bb n i (arithSum i) (.init (.scalar sc))

private theorem sumToN_header_switch_raw
    {fuel : Nat} (n i : Nat) (cmpOpt : Option Value) :
    runMirToBinarySwitch (fuel + 2) sumToNLoopBody (sumToNHeaderState n i cmpOpt) =
      let sc := boolToScalar (!Nat.ble n i)
      some (!sc.bits.beq 0, sc.bits, sumToNBranchState 2 n i sc, sumToNBranchState 3 n i sc) := by
  cases cmpOpt <;> rfl

private theorem sumToN_header_switch_ge
    {fuel : Nat} (i : Nat) (cmpOpt : Option Value) :
    runMirToBinarySwitch (fuel + 2) sumToNLoopBody (sumToNHeaderState i i cmpOpt) =
      some (false, 0, sumToNBranchState 2 i i ⟨0, 1⟩, sumToNBranchState 3 i i ⟨0, 1⟩) := by
  rw [sumToN_header_switch_raw, nat_ble_eq_true_of_le (Nat.le_refl i)]
  rfl

private theorem sumToN_header_switch_lt
    {fuel n i : Nat} (cmpOpt : Option Value) (h_lt : i < n) :
    runMirToBinarySwitch (fuel + 2) sumToNLoopBody (sumToNHeaderState n i cmpOpt) =
      some (true, 1, sumToNBranchState 2 n i ⟨1, 1⟩, sumToNBranchState 3 n i ⟨1, 1⟩) := by
  rw [sumToN_header_switch_raw, nat_ble_eq_false_of_lt h_lt]
  rfl

/-- One loop-body pass `bb2 → bb1` at iteration `i < n ≤ 1000` (both `u32` adds in range). -/
private theorem sumToN_body_step {n i : Nat} (hn : n ≤ 1000) (h_lt : i < n) :
    evalPlanToJoin sumToNLoopBody (.jump 1) (sumToNBranchState 2 n i ⟨1, 1⟩) =
      some (sumToNState 1 n (i + 1) (arithSum i + i) (.init (.scalar ⟨1, 1⟩))) := by
  have := arithSum_le_sq i
  have : i * i ≤ 1000 * 1000 := Nat.mul_le_mul (by omega) (by omega)
  rw [← wrapU32_add (show arithSum i + i < 4294967296 by omega),
    ← wrapU32_add (show i + 1 < 4294967296 by omega)]; rfl

/--
Inductive `wpTransPlan` proof for the `TransPlan.loop` sub-plan rooted at header
`bb1` for arbitrary symbolic `n ≤ 1000` and remaining iterations `rem = n - i`.
-/
private theorem wpTransPlan_sumToN_header
    (n : Nat) (hn : n ≤ 1000) :
    ∀ (rem i : Nat) (cmpOpt : Option Value),
      i + rem = n →
      wpTransPlan mirNoCallWP sumToNLoopBody
        (.loop 1 rem (.jump 1) .ret)
        (· = .normal (.scalar ⟨arithSum n, 4⟩, emptyMemory))
        (sumToNHeaderState n i cmpOpt)
  | 0, i, cmpOpt, h_sum => by
    obtain rfl : i = n := by omega
    rw [wpTransPlan, sumToN_header_switch_ge i cmpOpt]
    refine ⟨rfl, rfl, rfl, ?_⟩
    rw [wpTransPlan]
    rfl
  | rem + 1, i, cmpOpt, h_sum => by
    have h_lt : i < n := by omega
    rw [wpTransPlan, sumToN_header_switch_lt cmpOpt h_lt]
    dsimp only
    refine ⟨rfl, rfl, (fun h => by cases h), fun _ => ?_⟩
    rw [sumToN_body_step hn h_lt]
    dsimp only
    exact ⟨trivial,
      wpTransPlan_sumToN_header n hn rem (i + 1) (some (.scalar ⟨1, 1⟩)) (by omega)⟩

def sumToNTotalClaim (n : Nat) : TotalClaim where
  body := sumToNLoopBody
  pre args mem := args = [.scalar ⟨n, 4⟩] ∧ mem = emptyMemory
  post _ _ retVal mem' :=
    retVal = .scalar ⟨arithSum n, 4⟩ ∧ mem' = emptyMemory

/--
Symbolic total-correctness (`DWP` / `TotalVerificationResult`) and
`MirTerminatesAndNoUB` theorem for `sumToNLoopBody` across all `n ≤ 1000`.
-/
theorem sumToNLoop_total_and_terminates (n : Nat) (hn : n ≤ 1000) :
    TotalVerificationResult (sumToNTotalClaim n) ∧
    MirTerminatesAndNoUB sumToNLoopBody [.scalar ⟨n, 4⟩] emptyMemory := by
  have h_plan :
      wpTransPlan mirNoCallWP sumToNLoopBody (.seq 1 (.loop 1 n (.jump 1) .ret))
        (· = .normal (.scalar ⟨arithSum n, 4⟩, emptyMemory))
        (initMachineStateWithMemory sumToNLoopBody [.scalar ⟨n, 4⟩] emptyMemory) := by
    rw [wpTransPlan]
    exact wpTransPlan_sumToN_header n hn n 0 none (Nat.zero_add n)
  refine ⟨verifyTotalByTransPlan (ewp := mirNoCallWP) (sumToNTotalClaim n)
      (fun _ _ => .seq 1 (.loop 1 n (.jump 1) .ret)) ?_,
    mirTerminatesAndNoUB_of_dwp (ewp := mirNoCallWP) (P := fun _ _ => True)
      (DWP.mono (fun _ _ h_eq => ⟨_, _, h_eq, trivial⟩)
        (dwp_mirStatefulTree_of_transPlan h_plan))⟩
  rintro _ _ ⟨rfl, rfl⟩
  exact wpTransPlan_mono (fun _ h_eq => ⟨_, _, h_eq, rfl, rfl⟩) h_plan

def sumToNPartialClaim (n : Nat) : Claim where
  body := sumToNLoopBody
  pre args := args = [.scalar ⟨n, 4⟩]
  post _ retVal := retVal = .scalar ⟨arithSum n, 4⟩

/--
Coinductive partial-correctness (`VerificationResult`) verification of
`sumToNLoopBody` via `dwlp_mirTree_while_invariant` (without supplying a rank).
-/
theorem sumToNLoop_partial_by_coinductive_invariant (n : Nat) (hn : n ≤ 1000) :
    VerificationResult (sumToNPartialClaim n) := by
  refine verifyByDWLP (sumToNPartialClaim n) ?_
  rintro _ rfl
  refine dwlp_of_runMirTauToBlock (targetBlock := 1) 7
    (s' := sumToNHeaderState n 0 none) rfl ?_
  refine dwlp_mirTree_while_invariant (ewp := mirDefaultWP) sumToNLoopBody
    (fun s => ∃ i cmpOpt, i ≤ n ∧ s = sumToNHeaderState n i cmpOpt) 2 (.jump 1) .ret ?_
    ⟨0, none, Nat.zero_le n, rfl⟩
  rintro s ⟨i, cmpOpt, h_le, rfl⟩
  rcases Nat.lt_or_eq_of_le h_le with h_lt | rfl
  · refine ⟨true, 1, _, _, sumToN_header_switch_lt cmpOpt h_lt,
            (fun h => by cases h), fun _ => ?_⟩
    exact ⟨_, sumToN_body_step hn h_lt, trivial,
           ⟨i + 1, some (.scalar ⟨1, 1⟩), by omega, rfl⟩⟩
  · refine ⟨false, 0, _, _, sumToN_header_switch_ge i cmpOpt,
            fun _ => ?_, (fun h => by cases h)⟩
    rw [wpTransPlan]
    rintro _ _ ⟨⟩
    rfl

/-! ## Suite 3: Pillar 3 `&mut` Lenses, `ActiveTypedMutBorrow`, and `&mut FrameCursor` MIR -/

/-- Logical Rust struct `struct FrameCursor { pos: u32, len: u32 }`. -/
structure FrameCursor : Type where
  pos : Nat
  len : Nat
  deriving DecidableEq, Repr

/-- `ValueCodec` encoding `FrameCursor` as `Value.aggregate 0 [pos, len]`. -/
def frameCursorCodec : ValueCodec FrameCursor where
  encode c := .aggregate 0 [.scalar ⟨c.pos, 4⟩, .scalar ⟨c.len, 4⟩]
  decode
    | .aggregate 0 [.scalar ⟨p, 4⟩, .scalar ⟨l, 4⟩] => some { pos := p, len := l }
    | _ => none
  default := { pos := 0, len := 0 }
  decode_encode c := by rcases c with ⟨p, l⟩; rfl

/-- Pure state-update translation of `fn advance(&mut self, delta: u32) -> bool`. -/
def FrameCursor.advancePure (delta : Nat) : MutUpdate FrameCursor Bool :=
  fun c =>
    if Nat.ble (c.pos + delta) c.len then
      ({ c with pos := c.pos + delta }, true)
    else
      (c, false)

/-- Sub-place field lens `FrameCursor ⟶ pos` (`&mut cursor.pos`). -/
def FrameCursor.posLens : MutLens FrameCursor Nat where
  readView c := c.pos
  writeBack p c := { c with pos := p }

theorem lawfulMutLens_frameCursor_posLens :
    LawfulMutLens FrameCursor.posLens (fun _ => True) where
  valid_writeBack _ _ _ := trivial
  readView_writeBack _ _ _ := rfl
  writeBack_readView c _ := by cases c; rfl
  writeBack_writeBack _ _ c _ := by cases c; rfl

/--
Part 3A: Spatial `ActiveTypedMutBorrow` (`PointsTo ∗ BorrowToken .active`),
sequential `MutUpdate.seq` composition, sub-place lens reading, and
disjoint-allocation `AgreeOnFootprint` framing via `memoryPtrMutLens`.
-/
theorem pillar3_activeTypedMutBorrow_seq_and_disjoint_frame
    {rp : RawPtrVal} {m : Memory} {frameFp : Footprint}
    (c : FrameCursor) (d₁ d₂ : Nat)
    (h_borrow : ActiveTypedMutBorrow rp frameCursorCodec c ⟨m, mutBorrowFootprint rp⟩)
    (h_disj_addrs : ∀ allocId offset,
      (allocId, offset) ∈ frameFp.addrs → allocId ≠ rp.allocId)
    (h_disj_tags : ∀ tag ∈ frameFp.tags,
      ∃ entry,
        lookupBorrow m.borrows tag = some entry ∧
        entry.targetLocal ≠ rp.allocId) :
    let L := memoryPtrMutLens rp frameCursorCodec
    let (m₁, r₁) := L.applyUpdate (FrameCursor.advancePure d₁) m
    let (m₂, r₂) := L.applyUpdate (FrameCursor.advancePure d₂) m₁
    let (cSeq, rSeq) :=
      MutUpdate.seq (FrameCursor.advancePure d₁)
        (fun _ => FrameCursor.advancePure d₂) c
    (r₁, r₂) = rSeq ∧
    ActiveTypedMutBorrow rp frameCursorCodec cSeq ⟨m₂, mutBorrowFootprint rp⟩ ∧
    (L.comp FrameCursor.posLens).readView m₂ = cSeq.pos ∧
    AgreeOnFootprint frameFp m m₁ := by
  dsimp only
  obtain ⟨hr₁, h_sep₁⟩ :=
    memoryPtrMutLens_applyUpdate_sep (FrameCursor.advancePure d₁) h_borrow
  obtain ⟨hr₂, h_sep₂⟩ :=
    memoryPtrMutLens_applyUpdate_sep (FrameCursor.advancePure d₂) h_sep₁
  exact ⟨Prod.ext hr₁ hr₂, h_sep₂,
    congrArg FrameCursor.pos (memoryPtrMutLens_readView_of_sep h_sep₂),
    memoryPtrMutLens_writeBack_agreeOnDisjointAllocs _ frameFp
      h_borrow h_disj_addrs h_disj_tags⟩

/--
Part 3B: `V2026_06_01` `CapturedMir` body exercising `&mut FrameCursor` creation
(`Rvalue.ref (.mut false)`), dereference-field reads (`(*_3).0`, `(*_3).1`),
conditional dereference-field mutation (`(*_3).0 = _4` inside `bb1`), diamond
joining at `bb3`, and returning `(updated_cursor, ok_bool)`:
```rust
fn advance_cursor_mut(mut c: FrameCursor, delta: u32) -> (FrameCursor, bool) {
    let r: &mut FrameCursor = &mut c;
    let next_pos: u32 = (*r).pos + delta;
    let ok: bool = next_pos <= (*r).len;
    if ok {
        (*r).pos = next_pos;
    }
    (*r, ok)
}
```
-/
def advanceCursorMutMirBody : CapturedMir :=
  mkMirBody "test::advance_cursor_mut" 2
    [mkDecl .mut cursorRetMirTy,
     mkDecl .mut pairU32MirTy,
     mkDecl .not u32MirTy,
     mkDecl .mut pairU32MutRefMirTy,
     mkDecl .mut u32MirTy,
     mkDecl .mut boolMirTy,
     mkDecl .mut pairU32MirTy]
    [ -- bb0: _3 = &mut _1; _4 = (*_3).0 + _2; _5 = (_4 <= (*_3).1); switchInt(_5)
      { statements :=
          [mkStmt (.storageLive 3),
           mkStmt (.storageLive 4),
           mkStmt (.storageLive 5),
           mkStmt (.storageLive 6),
           mkStmt (.assign (locPlace 3) (.ref (.mut false) (locPlace 1))),
           mkStmt (.assign (locPlace 4)
             (.binaryOp .add
               (.copy { local_ := 3, projection := [.deref, .field 0 u32MirTy] })
               (.copy (locPlace 2)))),
           mkStmt (.assign (locPlace 5)
             (.binaryOp .le
               (.copy (locPlace 4))
               (.copy { local_ := 3, projection := [.deref, .field 1 u32MirTy] })))]
        terminator := mkTerm (.switchInt (.copy (locPlace 5))
          { branches := [(0, 2)], otherwise := 1 })
        isCleanup := false },
      -- bb1 (ok == true): (*_3).0 = _4; goto bb3
      { statements :=
          [mkStmt (.assign
            { local_ := 3, projection := [.deref, .field 0 u32MirTy] }
            (.use (.copy (locPlace 4))))]
        terminator := mkTerm (.goto 3)
        isCleanup := false },
      -- bb2 (ok == false): goto bb3
      { statements := []
        terminator := mkTerm (.goto 3)
        isCleanup := false },
      -- bb3 (join): _6 = *_3; _0 = (_6, _5); return
      { statements :=
          [mkStmt (.assign (locPlace 6)
            (.use (.copy { local_ := 3, projection := [.deref] }))),
           mkStmt (.assign (locPlace 0)
            (.aggregate .tuple [.copy (locPlace 6), .copy (locPlace 5)]))]
        terminator := mkTerm .return_
        isCleanup := false } ]

def advanceCursorMutPlan : TransPlan :=
  .branch 3 (.jump 3 3) (.jump 3 2) (.ret 3) 8

/--
`MutRefLocalSpec FrameCursor Bool` connecting `advanceCursorMutMirBody` to pure
`FrameCursor.advancePure` while certifying that Tree Borrows tag `1` remains
`.active` on local `1` at function exit.
-/
def advanceCursorMutSpec : MutRefLocalSpec FrameCursor Bool where
  body := advanceCursorMutMirBody
  stateCodec := frameCursorCodec
  retCodec := ValueCodec.rustBool
  pre c extraArgs mem :=
    c.pos < 10000 ∧
    c.len < 10000 ∧
    mem = emptyMemory ∧
    ∃ delta : Nat,
      delta < 10000 ∧
      extraArgs = [.scalar ⟨delta, 4⟩]
  update extraArgs :=
    match extraArgs with
    | [.scalar ⟨delta, 4⟩] => FrameCursor.advancePure delta
    | _ => fun c => (c, false)
  postMem _ _ _ mem' :=
    lookupBorrow mem'.borrows 1 =
      some { tag := 1, targetLocal := 1, targetProjection := [], perm := .active }

/--
`advanceCursorMutMirBody` state at `(bb, 0)`: cursor `_1 = (pos, len)`, `delta`,
the `&mut _1` pointer `_3`, `_4 = sum`, and comparison scalar `_5 = cmp`.
-/
private def advanceCursorMutState (bb pos len delta sum : Nat) (cmp : ScalarInt) :
    MachineState :=
  { frame := {
      blockIdx := bb
      stmtIdx := 0
      locals :=
        [.uninit,
         .init (.aggregate 0 [.scalar ⟨pos, 4⟩, .scalar ⟨len, 4⟩]),
         .init (.scalar ⟨delta, 4⟩),
         .init (.ptr { allocId := 1, offsetBytes := 0 } 8),
         .init (.scalar ⟨sum, 4⟩),
         .init (.scalar cmp),
         .uninit]
    }
    memory :=
      { emptyMemory with
        borrows :=
          [{ tag := 1, targetLocal := 1, targetProjection := [], perm := .active }]
        nextTag := 2 } }

private theorem advanceCursorMut_bb0_switch
    (c : FrameCursor) {delta : Nat} (h_add_lt : c.pos + delta < 4294967296) :
    runMirToBinarySwitch 8 advanceCursorMutMirBody
      (initMachineStateWithMemory advanceCursorMutMirBody
        [frameCursorCodec.encode c, .scalar ⟨delta, 4⟩] emptyMemory) =
      let cmp := boolToScalar (Nat.ble (c.pos + delta) c.len)
      some (!cmp.bits.beq 0, cmp.bits,
            advanceCursorMutState 1 c.pos c.len delta (c.pos + delta) cmp,
            advanceCursorMutState 2 c.pos c.len delta (c.pos + delta) cmp) := by
  rw [← wrapU32_add h_add_lt]; rfl

private theorem advanceCursorMut_wpTransPlan
    (c : FrameCursor) {delta : Nat} (h_add_lt : c.pos + delta < 4294967296) :
    wpTransPlan mirNoCallWP advanceCursorMutMirBody advanceCursorMutPlan
      (fun out =>
        out =
          .normal
            ((ValueCodec.pair frameCursorCodec ValueCodec.rustBool).encode
               (FrameCursor.advancePure delta c),
             { emptyMemory with
               borrows :=
                 [{ tag := 1, targetLocal := 1, targetProjection := [], perm := .active }]
               nextTag := 2 }))
      (initMachineStateWithMemory advanceCursorMutMirBody
        [frameCursorCodec.encode c, .scalar ⟨delta, 4⟩] emptyMemory) := by
  rw [advanceCursorMutPlan, wpTransPlan, advanceCursorMut_bb0_switch c h_add_lt]
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, trivial, trivial, ?_⟩
  rw [wpTransPlan, zipLocalSlots_eq_ite _ (by rfl), not_beq_boolToScalar_zero]
  dsimp only [FrameCursor.advancePure]
  cases Nat.ble (c.pos + delta) c.len <;> exact (@Eq.refl MirOutcome _)

/--
Symbolic total & stateful verification of `advanceCursorMutMirBody` against
`FrameCursor.advancePure` for all `c : FrameCursor` (`c.pos, c.len < 10000`) and
`delta < 10000` — proved via `TransPlan.branch` without case-splitting during
MIR diamond execution.
-/
theorem advanceCursorMutSpec_total_and_stateful_verified :
    TotalVerificationResult advanceCursorMutSpec.toTotalClaim ∧
    StatefulVerificationResult advanceCursorMutSpec.toStatefulClaim := by
  have h_tot : TotalVerificationResult advanceCursorMutSpec.toTotalClaim := by
    refine verifyMutRefLocalTotalByTransPlan (ewp := mirNoCallWP)
      advanceCursorMutSpec (fun _ _ _ => advanceCursorMutPlan) ?_
    rintro c extraArgs mem ⟨h_pos, h_len, rfl, delta, h_delta, rfl⟩
    have h_add_lt : c.pos + delta < 4294967296 := by omega
    exact wpTransPlan_mono (fun _ h_eq => h_eq ▸ ⟨_, rfl, rfl⟩)
      (advanceCursorMut_wpTransPlan c h_add_lt)
  exact ⟨h_tot, statefulOfTotalMutRefLocal h_tot⟩

end Anneal.FunctionalTranslationTests
