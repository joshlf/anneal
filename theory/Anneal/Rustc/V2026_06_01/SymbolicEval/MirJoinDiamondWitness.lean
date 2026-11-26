import Anneal.Rustc.V2026_06_01.SymbolicEval.MirSemanticsBridges

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
Concrete diamond / triangle / `switchTable` / caller-`&mut` / full-memory join witnesses,
`MirStateLiveEquiv` bridges, `Value.uninit` / `Memory.rootUnwindCeiling` regressions, and the
GVN / join-cut axiom policy.
-/

section MirJoinDiamondWitness

private def u64JoinMirTy : Ty := { kind := .uint .u64, layoutIdx := 0 }

private def u64JoinConstOp (n : Nat) : Operand :=
  .constant { ty := u64JoinMirTy, val := .scalar (.int { bits := n, sizeBytes := 8 }) }

private def defaultU64JoinLayout : TypeLayout :=
  { size := { bytes := 8 }
    align := { bytes := 8 }
    backendRepr := .scalar (.initialized (.int 64 false) ⟨0, 18446744073709551615⟩)
    fields := .primitive
    variants := .single 0
    isUninhabited := false }

private def defaultU64JoinFnAbi : FnAbi :=
  { args := []
    ret := { layout := defaultU64JoinLayout, mode := .direct }
    conv := .rust
    canUnwind := true }

/-- Production `CapturedMir` diamond body (`mirJoinDiamondBody`):
    - `_0`: `u64` return slot,
    - `_1`: `u64` input `x`,
    - `_2`: `u64` branch selector `flag`,
    - `_3`: branch-local `u64` temporary used only in the `then` arm (`bb1`), killed via
      `StorageDead(3)` before jumping to `bb3`.
    - `bb0`: `SwitchInt(_2)` (`0 -> bb2`, `otherwise -> bb1`),
    - `bb1` (`then` arm): `StorageLive(_3); _3 := _1 + 10; _0 := _3; StorageDead(_3); goto bb3`,
    - `bb2` (`else` arm): `_0 := _1 + 20; goto bb3`,
    - `bb3` (join block): `_0 := _0 + _1; return`. -/
def mirJoinDiamondBody : CapturedMir :=
  { defPath := "sym_eval::mir_join_diamond_witness"
    phase := .runtimePostCleanup
    role := .subject
    argCount := 2
    localDecls :=
      [ { mutability := .mut, ty := u64JoinMirTy, debugName := none }
      , { mutability := .not, ty := u64JoinMirTy, debugName := none }
      , { mutability := .not, ty := u64JoinMirTy, debugName := none }
      , { mutability := .mut, ty := u64JoinMirTy, debugName := none } ]
    basicBlocks :=
      [ { statements := []
          terminator :=
            { kind := .switchInt (.copy { local_ := 2, projection := [] })
                { branches := [(0, 2)], otherwise := 1 }
              span := "SymbolicEval.lean" }
          isCleanup := false }
      , { statements :=
            [ { kind := .storageLive 3, span := "SymbolicEval.lean" }
            , { kind := .assign { local_ := 3, projection := [] }
                  (.binaryOp .add
                    (.copy { local_ := 1, projection := [] })
                    (u64JoinConstOp 10))
                span := "SymbolicEval.lean" }
            , { kind := .assign { local_ := 0, projection := [] }
                  (.use (.copy { local_ := 3, projection := [] }))
                span := "SymbolicEval.lean" }
            , { kind := .storageDead 3, span := "SymbolicEval.lean" } ]
          terminator := { kind := .goto 3, span := "SymbolicEval.lean" }
          isCleanup := false }
      , { statements :=
            [ { kind := .assign { local_ := 0, projection := [] }
                  (.binaryOp .add
                    (.copy { local_ := 1, projection := [] })
                    (u64JoinConstOp 20))
                span := "SymbolicEval.lean" } ]
          terminator := { kind := .goto 3, span := "SymbolicEval.lean" }
          isCleanup := false }
      , { statements :=
            [ { kind := .assign { local_ := 0, projection := [] }
                  (.binaryOp .add
                    (.copy { local_ := 0, projection := [] })
                    (.copy { local_ := 1, projection := [] }))
                span := "SymbolicEval.lean" } ]
          terminator := { kind := .return_, span := "SymbolicEval.lean" }
          isCleanup := false } ]
    fnAbi := defaultU64JoinFnAbi
    layouts := emptyLayoutTable
    allocations := [] }

/-- Join-entry state of `mirJoinDiamondBody` at `bb3` (`stmtIdx = 0`) after an arm that stored
    `armVal` into `_0`: `_1 = x`, `_2 = flag`, and `_3` dead (killed by `StorageDead(3)` in `bb1`,
    never made live in `bb2`); the memory is the untouched initial memory. -/
def mirJoinDiamondArmState (x flag armVal : Nat) : MachineState :=
  let sInit := initMachineState mirJoinDiamondBody [.scalar ⟨x, 8⟩, .scalar ⟨flag, 8⟩]
  { sInit with
    frame :=
      { blockIdx := 3
        stmtIdx := 0
        locals :=
          [ .init (.scalar ⟨armVal, 8⟩)
          , .init (.scalar ⟨x, 8⟩)
          , .init (.scalar ⟨flag, 8⟩)
          , .dead ] } }

/-- Value stored into `_0` by the `else` arm `bb2` (`_0 := _1 + 20`, taken when `flag = 0`). -/
def mirJoinDiamondElseVal (x : Nat) : Nat := wrapScalarBits (Nat.add x 20) (scalarModulus 8)

/-- Value stored into `_0` by the `then` arm `bb1` (`_3 := _1 + 10; _0 := _3`, taken when
    `flag ≠ 0`). -/
def mirJoinDiamondThenVal (x : Nat) : Nat := wrapScalarBits (Nat.add x 10) (scalarModulus 8)

/-- Untrusted merge hint for `mirJoinDiamondBody`: only `_0` differs between the arms. -/
def mirJoinDiamondDiffers : List Bool := [true, false, false, false]

/-- State-level `ite` over the two arm states: what the prefix of `mirJoinDiamondBody` reaches. -/
def mirJoinDiamondArmResult (x flag : Nat) : MachineState :=
  if Nat.beq flag 0 then mirJoinDiamondArmState x flag (mirJoinDiamondElseVal x)
  else mirJoinDiamondArmState x flag (mirJoinDiamondThenVal x)

/-- Merged join state at `bb3`, built by the hint-driven `mergeMirJoinState` over the branch
    condition `Nat.beq flag 0`: `_0` carries `if Nat.beq flag 0 then x + 20 else x + 10` (wrapped)
    **inside** its scalar bits, while `_1`, `_2`, `_3`, the control point and the memory are shared
    verbatim. -/
def mirJoinDiamondMergedState (x flag : Nat) : MachineState :=
  mergeMirJoinState (Nat.beq flag 0) mirJoinDiamondDiffers
    (mirJoinDiamondArmState x flag (mirJoinDiamondElseVal x))
    (mirJoinDiamondArmState x flag (mirJoinDiamondThenVal x))

theorem mirJoinDiamond_arms_agree (x flag : Nat) :
    MirArmsAgree mirJoinDiamondDiffers
      (mirJoinDiamondArmState x flag (mirJoinDiamondElseVal x))
      (mirJoinDiamondArmState x flag (mirJoinDiamondThenVal x)) :=
  ⟨rfl, rfl, rfl, ⟨trivial, rfl, rfl, rfl, rfl⟩⟩

/-- **Non-Vacuity Witness for `evalJoinDiamondWP` / `wpMirJoinDiamond_merge_sound`
    (`mirJoinDiamond_evalJoinDiamondWP`)**: for all `x, flag : Nat`,
    1. each arm of `mirJoinDiamondBody` (`bb1` with the `StorageLive`/`StorageDead` temporary `_3`,
       `bb2` without it) steps via `wpMirUntilJoinSym` to its own arm state at `bb3`,
    2. the arms agree outside the hinted slot `_0` (`mirJoinDiamond_arms_agree`), and
    3. `bb3` is symbolically evaluated **once** on `mirJoinDiamondMergedState x flag` (built by
       `mergeMirJoinState`, without re-splitting on `Nat.beq flag 0`). -/
theorem mirJoinDiamond_evalJoinDiamondWP (x flag : Nat) :
    let armVal :=
      if Nat.beq flag 0 then
        wrapScalarBits (Nat.add x 20) (scalarModulus 8)
      else
        wrapScalarBits (Nat.add x 10) (scalarModulus 8)
    let expectedRet := wrapScalarBits (Nat.add armVal x) (scalarModulus 8)
    evalJoinDiamondWP 6 3 mirJoinDiamondBody 3
      (initMachineState mirJoinDiamondBody [.scalar ⟨x, 8⟩, .scalar ⟨flag, 8⟩])
      (mirJoinDiamondMergedState x flag)
      (mirNormalPost (fun retVal _ => retVal = .scalar ⟨expectedRet, 8⟩)) := by
  intro armVal expectedRet
  refine wpMirJoinDiamond_merge_sound ?_ (mirJoinDiamond_arms_agree x flag) ?_
  · -- Prefix cut up to join block `bb3`: each arm reaches its own arm state.
    show wpMirUntilJoinSym 6 mirJoinDiamondBody 3 _
      (fun s' => s' = mirJoinDiamondArmResult x flag) _
    (repeat' ((conv => whnf); split)); all_goals
      (rename_i hCond; change Nat.beq flag 0 = _ at hCond;
       dsimp only [mirJoinDiamondArmResult]; rw [hCond]; rfl)
  · -- Suffix from `bb3` evaluated ONCE on the merged state:
    rfl

/-- Fuel-level (`wpMirSym`) end-to-end witness of the merged diamond join cut. It stays within
    `{propext, Quot.sound}`, unlike the `DWLP`/`DWP` corollaries, whose *statements* mention the
    `coinductive_fixpoint`/`inductive_fixpoint`-built `Anneal.ITreeWP.DWLP`/`DWP` (which themselves
    depend on `Classical.choice`). -/
theorem mirJoinDiamond_wpMirSym_witness (x flag : Nat) :
    let armVal :=
      if Nat.beq flag 0 then
        wrapScalarBits (Nat.add x 20) (scalarModulus 8)
      else
        wrapScalarBits (Nat.add x 10) (scalarModulus 8)
    let expectedRet := wrapScalarBits (Nat.add armVal x) (scalarModulus 8)
    wpMirSym 9 mirJoinDiamondBody
      (initMachineState mirJoinDiamondBody [.scalar ⟨x, 8⟩, .scalar ⟨flag, 8⟩])
      (mirNormalPost (fun retVal _ => retVal = .scalar ⟨expectedRet, 8⟩)) :=
  wpMirSym_of_evalJoinDiamondWP (mirJoinDiamond_evalJoinDiamondWP x flag)

/-- `DWLP mirDefaultWP` witness on `mirCallTree mirJoinDiamondBody` via `wpMirJoinDiamond_sound`. -/
theorem mirJoinDiamond_verified_witness (x flag : Nat) :
    let armVal :=
      if Nat.beq flag 0 then
        wrapScalarBits (Nat.add x 20) (scalarModulus 8)
      else
        wrapScalarBits (Nat.add x 10) (scalarModulus 8)
    let expectedRet := wrapScalarBits (Nat.add armVal x) (scalarModulus 8)
    DWLP mirDefaultWP
      (mirCallTree mirJoinDiamondBody [.scalar ⟨x, 8⟩, .scalar ⟨flag, 8⟩])
      (fun out _ =>
        mirNormalPost (fun retVal _ => retVal = .scalar ⟨expectedRet, 8⟩) out)
      PUnit.unit :=
  wpMirJoinDiamond_sound (mirJoinDiamond_evalJoinDiamondWP x flag)

/-- **Negative control: the join cut is discriminating.** With `flag = 0` the `else` arm runs, so a
    cut demanding the `then` arm's state at `bb3` is refuted (the prefix check is not vacuous). -/
theorem mirJoinDiamond_cut_rejects_wrong_arm :
    ¬ wpMirUntilJoinSym 6 mirJoinDiamondBody 3
      (.running (initMachineState mirJoinDiamondBody [.scalar ⟨1, 8⟩, .scalar ⟨0, 8⟩]))
      (fun s' => s' = mirJoinDiamondArmState 1 0 (mirJoinDiamondThenVal 1)) (fun _ => True) := by
  intro h
  change mirJoinDiamondArmState 1 0 (mirJoinDiamondElseVal 1) =
    mirJoinDiamondArmState 1 0 (mirJoinDiamondThenVal 1) at h
  have hBits := congrArg (fun s : MachineState => match s.frame.locals with
    | .init (.scalar sc) :: _ => sc.bits
    | _ => 0) h
  exact absurd hBits (by decide)

/-- **Negative control: the merge hint is untrusted.** Without the `differs` hint on `_0`, the arms
    do not agree, so `mergeMirJoinState_eq_ite` / `wpMirJoinDiamond_merge_sound` cannot fire: a wrong
    hint makes verification fail, never unsound. -/
theorem mirJoinDiamond_unhinted_merge_rejected :
    ¬ MirArmsAgree [false, false, false, false]
      (mirJoinDiamondArmState 0 0 (mirJoinDiamondElseVal 0))
      (mirJoinDiamondArmState 0 0 (mirJoinDiamondThenVal 0)) := by
  intro h
  have hBits := congrArg (fun s : LocalSlot => match s with
    | .init (.scalar sc) => sc.bits
    | _ => 0) h.locals.1
  exact absurd hBits (by decide)

/-- **Asymmetric Dead/Scratch Slot Diamond (`mirJoinAsymmetricScratchBody`)**:
    Unlike `mirJoinDiamondBody`, `bb1` (`then` arm) allocates and initializes scratch local `_3`
    (`StorageLive(3); _3 := _1 + 10; _0 := _3; goto bb3`) **without** executing `StorageDead(3)`
    before jumping to `bb3`, while `bb2` (`else` arm) never touches `_3` (leaving `_3 = .dead`).
    At `bb3` entry, `_3` is `.dead` on `bb2` (`flag = 0`) and `.init (.scalar ⟨x + 10, 8⟩)` on
    `bb1` (`flag ≠ 0`). Because `_3` is dead (unused) in `bb3`, `mergeMirJoinState` with
    `differs = [true, false, false, true]` merges both arms and evaluates `bb3` **once** by `rfl`. -/
def mirJoinAsymmetricScratchBody : CapturedMir :=
  { mirJoinDiamondBody with
    defPath := "sym_eval::mir_join_asymmetric_scratch_witness"
    basicBlocks :=
      [ { statements := []
          terminator :=
            { kind := .switchInt (.copy { local_ := 2, projection := [] })
                { branches := [(0, 2)], otherwise := 1 }
              span := "SymbolicEval.lean" }
          isCleanup := false }
      , { statements :=
            [ { kind := .storageLive 3, span := "SymbolicEval.lean" }
            , { kind := .assign { local_ := 3, projection := [] }
                  (.binaryOp .add
                    (.copy { local_ := 1, projection := [] })
                    (u64JoinConstOp 10))
                span := "SymbolicEval.lean" }
            , { kind := .assign { local_ := 0, projection := [] }
                  (.use (.copy { local_ := 3, projection := [] }))
                span := "SymbolicEval.lean" } ]
          terminator := { kind := .goto 3, span := "SymbolicEval.lean" }
          isCleanup := false }
      , { statements :=
            [ { kind := .assign { local_ := 0, projection := [] }
                  (.binaryOp .add
                    (.copy { local_ := 1, projection := [] })
                    (u64JoinConstOp 20))
                span := "SymbolicEval.lean" } ]
          terminator := { kind := .goto 3, span := "SymbolicEval.lean" }
          isCleanup := false }
      , { statements :=
            [ { kind := .assign { local_ := 0, projection := [] }
                  (.binaryOp .add
                    (.copy { local_ := 0, projection := [] })
                    (.copy { local_ := 1, projection := [] }))
                span := "SymbolicEval.lean" } ]
          terminator := { kind := .return_, span := "SymbolicEval.lean" }
          isCleanup := false } ] }

/-- Join-entry state of `mirJoinAsymmetricScratchBody` at `bb3` with explicit slot `_3` state. -/
def mirJoinAsymmetricArmState (x flag armVal : Nat) (slot3 : LocalSlot) : MachineState :=
  let sInit := initMachineState mirJoinAsymmetricScratchBody [.scalar ⟨x, 8⟩, .scalar ⟨flag, 8⟩]
  { sInit with
    frame :=
      { blockIdx := 3
        stmtIdx := 0
        locals :=
          [ .init (.scalar ⟨armVal, 8⟩)
          , .init (.scalar ⟨x, 8⟩)
          , .init (.scalar ⟨flag, 8⟩)
          , slot3 ] } }

def mirJoinAsymmetricDiffers : List Bool := [true, false, false, true]

def mirJoinAsymmetricArmResult (x flag : Nat) : MachineState :=
  if Nat.beq flag 0 then
    mirJoinAsymmetricArmState x flag (mirJoinDiamondElseVal x) .dead
  else
    mirJoinAsymmetricArmState x flag (mirJoinDiamondThenVal x)
      (.init (.scalar ⟨mirJoinDiamondThenVal x, 8⟩))

def mirJoinAsymmetricMergedState (x flag : Nat) : MachineState :=
  mergeMirJoinState (Nat.beq flag 0) mirJoinAsymmetricDiffers
    (mirJoinAsymmetricArmState x flag (mirJoinDiamondElseVal x) .dead)
    (mirJoinAsymmetricArmState x flag (mirJoinDiamondThenVal x)
      (.init (.scalar ⟨mirJoinDiamondThenVal x, 8⟩)))

theorem mirJoinAsymmetric_arms_agree (x flag : Nat) :
    MirArmsAgree mirJoinAsymmetricDiffers
      (mirJoinAsymmetricArmState x flag (mirJoinDiamondElseVal x) .dead)
      (mirJoinAsymmetricArmState x flag (mirJoinDiamondThenVal x)
        (.init (.scalar ⟨mirJoinDiamondThenVal x, 8⟩))) :=
  ⟨rfl, rfl, rfl, ⟨trivial, rfl, rfl, trivial, rfl⟩⟩

/-- **Non-Vacuity Witness for Asymmetric Dead/Scratch Slots at Join
    (`mirJoinAsymmetricScratch_evalJoinDiamondWP`)**: even though `_3` is `.dead` on `bb2` and
    `.init (.scalar ⟨x + 10, 8⟩)` on `bb1` at `bb3` entry, `wpMirJoinDiamond_merge_sound` merges
    both arms and evaluates `bb3` **once** by `rfl`. -/
theorem mirJoinAsymmetricScratch_evalJoinDiamondWP (x flag : Nat) :
    let armVal :=
      if Nat.beq flag 0 then
        wrapScalarBits (Nat.add x 20) (scalarModulus 8)
      else
        wrapScalarBits (Nat.add x 10) (scalarModulus 8)
    let expectedRet := wrapScalarBits (Nat.add armVal x) (scalarModulus 8)
    evalJoinDiamondWP 5 3 mirJoinAsymmetricScratchBody 3
      (initMachineState mirJoinAsymmetricScratchBody [.scalar ⟨x, 8⟩, .scalar ⟨flag, 8⟩])
      (mirJoinAsymmetricMergedState x flag)
      (mirNormalPost (fun retVal _ => retVal = .scalar ⟨expectedRet, 8⟩)) := by
  intro armVal expectedRet
  refine wpMirJoinDiamond_merge_sound ?_ (mirJoinAsymmetric_arms_agree x flag) ?_
  · show wpMirUntilJoinSym 5 mirJoinAsymmetricScratchBody 3 _
      (fun s' => s' = mirJoinAsymmetricArmResult x flag) _
    (repeat' ((conv => whnf); split)); all_goals
      (rename_i hCond; change Nat.beq flag 0 = _ at hCond;
       dsimp only [mirJoinAsymmetricArmResult]; rw [hCond]; rfl)
  · rfl

theorem mirJoinAsymmetricScratch_wpMirSym_witness (x flag : Nat) :
    let armVal :=
      if Nat.beq flag 0 then
        wrapScalarBits (Nat.add x 20) (scalarModulus 8)
      else
        wrapScalarBits (Nat.add x 10) (scalarModulus 8)
    let expectedRet := wrapScalarBits (Nat.add armVal x) (scalarModulus 8)
    wpMirSym 8 mirJoinAsymmetricScratchBody
      (initMachineState mirJoinAsymmetricScratchBody [.scalar ⟨x, 8⟩, .scalar ⟨flag, 8⟩])
      (mirNormalPost (fun retVal _ => retVal = .scalar ⟨expectedRet, 8⟩)) :=
  wpMirSym_of_evalJoinDiamondWP (mirJoinAsymmetricScratch_evalJoinDiamondWP x flag)

/-- **Negative control on asymmetric scratch slot `_3` (`mirJoinAsymmetricScratch_unhinted_slot3_rejected`)**:
    if the hint `[true, false, false, false]` omits `differs[3] = true`, `MirArmsAgree` is refuted
    because `.dead ≠ .init (.scalar ...)`. -/
theorem mirJoinAsymmetricScratch_unhinted_slot3_rejected :
    ¬ MirArmsAgree [true, false, false, false]
      (mirJoinAsymmetricArmState 0 0 (mirJoinDiamondElseVal 0) .dead)
      (mirJoinAsymmetricArmState 0 0 (mirJoinDiamondThenVal 0)
        (.init (.scalar ⟨mirJoinDiamondThenVal 0, 8⟩))) := by
  intro h
  exact LocalSlot.noConfusion h.locals.2.2.2.1

/-- **Negative control on reading an asymmetric dead scratch slot in the join block
    (`mirJoinAsymmetricScratch_read_dead_slot3_rejected`)**: if a join block tries to read `_3`
    (`_0 := _0 + _3; return`) on `mirJoinAsymmetricMergedState 0 0` (where `_3 = .dead` because
    `flag = 0` took `bb2`), `wpMirSym` on the merged state is **refuted** (reading `.dead` faults
    with `.ub`). -/
def mirJoinReadScratchInJoinBody : CapturedMir :=
  { mirJoinAsymmetricScratchBody with
    defPath := "sym_eval::mir_join_read_scratch_in_join_neg"
    basicBlocks :=
      [ { statements := []
          terminator :=
            { kind := .switchInt (.copy { local_ := 2, projection := [] })
                { branches := [(0, 2)], otherwise := 1 }
              span := "SymbolicEval.lean" }
          isCleanup := false }
      , { statements :=
            [ { kind := .storageLive 3, span := "SymbolicEval.lean" }
            , { kind := .assign { local_ := 3, projection := [] }
                  (.binaryOp .add
                    (.copy { local_ := 1, projection := [] })
                    (u64JoinConstOp 10))
                span := "SymbolicEval.lean" }
            , { kind := .assign { local_ := 0, projection := [] }
                  (.use (.copy { local_ := 3, projection := [] }))
                span := "SymbolicEval.lean" } ]
          terminator := { kind := .goto 3, span := "SymbolicEval.lean" }
          isCleanup := false }
      , { statements :=
            [ { kind := .assign { local_ := 0, projection := [] }
                  (.binaryOp .add
                    (.copy { local_ := 1, projection := [] })
                    (u64JoinConstOp 20))
                span := "SymbolicEval.lean" } ]
          terminator := { kind := .goto 3, span := "SymbolicEval.lean" }
          isCleanup := false }
      , { statements :=
            [ { kind := .assign { local_ := 0, projection := [] }
                  (.binaryOp .add
                    (.copy { local_ := 0, projection := [] })
                    (.copy { local_ := 3, projection := [] }))
                span := "SymbolicEval.lean" } ]
          terminator := { kind := .return_, span := "SymbolicEval.lean" }
          isCleanup := false } ] }

theorem mirJoinAsymmetricScratch_read_dead_slot3_rejected :
    ¬ wpMirSym 3 mirJoinReadScratchInJoinBody
      (mirJoinAsymmetricMergedState 0 0)
      (fun _ => True) := by
  intro h
  exact h

/-- **Sequential Two-Diamond `CapturedMir` Witness (`mirSeqTwoDiamondBody`)**:
    Chains two `SwitchInt` diamonds (`bb0 -> {bb1, bb2} -> bb3 (join 1) -> {bb4, bb5} -> bb6 (join 2)`)
    by composing two `wpMirJoinDiamond_merge_sound` cuts back-to-back, evaluating `bb3` **once** on
    the first merged state and `bb6` **once** on the second merged state ($O(k)$ block evaluations
    instead of $2^k$ path unfoldings):
    - `_0`: `u64` return slot, `_1`: `x`, `_2`: `flag1`, `_3`: `flag2`, `_4`: scratch slot in `bb1`.
    - `bb0`: `SwitchInt(_2)` (`0 -> bb2`, `otherwise -> bb1`),
      - `bb1`: `StorageLive(_4); _4 := _1 + 1; _0 := _4; StorageDead(_4); goto bb3`,
      - `bb2`: `_0 := _1 + 2; goto bb3`,
    - `bb3` (Join 1): `SwitchInt(_3)` (`0 -> bb5`, `otherwise -> bb4`),
      - `bb4`: `_0 := _0 + 10; goto bb6`,
      - `bb5`: `_0 := _0 + 20; goto bb6`,
    - `bb6` (Join 2): `_0 := _0 + _1; return`. -/
def mirSeqTwoDiamondBody : CapturedMir :=
  { defPath := "sym_eval::mir_seq_two_diamond_witness"
    phase := .runtimePostCleanup
    role := .subject
    argCount := 3
    localDecls :=
      [ { mutability := .mut, ty := u64JoinMirTy, debugName := none }
      , { mutability := .not, ty := u64JoinMirTy, debugName := none }
      , { mutability := .not, ty := u64JoinMirTy, debugName := none }
      , { mutability := .not, ty := u64JoinMirTy, debugName := none }
      , { mutability := .mut, ty := u64JoinMirTy, debugName := none } ]
    basicBlocks :=
      [ { statements := []
          terminator :=
            { kind := .switchInt (.copy { local_ := 2, projection := [] })
                { branches := [(0, 2)], otherwise := 1 }
              span := "SymbolicEval.lean" }
          isCleanup := false }
      , { statements :=
            [ { kind := .storageLive 4, span := "SymbolicEval.lean" }
            , { kind := .assign { local_ := 4, projection := [] }
                  (.binaryOp .add
                    (.copy { local_ := 1, projection := [] })
                    (u64JoinConstOp 1))
                span := "SymbolicEval.lean" }
            , { kind := .assign { local_ := 0, projection := [] }
                  (.use (.copy { local_ := 4, projection := [] }))
                span := "SymbolicEval.lean" }
            , { kind := .storageDead 4, span := "SymbolicEval.lean" } ]
          terminator := { kind := .goto 3, span := "SymbolicEval.lean" }
          isCleanup := false }
      , { statements :=
            [ { kind := .assign { local_ := 0, projection := [] }
                  (.binaryOp .add
                    (.copy { local_ := 1, projection := [] })
                    (u64JoinConstOp 2))
                span := "SymbolicEval.lean" } ]
          terminator := { kind := .goto 3, span := "SymbolicEval.lean" }
          isCleanup := false }
      , { statements := []
          terminator :=
            { kind := .switchInt (.copy { local_ := 3, projection := [] })
                { branches := [(0, 5)], otherwise := 4 }
              span := "SymbolicEval.lean" }
          isCleanup := false }
      , { statements :=
            [ { kind := .assign { local_ := 0, projection := [] }
                  (.binaryOp .add
                    (.copy { local_ := 0, projection := [] })
                    (u64JoinConstOp 10))
                span := "SymbolicEval.lean" } ]
          terminator := { kind := .goto 6, span := "SymbolicEval.lean" }
          isCleanup := false }
      , { statements :=
            [ { kind := .assign { local_ := 0, projection := [] }
                  (.binaryOp .add
                    (.copy { local_ := 0, projection := [] })
                    (u64JoinConstOp 20))
                span := "SymbolicEval.lean" } ]
          terminator := { kind := .goto 6, span := "SymbolicEval.lean" }
          isCleanup := false }
      , { statements :=
            [ { kind := .assign { local_ := 0, projection := [] }
                  (.binaryOp .add
                    (.copy { local_ := 0, projection := [] })
                    (.copy { local_ := 1, projection := [] }))
                span := "SymbolicEval.lean" } ]
          terminator := { kind := .return_, span := "SymbolicEval.lean" }
          isCleanup := false } ]
    fnAbi := defaultU64JoinFnAbi
    layouts := emptyLayoutTable
    allocations := [] }

def mirSeqTwoDiamondDiffers : List Bool := [true, false, false, false, false]

def mirSeqTwoDiamondStateAt (bb : BasicBlockIdx) (x flag1 flag2 val0 : Nat) : MachineState :=
  let sInit :=
    initMachineState mirSeqTwoDiamondBody
      [.scalar ⟨x, 8⟩, .scalar ⟨flag1, 8⟩, .scalar ⟨flag2, 8⟩]
  { sInit with
    frame :=
      { blockIdx := bb
        stmtIdx := 0
        locals :=
          [ .init (.scalar ⟨val0, 8⟩)
          , .init (.scalar ⟨x, 8⟩)
          , .init (.scalar ⟨flag1, 8⟩)
          , .init (.scalar ⟨flag2, 8⟩)
          , .dead ] } }

def mirSeqDiamond1Val (x flag1 : Nat) : Nat :=
  if Nat.beq flag1 0 then
    wrapScalarBits (Nat.add x 2) (scalarModulus 8)
  else
    wrapScalarBits (Nat.add x 1) (scalarModulus 8)

def mirSeqDiamond2Val (x flag1 flag2 : Nat) : Nat :=
  let v1 := mirSeqDiamond1Val x flag1
  if Nat.beq flag2 0 then
    wrapScalarBits (Nat.add v1 20) (scalarModulus 8)
  else
    wrapScalarBits (Nat.add v1 10) (scalarModulus 8)

def mirSeqDiamond1ArmResult (x flag1 flag2 : Nat) : MachineState :=
  if Nat.beq flag1 0 then
    mirSeqTwoDiamondStateAt 3 x flag1 flag2 (wrapScalarBits (Nat.add x 2) (scalarModulus 8))
  else
    mirSeqTwoDiamondStateAt 3 x flag1 flag2 (wrapScalarBits (Nat.add x 1) (scalarModulus 8))

def mirSeqDiamond2ArmResult (x flag1 flag2 : Nat) : MachineState :=
  let v1 := mirSeqDiamond1Val x flag1
  if Nat.beq flag2 0 then
    mirSeqTwoDiamondStateAt 6 x flag1 flag2 (wrapScalarBits (Nat.add v1 20) (scalarModulus 8))
  else
    mirSeqTwoDiamondStateAt 6 x flag1 flag2 (wrapScalarBits (Nat.add v1 10) (scalarModulus 8))

def mirSeqDiamond1MergedState (x flag1 flag2 : Nat) : MachineState :=
  mergeMirJoinState (Nat.beq flag1 0) mirSeqTwoDiamondDiffers
    (mirSeqTwoDiamondStateAt 3 x flag1 flag2 (wrapScalarBits (Nat.add x 2) (scalarModulus 8)))
    (mirSeqTwoDiamondStateAt 3 x flag1 flag2 (wrapScalarBits (Nat.add x 1) (scalarModulus 8)))

def mirSeqDiamond2MergedState (x flag1 flag2 : Nat) : MachineState :=
  let v1 := mirSeqDiamond1Val x flag1
  mergeMirJoinState (Nat.beq flag2 0) mirSeqTwoDiamondDiffers
    (mirSeqTwoDiamondStateAt 6 x flag1 flag2 (wrapScalarBits (Nat.add v1 20) (scalarModulus 8)))
    (mirSeqTwoDiamondStateAt 6 x flag1 flag2 (wrapScalarBits (Nat.add v1 10) (scalarModulus 8)))

theorem mirSeqDiamond1_arms_agree (x flag1 flag2 : Nat) :
    MirArmsAgree mirSeqTwoDiamondDiffers
      (mirSeqTwoDiamondStateAt 3 x flag1 flag2 (wrapScalarBits (Nat.add x 2) (scalarModulus 8)))
      (mirSeqTwoDiamondStateAt 3 x flag1 flag2 (wrapScalarBits (Nat.add x 1) (scalarModulus 8))) :=
  ⟨rfl, rfl, rfl, ⟨trivial, rfl, rfl, rfl, rfl, rfl⟩⟩

theorem mirSeqDiamond2_arms_agree (x flag1 flag2 : Nat) :
    let v1 := mirSeqDiamond1Val x flag1
    MirArmsAgree mirSeqTwoDiamondDiffers
      (mirSeqTwoDiamondStateAt 6 x flag1 flag2 (wrapScalarBits (Nat.add v1 20) (scalarModulus 8)))
      (mirSeqTwoDiamondStateAt 6 x flag1 flag2 (wrapScalarBits (Nat.add v1 10) (scalarModulus 8))) :=
  ⟨rfl, rfl, rfl, ⟨trivial, rfl, rfl, rfl, rfl, rfl⟩⟩

/-- **Sequential Two-Diamond Compositional Join-Cut Witness (`mirSeqTwoDiamond_wpMirSym_witness`)**:
    Chains two `wpMirJoinDiamond_merge_sound` cuts across `bb3` and `bb6`, proving `wpMirSym` for
    all `x, flag1, flag2 : Nat` without exponential path splitting (`Classical.choice`-free). -/
theorem mirSeqTwoDiamond_wpMirSym_witness (x flag1 flag2 : Nat) :
    let expectedRet := wrapScalarBits (Nat.add (mirSeqDiamond2Val x flag1 flag2) x) (scalarModulus 8)
    wpMirSym 12 mirSeqTwoDiamondBody
      (initMachineState mirSeqTwoDiamondBody
        [.scalar ⟨x, 8⟩, .scalar ⟨flag1, 8⟩, .scalar ⟨flag2, 8⟩])
      (mirNormalPost (fun retVal _ => retVal = .scalar ⟨expectedRet, 8⟩)) := by
  intro expectedRet
  refine wpMirSym_of_evalJoinDiamondWP (prefixFuel := 6) (suffixFuel := 6) (joinBb := 3)
    (sJoin := mirSeqDiamond1MergedState x flag1 flag2) ?_
  refine wpMirJoinDiamond_merge_sound ?_ (mirSeqDiamond1_arms_agree x flag1 flag2) ?_
  · -- Diamond 1 (`bb0 -> {bb1, bb2} -> bb3`):
    show wpMirUntilJoinSym 6 mirSeqTwoDiamondBody 3 _
      (fun s' => s' = mirSeqDiamond1ArmResult x flag1 flag2) _
    (repeat' ((conv => whnf); split)); all_goals
      (rename_i hCond; change Nat.beq flag1 0 = _ at hCond;
       dsimp only [mirSeqDiamond1ArmResult]; rw [hCond]; rfl)
  · -- From `mirSeqDiamond1MergedState x flag1 flag2` at `bb3`, cut again at `bb6`:
    refine wpMirSym_of_evalJoinDiamondWP (prefixFuel := 3) (suffixFuel := 3) (joinBb := 6)
      (sJoin := mirSeqDiamond2MergedState x flag1 flag2) ?_
    refine wpMirJoinDiamond_merge_sound ?_ (mirSeqDiamond2_arms_agree x flag1 flag2) ?_
    · -- Diamond 2 (`bb3 -> {bb4, bb5} -> bb6`) evaluated ONCE from `mirSeqDiamond1MergedState`:
      show wpMirUntilJoinSym 3 mirSeqTwoDiamondBody 6 _
        (fun s' => s' = mirSeqDiamond2ArmResult x flag1 flag2) _
      ((conv => whnf); split); all_goals
        (rename_i hCond; change Nat.beq flag2 0 = _ at hCond;
         dsimp only [mirSeqDiamond2ArmResult]; rw [hCond]; rfl)
    · -- Join 2 (`bb6 -> return`) evaluated ONCE on `mirSeqDiamond2MergedState`:
      rfl

/-- `DWLP mirDefaultWP` witness for `mirSeqTwoDiamondBody`. -/
theorem mirSeqTwoDiamond_verified_witness (x flag1 flag2 : Nat) :
    let expectedRet := wrapScalarBits (Nat.add (mirSeqDiamond2Val x flag1 flag2) x) (scalarModulus 8)
    DWLP mirDefaultWP
      (mirCallTree mirSeqTwoDiamondBody
        [.scalar ⟨x, 8⟩, .scalar ⟨flag1, 8⟩, .scalar ⟨flag2, 8⟩])
      (fun out _ =>
        mirNormalPost (fun retVal _ => retVal = .scalar ⟨expectedRet, 8⟩) out)
      PUnit.unit :=
  (dwp_of_wpMirSym (mirSeqTwoDiamond_wpMirSym_witness x flag1 flag2)).toDWLP

/-- **`if`-without-`else` (triangle) `CapturedMir` witness body (`mirJoinTriangleBody`)**, the
    shape post-`SimplifyCfg` MIR gives `if c { … }`: on one side the `SwitchInt` jumps **directly** to
    the join block, so the two incoming paths have different lengths.
    - `bb0`: `_0 := _1 + 1; SwitchInt(_2)` (`0 -> bb2`, the join itself; `otherwise -> bb1`),
    - `bb1` (arm): `_0 := _0 + 10; goto bb2`,
    - `bb2` (join): `_0 := _0 + _1; return`. -/
def mirJoinTriangleBody : CapturedMir :=
  { mirJoinDiamondBody with
    defPath := "sym_eval::mir_join_triangle_witness"
    basicBlocks :=
      [ { statements :=
            [ { kind := .assign { local_ := 0, projection := [] }
                  (.binaryOp .add
                    (.copy { local_ := 1, projection := [] })
                    (u64JoinConstOp 1))
                span := "SymbolicEval.lean" } ]
          terminator :=
            { kind := .switchInt (.copy { local_ := 2, projection := [] })
                { branches := [(0, 2)], otherwise := 1 }
              span := "SymbolicEval.lean" }
          isCleanup := false }
      , { statements :=
            [ { kind := .assign { local_ := 0, projection := [] }
                  (.binaryOp .add
                    (.copy { local_ := 0, projection := [] })
                    (u64JoinConstOp 10))
                span := "SymbolicEval.lean" } ]
          terminator := { kind := .goto 2, span := "SymbolicEval.lean" }
          isCleanup := false }
      , { statements :=
            [ { kind := .assign { local_ := 0, projection := [] }
                  (.binaryOp .add
                    (.copy { local_ := 0, projection := [] })
                    (.copy { local_ := 1, projection := [] }))
                span := "SymbolicEval.lean" } ]
          terminator := { kind := .return_, span := "SymbolicEval.lean" }
          isCleanup := false } ] }

/-- Join-entry state of `mirJoinTriangleBody` at `bb2` (`stmtIdx = 0`) with `_0 = joinVal`. -/
def mirJoinTriangleArmState (x flag joinVal : Nat) : MachineState :=
  let sInit := initMachineState mirJoinTriangleBody [.scalar ⟨x, 8⟩, .scalar ⟨flag, 8⟩]
  { sInit with
    frame :=
      { blockIdx := 2
        stmtIdx := 0
        locals :=
          [ .init (.scalar ⟨joinVal, 8⟩)
          , .init (.scalar ⟨x, 8⟩)
          , .init (.scalar ⟨flag, 8⟩)
          , .dead ] } }

/-- `_0` on the direct path (`flag = 0`: `bb0 -> bb2`). -/
def mirJoinTriangleDirectVal (x : Nat) : Nat := wrapScalarBits (Nat.add x 1) (scalarModulus 8)

/-- `_0` on the arm path (`flag ≠ 0`: `bb0 -> bb1 -> bb2`). -/
def mirJoinTriangleArmVal (x : Nat) : Nat :=
  wrapScalarBits (Nat.add (mirJoinTriangleDirectVal x) 10) (scalarModulus 8)

/-- State-level `ite` over the two incoming states: what the prefix of `mirJoinTriangleBody`
    reaches at `bb2`. -/
def mirJoinTriangleArmResult (x flag : Nat) : MachineState :=
  if Nat.beq flag 0 then mirJoinTriangleArmState x flag (mirJoinTriangleDirectVal x)
  else mirJoinTriangleArmState x flag (mirJoinTriangleArmVal x)

/-- Merged triangle join state: only `_0` (hinted) carries `if Nat.beq flag 0 then _ else _` bits. -/
def mirJoinTriangleMergedState (x flag : Nat) : MachineState :=
  mergeMirJoinState (Nat.beq flag 0) mirJoinDiamondDiffers
    (mirJoinTriangleArmState x flag (mirJoinTriangleDirectVal x))
    (mirJoinTriangleArmState x flag (mirJoinTriangleArmVal x))

theorem mirJoinTriangle_arms_agree (x flag : Nat) :
    MirArmsAgree mirJoinDiamondDiffers
      (mirJoinTriangleArmState x flag (mirJoinTriangleDirectVal x))
      (mirJoinTriangleArmState x flag (mirJoinTriangleArmVal x)) :=
  ⟨rfl, rfl, rfl, ⟨trivial, rfl, rfl, rfl, rfl⟩⟩

/-- **Triangle join-cut witness (`mirJoinTriangle_evalJoinDiamondWP`)**: the production combinator
    `wpMirJoinDiamond_merge_sound` also covers `if`-without-`else` CFGs. The direct path reaches
    `bb2` straight from the `SwitchInt` and the arm path through `bb1`; both are cut at `bb2`, and
    `bb2` is evaluated **once** on the merged state, for all `x, flag : Nat`. -/
theorem mirJoinTriangle_evalJoinDiamondWP (x flag : Nat) :
    let joinVal :=
      if Nat.beq flag 0 then mirJoinTriangleDirectVal x else mirJoinTriangleArmVal x
    let expectedRet := wrapScalarBits (Nat.add joinVal x) (scalarModulus 8)
    evalJoinDiamondWP 6 3 mirJoinTriangleBody 2
      (initMachineState mirJoinTriangleBody [.scalar ⟨x, 8⟩, .scalar ⟨flag, 8⟩])
      (mirJoinTriangleMergedState x flag)
      (mirNormalPost (fun retVal _ => retVal = .scalar ⟨expectedRet, 8⟩)) := by
  intro joinVal expectedRet
  refine wpMirJoinDiamond_merge_sound ?_ (mirJoinTriangle_arms_agree x flag) ?_
  · -- Prefix cut at `bb2` along both the direct and the arm path.
    show wpMirUntilJoinSym 6 mirJoinTriangleBody 2 _
      (fun s' => s' = mirJoinTriangleArmResult x flag) _
    ((conv => whnf); split); all_goals
      (rename_i hCond; change Nat.beq flag 0 = _ at hCond;
       dsimp only [mirJoinTriangleArmResult]; rw [hCond]; rfl)
  · -- Join `bb2` evaluated ONCE on the merged state:
    rfl

/-- Fuel-level (`wpMirSym`, `Classical.choice`-free) end-to-end triangle witness. -/
theorem mirJoinTriangle_wpMirSym_witness (x flag : Nat) :
    let joinVal :=
      if Nat.beq flag 0 then mirJoinTriangleDirectVal x else mirJoinTriangleArmVal x
    let expectedRet := wrapScalarBits (Nat.add joinVal x) (scalarModulus 8)
    wpMirSym 9 mirJoinTriangleBody
      (initMachineState mirJoinTriangleBody [.scalar ⟨x, 8⟩, .scalar ⟨flag, 8⟩])
      (mirNormalPost (fun retVal _ => retVal = .scalar ⟨expectedRet, 8⟩)) :=
  wpMirSym_of_evalJoinDiamondWP (mirJoinTriangle_evalJoinDiamondWP x flag)

/-- `DWLP mirDefaultWP` witness for `mirJoinTriangleBody`. -/
theorem mirJoinTriangle_verified_witness (x flag : Nat) :
    let joinVal :=
      if Nat.beq flag 0 then mirJoinTriangleDirectVal x else mirJoinTriangleArmVal x
    let expectedRet := wrapScalarBits (Nat.add joinVal x) (scalarModulus 8)
    DWLP mirDefaultWP
      (mirCallTree mirJoinTriangleBody [.scalar ⟨x, 8⟩, .scalar ⟨flag, 8⟩])
      (fun out _ =>
        mirNormalPost (fun retVal _ => retVal = .scalar ⟨expectedRet, 8⟩) out)
      PUnit.unit :=
  wpMirJoinDiamond_sound (mirJoinTriangle_evalJoinDiamondWP x flag)

/-- **Negative control for `mirJoinTriangleBody`**: omitting the `_0` hint refutes `MirArmsAgree`
    because the direct edge (`x + 1`) and the arm (`x + 11`) disagree on `_0`. -/
theorem mirJoinTriangle_unhinted_merge_rejected :
    ¬ MirArmsAgree [false, false, false, false]
      (mirJoinTriangleArmState 0 0 (mirJoinTriangleDirectVal 0))
      (mirJoinTriangleArmState 0 0 (mirJoinTriangleArmVal 0)) := by
  intro h
  have hBits := congrArg (fun s : LocalSlot => match s with
    | .init (.scalar sc) => sc.bits
    | _ => 0) h.locals.1
  exact absurd hBits (by decide)

/-- **3-Way `SwitchInt` `CapturedMir` Witness (`mirJoinSwitch3Body`)**:
    - `bb0`: `SwitchInt(_2)` (`0 -> bb2`, `1 -> bb3`, `otherwise -> bb1`),
    - `bb1` (`otherwise`): `_0 := _1 + 10; goto bb4`,
    - `bb2` (`0`): `_0 := _1 + 20; goto bb4`,
    - `bb3` (`1`): `_0 := _1 + 30; goto bb4`,
    - `bb4` (join): `_0 := _0 + _1; return`. -/
def mirJoinSwitch3Body : CapturedMir :=
  { mirJoinDiamondBody with
    defPath := "sym_eval::mir_join_switch3_witness"
    basicBlocks :=
      [ { statements := []
          terminator :=
            { kind := .switchInt (.copy { local_ := 2, projection := [] })
                { branches := [(0, 2), (1, 3)], otherwise := 1 }
              span := "SymbolicEval.lean" }
          isCleanup := false }
      , { statements :=
            [ { kind := .assign { local_ := 0, projection := [] }
                  (.binaryOp .add
                    (.copy { local_ := 1, projection := [] })
                    (u64JoinConstOp 10))
                span := "SymbolicEval.lean" } ]
          terminator := { kind := .goto 4, span := "SymbolicEval.lean" }
          isCleanup := false }
      , { statements :=
            [ { kind := .assign { local_ := 0, projection := [] }
                  (.binaryOp .add
                    (.copy { local_ := 1, projection := [] })
                    (u64JoinConstOp 20))
                span := "SymbolicEval.lean" } ]
          terminator := { kind := .goto 4, span := "SymbolicEval.lean" }
          isCleanup := false }
      , { statements :=
            [ { kind := .assign { local_ := 0, projection := [] }
                  (.binaryOp .add
                    (.copy { local_ := 1, projection := [] })
                    (u64JoinConstOp 30))
                span := "SymbolicEval.lean" } ]
          terminator := { kind := .goto 4, span := "SymbolicEval.lean" }
          isCleanup := false }
      , { statements :=
            [ { kind := .assign { local_ := 0, projection := [] }
                  (.binaryOp .add
                    (.copy { local_ := 0, projection := [] })
                    (.copy { local_ := 1, projection := [] }))
                span := "SymbolicEval.lean" } ]
          terminator := { kind := .return_, span := "SymbolicEval.lean" }
          isCleanup := false } ] }

def mirJoinSwitch3ArmState (x flag armVal : Nat) : MachineState :=
  let sInit := initMachineState mirJoinSwitch3Body [.scalar ⟨x, 8⟩, .scalar ⟨flag, 8⟩]
  { sInit with
    frame :=
      { blockIdx := 4
        stmtIdx := 0
        locals :=
          [ .init (.scalar ⟨armVal, 8⟩)
          , .init (.scalar ⟨x, 8⟩)
          , .init (.scalar ⟨flag, 8⟩)
          , .dead ] } }

def mirJoinSwitch3Case0Val (x : Nat) : Nat := wrapScalarBits (Nat.add x 20) (scalarModulus 8)
def mirJoinSwitch3Case1Val (x : Nat) : Nat := wrapScalarBits (Nat.add x 30) (scalarModulus 8)
def mirJoinSwitch3DefaultVal (x : Nat) : Nat := wrapScalarBits (Nat.add x 10) (scalarModulus 8)

def mirJoinSwitch3ArmResult (x flag : Nat) : MachineState :=
  if Nat.beq flag 0 then mirJoinSwitch3ArmState x flag (mirJoinSwitch3Case0Val x)
  else if Nat.beq flag 1 then mirJoinSwitch3ArmState x flag (mirJoinSwitch3Case1Val x)
  else mirJoinSwitch3ArmState x flag (mirJoinSwitch3DefaultVal x)

def mirJoinSwitch3MergedState (x flag : Nat) : MachineState :=
  mergeMirJoinState (Nat.beq flag 0) mirJoinDiamondDiffers
    (mirJoinSwitch3ArmState x flag (mirJoinSwitch3Case0Val x))
    (mergeMirJoinState (Nat.beq flag 1) mirJoinDiamondDiffers
      (mirJoinSwitch3ArmState x flag (mirJoinSwitch3Case1Val x))
      (mirJoinSwitch3ArmState x flag (mirJoinSwitch3DefaultVal x)))

theorem mirJoinSwitch3_agree01 (x flag : Nat) :
    MirArmsAgree mirJoinDiamondDiffers
      (mirJoinSwitch3ArmState x flag (mirJoinSwitch3Case0Val x))
      (mirJoinSwitch3ArmState x flag (mirJoinSwitch3Case1Val x)) :=
  ⟨rfl, rfl, rfl, ⟨trivial, rfl, rfl, rfl, rfl⟩⟩

theorem mirJoinSwitch3_agree12 (x flag : Nat) :
    MirArmsAgree mirJoinDiamondDiffers
      (mirJoinSwitch3ArmState x flag (mirJoinSwitch3Case1Val x))
      (mirJoinSwitch3ArmState x flag (mirJoinSwitch3DefaultVal x)) :=
  ⟨rfl, rfl, rfl, ⟨trivial, rfl, rfl, rfl, rfl⟩⟩

/-- **3-Way `SwitchInt` Join-Cut Witness (`mirJoinSwitch3_evalJoinDiamondWP`)**:
    All 3 arms (`0 -> bb2`, `1 -> bb3`, `otherwise -> bb1`) are merged into
    `mirJoinSwitch3MergedState x flag` via `wpMirJoinSwitch3_merge_sound`, and `bb4` is evaluated
    **once** by `rfl`. -/
theorem mirJoinSwitch3_evalJoinDiamondWP (x flag : Nat) :
    let armVal :=
      if Nat.beq flag 0 then mirJoinSwitch3Case0Val x
      else if Nat.beq flag 1 then mirJoinSwitch3Case1Val x
      else mirJoinSwitch3DefaultVal x
    let expectedRet := wrapScalarBits (Nat.add armVal x) (scalarModulus 8)
    evalJoinDiamondWP 4 3 mirJoinSwitch3Body 4
      (initMachineState mirJoinSwitch3Body [.scalar ⟨x, 8⟩, .scalar ⟨flag, 8⟩])
      (mirJoinSwitch3MergedState x flag)
      (mirNormalPost (fun retVal _ => retVal = .scalar ⟨expectedRet, 8⟩)) := by
  intro armVal expectedRet
  refine wpMirJoinSwitch3_merge_sound ?_ (mirJoinSwitch3_agree01 x flag)
    (mirJoinSwitch3_agree12 x flag) ?_
  · show wpMirUntilJoinSym 4 mirJoinSwitch3Body 4 _
      (fun s' => s' = mirJoinSwitch3ArmResult x flag) _
    ((conv => whnf); split)
    · rename_i h0
      change Nat.beq flag 0 = true at h0
      dsimp only [mirJoinSwitch3ArmResult]
      rw [h0]
      rfl
    · rename_i h0
      change Nat.beq flag 0 = false at h0
      ((conv => whnf); split); all_goals
        (rename_i h1; change Nat.beq flag 1 = _ at h1;
         dsimp only [mirJoinSwitch3ArmResult]; rw [h0, h1]; rfl)
  · rfl

theorem mirJoinSwitch3_wpMirSym_witness (x flag : Nat) :
    let armVal :=
      if Nat.beq flag 0 then mirJoinSwitch3Case0Val x
      else if Nat.beq flag 1 then mirJoinSwitch3Case1Val x
      else mirJoinSwitch3DefaultVal x
    let expectedRet := wrapScalarBits (Nat.add armVal x) (scalarModulus 8)
    wpMirSym 7 mirJoinSwitch3Body
      (initMachineState mirJoinSwitch3Body [.scalar ⟨x, 8⟩, .scalar ⟨flag, 8⟩])
      (mirNormalPost (fun retVal _ => retVal = .scalar ⟨expectedRet, 8⟩)) :=
  wpMirSym_of_evalJoinDiamondWP (mirJoinSwitch3_evalJoinDiamondWP x flag)

theorem mirJoinSwitch3_verified_witness (x flag : Nat) :
    let armVal :=
      if Nat.beq flag 0 then mirJoinSwitch3Case0Val x
      else if Nat.beq flag 1 then mirJoinSwitch3Case1Val x
      else mirJoinSwitch3DefaultVal x
    let expectedRet := wrapScalarBits (Nat.add armVal x) (scalarModulus 8)
    DWLP mirDefaultWP
      (mirCallTree mirJoinSwitch3Body [.scalar ⟨x, 8⟩, .scalar ⟨flag, 8⟩])
      (fun out _ =>
        mirNormalPost (fun retVal _ => retVal = .scalar ⟨expectedRet, 8⟩) out)
      PUnit.unit :=
  wpMirJoinDiamond_sound (mirJoinSwitch3_evalJoinDiamondWP x flag)

/-- **Stateful `&mut u64` (`Memory.callerLocals`) Diamond Witness (`mirJoinCallerMutRefDiamondBody`)**:
    Models `fn update_out(out: &mut u64, x: u64, flag: u64) -> u64`:
    - `_0`: `u64` return slot,
    - `_1`: `&mut u64` reference pointing to caller-owned referent `callerLocals[4]`,
    - `_2`: `u64` input `x`,
    - `_3`: `u64` branch selector `flag`.
    - `bb0`: `SwitchInt(_3)` (`0 -> bb2`, `otherwise -> bb1`),
    - `bb1` (`then` arm): `*_1 := _2 + 10; goto bb3` (mutates `Memory.callerLocals[4]`!),
    - `bb2` (`else` arm): `*_1 := _2 + 20; goto bb3` (mutates `Memory.callerLocals[4]`!),
    - `bb3` (join block): `_0 := *_1; _0 := _0 + _2; return` (dereferences `*_1` from merged
      `Memory.callerLocals[4]` and adds `_2`). -/
private def u64MutRefJoinMirTy : Ty := { kind := .ref .mut (.uint .u64), layoutIdx := 0 }

def mirJoinCallerMutRefDiamondBody : CapturedMir :=
  { defPath := "sym_eval::mir_join_caller_mut_ref_diamond_witness"
    phase := .runtimePostCleanup
    role := .subject
    argCount := 3
    localDecls :=
      [ { mutability := .mut, ty := u64JoinMirTy, debugName := none }
      , { mutability := .not, ty := u64MutRefJoinMirTy, debugName := none }
      , { mutability := .not, ty := u64JoinMirTy, debugName := none }
      , { mutability := .not, ty := u64JoinMirTy, debugName := none } ]
    basicBlocks :=
      [ { statements := []
          terminator :=
            { kind := .switchInt (.copy { local_ := 3, projection := [] })
                { branches := [(0, 2)], otherwise := 1 }
              span := "SymbolicEval.lean" }
          isCleanup := false }
      , { statements :=
            [ { kind := .assign { local_ := 1, projection := [.deref] }
                  (.binaryOp .add
                    (.copy { local_ := 2, projection := [] })
                    (u64JoinConstOp 10))
                span := "SymbolicEval.lean" } ]
          terminator := { kind := .goto 3, span := "SymbolicEval.lean" }
          isCleanup := false }
      , { statements :=
            [ { kind := .assign { local_ := 1, projection := [.deref] }
                  (.binaryOp .add
                    (.copy { local_ := 2, projection := [] })
                    (u64JoinConstOp 20))
                span := "SymbolicEval.lean" } ]
          terminator := { kind := .goto 3, span := "SymbolicEval.lean" }
          isCleanup := false }
      , { statements :=
            [ { kind := .assign { local_ := 0, projection := [] }
                  (.use (.copy { local_ := 1, projection := [.deref] }))
                span := "SymbolicEval.lean" }
            , { kind := .assign { local_ := 0, projection := [] }
                  (.binaryOp .add
                    (.copy { local_ := 0, projection := [] })
                    (.copy { local_ := 2, projection := [] }))
                span := "SymbolicEval.lean" } ]
          terminator := { kind := .return_, span := "SymbolicEval.lean" }
          isCleanup := false } ]
    fnAbi := defaultU64JoinFnAbi
    layouts := emptyLayoutTable
    allocations := [] }

def mirJoinCallerMutBorrowEntry : BorrowEntry :=
  { tag := 1
    perm := .active
    targetLocal := 4
    targetProjection := []
    protector := some 1
    rangeOffset := 0
    rangeLen := 8 }

def mirJoinCallerMutMemWith (v : Nat) : Memory :=
  { emptyMemory with
    borrows := [mirJoinCallerMutBorrowEntry]
    nextTag := 2
    activeProtectors := [1]
    nextProtector := 2
    callerLocals :=
      [ .dead, .dead, .dead, .dead
      , .init (.scalar { bits := v, sizeBytes := 8 }) ] }

def mirJoinCallerMutInitState (initOut x flag : Nat) : MachineState :=
  let s0 :=
    initMachineState mirJoinCallerMutRefDiamondBody
      [.ptr { allocId := 1, offsetBytes := 0 } 8, .scalar ⟨x, 8⟩, .scalar ⟨flag, 8⟩]
  { s0 with memory := mirJoinCallerMutRefMemWith initOut }
where
  mirJoinCallerMutRefMemWith := mirJoinCallerMutMemWith

def mirJoinCallerMutArmState (x flag outVal : Nat) : MachineState :=
  { frame :=
      { blockIdx := 3
        stmtIdx := 0
        locals :=
          [ .uninit
          , .init (.ptr { allocId := 1, offsetBytes := 0 } 8)
          , .init (.scalar ⟨x, 8⟩)
          , .init (.scalar ⟨flag, 8⟩) ] }
    memory := mirJoinCallerMutMemWith outVal }

def mirJoinCallerMutLocalDiffers : List Bool := [false, false, false, false]
def mirJoinCallerMutCallerDiffers : List Bool := [false, false, false, false, true]

def mirJoinCallerMutArmResult (x flag : Nat) : MachineState :=
  if Nat.beq flag 0 then mirJoinCallerMutArmState x flag (mirJoinDiamondElseVal x)
  else mirJoinCallerMutArmState x flag (mirJoinDiamondThenVal x)

def mirJoinCallerMutMergedState (x flag : Nat) : MachineState :=
  mergeMirJoinStateWithCaller (Nat.beq flag 0)
    mirJoinCallerMutLocalDiffers mirJoinCallerMutCallerDiffers
    (mirJoinCallerMutArmState x flag (mirJoinDiamondElseVal x))
    (mirJoinCallerMutArmState x flag (mirJoinDiamondThenVal x))

/-- **Negative control (`mirJoinCallerMutRef_equal_memory_rejected`)**: because the two arms write
    different `u64` values (`x + 20` vs `x + 10`) through `*_1` into `Memory.callerLocals[4]`,
    their `Memory` states are not equal (`sElse.memory ≠ sThen.memory`), so the equal-`Memory`
    `MirArmsAgree` cannot merge this diamond. -/
theorem mirJoinCallerMutRef_equal_memory_rejected :
    ¬ MirArmsAgree mirJoinCallerMutLocalDiffers
      (mirJoinCallerMutArmState 0 0 (mirJoinDiamondElseVal 0))
      (mirJoinCallerMutArmState 0 0 (mirJoinDiamondThenVal 0)) := by
  intro h
  have hSlot := congrArg (fun m : Memory => match m.callerLocals with
    | _ :: _ :: _ :: _ :: .init (.scalar sc) :: _ => sc.bits
    | _ => 0) h.memory
  exact absurd hSlot (by decide)

theorem mirJoinCallerMutRef_arms_agree (x flag : Nat) :
    MirArmsAgreeWithCaller mirJoinCallerMutLocalDiffers mirJoinCallerMutCallerDiffers
      (mirJoinCallerMutArmState x flag (mirJoinDiamondElseVal x))
      (mirJoinCallerMutArmState x flag (mirJoinDiamondThenVal x)) :=
  ⟨rfl, rfl,
   ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ⟨rfl, rfl, rfl, rfl, trivial, rfl⟩, rfl, rfl, rfl⟩,
   ⟨rfl, rfl, rfl, rfl, rfl⟩⟩

/-- **Stateful `&mut u64` (`Memory.callerLocals`) Merged Join-Cut Witness
    (`mirJoinCallerMutRef_evalJoinDiamondWP`)**:
    Both arms write through `*_1` (`&mut u64`) into `Memory.callerLocals[4]`, `mergeMirMemory`
    pushes `if Nat.beq flag 0` inside `ScalarInt.bits` of `callerLocals[4]`, and `bb3` dereferences
    `*_1` and computes `_0 := *_1 + _2` **once** by `rfl` (certifying both the returned scalar and
    the mutated `Memory`!). -/
theorem mirJoinCallerMutRef_evalJoinDiamondWP (initOut x flag : Nat) :
    let armVal :=
      if Nat.beq flag 0 then mirJoinDiamondElseVal x else mirJoinDiamondThenVal x
    let expectedRet := wrapScalarBits (Nat.add armVal x) (scalarModulus 8)
    evalJoinDiamondWP 4 4 mirJoinCallerMutRefDiamondBody 3
      (mirJoinCallerMutInitState initOut x flag)
      (mirJoinCallerMutMergedState x flag)
      (mirNormalPost (fun retVal mem' =>
        retVal = .scalar ⟨expectedRet, 8⟩ ∧
          mem'.callerLocals =
            [ .dead, .dead, .dead, .dead
            , .init (.scalar { bits := armVal, sizeBytes := 8 }) ])) := by
  intro armVal expectedRet
  refine wpMirJoinDiamond_callerMerge_sound ?_ (mirJoinCallerMutRef_arms_agree x flag) ?_
  · show wpMirUntilJoinSym 4 mirJoinCallerMutRefDiamondBody 3 _
      (fun s' => s' = mirJoinCallerMutArmResult x flag) _
    ((conv => whnf); split); all_goals
      (rename_i hCond; change Nat.beq flag 0 = _ at hCond;
       dsimp only [mirJoinCallerMutArmResult]; rw [hCond]; rfl)
  · exact ⟨rfl, rfl⟩

theorem mirJoinCallerMutRef_wpMirSym_witness (initOut x flag : Nat) :
    let armVal :=
      if Nat.beq flag 0 then mirJoinDiamondElseVal x else mirJoinDiamondThenVal x
    let expectedRet := wrapScalarBits (Nat.add armVal x) (scalarModulus 8)
    wpMirSym 8 mirJoinCallerMutRefDiamondBody
      (mirJoinCallerMutInitState initOut x flag)
      (mirNormalPost (fun retVal mem' =>
        retVal = .scalar ⟨expectedRet, 8⟩ ∧
          mem'.callerLocals =
            [ .dead, .dead, .dead, .dead
            , .init (.scalar { bits := armVal, sizeBytes := 8 }) ])) :=
  wpMirSym_of_evalJoinDiamondWP (mirJoinCallerMutRef_evalJoinDiamondWP initOut x flag)

theorem mirJoinCallerMutRef_verified_witness (initOut x flag : Nat) :
    let armVal :=
      if Nat.beq flag 0 then mirJoinDiamondElseVal x else mirJoinDiamondThenVal x
    let expectedRet := wrapScalarBits (Nat.add armVal x) (scalarModulus 8)
    DWLP mirDefaultWP
      (mirTree mirJoinCallerMutRefDiamondBody (mirJoinCallerMutInitState initOut x flag))
      (fun out _ =>
        mirNormalPost (fun retVal mem' =>
          retVal = .scalar ⟨expectedRet, 8⟩ ∧
            mem'.callerLocals =
              [ .dead, .dead, .dead, .dead
              , .init (.scalar { bits := armVal, sizeBytes := 8 }) ]) out)
      PUnit.unit :=
  wpMirJoinDiamond_sound (mirJoinCallerMutRef_evalJoinDiamondWP initOut x flag)

def mirJoinGlobalAllocWith (b : UInt8) : CapturedAllocation :=
  { allocId := 99
    bytes := [some b]
    relocations := []
    align := { bytes := 1 }
    mutability := .mut }

/-- Minimal 1-block caller body restored when the callee returns from `Memory.callStack`:
    receives the callee return value in `_0` (`destination := { local_ := 0, projection := [] }`)
    and immediately executes `return_`. -/
def mirJoinCallerReturnBody : CapturedMir :=
  { mirJoinCallerMutRefDiamondBody with
    defPath := "SymbolicEval::mirJoinCallerReturnBody"
    argCount := 1
    localDecls :=
      [ { mutability := .mut, ty := u64JoinMirTy, debugName := some "_0" }
      , { mutability := .mut, ty := u64JoinMirTy, debugName := some "_1" } ]
    basicBlocks :=
      [ { statements := []
          terminator := { kind := .return_, span := "SymbolicEval.lean" }
          isCleanup := false } ] }

def mirJoinSavedFrameWith (v : Nat) : SavedCallerFrame :=
  { callerBody := mirJoinCallerReturnBody
    frame :=
      { blockIdx := 0
        stmtIdx := 0
        locals := [ .uninit, .init (.scalar { bits := v, sizeBytes := 8 }) ] }
    destination := { local_ := 0, projection := [] }
    returnTarget := 0 }

def mirJoinCallStackBorrowEntry : BorrowEntry :=
  { tag := 1
    perm := .active
    targetLocal := 1
    targetFrameDepth := 0
    targetProjection := []
    protector := none
    rangeOffset := 0
    rangeLen := 8 }

def mirJoinFullMemoryWith (b : UInt8) (v : Nat) : Memory :=
  { emptyMemory with
    globals := [mirJoinGlobalAllocWith b]
    borrows := [mirJoinCallStackBorrowEntry]
    nextTag := 2
    callStack := [mirJoinSavedFrameWith v]
    callerLocals :=
      [ .dead, .dead, .dead, .dead
      , .init (.scalar { bits := v, sizeBytes := 8 }) ] }

def mirJoinFullInitState (initOut x flag : Nat) : MachineState :=
  let s0 :=
    initMachineState mirJoinCallerMutRefDiamondBody
      [.ptr { allocId := 1, offsetBytes := 0 } 8, .scalar ⟨x, 8⟩, .scalar ⟨flag, 8⟩]
  { s0 with
    memory :=
      { emptyMemory with
        globals := [mirJoinGlobalAllocWith (if Nat.beq flag 0 then 20 else 10)]
        borrows := [mirJoinCallStackBorrowEntry]
        nextTag := 2
        callStack := [mirJoinSavedFrameWith initOut]
        callerLocals :=
          [ .dead, .dead, .dead, .dead
          , .init (.scalar
              { bits := if Nat.beq flag 0 then mirJoinDiamondElseVal x else mirJoinDiamondThenVal x
                sizeBytes := 8 }) ] } }

def mirJoinFullArmState (x flag : Nat) (b : UInt8) (outVal : Nat) : MachineState :=
  { frame :=
      { blockIdx := 3
        stmtIdx := 0
        locals :=
          [ .uninit
          , .init (.ptr { allocId := 1, offsetBytes := 0 } 8)
          , .init (.scalar ⟨x, 8⟩)
          , .init (.scalar ⟨flag, 8⟩) ] }
    memory := mirJoinFullMemoryWith b outVal }

def mirJoinFullGlobalDiffers : List (List Bool) := [[true]]
def mirJoinFullStackDiffers : List (List Bool) := [[false, true]]

def mirJoinFullArmResult (x flag : Nat) : MachineState :=
  if Nat.beq flag 0 then mirJoinFullArmState x flag 20 (mirJoinDiamondElseVal x)
  else mirJoinFullArmState x flag 10 (mirJoinDiamondThenVal x)

def mirJoinFullMergedState (x flag : Nat) : MachineState :=
  mergeMirJoinStateFull (Nat.beq flag 0)
    mirJoinCallerMutLocalDiffers mirJoinCallerMutCallerDiffers
    mirJoinFullGlobalDiffers mirJoinFullStackDiffers
    (mirJoinFullArmState x flag 20 (mirJoinDiamondElseVal x))
    (mirJoinFullArmState x flag 10 (mirJoinDiamondThenVal x))

/-- **Negative control (`mirJoinFullMemory_callerOnly_rejected`)**: when the two arms also diverge in
    `Memory.globals` (`20 : UInt8` vs `10 : UInt8`) and `Memory.callStack`, the `callerLocals`-only
    `MirArmsAgreeWithCaller` rejects the merge (`sElse.memory.globals ≠ sThen.memory.globals`). -/
theorem mirJoinFullMemory_callerOnly_rejected :
    ¬ MirArmsAgreeWithCaller mirJoinCallerMutLocalDiffers mirJoinCallerMutCallerDiffers
      (mirJoinFullArmState 0 0 20 (mirJoinDiamondElseVal 0))
      (mirJoinFullArmState 0 0 10 (mirJoinDiamondThenVal 0)) := by
  intro h
  have hByte := congrArg (fun gs : List CapturedAllocation => match gs with
    | a :: _ => a.bytes
    | [] => []) h.memory.globals
  exact absurd hByte (by decide)

theorem mirJoinFullMemory_arms_agree (x flag : Nat) :
    MirArmsAgreeFull mirJoinCallerMutLocalDiffers mirJoinCallerMutCallerDiffers
      mirJoinFullGlobalDiffers mirJoinFullStackDiffers
      (mirJoinFullArmState x flag 20 (mirJoinDiamondElseVal x))
      (mirJoinFullArmState x flag 10 (mirJoinDiamondThenVal x)) :=
  ⟨rfl, rfl,
   ⟨rfl,
    ⟨⟨rfl, ⟨trivial, rfl⟩, rfl, rfl, rfl⟩, rfl⟩,
    rfl, rfl, rfl, rfl,
    ⟨⟨rfl, rfl, rfl, ⟨rfl, trivial, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩,
    rfl, rfl, rfl,
    ⟨rfl, rfl, rfl, rfl, trivial, rfl⟩,
    rfl, rfl, rfl⟩,
   ⟨rfl, rfl, rfl, rfl, rfl⟩⟩

/-- **Full-Memory (`globals` + `callStack` + `callerLocals`) Merged Join-Cut Witness
    (`mirJoinFullMemory_evalJoinDiamondWP`)**:
    Both diamond arms (`bb1` and `bb2` of `mirJoinCallerMutRefDiamondBody`) write through `*_1` into
    `Memory.callStack[0].frame.locals[1]` via `evalForeignFrameDerefWrite` while carrying diverging
    `CapturedAllocation` bytes in `Memory.globals` (`20 : UInt8` vs `10 : UInt8`) and diverging
    `Memory.callerLocals`. At `bb3`, `wpMirJoinDiamond_fullMemoryMerge_sound` merges all three memory
    regions and evaluates `bb3` **once**: dereferencing `*_1` from `callStack[0].frame.locals[1]`,
    computing `_0 := *_1 + _2`, popping `callStack[0]` on `return_` into `mirJoinCallerReturnBody`,
    and certifying the returned scalar plus the merged `globals` byte and `callerLocals` slot. -/
theorem mirJoinFullMemory_evalJoinDiamondWP (initOut x flag : Nat) :
    let armByte : UInt8 := if Nat.beq flag 0 then 20 else 10
    let armVal :=
      if Nat.beq flag 0 then mirJoinDiamondElseVal x else mirJoinDiamondThenVal x
    let expectedRet := wrapScalarBits (Nat.add armVal x) (scalarModulus 8)
    evalJoinDiamondWP 4 5 mirJoinCallerMutRefDiamondBody 3
      (mirJoinFullInitState initOut x flag)
      (mirJoinFullMergedState x flag)
      (mirNormalPost (fun retVal mem' =>
        retVal = .scalar ⟨expectedRet, 8⟩ ∧
          mem'.globals = [mirJoinGlobalAllocWith armByte] ∧
          mem'.callStack = [] ∧
          mem'.callerLocals =
            [ .dead, .dead, .dead, .dead
            , .init (.scalar { bits := armVal, sizeBytes := 8 }) ])) := by
  intro armByte armVal expectedRet
  refine wpMirJoinDiamond_fullMemoryMerge_sound ?_ (mirJoinFullMemory_arms_agree x flag) ?_
  · show wpMirUntilJoinSym 4 mirJoinCallerMutRefDiamondBody 3 _
      (fun s' => s' = mirJoinFullArmResult x flag) _
    ((conv => whnf); split); all_goals
      (rename_i hCond; change Nat.beq flag 0 = _ at hCond;
       dsimp only [mirJoinFullArmResult, mirJoinFullInitState]; rw [hCond]; rfl)
  · refine ⟨rfl, ?_, rfl, rfl⟩
    dsimp only [armByte]
    cases Nat.beq flag 0 <;> rfl

theorem mirJoinFullMemory_wpMirSym_witness (initOut x flag : Nat) :
    let armByte : UInt8 := if Nat.beq flag 0 then 20 else 10
    let armVal :=
      if Nat.beq flag 0 then mirJoinDiamondElseVal x else mirJoinDiamondThenVal x
    let expectedRet := wrapScalarBits (Nat.add armVal x) (scalarModulus 8)
    wpMirSym 9 mirJoinCallerMutRefDiamondBody
      (mirJoinFullInitState initOut x flag)
      (mirNormalPost (fun retVal mem' =>
        retVal = .scalar ⟨expectedRet, 8⟩ ∧
          mem'.globals = [mirJoinGlobalAllocWith armByte] ∧
          mem'.callStack = [] ∧
          mem'.callerLocals =
            [ .dead, .dead, .dead, .dead
            , .init (.scalar { bits := armVal, sizeBytes := 8 }) ])) :=
  wpMirSym_of_evalJoinDiamondWP (mirJoinFullMemory_evalJoinDiamondWP initOut x flag)

theorem mirJoinFullMemory_verified_witness (initOut x flag : Nat) :
    let armByte : UInt8 := if Nat.beq flag 0 then 20 else 10
    let armVal :=
      if Nat.beq flag 0 then mirJoinDiamondElseVal x else mirJoinDiamondThenVal x
    let expectedRet := wrapScalarBits (Nat.add armVal x) (scalarModulus 8)
    DWLP mirDefaultWP
      (mirTree mirJoinCallerMutRefDiamondBody (mirJoinFullInitState initOut x flag))
      (fun out _ =>
        mirNormalPost (fun retVal mem' =>
          retVal = .scalar ⟨expectedRet, 8⟩ ∧
            mem'.globals = [mirJoinGlobalAllocWith armByte] ∧
            mem'.callStack = [] ∧
            mem'.callerLocals =
              [ .dead, .dead, .dead, .dead
              , .init (.scalar { bits := armVal, sizeBytes := 8 }) ]) out)
      PUnit.unit :=
  wpMirJoinDiamond_sound (mirJoinFullMemory_evalJoinDiamondWP initOut x flag)

/-- Canonicalize a `MirSemantics.LocalSlot` against a liveness bit (`true` = live at join,
    `false` = dead/scratch at join): dead/scratch slots are reset to `.dead` (the production
    `MirSemantics` analogue of `CanonLocals.canonicalize`). -/
def canonicalizeMirSlot (live : Bool) (s : LocalSlot) : LocalSlot :=
  if live then s else .dead

/-- Pointwise liveness canonicalization of a `List LocalSlot` local store. -/
def canonicalizeMirLocals : List Bool → List LocalSlot → List LocalSlot
  | live :: restMask, s :: restSlots =>
    canonicalizeMirSlot live s :: canonicalizeMirLocals restMask restSlots
  | _, slots => slots

theorem canonicalizeMirSlot_idempotent (live : Bool) (s : LocalSlot) :
    canonicalizeMirSlot live (canonicalizeMirSlot live s) = canonicalizeMirSlot live s := by
  cases live <;> rfl

theorem canonicalizeMirLocals_idempotent :
    ∀ (mask : List Bool) (slots : List LocalSlot),
      canonicalizeMirLocals mask (canonicalizeMirLocals mask slots) =
        canonicalizeMirLocals mask slots
  | [], _ => rfl
  | _ :: _, [] => rfl
  | live :: restMask, s :: restSlots => by
    simp [canonicalizeMirLocals, canonicalizeMirSlot_idempotent,
      canonicalizeMirLocals_idempotent restMask restSlots]

/-- Two `MirSemantics` local stores are live-equivalent under `liveMask` iff their canonicalized
    stores are equal. -/
def MirLocalsLiveEquiv (liveMask : List Bool) (lT lF : List LocalSlot) : Prop :=
  canonicalizeMirLocals liveMask lT = canonicalizeMirLocals liveMask lF

/-- Two `MachineState`s arriving at a join block are live-equivalent under `liveMask` iff they agree
    on `blockIdx`, `stmtIdx`, `memory`, and `canonicalizeMirLocals liveMask`. -/
structure MirStateLiveEquiv (liveMask : List Bool) (sT sF : MachineState) : Prop where
  blockIdx : sT.frame.blockIdx = sF.frame.blockIdx
  stmtIdx : sT.frame.stmtIdx = sF.frame.stmtIdx
  memory : sT.memory = sF.memory
  locals : MirLocalsLiveEquiv liveMask sT.frame.locals sF.frame.locals

/-- **Bridge from `MirLocalsLiveEquiv` (`liveMask`) to `MirArmSlotsAgree` (`differs = liveMask.map Bool.not`)**:
    any two local stores whose `liveMask`-canonicalizations are equal automatically satisfy
    `MirArmSlotsAgree (liveMask.map Bool.not) lT lF` (every `live = true` slot is equal in `lT` and
    `lF`, while every `live = false` dead/scratch slot has `differs = true`). -/
theorem mirArmSlotsAgree_of_liveEquiv :
    ∀ (liveMask : List Bool) {lT lF : List LocalSlot},
      MirLocalsLiveEquiv liveMask lT lF →
      MirArmSlotsAgree (liveMask.map Bool.not) lT lF
  | [], _, _, h => h
  | _ :: _, [], [], _ => rfl
  | _ :: _, [], _ :: _, h => by cases h
  | _ :: _, _ :: _, [], h => by cases h
  | true :: restMask, _ :: restT, _ :: restF, h => by
    injection h with hHead hTail
    exact ⟨hHead, mirArmSlotsAgree_of_liveEquiv restMask hTail⟩
  | false :: restMask, _ :: restT, _ :: restF, h => by
    injection h with _ hTail
    exact ⟨trivial, mirArmSlotsAgree_of_liveEquiv restMask hTail⟩

theorem mirArmsAgree_of_liveEquiv {liveMask : List Bool} {sT sF : MachineState}
    (h : MirStateLiveEquiv liveMask sT sF) :
    MirArmsAgree (liveMask.map Bool.not) sT sF :=
  ⟨h.blockIdx, h.stmtIdx, h.memory, mirArmSlotsAgree_of_liveEquiv liveMask h.locals⟩

/-- **Live-Equivalence Diamond Join Cut (`wpMirJoinDiamond_liveEquiv_sound`)**:
    if two `SwitchInt` arms reach `joinBb` in states `sT, sF` that are `MirStateLiveEquiv liveMask sT sF`
    (their `canonicalizeMirLocals liveMask` stores are identical, while dead/scratch slots where
    `liveMask[i] = false` may diverge arbitrarily), then proving `wpMirSym` **once** on
    `mergeMirJoinState cond (liveMask.map Bool.not) sT sF` discharges `evalJoinDiamondWP`. -/
theorem wpMirJoinDiamond_liveEquiv_sound
    {prefixFuel suffixFuel : Nat} {body : CapturedMir} {joinBb : BasicBlockIdx}
    {s : MachineState} {cond : Bool} {liveMask : List Bool} {sT sF : MachineState}
    {post : MirOutcome → Prop}
    (hPrefix : wpMirUntilJoinSym prefixFuel body joinBb (.running s)
      (fun s' => s' = if cond then sT else sF) post)
    (hLive : MirStateLiveEquiv liveMask sT sF)
    (hJoin : wpMirSym suffixFuel body (mergeMirJoinState cond (liveMask.map Bool.not) sT sF) post) :
    evalJoinDiamondWP prefixFuel suffixFuel body joinBb s
      (mergeMirJoinState cond (liveMask.map Bool.not) sT sF) post :=
  wpMirJoinDiamond_merge_sound hPrefix (mirArmsAgree_of_liveEquiv hLive) hJoin

theorem wpMirJoinDiamond_liveEquiv_dwlp_sound
    {prefixFuel : Nat} {body : CapturedMir} {joinBb : BasicBlockIdx}
    {s : MachineState} {cond : Bool} {liveMask : List Bool} {sT sF : MachineState}
    {post : MirOutcome → Prop}
    (hPrefix : wpMirUntilJoinSym prefixFuel body joinBb (.running s)
      (fun s' => s' = if cond then sT else sF) post)
    (hLive : MirStateLiveEquiv liveMask sT sF)
    (hJoin : DWLP mirDefaultWP
      (mirTree body (mergeMirJoinState cond (liveMask.map Bool.not) sT sF))
      (fun out _ => post out) PUnit.unit) :
    DWLP mirDefaultWP (mirTree body s) (fun out _ => post out) PUnit.unit :=
  wpMirJoinDiamond_merge_dwlp_sound hPrefix (mirArmsAgree_of_liveEquiv hLive) hJoin

/-- Concrete witness: the asymmetric scratch-slot arm states of `mirJoinAsymmetricScratchBody`
    (where slot `_3` is `.dead` in one arm and `.init (.scalar ⟨x + 1, 8⟩)` in the other) are
    `MirStateLiveEquiv [false, true, true, false]`! -/
theorem mirJoinAsymmetricScratch_liveEquiv (x flag : Nat) :
    MirStateLiveEquiv [false, true, true, false]
      (mirJoinAsymmetricArmState x flag (mirJoinDiamondElseVal x) .dead)
      (mirJoinAsymmetricArmState x flag (mirJoinDiamondThenVal x)
        (.init (.scalar ⟨wrapScalarBits (Nat.add x 1) (scalarModulus 8), 8⟩))) :=
  ⟨rfl, rfl, rfl, rfl⟩

/-!
### `Value.uninit` & `Memory.rootUnwindCeiling` Join-Cut Regressions

`Memory.rootUnwindCeiling` is narrowed to `false` by `enterTailCalleeFrame` when a non-unwinding
tail callee replaces the root activation, and `Value.uninit` marks an uninitialized sub-value of a
partially initialized aggregate. `mergeMirMemory` / `mergeMirMemoryFull` keep the `then` arm's
ceiling without an `ite`, so `MirMemoryAgree` / `MirMemoryAgreeFull` demand equal ceilings (without
that field `mergeMirMemory_false` / `mergeMirMemoryFull_false` would be false:
`mirJoinUninitCeiling_ceiling_mismatch_rejected`). A hinted slot holding or containing
`Value.uninit` merges to the slot-level `if cond then sT else sF`, never to an initialized scalar,
and an unhinted slot may not silently pair `Value.uninit` with an initialized value.
-/

theorem mergeMirMemory_rootUnwindCeiling (cond : Bool) (callerDiffers : List Bool)
    (mT mF : Memory) :
    (mergeMirMemory cond callerDiffers mT mF).rootUnwindCeiling = mT.rootUnwindCeiling := rfl

theorem mergeMirMemoryFull_rootUnwindCeiling (cond : Bool) (callerDiffers : List Bool)
    (globalDiffers stackDiffers : List (List Bool)) (mT mF : Memory) :
    (mergeMirMemoryFull cond callerDiffers globalDiffers stackDiffers mT mF).rootUnwindCeiling =
      mT.rootUnwindCeiling := rfl

/-- A hinted slot with `Value.uninit` on either arm is merged as the slot-level `ite`: the
    equal-width scalar fold never fabricates initialized bits from an uninitialized arm. -/
theorem mergeMirScalarSlot_uninit (cond : Bool) (sc : ScalarInt) :
    mergeMirScalarSlot cond true (.init .uninit) (.init (.scalar sc)) =
        (if cond then .init .uninit else .init (.scalar sc)) ∧
      mergeMirScalarSlot cond true (.init (.scalar sc)) (.init .uninit) =
        (if cond then .init (.scalar sc) else .init .uninit) :=
  ⟨rfl, rfl⟩

def mirJoinUninitThenLocal : Value := .aggregate 0 [.uninit, .scalar ⟨1, 8⟩]
def mirJoinUninitElseLocal : Value := .aggregate 0 [.scalar ⟨2, 8⟩, .uninit]
def mirJoinUninitThenCaller : Value := .aggregate 0 [.uninit, .scalar ⟨3, 8⟩]
def mirJoinUninitElseCaller : Value := .uninit

/-- Root-frame memory with root unwind ceiling `ceiling` and caller-owned referent `callerVal`
    (possibly `Value.uninit` or an aggregate containing it) at `callerLocals[0]`. -/
def mirJoinUninitCeilingMem (ceiling : Bool) (callerVal : Value) : Memory :=
  { emptyMemory with
    callerLocals := [.init callerVal, .init (.scalar ⟨7, 8⟩)]
    rootUnwindCeiling := ceiling }

def mirJoinUninitCeilingState (ceiling : Bool) (localVal callerVal : Value) : MachineState :=
  { frame := { blockIdx := 3, stmtIdx := 0, locals := [.init localVal, .init (.scalar ⟨7, 8⟩)] }
    memory := mirJoinUninitCeilingMem ceiling callerVal }

/-- `then` / `else` arm states at the join block: narrowed ceiling (`false`) on both arms, and
    slot 0 of both the frame locals and `Memory.callerLocals` holds different partially
    initialized (`Value.uninit`-containing) values. -/
def mirJoinUninitArmT : MachineState :=
  mirJoinUninitCeilingState false mirJoinUninitThenLocal mirJoinUninitThenCaller

def mirJoinUninitArmF : MachineState :=
  mirJoinUninitCeilingState false mirJoinUninitElseLocal mirJoinUninitElseCaller

theorem mirJoinUninitCeiling_arms_agree :
    MirArmsAgreeFull [true, false] [true, false] [] [] mirJoinUninitArmT mirJoinUninitArmF :=
  ⟨rfl, rfl,
   ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ⟨trivial, rfl, rfl⟩, rfl, rfl, rfl⟩,
   ⟨trivial, rfl, rfl⟩⟩

theorem mirJoinUninitCeiling_caller_arms_agree :
    MirArmsAgreeWithCaller [true, false] [true, false] mirJoinUninitArmT mirJoinUninitArmF :=
  ⟨rfl, rfl,
   ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ⟨trivial, rfl, rfl⟩, rfl, rfl, rfl⟩,
   ⟨trivial, rfl, rfl⟩⟩

/-- The full-memory merge of the narrowed-ceiling arms keeps `rootUnwindCeiling = false`, keeps
    each `Value.uninit`-carrying hinted slot as a slot-level `ite`, and is the state-level
    `if cond then sT else sF`. -/
theorem mirJoinUninitCeiling_merge (cond : Bool) :
    (mergeMirJoinStateFull cond [true, false] [true, false] [] []
        mirJoinUninitArmT mirJoinUninitArmF).memory.rootUnwindCeiling = false ∧
      (mergeMirJoinStateFull cond [true, false] [true, false] [] []
        mirJoinUninitArmT mirJoinUninitArmF).frame.locals =
        [ if cond then .init mirJoinUninitThenLocal else .init mirJoinUninitElseLocal
        , .init (.scalar ⟨7, 8⟩) ] ∧
      (mergeMirJoinStateFull cond [true, false] [true, false] [] []
        mirJoinUninitArmT mirJoinUninitArmF).memory.callerLocals =
        [ if cond then .init mirJoinUninitThenCaller else .init mirJoinUninitElseCaller
        , .init (.scalar ⟨7, 8⟩) ] ∧
      mergeMirJoinStateFull cond [true, false] [true, false] [] []
        mirJoinUninitArmT mirJoinUninitArmF =
        (if cond then mirJoinUninitArmT else mirJoinUninitArmF) ∧
      mergeMirJoinStateWithCaller cond [true, false] [true, false]
        mirJoinUninitArmT mirJoinUninitArmF =
        (if cond then mirJoinUninitArmT else mirJoinUninitArmF) :=
  ⟨rfl, rfl, rfl, mergeMirJoinStateFull_eq_ite mirJoinUninitCeiling_arms_agree,
   mergeMirJoinStateWithCaller_eq_ite mirJoinUninitCeiling_caller_arms_agree⟩

/-- `Lower.strictMachineState` (the spine normalizer of `stepMirStateStrict`, which normalizes
    `rootUnwindCeiling` via `strictBool` and `Value.uninit` via `strictValue`) is the identity on
    the merged narrowed-ceiling state for both concrete branch conditions. -/
theorem mirJoinUninitCeiling_merge_strict (cond : Bool) :
    strictMachineState 0
        (mergeMirJoinStateFull cond [true, false] [true, false] [] []
          mirJoinUninitArmT mirJoinUninitArmF) =
      .some (if cond then mirJoinUninitArmT else mirJoinUninitArmF) := by
  cases cond <;> rfl

/-- Arms that differ only in `rootUnwindCeiling` are rejected by both agreement relations, and the
    `cond = false` merges would wrongly keep the `then` arm's ceiling, so the ceiling field of
    `MirMemoryAgree` / `MirMemoryAgreeFull` is load-bearing for `mergeMirMemory_false` /
    `mergeMirMemoryFull_false`. -/
theorem mirJoinUninitCeiling_ceiling_mismatch_rejected :
    ¬ MirMemoryAgree [] (mirJoinUninitCeilingMem false .uninit)
        (mirJoinUninitCeilingMem true .uninit) ∧
      ¬ MirMemoryAgreeFull [] [] [] (mirJoinUninitCeilingMem false .uninit)
        (mirJoinUninitCeilingMem true .uninit) ∧
      mergeMirMemory false [] (mirJoinUninitCeilingMem false .uninit)
        (mirJoinUninitCeilingMem true .uninit) ≠ mirJoinUninitCeilingMem true .uninit ∧
      mergeMirMemoryFull false [] [] [] (mirJoinUninitCeilingMem false .uninit)
        (mirJoinUninitCeilingMem true .uninit) ≠ mirJoinUninitCeilingMem true .uninit :=
  ⟨fun h => Bool.false_ne_true h.rootUnwindCeiling,
   fun h => Bool.false_ne_true h.rootUnwindCeiling,
   fun h => Bool.false_ne_true (congrArg Memory.rootUnwindCeiling h),
   fun h => Bool.false_ne_true (congrArg Memory.rootUnwindCeiling h)⟩

/-- An unhinted local or caller slot may not pair a `Value.uninit`-carrying value with a
    different one: both full-memory agreement obligations fail on slot 0. -/
theorem mirJoinUninitCeiling_unhinted_uninit_rejected :
    ¬ MirArmsAgreeFull [false, false] [true, false] [] [] mirJoinUninitArmT mirJoinUninitArmF ∧
      ¬ MirArmsAgreeFull [true, false] [false, false] [] [] mirJoinUninitArmT mirJoinUninitArmF := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have hSlot : LocalSlot.init mirJoinUninitThenLocal = .init mirJoinUninitElseLocal :=
      h.locals.1
    cases hSlot
  · have hSlot : LocalSlot.init mirJoinUninitThenCaller = .init mirJoinUninitElseCaller :=
      h.memory.callerLocals.1
    cases hSlot

/-- Production join cut for the narrowed-ceiling, `Value.uninit`-carrying diamond: proving
    `wpMirSym` once on the merged state discharges `evalJoinDiamondWP` for every prefix that
    reaches `if cond then mirJoinUninitArmT else mirJoinUninitArmF`. -/
theorem mirJoinUninitCeiling_fullMemoryMerge_sound
    {prefixFuel suffixFuel : Nat} {body : CapturedMir} {joinBb : BasicBlockIdx}
    {s : MachineState} {cond : Bool} {post : MirOutcome → Prop}
    (hPrefix : wpMirUntilJoinSym prefixFuel body joinBb (.running s)
      (fun s' => s' = if cond then mirJoinUninitArmT else mirJoinUninitArmF) post)
    (hJoin : wpMirSym suffixFuel body
      (mergeMirJoinStateFull cond [true, false] [true, false] [] []
        mirJoinUninitArmT mirJoinUninitArmF) post) :
    evalJoinDiamondWP prefixFuel suffixFuel body joinBb s
      (mergeMirJoinStateFull cond [true, false] [true, false] [] []
        mirJoinUninitArmT mirJoinUninitArmF) post :=
  wpMirJoinDiamond_fullMemoryMerge_sound hPrefix mirJoinUninitCeiling_arms_agree hJoin

private def mirJoinUninitJoinOnlyBody (bb3 : BasicBlockData) : CapturedMir :=
  let dummyBb : BasicBlockData :=
    { statements := [], terminator := { kind := .unreachable, span := "SymbolicEval.lean" }
      isCleanup := false }
  { defPath := "sym_eval::mir_join_uninit_ceiling_witness"
    phase := .runtimePostCleanup
    role := .subject
    argCount := 1
    localDecls :=
      [ { mutability := .mut, ty := u64JoinMirTy, debugName := none }
      , { mutability := .not, ty := u64JoinMirTy, debugName := none } ]
    basicBlocks := [dummyBb, dummyBb, dummyBb, bb3]
    fnAbi := defaultU64JoinFnAbi
    layouts := emptyLayoutTable
    allocations := [] }

/-- Join block (`bb3`) that resumes unwinding: under `rootUnwindCeiling = false` it must fault
    with `.ub`, whereas under `rootUnwindCeiling = true` it escapes as `.returned .panic`. -/
def mirJoinUninitCeilingUnwindBody : CapturedMir :=
  mirJoinUninitJoinOnlyBody
    { statements := [], terminator := { kind := .unwindResume, span := "SymbolicEval.lean" }
      isCleanup := true }

/-- Operational `stepMirState` witness: the merged narrowed-ceiling state keeps
    `rootUnwindCeiling = false` unsplit, so `.unwindResume` at `bb3` faults with `.ub` for a
    symbolic `cond` by `rfl`, while an open ceiling (`true`) halts with `Outcome.panic`. -/
theorem mirJoinUninitCeiling_merge_unwind_ub (cond : Bool) :
    stepMirState mirJoinUninitCeilingUnwindBody
        (.running (mergeMirJoinStateFull cond [true, false] [true, false] [] []
          mirJoinUninitArmT mirJoinUninitArmF)) =
        MirStepNode.fail .ub ∧
      wpMirSym 2 mirJoinUninitCeilingUnwindBody
        (mirJoinUninitCeilingState true mirJoinUninitThenLocal mirJoinUninitThenCaller)
        (fun out => out = .panic) :=
  ⟨rfl, rfl⟩

/-- Join block (`bb3`) that re-initializes the `Value.uninit`-carrying slot `_0` via
    `StorageLive(_0); _0 := _1; return` without ever reading the merged `Value.uninit` slot. -/
def mirJoinUninitOverwriteBody : CapturedMir :=
  mirJoinUninitJoinOnlyBody
    { statements :=
        [ { kind := .storageLive 0, span := "SymbolicEval.lean" }
        , { kind := .assign { local_ := 0, projection := [] }
              (.use (.copy { local_ := 1, projection := [] }))
            span := "SymbolicEval.lean" } ]
      terminator := { kind := .return_, span := "SymbolicEval.lean" }
      isCleanup := false }

/-- Operational `wpMirSym` witness: re-initializing the merged `Value.uninit`-carrying slot `_0`
    from the shared initialized slot `_1` discharges `wpMirSym` once for symbolic `cond` without
    splitting on `cond`. -/
theorem mirJoinUninitCeiling_merge_overwrite_ok (cond : Bool) :
    wpMirSym 5 mirJoinUninitOverwriteBody
      (mergeMirJoinStateFull cond [true, false] [true, false] [] []
        mirJoinUninitArmT mirJoinUninitArmF)
      (mirNormalPost (fun retVal _ => retVal = .scalar ⟨7, 8⟩)) :=
  rfl

/-- Join block (`bb3`) that returns `_0` directly, reading the merged `Value.uninit`-carrying
    aggregate. -/
def mirJoinUninitReadFaultBody : CapturedMir :=
  mirJoinUninitJoinOnlyBody
    { statements := [], terminator := { kind := .return_, span := "SymbolicEval.lean" }
      isCleanup := false }

/-- Operational negative control: reading the merged `Value.uninit`-carrying slot `_0` faults with
    `.ub` on both arms (`cond = true` and `cond = false`). -/
theorem mirJoinUninitCeiling_merge_read_uninit_ub (cond : Bool) :
    stepMirState mirJoinUninitReadFaultBody
        (.running (mergeMirJoinStateFull cond [true, false] [true, false] [] []
          mirJoinUninitArmT mirJoinUninitArmF)) =
      MirStepNode.fail .ub := by
  cases cond <;> rfl

end MirJoinDiamondWitness

/-!
## Axiom Policy

Every GVN, canonical-state, join-cut, aliasing, witness, operator-bridge and fuel-level
`MirSemantics` join-cut theorem across the GVN / join-cut submodules depends on at most
`{propext, Quot.sound}`: no `sorryAx`, no `Lean.ofReduceBool` (closed witnesses use
`decide +kernel`), and no `Classical.choice` (the fuel-monotonicity, subtraction, low-mask,
and bitwise-complement lemmas avoid `omega` and `Nat.testBit_two_pow_sub_succ`, which can
introduce it). The only exceptions are the corollaries whose *statements* mention
`Anneal.ITreeWP.DWLP`/`DWP`
(`dwlp_of_wpMirUntilJoinSym`, `dwpMirJoinDiamond_sound`, `wpMirJoinDiamond_sound`,
`wpMirJoinDiamond_dwlp_sound`, `wpMirJoinDiamond_merge_dwlp_sound`,
`wpMirJoinDiamond_callerMerge_dwlp_sound`, `wpMirJoinDiamond_fullMemoryMerge_dwlp_sound`,
`wpMirJoinDiamond_liveEquiv_dwlp_sound`, `mirJoinDiamond_verified_witness`,
`mirSeqTwoDiamond_verified_witness`, `mirJoinTriangle_verified_witness`,
`mirJoinSwitch3_verified_witness`, `mirJoinCallerMutRef_verified_witness`,
`mirJoinFullMemory_verified_witness`): `DWLP`/`DWP` are
built with `coinductive_fixpoint`/`inductive_fixpoint` and themselves depend on `Classical.choice`,
so no proof of such a statement can avoid it, while their fuel-level premises
(`wpMirSym_of_evalJoinDiamondWP`, `wpMirJoinDiamond_merge_sound`,
`wpMirJoinDiamond_callerMerge_sound`, `wpMirJoinDiamond_fullMemoryMerge_sound`,
`wpMirJoinDiamond_liveEquiv_sound`, `wpMirJoinSwitch3_merge_sound`,
`mirJoinDiamond_wpMirSym_witness`, `mirJoinAsymmetricScratch_wpMirSym_witness`,
`mirSeqTwoDiamond_wpMirSym_witness`, `mirJoinTriangle_wpMirSym_witness`,
`mirJoinSwitch3_wpMirSym_witness`, `mirJoinCallerMutRef_wpMirSym_witness`,
`mirJoinFullMemory_wpMirSym_witness`, and the `Value.uninit` / `rootUnwindCeiling` regressions
`mirJoinUninitCeiling_fullMemoryMerge_sound`, `mirJoinUninitCeiling_merge_overwrite_ok`,
`mirJoinUninitCeiling_merge_unwind_ub`, `mirJoinUninitCeiling_merge_read_uninit_ub`) stay
`Classical.choice`-free.
`trusted/audit/TrustedBoundary.lean` admits no `#guard_msgs`/`#print` commands in audited modules,
so this inventory is checked out-of-file by `#print axioms` over the declarations above.
-/

end Anneal.Rustc.V2026_06_01.SymbolicEval
