# Reproduction Guide for FF-4.1 (`Anneal.SepLogicLenses`)

This guide documents the architecture, theorem inventory, and verification reproduction steps for **FF-4.1: Separation-Logic-Guarded Alias Erasure (`Anneal.SepLogicLenses`)** in `theory/Anneal/SepLogicLenses.lean`.

## Overview of Deliverables

`theory/Anneal/SepLogicLenses.lean` (exported by `theory/Anneal.lean`) replaces manual `Memory` record destructuring for `&mut`-bearing functions with a compositional separation-logic and functional-lens lifting layer:

1. **Section 1 — Independent Lens Algebra & Separation Logic Disjointness Bridge**:
   - `IndependentLenses`: Commutativity and non-interference (`get_set_other`, `get_set_other'`, `set_set_comm`) for pairs of `MutLens` over state `S`, with symmetry (`IndependentLenses.symm`).
   - `prodMutLens` & `prodMutLens_lawful`: Product of two independent lawful lenses `L₁ : MutLens S A` and `L₂ : MutLens S B` into a lawful `MutLens S (A × B)`.
   - `PairwiseIndependentLenses`: Lift pairwise lens independence across arbitrary lists of typed pointers.
   - `sepConj_activeTypedMutBorrow_disjoint` & `sepConj_entails_independentLenses`: Prove that separating conjunction `sepConj (ActiveTypedMutBorrow rp₁ codec₁ a₁) (sepConj (ActiveTypedMutBorrow rp₂ codec₂ a₂) R_frame)` in `m : Memory` forces `rp₁.allocId ≠ rp₂.allocId`, `rp₁.tag ≠ rp₂.tag`, and `IndependentLenses (memoryPtrMutLens rp₁ codec₁) (memoryPtrMutLens rp₂ codec₂)`.

2. **Section 2 — Separation-Logic-Guarded Deref Read/Write Lifting & Frame Preservation**:
   - `SepLensStateInv`: Invariant connecting a pure local environment `env : PureEnv`, a tracked list of dereferenced pointer values `entries : List (RawPtrVal × Value)`, and `m : Memory` (requiring `callStack = []`, `activeCallee = .none`, caller-frame target allocations `frameLen ≤ b.targetLocal`, valid caller local values, `ExclusiveActiveBorrow`, and pairwise distinct allocation IDs and tags).
   - `LensFramePreserved`: Guarantee that caller allocations and borrow tags outside the tracked pointer list remain unchanged across execution.
   - Inductive lifting relations extending `PureMirExec` to pointer operations:
     - `LiftDerefRead`: Reads `Operand.copy { local_ := ptrLoc, projection := [.deref] }` from the pure `entries` environment and proves Tree Borrows read-freezing (`freezeTreeBorrowsOnReadAtProj`) is an identity under `ExclusiveActiveBorrow`.
     - `LiftLensOperand` & `LiftLensRvalue`: Lift pure local/scalar operands, deref reads, binary operations, unary operations, and casts.
     - `LiftRetag`, `LiftDerefWrite`, `LiftPureAssign`, `LiftStorageLive`, `LiftStorageDead`, `LiftNop`, `LiftLensStmt`, `LiftLensStmts`, `LiftLensBlock`: Lift basic-block statements and control-flow transitions (`return_`, `goto`) over `(PureEnv, List (RawPtrVal × Value))`, proving `SepLensStateInv` and `LensFramePreserved` step-preservation (`LiftLensStmt.evalStmt_step`, `LiftLensStmts.exec_steps`).
   - Top-level fuel-free adequacy and verification bridges:
     - `mirWpConverges_of_liftLensStmts` & `mirWpConverges_of_sepLenses`
     - `verifyStatefulMir_of_sepLenses` & `verifyTotalMir_of_sepLenses`
     - `sepLensStateInv_of_sepConj_one` & `sepConj_activeTypedMutBorrow_preserved_one`
     - `sepLensStateInv_of_sepConj_two` & `sepConj_activeTypedMutBorrow_preserved_two`

3. **Section 3 — Concrete `add_assign` & `swap_u32` Verification (`Anneal.SepLogicLenses.Bench`)**:
   - `add_assign` & `add_assign_verified`: Concrete `CapturedMir` for `pub fn add_assign(x: &mut u32, delta: u32)` with retag, deref read (`*_1`), checked `u32` addition, and deref write (`*_1 = move _3`), discharged via `verifyStatefulMir_of_sepLenses` with separation-logic frame preservation and zero manual `Memory` destructuring.
   - `swap_u32` & `swap_u32_verified`: Concrete `CapturedMir` for `pub fn swap_u32(x: &mut u32, y: &mut u32)` with two retags, two deref reads (`*_1`, `*_2`), and two deref writes (`*_1 = copy _4`, `*_2 = copy _3`), discharged via `verifyStatefulMir_of_sepLenses` + `sepLensStateInv_of_sepConj_two` + `sepConj_activeTypedMutBorrow_preserved_two` with zero manual `Memory` destructuring.

## Environment Setup

```bash
export PATH="$HOME/.elan/bin:$HOME/.cargo/bin:$HOME/.local/bin:$PATH"
cd /usr/local/google/Projects/anneal-workspace/anneal-wt-ff-4-1
```

## Running Verification & Collecting Receipts

1. **Check for incomplete proof markers**:
   ```bash
   ./ci/check_todo.sh
   ```

2. **Audit Trusted Computing Base (TCB)**:
   ```bash
   python3 trusted/audit/check_trusted.py --fast
   ```

3. **Single-file Lean check on `SepLogicLenses.lean`**:
   ```bash
   cd examples && anneal-lean-run --mode file --concurrency 1 -- lake env lean ../theory/Anneal/SepLogicLenses.lean
   ```

4. **Full `Anneal` library build**:
   ```bash
   cd examples && anneal-lean-run --mode build --concurrency 1 -- lake build Anneal
   ```
