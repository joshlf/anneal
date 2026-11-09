# Reproduction & Verification Guide — `BRIEF-2`: Option 1B First-Class Polymorphism in `MirAst`, `MirSemantics`, and `anneal-rustc-capture`

This document provides copy-pasteable commands to reproduce and verify the complete integrated `BRIEF-2` workstream (`BRIEF-2.1`, `BRIEF-2.2`, and `BRIEF-2.3`, integrated with `BRIEF-1.1`) in `<path/to/anneal>`.

## 1. Worktree & Branch State

- **Supervisor Worktree**: `<path/to/anneal>`
- **Branches**: `sup/brief-2` (also aliased to `adv/brief-2`)
- **Leaf Branches Integrated**:
  - `adv/brief-2-1` (`f4e8bf6b2a3d88c25fd5adf75968a827c1c64f8a`): Polymorphic `MirAst` (`RigidTy.param`, `RigidTy.alias`, `GenericParamDef`, `TraitRef`, `TraitImplEntry`, `TypeSubst`, parametric `LayoutTable` slots, and `CapturedMir.instantiate`) across `V2026_06_01` and `V2026_08_01`.
  - `adv/brief-2-3` (`15b58b2b30c898c70bec4bf2d380742ea63532c6`): Direct Polymorphic & Trait-Impl Emission in `anneal-rustc-capture` (`lower_rigid_ty`, `collect_generic_type_params`, `LayoutTableBuilder::new_with_type_params`, `canonical_def_path` disambiguation, and `TraitImplEntry` extraction).
  - `adv/brief-1-1` (`f515de96b6f6e123139680516e77ff985d3d53a8`): Function-Item Reification (`ReifyFnPointer`), `fnPtrToPtr` Casts, and Indirect `FnPtr` Calls.
  - `adv/brief-2-2` (`e9df689eee009409b7276470bb5c1d3c8431ad71`): Polymorphic Callee & Trait-Method Resolution in `evalTerminator` (`Memory.traitImpls`, `MirCallReq.typeArgs`, `lookupCallee`, `resolveCalleeBodyAndArgs?`, `matchRigidTyPrefix`, `filterMostSpecificTraitImpls`, `upsertMatchingTraitImpl`, `checkCalleeSig`, and `initMachineStateWithCallees`).

## 2. Step-by-Step Reproduction Commands

### Step 2.1: Lean 4 Kernel Build (`Trusted`, `Anneal`, `Correspondence`)
```bash
export PATH="$HOME/.cargo/bin:$HOME/.elan/bin:$PATH"
cd <path/to/anneal>/examples
lake build Trusted Anneal Correspondence
```
Expected output: `Build completed successfully (83 jobs).` with exit code `0` and zero warnings, `sorry`, or `axiom`.

### Step 2.2: Single-File Kernel Verification of Polymorphic AST & Call Semantics (`V2026_06_01` & `V2026_08_01`)
```bash
export PATH="$HOME/.cargo/bin:$HOME/.elan/bin:$PATH"
cd <path/to/anneal>/examples
lake env lean ../theory/Correspondence/V2026_06_01/L1_TypesAndLayouts.lean
lake env lean ../theory/Correspondence/V2026_08_01/L1_TypesAndLayouts.lean
lake env lean ../theory/Correspondence/V2026_06_01/L5_ControlAndCalls.lean
lake env lean ../theory/Correspondence/V2026_08_01/L5_ControlAndCalls.lean
lake env lean ../theory/Correspondence/V2026_06_01/L6_WholeMachine.lean
lake env lean ../theory/Correspondence/V2026_08_01/L6_WholeMachine.lean
```
Expected output: Exit code `0` for all 6 files with zero warnings.

### Step 2.3: Rust Compiler Driver & Polymorphic MIR Emission Tests (`anneal-rustc-capture`)
```bash
export PATH="$HOME/.cargo/bin:$HOME/.elan/bin:$PATH"
cd <path/to/anneal>
cargo test -p anneal-rustc-capture
```
Expected output: All unit and integration tests (including `driver_captures_generic_functions_and_trait_impls`) pass with exit code `0`.

### Step 2.4: Trusted Boundary & Citation Audit
```bash
export PATH="$HOME/.cargo/bin:$HOME/.elan/bin:$PATH"
cd <path/to/anneal>
python3 trusted/audit/check_trusted.py --fast
```
Expected output: `PASS: kernel dependency closure, statement-origin separation, and Cargo DAG boundary (40 Trusted modules; 8239 Trusted kernel declarations; 16381 total replayed declarations; 11 claim theorem statements origin-checked; axioms=['propext', 'Classical.choice', 'Quot.sound'])` with exit code `0`.
