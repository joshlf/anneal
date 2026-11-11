# Reproduction & Verification Guide — `BRIEF-2.2`: Polymorphic Callee & Trait-Method Resolution in `evalTerminator`

This document provides copy-pasteable commands to reproduce and verify all implementation, correspondence proof, citation, and trusted-audit deliverables for `BRIEF-2.2` across both `V2026_06_01` and `V2026_08_01`.

## 1. Environment & Worktree Setup

```bash
export PATH="$HOME/.cargo/bin:$HOME/.elan/bin:$PATH"
cd <path/to/anneal>
git status --short --branch
git log --oneline b0c981aa266df49e301989fea30f86b3c889b254..HEAD
```

- **Worktree**: `<path/to/anneal>`
- **Branch**: `adv/brief-2-2`
- **Base Commit**: `b0c981aa266df49e301989fea30f86b3c889b254` (`Merge BRIEF-2.1, BRIEF-2.3, and BRIEF-1.1 into adv/brief-2-2`)

## 2. Full Lean Build (`Trusted`, `Anneal`, `Correspondence`)

```bash
export PATH="$HOME/.cargo/bin:$HOME/.elan/bin:$PATH"
cd <path/to/anneal>/examples
lake build Trusted Anneal Correspondence
```

Expected output: `Build completed successfully (83 jobs).` with exit code `0` and zero warnings, `sorry`, or `axiom`.

## 3. Single-File Kernel Verification of Correspondence Proofs (`V2026_06_01` & `V2026_08_01`)

```bash
export PATH="$HOME/.cargo/bin:$HOME/.elan/bin:$PATH"
cd <path/to/anneal>/examples
lake env lean ../theory/Correspondence/V2026_06_01/L5_ControlAndCalls.lean
lake env lean ../theory/Correspondence/V2026_08_01/L5_ControlAndCalls.lean
lake env lean ../theory/Correspondence/V2026_06_01/L6_WholeProgramTransition.lean
lake env lean ../theory/Correspondence/V2026_08_01/L6_WholeProgramTransition.lean
```

Key kernel-checked theorems in `L5_ControlAndCalls.lean` (both dialects):
- `mir_evalTerminator_polymorphic_id_u32_and_u64_end_to_end`: end-to-end execution of polymorphic `id::<u32>(42)` and `id::<u64>(99)` from a single polymorphic `CapturedMir` (`typeParamCount := 1`), stepping through `evalTerminator` -> `pushCalleeFrame` -> callee `.return_` -> `popFrame` and writing the returned scalar into the caller destination local.
- `mir_evalTerminator_trait_method_mono_and_generic_dispatch`: end-to-end trait-method resolution (`lookupCallee` / `resolveCalleeBodyAndArgs?`) across monomorphic overrides, generic `impl<T> MyTrait<T> for Range<T>`, specificity ordering between blanket and concrete impls (`filterMostSpecificTraitImpls`), duplicate `TraitImplEntry` deduplication (`upsertMatchingTraitImpl`), ambiguous overlapping impl rejection, unlinked/mismatched-arity override rejection (no silent fallback to default trait method bodies), repeated and out-of-order `RigidTy.param` bindings, method-level generic parameters (`matchRigidTyPrefix`), and compound caller `RigidTy.param` substitution (`allParamsInCallerLayouts` / `callerParamSubst`).
- `mir_evalTerminator_inherited_default_and_subject_traitImpls_dispatch`: end-to-end verification of `implPath == defPath` entries that inherit a trait's default method body (instantiating the default body with the full call-site `typeArgs`), non-shadowing of generic `TraitImplEntry` records by already-instantiated copies in `upsertMatchingTraitImpl`, and seeding of `Memory.traitImpls` from `body.traitImpls` in `initMachineStateWithCallees`.
- `mir_evalTerminator_uninstantiated_trait_method_extCall`: universal proof that trait-method calls with an uninstantiated `Self = RigidTy.param` return `lookupCallee = .none` and step to `MirStepNode.extCall` carrying `MirCallReq.typeArgs`.
- `mir_evalTerminator_indirect_polymorphic_fnptr_call`: end-to-end characterization of `ReifyFnPointer` (`checkCalleeSig` with polymorphic and trait-method instantiation) and indirect `FnPtr` `.call`/`.tailCall` with post-instantiation ABI signature checking (`checkCalleeTargetCompatible`).

## 4. Trusted Audit (`check_trusted.py --fast`)

```bash
export PATH="$HOME/.cargo/bin:$HOME/.elan/bin:$PATH"
cd <path/to/anneal>
python3 trusted/audit/check_trusted.py --fast
```

Expected output: `PASS: 40 Trusted modules; 8233 Trusted kernel declarations` with exit code `0`.

## 5. Pinned `rustc` & Rust Reference Citation Audit

```bash
cd <path/to/anneal>
AUDIT_BASE=8fd01641^ python3 <path/to/agent-home>/.gemini/antigravity/brain/fd0946cc-f4f4-453a-baa6-f2748a0ac7fe/scratch/audit_citations.py
```

Expected output: `Checked 36 citations across 10 files; mismatches=0`.
