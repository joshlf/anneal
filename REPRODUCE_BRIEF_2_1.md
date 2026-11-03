# Reproduction Instructions for BRIEF-2.1

1. Check out the branch:
   ```bash
   git checkout adv/brief-2-1
   ```

2. Verify that the build succeeds:
   ```bash
   cd trusted/lean
   lake build
   cd ../../theory
   lake build
   ```

3. Run the TrustedBoundary audit script:
   ```bash
   python3 trusted/audit/check_trusted.py --fast
   ```

4. Both should exit with `0`. The changes introduce `RigidTy.param`, `RigidTy.alias`, `GenericParamDef`, `TraitRef`, `TraitImplEntry`, and `TypeSubst` to `MirAst/Types.lean`, update `CapturedMir` with default fields in `MirAst/Body.lean`, and implement `CapturedMir.instantiate` and `@[simp] theorem instantiate_nil` across both V2026_06_01 and V2026_08_01.
