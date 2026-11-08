# Workstream Progress Document: MIR Pointer-to-Int Casts & MiniRust Correspondence

**Workstream ID**: `ws-diff-rc-d`  
**Title**: Support MIR Pointer-to-Int Casts & MiniRust Correspondence  
**Objective ID**: `OBJ-1-SHRINK-UNSUPPORTED-MIR`  
**Track**: `unstable` | **Priority**: `P1`  
**Lead Engineer (LDAP)**: `markdittmer`  
**Host Machine**: `cpl-nifty-canyon-4258.c.googlers.com` (`groupagent-anneal-bot`)  
**Active Milestone**: **Workstream Complete (Episodes 1 & 2 Verified)**  
**Active Branch**: `auto/ws-diff-rc-d` (Base: `unstable` at `a60d5c84cdfe2038f4e965c2a9c70c79f0c41009`)  
**Last Updated**: 2026-11-08T03:02:00Z  

---

## 1. Executive Status & Milestone Tracker

| Milestone | Scope / Deliverable | Status | Target Path | Verification Receipts |
|---|---|---|---|---|
| **Episode 1 (`ep1-lower-mir`)** | Lower Rvalue::Cast(PtrToInt / IntToPtr) in `anneal-mir` | **100% COMPLETE** | `anneal:crates/anneal-mir/src/lower/cast.rs` | `cargo test -p anneal-mir`: **13/13 PASS** (10 unit, 3 integration) |
| **Episode 2 (`ep2-lean-correspondence`)** | Prove MiniRust step correspondence for pointer-to-usize casts | **100% COMPLETE** | `anneal:theory/Anneal/Mir/Cast.lean` | `lake build Anneal.Mir.Cast`: **56/56 jobs clean** (0 warnings, 0 `sorry`) |

---

## 2. Resumption & Swarm UX

- **Node Lease**: Leased to `cpl-nifty-canyon-4258.c.googlers.com` (`groupagent-anneal-bot`).
- **Orchestration**: N-Round Adversarial implementation and verification with cross-family model diversity:
  - `AGENT_A_MODEL`: `gemini-launch-candidate-high` (Model Y)
  - `AGENT_B_MODEL`: `opus-5.5-max` (Model X)
  - `SUPERVISOR_MODEL`: `gemini-pro-coordinator`
  - `HELPER_MODEL`: `gemini-flash-next`
- **Narrator / Monitor**: Active in swarm; maintaining continuous progress records across execution waves.

---

## 3. Detailed Verification Summary

### Episode 1 (`ep1-lower-mir`): Complete
- Created `crates/anneal-mir` with `src/ir.rs`, `src/lower/mod.rs`, `src/lower/cast.rs`, and integration tests in `tests/cast_tests.rs`.
- Implemented lowering for `Rvalue::Cast(PointerExposeProvenance)` (`lower_ptr_to_int`) and `Rvalue::Cast(PointerWithExposedProvenance)` (`lower_int_to_ptr`).
- Implemented `ExposedProvenanceTracker` modeling MiniRust's `IntPtrCast::expose` and `int2ptr` semantics.
- Verified with `anneal-lean-run --mode build --concurrency 1 -- cargo test -p anneal-mir`: 13/13 passed.

### Episode 2 (`ep2-lean-correspondence`): Complete
- Created `theory/Anneal/Mir/Cast.lean` (`Anneal.Mir.Cast`).
- Proved exact roundtrip inversion between `ptrToAddress` and `addressToPtr` (`addressToPtr_ptrToAddress_eq`).
- Proved MiniRust step correspondence for pointer-to-usize casts (`ptr_to_usize_cast_step_correspondence`).
- Proved determinism of pointer cast evaluation (`ptr_to_usize_cast_deterministic`).
- Proved MiniRust step correspondence for int-to-pointer casts (`int_to_ptr_cast_step_correspondence`).
- Proved full roundtrip correspondence (`ptr_usize_ptr_roundtrip_correspondence`).
- Verified with `anneal-lean-run --mode build --concurrency 1 -- lake build Anneal.Mir.Cast`: 56/56 jobs clean, 0 warnings, 0 sorries.
