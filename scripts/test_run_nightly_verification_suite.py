#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Unit tests for `scripts/run_nightly_verification_suite.py`."""

from __future__ import annotations

import contextlib
import fcntl
import importlib.machinery
import importlib.util
import io
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
import textwrap
import threading
import time
from typing import Any
import unittest
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parent))
import audit_mir_coverage_matrix as mir_audit  # noqa: E402
import run_nightly_verification_suite as suite  # noqa: E402


REPO_ROOT = Path(__file__).resolve().parent.parent
UNTESTED_VARIANT_TEST = "tests/mir/MirUntestedVariantCorrespondenceTests.lean"
# Workspace-library imports of `MirUntestedVariantCorrespondenceTests.lean` (its header is
# `import Trusted`, `Anneal.MirFuelFree`, the two `Correspondence.V2026_06_01` layers,
# `MiniRustSpec.Correspondence.Translate` and `Lean.Elab.Command`).
UNTESTED_VARIANT_TEST_WORKSPACE_IMPORTS = (
    "Trusted",
    "Anneal.MirFuelFree",
    "Correspondence.V2026_06_01.L3_PlacesAndBasicMem",
    "Correspondence.V2026_06_01.L5_ControlAndCalls",
    "MiniRustSpec.Correspondence.Translate",
)

# The dual-authority correspondence modules `MIR_AST_CATEGORIES` cites for the 14 variants
# promoted to `proved_corresponding`, the cross-root kernel bridges closing the `Bundle`
# modules over `LM`, and concrete kernel-checked theorem / variant evidence in each file.
MIR_DUAL_AUTHORITY_MODULES: dict[str, tuple[str, ...]] = {
    "UnwindSetDiscrAndFnPtr": (
        "minirust/lean/MiniRustSpec/UnwindSetDiscrAndFnPtrMR.lean",
        "lean-miri/lean/LeanMiriSpec/UnwindSetDiscrAndFnPtrLM.lean",
    ),
    "DropBinderAndSubtype": (
        "minirust/lean/MiniRustSpec/DropBinderAndSubtypeMR.lean",
        "lean-miri/lean/LeanMiriSpec/DropBinderAndSubtypeLM.lean",
        "theory/Anneal/Mir/DropBinderAndSubtypeBundle.lean",
    ),
    "NullaryAndPtrCoercion": (
        "minirust/lean/MiniRustSpec/NullaryAndPtrCoercionMR.lean",
        "lean-miri/lean/LeanMiriSpec/NullaryAndPtrCoercionLM.lean",
        "theory/Anneal/Mir/NullaryAndPtrCoercionBundle.lean",
    ),
}
MIR_BUNDLE_KERNEL_BRIDGES: dict[str, str] = {
    "DropBinderAndSubtype": "tests/mir/DropBinderAndSubtypeCorrTests.lean",
    "NullaryAndPtrCoercion": "tests/mir/NullaryAndPtrCoercionCorrTests.lean",
}
# Each promoted variant maps to `{rel_path: (theorems_or_bundle_variant_names, ...)}`.
# For `MR`/`LM` files, every entry must be an actual `theorem`/`lemma` declaration in
# comment-stripped Lean code; for `Bundle` files, the first entry is the variant
# constructor listed in `allEp2Variants`/`allNpVariants` and the rest are theorems.
MIR_PROMOTED_VARIANT_THEOREMS: dict[str, dict[str, tuple[str, ...]]] = {
    "StatementKind.coverage": {
        "minirust/lean/MiniRustSpec/UnwindSetDiscrAndFnPtrMR.lean": (
            "coverage_stuttering_step",
            "c4_coverage_stuttering_three_way_witness",
        ),
        "lean-miri/lean/LeanMiriSpec/UnwindSetDiscrAndFnPtrLM.lean": (
            "step_coverage_simulation",
            "w_c4_coverage_multiStep",
        ),
        "minirust/lean/MiniRustSpec/DropBinderAndSubtypeMR.lean": (
            "v1_coverage_universal_sim",
            "v1_coverage_positive_and_ub_witness",
        ),
        "lean-miri/lean/LeanMiriSpec/DropBinderAndSubtypeLM.lean": (
            "lm_v1_v2_overlay_universal_sim",
            "lm_v1_v2_coverage_and_dropHint_witness",
        ),
        "theory/Anneal/Mir/DropBinderAndSubtypeBundle.lean": (
            ".coverage",
            "allEp2Variants_complete",
            "mrVariantSide_check",
            "variant_bundle_claims_with",
        ),
    },
    "StatementKind.backwardIncompatibleDropHint": {
        "minirust/lean/MiniRustSpec/UnwindSetDiscrAndFnPtrMR.lean": (
            "backwardIncompatibleDropHint_stuttering_step",
            "c5_backwardIncompatibleDropHint_dead_place_no_ub_witness",
        ),
        "lean-miri/lean/LeanMiriSpec/UnwindSetDiscrAndFnPtrLM.lean": (
            "step_backwardIncompatibleDropHint_simulation",
            "w_c5_dropHint_dead_uninit_dangling_vs_placeMention_ub",
        ),
        "minirust/lean/MiniRustSpec/DropBinderAndSubtypeMR.lean": (
            "v2_dropHint_universal_sim",
            "v2_dropHint_positive_and_ub_witness",
        ),
        "lean-miri/lean/LeanMiriSpec/DropBinderAndSubtypeLM.lean": (
            "lm_v1_v2_overlay_universal_sim",
            "lm_v1_v2_coverage_and_dropHint_witness",
        ),
        "theory/Anneal/Mir/DropBinderAndSubtypeBundle.lean": (
            ".backwardIncompatibleDropHint",
            "allEp2Variants_complete",
            "mrVariantSide_check",
            "variant_bundle_claims_with",
        ),
    },
    "TerminatorKind.drop": {
        "minirust/lean/MiniRustSpec/DropBinderAndSubtypeMR.lean": (
            "v3_drop_whole_coupled_lockstep_and_wfLive",
            "v3_drop_comprehensive_witness",
        ),
        "lean-miri/lean/LeanMiriSpec/DropBinderAndSubtypeLM.lean": (
            "lm_v3_drop_dead_ub_overlay_universal",
            "lm_v3_drop_comprehensive_witness",
        ),
        "theory/Anneal/Mir/DropBinderAndSubtypeBundle.lean": (
            ".dropTerminator",
            "allEp2Variants_complete",
            "mrVariantSide_check",
            "variant_bundle_claims_with",
        ),
    },
    "TerminatorKind.unwindResume": {
        "minirust/lean/MiniRustSpec/UnwindSetDiscrAndFnPtrMR.lean": (
            "unwindResume_continue_chain_coupled_steps_and_wfLive",
            "c2_unwindResume_all_five_regimes_witness",
        ),
        "lean-miri/lean/LeanMiriSpec/UnwindSetDiscrAndFnPtrLM.lean": (
            "step_unwindResume_cleanup_and_unreachable_simulation",
            "w_c2_c3_unwind_all_regimes_and_terminate",
        ),
    },
    "TerminatorKind.unwindTerminate": {
        "minirust/lean/MiniRustSpec/UnwindSetDiscrAndFnPtrMR.lean": (
            "unwindTerminate_lockstep_abort_mach_and_tb",
            "c3_unwindTerminate_three_way_witness",
        ),
        "lean-miri/lean/LeanMiriSpec/UnwindSetDiscrAndFnPtrLM.lean": (
            "step_unwindTerminate_directUnwind_abort_simulation",
            "w_c2_c3_unwind_all_regimes_and_terminate",
        ),
    },
    "ProjectionElem.unwrapUnsafeBinder": {
        "minirust/lean/MiniRustSpec/UnwindSetDiscrAndFnPtrMR.lean": (
            "unwrapUnsafeBinder_assign_coupled_lockstep_and_wfLive",
            "c9_unwrapUnsafeBinder_three_way_len_and_ub_witness",
        ),
        "lean-miri/lean/LeanMiriSpec/UnwindSetDiscrAndFnPtrLM.lean": (
            "step_unwrapUnsafeBinder_copy_simulation",
            "step_unwrapUnsafeBinder_write_simulation",
        ),
        "minirust/lean/MiniRustSpec/NullaryAndPtrCoercionMR.lean": (
            "np_v4_unwrapUnsafeBinder_three_way_witness",
            "npMrObserve_unwrap_mode_sensitivity",
        ),
        "lean-miri/lean/LeanMiriSpec/NullaryAndPtrCoercionLM.lean": (
            "lm_np_v4_unwrapUnsafeBinder_witness",
            "npLmObserve_v4_unwrapUnsafeBinder_table",
        ),
        "theory/Anneal/Mir/NullaryAndPtrCoercionBundle.lean": (
            ".unwrapUnsafeBinder",
            "allNpVariants_complete",
            "mrVariantSide_check",
            "ep2_nullary_ptrcoercion_fnptr_unwrap_capstone",
        ),
    },
    "Rvalue.nullaryOp": {
        "minirust/lean/MiniRustSpec/NullaryAndPtrCoercionMR.lean": (
            "np_v1_nullaryOp_coupled_step_sim_all_four",
            "np_v1_nullaryOp_three_way_witness",
        ),
        "lean-miri/lean/LeanMiriSpec/NullaryAndPtrCoercionLM.lean": (
            "lm_np_v1_nullaryOp_boundary_and_lowered_witness",
            "npLmObserve_v1_nullaryOp_table",
        ),
        "theory/Anneal/Mir/NullaryAndPtrCoercionBundle.lean": (
            ".nullaryOp",
            "allNpVariants_complete",
            "mrVariantSide_check",
            "ep2_nullary_ptrcoercion_fnptr_unwrap_capstone",
        ),
    },
    "Rvalue.shallowInitBox": {
        "minirust/lean/MiniRustSpec/DropBinderAndSubtypeMR.lean": (
            "v4_shallowInitBox_universal_sim",
            "v4_shallowInitBox_comprehensive_witness",
        ),
        "lean-miri/lean/LeanMiriSpec/DropBinderAndSubtypeLM.lean": (
            "trusted_shallowInitBox_eq_transmute_on_rawPtr",
            "lm_v4_shallowInitBox_boundary_and_lowered_witness",
        ),
        "theory/Anneal/Mir/DropBinderAndSubtypeBundle.lean": (
            ".shallowInitBox",
            "allEp2Variants_complete",
            "mrVariantSide_check",
            "variant_bundle_claims_with",
        ),
    },
    "Rvalue.wrapUnsafeBinder": {
        "minirust/lean/MiniRustSpec/DropBinderAndSubtypeMR.lean": (
            "v5_wrapUnsafeBinder_universal_sim",
            "v5_wrapUnsafeBinder_comprehensive_witness",
        ),
        "lean-miri/lean/LeanMiriSpec/DropBinderAndSubtypeLM.lean": (
            "lm_v5_wrapUnsafeBinder_evalRvalue_universal",
            "lm_v5_wrapUnsafeBinder_comprehensive_witness",
        ),
        "theory/Anneal/Mir/DropBinderAndSubtypeBundle.lean": (
            ".wrapUnsafeBinder",
            "allEp2Variants_complete",
            "mrVariantSide_check",
            "variant_bundle_claims_with",
        ),
    },
    "CastKind.pointerCoercion": {
        "minirust/lean/MiniRustSpec/UnwindSetDiscrAndFnPtrMR.lean": (
            "reify_and_closure_fnPointer_lockstep_M",
            "unsafeFnPointer_ground_truth_and_divergences",
        ),
        "lean-miri/lean/LeanMiriSpec/UnwindSetDiscrAndFnPtrLM.lean": (
            "step_cast_closureFnPointer_simulation",
            "step_cast_mutToConstPointer_thin_simulation",
        ),
        "minirust/lean/MiniRustSpec/NullaryAndPtrCoercionMR.lean": (
            "np_v2_pointerCoercion_dispatch",
            "np_v2_pointerCoercion_three_way_witness",
        ),
        "lean-miri/lean/LeanMiriSpec/NullaryAndPtrCoercionLM.lean": (
            "lm_np_v2_pointerCoercion_six_subkinds_witness",
            "npLmObserve_v2_pointerCoercion_table",
        ),
        "theory/Anneal/Mir/NullaryAndPtrCoercionBundle.lean": (
            ".pointerCoercion",
            "allNpVariants_complete",
            "mrVariantSide_check",
            "ep2_nullary_ptrcoercion_fnptr_unwrap_capstone",
        ),
    },
    "CastKind.subtype": {
        "minirust/lean/MiniRustSpec/UnwindSetDiscrAndFnPtrMR.lean": (
            "subtype_thinPtr_and_u32_coupled_lockstep",
            "c7_subtype_positive_and_invalid_ub_three_way_witness",
        ),
        "lean-miri/lean/LeanMiriSpec/UnwindSetDiscrAndFnPtrLM.lean": (
            "step_cast_subtype_scalar_and_ub_simulation",
            "w_c7_subtype_scalars_ptrs_newtype_and_ub",
        ),
        "minirust/lean/MiniRustSpec/DropBinderAndSubtypeMR.lean": (
            "v6_subtype_eq_transmute_and_sim",
            "v5_v6_binder_and_subtype_coupled_valRel_sim",
        ),
        "lean-miri/lean/LeanMiriSpec/DropBinderAndSubtypeLM.lean": (
            "miri_cast_subtype_eq_transmute",
            "lm_v6_castSubtype_comprehensive_witness",
        ),
        "theory/Anneal/Mir/DropBinderAndSubtypeBundle.lean": (
            ".castSubtype",
            "allEp2Variants_complete",
            "mrVariantSide_check",
            "variant_bundle_claims_with",
        ),
    },
    "CastKind.fnPtrToPtr": {
        "minirust/lean/MiniRustSpec/UnwindSetDiscrAndFnPtrMR.lean": (
            "fnPtrToPtr_lockstep_mach_and_tb",
            "c6_fnPtrToPtr_three_way_and_ub_witness",
        ),
        "lean-miri/lean/LeanMiriSpec/UnwindSetDiscrAndFnPtrLM.lean": (
            "step_cast_fnPtrToPtr_simulation",
            "w_c6_fnPtrToPtr_roundtrip_ub_and_divergence",
        ),
        "minirust/lean/MiniRustSpec/NullaryAndPtrCoercionMR.lean": (
            "np_v3_evalRvalue_fnPtrToPtr_eq",
            "np_v3_fnPtrToPtr_three_way_witness",
        ),
        "lean-miri/lean/LeanMiriSpec/NullaryAndPtrCoercionLM.lean": (
            "lm_np_v3_fnPtrToPtr_ub_and_divergence_witness",
            "npLmObserve_v3_fnPtrToPtr_table",
        ),
        "theory/Anneal/Mir/NullaryAndPtrCoercionBundle.lean": (
            ".fnPtrToPtr",
            "allNpVariants_complete",
            "mrVariantSide_check",
            "ep2_nullary_ptrcoercion_fnptr_unwrap_capstone",
        ),
    },
    "AggregateKind.rawPtr": {
        "minirust/lean/MiniRustSpec/DropBinderAndSubtypeMR.lean": (
            "v7_aggregateRawPtr_universal_sim",
            "v7_aggregateRawPtr_comprehensive_witness",
        ),
        "lean-miri/lean/LeanMiriSpec/DropBinderAndSubtypeLM.lean": (
            "lm_v7_writeAggregate_rawPtr_universal",
            "lm_v7_aggregateRawPtr_comprehensive_witness",
        ),
        "theory/Anneal/Mir/DropBinderAndSubtypeBundle.lean": (
            ".aggregateRawPtr",
            "allEp2Variants_complete",
            "mrVariantSide_check",
            "variant_bundle_claims_with",
        ),
    },
    "AggregateKind.closure": {
        "minirust/lean/MiniRustSpec/UnwindSetDiscrAndFnPtrMR.lean": (
            "closure_assign_coupled_lockstep_and_wfLive",
            "c10_closure_zst_capture_and_ub_three_way_witness",
        ),
        "lean-miri/lean/LeanMiriSpec/UnwindSetDiscrAndFnPtrLM.lean": (
            "step_aggregate_closure_zst_simulation",
            "step_aggregate_closure_twoCapture_simulation",
        ),
        "minirust/lean/MiniRustSpec/DropBinderAndSubtypeMR.lean": (
            "v8_closure_universal_sim",
            "v8_closure_coupled_valRel_sim",
        ),
        "lean-miri/lean/LeanMiriSpec/DropBinderAndSubtypeLM.lean": (
            "lm_v8_closure_overlay_universal",
            "lm_v8_aggregateClosure_comprehensive_witness",
        ),
        "theory/Anneal/Mir/DropBinderAndSubtypeBundle.lean": (
            ".aggregateClosure",
            "allEp2Variants_complete",
            "mrVariantSide_check",
            "variant_bundle_claims_with",
        ),
    },
}
MIR_PROMOTED_VARIANT_EVIDENCE: dict[str, tuple[str, ...]] = {
    "StatementKind.coverage": ("UnwindSetDiscrAndFnPtr", "DropBinderAndSubtype"),
    "StatementKind.backwardIncompatibleDropHint": ("UnwindSetDiscrAndFnPtr", "DropBinderAndSubtype"),
    "TerminatorKind.drop": ("DropBinderAndSubtype",),
    "TerminatorKind.unwindResume": ("UnwindSetDiscrAndFnPtr",),
    "TerminatorKind.unwindTerminate": ("UnwindSetDiscrAndFnPtr",),
    "ProjectionElem.unwrapUnsafeBinder": ("UnwindSetDiscrAndFnPtr", "NullaryAndPtrCoercion"),
    "Rvalue.nullaryOp": ("NullaryAndPtrCoercion",),
    "Rvalue.shallowInitBox": ("DropBinderAndSubtype",),
    "Rvalue.wrapUnsafeBinder": ("DropBinderAndSubtype",),
    "CastKind.pointerCoercion": ("UnwindSetDiscrAndFnPtr", "NullaryAndPtrCoercion"),
    "CastKind.subtype": ("UnwindSetDiscrAndFnPtr", "DropBinderAndSubtype"),
    "CastKind.fnPtrToPtr": ("UnwindSetDiscrAndFnPtr", "NullaryAndPtrCoercion"),
    "AggregateKind.rawPtr": ("DropBinderAndSubtype",),
    "AggregateKind.closure": ("UnwindSetDiscrAndFnPtr", "DropBinderAndSubtype"),
}

# Pillar 3 divergences resolved by `*_simulation` theorems (statement-pinned in their
# authority audit module, or in `tests/mir/MirUntestedVariantCorrespondenceTests.lean` itself).
RESOLVED_DIVERGENCE_IDS = frozenset(
    {
        "DIV-MR-CALL-TARGET-LOCAL",
        "DIV-MR-CALLER-BORROW-ACROSS-SCALAR-CALL",
        "DIV-MR-TB-TWOPHASE-DIRECT-WRITE",
        "DIV-MR-TB-FNENTRY-LOCAL-DEALLOC",
        "DIV-MR-TB-UNSAFECELL-PROTECTED-IM",
        "DIV-LM-RAW-OVERWRITE-CHAR-COPY",
        "DIV-LM-D6-OFFSET-DISABLED-TAG",
        "DIV-LM-ENUM-SET-DISCR-UNINIT",
        # Episode 2: fixed by the frame-depth-aware tail-call teardown (`disableFrameBorrows`
        # before `enterTailCalleeFrame` in `evalTailCallTerminator`).
        "DIV-TR-TAILCALL-DANGLING-CALLER-LOCAL",
        # Episode 2: fixed by narrowing the inherited unwind action of a non-unwinding tail
        # callee (`narrowCallStackForTailCallee`, `Memory.rootUnwindCeiling`).
        "DIV-LM-TAILCALL-NOUNWIND-UNWIND",
        # Episode 2: fixed by dispatching below the leading cast chain
        # (`stripLeadingOpaqueCast`, `eraseLeadingOpaqueCastDecls`).
        "DIV-TR-OPAQUECAST-ROOT-DISPATCH",
        # Episode 2: fixed by relocating the root's caller-owned referents past a wider tail
        # callee (`relocateRootCallerReferents`).
        "DIV-TR-TAILCALL-ROOT-CALLER-REFERENT-SHADOW",
    }
)
# The Episode 2 divergences of `tests/mir/MirUntestedVariantCorrespondenceTests.lean` whose
# witnesses were flipped to `*_simulation` theorems by the tail-call / opaque-cast repairs.
EPISODE2_FLIPPED_DIVERGENCE_IDS = frozenset(
    {
        "DIV-LM-TAILCALL-NOUNWIND-UNWIND",
        "DIV-TR-OPAQUECAST-ROOT-DISPATCH",
        "DIV-TR-TAILCALL-ROOT-CALLER-REFERENT-SHADOW",
    }
)
# Divergences that are still live (open actionable Anneal bugs): none.
OPEN_DIVERGENCE_IDS: frozenset[str] = frozenset()
ACTIONABLE_DIVERGENCE_COUNT = len(RESOLVED_DIVERGENCE_IDS) + len(OPEN_DIVERGENCE_IDS)

# A meaningful, hole-free statement for synthetic resolution theorems and their statement
# pins: the flip-direction witness polarity guard rejects vacuous ones (`True`, `0 = 0`).
SYNTH_STMT = "annealOutcome fooProg = miriOutcome fooProg"
# A synthetic divergence witness statement (distinct from `SYNTH_STMT`).
SYNTH_DIVERGENCE_STMT = "annealOutcome fooProg ≠ miriOutcome fooProg"

# Synthetic Stage-B corpus separating Episode 1's lifted slice wide pointers from unlifted
# unsized DSTs (8 functions; statement counts in comments).
SLICE_VS_DST_CORPUS = """
pub fn slice_only(p: *mut u32, n: usize, k: usize) -> usize {
    let s = unsafe { core::slice::from_raw_parts(p, n) };
    let w = core::ptr::slice_from_raw_parts_mut(p, n);
    let (a, b) = unsafe { (*w).split_at_mut(k) };
    s.len() + a.len() + b.len()
}

pub fn pure_add(a: u32, b: u32) -> u32 {
    let c = a + b;
    c
}

pub fn unsized_body(x: &[u8]) -> usize {
    let n = x.len();
    let bytes = core::mem::size_of_val(x);
    n + bytes
}

pub fn qsized_generic<T: ?Sized>(_t: &T, p: *const u8, n: usize) -> usize {
    let w = core::ptr::slice_from_raw_parts(p, n);
    let m = n + 1;
    m
}

pub fn generic_from_raw_parts(p: *const u8, n: usize) -> usize {
    let m = n * 2;
    let w: *const [u8] = core::ptr::from_raw_parts(p, n);
    m
}

pub fn qsized_without_slice_op<T: ?Sized>(_t: &T) -> usize {
    let m = 3;
    m
}

pub struct W<T: ?Sized>(core::marker::PhantomData<T>);
impl<T: ?Sized> W<T> {
    pub fn impl_qsized(&self, p: *const u8, n: usize) -> usize {
        let w = core::ptr::slice_from_raw_parts(p, n);
        let m = n;
        m
    }
}

pub fn dyn_dispatch(x: &u32) -> u32 {
    let d: &dyn Fooable = x;
    let y = *x;
    y
}
"""


_FAKE_LEAN_RUN_HONEST_BANNER = "Thread Budget (-j) : 4 threads (LEAN_NUM_THREADS=1)"


def _fake_lean_run_source(
    *,
    log: Path | None = None,
    probe_text: str = _FAKE_LEAN_RUN_HONEST_BANNER,
    probe_rc: int = 0,
    probe_sleep: float = 0,
    exec_threads: str | None = None,
    exec_rc: int = 0,
    exec_stdout: str = "",
    exec_sleep: float = 0,
    in_scope_passthrough: bool = False,
) -> str:
    """Source of a fake `anneal-lean-run` for `_wrapper_honors_lean_num_threads` tests.

    `--probe` prints `probe_text` and exits `probe_rc`; otherwise it runs the command after
    `--` with `LEAN_NUM_THREADS` overwritten by `exec_threads` (kept when `None`), unless
    `exec_rc` is non-zero. With `in_scope_passthrough`, an `ANNEAL_LEAN_RUN_IN_SCOPE=1`
    environment gets an honest banner and an untouched exec. A `*_sleep` hangs that phase
    with a same-group grandchild holding `stdout` (pid in `sleeper.pid` next to the
    script). Each call appends its argv, key environment, and seeded slice unit to `log`.
    """
    return (
        f"#!{sys.executable}\n"
        "import json, os, subprocess, sys, time\n"
        "args = sys.argv[1:]\n"
        f"LOG = {os.fspath(log) if log is not None else None!r}\n"
        "KEYS = ('LEAN_NUM_THREADS', 'ANNEAL_LSP_NO_EVICT', 'ANNEAL_LEAN_RUN_IN_SCOPE', 'ANNEAL_LEAN_RUN_ACTIVE',\n"
        "        'ANNEAL_LEAN_RUN_LEAN_M_MB', 'ANNEAL_LEAN_RUN_SLOTS', 'ANNEAL_LEAN_RUN_MEM_MB',\n"
        "        'ANNEAL_WORKTREE_CONCURRENCY', 'ANNEAL_LEAN_MEMORY_MAX_MB', 'ANNEAL_LEAN_TIMEOUT_SEC',\n"
        "        'ANNEAL_OOM_OFFLOAD_CMD', 'XDG_CONFIG_HOME', 'XDG_RUNTIME_DIR', 'HOME')\n"
        "unit = os.path.join(os.environ.get('XDG_CONFIG_HOME', '/nonexistent'), 'systemd/user/anneal-workloads.slice')\n"
        "if LOG:\n"
        "    with open(LOG, 'a', encoding='utf-8') as fh:\n"
        "        fh.write(json.dumps({'argv0': sys.argv[0], 'args': args,\n"
        "                             'env': {k: os.environ.get(k) for k in KEYS},\n"
        "                             'slice': open(unit, encoding='utf-8').read() if os.path.isfile(unit) else None}) + '\\n')\n"
        "def hang(sec):\n"
        "    if sec:\n"
        "        p = subprocess.Popen([sys.executable, '-c', 'import time; time.sleep(%r)' % sec])\n"
        "        open(os.path.join(os.path.dirname(os.path.abspath(sys.argv[0])), 'sleeper.pid'), 'w').write(str(p.pid))\n"
        "        time.sleep(sec)\n"
        f"in_scope = {in_scope_passthrough!r} and os.environ.get('ANNEAL_LEAN_RUN_IN_SCOPE') == '1'\n"
        "if '--probe' in args:\n"
        f"    hang({probe_sleep!r})\n"
        f"    text = {_FAKE_LEAN_RUN_HONEST_BANNER!r} if in_scope else {probe_text!r}\n"
        "    if text:\n"
        "        print(text)\n"
        f"    sys.exit({probe_rc!r})\n"
        f"hang({exec_sleep!r})\n"
        f"if {exec_rc!r}:\n"
        f"    sys.exit({exec_rc!r})\n"
        "cmd = args[args.index('--') + 1:]\n"
        "env = dict(os.environ)\n"
        f"if not in_scope and {exec_threads!r} is not None:\n"
        f"    env['LEAN_NUM_THREADS'] = {exec_threads!r}\n"
        f"sys.stdout.write({exec_stdout!r})\n"
        "sys.stdout.flush()\n"
        "os.execvpe(cmd[0], cmd, env)\n"
    )


def _write_fake_lean_run(path: Path, **kwargs: Any) -> Path:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(_fake_lean_run_source(**kwargs), encoding="utf-8")
    path.chmod(0o755)
    return path


class NightlyVerificationSuiteTests(unittest.TestCase):
    # Operator knobs read from the ambient environment that change which wrapper the suite
    # resolves or how long it waits for it. The suite runs these tests as one of its own
    # steps (`scripts_python_unit_tests`), with whatever the operator exported for the run.
    _AMBIENT_SUITE_KNOBS = (
        "ANNEAL_LEAN_RUN",
        "ANNEAL_LEAN_TIMEOUT_SEC",
        "ANNEAL_LEAN_MEMORY_MAX_MB",
        "ANNEAL_LEAN_RUN_IN_SCOPE",
        "ANNEAL_LSP_NO_EVICT",
        "LEAN_NUM_THREADS",
    )

    def setUp(self) -> None:
        # Every test starts without those knobs, and whatever a test writes to `os.environ`
        # is rolled back when it ends.
        patcher = mock.patch.dict(os.environ)
        patcher.start()
        self.addCleanup(patcher.stop)
        for knob in self._AMBIENT_SUITE_KNOBS:
            os.environ.pop(knob, None)

    def test_stage_a_syntactic_completeness_on_repo(self) -> None:
        stage_a = suite.compute_stage_a_syntactic_completeness(REPO_ROOT)
        mir = stage_a["anneal_mir_ast"]
        # Exactly the `Trusted.Rustc.V2026_06_01.MirAst` constructors (checked against the Lean
        # inductives by `scripts/audit_mir_coverage_matrix.py`).
        self.assertEqual(mir["total_variants"], 94)
        self.assertEqual(mir["proved_corresponding"], 90)
        self.assertEqual(mir["supported_and_tested"], 1)
        self.assertEqual(mir["unsupported_fail_closed"], 3)
        self.assertEqual(mir["supported_untested"], 0)
        self.assertEqual(mir["untested_variants"], [])
        self.assertEqual(
            mir["total_variants"],
            mir["proved_corresponding"]
            + mir["supported_and_tested"]
            + mir["supported_untested"]
            + mir["unsupported_fail_closed"],
        )
        statuses = {
            f"{entry['category']}.{name}": status
            for entry in suite.MIR_AST_CATEGORIES
            for name, status in entry["variants"]
        }
        self.assertEqual(statuses["StatementKind.constEvalCounter"], "proved_corresponding")
        self.assertEqual(statuses["TerminatorKind.tailCall"], "proved_corresponding")
        # Explicit phase boundary (rejected after borrowck by rustc and Miri).
        self.assertEqual(statuses["ProjectionElem.opaqueCast"], "supported_and_tested")
        self.assertGreaterEqual(mir["stage1_lowered_lintrinsic_op_variants"], 30)

        mr = stage_a["minirust_authority"]
        self.assertEqual(mr["spec_files"], 27)
        self.assertEqual(mr["shallow_types_translated"], 100)
        self.assertEqual(mr["interp_anchored_items"], 115)
        self.assertGreater(mr["audited_declarations"], 500)
        # `interp_anchored_items` counts the well-formed `tokenSha256` pins of
        # `MiniRustSpec/Anchors.lean`. Recount them independently of the suite: a malformed
        # hash would drop out of its count silently, and an item pinned twice would inflate
        # it without anchoring anything new, so neither may hide behind the pinned total.
        anchors_text = (REPO_ROOT / "minirust/lean/MiniRustSpec/Anchors.lean").read_text(
            encoding="utf-8"
        )
        anchors = re.findall(
            r'file\s*:=\s*"([^"]+)"[^{}]*?name\s*:=\s*"([^"]+)"\s*,\s*line\s*:=\s*(\d+)\s*,'
            r'\s*tokenSha256\s*:=\s*"([^"]*)"',
            anchors_text,
        )
        self.assertEqual(len(anchors), mr["interp_anchored_items"])
        self.assertEqual(len(re.findall(r"tokenSha256\s*:=", anchors_text)), len(anchors))
        self.assertEqual(len({anchor[:3] for anchor in anchors}), len(anchors))
        for file, name, line, token_sha256 in anchors:
            self.assertRegex(token_sha256, r"\A[0-9a-f]{64}\Z", f"{file}:{line} {name}")
        # The derived share is computed from the same two totals.
        self.assertLessEqual(mr["interp_anchored_items"], mr["spec_items_total"])
        self.assertEqual(
            mr["interp_anchored_pct_of_items"],
            round(100.0 * mr["interp_anchored_items"] / mr["spec_items_total"], 2),
        )
        self.assertLessEqual(mr["shallow_types_translated"], mr["shallow_types_candidates"])

        lm = stage_a["lean_miri_authority"]
        self.assertEqual(lm["vendored_miri_files"], 608)
        self.assertIn("LM-1.1", lm["milestones_merged"])
        self.assertIn("LM-3.3", lm["milestones_merged"])
        self.assertGreater(lm["audited_declarations"], 500)

    def test_mir_ast_categories_reconciled_to_90_of_94_proved_corresponding(self) -> None:
        statuses: dict[str, str] = {}
        for entry in suite.MIR_AST_CATEGORIES:
            for name, status in entry["variants"]:
                key = f"{entry['category']}.{name}"
                self.assertNotIn(key, statuses, "variant listed twice")
                statuses[key] = status
        self.assertEqual(len(statuses), 94)

        def with_status(status: str) -> list[str]:
            return [key for key, value in statuses.items() if value == status]

        self.assertEqual(len(with_status("proved_corresponding")), 90)
        self.assertEqual(with_status("supported_and_tested"), ["ProjectionElem.opaqueCast"])
        self.assertEqual(with_status("supported_untested"), [])
        self.assertEqual(
            with_status("unsupported_fail_closed"),
            ["TerminatorKind.inlineAsm", "Rvalue.threadLocalRef", "AggregateKind.coroutine"],
        )
        self.assertEqual(
            set(statuses.values()), {"proved_corresponding", "supported_and_tested", "unsupported_fail_closed"}
        )

        # The 14 variants promoted from `supported_and_tested` / `unsupported_fail_closed`.
        self.assertEqual(len(MIR_PROMOTED_VARIANT_EVIDENCE), 14)
        self.assertEqual(set(MIR_PROMOTED_VARIANT_THEOREMS), set(MIR_PROMOTED_VARIANT_EVIDENCE))
        for key in MIR_PROMOTED_VARIANT_EVIDENCE:
            self.assertEqual(statuses[key], "proved_corresponding", key)
        # Each cited module (and each cross-root kernel bridge closing a `Bundle` over `LM`)
        # exists in this tree, lexes cleanly, contains no `sorry` / `admit` / `native_decide` /
        # `axiom` declaration outside Lean comments and string literals, and declares concrete
        # correspondence theorems in that stripped code.
        proof_code: dict[str, str] = {}
        axiom_decl_re = re.compile(
            r"(?:^|\n)\s*(?:(?:private|protected|local|scoped|noncomputable|unsafe)\s+)*axiom\b"
        )
        all_checked_files = [
            *(rel for rels in MIR_DUAL_AUTHORITY_MODULES.values() for rel in rels),
            *MIR_BUNDLE_KERNEL_BRIDGES.values(),
        ]
        for family, rels in MIR_DUAL_AUTHORITY_MODULES.items():
            self.assertGreaterEqual(len(rels), 2, family)
            self.assertTrue(any(rel.endswith("MR.lean") for rel in rels), family)
            self.assertTrue(any(rel.endswith("LM.lean") for rel in rels), family)

        def check_clean_lean_code(rel: str) -> str:
            path = REPO_ROOT / rel
            self.assertTrue(path.is_file(), rel)
            code, lex_errors = mir_audit.strip_lean_source(path.read_text(encoding="utf-8"), keep_strings=False)
            self.assertEqual(lex_errors, [], f"{rel}: {lex_errors}")
            for banned in ("sorry", "admit", "native_decide"):
                self.assertIsNone(re.search(rf"\b{banned}\b", code), f"{rel}: {banned}")
            self.assertIsNone(axiom_decl_re.search(code), f"{rel}: axiom")
            return code

        for rel in all_checked_files:
            proof_code[rel] = check_clean_lean_code(rel)
        for key, families in MIR_PROMOTED_VARIANT_EVIDENCE.items():
            self.assertTrue(families, key)
            expected_files = {rel for family in families for rel in MIR_DUAL_AUTHORITY_MODULES[family]}
            by_file = MIR_PROMOTED_VARIANT_THEOREMS[key]
            self.assertEqual(set(by_file), expected_files, key)
            for rel, symbols in by_file.items():
                self.assertTrue(symbols, (key, rel))
                code = proof_code[rel]
                for sym in symbols:
                    if sym.startswith("."):
                        self.assertRegex(
                            code,
                            rf"{re.escape(sym)}\b",
                            f"{rel} missing bundle variant {sym} for {key}",
                        )
                    else:
                        self.assertRegex(
                            code,
                            rf"(?m)^(?:private\s+|protected\s+)?(?:theorem|lemma)\s+{re.escape(sym)}\b",
                            f"{rel} missing theorem {sym} for {key}",
                        )
        # Cross-root kernel bridge files declare concrete closing theorems.
        for rel, bridge_theorems in (
            (
                MIR_BUNDLE_KERNEL_BRIDGES["DropBinderAndSubtype"],
                ("ep2_all_8_variants_flip_verdict", "ep2_drop_mode_sensitivity_root"),
            ),
            (
                MIR_BUNDLE_KERNEL_BRIDGES["NullaryAndPtrCoercion"],
                (
                    "np_all_4_variants_flip_verdict",
                    "ep2_nullary_ptrcoercion_fnptr_unwrap_root_capstone",
                ),
            ),
        ):
            code = proof_code[rel]
            for sym in bridge_theorems:
                self.assertRegex(
                    code,
                    rf"(?m)^(?:private\s+|protected\s+)?(?:theorem|lemma)\s+{re.escape(sym)}\b",
                    f"{rel} missing bridge theorem {sym}",
                )
        # Float-cast correspondence modules cited in `MIR_AST_CATEGORIES` exist, pass hygiene,
        # and carry their fail-closed MiniRust boundary and direct Miri step-simulation theorems.
        float_umbrella = check_clean_lean_code("lean-miri/lean/LeanMiriSpec/FloatCastLM.lean")
        # The umbrella must *import* the direct-step submodule on its own line: a bare mention
        # in code, or a longer module name sharing the prefix, does not re-export its theorems.
        self.assertRegex(
            float_umbrella,
            r"(?m)^(?:public[ \t]+)?import[ \t]+LeanMiriSpec\.FloatCastLM\.RealStepDirect[ \t]*$",
        )
        for rel, required_theorems in (
            (
                "minirust/lean/MiniRustSpec/FloatCastMR.lean",
                ("fc_intTypeOf_float", "fc_translateTy_float"),
            ),
            (
                "lean-miri/lean/LeanMiriSpec/FloatCastLM/RealStepDirect.lean",
                ("step_cast_float_copy_simulation_mode", "step_cast_float_move_simulation_mode"),
            ),
            (
                "lean-miri/lean/LeanMiriSpec/WitFloatCastLM.lean",
                ("wfcW5_promoted_raw_pipeline_end_to_end", "wfcW5_indirect_float_pipeline_end_to_end"),
            ),
        ):
            code = check_clean_lean_code(rel)
            for sym in required_theorems:
                self.assertRegex(
                    code,
                    rf"(?m)^(?:private\s+|protected\s+)?(?:theorem|lemma)\s+{re.escape(sym)}\b",
                    f"{rel} missing float-cast theorem {sym}",
                )

        # The census and the Markdown-facing lists are derived from the same table.
        mir = suite.compute_stage_a_syntactic_completeness(REPO_ROOT)["anneal_mir_ast"]
        self.assertEqual(
            (
                mir["total_variants"],
                mir["proved_corresponding"],
                mir["supported_and_tested"],
                mir["supported_untested"],
                mir["unsupported_fail_closed"],
            ),
            (94, 90, 1, 0, 3),
        )
        self.assertEqual(mir["proved_corresponding_pct"], 95.74)
        self.assertEqual(mir["supported_total"], 91)
        self.assertEqual(mir["supported_pct"], 96.81)
        self.assertEqual(mir["untested_variants"], [])
        self.assertEqual(
            mir["unsupported_variants"],
            ["TerminatorKind.inlineAsm", "Rvalue.threadLocalRef", "AggregateKind.coroutine"],
        )
        by_category = {
            cat: (c["proved_corresponding"], c["supported_and_tested"], c["unsupported_fail_closed"], c["total"])
            for cat, c in mir["by_category"].items()
        }
        self.assertEqual(
            by_category,
            {
                "StatementKind": (12, 0, 0, 12),
                "NonDivergingIntrinsic": (2, 0, 0, 2),
                "TerminatorKind": (10, 0, 1, 11),
                "ProjectionElem": (7, 1, 0, 8),
                "Rvalue": (14, 0, 1, 15),
                "BinOp": (26, 0, 0, 26),
                "UnOp": (3, 0, 0, 3),
                "CastKind": (11, 0, 0, 11),
                "AggregateKind": (5, 0, 1, 6),
            },
        )

    def test_stage_b_blended_completeness_and_marginal_unlock_math(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            tmp_dir = Path(tmp)
            sample_rs = tmp_dir / "sample.rs"
            sample_rs.write_text(
                """
                pub fn pure_add(a: u32, b: u32) -> u32 {
                    let c = a.wrapping_add(b);
                    c
                }

                pub fn partially_blocked_float(x: u32) -> u32 {
                    let a = x + 1;
                    let b = a * 2;
                    let c = b - 1;
                    let _f: f64 = 1.0;
                    c
                }

                pub fn multi_blocked(x: u32) -> u32 {
                    let _f: f32 = 0.0;
                    unsafe { core::arch::asm!("nop") };
                    x
                }
                """,
                encoding="utf-8",
            )
            res = suite.analyze_corpus_completeness("synthetic", [sample_rs], alpha=0.5)
            self.assertEqual(res["total_fns"], 3)
            lifter = res["layers"]["anneal_proof_lifters"]
            self.assertEqual(lifter["fully_verifiable_fns"], 1)
            self.assertEqual(lifter["partially_covered_fns"], 2)
            self.assertEqual(lifter["uncovered_fns"], 0)
            self.assertGreater(lifter["within_blocked_fns_stmt_coverage_pct"], 50.0)
            self.assertAlmostEqual(lifter["within_blocked_fns_cfg_prefix_pct"], 37.5)
            self.assertGreater(
                lifter["blended_completeness_score_pct"],
                lifter["fully_verifiable_stmt_pct"],
            )

            # `float_arith_or_cast` is the sole blocker on `partially_blocked_float` (1 fn),
            # whereas `inline_asm` only appears alongside `float_arith_or_cast` (0 sole-blocker fns).
            blockers = {b["construct"]: b for b in res["top_marginal_unlock_blockers"]}
            self.assertEqual(blockers["float_arith_or_cast"]["sole_blocker_fn_count"], 1)
            self.assertEqual(blockers["float_arith_or_cast"]["blocked_fn_count"], 2)
            self.assertEqual(blockers["inline_asm"]["sole_blocker_fn_count"], 0)
            self.assertEqual(blockers["inline_asm"]["blocked_fn_count"], 1)

    def test_stage_b_separates_lifted_slice_wide_ptrs_from_unsized_dsts(self) -> None:
        lifted = suite.LIFTED_SLICE_WIDE_PTR_BLOCKER
        unsized = suite.UNSIZED_DST_BLOCKER
        layers = {name: aff for name, _pat, aff in suite.RUST_CONSTRUCT_BLOCKERS}
        self.assertNotIn("wide_ptr_or_unsized_dst", layers)
        self.assertNotIn("anneal_proof_lifters", layers[lifted])
        self.assertEqual(layers[lifted], {"minirust_correspondence", "lean_miri_correspondence"})
        self.assertEqual(
            layers[unsized],
            {"anneal_proof_lifters", "minirust_correspondence", "lean_miri_correspondence"},
        )
        with tempfile.TemporaryDirectory() as tmp:
            sample_rs = Path(tmp) / "slice_vs_dst.rs"
            sample_rs.write_text(SLICE_VS_DST_CORPUS, encoding="utf-8")
            res = suite.analyze_corpus_completeness("slice_vs_dst", [sample_rs], alpha=0.5)
        self.assertEqual(res["total_fns"], 8)
        self.assertEqual(res["total_stmt_units"], 4 + 2 + 3 + 3 + 3 + 2 + 3 + 3)
        counts = {
            layer: (d["fully_verifiable_fns"], d["partially_covered_fns"], d["uncovered_fns"])
            for layer, d in res["layers"].items()
        }
        # Lifters: `slice_only` (raw slice construction + split_at_mut + len), `pure_add` and
        # `qsized_without_slice_op` (no slice exemption claimed, so body-only scanning as
        # before) verify; size_of_val, generic `ptr::from_raw_parts`, a lifted slice op inside a
        # `T: ?Sized` fn or `impl<T: ?Sized>`, and `dyn` are partial (entry statement blocked
        # for the signature-guarded two).
        self.assertEqual(counts["anneal_proof_lifters"], (3, 5, 0))
        # Raw slice construction still blocks both correspondence layers.
        self.assertEqual(counts["minirust_correspondence"], (2, 6, 0))
        self.assertEqual(counts["lean_miri_correspondence"], (2, 6, 0))
        self.assertEqual(counts["trusted_mir"], (7, 1, 0))
        lifters = res["layers"]["anneal_proof_lifters"]
        # Entry prefixes of the 5 blocked fns (3 stmts each): `unsized_body` 1,
        # `generic_from_raw_parts` 1, and 0 for the signature-guarded `qsized_generic` /
        # `impl_qsized` (blocked at entry) and `dyn_dispatch`.
        self.assertAlmostEqual(lifters["within_blocked_fns_cfg_prefix_pct"], round(100.0 * 2 / 15, 2))
        self.assertAlmostEqual(lifters["within_blocked_fns_stmt_coverage_pct"], round(100.0 * 10 / 15, 2))
        top = {b["construct"]: b for b in res["top_marginal_unlock_blockers"]}
        self.assertEqual(set(top), {unsized, "dyn_trait_dispatch"})
        self.assertNotIn(lifted, top)
        self.assertEqual(top[unsized]["blocked_fn_count"], 4)
        self.assertEqual(top[unsized]["sole_blocker_fn_count"], 4)
        self.assertEqual(top[unsized]["uncovered_stmt_count"], 4)
        self.assertEqual(top["dyn_trait_dispatch"]["sole_blocker_fn_count"], 1)
        self.assertEqual(res["top_marginal_unlock_blockers"][0]["construct"], unsized)

    def test_lifted_slice_and_unsized_dst_patterns_do_not_overlap(self) -> None:
        patterns = {name: pat for name, pat, _aff in suite.RUST_CONSTRUCT_BLOCKERS}
        lifted = patterns[suite.LIFTED_SLICE_WIDE_PTR_BLOCKER]
        unsized = patterns[suite.UNSIZED_DST_BLOCKER]
        lifted_only = (
            "let s = unsafe { core::slice::from_raw_parts(p, n) }",
            "slice::from_raw_parts_mut(p, n)",
            "ptr::slice_from_raw_parts(p, n)",
            "core::ptr::slice_from_raw_parts_mut(p, n)",
            "NonNull::slice_from_raw_parts(nn, n)",
        )
        unsized_only = (
            "fn f<T: ?Sized>(t: &T)",
            "T: ? Sized",
            "core::mem::size_of_val(x)",
            "mem::size_of_val_raw(p)",
            "align_of_val(x)",
            "core::mem::align_of_val_raw(p)",
            "Layout::for_value(x)",
            "Layout::for_value_raw(p)",
            "<T as Pointee>::Metadata",
            "DynMetadata<dyn Foo>",
            "Dst::PointerMetadata::from_elem_count(n)",
            "core::ptr::metadata(p)",
            "core::ptr::from_raw_parts(p, n)",
            "ptr::from_raw_parts_mut(p, n)",
            "NonNull::from_raw_parts(nn, n)",
            "<*const [u8]>::from_raw_parts(p, n)",
            "p.to_raw_parts()",
            "<*const [u8]>::to_raw_parts(p)",
        )
        neither = (
            "v.len()",
            "s.split_at_mut(2)",
            "let (a, b) = s.split_at(k)",
            "Vec::from_raw_parts(p, n, c)",
            "String::from_raw_parts(p, n, c)",
            "std::fs::metadata(path)",
            "myslice::from_raw_parts(p)",
            "from_raw_parts(p, n)",
            "x.as_ptr()",
            "fn g<T: Sized>(t: T)",
        )
        for text in lifted_only:
            self.assertRegex(text, lifted)
            self.assertNotRegex(text, unsized)
        for text in unsized_only:
            self.assertRegex(text, unsized)
            self.assertNotRegex(text, lifted)
        for text in neither:
            self.assertNotRegex(text, lifted)
            self.assertNotRegex(text, unsized)

    def test_rust_fn_units_carry_signature_and_enclosing_headers(self) -> None:
        units = suite._extract_rust_fn_units(SLICE_VS_DST_CORPUS)
        by_name = {name: (stmts, sig) for name, stmts, sig in units}
        self.assertEqual(
            [name for name, _s, _g in units],
            [
                "slice_only",
                "pure_add",
                "unsized_body",
                "qsized_generic",
                "generic_from_raw_parts",
                "qsized_without_slice_op",
                "impl_qsized",
                "dyn_dispatch",
            ],
        )
        self.assertIn("?Sized", by_name["qsized_generic"][1])
        self.assertIn("impl<T: ?Sized> W<T>", by_name["impl_qsized"][1])
        self.assertNotIn("?Sized", by_name["slice_only"][1])
        self.assertEqual(
            suite._extract_rust_functions(SLICE_VS_DST_CORPUS),
            [(name, stmts) for name, stmts, _sig in units],
        )
        commented = """
        /* Nested /* block comment with { and impl<T: ?Sized> W<T> { fn ghost() {} } */ end */
        pub fn real_fn(p: *const u8, n: usize) -> usize {
            let _url = "http://example.com // not a comment { size_of_val ?Sized";
            let s = unsafe { core::slice::from_raw_parts(p, n) };
            s.len()
        }
        """
        c_units = suite._extract_rust_fn_units(commented)
        self.assertEqual([u[0] for u in c_units], ["real_fn"])
        self.assertNotIn("?Sized", c_units[0][2])
        self.assertFalse(any("size_of_val" in stmt for stmt in c_units[0][1]))
        # A byte char literal `b'"'` (and `b'{'`) must not open a string literal or a block,
        # while lifetimes (`'a`) and identifiers ending in `b` stay untouched.
        byte_chars = """
        pub fn scan<'a>(s: &'a [u8], ab: u8) -> usize {
            let q = s.iter().filter(|&&c| c == b'"' || c == b'{' || c == ab).count();
            let n = unsafe { core::slice::from_raw_parts(s.as_ptr(), q) };
            n.len()
        }
        pub fn after<T: ?Sized>(t: &T) -> usize { core::mem::size_of_val(t) }
        """
        stripped = suite._strip_rust_comments_and_strings(byte_chars)
        self.assertIn("size_of_val", stripped)
        self.assertIn("&'a [u8]", stripped)
        b_units = suite._extract_rust_fn_units(byte_chars)
        self.assertEqual([u[0] for u in b_units], ["scan", "after"])
        self.assertTrue(any("size_of_val" in stmt for stmt in b_units[1][1]))
        self.assertIn("?Sized", b_units[1][2])
        # Array `[T; N]` return/where types must not be mistaken for `;`-terminated trait method
        # declarations, and raw C-string literals `cr#"..."#` must not open unbalanced strings.
        arr_and_cr = """
        pub fn ret_array<T: ?Sized>(_t: &T, p: *const u8, n: usize) -> [usize; 2] {
            let _cs = cr#"raw C string with " quote and size_of_val"#;
            let _w = core::ptr::slice_from_raw_parts(p, n);
            [n, 0]
        }
        pub fn after_arr(p: *const u8, n: usize) -> [u8; 4] {
            let _s = unsafe { core::slice::from_raw_parts(p, n) };
            [0; 4]
        }
        """
        a_units = suite._extract_rust_fn_units(arr_and_cr)
        self.assertEqual([u[0] for u in a_units], ["ret_array", "after_arr"])
        self.assertIn("?Sized", a_units[0][2])
        self.assertFalse(any("size_of_val" in stmt for stmt in a_units[0][1]))

    def test_correspondence_divergence_switch_to_pass_detection(self) -> None:
        divs = suite.discover_correspondence_divergences(REPO_ROOT)
        self.assertEqual(divs["actionable_anneal_bugs_count"], len(OPEN_DIVERGENCE_IDS))
        self.assertEqual(
            sorted((d["id"], d["status"]) for d in divs["actionable_anneal_bugs"]),
            sorted((div_id, "open") for div_id in OPEN_DIVERGENCE_IDS),
        )
        for d in divs["actionable_anneal_bugs"]:
            self.assertTrue(d["live_in_source"], d["id"])
            self.assertEqual(d["file"], suite.UNTESTED_VARIANT_TEST_FILE)
        self.assertEqual(len(divs["resolved_correspondence_divergences"]), len(RESOLVED_DIVERGENCE_IDS))
        resolved_ids = {d["id"] for d in divs["resolved_correspondence_divergences"]}
        self.assertEqual(resolved_ids, RESOLVED_DIVERGENCE_IDS)
        self.assertEqual(divs["known_miri_diff_manifest_bugs"], [])
        for d in divs["resolved_correspondence_divergences"]:
            self.assertEqual(d["status"], "resolved")
            self.assertFalse(d["live_in_source"])
            self.assertTrue(d["resolution_live_in_source"], d["id"])
            self.assertTrue(d["resolution_statement_pinned"], d["id"])

        actionable_items = [
            item
            for item in suite.TRACKED_CORRESPONDENCE_DIVERGENCES
            if item["category"] != "intentional_modeling_choice"
        ]
        self.assertEqual(len(actionable_items), ACTIONABLE_DIVERGENCE_COUNT)
        for item in actionable_items:
            self.assertTrue(item.get("resolution_symbol"), item["id"])
            self.assertTrue(item["resolution_symbol"].endswith("_simulation"), item["id"])
        n_actionable = len(actionable_items)

        def write_synthetic_checkout(
            root: Path,
            *,
            live_ids: set[str] = frozenset(),
            missing_ids: set[str] = frozenset(),
            unpinned_ids: set[str] = frozenset(),
        ) -> None:
            for item in actionable_items:
                # Statement pins live in the entry's pin module (its `resolution_pin_file`,
                # else its authority audit module), written even for `missing_ids`, whose
                # resolution theorem itself is absent.
                if item["id"] not in unpinned_ids:
                    audit = root / item.get(
                        "resolution_pin_file", suite.AUTHORITY_AUDIT_FILES[item["authority"]]
                    )
                    audit.parent.mkdir(parents=True, exist_ok=True)
                    with audit.open("a", encoding="utf-8") as fh:
                        fh.write(f"example : {SYNTH_STMT} :=\n  {item['resolution_symbol']}\n")
                if item["id"] in missing_ids:
                    continue
                path = root / item.get("resolution_file", item["file"])
                path.parent.mkdir(parents=True, exist_ok=True)
                with path.open("a", encoding="utf-8") as fh:
                    fh.write(f"theorem {item['resolution_symbol']} : {SYNTH_STMT} := rfl\n")
                    if item["id"] in live_ids:
                        fh.write(f"theorem {item['witness_symbol']} : {SYNTH_DIVERGENCE_STMT} := rfl\n")

        # Fail-closed statement-pin linkage: a resolution theorem whose statement is not
        # locked by a non-trivial typed audit `example : <Prop> := <theorem>` pin (e.g.
        # only listed, commented out, applied mid-term, untyped `let _ :=` / `example :=`,
        # vacuous `: True` / wildcard `: _`, field-projected `.1`, or decoy-qualified
        # `Scratch.<thm>`) stays actionable as `resolution_unpinned`.
        with tempfile.TemporaryDirectory() as tmp:
            tmp_root = Path(tmp)
            write_synthetic_checkout(tmp_root, unpinned_ids={"DIV-MR-CALL-TARGET-LOCAL"})
            mr_audit = tmp_root / suite.AUTHORITY_AUDIT_FILES["MiniRustSpec"]
            with mr_audit.open("a", encoding="utf-8") as fh:
                fh.write(
                    "#assert_standard_axioms\n  callerRefMutSilentWrongLocal_simulation\n"
                    f"-- example : {SYNTH_STMT} := callerRefMutSilentWrongLocal_simulation\n"
                    f"example : {SYNTH_STMT} := id callerRefMutSilentWrongLocal_simulation\n"
                    "let _ := @callerRefMutSilentWrongLocal_simulation\n"
                    "example := callerRefMutSilentWrongLocal_simulation\n"
                    "example : _ := callerRefMutSilentWrongLocal_simulation\n"
                    "example : True := callerRefMutSilentWrongLocal_simulation\n"
                    "example : (True) := callerRefMutSilentWrongLocal_simulation\n"
                    f"example : {SYNTH_STMT} := callerRefMutSilentWrongLocal_simulation.1\n"
                    f"example : {SYNTH_STMT} := Scratch.callerRefMutSilentWrongLocal_simulation\n"
                    f"unsafe example : {SYNTH_STMT} := callerRefMutSilentWrongLocal_simulation\n"
                    # Self-typed pins lock nothing: the type is computed from the RHS.
                    "example : type_of% callerRefMutSilentWrongLocal_simulation :=\n"
                    "  callerRefMutSilentWrongLocal_simulation\n"
                    "example : (by exact type_of% @callerRefMutSilentWrongLocal_simulation) :=\n"
                    "  callerRefMutSilentWrongLocal_simulation\n"
                    "example : _ ∧ _ := callerRefMutSilentWrongLocal_simulation\n"
                    "example : ?_ := callerRefMutSilentWrongLocal_simulation\n"
                    "example : ?m := callerRefMutSilentWrongLocal_simulation\n"
                    "example : ?m ∧ ?n := callerRefMutSilentWrongLocal_simulation\n"
                    f"example : id ({SYNTH_STMT}) ∧ callerRefMutSilentWrongLocal_simulation = "
                    "callerRefMutSilentWrongLocal_simulation :=\n"
                    "  callerRefMutSilentWrongLocal_simulation\n"
                )
            synth_divs = suite.discover_correspondence_divergences(tmp_root)
            self.assertEqual(
                [(d["id"], d["status"]) for d in synth_divs["actionable_anneal_bugs"]],
                [("DIV-MR-CALL-TARGET-LOCAL", "resolution_unpinned")],
            )
            self.assertEqual(len(synth_divs["resolved_correspondence_divergences"]), n_actionable - 1)
            with mr_audit.open("a", encoding="utf-8") as fh:
                fh.write(f"example : {SYNTH_STMT} :=\n  @callerRefMutSilentWrongLocal_simulation\n")
            synth_divs = suite.discover_correspondence_divergences(tmp_root)
            self.assertEqual(synth_divs["actionable_anneal_bugs_count"], 0)
            self.assertEqual(len(synth_divs["resolved_correspondence_divergences"]), n_actionable)

        # A `private` (or `unsafe` / `partial`) modifier on its own line(s) before the
        # resolution theorem still makes it module-private, so it must not count.
        with tempfile.TemporaryDirectory() as tmp:
            tmp_root = Path(tmp)
            write_synthetic_checkout(tmp_root, missing_ids={"DIV-LM-ENUM-SET-DISCR-UNINIT"})
            lm23 = tmp_root / "lean-miri/lean/LeanMiriSpec/Correspondence/SimLM2_3.lean"
            lm23.parent.mkdir(parents=True, exist_ok=True)
            lm23.write_text(
                "@[simp]\nprivate\n\ntheorem step_setDiscriminant_uninit_simulation : True := trivial\n",
                encoding="utf-8",
            )
            synth_divs = suite.discover_correspondence_divergences(tmp_root)
            self.assertEqual(
                [(d["id"], d["status"]) for d in synth_divs["actionable_anneal_bugs"]],
                [("DIV-LM-ENUM-SET-DISCR-UNINIT", "resolution_missing")],
            )

        # Regression check: reintroducing a live `*_divergence` witness symbol in a
        # synthetic checkout must immediately flip `actionable_anneal_bugs_count` back > 0.
        with tempfile.TemporaryDirectory() as tmp:
            tmp_root = Path(tmp)
            write_synthetic_checkout(tmp_root, live_ids={"DIV-LM-RAW-OVERWRITE-CHAR-COPY"})
            synth_divs = suite.discover_correspondence_divergences(tmp_root)
            self.assertEqual(synth_divs["actionable_anneal_bugs_count"], 1)
            self.assertEqual(
                [(d["id"], d["status"]) for d in synth_divs["actionable_anneal_bugs"]],
                [("DIV-LM-RAW-OVERWRITE-CHAR-COPY", "open")],
            )
            self.assertEqual(len(synth_divs["resolved_correspondence_divergences"]), n_actionable - 1)

        # Fail-closed check: a witness that vanished WITHOUT its positive replacement
        # theorem (bare rename / deletion) is not counted as resolved.
        with tempfile.TemporaryDirectory() as tmp:
            tmp_root = Path(tmp)
            write_synthetic_checkout(tmp_root, missing_ids={"DIV-LM-D6-OFFSET-DISABLED-TAG"})
            synth_divs = suite.discover_correspondence_divergences(tmp_root)
            self.assertEqual(synth_divs["actionable_anneal_bugs_count"], 1)
            self.assertEqual(
                [(d["id"], d["status"]) for d in synth_divs["actionable_anneal_bugs"]],
                [("DIV-LM-D6-OFFSET-DISABLED-TAG", "resolution_missing")],
            )
            self.assertEqual(len(synth_divs["resolved_correspondence_divergences"]), n_actionable - 1)

        # An empty checkout (all witness files missing) must not report any resolution.
        with tempfile.TemporaryDirectory() as tmp:
            synth_divs = suite.discover_correspondence_divergences(Path(tmp))
            self.assertEqual(synth_divs["actionable_anneal_bugs_count"], n_actionable)
            self.assertEqual(synth_divs["resolved_correspondence_divergences"], [])
            self.assertEqual(
                {d["status"] for d in synth_divs["actionable_anneal_bugs"]},
                {"resolution_missing"},
            )

        # Comment, nested block-comment, string-literal, and non-theorem (`def`) spoofing
        # must fail closed (`resolution_missing`), while `abbrev` witness aliases and
        # character literals (`'"'`) must be handled accurately.
        with tempfile.TemporaryDirectory() as tmp:
            tmp_root = Path(tmp)
            write_synthetic_checkout(
                tmp_root,
                missing_ids={"DIV-LM-D6-OFFSET-DISABLED-TAG", "DIV-LM-ENUM-SET-DISCR-UNINIT"},
            )
            d6_file = tmp_root / "lean-miri/lean/LeanMiriSpec/Correspondence/SimLM3_1.lean"
            with d6_file.open("a", encoding="utf-8") as fh:
                fh.write(
                    "-- theorem step_binOp_offset_disabled_simulation : True := trivial\n"
                    "/- outer /- theorem step_binOp_offset_disabled_simulation : True := trivial -/ -/\n"
                    'def docStr : String := "theorem step_binOp_offset_disabled_simulation"\n'
                    "def step_binOp_offset_disabled_simulation : Unit := ()\n"
                )
            lm23_file = tmp_root / "lean-miri/lean/LeanMiriSpec/Correspondence/SimLM2_3.lean"
            lm23_file.parent.mkdir(parents=True, exist_ok=True)
            lm23_file.write_text(
                "def quoteChar : Char := '\"'\n"
                "-- Replaces theorem step_setDiscriminant_uninit_divergence\n"
                f"@[simp] theorem step_setDiscriminant_uninit_simulation : {SYNTH_STMT} := rfl\n",
                encoding="utf-8",
            )
            synth_divs = suite.discover_correspondence_divergences(tmp_root)
            self.assertEqual(
                [(d["id"], d["status"]) for d in synth_divs["actionable_anneal_bugs"]],
                [("DIV-LM-D6-OFFSET-DISABLED-TAG", "resolution_missing")],
            )
            self.assertEqual(len(synth_divs["resolved_correspondence_divergences"]), n_actionable - 1)

            # Reintroducing a witness via `abbrev` must also be caught as `open`.
            with lm23_file.open("a", encoding="utf-8") as fh:
                fh.write("abbrev step_setDiscriminant_uninit_divergence := True\n")
            synth_divs2 = suite.discover_correspondence_divergences(tmp_root)
            self.assertEqual(
                sorted((d["id"], d["status"]) for d in synth_divs2["actionable_anneal_bugs"]),
                [
                    ("DIV-LM-D6-OFFSET-DISABLED-TAG", "resolution_missing"),
                    ("DIV-LM-ENUM-SET-DISCR-UNINIT", "open"),
                ],
            )
            state_dir = tmp_root / "state_render"
            _, _, md = suite.run_suite_and_generate_dashboard(
                repo_root=tmp_root, profile="census-only", state_dir=state_dir
            )
            self.assertIn(
                "**missing resolution** `step_binOp_offset_disabled_simulation`", md
            )

        # Scanner robustness: namespace-qualified, same-line `... in`-prefixed, and
        # `nonrec` / attributed witnesses are live (`open`), while a resolution that
        # only appears after `#exit` or only under a primed name does not count.
        with tempfile.TemporaryDirectory() as tmp:
            tmp_root = Path(tmp)
            write_synthetic_checkout(
                tmp_root,
                missing_ids={"DIV-LM-ENUM-SET-DISCR-UNINIT", "DIV-MR-TB-FNENTRY-LOCAL-DEALLOC"},
            )
            prov = tmp_root / "minirust/lean/MiniRustSpec/Correspondence/ProvenanceWitness.lean"
            with prov.open("a", encoding="utf-8") as fh:
                fh.write(
                    "theorem ProvenanceWitness.callerRefMutSilentWrongLocal_divergence : "
                    "True := trivial\n"
                    "set_option maxHeartbeats 400000 in theorem "
                    "callerBorrowAcrossScalarCall_divergence : True := trivial\n"
                )
            ref = tmp_root / "minirust/lean/MiniRustSpec/Correspondence/RefWitness.lean"
            with ref.open("a", encoding="utf-8") as fh:
                fh.write(
                    "open Foo in\n@[reducible] nonrec def twoPhaseDirectWriteTreeBorrowsGap : "
                    "Nat := 0\n"
                    "theorem retagFnEntryLocalDealloc_simulation' : True := trivial\n"
                )
            lm23 = tmp_root / "lean-miri/lean/LeanMiriSpec/Correspondence/SimLM2_3.lean"
            lm23.parent.mkdir(parents=True, exist_ok=True)
            lm23.write_text(
                "#exit\ntheorem step_setDiscriminant_uninit_simulation : True := trivial\n",
                encoding="utf-8",
            )
            synth_divs = suite.discover_correspondence_divergences(tmp_root)
            self.assertEqual(
                sorted((d["id"], d["status"]) for d in synth_divs["actionable_anneal_bugs"]),
                [
                    ("DIV-LM-ENUM-SET-DISCR-UNINIT", "resolution_missing"),
                    ("DIV-MR-CALL-TARGET-LOCAL", "open"),
                    ("DIV-MR-CALLER-BORROW-ACROSS-SCALAR-CALL", "open"),
                    ("DIV-MR-TB-FNENTRY-LOCAL-DEALLOC", "resolution_missing"),
                    ("DIV-MR-TB-TWOPHASE-DIRECT-WRITE", "open"),
                ],
            )
            self.assertEqual(len(synth_divs["resolved_correspondence_divergences"]), n_actionable - 5)

        # Asymmetric resolution vs. witness enforcement: `private`/`unsafe`/wrong-namespace
        # `resolution_symbol` declarations must be rejected (`resolution_missing`), whereas
        # `local attribute [...] in`, `axiom`/`opaque`, guillemet-quoted `«...»`, and
        # multi-line `private\ntheorem` witnesses must still be detected as `open`.
        with tempfile.TemporaryDirectory() as tmp:
            tmp_root = Path(tmp)
            write_synthetic_checkout(
                tmp_root,
                missing_ids={
                    "DIV-LM-ENUM-SET-DISCR-UNINIT",
                    "DIV-LM-D6-OFFSET-DISABLED-TAG",
                    "DIV-MR-TB-FNENTRY-LOCAL-DEALLOC",
                },
            )
            lm23 = tmp_root / "lean-miri/lean/LeanMiriSpec/Correspondence/SimLM2_3.lean"
            lm23.parent.mkdir(parents=True, exist_ok=True)
            lm23.write_text(
                "private theorem step_setDiscriminant_uninit_simulation : True := trivial\n"
                "unsafe theorem step_setDiscriminant_uninit_simulation : True := trivial\n",
                encoding="utf-8",
            )
            lm31 = tmp_root / "lean-miri/lean/LeanMiriSpec/Correspondence/SimLM3_1.lean"
            with lm31.open("a", encoding="utf-8") as fh:
                fh.write(
                    "theorem BogusNs.step_binOp_offset_disabled_simulation : True := trivial\n"
                    "private\ntheorem step_raw_overwritten_direct_copy_invalid_char_divergence : "
                    "True := trivial\n"
                )
            ref = tmp_root / "minirust/lean/MiniRustSpec/Correspondence/RefWitness.lean"
            with ref.open("a", encoding="utf-8") as fh:
                fh.write(
                    "namespace Scratch\n"
                    "theorem retagFnEntryLocalDealloc_simulation : True := trivial\n"
                    "end Scratch\n"
                    "axiom «twoPhaseDirectWriteTreeBorrowsGap» : True\n"
                )
            prov = tmp_root / "minirust/lean/MiniRustSpec/Correspondence/ProvenanceWitness.lean"
            with prov.open("a", encoding="utf-8") as fh:
                fh.write(
                    "local attribute [simp] id in theorem "
                    "callerBorrowAcrossScalarCall_divergence : True := trivial\n"
                )
            synth_divs = suite.discover_correspondence_divergences(tmp_root)
            self.assertEqual(
                sorted((d["id"], d["status"]) for d in synth_divs["actionable_anneal_bugs"]),
                [
                    ("DIV-LM-D6-OFFSET-DISABLED-TAG", "resolution_missing"),
                    ("DIV-LM-ENUM-SET-DISCR-UNINIT", "resolution_missing"),
                    ("DIV-LM-RAW-OVERWRITE-CHAR-COPY", "open"),
                    ("DIV-MR-CALLER-BORROW-ACROSS-SCALAR-CALL", "open"),
                    ("DIV-MR-TB-FNENTRY-LOCAL-DEALLOC", "resolution_missing"),
                    ("DIV-MR-TB-TWOPHASE-DIRECT-WRITE", "open"),
                ],
            )
            self.assertEqual(len(synth_divs["resolved_correspondence_divergences"]), n_actionable - 6)

        # Token-level Lean 4 grammar edge cases: `open Foo in private\ntheorem`,
        # `private @[simp,\n  reducible]\ntheorem`, `section private theorem ... end`,
        # and `section #exit\ntheorem` must NOT satisfy `resolution_symbol`, whereas
        # same-line `namespace Foo theorem <witness> ... end Foo`, `mutual def <witness> ... end`,
        # `#exit'` non-truncation, and `r#"\"#` raw strings must still detect witnesses as `open`.
        with tempfile.TemporaryDirectory() as tmp:
            tmp_root = Path(tmp)
            write_synthetic_checkout(
                tmp_root,
                missing_ids={
                    "DIV-LM-ENUM-SET-DISCR-UNINIT",
                    "DIV-LM-D6-OFFSET-DISABLED-TAG",
                    "DIV-MR-TB-FNENTRY-LOCAL-DEALLOC",
                    "DIV-MR-TB-UNSAFECELL-PROTECTED-IM",
                },
            )
            lm23 = tmp_root / "lean-miri/lean/LeanMiriSpec/Correspondence/SimLM2_3.lean"
            lm23.parent.mkdir(parents=True, exist_ok=True)
            lm23.write_text(
                "open Foo in private\n"
                "theorem step_setDiscriminant_uninit_simulation : 0 = 0 := rfl\n"
                "private @[simp,\n  reducible]\n"
                "theorem step_setDiscriminant_uninit_simulation : 0 = 0 := rfl\n",
                encoding="utf-8",
            )
            lm31 = tmp_root / "lean-miri/lean/LeanMiriSpec/Correspondence/SimLM3_1.lean"
            with lm31.open("a", encoding="utf-8") as fh:
                fh.write(
                    "section private theorem step_binOp_offset_disabled_simulation : "
                    "0 = 0 := rfl end\n"
                    "#exit'\n"
                    "theorem step_raw_overwritten_direct_copy_invalid_char_divergence : "
                    "0 = 0 := rfl\n"
                )
            ref = tmp_root / "minirust/lean/MiniRustSpec/Correspondence/RefWitness.lean"
            with ref.open("a", encoding="utf-8") as fh:
                fh.write(
                    "section #exit\n"
                    "theorem retagFnEntryLocalDealloc_simulation : 0 = 0 := rfl\n"
                )
            tb = tmp_root / "minirust/lean/MiniRustSpec/Correspondence/TbWitness.lean"
            tb.parent.mkdir(parents=True, exist_ok=True)
            tb.write_text(
                "mutual def unsafeCellProtectedInteriorMut : Nat := 0 end\n",
                encoding="utf-8",
            )
            prov = tmp_root / "minirust/lean/MiniRustSpec/Correspondence/ProvenanceWitness.lean"
            with prov.open("a", encoding="utf-8") as fh:
                fh.write(
                    'def rawBackslash := r#"\\"#\n'
                    "namespace Foo theorem callerRefMutSilentWrongLocal_divergence : "
                    "0 = 0 := rfl end Foo\n"
                )
            synth_divs = suite.discover_correspondence_divergences(tmp_root)
            self.assertEqual(
                sorted((d["id"], d["status"]) for d in synth_divs["actionable_anneal_bugs"]),
                [
                    ("DIV-LM-D6-OFFSET-DISABLED-TAG", "resolution_missing"),
                    ("DIV-LM-ENUM-SET-DISCR-UNINIT", "resolution_missing"),
                    ("DIV-LM-RAW-OVERWRITE-CHAR-COPY", "open"),
                    ("DIV-MR-CALL-TARGET-LOCAL", "open"),
                    ("DIV-MR-TB-FNENTRY-LOCAL-DEALLOC", "resolution_missing"),
                    ("DIV-MR-TB-UNSAFECELL-PROTECTED-IM", "open"),
                ],
            )
            self.assertEqual(len(synth_divs["resolved_correspondence_divergences"]), n_actionable - 6)

    def test_episode2_divergences_tracked_with_live_witnesses(self) -> None:
        divs = suite.discover_correspondence_divergences(REPO_ROOT, include_statements=True)
        actionable = {d["id"]: d for d in divs["actionable_anneal_bugs"]}
        resolved = {d["id"]: d for d in divs["resolved_correspondence_divergences"]}
        modeling = {d["id"]: d for d in divs["intentional_modeling_choices"]}
        episode2 = {
            item["id"]: item
            for item in suite.TRACKED_CORRESPONDENCE_DIVERGENCES
            if item["file"] == suite.UNTESTED_VARIANT_TEST_FILE
        }
        episode2_actionable = {
            i: item for i, item in episode2.items() if item["category"] == "actionable_anneal_bug"
        }
        self.assertEqual(
            set(episode2_actionable),
            EPISODE2_FLIPPED_DIVERGENCE_IDS | {"DIV-TR-TAILCALL-DANGLING-CALLER-LOCAL"},
        )
        # Every Episode 2 actionable divergence is resolved in the live tree: its witness is
        # gone, and its `*_simulation` theorem is declared once in the file's namespace, is
        # non-vacuous and hole-free, and is statement-pinned there. No open divergence is left.
        self.assertEqual(OPEN_DIVERGENCE_IDS, frozenset())
        self.assertEqual(divs["actionable_anneal_bugs_count"], 0)
        self.assertEqual(actionable, {})
        text = (REPO_ROOT / suite.UNTESTED_VARIANT_TEST_FILE).read_text(encoding="utf-8")
        ns_end = f"end {suite.UNTESTED_VARIANT_NAMESPACE}"
        self.assertEqual(text.count(ns_end), 1)
        for div_id, item in episode2_actionable.items():
            with self.subTest(divergence=div_id):
                self.assertEqual(item["resolution_namespace"], suite.UNTESTED_VARIANT_NAMESPACE)
                self.assertEqual(item["resolution_pin_file"], suite.UNTESTED_VARIANT_TEST_FILE)
                self.assertIn(div_id, RESOLVED_DIVERGENCE_IDS)
                record = resolved[div_id]
                self.assertEqual(record["status"], "resolved")
                self.assertFalse(record["live_in_source"])
                self.assertTrue(record["resolution_live_in_source"])
                self.assertTrue(record["resolution_valid"])
                self.assertEqual(record["resolution_problems"], [])
                self.assertTrue(record["resolution_statement_pinned"])
                self.assertEqual(record["resolution_pin_problems"], [])
                self.assertEqual(record["witness_statements"], [])
                self.assertEqual(len(record["resolution_statements"]), 1)
                resolution, witness = item["resolution_symbol"], item["witness_symbol"]
                self.assertTrue(resolution.endswith("_simulation"))
                self.assertEqual(
                    len(re.findall(rf"(?m)^theorem {re.escape(resolution)}(?![\w'!?])", text)), 1
                )
                self.assertIsNone(
                    re.search(
                        rf"(?m)^\s*(?:private\s+)?(?:theorem|lemma|def|abbrev)\s+"
                        rf"{re.escape(witness)}(?![\w'!?])",
                        text,
                    )
                )
        for div_id in ("MODEL-LM-TAILCALL-MODULAR-ROOT", "MODEL-LM-TAILCALL-DIRECT-ARITY-STEP"):
            self.assertIn(div_id, modeling)
            self.assertTrue(modeling[div_id]["live_in_source"])

        # Switch-to-pass is fail-closed, checked on a synthetic copy of the file in which
        # `DIV-TR-OPAQUECAST-ROOT-DISPATCH` is still open (a live witness with a divergence
        # statement) next to the other resolved Episode 2 entries: the witness theorem must
        # be replaced by the registered `resolution_symbol`, declared in the file's namespace
        # and statement-pinned there; a bare rename, a decoy namespace, or a missing pin does
        # not resolve the entry.
        opaque_id = "DIV-TR-OPAQUECAST-ROOT-DISPATCH"
        witness = episode2[opaque_id]["witness_symbol"]
        resolution = episode2[opaque_id]["resolution_symbol"]
        self.assertEqual(
            (witness, resolution),
            (
                "opaqueCast_trusted_root_dispatch_divergence",
                "opaqueCast_trusted_root_dispatch_simulation",
            ),
        )
        other_lines: list[str] = []
        for div_id, item in episode2.items():
            if div_id == opaque_id:
                continue
            if item["category"] == "actionable_anneal_bug":
                other_lines.append(f"theorem {item['resolution_symbol']} : {SYNTH_STMT} := rfl")
                other_lines.append(f"example : {SYNTH_STMT} := {item['resolution_symbol']}")
            else:
                other_lines.append(
                    f"theorem {item['witness_symbol']} : {SYNTH_DIVERGENCE_STMT} := rfl"
                )
        witness_decl = f"theorem {witness} : {SYNTH_DIVERGENCE_STMT} := rfl"
        ns_end_line = f"{ns_end}\n"

        def synth_text(opaque_block: str) -> str:
            return "\n".join(
                [f"namespace {suite.UNTESTED_VARIANT_NAMESPACE}", *other_lines, opaque_block]
            ) + f"\n{ns_end_line}"

        open_text = synth_text(witness_decl)
        self.assertEqual(open_text.count(witness_decl), 1)

        def write_tree(root: Path, body: str) -> None:
            target = root / suite.UNTESTED_VARIANT_TEST_FILE
            target.parent.mkdir(parents=True)
            target.write_text(body, encoding="utf-8")

        def status_after(new_text: str) -> str:
            with tempfile.TemporaryDirectory() as tmp:
                root = Path(tmp)
                write_tree(root, new_text)
                fixed = suite.discover_correspondence_divergences(root)
                by_id = {
                    d["id"]: d
                    for d in fixed["actionable_anneal_bugs"] + fixed["resolved_correspondence_divergences"]
                }
                for div_id in set(episode2_actionable) - {opaque_id}:
                    self.assertEqual(by_id[div_id]["status"], "resolved")
                for div_id in set(episode2) - set(episode2_actionable):
                    self.assertNotIn(div_id, by_id)
                return by_id[opaque_id]["status"]

        self.assertEqual(status_after(open_text), "open")
        renamed = open_text.replace(f"theorem {witness}", f"theorem {resolution}")
        pin = f"example : {SYNTH_DIVERGENCE_STMT} := {resolution}\n"
        self.assertEqual(
            status_after(
                open_text.replace(
                    f"theorem {witness}", "theorem opaqueCast_trusted_root_dispatch_erasure_commutes"
                )
            ),
            "resolution_missing",
        )
        self.assertEqual(status_after(renamed), "resolution_unpinned")
        self.assertEqual(
            status_after(
                renamed.replace(ns_end_line, f"namespace Scratch\n{pin}end Scratch\n{ns_end_line}")
            ),
            "resolution_unpinned",
        )
        renamed_pinned = renamed.replace(ns_end_line, f"{pin}{ns_end_line}")
        self.assertEqual(status_after(renamed_pinned), "resolved")
        flipped_pinned = synth_text(
            f"theorem {resolution} : {SYNTH_STMT} := rfl\nexample : {SYNTH_STMT} := {resolution}"
        )
        self.assertEqual(status_after(flipped_pinned), "resolved")
        # The single-tree scan cannot tell the bare rename from a fix, but the flip-direction
        # audit against the open baseline can: the renamed "simulation" theorem restates the
        # divergence witness (`polarity_not_flipped`), whereas a theorem with a flipped
        # statement passes.
        for current_text, expected_violations in (
            (renamed_pinned, [(opaque_id, "polarity_not_flipped")]),
            (flipped_pinned, []),
        ):
            with tempfile.TemporaryDirectory() as base_tmp, tempfile.TemporaryDirectory() as cur_tmp:
                base_root, cur_root = Path(base_tmp), Path(cur_tmp)
                write_tree(base_root, open_text)
                write_tree(cur_root, current_text)
                audit = suite.audit_flip_direction_transitions(base_root, cur_root)
                self.assertEqual(
                    audit["transitions"], [{"id": opaque_id, "from": "open", "to": "resolved"}]
                )
                self.assertEqual(
                    [(v["id"], v["reason"]) for v in audit["violations"]], expected_violations
                )
                self.assertEqual(audit["passed"], not expected_violations)
        decoy = (
            "namespace Scratch\n"
            f"theorem {resolution} : 0 = 0 := rfl\n"
            "end Scratch\n"
            "theorem opaqueCast_trusted_root_dispatch_erasure_commutes"
        )
        self.assertEqual(
            status_after(
                open_text.replace(f"theorem {witness}", decoy).replace(
                    ns_end_line, f"{pin}{ns_end_line}"
                )
            ),
            "resolution_missing",
        )

    def test_episode2_flips_pass_the_flip_direction_audit_on_the_live_tree(self) -> None:
        """The three Episode 2 flips of the live tree, audited against baselines derived
        from it: a baseline in which each witness is still open with a divergence statement
        (the flips pass), and baselines in which a live `*_simulation` theorem is merely its
        old witness under a new name (each is rejected as `polarity_not_flipped`)."""
        items = {
            item["id"]: item
            for item in suite.TRACKED_CORRESPONDENCE_DIVERGENCES
            if item["id"] in EPISODE2_FLIPPED_DIVERGENCE_IDS
        }
        self.assertEqual(set(items), EPISODE2_FLIPPED_DIVERGENCE_IDS)
        rel = suite.UNTESTED_VARIANT_TEST_FILE
        live_text = (REPO_ROOT / rel).read_text(encoding="utf-8")
        ns_end = f"end {suite.UNTESTED_VARIANT_NAMESPACE}"
        self.assertEqual(live_text.count(ns_end), 1)

        def copy_tracked_tree(dest: Path, untested_variant_text: str) -> None:
            for tracked in suite.flip_direction_tracked_files():
                src = REPO_ROOT / tracked
                if src.is_file():
                    dst = dest / tracked
                    dst.parent.mkdir(parents=True, exist_ok=True)
                    shutil.copyfile(src, dst)
            (dest / rel).write_text(untested_variant_text, encoding="utf-8")

        def rename_theorem(body: str, old: str, new: str) -> str:
            renamed, count = re.subn(
                rf"(?m)^theorem {re.escape(old)}(?![\w'!?])", f"theorem {new}", body
            )
            self.assertEqual(count, 1, old)
            return renamed

        # 1. Every witness open in the baseline, with a divergence statement that the live
        #    resolution theorem does not restate: three clean `open -> resolved` flips.
        open_baseline = live_text
        for item in items.values():
            open_baseline = rename_theorem(
                open_baseline, item["resolution_symbol"], f"{item['resolution_symbol']}_pre_flip"
            )
        open_baseline = open_baseline.replace(
            ns_end,
            "".join(
                f"theorem {item['witness_symbol']} : {SYNTH_DIVERGENCE_STMT} := rfl\n"
                for item in items.values()
            )
            + ns_end,
        )
        with tempfile.TemporaryDirectory() as tmp:
            base = Path(tmp)
            copy_tracked_tree(base, open_baseline)
            base_divs = suite.discover_correspondence_divergences(base)
            self.assertEqual(
                sorted((d["id"], d["status"]) for d in base_divs["actionable_anneal_bugs"]),
                sorted((div_id, "open") for div_id in EPISODE2_FLIPPED_DIVERGENCE_IDS),
            )
            audit = suite.audit_flip_direction_transitions(base, REPO_ROOT)
        self.assertTrue(audit["passed"], audit["violations"])
        self.assertEqual(audit["violations"], [])
        self.assertEqual(
            sorted((t["id"], t["from"], t["to"]) for t in audit["transitions"]),
            sorted((div_id, "open", "resolved") for div_id in EPISODE2_FLIPPED_DIVERGENCE_IDS),
        )
        self.assertEqual(
            (audit["baseline_actionable_count"], audit["current_actionable_count"]), (3, 0)
        )

        # 2. A baseline in which one live `*_simulation` theorem carried its witness's name
        #    (same statement): that flip is a rename, not a polarity flip.
        for div_id, item in sorted(items.items()):
            with self.subTest(renamed=div_id), tempfile.TemporaryDirectory() as tmp:
                base = Path(tmp)
                copy_tracked_tree(
                    base,
                    rename_theorem(live_text, item["resolution_symbol"], item["witness_symbol"]),
                )
                audit = suite.audit_flip_direction_transitions(base, REPO_ROOT)
                self.assertFalse(audit["passed"])
                self.assertEqual(
                    audit["transitions"], [{"id": div_id, "from": "open", "to": "resolved"}]
                )
                self.assertEqual(
                    [(v["id"], v["reason"]) for v in audit["violations"]],
                    [(div_id, "polarity_not_flipped")],
                )

    def _actionable_items(self) -> list[dict[str, str]]:
        return [
            item
            for item in suite.TRACKED_CORRESPONDENCE_DIVERGENCES
            if item["category"] != "intentional_modeling_choice"
        ]

    def _write_flip_tree(
        self,
        root: Path,
        overrides: dict[str, tuple[str | None, str | None, str | None]] | None = None,
    ) -> None:
        """Write a synthetic checkout in which every actionable divergence is resolved
        (`theorem <resolution> : SYNTH_STMT := rfl` plus a `SYNTH_STMT` statement pin),
        except for each `overrides[id] = (witness_decl_tail, resolution_decl_tail,
        pin_type)`, whose non-`None` parts are written instead (`<symbol> <tail>`)."""
        for item in self._actionable_items():
            witness, resolution, pin = (overrides or {}).get(
                item["id"], (None, f": {SYNTH_STMT} := rfl", SYNTH_STMT)
            )
            src = root / item["file"]
            res = root / item.get("resolution_file", item["file"])
            audit = root / item.get(
                "resolution_pin_file", suite.AUTHORITY_AUDIT_FILES[item["authority"]]
            )
            for path, text in (
                (src, witness and f"theorem {item['witness_symbol']} {witness}\n"),
                (res, resolution and f"theorem {item['resolution_symbol']} {resolution}\n"),
                (audit, pin and f"example : {pin} :=\n  {item['resolution_symbol']}\n"),
            ):
                if text:
                    path.parent.mkdir(parents=True, exist_ok=True)
                    with path.open("a", encoding="utf-8") as fh:
                        fh.write(text)

    def _flip_status(self, root: Path, div_id: str) -> dict[str, object]:
        divs = suite.discover_correspondence_divergences(root)
        by_id = {
            d["id"]: d
            for d in divs["actionable_anneal_bugs"] + divs["resolved_correspondence_divergences"]
        }
        return by_id[div_id]

    def test_flip_direction_guard_rejects_vacuous_and_hole_riddled_resolution_theorems(self) -> None:
        div_id = "DIV-LM-ENUM-SET-DISCR-UNINIT"
        sym = "step_setDiscriminant_uninit_simulation"
        stmt = SYNTH_STMT
        # A resolution theorem that states or proves nothing is `resolution_invalid`
        # (fail closed), even with a meaningful statement pin.
        invalid_cases: list[tuple[str, set[str]]] = [
            (": True := trivial", {"vacuous_statement", "closed_trivial_statement"}),
            (": (True) := trivial", {"vacuous_statement", "closed_trivial_statement"}),
            (": ¬False := id", {"vacuous_statement", "closed_trivial_statement"}),
            (": True ∧ ¬False := ⟨trivial, id⟩", {"vacuous_statement", "closed_trivial_statement"}),
            (": 0 = 0 := rfl", {"vacuous_statement", "closed_trivial_statement"}),
            (": annealOutcome fooProg = annealOutcome fooProg := rfl", {"vacuous_statement"}),
            (": annealOutcome fooProg ↔ annealOutcome fooProg := Iff.rfl", {"vacuous_statement"}),
            (f": True ∨ {stmt} := Or.inl trivial", {"vacuous_statement"}),
            (": _ := foo", {"wildcard_statement"}),
            (": ?m := foo", {"metavariable_hole", "closed_trivial_statement"}),
            (f": {stmt} ∧ ?_ := foo", {"metavariable_hole"}),
            (f"(h : ?m) : {stmt} := foo", {"metavariable_hole"}),
            (f"{{x : ?t}} : {stmt} := foo", {"metavariable_hole"}),
            # Vacuous antecedents, also nested under binders and in Pi binders.
            (f": False → {stmt} := fun h => h.elim", {"vacuous_statement"}),
            (f": False -> {stmt} := fun h => h.elim", {"vacuous_statement"}),
            (f": (False) → {stmt} := fun h => h.elim", {"vacuous_statement"}),
            (f": ¬True → {stmt} := fun h => absurd trivial h", {"vacuous_statement"}),
            (f": (h : False) → {stmt} := fun h => h.elim", {"vacuous_statement"}),
            (f": ∀ x : Nat, False → {stmt} := fun _ h => h.elim", {"vacuous_statement"}),
            (f": ∀ (x : Nat) (h : False), {stmt} := nofun", {"vacuous_statement"}),
            (f": ∀ x, ∀ h : False, {stmt} := nofun", {"vacuous_statement"}),
            (f": (∀ x, annealOutcome x = 1 → False → {stmt}) := nofun", {"vacuous_statement"}),
            (f": annealOutcome fooProg = 1 → ∀ y, False → {stmt} := nofun", {"vacuous_statement"}),
            (f"(h : False) : {stmt} := h.elim", {"vacuous_statement"}),
            (f"⦃h : False⦄ : {stmt} := h.elim", {"vacuous_statement"}),
            (f"[inst : False] : {stmt} := inst.elim", {"vacuous_statement"}),
            (
                f"\n    {{body : CapturedMir}}\n    (hstate : stateRel body)\n    (hfalse : False) :\n"
                f"    {stmt} := by\n  exact hfalse.elim\n",
                {"vacuous_statement"},
            ),
            # Self-typed statements.
            (": type_of% fooLemma := fooLemma", {"self_typed_statement"}),
            (f": (by exact {stmt}) := rfl", {"self_typed_statement"}),
            # `sorry` / `admit` anywhere in the signature or the proof.
            (f": {stmt} := sorry", {"sorry_or_admit"}),
            (f": {stmt} := by sorry", {"sorry_or_admit"}),
            (f": {stmt} := by admit", {"sorry_or_admit"}),
            (f": {stmt} := sorryAx _ false", {"sorry_or_admit"}),
            (f": {stmt} := by\n  simp only [annealOutcome]\n  sorry\n", {"sorry_or_admit"}),
            (
                f": {stmt} := by\n  set_option maxHeartbeats 400000 in\n  sorry\n",
                {"sorry_or_admit"},
            ),
            (f": {stmt} := aux\nwhere\n  aux : {stmt} := sorry\n", {"sorry_or_admit"}),
            (
                ": ∀ n : Nat, annealOutcome n = miriOutcome n\n  | 0 => rfl\n  | _ + 1 => sorry\n",
                {"sorry_or_admit"},
            ),
            (": annealOutcome sorry = miriOutcome fooProg := rfl", {"sorry_or_admit"}),
            (f": {stmt} := by\n  decreasing_by admit\n", {"sorry_or_admit"}),
        ]
        for tail, expected in invalid_cases:
            with self.subTest(tail=tail), tempfile.TemporaryDirectory() as tmp:
                root = Path(tmp)
                self._write_flip_tree(root, {div_id: (None, tail, stmt)})
                rec = self._flip_status(root, div_id)
                self.assertEqual(rec["status"], "resolution_invalid")
                self.assertTrue(rec["resolution_live_in_source"])
                self.assertFalse(rec["resolution_valid"])
                self.assertEqual(set(rec["resolution_problems"]), expected)
        # Meaningful, hole-free resolution theorems (multi-line headers, binders,
        # `let`, equation compilers, `where` helpers, `match` / `set_option ... in` in
        # tactic proofs, and a vacuous conjunct beside a meaningful one) resolve.
        valid_cases = [
            f": {stmt} := rfl",
            "(h : annealOutcome fooProg = 3) : miriOutcome fooProg = 3 := by simp [h]",
            (
                f"\n    {{body : CapturedMir}} {{s : MachineState}}\n    (hstate : stateRel body s) :\n"
                f"    stepMirFn body s = .step s ∧\n      {stmt} := by\n  constructor <;> simp [hstate]\n"
            ),
            ": let s := annealOutcome fooProg; s = miriOutcome fooProg := rfl",
            ": ∀ n : Nat, annealOutcome n = miriOutcome n\n  | 0 => rfl\n  | _ + 1 => rfl\n",
            f": {stmt} := aux\nwhere\n  aux : {stmt} := rfl\n",
            f": {stmt} := by\n  match fooProg with\n  | _ => rfl\n",
            f": {stmt} := by\n  set_option maxHeartbeats 400000 in\n  simp\n",
            f": {stmt} ∧ (False → annealOutcome barProg = 0) := ⟨rfl, nofun⟩",
            f": ∀ x, annealOutcome x = miriOutcome x <| fooProg := fun _ => rfl",
        ]
        for tail in valid_cases:
            with self.subTest(tail=tail), tempfile.TemporaryDirectory() as tmp:
                root = Path(tmp)
                self._write_flip_tree(root, {div_id: (None, tail, stmt)})
                rec = self._flip_status(root, div_id)
                self.assertEqual((rec["status"], rec["resolution_problems"]), ("resolved", []))
                self.assertTrue(rec["resolution_valid"])
        lm23 = "lean-miri/lean/LeanMiriSpec/Correspondence/SimLM2_3.lean"
        # Fail closed across namespaces: a vacuous candidate in the expected namespace
        # invalidates a meaningful one (a decoy namespace's vacuous theorem does not).
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            self._write_flip_tree(root, {div_id: (None, None, stmt)})
            target = root / lm23
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_text(
                f"theorem {sym} : {stmt} := rfl\n"
                f"namespace LeanMiriSpec\ntheorem {sym} : True := trivial\nend LeanMiriSpec\n",
                encoding="utf-8",
            )
            rec = self._flip_status(root, div_id)
            self.assertEqual(rec["status"], "resolution_invalid")
            target.write_text(
                f"theorem {sym} : {stmt} := rfl\n"
                f"namespace Scratch\ntheorem {sym} : True := trivial\nend Scratch\n",
                encoding="utf-8",
            )
            self.assertEqual(self._flip_status(root, div_id)["status"], "resolved")
            # A `sorry` in an unrelated later declaration does not leak into the
            # resolution theorem, while a `sorry` before the next declaration does.
            target.write_text(
                f"theorem {sym} : {stmt} := rfl\n\ntheorem unrelated : {stmt} := sorry\n",
                encoding="utf-8",
            )
            self.assertEqual(self._flip_status(root, div_id)["status"], "resolved")
            target.write_text(
                f"theorem {sym} : {stmt} := by\n  first\n  | rfl\n  | sorry\n\n#print axioms {sym}\n",
                encoding="utf-8",
            )
            self.assertEqual(self._flip_status(root, div_id)["status"], "resolution_invalid")
            # The dashboard reports the invalid resolution with its reasons.
            _, _, md = suite.run_suite_and_generate_dashboard(
                repo_root=root, profile="census-only", state_dir=root / "state_render"
            )
            self.assertIn(f"**invalid resolution** `{sym}` (`{lm23}`: sorry_or_admit)", md)

    def test_flip_direction_guard_rejects_vacuous_self_typed_and_hole_statement_pins(self) -> None:
        div_id = "DIV-MR-CALL-TARGET-LOCAL"
        sym = "callerRefMutSilentWrongLocal_simulation"
        stmt = SYNTH_STMT
        rejected_pins: list[tuple[str, list[str]]] = [
            # Filtered by the declaration scanner itself (no candidate pin remains).
            ("example : True := {sym}", []),
            ("example : _ := {sym}", []),
            ("example : ?m := {sym}", []),
            # Self-typed, tactic-synthesized, wildcard, or metavariable types.
            ("example : type_of% {sym} := {sym}", ["self_typed_or_hole_pin"]),
            (f"example : (by exact {stmt}) := {{sym}}", ["self_typed_or_hole_pin"]),
            (f"example : {stmt} ∧ _ := {{sym}}", ["self_typed_or_hole_pin"]),
            (f"example : {stmt} ∧ ?m := {{sym}}", ["self_typed_or_hole_pin"]),
            (f"example : {stmt} ∧ ?_ := {{sym}}", ["self_typed_or_hole_pin"]),
            # Vacuous statements and antecedents, also under binders.
            ("example : True ∧ True := {sym}", ["pin_closed_trivial_statement", "pin_vacuous_statement"]),
            ("example : 0 = 0 := {sym}", ["pin_closed_trivial_statement", "pin_vacuous_statement"]),
            (
                "example : annealOutcome fooProg = annealOutcome fooProg := {sym}",
                ["pin_vacuous_statement"],
            ),
            (f"example : False → {stmt} := {{sym}}", ["pin_vacuous_statement"]),
            (f"example : ¬True -> {stmt} := {{sym}}", ["pin_vacuous_statement"]),
            (f"example : (h : False) → {stmt} := {{sym}}", ["pin_vacuous_statement"]),
            (f"example : ∀ x : Nat, False → {stmt} := {{sym}}", ["pin_vacuous_statement"]),
            (f"example : ∀ {{x : Nat}} (h : False), {stmt} := {{sym}}", ["pin_vacuous_statement"]),
            (f"example (h : False) : {stmt} := {{sym}} h", ["pin_vacuous_statement"]),
            (f"example :\n    ∀ (h : False),\n      {stmt} :=\n  @{{sym}}", ["pin_vacuous_statement"]),
            # Holes that the coarse token scan cannot see.
            (f"example : {stmt} ∧ sorry := {{sym}}", ["pin_sorry_or_admit"]),
        ]
        for pin_text, reasons in rejected_pins:
            with self.subTest(pin=pin_text), tempfile.TemporaryDirectory() as tmp:
                root = Path(tmp)
                self._write_flip_tree(root, {div_id: (None, f": {stmt} := rfl", None)})
                audit = root / suite.AUTHORITY_AUDIT_FILES["MiniRustSpec"]
                with audit.open("a", encoding="utf-8") as fh:
                    fh.write(pin_text.replace("{sym}", sym) + "\n")
                rec = self._flip_status(root, div_id)
                self.assertEqual(rec["status"], "resolution_unpinned")
                self.assertEqual(rec["resolution_pin_problems"], reasons)
                # A meaningful pin beside the rejected one resolves the entry.
                with audit.open("a", encoding="utf-8") as fh:
                    fh.write(f"example : {stmt} :=\n  @{sym}\n")
                rec = self._flip_status(root, div_id)
                self.assertEqual((rec["status"], rec["resolution_pin_problems"]), ("resolved", []))
        # The dashboard reports why a pin was rejected.
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            self._write_flip_tree(
                root, {div_id: (None, f": {stmt} := rfl", f"∀ (h : False), {stmt}")}
            )
            _, _, md = suite.run_suite_and_generate_dashboard(
                repo_root=root, profile="census-only", state_dir=root / "state_render"
            )
            self.assertIn(f"**unpinned resolution** `{sym}`", md)
            self.assertIn("rejected pins: pin_vacuous_statement", md)

    def test_flip_direction_transition_audit_against_a_baseline_tree(self) -> None:
        stmt = SYNTH_STMT
        changed_stmt = "annealOutcome fooProg = miriOutcome fooProg ∧ annealTrace fooProg = miriTrace fooProg"
        baseline_overrides = {
            # Proper flip: witness only in the baseline.
            "DIV-LM-D6-OFFSET-DISABLED-TAG": (f": {SYNTH_DIVERGENCE_STMT} := rfl", None, None),
            # Bare rename: the baseline witness statement becomes the "simulation".
            "DIV-LM-ENUM-SET-DISCR-UNINIT": (": annealStep s ≠ miriStep s := by decide", None, None),
            # The simulation theorem already held, unchanged, next to the live witness.
            "DIV-MR-TB-UNSAFECELL-PROTECTED-IM": (
                f": {SYNTH_DIVERGENCE_STMT} := rfl",
                f": {stmt} := rfl",
                stmt,
            ),
            # The same, but the flip changes the simulation statement.
            "DIV-MR-TB-TWOPHASE-DIRECT-WRITE": (
                f": {SYNTH_DIVERGENCE_STMT} := rfl",
                f": {stmt} := rfl",
                stmt,
            ),
            # Incomplete flips: vacuous simulation / vacuous pin.
            "DIV-LM-RAW-OVERWRITE-CHAR-COPY": (f": {SYNTH_DIVERGENCE_STMT} := rfl", None, None),
            "DIV-MR-CALLER-BORROW-ACROSS-SCALAR-CALL": (
                f": {SYNTH_DIVERGENCE_STMT} := rfl",
                None,
                None,
            ),
        }
        current_overrides = {
            "DIV-LM-D6-OFFSET-DISABLED-TAG": (None, f": {stmt} := rfl", stmt),
            "DIV-LM-ENUM-SET-DISCR-UNINIT": (None, ": annealStep s ≠ miriStep s := by decide", "annealStep s ≠ miriStep s"),
            "DIV-MR-TB-UNSAFECELL-PROTECTED-IM": (None, f": {stmt} := rfl", stmt),
            "DIV-MR-TB-TWOPHASE-DIRECT-WRITE": (None, f": {changed_stmt} := ⟨rfl, rfl⟩", changed_stmt),
            "DIV-LM-RAW-OVERWRITE-CHAR-COPY": (None, ": True := trivial", stmt),
            "DIV-MR-CALLER-BORROW-ACROSS-SCALAR-CALL": (None, f": {stmt} := rfl", "True ∧ True"),
            # Regressions of resolved entries: the witness is back / the simulation
            # became vacuous.
            "DIV-MR-CALL-TARGET-LOCAL": (f": {SYNTH_DIVERGENCE_STMT} := rfl", f": {stmt} := rfl", stmt),
            "DIV-MR-TB-FNENTRY-LOCAL-DEALLOC": (None, ": 0 = 0 := rfl", stmt),
        }
        with tempfile.TemporaryDirectory() as base_tmp, tempfile.TemporaryDirectory() as cur_tmp:
            base_root, cur_root = Path(base_tmp), Path(cur_tmp)
            self._write_flip_tree(base_root, baseline_overrides)
            self._write_flip_tree(cur_root, current_overrides)
            audit = suite.audit_flip_direction_transitions(base_root, cur_root)
            self.assertFalse(audit["passed"])
            self.assertEqual(
                sorted((t["id"], t["from"], t["to"]) for t in audit["transitions"]),
                sorted(
                    [
                        ("DIV-LM-D6-OFFSET-DISABLED-TAG", "open", "resolved"),
                        ("DIV-LM-ENUM-SET-DISCR-UNINIT", "open", "resolved"),
                        ("DIV-MR-TB-UNSAFECELL-PROTECTED-IM", "open", "resolved"),
                        ("DIV-MR-TB-TWOPHASE-DIRECT-WRITE", "open", "resolved"),
                        ("DIV-LM-RAW-OVERWRITE-CHAR-COPY", "open", "resolution_invalid"),
                        ("DIV-MR-CALLER-BORROW-ACROSS-SCALAR-CALL", "open", "resolution_unpinned"),
                        ("DIV-MR-CALL-TARGET-LOCAL", "resolved", "open"),
                        ("DIV-MR-TB-FNENTRY-LOCAL-DEALLOC", "resolved", "resolution_invalid"),
                    ]
                ),
            )
            self.assertEqual(
                sorted((v["id"], v["reason"]) for v in audit["violations"]),
                sorted(
                    [
                        ("DIV-LM-ENUM-SET-DISCR-UNINIT", "polarity_not_flipped"),
                        ("DIV-MR-TB-UNSAFECELL-PROTECTED-IM", "resolution_predates_flip"),
                        ("DIV-LM-RAW-OVERWRITE-CHAR-COPY", "incomplete_flip"),
                        ("DIV-MR-CALLER-BORROW-ACROSS-SCALAR-CALL", "incomplete_flip"),
                        ("DIV-MR-CALL-TARGET-LOCAL", "flip_regressed"),
                        ("DIV-MR-TB-FNENTRY-LOCAL-DEALLOC", "flip_regressed"),
                    ]
                ),
            )
            details = {v["id"]: v["detail"] for v in audit["violations"]}
            self.assertIn("vacuous_statement", details["DIV-LM-RAW-OVERWRITE-CHAR-COPY"])
            self.assertIn("pin_vacuous_statement", details["DIV-MR-CALLER-BORROW-ACROSS-SCALAR-CALL"])
            self.assertIn("annealStep s ≠ miriStep s", details["DIV-LM-ENUM-SET-DISCR-UNINIT"])
            # An unchanged tree has no transitions.
            same = suite.audit_flip_direction_transitions(cur_root, cur_root)
            self.assertEqual((same["passed"], same["transitions"], same["violations"]), (True, [], []))
            # Only the proper flips remain once the violating entries are fixed.
            fixed_overrides = {
                k: v
                for k, v in current_overrides.items()
                if k in ("DIV-LM-D6-OFFSET-DISABLED-TAG", "DIV-MR-TB-TWOPHASE-DIRECT-WRITE")
            }
            fixed_root = Path(cur_tmp) / "fixed"
            self._write_flip_tree(fixed_root, fixed_overrides)
            base_fixed = Path(base_tmp) / "fixed"
            self._write_flip_tree(
                base_fixed,
                {
                    k: v
                    for k, v in baseline_overrides.items()
                    if k in ("DIV-LM-D6-OFFSET-DISABLED-TAG", "DIV-MR-TB-TWOPHASE-DIRECT-WRITE")
                },
            )
            ok = suite.audit_flip_direction_transitions(base_fixed, fixed_root)
            self.assertTrue(ok["passed"], ok["violations"])
            self.assertEqual(
                sorted(t["id"] for t in ok["transitions"]),
                ["DIV-LM-D6-OFFSET-DISABLED-TAG", "DIV-MR-TB-TWOPHASE-DIRECT-WRITE"],
            )

    def test_flip_direction_audit_fails_the_dashboard_run_and_cli_on_violations(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            tmp_dir = Path(tmp)
            base = tmp_dir / "baseline"
            for rel in suite.flip_direction_tracked_files():
                src = REPO_ROOT / rel
                if src.is_file():
                    dst = base / rel
                    dst.parent.mkdir(parents=True, exist_ok=True)
                    shutil.copyfile(src, dst)
            code, dashboard, md = suite.run_suite_and_generate_dashboard(
                repo_root=REPO_ROOT,
                profile="census-only",
                state_dir=tmp_dir / "state_same",
                flip_baseline_root=base,
            )
            flip = dashboard["pillar_3_known_issues_and_regressions"]["flip_direction_audit"]
            self.assertEqual((code, flip["passed"], flip["transitions"]), (0, True, []))
            self.assertIn("### 3C. Flip-Direction Witness Polarity Audit", md)
            # A baseline in which the resolved `step_setDiscriminant_uninit_simulation`
            # was still its `_divergence` witness, with the same statement: the current
            # "simulation" theorem is a rename, not a flip.
            lm23 = base / "lean-miri/lean/LeanMiriSpec/Correspondence/SimLM2_3.lean"
            renamed_text, renames = re.subn(
                r"\btheorem step_setDiscriminant_uninit_simulation\b",
                "theorem step_setDiscriminant_uninit_divergence",
                lm23.read_text(encoding="utf-8"),
            )
            self.assertEqual(renames, 1)
            lm23.write_text(renamed_text, encoding="utf-8")
            code, dashboard, md = suite.run_suite_and_generate_dashboard(
                repo_root=REPO_ROOT,
                profile="census-only",
                state_dir=tmp_dir / "state_renamed",
                flip_baseline_root=base,
            )
            self.assertEqual(code, suite.EXIT_SUITE_REGRESSION)
            flip = dashboard["pillar_3_known_issues_and_regressions"]["flip_direction_audit"]
            self.assertEqual(
                [(v["id"], v["reason"]) for v in flip["violations"]],
                [("DIV-LM-ENUM-SET-DISCR-UNINIT", "polarity_not_flipped")],
            )
            self.assertIn(
                "**VIOLATION** `DIV-LM-ENUM-SET-DISCR-UNINIT` (`polarity_not_flipped`)", md
            )
            saved = json.loads(
                (tmp_dir / "state_renamed/reports/LATEST_DASHBOARD_STATE.json").read_text(
                    encoding="utf-8"
                )
            )
            self.assertFalse(
                saved["pillar_3_known_issues_and_regressions"]["flip_direction_audit"]["passed"]
            )
            out = subprocess.run(
                [
                    sys.executable,
                    str(REPO_ROOT / "scripts/run_nightly_verification_suite.py"),
                    "--profile",
                    "census-only",
                    "--state-dir",
                    str(tmp_dir / "state_cli"),
                    "--flip-baseline-root",
                    str(base),
                ],
                capture_output=True,
                text=True,
                check=False,
            )
            self.assertEqual(out.returncode, suite.EXIT_SUITE_REGRESSION, out.stderr)
            self.assertIn("(`polarity_not_flipped`)", out.stdout)
            # Without a baseline, the audit does not run.
            code, dashboard, md = suite.run_suite_and_generate_dashboard(
                repo_root=REPO_ROOT, profile="census-only", state_dir=tmp_dir / "state_none"
            )
            self.assertEqual(code, 0)
            self.assertIsNone(dashboard["pillar_3_known_issues_and_regressions"]["flip_direction_audit"])
            self.assertNotIn("3C. Flip-Direction", md)
            # An unknown baseline revision or a missing baseline directory is an error.
            for flag, value in (
                ("--flip-baseline-ref", "refs/heads/no-such-flip-baseline-ref"),
                ("--flip-baseline-root", str(tmp_dir / "missing")),
            ):
                with self.subTest(flag=flag):
                    out = subprocess.run(
                        [
                            sys.executable,
                            str(REPO_ROOT / "scripts/run_nightly_verification_suite.py"),
                            "--profile",
                            "census-only",
                            "--state-dir",
                            str(tmp_dir / "state_err"),
                            flag,
                            value,
                        ],
                        capture_output=True,
                        text=True,
                        check=False,
                    )
                    self.assertEqual(out.returncode, suite.EXIT_INTERNAL_ERROR, out.stderr)

    def test_materialize_flip_baseline_tree_reads_tracked_files_at_a_git_revision(self) -> None:
        git = shutil.which("git")
        if git is None:
            self.skipTest("git is not installed")
        with tempfile.TemporaryDirectory() as tmp:
            repo = Path(tmp) / "repo"
            repo.mkdir()

            def run_git(*args: str) -> None:
                subprocess.run(
                    [
                        git,
                        "-c",
                        "user.name=Flip Audit Test",
                        "-c",
                        "user.email=flip-audit@example.com",
                        "-c",
                        "commit.gpgsign=false",
                        *args,
                    ],
                    cwd=repo,
                    check=True,
                    capture_output=True,
                )

            run_git("init", "-q")
            self._write_flip_tree(
                repo, {"DIV-LM-D6-OFFSET-DISABLED-TAG": (f": {SYNTH_DIVERGENCE_STMT} := rfl", None, None)}
            )
            run_git("add", "-A")
            run_git("commit", "-q", "-m", "baseline")
            d6 = repo / "lean-miri/lean/LeanMiriSpec/Correspondence/SimLM3_1.lean"
            witness_line = (
                f"theorem step_binOp_offset_disabled_divergence : {SYNTH_DIVERGENCE_STMT} := rfl\n"
            )
            d6_text = d6.read_text(encoding="utf-8")
            self.assertEqual(d6_text.count(witness_line), 1)
            d6.write_text(
                d6_text.replace(
                    witness_line,
                    f"theorem step_binOp_offset_disabled_simulation : {SYNTH_STMT} := rfl\n",
                ),
                encoding="utf-8",
            )
            with (repo / suite.AUTHORITY_AUDIT_FILES["LeanMiriSpec"]).open("a", encoding="utf-8") as fh:
                fh.write(f"example : {SYNTH_STMT} :=\n  step_binOp_offset_disabled_simulation\n")
            (repo / "unrelated.txt").write_text("not a tracked file\n", encoding="utf-8")
            run_git("add", "-A")
            run_git("commit", "-q", "-m", "flip")
            dest = Path(tmp) / "baseline_tree"
            self.assertEqual(suite.materialize_flip_baseline_tree(repo, "HEAD~1", dest), dest)
            self.assertFalse((dest / "unrelated.txt").exists())
            self.assertTrue((dest / "lean-miri/lean/LeanMiriSpec/Correspondence/SimLM3_1.lean").is_file())
            audit = suite.audit_flip_direction_transitions(dest, repo)
            self.assertTrue(audit["passed"], audit["violations"])
            self.assertEqual(
                audit["transitions"],
                [{"id": "DIV-LM-D6-OFFSET-DISABLED-TAG", "from": "open", "to": "resolved"}],
            )
            with self.assertRaises(ValueError):
                suite.materialize_flip_baseline_tree(repo, "no-such-ref", Path(tmp) / "x")

    def test_flip_direction_audit_rejects_proof_holes_hidden_behind_macros_and_axioms(self) -> None:
        d6 = "DIV-LM-D6-OFFSET-DISABLED-TAG"
        sym = "step_binOp_offset_disabled_simulation"
        sim31 = "lean-miri/lean/LeanMiriSpec/Correspondence/SimLM3_1.lean"

        def flip_trees(tmp: str, cur_decls: str) -> tuple[Path, Path]:
            base_root, cur_root = Path(tmp) / "base", Path(tmp) / "cur"
            self._write_flip_tree(base_root, {d6: (f": {SYNTH_DIVERGENCE_STMT} := rfl", None, None)})
            self._write_flip_tree(cur_root, {d6: (None, None, SYNTH_STMT)})
            with (cur_root / sim31).open("a", encoding="utf-8") as fh:
                fh.write(cur_decls)
            return base_root, cur_root

        # A hole that the theorem's own text does not spell but that an earlier command
        # of its module supplies (a tactic macro or notation expanding to `sorry`, an
        # `axiom`, an `@[simp]` / `attribute [simp]` lemma or an `instance` proved by
        # `sorry`, or `debug.skipKernelTC`) already fails the single-tree scan
        # (`hole_dependency`), so the flip audit reports an incomplete flip.
        hidden_before = {
            "macro_sorry": (
                'macro "close_goal" : tactic => `(tactic| sorry)\n'
                f"theorem {sym} : {SYNTH_STMT} := by close_goal\n"
            ),
            "macro_admit": (
                'macro "close_goal" : tactic => `(tactic| admit)\n'
                f"theorem {sym} : {SYNTH_STMT} := by close_goal\n"
            ),
            "notation": f'notation "cheat" => sorry\ntheorem {sym} : {SYNTH_STMT} := cheat\n',
            "axiom": f"axiom flipCheat : False\ntheorem {sym} : {SYNTH_STMT} := flipCheat.elim\n",
            "simp_lemma": (
                f"@[simp] theorem flipCheat : {SYNTH_STMT} := sorry\n"
                f"theorem {sym} : {SYNTH_STMT} := by simp\n"
            ),
            "attribute": (
                f"theorem flipCheat : {SYNTH_STMT} := sorry\nattribute [simp] flipCheat\n"
                f"theorem {sym} : {SYNTH_STMT} := by simp\n"
            ),
            "instance": (
                f"instance flipCheat : Fact ({SYNTH_STMT}) := ⟨sorry⟩\n"
                f"theorem {sym} : {SYNTH_STMT} := Fact.out\n"
            ),
            "skip_kernel_tc": (
                f"set_option debug.skipKernelTC true in\ntheorem {sym} : {SYNTH_STMT} := cheat\n"
            ),
        }
        for label, decls in hidden_before.items():
            with self.subTest(hole=label), tempfile.TemporaryDirectory() as tmp:
                base_root, cur_root = flip_trees(tmp, decls)
                rec = self._flip_status(cur_root, d6)
                self.assertEqual(
                    (rec["status"], rec["resolution_problems"]), ("resolution_invalid", ["hole_dependency"])
                )
                audit = suite.audit_flip_direction_transitions(base_root, cur_root)
                self.assertEqual(
                    [(v["id"], v["reason"]) for v in audit["violations"]], [(d6, "incomplete_flip")]
                )
                self.assertIn("hole_dependency", audit["violations"][0]["detail"])

        # A hole that the single-tree scan cannot pin on the theorem (a later declaration,
        # or a metaprogram building `sorryAx` from a quoted name) passes that scan, but
        # the flip audit sees the flip add it to the resolution file.
        hidden_after = {
            "later_sorry": (f"theorem laterHelper : {SYNTH_STMT} := sorry\n", {"sorry": 1}),
            "later_axiom": ("axiom laterCheat : False\n", {"axiom": 1}),
            "name_literal": ('elab "cheat" : term => return mkConst ``sorryAx\n', {"sorryAx": 1}),
            "kernel_bypass": (
                "def addUnchecked := Lean.Environment.addDeclWithoutChecking\n",
                {"addDeclWithoutChecking": 1},
            ),
        }
        for label, (hole_decl, added) in hidden_after.items():
            with self.subTest(hole=label), tempfile.TemporaryDirectory() as tmp:
                base_root, cur_root = flip_trees(tmp, f"theorem {sym} : {SYNTH_STMT} := rfl\n{hole_decl}")
                self.assertEqual(self._flip_status(cur_root, d6)["status"], "resolved")
                audit = suite.audit_flip_direction_transitions(base_root, cur_root)
                self.assertEqual(
                    [(v["id"], v["reason"]) for v in audit["violations"]],
                    [(d6, "proof_hole_introduced")],
                )
                self.assertIn(f"`{sim31}` gained proof-hole tokens {added}", audit["violations"][0]["detail"])
                # A hole that the baseline already had is not attributed to the flip,
                # and `.axiom` / `.sorry` field accesses are not holes.
                with (base_root / sim31).open("a", encoding="utf-8") as fh:
                    fh.write(hole_decl)
                    fh.write("def fieldUses : Nat := Config.axiom + Tactic.sorry\n")
                self.assertTrue(suite.audit_flip_direction_transitions(base_root, cur_root)["passed"])

    def test_census_only_end_to_end_dashboard_and_ratchet(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            state_dir = Path(tmp) / "state_out"
            code, dashboard, report_md = suite.run_suite_and_generate_dashboard(
                repo_root=REPO_ROOT,
                profile="census-only",
                state_dir=state_dir,
            )
            self.assertEqual(code, 0)
            self.assertEqual(
                dashboard["pillar_2_correctness_and_correspondence"]["overall_status"],
                "PASS",
            )
            self.assertIn("Pillar 1: 10,000-Foot Project Completeness", report_md)
            self.assertTrue((state_dir / "reports/LATEST_DASHBOARD_STATE.json").is_file())
            self.assertTrue((state_dir / "reports/LATEST_SUITE_REPORT.md").is_file())
            self.assertTrue((state_dir / "state/correspondence_ratchet.json").is_file())
            self.assertTrue((state_dir / "state/completeness_history.jsonl").is_file())

            loaded = json.loads(
                (state_dir / "reports/LATEST_DASHBOARD_STATE.json").read_text(encoding="utf-8")
            )
            self.assertEqual(loaded["schema_version"], 1)

    def test_build_suite_steps_ordering_core_theory_and_profile_isolation(self) -> None:
        census_steps = suite.build_suite_steps(REPO_ROOT, "census-only")
        census_names = [s[0] for s in census_steps]
        self.assertEqual(
            census_names,
            ["lean_miri_semantic_source_lint", "ci_check_non_stable_version"],
        )
        for _name, _cat, cmd, _timeout in census_steps:
            self.assertNotIn("lake", cmd)
            self.assertNotIn("cargo", cmd)

        quick_steps = suite.build_suite_steps(REPO_ROOT, "quick")
        quick_names = [s[0] for s in quick_steps]
        self.assertIn("lake_build_core_theory", quick_names)
        self.assertIn("check_trusted_fast", quick_names)
        self.assertLess(
            quick_names.index("lake_build_core_theory"),
            quick_names.index("check_trusted_fast"),
        )
        self.assertNotIn("check_trusted_self_test", quick_names)
        for wave_step in suite.LOW_RAM_SINGLE_THREAD_STEPS | {"lake_build_examples_miri_vendor"}:
            self.assertNotIn(wave_step, quick_names)
        self.assertEqual(quick_names[-2:], ["lake_build_examples_trusted", "rust_workspace_unit_tests"])

        nightly_steps = suite.build_suite_steps(REPO_ROOT, "nightly")
        nightly_names = [s[0] for s in nightly_steps]
        core_idx = nightly_names.index("lake_build_core_theory")
        for dependent in (
            "check_trusted_fast",
            "check_trusted_self_test",
            "tests_mir_bit_validity_stage1",
            "tests_mir_byte_codec",
            "tests_mir_cast_stage1",
            "tests_mir_adt_and_control",
            "tests_mir_slice_wide_ptr_lens",
            "tests_mir_untested_variant_correspondence",
            "lake_build_correspondence",
            "lake_build_minirust_spec_core",
            "lake_build_minirust_spec",
            "lake_build_examples_trusted",
            "lake_build_examples_miri_vendor",
            "lake_build_lean_miri_spec_core",
            "lake_build_lean_miri_spec",
        ):
            self.assertIn(dependent, nightly_names)
            self.assertLess(
                core_idx,
                nightly_names.index(dependent),
                f"lake_build_core_theory must precede {dependent}",
            )

        core_step = dict((s[0], s) for s in nightly_steps)["lake_build_core_theory"]
        self.assertEqual(core_step[1], "cat1_trusted_boundary")
        self.assertEqual(
            core_step[2][-5:],
            ["lake", "build", "Trusted", "Anneal", "MiniRust"],
        )

        # `lake env lean` never builds imports: every `tests_mir_*` file's workspace
        # imports must be built (`lake build +<Module>`) before it runs. `Anneal.ByteCodec`
        # and `Anneal.Mir.Cast` are outside the `Trusted`/`Anneal`/`MiniRust` closure, so
        # on a cold checkout `lake_build_core_theory` alone leaves them without `.olean`s.
        self.assertNotIn("lake_build_mir_test_modules", quick_names)
        self.assertNotIn("lake_build_mir_test_modules", census_names)
        by_name = dict((s[0], s) for s in nightly_steps)
        mods_step = by_name["lake_build_mir_test_modules"]
        sep = mods_step[2].index("--") if "--" in mods_step[2] else -1
        inner = mods_step[2][sep + 1 :]
        self.assertEqual(inner[:2], ["lake", "build"])
        built = {t[1:] for t in inner[2:] if t.startswith("+")}
        mods_idx = nightly_names.index("lake_build_mir_test_modules")
        self.assertLess(core_idx, mods_idx)
        import_re = re.compile(r"^import\s+(\S+)", re.MULTILINE)
        workspace_libs = suite.CORE_THEORY_LIBS + ("Correspondence", "MiniRustSpec")
        for step_name, rel in suite.MIR_STANDALONE_LEAN_TESTS:
            self.assertLess(mods_idx, nightly_names.index(step_name))
            self.assertEqual(by_name[step_name][2][-4:], ["lake", "env", "lean", rel])
            path = REPO_ROOT / rel
            if not path.is_file():
                # Only the Episode 2 correspondence suite may be absent (written concurrently);
                # its declared header is then covered by `_MIR_TEST_MODULE_FALLBACK`.
                self.assertEqual(rel, UNTESTED_VARIANT_TEST)
                imports = list(UNTESTED_VARIANT_TEST_WORKSPACE_IMPORTS)
            else:
                imports = import_re.findall(path.read_text(encoding="utf-8"))
            self.assertTrue(imports, rel)
            for mod in imports:
                if mod.split(".")[0] in workspace_libs:
                    self.assertIn(mod, built, f"{rel} imports {mod}, which must be pre-built")
        self.assertTrue({"Anneal.ByteCodec", "Anneal.Mir.Cast", "Anneal.Mir.AdtAndControl"} <= built)
        self.assertTrue(set(UNTESTED_VARIANT_TEST_WORKSPACE_IMPORTS) <= built)
        self.assertEqual(sorted(built), sorted(suite._MIR_TEST_MODULE_FALLBACK))
        self.assertEqual(len(suite._MIR_TEST_MODULE_FALLBACK), len(set(suite._MIR_TEST_MODULE_FALLBACK)))
        # The exact standalone `tests/mir` suites the nightly runs, including the
        # `Anneal.Mir.AdtAndControl` kernel-regression / axiom-pin suite, Episode 1's slice-lens
        # witnesses and Episode 2's untested-variant correspondence suite.
        self.assertEqual(
            sorted(rel for _step, rel in suite.MIR_STANDALONE_LEAN_TESTS),
            sorted(
                f"tests/mir/{name}.lean"
                for name in (
                    "BitValidityStage1Tests",
                    "ByteCodecTests",
                    "CastStage1Tests",
                    "AdtAndControlTests",
                    "MirSliceWidePtrLensTests",
                    "MirUntestedVariantCorrespondenceTests",
                )
            ),
        )

    @staticmethod
    def _inner_cmd(cmd: list[str]) -> list[str]:
        """The command a step runs, without its `anneal-lean-run` wrapper prefix."""
        return cmd[cmd.index("--") + 1 :] if suite._is_lean_run_wrapped(cmd) else cmd

    def test_examples_trusted_prebuild_precedes_rust_workspace_unit_tests(self) -> None:
        # Parallel `trusted/rustc-capture` tests each start `lake --dir examples build Trusted`
        # when `examples/.lake/build/lib/lean/Trusted.olean` is missing; the suite builds it
        # once, before any `cargo test`, in both profiles that run `cargo test --workspace`.
        census_names = [s[0] for s in suite.build_suite_steps(REPO_ROOT, "census-only")]
        self.assertNotIn("lake_build_examples_trusted", census_names)
        for profile in ("quick", "nightly"):
            steps = suite.build_suite_steps(REPO_ROOT, profile)
            names = [s[0] for s in steps]
            self.assertEqual(names.count("lake_build_examples_trusted"), 1, profile)
            self.assertEqual(names.count("rust_workspace_unit_tests"), 1, profile)
            idx = names.index("lake_build_examples_trusted")
            self.assertEqual(idx + 1, names.index("rust_workspace_unit_tests"), profile)
            self.assertLess(names.index("lake_build_core_theory"), idx, profile)
            _name, category, cmd, timeout_sec = steps[idx]
            self.assertEqual(category, "cat1_trusted_boundary")
            self.assertEqual(timeout_sec, 600)
            self.assertTrue(suite._is_lean_run_wrapped(cmd))
            self.assertEqual(suite._lean_run_wrapper_flags(cmd), ("build", 600, True))
            self.assertEqual(self._inner_cmd(cmd), ["lake", "--dir", "examples", "build", "Trusted"])
            self.assertGreaterEqual(
                suite._outer_timeout_sec(cmd, timeout_sec), timeout_sec + suite.WRAPPER_TIMEOUT_GRACE_SEC
            )
            # No `cargo test` (which may run the racing tests) is scheduled before it.
            cargo_test_steps = [
                name for name, _c, step_cmd, _t in steps if self._inner_cmd(step_cmd)[:2] == ["cargo", "test"]
            ]
            self.assertIn("rust_workspace_unit_tests", cargo_test_steps)
            for name in cargo_test_steps:
                self.assertLess(idx, names.index(name), f"{profile}/{name}")
        # Without a resolvable wrapper the step runs the bare Lake command.
        with mock.patch.object(suite, "_resolve_anneal_lean_run", return_value=None):
            bare = {name: cmd for name, _c, cmd, _t in suite.build_suite_steps(REPO_ROOT, "quick")}
        self.assertEqual(bare["lake_build_examples_trusted"], ["lake", "--dir", "examples", "build", "Trusted"])
        # The prebuild keeps the ambient thread count even on a low-RAM host.
        env = suite._build_step_env(
            "lake_build_examples_trusted",
            base_env={"PATH": "/usr/bin", "LEAN_NUM_THREADS": "4"},
            effective_ram_mib=5712,
        )
        self.assertEqual(env["LEAN_NUM_THREADS"], "4")
        self.assertEqual(env["LAKE_ARTIFACT_CACHE"], "true")
        self.assertEqual(env["LAKE_RESTORE_ARTIFACTS"], "true")

    def test_lean_miri_spec_build_is_split_into_vendor_and_spec_steps(self) -> None:
        for profile in ("census-only", "quick"):
            names = [s[0] for s in suite.build_suite_steps(REPO_ROOT, profile)]
            self.assertNotIn("lake_build_examples_miri_vendor", names)
            self.assertNotIn("lake_build_lean_miri_spec_core", names)
            self.assertNotIn("lake_build_lean_miri_spec", names)
        steps = suite.build_suite_steps(REPO_ROOT, "nightly")
        names = [s[0] for s in steps]
        by_name = {name: (cat, cmd, timeout_sec) for name, cat, cmd, timeout_sec in steps}
        self.assertEqual(len(names), len(set(names)))
        vendor_idx = names.index("lake_build_examples_miri_vendor")
        self.assertEqual(names[vendor_idx + 1], "lake_build_lean_miri_spec_core")
        self.assertEqual(names[vendor_idx + 2], "lake_build_lean_miri_spec")
        self.assertEqual(names[vendor_idx - 1], "lake_build_minirust_spec")
        self.assertLess(names.index("lake_build_core_theory"), vendor_idx)
        expected = {
            "lake_build_examples_miri_vendor": (["lake", "--dir", "examples", "build", "Miri"], 900),
            "lake_build_lean_miri_spec_core": (
                [
                    "lake",
                    "--dir",
                    "examples",
                    "build",
                    "LeanMiriSpec.Correspondence.Translate",
                    "LeanMiriSpec.Correspondence.SimLM2_1",
                    "LeanMiriSpec.Correspondence.SimLM3_1",
                ],
                1200,
            ),
            "lake_build_lean_miri_spec": (["lake", "--dir", "examples", "build", "LeanMiriSpec"], 1800),
        }
        grace = suite.WRAPPER_TIMEOUT_GRACE_SEC
        for name, (inner, budget) in expected.items():
            category, cmd, timeout_sec = by_name[name]
            self.assertEqual(category, "cat2_correspondence_suites", name)
            self.assertEqual(timeout_sec, budget, name)
            self.assertTrue(suite._is_lean_run_wrapped(cmd), name)
            self.assertEqual(suite._lean_run_wrapper_flags(cmd), ("build", budget, True), name)
            self.assertEqual(self._inner_cmd(cmd), inner, name)
            self.assertEqual(
                suite._outer_timeout_sec(cmd, timeout_sec),
                max(suite.LEAN_RUN_SLOT_WAIT_SEC["build"], budget)
                + max(suite.LEAN_RUN_OOM_RETRY_WINDOW_SEC, budget)
                + grace,
                name,
            )
        # All three steps (and the `Trusted` prebuild) name libraries the `examples` Lake root
        # declares, the core wave's `.lean` files exist on disk, and the vendored library is
        # the one the stale-`.olean` guard already treats as independent of `Trusted`.
        import tomllib

        examples_libs = {
            lib["name"]
            for lib in tomllib.loads((REPO_ROOT / "examples/lakefile.toml").read_text(encoding="utf-8"))["lean_lib"]
        }
        self.assertTrue({"Trusted", "Miri", "LeanMiriSpec"} <= examples_libs)
        for mod in ("Translate", "SimLM2_1", "SimLM3_1"):
            self.assertTrue(
                (REPO_ROOT / f"lean-miri/lean/LeanMiriSpec/Correspondence/{mod}.lean").is_file(), mod
            )
        self.assertIn("Miri", suite._TRUSTED_INDEPENDENT_LIBS)
        self.assertNotIn("LeanMiriSpec", suite._TRUSTED_INDEPENDENT_LIBS)
        # Without a resolvable wrapper all three run the bare Lake commands, in the same order.
        with mock.patch.object(suite, "_resolve_anneal_lean_run", return_value=None):
            bare = [(name, cmd) for name, _c, cmd, _t in suite.build_suite_steps(REPO_ROOT, "nightly")]
        self.assertEqual([name for name, _cmd in bare], names)
        bare_by_name = dict(bare)
        for name, (inner, _budget) in expected.items():
            self.assertEqual(bare_by_name[name], inner, name)

    def test_minirust_spec_build_is_split_into_core_and_spec_waves(self) -> None:
        for profile in ("census-only", "quick"):
            names = [s[0] for s in suite.build_suite_steps(REPO_ROOT, profile)]
            self.assertNotIn("lake_build_minirust_spec_core", names)
            self.assertNotIn("lake_build_minirust_spec", names)
        steps = suite.build_suite_steps(REPO_ROOT, "nightly")
        names = [s[0] for s in steps]
        by_name = {name: (cat, cmd, timeout_sec) for name, cat, cmd, timeout_sec in steps}
        corr_idx = names.index("lake_build_correspondence")
        self.assertEqual(names[corr_idx + 1], "lake_build_minirust_spec_core")
        self.assertEqual(names[corr_idx + 2], "lake_build_minirust_spec")
        self.assertEqual(names[corr_idx + 3], "lake_build_examples_miri_vendor")
        expected = {
            "lake_build_minirust_spec_core": (
                [
                    "lake",
                    "build",
                    "MiniRustSpec.Correspondence.MiniRustEval",
                    "MiniRustSpec.Correspondence.AnnealEval",
                ],
                900,
            ),
            "lake_build_minirust_spec": (["lake", "build", "MiniRustSpec"], 1200),
        }
        grace = suite.WRAPPER_TIMEOUT_GRACE_SEC
        for name, (inner, budget) in expected.items():
            category, cmd, timeout_sec = by_name[name]
            self.assertEqual(category, "cat2_correspondence_suites", name)
            self.assertEqual(timeout_sec, budget, name)
            self.assertTrue(suite._is_lean_run_wrapped(cmd), name)
            self.assertEqual(suite._lean_run_wrapper_flags(cmd), ("build", budget, True), name)
            self.assertEqual(self._inner_cmd(cmd), inner, name)
            self.assertEqual(
                suite._outer_timeout_sec(cmd, timeout_sec),
                max(suite.LEAN_RUN_SLOT_WAIT_SEC["build"], budget)
                + max(suite.LEAN_RUN_OOM_RETRY_WINDOW_SEC, budget)
                + grace,
                name,
            )
        for mod in ("MiniRustEval", "AnnealEval"):
            self.assertTrue(
                (REPO_ROOT / f"minirust/lean/MiniRustSpec/Correspondence/{mod}.lean").is_file(), mod
            )
        with mock.patch.object(suite, "_resolve_anneal_lean_run", return_value=None):
            bare = [(name, cmd) for name, _c, cmd, _t in suite.build_suite_steps(REPO_ROOT, "nightly")]
        self.assertEqual([name for name, _cmd in bare], names)
        bare_by_name = dict(bare)
        for name, (inner, _budget) in expected.items():
            self.assertEqual(bare_by_name[name], inner, name)

    def test_low_ram_single_thread_policy_covers_minirust_spec_and_lean_miri_spec_only(self) -> None:
        self.assertEqual(
            suite.LOW_RAM_SINGLE_THREAD_STEPS,
            frozenset(
                {
                    "lake_build_minirust_spec_core",
                    "lake_build_minirust_spec",
                    "lake_build_lean_miri_spec_core",
                    "lake_build_lean_miri_spec",
                }
            ),
        )
        self.assertEqual(suite.LEAN_MIRI_SPEC_SINGLE_THREAD_RAM_THRESHOLD_MIB, 10240)
        nightly = suite.build_suite_steps(REPO_ROOT, "nightly")
        nightly_names = [name for name, _c, _cmd, _t in nightly]
        self.assertTrue(suite.LOW_RAM_SINGLE_THREAD_STEPS <= set(nightly_names))

        def threads(step: str, ram: object, base: str | None = "4", **kwargs: object) -> str | None:
            base_env = {"PATH": "/usr/bin"}
            if base is not None:
                base_env["LEAN_NUM_THREADS"] = base
            return suite._build_step_env(step, base_env=base_env, effective_ram_mib=ram, **kwargs).get(
                "LEAN_NUM_THREADS"
            )

        for step in sorted(suite.LOW_RAM_SINGLE_THREAD_STEPS):
            # Strictly below 10 GiB: single-threaded, whatever the ambient value.
            for ram in (1, 5712, 10239):
                self.assertEqual(threads(step, ram), "1", (step, ram))
                self.assertEqual(threads(step, ram, base=None), "1", (step, ram))
            # At or above it, or with no usable ceiling: untouched.
            for ram in (10240, 32768, None, True, 5712.0, "5712"):
                self.assertEqual(threads(step, ram), "4", (step, ram))
                self.assertIsNone(threads(step, ram, base=None), (step, ram))
            # Explicit overrides still win.
            self.assertEqual(threads(step, 5712, env_overrides={"LEAN_NUM_THREADS": "3"}), "3", step)
            # The exported threshold is the one the policy reads.
            with mock.patch.object(suite, "LEAN_MIRI_SPEC_SINGLE_THREAD_RAM_THRESHOLD_MIB", 4096):
                self.assertEqual(threads(step, 5712), "4", step)
                self.assertEqual(threads(step, 4095), "1", step)

        # Every other step of every profile keeps its thread count below 10 GiB, the
        # vendored `Miri` build and the `Trusted` prebuild included.
        others = {
            name
            for profile in ("census-only", "quick", "nightly")
            for name, _c, _cmd, _t in suite.build_suite_steps(REPO_ROOT, profile)
        } - suite.LOW_RAM_SINGLE_THREAD_STEPS
        self.assertTrue(
            {"lake_build_examples_miri_vendor", "lake_build_examples_trusted", "lake_build_correspondence"} <= others
        )
        for step in sorted(others):
            self.assertEqual(threads(step, 5712), "4", step)
            self.assertIsNone(threads(step, 5712, base=None), step)

        # Only the four right-sized steps probe the host and their wrapper.
        with (
            mock.patch.object(suite, "_probe_effective_ram_ceiling_mib", return_value=65536) as host_probe,
            mock.patch.object(suite, "_probe_lean_run_memory_max_mib", return_value=5712) as wrapper_probe,
        ):
            seen = {
                name: suite._build_step_env(name, base_env={"PATH": "/usr/bin", "LEAN_NUM_THREADS": "7"}, cmd=cmd).get(
                    "LEAN_NUM_THREADS"
                )
                for name, _c, cmd, _t in nightly
            }
        self.assertEqual(host_probe.call_count, 4)
        by_name = {name: cmd for name, _c, cmd, _t in nightly}
        self.assertEqual(
            sorted(call.args[0] for call in wrapper_probe.call_args_list),
            sorted(by_name[name] for name in suite.LOW_RAM_SINGLE_THREAD_STEPS),
        )
        self.assertEqual(
            seen,
            {name: ("1" if name in suite.LOW_RAM_SINGLE_THREAD_STEPS else "7") for name in nightly_names},
        )

        # End to end through `_run_step`: with a wrapper that plans a 5712 MiB scope, the
        # `MiniRustSpec` and `LeanMiriSpec` builds see `LEAN_NUM_THREADS=1`, and the vendored
        # `Miri` build keeps the ambient 7 threads.
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp).resolve()
            wrapper = root / "bin/anneal-lean-run"
            wrapper.parent.mkdir()
            wrapper.write_text(
                f"#!{sys.executable}\n"
                "import json, os, sys\n"
                "args = sys.argv[1:]\n"
                "if '--probe' in args:\n"
                "    print(json.dumps({'memory_max_mb': 5712}))\n"
                "    sys.exit(0)\n"
                "cmd = args[args.index('--') + 1:]\n"
                "os.execvp(cmd[0], cmd)\n",
                encoding="utf-8",
            )
            wrapper.chmod(0o755)
            out_file = root / "threads.txt"
            dump = (
                "import os, pathlib; "
                f"pathlib.Path({str(out_file)!r}).write_text(os.environ.get('LEAN_NUM_THREADS', '<unset>'))"
            )
            run_cmd = [str(wrapper), "--mode", "build", "--timeout", "30", "--", sys.executable, "-c", dump]
            for step, expected in (
                ("lake_build_minirust_spec_core", "1"),
                ("lake_build_minirust_spec", "1"),
                ("lake_build_lean_miri_spec_core", "1"),
                ("lake_build_lean_miri_spec", "1"),
                ("lake_build_examples_miri_vendor", "7"),
            ):
                out_file.unlink(missing_ok=True)
                with (
                    mock.patch.object(suite, "_probe_effective_ram_ceiling_mib", return_value=65536),
                    mock.patch.dict(os.environ, {"LEAN_NUM_THREADS": "7"}),
                ):
                    res = suite._run_step(
                        name=step,
                        category="cat2_correspondence_suites",
                        cmd=run_cmd,
                        cwd=root,
                        timeout_sec=30,
                    )
                self.assertEqual(res["status"], "PASS", res.get("failure_excerpt"))
                self.assertEqual(out_file.read_text(encoding="utf-8"), expected, step)

    def test_low_ram_policy_skips_probe_on_explicit_override_and_passthrough(self) -> None:
        # 1. Explicit `env_overrides={"LEAN_NUM_THREADS": ...}` takes final precedence AND
        #    avoids spawning a wasted wrapper probe for every right-sized step.
        # 2. Under `ANNEAL_LEAN_RUN_IN_SCOPE=1` without `--nested-ok`, the wrapper runs
        #    `_exec_passthrough` and never creates a new leaf scope, so
        #    `_probe_lean_run_memory_max_mib` must return `None` (no phantom nested cap)
        #    while `--nested-ok` still probes the wrapper.
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp).resolve()
            wrapper = root / "bin/anneal-lean-run"
            wrapper.parent.mkdir()
            probe_log = root / "probes.txt"
            wrapper.write_text(
                f"#!{sys.executable}\n"
                "import json, sys\n"
                f"open({str(probe_log)!r}, 'a', encoding='utf-8').write(json.dumps(sys.argv[1:]) + '\\n')\n"
                "print(json.dumps({'memory_max_mb': 5712}))\n",
                encoding="utf-8",
            )
            wrapper.chmod(0o755)
            probe_log.write_text("", encoding="utf-8")

            def probe_count() -> int:
                return len(probe_log.read_text(encoding="utf-8").splitlines())

            plain_cmd = [str(wrapper), "--mode", "build", "--timeout", "1200", "--", "lake", "build", "MiniRustSpec"]
            nested_cmd = [
                str(wrapper),
                "--mode",
                "build",
                "--nested-ok",
                "--timeout",
                "1200",
                "--",
                "lake",
                "build",
                "MiniRustSpec",
            ]

            for step in sorted(suite.LOW_RAM_SINGLE_THREAD_STEPS):
                before = probe_count()
                with mock.patch.object(suite, "_probe_effective_ram_ceiling_mib", return_value=4096) as host_probe:
                    env = suite._build_step_env(
                        step,
                        base_env={"PATH": "/usr/bin", "LEAN_NUM_THREADS": "7"},
                        env_overrides={"LEAN_NUM_THREADS": "3"},
                        cmd=plain_cmd,
                        cwd=root,
                    )
                self.assertEqual(env["LEAN_NUM_THREADS"], "3", step)
                self.assertEqual(host_probe.call_count, 0, step)
                self.assertEqual(probe_count(), before, step)

                # Re-entrancy pass-through inside a >= 10 GiB enclosing scope: do not probe
                # a phantom nested scope that will never be created.
                before = probe_count()
                self.assertIsNone(
                    suite._probe_lean_run_memory_max_mib(
                        plain_cmd, env={"ANNEAL_LEAN_RUN_IN_SCOPE": "1"}, cwd=root
                    )
                )
                with mock.patch.object(suite, "_probe_effective_ram_ceiling_mib", return_value=12288):
                    pt_high = suite._build_step_env(
                        step,
                        base_env={"PATH": "/usr/bin", "LEAN_NUM_THREADS": "7", "ANNEAL_LEAN_RUN_IN_SCOPE": "1"},
                        cmd=plain_cmd,
                        cwd=root,
                    )
                self.assertEqual(pt_high["LEAN_NUM_THREADS"], "7", step)
                self.assertEqual(probe_count(), before, step)

                # Inside a < 10 GiB enclosing scope, the host/cgroup ceiling still forces 1 thread.
                with mock.patch.object(suite, "_probe_effective_ram_ceiling_mib", return_value=8192):
                    pt_low = suite._build_step_env(
                        step,
                        base_env={"PATH": "/usr/bin", "LEAN_NUM_THREADS": "7", "ANNEAL_LEAN_RUN_IN_SCOPE": "1"},
                        cmd=plain_cmd,
                        cwd=root,
                    )
                self.assertEqual(pt_low["LEAN_NUM_THREADS"], "1", step)
                self.assertEqual(probe_count(), before, step)

                # With `--nested-ok`, the wrapper WILL create a nested scope, so probing runs.
                with mock.patch.object(suite, "_probe_effective_ram_ceiling_mib", return_value=12288):
                    nested_env = suite._build_step_env(
                        step,
                        base_env={"PATH": "/usr/bin", "LEAN_NUM_THREADS": "7", "ANNEAL_LEAN_RUN_IN_SCOPE": "1"},
                        cmd=nested_cmd,
                        cwd=root,
                    )
                self.assertEqual(nested_env["LEAN_NUM_THREADS"], "1", step)
                self.assertEqual(probe_count(), before + 1, step)

    def test_real_wrapper_end_to_end_low_ram_right_sizing_and_oom_threads_diagnostic(self) -> None:
        # Cross-script integration: `_run_step` -> real `scripts/anneal-lean-run` (isolated to a
        # temp runtime dir with synthetic 5712 MiB / 8-thread envelope). `lake_build_minirust_spec`
        # and `lake_build_lean_miri_spec` receive `LEAN_NUM_THREADS=1` and report
        # `threads=1, thread_budget=8` on exit 137, whereas `lake_build_examples_miri_vendor` and
        # `lake_build_examples_trusted` keep the ambient thread count.
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp).resolve()
            rt = root / "rt"
            rt.mkdir()
            shim = root / "anneal-lean-run"
            wrapper_src = REPO_ROOT / "scripts/anneal-lean-run"
            shim.write_text(
                f"#!{sys.executable}\n"
                "import importlib.machinery, importlib.util, pathlib, sys\n"
                "sys.dont_write_bytecode = True\n"
                f"loader = importlib.machinery.SourceFileLoader('alr_e2e', {os.fspath(wrapper_src)!r})\n"
                "spec = importlib.util.spec_from_loader(loader.name, loader)\n"
                "mod = importlib.util.module_from_spec(spec)\n"
                "loader.exec_module(mod)\n"
                f"rt = pathlib.Path({os.fspath(rt)!r})\n"
                "mod.resolve_runtime_base = lambda: (rt, False)\n"
                "def _probe(*_a, **_kw):\n"
                "    d = mod.compute_workload_memory_envelope(\n"
                "        cpu_cores=8, mem_total_mb=65536, mem_avail_mb=50000,\n"
                "        user_systemd_active=False, cli_concurrency=1, mode='build',\n"
                "        runtime_base=str(rt),\n"
                "    )\n"
                "    d['memory_max_mb'] = 5712\n"
                "    d['threads'] = 8\n"
                "    return d\n"
                "mod.probe_host_envelope = _probe\n"
                "mod.stamp_last_oom = lambda *a, **kw: None\n"
                "mod._try_oom_offload = lambda *a, **kw: None\n"
                "sys.exit(mod.main(sys.argv[1:]))\n",
                encoding="utf-8",
            )
            shim.chmod(0o755)
            out_file = root / "seen_threads.txt"
            child_ok = (
                "import os, pathlib; "
                f"pathlib.Path({str(out_file)!r}).write_text(os.environ.get('LEAN_NUM_THREADS', '<unset>'))"
            )
            cmd_ok = [str(shim), "--mode", "build", "--no-slot-lock", "--timeout", "30", "--", sys.executable, "-c", child_ok]
            for step, expected in (
                ("lake_build_minirust_spec_core", "1"),
                ("lake_build_minirust_spec", "1"),
                ("lake_build_lean_miri_spec_core", "1"),
                ("lake_build_lean_miri_spec", "1"),
                ("lake_build_examples_miri_vendor", "5"),
                ("lake_build_examples_trusted", "5"),
            ):
                out_file.unlink(missing_ok=True)
                with (
                    mock.patch.object(suite, "_probe_effective_ram_ceiling_mib", return_value=65536),
                    mock.patch.dict(os.environ, {"LEAN_NUM_THREADS": "5"}),
                ):
                    res = suite._run_step(step, "cat2_correspondence_suites", cmd_ok, cwd=root, timeout_sec=30)
                self.assertEqual(res["status"], "PASS", (step, res.get("failure_excerpt")))
                self.assertEqual(out_file.read_text(encoding="utf-8"), expected, step)

            # On OOM (exit 137) under the real wrapper, the failure excerpt reports `threads=1, thread_budget=8`.
            cmd_oom = [str(shim), "--mode", "build", "--no-slot-lock", "--timeout", "30", "--", "sh", "-c", "exit 137"]
            with (
                mock.patch.object(suite, "_probe_effective_ram_ceiling_mib", return_value=65536),
                mock.patch.dict(os.environ, {"LEAN_NUM_THREADS": "5"}),
            ):
                res_oom = suite._run_step(
                    "lake_build_minirust_spec", "cat2_correspondence_suites", cmd_oom, cwd=root, timeout_sec=30
                )
            self.assertEqual(res_oom["status"], "FAIL")
            self.assertEqual(res_oom["exit_code"], 137)
            self.assertIn("MemoryMax=5712M, MemorySwapMax=0, mode=build, threads=1, thread_budget=8,", res_oom["failure_excerpt"])

    def test_examples_trusted_and_miri_split_dashboard_and_stale_olean_coherence(self) -> None:
        # 1. When `examples` has a stale `Trusted` module, `clean_stale_oleans` removes
        #    `Trusted` and `LeanMiriSpec` while preserving vendored `Miri` `.olean`s, matching
        #    the `lake_build_examples_trusted` -> ... -> `lake_build_examples_miri_vendor` ->
        #    `lake_build_lean_miri_spec` build order.
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "examples").mkdir()
            shutil.copy2(REPO_ROOT / "examples/lakefile.toml", root / "examples/lakefile.toml")
            t_old = 1_700_000_000_000_000_000
            t_new = t_old + 5_000_000_000

            def touch(path: Path, ns: int, text: str = "") -> Path:
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(text, encoding="utf-8")
                os.utime(path, ns=(ns, ns))
                return path

            touch(root / "trusted/lean/Trusted/Core.lean", t_new, "-- edited\n")
            touch(root / "lean-miri/vendor/Miri/Core.lean", t_old, "-- vendor\n")
            touch(root / "lean-miri/lean/LeanMiriSpec/Spec.lean", t_old, "-- spec\n")
            ex_lib = root / "examples/.lake/build/lib/lean"
            trusted_olean = touch(ex_lib / "Trusted/Core.olean", t_old)
            miri_olean = touch(ex_lib / "Miri/Core.olean", t_old)
            spec_olean = touch(ex_lib / "LeanMiriSpec/Spec.olean", t_old)

            removed = suite.clean_stale_oleans(root)
            self.assertIn(trusted_olean, removed)
            self.assertIn(spec_olean, removed)
            self.assertNotIn(miri_olean, removed)
            self.assertFalse(trusted_olean.exists())
            self.assertFalse(spec_olean.exists())
            self.assertTrue(miri_olean.exists())

            # 2. `run_suite_and_generate_dashboard` records the new steps and reconciled 90/94
            #    MIR matrix in both JSON and Markdown outputs for `quick` (12) and `nightly` (31).
            #    Stub Stage B corpus scanning and divergence discovery (covered by their own
            #    end-to-end tests) so running both profiles stays fast while Stage A, step
            #    planning, Markdown rendering, and JSON persistence remain real.
            empty_layer = {
                "fully_verifiable_fn_pct": 0.0,
                "fully_verifiable_fns": 0,
                "partially_covered_fn_pct": 0.0,
                "partially_covered_fns": 0,
                "within_blocked_fns_stmt_coverage_pct": 0.0,
                "within_blocked_fns_cfg_prefix_pct": 0.0,
                "total_stmt_coverage_pct": 0.0,
                "blended_completeness_score_pct": 0.0,
            }
            stub_stage_b = {
                "combined": {
                    "total_fns": 0,
                    "total_stmt_units": 0,
                    "top_marginal_unlock_blockers": [],
                    "layers": {
                        layer: dict(empty_layer)
                        for layer in (
                            "trusted_mir",
                            "anneal_proof_lifters",
                            "minirust_correspondence",
                            "lean_miri_correspondence",
                        )
                    },
                },
                "corpora": {},
            }
            stub_divs = {"actionable_anneal_bugs_count": 0, "actionable_anneal_bugs": []}
            for profile, expected_count, required_order in (
                ("quick", 12, ("lake_build_core_theory", "lake_build_examples_trusted", "rust_workspace_unit_tests")),
                (
                    "nightly",
                    31,
                    (
                        "lake_build_core_theory",
                        "lake_build_examples_trusted",
                        "rust_workspace_unit_tests",
                        "lake_build_correspondence",
                        "lake_build_minirust_spec_core",
                        "lake_build_minirust_spec",
                        "lake_build_examples_miri_vendor",
                        "lake_build_lean_miri_spec_core",
                        "lake_build_lean_miri_spec",
                    ),
                ),
            ):
                state_dir = root / f"state_{profile}"
                seen_steps: list[str] = []

                def fake_run_step(
                    name: str,
                    category: str,
                    cmd: list[str],
                    cwd: Path,
                    timeout_sec: int = 900,
                    env_overrides: dict[str, str] | None = None,
                ) -> dict[str, Any]:
                    seen_steps.append(name)
                    return {
                        "name": name,
                        "category": category,
                        "status": "PASS",
                        "exit_code": 0,
                        "duration_sec": 0.01,
                        "command": " ".join(cmd),
                        "audit_tags": [],
                        "failure_excerpt": "",
                    }

                with (
                    mock.patch.object(suite, "compute_stage_b_empirical_corpora", return_value=stub_stage_b),
                    mock.patch.object(suite, "discover_correspondence_divergences", return_value=stub_divs),
                    mock.patch.object(suite, "_preflight_clean_stale_oleans", return_value=[]),
                    mock.patch.object(suite, "_run_step", side_effect=fake_run_step),
                ):
                    rc, dash, md = suite.run_suite_and_generate_dashboard(REPO_ROOT, profile, state_dir)
                self.assertEqual(rc, suite.EXIT_SUCCESS, profile)
                self.assertEqual(len(seen_steps), expected_count, profile)
                indices = [seen_steps.index(s) for s in required_order]
                self.assertEqual(indices, sorted(indices), (profile, required_order))
                p2 = dash["pillar_2_correctness_and_correspondence"]
                self.assertEqual(p2["steps_total"], expected_count, profile)
                self.assertEqual(p2["steps_passed"], expected_count, profile)
                mir = dash["pillar_1_completeness"]["syntactic_authorities"]["anneal_mir_ast"]
                self.assertEqual(mir["proved_corresponding"], 90)
                self.assertEqual(mir["total_variants"], 94)
                self.assertIn("`90` (`95.74%`)", md)
                self.assertIn("`lake_build_examples_trusted`", md)
                if profile == "nightly":
                    self.assertIn("`lake_build_examples_miri_vendor`", md)
                    self.assertLess(md.index("`lake_build_examples_miri_vendor`"), md.index("`lake_build_lean_miri_spec`"))
                persisted = json.loads((state_dir / "reports/LATEST_DASHBOARD_STATE.json").read_text(encoding="utf-8"))
                self.assertEqual(persisted["pillar_2_correctness_and_correspondence"]["steps_total"], expected_count)

    def test_mir_test_prebuild_modules_fallback_when_a_header_is_missing(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            shutil.copy2(REPO_ROOT / "lakefile.toml", root / "lakefile.toml")
            (root / "tests/mir").mkdir(parents=True)
            for _step, rel in suite.MIR_STANDALONE_LEAN_TESTS:
                if rel != UNTESTED_VARIANT_TEST:
                    shutil.copy2(REPO_ROOT / rel, root / rel)
            # The correspondence suite is absent: the fallback fills in its imports, keeping
            # the first-seen order of the full union.
            self.assertEqual(suite.mir_test_prebuild_modules(root), list(suite._MIR_TEST_MODULE_FALLBACK))
            (root / UNTESTED_VARIANT_TEST).write_text(
                "import Trusted\nimport Anneal.MirFuelFree\n"
                "import Correspondence.V2026_06_01.L3_PlacesAndBasicMem\n"
                "import Correspondence.V2026_06_01.L5_ControlAndCalls\n"
                "import MiniRustSpec.Correspondence.Translate\nimport Lean.Elab.Command\n",
                encoding="utf-8",
            )
            self.assertEqual(suite.mir_test_prebuild_modules(root), list(suite._MIR_TEST_MODULE_FALLBACK))
        if (REPO_ROOT / UNTESTED_VARIANT_TEST).is_file():
            self.assertEqual(suite.mir_test_prebuild_modules(REPO_ROOT), list(suite._MIR_TEST_MODULE_FALLBACK))

    def test_timeout_propagation_and_calibrated_step_timeouts(self) -> None:
        nightly_by_name = {
            name: (cat, cmd, timeout_sec)
            for name, cat, cmd, timeout_sec in suite.build_suite_steps(REPO_ROOT, "nightly")
        }
        expected_timeouts = {
            "lake_build_core_theory": 900,
            "check_trusted_fast": 600,
            "lake_build_examples_trusted": 600,
            "rust_workspace_unit_tests": 600,
            "check_trusted_self_test": 1500,
            "tests_mir_bit_validity_stage1": 300,
            "tests_mir_byte_codec": 300,
            "tests_mir_cast_stage1": 300,
            "tests_mir_adt_and_control": 300,
            "tests_mir_slice_wide_ptr_lens": 300,
            "tests_mir_untested_variant_correspondence": 300,
            "lake_build_correspondence": 900,
            "lake_build_minirust_spec_core": 900,
            "lake_build_minirust_spec": 1200,
            "lake_build_examples_miri_vendor": 900,
            "lake_build_lean_miri_spec_core": 1200,
            "lake_build_lean_miri_spec": 1800,
            "domain_integration_tests_anneal_difftest": 1500,
            "cargo_anneal_e2e_minirust_correspondence": 600,
            "cargo_anneal_e2e_pipeline_and_adoption": 900,
        }
        # Raised from 900 s: also pre-builds the `Correspondence` L3/L5 and
        # `MiniRustSpec.Correspondence.Translate` closure of the correspondence suite.
        expected_timeouts["lake_build_mir_test_modules"] = 1500
        for step_name, exp_timeout in expected_timeouts.items():
            self.assertIn(step_name, nightly_by_name)
            _cat, cmd, timeout_sec = nightly_by_name[step_name]
            self.assertEqual(timeout_sec, exp_timeout, f"Unexpected timeout for {step_name}")
            self.assertEqual(Path(cmd[0]).name, "anneal-lean-run", f"{step_name} must be wrapped")
            self.assertIn("--timeout", cmd)
            t_idx = cmd.index("--timeout")
            self.assertEqual(int(cmd[t_idx + 1]), timeout_sec)

        # Every wrapped step in every profile hands its exact step budget to the wrapper.
        for profile in ("census-only", "quick", "nightly"):
            for name, _cat, cmd, timeout_sec in suite.build_suite_steps(REPO_ROOT, profile):
                if not suite._is_lean_run_wrapped(cmd):
                    continue
                mode, inner_timeout, slot_lock = suite._lean_run_wrapper_flags(cmd)
                self.assertEqual(inner_timeout, timeout_sec, f"{profile}/{name}")
                self.assertTrue(slot_lock, f"{profile}/{name}")
                expected_mode = "file" if name.startswith("tests_mir_") else "build"
                self.assertEqual(mode, expected_mode, f"{profile}/{name}")

    def test_run_step_wrapper_timeout_grace_and_exit_124_classification(self) -> None:
        # When a wrapped command exits with 124 (inner anneal-lean-run timeout),
        # `_run_step` classifies status as TIMEOUT and preserves diagnostic stderr.
        res = suite._run_step(
            name="simulated_inner_timeout",
            category="cat2_correspondence_suites",
            cmd=[
                sys.executable,
                "-c",
                "import sys; sys.stderr.write('[anneal-lean-run] ERROR: Command timed out\\n'); sys.exit(124)",
            ],
            cwd=REPO_ROOT,
            timeout_sec=10,
        )
        self.assertEqual(res["status"], "TIMEOUT")
        self.assertEqual(res["exit_code"], 124)
        self.assertIn("[anneal-lean-run] ERROR: Command timed out", res["failure_excerpt"])

        # Verify `_ensure_toolchain_path` populates existing user toolchain dirs into minimal PATH.
        minimal_env = {"PATH": "/usr/bin:/bin"}
        suite._ensure_toolchain_path(minimal_env)
        for rel in (".elan/bin", ".cargo/bin", ".local/bin"):
            cand = Path.home() / rel
            if cand.is_dir():
                self.assertIn(str(cand), minimal_env["PATH"].split(":"))

    def test_outer_timeout_covers_wrapper_slot_wait_and_grace(self) -> None:
        lr = str(REPO_ROOT / "scripts/anneal-lean-run")
        grace = suite.WRAPPER_TIMEOUT_GRACE_SEC
        # What the wrapper does whatever its `--timeout` is (`run_bounded_command` in both
        # `scripts/anneal-lean-run` and the fleet copy): queue up to 1200 s for a build slot
        # in `build` mode and up to 180 s in `file` mode on a memory-capped slice, and give a
        # `build` command the OOM killer ended one retry that expires at most 1200 s after
        # the slot was acquired.
        build_wait = suite.LEAN_RUN_SLOT_WAIT_SEC["build"]
        file_wait = suite.LEAN_RUN_SLOT_WAIT_SEC["file"]
        retry = suite.LEAN_RUN_OOM_RETRY_WINDOW_SEC
        self.assertEqual((build_wait, file_wait, retry), (1200, 180, 1200))
        wrapper_src = (REPO_ROOT / "scripts/anneal-lean-run").read_text(encoding="utf-8")
        self.assertIn("slot_timeout = 1200\n", wrapper_src)
        self.assertIn("slot_timeout = 180\n", wrapper_src)
        self.assertIn(
            "retry_timeout = min(900, max(120, int(1200 - (time.monotonic() - slot_t0))))", wrapper_src
        )
        # Direct commands: the step budget is the only deadline.
        self.assertEqual(suite._outer_timeout_sec(["cargo", "test"], 600), 600)
        # `--mode build`: the outer deadline must exceed the slot queue plus the longer of
        # the command's own `T`-second clock and the OOM-retry window. (A wrapper from before
        # the fixed 1200 s queue waited `max(30, T)` s, which a `T` above 1200 still covers.)
        build = [lr, "--mode", "build", "--concurrency", "1", "--timeout", "1200", "--", "lake", "build"]
        self.assertEqual(suite._outer_timeout_sec(build, 1200), 1200 + 1200 + grace)
        long_build = [lr, "--mode", "build", "--timeout", "1800", "--", "lake", "build"]
        self.assertEqual(suite._outer_timeout_sec(long_build, 1800), 1800 + 1800 + grace)
        short = [lr, "--mode", "build", "--timeout", "10", "--", "lake", "build"]
        self.assertEqual(suite._outer_timeout_sec(short, 10), build_wait + retry + grace)
        mid = [lr, "--mode", "build", "--timeout", "600", "--", "cargo", "test"]
        self.assertEqual(suite._outer_timeout_sec(mid, 600), build_wait + retry + grace)
        # A step that queued 700 s behind another build and then needs 550 s of its 600 s
        # budget is still running at 1250 s: the old `T + max(30, T) + grace` deadline
        # (1230 s) killed it.
        self.assertGreater(suite._outer_timeout_sec(mid, 600), 700 + 550)
        # `file` mode queues only on a memory-capped slice, and never retries.
        file_cmd = [lr, "--mode", "file", "--timeout", "300", "--", "lake", "env", "lean", "X.lean"]
        self.assertEqual(suite._outer_timeout_sec(file_cmd, 300), 300 + file_wait + grace)
        # `--no-slot-lock` never queues (unless `--exclusive` asks for every slot), and
        # `--no-oom-retry` leaves the command's own clock as the only one.
        nolock = [lr, "--mode", "build", "--no-slot-lock", "--timeout=900", "--", "lake", "build"]
        self.assertEqual(suite._lean_run_wrapper_flags(nolock), ("build", 900, False))
        self.assertEqual(suite._outer_timeout_sec(nolock, 900), retry + grace)
        noretry = [lr, "--mode", "build", "--no-slot-lock", "--no-oom-retry", "--timeout=900", "--", "lake"]
        self.assertEqual(suite._outer_timeout_sec(noretry, 900), 900 + grace)
        queued_noretry = [lr, "--mode", "build", "--no-oom", "--timeout", "900", "--", "lake", "build"]
        self.assertEqual(suite._outer_timeout_sec(queued_noretry, 900), build_wait + 900 + grace)
        exclusive = [lr, "--mode", "build", "--no-slot-lock", "--exclusive", "--timeout", "900", "--", "lake"]
        self.assertEqual(suite._lean_run_wrapper_flags(exclusive), ("build", 900, True))
        self.assertEqual(suite._outer_timeout_sec(exclusive, 900), build_wait + retry + grace)
        file_nolock = [lr, "--mode", "file", "--no-slot-lock", "--timeout", "300", "--", "lean", "X.lean"]
        self.assertEqual(suite._outer_timeout_sec(file_nolock, 300), 300 + grace)
        # `auto` resolves like the wrapper; without `--timeout` the wrapper defaults apply.
        auto_file = [lr, "--", "lake", "env", "lean", "X.lean"]
        self.assertEqual(suite._lean_run_wrapper_flags(auto_file), ("file", None, True))
        self.assertEqual(suite._outer_timeout_sec(auto_file, 60), 180 + file_wait + grace)
        auto_file_nosep = [lr, "lake", "env", "lean", "X.lean"]
        self.assertEqual(suite._lean_run_wrapper_flags(auto_file_nosep), ("file", None, True))
        self.assertEqual(suite._outer_timeout_sec(auto_file_nosep, 60), 180 + file_wait + grace)
        auto_build = [lr, "--", "lake", "build", "Anneal"]
        self.assertEqual(suite._lean_run_wrapper_flags(auto_build), ("build", None, True))
        self.assertEqual(suite._outer_timeout_sec(auto_build, 60), build_wait + retry + grace)
        # Inner command `--` and inner flags (e.g. `cargo test -- --no-slot-lock --timeout 5`)
        # must never be mistaken for wrapper flags.
        inner_sep = [
            lr,
            "--mode",
            "build",
            "--timeout",
            "600",
            "cargo",
            "test",
            "--",
            "--no-slot-lock",
            "--mode",
            "file",
            "--timeout",
            "5",
        ]
        self.assertEqual(suite._lean_run_wrapper_flags(inner_sep), ("build", 600, True))
        self.assertEqual(suite._outer_timeout_sec(inner_sep, 600), build_wait + retry + grace)
        # `argparse` long-option prefix abbreviations (`--time`, `--no-slot`, `--conc`) and
        # `ANNEAL_LEAN_TIMEOUT_SEC` env fallback when `--timeout` is omitted.
        abbrev = [lr, "--mo", "build", "--no-slot", "--conc=1", "--time", "450", "--", "lake", "build"]
        self.assertEqual(suite._lean_run_wrapper_flags(abbrev), ("build", 450, False))
        self.assertEqual(suite._outer_timeout_sec(abbrev, 300), retry + grace)
        self.assertEqual(
            suite._outer_timeout_sec(auto_build, 60, env={"ANNEAL_LEAN_TIMEOUT_SEC": "1500"}),
            1500 + 1500 + grace,
        )
        self.assertEqual(
            suite._outer_timeout_sec(auto_file, 60, env={"ANNEAL_LEAN_TIMEOUT_SEC": "240"}),
            240 + file_wait + grace,
        )
        # Explicit `--timeout 0` on the command line overrides `ANNEAL_LEAN_TIMEOUT_SEC`
        # (falling back to the mode default 900s/180s), and `-- --` leaves the second
        # `--` in `inner` (so `detect_mode` resolves to `"build"`, matching `anneal-lean-run`).
        explicit_zero = [lr, "--timeout", "0", "--", "lake", "build", "Anneal"]
        self.assertEqual(
            suite._outer_timeout_sec(explicit_zero, 60, env={"ANNEAL_LEAN_TIMEOUT_SEC": "1500"}),
            build_wait + retry + grace,
        )
        double_sep = [lr, "--", "--", "lake", "env", "lean", "X.lean"]
        self.assertEqual(suite._lean_run_wrapper_flags(double_sep), ("build", None, True))
        # A wrapped step never gets a shorter outer deadline than its wrapper can take:
        # the queue for a slot, then the step budget or (in `build` mode) the retry window.
        for profile in ("quick", "nightly"):
            for name, _cat, cmd, timeout_sec in suite.build_suite_steps(REPO_ROOT, profile):
                outer = suite._outer_timeout_sec(cmd, timeout_sec)
                if suite._is_lean_run_wrapped(cmd):
                    mode, _t, _lock = suite._lean_run_wrapper_flags(cmd)
                    if mode == "build":
                        expected = max(build_wait, timeout_sec) + max(retry, timeout_sec) + grace
                        self.assertGreaterEqual(
                            outer, timeout_sec + max(30, timeout_sec) + grace, f"{profile}/{name}"
                        )
                    else:
                        expected = file_wait + timeout_sec + grace
                    self.assertEqual(outer, expected, f"{profile}/{name}")
                    self.assertGreaterEqual(outer, timeout_sec + grace, f"{profile}/{name}")
                else:
                    self.assertEqual(outer, timeout_sec, f"{profile}/{name}")

    def _assert_pid_gone(self, pid: int, what: str) -> None:
        deadline = time.monotonic() + 10.0
        while time.monotonic() < deadline:
            try:
                state = Path(f"/proc/{pid}/stat").read_text().rsplit(")", 1)[1].split()[0]
            except (OSError, IndexError):
                return
            if state == "Z":
                return
            time.sleep(0.05)
        try:
            os.kill(pid, 9)
        except OSError:
            pass
        self.fail(f"{what} (pid {pid}) survived the step timeout")

    def test_run_step_timeout_terminates_whole_step_process_tree(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            pid_file = Path(tmp) / "pids"
            # A same-group grandchild (as `cargo` children are) must not outlive the step.
            script = (
                "import subprocess, sys, time\n"
                f"child = subprocess.Popen([sys.executable, '-c', 'import time; time.sleep(60)'])\n"
                f"open({str(pid_file)!r}, 'w').write(str(child.pid))\n"
                "print('partial-output-before-timeout', flush=True)\n"
                "time.sleep(60)\n"
            )
            t0 = time.monotonic()
            res = suite._run_step(
                name="hung_step",
                category="cat7_python_and_ci_tests",
                cmd=[sys.executable, "-c", script],
                cwd=REPO_ROOT,
                timeout_sec=3,  # ample slack for two interpreter start-ups under load
            )
            self.assertLess(time.monotonic() - t0, 30.0)
            self.assertEqual(res["status"], "TIMEOUT")
            self.assertEqual(res["exit_code"], 124)
            self.assertIn("partial-output-before-timeout", res["failure_excerpt"])
            self.assertIn("Timed out after", res["failure_excerpt"])
            self.assertTrue(pid_file.is_file(), "step was killed before it spawned its child")
            self._assert_pid_gone(int(pid_file.read_text()), "same-group grandchild")

    def _spawn_ready_step(self, script: str, ready: Path) -> subprocess.Popen[bytes]:
        """Start `script` exactly as `_run_step` does (own session) and wait until it
        creates `ready`, so signal tests never race interpreter start-up."""
        proc = subprocess.Popen(
            [sys.executable, "-c", script],
            stdin=subprocess.DEVNULL,
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
            start_new_session=True,
        )
        deadline = time.monotonic() + 60.0
        while not ready.exists():
            if proc.poll() is not None or time.monotonic() > deadline:
                suite._terminate_step(proc)
                self.fail(f"step never became ready (exit {proc.returncode})")
            time.sleep(0.02)
        return proc

    def test_terminate_step_lets_wrapper_reap_its_separate_session_scope(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            pid_file = Path(tmp) / "pids"
            ready = Path(tmp) / "ready"
            # Mirrors `anneal-lean-run`: the build runs in its own session and is only
            # reaped by the wrapper's SIGTERM handler, so a bare SIGKILL of the wrapper
            # (what `subprocess.run(timeout=...)` does) would orphan it.
            script = (
                "import os, signal, subprocess, sys, time\n"
                "child = subprocess.Popen([sys.executable, '-c', 'import time; time.sleep(60)'],\n"
                "                         start_new_session=True)\n"
                f"open({str(pid_file)!r}, 'w').write(str(child.pid))\n"
                "def on_term(signum, frame):\n"
                "    os.killpg(child.pid, signal.SIGKILL)\n"
                "    child.wait()\n"
                "    sys.exit(128 + signum)\n"
                "signal.signal(signal.SIGTERM, on_term)\n"
                f"open({str(ready)!r}, 'w').close()\n"
                "time.sleep(60)\n"
            )
            proc = self._spawn_ready_step(script, ready)
            suite._terminate_step(proc)
            self.assertEqual(proc.returncode, 128 + 15)  # exited through its handler
            self._assert_pid_gone(int(pid_file.read_text()), "separate-session build scope")

        # End to end: a hung wrapper is still reported as a TIMEOUT through `_run_step`.
        res = suite._run_step(
            name="hung_wrapper",
            category="cat2_correspondence_suites",
            cmd=[sys.executable, "-c", "import time; time.sleep(60)"],
            cwd=REPO_ROOT,
            timeout_sec=1,
        )
        self.assertEqual((res["status"], res["exit_code"]), ("TIMEOUT", 124))

    def test_run_step_reports_launch_failure_and_undecodable_output(self) -> None:
        missing = suite._run_step(
            name="missing_tool",
            category="cat7_python_and_ci_tests",
            cmd=[str(REPO_ROOT / "scripts" / "no-such-tool-ep2")],
            cwd=REPO_ROOT,
            timeout_sec=5,
        )
        self.assertEqual(missing["status"], "FAIL")
        self.assertEqual(missing["exit_code"], 127)
        garbage = suite._run_step(
            name="binary_output",
            category="cat7_python_and_ci_tests",
            cmd=[sys.executable, "-c", "import sys; sys.stdout.buffer.write(b'\\xff\\xfe bad'); sys.exit(3)"],
            cwd=REPO_ROOT,
            timeout_sec=10,
        )
        self.assertEqual(garbage["status"], "FAIL")
        self.assertEqual(garbage["exit_code"], 3)
        self.assertIn("bad", garbage["failure_excerpt"])

    def test_lean_header_imports_parses_module_system_and_comments(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            f = Path(tmp) / "T.lean"
            f.write_text(
                "\ufeff/- header /- nested -/ comment -/\n"
                "module\n"
                "-- line comment import Fake.Module\n"
                "public import Anneal.ByteCodec\n"
                "meta import all Anneal.Mir.Cast  -- trailing\n"
                "import «Anneal».BitValidity import Foo.«a b».c\n"
                "import Bar.«x--y».«z/-w» -- comment after guillemets\n"
                "\n"
                "theorem t : True := by\n"
                "  trivial\n"
                "import Not.A.Header.Import\n",
                encoding="utf-8",
            )
            self.assertEqual(
                suite._lean_header_imports(f),
                [
                    "Anneal.ByteCodec",
                    "Anneal.Mir.Cast",
                    "Anneal.BitValidity",
                    "Foo.a b.c",
                    "Bar.x--y.z/-w",
                ],
            )
            self.assertIsNone(suite._lean_header_imports(Path(tmp) / "missing.lean"))

    def test_discover_correspondence_divergences_ignores_commented_out_witness(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            target = root / UNTESTED_VARIANT_TEST
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_text(
                "-- theorem tailCall_leanMiri_nounwind_callee : True := trivial\n"
                "/- theorem opaqueCast_trusted_root_dispatch_divergence : True := trivial -/\n"
                "theorem tailCall_leanMiri_root_stop_diverges : True := trivial\n",
                encoding="utf-8",
            )
            divs = suite.discover_correspondence_divergences(root)
            open_by_id = {d["id"]: d for d in divs["actionable_anneal_bugs"]}
            # Commented-out witnesses are not live, and without their pinned `*_simulation`
            # replacements the entries fail closed as `resolution_missing` (not `resolved`).
            for div_id in ("DIV-LM-TAILCALL-NOUNWIND-UNWIND", "DIV-TR-OPAQUECAST-ROOT-DISPATCH"):
                self.assertFalse(open_by_id[div_id]["live_in_source"])
                self.assertEqual(open_by_id[div_id]["status"], "resolution_missing")
            self.assertEqual(divs["resolved_correspondence_divergences"], [])
            by_id = {d["id"]: d for d in divs["intentional_modeling_choices"]}
            self.assertTrue(by_id["MODEL-LM-TAILCALL-MODULAR-ROOT"]["live_in_source"])
            self.assertFalse(by_id["MODEL-LM-TAILCALL-DIRECT-ARITY-STEP"]["live_in_source"])

    def test_terminate_step_grants_grace_window_to_same_group_descendants(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            marker = Path(tmp) / "cleaned"
            child_ready = Path(tmp) / "child_ready"
            ready = Path(tmp) / "ready"
            # The leader exits immediately on SIGTERM while its same-group child takes
            # 0.25 s to write `marker` before exiting cleanly: escalating to SIGKILL as
            # soon as the leader is gone would kill the child mid-cleanup.
            child_code = (
                "import pathlib, signal, sys, time\n"
                "def handler(s, f):\n"
                "    time.sleep(0.25)\n"
                f"    pathlib.Path({str(marker)!r}).write_text('grace-ok')\n"
                "    sys.exit(0)\n"
                "signal.signal(signal.SIGTERM, handler)\n"
                f"open({str(child_ready)!r}, 'w').close()\n"
                "time.sleep(60)\n"
            )
            leader_code = (
                "import os, signal, subprocess, sys, time\n"
                "signal.signal(signal.SIGTERM, lambda s, f: sys.exit(0))\n"
                f"subprocess.Popen([sys.executable, '-c', {child_code!r}])\n"
                f"while not os.path.exists({str(child_ready)!r}):\n"
                "    time.sleep(0.01)\n"
                f"open({str(ready)!r}, 'w').close()\n"
                "time.sleep(60)\n"
            )
            proc = self._spawn_ready_step(leader_code, ready)
            suite._terminate_step(proc)
            self.assertEqual(proc.returncode, 0)
            self.assertTrue(marker.is_file(), "same-group child was SIGKILLed before grace window")
            self.assertEqual(marker.read_text(), "grace-ok")

    def test_flip_direction_guard_hardens_parser_tautology_pin_and_transition_bypasses(self) -> None:
        div_id = "DIV-LM-ENUM-SET-DISCR-UNINIT"
        sym = "step_setDiscriminant_uninit_simulation"
        lm23 = "lean-miri/lean/LeanMiriSpec/Correspondence/SimLM2_3.lean"
        pin_div = "DIV-MR-CALL-TARGET-LOCAL"
        pin_sym = "callerRefMutSilentWrongLocal_simulation"
        stmt = SYNTH_STMT

        # 1. Guillemet-escaped / `_root_`-qualified logicals, tautological self-implications,
        #    contradictory hypotheses, prefix connectives, vacuous existentials, literal
        #    contradictions, nested holes, tactic-typed binders, `where` modifier/attribute
        #    helpers, `in`-scoped tactic commands, and `mutual` sibling holes are all rejected.
        bypass_theorems: list[tuple[str, set[str]]] = [
            (": «True» := trivial", {"vacuous_statement", "closed_trivial_statement"}),
            (": _root_.True := trivial", {"vacuous_statement", "closed_trivial_statement"}),
            (f": «False» → {stmt} := fun h => h.elim", {"vacuous_statement"}),
            (f": _root_.False → {stmt} := fun h => h.elim", {"vacuous_statement"}),
            (f": {stmt} := «sorryAx» _ false", {"sorry_or_admit"}),
            (f": {stmt} := by native_decide", {"sorry_or_admit"}),
            # Circular / tautological hypotheses and excluded middle.
            (f"(h : {stmt}) : {stmt} := h", {"vacuous_statement"}),
            (f": {stmt} → {stmt} := id", {"vacuous_statement"}),
            (
                ": ∀ x, annealOutcome x = miriOutcome x → stepMirFn x = .ub → "
                "annealOutcome x = miriOutcome x := fun _ h _ => h",
                {"vacuous_statement"},
            ),
            (
                f": ({stmt} ∧ stepMirFn fooProg = .ub) → {stmt} := And.left",
                {"vacuous_statement"},
            ),
            (
                f"(h : {stmt}) : {stmt} ∨ stepMirFn fooProg = .ub := Or.inl h",
                {"vacuous_statement"},
            ),
            (
                ": annealOutcome fooProg = miriOutcome fooProg ∨ "
                "annealOutcome fooProg ≠ miriOutcome fooProg := Classical.em _",
                {"vacuous_statement"},
            ),
            (
                f"(h1 : stepMirFn fooProg = .ub) (h2 : stepMirFn fooProg ≠ .ub) : {stmt} := "
                "absurd h1 h2",
                {"vacuous_statement"},
            ),
            (
                f"(h : stepMirFn fooProg = .ub ∧ ¬(stepMirFn fooProg = .ub)) : {stmt} := "
                "absurd h.1 h.2",
                {"vacuous_statement"},
            ),
            # Prefix logicals, uninhabited/trivial types, and distinct literal contradictions.
            (": Eq (annealOutcome fooProg) (annealOutcome fooProg) := rfl", {"vacuous_statement"}),
            (": @Eq Nat (annealOutcome fooProg) (annealOutcome fooProg) := rfl", {"vacuous_statement"}),
            (f": Iff ({stmt}) ({stmt}) := Iff.rfl", {"vacuous_statement"}),
            (f": Or True ({stmt}) := Or.inl trivial", {"vacuous_statement"}),
            (f": And False ({stmt}) → {stmt} := fun h => h.1.elim", {"vacuous_statement"}),
            (f"(h : Fin 0) : {stmt} := h.elim0", {"vacuous_statement"}),
            (f"(h : ULift False) : {stmt} := h.down.elim", {"vacuous_statement"}),
            (": PLift True := ⟨trivial⟩", {"vacuous_statement", "closed_trivial_statement"}),
            (f": (0 = 1) → {stmt} := nofun", {"vacuous_statement"}),
            (f": (true = false) → {stmt} := nofun", {"vacuous_statement"}),
            (f": (Bool.true = Bool.false) → {stmt} := nofun", {"vacuous_statement"}),
            (": 0 ≠ 1 := by decide", {"vacuous_statement", "closed_trivial_statement"}),
            # Auto-param default on a vacuous binder.
            (f"(h : False := nomatch) : {stmt} := h.elim", {"vacuous_statement"}),
            # Vacuous existentials.
            (": ∃ (_ : CapturedMir), True := ⟨fooProg, trivial⟩", {"vacuous_statement"}),
            (": ∃ out, annealOutcome fooProg = out := ⟨_, rfl⟩", {"vacuous_statement"}),
            (": ∃ (out : Value), out = annealOutcome fooProg := ⟨_, rfl⟩", {"vacuous_statement"}),
            # Nested wildcard holes and tactic-synthesized binder types.
            ("(_ : CapturedMir) : id _ := trivial", {"wildcard_statement"}),
            (": annealOutcome fooProg = _ := rfl", {"wildcard_statement"}),
            (f"(h : _) : {stmt} := h", {"wildcard_statement"}),
            (f"(h : by exact False) : {stmt} := h.elim", {"self_typed_statement"}),
            (f"(h : type_of% fooLemma) : {stmt} := h", {"self_typed_statement"}),
            # `where` helpers with attributes/modifiers and `in`-scoped tactic commands.
            (
                f": {stmt} := aux\nwhere\n  @[simp] aux : {stmt} := sorry\n",
                {"sorry_or_admit"},
            ),
            (
                f": {stmt} := aux\nwhere\n  private aux : {stmt} := sorry\n",
                {"sorry_or_admit"},
            ),
            (
                f": {stmt} := aux\nwhere\n  noncomputable aux : {stmt} := sorry\n",
                {"sorry_or_admit"},
            ),
            (
                f"(h : CapturedMir) : {stmt} := by\n  omit h in\n  sorry\n",
                {"sorry_or_admit"},
            ),
            (
                f": {stmt} := by\n  attribute [local simp] fooLemma in\n  sorry\n",
                {"sorry_or_admit"},
            ),
        ]
        for tail, expected in bypass_theorems:
            with self.subTest(theorem_tail=tail), tempfile.TemporaryDirectory() as tmp:
                root = Path(tmp)
                self._write_flip_tree(root, {div_id: (None, tail, stmt)})
                rec = self._flip_status(root, div_id)
                self.assertEqual(rec["status"], "resolution_invalid")
                self.assertEqual(set(rec["resolution_problems"]), expected)

        # Positive controls: auto-param tactic defaults, `match` wildcard arms, dependent
        # proof-term arguments `(by ...)`, non-trivial existentials, and `⦃...⦄` binders pass.
        valid_controls = [
            f"⦃body : CapturedMir⦄ (_hlive : body ≠ deadBody := by rintro ⟨⟩) : "
            f"annealOutcome body = miriOutcome body := rfl",
            f"(k : TyKind) (hk : sizeOf k = match k with | .bool => 1 | _ => 4) : {stmt} := rfl",
            f"(idx : Nat) (hlt : idx < 4) : getElem fooArr idx (by exact hlt) = miriElem idx := rfl",
            ": ∃ s', stepMirFn fooProg s = .step s' ∧ mirStateRel s' m' := ⟨s, rfl, hrel⟩",
        ]
        for tail in valid_controls:
            with self.subTest(valid_tail=tail), tempfile.TemporaryDirectory() as tmp:
                root = Path(tmp)
                self._write_flip_tree(root, {div_id: (None, tail, stmt)})
                rec = self._flip_status(root, div_id)
                self.assertEqual((rec["status"], rec["resolution_problems"]), ("resolved", []))

        # `mutual ... end` sibling `sorry` invalidates a resolution theorem in the same block,
        # while a hole-free `mutual` block resolves.
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            self._write_flip_tree(root, {div_id: (None, None, stmt)})
            target = root / lm23
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_text(
                f"mutual\n"
                f"  theorem {sym} : {stmt} := mutualHelper\n"
                f"  theorem mutualHelper : {stmt} := sorry\n"
                f"end\n",
                encoding="utf-8",
            )
            rec = self._flip_status(root, div_id)
            self.assertEqual(rec["status"], "resolution_invalid")
            self.assertEqual(rec["resolution_problems"], ["sorry_or_admit"])
            target.write_text(
                f"mutual\n"
                f"  theorem {sym} : {stmt} := mutualHelper\n"
                f"  theorem mutualHelper : {stmt} := rfl\n"
                f"end\n",
                encoding="utf-8",
            )
            self.assertEqual(self._flip_status(root, div_id)["status"], "resolved")

        # 2. Statement-pin RHS operators (`|>`, `▸`, `<|`, `$`), binder holes (`(h : _)`),
        #    binder self-references, `⦃h : False⦄` strict-implicit binders, and `_root_.True`
        #    are all rejected; a legitimate `⦃...⦄` statement pin is accepted.
        bypass_pins: list[tuple[str, list[str]]] = [
            (f"example : {stmt} := {{sym}} |> ignoreFirst realProof", []),
            (f"example : {stmt} := {{sym}} ▸ realProof", []),
            (f"example : {stmt} := {{sym}} <| argA", []),
            (f"example : {stmt} := {{sym}} $ argA", []),
            ("example : «True» := {sym}", []),
            ("example : _root_.True := {sym}", ["pin_closed_trivial_statement", "pin_vacuous_statement"]),
            (f"example (h : _) : {stmt} := {{sym}} h", ["self_typed_or_hole_pin"]),
            (f"example [_] : {stmt} := {{sym}}", ["self_typed_or_hole_pin"]),
            (f"example (h : type_of% {{sym}}) : {stmt} := {{sym}} h", ["self_typed_or_hole_pin"]),
            (f"example (h : by exact False) : {stmt} := {{sym}} h", ["self_typed_or_hole_pin"]),
            (f"example ⦃h : False⦄ : {stmt} := {{sym}} h", ["pin_vacuous_statement"]),
            (f"example (h : {stmt}) : {stmt} := {{sym}} h", ["pin_vacuous_statement"]),
        ]
        for pin_text, expected_reasons in bypass_pins:
            with self.subTest(pin=pin_text), tempfile.TemporaryDirectory() as tmp:
                root = Path(tmp)
                self._write_flip_tree(root, {pin_div: (None, f": {stmt} := rfl", None)})
                audit_file = root / suite.AUTHORITY_AUDIT_FILES["MiniRustSpec"]
                with audit_file.open("a", encoding="utf-8") as fh:
                    fh.write(pin_text.replace("{sym}", pin_sym) + "\n")
                rec = self._flip_status(root, pin_div)
                self.assertEqual(rec["status"], "resolution_unpinned")
                self.assertEqual(rec["resolution_pin_problems"], expected_reasons)
                with audit_file.open("a", encoding="utf-8") as fh:
                    fh.write(
                        f"example ⦃body : CapturedMir⦄ : annealOutcome body = miriOutcome body :=\n"
                        f"  @{pin_sym}\n"
                    )
                self.assertEqual(self._flip_status(root, pin_div)["status"], "resolved")

        # 3. Baseline-to-current transition audit catches cosmetically rewritten witness
        #    statements (`polarity_not_flipped`), cosmetically rewritten pre-existing
        #    resolutions (`resolution_predates_flip`), non-`open` incomplete flips,
        #    `native_decide` / `implemented_by` / `«sorryAx»` holes, witness-file holes,
        #    and `resolved -> resolved` statement rewrites backed by a new proof hole.
        d6 = "DIV-LM-D6-OFFSET-DISABLED-TAG"
        sim31 = "lean-miri/lean/LeanMiriSpec/Correspondence/SimLM3_1.lean"
        with tempfile.TemporaryDirectory() as tmp:
            base_root, cur_root = Path(tmp) / "base", Path(tmp) / "cur"
            self._write_flip_tree(
                base_root,
                {
                    # Witness uses binder `(s : MachineState)` and `≠`.
                    div_id: ("(s : MachineState) : annealStep s ≠ miriStep s := by decide", None, None),
                    # Pre-existing simulation uses `(s : MachineState)`.
                    "DIV-MR-TB-UNSAFECELL-PROTECTED-IM": (
                        f": {SYNTH_DIVERGENCE_STMT} := rfl",
                        "(s : MachineState) : annealOutcome s = miriOutcome s := rfl",
                        "∀ s : MachineState, annealOutcome s = miriOutcome s",
                    ),
                    # Baseline is `resolution_missing` (neither witness nor resolution).
                    "DIV-LM-RAW-OVERWRITE-CHAR-COPY": (None, None, None),
                    # Proper flip in `SimLM3_1` whose witness file `WitLM3_1` gains a hole.
                    d6: (f": {SYNTH_DIVERGENCE_STMT} := rfl", None, None),
                },
            )
            self._write_flip_tree(
                cur_root,
                {
                    # Cosmetically alpha-renamed + `∀`-wrapped + `True ∧`-padded witness!
                    div_id: (
                        None,
                        ": ∀ {st : MachineState}, True ∧ (id (annealStep st ≠ miriStep st)) := by decide",
                        "∀ {st : MachineState}, annealStep st ≠ miriStep st",
                    ),
                    # Cosmetically `∀`-wrapped pre-existing simulation!
                    "DIV-MR-TB-UNSAFECELL-PROTECTED-IM": (
                        None,
                        ": ∀ (st : MachineState), (annealOutcome st = miriOutcome st) := rfl",
                        "∀ (st : MachineState), annealOutcome st = miriOutcome st",
                    ),
                    # `resolution_missing -> resolution_unpinned` (non-`open` incomplete flip).
                    "DIV-LM-RAW-OVERWRITE-CHAR-COPY": (None, f": {stmt} := rfl", None),
                    # Proper flip on `SimLM3_1`, but `WitLM3_1` gains `«sorryAx»` and
                    # an already-resolved entry (`DIV-MR-CALL-TARGET-LOCAL`) rewrites its
                    # statement with a new `axiom` in its module.
                    d6: (None, f": {stmt} := rfl", stmt),
                    pin_div: (
                        None,
                        ": annealOutcome barProg = miriOutcome barProg := cheatAx",
                        "annealOutcome barProg = miriOutcome barProg",
                    ),
                },
            )
            with (cur_root / sim31).open("a", encoding="utf-8") as fh:
                fh.write("def hiddenHole : False := «sorryAx» False false\n")
            mr_wit = cur_root / "minirust/lean/MiniRustSpec/Correspondence/ProvenanceWitness.lean"
            with mr_wit.open("a", encoding="utf-8") as fh:
                fh.write("axiom cheatAx : annealOutcome barProg = miriOutcome barProg\n")
            audit = suite.audit_flip_direction_transitions(base_root, cur_root)
            self.assertFalse(audit["passed"])
            self.assertEqual(
                sorted((v["id"], v["reason"]) for v in audit["violations"]),
                sorted(
                    [
                        (div_id, "polarity_not_flipped"),
                        ("DIV-MR-TB-UNSAFECELL-PROTECTED-IM", "resolution_predates_flip"),
                        ("DIV-LM-RAW-OVERWRITE-CHAR-COPY", "incomplete_flip"),
                        (d6, "proof_hole_introduced"),
                        (pin_div, "proof_hole_introduced"),
                    ]
                ),
            )

    def test_flip_direction_guard_precedence_scoping_definitions_and_unnamed_holes(self) -> None:
        div_id = "DIV-LM-ENUM-SET-DISCR-UNINIT"
        sym = "step_setDiscriminant_uninit_simulation"
        lm23 = "lean-miri/lean/LeanMiriSpec/Correspondence/SimLM2_3.lean"
        stmt = SYNTH_STMT

        def status_of_tail(tail: str) -> tuple[object, object]:
            with tempfile.TemporaryDirectory() as tmp:
                root = Path(tmp)
                self._write_flip_tree(root, {div_id: (None, tail, stmt)})
                rec = self._flip_status(root, div_id)
                return rec["status"], rec["resolution_problems"]

        def status_of_module(text: str) -> tuple[object, object]:
            with tempfile.TemporaryDirectory() as tmp:
                root = Path(tmp)
                self._write_flip_tree(root, {div_id: (None, None, stmt)})
                (root / lm23).parent.mkdir(parents=True, exist_ok=True)
                (root / lm23).write_text(text, encoding="utf-8")
                rec = self._flip_status(root, div_id)
                return rec["status"], rec["resolution_problems"]

        # 1. Meaningful statements that the statement analysis must not call vacuous:
        #    `=` binds tighter than `∧` / `→` (no one-point `∃` rule for `v = e ∧ Q`),
        #    `01` is `1`, a `∀` / Pi binder shadows a hypothesis about the outer name,
        #    `@Eq (Fin 2) 0 2` wraps around, `²` is no numeral, and a quoted name
        #    literal (``` ``sorryAx ```) names a constant without using it.
        meaningful_tails = [
            ": ∃ v, v = annealOutcome fooProg ∧ stepOk fooProg := ⟨_, rfl, hok⟩",
            f": {stmt} → stepOk fooProg := fun _ => hok",
            f"(h : annealOutcome fooProg = 01) : {stmt} := rfl",
            "(h : annealOutcome x = miriOutcome x) : ∀ x, annealOutcome x = miriOutcome x := fun _ => rfl",
            "(h : stepOk x) : (x : CapturedMir) → stepOk x := fun _ => hok",
            f": (@Eq (Fin 2) 0 2) → {stmt} := fun _ => rfl",
            f"(h : annealOutcome fooProg = ²) : {stmt} := rfl",
            f": {stmt} := by\n  have := isForbidden ``sorryAx\n  rfl\n",
        ]
        for tail in meaningful_tails:
            with self.subTest(meaningful=tail):
                self.assertEqual(status_of_tail(tail), ("resolved", []))
        # ... while equal literals, a quoted name used as a keyword to cut the proof
        # short, and a kernel-check bypass inside the proof are still rejected.
        rejected_tails: list[tuple[str, list[str]]] = [
            (f": (1 = 01) ∨ {stmt} := Or.inl rfl", ["vacuous_statement"]),
            (f": {stmt} := by\n  first\n  | exact `example\n  | sorry\n", ["sorry_or_admit"]),
            (
                f": {stmt} := by\n  set_option debug.skipKernelTC true in\n  exact cheat\n",
                ["sorry_or_admit"],
            ),
        ]
        for tail, problems in rejected_tails:
            with self.subTest(rejected=tail):
                self.assertEqual(status_of_tail(tail), ("resolution_invalid", problems))

        # 2. Module context: section `variable` hypotheses (scoped by `in`, `section`, and
        #    `namespace`), this module's trivially true / false definitions, and holes
        #    of earlier declarations that the proof uses by name or unnamed.
        vacuous = ("resolution_invalid", ["vacuous_statement"])
        closed_vacuous = ("resolution_invalid", ["closed_trivial_statement", "vacuous_statement"])
        hole_dep = ("resolution_invalid", ["hole_dependency"])
        resolved = ("resolved", [])
        thm = f"theorem {sym}"  # the resolution theorem's head
        res = f"{thm} : {stmt}"  # ... with a meaningful statement
        sim_def = "def Simulates (p : CapturedMir) : Prop"
        module_cases: list[tuple[str, str, tuple[object, object]]] = [
            ("variable", f"variable (hfalse : False)\ninclude hfalse\n{res} := hfalse.elim\n", vacuous),
            ("variable_in", f"variable (h : {stmt}) in\n{res} := h\n", vacuous),
            ("section_variable", f"section\nvariable (hfalse : False)\nend\n{res} := rfl\n", resolved),
            ("namespace_variable", f"namespace Foo\nvariable (hfalse : False)\nend Foo\n{res} := rfl\n", resolved),
            (
                "variable_in_other_command",
                f"variable (hfalse : False) in\ninstance : Inhabited Nat := ⟨0⟩\n{res} := rfl\n",
                resolved,
            ),
            (
                "benign_variable",
                f"variable {{body : CapturedMir}}\n{thm} : annealOutcome body = miriOutcome body := rfl\n",
                resolved,
            ),
            ("def_true", f"{sim_def} := True\n{thm} : Simulates fooProg := trivial\n", closed_vacuous),
            ("def_untyped", f"def Simulates := True\n{thm} : Simulates := trivial\n", closed_vacuous),
            (
                "def_fun",
                f"def Simulates : CapturedMir → Prop := fun _ => True\n{thm} : Simulates fooProg := trivial\n",
                closed_vacuous,
            ),
            (
                "def_alternatives",
                f"def Simulates : CapturedMir → Prop\n  | _ => True\n{thm} : Simulates fooProg := trivial\n",
                closed_vacuous,
            ),
            (
                "def_match",
                f"{sim_def} := match p with\n  | _ => True\n{thm} : Simulates fooProg := trivial\n",
                closed_vacuous,
            ),
            (
                "def_reflexive",
                f"{sim_def} := annealOutcome p = annealOutcome p\n{thm} : ∀ p, Simulates p := fun _ => rfl\n",
                vacuous,
            ),
            ("def_false_hypothesis", f"def Broken : Prop := False\n{thm} (h : Broken) : {stmt} := h.elim\n", vacuous),
            (
                "def_chained",
                f"def A : Prop := True\ndef B : Prop := A ∧ A\n{thm} : B := ⟨trivial, trivial⟩\n",
                closed_vacuous,
            ),
            (
                "def_qualified",
                f"def Foo.Simulates (p : CapturedMir) : Prop := True\n{thm} : Foo.Simulates fooProg := trivial\n",
                closed_vacuous,
            ),
            (
                "def_meaningful",
                f"{sim_def} := annealOutcome p = miriOutcome p\n{thm} : Simulates fooProg := rfl\n",
                resolved,
            ),
            (
                "def_closed_body",
                f"{sim_def} := 0 < 1\n{thm} : Simulates fooProg := by decide\n",
                ("resolution_invalid", ["closed_trivial_statement"]),
            ),
            (
                "def_closed_meaningful_body",
                f"{sim_def} := {stmt}\n{thm} : ∀ p, Simulates p := fun _ => rfl\n",
                resolved,
            ),
            ("non_prop_constant", f"def n : Nat := 5\n{thm} : annealOutcome fooProg = n := rfl\n", resolved),
            (
                "set_option_in_ends_previous_body",
                f"{res} := rfl\nset_option debug.skipKernelTC true in\ntheorem later : {stmt} := cheat\n",
                resolved,
            ),
            ("named_sorry", f"theorem helper : {stmt} := sorry\n{res} := helper\n", hole_dep),
            ("named_axiom", f"axiom cheat : {stmt}\n{res} := cheat\n", hole_dep),
            (
                "transitive",
                f"theorem h1 : {stmt} := sorry\ntheorem h2 : {stmt} := h1\n{res} := h2\n",
                hole_dep,
            ),
            (
                "mutual_transitive",
                f"mutual\n  theorem mA : {stmt} := mB\n  theorem mB : {stmt} := sorry\nend\n{res} := mA\n",
                hole_dep,
            ),
            (
                "simp_attribute",
                f"open Foo\n@[simp] theorem cheat : {stmt} := sorry\n{res} := by simp\n",
                hole_dep,
            ),
            (
                "attribute_command",
                f"theorem cheat : {stmt} := sorry\nattribute [simp] cheat\n{res} := by simp\n",
                hole_dep,
            ),
            (
                "instance_using_hole",
                f"theorem cheat : {stmt} := sorry\ninstance : Fact ({stmt}) := ⟨cheat⟩\n{res} := Fact.out\n",
                hole_dep,
            ),
            ("notation", f'notation "cheat" => sorry\n{res} := cheat\n', hole_dep),
            ("skip_kernel_tc", f"set_option debug.skipKernelTC true\n{res} := cheat\n", hole_dep),
            ("lemma_search", f"theorem unused : {stmt} := sorry\n{res} := by exact?\n", hole_dep),
            ("lemma_search_clean", f"theorem okLemma : {stmt} := rfl\n{res} := by exact?\n", resolved),
            ("unused_unattributed_hole", f"theorem unused : {stmt} := sorry\n{res} := rfl\n", resolved),
            ("clean_simp_lemma", f"@[simp] theorem okSimp : {stmt} := rfl\n{res} := by simp\n", resolved),
            (
                "audit_elab_name_literal",
                f'elab "#audit" : command => do\n  if n == ``sorryAx then throwError "no"\n{res} := rfl\n',
                resolved,
            ),
        ]
        for label, text, expected in module_cases:
            with self.subTest(module=label):
                self.assertEqual(status_of_module(text), expected)

        # 3. Statement pins see the audit module's `variable` hypotheses and definitions.
        pin_div = "DIV-MR-CALL-TARGET-LOCAL"
        pin_sym = "callerRefMutSilentWrongLocal_simulation"
        for prelude, reasons in (
            ("variable (hfalse : False)\n", ["pin_vacuous_statement"]),
            ("def Locked : Prop := True\n", ["pin_closed_trivial_statement", "pin_vacuous_statement"]),
        ):
            with self.subTest(pin_prelude=prelude), tempfile.TemporaryDirectory() as tmp:
                root = Path(tmp)
                self._write_flip_tree(root, {pin_div: (None, f": {stmt} := rfl", None)})
                audit_file = root / suite.AUTHORITY_AUDIT_FILES["MiniRustSpec"]
                pin_type = stmt if prelude.startswith("variable") else "Locked"
                with audit_file.open("a", encoding="utf-8") as fh:
                    fh.write(f"{prelude}example : {pin_type} := {pin_sym}\n")
                rec = self._flip_status(root, pin_div)
                self.assertEqual(
                    (rec["status"], rec["resolution_pin_problems"]), ("resolution_unpinned", reasons)
                )

        # 4. A move back to `open` (the witness is restored) is no incomplete flip.
        raw = "DIV-LM-RAW-OVERWRITE-CHAR-COPY"
        with tempfile.TemporaryDirectory() as tmp:
            base_root, cur_root = Path(tmp) / "base", Path(tmp) / "cur"
            self._write_flip_tree(
                base_root, {raw: (None, None, None), div_id: (None, ": True := trivial", stmt)}
            )
            self._write_flip_tree(
                cur_root,
                {
                    raw: (f": {SYNTH_DIVERGENCE_STMT} := rfl", None, None),
                    div_id: (f": {SYNTH_DIVERGENCE_STMT} := rfl", None, None),
                },
            )
            self.assertEqual(self._flip_status(base_root, raw)["status"], "resolution_missing")
            self.assertEqual(self._flip_status(base_root, div_id)["status"], "resolution_invalid")
            audit = suite.audit_flip_direction_transitions(base_root, cur_root)
            self.assertTrue(audit["passed"], audit["violations"])
            self.assertEqual(
                sorted((t["id"], t["from"], t["to"]) for t in audit["transitions"]),
                [(div_id, "resolution_invalid", "open"), (raw, "resolution_missing", "open")],
            )

    def test_materialize_flip_baseline_tree_from_a_repo_subdirectory(self) -> None:
        git = shutil.which("git")
        if git is None:
            self.skipTest("git is not installed")
        with tempfile.TemporaryDirectory() as tmp:
            top = Path(tmp) / "top"
            repo = top / "anneal"
            repo.mkdir(parents=True)

            def run_git(*args: str) -> None:
                subprocess.run(
                    [
                        git,
                        "-c",
                        "user.name=Flip Audit Test",
                        "-c",
                        "user.email=flip-audit@example.com",
                        "-c",
                        "commit.gpgsign=false",
                        *args,
                    ],
                    cwd=top,
                    check=True,
                    capture_output=True,
                )

            run_git("init", "-q")
            self._write_flip_tree(repo)
            run_git("add", "-A")
            run_git("commit", "-q", "-m", "baseline")
            dest = Path(tmp) / "baseline_tree"
            suite.materialize_flip_baseline_tree(repo, "HEAD", dest)
            for rel in suite.flip_direction_tracked_files():
                if (repo / rel).is_file():
                    self.assertTrue((dest / rel).is_file(), rel)
                    self.assertEqual((dest / rel).read_bytes(), (repo / rel).read_bytes(), rel)
            self.assertTrue(suite.audit_flip_direction_transitions(dest, repo)["passed"])

    def test_flip_direction_guard_operators_scopes_defs_pins_and_cross_file_imports(self) -> None:
        div_id = "DIV-LM-ENUM-SET-DISCR-UNINIT"
        sym = "step_setDiscriminant_uninit_simulation"
        lm23 = "lean-miri/lean/LeanMiriSpec/Correspondence/SimLM2_3.lean"
        pin_div = "DIV-MR-CALL-TARGET-LOCAL"
        pin_sym = "callerRefMutSilentWrongLocal_simulation"
        stmt = SYNTH_STMT

        def status_of_tail(tail: str) -> tuple[object, object]:
            with tempfile.TemporaryDirectory() as tmp:
                root = Path(tmp)
                self._write_flip_tree(root, {div_id: (None, tail, stmt)})
                rec = self._flip_status(root, div_id)
                return rec["status"], rec["resolution_problems"]

        def status_of_module(text: str, extra_files: dict[str, str] | None = None) -> tuple[object, object]:
            with tempfile.TemporaryDirectory() as tmp:
                root = Path(tmp)
                self._write_flip_tree(root, {div_id: (None, None, stmt)})
                for rel, content in (extra_files or {}).items():
                    p = root / rel
                    p.parent.mkdir(parents=True, exist_ok=True)
                    p.write_text(content, encoding="utf-8")
                (root / lm23).parent.mkdir(parents=True, exist_ok=True)
                (root / lm23).write_text(text, encoding="utf-8")
                rec = self._flip_status(root, div_id)
                return rec["status"], rec["resolution_problems"]

        # 1. Arithmetic, comparison, list, and let-bound expressions that are genuinely
        #    distinct on both sides must resolve cleanly, and flipping `<` to `≥` across
        #    checkouts must not be misclassified as `polarity_not_flipped`.
        for valid_tail in (
            ": annealOutcome fooProg + delta = annealOutcome fooProg - delta := h",
            ": annealOutcome fooProg < miriOutcome fooProg → annealOutcome fooProg > miriOutcome fooProg := h",
            ": [annealOutcome fooProg] ++ xs = miriOutcome fooProg :: xs := h",
            ": let s := annealOutcome fooProg; s = miriOutcome fooProg := rfl",
        ):
            with self.subTest(valid_operator_tail=valid_tail):
                self.assertEqual(status_of_tail(valid_tail), ("resolved", []))

        with tempfile.TemporaryDirectory() as tmp:
            base_root, cur_root = Path(tmp) / "base", Path(tmp) / "cur"
            self._write_flip_tree(
                base_root,
                {div_id: (": annealOutcome fooProg < miriOutcome fooProg := by decide", None, None)},
            )
            self._write_flip_tree(
                cur_root,
                {
                    div_id: (
                        None,
                        ": annealOutcome fooProg >= miriOutcome fooProg := by decide",
                        "annealOutcome fooProg ≥ miriOutcome fooProg",
                    )
                },
            )
            audit_op = suite.audit_flip_direction_transitions(base_root, cur_root)
            self.assertTrue(audit_op["passed"], audit_op["violations"])

        # 2. Closed-trivial bypasses (unused section `variable`, unused theorem/forall/arrow
        #    binders, pure `Nat` arithmetic, quoted name literals, dead `let`, and vacuous
        #    domain padding conjoined/disjoined with `0 < 1`) and scope-token vacuity (`let`,
        #    `have`, `show`, `if`, `match`) are rejected.
        closed_only = ("resolution_invalid", ["closed_trivial_statement"])
        vacuous = ("resolution_invalid", ["vacuous_statement"])
        closed_vacuous = ("resolution_invalid", ["closed_trivial_statement", "vacuous_statement"])
        hole_dep = ("resolution_invalid", ["hole_dependency"])
        resolved = ("resolved", [])

        tail_cases: list[tuple[str, tuple[object, object]]] = [
            ("(p : CapturedMir) : 0 < 1 := by decide", closed_only),
            (": ∀ (p : CapturedMir), 0 < 1 := fun _ => by decide", closed_only),
            (": CapturedMir → 0 < 1 := fun _ => by decide", closed_only),
            ("(n : Nat) : n + 0 = n := by omega", closed_only),
            (": (`foo ≠ `bar) := by decide", closed_only),
            (": let _ := fooProg; 0 < 1 := by decide", closed_only),
            (": (0 < 1) ∧ (annealOutcome fooProg = annealOutcome fooProg) := ⟨by decide, rfl⟩", closed_only),
            (
                ": ((annealOutcome fooProg = miriOutcome fooProg) ∧ False) ∨ (0 < 1) := Or.inr (by decide)",
                closed_only,
            ),
            (": let _ := fooProg; True := trivial", vacuous),
            (": let a := annealOutcome fooProg; a = annealOutcome fooProg := rfl", vacuous),
            (": have _ := fooProg; True := trivial", vacuous),
            (": show Prop from (annealOutcome fooProg = annealOutcome fooProg) := rfl", vacuous),
            (": if stepOk fooProg then True else True := by split <;> trivial", vacuous),
            (": if stepOk fooProg then stepOk fooProg else ¬ stepOk fooProg := by split <;> assumption", vacuous),
            (": match fooProg with | _ => annealOutcome fooProg = annealOutcome fooProg := rfl", vacuous),
        ]
        for tail, expected in tail_cases:
            with self.subTest(tail_case=tail):
                self.assertEqual(status_of_tail(tail), expected)

        # 3. Module-level `variable` closed-trivial bypass, definitional vacuity (`by exact`,
        #    `by trivial`, tautology under binder hyps, untyped closed `def`, `: ∀ _, Prop`,
        #    empty `structure ... : Prop`, 0-constructor `inductive`, 0-arg `Or A P`,
        #    `(Simulates) fooProg`, `fooProg |> Simulates`, multi-arm `∀` match), and
        #    metaprogram `mkConst ``sorryAx` holes.
        thm = f"theorem {sym}"
        sim_def = "def Simulates (p : CapturedMir) : Prop"
        mod_cases: list[tuple[str, str, tuple[object, object]]] = [
            ("unused_section_variable_closed", f"variable {{body : CapturedMir}}\n{thm} : 0 < 1 := by decide\n", closed_only),
            ("def_by_exact_true", f"{sim_def} := by exact True\n{thm} : Simulates fooProg := trivial\n", closed_vacuous),
            ("def_by_trivial", f"{sim_def} := by trivial\n{thm} : Simulates fooProg := trivial\n", closed_vacuous),
            (
                "def_self_implication",
                f"{sim_def} := stepOk p → stepOk p\n{thm} : Simulates fooProg := id\n",
                closed_vacuous,
            ),
            (
                "def_untyped_closed_param",
                f"def Simulates (p : CapturedMir) := 0 < 1\n{thm} : Simulates fooProg := by decide\n",
                closed_only,
            ),
            (
                "def_forall_prop_closed",
                f"def Simulates : ∀ (_ : CapturedMir), Prop := fun _ => 0 < 1\n{thm} : Simulates fooProg := by decide\n",
                closed_only,
            ),
            (
                "empty_prop_structure",
                f"structure Simulates (p : CapturedMir) : Prop where\n{thm} : Simulates fooProg := ⟨⟩\n",
                closed_vacuous,
            ),
            (
                "empty_prop_inductive",
                f"inductive Broken (p : CapturedMir) : Prop\n{thm} (h : Broken fooProg) : {stmt} := nomatch h\n",
                vacuous,
            ),
            (
                "zero_arg_def_in_prefix_or",
                f"def A : Prop := True\n{thm} : Or A ({stmt}) := Or.inl trivial\n",
                vacuous,
            ),
            (
                "parenthesized_def_head",
                f"{sim_def} := True\n{thm} : (Simulates) fooProg := trivial\n",
                closed_vacuous,
            ),
            (
                "piped_def_application",
                f"{sim_def} := True\n{thm} : fooProg |> Simulates := trivial\n",
                closed_vacuous,
            ),
            (
                "match_arm_forall_all_vacuous",
                f"def Simulates : CapturedMir → Prop\n  | .a => ∀ x, True\n  | .b => True\n{thm} : Simulates fooProg := trivial\n",
                closed_vacuous,
            ),
            (
                "match_arm_forall_second_arm_meaningful",
                f"def Simulates : CapturedMir → Prop\n  | .a => ∀ x, True\n  | .b => {stmt}\n{thm} : Simulates fooProg := rfl\n",
                resolved,
            ),
            (
                "elab_mkconst_quoted_sorryax",
                f'elab "cheat" : term => return mkConst ``sorryAx\n{thm} : {stmt} := cheat\n',
                hole_dep,
            ),
        ]
        for label, text, expected in mod_cases:
            with self.subTest(mod_case=label):
                self.assertEqual(status_of_module(text), expected)

        # 4. Statement-pin RHS specialization, `sorry` argument, and ambient-hole checks.
        pin_cases: list[tuple[str, list[str]]] = [
            (f"example : {stmt} := {pin_sym} sorry\n", ["pin_sorry_or_admit"]),
            (f"example : {stmt} := {pin_sym} emptyProg\n", ["pin_instantiates_or_duplicates_arg"]),
            (
                f"example (x : CapturedMir) : annealOutcome x = miriOutcome x := {pin_sym} x x\n",
                ["pin_instantiates_or_duplicates_arg"],
            ),
            (
                f"set_option debug.skipKernelTC true\nexample : {stmt} := {pin_sym}\n",
                ["pin_hole_dependency"],
            ),
        ]
        for pin_src, expected_pin_reasons in pin_cases:
            with self.subTest(pin_src=pin_src), tempfile.TemporaryDirectory() as tmp:
                root = Path(tmp)
                self._write_flip_tree(root, {pin_div: (None, f": {stmt} := rfl", None)})
                audit_file = root / suite.AUTHORITY_AUDIT_FILES["MiniRustSpec"]
                with audit_file.open("a", encoding="utf-8") as fh:
                    fh.write(pin_src)
                rec = self._flip_status(root, pin_div)
                self.assertEqual(
                    (rec["status"], rec["resolution_pin_problems"]),
                    ("resolution_unpinned", expected_pin_reasons),
                )

        # 5. Cross-file imported definitions and holes (1-hop and 2-hop chains, imported pin
        #    definitions, and `materialize_flip_baseline_tree` + `audit_flip_direction_transitions`
        #    catching a hole added inside an imported helper module).
        helper_a = "lean-miri/lean/LeanMiriSpec/Correspondence/CheatA.lean"
        helper_b = "lean-miri/lean/LeanMiriSpec/Correspondence/CheatB.lean"
        self.assertEqual(
            status_of_module(
                f"import LeanMiriSpec.Correspondence.CheatB\n{thm} : Simulates fooProg := trivial\n",
                {
                    helper_a: "def BaseTrue : Prop := True\n",
                    helper_b: f"import LeanMiriSpec.Correspondence.CheatA\n{sim_def} := BaseTrue\n",
                },
            ),
            closed_vacuous,
        )
        self.assertEqual(
            status_of_module(
                f"import LeanMiriSpec.Correspondence.CheatB\n{thm} : {stmt} := wrapHole\n",
                {
                    helper_a: f"axiom rawAx : {stmt}\n",
                    helper_b: f"import LeanMiriSpec.Correspondence.CheatA\ntheorem wrapHole : {stmt} := rawAx\n",
                },
            ),
            hole_dep,
        )
        self.assertEqual(
            status_of_module(
                f"import LeanMiriSpec.Correspondence.CheatA\n{thm} : {stmt} := by simp\n",
                {helper_a: f"@[simp] theorem cheatSimp : {stmt} := sorry\n"},
            ),
            hole_dep,
        )

        # Pin importing a vacuous definition from another module is rejected as unpinned.
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            self._write_flip_tree(root, {pin_div: (None, f": {stmt} := rfl", None)})
            pin_helper = root / "minirust/lean/MiniRustSpec/PinCheat.lean"
            pin_helper.parent.mkdir(parents=True, exist_ok=True)
            pin_helper.write_text("def Locked : Prop := True\n", encoding="utf-8")
            audit_file = root / suite.AUTHORITY_AUDIT_FILES["MiniRustSpec"]
            existing_audit = audit_file.read_text(encoding="utf-8")
            audit_file.write_text(
                f"import MiniRustSpec.PinCheat\n{existing_audit}\nexample : Locked := {pin_sym}\n",
                encoding="utf-8",
            )
            rec = self._flip_status(root, pin_div)
            self.assertEqual(
                (rec["status"], rec["resolution_pin_problems"]),
                ("resolution_unpinned", ["pin_closed_trivial_statement", "pin_vacuous_statement"]),
            )

        # Git revision materialization + transition audit catches a proof hole added to an
        # imported helper module during a flip.
        git = shutil.which("git")
        if git is not None:
            with tempfile.TemporaryDirectory() as tmp:
                repo = Path(tmp) / "repo"
                repo.mkdir(parents=True)

                def run_git(*args: str) -> None:
                    subprocess.run(
                        [
                            git,
                            "-c",
                            "user.name=Flip Audit Test",
                            "-c",
                            "user.email=flip-audit@example.com",
                            "-c",
                            "commit.gpgsign=false",
                            *args,
                        ],
                        cwd=repo,
                        check=True,
                        capture_output=True,
                    )

                run_git("init", "-q")
                self._write_flip_tree(
                    repo, {div_id: (f": {SYNTH_DIVERGENCE_STMT} := rfl", None, None)}
                )
                (repo / helper_a).parent.mkdir(parents=True, exist_ok=True)
                (repo / helper_a).write_text("def benignHelper : Nat := 1\n", encoding="utf-8")
                run_git("add", "-A")
                run_git("commit", "-q", "-m", "baseline")

                # Flip `div_id` (`open -> resolved`) while smuggling an unused `axiom` into
                # imported `CheatA.lean` so `c["status"]` is `"resolved"` and `check_added_holes`
                # across the import closure catches it.
                for sub in ("lean-miri", "minirust", "tests"):
                    if (repo / sub).exists():
                        shutil.rmtree(repo / sub)
                self._write_flip_tree(repo, {div_id: (None, f": {stmt} := rfl", stmt)})
                sim_text = (repo / lm23).read_text(encoding="utf-8")
                (repo / lm23).write_text(
                    f"import LeanMiriSpec.Correspondence.CheatA\n{sim_text}",
                    encoding="utf-8",
                )
                (repo / helper_a).parent.mkdir(parents=True, exist_ok=True)
                (repo / helper_a).write_text(
                    "def benignHelper : Nat := 1\naxiom smuggledHole : False\n",
                    encoding="utf-8",
                )

                base_dest = Path(tmp) / "base_dest"
                suite.materialize_flip_baseline_tree(repo, "HEAD", base_dest)
                self.assertTrue((base_dest / helper_a).is_file())
                audit_imp = suite.audit_flip_direction_transitions(base_dest, repo)
                self.assertFalse(audit_imp["passed"])
                self.assertEqual(
                    [(v["id"], v["reason"]) for v in audit_imp["violations"]],
                    [(div_id, "proof_hole_introduced")],
                )

    def test_lean_source_stripping_caching_and_import_summary_scans(self) -> None:
        # 1. The bulk-copying comment/literal stripper keeps the exact character-level
        #    output: nested and doc block comments, line comments, escaped and raw
        #    strings, character literals, primes, `r` ending an identifier, string gaps
        #    (backslash-newline), and unterminated spans.
        strip_cases = [
            (
                "theorem a : x = y := rfl -- trailing sorry\n",
                "theorem a : x = y := rfl                  \n",
            ),
            (
                "/- outer /- nested sorry -/ still -/ theorem b : P := h\n",
                "                                     theorem b : P := h\n",
            ),
            ("/-- doc\n  sorry -/\ntheorem c : P := h", "       \n          \ntheorem c : P := h"),
            (
                'def s := "a\\"b sorry" ++ r#"raw "sorry" #"# ++ r"x"\n',
                "def s :=              ++                    ++     \n",
            ),
            ("def ch := '\"' ++ '\\'' ++ \"q\"\n", "def ch :=     ++      ++    \n"),
            ('def gap := "line\\\nnext"\nend', "def gap :=            \nend"),
            ("theorem prime' : x' = y := rfl\n", "theorem prime' : x' = y := rfl\n"),
            ('def r2 := sorr"y" ++ (r"z")\n', "def r2 := sorr    ++ (    )\n"),
            ("/- unterminated sorry", " " * 21),
            ('"unterminated sorry', " " * 19),
            ("-- only a comment", " " * 17),
        ]
        for src, expected in strip_cases:
            with self.subTest(strip=src):
                self.assertEqual(suite._strip_lean_comments_and_strings(src), expected)

        # 2. File metadata is cached by content: a same-size rewrite that keeps the
        #    modification time is never served stale.
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "Module.lean"
            path.write_text("theorem a : x = y := sorry\n", encoding="utf-8")
            before = path.stat()
            self.assertEqual(suite._lean_file_hole_token_counts(path)["sorry"], 1)
            path.write_text("theorem a : x = y := rfl  \n", encoding="utf-8")
            os.utime(path, ns=(before.st_atime_ns, before.st_mtime_ns))
            after = path.stat()
            self.assertEqual((after.st_size, after.st_mtime_ns), (before.st_size, before.st_mtime_ns))
            self.assertEqual(suite._lean_file_hole_token_counts(path)["sorry"], 0)

        # 3. An imported module's summary scan exports exactly what a full scan does
        #    (holey declarations, unnamed holes, and definitions that reduce to a fixed
        #    proposition), and a scan restricted to `resolution_symbols` analyzes only
        #    those theorems.
        modules = [
            (
                "def Trivial (p : CapturedMir) : Prop := True\n"
                "def Closed : Prop := 0 < 1\n"
                "def Chained (p : CapturedMir) : Prop := Trivial p ∧ Closed\n"
                "theorem holeyThm : annealOutcome fooProg = 1 := sorry\n"
                "theorem usesHole : annealOutcome fooProg = 1 := holeyThm\n"
                "theorem clean : annealOutcome fooProg = 1 := rfl\n"
                "structure Vacuous (p : CapturedMir) : Prop where\n"
                "inductive Never : Prop\n"
            ),
            (
                "theorem clean : annealOutcome fooProg = 1 := rfl\n"
                "@[simp] theorem attrHole : miriOutcome fooProg = 1 := sorry\n"
                "theorem later : annealOutcome fooProg = 2 := by simp\n"
            ),
            (
                "axiom cheat : annealOutcome fooProg = 1\n"
                "instance : Fact (annealOutcome fooProg = 1) := ⟨cheat⟩\n"
                "theorem clean : annealOutcome fooProg = 1 := rfl\n"
            ),
        ]
        for src in modules:
            with self.subTest(module=src.splitlines()[0]):
                full = suite._scan_lean_declarations_and_pins(src)
                summary = suite._scan_lean_declarations_and_pins(src, summary_only=True)
                for key in ("holey_names", "ambient_hole", "prop_def_inline"):
                    self.assertEqual(summary[key], full[key], key)
                self.assertEqual(
                    (summary["resolutions"], summary["decl_statements"], summary["pins"]), ({}, {}, {})
                )
                only_clean = suite._scan_lean_declarations_and_pins(
                    src, resolution_symbols=frozenset({"clean"})
                )
                self.assertEqual(set(only_clean["resolutions"]), {"clean"})
                self.assertEqual(only_clean["resolutions"]["clean"], full["resolutions"]["clean"])
        first = suite._scan_lean_declarations_and_pins(modules[0])
        self.assertEqual(first["holey_names"], {"holeyThm", "usesHole"})
        self.assertEqual(
            {name: spec[2] for name, spec in first["prop_def_inline"].items()},
            {
                "Trivial": ["True"],
                "Closed": ["(", "0", "<", "1", ")"],
                "Chained": ["(", "True", "∧", "(", "0", "<", "1", ")", ")"],
                "Vacuous": ["True"],
                "Never": ["False"],
            },
        )
        self.assertTrue(suite._scan_lean_declarations_and_pins(modules[1])["ambient_hole"])
        self.assertTrue(suite._scan_lean_declarations_and_pins(modules[2])["ambient_hole"])

    def test_run_step_injects_lake_artifact_cache_env_without_mutating_os_environ(self) -> None:
        # `_build_step_env` always enforces `LAKE_ARTIFACT_CACHE=true` and
        # `LAKE_RESTORE_ARTIFACTS=true`, even if base env unset or disabled them,
        # without mutating the caller's mapping or `os.environ`.
        base = {"PATH": "/usr/bin", "LAKE_ARTIFACT_CACHE": "false", "LAKE_RESTORE_ARTIFACTS": "false"}
        env = suite._build_step_env("lake_build_core_theory", base_env=base)
        self.assertEqual(env["LAKE_ARTIFACT_CACHE"], "true")
        self.assertEqual(env["LAKE_RESTORE_ARTIFACTS"], "true")
        self.assertEqual(base["LAKE_ARTIFACT_CACHE"], "false")
        self.assertEqual(base["LAKE_RESTORE_ARTIFACTS"], "false")

        # End-to-end `_run_step` subprocess observes both variables as `"true"`.
        with tempfile.TemporaryDirectory() as tmp:
            out_file = Path(tmp) / "env.json"
            probe_code = (
                "import json, os, pathlib; "
                f"pathlib.Path({str(out_file)!r}).write_text(json.dumps({{"
                "'LAKE_ARTIFACT_CACHE': os.environ.get('LAKE_ARTIFACT_CACHE'), "
                "'LAKE_RESTORE_ARTIFACTS': os.environ.get('LAKE_RESTORE_ARTIFACTS')"
                "}))"
            )
            res = suite._run_step(
                name="probe_lake_cache_env",
                category="cat1_trusted_boundary",
                cmd=[sys.executable, "-c", probe_code],
                cwd=REPO_ROOT,
                timeout_sec=10,
            )
            self.assertEqual(res["status"], "PASS", res.get("failure_excerpt"))
            observed = json.loads(out_file.read_text(encoding="utf-8"))
            self.assertEqual(observed["LAKE_ARTIFACT_CACHE"], "true")
            self.assertEqual(observed["LAKE_RESTORE_ARTIFACTS"], "true")

    def test_resolve_anneal_lean_run_precedence_and_edge_cases(self) -> None:
        # The `PATH` / `~/.local/bin` candidates must pass `_wrapper_honors_lean_num_threads`
        # whenever an in-repo wrapper exists, so they are minimal wrappers that keep the
        # caller's `LEAN_NUM_THREADS` (no `--probe` banner; exec the command untouched).
        def make_exe(path: Path, *, executable: bool = True) -> Path:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(
                "#!/bin/sh\n"
                'case " $* " in *" --probe "*) exit 0 ;; esac\n'
                'while [ "$#" -gt 0 ] && [ "$1" != "--" ]; do shift; done\n'
                '[ "$#" -gt 0 ] && shift\n'
                '[ "$#" -gt 0 ] && exec "$@"\n'
                "exit 0\n",
                encoding="utf-8",
            )
            path.chmod(0o755 if executable else 0o644)
            return path

        with tempfile.TemporaryDirectory() as tmp, mock.patch.dict(suite._WRAPPER_THREAD_PROBE_CACHE, clear=True):
            root = Path(tmp)
            repo = root / "repo"
            repo_wrapper = make_exe(repo / "scripts/anneal-lean-run")
            home_dir = root / "home"
            home_wrapper = make_exe(home_dir / ".local/bin/anneal-lean-run")
            path_bin = root / "path_bin"
            path_wrapper = make_exe(path_bin / "anneal-lean-run")
            env_wrapper = make_exe(root / "custom/anneal-lean-run")
            non_exec = make_exe(root / "custom/non_exec_lean_run", executable=False)
            broken_link = root / "custom/broken_lean_run"
            broken_link.symlink_to(root / "does_not_exist")

            # 1. `ANNEAL_LEAN_RUN` takes highest precedence when executable file.
            self.assertEqual(
                suite._resolve_anneal_lean_run(
                    repo,
                    env={
                        "ANNEAL_LEAN_RUN": str(env_wrapper),
                        "PATH": str(path_bin),
                        "HOME": str(home_dir),
                    },
                ),
                env_wrapper,
            )

            # 2. Invalid/non-executable/broken-symlink/directory `ANNEAL_LEAN_RUN`
            #    falls through to `PATH`.
            for bad in (str(non_exec), str(broken_link), str(root / "custom"), "   "):
                self.assertEqual(
                    suite._resolve_anneal_lean_run(
                        repo,
                        env={
                            "ANNEAL_LEAN_RUN": bad,
                            "PATH": str(path_bin),
                            "HOME": str(home_dir),
                        },
                    ),
                    path_wrapper,
                    f"bad ANNEAL_LEAN_RUN={bad!r} should fall through to PATH",
                )

            # 3. Minimal cron `PATH` (omitting `~/.local/bin`) prefers fleet-managed
            #    `~/.local/bin/anneal-lean-run` over in-repo `scripts/anneal-lean-run`.
            self.assertEqual(
                suite._resolve_anneal_lean_run(
                    repo,
                    env={"PATH": "/usr/bin:/bin", "HOME": str(home_dir)},
                ),
                home_wrapper,
            )

            # 4. When `~/.local/bin/anneal-lean-run` is absent or non-executable and
            #    not on `PATH`, falls back to in-repo `scripts/anneal-lean-run`.
            home_wrapper.chmod(0o644)
            self.assertEqual(
                suite._resolve_anneal_lean_run(
                    repo,
                    env={"PATH": "/usr/bin:/bin", "HOME": str(home_dir)},
                ),
                repo_wrapper,
            )
            self.assertEqual(
                suite._resolve_anneal_lean_run(repo, env={"PATH": ""}),
                repo_wrapper,
            )

            # 5. Returns `None` when none of the candidates is executable.
            repo_wrapper.chmod(0o644)
            self.assertIsNone(
                suite._resolve_anneal_lean_run(
                    repo,
                    env={"PATH": "/usr/bin:/bin", "HOME": str(home_dir)},
                )
            )

    def test_clean_stale_oleans_freshness_transitive_trusted_and_safety(self) -> None:
        def touch(path: Path, ts_sec: float) -> Path:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text("x", encoding="utf-8")
            os.utime(path, (ts_sec, ts_sec))
            return path

        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            t_old = 1_700_000_000.0
            t_mid = 1_700_000_100.0
            t_new = 1_700_000_200.0

            # Sources
            touch(root / "trusted/lean/Trusted.lean", t_old)
            touch(root / "trusted/lean/Trusted/Core.lean", t_old)
            touch(root / "theory/Anneal/Fresh.lean", t_old)
            touch(root / "theory/Anneal/Stale.lean", t_new)
            touch(root / "minirust/lean/MiniRustSpec/Spec.lean", t_old)
            touch(root / "examples/Smoke.lean", t_new)
            touch(root / "lean-miri/vendor/Miri/Keep.lean", t_old)

            # Root `.lake/build/lib/lean/` artifacts
            trusted_olean = touch(root / ".lake/build/lib/lean/Trusted.olean", t_mid)
            trusted_core = touch(root / ".lake/build/lib/lean/Trusted/Core.olean", t_mid)
            fresh_olean = touch(root / ".lake/build/lib/lean/Anneal/Fresh.olean", t_mid)
            stale_olean = touch(root / ".lake/build/lib/lean/Anneal/Stale.olean", t_mid)
            stale_server = touch(root / ".lake/build/lib/lean/Anneal/Stale.olean.server", t_mid)
            stale_priv = touch(root / ".lake/build/lib/lean/Anneal/Stale.olean.private", t_mid)
            stale_ilean = touch(root / ".lake/build/lib/lean/Anneal/Stale.ilean", t_mid)
            spec_olean = touch(root / ".lake/build/lib/lean/MiniRustSpec/Spec.olean", t_mid)
            # Non-artifact sentinel outside `.lake/build/lib/lean/` must never be touched.
            outside_file = touch(root / ".lake/build/sentinel.olean", t_old)

            # `examples/.lake/build/lib/lean/` artifacts
            ex_smoke_olean = touch(root / "examples/.lake/build/lib/lean/Smoke.olean", t_mid)
            ex_smoke_ilean = touch(root / "examples/.lake/build/lib/lean/Smoke.ilean", t_mid)
            ex_miri_olean = touch(root / "examples/.lake/build/lib/lean/Miri/Keep.olean", t_mid)

            # Case 1: Only directly stale modules (`Anneal/Stale`, `examples/Smoke`) are removed;
            # fresh `Trusted`, `Anneal/Fresh`, `MiniRustSpec/Spec`, `Miri/Keep`, and outside files stay.
            removed = suite.clean_stale_oleans(root)
            self.assertEqual(
                set(removed),
                {stale_olean, stale_server, stale_priv, stale_ilean, ex_smoke_olean, ex_smoke_ilean},
            )
            self.assertTrue(trusted_olean.is_file())
            self.assertTrue(trusted_core.is_file())
            self.assertTrue(fresh_olean.is_file())
            self.assertTrue(spec_olean.is_file())
            self.assertTrue(ex_miri_olean.is_file())
            self.assertTrue(outside_file.is_file())

            # Case 2: Re-running when everything remaining is fresh is a fast no-op.
            t0 = time.monotonic()
            self.assertEqual(suite.clean_stale_oleans(root), [])
            self.assertLess(time.monotonic() - t0, 0.25)

            # Case 3: Updating `trusted/lean/Trusted/Core.lean` transitively invalidates
            # `Trusted` and downstream `Anneal`/`MiniRustSpec` `.olean`s, while sparing
            # vendored `Miri` (which does not import `Trusted`) and files outside `lib/lean/`.
            touch(root / "trusted/lean/Trusted/Core.lean", t_new)
            removed_trans = suite.clean_stale_oleans(root)
            self.assertEqual(
                set(removed_trans),
                {trusted_olean, trusted_core, fresh_olean, spec_olean},
            )
            self.assertTrue(ex_miri_olean.is_file())
            self.assertTrue(outside_file.is_file())

            # Case 4: Symlink safety — never traverse a symlinked dir inside `lib/lean/`.
            escape_dir = root / "outside_secret"
            escape_file = touch(escape_dir / "Target.olean", t_old)
            (root / ".lake/build/lib/lean/Anneal").mkdir(parents=True, exist_ok=True)
            (root / ".lake/build/lib/lean/Anneal/Escape").symlink_to(escape_dir)
            suite.clean_stale_oleans(root)
            self.assertTrue(escape_file.is_file())

    def test_lake_hash_matches_lean_4_34_1_known_answers(self) -> None:
        # Ground truth printed by Lean 4.34.1 itself (`import Lake`,
        # `#eval (Lake.Hash.ofText s).hex` / `(Lake.Hash.ofByteArray b).hex`); the same
        # function reproduces the source hashes in real `.lake/build/lib/lean/*.trace` files.
        for text, expected in (
            ("", "21c42906adea99f5"),
            ("a", "6ccb214a796350f7"),
            ("abcdefg", "5ada98fa484c431b"),  # 7-byte tail only
            ("abcdefgh", "4a88fc15a029668c"),  # exactly one 8-byte block
            ("import Trusted\n\ndef x := 1\n", "6a39cb7a09a54b0c"),
            ("import Trusted\r\n\r\ndef x := 1\r\n", "6a39cb7a09a54b0c"),  # `\r\n` -> `\n`
            ("a\rb\n", "c1b3a4fcd8bb7ad6"),  # a lone `\r` is kept
            ("theorem «π» : α → β := λ x => x -- ∀∃\n", "7b8d1ae2cbe92fc4"),
        ):
            self.assertEqual(suite._lake_text_hash_hex(text.encode("utf-8")), expected, repr(text))
        self.assertEqual(
            suite._lake_bytes_hash_hex(bytes([0, 1, 2, 255, 13, 10, 7, 8, 9])), "0692aef1a8bd5877"
        )
        # Binary hashing never normalizes line endings.
        self.assertNotEqual(suite._lake_bytes_hash_hex(b"a\r\nb"), suite._lake_text_hash_hex(b"a\r\nb"))

    @staticmethod
    def _write_file_at(path: Path, content: bytes, ts_sec: float) -> Path:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(content)
        os.utime(path, (ts_sec, ts_sec))
        return path

    def _write_lake_built_module(
        self,
        lib_dir: Path,
        rel_mod: str,
        built_from: bytes,
        built_at: float,
        *,
        module_system: bool = False,
        fetched_at: float | None = None,
    ) -> dict[str, Path]:
        """Lay down what Lake 4.34.1 leaves in `.lake/build/lib/lean/` for module `rel_mod`
        built from source text `built_from` at `built_at` in some other checkout: the
        `.olean` parts, `.ilean`, their `.hash` sidecars and the `.trace` naming the source
        and output content hashes (`schemaVersion` `2025-09-10`).

        With `fetched_at`, the artifacts were instead restored from Lake's cache at that
        time: they keep their `built_at` mtime (hard links), while the `.hash` sidecars and
        the `.trace` are written at `fetched_at`, and the trace is the synthetic one of
        `BuildMetadata.ofFetch`, which names the outputs but no inputs."""
        files: dict[str, Path] = {}
        hashes: dict[str, str] = {}
        parts = [".olean", ".olean.server", ".olean.private"] if module_system else [".olean"]
        extras = [".ir", ".ir.sig", ".ltar"] if module_system else []
        for suffix in (*parts, ".ilean", *extras):
            content = f"{rel_mod}{suffix}:".encode("utf-8") + built_from
            hashes[suffix] = suite._lake_bytes_hash_hex(content)
            files[suffix] = self._write_file_at(lib_dir / f"{rel_mod}{suffix}", content, built_at)
            files[f"{suffix}.hash"] = self._write_file_at(
                lib_dir / f"{rel_mod}{suffix}.hash",
                hashes[suffix].encode("ascii"),
                built_at if fetched_at is None else fetched_at,
            )
        trace = {
            "synthetic": False,
            "schemaVersion": "2025-09-10",
            "depHash": "56989c8629fa0281",
            "log": [],
            "inputs": [
                ["deps", [["imports", []]]],
                ["Lean 4.34.1, commit 5045d0056413266e57c625dcd7c365b10e377c52", "e9f3658beb070375"],
                [
                    f"/some/other/worktree/examples/../src/{rel_mod}.lean",
                    suite._lake_text_hash_hex(built_from),
                ],
                ["options", "00000000000006bb"],
                [f"Module.name: {rel_mod.replace('/', '.')}", "48eba4641e299005"],
            ],
            "outputs": {
                "o": [f"{hashes[suffix]}{suffix}" for suffix in parts],
                "m": module_system,
                "i": f"{hashes['.ilean']}.ilean",
                "c": "27e03df3817a8e48.c",
            },
        }
        if fetched_at is not None:
            trace = {
                "synthetic": True,
                "schemaVersion": "2025-09-10",
                "outputs": trace["outputs"],
                "log": [],
                "inputs": [],
                "depHash": "cca9185a3f3ac0e6",
            }
        files[".trace"] = self._write_file_at(
            lib_dir / f"{rel_mod}.trace",
            json.dumps(trace).encode("utf-8"),
            built_at if fetched_at is None else fetched_at,
        )
        return files

    def test_clean_stale_oleans_trusts_lake_content_hashes_over_inverted_mtimes(self) -> None:
        # Lake hard-links cached artifacts into the build directory, so a restored `.olean`
        # keeps the mtime of whichever checkout first built it; a cache seeded from another
        # worktree looks the same. Every source of this checkout is then "newer" than its
        # `.olean` although Lake (which decides by content hash) considers all of it fresh.
        t_built, t_checkout, t_edit = 1_700_000_000.0, 1_700_000_500.0, 1_700_001_000.0
        sources = {
            "trusted/lean/Trusted.lean": b"import Trusted.Core\n",
            "trusted/lean/Trusted/Core.lean": b"def core := 1\n",
            "theory/Anneal/Mod.lean": b"import Trusted\ndef m := core\n",
            "theory/Anneal/Other.lean": b"import Trusted\ndef o := core\n",
            "lean-miri/vendor/Miri/Keep.lean": b"def keep := 0\n",
        }
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            lib = root / ".lake/build/lib/lean"
            ex_lib = root / "examples/.lake/build/lib/lean"
            for rel, text in sources.items():
                self._write_file_at(root / rel, text, t_checkout)
            # A CRLF checkout of the LF text Lake hashed is still the same source.
            self._write_file_at(
                root / "theory/Anneal/Mod.lean",
                sources["theory/Anneal/Mod.lean"].replace(b"\n", b"\r\n"),
                t_checkout,
            )
            built: dict[tuple[str, str], dict[str, Path]] = {}
            for where, lib_dir, rel_mod, src_rel in (
                ("root", lib, "Trusted", "trusted/lean/Trusted.lean"),
                ("root", lib, "Trusted/Core", "trusted/lean/Trusted/Core.lean"),
                ("root", lib, "Anneal/Mod", "theory/Anneal/Mod.lean"),
                ("root", lib, "Anneal/Other", "theory/Anneal/Other.lean"),
                ("examples", ex_lib, "Trusted", "trusted/lean/Trusted.lean"),
                ("examples", ex_lib, "Trusted/Core", "trusted/lean/Trusted/Core.lean"),
                ("examples", ex_lib, "Miri/Keep", "lean-miri/vendor/Miri/Keep.lean"),
            ):
                built[(where, rel_mod)] = self._write_lake_built_module(
                    lib_dir, rel_mod, sources[src_rel], t_built, module_system=rel_mod == "Anneal/Other"
                )
            all_files = {p for files in built.values() for p in files.values()}

            def files_of(*keys: tuple[str, str]) -> set[Path]:
                return {p for key in keys for p in built[key].values()}

            # Nothing is stale: the guard must not wipe a coherent cache (it used to delete
            # every one of these files, `Trusted` first and then everything downstream).
            self.assertEqual(suite.clean_stale_oleans(root), [])
            self.assertTrue(all(p.is_file() for p in all_files))

            # A real edit of one module removes exactly that module's files, including the
            # module-system `.olean.server` / `.olean.private` / `.ir` / `.ir.sig` companions
            # and its `.ltar` archive.
            self._write_file_at(root / "theory/Anneal/Other.lean", b"import Trusted\ndef o := 2\n", t_edit)
            removed = suite.clean_stale_oleans(root)
            self.assertEqual(set(removed), files_of(("root", "Anneal/Other")))
            self.assertEqual(
                {p.name for p in removed},
                {
                    f"Other{sfx}{tail}"
                    for sfx in (
                        ".olean",
                        ".olean.server",
                        ".olean.private",
                        ".ilean",
                        ".ir",
                        ".ir.sig",
                        ".ltar",
                    )
                    for tail in ("", ".hash")
                }
                | {"Other.trace"},
            )
            self.assertEqual(suite.clean_stale_oleans(root), [])

            # A real edit of a `Trusted` source invalidates `Trusted` and everything downstream
            # in both Lake roots, and still spares vendored `Miri`.
            self._write_file_at(root / "trusted/lean/Trusted/Core.lean", b"def core := 2\n", t_edit)
            removed = suite.clean_stale_oleans(root)
            self.assertEqual(
                set(removed),
                files_of(
                    ("root", "Trusted"),
                    ("root", "Trusted/Core"),
                    ("root", "Anneal/Mod"),
                    ("examples", "Trusted"),
                    ("examples", "Trusted/Core"),
                ),
            )
            self.assertTrue(all(p.is_file() for p in files_of(("examples", "Miri/Keep"))))
            self.assertEqual(suite.clean_stale_oleans(root), [])

    def test_clean_stale_oleans_exoneration_requires_private_self_consistent_lake_records(self) -> None:
        # An mtime-stale module is kept only on positive evidence. Each tampering below
        # leaves the source "newer" than its `.olean` and breaks one link of that evidence,
        # so the guard must fall back to the mtime verdict and remove the module.
        t_built, t_checkout = 1_700_000_000.0, 1_700_000_500.0
        source = b"import Trusted\ndef m := 1\n"

        def retime(path: Path, ts_sec: float) -> None:
            os.utime(path, (ts_sec, ts_sec))

        def rewrite_trace(files: dict[str, Path], edit) -> None:
            doc = json.loads(files[".trace"].read_text(encoding="utf-8"))
            edit(doc)
            self._write_file_at(files[".trace"], json.dumps(doc).encode("utf-8"), t_built)

        def other_source_named(doc: dict) -> None:
            doc["inputs"][2][0] = "/some/other/worktree/src/Anneal/NotMod.lean"

        def source_named_twice(doc: dict) -> None:
            doc["inputs"].append(["/elsewhere/Anneal/Mod.lean", "0123456789abcdef"])

        def uppercase_source_hash(doc: dict) -> None:
            doc["inputs"][2][1] = doc["inputs"][2][1].upper() if doc["inputs"][2][1].upper() != doc["inputs"][2][1] else "G" * 16

        def olean_output_dropped(doc: dict) -> None:
            doc["outputs"]["o"] = []

        def extra_part_named(doc: dict) -> None:
            doc["outputs"]["o"].append("0123456789abcdef.olean.server")

        tamperings = {
            "source_edited_in_place": lambda root, f: self._write_file_at(
                root / "theory/Anneal/Mod.lean", b"import Trusted\ndef m := 2\n", t_checkout
            ),
            "trace_missing": lambda root, f: f.pop(".trace").unlink(),
            "trace_not_json": lambda root, f: self._write_file_at(f[".trace"], b"{not json", t_built),
            "trace_not_an_object": lambda root, f: self._write_file_at(f[".trace"], b"[]", t_built),
            "trace_is_a_symlink": lambda root, f: (
                shutil.move(str(f[".trace"]), str(root / "elsewhere.trace")),
                f[".trace"].symlink_to(root / "elsewhere.trace"),
            ),
            # `cp -al`-seeded caches share `.trace` / `.hash` inodes with another tree, whose
            # Lake rewrites them in place for *its* sources.
            "trace_hard_linked": lambda root, f: os.link(f[".trace"], root / "other_tree.trace"),
            "trace_names_another_source": lambda root, f: rewrite_trace(f, other_source_named),
            "trace_names_the_source_twice": lambda root, f: rewrite_trace(f, source_named_twice),
            "trace_source_hash_malformed": lambda root, f: rewrite_trace(f, uppercase_source_hash),
            "trace_without_olean_output": lambda root, f: rewrite_trace(f, olean_output_dropped),
            "trace_names_a_part_missing_on_disk": lambda root, f: rewrite_trace(f, extra_part_named),
            "olean_part_on_disk_not_in_trace": lambda root, f: f.update(
                {
                    ".olean.private": self._write_file_at(
                        f[".olean"].with_name("Mod.olean.private"), b"stray", t_built
                    )
                }
            ),
            "sidecar_missing": lambda root, f: f.pop(".olean.hash").unlink(),
            "sidecar_mismatch": lambda root, f: self._write_file_at(
                f[".olean.hash"], b"0123456789abcdef", t_built
            ),
            "sidecar_hard_linked": lambda root, f: os.link(f[".olean.hash"], root / "other_tree.hash"),
            # The `.olean` was replaced after Lake recorded its hash (an interrupted rebuild).
            "sidecar_older_than_olean": lambda root, f: retime(f[".olean"], t_built + 60),
        }
        for name, tamper in tamperings.items():
            with self.subTest(tampering=name), tempfile.TemporaryDirectory() as tmp:
                root = Path(tmp)
                self._write_file_at(root / "theory/Anneal/Mod.lean", source, t_checkout)
                files = self._write_lake_built_module(
                    root / ".lake/build/lib/lean", "Anneal/Mod", source, t_built
                )
                self.assertEqual(suite.clean_stale_oleans(root), [], "control: coherent records")
                tamper(root, files)
                self.assertEqual(set(suite.clean_stale_oleans(root)), set(files.values()))
                self.assertFalse(any(os.path.lexists(p) for p in files.values()))
                self.assertTrue((root / "theory/Anneal/Mod.lean").is_file())

    def test_clean_stale_oleans_trusts_lake_cache_fetch_traces_written_after_the_source(self) -> None:
        # What the guard itself causes: it removes a stale module, Lake restores the module
        # from its artifact cache, and the restored `.olean` (a hard link) is again older than
        # the source. Lake then writes a synthetic `.trace` without inputs, so no source hash
        # can be compared; but Lake derived the module's input hash from the source when it
        # wrote that trace. If such a trace were not accepted, every restored module would be
        # removed and restored again on every run.
        t_built, t_checkout, t_fetched, t_edit = (
            1_700_000_000.0,
            1_700_000_500.0,
            1_700_001_000.0,
            1_700_001_500.0,
        )
        sources = {
            "trusted/lean/Trusted/Core.lean": ("Trusted/Core", b"def core := 1\n"),
            "theory/Anneal/Mod.lean": ("Anneal/Mod", b"import Trusted.Core\n"),
        }

        def lay_out(root: Path, fetched_at: float) -> set[Path]:
            files: set[Path] = set()
            for rel, (rel_mod, text) in sources.items():
                self._write_file_at(root / rel, text, t_checkout)
                files.update(
                    self._write_lake_built_module(
                        root / ".lake/build/lib/lean", rel_mod, text, t_built, fetched_at=fetched_at
                    ).values()
                )
            return files

        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            files = lay_out(root, t_fetched)
            self.assertEqual(suite.clean_stale_oleans(root), [])
            # Fetched in the very instant the source was written still counts.
            for path in (root / ".lake/build/lib/lean").rglob("*.trace"):
                os.utime(path, (t_checkout, t_checkout))
            for path in (root / ".lake/build/lib/lean").rglob("*.hash"):
                os.utime(path, (t_checkout, t_checkout))
            self.assertEqual(suite.clean_stale_oleans(root), [])
            # A later edit is newer than the restore: the module is stale again, and an
            # edited `Trusted` module takes its dependents with it.
            self._write_file_at(root / "theory/Anneal/Mod.lean", b"import Trusted.Core\ndef m := 1\n", t_edit)
            removed = set(suite.clean_stale_oleans(root))
            self.assertEqual({p.name.split(".")[0] for p in removed}, {"Mod"})
            self.assertTrue(removed < files)
            self._write_file_at(root / "trusted/lean/Trusted/Core.lean", b"def core := 2\n", t_edit)
            self.assertEqual(set(suite.clean_stale_oleans(root)), files - removed)

        # A cache seeded from another checkout carries fetch traces that predate this
        # checkout's sources: nothing ties them to these sources, so the mtime verdict stands.
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            files = lay_out(root, t_built + 60)
            self.assertEqual(set(suite.clean_stale_oleans(root)), files)

        # A fetch trace is trusted on the same terms as a build trace: private files only,
        # and a sidecar that still matches the output the trace names.
        for name in ("trace_hard_linked", "sidecar_mismatch", "inputs_present_on_synthetic_trace"):
            with self.subTest(tampering=name), tempfile.TemporaryDirectory() as tmp:
                root = Path(tmp)
                files = lay_out(root, t_fetched)
                mod_trace = root / ".lake/build/lib/lean/Anneal/Mod.trace"
                if name == "trace_hard_linked":
                    os.link(mod_trace, root / "other_tree.trace")
                elif name == "sidecar_mismatch":
                    self._write_file_at(
                        root / ".lake/build/lib/lean/Anneal/Mod.olean.hash", b"0123456789abcdef", t_fetched
                    )
                else:
                    doc = json.loads(mod_trace.read_text(encoding="utf-8"))
                    doc["inputs"] = [["options", "00000000000006bb"]]
                    self._write_file_at(mod_trace, json.dumps(doc).encode("utf-8"), t_fetched)
                removed = set(suite.clean_stale_oleans(root))
                self.assertEqual({p.name.split(".")[0] for p in removed}, {"Mod"})

    def test_clean_stale_oleans_is_stable_after_an_incremental_trusted_rebuild(self) -> None:
        # Lake rebuilds only the importers of an edited module. After `Trusted/Edited.lean`
        # changes, the unrelated `Trusted/Leaf.olean` legitimately stays older than the newest
        # `trusted/lean` source forever; comparing every `Trusted` `.olean` with that newest
        # source would wipe the whole root on every later run. No Lake records are involved.
        t_first_build, t_edit, t_rebuild = 1_700_000_000.0, 1_700_000_500.0, 1_700_001_000.0
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            lib = root / ".lake/build/lib/lean"
            self._write_file_at(root / "trusted/lean/Trusted/Leaf.lean", b"def leaf := 0\n", t_first_build - 100)
            self._write_file_at(root / "trusted/lean/Trusted/Edited.lean", b"def edited := 2\n", t_edit)
            self._write_file_at(root / "theory/Anneal/Mod.lean", b"import Trusted.Edited\n", t_first_build - 100)
            self._write_file_at(root / "theory/Anneal/Indep.lean", b"import Trusted.Leaf\n", t_first_build - 100)
            leaf = self._write_file_at(lib / "Trusted/Leaf.olean", b"x", t_first_build)
            indep = self._write_file_at(lib / "Anneal/Indep.olean", b"x", t_first_build)
            edited = self._write_file_at(lib / "Trusted/Edited.olean", b"x", t_rebuild)
            mod = self._write_file_at(lib / "Anneal/Mod.olean", b"x", t_rebuild)
            self.assertEqual(suite.clean_stale_oleans(root), [])
            self.assertTrue(all(p.is_file() for p in (leaf, indep, edited, mod)))
            # Once a `Trusted` source is newer than its own `.olean` (and nothing proves it
            # unchanged), the whole root is stale against `Trusted`.
            self._write_file_at(root / "trusted/lean/Trusted/Leaf.lean", b"def leaf := 1\n", t_rebuild + 100)
            self.assertEqual(set(suite.clean_stale_oleans(root)), {leaf, indep, edited, mod})

    def test_clean_stale_oleans_unreadable_and_symlinked_artifacts(self) -> None:
        t_built, t_checkout = 1_700_000_000.0, 1_700_000_500.0
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            lib = root / ".lake/build/lib/lean"
            outside = self._write_file_at(root / "elsewhere/Linked.olean", b"x", t_built)
            for mod in ("Dangling", "Linked", "Fresh"):
                self._write_file_at(root / f"theory/Anneal/{mod}.lean", b"def x := 1\n", t_built - 100)
            fresh = self._write_file_at(lib / "Anneal/Fresh.olean", b"x", t_built)
            # A dangling `.olean` can never be loaded: the module is stale even though its
            # source is older than everything, and so are its readable companions.
            dangling = lib / "Anneal/Dangling.olean"
            dangling.symlink_to(root / "elsewhere/missing.olean")
            dangling_ilean = self._write_file_at(lib / "Anneal/Dangling.ilean", b"x", t_built)
            # A symlinked `.olean` is judged by its target and, when stale, only unlinked.
            linked = lib / "Anneal/Linked.olean"
            linked.symlink_to(outside)
            self.assertEqual(suite.clean_stale_oleans(root), [dangling_ilean, dangling])
            self.assertFalse(os.path.lexists(dangling))
            self.assertTrue(linked.is_symlink() and fresh.is_file())
            self._write_file_at(root / "theory/Anneal/Linked.lean", b"def x := 2\n", t_checkout)
            self.assertEqual(suite.clean_stale_oleans(root), [linked])
            self.assertFalse(os.path.lexists(linked))
            self.assertTrue(outside.is_file() and fresh.is_file())

            # An unreadable `Trusted` `.olean` makes the whole root stale against `Trusted`.
            broken_trusted = lib / "Trusted/Core.olean"
            broken_trusted.parent.mkdir(parents=True)
            broken_trusted.symlink_to(root / "elsewhere/missing.olean")
            self.assertEqual(set(suite.clean_stale_oleans(root)), {broken_trusted, fresh})

    def test_preflight_stale_olean_guard_runs_once_before_lake_steps_and_never_aborts_the_suite(self) -> None:
        events: list[str] = []

        def fake_run_step(name: str, category: str, cmd: list[str], cwd: Path, timeout_sec: int = 900, **_kw):
            events.append(f"step:{name}")
            return {
                "name": name,
                "category": category,
                "status": "PASS",
                "exit_code": 0,
                "duration_sec": 0.0,
                "command": " ".join(cmd),
                "audit_tags": [],
                "failure_excerpt": "",
            }

        def fake_clean(repo_root: Path) -> list[Path]:
            events.append(f"clean:{repo_root}")
            return []

        def failing_clean(repo_root: Path) -> list[Path]:
            events.append("clean:boom")
            raise RuntimeError("boom")

        def run(profile: str, clean) -> tuple[int, str]:
            events.clear()
            stderr = io.StringIO()
            with (
                tempfile.TemporaryDirectory() as tmp,
                mock.patch.object(suite, "_run_step", fake_run_step),
                mock.patch.object(suite, "clean_stale_oleans", clean),
                contextlib.redirect_stderr(stderr),
            ):
                code, dashboard, _md = suite.run_suite_and_generate_dashboard(
                    repo_root=REPO_ROOT, profile=profile, state_dir=Path(tmp) / "state"
                )
            self.assertEqual(
                dashboard["pillar_2_correctness_and_correspondence"]["steps_total"],
                len(suite.build_suite_steps(REPO_ROOT, profile)),
            )
            return code, stderr.getvalue()

        for profile in ("quick", "nightly"):
            code, err = run(profile, fake_clean)
            self.assertEqual(code, 0)
            self.assertEqual(err, "")
            # Exactly once, on the suite's repo root, before the first step runs.
            self.assertEqual(events[0], f"clean:{REPO_ROOT}")
            self.assertEqual([e for e in events if e.startswith("clean:")], [events[0]])
            self.assertEqual(
                events[1:], [f"step:{name}" for name, _c, _cmd, _t in suite.build_suite_steps(REPO_ROOT, profile)]
            )
        # `census-only` runs no Lake/Lean step, so the build directories are left alone.
        code, _err = run("census-only", fake_clean)
        self.assertEqual(code, 0)
        self.assertFalse(any(e.startswith("clean:") for e in events))
        # The guard is best-effort: its failure is reported and every step still runs.
        code, err = run("quick", failing_clean)
        self.assertEqual(code, 0)
        self.assertIn("stale .olean pre-flight failed (RuntimeError: boom)", err)
        self.assertEqual(events[0], "clean:boom")
        self.assertEqual(len(events), 1 + len(suite.build_suite_steps(REPO_ROOT, "quick")))

    def test_preflight_stale_olean_guard_reports_what_it_removed(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            self._write_file_at(root / "theory/Anneal/Stale.lean", b"def s := 1\n", 1_700_000_500.0)
            stale = self._write_file_at(root / ".lake/build/lib/lean/Anneal/Stale.olean", b"x", 1_700_000_000.0)
            ilean = self._write_file_at(root / ".lake/build/lib/lean/Anneal/Stale.ilean", b"x", 1_700_000_000.0)
            stderr = io.StringIO()
            with contextlib.redirect_stderr(stderr):
                removed = suite._preflight_clean_stale_oleans(root)
            self.assertEqual(removed, [ilean, stale])
            self.assertEqual(
                stderr.getvalue(),
                "[nightly-suite] stale .olean pre-flight removed 2 artifact file(s) of 1 module(s): "
                ".lake/build/lib/lean/Anneal/Stale.olean\n",
            )
            stderr = io.StringIO()
            with contextlib.redirect_stderr(stderr):
                self.assertEqual(suite._preflight_clean_stale_oleans(root), [])
            self.assertEqual(stderr.getvalue(), "")

    def test_preflight_stale_olean_guard_reports_orphan_non_olean_module_count(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            self._write_file_at(root / "theory/Anneal/Orphan.lean", b"def o := 1\n", 1_700_000_500.0)
            ilean = self._write_file_at(root / ".lake/build/lib/lean/Anneal/Orphan.ilean", b"x", 1_700_000_000.0)
            trace = self._write_file_at(root / ".lake/build/lib/lean/Anneal/Orphan.trace", b"{}", 1_700_000_000.0)
            stderr = io.StringIO()
            with contextlib.redirect_stderr(stderr):
                removed = suite._preflight_clean_stale_oleans(root)
            self.assertEqual(removed, [ilean, trace])
            self.assertEqual(
                stderr.getvalue(),
                "[nightly-suite] stale .olean pre-flight removed 2 artifact file(s) of 1 module(s): "
                ".lake/build/lib/lean/Anneal/Orphan.ilean\n",
            )

    def test_clean_stale_oleans_detects_partial_trusted_rebuild_via_import_hashes(self) -> None:
        t_first, t_edit, t_rebuild = 1_700_000_000.0, 1_700_000_500.0, 1_700_001_000.0

        def import_art_hex(olean_hash_hex: str) -> str:
            return f"{suite._lake_mix_hash(suite._LAKE_HASH_NIL, int(olean_hash_hex, 16)):016x}"

        def write_built_mod(
            root: Path,
            rel_mod: str,
            src_rel: str,
            src_bytes: bytes,
            olean_hash: str,
            src_mtime: float,
            build_mtime: float,
            dep_hashes: dict[str, str],
        ) -> list[Path]:
            src_path = self._write_file_at(root / src_rel, src_bytes, src_mtime)
            lib = root / ".lake/build/lib/lean"
            olean = self._write_file_at(lib / f"{rel_mod}.olean", b"o", build_mtime)
            ohash = self._write_file_at(lib / f"{rel_mod}.olean.hash", f"{olean_hash}\n".encode("ascii"), build_mtime)
            trace_doc = {
                "synthetic": False,
                "schemaVersion": "2025-09-10",
                "outputs": {"o": [f"{olean_hash}.olean"], "m": False},
                "inputs": [
                    [
                        "deps",
                        [
                            [
                                "imports",
                                [
                                    [f"{dep.replace('/', '.')}:importAllArts", import_art_hex(h)]
                                    for dep, h in dep_hashes.items()
                                ],
                            ]
                        ],
                    ],
                    [os.fspath(src_path), suite._lake_text_hash_hex(src_bytes)],
                ],
                "depHash": "0123456789abcdef",
            }
            trace = self._write_file_at(
                lib / f"{rel_mod}.trace", json.dumps(trace_doc).encode("utf-8"), build_mtime
            )
            return [olean, ohash, trace]

        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            core_h1 = "1111111111111111"
            mid_h = "2222222222222222"
            top_h = "3333333333333333"
            indep_h = "4444444444444444"
            core_files = write_built_mod(
                root, "Trusted/Core", "trusted/lean/Trusted/Core.lean", b"def core := 1\n",
                core_h1, t_first - 100, t_first, {},
            )
            mid_files = write_built_mod(
                root, "Anneal/Mid", "theory/Anneal/Mid.lean", b"import Trusted.Core\n",
                mid_h, t_first - 100, t_first, {"Trusted/Core": core_h1},
            )
            top_files = write_built_mod(
                root, "Anneal/Top", "theory/Anneal/Top.lean", b"import Anneal.Mid\n",
                top_h, t_first - 100, t_first, {"Anneal/Mid": mid_h},
            )
            indep_files = write_built_mod(
                root, "Anneal/Indep", "theory/Anneal/Indep.lean", b"def indep := 0\n",
                indep_h, t_first - 100, t_first, {},
            )
            # Coherent tree: nothing removed.
            self.assertEqual(suite.clean_stale_oleans(root), [])

            # Partial `lake build Trusted`: Trusted/Core rebuilt cleanly to a new hash while
            # Anneal/Mid and Anneal/Top were never rebuilt (every source is still older than
            # its own `.olean`). Rule 3 catches Mid and transitively Top, keeping Core & Indep.
            core_h2 = "aaaaaaaaaaaaaaaa"
            core_files = write_built_mod(
                root, "Trusted/Core", "trusted/lean/Trusted/Core.lean", b"def core := 2\n",
                core_h2, t_edit, t_rebuild, {},
            )
            removed = set(suite.clean_stale_oleans(root))
            self.assertEqual(removed, set(mid_files + top_files))
            self.assertTrue(all(p.is_file() for p in core_files + indep_files))

    # Content hashes Lake 4.34.1 itself wrote (`<Mod>.<part>.hash`) when building a
    # scratch package, and the `<Mod>:importAllArts` hashes it then recorded in the
    # `.trace` of a classic module importing both `ModA` (module system) and `PlainB`.
    _LAKE_MODULE_SYSTEM_PART_HASHES = {
        ".olean": "be0c133e0d0edd5c",
        ".olean.server": "7f9db8e8a33ad80a",
        ".olean.private": "f2cba97f1ec4f19f",
        ".ir.sig": "6065654aaed314af",
        ".ir": "9d207ed66150a81d",
    }
    _LAKE_MODULE_SYSTEM_IMPORT_ALL_ARTS = "2b1fd038f266de81"
    _LAKE_CLASSIC_PART_HASHES = {".olean": "de7b71add399177b"}
    _LAKE_CLASSIC_IMPORT_ALL_ARTS = "11758f8857b189a3"

    def _write_lake_module_with_hashes(
        self,
        lib_dir: Path,
        rel_mod: str,
        part_hashes: dict[str, str],
        built_at: float,
        *,
        imports: dict[str, str] | None = None,
        fetched: bool = False,
    ) -> dict[str, Path]:
        """Lay down module `rel_mod` as Lake leaves it at `built_at`: one artifact and one
        `.hash` sidecar (holding the given content hash) per part of `part_hashes`, and a
        `.trace` recording `<Dep>:importAllArts` for each of `imports` (`{Dep/Mod: hex}`),
        or the import-free synthetic trace of a cache fetch."""
        files: dict[str, Path] = {}
        for suffix, content_hash in part_hashes.items():
            files[suffix] = self._write_file_at(lib_dir / f"{rel_mod}{suffix}", b"artifact", built_at)
            files[f"{suffix}.hash"] = self._write_file_at(
                lib_dir / f"{rel_mod}{suffix}.hash", content_hash.encode("ascii"), built_at
            )
        outputs = {"o": [f"{h}{sfx}" for sfx, h in part_hashes.items() if sfx.startswith(".olean")]}
        recorded: list[list[str]] = []
        for dep, import_hash in (imports or {}).items():
            dep_name = dep.replace("/", ".")
            recorded.append([f"{dep_name} transitive imports (legacy)", "00000000000006bb"])
            recorded.append([f"{dep_name}:importAllArts", import_hash])
        trace: dict[str, object] = {
            "synthetic": False,
            "schemaVersion": "2025-09-10",
            "outputs": outputs,
            "log": [],
            "inputs": [
                ["deps", [["Pkg/Lib:extraDep", [["@Pkg:extraDep", "00000000000006bb"]]], ["imports", recorded]]],
                [f"/some/worktree/src/{rel_mod}.lean", "ad651cc2b3431caa"],
            ],
            "depHash": "56989c8629fa0281",
        }
        if fetched:
            trace = {
                "synthetic": True,
                "schemaVersion": "2025-09-10",
                "outputs": outputs,
                "log": [],
                "inputs": [],
                "depHash": "cca9185a3f3ac0e6",
            }
        files[".trace"] = self._write_file_at(
            lib_dir / f"{rel_mod}.trace", json.dumps(trace, indent=1).encode("utf-8"), built_at
        )
        return files

    @staticmethod
    def _classic_import_all_arts(olean_hash: str) -> str:
        return f"{suite._lake_mix_hash(suite._LAKE_HASH_NIL, int(olean_hash, 16)):016x}"

    def test_clean_stale_oleans_import_hash_rule_matches_lake_for_module_system_imports(self) -> None:
        # Lake mixes five artifact hashes into the `importAllArts` trace of a module-system
        # dependency (`.olean`, `.olean.server`, `.olean.private`, `.ir.sig`, `.ir`) and one
        # for a classic module. Mixing only the three `.olean` parts disagrees with every
        # trace Lake writes for an importer of a `module` file, which made the guard delete
        # that importer, and everything Lake had built on top of it, on every single run.
        t_dep, t_importer, t_top = 1_700_000_000.0, 1_700_000_100.0, 1_700_000_200.0
        mod_a_hashes = self._LAKE_MODULE_SYSTEM_PART_HASHES
        importer_olean, top_olean = "5555555555555555", "6666666666666666"

        def build(root: Path) -> dict[str, dict[str, Path]]:
            lib = root / "examples/.lake/build/lib/lean"
            return {
                "ModA": self._write_lake_module_with_hashes(lib, "Miri/ModA", mod_a_hashes, t_dep),
                "PlainB": self._write_lake_module_with_hashes(
                    lib, "Miri/PlainB", self._LAKE_CLASSIC_PART_HASHES, t_dep
                ),
                "Importer": self._write_lake_module_with_hashes(
                    lib,
                    "Miri/Importer",
                    {".olean": importer_olean},
                    t_importer,
                    imports={
                        "Miri/ModA": self._LAKE_MODULE_SYSTEM_IMPORT_ALL_ARTS,
                        "Miri/PlainB": self._LAKE_CLASSIC_IMPORT_ALL_ARTS,
                    },
                ),
                "Top": self._write_lake_module_with_hashes(
                    lib,
                    "Miri/Top",
                    {".olean": top_olean},
                    t_top,
                    imports={"Miri/Importer": self._classic_import_all_arts(importer_olean)},
                ),
            }

        def rerecord(files: dict[str, Path], suffix: str, content_hash: str, ts_sec: float) -> None:
            self._write_file_at(files[f"{suffix}.hash"], content_hash.encode("ascii"), ts_sec)

        def scanned(root: Path, mod: str) -> dict[str, str]:
            return suite._scan_lean_module_artifacts(os.fspath(root / "examples/.lake/build/lib/lean"))[mod]

        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            built = build(root)
            # The formula reproduces what Lake recorded, for both kinds of module.
            self.assertEqual(
                suite._lean_module_current_import_all_arts_hex(scanned(root, "Miri/ModA")),
                self._LAKE_MODULE_SYSTEM_IMPORT_ALL_ARTS,
            )
            self.assertEqual(
                suite._lean_module_current_import_all_arts_hex(scanned(root, "Miri/PlainB")),
                self._LAKE_CLASSIC_IMPORT_ALL_ARTS,
            )
            # A freshly built tree is coherent, and deciding so needs no sidecar content:
            # nothing was recorded after the traces that depend on it.
            with mock.patch.object(
                suite, "_lean_module_current_import_all_arts_hex", side_effect=AssertionError("sidecar read")
            ):
                self.assertEqual(suite.clean_stale_oleans(root), [])
            # Lake rewrites a `.hash` sidecar whenever the artifact looks newer than it. The
            # same hashes recorded again later are not a rebuild.
            for suffix, content_hash in mod_a_hashes.items():
                rerecord(built["ModA"], suffix, content_hash, t_top + 100)
            rerecord(built["PlainB"], ".olean", self._LAKE_CLASSIC_PART_HASHES[".olean"], t_top + 100)
            self.assertEqual(suite.clean_stale_oleans(root), [])
            self.assertTrue(all(p.is_file() for files in built.values() for p in files.values()))

        # A rebuild of the module-system dependency that changes any one of the five parts
        # (here each in turn, the `.olean` itself staying identical for four of them)
        # invalidates the importer Lake built against the old ones, and what was built on it.
        for suffix in mod_a_hashes:
            with self.subTest(rebuilt_part=suffix), tempfile.TemporaryDirectory() as tmp:
                root = Path(tmp)
                built = build(root)
                rerecord(built["ModA"], suffix, "abcdefabcdefabcd", t_top + 100)
                self.assertEqual(
                    set(suite.clean_stale_oleans(root)),
                    set(built["Importer"].values()) | set(built["Top"].values()),
                )
                self.assertTrue(all(p.is_file() for mod in ("ModA", "PlainB") for p in built[mod].values()))
                self.assertEqual(suite.clean_stale_oleans(root), [])

        # A dependency whose files do not let its hash be verified is no evidence at all.
        def drop_ir_sidecar(files: dict[str, Path]) -> None:
            files[".ir.hash"].unlink()

        def drop_ir(files: dict[str, Path]) -> None:
            files[".ir"].unlink()
            files[".ir.hash"].unlink()

        def link_sidecar(files: dict[str, Path]) -> None:
            os.link(files[".olean.hash"], files[".olean.hash"].with_name("ModA.olean.hash.seed"))

        def garble_sidecar(files: dict[str, Path]) -> None:
            rerecord(files, ".olean.server", "not-a-lake-hash!", t_top + 100)

        def outdate_sidecar(files: dict[str, Path]) -> None:
            os.utime(files[".olean.private"], (t_top + 200, t_top + 200))

        for unverifiable in (drop_ir_sidecar, drop_ir, link_sidecar, garble_sidecar, outdate_sidecar):
            with self.subTest(unverifiable=unverifiable.__name__), tempfile.TemporaryDirectory() as tmp:
                root = Path(tmp)
                built = build(root)
                rerecord(built["ModA"], ".olean", "abcdefabcdefabcd", t_top + 100)
                unverifiable(built["ModA"])
                self.assertIsNone(suite._lean_module_current_import_all_arts_hex(scanned(root, "Miri/ModA")))
                self.assertEqual(suite.clean_stale_oleans(root), [])

    def test_clean_stale_oleans_import_hash_rule_needs_a_private_build_trace_and_a_later_rebuild(self) -> None:
        t_dep, t_importer, t_top, t_rebuild = (
            1_700_000_000.0,
            1_700_000_100.0,
            1_700_000_200.0,
            1_700_000_300.0,
        )
        dep_h1, dep_h2, importer_olean, top_olean = (
            "1111111111111111",
            "2222222222222222",
            "5555555555555555",
            "6666666666666666",
        )

        def build(root: Path, *, importer_fetched: bool = False, recorded_dep: str = dep_h1):
            lib = root / ".lake/build/lib/lean"
            return {
                "Dep": self._write_lake_module_with_hashes(lib, "Anneal/Dep", {".olean": dep_h1}, t_dep),
                "Importer": self._write_lake_module_with_hashes(
                    lib,
                    "Anneal/Importer",
                    {".olean": importer_olean},
                    t_importer,
                    imports={
                        "Anneal/Dep": self._classic_import_all_arts(recorded_dep),
                        # Recorded imports this Lake root does not hold are not its business.
                        "Init/Prelude": "0123456789abcdef",
                    },
                    fetched=importer_fetched,
                ),
                "Top": self._write_lake_module_with_hashes(
                    lib,
                    "Anneal/Top",
                    {".olean": top_olean},
                    t_top,
                    imports={"Anneal/Importer": self._classic_import_all_arts(importer_olean)},
                ),
            }

        def rebuild_dep(built: dict[str, dict[str, Path]]) -> None:
            self._write_file_at(built["Dep"][".olean"], b"artifact 2", t_rebuild)
            self._write_file_at(built["Dep"][".olean.hash"], dep_h2.encode("ascii"), t_rebuild)

        def all_files(built: dict[str, dict[str, Path]]) -> set[Path]:
            return {p for files in built.values() for p in files.values()}

        # Baseline: the dependency is rebuilt after its importer, which then goes, with `Top`.
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            built = build(root)
            rebuild_dep(built)
            self.assertEqual(
                set(suite.clean_stale_oleans(root)),
                set(built["Importer"].values()) | set(built["Top"].values()),
            )

        # A recorded hash that disagrees with a dependency nobody touched since the trace
        # was written is not a rebuild. (This is what every trace looks like once a Lake
        # release changes what it mixes into `importAllArts`.)
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            built = build(root, recorded_dep="9999999999999999")
            self.assertEqual(suite.clean_stale_oleans(root), [])
            self.assertTrue(all(p.is_file() for p in all_files(built)))

        # A module Lake restored from its cache has a synthetic trace naming no import:
        # rule 3 has no evidence about it, and does not cascade through it either.
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            built = build(root, importer_fetched=True)
            rebuild_dep(built)
            self.assertEqual(suite.clean_stale_oleans(root), [])
            self.assertTrue(all(p.is_file() for p in all_files(built)))

        # Only a private regular `.trace` is evidence: not one another tree can rewrite
        # through a second hard link, not a symlink, not a FIFO (which must not block the
        # suite either), and not one that is no JSON.
        def link_trace(trace: Path) -> None:
            os.link(trace, trace.with_name("Importer.trace.seed"))

        def symlink_trace(trace: Path) -> None:
            target = trace.with_name("Importer.trace.real")
            trace.rename(target)
            trace.symlink_to(target)

        def fifo_trace(trace: Path) -> None:
            trace.unlink()
            os.mkfifo(trace)

        def truncate_trace(trace: Path) -> None:
            self._write_file_at(trace, trace.read_bytes()[:-2], t_importer)

        for tamper in (link_trace, symlink_trace, fifo_trace, truncate_trace):
            with self.subTest(trace=tamper.__name__), tempfile.TemporaryDirectory() as tmp:
                root = Path(tmp)
                built = build(root)
                rebuild_dep(built)
                tamper(built["Importer"][".trace"])
                self.assertEqual(suite.clean_stale_oleans(root), [])
                self.assertTrue(all(os.path.lexists(p) for p in all_files(built)))

    def test_clean_stale_oleans_import_hash_rule_reaches_trusted_dependents(self) -> None:
        # `Trusted/Leaf` is rebuilt (say by a build of that one module) after `Trusted/Mid`
        # was built against the old one. Every source is older than its `.olean`, so only
        # the recorded import hashes show it. `Trusted/Mid` is then stale, and with a stale
        # `Trusted` module so is everything of the root that can import `Trusted`, whatever
        # trace it has; vendored `Miri` cannot.
        t_built, t_rebuild = 1_700_000_000.0, 1_700_000_500.0
        leaf_h1, leaf_h2, mid_h = "1111111111111111", "2222222222222222", "3333333333333333"
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            lib = root / ".lake/build/lib/lean"
            leaf = self._write_lake_module_with_hashes(lib, "Trusted/Leaf", {".olean": leaf_h1}, t_built)
            mid = self._write_lake_module_with_hashes(
                lib,
                "Trusted/Mid",
                {".olean": mid_h},
                t_built + 10,
                imports={"Trusted/Leaf": self._classic_import_all_arts(leaf_h1)},
            )
            fetched = self._write_lake_module_with_hashes(
                lib, "Anneal/Fetched", {".olean": "4444444444444444"}, t_built + 20, fetched=True
            )
            bare = self._write_file_at(lib / "MiniRust/Bare.olean", b"artifact", t_built + 20)
            miri = self._write_lake_module_with_hashes(
                lib, "Miri/Keep", {".olean": "7777777777777777"}, t_built + 20
            )
            self.assertEqual(suite.clean_stale_oleans(root), [])
            self._write_file_at(leaf[".olean"], b"artifact 2", t_rebuild)
            self._write_file_at(leaf[".olean.hash"], leaf_h2.encode("ascii"), t_rebuild)
            self.assertEqual(
                set(suite.clean_stale_oleans(root)),
                set(leaf.values()) | set(mid.values()) | set(fetched.values()) | {bare},
            )
            self.assertTrue(all(p.is_file() for p in miri.values()))
            self.assertEqual(suite.clean_stale_oleans(root), [])

    def test_clean_stale_oleans_removes_module_with_missing_local_dependency(self) -> None:
        # Regression: a build trace in `<lake_root>/.lake/build/lib/lean/` recording a direct
        # import of a local workspace library whose `.olean` is absent (e.g. a leftover
        # downstream `.olean` after a prior partial clean or another branch's build) must be
        # removed along with its transitive importers, while missing stdlib (`Init.*`) entries
        # are never treated as stale.
        t_built = 1_700_000_000.0
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "lakefile.toml").write_text(
                '[[lean_lib]]\nname = "Trusted"\nsrcDir = "trusted/lean"\n'
                '[[lean_lib]]\nname = "Anneal"\nsrcDir = "theory"\n',
                encoding="utf-8",
            )
            lib = root / ".lake/build/lib/lean"
            zombie = self._write_lake_module_with_hashes(
                lib,
                "Anneal/MirFuelFree",
                {".olean": "1111111111111111"},
                t_built,
                imports={
                    "Anneal/Lower": "2222222222222222",
                    "Init/Prelude": "3333333333333333",
                },
            )
            top = self._write_lake_module_with_hashes(
                lib,
                "Anneal/Top",
                {".olean": "4444444444444444"},
                t_built + 10,
                imports={"Anneal/MirFuelFree": self._classic_import_all_arts("1111111111111111")},
            )
            stdlib_only = self._write_lake_module_with_hashes(
                lib,
                "Anneal/Keep",
                {".olean": "5555555555555555"},
                t_built + 10,
                imports={"Init/Prelude": "3333333333333333"},
            )
            removed = set(suite.clean_stale_oleans(root))
            self.assertEqual(removed, set(zombie.values()) | set(top.values()))
            self.assertTrue(all(p.is_file() for p in stdlib_only.values()))
            self.assertEqual(suite.clean_stale_oleans(root), [])

        # Same check without `lakefile.toml` (source-tree fallback) and with a torn dependency
        # (only `.ilean`, missing `.olean`).
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            self._write_file_at(root / "theory/Anneal/Lower.lean", b"def x := 1\n", t_built - 100)
            lib = root / ".lake/build/lib/lean"
            torn_ilean = self._write_file_at(lib / "Anneal/Lower.ilean", b"{}", t_built)
            zombie = self._write_lake_module_with_hashes(
                lib,
                "Anneal/Consumer",
                {".olean": "6666666666666666"},
                t_built + 10,
                imports={"Anneal/Lower": "7777777777777777"},
            )
            self.assertEqual(set(suite.clean_stale_oleans(root)), set(zombie.values()))
            self.assertTrue(torn_ilean.is_file())

    def test_read_private_regular_file_handles_short_reads_growth_and_rule1_fifo(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            sample = root / "trace.json"
            payload = b"0123456789abcdef"
            sample.write_bytes(payload)

            # POSIX short read: multiple chunks assembling `expected` bytes succeed.
            real_read = os.read
            reads: list[int] = []

            def chunked_read(fd: int, n: int) -> bytes:
                reads.append(n)
                return real_read(fd, min(n, 4))

            with mock.patch("os.read", side_effect=chunked_read):
                got = suite._read_private_regular_file(os.fspath(sample))
            self.assertIsNotNone(got)
            assert got is not None
            self.assertEqual(got[0], payload)
            self.assertGreaterEqual(len(reads), 4)

            # Concurrent growth past `st_size` is detected and rejected rather than truncated.
            appended = False

            def growing_read(fd: int, n: int) -> bytes:
                nonlocal appended
                if not appended:
                    appended = True
                    with open(sample, "ab") as fh:
                        fh.write(b"EXTRA")
                return real_read(fd, n)

            with mock.patch("os.read", side_effect=growing_read):
                self.assertIsNone(suite._read_private_regular_file(os.fspath(sample)))

            # Rule 1 (`_lake_records_prove_source_unchanged`) never blocks on a FIFO `.trace`
            # or `.olean.hash`.
            t_old, t_new = 1_700_000_000.0, 1_700_000_200.0
            src = self._write_file_at(root / "theory/Anneal/Fifo.lean", b"def f := 1\n", t_new)
            lib = root / ".lake/build/lib/lean/Anneal"
            lib.mkdir(parents=True)
            olean = self._write_file_at(lib / "Fifo.olean", b"art", t_old)
            fifo_trace = lib / "Fifo.trace"
            os.mkfifo(fifo_trace)
            self.assertFalse(
                suite._lake_records_prove_source_unchanged(
                    "Anneal/Fifo",
                    {".olean": os.fspath(olean), ".trace": os.fspath(fifo_trace)},
                    os.fspath(src),
                    os.stat(src).st_mtime_ns,
                )
            )

    def test_probe_ram_ceiling_honors_cgroup_v2_memory_high_and_rejects_escapes(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            meminfo = root / "meminfo"
            meminfo.write_text(
                "MemTotal:       67108864 kB\nMemAvailable:   52428800 kB\n",
                encoding="utf-8",
            )
            cg_root = root / "cgroup"
            leaf = cg_root / "user.slice/anneal.scope"
            leaf.mkdir(parents=True)
            (cg_root / "memory.max").write_text("max\n", encoding="utf-8")
            (cg_root / "user.slice/memory.max").write_text("max\n", encoding="utf-8")
            (leaf / "memory.max").write_text("max\n", encoding="utf-8")
            (leaf / "memory.high").write_text(str(6144 * 1024 * 1024) + "\n", encoding="utf-8")
            proc_cg = root / "proc_cg"
            proc_cg.write_text("0::/user.slice/anneal.scope\n", encoding="utf-8")
            self.assertEqual(
                suite._probe_effective_ram_ceiling_mib(
                    proc_meminfo=meminfo, proc_self_cgroup=proc_cg, cgroup_root=cg_root
                ),
                6144,
            )

            # Symlink escape, NUL byte in cgroup path, and FIFO `memory.max` are safely ignored.
            outside = root / "outside"
            outside.mkdir()
            (outside / "memory.max").write_text(str(128 * 1024 * 1024) + "\n", encoding="utf-8")
            (cg_root / "escape").symlink_to(outside)
            self.assertIsNone(suite._safe_cgroup_subpath(cg_root, "/escape"))
            self.assertIsNone(suite._safe_cgroup_subpath(cg_root, "/user.slice/\x00bad"))
            fifo_lim = leaf / "memory.fifo"
            os.mkfifo(fifo_lim)
            self.assertIsNone(suite._parse_cgroup_memory_limit_mib(fifo_lim))
            link_lim = leaf / "memory.link"
            link_lim.symlink_to(outside / "memory.max")
            self.assertIsNone(suite._parse_cgroup_memory_limit_mib(link_lim))

    def test_probe_ram_ceiling_and_lean_miri_spec_single_thread_right_sizing(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            meminfo_64g = root / "meminfo_64g"
            meminfo_64g.write_text(
                "MemTotal:       67108864 kB\nMemAvailable:   52428800 kB\n",
                encoding="utf-8",
            )
            meminfo_8g = root / "meminfo_8g"
            meminfo_8g.write_text(
                "MemTotal:        8388608 kB\nMemAvailable:    6291456 kB\n",
                encoding="utf-8",
            )
            cg_root = root / "cgroup"
            leaf = cg_root / "user.slice/user-1000.slice/anneal.scope"
            leaf.mkdir(parents=True)
            proc_cg = root / "proc_self_cgroup"
            proc_cg.write_text("0::/user.slice/user-1000.slice/anneal.scope\n", encoding="utf-8")

            # Unbounded `"max"` across the hierarchy falls back to `/proc/meminfo`.
            (cg_root / "memory.max").write_text("max\n", encoding="utf-8")
            (cg_root / "user.slice/memory.max").write_text("max\n", encoding="utf-8")
            (leaf / "memory.max").write_text("max\n", encoding="utf-8")
            self.assertEqual(
                suite._probe_effective_ram_ceiling_mib(
                    proc_meminfo=meminfo_64g, proc_self_cgroup=proc_cg, cgroup_root=cg_root
                ),
                51200,
            )
            self.assertEqual(
                suite._probe_effective_ram_ceiling_mib(
                    proc_meminfo=meminfo_8g, proc_self_cgroup=proc_cg, cgroup_root=cg_root
                ),
                6144,
            )

            # Ancestor cgroup v2 `memory.max` (`5712 MiB` capsule cap) tightens host 64 GiB.
            (cg_root / "user.slice/memory.max").write_text(
                str(5712 * 1024 * 1024) + "\n", encoding="utf-8"
            )
            self.assertEqual(
                suite._probe_effective_ram_ceiling_mib(
                    proc_meminfo=meminfo_64g, proc_self_cgroup=proc_cg, cgroup_root=cg_root
                ),
                5712,
            )

            # Missing files yield `None` cleanly (no exception).
            self.assertIsNone(
                suite._probe_effective_ram_ceiling_mib(
                    proc_meminfo=root / "nope", proc_self_cgroup=root / "nope2", cgroup_root=root / "nope3"
                )
            )

        # `lake_build_lean_miri_spec` sets `LEAN_NUM_THREADS=1` iff ceiling < 10240 MiB.
        low_env = suite._build_step_env(
            "lake_build_lean_miri_spec",
            base_env={"PATH": "/usr/bin", "LEAN_NUM_THREADS": "4"},
            effective_ram_mib=5712,
        )
        self.assertEqual(low_env["LEAN_NUM_THREADS"], "1")

        boundary_low = suite._build_step_env(
            "lake_build_lean_miri_spec",
            base_env={"PATH": "/usr/bin"},
            effective_ram_mib=10239,
        )
        self.assertEqual(boundary_low["LEAN_NUM_THREADS"], "1")

        boundary_high = suite._build_step_env(
            "lake_build_lean_miri_spec",
            base_env={"PATH": "/usr/bin"},
            effective_ram_mib=10240,
        )
        self.assertNotIn("LEAN_NUM_THREADS", boundary_high)

        high_preserve = suite._build_step_env(
            "lake_build_lean_miri_spec",
            base_env={"PATH": "/usr/bin", "LEAN_NUM_THREADS": "4"},
            effective_ram_mib=32768,
        )
        self.assertEqual(high_preserve["LEAN_NUM_THREADS"], "4")

        # `lake_build_minirust_spec` follows the same threshold.
        for ram_mib, expected in ((5712, "1"), (10239, "1"), (10240, "4"), (32768, "4")):
            minirust_env = suite._build_step_env(
                "lake_build_minirust_spec",
                base_env={"PATH": "/usr/bin", "LEAN_NUM_THREADS": "4"},
                effective_ram_mib=ram_mib,
            )
            self.assertEqual(minirust_env["LEAN_NUM_THREADS"], expected, ram_mib)

        # Other steps are unaffected even under `< 10240 MiB`, including the vendored
        # `Miri` build that precedes `lake_build_lean_miri_spec`.
        for other_step in ("lake_build_core_theory", "lake_build_examples_miri_vendor", "lake_build_correspondence"):
            other_low = suite._build_step_env(
                other_step,
                base_env={"PATH": "/usr/bin", "LEAN_NUM_THREADS": "4"},
                effective_ram_mib=5712,
            )
            self.assertEqual(other_low["LEAN_NUM_THREADS"], "4", other_step)
            self.assertNotIn(
                "LEAN_NUM_THREADS",
                suite._build_step_env(other_step, base_env={"PATH": "/usr/bin"}, effective_ram_mib=5712),
                other_step,
            )

    def test_lean_miri_spec_right_sizing_honors_wrapper_planned_memory_max(self) -> None:
        # `anneal-lean-run` runs the step in its own scope with `MemoryMax=<memory_max_mb>M`
        # (5712M on an 8 GiB capsule). The suite process is outside that scope, so on a host
        # whose own RAM looks ample only the wrapper's `--probe --json` reveals the cap.
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            wrapper = root / "bin/anneal-lean-run"
            argv_log = root / "argv.jsonl"
            reply = root / "reply.txt"
            wrapper.parent.mkdir()
            wrapper.write_text(
                textwrap.dedent(
                    f"""\
                    #!{sys.executable}
                    import json, os, sys
                    args = sys.argv[1:]
                    with open({str(argv_log)!r}, "a", encoding="utf-8") as fh:
                        fh.write(json.dumps(args) + "\\n")
                    if "--probe" in args:
                        reply = open({str(reply)!r}, encoding="utf-8").read()
                        if reply.startswith("exit:"):
                            sys.exit(int(reply[5:]))
                        sys.stdout.write(reply)
                        sys.exit(0)
                    cmd = args[args.index("--") + 1:]
                    os.execvp(cmd[0], cmd)
                    """
                ),
                encoding="utf-8",
            )
            wrapper.chmod(0o755)
            argv_log.write_text("", encoding="utf-8")

            def probes() -> list[list[str]]:
                return [json.loads(line) for line in argv_log.read_text(encoding="utf-8").splitlines()]

            step_cmd = [
                str(wrapper),
                "--mode",
                "build",
                "--concurrency",
                "1",
                "--timeout",
                "1800",
                "--",
                "lake",
                "--dir",
                "examples",
                "build",
                "LeanMiriSpec",
            ]
            # The probe forwards exactly the wrapper's own options, pins the mode the wrapper
            # resolves for the real command, and never forwards the command itself.
            reply.write_text(json.dumps({"memory_max_mb": 5712, "threads": 8}), encoding="utf-8")
            self.assertEqual(suite._probe_lean_run_memory_max_mib(step_cmd), 5712)
            self.assertEqual(
                probes(),
                [
                    [
                        "--mode",
                        "build",
                        "--concurrency",
                        "1",
                        "--timeout",
                        "1800",
                        "--mode",
                        "build",
                        "--probe",
                        "--json",
                    ]
                ],
            )
            joined = [str(wrapper), "--mode=build", "--time", "60", "--no-slot-lock", "lake", "build"]
            self.assertEqual(suite._probe_lean_run_memory_max_mib(joined), 5712)
            self.assertEqual(
                probes()[-1],
                ["--mode=build", "--time", "60", "--no-slot-lock", "--mode", "build", "--probe", "--json"],
            )
            # Without the command, the wrapper's `auto` mode resolves to `build`: a wrapper
            # that will run its command in `file` mode (lower `MemoryMax`) must be probed
            # in `file` mode, whether `--mode` is omitted, `auto`, or abbreviated.
            for wrapper_opts, inner, want_mode in (
                ([], ["lake", "env", "lean", "tests/mir/X.lean"], "file"),
                (["--mode", "auto"], ["lean", "X.lean"], "file"),
                (
                    ["--mode=auto", "--timeout", "300"],
                    ["--", "lake", "--dir", "examples", "env", "lean", "X.lean"],
                    "file",
                ),
                (["--mod", "auto"], ["lake", "env", "lean", "--run", "X.lean"], "build"),
                ([], ["lake", "build", "MiniRustSpec"], "build"),
                (["--mode", "file"], ["lake", "build", "MiniRustSpec"], "file"),
                (["--mode", "build"], ["lean", "X.lean"], "build"),
            ):
                auto_cmd = [str(wrapper), *wrapper_opts, *inner]
                self.assertEqual(suite._probe_lean_run_memory_max_mib(auto_cmd), 5712, auto_cmd)
                self.assertEqual(
                    probes()[-1], [*wrapper_opts, "--mode", want_mode, "--probe", "--json"], auto_cmd
                )
            # Anything but a positive integer `memory_max_mb` from a successful probe is no answer.
            for bad in (
                "exit:3",
                "not json",
                "[]",
                json.dumps({"threads": 4}),
                json.dumps({"memory_max_mb": "5712"}),
                json.dumps({"memory_max_mb": 0}),
                json.dumps({"memory_max_mb": True}),
                json.dumps({"memory_max_mb": 5712.5}),
            ):
                reply.write_text(bad, encoding="utf-8")
                self.assertIsNone(suite._probe_lean_run_memory_max_mib(step_cmd), bad)
            self.assertIsNone(suite._probe_lean_run_memory_max_mib(["lake", "build", "LeanMiriSpec"]))
            self.assertIsNone(
                suite._probe_lean_run_memory_max_mib([str(root / "missing/anneal-lean-run"), "--", "lake"])
            )

            def threads(step: str, cmd: list[str] | None, **kwargs: object) -> str | None:
                env = suite._build_step_env(step, base_env={"PATH": "/usr/bin"}, cmd=cmd, cwd=root, **kwargs)
                return env.get("LEAN_NUM_THREADS")

            with mock.patch.object(suite, "_probe_effective_ram_ceiling_mib", return_value=65536):
                reply.write_text(json.dumps({"memory_max_mb": 5712}), encoding="utf-8")
                self.assertEqual(threads("lake_build_lean_miri_spec", step_cmd), "1")
                reply.write_text(json.dumps({"memory_max_mb": 10239}), encoding="utf-8")
                self.assertEqual(threads("lake_build_lean_miri_spec", step_cmd), "1")
                reply.write_text(json.dumps({"memory_max_mb": 10240}), encoding="utf-8")
                self.assertIsNone(threads("lake_build_lean_miri_spec", step_cmd))
                # A failed wrapper probe falls back to the host/cgroup ceiling alone.
                reply.write_text("exit:3", encoding="utf-8")
                self.assertIsNone(threads("lake_build_lean_miri_spec", step_cmd))
                # Neither an unwrapped command, another step, nor an explicit ceiling asks the wrapper.
                reply.write_text(json.dumps({"memory_max_mb": 5712}), encoding="utf-8")
                asked = len(probes())
                self.assertIsNone(threads("lake_build_lean_miri_spec", ["lake", "build", "LeanMiriSpec"]))
                self.assertIsNone(threads("lake_build_lean_miri_spec", None))
                self.assertIsNone(threads("lake_build_core_theory", step_cmd))
                self.assertIsNone(threads("lake_build_examples_miri_vendor", step_cmd))
                self.assertIsNone(threads("lake_build_correspondence", step_cmd))
                self.assertIsNone(threads("lake_build_lean_miri_spec", step_cmd, effective_ram_mib=32768))
                self.assertIsNone(threads("lake_build_lean_miri_spec", step_cmd, effective_ram_mib=None))
                self.assertEqual(len(probes()), asked)
                # `lake_build_minirust_spec` asks its wrapper exactly like `lake_build_lean_miri_spec`.
                self.assertEqual(threads("lake_build_minirust_spec", step_cmd), "1")
                self.assertEqual(len(probes()), asked + 1)
                reply.write_text(json.dumps({"memory_max_mb": 10240}), encoding="utf-8")
                self.assertIsNone(threads("lake_build_minirust_spec", step_cmd))
            # The tightest ceiling wins in either direction, and an unreadable host probe
            # still leaves the wrapper's answer.
            reply.write_text(json.dumps({"memory_max_mb": 157253}), encoding="utf-8")
            with mock.patch.object(suite, "_probe_effective_ram_ceiling_mib", return_value=5712):
                self.assertEqual(threads("lake_build_lean_miri_spec", step_cmd), "1")
            with mock.patch.object(suite, "_probe_effective_ram_ceiling_mib", return_value=None):
                self.assertIsNone(threads("lake_build_lean_miri_spec", step_cmd))
                reply.write_text(json.dumps({"memory_max_mb": 5712}), encoding="utf-8")
                self.assertEqual(threads("lake_build_lean_miri_spec", step_cmd), "1")

            # End to end: `_run_step` hands the wrapped step `LEAN_NUM_THREADS=1` exactly when
            # the wrapper's planned cap is below 10 GiB.
            out_file = root / "threads.txt"
            dump = (
                "import os, pathlib; "
                f"pathlib.Path({str(out_file)!r}).write_text(os.environ.get('LEAN_NUM_THREADS', '<unset>'))"
            )
            run_cmd = [str(wrapper), "--mode", "build", "--timeout", "30", "--", sys.executable, "-c", dump]
            for mem_max_mb, expected in ((5712, "1"), (157253, "7")):
                reply.write_text(json.dumps({"memory_max_mb": mem_max_mb}), encoding="utf-8")
                with (
                    mock.patch.object(suite, "_probe_effective_ram_ceiling_mib", return_value=65536),
                    mock.patch.dict(os.environ, {"LEAN_NUM_THREADS": "7"}),
                ):
                    res = suite._run_step(
                        name="lake_build_lean_miri_spec",
                        category="cat2_correspondence_suites",
                        cmd=run_cmd,
                        cwd=root,
                        timeout_sec=30,
                    )
                self.assertEqual(res["status"], "PASS", res.get("failure_excerpt"))
                self.assertEqual(out_file.read_text(encoding="utf-8"), expected)

    def test_probe_lean_run_reconciles_multi_slot_concurrency_and_skips_non_exec_flags(self) -> None:
        # 1. On a multi-slot host (`build_slots > cli_concurrency`), `anneal-lean-run --probe`
        #    evaluates at `--concurrency 1` while actual execution raises `w_eff` to
        #    `build_slots` (unless `--exclusive`). `_probe_lean_run_memory_max_mib` must
        #    re-probe at `build_slots` so `< 10 GiB` per-slot caps still trigger
        #    `LEAN_NUM_THREADS=1` for `LOW_RAM_SINGLE_THREAD_STEPS`.
        # 2. Non-executing / mutating wrapper flags (`--ensure-slice`, `--ensure`, `--probe`,
        #    `--print-limits`, `-h`, `--help`) must return `None` without spawning the wrapper.
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            wrapper = root / "bin/anneal-lean-run"
            argv_log = root / "argv.jsonl"
            wrapper.parent.mkdir()
            wrapper.write_text(
                textwrap.dedent(
                    f"""\
                    #!{sys.executable}
                    import json, os, sys
                    args = sys.argv[1:]
                    with open({str(argv_log)!r}, "a", encoding="utf-8") as fh:
                        fh.write(json.dumps(args) + "\\n")
                    # Simulate a 3-slot host (~24 GiB live pool): w_eff=1 -> 21600 MiB (>= 10 GiB),
                    # w_eff=3 -> 7200 MiB (< 10 GiB). Last `--concurrency` wins as in argparse.
                    conc = 3
                    i = 0
                    while i < len(args):
                        if args[i] == "--concurrency" and i + 1 < len(args):
                            conc = int(args[i + 1])
                            i += 2
                            continue
                        if args[i].startswith("--concurrency="):
                            conc = int(args[i].split("=", 1)[1])
                        i += 1
                    if os.environ.get("FAIL_REPROBE") == "1" and conc == 3:
                        sys.exit(2)
                    sys.stdout.write(json.dumps({{
                        "memory_max_mb": 21600 // conc,
                        "w_eff": conc,
                        "build_slots": 3,
                    }}))
                    """
                ),
                encoding="utf-8",
            )
            wrapper.chmod(0o755)
            argv_log.write_text("", encoding="utf-8")

            def probes() -> list[list[str]]:
                return [json.loads(line) for line in argv_log.read_text(encoding="utf-8").splitlines()]

            # Non-executing / mutating flags, `-h...` clusters, and empty inner commands never spawn the wrapper.
            for non_exec in (
                [str(wrapper)],
                [str(wrapper), "--mode", "build"],
                [str(wrapper), "--mode", "build", "--"],
                [str(wrapper), "--ensure-slice"],
                [str(wrapper), "--ensure", "--", "lake", "build"],
                [str(wrapper), "--probe", "--json"],
                [str(wrapper), "--print-limits"],
                [str(wrapper), "-h"],
                [str(wrapper), "-hW1", "--", "lake", "build"],
                [str(wrapper), "--help"],
            ):
                self.assertIsNone(suite._probe_lean_run_memory_max_mib(non_exec), non_exec)
            self.assertEqual(probes(), [])
            # A `--help` after `--` belongs to the wrapped command, not the wrapper.
            self.assertEqual(
                suite._probe_lean_run_memory_max_mib(
                    [str(wrapper), "--mode", "build", "--concurrency", "3", "--", "lake", "--help"]
                ),
                7200,
            )
            self.assertEqual(len(probes()), 1)

            # `--concurrency 1` without `--exclusive` re-probes at `build_slots=3` -> 7200 MiB.
            step_cmd = [
                str(wrapper),
                "--mode",
                "build",
                "--concurrency",
                "1",
                "--timeout",
                "1800",
                "--",
                "lake",
                "--dir",
                "examples",
                "build",
                "LeanMiriSpec",
            ]
            before = len(probes())
            self.assertEqual(suite._probe_lean_run_memory_max_mib(step_cmd), 7200)
            new_probes = probes()[before:]
            self.assertEqual(len(new_probes), 2)
            self.assertEqual(new_probes[1][-4:], ["--concurrency", "3", "--probe", "--json"])

            with mock.patch.object(suite, "_probe_effective_ram_ceiling_mib", return_value=32768):
                for step_name in ("lake_build_minirust_spec", "lake_build_lean_miri_spec"):
                    env = suite._build_step_env(
                        step_name, base_env={"PATH": "/usr/bin"}, cmd=step_cmd, cwd=root
                    )
                    self.assertEqual(env.get("LEAN_NUM_THREADS"), "1", step_name)
                # A failed re-probe fails closed: neither the inflated 21600 MiB cap of the
                # first probe nor `None` (which would leave only the 32 GiB host ceiling and
                # keep the step multi-threaded), but the per-slot lower bound 21600 * 1 // 3.
                self.assertEqual(
                    suite._probe_lean_run_memory_max_mib(step_cmd, env={"FAIL_REPROBE": "1"}),
                    7200,
                )
                for step_name in ("lake_build_minirust_spec", "lake_build_lean_miri_spec"):
                    env = suite._build_step_env(
                        step_name,
                        base_env={"PATH": "/usr/bin", "FAIL_REPROBE": "1"},
                        cmd=step_cmd,
                        cwd=root,
                    )
                    self.assertEqual(env.get("LEAN_NUM_THREADS"), "1", step_name)
                # With `--exclusive`, execution stays at `w_eff=1` (21600 MiB >= 10 GiB):
                # even an older wrapper that reports `w_eff=3` on `--exclusive --concurrency 3`
                # re-probes to `w_eff=1` (21600 MiB) and skips single-threading.
                excl_cmd = [
                    str(wrapper),
                    "--mode",
                    "build",
                    "--exclusive",
                    "--concurrency",
                    "3",
                    "--",
                    "lake",
                    "build",
                    "MiniRustSpec",
                ]
                self.assertEqual(suite._probe_lean_run_memory_max_mib(excl_cmd), 21600)
                excl_env = suite._build_step_env(
                    "lake_build_minirust_spec", base_env={"PATH": "/usr/bin"}, cmd=excl_cmd, cwd=root
                )
                self.assertNotIn("LEAN_NUM_THREADS", excl_env)

            # End-to-end against real `scripts/anneal-lean-run` on a synthetic 3-slot host
            # (`w_file=3`, 24 GiB host RAM -> 18 GiB slice: w_eff=1 gives 16.2 GiB >= 10 GiB,
            # while runtime w_eff=3 gives 5.4 GiB < 10 GiB).
            xdg = root / "xdg"
            (xdg / "anneal").mkdir(parents=True)
            (xdg / "anneal/concurrency").write_text("3\n", encoding="utf-8")
            meminfo = root / "meminfo"
            meminfo.write_text(
                f"MemTotal:       {24576 * 1024} kB\nMemAvailable:   {22528 * 1024} kB\n",
                encoding="utf-8",
            )
            real_shim = root / "real_host_bin/anneal-lean-run"
            real_shim.parent.mkdir()
            real_shim.write_text(
                f"#!{sys.executable}\n"
                "import importlib.machinery, importlib.util, pathlib, sys\n"
                "sys.dont_write_bytecode = True\n"
                f"loader = importlib.machinery.SourceFileLoader('alr_ms', {os.fspath(REPO_ROOT / 'scripts/anneal-lean-run')!r})\n"
                "spec = importlib.util.spec_from_loader(loader.name, loader)\n"
                "mod = importlib.util.module_from_spec(spec)\n"
                "loader.exec_module(mod)\n"
                "orig = mod.probe_host_envelope\n"
                f"mod.probe_host_envelope = lambda *a, **kw: orig(*a, meminfo_path=pathlib.Path({os.fspath(meminfo)!r}), "
                f"cgroup_root=pathlib.Path({os.fspath(root / 'no_cg')!r}), proc_cgroup_path=pathlib.Path({os.fspath(root / 'no_proc_cg')!r}), "
                "user_systemd_active=False, cpu_cores=24, **kw)\n"
                "sys.exit(mod.main(sys.argv[1:]))\n",
                encoding="utf-8",
            )
            real_shim.chmod(0o755)
            real_cmd = [
                os.fspath(real_shim),
                "--mode",
                "build",
                "--concurrency",
                "1",
                "--timeout",
                "1800",
                "--",
                "lake",
                "--dir",
                "examples",
                "build",
                "LeanMiriSpec",
            ]
            real_env = {"PATH": "/usr/bin", "XDG_CONFIG_HOME": os.fspath(xdg)}
            real_cap = suite._probe_lean_run_memory_max_mib(real_cmd, env=real_env, cwd=root)
            self.assertIsNotNone(real_cap)
            assert real_cap is not None
            self.assertLess(real_cap, suite.LEAN_MIRI_SPEC_SINGLE_THREAD_RAM_THRESHOLD_MIB)
            with mock.patch.object(suite, "_probe_effective_ram_ceiling_mib", return_value=22528):
                step_env = suite._build_step_env(
                    "lake_build_lean_miri_spec", base_env=real_env, cmd=real_cmd, cwd=root
                )
            self.assertEqual(step_env.get("LEAN_NUM_THREADS"), "1")

    def test_probe_lean_run_failed_reprobe_reports_lower_bound_never_none(self) -> None:
        # `_build_step_env` reads a `None` wrapper cap as "no wrapper cap". Once the first
        # probe has shown that the wrapper executes at another concurrency, a failed or
        # unusable re-probe must therefore still answer with a lower bound on the cap the
        # command will really get, so a low-RAM step is never left multi-threaded.
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            wrapper = root / "bin/anneal-lean-run"
            table = root / "replies.json"
            argv_log = root / "argv.jsonl"
            wrapper.parent.mkdir()
            # Replies are keyed by the last `--concurrency` / `-W` on the command line
            # (argparse's last-wins rule); `"exit:<n>"` makes that probe fail.
            wrapper.write_text(
                textwrap.dedent(
                    f"""\
                    #!{sys.executable}
                    import json, sys
                    args = sys.argv[1:]
                    with open({str(argv_log)!r}, "a", encoding="utf-8") as fh:
                        fh.write(json.dumps(args) + "\\n")
                    conc = "unset"
                    for i, arg in enumerate(args):
                        if arg in ("--concurrency", "-W") and i + 1 < len(args):
                            conc = args[i + 1]
                        elif arg.startswith("--concurrency="):
                            conc = arg.split("=", 1)[1]
                    with open({str(table)!r}, encoding="utf-8") as fh:
                        reply = json.load(fh)[conc]
                    if isinstance(reply, str) and reply.startswith("exit:"):
                        sys.exit(int(reply[5:]))
                    sys.stdout.write(reply if isinstance(reply, str) else json.dumps(reply))
                    """
                ),
                encoding="utf-8",
            )
            wrapper.chmod(0o755)

            def probe(wrapper_opts: list[str], replies: dict[str, object]) -> tuple[int | None, list[list[str]]]:
                table.write_text(json.dumps(replies), encoding="utf-8")
                argv_log.write_text("", encoding="utf-8")
                cmd = [str(wrapper), "--mode", "build", *wrapper_opts, "--", "lake", "build", "MiniRustSpec"]
                cap = suite._probe_lean_run_memory_max_mib(cmd)
                calls = [json.loads(line) for line in argv_log.read_text(encoding="utf-8").splitlines()]
                return cap, calls

            def first(mem: int, w_eff: int, slots: int) -> dict[str, int]:
                return {"memory_max_mb": mem, "w_eff": w_eff, "build_slots": slots}

            # 1. Non-exclusive: execution runs at `build_slots`, so the pool is split
            #    `build_slots / w_eff` ways further than the first probe planned.
            for spelling in (["--concurrency", "1"], ["--concurrency=1"], ["-W", "1"]):
                for bad_reprobe in (
                    "exit:2",
                    "not json",
                    "[]",
                    {"w_eff": 3, "build_slots": 3},
                    {"memory_max_mb": 0, "w_eff": 3, "build_slots": 3},
                    {"memory_max_mb": True, "w_eff": 3, "build_slots": 3},
                    {"memory_max_mb": "7200", "w_eff": 3, "build_slots": 3},
                ):
                    cap, calls = probe(spelling, {"1": first(21600, 1, 3), "3": bad_reprobe})
                    self.assertEqual(cap, 7200, (spelling, bad_reprobe))
                    self.assertEqual(len(calls), 2, (spelling, bad_reprobe))
                    self.assertEqual(calls[1][-4:], ["--concurrency", "3", "--probe", "--json"])
                # A usable re-probe is still taken verbatim, above or below that bound.
                for runtime_mem in (6100, 7200, 9000):
                    cap, _calls = probe(spelling, {"1": first(21600, 1, 3), "3": first(runtime_mem, 3, 3)})
                    self.assertEqual(cap, runtime_mem, spelling)
            # The bound scales by `w_eff / build_slots`, rounds down, and stays positive.
            cap, _calls = probe(["--concurrency", "2"], {"2": first(20001, 2, 3), "3": "exit:1"})
            self.assertEqual(cap, 13334)
            cap, _calls = probe(["--concurrency", "1"], {"1": first(2, 1, 4), "4": "exit:1"})
            self.assertEqual(cap, 1)

            # 2. `--exclusive` on an older wrapper whose probe ignored it: execution runs at
            #    `w_eff = 1`, so the first cap (planned for 3 slots) is already a lower bound.
            cap, calls = probe(["--exclusive", "--concurrency", "3"], {"3": first(7200, 3, 3), "1": "exit:2"})
            self.assertEqual(cap, 7200)
            self.assertEqual(calls[1][-4:], ["--concurrency", "1", "--probe", "--json"])
            cap, _calls = probe(
                ["--exclusive", "--concurrency", "3"], {"3": first(7200, 3, 3), "1": {"w_eff": 1}}
            )
            self.assertEqual(cap, 7200)

            # 3. A first probe without a usable cap is no answer, and is not re-probed.
            for unusable in ({"w_eff": 1, "build_slots": 3}, {"memory_max_mb": 0, "w_eff": 1, "build_slots": 3}):
                cap, calls = probe(["--concurrency", "1"], {"1": unusable, "3": first(7200, 3, 3)})
                self.assertIsNone(cap, unusable)
                self.assertEqual(len(calls), 1, unusable)
            # Nor is a consistent one (`w_eff >= build_slots`, or no concurrency fields).
            for consistent in (first(7200, 3, 3), first(5400, 4, 3), {"memory_max_mb": 7200}):
                cap, calls = probe(["--concurrency", "1"], {"1": consistent})
                self.assertEqual(cap, consistent["memory_max_mb"], consistent)
                self.assertEqual(len(calls), 1, consistent)

            # 4. The regression itself: a 9000 MiB first answer is already below 10 GiB, so
            #    the cap at two slots is too. With the re-probe failing, both low-RAM steps
            #    must stay single-threaded on a host whose own ceiling is 32 GiB.
            table.write_text(json.dumps({"1": first(9000, 1, 2), "2": "exit:2"}), encoding="utf-8")
            step_cmd = [str(wrapper), "--mode", "build", "--concurrency", "1", "--", "lake", "build", "MiniRustSpec"]
            self.assertEqual(suite._probe_lean_run_memory_max_mib(step_cmd), 4500)
            with mock.patch.object(suite, "_probe_effective_ram_ceiling_mib", return_value=32768):
                for step_name in sorted(suite.LOW_RAM_SINGLE_THREAD_STEPS):
                    env = suite._build_step_env(
                        step_name, base_env={"PATH": "/usr/bin"}, cmd=step_cmd, cwd=root
                    )
                    self.assertEqual(env.get("LEAN_NUM_THREADS"), "1", step_name)
                # The vendored `Miri` build is not a low-RAM step and never asks the wrapper.
                argv_log.write_text("", encoding="utf-8")
                env = suite._build_step_env(
                    "lake_build_examples_miri_vendor", base_env={"PATH": "/usr/bin"}, cmd=step_cmd, cwd=root
                )
                self.assertNotIn("LEAN_NUM_THREADS", env)
                self.assertEqual(argv_log.read_text(encoding="utf-8"), "")

            # 5. If `build_slots` grows between probe 1 and probe 2 (so the re-probe still
            #    reports `w_eff < build_slots`), clamp fail-closed without a 3rd probe.
            cap, calls = probe(["--concurrency", "1"], {"1": first(21600, 1, 2), "2": first(12000, 2, 4)})
            self.assertEqual(cap, 6000)
            self.assertEqual(len(calls), 2)

            # 6. Short-circuit: when the host/cgroup ceiling is already `< 10 GiB`,
            #    `_build_step_env` single-threads immediately without spawning the wrapper.
            table.write_text(json.dumps({"1": first(21600, 1, 3), "3": first(7200, 3, 3)}), encoding="utf-8")
            argv_log.write_text("", encoding="utf-8")
            with mock.patch.object(suite, "_probe_effective_ram_ceiling_mib", return_value=8192):
                for step_name in sorted(suite.LOW_RAM_SINGLE_THREAD_STEPS):
                    env = suite._build_step_env(
                        step_name, base_env={"PATH": "/usr/bin"}, cmd=step_cmd, cwd=root
                    )
                    self.assertEqual(env.get("LEAN_NUM_THREADS"), "1", step_name)
            self.assertEqual(argv_log.read_text(encoding="utf-8"), "")
            # At `>= 10 GiB` or non-integer (`None` / `bool`) host ceiling, the wrapper IS still probed.
            for host_mib in (10240, None, True):
                argv_log.write_text("", encoding="utf-8")
                with mock.patch.object(suite, "_probe_effective_ram_ceiling_mib", return_value=host_mib):
                    env = suite._build_step_env(
                        "lake_build_minirust_spec", base_env={"PATH": "/usr/bin"}, cmd=step_cmd, cwd=root
                    )
                self.assertEqual(env.get("LEAN_NUM_THREADS"), "1", host_mib)
                self.assertEqual(len(argv_log.read_text(encoding="utf-8").splitlines()), 2, host_mib)

    def test_resolve_anneal_lean_run_anchors_relative_candidates(self) -> None:
        # Steps run with `cwd=repo_root`; a relative `ANNEAL_LEAN_RUN` or `PATH` entry that
        # was found executable from the current directory must not be re-resolved there.
        def make_exe(path: Path) -> Path:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text("#!/bin/sh\nexit 0\n", encoding="utf-8")
            path.chmod(0o755)
            return path

        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp).resolve()
            repo = root / "repo"
            repo.mkdir()
            env_wrapper = make_exe(root / "custom/anneal-lean-run")
            path_wrapper = make_exe(root / "bin/anneal-lean-run")
            home_wrapper = make_exe(root / "home/.local/bin/anneal-lean-run")
            local_wrapper = make_exe(root / "repo_local/scripts/anneal-lean-run")
            old_cwd = os.getcwd()
            os.chdir(root)
            try:
                from_env = suite._resolve_anneal_lean_run(
                    repo, env={"ANNEAL_LEAN_RUN": "custom/anneal-lean-run", "PATH": ""}
                )
                from_path = suite._resolve_anneal_lean_run(repo, env={"PATH": "bin"})
                from_home_env = suite._resolve_anneal_lean_run(repo, env={"PATH": "", "HOME": "home"})
                from_home_arg = suite._resolve_anneal_lean_run(repo, env={"PATH": ""}, home=Path("home"))
                from_local = suite._resolve_anneal_lean_run(Path("repo_local"), env={"PATH": ""})
            finally:
                os.chdir(old_cwd)
            self.assertEqual(from_env, env_wrapper)
            self.assertEqual(from_path, path_wrapper)
            self.assertEqual(from_home_env, home_wrapper)
            self.assertEqual(from_home_arg, home_wrapper)
            self.assertEqual(from_local, local_wrapper)

    def test_wrapper_honors_lean_num_threads_probe_and_exec_verdicts(self) -> None:
        # On this host the in-repo wrapper keeps `LEAN_NUM_THREADS=1`, and its `--probe`
        # says so; the older fleet wrapper (when installed) reports its budget instead.
        self.assertTrue(suite._wrapper_honors_lean_num_threads(REPO_ROOT / "scripts/anneal-lean-run"))
        fleet = Path.home() / ".local/bin/anneal-lean-run"
        if fleet.is_file() and os.access(fleet, os.X_OK):
            probe = subprocess.run(
                [os.fspath(fleet), "--mode", "build", "--concurrency", "1", "--probe"],
                env={**os.environ, "LEAN_NUM_THREADS": "1"},
                capture_output=True,
                text=True,
                timeout=30,
                check=False,
            )
            banner = re.search(r"\(LEAN_NUM_THREADS=([^)]*)\)", probe.stdout)
            if banner is not None and banner.group(1) != "1":
                self.assertFalse(suite._wrapper_honors_lean_num_threads(fleet))

        with tempfile.TemporaryDirectory() as tmp, mock.patch.dict(suite._WRAPPER_THREAD_PROBE_CACHE, clear=True):
            root = Path(tmp).resolve()
            log = root / "calls.jsonl"
            honest = "Thread Budget (-j) : 4 threads (LEAN_NUM_THREADS=1)"
            cases: list[tuple[str, dict[str, Any], bool]] = [
                ("honest_banner_honoring_exec", {"probe_text": honest}, True),
                ("no_banner_honoring_exec", {"probe_text": ""}, True),
                (
                    "prefixed_var_name_no_false_positive",
                    {"probe_text": honest + "\n  DEFAULT_LEAN_NUM_THREADS=96"},
                    True,
                ),
                ("probe_clobber", {"probe_text": "Thread Budget (-j) : 3 threads (LEAN_NUM_THREADS=3)"}, False),
                ("exec_clobber", {"probe_text": honest, "exec_threads": "3"}, False),
                ("no_banner_exec_clobber", {"probe_text": "", "exec_threads": "3"}, False),
                ("exec_unsets", {"probe_text": honest, "exec_threads": ""}, False),
                ("exec_whitespace_wrapped_threads", {"probe_text": honest, "exec_threads": " 1\n"}, False),
                ("exec_leading_newline", {"probe_text": honest, "exec_stdout": "\n"}, False),
                (
                    "one_core_banner_exec_clobber",
                    {"probe_text": "Thread Budget (-j) : 1 threads (LEAN_NUM_THREADS=1)", "exec_threads": "3"},
                    False,
                ),
                ("one_core_banner_honoring", {"probe_text": "Thread Budget (-j) : 1 threads (LEAN_NUM_THREADS=1)"}, True),
                ("second_banner_clobbers", {"probe_text": honest + "\n" + honest.replace("=1)", "=8)")}, False),
                ("stray_threads_mention", {"probe_text": honest + "\n  child env: LEAN_NUM_THREADS=8"}, False),
                ("banner_spaces_value", {"probe_text": "Thread Budget (-j) : 4 threads (LEAN_NUM_THREADS= 11)"}, False),
                (
                    "oversized_probe_stdout_fails_closed",
                    {"probe_text": ("x" * (suite._WRAPPER_PROBE_MAX_OUTPUT_BYTES + 64)) + "\nLEAN_NUM_THREADS=96"},
                    False,
                ),
                ("probe_nonzero_exit", {"probe_text": honest, "probe_rc": 2}, False),
                ("exec_nonzero_exit", {"probe_text": honest, "exec_rc": 1}, False),
                ("exec_stdout_chatter", {"probe_text": honest, "exec_stdout": "[wrapper] scope ok\n"}, False),
            ]
            for label, kwargs, expected in cases:
                wrapper = _write_fake_lean_run(root / label / "anneal-lean-run", log=log, **kwargs)
                self.assertIs(suite._wrapper_honors_lean_num_threads(wrapper), expected, label)

            # Every probe ran the exact text `--probe` (no `--json`) and the slot-free exec check,
            # with the caller's `LEAN_NUM_THREADS=1`, no LSP eviction, and private XDG dirs.
            calls = [json.loads(line) for line in log.read_text(encoding="utf-8").splitlines()]
            probe_calls = [c for c in calls if "--probe" in c["args"]]
            exec_calls = [c for c in calls if "--probe" not in c["args"]]
            self.assertEqual(len(probe_calls), len(cases))
            for call in probe_calls:
                self.assertEqual(call["args"], ["--mode", "build", "--concurrency", "1", "--probe"])
            self.assertTrue(exec_calls)
            for call in exec_calls:
                self.assertEqual(
                    call["args"],
                    ["--mode", "file", "--no-slot-lock", "--", sys.executable, "-B", "-c", suite._WRAPPER_EXEC_THREADS_DUMP],
                )
            for call in calls:
                env = call["env"]
                self.assertEqual(env["LEAN_NUM_THREADS"], "1")
                self.assertEqual(env["ANNEAL_LSP_NO_EVICT"], "1")
                self.assertIsNone(env["ANNEAL_LEAN_RUN_IN_SCOPE"])
                for var in ("XDG_CONFIG_HOME", "XDG_RUNTIME_DIR"):
                    self.assertTrue(env[var] and Path(env[var]).name in ("config", "runtime"), (var, env[var]))
                    self.assertNotEqual(env[var], os.environ.get(var))
                    self.assertFalse(Path(env[var]).exists(), "probe temp dirs are removed")
            # A clobbering or oversized `--probe` is rejected before anything is executed through it.
            for rejected_label in ("probe_clobber", "oversized_probe_stdout_fails_closed"):
                self.assertFalse(any(Path(c["argv0"]).parent.name == rejected_label for c in exec_calls), rejected_label)

    def test_wrapper_honors_lean_num_threads_rejects_bypasses(self) -> None:
        with tempfile.TemporaryDirectory() as tmp, mock.patch.dict(suite._WRAPPER_THREAD_PROBE_CACHE, clear=True):
            root = Path(tmp).resolve()
            log = root / "calls.jsonl"

            def spawns() -> int:
                return len(log.read_text(encoding="utf-8").splitlines()) if log.exists() else 0

            good = _write_fake_lean_run(root / "good/anneal-lean-run", log=log)
            # Missing, directory, non-executable, and dangling-symlink paths: `False`, nothing spawned.
            non_exec = _write_fake_lean_run(root / "nonexec/anneal-lean-run", log=log)
            non_exec.chmod(0o644)
            dangling = root / "dangling"
            dangling.symlink_to(root / "nowhere")
            for bad in (root / "missing", root / "good", non_exec, dangling, Path("bad\0path")):
                self.assertFalse(suite._wrapper_honors_lean_num_threads(bad), bad)
            self.assertEqual(spawns(), 0)
            # Non-positive, non-finite, or boolean timeouts never spawn either.
            for timeout in (0, -1.0, float("nan"), float("inf"), float("-inf"), True):
                self.assertFalse(suite._wrapper_honors_lean_num_threads(good, timeout_sec=timeout), timeout)
            self.assertEqual(spawns(), 0)

            # A symlink to an honoring wrapper is judged by its target.
            link = root / "link/anneal-lean-run"
            link.parent.mkdir()
            link.symlink_to(good)
            self.assertTrue(suite._wrapper_honors_lean_num_threads(link))

            # A bare relative name is the file in the current directory, never a `PATH` lookup
            # (which here would find an honoring wrapper and mask the clobbering one).
            clobber_dir = root / "cwd"
            _write_fake_lean_run(clobber_dir / "anneal-lean-run", log=log, exec_threads="3")
            old_cwd = os.getcwd()
            os.chdir(clobber_dir)
            try:
                self.assertFalse(
                    suite._wrapper_honors_lean_num_threads(
                        Path("anneal-lean-run"), env={**os.environ, "PATH": os.fspath(good.parent)}
                    )
                )
            finally:
                os.chdir(old_cwd)

            # An ambient `ANNEAL_LEAN_RUN_IN_SCOPE=1` (the suite running under a wrapper) must not
            # turn a clobbering wrapper's re-entrancy pass-through into a pass.
            sneaky = _write_fake_lean_run(
                root / "sneaky/anneal-lean-run",
                log=log,
                probe_text="Thread Budget (-j) : 4 threads (LEAN_NUM_THREADS=4)",
                exec_threads="4",
                in_scope_passthrough=True,
            )
            self.assertFalse(
                suite._wrapper_honors_lean_num_threads(sneaky, env={**os.environ, "ANNEAL_LEAN_RUN_IN_SCOPE": "1"})
            )

            # Ambient operator overrides (`ANNEAL_WORKTREE_CONCURRENCY`, `ANNEAL_LEAN_MEMORY_MAX_MB`,
            # `ANNEAL_LEAN_TIMEOUT_SEC`, `ANNEAL_OOM_OFFLOAD_CMD`, and outer-scope metadata) are
            # scrubbed from the probe so they cannot break or side-effect a valid wrapper.
            hostile_overrides = {
                "ANNEAL_LEAN_RUN_IN_SCOPE": "1",
                "ANNEAL_LEAN_RUN_ACTIVE": "1",
                "ANNEAL_LEAN_RUN_LEAN_M_MB": "64",
                "ANNEAL_LEAN_RUN_SLOTS": "9",
                "ANNEAL_LEAN_RUN_MEM_MB": "1",
                "ANNEAL_WORKTREE_CONCURRENCY": "500",
                "ANNEAL_LEAN_MEMORY_MAX_MB": "1",
                "ANNEAL_LEAN_TIMEOUT_SEC": "1",
                "ANNEAL_OOM_OFFLOAD_CMD": "/bin/false",
            }
            before = spawns()
            scrub_probe = _write_fake_lean_run(root / "scrub/anneal-lean-run", log=log)
            self.assertTrue(
                suite._wrapper_honors_lean_num_threads(scrub_probe, env={**os.environ, **hostile_overrides})
            )
            scrub_calls = [json.loads(line) for line in log.read_text(encoding="utf-8").splitlines()[before:]]
            self.assertEqual(len(scrub_calls), 2)
            for call in scrub_calls:
                for key in hostile_overrides:
                    self.assertIsNone(call["env"][key], key)
            # And on the real in-repo wrapper, hostile overrides must not cause headroom/OOM rejection.
            self.assertTrue(
                suite._wrapper_honors_lean_num_threads(
                    REPO_ROOT / "scripts/anneal-lean-run", env={**os.environ, **hostile_overrides}
                )
            )

            # Hung `--probe` or exec check: `False` within the timeout, and the wrapper's
            # process group (including a grandchild holding stdout) is gone.
            for label, kwargs in (("hung_probe", {"probe_sleep": 60}), ("hung_exec", {"exec_sleep": 60})):
                hung = _write_fake_lean_run(root / label / "anneal-lean-run", log=log, **kwargs)
                t0 = time.monotonic()
                self.assertFalse(suite._wrapper_honors_lean_num_threads(hung, timeout_sec=1.0), label)
                self.assertLess(time.monotonic() - t0, 10.0, label)
                pid_file = hung.parent / "sleeper.pid"
                deadline = time.monotonic() + 5.0
                while pid_file.exists() and time.monotonic() < deadline:
                    try:
                        os.kill(int(pid_file.read_text(encoding="utf-8")), 0)
                    except (ProcessLookupError, ValueError):
                        break
                    time.sleep(0.05)
                else:
                    if pid_file.exists():
                        self.fail(f"{label}: probe sleeper survived the timeout")

            # The existing `anneal-workloads.slice` unit is seeded into the private config dir.
            fake_home = root / "home"
            unit = fake_home / ".config/systemd/user/anneal-workloads.slice"
            unit.parent.mkdir(parents=True)
            unit.write_text("[Slice]\nMemoryMax=1234M\n", encoding="utf-8")
            seeded = _write_fake_lean_run(root / "seed/anneal-lean-run", log=log)
            before = spawns()
            self.assertTrue(
                suite._wrapper_honors_lean_num_threads(
                    seeded, env={"PATH": os.environ.get("PATH", ""), "HOME": os.fspath(fake_home)}
                )
            )
            new_calls = [json.loads(line) for line in log.read_text(encoding="utf-8").splitlines()[before:]]
            self.assertEqual(len(new_calls), 2)
            for call in new_calls:
                self.assertEqual(call["slice"], "[Slice]\nMemoryMax=1234M\n")
                self.assertEqual(call["env"]["HOME"], os.fspath(fake_home))

            # Even when the caller's `HOME` has no (or a stale) `anneal-workloads.slice`,
            # probing the real in-repo wrapper synthesizes the matching unit from `--probe`
            # so `ensure_workloads_slice` never invokes `systemctl --user daemon-reload`.
            real_systemctl = shutil.which("systemctl") or "/usr/bin/systemctl"
            if Path(real_systemctl).is_file():
                spy_bin = root / "spy_bin"
                spy_bin.mkdir()
                spy_log = root / "systemctl_calls.jsonl"
                spy_systemctl = spy_bin / "systemctl"
                spy_systemctl.write_text(
                    f"#!{sys.executable}\n"
                    "import json, os, sys\n"
                    f"with open({os.fspath(spy_log)!r}, 'a', encoding='utf-8') as fh:\n"
                    "    fh.write(json.dumps(sys.argv[1:]) + '\\n')\n"
                    f"os.execv({real_systemctl!r}, [{real_systemctl!r}, *sys.argv[1:]])\n",
                    encoding="utf-8",
                )
                spy_systemctl.chmod(0o755)
                empty_home = root / "empty_home"
                empty_home.mkdir()
                spy_path = os.pathsep.join([os.fspath(spy_bin), os.environ.get("PATH", "/usr/bin:/bin")])
                for label, extra_env in (
                    ("empty_home", {"PATH": spy_path, "HOME": os.fspath(empty_home)}),
                    ("stale_home", {"PATH": spy_path, "HOME": os.fspath(fake_home)}),
                ):
                    self.assertTrue(
                        suite._wrapper_honors_lean_num_threads(REPO_ROOT / "scripts/anneal-lean-run", env=extra_env),
                        label,
                    )
                if spy_log.exists():
                    sc_calls = [json.loads(line) for line in spy_log.read_text(encoding="utf-8").splitlines()]
                    self.assertFalse(
                        any("daemon-reload" in args for args in sc_calls),
                        f"probe triggered daemon-reload: {sc_calls}",
                    )

    def test_wrapper_honors_lean_num_threads_memo_invalidates_on_any_change(self) -> None:
        with tempfile.TemporaryDirectory() as tmp, mock.patch.dict(suite._WRAPPER_THREAD_PROBE_CACHE, clear=True):
            root = Path(tmp).resolve()
            log = root / "calls.jsonl"

            def spawns() -> int:
                return len(log.read_text(encoding="utf-8").splitlines()) if log.exists() else 0

            honest_src = _fake_lean_run_source(log=log)
            clobbering_src = _fake_lean_run_source(log=log, exec_threads="7")
            width = max(len(honest_src), len(clobbering_src))

            def padded(src: str) -> str:
                return src + "#" * (width - len(src))

            wrapper = root / "bin/anneal-lean-run"
            wrapper.parent.mkdir()
            wrapper.write_text(padded(honest_src), encoding="utf-8")
            wrapper.chmod(0o755)
            self.assertTrue(suite._wrapper_honors_lean_num_threads(wrapper))
            first = spawns()
            self.assertEqual(first, 2)
            # Repeated calls (as from repeated `build_suite_steps()`) spawn nothing.
            for _ in range(3):
                self.assertTrue(suite._wrapper_honors_lean_num_threads(wrapper))
                self.assertTrue(suite._wrapper_honors_lean_num_threads(Path(os.path.relpath(wrapper))))
            self.assertEqual(spawns(), first, "a relative spelling shares the absolute path's entry")

            # Same-size in-place rewrite (same inode) with the mtime restored: still re-probed.
            st = wrapper.stat()
            wrapper.write_text(padded(clobbering_src), encoding="utf-8")
            os.utime(wrapper, ns=(st.st_atime_ns, st.st_mtime_ns))
            st_rewritten = wrapper.stat()
            self.assertEqual(
                (st_rewritten.st_ino, st_rewritten.st_size, st_rewritten.st_mtime_ns),
                (st.st_ino, st.st_size, st.st_mtime_ns),
            )
            self.assertFalse(suite._wrapper_honors_lean_num_threads(wrapper))
            self.assertEqual(spawns(), first + 2)
            first = spawns()
            # Even an identical `os.stat` (as on a filesystem with coarse timestamps) cannot
            # serve the old verdict: the content digest is part of the key.
            real_stat = os.stat
            frozen = {os.fspath(wrapper): real_stat(wrapper)}

            def frozen_stat(path: Any, *args: Any, **kwargs: Any) -> os.stat_result:
                if isinstance(path, (str, os.PathLike)) and os.fspath(path) in frozen:
                    return frozen[os.fspath(path)]
                return real_stat(path, *args, **kwargs)

            wrapper.write_text(padded(honest_src), encoding="utf-8")
            with mock.patch.object(suite.os, "stat", side_effect=frozen_stat):
                self.assertTrue(suite._wrapper_honors_lean_num_threads(wrapper))
            self.assertEqual(spawns(), first + 2)
            wrapper.write_text(padded(clobbering_src), encoding="utf-8")
            first = spawns()

            # Atomic replacement (new inode) back to an honoring wrapper: re-probed.
            replacement = _write_fake_lean_run(root / "bin/.anneal-lean-run.new", log=log)
            os.replace(replacement, wrapper)
            self.assertTrue(suite._wrapper_honors_lean_num_threads(wrapper))
            self.assertEqual(spawns(), first + 2)
            first = spawns()

            # Touching the mtime alone re-probes; a different probe environment or timeout too.
            os.utime(wrapper, ns=(st.st_atime_ns, st.st_mtime_ns + 1_000_000_000))
            self.assertTrue(suite._wrapper_honors_lean_num_threads(wrapper))
            self.assertEqual(spawns(), first + 2)
            self.assertTrue(suite._wrapper_honors_lean_num_threads(wrapper, env={**os.environ, "ANNEAL_X": "1"}))
            self.assertEqual(spawns(), first + 4)
            self.assertTrue(suite._wrapper_honors_lean_num_threads(wrapper, timeout_sec=6.0))
            self.assertEqual(spawns(), first + 6)
            first = spawns()
            # Ambient values the probe overrides or scrubs do not split the cache.
            for noise in (
                {"LEAN_NUM_THREADS": "9"},
                {"ANNEAL_LEAN_RUN_IN_SCOPE": "1"},
                {"ANNEAL_WORKTREE_CONCURRENCY": "8"},
                {"ANNEAL_LEAN_MEMORY_MAX_MB": "512"},
                {"ANNEAL_OOM_OFFLOAD_CMD": "/bin/false"},
                {"XDG_RUNTIME_DIR": "/x"},
            ):
                self.assertTrue(suite._wrapper_honors_lean_num_threads(wrapper, env={**os.environ, **noise}), noise)
            self.assertEqual(spawns(), first)

            # Losing the executable bit is `False` at once, never a stale cached `True`.
            wrapper.chmod(0o644)
            self.assertFalse(suite._wrapper_honors_lean_num_threads(wrapper))
            self.assertEqual(spawns(), first)

    def test_resolve_anneal_lean_run_skips_ambient_wrappers_that_clobber_threads(self) -> None:
        with tempfile.TemporaryDirectory() as tmp, mock.patch.dict(suite._WRAPPER_THREAD_PROBE_CACHE, clear=True):
            root = Path(tmp).resolve()
            log = root / "calls.jsonl"
            repo = root / "repo"
            local = _write_fake_lean_run(repo / "scripts/anneal-lean-run", log=log)
            home = root / "home"
            path_bin = root / "path_bin"
            variants = {
                "probe_clobber": {"probe_text": "Thread Budget (-j) : 3 threads (LEAN_NUM_THREADS=3)"},
                "exec_clobber": {"probe_text": "Thread Budget (-j) : 3 threads (LEAN_NUM_THREADS=1)", "exec_threads": "3"},
            }
            for label, kwargs in variants.items():
                home_wrapper = _write_fake_lean_run(home / ".local/bin/anneal-lean-run", log=log, **kwargs)
                path_wrapper = _write_fake_lean_run(path_bin / "anneal-lean-run", log=log, **kwargs)
                base = {"HOME": os.fspath(home)}
                # `PATH` hit and minimal-cron `~/.local/bin` hit both fall back to the in-repo wrapper.
                self.assertEqual(
                    suite._resolve_anneal_lean_run(repo, env={**base, "PATH": os.fspath(path_bin)}), local, label
                )
                self.assertEqual(suite._resolve_anneal_lean_run(repo, env={**base, "PATH": "/usr/bin:/bin"}), local, label)
                self.assertEqual(
                    suite._resolve_anneal_lean_run(repo, env={"PATH": "/usr/bin:/bin"}, home=home), local, label
                )
                # An explicit `ANNEAL_LEAN_RUN` override is never second-guessed.
                self.assertEqual(
                    suite._resolve_anneal_lean_run(
                        repo, env={**base, "PATH": os.fspath(path_bin), "ANNEAL_LEAN_RUN": os.fspath(home_wrapper)}
                    ),
                    home_wrapper,
                    label,
                )
                # Without an in-repo wrapper there is nothing better: the candidate stays.
                self.assertEqual(
                    suite._resolve_anneal_lean_run(root / "bare", env={**base, "PATH": os.fspath(path_bin)}),
                    path_wrapper,
                    label,
                )
                self.assertEqual(
                    suite._resolve_anneal_lean_run(root / "bare", env={**base, "PATH": "/usr/bin:/bin"}),
                    home_wrapper,
                    label,
                )
                # A non-executable in-repo wrapper is no fallback either.
                local.chmod(0o644)
                try:
                    self.assertEqual(
                        suite._resolve_anneal_lean_run(repo, env={**base, "PATH": os.fspath(path_bin)}),
                        path_wrapper,
                        label,
                    )
                finally:
                    local.chmod(0o755)

            # An honoring ambient wrapper is still preferred over the in-repo one.
            _write_fake_lean_run(path_bin / "anneal-lean-run", log=log)
            self.assertEqual(
                suite._resolve_anneal_lean_run(repo, env={"PATH": os.fspath(path_bin), "HOME": os.fspath(home)}),
                path_bin / "anneal-lean-run",
            )
            # A `PATH` / `~/.local/bin` symlink to the in-repo wrapper is used as is, unprobed.
            link_bin = root / "link_bin"
            link_bin.mkdir()
            (link_bin / "anneal-lean-run").symlink_to(local)
            local.write_text(_fake_lean_run_source(log=log, exec_threads="3"), encoding="utf-8")
            before = log.read_text(encoding="utf-8")
            self.assertEqual(
                suite._resolve_anneal_lean_run(repo, env={"PATH": os.fspath(link_bin), "HOME": os.fspath(home)}),
                link_bin / "anneal-lean-run",
            )
            self.assertEqual(log.read_text(encoding="utf-8"), before)

            # A clobbering first `PATH` wrapper falls through to a later honoring `PATH` entry
            # or an honoring `~/.local/bin/anneal-lean-run` before falling back to `local`, and
            # an embedded NUL byte in an earlier `PATH` entry does not crash resolution.
            bad_bin = root / "bad_bin"
            good_bin = root / "good_bin"
            _write_fake_lean_run(
                bad_bin / "anneal-lean-run",
                log=log,
                probe_text="Thread Budget (-j) : 3 threads (LEAN_NUM_THREADS=3)",
            )
            good_path_wrapper = _write_fake_lean_run(good_bin / "anneal-lean-run", log=log)
            good_home = root / "good_home"
            good_home_wrapper = _write_fake_lean_run(good_home / ".local/bin/anneal-lean-run", log=log)
            self.assertEqual(
                suite._resolve_anneal_lean_run(
                    repo,
                    env={
                        "PATH": os.pathsep.join(["bad\x00dir", os.fspath(bad_bin), os.fspath(good_bin)]),
                        "HOME": os.fspath(home),
                    },
                ),
                good_path_wrapper,
            )
            self.assertEqual(
                suite._resolve_anneal_lean_run(
                    repo,
                    env={"PATH": os.fspath(bad_bin), "HOME": os.fspath(good_home)},
                ),
                good_home_wrapper,
            )
            # When `~/.local/bin/anneal-lean-run` is a symlink to an already-rejected `PATH`
            # wrapper, it is not probed a second time before falling back to `local`.
            sym_home = root / "sym_home"
            (sym_home / ".local/bin").mkdir(parents=True)
            (sym_home / ".local/bin/anneal-lean-run").symlink_to(bad_bin / "anneal-lean-run")
            suite._WRAPPER_THREAD_PROBE_CACHE.clear()
            before_lines = len(log.read_text(encoding="utf-8").splitlines())
            self.assertEqual(
                suite._resolve_anneal_lean_run(
                    repo,
                    env={"PATH": os.fspath(bad_bin), "HOME": os.fspath(sym_home)},
                ),
                local,
            )
            after_lines = len(log.read_text(encoding="utf-8").splitlines())
            self.assertEqual(after_lines - before_lines, 1)

    def test_nightly_low_ram_waves_run_single_threaded_despite_clobbering_ambient_wrapper(self) -> None:
        # End to end: an ambient fleet wrapper on `PATH` and in `~/.local/bin` that clobbers
        # `LEAN_NUM_THREADS=1` to `3` is skipped by `build_suite_steps`, every
        # `LOW_RAM_SINGLE_THREAD_STEPS` step runs under the real in-repo
        # `scripts/anneal-lean-run`, and on a < 10 GiB host the child sees `LEAN_NUM_THREADS=1`.
        with tempfile.TemporaryDirectory() as tmp, mock.patch.dict(suite._WRAPPER_THREAD_PROBE_CACHE, clear=True):
            root = Path(tmp).resolve()
            home = root / "home"
            # The real wrapper reconciles `anneal-workloads.slice` under `$HOME/.config`; seed
            # the fake home with the live unit so it finds it current and reloads nothing.
            live_cfg = os.environ.get("XDG_CONFIG_HOME", "").strip() or os.fspath(Path.home() / ".config")
            live_unit = Path(live_cfg) / "systemd/user/anneal-workloads.slice"
            if live_unit.is_file():
                (home / ".config/systemd/user").mkdir(parents=True)
                shutil.copyfile(live_unit, home / ".config/systemd/user/anneal-workloads.slice")
            fleet = _write_fake_lean_run(
                home / ".local/bin/anneal-lean-run",
                probe_text="Thread Budget (-j) : 3 threads (LEAN_NUM_THREADS=3)",
                exec_threads="3",
            )
            path_bin = root / "path_bin"
            path_bin.mkdir()
            (path_bin / "anneal-lean-run").symlink_to(fleet)
            in_repo = REPO_ROOT / "scripts/anneal-lean-run"
            ambient_path = os.pathsep.join([os.fspath(path_bin), os.environ.get("PATH", "/usr/bin:/bin")])
            with mock.patch.dict(os.environ, {"PATH": ambient_path, "HOME": os.fspath(home), "LEAN_NUM_THREADS": "3"}):
                self.assertEqual(suite._resolve_anneal_lean_run(REPO_ROOT), Path(os.path.abspath(in_repo)))
                steps = {name: cmd for name, _c, cmd, _t in suite.build_suite_steps(REPO_ROOT, "nightly")}
                self.assertTrue(suite.LOW_RAM_SINGLE_THREAD_STEPS <= set(steps))
                out_file = root / "threads.txt"
                dump = (
                    "import os, pathlib; "
                    f"pathlib.Path({str(out_file)!r}).write_text(os.environ.get('LEAN_NUM_THREADS', '<unset>'))"
                )
                for step in sorted(suite.LOW_RAM_SINGLE_THREAD_STEPS):
                    cmd = steps[step]
                    self.assertEqual(cmd[0], os.fspath(in_repo), step)
                    sep = cmd.index("--")
                    # Same wrapper and flags; slot-free so the test never queues behind real builds.
                    run_cmd = [*cmd[:sep], "--no-slot-lock", "--", sys.executable, "-B", "-c", dump]
                    for wrapper, expected in ((cmd[0], "1"), (os.fspath(fleet), "3")):
                        out_file.unlink(missing_ok=True)
                        with mock.patch.object(suite, "_probe_effective_ram_ceiling_mib", return_value=5712):
                            res = suite._run_step(
                                step, "cat2_correspondence_suites", [wrapper, *run_cmd[1:]], cwd=root, timeout_sec=120
                            )
                        self.assertEqual(res["status"], "PASS", (step, wrapper, res.get("failure_excerpt")))
                        # The fleet wrapper (negative control) shows the clobbering the fallback avoids.
                        self.assertEqual(out_file.read_text(encoding="utf-8"), expected, (step, wrapper))

    def test_renamed_anneal_lean_run_override_keeps_wrapper_deadline_and_ram_probe(self) -> None:
        # `ANNEAL_LEAN_RUN` may give the wrapper any file name. A step it wraps still queues
        # for a build slot and enforces its own `--timeout`, so the outer deadline must
        # cover both (at the bare step budget the suite would kill a queued step and lose the
        # wrapper's exit-124 diagnostic), and the `MemoryMax` it plans must still right-size
        # `lake_build_lean_miri_spec`. Recognizing the wrapper by its name alone missed both.
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp).resolve()
            renamed = root / "bin/lean-run-v2"
            renamed.parent.mkdir()
            renamed.write_text(
                f"#!{sys.executable}\n"
                "import json, os, sys\n"
                "args = sys.argv[1:]\n"
                "if '--probe' in args:\n"
                "    print(json.dumps({'memory_max_mb': 5712}))\n"
                "    sys.exit(0)\n"
                "cmd = args[args.index('--') + 1:]\n"
                "os.execvp(cmd[0], cmd)\n",
                encoding="utf-8",
            )
            renamed.chmod(0o755)
            self.assertNotIn("ANNEAL_LEAN_RUN", os.environ)
            canonical = {
                name: (cmd, timeout_sec)
                for name, _cat, cmd, timeout_sec in suite.build_suite_steps(REPO_ROOT, "nightly")
            }
            canonical_outer = {
                name: suite._outer_timeout_sec(cmd, timeout_sec) for name, (cmd, timeout_sec) in canonical.items()
            }
            canonical_wrapped = {
                name for name, (cmd, _t) in canonical.items() if Path(cmd[0]).name == "anneal-lean-run"
            }
            self.assertEqual(len(canonical), 31)
            self.assertEqual(len(canonical_wrapped), 23)

            with mock.patch.dict(os.environ, {"ANNEAL_LEAN_RUN": os.fspath(renamed), "LEAN_NUM_THREADS": "7"}):
                steps = suite.build_suite_steps(REPO_ROOT, "nightly")
                self.assertEqual([name for name, _c, _cmd, _t in steps], list(canonical))
                for name, _cat, cmd, timeout_sec in steps:
                    canon_cmd, canon_timeout = canonical[name]
                    self.assertEqual(timeout_sec, canon_timeout, name)
                    if name not in canonical_wrapped:
                        self.assertEqual(cmd, canon_cmd, name)
                        self.assertFalse(suite._is_lean_run_wrapped(cmd), name)
                        self.assertEqual(suite._outer_timeout_sec(cmd, timeout_sec), timeout_sec, name)
                        continue
                    self.assertEqual(cmd, [os.fspath(renamed), *canon_cmd[1:]], name)
                    self.assertTrue(suite._is_lean_run_wrapped(cmd), name)
                    self.assertEqual(suite._lean_run_wrapper_flags(cmd), suite._lean_run_wrapper_flags(canon_cmd), name)
                    self.assertEqual(suite._outer_timeout_sec(cmd, timeout_sec), canonical_outer[name], name)
                    self.assertGreaterEqual(
                        suite._outer_timeout_sec(cmd, timeout_sec),
                        timeout_sec + suite.WRAPPER_TIMEOUT_GRACE_SEC,
                        name,
                    )
                miri_cmd = next(cmd for name, _c, cmd, _t in steps if name == "lake_build_lean_miri_spec")
                self.assertEqual(suite._outer_timeout_sec(miri_cmd, 1800), 2 * 1800 + suite.WRAPPER_TIMEOUT_GRACE_SEC)
                self.assertEqual(suite._probe_lean_run_memory_max_mib(miri_cmd), 5712)
                by_step = {name: cmd for name, _c, cmd, _t in steps}
                with mock.patch.object(suite, "_probe_effective_ram_ceiling_mib", return_value=65536):
                    step_env = suite._build_step_env("lake_build_lean_miri_spec", cmd=miri_cmd, cwd=root)
                    minirust_env = suite._build_step_env(
                        "lake_build_minirust_spec", cmd=by_step["lake_build_minirust_spec"], cwd=root
                    )
                    # Negative controls: steps the low-RAM policy does not right-size keep the
                    # ambient thread count although the same wrapper plans the same 5712 MiB cap.
                    vendor_env = suite._build_step_env(
                        "lake_build_examples_miri_vendor", cmd=by_step["lake_build_examples_miri_vendor"], cwd=root
                    )
                    corr_env = suite._build_step_env(
                        "lake_build_correspondence", cmd=by_step["lake_build_correspondence"], cwd=root
                    )
                self.assertEqual(step_env["LEAN_NUM_THREADS"], "1")
                self.assertEqual(minirust_env["LEAN_NUM_THREADS"], "1")
                self.assertEqual(vendor_env["LEAN_NUM_THREADS"], "7")
                self.assertEqual(corr_env["LEAN_NUM_THREADS"], "7")
                self.assertEqual(os.environ["LEAN_NUM_THREADS"], "7")
                # End to end: the wrapped step itself sees the right-sized thread count.
                out_file = root / "threads.txt"
                dump = (
                    "import os, pathlib; "
                    f"pathlib.Path({str(out_file)!r}).write_text(os.environ.get('LEAN_NUM_THREADS', '<unset>'))"
                )
                with mock.patch.object(suite, "_probe_effective_ram_ceiling_mib", return_value=65536):
                    res = suite._run_step(
                        name="lake_build_lean_miri_spec",
                        category="cat2_correspondence_suites",
                        cmd=[os.fspath(renamed), "--mode", "build", "--timeout", "30", "--"]
                        + [sys.executable, "-c", dump],
                        cwd=root,
                        timeout_sec=30,
                    )
                self.assertEqual(res["status"], "PASS", res.get("failure_excerpt"))
                self.assertEqual(out_file.read_text(encoding="utf-8"), "1")

            # Without that override in its environment the same file is an ordinary command,
            # and an override that names another file changes nothing for it.
            for env in ({}, {"ANNEAL_LEAN_RUN": ""}, {"ANNEAL_LEAN_RUN": os.fspath(root / "bin/other")}):
                self.assertFalse(suite._is_lean_run_wrapped(miri_cmd, env), env)
                self.assertEqual(suite._outer_timeout_sec(miri_cmd, 1800, env=env), 1800, env)
                self.assertIsNone(suite._probe_lean_run_memory_max_mib(miri_cmd, env=env), env)
            self.assertFalse(suite._is_lean_run_wrapped([], {"ANNEAL_LEAN_RUN": os.fspath(renamed)}))
            # A relative override is anchored like `_resolve_anneal_lean_run` anchors it.
            self.assertTrue(
                suite._is_lean_run_wrapped(
                    miri_cmd, {"ANNEAL_LEAN_RUN": f"  {os.path.relpath(renamed)}  "}
                )
            )

    def test_ensure_toolchain_path_and_build_step_env_isolate_home_and_probe_overrides(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            fake_home = root / "fake_home"
            (fake_home / ".elan/bin").mkdir(parents=True)
            (fake_home / ".cargo/bin").mkdir(parents=True)

            # Isolated `base_env` with explicit `HOME` prepends exactly that `HOME`'s existing
            # toolchain directories, and nothing of the host process's `Path.home()`. (The
            # temporary directory may itself be under the host home, as with `TMPDIR=~/tmp`,
            # so the whole `PATH` is compared rather than its entries' prefixes.)
            env_with_home = suite._build_step_env(
                "ci_check_non_stable_version",
                base_env={"HOME": str(fake_home), "PATH": "/usr/bin"},
            )
            self.assertEqual(
                env_with_home["PATH"].split(os.pathsep),
                [str(fake_home / ".elan/bin"), str(fake_home / ".cargo/bin"), "/usr/bin"],
            )

            # Isolated `base_env` without `HOME` must not leak ambient host `HOME` either.
            env_no_home = suite._build_step_env(
                "ci_check_non_stable_version",
                base_env={"PATH": "/usr/bin"},
            )
            self.assertEqual(env_no_home["PATH"], "/usr/bin")

            # `env_overrides` (renamed `ANNEAL_LEAN_RUN` / `ANNEAL_LEAN_MEMORY_MAX_MB`) must be
            # visible to `_probe_lean_run_memory_max_mib`, while explicit `LEAN_NUM_THREADS` in
            # `env_overrides` still takes final precedence.
            renamed = root / "custom-wrapper"
            renamed.write_text(
                f"#!{sys.executable}\n"
                "import json, os, sys\n"
                "mb = int(os.environ.get('ANNEAL_LEAN_MEMORY_MAX_MB', '5712'))\n"
                "print(json.dumps({'memory_max_mb': mb}))\n",
                encoding="utf-8",
            )
            renamed.chmod(0o755)
            cmd = [str(renamed), "--mode", "build", "--", "lake", "--dir", "examples", "build", "LeanMiriSpec"]
            with mock.patch.object(suite, "_probe_effective_ram_ceiling_mib", return_value=65536):
                probed_low = suite._build_step_env(
                    "lake_build_lean_miri_spec",
                    base_env={"PATH": "/usr/bin"},
                    env_overrides={"ANNEAL_LEAN_RUN": str(renamed)},
                    cmd=cmd,
                    cwd=root,
                )
                self.assertEqual(probed_low.get("LEAN_NUM_THREADS"), "1")

                probed_high = suite._build_step_env(
                    "lake_build_lean_miri_spec",
                    base_env={"PATH": "/usr/bin"},
                    env_overrides={"ANNEAL_LEAN_RUN": str(renamed), "ANNEAL_LEAN_MEMORY_MAX_MB": "16384"},
                    cmd=cmd,
                    cwd=root,
                )
                self.assertNotIn("LEAN_NUM_THREADS", probed_high)

                explicit_override = suite._build_step_env(
                    "lake_build_lean_miri_spec",
                    base_env={"PATH": "/usr/bin"},
                    env_overrides={"ANNEAL_LEAN_RUN": str(renamed), "LEAN_NUM_THREADS": "4"},
                    cmd=cmd,
                    cwd=root,
                )
                self.assertEqual(explicit_override.get("LEAN_NUM_THREADS"), "4")

    def test_outer_timeout_handles_passthrough_lsp_no_evict_and_lake_global_opts_auto_mode(self) -> None:
        lr = str(REPO_ROOT / "scripts/anneal-lean-run")
        grace = suite.WRAPPER_TIMEOUT_GRACE_SEC
        build_wait = suite.LEAN_RUN_SLOT_WAIT_SEC["build"]
        file_wait = suite.LEAN_RUN_SLOT_WAIT_SEC["file"]

        cmd_build = [lr, "--mode", "build", "--timeout", "600", "--", "lake", "build", "Anneal"]
        cmd_nested = [lr, "--mode", "build", "--timeout", "600", "--nested-ok", "--", "lake", "build", "Anneal"]

        # Inside an enclosing `anneal-lean-run` scope (`ANNEAL_LEAN_RUN_IN_SCOPE=1`),
        # the wrapper executes `_exec_passthrough` (no slot wait, no OOM retry, no internal timer),
        # so `_outer_timeout_sec` returns the exact step budget unless `--nested-ok` is set.
        self.assertEqual(
            suite._outer_timeout_sec(cmd_build, 600, env={"ANNEAL_LEAN_RUN_IN_SCOPE": "1"}),
            600,
        )
        self.assertEqual(
            suite._outer_timeout_sec(cmd_nested, 600, env={"ANNEAL_LEAN_RUN_IN_SCOPE": "1"}),
            build_wait + max(600, suite.LEAN_RUN_OOM_RETRY_WINDOW_SEC) + grace,
        )

        # `ANNEAL_LSP_NO_EVICT=1` disables on-OOM retry in `anneal-lean-run`, matching `--no-oom-retry`.
        self.assertEqual(
            suite._outer_timeout_sec(cmd_build, 600, env={"ANNEAL_LSP_NO_EVICT": "1"}),
            build_wait + 600 + grace,
        )

        # `auto` mode scans past Lake global options (`--dir`, `-d`, `-q`, `+toolchain`, `--`)
        # before `env lean`, matching `scripts/anneal-lean-run`'s `_lake_env_lean_index`.
        for file_cmd in (
            [lr, "--timeout", "180", "--", "lake", "--dir", "examples", "env", "lean", "Foo.lean"],
            [lr, "--timeout", "180", "--", "lake", "-dexamples", "-q", "env", "--", "lean", "Foo.lean"],
            [lr, "--timeout", "180", "--", "lake", "+nightly", "-Kfoo=bar", "env", "lean", "Foo.lean"],
        ):
            self.assertEqual(suite._lean_run_wrapper_flags(file_cmd), ("file", 180, True), file_cmd)
            self.assertEqual(suite._outer_timeout_sec(file_cmd, 180, env={}), file_wait + 180 + grace, file_cmd)
        run_cmd = [lr, "--timeout", "180", "--", "lake", "--dir", "examples", "env", "lean", "--run", "Foo.lean"]
        self.assertEqual(suite._lean_run_wrapper_flags(run_cmd)[0], "build")

    def test_auto_mode_detection_matches_the_in_repo_wrapper(self) -> None:
        # `_lake_env_lean_index` and its three option tables are a copy of the wrapper's
        # (`detect_mode`). Load the wrapper and compare, so the copy cannot drift silently.
        loader = importlib.machinery.SourceFileLoader(
            "anneal_lean_run_under_test", os.fspath(REPO_ROOT / "scripts/anneal-lean-run")
        )
        wrapper = importlib.util.module_from_spec(importlib.util.spec_from_loader(loader.name, loader))
        with mock.patch.object(sys, "dont_write_bytecode", True):
            loader.exec_module(wrapper)
        for table in ("_LAKE_VALUE_OPTS", "_LAKE_VALUE_EQ_PREFIXES", "_LAKE_FLAG_OPTS"):
            self.assertEqual(set(getattr(suite, table)), set(getattr(wrapper, table)), table)
        lr = "/opt/bin/anneal-lean-run"
        for inner in (
            ["lean", "Foo.lean"],
            ["/toolchain/bin/lean", "--run", "Foo.lean"],
            ["lake", "env", "lean", "Foo.lean"],
            ["lake", "env", "--", "lean", "Foo.lean"],
            ["lake", "env", "lean", "--run", "Foo.lean"],
            ["lake", "--dir", "examples", "env", "lean", "Foo.lean"],
            ["lake", "-d", "examples", "-q", "env", "lean", "Foo.lean"],
            ["lake", "-dexamples", "+nightly", "-Kfoo=bar", "--wfail", "env", "lean", "Foo.lean"],
            ["lake", "--file=lakefile.toml", "--packages=p.json", "env", "lean", "Foo.lean"],
            ["lake", "--dir", "examples", "build", "LeanMiriSpec"],
            ["lake", "--unknown-flag", "env", "lean", "Foo.lean"],
            ["lake", "--", "env", "lean", "Foo.lean"],
            ["lake", "-d"],
            ["lake", "env"],
            ["lake", "env", "printenv"],
            ["lake", "exe", "lean", "Foo.lean"],
            ["cargo", "test"],
            ["env", "lean", "Foo.lean"],
        ):
            expected = wrapper.detect_mode(inner, "auto")
            self.assertEqual(suite._lean_run_wrapper_flags([lr, "--", *inner])[0], expected, inner)
            self.assertEqual(suite._lean_run_wrapper_flags([lr, *inner])[0], expected, inner)

    def test_wrapper_option_tables_and_memory_probe_match_the_in_repo_wrapper(self) -> None:
        # `_LEAN_RUN_VALUE_OPTS` / `_LEAN_RUN_BOOL_OPTS` / `_LEAN_RUN_NON_EXEC_OPTS` are a copy of
        # the wrapper's `build_parser()`, and the two-probe protocol of
        # `_probe_lean_run_memory_max_mib` mirrors its `resolve_effective_concurrency`. The other
        # probe tests answer from a hand-written table, which encodes what the suite assumes
        # about the wrapper. Here the in-repo wrapper's own parser and memory envelope answer
        # (in process, no subprocess), so neither copy can drift silently.
        loader = importlib.machinery.SourceFileLoader(
            "anneal_lean_run_probe_under_test", os.fspath(REPO_ROOT / "scripts/anneal-lean-run")
        )
        wrapper = importlib.util.module_from_spec(importlib.util.spec_from_loader(loader.name, loader))
        with mock.patch.object(sys, "dont_write_bytecode", True):
            loader.exec_module(wrapper)
        # `build_parser` reads `ANNEAL_LEAN_MEMORY_MAX_MB` / `ANNEAL_LEAN_TIMEOUT_SEC` defaults.
        with mock.patch.dict(os.environ, clear=True):
            parser = wrapper.build_parser()

        # 1. Option tables: every wrapper option, split by whether it takes a value, and the
        #    ones after which the wrapper never runs the wrapped command.
        actions = parser._option_string_actions
        self.assertEqual({o for o, a in actions.items() if a.nargs != 0}, set(suite._LEAN_RUN_VALUE_OPTS))
        self.assertEqual({o for o, a in actions.items() if a.nargs == 0}, set(suite._LEAN_RUN_BOOL_OPTS))
        self.assertEqual(
            {o for o, a in actions.items() if a.dest in ("help", "probe", "ensure_slice")},
            set(suite._LEAN_RUN_NON_EXEC_OPTS),
        )

        def parse(argv: list[str]):
            """The wrapper's parsed arguments, or its `SystemExit` code (help: 0, usage error: 2)."""
            try:
                with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
                    return parser.parse_args(argv)
            except SystemExit as exc:
                return int(exc.code or 0)

        def make_host(mem_total: int, mem_avail: int, cores: int, c_high: int | None) -> dict:
            ancestors = (
                []
                if c_high is None
                else [
                    {
                        "path": "/sys/fs/cgroup/user.slice",
                        "name": "user.slice",
                        "c_high_mb": c_high,
                        "w_mb": 512,
                        "is_shared_user_slice": False,
                    }
                ]
            )
            return dict(cpu_cores=cores, mem_total_mb=mem_total, mem_avail_mb=mem_avail, ancestors=ancestors)

        def plan(host: dict, w_file: int | None, args, mode: str, is_probe: bool) -> dict:
            return wrapper.compute_workload_memory_envelope(
                **host,
                w_file=w_file,
                cli_concurrency=args.concurrency,
                exclusive=args.exclusive,
                is_probe=is_probe,
                mode=mode,
                override_mem_mb=args.memory_max_mb,
                override_timeout_sec=args.timeout,
                unsafe_ignore_cgroup=args.unsafe_ignore_cgroup,
            )

        # What the fake `subprocess.run` answers: `w_files[k]` is the host's concurrency file
        # at the k-th probe (the last entry repeats), and probes from `fail_from` on exit 1.
        state: dict = {"host": make_host(65536, 60000, 32, None), "w_files": [None], "fail_from": None}
        calls: list[list[str]] = []

        def fake_run(argv: list[str], **_kwargs: object) -> subprocess.CompletedProcess:
            calls.append(list(argv))
            if state["fail_from"] is not None and len(calls) >= state["fail_from"]:
                return subprocess.CompletedProcess(argv, 1, "", "probe failed")
            args = parse(list(argv[1:]))
            if isinstance(args, int):
                return subprocess.CompletedProcess(argv, args, "usage: anneal-lean-run", "")
            # Every probe the suite spawns is a pure `--probe --json` with no wrapped command.
            self.assertTrue(args.probe and args.json and not args.ensure_slice and not args.cmd, argv)
            w_file = state["w_files"][min(len(calls), len(state["w_files"])) - 1]
            limits = plan(state["host"], w_file, args, wrapper.detect_mode([], args.mode), True)
            return subprocess.CompletedProcess(argv, 0, json.dumps(limits), "")

        def probe(cmd: list[str]) -> int | None:
            calls.clear()
            with mock.patch.object(suite.subprocess, "run", side_effect=fake_run):
                return suite._probe_lean_run_memory_max_mib(cmd, env={})

        lr = "/opt/bin/anneal-lean-run"

        # 2. The suite reports a cap exactly when the wrapper would run the wrapped command, and
        #    never spawns it for help / `--probe` / `--ensure-slice` (which mutates systemd units).
        for opts in (
            ["-h"],
            ["-hW1"],
            ["--he"],
            ["--probe"],
            ["--pro"],
            ["--print"],
            ["--ensure"],
            ["--ens", "--json"],
            ["--pr"],  # Ambiguous abbreviations and bad values: the wrapper exits 2.
            ["--e"],
            ["--no"],
            ["--m", "file"],
            ["--mode", "bogus"],
            ["-W", "x"],
            ["-W", "--ensure-slice"],
            ["--mode", "-h"],
            ["--timeout", "--ensure-slice"],
            ["--", "--ensure-slice"],
            [],
            ["--json"],
            ["--ex"],
            ["-W", "2"],
            ["-W2"],
            ["-W=2"],
            ["--conc=2"],
            ["--mode=file"],
            ["--nested", "--no-s", "--no-o"],
            ["--t", "5", "--me", "9000", "--u"],
        ):
            for tail in (["--", "lake", "build"], ["lake", "build"], ["--"], []):
                parsed = parse([*opts, *tail])
                executes = (
                    not isinstance(parsed, int)
                    and not parsed.probe
                    and not parsed.ensure_slice
                    and bool(parsed.cmd[1:] if parsed.cmd[:1] == ["--"] else parsed.cmd)
                )
                got = probe([lr, *opts, *tail])
                self.assertEqual(got is not None, executes, (opts, tail))
                if parsed == 0 or (not isinstance(parsed, int) and not executes):
                    self.assertEqual(calls, [], (opts, tail))

        # 3. The cap the suite derives is the `MemoryMax` the wrapper executes with, in at most
        #    two probes. When only the re-probe fails, or the host's concurrency file changes
        #    between the two probes, it is still at most that `MemoryMax` (fail-closed: callers
        #    single-thread below a threshold).
        reprobed = clamped = 0
        for host in (
            make_host(16384, 14000, 8, None),
            make_host(65536, 60000, 32, None),
            make_host(65536, 60000, 32, 49152),
            make_host(262144, 200000, 96, 131072),
        ):
            for w_file in (None, 1, 2, 4):
                for cli_opts in (
                    [],
                    ["--concurrency", "1"],
                    ["-W2"],
                    ["--conc=3"],
                    ["--concurrency", "1", "--exclusive"],
                    ["--concurrency", "3", "--exclusive"],
                ):
                    for inner in (["lake", "build", "MiniRustSpec"], ["lake", "env", "lean", "Foo.lean"]):
                        for extra in ([], ["--memory-max-mb", "9000"]):
                            cmd = [lr, *cli_opts, *extra, "--timeout", "900", "--", *inner]
                            case = (host["mem_total_mb"], bool(host["ancestors"]), w_file, cli_opts, inner[1], extra)
                            args = parse(cmd[1:])
                            mode = wrapper.detect_mode(inner, args.mode)

                            def executed_cap(w_file_at_exec: int | None) -> int:
                                return plan(host, w_file_at_exec, args, mode, False)["memory_max_mb"]

                            want = executed_cap(w_file)
                            self.assertGreater(want, 0, case)
                            state.update(host=host, w_files=[w_file], fail_from=None)
                            self.assertEqual(probe(cmd), want, case)
                            self.assertLessEqual(len(calls), 2, case)
                            if len(calls) < 2:
                                continue
                            reprobed += 1
                            self.assertIsNotNone(w_file, case)

                            state.update(fail_from=2)
                            low = probe(cmd)
                            self.assertIsNotNone(low, case)
                            self.assertTrue(1 <= low <= want, (case, low, want))

                            for drifted in (w_file + 2, max(1, w_file - 1)):
                                state.update(w_files=[w_file, drifted], fail_from=None)
                                got = probe(cmd)
                                self.assertEqual(len(calls), 2, case)
                                self.assertIsNotNone(got, case)
                                self.assertLessEqual(got, executed_cap(drifted), (case, drifted))
                                clamped += executed_cap(drifted) < want and got < want
        self.assertGreater(reprobed, 0)
        self.assertGreater(clamped, 0)

    def test_run_step_survives_real_wrapper_slot_contention_exceeding_step_budget(self) -> None:
        # End-to-end verification under real `flock` build-slot contention using the actual
        # `scripts/anneal-lean-run` implementation (isolated to a temp runtime dir so it never
        # touches host build slots or systemd):
        # 1. A `build` step with `timeout_sec=1` queues behind a held slot lock for ~2.2s
        #    (> `timeout_sec`), then runs within its 1s budget and PASSes because
        #    `_outer_timeout_sec` covers the wrapper's slot queue wait.
        # 2. With `ANNEAL_LEAN_RUN_IN_SCOPE=1` (re-entrancy pass-through, where the real
        #    wrapper `exec`s immediately with no slot lock and no internal `--timeout`),
        #    a 5s command under `timeout_sec=1` times out cleanly near 1s instead of hanging
        #    for the wrapped build deadline.
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            runtime_dir = root / "rt"
            slot_dir = runtime_dir / f"anneal-build-slots-{os.getuid()}"
            slot_dir.mkdir(parents=True)
            marker = root / "ran.txt"
            shim = root / "anneal-lean-run"
            wrapper_src = REPO_ROOT / "scripts/anneal-lean-run"
            shim.write_text(
                f"#!{sys.executable}\n"
                "import importlib.machinery, importlib.util, pathlib, sys\n"
                "sys.dont_write_bytecode = True\n"
                f"loader = importlib.machinery.SourceFileLoader('alr_real', {os.fspath(wrapper_src)!r})\n"
                "spec = importlib.util.spec_from_loader(loader.name, loader)\n"
                "mod = importlib.util.module_from_spec(spec)\n"
                "loader.exec_module(mod)\n"
                f"rt = pathlib.Path({os.fspath(runtime_dir)!r})\n"
                "mod.resolve_runtime_base = lambda: (rt, False)\n"
                "orig_probe = mod.probe_host_envelope\n"
                "def _probe(*a, **kw):\n"
                "    d = orig_probe(*a, **kw)\n"
                "    d['build_slots'] = 1\n"
                "    d['runtime_base'] = str(rt)\n"
                "    d['user_systemd_active'] = False\n"
                "    d['systemd_user_scope'] = False\n"
                "    d['memory_max_mb'] = max(int(d.get('memory_max_mb', 0)), 4096)\n"
                "    return d\n"
                "mod.probe_host_envelope = _probe\n"
                "sys.exit(mod.main(sys.argv[1:]))\n",
                encoding="utf-8",
            )
            shim.chmod(0o755)

            lock_path = slot_dir / "slot-1.lock"
            lock_fd = os.open(os.fspath(lock_path), os.O_CREAT | os.O_RDWR, 0o600)
            fcntl.flock(lock_fd, fcntl.LOCK_EX | fcntl.LOCK_NB)

            def release_later() -> None:
                time.sleep(2.2)
                os.close(lock_fd)

            holder = threading.Thread(target=release_later, daemon=True)
            holder.start()
            try:
                cmd = [
                    os.fspath(shim),
                    "--mode",
                    "build",
                    "--concurrency",
                    "1",
                    "--timeout",
                    "1",
                    "--",
                    sys.executable,
                    "-c",
                    f"import pathlib; pathlib.Path({os.fspath(marker)!r}).write_text('ok')",
                ]
                res = suite._run_step(
                    "queued_real_wrapper_build",
                    "cat1_trusted_boundary",
                    cmd,
                    cwd=root,
                    timeout_sec=1,
                )
            finally:
                holder.join(timeout=5.0)

            self.assertEqual(res["status"], "PASS", res.get("failure_excerpt"))
            self.assertEqual(marker.read_text(encoding="utf-8"), "ok")
            self.assertGreaterEqual(res["duration_sec"], 2.0)

            # Negative control: in passthrough mode (`ANNEAL_LEAN_RUN_IN_SCOPE=1`),
            # the wrapper executes `exec` directly with no internal timer, so the
            # outer deadline enforces `timeout_sec=1` promptly rather than waiting 2430s.
            sleep_cmd = [
                os.fspath(shim),
                "--mode",
                "build",
                "--timeout",
                "1",
                "--",
                sys.executable,
                "-c",
                "import time; time.sleep(10)",
            ]
            res_pt = suite._run_step(
                "passthrough_real_wrapper_timeout",
                "cat1_trusted_boundary",
                sleep_cmd,
                cwd=root,
                timeout_sec=1,
                env_overrides={"ANNEAL_LEAN_RUN_IN_SCOPE": "1"},
            )
            self.assertEqual(res_pt["status"], "TIMEOUT")
            self.assertEqual(res_pt["exit_code"], 124)
            self.assertLess(res_pt["duration_sec"], 5.0)

    def test_run_step_empty_cmd_and_dashboard_corrupt_state_json_resilience(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            # Empty `cmd` must fail cleanly with exit 127 rather than crashing with `IndexError`.
            empty_res = suite._run_step("empty_step", "cat7_python_and_ci_tests", [], cwd=root, timeout_sec=10)
            self.assertEqual(empty_res["status"], "FAIL")
            self.assertEqual(empty_res["exit_code"], 127)
            self.assertIn("<empty>", empty_res["failure_excerpt"])

            # Non-dict / malformed `LATEST_CAMPAIGN_SUMMARY.json` and `correspondence_ratchet.json`
            # must never crash `run_suite_and_generate_dashboard`.
            state_dir = root / "state_out"
            difftest_dir = root / "difftest_in"
            (state_dir / "state").mkdir(parents=True)
            (difftest_dir / "reports").mkdir(parents=True)
            (difftest_dir / "reports/LATEST_CAMPAIGN_SUMMARY.json").write_text("[]\n", encoding="utf-8")
            (state_dir / "state/correspondence_ratchet.json").write_text(
                '{"high_water_minirust_audited_decls": "corrupt", "high_water_blended_completeness_pct": true}\n',
                encoding="utf-8",
            )
            code, dashboard, _md = suite.run_suite_and_generate_dashboard(
                repo_root=REPO_ROOT,
                profile="census-only",
                state_dir=state_dir,
                difftest_dir=difftest_dir,
            )
            self.assertEqual(code, suite.EXIT_SUCCESS)
            self.assertEqual(
                dashboard["pillar_2_correctness_and_correspondence"]["latest_differential_testing"]["overall_status"],
                "unknown",
            )
            ratchet = json.loads((state_dir / "state/correspondence_ratchet.json").read_text(encoding="utf-8"))
            self.assertIsInstance(ratchet["high_water_minirust_audited_decls"], int)
            self.assertIsInstance(ratchet["high_water_blended_completeness_pct"], float)

    def test_tracecheck_import_isolation_matches_check_trusted_downstream_targets(self) -> None:
        tc_path = REPO_ROOT / "theory/Anneal/Rustc/V2026_06_01/TraceCheck.lean"
        tc_imports = suite._lean_header_imports(tc_path)
        self.assertIsNotNone(tc_imports)
        assert tc_imports is not None
        self.assertNotIn("Anneal.Rustc.V2026_06_01.SymbolicEval", tc_imports)

        # Load `DOWNSTREAM_TARGETS` from `trusted/audit/check_trusted.py` and verify exact parity
        # for `TraceCheck`, `Lower`, and `SymbolicEval`.
        check_trusted_src = (REPO_ROOT / "trusted/audit/check_trusted.py").read_text(encoding="utf-8")
        m = re.search(
            r'\("Anneal\.Rustc\.V2026_06_01\.TraceCheck",\s*"[^"]+",\s*(\[[^\]]+\]),\s*"theory"\)',
            check_trusted_src,
        )
        self.assertIsNotNone(m, "TraceCheck entry missing from check_trusted.py DOWNSTREAM_TARGETS")
        assert m is not None
        expected_tc_imports = json.loads(m.group(1))
        actual_tc_proj = [imp for imp in tc_imports if not imp.startswith(("Init", "Std"))]
        self.assertEqual(actual_tc_proj, expected_tc_imports)

        # Also verify `Lower.lean` required zero new imports.
        lower_imports = suite._lean_header_imports(
            REPO_ROOT / "theory/Anneal/Rustc/V2026_06_01/Lower.lean"
        )
        self.assertIsNotNone(lower_imports)
        assert lower_imports is not None
        m_lower = re.search(
            r'\("Anneal\.Rustc\.V2026_06_01\.Lower",\s*"[^"]+",\s*(\[[^\]]+\]),\s*"theory"\)',
            check_trusted_src,
        )
        self.assertIsNotNone(m_lower)
        assert m_lower is not None
        self.assertEqual(
            [imp for imp in lower_imports if not imp.startswith(("Init", "Std"))],
            json.loads(m_lower.group(1)),
        )

        # The re-export keeps `SymbolicEval` importing `Lower` (never the reverse), and neither
        # the consumers of the moved names nor the memory-slimmed `MirLiftCore` gained or lost
        # an import: every registered header is still matched exactly.
        self.assertNotIn("Anneal.Rustc.V2026_06_01.SymbolicEval", lower_imports)
        for module in (
            "Anneal.Rustc.V2026_06_01.SymbolicEval",
            "Anneal.Rustc.V2026_06_01.SymReflect",
            "Anneal.MirFuelFree",
            "Anneal.MirLiftCore",
        ):
            entry = re.search(
                rf'\("{re.escape(module)}",\s*"([^"]+)",\s*(\[[^\]]*\]),\s*"theory"\)', check_trusted_src
            )
            self.assertIsNotNone(entry, f"{module} missing from check_trusted.py DOWNSTREAM_TARGETS")
            assert entry is not None
            registered = json.loads(entry.group(2))
            imports = suite._lean_header_imports(REPO_ROOT / entry.group(1))
            self.assertIsNotNone(imports, module)
            assert imports is not None
            self.assertEqual(
                [imp for imp in imports if imp in registered or not imp.startswith(("Init", "Std"))],
                registered,
                module,
            )

    def test_domain_integration_tests_anneal_difftest_config_and_timeout_invariants(self) -> None:
        nightly_steps = suite.build_suite_steps(REPO_ROOT, "nightly")
        self.assertEqual(len(nightly_steps), 31)
        for step in nightly_steps:
            self.assertEqual(len(step), 4)
        by_name = {name: (cat, cmd, timeout) for name, cat, cmd, timeout in nightly_steps}
        self.assertIn("domain_integration_tests_anneal_difftest", by_name)
        cat, cmd, timeout = by_name["domain_integration_tests_anneal_difftest"]
        self.assertEqual(cat, "cat4_rust_domain_integration_tests")
        self.assertEqual(timeout, 1500)
        self.assertTrue(suite._is_lean_run_wrapped(cmd))
        mode, inner_timeout, slot_lock = suite._lean_run_wrapper_flags(cmd)
        self.assertEqual(mode, "build")
        self.assertEqual(inner_timeout, timeout)
        self.assertTrue(slot_lock)
        sep = cmd.index("--")
        self.assertEqual(
            cmd[sep + 1 :],
            [
                "cargo",
                "test",
                "--manifest-path",
                "crates/anneal-difftest/Cargo.toml",
                "--lib",
                "--bins",
                "--tests",
                "--locked",
            ],
        )
        outer_timeout = suite._outer_timeout_sec(cmd, timeout)
        self.assertGreater(outer_timeout, timeout)
        # Step env always receives Lake artifact-cache restoration defaults and never leaks into os.environ.
        before_env = os.environ.copy()
        step_env = suite._build_step_env("domain_integration_tests_anneal_difftest")
        self.assertEqual(step_env["LAKE_ARTIFACT_CACHE"], "true")
        self.assertEqual(step_env["LAKE_RESTORE_ARTIFACTS"], "true")
        self.assertEqual(os.environ, before_env)


if __name__ == "__main__":
    unittest.main()
