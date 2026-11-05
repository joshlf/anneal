// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! End-to-end integration test for the Rust artifact trace observer and
//! Lean 4 `TraceCheck` consistency verifier.
//!
//! Exercises the complete pipeline:
//! 1. Compiles and captures a real Rust crate (`trace_pkg`) through
//!    `anneal-rustc-capture` (`run_cargo_capture` +
//!    `scaffold_workspace_with_config`), extracting `Mir.TracePkg.*` modules
//!    with compiler-computed `LayoutTable`s and `LocalDecl`s.
//! 2. Executes the unmodified Rust root functions (`trace_pkg::process_packet`
//!    and `trace_pkg::inspect_ptr_identity`) under `TraceRecorder::observe_root`
//!    / `TraceRecorder::observe_root_with_inlined_callees`, capturing raw
//!    `&[u8]` byte slices via `value_as_raw_bytes` at root entry/exit and at
//!    `#[anneal_trace::external]` boundaries (`ext_scale_add`, `helper_double`),
//!    including a `#[repr(C)]` struct `PaddedConfig` with deliberately corrupted
//!    uninitialized padding bytes and a watched allocation registered in the
//!    shadow provenance table (`register_allocation`).
//! 3. Generates Lean 4 `TraceVerify` modules via `render_trace_check_lean_module`
//!    and diagnostic/tampered-outcome snippets via
//!    `render_trace_diag_eval_lean_snippet` and
//!    `render_tampered_outcome_diag_lean_snippet`, invoking `lake env lean`
//!    inside the scaffolded `.anneal/` workspace to kernel-verify:
//!    - **Design Choice 1 (Interposition & Branch Erasure)**:
//!      - Call-boundary-only checking (`check_branches = false`) against
//!        `mirObsErasedStatefulTree` (`checkRawByteTraceObsErasedBounded_sound`
//!        and `diagnoseRawByteTraceObsErasedBounded`),
//!      - Full branch + call checking (`check_branches = true`) against
//!        `mirStatefulTree` (`checkRawByteTraceFullBounded_sound` and
//!        `diagnoseRawByteTraceFullBounded`),
//!      - Transparent callee inlining (`inlined_callee_modules`) where
//!        `helper_double` steps via `.tau` while `ext_scale_add` is checked at
//!        its `MirCallE` boundary,
//!      - Deterministic negative diagnostic classification of tampered traces
//!        (`(diagnoseRawByteTraceObsErasedBounded ...).tagName = "outcome_mismatch" := by rfl`).
//!    - **Design Choice 2 (Raw Byte Decoding & Shadow Provenance)**:
//!      - Decoding raw `&[u8]` struct bytes with arbitrary padding garbage
//!        using `Mir.TracePkg.process_packet.body.layouts`,
//!      - Translating native 64-bit runtime pointer addresses via
//!        `ShadowProvenanceTable` to `Value.ptr { allocId, offsetBytes }`.

use std::env;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::{SystemTime, UNIX_EPOCH};

use cargo_anneal::{
    BatchTraceEvalCase, CaptureDriverConfig, RecordedEvent, RecordedOutcome, RecordedShadowAlloc,
    ScaffoldConfig, TraceCheckModuleConfig, TraceRecorder, capture_value_bytes,
    render_batch_trace_eval_lean_module, render_raw_byte_trace_lean,
    render_raw_byte_trace_lean_def, render_shadow_provenance_table_lean,
    render_tampered_outcome_diag_lean_snippet, render_trace_check_lean_module,
    render_trace_diag_eval_lean_snippet, run_cargo_capture, run_lake_verify_targets,
    scaffold_workspace_with_config, value_as_raw_bytes,
};

fn unique_temp_dir(label: &str) -> PathBuf {
    let nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("system clock after epoch")
        .as_nanos();
    let dir = env::temp_dir().join(format!(
        "cargo-anneal-trace-e2e-{}-{}-{}",
        label,
        std::process::id(),
        nanos
    ));
    fs::create_dir_all(&dir).expect("create temporary directory");
    dir
}

fn anneal_checkout_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(Path::parent)
        .expect("resolve Anneal workspace root from CARGO_MANIFEST_DIR")
        .to_path_buf()
}

fn ensure_rustc_capture_binary(checkout_root: &Path) -> PathBuf {
    let exe_name = format!("anneal-rustc-capture{}", env::consts::EXE_SUFFIX);
    let target_dir = env::var_os("CARGO_TARGET_DIR")
        .map(PathBuf::from)
        .unwrap_or_else(|| checkout_root.join("target"));
    let default_bin = target_dir.join("debug").join(&exe_name);

    let cargo_bin = env::var("CARGO").unwrap_or_else(|_| "cargo".to_string());
    let status = Command::new(cargo_bin)
        .current_dir(checkout_root)
        .arg("build")
        .arg("-p")
        .arg("anneal-rustc-capture")
        .arg("--bin")
        .arg("anneal-rustc-capture")
        .status()
        .expect("build anneal-rustc-capture binary");
    assert!(
        status.success(),
        "cargo build -p anneal-rustc-capture must succeed"
    );
    assert!(
        default_bin.is_file(),
        "expected compiled wrapper binary at {}",
        default_bin.display()
    );
    default_bin
}

/// Exact `trace_pkg` module compiled both natively (under `#[cfg(test)]`, where
/// `#[anneal_trace::external]` records boundary calls) and by
/// `anneal-rustc-capture` (`cargo check`, where `#[anneal_trace::external]`
/// emits the unmodified function bodies).
mod trace_pkg {
    #[anneal_trace::capture]
    #[repr(C)]
    #[derive(Clone, Copy, Debug)]
    pub struct PaddedConfig {
        pub mode: u8,
        pub threshold: u32,
    }

    #[anneal_trace::external]
    #[inline(never)]
    pub fn ext_scale_add(x: u32, bonus: u32) -> u32 {
        x + bonus
    }

    #[anneal_trace::external]
    #[inline(never)]
    pub fn helper_double(x: u32) -> u32 {
        x + x
    }

    pub fn process_packet(cfg: PaddedConfig, input: u32) -> u32 {
        if cfg.mode == 0 {
            helper_double(input)
        } else {
            let scaled = ext_scale_add(input, cfg.threshold);
            helper_double(scaled)
        }
    }

    pub fn inspect_ptr_identity(p: &u32) -> &u32 {
        p
    }

    #[allow(dead_code)]
    pub fn transmute_padded_to_u64(cfg: PaddedConfig) -> u64 {
        unsafe { core::mem::transmute::<PaddedConfig, u64>(cfg) }
    }

    pub fn deref_shared_u32(p: &u32) -> u32 {
        *p + 1
    }

    pub fn deref_mut_u32(p: &mut u32) -> u32 {
        *p += 5;
        *p
    }

    pub fn deref_padded_config(p: &PaddedConfig) -> u32 {
        (p.mode as u32) + p.threshold
    }

    pub fn deref_only_threshold(p: &PaddedConfig) -> u32 {
        p.threshold
    }

    #[anneal_trace::capture]
    #[derive(Clone, Copy, Debug)]
    pub struct RustReordered {
        pub a: u8,
        pub b: u32,
    }

    pub fn deref_rust_reordered(p: &RustReordered) -> u32 {
        (p.a as u32) + p.b
    }

    #[repr(u8)]
    #[derive(Clone, Copy, Debug)]
    pub enum PaddedEnum {
        Pair(u8, u32) = 0,
        #[allow(dead_code)]
        Single(u8) = 1,
    }

    pub fn sum_padded_array(arr: [PaddedConfig; 2]) -> u32 {
        (arr[0].mode as u32) + arr[0].threshold + (arr[1].mode as u32) + arr[1].threshold
    }

    pub fn eval_padded_enum(e: PaddedEnum) -> u32 {
        match e {
            PaddedEnum::Pair(tag_val, count) => (tag_val as u32) + count,
            PaddedEnum::Single(v) => v as u32,
        }
    }

    #[anneal_trace::external]
    #[inline(never)]
    pub fn ext_read_shared(p: &u32) -> u32 {
        *p + 10
    }

    pub fn call_ext_shared_ref(p: &u32) -> u32 {
        ext_read_shared(p)
    }

    #[anneal_trace::external]
    #[inline(never)]
    pub fn ext_bump_mut(p: &mut u32) -> u32 {
        *p += 1;
        *p
    }

    pub fn call_ext_mut_ref(mut x: u32) -> u32 {
        ext_bump_mut(&mut x)
    }

    #[anneal_trace::external]
    #[inline(never)]
    #[allow(clippy::not_unsafe_ptr_arg_deref)]
    pub fn ext_read_raw_ptr(p: *const u32) -> u32 {
        unsafe { *p }
    }

    pub fn call_ext_raw_ptr(x: u32) -> u32 {
        ext_read_raw_ptr(&x as *const u32)
    }

    #[repr(transparent)]
    pub struct MutWrapper<'a>(pub &'a mut u32);

    impl cargo_anneal::trace_observer::TraceCapture for MutWrapper<'_> {
        fn write_captured_bytes(&self, dst: &mut [Option<u8>]) {
            self.0.write_captured_bytes(dst);
        }
    }

    #[anneal_trace::external]
    #[inline(never)]
    pub fn ext_bump_mut_wrapper(w: MutWrapper<'_>) -> u32 {
        *w.0 += 1;
        *w.0
    }

    pub fn call_ext_mut_wrapper(mut x: u32) -> u32 {
        ext_bump_mut_wrapper(MutWrapper(&mut x))
    }

    #[repr(transparent)]
    #[derive(Clone, Copy)]
    pub struct RawPtrWrapper(pub *const u32);

    impl cargo_anneal::trace_observer::TraceCapture for RawPtrWrapper {
        fn write_captured_bytes(&self, dst: &mut [Option<u8>]) {
            self.0.write_captured_bytes(dst);
        }
    }

    #[anneal_trace::external]
    #[inline(never)]
    pub fn ext_read_raw_wrapper(w: RawPtrWrapper) -> u32 {
        unsafe { *w.0 }
    }

    pub fn call_ext_raw_wrapper(x: u32) -> u32 {
        ext_read_raw_wrapper(RawPtrWrapper(&x as *const u32))
    }
}

const TRACE_PKG_LIB_RS: &str = r#"#![allow(dead_code)]

#[anneal_trace::capture]
#[repr(C)]
#[derive(Clone, Copy, Debug)]
pub struct PaddedConfig {
    pub mode: u8,
    pub threshold: u32,
}

#[anneal_trace::external]
#[inline(never)]
pub fn ext_scale_add(x: u32, bonus: u32) -> u32 {
    x + bonus
}

#[anneal_trace::external]
#[inline(never)]
pub fn helper_double(x: u32) -> u32 {
    x + x
}

pub fn process_packet(cfg: PaddedConfig, input: u32) -> u32 {
    if cfg.mode == 0 {
        helper_double(input)
    } else {
        let scaled = ext_scale_add(input, cfg.threshold);
        helper_double(scaled)
    }
}

pub fn inspect_ptr_identity(p: &u32) -> &u32 {
    p
}

pub fn transmute_padded_to_u64(cfg: PaddedConfig) -> u64 {
    unsafe { core::mem::transmute::<PaddedConfig, u64>(cfg) }
}

pub fn deref_shared_u32(p: &u32) -> u32 {
    *p + 1
}

pub fn deref_mut_u32(p: &mut u32) -> u32 {
    *p += 5;
    *p
}

pub fn deref_padded_config(p: &PaddedConfig) -> u32 {
    (p.mode as u32) + p.threshold
}

pub fn deref_only_threshold(p: &PaddedConfig) -> u32 {
    p.threshold
}

#[derive(Clone, Copy, Debug)]
pub struct RustReordered {
    pub a: u8,
    pub b: u32,
}

pub fn deref_rust_reordered(p: &RustReordered) -> u32 {
    (p.a as u32) + p.b
}

#[repr(u8)]
#[derive(Clone, Copy, Debug)]
pub enum PaddedEnum {
    Pair(u8, u32) = 0,
    Single(u8) = 1,
}

pub fn sum_padded_array(arr: [PaddedConfig; 2]) -> u32 {
    (arr[0].mode as u32) + arr[0].threshold + (arr[1].mode as u32) + arr[1].threshold
}

pub fn eval_padded_enum(e: PaddedEnum) -> u32 {
    match e {
        PaddedEnum::Pair(tag_val, count) => (tag_val as u32) + count,
        PaddedEnum::Single(v) => v as u32,
    }
}

#[anneal_trace::external]
#[inline(never)]
pub fn ext_read_shared(p: &u32) -> u32 {
    *p + 10
}

pub fn call_ext_shared_ref(p: &u32) -> u32 {
    ext_read_shared(p)
}

#[anneal_trace::external]
#[inline(never)]
pub fn ext_bump_mut(p: &mut u32) -> u32 {
    *p += 1;
    *p
}

pub fn call_ext_mut_ref(mut x: u32) -> u32 {
    ext_bump_mut(&mut x)
}

#[anneal_trace::external]
#[inline(never)]
pub fn ext_read_raw_ptr(p: *const u32) -> u32 {
    unsafe { *p }
}

pub fn call_ext_raw_ptr(x: u32) -> u32 {
    ext_read_raw_ptr(&x as *const u32)
}

#[repr(transparent)]
pub struct MutWrapper<'a>(pub &'a mut u32);

#[anneal_trace::external]
#[inline(never)]
pub fn ext_bump_mut_wrapper(w: MutWrapper<'_>) -> u32 {
    *w.0 += 1;
    *w.0
}

pub fn call_ext_mut_wrapper(mut x: u32) -> u32 {
    ext_bump_mut_wrapper(MutWrapper(&mut x))
}

#[repr(transparent)]
#[derive(Clone, Copy)]
pub struct RawPtrWrapper(pub *const u32);

#[anneal_trace::external]
#[inline(never)]
pub fn ext_read_raw_wrapper(w: RawPtrWrapper) -> u32 {
    unsafe { *w.0 }
}

pub fn call_ext_raw_wrapper(x: u32) -> u32 {
    ext_read_raw_wrapper(RawPtrWrapper(&x as *const u32))
}
"#;

#[test]
fn batch_trace_module_rendering_and_tampered_diag_contract() {
    let mut cfg_val = trace_pkg::PaddedConfig {
        mode: 1,
        threshold: 11,
    };
    unsafe {
        let base = (&mut cfg_val as *mut trace_pkg::PaddedConfig).cast::<u8>();
        *base.add(1) = 0xAA;
        *base.add(2) = 0xBB;
        *base.add(3) = 0xCC;
    }
    let raw_cfg_bytes = value_as_raw_bytes(&cfg_val);
    assert_eq!(
        capture_value_bytes(&cfg_val),
        vec![
            Some(1),
            None,
            None,
            None,
            Some(11),
            Some(0),
            Some(0),
            Some(0)
        ]
    );
    assert_eq!(raw_cfg_bytes, vec![1, 0, 0, 0, 11, 0, 0, 0]);
    let input_val: u32 = 10;
    let raw_input_bytes = value_as_raw_bytes(&input_val);

    let (res, trace) = TraceRecorder::observe_root_with_inlined_callees(
        "trace_pkg::process_packet",
        vec![raw_cfg_bytes, raw_input_bytes],
        ["trace_pkg::helper_double"],
        |rec| {
            rec.register_address_range(0x2000, 4, 7, 7);
            trace_pkg::process_packet(cfg_val, input_val)
        },
    );
    assert_eq!(res.expect("normal return"), 42);
    assert_eq!(
        trace.shadow_provenance,
        vec![RecordedShadowAlloc {
            base_addr: 0x2000,
            byte_len: 4,
            alloc_id: 7,
            tag: 7,
            raw_bytes: Vec::new(),
        }]
    );

    let named_def = render_raw_byte_trace_lean_def(
        "packetRawTrace",
        &trace,
        "emptyMemory",
        &["Mir.TracePkg.helper_double".to_string()],
    );
    assert!(named_def.contains("def packetRawTrace : RawByteTrace :="));
    assert!(named_def.contains("rawArgs := [[1, 0, 0, 0, 11, 0, 0, 0], [10, 0, 0, 0]]"));

    let cfg = TraceCheckModuleConfig {
        module_namespace: "TraceVerify.BatchContract".to_string(),
        root_mir_module: "Mir.TracePkg.process_packet".to_string(),
        callee_sig_modules: vec!["Mir.TracePkg.ext_scale_add".to_string()],
        inlined_callee_modules: vec!["Mir.TracePkg.helper_double".to_string()],
        init_mem_expr: None,
        fuel: 60,
        check_branches: false,
    };
    let batch_module = render_batch_trace_eval_lean_module(
        "TraceVerify.BatchContract",
        &[BatchTraceEvalCase {
            case_ident: "process_packet_ok".to_string(),
            config: cfg,
            trace,
            expected_diag_tag: Some("ok".to_string()),
            tampered_outcome: Some(RecordedOutcome::Normal {
                raw_ret: vec![99, 0, 0, 0],
            }),
        }],
        true,
    );
    assert!(batch_module.contains("checkRawByteTraceObsErasedBounded_sound 60"));
    assert!(batch_module.contains("diagnoseRawByteTraceObsErasedBounded 60"));
    assert!(
        batch_module.contains(
            "theorem process_packet_ok_tampered_outcome_mismatch :\n    (diagnoseRawByteTraceObsErasedBounded 60 Mir.TracePkg.process_packet.body process_packet_ok_calleeSigs process_packet_ok_shadowTable { process_packet_ok_rawTrace with outcome := .normal [99, 0, 0, 0] }).tagName = \"outcome_mismatch\" := by\n  rfl"
        )
    );
}

#[test]
fn end_to_end_rust_trace_observer_and_lean_itree_consistency_check() {
    let checkout_root = anneal_checkout_root();
    let wrapper_bin = ensure_rustc_capture_binary(&checkout_root);

    let temp_crate = unique_temp_dir("observer");
    let src_dir = temp_crate.join("src");
    fs::create_dir_all(&src_dir).expect("create temporary crate src/");

    let anneal_trace_dir = checkout_root.join("crates/anneal-trace");
    let cargo_toml = format!(
        r#"[package]
name = "trace_pkg"
version = "0.1.0"
edition = "2024"
publish = false

[dependencies]
anneal-trace = {{ path = {:?} }}
"#,
        anneal_trace_dir.display()
    );
    fs::write(temp_crate.join("Cargo.toml"), cargo_toml).expect("write Cargo.toml");
    fs::write(src_dir.join("lib.rs"), TRACE_PKG_LIB_RS).expect("write src/lib.rs");

    // 1. Run `cargo check` under `anneal-rustc-capture` and scaffold `.anneal/`.
    let units_dir = temp_crate.join("target").join("anneal").join("units");
    let mut capture_cfg = CaptureDriverConfig::new(&temp_crate);
    capture_cfg.units_dir = units_dir.clone();
    capture_cfg.rustc_wrapper = Some(wrapper_bin);
    let (_manifest, records) = run_cargo_capture(&capture_cfg).expect("capture trace_pkg MIR");
    assert!(
        !records.is_empty(),
        "expected captured unit records for trace_pkg"
    );

    let mut scaffold_cfg = ScaffoldConfig::new(&temp_crate);
    scaffold_cfg.units_dir = Some(units_dir);
    scaffold_cfg.anneal_repo_root = Some(checkout_root.clone());
    let scaffold_report =
        scaffold_workspace_with_config(&scaffold_cfg, &records).expect("scaffold .anneal");
    assert!(
        scaffold_report
            .generated_mir_files
            .iter()
            .any(|p| p.ends_with("Mir/TracePkg/process_packet.lean")),
        "expected Mir/TracePkg/process_packet.lean in generated MIR files"
    );

    // 2. Construct a `PaddedConfig` in memory and deliberately write non-zero
    //    junk bytes (`0xAA, 0xBB, 0xCC`) into its 3 padding bytes at offsets
    //    1..4 so we verify that `capture_value_bytes` marks padding as `None`
    //    without reading padding bytes and `value_as_raw_bytes` masks unknown
    //    padding bytes as `0`.
    let mut cfg_val = trace_pkg::PaddedConfig {
        mode: 1,
        threshold: 11,
    };
    unsafe {
        let base = (&mut cfg_val as *mut trace_pkg::PaddedConfig).cast::<u8>();
        *base.add(1) = 0xAA;
        *base.add(2) = 0xBB;
        *base.add(3) = 0xCC;
    }
    assert_eq!(
        capture_value_bytes(&cfg_val),
        vec![
            Some(1),
            None,
            None,
            None,
            Some(11),
            Some(0),
            Some(0),
            Some(0)
        ]
    );
    let raw_cfg_bytes = value_as_raw_bytes(&cfg_val);
    assert_eq!(
        raw_cfg_bytes,
        vec![1, 0, 0, 0, 11, 0, 0, 0],
        "expected 8-byte repr(C) struct with padding masked as 0 without reading padding"
    );

    let input_val: u32 = 10;
    let raw_input_bytes = value_as_raw_bytes(&input_val);

    // 3a. Execute unmodified `trace_pkg::process_packet(cfg_val, 10)` under
    //     `TraceRecorder::observe_root_with_inlined_callees`:
    //     - `ext_scale_add(10, 11) -> 21` is interposed via `#[anneal_trace::external]`
    //       and recorded as an `ExtCall` event.
    //     - `helper_double(21) -> 42` is listed in `inlined_callees` and stepped
    //       via `.tau` in the Lean ITree model.
    let (res_call_only, trace_call_only) = TraceRecorder::observe_root_with_inlined_callees(
        "trace_pkg::process_packet",
        vec![raw_cfg_bytes.clone(), raw_input_bytes.clone()],
        ["trace_pkg::helper_double"],
        |_rec| trace_pkg::process_packet(cfg_val, input_val),
    );
    assert_eq!(res_call_only.expect("normal return"), 42);
    assert_eq!(
        trace_call_only.events,
        vec![RecordedEvent::ExtCall {
            def_path: "trace_pkg::ext_scale_add".to_string(),
            raw_args: vec![vec![10, 0, 0, 0], vec![11, 0, 0, 0]],
            raw_ret: vec![21, 0, 0, 0],
        }]
    );
    assert_eq!(
        trace_call_only.outcome,
        RecordedOutcome::Normal {
            raw_ret: vec![42, 0, 0, 0]
        }
    );

    // 3b. Also record a full trace (`check_branches = true`) that includes the
    //     `switchInt` branch observation (`record_branch(0)` for the `false`
    //     boolean comparison `cfg.mode == 0` in `if cfg.mode == 0`).
    let mut trace_full = trace_call_only.clone();
    trace_full
        .events
        .insert(0, RecordedEvent::Branch { tag: 0 });

    // 3c. Execute unmodified `trace_pkg::inspect_ptr_identity(&watched_u32)`
    //     under `TraceRecorder` with `watched_u32` registered in the shadow
    //     provenance table at `(alloc_id = 7, tag = 7)`.
    let watched_box: Box<u32> = Box::new(123456);
    let watched_ref: &u32 = &watched_box;
    let (res_ptr, trace_ptr) = TraceRecorder::observe_root(
        "trace_pkg::inspect_ptr_identity",
        vec![value_as_raw_bytes(&watched_ref)],
        |rec| {
            rec.register_allocation(watched_ref, 7, 7);
            trace_pkg::inspect_ptr_identity(watched_ref)
        },
    );
    assert_eq!(*res_ptr.expect("normal ptr return"), 123456);
    assert_eq!(trace_ptr.shadow_provenance.len(), 1);
    assert_eq!(
        trace_ptr.shadow_provenance[0].base_addr,
        (watched_ref as *const u32) as usize
    );
    assert_eq!(trace_ptr.shadow_provenance[0].byte_len, 4);
    assert_eq!(trace_ptr.shadow_provenance[0].alloc_id, 7);
    assert_eq!(trace_ptr.shadow_provenance[0].tag, 7);
    assert_eq!(
        trace_ptr.shadow_provenance[0].raw_bytes,
        vec![64, 226, 1, 0]
    );

    // 3d. Execute I-08 positive and negative fixtures under `TraceRecorder`:
    //     - Limit 1 (padding offsets decoded as `.uninit` using layout):
    //       `process_packet` with non-zero padding bytes `[1, 0xAA, 0xBB, 0xCC, 11, 0, 0, 0]`
    //       (positive) and `transmute_padded_to_u64` (negative: faults on `.uninit` padding).
    let mut trace_nonzero_padding = trace_call_only.clone();
    trace_nonzero_padding.raw_args[0] = vec![1, 0xAA, 0xBB, 0xCC, 11, 0, 0, 0];

    let (_res_transmute_padded, trace_transmute_padded) = TraceRecorder::observe_root(
        "trace_pkg::transmute_padded_to_u64",
        vec![vec![1, 0xAA, 0xBB, 0xCC, 11, 0, 0, 0]],
        |_rec| 0u64,
    );

    //     - Limit 2 (initial memory for registered pointer allocations):
    //       `deref_shared_u32(&watched_box)`, `deref_mut_u32(&mut watched_mut_box)`,
    //       and `deref_padded_config(&cfg_val)` with `register_allocation` (positive) vs.
    //       unregistered / empty-byte `shadow_provenance` (negative: `step_faulted`).
    let (res_deref_shared, trace_deref_shared) = TraceRecorder::observe_root(
        "trace_pkg::deref_shared_u32",
        vec![value_as_raw_bytes(&watched_ref)],
        |rec| {
            rec.register_allocation(watched_ref, 7, 7);
            trace_pkg::deref_shared_u32(watched_ref)
        },
    );
    assert_eq!(res_deref_shared.expect("normal deref_shared return"), 123457);

    let mut watched_mut_box: Box<u32> = Box::new(123456);
    let watched_mut_addr_bytes = {
        let r: &u32 = &watched_mut_box;
        value_as_raw_bytes(&r)
    };
    let (res_deref_mut, trace_deref_mut) = TraceRecorder::observe_root(
        "trace_pkg::deref_mut_u32",
        vec![watched_mut_addr_bytes],
        |rec| {
            rec.register_allocation(&*watched_mut_box, 9, 9);
            trace_pkg::deref_mut_u32(&mut watched_mut_box)
        },
    );
    assert_eq!(res_deref_mut.expect("normal deref_mut return"), 123461);

    let cfg_ref: &trace_pkg::PaddedConfig = &cfg_val;
    let (res_deref_padded, mut trace_deref_padded) = TraceRecorder::observe_root(
        "trace_pkg::deref_padded_config",
        vec![value_as_raw_bytes(&cfg_ref)],
        |rec| {
            rec.register_allocation(cfg_ref, 11, 11);
            trace_pkg::deref_padded_config(cfg_ref)
        },
    );
    assert_eq!(res_deref_padded.expect("normal deref_padded return"), 12);
    // Inject non-zero padding junk into `shadow_provenance[0].raw_bytes` at offsets 1..4
    // to prove that `mem.globals` also decodes padding offsets as `none` (`.uninit`).
    trace_deref_padded.shadow_provenance[0].raw_bytes = vec![1, 0xAA, 0xBB, 0xCC, 11, 0, 0, 0];

    let (res_deref_only_thresh, mut trace_deref_only_thresh) = TraceRecorder::observe_root(
        "trace_pkg::deref_only_threshold",
        vec![value_as_raw_bytes(&cfg_ref)],
        |rec| {
            rec.register_allocation(cfg_ref, 17, 17);
            trace_pkg::deref_only_threshold(cfg_ref)
        },
    );
    assert_eq!(
        res_deref_only_thresh.expect("normal deref_only_threshold return"),
        11
    );
    trace_deref_only_thresh.shadow_provenance[0].raw_bytes =
        vec![1, 0xAA, 0xBB, 0xCC, 11, 0, 0, 0];

    let reordered_val = trace_pkg::RustReordered { a: 1, b: 300 };
    let reordered_ref: &trace_pkg::RustReordered = &reordered_val;
    let (res_deref_reordered, mut trace_deref_reordered) = TraceRecorder::observe_root(
        "trace_pkg::deref_rust_reordered",
        vec![value_as_raw_bytes(&reordered_ref)],
        |rec| {
            rec.register_allocation(reordered_ref, 19, 19);
            trace_pkg::deref_rust_reordered(reordered_ref)
        },
    );
    assert_eq!(
        res_deref_reordered.expect("normal deref_rust_reordered return"),
        301
    );
    // In `repr(Rust)` for `RustReordered { a: u8, b: u32 }`, rustc places `b` at 0..4
    // (`[44, 1, 0, 0]`), `a` at 4 (`1`), and trailing padding at 5..8 (`[0xDD, 0xEE, 0xFF]`).
    trace_deref_reordered.shadow_provenance[0].raw_bytes =
        vec![44, 1, 0, 0, 1, 0xDD, 0xEE, 0xFF];

    let arr_u32: [u32; 2] = [77, 88];
    let first_elem_ref: &u32 = &arr_u32[0];
    let (res_deref_prefix, mut trace_deref_prefix) = TraceRecorder::observe_root(
        "trace_pkg::deref_shared_u32",
        vec![value_as_raw_bytes(&first_elem_ref)],
        |_rec| trace_pkg::deref_shared_u32(first_elem_ref),
    );
    assert_eq!(res_deref_prefix.expect("normal deref_prefix return"), 78);
    trace_deref_prefix.shadow_provenance.push(RecordedShadowAlloc {
        base_addr: (first_elem_ref as *const u32) as usize,
        byte_len: 8,
        alloc_id: 21,
        tag: 21,
        raw_bytes: vec![77, 0, 0, 0, 88, 0, 0, 0],
    });

    let (_res_sum_arr, trace_sum_arr) = TraceRecorder::observe_root(
        "trace_pkg::sum_padded_array",
        vec![vec![
            1, 0xAA, 0xBB, 0xCC, 11, 0, 0, 0, 2, 0xDD, 0xEE, 0xFF, 22, 0, 0, 0,
        ]],
        |_rec| {
            trace_pkg::sum_padded_array([
                trace_pkg::PaddedConfig {
                    mode: 1,
                    threshold: 11,
                },
                trace_pkg::PaddedConfig {
                    mode: 2,
                    threshold: 22,
                },
            ])
        },
    );

    let (_res_eval_enum, trace_eval_enum) = TraceRecorder::observe_root(
        "trace_pkg::eval_padded_enum",
        vec![vec![0, 1, 0xAA, 0xBB, 11, 0, 0, 0]],
        |_rec| trace_pkg::eval_padded_enum(trace_pkg::PaddedEnum::Pair(1, 11)),
    );

    //     - Limit 3 (reject/flag external calls taking `&mut` or raw-pointer args):
    //       `call_ext_shared_ref` calling `ext_read_shared(&u32)` (positive: memory-pure
    //       `&Freeze` allowed) vs. `call_ext_mut_ref` calling `ext_bump_mut(&mut u32)`,
    //       `call_ext_raw_ptr` calling `ext_read_raw_ptr(*const u32)`, and wrapper structs
    //       `call_ext_mut_wrapper` / `call_ext_raw_wrapper` (negative: rejected by
    //       `decodeRawByteTrace` / `checkRawByteTraceObsErasedBounded` and flagged with
    //       `"impure_ext_call_ptr_arg"`).
    let (res_ext_shared, trace_ext_shared) = TraceRecorder::observe_root(
        "trace_pkg::call_ext_shared_ref",
        vec![value_as_raw_bytes(&watched_ref)],
        |rec| {
            rec.register_allocation(watched_ref, 7, 7);
            trace_pkg::call_ext_shared_ref(watched_ref)
        },
    );
    assert_eq!(res_ext_shared.expect("normal ext_shared return"), 123466);

    let (res_ext_mut, mut trace_ext_mut) = TraceRecorder::observe_root(
        "trace_pkg::call_ext_mut_ref",
        vec![value_as_raw_bytes(&41u32)],
        |_rec| trace_pkg::call_ext_mut_ref(41),
    );
    assert_eq!(res_ext_mut.expect("normal ext_mut return"), 42);
    assert_eq!(trace_ext_mut.events.len(), 1);
    if let RecordedEvent::ExtCall { ref raw_args, .. } = trace_ext_mut.events[0] {
        let arg_addr = usize::from_le_bytes(raw_args[0].as_slice().try_into().unwrap());
        trace_ext_mut.shadow_provenance.push(RecordedShadowAlloc {
            base_addr: arg_addr,
            byte_len: 4,
            alloc_id: 13,
            tag: 13,
            raw_bytes: vec![41, 0, 0, 0],
        });
    }

    let (res_ext_raw, mut trace_ext_raw) = TraceRecorder::observe_root(
        "trace_pkg::call_ext_raw_ptr",
        vec![value_as_raw_bytes(&77u32)],
        |_rec| trace_pkg::call_ext_raw_ptr(77),
    );
    assert_eq!(res_ext_raw.expect("normal ext_raw return"), 77);
    assert_eq!(trace_ext_raw.events.len(), 1);
    if let RecordedEvent::ExtCall { ref raw_args, .. } = trace_ext_raw.events[0] {
        let arg_addr = usize::from_le_bytes(raw_args[0].as_slice().try_into().unwrap());
        trace_ext_raw.shadow_provenance.push(RecordedShadowAlloc {
            base_addr: arg_addr,
            byte_len: 4,
            alloc_id: 15,
            tag: 15,
            raw_bytes: vec![77, 0, 0, 0],
        });
    }

    let (res_ext_mut_wrap, mut trace_ext_mut_wrap) = TraceRecorder::observe_root(
        "trace_pkg::call_ext_mut_wrapper",
        vec![value_as_raw_bytes(&41u32)],
        |_rec| trace_pkg::call_ext_mut_wrapper(41),
    );
    assert_eq!(res_ext_mut_wrap.expect("normal ext_mut_wrap return"), 42);
    assert_eq!(trace_ext_mut_wrap.events.len(), 1);
    if let RecordedEvent::ExtCall { ref raw_args, .. } = trace_ext_mut_wrap.events[0] {
        let arg_addr = usize::from_le_bytes(raw_args[0].as_slice().try_into().unwrap());
        trace_ext_mut_wrap
            .shadow_provenance
            .push(RecordedShadowAlloc {
                base_addr: arg_addr,
                byte_len: 4,
                alloc_id: 23,
                tag: 23,
                raw_bytes: vec![41, 0, 0, 0],
            });
    }

    let (res_ext_raw_wrap, mut trace_ext_raw_wrap) = TraceRecorder::observe_root(
        "trace_pkg::call_ext_raw_wrapper",
        vec![value_as_raw_bytes(&77u32)],
        |_rec| trace_pkg::call_ext_raw_wrapper(77),
    );
    assert_eq!(res_ext_raw_wrap.expect("normal ext_raw_wrap return"), 77);
    assert_eq!(trace_ext_raw_wrap.events.len(), 1);
    if let RecordedEvent::ExtCall { ref raw_args, .. } = trace_ext_raw_wrap.events[0] {
        let arg_addr = usize::from_le_bytes(raw_args[0].as_slice().try_into().unwrap());
        trace_ext_raw_wrap
            .shadow_provenance
            .push(RecordedShadowAlloc {
                base_addr: arg_addr,
                byte_len: 4,
                alloc_id: 25,
                tag: 25,
                raw_bytes: vec![77, 0, 0, 0],
            });
    }

    // 4. Render the Lean 4 trace-verification module and append:
    //    1) A full-trace consistency & diagnostic proof (`checkRawByteTraceFullBounded_sound`
    //       + `diagnoseRawByteTraceFullBounded ... .tagName = "ok"`) for `trace_full`,
    //    2) A tampered-outcome negative diagnostic assertion proving by `rfl` that
    //       replacing the return bytes with `[99, 0, 0, 0]` deterministically yields
    //       `(diagnoseRawByteTraceObsErasedBounded ...).tagName = "outcome_mismatch"`,
    //    3) A shadow-provenance pointer trace consistency & diagnostic proof for
    //       `inspect_ptr_identity`, and
    //    4) Positive and negative kernel-checked theorems for all 3 I-08 limits.
    let obs_erased_cfg = TraceCheckModuleConfig {
        module_namespace: "TraceVerify.ObsErased".to_string(),
        root_mir_module: "Mir.TracePkg.process_packet".to_string(),
        callee_sig_modules: vec!["Mir.TracePkg.ext_scale_add".to_string()],
        inlined_callee_modules: vec!["Mir.TracePkg.helper_double".to_string()],
        init_mem_expr: None,
        fuel: 60,
        check_branches: false,
    };
    let full_cfg = TraceCheckModuleConfig {
        check_branches: true,
        ..obs_erased_cfg.clone()
    };
    let ptr_cfg = TraceCheckModuleConfig {
        module_namespace: "TraceVerify.ObsErased".to_string(),
        root_mir_module: "Mir.TracePkg.inspect_ptr_identity".to_string(),
        callee_sig_modules: vec![],
        inlined_callee_modules: vec![],
        init_mem_expr: None,
        fuel: 20,
        check_branches: false,
    };

    let mut obs_erased_lean = render_trace_check_lean_module(&obs_erased_cfg, &trace_call_only);

    let full_trace_lean_expr = render_raw_byte_trace_lean(
        &trace_full,
        "emptyMemory",
        &["Mir.TracePkg.helper_double".to_string()],
    );
    let ptr_table_lean_expr = render_shadow_provenance_table_lean(&trace_ptr.shadow_provenance);
    let ptr_trace_lean_expr = render_raw_byte_trace_lean(&trace_ptr, "emptyMemory", &[]);

    let nonzero_pad_trace_lean_expr = render_raw_byte_trace_lean(
        &trace_nonzero_padding,
        "emptyMemory",
        &["Mir.TracePkg.helper_double".to_string()],
    );
    let transmute_pad_trace_lean_expr =
        render_raw_byte_trace_lean(&trace_transmute_padded, "emptyMemory", &[]);

    let deref_shared_table_lean_expr =
        render_shadow_provenance_table_lean(&trace_deref_shared.shadow_provenance);
    let deref_shared_trace_lean_expr =
        render_raw_byte_trace_lean(&trace_deref_shared, "emptyMemory", &[]);
    let deref_shared_no_bytes_table_lean_expr =
        render_shadow_provenance_table_lean(&[RecordedShadowAlloc {
            raw_bytes: Vec::new(),
            ..trace_deref_shared.shadow_provenance[0].clone()
        }]);

    let deref_mut_table_lean_expr =
        render_shadow_provenance_table_lean(&trace_deref_mut.shadow_provenance);
    let deref_mut_trace_lean_expr =
        render_raw_byte_trace_lean(&trace_deref_mut, "emptyMemory", &[]);

    let deref_padded_table_lean_expr =
        render_shadow_provenance_table_lean(&trace_deref_padded.shadow_provenance);
    let deref_padded_trace_lean_expr =
        render_raw_byte_trace_lean(&trace_deref_padded, "emptyMemory", &[]);

    let deref_only_thresh_table_lean_expr =
        render_shadow_provenance_table_lean(&trace_deref_only_thresh.shadow_provenance);
    let deref_only_thresh_trace_lean_expr =
        render_raw_byte_trace_lean(&trace_deref_only_thresh, "emptyMemory", &[]);

    let deref_reordered_table_lean_expr =
        render_shadow_provenance_table_lean(&trace_deref_reordered.shadow_provenance);
    let deref_reordered_trace_lean_expr =
        render_raw_byte_trace_lean(&trace_deref_reordered, "emptyMemory", &[]);

    let deref_prefix_table_lean_expr =
        render_shadow_provenance_table_lean(&trace_deref_prefix.shadow_provenance);
    let deref_prefix_trace_lean_expr =
        render_raw_byte_trace_lean(&trace_deref_prefix, "emptyMemory", &[]);

    let sum_arr_trace_lean_expr = render_raw_byte_trace_lean(&trace_sum_arr, "emptyMemory", &[]);
    let eval_enum_trace_lean_expr =
        render_raw_byte_trace_lean(&trace_eval_enum, "emptyMemory", &[]);

    let ext_shared_table_lean_expr =
        render_shadow_provenance_table_lean(&trace_ext_shared.shadow_provenance);
    let ext_shared_trace_lean_expr =
        render_raw_byte_trace_lean(&trace_ext_shared, "emptyMemory", &[]);

    let ext_mut_table_lean_expr =
        render_shadow_provenance_table_lean(&trace_ext_mut.shadow_provenance);
    let ext_mut_trace_lean_expr =
        render_raw_byte_trace_lean(&trace_ext_mut, "emptyMemory", &[]);

    let ext_raw_table_lean_expr =
        render_shadow_provenance_table_lean(&trace_ext_raw.shadow_provenance);
    let ext_raw_trace_lean_expr =
        render_raw_byte_trace_lean(&trace_ext_raw, "emptyMemory", &[]);

    let ext_mut_wrap_table_lean_expr =
        render_shadow_provenance_table_lean(&trace_ext_mut_wrap.shadow_provenance);
    let ext_mut_wrap_trace_lean_expr =
        render_raw_byte_trace_lean(&trace_ext_mut_wrap, "emptyMemory", &[]);

    let ext_raw_wrap_table_lean_expr =
        render_shadow_provenance_table_lean(&trace_ext_raw_wrap.shadow_provenance);
    let ext_raw_wrap_trace_lean_expr =
        render_raw_byte_trace_lean(&trace_ext_raw_wrap, "emptyMemory", &[]);

    let full_diag_ok_snippet = render_trace_diag_eval_lean_snippet(
        "full_trace_diag_ok",
        &full_cfg,
        "calleeSigs",
        "shadowTable",
        "observedFullRawTrace",
        "ok",
        false,
    );
    let tampered_outcome_snippet = render_tampered_outcome_diag_lean_snippet(
        "tampered_outcome_diag_mismatch",
        &obs_erased_cfg,
        "calleeSigs",
        "shadowTable",
        "observedRawTrace",
        &RecordedOutcome::Normal {
            raw_ret: vec![99, 0, 0, 0],
        },
    );
    let ptr_diag_ok_snippet = render_trace_diag_eval_lean_snippet(
        "shadow_provenance_ptr_diag_ok",
        &ptr_cfg,
        "[]",
        "ptrShadowTable",
        "ptrObservedRawTrace",
        "ok",
        false,
    );

    obs_erased_lean = obs_erased_lean.replace(
        "import Mir.TracePkg.process_packet\n",
        concat!(
            "import Mir.TracePkg.process_packet\n",
            "import Mir.TracePkg.inspect_ptr_identity\n",
            "import Mir.TracePkg.transmute_padded_to_u64\n",
            "import Mir.TracePkg.deref_shared_u32\n",
            "import Mir.TracePkg.deref_mut_u32\n",
            "import Mir.TracePkg.deref_padded_config\n",
            "import Mir.TracePkg.deref_only_threshold\n",
            "import Mir.TracePkg.deref_rust_reordered\n",
            "import Mir.TracePkg.sum_padded_array\n",
            "import Mir.TracePkg.eval_padded_enum\n",
            "import Mir.TracePkg.ext_read_shared\n",
            "import Mir.TracePkg.call_ext_shared_ref\n",
            "import Mir.TracePkg.ext_bump_mut\n",
            "import Mir.TracePkg.call_ext_mut_ref\n",
            "import Mir.TracePkg.ext_read_raw_ptr\n",
            "import Mir.TracePkg.call_ext_raw_ptr\n",
            "import Mir.TracePkg.ext_bump_mut_wrapper\n",
            "import Mir.TracePkg.call_ext_mut_wrapper\n",
            "import Mir.TracePkg.ext_read_raw_wrapper\n",
            "import Mir.TracePkg.call_ext_raw_wrapper\n",
        ),
    );
    let extra_theorems = format!(
        r#"
@[reducible]
def observedFullRawTrace : RawByteTrace :=
{full_trace_lean_expr}

set_option maxHeartbeats 400000 in
theorem full_trace_consistent :
    ∃ obsTrace tr out,
      decodeRawByteTrace Mir.TracePkg.process_packet.body calleeSigs shadowTable observedFullRawTrace = some obsTrace ∧
      MatchesObservedEvents obsTrace.events tr ∧
      MatchesObservedOutcome obsTrace.outcome out ∧
      ReachesRet
        (mirStatefulTree Mir.TracePkg.process_packet.body obsTrace.args
          {{ obsTrace.initMem with callees := obsTrace.inlinedCallees }})
        tr out :=
  checkRawByteTraceFullBounded_sound 60 Mir.TracePkg.process_packet.body calleeSigs shadowTable observedFullRawTrace rfl

{full_diag_ok_snippet}
set_option maxHeartbeats 400000 in
theorem corrupted_trace_rejected :
    checkRawByteTraceObsErasedBounded 60 Mir.TracePkg.process_packet.body calleeSigs shadowTable
      {{ observedRawTrace with outcome := .normal [99, 0, 0, 0] }} = false :=
  rfl

{tampered_outcome_snippet}
@[reducible]
def ptrShadowTable : ShadowProvenanceTable := {ptr_table_lean_expr}

@[reducible]
def ptrObservedRawTrace : RawByteTrace :=
{ptr_trace_lean_expr}

set_option maxHeartbeats 400000 in
theorem shadow_provenance_ptr_trace_consistent :
    ∃ obsTrace tr out,
      decodeRawByteTrace Mir.TracePkg.inspect_ptr_identity.body [] ptrShadowTable ptrObservedRawTrace = some obsTrace ∧
      MatchesObservedEvents obsTrace.events tr ∧
      MatchesObservedOutcome obsTrace.outcome out ∧
      ReachesRet
        (mirObsErasedStatefulTree Mir.TracePkg.inspect_ptr_identity.body obsTrace.args
          {{ obsTrace.initMem with callees := obsTrace.inlinedCallees }})
        tr out :=
  checkRawByteTraceObsErasedBounded_sound 20 Mir.TracePkg.inspect_ptr_identity.body [] ptrShadowTable ptrObservedRawTrace rfl

{ptr_diag_ok_snippet}
/-! ### Issue I-08 Limit 1: Decode padding offsets as `.uninit` using layout -/

@[reducible]
def nonzeroPadRawTrace : RawByteTrace :=
{nonzero_pad_trace_lean_expr}

@[reducible]
def transmutePadRawTrace : RawByteTrace :=
{transmute_pad_trace_lean_expr}

@[reducible]
def sumPaddedArrRawTrace : RawByteTrace :=
{sum_arr_trace_lean_expr}

@[reducible]
def evalPaddedEnumRawTrace : RawByteTrace :=
{eval_enum_trace_lean_expr}

set_option maxHeartbeats 400000 in
theorem limit1_padded_config_padding_bytes_decoded_as_uninit :
    match Mir.TracePkg.process_packet.body.localDecls with
    | _ :: cfgDecl :: _ =>
      rawBytesWithProvenance
        []
        cfgDecl.ty
        [1, 0xAA, 0xBB, 0xCC, 11, 0, 0, 0]
        Mir.TracePkg.process_packet.body.layouts =
      [ .init 1 none,
        .uninit,
        .uninit,
        .uninit,
        .init 11 none,
        .init 0 none,
        .init 0 none,
        .init 0 none ]
    | _ => False := by
  rfl

set_option maxHeartbeats 400000 in
theorem limit1_array_padded_config_padding_bytes_decoded_as_uninit :
    match Mir.TracePkg.sum_padded_array.body.localDecls with
    | _ :: arrDecl :: _ =>
      rawBytesWithProvenance
        []
        arrDecl.ty
        [1, 0xAA, 0xBB, 0xCC, 11, 0, 0, 0, 2, 0xDD, 0xEE, 0xFF, 22, 0, 0, 0]
        Mir.TracePkg.sum_padded_array.body.layouts =
      [ .init 1 none,
        .uninit,
        .uninit,
        .uninit,
        .init 11 none,
        .init 0 none,
        .init 0 none,
        .init 0 none,
        .init 2 none,
        .uninit,
        .uninit,
        .uninit,
        .init 22 none,
        .init 0 none,
        .init 0 none,
        .init 0 none ]
    | _ => False := by
  rfl

set_option maxHeartbeats 400000 in
theorem limit1_padded_enum_padding_bytes_decoded_as_uninit :
    match Mir.TracePkg.eval_padded_enum.body.localDecls with
    | _ :: enumDecl :: _ =>
      rawBytesWithProvenance
        []
        enumDecl.ty
        [0, 1, 0xAA, 0xBB, 11, 0, 0, 0]
        Mir.TracePkg.eval_padded_enum.body.layouts =
      [ .init 0 none,
        .init 1 none,
        .uninit,
        .uninit,
        .init 11 none,
        .init 0 none,
        .init 0 none,
        .init 0 none ]
    | _ => False := by
  rfl

set_option maxHeartbeats 400000 in
theorem limit1_positive_nonzero_padding_trace_consistent :
    ∃ obsTrace tr out,
      decodeRawByteTrace Mir.TracePkg.process_packet.body calleeSigs shadowTable nonzeroPadRawTrace = some obsTrace ∧
      MatchesObservedEvents obsTrace.events tr ∧
      MatchesObservedOutcome obsTrace.outcome out ∧
      ReachesRet
        (mirObsErasedStatefulTree Mir.TracePkg.process_packet.body obsTrace.args
          {{ obsTrace.initMem with callees := obsTrace.inlinedCallees }})
        tr out :=
  checkRawByteTraceObsErasedBounded_sound 60 Mir.TracePkg.process_packet.body calleeSigs shadowTable nonzeroPadRawTrace rfl

set_option maxHeartbeats 400000 in
theorem limit1_positive_sum_padded_array_consistent :
    ∃ obsTrace tr out,
      decodeRawByteTrace Mir.TracePkg.sum_padded_array.body [] [] sumPaddedArrRawTrace = some obsTrace ∧
      MatchesObservedEvents obsTrace.events tr ∧
      MatchesObservedOutcome obsTrace.outcome out ∧
      ReachesRet
        (mirObsErasedStatefulTree Mir.TracePkg.sum_padded_array.body obsTrace.args
          {{ obsTrace.initMem with callees := obsTrace.inlinedCallees }})
        tr out :=
  checkRawByteTraceObsErasedBounded_sound 60 Mir.TracePkg.sum_padded_array.body [] [] sumPaddedArrRawTrace rfl

set_option maxHeartbeats 400000 in
theorem limit1_positive_eval_padded_enum_consistent :
    ∃ obsTrace tr out,
      decodeRawByteTrace Mir.TracePkg.eval_padded_enum.body [] [] evalPaddedEnumRawTrace = some obsTrace ∧
      MatchesObservedEvents obsTrace.events tr ∧
      MatchesObservedOutcome obsTrace.outcome out ∧
      ReachesRet
        (mirObsErasedStatefulTree Mir.TracePkg.eval_padded_enum.body obsTrace.args
          {{ obsTrace.initMem with callees := obsTrace.inlinedCallees }})
        tr out :=
  checkRawByteTraceObsErasedBounded_sound 60 Mir.TracePkg.eval_padded_enum.body [] [] evalPaddedEnumRawTrace rfl

set_option maxHeartbeats 400000 in
theorem limit1_negative_uninit_padding_rejected_as_u64_scalar :
    match Mir.TracePkg.transmute_padded_to_u64.body.localDecls with
    | u64Decl :: cfgDecl :: _ =>
      decodeValueFromBytes
        defaultCodecFuel
        Mir.TracePkg.transmute_padded_to_u64.body.layouts
        u64Decl.ty
        (rawBytesWithProvenance
          []
          cfgDecl.ty
          [1, 0xAA, 0xBB, 0xCC, 11, 0, 0, 0]
          Mir.TracePkg.transmute_padded_to_u64.body.layouts) = none
    | _ => False := by
  rfl

set_option maxHeartbeats 400000 in
theorem limit1_negative_transmute_padded_to_u64_faults :
    checkRawByteTraceObsErasedBounded 20 Mir.TracePkg.transmute_padded_to_u64.body [] [] transmutePadRawTrace = false ∧
    (diagnoseRawByteTraceObsErasedBounded 20 Mir.TracePkg.transmute_padded_to_u64.body [] [] transmutePadRawTrace).tagName = "step_faulted" := by
  exact ⟨rfl, rfl⟩

/-! ### Issue I-08 Limit 2: Initial memory for registered pointer allocations -/

@[reducible]
def derefSharedShadowTable : ShadowProvenanceTable := {deref_shared_table_lean_expr}

@[reducible]
def derefSharedNoBytesShadowTable : ShadowProvenanceTable := {deref_shared_no_bytes_table_lean_expr}

@[reducible]
def derefSharedRawTrace : RawByteTrace :=
{deref_shared_trace_lean_expr}

@[reducible]
def derefMutShadowTable : ShadowProvenanceTable := {deref_mut_table_lean_expr}

@[reducible]
def derefMutRawTrace : RawByteTrace :=
{deref_mut_trace_lean_expr}

@[reducible]
def derefPaddedShadowTable : ShadowProvenanceTable := {deref_padded_table_lean_expr}

@[reducible]
def derefPaddedRawTrace : RawByteTrace :=
{deref_padded_trace_lean_expr}

@[reducible]
def derefOnlyThreshShadowTable : ShadowProvenanceTable := {deref_only_thresh_table_lean_expr}

@[reducible]
def derefOnlyThreshRawTrace : RawByteTrace :=
{deref_only_thresh_trace_lean_expr}

@[reducible]
def derefReorderedShadowTable : ShadowProvenanceTable := {deref_reordered_table_lean_expr}

@[reducible]
def derefReorderedRawTrace : RawByteTrace :=
{deref_reordered_trace_lean_expr}

@[reducible]
def derefPrefixShadowTable : ShadowProvenanceTable := {deref_prefix_table_lean_expr}

@[reducible]
def derefPrefixRawTrace : RawByteTrace :=
{deref_prefix_trace_lean_expr}

set_option maxHeartbeats 400000 in
theorem limit2_positive_deref_shared_u32_consistent :
    ∃ obsTrace tr out,
      decodeRawByteTrace Mir.TracePkg.deref_shared_u32.body [] derefSharedShadowTable derefSharedRawTrace = some obsTrace ∧
      MatchesObservedEvents obsTrace.events tr ∧
      MatchesObservedOutcome obsTrace.outcome out ∧
      ReachesRet
        (mirObsErasedStatefulTree Mir.TracePkg.deref_shared_u32.body obsTrace.args
          {{ obsTrace.initMem with callees := obsTrace.inlinedCallees }})
        tr out :=
  checkRawByteTraceObsErasedBounded_sound 20 Mir.TracePkg.deref_shared_u32.body [] derefSharedShadowTable derefSharedRawTrace rfl

set_option maxHeartbeats 400000 in
theorem limit2_positive_deref_shared_u32_diag_ok :
    (diagnoseRawByteTraceObsErasedBounded 20 Mir.TracePkg.deref_shared_u32.body [] derefSharedShadowTable derefSharedRawTrace).tagName = "ok" := by
  rfl

set_option maxHeartbeats 400000 in
theorem limit2_positive_deref_mut_u32_consistent :
    ∃ obsTrace tr out,
      decodeRawByteTrace Mir.TracePkg.deref_mut_u32.body [] derefMutShadowTable derefMutRawTrace = some obsTrace ∧
      MatchesObservedEvents obsTrace.events tr ∧
      MatchesObservedOutcome obsTrace.outcome out ∧
      ReachesRet
        (mirObsErasedStatefulTree Mir.TracePkg.deref_mut_u32.body obsTrace.args
          {{ obsTrace.initMem with callees := obsTrace.inlinedCallees }})
        tr out :=
  checkRawByteTraceObsErasedBounded_sound 20 Mir.TracePkg.deref_mut_u32.body [] derefMutShadowTable derefMutRawTrace rfl

set_option maxHeartbeats 400000 in
theorem limit2_positive_deref_padded_config_consistent :
    ∃ obsTrace tr out,
      decodeRawByteTrace Mir.TracePkg.deref_padded_config.body [] derefPaddedShadowTable derefPaddedRawTrace = some obsTrace ∧
      MatchesObservedEvents obsTrace.events tr ∧
      MatchesObservedOutcome obsTrace.outcome out ∧
      ReachesRet
        (mirObsErasedStatefulTree Mir.TracePkg.deref_padded_config.body obsTrace.args
          {{ obsTrace.initMem with callees := obsTrace.inlinedCallees }})
        tr out :=
  checkRawByteTraceObsErasedBounded_sound 20 Mir.TracePkg.deref_padded_config.body [] derefPaddedShadowTable derefPaddedRawTrace rfl

set_option maxHeartbeats 400000 in
theorem limit1_and_2_deref_padded_config_globals_padding_is_none :
    match decodeRawByteTrace Mir.TracePkg.deref_padded_config.body [] derefPaddedShadowTable derefPaddedRawTrace with
    | some obsTrace =>
      (obsTrace.initMem.globals.map (fun g => g.bytes)) =
        [[some 1, none, none, none, some 11, some 0, some 0, some 0]]
    | none => False := by
  rfl

set_option maxHeartbeats 400000 in
theorem limit2_positive_deref_only_threshold_consistent :
    ∃ obsTrace tr out,
      decodeRawByteTrace Mir.TracePkg.deref_only_threshold.body [] derefOnlyThreshShadowTable derefOnlyThreshRawTrace = some obsTrace ∧
      MatchesObservedEvents obsTrace.events tr ∧
      MatchesObservedOutcome obsTrace.outcome out ∧
      ReachesRet
        (mirObsErasedStatefulTree Mir.TracePkg.deref_only_threshold.body obsTrace.args
          {{ obsTrace.initMem with callees := obsTrace.inlinedCallees }})
        tr out :=
  checkRawByteTraceObsErasedBounded_sound 20 Mir.TracePkg.deref_only_threshold.body [] derefOnlyThreshShadowTable derefOnlyThreshRawTrace rfl

set_option maxHeartbeats 400000 in
theorem limit2_positive_deref_rust_reordered_consistent :
    ∃ obsTrace tr out,
      decodeRawByteTrace Mir.TracePkg.deref_rust_reordered.body [] derefReorderedShadowTable derefReorderedRawTrace = some obsTrace ∧
      MatchesObservedEvents obsTrace.events tr ∧
      MatchesObservedOutcome obsTrace.outcome out ∧
      ReachesRet
        (mirObsErasedStatefulTree Mir.TracePkg.deref_rust_reordered.body obsTrace.args
          {{ obsTrace.initMem with callees := obsTrace.inlinedCallees }})
        tr out :=
  checkRawByteTraceObsErasedBounded_sound 40 Mir.TracePkg.deref_rust_reordered.body [] derefReorderedShadowTable derefReorderedRawTrace rfl

set_option maxHeartbeats 400000 in
theorem limit1_and_2_deref_rust_reordered_globals_padding_is_none :
    match decodeRawByteTrace Mir.TracePkg.deref_rust_reordered.body [] derefReorderedShadowTable derefReorderedRawTrace with
    | some obsTrace =>
      (obsTrace.initMem.globals.map (fun g => g.bytes)) =
        [[some 44, some 1, some 0, some 0, some 1, none, none, none]]
    | none => False := by
  rfl

set_option maxHeartbeats 400000 in
theorem limit2_positive_deref_shared_u32_prefix_of_larger_alloc_consistent :
    ∃ obsTrace tr out,
      decodeRawByteTrace Mir.TracePkg.deref_shared_u32.body [] derefPrefixShadowTable derefPrefixRawTrace = some obsTrace ∧
      MatchesObservedEvents obsTrace.events tr ∧
      MatchesObservedOutcome obsTrace.outcome out ∧
      ReachesRet
        (mirObsErasedStatefulTree Mir.TracePkg.deref_shared_u32.body obsTrace.args
          {{ obsTrace.initMem with callees := obsTrace.inlinedCallees }})
        tr out :=
  checkRawByteTraceObsErasedBounded_sound 20 Mir.TracePkg.deref_shared_u32.body [] derefPrefixShadowTable derefPrefixRawTrace rfl

set_option maxHeartbeats 400000 in
theorem limit2_negative_unregistered_ptr_deref_faults :
    checkRawByteTraceObsErasedBounded 20 Mir.TracePkg.deref_shared_u32.body [] [] derefSharedRawTrace = false ∧
    (diagnoseRawByteTraceObsErasedBounded 20 Mir.TracePkg.deref_shared_u32.body [] [] derefSharedRawTrace).tagName = "step_faulted" ∧
    checkRawByteTraceObsErasedBounded 20 Mir.TracePkg.deref_shared_u32.body [] derefSharedNoBytesShadowTable derefSharedRawTrace = false ∧
    (diagnoseRawByteTraceObsErasedBounded 20 Mir.TracePkg.deref_shared_u32.body [] derefSharedNoBytesShadowTable derefSharedRawTrace).tagName = "step_faulted" ∧
    checkRawByteTraceObsErasedBounded 20 Mir.TracePkg.deref_mut_u32.body [] [] derefMutRawTrace = false ∧
    (diagnoseRawByteTraceObsErasedBounded 20 Mir.TracePkg.deref_mut_u32.body [] [] derefMutRawTrace).tagName = "step_faulted" := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ### Issue I-08 Limit 3: Reject/flag external calls taking `&mut` or raw-pointer args -/

@[reducible]
def extSharedShadowTable : ShadowProvenanceTable := {ext_shared_table_lean_expr}

@[reducible]
def extSharedRawTrace : RawByteTrace :=
{ext_shared_trace_lean_expr}

@[reducible]
def extMutShadowTable : ShadowProvenanceTable := {ext_mut_table_lean_expr}

@[reducible]
def extMutRawTrace : RawByteTrace :=
{ext_mut_trace_lean_expr}

@[reducible]
def extRawShadowTable : ShadowProvenanceTable := {ext_raw_table_lean_expr}

@[reducible]
def extRawRawTrace : RawByteTrace :=
{ext_raw_trace_lean_expr}

@[reducible]
def extMutWrapShadowTable : ShadowProvenanceTable := {ext_mut_wrap_table_lean_expr}

@[reducible]
def extMutWrapRawTrace : RawByteTrace :=
{ext_mut_wrap_trace_lean_expr}

@[reducible]
def extRawWrapShadowTable : ShadowProvenanceTable := {ext_raw_wrap_table_lean_expr}

@[reducible]
def extRawWrapRawTrace : RawByteTrace :=
{ext_raw_wrap_trace_lean_expr}

set_option maxHeartbeats 400000 in
theorem limit3_positive_ext_call_shared_freeze_ref_consistent :
    ∃ obsTrace tr out,
      decodeRawByteTrace Mir.TracePkg.call_ext_shared_ref.body [Mir.TracePkg.ext_read_shared.body] extSharedShadowTable extSharedRawTrace = some obsTrace ∧
      MatchesObservedEvents obsTrace.events tr ∧
      MatchesObservedOutcome obsTrace.outcome out ∧
      ReachesRet
        (mirObsErasedStatefulTree Mir.TracePkg.call_ext_shared_ref.body obsTrace.args
          {{ obsTrace.initMem with callees := obsTrace.inlinedCallees }})
        tr out :=
  checkRawByteTraceObsErasedBounded_sound 30 Mir.TracePkg.call_ext_shared_ref.body [Mir.TracePkg.ext_read_shared.body] extSharedShadowTable extSharedRawTrace rfl

set_option maxHeartbeats 400000 in
theorem limit3_negative_ext_call_mut_ref_rejected_and_flagged :
    decodeRawByteTrace Mir.TracePkg.call_ext_mut_ref.body [Mir.TracePkg.ext_bump_mut.body] extMutShadowTable extMutRawTrace = none ∧
    checkRawByteTraceObsErasedBounded 30 Mir.TracePkg.call_ext_mut_ref.body [Mir.TracePkg.ext_bump_mut.body] extMutShadowTable extMutRawTrace = false ∧
    diagnoseRawByteTraceObsErasedBounded 30 Mir.TracePkg.call_ext_mut_ref.body [Mir.TracePkg.ext_bump_mut.body] extMutShadowTable extMutRawTrace =
      .impureExtCallPtrArg "trace_pkg::ext_bump_mut" 0 0 ∧
    (diagnoseRawByteTraceObsErasedBounded 30 Mir.TracePkg.call_ext_mut_ref.body [Mir.TracePkg.ext_bump_mut.body] extMutShadowTable extMutRawTrace).tagName =
      "impure_ext_call_ptr_arg" := by
  exact ⟨rfl, rfl, rfl, rfl⟩

set_option maxHeartbeats 400000 in
theorem limit3_negative_ext_call_raw_ptr_rejected_and_flagged :
    decodeRawByteTrace Mir.TracePkg.call_ext_raw_ptr.body [Mir.TracePkg.ext_read_raw_ptr.body] extRawShadowTable extRawRawTrace = none ∧
    checkRawByteTraceObsErasedBounded 30 Mir.TracePkg.call_ext_raw_ptr.body [Mir.TracePkg.ext_read_raw_ptr.body] extRawShadowTable extRawRawTrace = false ∧
    diagnoseRawByteTraceObsErasedBounded 30 Mir.TracePkg.call_ext_raw_ptr.body [Mir.TracePkg.ext_read_raw_ptr.body] extRawShadowTable extRawRawTrace =
      .impureExtCallPtrArg "trace_pkg::ext_read_raw_ptr" 0 0 ∧
    (diagnoseRawByteTraceObsErasedBounded 30 Mir.TracePkg.call_ext_raw_ptr.body [Mir.TracePkg.ext_read_raw_ptr.body] extRawShadowTable extRawRawTrace).tagName =
      "impure_ext_call_ptr_arg" := by
  exact ⟨rfl, rfl, rfl, rfl⟩

set_option maxHeartbeats 400000 in
theorem limit3_negative_ext_call_mut_wrapper_rejected_and_flagged :
    decodeRawByteTrace Mir.TracePkg.call_ext_mut_wrapper.body [Mir.TracePkg.ext_bump_mut_wrapper.body] extMutWrapShadowTable extMutWrapRawTrace = none ∧
    checkRawByteTraceObsErasedBounded 30 Mir.TracePkg.call_ext_mut_wrapper.body [Mir.TracePkg.ext_bump_mut_wrapper.body] extMutWrapShadowTable extMutWrapRawTrace = false ∧
    diagnoseRawByteTraceObsErasedBounded 30 Mir.TracePkg.call_ext_mut_wrapper.body [Mir.TracePkg.ext_bump_mut_wrapper.body] extMutWrapShadowTable extMutWrapRawTrace =
      .impureExtCallPtrArg "trace_pkg::ext_bump_mut_wrapper" 0 0 ∧
    (diagnoseRawByteTraceObsErasedBounded 30 Mir.TracePkg.call_ext_mut_wrapper.body [Mir.TracePkg.ext_bump_mut_wrapper.body] extMutWrapShadowTable extMutWrapRawTrace).tagName =
      "impure_ext_call_ptr_arg" := by
  exact ⟨rfl, rfl, rfl, rfl⟩

set_option maxHeartbeats 400000 in
theorem limit3_negative_ext_call_raw_wrapper_rejected_and_flagged :
    decodeRawByteTrace Mir.TracePkg.call_ext_raw_wrapper.body [Mir.TracePkg.ext_read_raw_wrapper.body] extRawWrapShadowTable extRawWrapRawTrace = none ∧
    checkRawByteTraceObsErasedBounded 30 Mir.TracePkg.call_ext_raw_wrapper.body [Mir.TracePkg.ext_read_raw_wrapper.body] extRawWrapShadowTable extRawWrapRawTrace = false ∧
    diagnoseRawByteTraceObsErasedBounded 30 Mir.TracePkg.call_ext_raw_wrapper.body [Mir.TracePkg.ext_read_raw_wrapper.body] extRawWrapShadowTable extRawWrapRawTrace =
      .impureExtCallPtrArg "trace_pkg::ext_read_raw_wrapper" 0 0 ∧
    (diagnoseRawByteTraceObsErasedBounded 30 Mir.TracePkg.call_ext_raw_wrapper.body [Mir.TracePkg.ext_read_raw_wrapper.body] extRawWrapShadowTable extRawWrapRawTrace).tagName =
      "impure_ext_call_ptr_arg" := by
  exact ⟨rfl, rfl, rfl, rfl⟩

set_option maxHeartbeats 400000 in
theorem limit3_negative_direct_observed_trace_mut_ref_rejected :
    let bypassTrace : ObservedTrace := {{
      args := [.scalar ⟨41, 4⟩]
      initMem := emptyMemory
      inlinedCallees := []
      events := [.extCall "trace_pkg::ext_bump_mut" [.ptr ⟨1, 0⟩ 8] (.scalar ⟨42, 4⟩)]
      outcome := .normal (.scalar ⟨42, 4⟩)
    }}
    checkObservedTraceConsistencyBounded 30 false Mir.TracePkg.call_ext_mut_ref.body bypassTrace = false ∧
    (diagnoseObservedTraceBounded 30 false Mir.TracePkg.call_ext_mut_ref.body bypassTrace).tagName =
      "impure_ext_call_ptr_arg" := by
  exact ⟨rfl, rfl⟩

end TraceVerify.ObsErased
"#
    );
    obs_erased_lean = obs_erased_lean.replacen("\nend TraceVerify.ObsErased\n", &extra_theorems, 1);

    let trace_verify_path = temp_crate
        .join(".anneal")
        .join("generated")
        .join("Verify")
        .join("TracePkg")
        .join("TraceObserverCheck.lean");
    fs::write(&trace_verify_path, &obs_erased_lean).expect("write TraceObserverCheck.lean");

    // 5. Run `lake env lean` inside `.anneal/` to verify all theorems in the
    //    Lean 4 kernel.
    let anneal_dir = temp_crate.join(".anneal");
    let lake_targets: Vec<String> = [
        "Anneal",
        "Mir.TracePkg.process_packet",
        "Mir.TracePkg.ext_scale_add",
        "Mir.TracePkg.helper_double",
        "Mir.TracePkg.inspect_ptr_identity",
        "Mir.TracePkg.transmute_padded_to_u64",
        "Mir.TracePkg.deref_shared_u32",
        "Mir.TracePkg.deref_mut_u32",
        "Mir.TracePkg.deref_padded_config",
        "Mir.TracePkg.deref_only_threshold",
        "Mir.TracePkg.deref_rust_reordered",
        "Mir.TracePkg.sum_padded_array",
        "Mir.TracePkg.eval_padded_enum",
        "Mir.TracePkg.ext_read_shared",
        "Mir.TracePkg.call_ext_shared_ref",
        "Mir.TracePkg.ext_bump_mut",
        "Mir.TracePkg.call_ext_mut_ref",
        "Mir.TracePkg.ext_read_raw_ptr",
        "Mir.TracePkg.call_ext_raw_ptr",
        "Mir.TracePkg.ext_bump_mut_wrapper",
        "Mir.TracePkg.call_ext_mut_wrapper",
        "Mir.TracePkg.ext_read_raw_wrapper",
        "Mir.TracePkg.call_ext_raw_wrapper",
    ]
    .iter()
    .map(|s| (*s).to_string())
    .collect();
    run_lake_verify_targets(&anneal_dir, &lake_targets)
        .expect("lake build of Mir.TracePkg modules must succeed");

    let lean_output = Command::new("lake")
        .current_dir(&anneal_dir)
        .arg("env")
        .arg("lean")
        .arg(&trace_verify_path)
        .output()
        .expect("run lake env lean on TraceObserverCheck.lean");
    assert!(
        lean_output.status.success(),
        "Lean 4 kernel verification of TraceObserverCheck.lean failed:\nstdout:\n{}\nstderr:\n{}\nmodule:\n{}",
        String::from_utf8_lossy(&lean_output.stdout),
        String::from_utf8_lossy(&lean_output.stderr),
        obs_erased_lean
    );

    let _ = fs::remove_dir_all(&temp_crate);
}
