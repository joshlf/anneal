//! End-to-end integration test for the Rust artifact trace observer and
//! Lean 4 `TraceCheck` consistency verifier.
//!
//! Exercises the complete pipeline:
//! 1. Compiles and captures a real Rust crate (`trace_pkg`) through
//!    `anneal-rustc-capture` (`run_cargo_capture` +
//!    `scaffold_workspace_with_config`), extracting `Mir.TracePkg.*` modules
//!    with compiler-computed `LayoutTable`s and `LocalDecl`s.
//! 2. Executes the Rust functions under `TraceRecorder::observe_root`,
//!    capturing raw `&[u8]` byte slices via `value_as_raw_bytes` at root
//!    entry/exit and external call boundaries (`ext_scale_add`), including a
//!    `#[repr(C)]` struct `PaddedConfig` with deliberately corrupted uninitialized
//!    padding bytes and a watched allocation registered in the shadow provenance
//!    table (`register_allocation`).
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
    ScaffoldConfig, TraceCheckModuleConfig, TraceRecorder, render_batch_trace_eval_lean_module,
    render_raw_byte_trace_lean, render_raw_byte_trace_lean_def,
    render_shadow_provenance_table_lean, render_tampered_outcome_diag_lean_snippet,
    render_trace_check_lean_module, render_trace_diag_eval_lean_snippet, run_cargo_capture,
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

/// Mirror of `trace_pkg::PaddedConfig` in the test harness so we can execute the
/// exact same Rust code under `TraceRecorder` and capture its live runtime byte
/// slices (including non-zero garbage in the 3 padding bytes at offsets `1..4`).
#[repr(C)]
#[derive(Clone, Copy, Debug)]
struct PaddedConfig {
    mode: u8,
    threshold: u32,
}

fn ext_scale_add(x: u32, bonus: u32) -> u32 {
    x + bonus
}

fn helper_double(x: u32) -> u32 {
    x + x
}

#[test]
fn batch_trace_module_rendering_and_tampered_diag_contract() {
    let mut cfg_val = PaddedConfig {
        mode: 1,
        threshold: 11,
    };
    unsafe {
        let base = (&mut cfg_val as *mut PaddedConfig).cast::<u8>();
        *base.add(1) = 0xAA;
        *base.add(2) = 0xBB;
        *base.add(3) = 0xCC;
    }
    let raw_cfg_bytes = value_as_raw_bytes(&cfg_val);
    let input_val: u32 = 10;
    let raw_input_bytes = value_as_raw_bytes(&input_val);

    let (res, trace) = TraceRecorder::observe_root(
        "trace_pkg::process_packet",
        vec![raw_cfg_bytes, raw_input_bytes],
        |rec| {
            rec.register_address_range(0x2000, 4, 7, 7);
            let scaled = rec.observe_ext_call(
                "trace_pkg::ext_scale_add",
                vec![
                    value_as_raw_bytes(&input_val),
                    value_as_raw_bytes(&cfg_val.threshold),
                ],
                || ext_scale_add(input_val, cfg_val.threshold),
            );
            helper_double(scaled)
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
        }]
    );

    let named_def = render_raw_byte_trace_lean_def(
        "packetRawTrace",
        &trace,
        "emptyMemory",
        &["Mir.TracePkg.helper_double".to_string()],
    );
    assert!(named_def.contains("def packetRawTrace : RawByteTrace :="));
    assert!(named_def.contains("rawArgs := [[1, 170, 187, 204, 11, 0, 0, 0], [10, 0, 0, 0]]"));

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

    let cargo_toml = r#"[package]
name = "trace_pkg"
version = "0.1.0"
edition = "2024"
publish = false
"#;
    fs::write(temp_crate.join("Cargo.toml"), cargo_toml).expect("write Cargo.toml");

    // `trace_pkg` defines:
    // - `PaddedConfig`: a `#[repr(C)]` struct with 1-byte `mode`, 3 bytes of
    //   inter-field padding, and 4-byte `threshold` (total 8 bytes).
    // - `ext_scale_add`: an external/callee function that will be observed at
    //   its `MirCallE` boundary.
    // - `helper_double`: an internal helper function that will be placed in
    //   `inlinedCallees` (`Memory.callees`) and stepped transparently via `.tau`.
    // - `process_packet`: a root function that branches on `cfg.mode`
    //   (`TerminatorKind.switchInt`), invokes `ext_scale_add` on the non-zero
    //   branch, and doubles the result via `helper_double`.
    // - `inspect_ptr_identity`: a function taking `&u32` whose pointer argument
    //   and return value are decoded via the shadow provenance table
    //   (`ShadowProvenanceTable`).
    let lib_rs = r#"#![allow(dead_code)]

#[repr(C)]
#[derive(Clone, Copy)]
pub struct PaddedConfig {
    pub mode: u8,
    pub threshold: u32,
}

#[inline(never)]
pub fn ext_scale_add(x: u32, bonus: u32) -> u32 {
    x + bonus
}

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
"#;
    fs::write(src_dir.join("lib.rs"), lib_rs).expect("write src/lib.rs");

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
    //    1..4 so we verify that `decodeRawValue` ignores struct padding bytes.
    let mut cfg_val = PaddedConfig {
        mode: 1,
        threshold: 11,
    };
    unsafe {
        let base = (&mut cfg_val as *mut PaddedConfig).cast::<u8>();
        *base.add(1) = 0xAA;
        *base.add(2) = 0xBB;
        *base.add(3) = 0xCC;
    }
    let raw_cfg_bytes = value_as_raw_bytes(&cfg_val);
    assert_eq!(
        raw_cfg_bytes,
        vec![1, 0xAA, 0xBB, 0xCC, 11, 0, 0, 0],
        "expected 8-byte repr(C) struct with 3 corrupted padding bytes"
    );

    let input_val: u32 = 10;
    let raw_input_bytes = value_as_raw_bytes(&input_val);

    // 3a. Execute `process_packet(cfg_val, 10)` under `TraceRecorder` in
    //     call-boundary-only mode (`check_branches = false`):
    //     - `ext_scale_add(10, 11) -> 21` is interposed and recorded as an
    //       `ExtCall` event.
    //     - `helper_double(21) -> 42` is NOT interposed at the boundary because
    //       it is placed in `inlinedCallees` and stepped via `.tau` in the Lean
    //       ITree model.
    let (res_call_only, trace_call_only) = TraceRecorder::observe_root(
        "trace_pkg::process_packet",
        vec![raw_cfg_bytes.clone(), raw_input_bytes.clone()],
        |rec| {
            if cfg_val.mode == 0 {
                helper_double(input_val)
            } else {
                let scaled = rec.observe_ext_call(
                    "trace_pkg::ext_scale_add",
                    vec![
                        value_as_raw_bytes(&input_val),
                        value_as_raw_bytes(&cfg_val.threshold),
                    ],
                    || ext_scale_add(input_val, cfg_val.threshold),
                );
                helper_double(scaled)
            }
        },
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

    // 3c. Execute `inspect_ptr_identity(&watched_u32)` under `TraceRecorder`
    //     with `watched_u32` registered in the shadow provenance table at
    //     `(alloc_id = 7, tag = 7)`.
    let watched_box: Box<u32> = Box::new(123456);
    let watched_ref: &u32 = &watched_box;
    let (res_ptr, trace_ptr) = TraceRecorder::observe_root(
        "trace_pkg::inspect_ptr_identity",
        vec![value_as_raw_bytes(&watched_ref)],
        |rec| {
            rec.register_allocation(watched_ref, 7, 7);
            watched_ref
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

    // 4. Render the Lean 4 trace-verification module and append:
    //    1) A full-trace consistency & diagnostic proof (`checkRawByteTraceFullBounded_sound`
    //       + `diagnoseRawByteTraceFullBounded ... .tagName = "ok"`) for `trace_full`,
    //    2) A tampered-outcome negative diagnostic assertion proving by `rfl` that
    //       replacing the return bytes with `[99, 0, 0, 0]` deterministically yields
    //       `(diagnoseRawByteTraceObsErasedBounded ...).tagName = "outcome_mismatch"`, and
    //    3) A shadow-provenance pointer trace consistency & diagnostic proof for
    //       `inspect_ptr_identity`.
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
        "import Mir.TracePkg.process_packet\nimport Mir.TracePkg.inspect_ptr_identity\n",
    );
    let extra_theorems = format!(
        r#"
@[reducible]
def observedFullRawTrace : RawByteTrace :=
{full_trace_lean_expr}

set_option maxHeartbeats 2000000 in
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
set_option maxHeartbeats 2000000 in
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

set_option maxHeartbeats 2000000 in
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
    let build_status = Command::new("lake")
        .current_dir(&anneal_dir)
        .arg("build")
        .arg("Anneal")
        .arg("Mir.TracePkg.process_packet")
        .arg("Mir.TracePkg.ext_scale_add")
        .arg("Mir.TracePkg.helper_double")
        .arg("Mir.TracePkg.inspect_ptr_identity")
        .status()
        .expect("run lake build on Mir.TracePkg modules");
    assert!(
        build_status.success(),
        "lake build of Mir.TracePkg modules must succeed"
    );

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
