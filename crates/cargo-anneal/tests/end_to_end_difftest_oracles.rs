// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Unit and end-to-end integration tests for the shared Miri + Anneal
//! differential oracle pipeline (`cargo_anneal::miri_oracle`).

use std::env;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::{SystemTime, UNIX_EPOCH};

use cargo_anneal::{
    ALLOW_MISSING_MIRI_ENV, AnnealOutcome, ComparisonVerdict, DEFAULT_CAPTURE_RUSTFLAGS,
    DEFAULT_MIRI_FLAGS, DifftestOracleConfig, DivergenceKind, MiriOutcome, MiriToolchain,
    NotComparedReason, OracleItemSpec, SourcePos, SourceSpan, compare_miri_and_anneal,
    confirm_anneal_outcomes_in_kernel, discover_zero_arg_pub_fns, parse_anneal_probe_output,
    parse_miri_process_output, run_difftest_oracle_pipeline,
};

fn unique_temp_dir(label: &str) -> PathBuf {
    let nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("system clock after epoch")
        .as_nanos();
    let dir = env::temp_dir().join(format!(
        "cargo-anneal-oracles-{}-{}-{}",
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

#[test]
fn comparator_covers_every_verdict_divergence_and_not_compared_class() {
    let span_a = SourceSpan::parse_anneal_span("src/lib.rs:10:5: 10:20").unwrap();
    let span_b = SourceSpan::parse_anneal_span("src/lib.rs:20:5: 20:15").unwrap();
    let pos_in_a = SourcePos::parse_rustc_pos("src/lib.rs:10:5").unwrap();
    let pos_in_b = SourcePos::parse_rustc_pos("src/lib.rs:20:9").unwrap();

    // 1. Agree: PassUnit, PassScalar, Panic (matching span), Ub (matching span)
    assert_eq!(
        compare_miri_and_anneal(&MiriOutcome::PassUnit, &AnnealOutcome::PassUnit),
        ComparisonVerdict::Agree
    );
    assert_eq!(
        compare_miri_and_anneal(
            &MiriOutcome::PassScalar {
                bits: 42,
                size_bytes: 4
            },
            &AnnealOutcome::PassScalar {
                bits: 42,
                size_bytes: 4
            }
        ),
        ComparisonVerdict::Agree
    );
    assert_eq!(
        compare_miri_and_anneal(
            &MiriOutcome::Panic {
                pos: Some(pos_in_a.clone()),
                message: "overflow".to_string()
            },
            &AnnealOutcome::Panic {
                span: Some(span_a.clone())
            }
        ),
        ComparisonVerdict::Agree
    );
    assert_eq!(
        compare_miri_and_anneal(
            &MiriOutcome::Ub {
                pos: Some(pos_in_a.clone()),
                message: "dangling".to_string()
            },
            &AnnealOutcome::Ub {
                span: Some(span_a.clone())
            }
        ),
        ComparisonVerdict::Agree
    );

    // 2. Diverge::WrongValue (different scalar bits, different scalar width,
    //    unit vs scalar)
    assert_eq!(
        compare_miri_and_anneal(
            &MiriOutcome::PassScalar {
                bits: 42,
                size_bytes: 4
            },
            &AnnealOutcome::PassScalar {
                bits: 43,
                size_bytes: 4
            }
        ),
        ComparisonVerdict::Diverge(DivergenceKind::WrongValue {
            miri: "pass:scalar:42:4".to_string(),
            anneal: "pass:scalar:43:4".to_string(),
        })
    );
    assert_eq!(
        compare_miri_and_anneal(
            &MiriOutcome::PassUnit,
            &AnnealOutcome::PassScalar {
                bits: 0,
                size_bytes: 1
            }
        ),
        ComparisonVerdict::Diverge(DivergenceKind::WrongValue {
            miri: "pass:unit".to_string(),
            anneal: "pass:scalar:0:1".to_string(),
        })
    );

    // 3. Diverge::FalsePositiveUb (Miri Pass or Panic vs Anneal Ub)
    assert_eq!(
        compare_miri_and_anneal(
            &MiriOutcome::PassScalar {
                bits: 1,
                size_bytes: 4
            },
            &AnnealOutcome::Ub {
                span: Some(span_a.clone())
            }
        ),
        ComparisonVerdict::Diverge(DivergenceKind::FalsePositiveUb {
            miri: "pass:scalar:1:4".to_string(),
            anneal_span: Some(span_a.clone()),
        })
    );
    assert_eq!(
        compare_miri_and_anneal(
            &MiriOutcome::Panic {
                pos: Some(pos_in_a.clone()),
                message: "panicked".to_string()
            },
            &AnnealOutcome::Ub {
                span: Some(span_a.clone())
            }
        ),
        ComparisonVerdict::Diverge(DivergenceKind::FalsePositiveUb {
            miri: "panic@src/lib.rs:10:5".to_string(),
            anneal_span: Some(span_a.clone()),
        })
    );

    // 4. Diverge::MissedUb (Miri Ub vs Anneal Pass or Panic)
    assert_eq!(
        compare_miri_and_anneal(
            &MiriOutcome::Ub {
                pos: Some(pos_in_a.clone()),
                message: "oob".to_string()
            },
            &AnnealOutcome::PassScalar {
                bits: 10,
                size_bytes: 4
            }
        ),
        ComparisonVerdict::Diverge(DivergenceKind::MissedUb {
            miri_pos: Some(pos_in_a.clone()),
            miri_msg: "oob".to_string(),
            anneal: "pass:scalar:10:4".to_string(),
        })
    );

    // 5. Diverge::PanicVsReturn and ReturnVsPanic
    assert_eq!(
        compare_miri_and_anneal(
            &MiriOutcome::Panic {
                pos: Some(pos_in_a.clone()),
                message: "div by zero".to_string()
            },
            &AnnealOutcome::PassUnit
        ),
        ComparisonVerdict::Diverge(DivergenceKind::PanicVsReturn {
            miri_pos: Some(pos_in_a.clone()),
            miri_msg: "div by zero".to_string(),
            anneal: "pass:unit".to_string(),
        })
    );
    assert_eq!(
        compare_miri_and_anneal(
            &MiriOutcome::PassUnit,
            &AnnealOutcome::Panic {
                span: Some(span_a.clone())
            }
        ),
        ComparisonVerdict::Diverge(DivergenceKind::ReturnVsPanic {
            miri: "pass:unit".to_string(),
            anneal_span: Some(span_a.clone()),
        })
    );

    // 6. Diverge::UbLocationMismatch (mismatched span or missing span)
    assert_eq!(
        compare_miri_and_anneal(
            &MiriOutcome::Ub {
                pos: Some(pos_in_b.clone()),
                message: "frozen write".to_string()
            },
            &AnnealOutcome::Ub {
                span: Some(span_a.clone())
            }
        ),
        ComparisonVerdict::Diverge(DivergenceKind::UbLocationMismatch {
            miri_pos: Some(pos_in_b.clone()),
            miri_msg: "frozen write".to_string(),
            anneal_span: Some(span_a.clone()),
        })
    );
    assert_eq!(
        compare_miri_and_anneal(
            &MiriOutcome::Ub {
                pos: None,
                message: "missing pos".to_string()
            },
            &AnnealOutcome::Ub {
                span: Some(span_a.clone())
            }
        ),
        ComparisonVerdict::Diverge(DivergenceKind::UbLocationMismatch {
            miri_pos: None,
            miri_msg: "missing pos".to_string(),
            anneal_span: Some(span_a.clone()),
        })
    );

    // 7. Diverge::PanicSiteMismatch (mismatched span or missing span)
    assert_eq!(
        compare_miri_and_anneal(
            &MiriOutcome::Panic {
                pos: Some(pos_in_b.clone()),
                message: "wrong panic site".to_string()
            },
            &AnnealOutcome::Panic {
                span: Some(span_a.clone())
            }
        ),
        ComparisonVerdict::Diverge(DivergenceKind::PanicSiteMismatch {
            miri_pos: Some(pos_in_b),
            anneal_span: Some(span_a.clone()),
        })
    );

    // 8. NotCompared: ExternalCall, Unsupported, OutOfFuel, MiriOracleError,
    //    CaptureFailed. None of these may ever be classified as Agree.
    let not_compared_cases = vec![
        (
            MiriOutcome::PassUnit,
            AnnealOutcome::ExternalCall {
                def_path: "core::intrinsics::exact_div".to_string(),
                span: Some(span_b.clone()),
            },
            NotComparedReason::ExternalCall("core::intrinsics::exact_div".to_string()),
        ),
        (
            MiriOutcome::Ub {
                pos: Some(pos_in_a),
                message: "ub".to_string(),
            },
            AnnealOutcome::Unsupported {
                span: Some(span_b.clone()),
            },
            NotComparedReason::Unsupported(Some(span_b.clone())),
        ),
        (
            MiriOutcome::PassUnit,
            AnnealOutcome::OutOfFuel {
                span: Some(span_b),
            },
            NotComparedReason::OutOfFuel(Some(
                SourceSpan::parse_anneal_span("src/lib.rs:20:5: 20:15").unwrap(),
            )),
        ),
        (
            MiriOutcome::OracleError("driver failed".to_string()),
            AnnealOutcome::PassUnit,
            NotComparedReason::MiriOracleError("driver failed".to_string()),
        ),
        (
            MiriOutcome::PassUnit,
            AnnealOutcome::CaptureOrLeanError("lean failed".to_string()),
            NotComparedReason::CaptureFailed("lean failed".to_string()),
        ),
    ];
    for (m, a, expected_reason) in not_compared_cases {
        let v = compare_miri_and_anneal(&m, &a);
        assert!(!v.is_agree(), "NotCompared case must never be Agree: {v:?}");
        assert_eq!(v, ComparisonVerdict::NotCompared(expected_reason));
    }
}

#[test]
fn parsers_and_discovery_handle_miri_and_anneal_probe_formats() {
    let src = "\
pub fn helper_with_arg(x: u32) -> u32 { x + 1 }
pub fn first_item() -> u32 { 1 }
pub unsafe fn second_item() {}
fn private_item() {}
";
    assert_eq!(
        discover_zero_arg_pub_fns(src),
        vec!["first_item".to_string(), "second_item".to_string()]
    );

    let panic_stderr = "\
thread 'main' (12345) panicked at src/lib.rs:140:5:
attempt to compute `u32::MAX + 1_u32`, which would overflow
note: run with `RUST_BACKTRACE=1` for a backtrace
";
    let panic_out = parse_miri_process_output(
        "panic_checked_add_overflow",
        false,
        "MIRI_START:panic_checked_add_overflow\n",
        panic_stderr,
    );
    assert_eq!(
        panic_out,
        MiriOutcome::Panic {
            pos: Some(SourcePos {
                file: "src/lib.rs".to_string(),
                line: 140,
                col: 5,
            }),
            message: "attempt to compute `u32::MAX + 1_u32`, which would overflow".to_string(),
        }
    );

    let probe_stdout = "\
ANNEAL_PROBE\tfirst_item\tpass:scalar:42:4\tsrc/lib.rs:10:5: 10:15
ANNEAL_PROBE\tsecond_item\tub\tsrc/lib.rs:22:9: 22:16
ANNEAL_PROBE\tthird_item\texternalCall:core::intrinsics::exact_div\tsrc/lib.rs:30:5: 30:25
";
    let parsed = parse_anneal_probe_output(probe_stdout).expect("parse probe stdout");
    assert_eq!(
        parsed.get("first_item"),
        Some(&AnnealOutcome::PassScalar {
            bits: 42,
            size_bytes: 4
        })
    );
    assert_eq!(
        parsed.get("second_item"),
        Some(&AnnealOutcome::Ub {
            span: Some(SourceSpan::parse_anneal_span("src/lib.rs:22:9: 22:16").unwrap())
        })
    );
    assert_eq!(
        parsed.get("third_item"),
        Some(&AnnealOutcome::ExternalCall {
            def_path: "core::intrinsics::exact_div".to_string(),
            span: Some(SourceSpan::parse_anneal_span("src/lib.rs:30:5: 30:25").unwrap()),
        })
    );
}

#[test]
fn missing_miri_sysroot_is_a_hard_error() {
    let empty_dir = unique_temp_dir("missing-sysroot");
    let err = MiriToolchain::resolve(None, None, Some(&empty_dir))
        .expect_err("missing lib/rustlib in sysroot must fail with hard error");
    assert!(
        err.contains("missing lib/rustlib"),
        "unexpected error message: {err}"
    );
    let _ = fs::remove_dir_all(&empty_dir);
}

#[test]
fn end_to_end_canary_corpus_runs_real_miri_and_real_lean_and_catches_divergences() {
    let toolchain = match MiriToolchain::resolve(None, None, None) {
        Ok(tc) => tc,
        Err(err) => {
            if env::var(ALLOW_MISSING_MIRI_ENV).as_deref() == Ok("1") {
                println!(
                    "SKIPPED: end_to_end_canary_corpus ({ALLOW_MISSING_MIRI_ENV}=1): {err}"
                );
                return;
            }
            panic!(
                "Miri toolchain/sysroot is required (set {ALLOW_MISSING_MIRI_ENV}=1 only when \
                 explicitly opting out): {err}"
            );
        }
    };

    let checkout_root = anneal_checkout_root();
    let wrapper_bin = ensure_rustc_capture_binary(&checkout_root);

    let temp_dir = unique_temp_dir("canary-corpus");
    let corpus_root = temp_dir.join("canary_corpus");
    fs::create_dir_all(corpus_root.join("src")).expect("create canary src dir");

    let cargo_toml = "\
[package]
name = \"canary_corpus\"
version = \"0.1.0\"
edition = \"2024\"

[lib]
path = \"src/lib.rs\"
";
    fs::write(corpus_root.join("Cargo.toml"), cargo_toml).expect("write Cargo.toml");

    let lib_rs = "\
#![no_std]
#![allow(
    arithmetic_overflow,
    unconditional_panic,
    deref_nullptr,
    internal_features,
    integer_to_ptr_transmutes
)]
#![feature(core_intrinsics)]

use core::intrinsics::{exact_div, offset};

#[repr(C)]
struct PairU32 {
    a: u32,
    b: u32,
}

pub fn canary_pass_unit() {}

pub fn canary_pass_scalar() -> u32 {
    40 + 2
}

pub fn canary_pass_negative_i32() -> i32 {
    -5
}

pub fn canary_panic_overflow() -> u32 {
    let x: u32 = u32::MAX;
    let y: u32 = 1;
    x + y
}

pub fn canary_ub_null_deref() -> u32 {
    let p: *const u32 = 0usize as *const u32;
    unsafe { *p }
}

pub fn tb_child_write_then_parent_read() -> u32 {
    let mut x: u32 = 0;
    let root: *mut u32 = &raw mut x;
    let r: &mut u32 = unsafe { &mut *root };
    *r = 1;
    let y = unsafe { *root };
    y
}

pub fn tb_child_write_then_parent_write() -> u32 {
    let mut x: u32 = 1;
    let p1: *mut u32 = &raw mut x;
    let r2: &mut u32 = unsafe { &mut *p1 };
    *r2 = 2;
    unsafe {
        *p1 = 3;
    }
    unsafe { *p1 }
}

pub fn safe_reborrow_then_parent_write() -> u32 {
    let mut x: u32 = 5;
    let p: &mut u32 = &mut x;
    {
        let q: &mut u32 = &mut *p;
        *q = 6;
    }
    *p = 7;
    *p
}

pub fn ub_tb_use_frozen_mut_after_parent_read() -> u32 {
    let mut x: u32 = 0;
    let root: *mut u32 = &raw mut x;
    let r: &mut u32 = unsafe { &mut *root };
    *r = 1;
    let _obs = unsafe { *root };
    *r = 2;
    unsafe { *root }
}

pub fn ub_tb_conflicting_active_mut_borrows() -> u32 {
    let mut x: u32 = 1;
    let p1: *mut u32 = &raw mut x;
    let r2: &mut u32 = unsafe { &mut *p1 };
    *r2 = 2;
    unsafe {
        *p1 = 3;
    }
    *r2
}

pub fn pass_ptr_offset_within_array() -> u32 {
    let pair = PairU32 { a: 100, b: 300 };
    let base: *const u32 = &raw const pair.a;
    unsafe {
        let p1 = offset(base, 1isize);
        *p1
    }
}

pub fn canary_external_call_exact_div() -> u32 {
    unsafe { exact_div(20u32, 4u32) }
}

#[inline(never)]
fn unlinked_helper_ten() -> u32 {
    10
}

pub fn canary_external_call_unlinked_helper() -> u32 {
    unlinked_helper_ten()
}
";
    fs::write(corpus_root.join("src/lib.rs"), lib_rs).expect("write src/lib.rs");

    let discovered = discover_zero_arg_pub_fns(lib_rs);
    assert_eq!(discovered.len(), 13);
    let items: Vec<OracleItemSpec> = discovered
        .into_iter()
        .map(OracleItemSpec::new)
        .collect();

    let config = DifftestOracleConfig {
        corpus_root: corpus_root.clone(),
        capture_rustflags: DEFAULT_CAPTURE_RUSTFLAGS
            .iter()
            .map(|s| (*s).to_string())
            .collect(),
        miri_flags: DEFAULT_MIRI_FLAGS.iter().map(|s| (*s).to_string()).collect(),
        anneal_repo_root: Some(checkout_root),
        rustc_wrapper: Some(wrapper_bin),
        toolchain,
    };

    let report = run_difftest_oracle_pipeline(&config, &items)
        .expect("run Miri + Anneal oracle pipeline on canary corpus");

    // 11 Agree (5 base canaries + 5 Tree Borrows parent/child items
    // + `canary_external_call_exact_div`, interpreted inline since I-11)
    // + 1 Diverge (`pass_ptr_offset_within_array`)
    // + 1 NotCompared (`canary_external_call_unlinked_helper`) = 13
    for item in &report.items {
        println!(
            "ORACLE_CANARY\t{}\tmiri={}\tanneal={}\tverdict={:?}\tkernel_confirmed={}",
            item.name,
            item.miri.summary_tag(),
            item.anneal.summary_tag(),
            item.verdict,
            item.kernel_confirmed
        );
    }
    assert_eq!(report.items.len(), 13);
    assert_eq!(report.agree_count, 11);
    assert_eq!(report.diverge_count, 1);
    assert_eq!(report.not_compared_count, 1);
    let confirm_path = report
        .confirm_module_path
        .as_ref()
        .expect("divergent items must produce MiriOracleConfirm.lean");
    assert!(
        confirm_path.is_file(),
        "divergent items must be kernel-certified in MiriOracleConfirm.lean"
    );
    let confirm_text = fs::read_to_string(confirm_path).expect("read MiriOracleConfirm.lean");
    assert!(
        confirm_text.contains("theorem confirm_tag_pass_ptr_offset_within_array"),
        "missing confirm_tag_pass_ptr_offset_within_array in MiriOracleConfirm.lean"
    );
    assert!(
        confirm_text.contains("theorem confirm_probe_pass_ptr_offset_within_array"),
        "missing confirm_probe_pass_ptr_offset_within_array in MiriOracleConfirm.lean"
    );
    let probe_path = corpus_root.join(".anneal/oracle/MiriOracleProbe.lean");
    assert!(
        probe_path.is_file(),
        "MiriOracleProbe.lean must exist at {}",
        probe_path.display()
    );

    // Verify the 5 base agreeing canaries:
    assert_eq!(
        report.item("canary_pass_unit").unwrap().verdict,
        ComparisonVerdict::Agree
    );
    assert_eq!(
        report.item("canary_pass_scalar").unwrap().verdict,
        ComparisonVerdict::Agree
    );
    let neg_i32 = report.item("canary_pass_negative_i32").unwrap();
    assert_eq!(neg_i32.verdict, ComparisonVerdict::Agree);
    assert_eq!(
        neg_i32.miri,
        MiriOutcome::PassScalar {
            bits: (-5i32 as u32) as u128,
            size_bytes: 4
        }
    );
    assert_eq!(
        report.item("canary_panic_overflow").unwrap().verdict,
        ComparisonVerdict::Agree
    );
    let ub_null = report.item("canary_ub_null_deref").unwrap();
    assert_eq!(ub_null.verdict, ComparisonVerdict::Agree);
    if let MiriOutcome::Ub { pos: Some(pos), .. } = &ub_null.miri {
        assert_eq!(pos.line, 37, "Miri UB line must skip line-36 cast warning");
    } else {
        panic!("expected MiriOutcome::Ub with pos on canary_ub_null_deref");
    }

    // Verify the 3 Tree Borrows parent/child passing counterexamples now AGREE:
    for (name, expected_bits) in [
        ("tb_child_write_then_parent_read", 1u128),
        ("tb_child_write_then_parent_write", 3u128),
        ("safe_reborrow_then_parent_write", 7u128),
    ] {
        let item_rep = report.item(name).unwrap();
        assert_eq!(
            item_rep.verdict,
            ComparisonVerdict::Agree,
            "{name} must agree with Miri under hierarchical Tree Borrows"
        );
        assert_eq!(
            item_rep.anneal,
            AnnealOutcome::PassScalar {
                bits: expected_bits,
                size_bytes: 4
            }
        );
    }

    // Verify the 2 Tree Borrows parent/child UB tests agree on BOTH verdict AND
    // exact UB source location:
    for (name, expected_ub_line) in [
        ("ub_tb_use_frozen_mut_after_parent_read", 77u32),
        ("ub_tb_conflicting_active_mut_borrows", 89u32),
    ] {
        let item_rep = report.item(name).unwrap();
        assert_eq!(
            item_rep.verdict,
            ComparisonVerdict::Agree,
            "{name} must agree with Miri on both UB verdict and source location"
        );
        match (&item_rep.miri, &item_rep.anneal) {
            (
                MiriOutcome::Ub {
                    pos: Some(m_pos), ..
                },
                AnnealOutcome::Ub {
                    span: Some(a_span),
                },
            ) => {
                assert_eq!(m_pos.line, expected_ub_line);
                assert!(
                    a_span.contains_pos(m_pos),
                    "Anneal span {a_span:?} must contain Miri pos {m_pos:?}"
                );
            }
            other => panic!("expected matching UB with spans for {name}, got {other:?}"),
        }
    }

    // Verify the divergent pointer-offset item is kernel-confirmed:
    let ptr_offset = report.item("pass_ptr_offset_within_array").unwrap();
    assert!(ptr_offset.kernel_confirmed);
    assert_eq!(
        ptr_offset.verdict,
        ComparisonVerdict::Diverge(DivergenceKind::WrongValue {
            miri: "pass:scalar:300:4".to_string(),
            anneal: "pass:scalar:100:4".to_string(),
        })
    );

    // Verify `exact_div` is now interpreted inline and agrees with Miri on the
    // exact quotient (20 / 4 = 5):
    let exact_div_item = report.item("canary_external_call_exact_div").unwrap();
    assert_eq!(exact_div_item.verdict, ComparisonVerdict::Agree);
    assert_eq!(
        exact_div_item.anneal,
        AnnealOutcome::PassScalar {
            bits: 5,
            size_bytes: 4
        }
    );

    // Verify the unlinked external-call item is NotCompared (never Agree):
    let ext_call = report.item("canary_external_call_unlinked_helper").unwrap();
    assert!(!ext_call.verdict.is_agree());
    assert_eq!(
        ext_call.verdict,
        ComparisonVerdict::NotCompared(NotComparedReason::ExternalCall(
            "canary_corpus::unlinked_helper_ten".to_string()
        ))
    );

    // Negative check 1: tampering with an item's claimed Anneal outcome tag in
    // `confirm_anneal_outcomes_in_kernel` must fail Lean kernel type-checking.
    let tampered_tag = vec![(
        OracleItemSpec::new("tb_child_write_then_parent_read"),
        AnnealOutcome::Ub {
            span: Some(
                SourceSpan::parse_anneal_span("src/lib.rs:45:5: 45:25")
                    .expect("parse tampered span"),
            ),
        },
    )];
    let confirm_err = confirm_anneal_outcomes_in_kernel(
        &corpus_root,
        &report.crate_camel,
        &tampered_tag,
    )
    .expect_err("tampered kernel confirmation theorem must fail to compile");
    assert!(
        confirm_err.contains("Lean kernel confirmation failed"),
        "unexpected error: {confirm_err}"
    );

    // Negative check 2: keeping `AnnealOutcome::Ub` (matching `MirDiffTag.ub`)
    // on `ub_tb_use_frozen_mut_after_parent_read` but tampering with the source
    // span must also fail Lean kernel type-checking (`confirm_probe_<name>`).
    let tampered_span = vec![(
        OracleItemSpec::new("ub_tb_use_frozen_mut_after_parent_read"),
        AnnealOutcome::Ub {
            span: Some(
                SourceSpan::parse_anneal_span("src/lib.rs:99:1: 99:5")
                    .expect("parse tampered span"),
            ),
        },
    )];
    let span_err = confirm_anneal_outcomes_in_kernel(
        &corpus_root,
        &report.crate_camel,
        &tampered_span,
    )
    .expect_err("tampered span in kernel confirmation theorem must fail to compile");
    assert!(
        span_err.contains("Lean kernel confirmation failed"),
        "unexpected error: {span_err}"
    );

    fs::write(confirm_path, &confirm_text)
        .expect("restore valid MiriOracleConfirm.lean");

    let _ = fs::remove_dir_all(&temp_dir);
}
