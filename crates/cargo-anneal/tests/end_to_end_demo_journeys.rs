//! End-to-end integration test exercising all four Anneal user journeys on
//! `examples/wireframe-demo` (`wireframe_demo`):
//!
//! 1. **Journey 1 (Bootstrap)**: Zero-authored-file `defaultProof` discharge on
//!    `WIRE_VERSION_V1` and `wire_protocol_version`, `#[model]` and
//!    `#[invariant]` companion capture, universal symbolic `#[spec]`
//!    verification on `frame_total_len`, stateful `&mut FrameCursor`
//!    verification on `advance_cursor` via `Anneal.FunctionalTranslation`, and
//!    whole-crate `CrateVerify` (`CrateVerificationResult`) kernel replay.
//! 2. **Journey 2 (Find & Repair an Existing `unsafe` Bug)**: Rejects unguarded
//!    `core::mem::transmute::<[u8; 4], WireHeader>(raw)` in `decode_wire_header`,
//!    kernel-checks a `¬ claim.holds` Undefined Behavior counterexample at
//!    `raw = [1, 2, 4, 0]` (`refuteClaimByBoundedUB`), and verifies the repaired
//!    function unconditionally.
//! 3. **Journey 3 (Keeping the Code Author and Reviewer in Check)**:
//!    - *3A*: Locks specifications with `--allow-impl-edit clamp_payload_window`
//!      and verifies that `agent-verify` blocks `#[spec]` tampering, buggy
//!      implementations, `sorry`, and rogue `axiom` declarations before
//!      accepting the sound implementation.
//!    - *3B*: Enforces `MirNoUB` across all `256` `u8` inputs via
//!      `refineSafeSpec` on safe `parse_compression_flag`, refuting a
//!      human-authored `unsafe { core::mem::transmute::<u8, bool>(flags_byte) }`
//!      shortcut at `flags_byte = 2`, checking vacuous-spec rejection via
//!      `lock-specs`, and verifying the repaired safe implementation.
//! 4. **Journey 4 (Iterative Verified `safe -> unsafe` Optimization)**: Freezes
//!    `checksum_frame_safe` as `specBody` via `StatefulEquivItemSpec` and
//!    `--allow-impl-edit checksum_frame_fast`, rejects an endianness-buggy
//!    `transmute` iteration via `--item checksum_frame_fast`, and verifies full
//!    behavioral equivalence (`StatefulEquivVerificationResult`) across all
//!    `2^64` 8-byte frames.

use std::env;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::{SystemTime, UNIX_EPOCH};

use cargo_anneal::{VerificationStatus, render_verification_report, verify_workspace_with_options, CliOptions, CliSubcommand};

fn unique_temp_dir(label: &str) -> PathBuf {
    let nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("system clock after epoch")
        .as_nanos();
    let dir = env::temp_dir().join(format!(
        "cargo-anneal-demo-{}-{}-{}",
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

fn ensure_binaries(checkout_root: &Path) -> (PathBuf, PathBuf) {
    let wrapper_name = format!("anneal-rustc-capture{}", env::consts::EXE_SUFFIX);
    let cli_name = format!("cargo-anneal{}", env::consts::EXE_SUFFIX);
    let target_dir = env::var_os("CARGO_TARGET_DIR")
        .map(PathBuf::from)
        .unwrap_or_else(|| checkout_root.join("target"));
    let wrapper_bin = target_dir.join("debug").join(&wrapper_name);
    let cli_bin = target_dir.join("debug").join(&cli_name);

    let cargo_bin = env::var("CARGO").unwrap_or_else(|_| "cargo".to_string());
    let status = Command::new(cargo_bin)
        .current_dir(checkout_root)
        .arg("build")
        .arg("-p")
        .arg("anneal-rustc-capture")
        .arg("--bin")
        .arg("anneal-rustc-capture")
        .arg("-p")
        .arg("cargo-anneal")
        .arg("--bin")
        .arg("cargo-anneal")
        .status()
        .expect("build anneal-rustc-capture and cargo-anneal binaries");
    assert!(status.success(), "cargo build must succeed");
    (wrapper_bin, cli_bin)
}

fn copy_dir_recursive(src: &Path, dst: &Path) {
    fs::create_dir_all(dst).expect("create destination directory");
    for entry in fs::read_dir(src).expect("read source directory") {
        let entry = entry.expect("read directory entry");
        let file_type = entry.file_type().expect("read entry file type");
        let src_path = entry.path();
        let dst_path = dst.join(entry.file_name());
        if file_type.is_dir() {
            copy_dir_recursive(&src_path, &dst_path);
        } else {
            fs::copy(&src_path, &dst_path).expect("copy file");
        }
    }
}

fn replace_once(text: &str, old: &str, new: &str, label: &str) -> String {
    assert!(
        text.contains(old),
        "expected snippet missing in {label}:\n{old}"
    );
    text.replacen(old, new, 1)
}

#[test]
fn end_to_end_four_demo_user_journeys() {
    let checkout_root = anneal_checkout_root();
    let (wrapper_bin, cli_bin) = ensure_binaries(&checkout_root);
    let anneal_spec_dir = checkout_root.join("crates/anneal-spec");
    let demo_dir = checkout_root.join("examples/wireframe-demo");

    let temp_root = unique_temp_dir("journeys");
    let temp_crate = temp_root.join("wireframe-demo");
    copy_dir_recursive(&demo_dir.join("src"), &temp_crate.join("src"));
    copy_dir_recursive(&demo_dir.join("anneal"), &temp_crate.join("anneal"));

    let cargo_toml_raw =
        fs::read_to_string(demo_dir.join("Cargo.toml")).expect("read wireframe-demo/Cargo.toml");
    let patched_cargo_toml = cargo_toml_raw.replace(
        "../../crates/anneal-spec",
        &anneal_spec_dir.display().to_string(),
    );
    fs::write(temp_crate.join("Cargo.toml"), patched_cargo_toml)
        .expect("write patched Cargo.toml");

    let bin_dir = cli_bin.parent().expect("cli_bin parent dir");
    let home_dir = env::var_os("HOME").map(PathBuf::from).unwrap_or_default();
    let mut path_entries = vec![
        bin_dir.to_path_buf(),
        home_dir.join(".elan/bin"),
        home_dir.join(".cargo/bin"),
    ];
    if let Some(existing) = env::var_os("PATH") {
        path_entries.extend(env::split_paths(&existing));
    }
    let path_env = env::join_paths(path_entries).expect("join PATH");

    let specs_dir = temp_crate.join("anneal/proofs/Specs/WireframeDemo");
    let proof_dir = temp_crate.join("anneal/proofs/Proof/WireframeDemo");
    let lib_rs_path = temp_crate.join("src/lib.rs");
    let clean_lib_rs = fs::read_to_string(&lib_rs_path).expect("read src/lib.rs");

    // =========================================================================
    // Journey 1: Bootstrap Verification on Safe Rust + CrateVerify Rollup
    // =========================================================================
    assert!(!specs_dir.join("WIRE_VERSION_V1.lean").exists());
    assert!(!proof_dir.join("WIRE_VERSION_V1.lean").exists());
    assert!(!specs_dir.join("wire_protocol_version.lean").exists());
    assert!(!proof_dir.join("wire_protocol_version.lean").exists());
    assert!(!specs_dir.join("frame_total_len.lean").exists());
    assert!(proof_dir.join("frame_total_len.lean").is_file());
    assert!(specs_dir.join("advance_cursor.lean").is_file());
    assert!(proof_dir.join("advance_cursor.lean").is_file());

    let units_dir = temp_crate.join("target/anneal/units");
    let base_opts = CliOptions {
        subcommand: CliSubcommand::Verify,
        workspace_root: temp_crate.clone(),
        manifest_path: None,
        units_dir: units_dir.clone(),
        rustc_wrapper: Some(wrapper_bin.clone()),
        anneal_repo_root: Some(checkout_root.clone()),
        from_existing_units: false,
        init_specs: false,
        init_proofs: false,
        allow_assumptions: false,
        locked_specs: false,
        item_filter: None,
        allow_impl_edit: None,
        filter: None,
        extra_cargo_args: Vec::new(),
    };

    let bootstrap_report = verify_workspace_with_options(&base_opts)
        .expect("Journey 1 bootstrap verification must succeed unconditionally");
    for mod_name in [
        "Verify.WireframeDemo.WIRE_VERSION_V1",
        "Verify.WireframeDemo.wire_protocol_version",
        "Verify.WireframeDemo.frame_total_len",
        "Verify.WireframeDemo.advance_cursor",
        "Verify.WireframeDemo.decode_wire_header",
        "Verify.WireframeDemo.clamp_payload_window",
        "Verify.WireframeDemo.parse_compression_flag",
        "Verify.WireframeDemo.checksum_frame_safe",
        "Verify.WireframeDemo.checksum_frame_fast",
    ] {
        assert_eq!(
            bootstrap_report.status_for(mod_name),
            Some(&VerificationStatus::VerifiedUnconditional),
            "expected {mod_name} to verify as VerifiedUnconditional"
        );
    }
    assert!(
        temp_crate.join(".anneal/generated/CrateVerify.lean").is_file(),
        "expected whole-crate CrateVerify.lean rollup module to be generated"
    );
    let rendered_bootstrap = render_verification_report(&bootstrap_report);
    assert!(
        rendered_bootstrap.contains("Totals: 9 unconditional, 0 conditional")
            && rendered_bootstrap.contains("TrustedBoundary kernel replay: PASS"),
        "unexpected bootstrap summary:\n{rendered_bootstrap}"
    );

    // =========================================================================
    // Journey 2: Find an Existing `unsafe` Bug & Kernel-Check Refutation
    // =========================================================================
    let buggy_j2_rs = replace_once(
        &clean_lib_rs,
        "    if raw[1] > 1 {\n        return 0;\n    }\n",
        "",
        "Journey 2 remove raw[1] > 1 guard",
    );
    fs::write(&lib_rs_path, &buggy_j2_rs).expect("write buggy decode_wire_header");

    let mut decode_item_opts = base_opts.clone();
    decode_item_opts.item_filter = Some("decode_wire_header".to_string());
    assert!(
        verify_workspace_with_options(&decode_item_opts).is_err(),
        "Journey 2 buggy decode_wire_header must fail verification"
    );

    let refute_j2_path = temp_crate.join(".anneal/generated/RefuteJourney2.lean");
    fs::write(
        &refute_j2_path,
        r#"import Trusted
import Anneal
import Obligations.WireframeDemo.decode_wire_header

namespace RefuteJourney2
open Trusted.MirAst
open Trusted.MirSemantics
open Trusted.VerificationResult
open Anneal.Rustc.V2026_06_01.SymbolicEval

def badRawArg : List Value :=
  [.aggregate 0 [
    .scalar { bits := 1, sizeBytes := 1 },
    .scalar { bits := 2, sizeBytes := 1 },
    .scalar { bits := 4, sizeBytes := 1 },
    .scalar { bits := 0, sizeBytes := 1 }
  ]]

theorem buggy_decode_wire_header_refuted :
    ¬ Obligations.WireframeDemo.decode_wire_header.claim.holds :=
  refuteClaimByBoundedUB
    Obligations.WireframeDemo.decode_wire_header.claim
    32
    badRawArg
    trivial
    rfl

end RefuteJourney2
"#,
    )
    .expect("write RefuteJourney2.lean");
    let lean_refute_j2 = Command::new("lake")
        .current_dir(temp_crate.join(".anneal"))
        .env("PATH", &path_env)
        .args(["env", "lean", refute_j2_path.to_str().expect("utf8 path")])
        .output()
        .expect("run lake env lean on RefuteJourney2.lean");
    assert!(
        lean_refute_j2.status.success(),
        "Journey 2 UB counterexample witness must compile in Lean kernel:\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&lean_refute_j2.stdout),
        String::from_utf8_lossy(&lean_refute_j2.stderr)
    );
    let _ = fs::remove_file(&refute_j2_path);

    fs::write(&lib_rs_path, &clean_lib_rs).expect("restore repaired decode_wire_header");
    verify_workspace_with_options(&decode_item_opts)
        .expect("Journey 2 repaired decode_wire_header must verify unconditionally");

    // =========================================================================
    // Journey 3A: Agent Authoring Under Locked Specs (--allow-impl-edit)
    // =========================================================================
    let stub_j3a_rs = replace_once(
        &clean_lib_rs,
        "    if requested <= max_window {\n        requested\n    } else {\n        max_window\n    }",
        "    let _ = (\n        requested,\n        max_window,\n    );\n    0",
        "Journey 3A stub clamp_payload_window",
    );
    fs::write(&lib_rs_path, &stub_j3a_rs).expect("write stub clamp_payload_window");

    let lock_j3a = Command::new(&cli_bin)
        .current_dir(&temp_crate)
        .env("PATH", &path_env)
        .env("ANNEAL_RUSTC_CAPTURE", &wrapper_bin)
        .env("ANNEAL_REPO_ROOT", &checkout_root)
        .args(["lock-specs", "--allow-impl-edit", "clamp_payload_window"])
        .output()
        .expect("run lock-specs --allow-impl-edit clamp_payload_window");
    assert!(
        lock_j3a.status.success(),
        "lock-specs --allow-impl-edit clamp_payload_window must succeed:\n{}\n{}",
        String::from_utf8_lossy(&lock_j3a.stdout),
        String::from_utf8_lossy(&lock_j3a.stderr)
    );
    let spec_lock_json =
        fs::read_to_string(temp_crate.join(".anneal/spec-lock.json")).expect("read spec-lock.json");
    assert!(
        spec_lock_json.contains("\"wireframe_demo::clamp_payload_window\""),
        "spec-lock.json must record clamp_payload_window in mutable_subjects:\n{spec_lock_json}"
    );

    let mut clamp_agent_opts = base_opts.clone();
    clamp_agent_opts.subcommand = CliSubcommand::AgentVerify;
    clamp_agent_opts.locked_specs = true;
    clamp_agent_opts.item_filter = Some("clamp_payload_window".to_string());

    // 3A-1: Tampering with `#[anneal_spec::spec]` ensures clause must fail spec-lock!
    let tampered_spec_rs = replace_once(
        &clean_lib_rs,
        "    ensures: |ref ret| *ret <= max_window && *ret <= requested && (*ret == requested || *ret == max_window),",
        "    ensures: |ref ret| *ret <= max_window,",
        "Journey 3A tamper spec",
    );
    fs::write(&lib_rs_path, &tampered_spec_rs).expect("write tampered spec");
    let tamper_err = verify_workspace_with_options(&clamp_agent_opts)
        .expect_err("agent-verify must reject tampered #[anneal_spec::spec]");
    assert!(
        tamper_err.contains("spec-lock violation"),
        "expected spec-lock violation on tampered #[spec], got:\n{tamper_err}"
    );

    // 3A-2: Buggy implementation (`max_window`) with unmodified spec must fail verification!
    let buggy_j3a_rs = replace_once(
        &clean_lib_rs,
        "    if requested <= max_window {\n        requested\n    } else {\n        max_window\n    }",
        "    let _ = (\n        requested,\n        max_window,\n    );\n    max_window",
        "Journey 3A buggy impl",
    );
    fs::write(&lib_rs_path, &buggy_j3a_rs).expect("write buggy clamp_payload_window");
    assert!(
        verify_workspace_with_options(&clamp_agent_opts).is_err(),
        "agent-verify must reject buggy clamp_payload_window implementation"
    );

    // 3A-3: Rogue `axiom` in Proof/WireframeDemo/clamp_payload_window.lean must fail TrustedBoundary!
    fs::write(&lib_rs_path, &clean_lib_rs).expect("restore clean src/lib.rs");
    let clamp_proof_path = proof_dir.join("clamp_payload_window.lean");
    let clean_clamp_proof = fs::read_to_string(&clamp_proof_path).expect("read clamp proof");
    fs::write(
        &clamp_proof_path,
        r#"import Trusted
import Obligations.WireframeDemo.clamp_payload_window
namespace Proof.WireframeDemo.clamp_payload_window
open Trusted.VerificationResult
axiom cheat_clamp : VerificationResult Obligations.WireframeDemo.clamp_payload_window.claim
theorem verified : VerificationResult Obligations.WireframeDemo.clamp_payload_window.claim :=
  cheat_clamp
end Proof.WireframeDemo.clamp_payload_window
"#,
    )
    .expect("write rogue axiom clamp proof");
    assert!(
        verify_workspace_with_options(&clamp_agent_opts).is_err(),
        "agent-verify must reject rogue axiom in Proof/WireframeDemo/clamp_payload_window.lean"
    );

    // 3A-4: Sound implementation + sound proof passes locked agent-verify!
    fs::write(&clamp_proof_path, &clean_clamp_proof).expect("restore clean clamp proof");
    verify_workspace_with_options(&clamp_agent_opts)
        .expect("Journey 3A sound clamp_payload_window must pass locked agent-verify");

    // =========================================================================
    // Journey 3B: Agent Reviewing Human Code (refineSafeSpec + NonVacuousPre)
    // =========================================================================
    let human_transmute_rs = replace_once(
        &clean_lib_rs,
        "    (flags_byte & 1) != 0",
        "    unsafe { core::mem::transmute::<u8, bool>(flags_byte) }",
        "Journey 3B human transmute shortcut",
    );
    fs::write(&lib_rs_path, &human_transmute_rs).expect("write human transmute shortcut");
    let mut parse_flag_opts = base_opts.clone();
    parse_flag_opts.item_filter = Some("parse_compression_flag".to_string());
    assert!(
        verify_workspace_with_options(&parse_flag_opts).is_err(),
        "Journey 3B refineSafeSpec must reject human `unsafe {{ transmute }}` behind requires"
    );

    let refute_j3b_path = temp_crate.join(".anneal/generated/RefuteJourney3B.lean");
    fs::write(
        &refute_j3b_path,
        r#"import Trusted
import Anneal
import Specs.WireframeDemo.parse_compression_flag
import Obligations.WireframeDemo.parse_compression_flag

namespace RefuteJourney3B
open Trusted.MirSemantics
open Trusted.VerificationResult
open Anneal.Rustc.V2026_06_01.SymbolicEval

theorem human_transmute_shortcut_refuted :
    ¬ Obligations.WireframeDemo.parse_compression_flag.claim.holds :=
  refuteClaimByBoundedUB
    Obligations.WireframeDemo.parse_compression_flag.claim
    16
    [.scalar { bits := 2, sizeBytes := 1 }]
    ⟨2, by omega, rfl⟩
    rfl

end RefuteJourney3B
"#,
    )
    .expect("write RefuteJourney3B.lean");
    let lean_refute_j3b = Command::new("lake")
        .current_dir(temp_crate.join(".anneal"))
        .env("PATH", &path_env)
        .args(["env", "lean", refute_j3b_path.to_str().expect("utf8 path")])
        .output()
        .expect("run lake env lean on RefuteJourney3B.lean");
    assert!(
        lean_refute_j3b.status.success(),
        "Journey 3B UB counterexample at flags_byte=2 must compile in Lean kernel:\n{}\n{}",
        String::from_utf8_lossy(&lean_refute_j3b.stdout),
        String::from_utf8_lossy(&lean_refute_j3b.stderr)
    );
    let _ = fs::remove_file(&refute_j3b_path);

    // Vacuous specification rejection check (`lock-specs` NonVacuousPre check).
    fs::write(&lib_rs_path, &clean_lib_rs).expect("restore clean src/lib.rs");
    let parse_spec_path = specs_dir.join("parse_compression_flag.lean");
    let clean_parse_spec = fs::read_to_string(&parse_spec_path).expect("read parse spec");
    fs::write(
        &parse_spec_path,
        r#"import Trusted
import Mir.WireframeDemo.parse_compression_flag
import Obligations.WireframeDemo.parse_compression_flag
namespace Specs.WireframeDemo.parse_compression_flag
open Trusted.VerificationResult
instance : ItemSpec "wireframe_demo::parse_compression_flag" :=
  Obligations.WireframeDemo.parse_compression_flag.refineSafeSpec
    (fun _ => False)
    (fun _ => True)
    (fun _ _ => True)
end Specs.WireframeDemo.parse_compression_flag
"#,
    )
    .expect("write vacuous parse_compression_flag spec");
    let vacuous_lock = Command::new(&cli_bin)
        .current_dir(&temp_crate)
        .env("PATH", &path_env)
        .env("ANNEAL_RUSTC_CAPTURE", &wrapper_bin)
        .env("ANNEAL_REPO_ROOT", &checkout_root)
        .arg("lock-specs")
        .output()
        .expect("run lock-specs on vacuous spec");
    assert!(
        !vacuous_lock.status.success(),
        "lock-specs must reject vacuous `False` safety domain on parse_compression_flag"
    );

    fs::write(&parse_spec_path, &clean_parse_spec).expect("restore clean parse spec");
    verify_workspace_with_options(&parse_flag_opts)
        .expect("Journey 3B repaired safe parse_compression_flag must verify unconditionally");

    // =========================================================================
    // Journey 4: Iterative Verified `safe -> unsafe` Checksum Optimization
    // =========================================================================
    let lock_j4 = Command::new(&cli_bin)
        .current_dir(&temp_crate)
        .env("PATH", &path_env)
        .env("ANNEAL_RUSTC_CAPTURE", &wrapper_bin)
        .env("ANNEAL_REPO_ROOT", &checkout_root)
        .args(["lock-specs", "--allow-impl-edit", "checksum_frame_fast"])
        .output()
        .expect("run lock-specs --allow-impl-edit checksum_frame_fast");
    assert!(
        lock_j4.status.success(),
        "lock-specs --allow-impl-edit checksum_frame_fast must succeed:\n{}\n{}",
        String::from_utf8_lossy(&lock_j4.stdout),
        String::from_utf8_lossy(&lock_j4.stderr)
    );

    let mut fast_item_opts = base_opts.clone();
    fast_item_opts.subcommand = CliSubcommand::AgentVerify;
    fast_item_opts.locked_specs = true;
    fast_item_opts.item_filter = Some("checksum_frame_fast".to_string());

    // Iteration 1: Little-endian `u16` lanes without byte-swap -> rejected!
    let iter1_buggy_rs = replace_once(
        &clean_lib_rs,
        "    let w0 = (((words[0] & 0x00ff) << 8) | (words[0] >> 8)) as u32;\n    let w1 = (((words[1] & 0x00ff) << 8) | (words[1] >> 8)) as u32;\n    let w2 = (((words[2] & 0x00ff) << 8) | (words[2] >> 8)) as u32;\n    let w3 = (((words[3] & 0x00ff) << 8) | (words[3] >> 8)) as u32;",
        "    let w0 = words[0] as u32;\n    let w1 = words[1] as u32;\n    let w2 = words[2] as u32;\n    let w3 = words[3] as u32;",
        "Journey 4 Iteration 1 little-endian bug",
    );
    fs::write(&lib_rs_path, &iter1_buggy_rs).expect("write Iteration 1 buggy checksum_frame_fast");
    assert!(
        verify_workspace_with_options(&fast_item_opts).is_err(),
        "Journey 4 Iteration 1 unswapped little-endian lanes must fail StatefulEquivVerificationResult"
    );

    // Iteration 2: Byte-swapped `u16` lanes -> passes `--item` AND full-crate `agent-verify`!
    fs::write(&lib_rs_path, &clean_lib_rs).expect("restore Iteration 2 checksum_frame_fast");
    verify_workspace_with_options(&fast_item_opts)
        .expect("Journey 4 Iteration 2 `--item checksum_frame_fast` must pass");

    let mut full_agent_opts = base_opts;
    full_agent_opts.subcommand = CliSubcommand::AgentVerify;
    full_agent_opts.locked_specs = true;
    let final_report = verify_workspace_with_options(&full_agent_opts)
        .expect("Journey 4 full-crate locked agent-verify + CrateVerify rollup must pass");
    let rendered_final = render_verification_report(&final_report);
    assert!(
        rendered_final.contains("Verify.WireframeDemo.checksum_frame_fast: UNCONDITIONAL")
            && rendered_final.contains("Totals: 9 unconditional, 0 conditional")
            && rendered_final.contains("TrustedBoundary kernel replay: PASS"),
        "unexpected final Journey 4 report:\n{rendered_final}"
    );

    let _ = fs::remove_dir_all(&temp_root);
}
