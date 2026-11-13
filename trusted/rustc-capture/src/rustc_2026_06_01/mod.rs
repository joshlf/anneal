//! Version-scoped `rustc_driver` backend for
//! `rustc 1.98.0-nightly (14210df0e 2026-05-31)` (`V2026_06_01`).
//!
//! All `rustc_private` compiler queries (`tcx.optimized_mir`, `tcx.layout_of`,
//! `tcx.fn_abi_of_instance`, `tcx.global_alloc`, and `anodized` / external
//! sidecar attribute extraction) live under this module directory so future
//! `rustc` versions can be added alongside it without modifying the outer
//! manifest protocol.

pub mod driver;
pub mod layout_lower;
pub mod mir_lower;
pub mod specs;

use crate::manifest::{MIR_DIALECT_V2026_06_01, RUSTC_COMMIT_SHA, RUSTC_VERSION_STRING};

/// Returns the dialect identifier and pinned `rustc` commit SHA handled by this
/// backend.
pub const fn backend_descriptor() -> (&'static str, &'static str, &'static str) {
    (
        MIR_DIALECT_V2026_06_01,
        RUSTC_VERSION_STRING,
        RUSTC_COMMIT_SHA,
    )
}

#[cfg(test)]
mod tests {
    use std::fs;
    use std::path::{Path, PathBuf};
    use std::process::Command;
    use std::time::{SystemTime, UNIX_EPOCH};

    use crate::manifest::{
        ANNEAL_CAPTURE_DIR_ENV, ANNEAL_CAPTURE_FILTER_ENV, CapturedItemKind, UnitCaptureManifest,
        sha256_hex,
    };
    use crate::rustc_2026_06_01::driver::{
        decode_os_args, derive_unit_id, disambiguate_identifier, matches_capture_filter,
        normalize_wrapper_args, parse_capture_filter, run_with_args, run_with_args_and_filter,
        should_run_capture_for_args,
    };
    use crate::rustc_2026_06_01::mir_lower::{
        is_unnamed_const_def_path, verification_runtime_check_value,
    };

    fn unique_temp_dir(label: &str) -> PathBuf {
        let nanos = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .map(|d| d.as_nanos())
            .unwrap_or(0);
        let pid = std::process::id();
        let dir = std::env::temp_dir().join(format!("anneal-rustc-capture-{label}-{pid}-{nanos}"));
        fs::create_dir_all(&dir).expect("create temp test dir");
        dir
    }

    fn verify_captured_demo_artifacts(capture_dir: &Path) {
        let manifest_path = capture_dir.join("demo").join("UnitCaptureManifest.json");
        assert!(
            manifest_path.exists(),
            "expected UnitCaptureManifest.json at {}",
            manifest_path.display()
        );

        let manifest_json =
            fs::read_to_string(&manifest_path).expect("read UnitCaptureManifest.json");
        let parsed = UnitCaptureManifest::from_json_str(&manifest_json)
            .expect("parse UnitCaptureManifest.json");

        assert_eq!(parsed.unit_id, "demo");
        assert_eq!(parsed.crate_name, "demo");
        assert!(parsed.compilation_succeeded);
        assert!(!parsed.rust_sources.is_empty());
        assert!(!parsed.unit_targets.is_empty());

        let answer_target = parsed
            .unit_targets
            .iter()
            .find(|t| t.target.def_id == "demo::answer")
            .expect("find demo::answer in UnitCaptureManifest");
        assert_eq!(answer_target.item_kind, CapturedItemKind::Subject);
        assert_eq!(answer_target.associated_subject_def_id, None);
        assert_eq!(answer_target.lean_module_name, "Mir.Demo.answer");
        assert_eq!(answer_target.target.mir_module_path, "Mir/Demo/answer.lean");

        let lean_path = capture_dir
            .join("demo")
            .join(&answer_target.target.mir_module_path);
        assert!(
            lean_path.exists(),
            "expected emitted Lean module at {}",
            lean_path.display()
        );
        let lean_source = fs::read_to_string(&lean_path).expect("read Mir/Demo/answer.lean");
        assert_eq!(
            sha256_hex(lean_source.as_bytes()),
            answer_target.target.mir_module_sha256
        );
        assert!(lean_source.contains("namespace Mir.Demo.answer"));
        assert!(lean_source.contains("def layouts : LayoutTable :="));
        assert!(lean_source.contains("def body : CapturedMir :="));
        assert!(lean_source.contains("def defaultClaim : Claim :="));
        assert!(lean_source.contains("-- TypeLayout[0]: size="));
        assert!(lean_source.contains("-- bb0:"));

        let req_target = parsed
            .unit_targets
            .iter()
            .find(|t| t.target.def_id == "demo::__anodized_fn_requires_answer")
            .expect("find companion requires item");
        assert_eq!(req_target.item_kind, CapturedItemKind::InlineSpecRequires);
        assert_eq!(
            req_target.associated_subject_def_id.as_deref(),
            Some("demo::answer")
        );

        let ens_target = parsed
            .unit_targets
            .iter()
            .find(|t| t.target.def_id == "demo::__anodized_fn_ensures_answer")
            .expect("find companion ensures item");
        assert_eq!(ens_target.item_kind, CapturedItemKind::InlineSpecEnsures);
        assert_eq!(
            ens_target.associated_subject_def_id.as_deref(),
            Some("demo::answer")
        );

        let qual_target = parsed
            .unit_targets
            .iter()
            .find(|t| t.target.def_id == "demo::__anodized_fn_qualifiers_answer")
            .expect("find companion qualifiers item");
        assert_eq!(
            qual_target.item_kind,
            CapturedItemKind::InlineSpecQualifiers
        );
        assert_eq!(
            qual_target.associated_subject_def_id.as_deref(),
            Some("demo::answer")
        );

        let ext_req_target = parsed
            .unit_targets
            .iter()
            .find(|t| t.target.def_id == "demo::__anodized_fn_requires_ext_fn")
            .expect("find external spec requires item");
        assert_eq!(
            ext_req_target.item_kind,
            CapturedItemKind::InlineSpecRequires
        );
        assert_eq!(
            ext_req_target.associated_subject_def_id.as_deref(),
            Some("core::num::u32::wrapping_add")
        );

        let ext_marker = parsed
            .unit_targets
            .iter()
            .find(|t| t.target.def_id == "demo::__ANNEAL_EXT_SPEC_TARGET_ext_fn")
            .expect("find external spec marker item");
        assert_eq!(ext_marker.item_kind, CapturedItemKind::ExternalSpec);
        assert_eq!(
            ext_marker.associated_subject_def_id.as_deref(),
            Some("core::num::u32::wrapping_add")
        );

        let model_fn = parsed
            .unit_targets
            .iter()
            .find(|t| t.target.def_id == "demo::MyCounter")
            .expect("find model item");
        assert_eq!(model_fn.item_kind, CapturedItemKind::Model);
    }

    #[test]
    fn driver_captures_unit_manifest_and_mir_lean_modules() {
        let temp_root = unique_temp_dir("integration");
        let capture_dir = temp_root.join("capture");
        let out_dir = temp_root.join("out");
        fs::create_dir_all(&capture_dir).expect("create capture dir");
        fs::create_dir_all(&out_dir).expect("create out dir");

        let src_path = temp_root.join("demo_lib.rs");
        let sample_rust = r#"#![allow(dead_code, non_snake_case, non_upper_case_globals)]

pub fn answer(x: u32) -> u32 {
    x.wrapping_add(41)
}

pub const fn __anodized_fn_qualifiers_answer() -> (&'static str, bool, bool) {
    ("safe", false, false)
}

pub fn __anodized_fn_requires_answer(x: &u32) -> bool {
    *x < 100
}

pub fn __anodized_fn_ensures_answer(old_x: &u32, output: &u32) -> bool {
    *output == old_x.wrapping_add(41)
}

pub const __ANNEAL_EXT_SPEC_TARGET_ext_fn: &str = "core::num::u32::wrapping_add";

pub fn __anodized_fn_requires_ext_fn(_a: &u32, _b: &u32) -> bool {
    true
}

pub const __ANNEAL_MODEL_MyCounter: &str = "MyCounter";

pub fn MyCounter(val: u32) -> bool {
    val <= 1000
}
"#;
        fs::write(&src_path, sample_rust.as_bytes()).expect("write sample rust source");

        let args = vec![
            "anneal-rustc-capture".to_owned(),
            "rustc".to_owned(),
            "--crate-name".to_owned(),
            "demo".to_owned(),
            "--crate-type".to_owned(),
            "lib".to_owned(),
            "--edition=2024".to_owned(),
            "--out-dir".to_owned(),
            out_dir.to_string_lossy().into_owned(),
            src_path.to_string_lossy().into_owned(),
        ];

        let code = run_with_args(&args, Some(capture_dir.clone()), None);
        assert_eq!(
            code, 0,
            "expected run_with_args to succeed with exit code 0"
        );
        verify_captured_demo_artifacts(&capture_dir);

        // If the compiled binary is present alongside the test executable in
        // `target/debug/anneal-rustc-capture`, also exercise it as an external
        // subprocess wrapper.
        if let Ok(test_exe) = std::env::current_exe() {
            if let Some(debug_dir) = test_exe.parent().and_then(|p| p.parent()) {
                let candidate_bin = debug_dir.join("anneal-rustc-capture");
                if candidate_bin.exists() {
                    let sub_capture_dir = temp_root.join("sub_capture");
                    let sub_out_dir = temp_root.join("sub_out");
                    fs::create_dir_all(&sub_capture_dir).expect("create sub_capture dir");
                    fs::create_dir_all(&sub_out_dir).expect("create sub_out dir");

                    let output = Command::new(&candidate_bin)
                        .arg("rustc")
                        .arg("--crate-name")
                        .arg("demo")
                        .arg("--crate-type")
                        .arg("lib")
                        .arg("--edition=2024")
                        .arg("--out-dir")
                        .arg(&sub_out_dir)
                        .arg(&src_path)
                        .env(ANNEAL_CAPTURE_DIR_ENV, &sub_capture_dir)
                        .output()
                        .expect("spawn anneal-rustc-capture subprocess");
                    assert!(
                        output.status.success(),
                        "subprocess failed: {}",
                        String::from_utf8_lossy(&output.stderr)
                    );
                    verify_captured_demo_artifacts(&sub_capture_dir);
                }
            }
        }

        let _ = fs::remove_dir_all(&temp_root);
    }

    #[test]
    fn wrapper_arg_normalization_and_filtering() {
        let wrapped = vec![
            "/path/to/anneal-rustc-capture".to_owned(),
            "/rustup/toolchains/nightly/bin/rustc".to_owned(),
            "--crate-name".to_owned(),
            "my_crate".to_owned(),
            "src/lib.rs".to_owned(),
        ];
        let normalized = normalize_wrapper_args(&wrapped);
        assert_eq!(normalized[0], "/rustup/toolchains/nightly/bin/rustc");
        assert!(should_run_capture_for_args(&normalized));

        let version_query = vec!["rustc".to_owned(), "-vV".to_owned()];
        assert!(!should_run_capture_for_args(&version_query));

        let print_query = vec![
            "rustc".to_owned(),
            "--crate-name".to_owned(),
            "___".to_owned(),
            "--print=file-names".to_owned(),
            "src/lib.rs".to_owned(),
        ];
        assert!(!should_run_capture_for_args(&print_query));

        let build_script = vec![
            "rustc".to_owned(),
            "--crate-name".to_owned(),
            "build_script_build".to_owned(),
            "build.rs".to_owned(),
        ];
        assert!(!should_run_capture_for_args(&build_script));

        let with_meta = vec![
            "rustc".to_owned(),
            "-C".to_owned(),
            "metadata=4f9a1c".to_owned(),
        ];
        assert_eq!(derive_unit_id("demo", &with_meta), "demo-4f9a1c");

        let temp_install = unique_temp_dir("packaged-sysroot");
        let bin_dir = temp_install.join("bin");
        let rustlib_dir = temp_install.join("rust/lib/rustlib");
        fs::create_dir_all(&bin_dir).expect("create packaged bin dir");
        fs::create_dir_all(&rustlib_dir).expect("create packaged rustlib dir");
        let direct_driver = bin_dir.join("anneal-rustc-capture");
        let direct_args = vec![
            direct_driver.to_string_lossy().into_owned(),
            "--crate-name".to_owned(),
            "my_crate".to_owned(),
            "src/lib.rs".to_owned(),
        ];
        let normalized_direct = normalize_wrapper_args(&direct_args);
        let expected_sysroot = temp_install.join("rust").to_string_lossy().into_owned();
        assert!(
            normalized_direct
                .windows(2)
                .any(|w| w[0] == "--sysroot" && w[1] == expected_sysroot),
            "expected packaged sysroot {expected_sysroot} in {normalized_direct:?}"
        );
        let _ = fs::remove_dir_all(&temp_install);

        let valid_os = vec![
            std::ffi::OsString::from("anneal-rustc-capture"),
            std::ffi::OsString::from("--version"),
        ];
        assert_eq!(
            decode_os_args(valid_os).expect("decode valid UTF-8 args"),
            vec!["anneal-rustc-capture".to_owned(), "--version".to_owned()]
        );

        #[cfg(unix)]
        {
            use std::os::unix::ffi::OsStringExt;
            let bad_prog = vec![
                std::ffi::OsString::from_vec(vec![b'a', 0xff]),
                std::ffi::OsString::from("--version"),
            ];
            let prog_err = decode_os_args(bad_prog).expect_err("reject non-UTF-8 program name");
            assert!(prog_err.contains("compiler program name is not UTF-8"));

            let bad_arg = vec![
                std::ffi::OsString::from("anneal-rustc-capture"),
                std::ffi::OsString::from_vec(vec![b'-', 0xfe]),
            ];
            let arg_err = decode_os_args(bad_arg).expect_err("reject non-UTF-8 argument");
            assert!(arg_err.contains("compiler argument is not UTF-8"));
        }
    }

    #[test]
    fn driver_captures_enums_arrays_refs_and_calls_mir_ast() {
        let temp_root = unique_temp_dir("rich-mir");
        let capture_dir = temp_root.join("capture");
        let out_dir = temp_root.join("out");
        fs::create_dir_all(&capture_dir).expect("create capture dir");
        fs::create_dir_all(&out_dir).expect("create out dir");

        let src_path = temp_root.join("rich_lib.rs");
        let sample_rust = r#"#![allow(dead_code, internal_features)]
#![feature(custom_mir, core_intrinsics)]

use core::intrinsics::mir::*;

#[derive(Clone, Copy)]
pub enum Status {
    Ok(u32),
    Err(u32),
}

pub fn eval_status(s: Status, fallback: Option<u32>) -> u32 {
    match s {
        Status::Ok(v) => v,
        Status::Err(e) => match fallback {
            Some(f) => f.wrapping_add(e),
            None => e,
        },
    }
}

pub fn make_status_ok(x: u32) -> Status {
    Status::Ok(x)
}

#[custom_mir(dialect = "runtime", phase = "post-cleanup")]
pub fn set_status_discriminant(s: &mut Status) {
    mir! {
        {
            SetDiscriminant(*s, 1);
            Return()
        }
    }
}

pub fn array_repeat_and_index(v: u32, idx: usize) -> u32 {
    let arr: [u32; 3] = [v; 3];
    arr[idx]
}

pub fn ref_and_deref(mut x: u32) -> u32 {
    let mr: &mut u32 = &mut x;
    *mr = (*mr).wrapping_add(1);
    let sr: &u32 = &x;
    *sr
}

#[inline(never)]
pub fn helper_inc(x: u32) -> u32 {
    x.wrapping_add(1)
}

pub fn caller_invoke(x: u32) -> u32 {
    helper_inc(x)
}
"#;
        fs::write(&src_path, sample_rust.as_bytes()).expect("write rich rust source");

        let args = vec![
            "anneal-rustc-capture".to_owned(),
            "rustc".to_owned(),
            "--crate-name".to_owned(),
            "rich".to_owned(),
            "--crate-type".to_owned(),
            "lib".to_owned(),
            "--edition=2024".to_owned(),
            "--out-dir".to_owned(),
            out_dir.to_string_lossy().into_owned(),
            src_path.to_string_lossy().into_owned(),
        ];

        let code = run_with_args(&args, Some(capture_dir.clone()), None);
        assert_eq!(
            code, 0,
            "expected run_with_args to succeed with exit code 0"
        );

        let manifest_path = capture_dir.join("rich").join("UnitCaptureManifest.json");
        let manifest_json =
            fs::read_to_string(&manifest_path).expect("read UnitCaptureManifest.json");
        let parsed = UnitCaptureManifest::from_json_str(&manifest_json)
            .expect("parse UnitCaptureManifest.json");
        assert!(parsed.compilation_succeeded);

        let read_mir_module = |def_id: &str| -> String {
            let record = parsed
                .unit_targets
                .iter()
                .find(|t| t.target.def_id == def_id)
                .unwrap_or_else(|| panic!("find {def_id} in UnitCaptureManifest"));
            let lean_path = capture_dir
                .join("rich")
                .join(&record.target.mir_module_path);
            let source = fs::read_to_string(&lean_path)
                .unwrap_or_else(|e| panic!("read {}: {e}", lean_path.display()));
            assert_eq!(
                sha256_hex(source.as_bytes()),
                record.target.mir_module_sha256
            );
            source
        };

        // 1. Enums: Option<u32> and Status (Rvalue::Discriminant,
        //    StatementKind::SetDiscriminant, and ProjectionElem::Downcast +
        //    ProjectionElem::Field).
        let eval_status_lean = read_mir_module("rich::eval_status");
        assert!(eval_status_lean.contains("(RigidTy.adt \"rich::Status\" List.nil)"));
        assert!(
            eval_status_lean.contains(
                "(RigidTy.adt \"std::option::Option\" (List.cons (RigidTy.uint UintTy.u32) List.nil))"
            ) || eval_status_lean.contains(
                "(RigidTy.adt \"core::option::Option\" (List.cons (RigidTy.uint UintTy.u32) List.nil))"
            ),
            "eval_status_lean:\n{eval_status_lean}"
        );
        assert!(eval_status_lean.contains("(VariantsShape.multiple"));
        assert!(eval_status_lean.contains("(Rvalue.discriminant"));
        assert!(eval_status_lean.contains("(TerminatorKind.switchInt"));
        assert!(eval_status_lean.contains("(ProjectionElem.downcast (Option.some \"Ok\") 0)"));
        assert!(eval_status_lean.contains("(ProjectionElem.downcast (Option.some \"Err\") 1)"));
        assert!(eval_status_lean.contains("(ProjectionElem.downcast (Option.some \"Some\") 1)"));
        assert!(eval_status_lean.contains("(ProjectionElem.field 0"));

        let make_status_lean = read_mir_module("rich::make_status_ok");
        assert!(
            make_status_lean
                .contains("(Rvalue.aggregate (AggregateKind.adt \"rich::Status\" 0 Option.none)")
        );

        let set_discr_lean = read_mir_module("rich::set_status_discriminant");
        assert!(set_discr_lean.contains(
            "(StatementKind.setDiscriminant { local_ := 1, projection := (List.cons ProjectionElem.deref List.nil) } 1)"
        ));

        // 2. Fixed-size arrays ([u32; 3]), Rvalue::Repeat, and
        //    ProjectionElem::Index.
        let array_lean = read_mir_module("rich::array_repeat_and_index");
        assert!(array_lean.contains("(RigidTy.array (RigidTy.uint UintTy.u32) 3)"));
        assert!(array_lean.contains("(FieldsShape.array { bytes := 4 } 3)"));
        assert!(
            array_lean.contains(
                "(Rvalue.repeat (Operand.copy { local_ := 1, projection := List.nil }) 3)"
            )
        );
        assert!(array_lean.contains("(ProjectionElem.index"));

        // 3. References and dereferences (&u32, &mut u32, *r via Rvalue::Ref
        //    and ProjectionElem::Deref).
        let ref_lean = read_mir_module("rich::ref_and_deref");
        assert!(ref_lean.contains("(RigidTy.ref Mutability.mut (RigidTy.uint UintTy.u32))"));
        assert!(ref_lean.contains("(RigidTy.ref Mutability.not (RigidTy.uint UintTy.u32))"));
        assert!(ref_lean.contains(
            "(Rvalue.ref (BorrowKind.mut false) { local_ := 1, projection := List.nil })"
        ));
        assert!(
            ref_lean
                .contains("(Rvalue.ref BorrowKind.shared { local_ := 1, projection := List.nil })")
        );
        assert!(ref_lean.contains("ProjectionElem.deref"));

        // 4. Function calls (TerminatorKind::Call from a caller function to a
        //    helper function).
        let caller_lean = read_mir_module("rich::caller_invoke");
        assert!(caller_lean.contains("(TerminatorKind.call"));
        assert!(caller_lean.contains("(RigidTy.fnDef \"rich::helper_inc\" List.nil)"));

        let _ = fs::remove_dir_all(&temp_root);
    }

    #[test]
    fn driver_inlines_anodized_closure_wrappers_and_links_local_external_spec() {
        let temp_root = unique_temp_dir("anodized-inline");
        let capture_dir = temp_root.join("capture");
        let out_dir = temp_root.join("out");
        fs::create_dir_all(&capture_dir).expect("create capture dir");
        fs::create_dir_all(&out_dir).expect("create out dir");

        let src_path = temp_root.join("spec_lib.rs");
        let sample_rust = r#"#![allow(dead_code, non_snake_case, non_upper_case_globals)]

pub mod __ {
    pub fn coerce_input<T, F: FnOnce(T) -> bool>(_: F, _: &T) {}
    pub fn eval_once<T, F: FnOnce() -> T>(f: F) -> T {
        f()
    }
    pub fn eval<T, F: Fn() -> T>(f: F) -> T {
        f()
    }
    pub fn apply_keep<T, U, F: Fn(U) -> (T, U)>(f: F, v: U) -> (T, U) {
        f(v)
    }
}

pub fn local_target(x: u32) -> u32 {
    x
}

pub const __ANNEAL_EXT_SPEC_TARGET_local_target_spec: &str = "local_target";

pub fn local_target_spec(_x: u32) -> u32 {
    unreachable!()
}

pub fn __anodized_fn_requires_local_target_spec(x: u32) -> bool {
    let __anodized_check_0: bool = __::eval_once(|| x == 7);
    __anodized_check_0
}

pub fn __anodized_fn_ensures_local_target_spec(x: u32, __anodized_output: u32) -> bool {
    if false {
        __::coerce_input(|ref ret| *ret == x, &__anodized_output);
    }
    let __anodized_post_0: bool = __::eval(|| match __anodized_output {
        ref ret => *ret == x,
    });
    let (__anodized_post_1, __anodized_output): (bool, u32) =
        __::apply_keep(|ret: u32| (ret == 7, ret), __anodized_output);
    let _ = __anodized_output;
    __anodized_post_0 && __anodized_post_1
}
"#;
        fs::write(&src_path, sample_rust.as_bytes()).expect("write spec rust source");

        let args = vec![
            "anneal-rustc-capture".to_owned(),
            "rustc".to_owned(),
            "--crate-name".to_owned(),
            "spec_demo".to_owned(),
            "--crate-type".to_owned(),
            "lib".to_owned(),
            "--edition=2024".to_owned(),
            "--out-dir".to_owned(),
            out_dir.to_string_lossy().into_owned(),
            src_path.to_string_lossy().into_owned(),
        ];

        let code = run_with_args(&args, Some(capture_dir.clone()), None);
        assert_eq!(
            code, 0,
            "expected run_with_args to succeed with exit code 0"
        );

        let manifest_path = capture_dir
            .join("spec_demo")
            .join("UnitCaptureManifest.json");
        let manifest_json =
            fs::read_to_string(&manifest_path).expect("read UnitCaptureManifest.json");
        let parsed = UnitCaptureManifest::from_json_str(&manifest_json)
            .expect("parse UnitCaptureManifest.json");
        assert!(parsed.compilation_succeeded);

        let req_target = parsed
            .unit_targets
            .iter()
            .find(|t| t.target.def_id == "spec_demo::__anodized_fn_requires_local_target_spec")
            .expect("find external spec requires item");
        assert_eq!(req_target.item_kind, CapturedItemKind::InlineSpecRequires);
        assert_eq!(
            req_target.associated_subject_def_id.as_deref(),
            Some("spec_demo::local_target")
        );

        let ens_target = parsed
            .unit_targets
            .iter()
            .find(|t| t.target.def_id == "spec_demo::__anodized_fn_ensures_local_target_spec")
            .expect("find external spec ensures item");
        assert_eq!(ens_target.item_kind, CapturedItemKind::InlineSpecEnsures);
        assert_eq!(
            ens_target.associated_subject_def_id.as_deref(),
            Some("spec_demo::local_target")
        );

        let req_lean = fs::read_to_string(
            capture_dir
                .join("spec_demo")
                .join(&req_target.target.mir_module_path),
        )
        .expect("read requires lean module");
        assert!(!req_lean.contains("TerminatorKind.call"));
        assert!(!req_lean.contains("AggregateKind.closure"));
        assert!(req_lean.contains("BinOp.eq"));

        let ens_lean = fs::read_to_string(
            capture_dir
                .join("spec_demo")
                .join(&ens_target.target.mir_module_path),
        )
        .expect("read ensures lean module");
        assert!(!ens_lean.contains("TerminatorKind.call"));
        assert!(!ens_lean.contains("AggregateKind.closure"));
        assert!(ens_lean.contains("BinOp.eq"));

        let _ = fs::remove_dir_all(&temp_root);
    }

    #[test]
    fn driver_resolves_external_spec_targets_across_local_inherent_and_core_paths() {
        let temp_root = unique_temp_dir("ext-spec-target-resolution");
        let capture_dir = temp_root.join("capture");
        let out_dir = temp_root.join("out");
        fs::create_dir_all(&capture_dir).expect("create capture dir");
        fs::create_dir_all(&out_dir).expect("create out dir");

        let src_path = temp_root.join("ext_spec_lib.rs");
        let sample_rust = r#"#![allow(dead_code, non_snake_case, non_upper_case_globals)]

pub fn local_helper(x: u32) -> u32 {
    x.wrapping_add(1)
}

pub const __ANNEAL_EXT_SPEC_TARGET_ext_local_helper: &str = "crate::local_helper";
pub fn ext_local_helper(x: u32) -> u32 {
    let _: fn(u32) -> u32 = *::core::hint::black_box(&crate::local_helper);
    let _ = (x,);
    unreachable!()
}
pub fn __anodized_fn_requires_ext_local_helper(x: u32) -> bool {
    x < 100
}
pub fn __anodized_fn_ensures_ext_local_helper(x: u32, out: u32) -> bool {
    out == x.wrapping_add(1)
}

pub const __ANNEAL_EXT_SPEC_TARGET_ext_slice_len: &str = "<[u8]>::len";
pub fn ext_slice_len(s: &[u8]) -> usize {
    let _: fn(&[u8]) -> usize = *::core::hint::black_box(&<[u8]>::len);
    let _ = (s,);
    unreachable!()
}

pub const __ANNEAL_EXT_SPEC_TARGET_ext_raw_parts_mut: &str = "std::slice::from_raw_parts_mut";
pub unsafe fn ext_raw_parts_mut<'a>(data: *mut u8, len: usize) -> &'a mut [u8] {
    let _: unsafe fn(*mut u8, usize) -> &'a mut [u8] =
        *::core::hint::black_box(&std::slice::from_raw_parts_mut);
    let _ = (data, len);
    unreachable!()
}

pub trait MyTrait {
    fn trait_op(&self) -> u32;
}

pub struct LocalStruct(pub u32);

impl MyTrait for LocalStruct {
    fn trait_op(&self) -> u32 {
        self.0
    }
}

pub const __ANNEAL_EXT_SPEC_TARGET_ext_trait_impl_op: &str = "<LocalStruct as MyTrait>::trait_op";
pub fn ext_trait_impl_op(s: &LocalStruct) -> u32 {
    let _: fn(&LocalStruct) -> u32 =
        *::core::hint::black_box(&<LocalStruct as MyTrait>::trait_op);
    let _ = (s,);
    unreachable!()
}
"#;
        fs::write(&src_path, sample_rust.as_bytes()).expect("write ext_spec_lib.rs");

        let args = vec![
            "anneal-rustc-capture".to_owned(),
            "rustc".to_owned(),
            "--crate-name".to_owned(),
            "ext_spec_demo".to_owned(),
            "--crate-type".to_owned(),
            "lib".to_owned(),
            "--edition=2024".to_owned(),
            "--out-dir".to_owned(),
            out_dir.to_string_lossy().into_owned(),
            src_path.to_string_lossy().into_owned(),
        ];

        let code = run_with_args(&args, Some(capture_dir.clone()), None);
        assert_eq!(
            code, 0,
            "expected run_with_args to succeed with exit code 0"
        );

        let manifest_path = capture_dir
            .join("ext_spec_demo")
            .join("UnitCaptureManifest.json");
        let manifest_json =
            fs::read_to_string(&manifest_path).expect("read UnitCaptureManifest.json");
        let parsed = UnitCaptureManifest::from_json_str(&manifest_json)
            .expect("parse UnitCaptureManifest.json");
        assert!(parsed.compilation_succeeded);

        let local_ext = parsed
            .unit_targets
            .iter()
            .find(|t| t.target.def_id == "ext_spec_demo::ext_local_helper")
            .expect("find ext_local_helper");
        assert_eq!(local_ext.item_kind, CapturedItemKind::ExternalSpec);
        assert_eq!(
            local_ext.associated_subject_def_id.as_deref(),
            Some("ext_spec_demo::local_helper")
        );

        let local_req = parsed
            .unit_targets
            .iter()
            .find(|t| t.target.def_id == "ext_spec_demo::__anodized_fn_requires_ext_local_helper")
            .expect("find requires companion for ext_local_helper");
        assert_eq!(
            local_req.associated_subject_def_id.as_deref(),
            Some("ext_spec_demo::local_helper")
        );

        let slice_len_ext = parsed
            .unit_targets
            .iter()
            .find(|t| t.target.def_id == "ext_spec_demo::ext_slice_len")
            .expect("find clause-less ext_slice_len");
        assert_eq!(slice_len_ext.item_kind, CapturedItemKind::ExternalSpec);
        assert_eq!(
            slice_len_ext.associated_subject_def_id.as_deref(),
            Some("core::slice::<impl [T]>::len")
        );

        let raw_parts_ext = parsed
            .unit_targets
            .iter()
            .find(|t| t.target.def_id == "ext_spec_demo::ext_raw_parts_mut")
            .expect("find clause-less ext_raw_parts_mut");
        assert_eq!(raw_parts_ext.item_kind, CapturedItemKind::ExternalSpec);
        assert_eq!(
            raw_parts_ext.associated_subject_def_id.as_deref(),
            Some("core::slice::from_raw_parts_mut")
        );

        let trait_impl_ext = parsed
            .unit_targets
            .iter()
            .find(|t| t.target.def_id == "ext_spec_demo::ext_trait_impl_op")
            .expect("find ext_trait_impl_op");
        assert_eq!(trait_impl_ext.item_kind, CapturedItemKind::ExternalSpec);
        assert_eq!(
            trait_impl_ext.associated_subject_def_id.as_deref(),
            Some("ext_spec_demo::<LocalStruct as MyTrait>::trait_op")
        );

        let _ = fs::remove_dir_all(&temp_root);
    }

    #[test]
    fn driver_captures_type_invariant_and_unsafe_impl_targets() {
        let temp_root = unique_temp_dir("invariant-unsafe-impl");
        let capture_dir = temp_root.join("capture");
        let out_dir = temp_root.join("out");
        fs::create_dir_all(&capture_dir).expect("create capture dir");
        fs::create_dir_all(&out_dir).expect("create out dir");

        let src_path = temp_root.join("inv_lib.rs");
        let sample_rust = r#"#![allow(dead_code, non_snake_case)]

pub struct NonZeroCounter(pub u32);

impl NonZeroCounter {
    #[doc(hidden)]
    #[doc = "\u{200b}anneal::type_invariant=NonZeroCounter"]
    pub fn __anneal_type_invariant_non_zero_counter(&self) -> bool {
        self.0 > 0
    }
}

pub unsafe trait TrustedZeroable {}

unsafe impl TrustedZeroable for NonZeroCounter {}

#[doc(hidden)]
#[doc = "\u{200b}anneal::unsafe_impl=TrustedZeroable::NonZeroCounter"]
pub fn __anneal_unsafe_impl_TrustedZeroable_for_NonZeroCounter() -> bool {
    true
}

pub fn __anodized_fn_requires___anneal_unsafe_impl_TrustedZeroable_for_NonZeroCounter() -> bool {
    true
}
"#;
        fs::write(&src_path, sample_rust.as_bytes()).expect("write inv_lib.rs");

        let args = vec![
            "anneal-rustc-capture".to_owned(),
            "rustc".to_owned(),
            "--crate-name".to_owned(),
            "inv_demo".to_owned(),
            "--crate-type".to_owned(),
            "lib".to_owned(),
            "--edition=2024".to_owned(),
            "--out-dir".to_owned(),
            out_dir.to_string_lossy().into_owned(),
            src_path.to_string_lossy().into_owned(),
        ];

        let code = run_with_args(&args, Some(capture_dir.clone()), None);
        assert_eq!(
            code, 0,
            "expected run_with_args to succeed with exit code 0"
        );

        let manifest_path = capture_dir
            .join("inv_demo")
            .join("UnitCaptureManifest.json");
        let manifest_json =
            fs::read_to_string(&manifest_path).expect("read UnitCaptureManifest.json");
        let parsed = UnitCaptureManifest::from_json_str(&manifest_json)
            .expect("parse UnitCaptureManifest.json");
        assert!(parsed.compilation_succeeded);

        let inv_target = parsed
            .unit_targets
            .iter()
            .find(|t| {
                t.target.def_id
                    == "inv_demo::NonZeroCounter::__anneal_type_invariant_non_zero_counter"
            })
            .expect("find type invariant item in UnitCaptureManifest");
        assert_eq!(inv_target.item_kind, CapturedItemKind::TypeInvariant);
        assert_eq!(
            inv_target.associated_subject_def_id.as_deref(),
            Some("inv_demo::NonZeroCounter")
        );

        let unsafe_impl_target = parsed
            .unit_targets
            .iter()
            .find(|t| {
                t.target.def_id
                    == "inv_demo::__anneal_unsafe_impl_TrustedZeroable_for_NonZeroCounter"
            })
            .expect("find unsafe impl witness item in UnitCaptureManifest");
        assert_eq!(
            unsafe_impl_target.item_kind,
            CapturedItemKind::UnsafeTraitImpl
        );
        assert_eq!(
            unsafe_impl_target.associated_subject_def_id.as_deref(),
            Some("TrustedZeroable::NonZeroCounter")
        );

        let unsafe_impl_req = parsed
            .unit_targets
            .iter()
            .find(|t| {
                t.target.def_id
                    == "inv_demo::__anodized_fn_requires___anneal_unsafe_impl_TrustedZeroable_for_NonZeroCounter"
            })
            .expect("find requires companion for unsafe impl witness");
        assert_eq!(
            unsafe_impl_req.item_kind,
            CapturedItemKind::InlineSpecRequires
        );
        assert_eq!(
            unsafe_impl_req.associated_subject_def_id.as_deref(),
            Some("inv_demo::__anneal_unsafe_impl_TrustedZeroable_for_NonZeroCounter")
        );

        let _ = fs::remove_dir_all(&temp_root);
    }

    #[test]
    fn unit_helpers_detect_unnamed_consts_filters_and_collisions() {
        assert!(is_unnamed_const_def_path("_"));
        assert!(is_unnamed_const_def_path("zerocopy::_"));
        assert!(is_unnamed_const_def_path("zerocopy::util::macros::_"));
        assert!(!is_unnamed_const_def_path("zerocopy::NAMED_CONST"));
        assert!(!is_unnamed_const_def_path("zerocopy::__ANNEAL_SPEC_FOO"));
        assert!(!is_unnamed_const_def_path("zerocopy::leading__underscore"));

        assert_eq!(parse_capture_filter(None), Vec::<String>::new());
        assert_eq!(parse_capture_filter(Some(" ,  , ")), Vec::<String>::new());
        assert_eq!(
            parse_capture_filter(Some(" checked_scale , foo::bar , ")),
            vec!["checked_scale".to_owned(), "foo::bar".to_owned()]
        );

        let patterns = parse_capture_filter(Some("checked_scale,special_stem"));
        assert!(matches_capture_filter(
            "demo::ffi::checked_scale",
            "ffi_checked_scale",
            &patterns
        ));
        assert!(matches_capture_filter(
            "demo::unmatched_path",
            "my_special_stem_v1",
            &patterns
        ));
        assert!(!matches_capture_filter(
            "demo::other_fn",
            "other_fn",
            &patterns
        ));
        assert!(matches_capture_filter("demo::anything", "anything", &[]));

        let mut used = std::collections::BTreeSet::new();
        let mut counts = std::collections::BTreeMap::new();
        assert_eq!(
            disambiguate_identifier("Zerocopy_impl_foo", &mut used, &mut counts),
            "Zerocopy_impl_foo"
        );
        assert_eq!(
            disambiguate_identifier("Zerocopy_impl_foo", &mut used, &mut counts),
            "Zerocopy_impl_foo_2"
        );
        assert_eq!(
            disambiguate_identifier("Zerocopy_impl_foo", &mut used, &mut counts),
            "Zerocopy_impl_foo_3"
        );
    }

    #[test]
    fn runtime_checks_fix_ub_checks_true_and_keep_session_flags() {
        use rustc_middle::mir::RuntimeChecks;

        // The verification policy ignores the session for `UbChecks` and
        // defers to it for the other runtime checks.
        assert!(verification_runtime_check_value(
            RuntimeChecks::UbChecks,
            |_| false
        ));
        assert!(!verification_runtime_check_value(
            RuntimeChecks::OverflowChecks,
            |_| false
        ));
        assert!(verification_runtime_check_value(
            RuntimeChecks::OverflowChecks,
            |_| true
        ));
        assert!(!verification_runtime_check_value(
            RuntimeChecks::ContractChecks,
            |_| false
        ));

        // End to end: with debug assertions and overflow checks disabled,
        // `rustc` evaluates both operands to `false`. `-Zmir-opt-level=0` keeps
        // `InstSimplify` from folding the `UbChecks` operand before capture, as
        // `#![rustc_preserve_ub_checks]` does for `core`.
        let temp_root = unique_temp_dir("runtime-checks");
        let capture_dir = temp_root.join("capture");
        let out_dir = temp_root.join("out");
        fs::create_dir_all(&capture_dir).expect("create capture dir");
        fs::create_dir_all(&out_dir).expect("create out dir");

        let src_path = temp_root.join("rt_checks.rs");
        let sample_rust = r#"#![allow(internal_features)]
#![feature(core_intrinsics)]

pub fn ub_checks_flag() -> bool {
    core::intrinsics::ub_checks()
}

pub fn overflow_checks_flag() -> bool {
    core::intrinsics::overflow_checks()
}
"#;
        fs::write(&src_path, sample_rust.as_bytes()).expect("write rt_checks.rs");

        let args = vec![
            "anneal-rustc-capture".to_owned(),
            "rustc".to_owned(),
            "--crate-name".to_owned(),
            "rt_checks".to_owned(),
            "--crate-type".to_owned(),
            "lib".to_owned(),
            "--edition=2024".to_owned(),
            "-Zmir-opt-level=0".to_owned(),
            "-Cdebug-assertions=off".to_owned(),
            "-Coverflow-checks=off".to_owned(),
            "--out-dir".to_owned(),
            out_dir.to_string_lossy().into_owned(),
            src_path.to_string_lossy().into_owned(),
        ];

        let code = run_with_args(&args, Some(capture_dir.clone()), None);
        assert_eq!(
            code, 0,
            "expected run_with_args to succeed with exit code 0"
        );

        let manifest_path = capture_dir
            .join("rt_checks")
            .join("UnitCaptureManifest.json");
        let manifest_json =
            fs::read_to_string(&manifest_path).expect("read UnitCaptureManifest.json");
        let parsed = UnitCaptureManifest::from_json_str(&manifest_json)
            .expect("parse UnitCaptureManifest.json");
        assert!(parsed.compilation_succeeded);

        let read_mir_module = |def_id: &str| -> String {
            let record = parsed
                .unit_targets
                .iter()
                .find(|t| t.target.def_id == def_id)
                .unwrap_or_else(|| panic!("find {def_id} in UnitCaptureManifest"));
            let lean_path = capture_dir
                .join("rt_checks")
                .join(&record.target.mir_module_path);
            fs::read_to_string(&lean_path)
                .unwrap_or_else(|e| panic!("read {}: {e}", lean_path.display()))
        };

        let true_const = "(ConstValue.scalar (ConstScalar.int { bits := 1, sizeBytes := 1 }))";
        let false_const = "(ConstValue.scalar (ConstScalar.int { bits := 0, sizeBytes := 1 }))";

        let ub_lean = read_mir_module("rt_checks::ub_checks_flag");
        assert!(ub_lean.contains(true_const), "ub_checks_flag:\n{ub_lean}");
        assert!(!ub_lean.contains(false_const), "ub_checks_flag:\n{ub_lean}");

        let overflow_lean = read_mir_module("rt_checks::overflow_checks_flag");
        assert!(
            overflow_lean.contains(false_const),
            "overflow_checks_flag:\n{overflow_lean}"
        );
        assert!(
            !overflow_lean.contains(true_const),
            "overflow_checks_flag:\n{overflow_lean}"
        );

        let _ = fs::remove_dir_all(&temp_root);
    }

    #[test]
    fn driver_names_intrinsics_by_defining_path_in_std_crates() {
        // A crate that links `std` sees `core::intrinsics` through the
        // `std::intrinsics` re-export. Intrinsic callees must still be named
        // `core::intrinsics::*`, the paths the MIR semantics recognize, while
        // other re-exported items keep their visible `std::` paths. The
        // assertions inspect `RigidTy.fnDef` terms because the emitted module's
        // `-- bb` comments print rustc's own MIR, which uses visible paths.
        let temp_root = unique_temp_dir("intrinsic-paths");
        let capture_dir = temp_root.join("capture");
        let out_dir = temp_root.join("out");
        fs::create_dir_all(&capture_dir).expect("create capture dir");
        fs::create_dir_all(&out_dir).expect("create out dir");

        let src_path = temp_root.join("ipath.rs");
        let sample_rust = r#"#![allow(internal_features)]
#![feature(core_intrinsics)]

pub fn pop(x: u32) -> u32 {
    core::intrinsics::ctpop(x)
}

pub fn ediv(a: u32, b: u32) -> u32 {
    unsafe { std::intrinsics::exact_div(a, b) }
}

pub fn hint(x: bool) -> u32 {
    if x {
        unsafe { core::hint::unreachable_unchecked() }
    }
    7
}
"#;
        fs::write(&src_path, sample_rust.as_bytes()).expect("write ipath.rs");

        let args = vec![
            "anneal-rustc-capture".to_owned(),
            "rustc".to_owned(),
            "--crate-name".to_owned(),
            "ipath".to_owned(),
            "--crate-type".to_owned(),
            "lib".to_owned(),
            "--edition=2024".to_owned(),
            "-Zmir-opt-level=0".to_owned(),
            "--out-dir".to_owned(),
            out_dir.to_string_lossy().into_owned(),
            src_path.to_string_lossy().into_owned(),
        ];

        let code = run_with_args(&args, Some(capture_dir.clone()), None);
        assert_eq!(
            code, 0,
            "expected run_with_args to succeed with exit code 0"
        );

        let manifest_path = capture_dir.join("ipath").join("UnitCaptureManifest.json");
        let manifest_json =
            fs::read_to_string(&manifest_path).expect("read UnitCaptureManifest.json");
        let parsed = UnitCaptureManifest::from_json_str(&manifest_json)
            .expect("parse UnitCaptureManifest.json");
        assert!(parsed.compilation_succeeded);

        let read_mir_module = |def_id: &str| -> String {
            let record = parsed
                .unit_targets
                .iter()
                .find(|t| t.target.def_id == def_id)
                .unwrap_or_else(|| panic!("find {def_id} in UnitCaptureManifest"));
            let lean_path = capture_dir
                .join("ipath")
                .join(&record.target.mir_module_path);
            fs::read_to_string(&lean_path)
                .unwrap_or_else(|e| panic!("read {}: {e}", lean_path.display()))
        };

        let pop_lean = read_mir_module("ipath::pop");
        assert!(
            pop_lean.contains("(RigidTy.fnDef \"core::intrinsics::ctpop\""),
            "pop:\n{pop_lean}"
        );
        assert!(
            !pop_lean.contains("(RigidTy.fnDef \"std::intrinsics::"),
            "pop:\n{pop_lean}"
        );

        let ediv_lean = read_mir_module("ipath::ediv");
        assert!(
            ediv_lean.contains("(RigidTy.fnDef \"core::intrinsics::exact_div\""),
            "ediv:\n{ediv_lean}"
        );
        assert!(
            !ediv_lean.contains("(RigidTy.fnDef \"std::intrinsics::"),
            "ediv:\n{ediv_lean}"
        );

        let hint_lean = read_mir_module("ipath::hint");
        assert!(
            hint_lean.contains("(RigidTy.fnDef \"core::hint::unreachable_unchecked\""),
            "hint:\n{hint_lean}"
        );

        let _ = fs::remove_dir_all(&temp_root);
    }

    #[test]
    fn driver_skips_anonymous_consts_disambiguates_collisions_and_applies_filter() {
        use std::collections::BTreeSet;

        let temp_root = unique_temp_dir("large-crate-filter");
        let capture_all_dir = temp_root.join("capture_all");
        let capture_filtered_dir = temp_root.join("capture_filtered");
        let out_dir = temp_root.join("out");
        fs::create_dir_all(&capture_all_dir).expect("create capture_all dir");
        fs::create_dir_all(&capture_filtered_dir).expect("create capture_filtered dir");
        fs::create_dir_all(&out_dir).expect("create out dir");

        let src_path = temp_root.join("large_crate_lib.rs");
        // This fixture exercises all three large-crate features:
        // 1. Multiple `const _: () = ...` static assertions (must be skipped)
        //    alongside a named `pub const NAMED_LIMIT: u32` (must be kept).
        // 2. Items that produce identical sanitized item stems (`pub mod a {
        //    pub fn b() }` vs `pub fn a_b()`, plus two generic `impl` blocks
        //    defining methods with identical sanitized stems) so collision
        //    disambiguation (`_2`, `_3`) is exercised.
        // 3. A filtered target (`keep_target`) with `anodized`-style companion
        //    functions (`__anodized_fn_requires_keep_target` and
        //    `__anodized_fn_ensures_keep_target`) and an unrelated function
        //    (`unselected_helper`) that `ANNEAL_CAPTURE_FILTER=keep_target`
        //    must exclude.
        let sample_rust = r#"#![allow(dead_code, non_snake_case)]

const _: () = {
    assert!(1 + 1 == 2);
};

pub mod nested {
    const _: usize = 0;
}

pub const NAMED_LIMIT: u32 = 100;

pub mod dup {
    pub fn item(x: u32) -> u32 {
        x
    }
}

pub fn dup_item(x: u32) -> u32 {
    x.wrapping_add(1)
}

pub fn outer_scope() -> u32 {
    fn inner_helper() -> u32 {
        10
    }
    let first = inner_helper();
    {
        fn inner_helper() -> u32 {
            20
        }
        first + inner_helper()
    }
}

pub fn keep_target(x: u32) -> u32 {
    x
}

pub fn __anodized_fn_requires_keep_target(x: u32) -> bool {
    x < NAMED_LIMIT
}

pub fn __anodized_fn_ensures_keep_target(x: u32, output: u32) -> bool {
    output == x
}

pub fn unselected_helper(y: u32) -> u32 {
    y
}
"#;
        fs::write(&src_path, sample_rust.as_bytes()).expect("write large_crate_lib.rs");

        let args = vec![
            "anneal-rustc-capture".to_owned(),
            "rustc".to_owned(),
            "--crate-name".to_owned(),
            "large_demo".to_owned(),
            "--crate-type".to_owned(),
            "lib".to_owned(),
            "--edition=2024".to_owned(),
            "--out-dir".to_owned(),
            out_dir.to_string_lossy().into_owned(),
            src_path.to_string_lossy().into_owned(),
        ];

        // 1. Unfiltered capture: verify anonymous const skipping and collision
        // disambiguation.
        let code_all = run_with_args_and_filter(&args, Some(capture_all_dir.clone()), None, None);
        assert_eq!(code_all, 0, "unfiltered capture must succeed");

        let all_manifest_path = capture_all_dir
            .join("large_demo")
            .join("UnitCaptureManifest.json");
        let all_manifest_json =
            fs::read_to_string(&all_manifest_path).expect("read unfiltered manifest");
        let all_parsed = UnitCaptureManifest::from_json_str(&all_manifest_json)
            .expect("parse unfiltered manifest");
        assert!(all_parsed.compilation_succeeded);

        // No anonymous `const _` items may appear in `unit_targets`.
        for rec in &all_parsed.unit_targets {
            assert!(
                !rec.target.def_id.ends_with("::_") && rec.target.def_id != "_",
                "anonymous const should have been skipped, found {}",
                rec.target.def_id
            );
        }

        // Named constant `NAMED_LIMIT` must still be captured.
        assert!(
            all_parsed
                .unit_targets
                .iter()
                .any(|t| t.target.def_id == "large_demo::NAMED_LIMIT"),
            "expected named constant large_demo::NAMED_LIMIT to be captured"
        );

        // Every emitted `def_id`, `lean_module_name`, and `mir_module_path`
        // must be unique across `unit_targets`, with `_2` disambiguating the
        // colliding stems.
        let mut seen_def_ids = BTreeSet::new();
        let mut seen_lean_modules = BTreeSet::new();
        let mut seen_mir_paths = BTreeSet::new();
        for rec in &all_parsed.unit_targets {
            assert!(
                seen_def_ids.insert(rec.target.def_id.clone()),
                "duplicate def_id in UnitCaptureManifest: {}",
                rec.target.def_id
            );
            assert!(
                seen_lean_modules.insert(rec.lean_module_name.clone()),
                "duplicate lean_module_name in UnitCaptureManifest: {}",
                rec.lean_module_name
            );
            assert!(
                seen_mir_paths.insert(rec.target.mir_module_path.clone()),
                "duplicate mir_module_path in UnitCaptureManifest: {}",
                rec.target.mir_module_path
            );
        }
        assert!(
            seen_lean_modules.contains("Mir.LargeDemo.dup_item")
                && seen_lean_modules.contains("Mir.LargeDemo.dup_item_2"),
            "expected colliding dup::item and dup_item stems to disambiguate with _2: {seen_lean_modules:?}"
        );
        assert!(
            seen_def_ids.contains("large_demo::outer_scope::inner_helper")
                && seen_def_ids.contains("large_demo::outer_scope::inner_helper_2"),
            "expected colliding inner_helper def_ids to disambiguate with _2: {seen_def_ids:?}"
        );
        assert!(
            seen_lean_modules.contains("Mir.LargeDemo.outer_scope_inner_helper")
                && seen_lean_modules.contains("Mir.LargeDemo.outer_scope_inner_helper_2"),
            "expected colliding inner_helper stems to disambiguate with _2: {seen_lean_modules:?}"
        );

        // 2. Filtered capture (`keep_target`): verify that only `keep_target`
        // and its associated companion specs are emitted.
        let code_filtered = run_with_args_and_filter(
            &args,
            Some(capture_filtered_dir.clone()),
            None,
            Some("keep_target".to_owned()),
        );
        assert_eq!(code_filtered, 0, "filtered capture must succeed");

        let filtered_manifest_path = capture_filtered_dir
            .join("large_demo")
            .join("UnitCaptureManifest.json");
        let filtered_manifest_json =
            fs::read_to_string(&filtered_manifest_path).expect("read filtered manifest");
        let filtered_parsed = UnitCaptureManifest::from_json_str(&filtered_manifest_json)
            .expect("parse filtered manifest");
        assert!(filtered_parsed.compilation_succeeded);

        let filtered_def_ids: Vec<&str> = filtered_parsed
            .unit_targets
            .iter()
            .map(|t| t.target.def_id.as_str())
            .collect();
        assert_eq!(
            filtered_def_ids,
            vec![
                "large_demo::__anodized_fn_ensures_keep_target",
                "large_demo::__anodized_fn_requires_keep_target",
                "large_demo::keep_target",
            ],
            "expected ANNEAL_CAPTURE_FILTER={} to keep only keep_target and its spec companions",
            ANNEAL_CAPTURE_FILTER_ENV
        );

        let _ = fs::remove_dir_all(&temp_root);
    }

    #[test]
    fn driver_captures_generic_functions_and_trait_impls() {
        use std::process::Command;

        let temp_root = unique_temp_dir("generics-traits");
        let capture_dir = temp_root.join("capture");
        let out_dir = temp_root.join("out");
        fs::create_dir_all(&capture_dir).expect("create capture dir");
        fs::create_dir_all(&out_dir).expect("create out dir");

        let src_path = temp_root.join("demo_generics.rs");
        let sample_rust = r#"#![allow(dead_code, non_snake_case, non_upper_case_globals)]

#[derive(Copy, Clone)]
pub struct Wrapper<T>(pub T);

#[derive(Copy, Clone)]
pub struct Pair<A, B>(pub A, pub B);

#[derive(Copy, Clone)]
pub struct PairWithHeader<T> {
    pub header: u64,
    pub payload: T,
}

pub fn swap_pair<'a, T: Copy, U: Copy>(_tag: &'a u32, a: T, b: U) -> (U, T) {
    (b, a)
}

pub fn wrap_array<T: Copy>(x: T) -> [T; 2] {
    [x, x]
}

pub fn wrap_opt<T: Copy>(x: T) -> Option<T> {
    Some(x)
}

pub fn make_header_pair<T: Copy>(header: u64, payload: T) -> PairWithHeader<T> {
    PairWithHeader { header, payload }
}

impl<T: Copy> Pair<T, TypeA> {
    pub fn first(self) -> T {
        self.0
    }
}

impl<T: Copy> Pair<T, TypeB> {
    pub fn first(self) -> T {
        self.0
    }
}

impl<T: Copy> Pair<T, T> {
    pub fn diag_first(self) -> T {
        self.0
    }
}

impl<T: Copy> Wrapper<T> {
    pub fn get(self) -> T {
        self.0
    }

    pub fn pair_with<U: Copy>(self, u: U) -> (T, U) {
        (self.0, u)
    }
}

impl Wrapper<u32> {
    pub fn spec_tag(self) -> u32 {
        self.0
    }
}

impl Wrapper<u64> {
    pub fn spec_tag(self) -> u32 {
        self.0 as u32
    }
}

pub trait MyTrait {
    type Assoc;
    fn method(&self) -> Self::Assoc;
}

pub struct TypeA;
pub struct TypeB;

impl MyTrait for TypeA {
    type Assoc = u32;
    fn method(&self) -> u32 {
        1
    }
}

impl MyTrait for TypeB {
    type Assoc = u64;
    fn method(&self) -> u64 {
        2
    }
}

impl<T: Copy> MyTrait for Wrapper<T> {
    type Assoc = T;
    fn method(&self) -> T {
        self.0
    }
}

pub fn normalized_assoc(a: &TypeA) -> <TypeA as MyTrait>::Assoc {
    a.method()
}

pub fn unnormalized_assoc<T: MyTrait>(x: &T) -> <T as MyTrait>::Assoc {
    x.method()
}

pub mod inner {
    #[derive(Copy, Clone)]
    pub struct GenericBox<T>(pub T);

    impl<T: Copy> GenericBox<T> {
        #[doc = "\u{200b}anneal::type_invariant=GenericBox"]
        pub fn __anneal_type_invariant_generic_box(&self) -> bool {
            true
        }

        pub fn unbox(self) -> T {
            self.0
        }

        pub fn __anodized_fn_requires_unbox(self) -> bool {
            true
        }
    }

    impl GenericBox<u32> {
        pub fn unbox_u32(self) -> u32 {
            self.0
        }
    }
}
"#;
        fs::write(&src_path, sample_rust.as_bytes()).expect("write sample rust source");

        let args = vec![
            "anneal-rustc-capture".to_owned(),
            "rustc".to_owned(),
            "--crate-name".to_owned(),
            "demo_generics".to_owned(),
            "--crate-type".to_owned(),
            "lib".to_owned(),
            "--edition=2024".to_owned(),
            "--out-dir".to_owned(),
            out_dir.to_string_lossy().into_owned(),
            src_path.to_string_lossy().into_owned(),
        ];

        let code = run_with_args(&args, Some(capture_dir.clone()), None);
        assert_eq!(
            code, 0,
            "expected run_with_args to succeed with exit code 0"
        );

        let crate_capture_dir = capture_dir.join("demo_generics");
        let manifest_path = crate_capture_dir.join("UnitCaptureManifest.json");
        let manifest_content = fs::read_to_string(&manifest_path).unwrap();
        let manifest: crate::manifest::UnitCaptureManifest =
            crate::manifest::UnitCaptureManifest::from_json_str(&manifest_content).unwrap();
        assert!(manifest.compilation_succeeded);

        let find_target = |def_id: &str| {
            manifest
                .unit_targets
                .iter()
                .find(|t| t.target.def_id == def_id)
                .unwrap_or_else(|| {
                    panic!(
                        "missing target {def_id}; available: {:?}",
                        manifest
                            .unit_targets
                            .iter()
                            .map(|t| &t.target.def_id)
                            .collect::<Vec<_>>()
                    )
                })
        };

        // 1. Free generic function with lifetime `'a` + type params `T, U`:
        // lifetime must be erased and type params must have dense 0-based indices 0 and 1.
        let swap_pair = find_target("demo_generics::swap_pair");
        assert!(swap_pair.trait_impls.is_empty());
        let swap_lean =
            fs::read_to_string(crate_capture_dir.join(&swap_pair.target.mir_module_path)).unwrap();
        assert!(swap_lean.contains("typeParamCount := 2"));
        assert!(swap_lean.contains(
            "genericParams := (List.cons { idx := 0, name := \"T\" } (List.cons { idx := 1, name := \"U\" } List.nil))"
        ));
        assert!(swap_lean.contains("(RigidTy.param 0 \"T\")"));
        assert!(swap_lean.contains("(RigidTy.param 1 \"U\")"));
        assert!(swap_lean.contains("fieldLayouts := (List.cons 1 (List.cons 0 List.nil))"));

        // 2. Generic inherent impl methods (`get` with 1 parent param, `pair_with` with 1 parent + 1 own param)
        // and specialized inherent impl methods (`Wrapper<u32>::spec_tag` vs `Wrapper<u64>::spec_tag`).
        let wrapper_get = find_target("demo_generics::Wrapper::<T>::get");
        let wrapper_pair_with = find_target("demo_generics::Wrapper::<T>::pair_with");
        let spec_u32 = find_target("demo_generics::<Wrapper<u32>>::spec_tag");
        let spec_u64 = find_target("demo_generics::<Wrapper<u64>>::spec_tag");
        let pair_type_a = find_target("demo_generics::<Pair<T, TypeA>>::first");
        let pair_type_b = find_target("demo_generics::<Pair<T, TypeB>>::first");
        let pair_diagonal = find_target("demo_generics::<Pair<T, T>>::diag_first");
        assert_eq!(
            wrapper_get.lean_module_name,
            "Mir.DemoGenerics.Wrapper_T_get"
        );
        assert_eq!(
            wrapper_pair_with.lean_module_name,
            "Mir.DemoGenerics.Wrapper_T_pair_with"
        );
        assert_eq!(
            spec_u32.lean_module_name,
            "Mir.DemoGenerics.Wrapper_u32_spec_tag"
        );
        assert_eq!(
            spec_u64.lean_module_name,
            "Mir.DemoGenerics.Wrapper_u64_spec_tag"
        );
        assert_eq!(
            pair_type_a.lean_module_name,
            "Mir.DemoGenerics.Pair_T_TypeA_first"
        );
        assert_eq!(
            pair_type_b.lean_module_name,
            "Mir.DemoGenerics.Pair_T_TypeB_first"
        );
        assert_eq!(
            pair_diagonal.lean_module_name,
            "Mir.DemoGenerics.Pair_T_T_diag_first"
        );

        let pair_with_lean =
            fs::read_to_string(crate_capture_dir.join(&wrapper_pair_with.target.mir_module_path))
                .unwrap();
        assert!(pair_with_lean.contains("typeParamCount := 2"));
        assert!(pair_with_lean.contains(
            "genericParams := (List.cons { idx := 0, name := \"T\" } (List.cons { idx := 1, name := \"U\" } List.nil))"
        ));

        // 3. Multiple trait impls (`TypeA`, `TypeB`, and generic `Wrapper<T>`) must have distinct
        // canonical paths, distinct Lean module names, and populated `trait_impls`.
        let a_method = find_target("demo_generics::<TypeA as MyTrait>::method");
        let b_method = find_target("demo_generics::<TypeB as MyTrait>::method");
        let w_method = find_target("demo_generics::<Wrapper<T> as MyTrait>::method");
        assert_eq!(
            a_method.lean_module_name,
            "Mir.DemoGenerics.TypeA_as_MyTrait_method"
        );
        assert_eq!(
            b_method.lean_module_name,
            "Mir.DemoGenerics.TypeB_as_MyTrait_method"
        );
        assert_eq!(
            w_method.lean_module_name,
            "Mir.DemoGenerics.Wrapper_T_as_MyTrait_method"
        );

        assert_eq!(a_method.trait_impls.len(), 1);
        assert_eq!(
            a_method.trait_impls[0].trait_method_def_path,
            "demo_generics::MyTrait::method"
        );
        assert_eq!(a_method.trait_impls[0].impl_path, a_method.target.def_id);
        assert_eq!(
            a_method.trait_impls[0].trait_args_lean,
            vec!["(RigidTy.adt \"demo_generics::TypeA\" List.nil)"]
        );

        assert_eq!(b_method.trait_impls.len(), 1);
        assert_eq!(
            b_method.trait_impls[0].trait_method_def_path,
            "demo_generics::MyTrait::method"
        );
        assert_eq!(b_method.trait_impls[0].impl_path, b_method.target.def_id);
        assert_eq!(
            b_method.trait_impls[0].trait_args_lean,
            vec!["(RigidTy.adt \"demo_generics::TypeB\" List.nil)"]
        );

        assert_eq!(w_method.trait_impls.len(), 1);
        assert_eq!(
            w_method.trait_impls[0].trait_method_def_path,
            "demo_generics::MyTrait::method"
        );
        assert_eq!(w_method.trait_impls[0].impl_path, w_method.target.def_id);
        assert_eq!(
            w_method.trait_impls[0].trait_args_lean,
            vec![
                "(RigidTy.adt \"demo_generics::Wrapper\" (List.cons (RigidTy.param 0 \"T\") List.nil))"
            ]
        );

        // 4. `TyKind::Alias` normalization (`<TypeA as MyTrait>::Assoc` -> `u32`) and unnormalized
        // projection fallback (`<T as MyTrait>::Assoc` -> `RigidTy.alias "demo_generics::MyTrait::Assoc" [.param 0 "T"]`).
        let norm_assoc = find_target("demo_generics::normalized_assoc");
        let norm_lean =
            fs::read_to_string(crate_capture_dir.join(&norm_assoc.target.mir_module_path)).unwrap();
        assert!(
            !norm_lean.contains("RigidTy.alias"),
            "concrete associated type <TypeA as MyTrait>::Assoc must normalize to u32"
        );
        assert!(norm_lean.contains("(RigidTy.uint UintTy.u32)"));

        let unnorm_assoc = find_target("demo_generics::unnormalized_assoc");
        let unnorm_lean =
            fs::read_to_string(crate_capture_dir.join(&unnorm_assoc.target.mir_module_path))
                .unwrap();
        assert!(unnorm_lean.contains(
            "(RigidTy.alias \"demo_generics::MyTrait::Assoc\" (List.cons (RigidTy.param 0 \"T\") List.nil))"
        ));

        // 5. Generic type invariant and inline spec companion resolution inside `inner::GenericBox<T>`.
        let generic_box_inv = find_target(
            "demo_generics::inner::GenericBox::<T>::__anneal_type_invariant_generic_box",
        );
        assert_eq!(
            generic_box_inv.item_kind,
            crate::manifest::CapturedItemKind::TypeInvariant
        );
        assert_eq!(
            generic_box_inv.associated_subject_def_id.as_deref(),
            Some("demo_generics::inner::GenericBox")
        );

        let generic_box_req =
            find_target("demo_generics::inner::GenericBox::<T>::__anodized_fn_requires_unbox");
        assert_eq!(
            generic_box_req.item_kind,
            crate::manifest::CapturedItemKind::InlineSpecRequires
        );
        assert_eq!(
            generic_box_req.associated_subject_def_id.as_deref(),
            Some("demo_generics::inner::GenericBox::<T>::unbox")
        );

        // 5. End-to-end Lean 4 kernel typechecking of emitted polymorphic modules and
        // `CapturedMir.instantiate` reduction theorems.
        let repo_root = Path::new(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .and_then(Path::parent)
            .expect("repo root");
        let examples_dir = repo_root.join("examples");
        let lean_lib_dir = examples_dir.join(".lake/build/lib/lean");
        let resolve_bin = |name: &str| -> PathBuf {
            if let Ok(home) = std::env::var("HOME") {
                let elan_bin = PathBuf::from(home).join(".elan/bin").join(name);
                if elan_bin.exists() {
                    return elan_bin;
                }
            }
            PathBuf::from(name)
        };
        if !lean_lib_dir.join("Trusted.olean").exists() {
            let status = Command::new(resolve_bin("lake"))
                .args(["--dir", examples_dir.to_str().unwrap(), "build", "Trusted"])
                .status()
                .expect("invoke lake build Trusted");
            assert!(status.success(), "lake build Trusted must succeed");
        }

        let lean_bin = resolve_bin("lean");
        std::fs::copy(
            examples_dir.join("lean-toolchain"),
            crate_capture_dir.join("lean-toolchain"),
        )
        .ok();
        let lean_path_env = format!("{}:{}", lean_lib_dir.display(), crate_capture_dir.display());
        let verified_modules = [
            "Mir/DemoGenerics/swap_pair.lean",
            "Mir/DemoGenerics/wrap_array.lean",
            "Mir/DemoGenerics/wrap_opt.lean",
            "Mir/DemoGenerics/make_header_pair.lean",
            "Mir/DemoGenerics/Wrapper_T_pair_with.lean",
            "Mir/DemoGenerics/Wrapper_T_as_MyTrait_method.lean",
            "Mir/DemoGenerics/unnormalized_assoc.lean",
        ];
        for rel_path in verified_modules {
            let src_lean = crate_capture_dir.join(rel_path);
            let dst_olean = src_lean.with_extension("olean");
            let out = Command::new(&lean_bin)
                .current_dir(&crate_capture_dir)
                .env("LEAN_PATH", &lean_path_env)
                .arg("-R")
                .arg(&crate_capture_dir)
                .arg("-o")
                .arg(&dst_olean)
                .arg(&src_lean)
                .output()
                .expect("compile emitted Mir module with lean");
            assert!(
                out.status.success(),
                "lean failed on {}:\nstdout: {}\nstderr: {}",
                src_lean.display(),
                String::from_utf8_lossy(&out.stdout),
                String::from_utf8_lossy(&out.stderr)
            );
        }

        let verify_lean_path = crate_capture_dir.join("VerifyPolymorphicCapture.lean");
        let verify_lean_src = r#"import Trusted
import Mir.DemoGenerics.swap_pair
import Mir.DemoGenerics.wrap_array
import Mir.DemoGenerics.wrap_opt
import Mir.DemoGenerics.make_header_pair
import Mir.DemoGenerics.Wrapper_T_pair_with
import Mir.DemoGenerics.Wrapper_T_as_MyTrait_method
import Mir.DemoGenerics.unnormalized_assoc

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst

def u32Layout : TypeLayout :=
  { size := { bytes := 4 }
    align := { bytes := 4 }
    backendRepr := .scalar (.initialized (.int 32 false) { start := 0, end_ := 4294967295 })
    fields := .primitive
    variants := .single 0
    isUninhabited := false }

def u64Layout : TypeLayout :=
  { size := { bytes := 8 }
    align := { bytes := 8 }
    backendRepr := .scalar (.initialized (.int 64 false) { start := 0, end_ := 18446744073709551615 })
    fields := .primitive
    variants := .single 0
    isUninhabited := false }

def substU32U64 : TypeSubst :=
  [(.uint .u32, u32Layout), (.uint .u64, u64Layout)]

def substU32 : TypeSubst :=
  [(.uint .u32, u32Layout)]

-- 1. Well-formedness preservation and parameter count reduction under instantiation
example : (Mir.DemoGenerics.swap_pair.body.instantiate substU32U64).wellFormed =
    Mir.DemoGenerics.swap_pair.body.wellFormed := rfl
example : (Mir.DemoGenerics.swap_pair.body.instantiate substU32U64).typeParamCount = 0 := rfl
example : (Mir.DemoGenerics.swap_pair.body.instantiate substU32U64).genericParams = [] := rfl

-- 2. Return local `_0 : (U, T)` of `swap_pair` instantiates to `(u64, u32)` with size 16, align 8
example :
    ((get? (Mir.DemoGenerics.swap_pair.body.instantiate substU32U64).localDecls 0).map (fun d => d.ty.kind)) =
      .some (.tuple [.uint .u64, .uint .u32]) := rfl
example :
    (Mir.DemoGenerics.swap_pair.body.instantiate substU32U64).fnAbi.ret.layout.size = { bytes := 16 } := rfl
example :
    (Mir.DemoGenerics.swap_pair.body.instantiate substU32U64).fnAbi.ret.layout.align = { bytes := 8 } := rfl

-- 3. `Wrapper<T>::pair_with<U>` instantiates both parent param `T` (idx 0) and method param `U` (idx 1)
example :
    ((get? (Mir.DemoGenerics.Wrapper_T_pair_with.body.instantiate substU32U64).localDecls 0).map (fun d => d.ty.kind)) =
      .some (.tuple [.uint .u32, .uint .u64]) := rfl
example :
    ((get? (Mir.DemoGenerics.Wrapper_T_pair_with.body.instantiate substU32U64).localDecls 1).map (fun d => d.ty.kind)) =
      .some (.adt "demo_generics::Wrapper" [.uint .u32]) := rfl

-- 4. `wrap_array<T>`, `wrap_opt<T>`, and `make_header_pair<T>` recompute `[u32; 2]` (8B, align 4),
--    `Option<u32>` (8B, align 4), and `PairWithHeader<u32>` (16B, align 8)
example :
    (Mir.DemoGenerics.wrap_array.body.instantiate substU32).fnAbi.ret.layout.size = { bytes := 8 } := rfl
example :
    (Mir.DemoGenerics.wrap_array.body.instantiate substU32).fnAbi.ret.layout.align = { bytes := 4 } := rfl
example :
    (Mir.DemoGenerics.wrap_opt.body.instantiate substU32).fnAbi.ret.layout.size = { bytes := 8 } := rfl
example :
    (Mir.DemoGenerics.wrap_opt.body.instantiate substU32).fnAbi.ret.layout.align = { bytes := 4 } := rfl
example :
    (Mir.DemoGenerics.make_header_pair.body.instantiate substU32).fnAbi.ret.layout.size = { bytes := 16 } := rfl
example :
    (Mir.DemoGenerics.make_header_pair.body.instantiate substU32).fnAbi.ret.layout.align = { bytes := 8 } := rfl

-- 5. Generic trait impl `<Wrapper<T> as MyTrait>::method` instantiates `traitImpls`
example :
    (Mir.DemoGenerics.Wrapper_T_as_MyTrait_method.body.instantiate substU32).traitImpls =
      [{ traitRef :=
           { defPath := "demo_generics::MyTrait::method"
             args := [.adt "demo_generics::Wrapper" [.uint .u32]] }
         implPath := "demo_generics::<Wrapper<T> as MyTrait>::method" }] := rfl
"#;
        fs::write(&verify_lean_path, verify_lean_src.as_bytes())
            .expect("write VerifyPolymorphicCapture.lean");
        let verify_out = Command::new(&lean_bin)
            .current_dir(&crate_capture_dir)
            .env("LEAN_PATH", &lean_path_env)
            .arg(&verify_lean_path)
            .output()
            .expect("run lean kernel verification on instantiated polymorphic MIR");
        assert!(
            verify_out.status.success(),
            "Lean kernel verification failed:\nstdout: {}\nstderr: {}",
            String::from_utf8_lossy(&verify_out.stdout),
            String::from_utf8_lossy(&verify_out.stderr)
        );

        let _ = fs::remove_dir_all(&temp_root);
    }

    #[test]
    fn driver_captures_sysroot_core_slice_and_range_bounds_mir() {
        let nanos = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let temp_root = std::env::temp_dir().join(format!(
            "anneal-rustc-capture-sysroot-test-{}-{nanos}",
            std::process::id()
        ));
        let capture_dir = temp_root.join("units");
        fs::create_dir_all(&temp_root).expect("create temp test dir");

        let src_path = temp_root.join("sysroot_lib.rs");
        let rust_source = r#"#![no_std]

use core::ops::{Range, RangeBounds};

pub fn slice_len_and_ptr<T>(s: &[T]) -> (usize, *const T) {
    let len_fn: fn(&[T]) -> usize = <[T]>::len;
    (len_fn(s), s.as_ptr())
}

pub unsafe fn rebuild_and_split<T>(ptr: *mut T, len: usize, mid: usize) -> (*mut [T], *mut [T]) {
    let whole: &mut [T] = unsafe { core::slice::from_raw_parts_mut(ptr, len) };
    let (left, right) = whole.split_at_mut(mid);
    (left as *mut [T], right as *mut [T])
}

pub fn check_range_contains(r: &Range<usize>, idx: &usize) -> bool {
    const OPTION_IS_SOME_FN: fn(&Option<usize>) -> bool = Option::<usize>::is_some;
    let opt = Some(*idx);
    let fallback = opt.unwrap_or_else(usize::default);
    OPTION_IS_SOME_FN(&Some(fallback)) && RangeBounds::contains(r, idx)
}
"#;
        fs::write(&src_path, rust_source.as_bytes()).expect("write sysroot_lib.rs");

        let args = vec![
            String::from("rustc"),
            String::from("--crate-name"),
            String::from("demo_sysroot"),
            String::from("--crate-type"),
            String::from("lib"),
            String::from("--edition=2024"),
            String::from("-C"),
            String::from("metadata=sysroot01"),
            String::from("--out-dir"),
            temp_root.to_string_lossy().into_owned(),
            src_path.to_string_lossy().into_owned(),
        ];

        let exit_code = run_with_args(&args, Some(capture_dir.clone()), None);
        assert_eq!(exit_code, 0, "rustc_driver capture run must succeed");

        let unit_dir = capture_dir.join("demo_sysroot-sysroot01");
        let manifest_path = unit_dir.join("UnitCaptureManifest.json");
        let manifest_str =
            fs::read_to_string(&manifest_path).expect("read UnitCaptureManifest.json");
        let manifest =
            UnitCaptureManifest::from_json_str(&manifest_str).expect("parse UnitCaptureManifest");
        assert!(manifest.compilation_succeeded);

        // 1. Verify primary crate subjects are captured as `Subject`.
        for expected_subj in [
            "demo_sysroot::slice_len_and_ptr",
            "demo_sysroot::rebuild_and_split",
            "demo_sysroot::check_range_contains",
        ] {
            let rec = manifest
                .unit_targets
                .iter()
                .find(|t| t.target.def_id == expected_subj)
                .unwrap_or_else(|| panic!("missing subject target {expected_subj}"));
            assert_eq!(rec.item_kind, CapturedItemKind::Subject);
        }

        // 2. Verify reachable sysroot (`core`) MIR bodies are extracted from `.rmeta`
        // into `Mir/Core/*.lean` with `CapturedItemKind::Callee` and polymorphic
        // `genericParams`.
        let core_targets: Vec<&crate::manifest::UnitTargetRecord> = manifest
            .unit_targets
            .iter()
            .filter(|t| t.lean_module_name.starts_with("Mir.Core."))
            .collect();
        assert!(
            !core_targets.is_empty(),
            "expected Mir.Core.* targets extracted from sysroot .rmeta"
        );
        for ct in &core_targets {
            assert_eq!(
                ct.item_kind,
                CapturedItemKind::Callee,
                "sysroot target {} must have Callee item_kind",
                ct.target.def_id
            );
            assert!(
                ct.target.mir_module_path.starts_with("Mir/Core/"),
                "unexpected mir_module_path: {}",
                ct.target.mir_module_path
            );
        }

        let core_def_ids: Vec<&str> = core_targets
            .iter()
            .map(|t| t.target.def_id.as_str())
            .collect();
        for required_sub in [
            "len",
            "as_ptr",
            "from_raw_parts_mut",
            "split_at_mut",
            "contains",
            "start_bound",
            "end_bound",
            "is_some",
            "unwrap_or_else",
            "default",
        ] {
            assert!(
                core_def_ids.iter().any(|id| id.contains(required_sub)),
                "expected sysroot core targets to include `{required_sub}`, got: {core_def_ids:?}"
            );
        }

        // Check that polymorphic sysroot bodies preserve genericParams and real CFG blocks.
        let len_rec = core_targets
            .iter()
            .find(|t| t.target.def_id.ends_with("::len"))
            .expect("find <[T]>::len in core_targets");
        let len_lean = fs::read_to_string(unit_dir.join(&len_rec.target.mir_module_path))
            .expect("read len.lean");
        assert!(
            len_lean.contains("genericParams := (List.cons { idx := 0, name := \"T\" } List.nil)"),
            "<[T]>::len must preserve polymorphic genericParams:\n{len_lean}"
        );
        assert!(
            len_lean.contains("phase := MirPhaseTag.runtimeOptimized"),
            "<[T]>::len from .rmeta must record MirPhaseTag.runtimeOptimized phase:\n{len_lean}"
        );

        // 3. Verify that every emitted Mir/DemoSysroot/*.lean and Mir/Core/*.lean module
        // typechecks cleanly in the Lean 4 kernel!
        let repo_root = Path::new(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .and_then(Path::parent)
            .expect("repo root");
        let examples_dir = repo_root.join("examples");
        let lean_lib_dir = examples_dir.join(".lake/build/lib/lean");
        let resolve_bin = |name: &str| -> PathBuf {
            if let Ok(home) = std::env::var("HOME") {
                let elan_bin = PathBuf::from(home).join(".elan/bin").join(name);
                if elan_bin.exists() {
                    return elan_bin;
                }
            }
            PathBuf::from(name)
        };
        if !lean_lib_dir.join("Trusted.olean").exists() {
            let status = Command::new(resolve_bin("lake"))
                .args(["--dir", examples_dir.to_str().unwrap(), "build", "Trusted"])
                .status()
                .expect("invoke lake build Trusted");
            assert!(status.success(), "lake build Trusted must succeed");
        }

        let lean_bin = resolve_bin("lean");
        std::fs::copy(
            examples_dir.join("lean-toolchain"),
            unit_dir.join("lean-toolchain"),
        )
        .ok();
        let lean_path_env = format!("{}:{}", lean_lib_dir.display(), unit_dir.display());
        for target_rec in &manifest.unit_targets {
            let src_lean = unit_dir.join(&target_rec.target.mir_module_path);
            let dst_olean = src_lean.with_extension("olean");
            let out = Command::new(&lean_bin)
                .current_dir(&unit_dir)
                .env("LEAN_PATH", &lean_path_env)
                .arg("-R")
                .arg(&unit_dir)
                .arg("-o")
                .arg(&dst_olean)
                .arg(&src_lean)
                .output()
                .expect("compile emitted Mir module with lean");
            assert!(
                out.status.success(),
                "lean failed on {} ({}):\nstdout: {}\nstderr: {}",
                target_rec.target.def_id,
                src_lean.display(),
                String::from_utf8_lossy(&out.stdout),
                String::from_utf8_lossy(&out.stderr)
            );
        }

        let _ = fs::remove_dir_all(&temp_root);
    }
}
