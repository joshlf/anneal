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
    (MIR_DIALECT_V2026_06_01, RUSTC_VERSION_STRING, RUSTC_COMMIT_SHA)
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
        derive_unit_id, disambiguate_identifier, matches_capture_filter, normalize_wrapper_args,
        parse_capture_filter, run_with_args, run_with_args_and_filter,
        should_run_capture_for_args,
    };
    use crate::rustc_2026_06_01::mir_lower::is_unnamed_const_def_path;

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
        assert_eq!(code, 0, "expected run_with_args to succeed with exit code 0");
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
        assert_eq!(code, 0, "expected run_with_args to succeed with exit code 0");

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
        assert!(make_status_lean.contains(
            "(Rvalue.aggregate (AggregateKind.adt \"rich::Status\" 0 Option.none)"
        ));

        let set_discr_lean = read_mir_module("rich::set_status_discriminant");
        assert!(set_discr_lean.contains(
            "(StatementKind.setDiscriminant { local_ := 1, projection := (List.cons ProjectionElem.deref List.nil) } 1)"
        ));

        // 2. Fixed-size arrays ([u32; 3]), Rvalue::Repeat, and
        //    ProjectionElem::Index.
        let array_lean = read_mir_module("rich::array_repeat_and_index");
        assert!(array_lean.contains("(RigidTy.array (RigidTy.uint UintTy.u32) 3)"));
        assert!(array_lean.contains("(FieldsShape.array { bytes := 4 } 3)"));
        assert!(array_lean.contains(
            "(Rvalue.repeat (Operand.copy { local_ := 1, projection := List.nil }) 3)"
        ));
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
            ref_lean.contains(
                "(Rvalue.ref BorrowKind.shared { local_ := 1, projection := List.nil })"
            )
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
        assert_eq!(code, 0, "expected run_with_args to succeed with exit code 0");

        let manifest_path = capture_dir.join("spec_demo").join("UnitCaptureManifest.json");
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
        assert_eq!(code, 0, "expected run_with_args to succeed with exit code 0");

        let manifest_path = capture_dir.join("inv_demo").join("UnitCaptureManifest.json");
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
        let code_all =
            run_with_args_and_filter(&args, Some(capture_all_dir.clone()), None, None);
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
}
