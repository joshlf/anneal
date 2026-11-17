//! End-to-end Rust-to-Python fault-site coverage parity tests (`Episode 2`).
//!
//! Verifies 1-to-1 agreement between:
//! 1. Rust `cargo_anneal::fault_census::census_lean_mir_module`,
//! 2. Lean 4 `Anneal.FaultSiteCensus.censusMirBodyFaultSites` witness definitions in
//!    `theory/Anneal/FaultSiteCensus.lean`, and
//! 3. Pure-Python `census_lean_mir_module` & `--audit-fault-coverage` in
//!    `trusted/audit/check_trusted.py`
//! across diverse emitted MIR bodies, real `rustc`-captured crates, and fail-closed
//! negative mutations (`FaultCensus/*.json`, `Mir/*.lean`, `Obligations/*.lean`, and
//! `PropertyRegistry`).

use std::env;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::{SystemTime, UNIX_EPOCH};

use anneal_rustc_capture::lean_emit::{
    IrAbiPassMode, IrAggregateKind, IrAlign, IrArgAbi, IrBackendRepr, IrBasicBlockData, IrBinOp,
    IrBorrowKind, IrCallConv, IrCapturedMir, IrCastKind, IrConstOperand, IrConstScalar,
    IrConstValue, IrContractRole, IrFieldsShape, IrFnAbi, IrIntTy, IrLayoutTable, IrLocalDecl,
    IrMirPhaseTag, IrMutability, IrNonDivergingIntrinsic, IrNullOp, IrOperand, IrPlace,
    IrPrimitiveKind, IrProjectionElem, IrProvenancePtr, IrRetagKind, IrRigidTy, IrRvalue,
    IrScalarInt, IrScalarLayout, IrSize, IrStatement, IrStatementKind, IrSwitchTargets,
    IrTerminator, IrTerminatorKind, IrTy, IrTypeLayout, IrUintTy, IrUnOp, IrUnwindAction,
    IrVariantsShape, IrWrappingRange, emit_mir_lean_module,
};
use cargo_anneal::fault_census::{
    FaultSite, MirFaultClass, census_ir_captured_mir, census_lean_mir_module,
};
use cargo_anneal::{
    CaptureDriverConfig, ScaffoldConfig, VerificationStatus, VerifyConfig, run_cargo_capture,
    scaffold_workspace_with_config, verify_workspace_with_config,
};

fn unique_temp_dir(label: &str) -> PathBuf {
    let nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("system clock after epoch")
        .as_nanos();
    let dir = env::temp_dir().join(format!(
        "cargo-anneal-py-parity-{}-{}-{}",
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
    if default_bin.is_file() {
        return default_bin;
    }

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

struct ParityRng(u64);

impl ParityRng {
    fn next_u64(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x >> 12;
        x ^= x << 25;
        x ^= x >> 27;
        self.0 = x;
        x.wrapping_mul(0x2545_F491_4F6C_DD1D)
    }

    fn below(&mut self, n: usize) -> usize {
        (self.next_u64() % (n as u64)) as usize
    }

    fn chance(&mut self, percent: u64) -> bool {
        self.next_u64() % 100 < percent
    }

    fn pick<'a>(&mut self, items: &'a [&'a str]) -> &'a str {
        items[self.below(items.len())]
    }
}

const CALLEE_POOL: [&str; 12] = [
    "core::intrinsics::unreachable",
    "core::hint::unreachable_unchecked",
    "core::intrinsics::exact_div",
    "core::intrinsics::unchecked_add",
    "core::intrinsics::unchecked_shl",
    "core::intrinsics::ctlz_nonzero",
    "core::intrinsics::arith_offset",
    "core::intrinsics::const_eval_select",
    "core::intrinsics::size_of_val",
    "core::intrinsics::wrapping_add",
    "core::panicking::panic",
    "std::intrinsics::unchecked_add",
];

const COERCION_POOL: [&str; 5] = [
    "Unsize",
    "ArrayToPointer",
    "MutToConstPointer",
    "ReifyFnPointer",
    "ClosureFnPointer(Safe)",
];

fn random_ty(rng: &mut ParityRng) -> IrTy {
    let kind = match rng.below(5) {
        0 => IrRigidTy::Bool,
        1 => IrRigidTy::Uint(IrUintTy::U32),
        2 => IrRigidTy::Int(IrIntTy::I32),
        3 => IrRigidTy::Ref(IrMutability::Mut, Box::new(IrRigidTy::Uint(IrUintTy::U32))),
        _ => IrRigidTy::RawPtr(IrMutability::Not, Box::new(IrRigidTy::Uint(IrUintTy::U32))),
    };
    IrTy {
        kind,
        layout_idx: 0,
    }
}

fn random_place(rng: &mut ParityRng) -> IrPlace {
    let mut projection = Vec::new();
    for _ in 0..rng.below(4) {
        projection.push(match rng.below(8) {
            0 => IrProjectionElem::Deref,
            1 => IrProjectionElem::Field(rng.below(3), random_ty(rng)),
            2 => IrProjectionElem::Index(rng.below(3)),
            3 => IrProjectionElem::ConstantIndex {
                offset: rng.below(4) as u64,
                min_length: 4,
                from_end: rng.chance(50),
            },
            4 => IrProjectionElem::Subslice {
                from_idx: 0,
                to_idx: 2,
                from_end: rng.chance(50),
            },
            5 => IrProjectionElem::Downcast(Some("Variant".to_string()), rng.below(2)),
            6 => IrProjectionElem::OpaqueCast(random_ty(rng)),
            _ => IrProjectionElem::UnwrapUnsafeBinder(random_ty(rng)),
        });
    }
    IrPlace {
        local_: rng.below(4),
        projection,
    }
}

fn random_operand(rng: &mut ParityRng) -> IrOperand {
    match rng.below(4) {
        0 => IrOperand::Copy(random_place(rng)),
        1 => IrOperand::Move(random_place(rng)),
        2 => IrOperand::Constant(IrConstOperand {
            ty: IrTy {
                kind: IrRigidTy::FnDef(rng.pick(&CALLEE_POOL).to_string(), Vec::new()),
                layout_idx: 0,
            },
            val: IrConstValue::ZeroSized,
        }),
        _ => {
            let val = match rng.below(4) {
                0 => IrConstValue::ZeroSized,
                1 => IrConstValue::Scalar(IrConstScalar::Int(IrScalarInt {
                    bits: rng.below(100) as u128,
                    size_bytes: 4,
                })),
                2 => IrConstValue::Indirect {
                    alloc_id: 0,
                    offset_bytes: 0,
                },
                _ => IrConstValue::Slice {
                    data: IrConstScalar::Ptr(
                        IrProvenancePtr {
                            alloc_id: 0,
                            offset_bytes: 0,
                        },
                        8,
                    ),
                    meta: 2,
                },
            };
            IrOperand::Constant(IrConstOperand {
                ty: random_ty(rng),
                val,
            })
        }
    }
}

fn random_rvalue(rng: &mut ParityRng) -> IrRvalue {
    const BIN_OPS: [IrBinOp; 10] = [
        IrBinOp::Add,
        IrBinOp::AddUnchecked,
        IrBinOp::SubUnchecked,
        IrBinOp::MulWithOverflow,
        IrBinOp::Div,
        IrBinOp::Rem,
        IrBinOp::Shl,
        IrBinOp::ShlUnchecked,
        IrBinOp::Eq,
        IrBinOp::Offset,
    ];
    match rng.below(14) {
        0 => IrRvalue::Use(random_operand(rng)),
        1 => IrRvalue::Repeat(random_operand(rng), 2),
        2 => IrRvalue::Ref(
            if rng.chance(50) {
                IrBorrowKind::Shared
            } else {
                IrBorrowKind::Mut {
                    allow_two_phase: false,
                }
            },
            random_place(rng),
        ),
        3 => IrRvalue::ThreadLocalRef("tls::VAR".to_string()),
        4 => IrRvalue::RawPtr(
            if rng.chance(50) {
                IrMutability::Not
            } else {
                IrMutability::Mut
            },
            random_place(rng),
        ),
        5 => IrRvalue::Len(random_place(rng)),
        6 => {
            let ck = match rng.below(10) {
                0 => IrCastKind::PointerExposeProvenance,
                1 => IrCastKind::PointerWithExposedProvenance,
                2 => IrCastKind::PointerCoercion(rng.pick(&COERCION_POOL).to_string()),
                3 => IrCastKind::IntToInt,
                4 => IrCastKind::FloatToInt,
                5 => IrCastKind::FloatToFloat,
                6 => IrCastKind::IntToFloat,
                7 => IrCastKind::PtrToPtr,
                8 => IrCastKind::FnPtrToPtr,
                _ => IrCastKind::Transmute,
            };
            IrRvalue::Cast(ck, random_operand(rng), random_ty(rng))
        }
        7 => IrRvalue::BinaryOp(
            BIN_OPS[rng.below(BIN_OPS.len())],
            random_operand(rng),
            random_operand(rng),
        ),
        8 => IrRvalue::NullaryOp(IrNullOp::SizeOf, random_ty(rng)),
        9 => {
            let uop = match rng.below(3) {
                0 => IrUnOp::Not,
                1 => IrUnOp::Neg,
                _ => IrUnOp::PtrMetadata,
            };
            IrRvalue::UnaryOp(uop, random_operand(rng))
        }
        10 => IrRvalue::Discriminant(random_place(rng)),
        11 => {
            let ak = match rng.below(5) {
                0 => IrAggregateKind::Tuple,
                1 => IrAggregateKind::Adt(
                    "demo::UnionOrStruct".to_string(),
                    0,
                    if rng.chance(50) { Some(0) } else { None },
                ),
                2 => IrAggregateKind::RawPtr(random_ty(rng), IrMutability::Mut),
                3 => IrAggregateKind::Coroutine("demo::coro".to_string()),
                _ => IrAggregateKind::Array(random_ty(rng)),
            };
            IrRvalue::Aggregate(ak, vec![random_operand(rng)])
        }
        12 => IrRvalue::CopyForDeref(random_place(rng)),
        _ => IrRvalue::WrapUnsafeBinder(random_operand(rng), random_ty(rng)),
    }
}

fn random_captured_mir(rng: &mut ParityRng, case_idx: usize) -> IrCapturedMir {
    let num_bbs = 1 + rng.below(3);
    let mut basic_blocks = Vec::with_capacity(num_bbs);
    for _ in 0..num_bbs {
        let num_stmts = rng.below(4);
        let mut statements = Vec::with_capacity(num_stmts);
        for _ in 0..num_stmts {
            let kind = match rng.below(10) {
                0 => IrStatementKind::Assign(random_place(rng), random_rvalue(rng)),
                1 => IrStatementKind::SetDiscriminant(random_place(rng), rng.below(2)),
                2 => IrStatementKind::Deinit(random_place(rng)),
                3 => IrStatementKind::StorageLive(rng.below(4)),
                4 => IrStatementKind::StorageDead(rng.below(4)),
                5 => IrStatementKind::Retag(IrRetagKind::Default, random_place(rng)),
                6 => IrStatementKind::PlaceMention(random_place(rng)),
                7 => IrStatementKind::Intrinsic(IrNonDivergingIntrinsic::Assume(random_operand(
                    rng,
                ))),
                8 => IrStatementKind::Intrinsic(IrNonDivergingIntrinsic::CopyNonOverlapping {
                    src: random_operand(rng),
                    dst: random_operand(rng),
                    count: random_operand(rng),
                }),
                _ => IrStatementKind::Nop,
            };
            statements.push(IrStatement {
                kind,
                span: "src/lib.rs:10:5".to_string(),
                comment: None,
            });
        }
        let target_bb = rng.below(num_bbs + 1);
        let unwind = match rng.below(4) {
            0 => IrUnwindAction::Continue,
            1 => IrUnwindAction::Unreachable,
            2 => IrUnwindAction::Terminate,
            _ => IrUnwindAction::Cleanup(rng.below(num_bbs)),
        };
        let term_kind = match rng.below(8) {
            0 => IrTerminatorKind::Goto(target_bb),
            1 => IrTerminatorKind::SwitchInt(
                random_operand(rng),
                IrSwitchTargets {
                    branches: vec![(0, rng.below(num_bbs))],
                    otherwise: target_bb,
                },
            ),
            2 => IrTerminatorKind::Return,
            3 => IrTerminatorKind::Unreachable,
            4 => IrTerminatorKind::Drop {
                place: random_place(rng),
                target: target_bb,
                unwind,
            },
            5 => IrTerminatorKind::Call {
                func: random_operand(rng),
                args: vec![random_operand(rng)],
                destination: random_place(rng),
                target: if rng.chance(70) {
                    Some(rng.below(num_bbs))
                } else {
                    None
                },
                unwind,
            },
            6 => IrTerminatorKind::TailCall {
                func: random_operand(rng),
                args: vec![random_operand(rng)],
            },
            _ => IrTerminatorKind::Assert {
                cond: random_operand(rng),
                expected: true,
                target: target_bb,
                unwind,
            },
        };
        basic_blocks.push(IrBasicBlockData {
            statements,
            terminator: IrTerminator {
                kind: term_kind,
                span: "src/lib.rs:20:5".to_string(),
                comment: None,
            },
            is_cleanup: false,
        });
    }
    let u32_layout = IrTypeLayout {
        size: IrSize { bytes: 4 },
        align: IrAlign { bytes: 4 },
        backend_repr: IrBackendRepr::Scalar(IrScalarLayout::Initialized {
            value: IrPrimitiveKind::Int {
                bits: 32,
                signed: false,
            },
            valid_range: IrWrappingRange {
                start: 0,
                end_: u32::MAX as u128,
            },
        }),
        fields: IrFieldsShape::Primitive,
        variants: IrVariantsShape::Single { index: 0 },
        is_uninhabited: false,
        field_layouts: Vec::new(),
    };
    IrCapturedMir {
        def_path: format!("parity::case_{case_idx}"),
        phase: IrMirPhaseTag::RuntimePostCleanup,
        role: IrContractRole::Subject,
        arg_count: 1,
        local_decls: vec![
            IrLocalDecl {
                mutability: IrMutability::Mut,
                ty: IrTy {
                    kind: IrRigidTy::Uint(IrUintTy::U32),
                    layout_idx: 0,
                },
                debug_name: Some("_0".to_string()),
            };
            4
        ],
        basic_blocks,
        fn_abi: IrFnAbi {
            args: Vec::new(),
            ret: IrArgAbi {
                layout: u32_layout.clone(),
                mode: IrAbiPassMode::Direct,
            },
            conv: IrCallConv::Rust,
            can_unwind: true,
        },
        layouts: IrLayoutTable {
            pointer_bits: 64,
            is_little_endian: true,
            entries: vec![u32_layout],
        },
        allocations: Vec::new(),
        type_param_count: 0,
        generic_params: Vec::new(),
        trait_impls: Vec::new(),
    }
}

#[test]
fn python_census_and_audit_fault_coverage_match_rust_and_lean_end_to_end() {
    let checkout_root = anneal_checkout_root();
    let check_trusted_py = checkout_root.join("trusted/audit/check_trusted.py");

    // 1. Differential parity across 200 randomized emitted `Mir/<Item>.lean` modules
    //    between Rust `census_lean_mir_module`, Rust `census_ir_captured_mir`, and
    //    Python `check_trusted.py::census_lean_mir_module` & `emit_mir_obligation_fault_sites`.
    let diff_dir = unique_temp_dir("diff-200");
    let mut rng = ParityRng(0xE2_FA01_7C0D_E123);
    let mut cases_json = Vec::new();
    for idx in 0..200 {
        let ir = random_captured_mir(&mut rng, idx);
        let ir_sites = census_ir_captured_mir(&ir);
        let lean_src = emit_mir_lean_module(&format!("Mir.Parity.case_{idx}"), &ir);
        let rust_sites = census_lean_mir_module(&lean_src).expect("Rust strict census");
        assert_eq!(ir_sites, rust_sites, "Rust IR vs Lean-text census mismatch on case {idx}");
        let mir_file = diff_dir.join(format!("case_{idx}.lean"));
        fs::write(&mir_file, &lean_src).expect("write Mir case");
        let expected_tuples: Vec<(usize, usize, &str)> = rust_sites
            .iter()
            .map(|s: &FaultSite| (s.block_idx, s.stmt_idx, s.fault_class.as_str()))
            .collect();
        cases_json.push((mir_file.to_string_lossy().to_string(), expected_tuples));
    }

    let manifest_cases_path = diff_dir.join("cases.json");
    let mut json_buf = String::from("[\n");
    for (i, (path_str, sites)) in cases_json.iter().enumerate() {
        let sites_str: Vec<String> = sites
            .iter()
            .map(|(b, s, c)| format!("[{b}, {s}, \"{c}\"]"))
            .collect();
        json_buf.push_str(&format!(
            "  {{\"path\": \"{}\", \"sites\": [{}]}}{}\n",
            path_str.replace('\\', "\\\\").replace('"', "\\\""),
            sites_str.join(", "),
            if i + 1 < cases_json.len() { "," } else { "" }
        ));
    }
    json_buf.push_str("]\n");
    fs::write(&manifest_cases_path, &json_buf).expect("write cases.json");

    let py_script = format!(
        r#"
import importlib.util, json
from pathlib import Path

repo = Path({repo:?})
spec = importlib.util.spec_from_file_location("ct", repo / "trusted/audit/check_trusted.py")
ct = importlib.util.module_from_spec(spec)
spec.loader.exec_module(ct)

# Verify 12 MirFaultClass rank/string parity with Rust
expected_classes = {classes:?}
assert list(ct.MIR_FAULT_CLASSES) == expected_classes

# Verify cross-language pins against Terminators.lean and theory/Anneal/FaultSiteCensus.lean
pins = ct.check_fault_census_source_pins(repo)
assert pins == {{"terminators": True, "faultSiteCensus": True}}, pins

# Verify 4+2 false-proof mutation probes
probes = ct.run_false_proof_mutation_probes()
assert probes["faultClasses"] == 12
assert len(probes["probesPassed"]) == 6

# Verify 100% agreement across all 200 randomized Mir modules
cases = json.loads(Path({cases_path:?}).read_text())
for idx, entry in enumerate(cases):
    src = Path(entry["path"]).read_text()
    py_sites = [[s.block_idx, s.stmt_idx, s.fault_class] for s in ct.census_lean_mir_module(src)]
    assert py_sites == entry["sites"], f"case {{idx}} mismatch: py={{py_sites}} vs rust={{entry['sites']}}"
    body = ct.parse_lean_mir_module_body_strict(src)
    ob_sites = [[s.block_idx, s.stmt_idx, s.fault_class] for s in ct.emit_mir_obligation_fault_sites(body)]
    assert ob_sites == entry["sites"], f"case {{idx}} ob emitter mismatch"
print("PYTHON_200_CASES_PARITY_OK")
"#,
        repo = checkout_root.to_string_lossy(),
        classes = MirFaultClass::ALL.map(|c| c.as_str()),
        cases_path = manifest_cases_path.to_string_lossy(),
    );
    let out = Command::new("python3")
        .arg("-B")
        .arg("-c")
        .arg(&py_script)
        .output()
        .expect("run Python differential parity check");
    assert!(
        out.status.success()
            && String::from_utf8_lossy(&out.stdout).contains("PYTHON_200_CASES_OK".replace("200_CASES_OK", "200_CASES_PARITY_OK").as_str()),
        "Python differential parity failed:\nstdout: {}\nstderr: {}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
    let _ = fs::remove_dir_all(&diff_dir);

    // 2. Real `rustc`-captured crate: run `cargo anneal` capture, scaffold, and verify,
    //    then run `python3 -B trusted/audit/check_trusted.py --audit-fault-coverage <crate>`
    //    and verify positive pass + fail-closed rejection on mutations!
    let wrapper_bin = ensure_rustc_capture_binary(&checkout_root);
    let temp_crate = unique_temp_dir("verified-crate");
    let src_dir = temp_crate.join("src");
    fs::create_dir_all(&src_dir).expect("create src/");

    let anneal_spec_dir = checkout_root.join("crates/anneal-spec");
    let cargo_toml = format!(
        r#"[package]
name = "parity_pkg"
version = "0.1.0"
edition = "2024"
publish = false

[dependencies]
anneal-spec = {{ path = "{}" }}
"#,
        anneal_spec_dir.display()
    );
    fs::write(temp_crate.join("Cargo.toml"), cargo_toml).expect("write Cargo.toml");
    let lib_rs = r#"#![allow(dead_code)]
use anneal_spec::*;

#[anneal_spec::spec(requires: x == 7, ensures: |ref ret| *ret == 7)]
pub fn passthrough_bounded(x: u32) -> u32 {
    x
}
"#;
    fs::write(src_dir.join("lib.rs"), lib_rs).expect("write src/lib.rs");

    let mut driver_cfg = CaptureDriverConfig::new(&temp_crate);
    driver_cfg.rustc_wrapper = Some(wrapper_bin);
    let (_manifest, records) = run_cargo_capture(&driver_cfg).expect("run_cargo_capture");
    let scaffold_cfg = ScaffoldConfig {
        workspace_root: temp_crate.clone(),
        units_dir: Some(driver_cfg.units_dir.clone()),
        anneal_repo_root: Some(checkout_root.clone()),
        init_spec_templates: false,
        init_proof_templates: false,
    };
    let scaffold_rep =
        scaffold_workspace_with_config(&scaffold_cfg, &records).expect("scaffold_workspace_with_config");
    assert!(
        !scaffold_rep.generated_fault_census_files.is_empty(),
        "expected FaultCensus/*.json receipts to be generated"
    );

    let verify_cfg = VerifyConfig::new(&temp_crate);
    let verify_rep = verify_workspace_with_config(&verify_cfg).expect("verify_workspace");
    assert_eq!(verify_rep.items.len(), 1);
    assert_eq!(
        verify_rep.items[0].status,
        VerificationStatus::VerifiedUnconditional
    );

    // Invoke `python3 -B trusted/audit/check_trusted.py --audit-fault-coverage <temp_crate>`
    let audit_ok = Command::new("python3")
        .arg("-B")
        .arg(&check_trusted_py)
        .arg("--audit-fault-coverage")
        .arg(&temp_crate)
        .output()
        .expect("invoke check_trusted.py --audit-fault-coverage");
    assert!(
        audit_ok.status.success()
            && String::from_utf8_lossy(&audit_ok.stdout).contains("PASS: fault-site coverage audit"),
        "expected --audit-fault-coverage to succeed on verified crate:\nstdout: {}\nstderr: {}",
        String::from_utf8_lossy(&audit_ok.stdout),
        String::from_utf8_lossy(&audit_ok.stderr)
    );

    // 3. Negative mutations on the real captured crate must fail closed in
    //    `check_trusted.py --audit-fault-coverage`:
    let receipt_path = &scaffold_rep.generated_fault_census_files[0];
    let original_receipt = fs::read_to_string(receipt_path).expect("read receipt");

    // 3a. Dropping a discharged site in `FaultCensus/<Item>.json` fails closed.
    let stripped_discharged = original_receipt.replacen(
        "\"discharged_sites\": [",
        "\"discharged_sites\": [], \"_unused\": [",
        1,
    );
    // Test both schema rejection and empty discharged_sites rejection:
    let empty_discharged = {
        let start = original_receipt
            .find("\"discharged_sites\": [")
            .expect("discharged_sites start");
        let after = &original_receipt[start..];
        let close = after.find("],\n  \"callee_closure\"").expect("discharged_sites close") + start;
        format!(
            "{}\"discharged_sites\": []{}",
            &original_receipt[..start],
            &original_receipt[close + 1..]
        )
    };
    fs::write(receipt_path, &empty_discharged).expect("write empty discharged_sites receipt");
    let audit_missing = Command::new("python3")
        .arg("-B")
        .arg(&check_trusted_py)
        .arg("--audit-fault-coverage")
        .arg(&temp_crate)
        .output()
        .expect("invoke check_trusted.py on empty discharged_sites");
    assert!(
        !audit_missing.status.success()
            && String::from_utf8_lossy(&audit_missing.stderr).contains("Trusted check failed (fault-coverage)"),
        "expected empty discharged_sites to fail closed:\nstderr: {}",
        String::from_utf8_lossy(&audit_missing.stderr)
    );

    // 3b. Extra/unknown schema key in `FaultCensus/<Item>.json` fails closed.
    fs::write(receipt_path, &stripped_discharged).expect("write malformed schema receipt");
    let audit_schema = Command::new("python3")
        .arg("-B")
        .arg(&check_trusted_py)
        .arg("--audit-fault-coverage")
        .arg(&temp_crate)
        .output()
        .expect("invoke check_trusted.py on bad schema");
    assert!(!audit_schema.status.success());

    // Restore receipt, then mutate `Mir/<Item>.lean` and verify SHA-256 / census drift fails closed.
    fs::write(receipt_path, &original_receipt).expect("restore receipt");
    let mir_path = temp_crate.join(".anneal/generated/Mir/ParityPkg/passthrough_bounded.lean");
    let original_mir = fs::read_to_string(&mir_path).expect("read Mir");
    fs::write(&mir_path, format!("{original_mir}\n-- tampered\n")).expect("tamper Mir");
    let audit_tampered_mir = Command::new("python3")
        .arg("-B")
        .arg(&check_trusted_py)
        .arg("--audit-fault-coverage")
        .arg(&temp_crate)
        .output()
        .expect("invoke check_trusted.py on tampered Mir");
    assert!(
        !audit_tampered_mir.status.success()
            && String::from_utf8_lossy(&audit_tampered_mir.stderr).contains("SHA-256 mismatch"),
        "expected tampered Mir to fail closed on SHA-256 mismatch:\nstderr: {}",
        String::from_utf8_lossy(&audit_tampered_mir.stderr)
    );

    // Restore Mir and confirm `--audit-fault-coverage` passes again.
    fs::write(&mir_path, &original_mir).expect("restore Mir");
    let audit_restored = Command::new("python3")
        .arg("-B")
        .arg(&check_trusted_py)
        .arg("--audit-fault-coverage")
        .arg(&temp_crate)
        .output()
        .expect("invoke check_trusted.py after restore");
    assert!(audit_restored.status.success());

    let _ = fs::remove_dir_all(&temp_crate);
}
