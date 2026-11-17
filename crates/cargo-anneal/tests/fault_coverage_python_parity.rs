//! End-to-end Rust-to-Python fault-site coverage parity tests (`Episode 2`).
//!
//! Verifies 1-to-1 agreement between:
//! 1. Rust `cargo_anneal::fault_census::census_lean_mir_module` (and its IR twin
//!    `census_ir_captured_mir`), `direct_callee_def_paths`, `reified_fn_def_paths`, and
//!    `reconcile_multi_item_coverage`,
//! 2. Lean 4 `Anneal.FaultSiteCensus.censusMirBodyFaultSites` witness definitions in
//!    `theory/Anneal/FaultSiteCensus.lean` (via the Python source pins), and
//! 3. Pure-Python `census_lean_mir_module`, `emit_mir_obligation_fault_sites`,
//!    `reconcile_multi_item_coverage` & `--audit-fault-coverage` in
//!    `trusted/audit/check_trusted.py`
//! across an exhaustive IR-variant sweep plus randomized emitted MIR bodies (including
//! strict-parser rejections, which must be rejected by both sides), real `rustc`-captured
//! crates (single-crate verified, and a scaffold-only multi-crate workspace with real
//! inline callees, modular external-spec contracts and a `spec(trusted)` subject), and
//! fail-closed negative mutations (`FaultCensus/*.json` sites and callee closures,
//! `Mir/*.lean`, `Obligations/*.lean`, `Verify/*.lean`).

use std::collections::BTreeSet;
use std::env;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::time::{SystemTime, UNIX_EPOCH};

use anneal_rustc_capture::lean_emit::{
    IrAbiPassMode, IrAggregateKind, IrAlign, IrArgAbi, IrBackendRepr, IrBasicBlockData, IrBinOp,
    IrBorrowKind, IrCallConv, IrCapturedMir, IrCastKind, IrConstOperand, IrConstScalar,
    IrConstValue, IrContractRole, IrFieldsShape, IrFloatTy, IrFnAbi, IrIntTy, IrLayoutTable,
    IrLocalDecl, IrMirPhaseTag, IrMutability, IrNonDivergingIntrinsic, IrNullOp, IrOperand,
    IrPlace, IrPrimitiveKind, IrProjectionElem, IrProvenancePtr, IrRetagKind, IrRigidTy, IrRvalue,
    IrSafety, IrScalarInt, IrScalarLayout, IrSize, IrStatement, IrStatementKind, IrSwitchTargets,
    IrTerminator, IrTerminatorKind, IrTy, IrTypeLayout, IrUintTy, IrUnOp, IrUnwindAction,
    IrVariantsShape, IrWrappingRange, emit_mir_lean_module,
};
use cargo_anneal::fault_census::{
    CalleeClosure, FaultSite, ItemCoverageInput, MirFaultClass, MultiItemCoverageVerdict,
    PropertyRegistry, census_ir_captured_mir, census_lean_mir_module, census_mir_fault_sites,
    direct_callee_def_paths, parse_lean_mir_module_body_strict, reconcile_multi_item_coverage,
    reified_fn_def_paths,
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

const CALLEE_POOL: [&str; 15] = [
    "core::intrinsics::unreachable",
    "core::hint::unreachable_unchecked",
    "std::hint::unreachable_unchecked",
    "core::intrinsics::exact_div",
    "core::intrinsics::unchecked_add",
    "core::intrinsics::unchecked_shl",
    "core::intrinsics::unchecked_rem",
    "core::intrinsics::ctlz_nonzero",
    "core::intrinsics::arith_offset",
    "core::intrinsics::const_eval_select",
    "core::intrinsics::size_of_val",
    "core::intrinsics::wrapping_add",
    "core::panicking::panic",
    "std::intrinsics::unchecked_add",
    "parity::helper",
];

const COERCION_POOL: [&str; 9] = [
    "Unsize",
    "ArrayToPointer",
    "MutToConstPointer",
    "ReifyFnPointer",
    "ReifyFnPointer(Safe)",
    "UnsafeFnPointer",
    "ClosureFnPointer(Safe)",
    "ClosureFnPointer",
    "DynStar",
];

const BIN_OPS_ALL: [IrBinOp; 26] = [
    IrBinOp::Add,
    IrBinOp::AddUnchecked,
    IrBinOp::AddWithOverflow,
    IrBinOp::Sub,
    IrBinOp::SubUnchecked,
    IrBinOp::SubWithOverflow,
    IrBinOp::Mul,
    IrBinOp::MulUnchecked,
    IrBinOp::MulWithOverflow,
    IrBinOp::Div,
    IrBinOp::Rem,
    IrBinOp::BitXor,
    IrBinOp::BitAnd,
    IrBinOp::BitOr,
    IrBinOp::Shl,
    IrBinOp::ShlUnchecked,
    IrBinOp::Shr,
    IrBinOp::ShrUnchecked,
    IrBinOp::Eq,
    IrBinOp::Lt,
    IrBinOp::Le,
    IrBinOp::Ne,
    IrBinOp::Ge,
    IrBinOp::Gt,
    IrBinOp::Cmp,
    IrBinOp::Offset,
];

const RIGID_TY_KINDS: usize = 20;

/// Every `IrRigidTy` shape except `FnDef` (an `RigidTy.fnDef`-typed constant must be
/// zero-sized, so `FnDef` only appears in function-item operands), nested up to depth 2.
fn rigid_ty_variant(rng: &mut ParityRng, which: usize, depth: usize) -> IrRigidTy {
    let leaf = |rng: &mut ParityRng| {
        if depth >= 2 {
            IrRigidTy::Uint(IrUintTy::U32)
        } else {
            let k = rng.below(RIGID_TY_KINDS);
            rigid_ty_variant(rng, k, depth + 1)
        }
    };
    match which % RIGID_TY_KINDS {
        0 => IrRigidTy::Bool,
        1 => IrRigidTy::Char,
        2 => IrRigidTy::Int(IrIntTy::I32),
        3 => IrRigidTy::Uint(IrUintTy::U32),
        4 => IrRigidTy::Float(IrFloatTy::F64),
        5 => IrRigidTy::Never,
        6 => IrRigidTy::Str,
        7 => IrRigidTy::Tuple(vec![leaf(rng), leaf(rng)]),
        8 => IrRigidTy::Array(Box::new(leaf(rng)), 4),
        9 => IrRigidTy::Slice(Box::new(leaf(rng))),
        10 => IrRigidTy::Ref(IrMutability::Mut, Box::new(leaf(rng))),
        11 => IrRigidTy::RawPtr(IrMutability::Not, Box::new(leaf(rng))),
        12 => IrRigidTy::Adt("parity::Wrapper".to_string(), vec![leaf(rng)]),
        13 => IrRigidTy::FnPtr(
            vec![leaf(rng)],
            Box::new(IrRigidTy::Bool),
            if rng.chance(50) { IrSafety::Safe } else { IrSafety::Unsafe },
            if rng.chance(50) { IrCallConv::Rust } else { IrCallConv::C },
        ),
        14 => IrRigidTy::Closure("parity::case::{closure#0}".to_string(), vec![leaf(rng)]),
        15 => IrRigidTy::Dynamic("dyn parity::Trait".to_string()),
        16 => IrRigidTy::Foreign("parity::Opaque".to_string()),
        17 => IrRigidTy::Other("parity::other".to_string()),
        18 => IrRigidTy::Param {
            index: 0,
            name: "T".to_string(),
        },
        _ => IrRigidTy::Alias {
            def_path: "parity::Alias".to_string(),
            args: vec![leaf(rng)],
        },
    }
}

fn ty_of(kind: IrRigidTy) -> IrTy {
    IrTy {
        kind,
        layout_idx: 0,
    }
}

fn random_ty(rng: &mut ParityRng) -> IrTy {
    let k = rng.below(RIGID_TY_KINDS);
    ty_of(rigid_ty_variant(rng, k, 0))
}

fn fn_item(def_path: &str, generic_args: Vec<IrRigidTy>) -> IrOperand {
    IrOperand::Constant(IrConstOperand {
        ty: ty_of(IrRigidTy::FnDef(def_path.to_string(), generic_args)),
        val: IrConstValue::ZeroSized,
    })
}

fn local(local_: usize) -> IrPlace {
    IrPlace {
        local_,
        projection: Vec::new(),
    }
}

fn const_u32(bits: u128) -> IrOperand {
    IrOperand::Constant(IrConstOperand {
        ty: ty_of(IrRigidTy::Uint(IrUintTy::U32)),
        val: IrConstValue::Scalar(IrConstScalar::Int(IrScalarInt {
            bits,
            size_bytes: 4,
        })),
    })
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
            5 => IrProjectionElem::Downcast(
                if rng.chance(50) { Some("Variant".to_string()) } else { None },
                rng.below(2),
            ),
            6 => IrProjectionElem::OpaqueCast(random_ty(rng)),
            _ => IrProjectionElem::UnwrapUnsafeBinder(random_ty(rng)),
        });
    }
    IrPlace {
        local_: rng.below(4),
        projection,
    }
}

fn random_const_value(rng: &mut ParityRng) -> IrConstValue {
    match rng.below(6) {
        0 => IrConstValue::ZeroSized,
        1 => IrConstValue::Scalar(IrConstScalar::Int(IrScalarInt {
            bits: rng.below(100) as u128,
            size_bytes: 4,
        })),
        2 => IrConstValue::Scalar(IrConstScalar::Ptr(
            IrProvenancePtr {
                alloc_id: rng.below(3) as u64,
                offset_bytes: 0,
            },
            8,
        )),
        3 => IrConstValue::Indirect {
            alloc_id: 0,
            offset_bytes: rng.below(8) as u64,
        },
        4 => IrConstValue::Unevaluated("parity::CONST".to_string()),
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
    }
}

fn random_fn_item(rng: &mut ParityRng) -> IrOperand {
    let generic_args = if rng.chance(30) {
        vec![IrRigidTy::Param {
            index: 0,
            name: "T".to_string(),
        }]
    } else {
        Vec::new()
    };
    fn_item(rng.pick(&CALLEE_POOL), generic_args)
}

fn random_operand(rng: &mut ParityRng) -> IrOperand {
    match rng.below(6) {
        0 => IrOperand::Copy(random_place(rng)),
        1 => IrOperand::Move(random_place(rng)),
        2 => random_fn_item(rng),
        3 => IrOperand::Constant(IrConstOperand {
            // `RigidTy.param`-typed constants (`paramTypedConst`), zero-sized or not.
            ty: ty_of(IrRigidTy::Param {
                index: rng.below(2) as u32,
                name: "T".to_string(),
            }),
            val: random_const_value(rng),
        }),
        _ => IrOperand::Constant(IrConstOperand {
            ty: random_ty(rng),
            val: random_const_value(rng),
        }),
    }
}

fn cast_kind_variant(rng: &mut ParityRng, which: usize) -> IrCastKind {
    match which % 11 {
        0 => IrCastKind::PointerExposeProvenance,
        1 => IrCastKind::PointerWithExposedProvenance,
        2 => IrCastKind::PointerCoercion(rng.pick(&COERCION_POOL).to_string()),
        3 => IrCastKind::IntToInt,
        4 => IrCastKind::FloatToInt,
        5 => IrCastKind::FloatToFloat,
        6 => IrCastKind::IntToFloat,
        7 => IrCastKind::PtrToPtr,
        8 => IrCastKind::FnPtrToPtr,
        9 => IrCastKind::Transmute,
        _ => IrCastKind::Subtype,
    }
}

fn null_op_variant(which: usize) -> IrNullOp {
    match which % 5 {
        0 => IrNullOp::SizeOf,
        1 => IrNullOp::AlignOf,
        2 => IrNullOp::OffsetOf(vec![(0, 1), (1, 0)]),
        3 => IrNullOp::UbChecks,
        _ => IrNullOp::ContractChecks,
    }
}

fn aggregate_kind_variant(rng: &mut ParityRng, which: usize) -> IrAggregateKind {
    match which % 7 {
        0 => IrAggregateKind::Tuple,
        1 => IrAggregateKind::Adt("parity::UnionOrStruct".to_string(), 0, Some(0)),
        2 => IrAggregateKind::Adt("parity::UnionOrStruct".to_string(), 1, None),
        3 => IrAggregateKind::RawPtr(random_ty(rng), IrMutability::Mut),
        4 => IrAggregateKind::Coroutine("parity::coro".to_string()),
        5 => IrAggregateKind::Closure("parity::case::{closure#0}".to_string()),
        _ => IrAggregateKind::Array(random_ty(rng)),
    }
}

fn rvalue_variant(rng: &mut ParityRng, which: usize) -> IrRvalue {
    match which % 15 {
        0 => IrRvalue::Use(random_operand(rng)),
        1 => IrRvalue::Repeat(random_operand(rng), 2),
        2 => IrRvalue::Ref(
            if rng.chance(50) {
                IrBorrowKind::Shared
            } else {
                IrBorrowKind::Mut {
                    allow_two_phase: rng.chance(50),
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
            let k = rng.below(11);
            let ck = cast_kind_variant(rng, k);
            // Reified / closure fn-pointer coercions of a function item exercise
            // `reified_fn_def_paths` parity.
            let op = if matches!(&ck, IrCastKind::PointerCoercion(_)) && rng.chance(50) {
                random_fn_item(rng)
            } else {
                random_operand(rng)
            };
            IrRvalue::Cast(ck, op, random_ty(rng))
        }
        7 => IrRvalue::BinaryOp(
            BIN_OPS_ALL[rng.below(BIN_OPS_ALL.len())],
            random_operand(rng),
            random_operand(rng),
        ),
        8 => IrRvalue::NullaryOp(null_op_variant(rng.below(5)), random_ty(rng)),
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
            let k = rng.below(7);
            let ak = aggregate_kind_variant(rng, k);
            let n = rng.below(3);
            IrRvalue::Aggregate(ak, (0..n).map(|_| random_operand(rng)).collect())
        }
        12 => IrRvalue::ShallowInitBox(random_operand(rng), random_ty(rng)),
        13 => IrRvalue::CopyForDeref(random_place(rng)),
        _ => IrRvalue::WrapUnsafeBinder(random_operand(rng), random_ty(rng)),
    }
}

fn random_rvalue(rng: &mut ParityRng) -> IrRvalue {
    let k = rng.below(15);
    rvalue_variant(rng, k)
}

fn retag_kind_variant(which: usize) -> IrRetagKind {
    match which % 4 {
        0 => IrRetagKind::FnEntry,
        1 => IrRetagKind::TwoPhase,
        2 => IrRetagKind::Raw,
        _ => IrRetagKind::Default,
    }
}

fn statement_variant(rng: &mut ParityRng, which: usize) -> IrStatementKind {
    match which % 13 {
        0 => IrStatementKind::Assign(random_place(rng), random_rvalue(rng)),
        1 => IrStatementKind::SetDiscriminant(random_place(rng), rng.below(2)),
        2 => IrStatementKind::Deinit(random_place(rng)),
        3 => IrStatementKind::StorageLive(rng.below(4)),
        4 => IrStatementKind::StorageDead(rng.below(4)),
        5 => IrStatementKind::Retag(retag_kind_variant(rng.below(4)), random_place(rng)),
        6 => IrStatementKind::PlaceMention(random_place(rng)),
        7 => IrStatementKind::Intrinsic(IrNonDivergingIntrinsic::Assume(random_operand(rng))),
        8 => IrStatementKind::Intrinsic(IrNonDivergingIntrinsic::CopyNonOverlapping {
            src: random_operand(rng),
            dst: random_operand(rng),
            count: random_operand(rng),
        }),
        9 => IrStatementKind::Coverage,
        10 => IrStatementKind::ConstEvalCounter,
        11 => IrStatementKind::BackwardIncompatibleDropHint(random_place(rng)),
        _ => IrStatementKind::Nop,
    }
}

fn random_unwind(rng: &mut ParityRng, num_bbs: usize) -> IrUnwindAction {
    match rng.below(5) {
        0 => IrUnwindAction::Continue,
        1 => IrUnwindAction::Unreachable,
        2 => IrUnwindAction::Terminate,
        // Occasionally out of bounds, exercising `cfgTargetsInBounds` parity.
        3 => IrUnwindAction::Cleanup(rng.below(num_bbs + 1)),
        _ => IrUnwindAction::Cleanup(rng.below(num_bbs)),
    }
}

fn random_call_func(rng: &mut ParityRng) -> IrOperand {
    match rng.below(10) {
        0 => IrOperand::Copy(local(rng.below(4))),
        1 => IrOperand::Constant(IrConstOperand {
            ty: ty_of(IrRigidTy::Param {
                index: 0,
                name: "F".to_string(),
            }),
            val: IrConstValue::ZeroSized,
        }),
        2 => IrOperand::Move(random_place(rng)),
        _ => random_fn_item(rng),
    }
}

fn terminator_variant(rng: &mut ParityRng, which: usize, num_bbs: usize) -> IrTerminatorKind {
    let target_bb = if rng.chance(90) {
        rng.below(num_bbs)
    } else {
        num_bbs
    };
    match which % 11 {
        0 => IrTerminatorKind::Goto(target_bb),
        1 => {
            let n = rng.below(4);
            IrTerminatorKind::SwitchInt(
                random_operand(rng),
                IrSwitchTargets {
                    branches: (0..n).map(|i| (i as u128, rng.below(num_bbs))).collect(),
                    otherwise: target_bb,
                },
            )
        }
        2 => IrTerminatorKind::UnwindResume,
        3 => IrTerminatorKind::UnwindTerminate,
        4 => IrTerminatorKind::Return,
        5 => IrTerminatorKind::Unreachable,
        6 => {
            let unwind = random_unwind(rng, num_bbs);
            IrTerminatorKind::Drop {
                place: random_place(rng),
                target: target_bb,
                unwind,
            }
        }
        7 => {
            let func = random_call_func(rng);
            // `const_eval_select(args, called_in_const, called_at_rt)` takes exactly three
            // arguments; other arities fall through to `extCall` and must fail closed.
            let args: Vec<IrOperand> = if matches!(
                &func,
                IrOperand::Constant(IrConstOperand {
                    ty: IrTy { kind: IrRigidTy::FnDef(p, _), .. },
                    ..
                }) if p == "core::intrinsics::const_eval_select"
            ) && rng.chance(70)
            {
                vec![
                    IrOperand::Move(local(1)),
                    random_fn_item(rng),
                    if rng.chance(80) {
                        random_fn_item(rng)
                    } else {
                        IrOperand::Copy(local(2))
                    },
                ]
            } else {
                let n = rng.below(4);
                (0..n).map(|_| random_operand(rng)).collect()
            };
            let target = if rng.chance(70) {
                Some(target_bb)
            } else {
                None
            };
            let unwind = random_unwind(rng, num_bbs);
            IrTerminatorKind::Call {
                func,
                args,
                destination: random_place(rng),
                target,
                unwind,
            }
        }
        8 => {
            let func = random_call_func(rng);
            let n = rng.below(4);
            IrTerminatorKind::TailCall {
                func,
                args: (0..n).map(|_| random_operand(rng)).collect(),
            }
        }
        9 => {
            let unwind = random_unwind(rng, num_bbs);
            IrTerminatorKind::Assert {
                cond: random_operand(rng),
                expected: rng.chance(50),
                target: target_bb,
                unwind,
            }
        }
        _ => {
            let n = rng.below(3);
            let unwind = random_unwind(rng, num_bbs);
            IrTerminatorKind::InlineAsm {
                template: "nop".to_string(),
                targets: (0..n).map(|_| rng.below(num_bbs)).collect(),
                unwind,
            }
        }
    }
}

fn captured_mir_from_blocks(case_idx: usize, basic_blocks: Vec<IrBasicBlockData>) -> IrCapturedMir {
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

fn block(statements: Vec<IrStatementKind>, kind: IrTerminatorKind) -> IrBasicBlockData {
    IrBasicBlockData {
        statements: statements
            .into_iter()
            .map(|kind| IrStatement {
                kind,
                span: "src/lib.rs:10:5".to_string(),
                comment: None,
            })
            .collect(),
        terminator: IrTerminator {
            kind,
            span: "src/lib.rs:20:5".to_string(),
            comment: None,
        },
        is_cleanup: false,
    }
}

fn random_captured_mir(rng: &mut ParityRng, case_idx: usize) -> IrCapturedMir {
    let num_bbs = 1 + rng.below(3);
    let mut basic_blocks = Vec::with_capacity(num_bbs);
    for _ in 0..num_bbs {
        let num_stmts = rng.below(4);
        let statements = (0..num_stmts)
            .map(|_| {
                let k = rng.below(13);
                statement_variant(rng, k)
            })
            .collect();
        let k = rng.below(11);
        let term_kind = terminator_variant(rng, k, num_bbs);
        basic_blocks.push(block(statements, term_kind));
    }
    captured_mir_from_blocks(case_idx, basic_blocks)
}

/// Deterministic sweep guaranteeing that every IR variant family reaches both censuses:
/// every `BinOp`, `NullOp`, `CastKind`, pointer coercion, `AggregateKind`, `Rvalue`,
/// `StatementKind`, `RetagKind`, `TerminatorKind`, `ConstValue`, `RigidTy` shape, every
/// `CALLEE_POOL` callee at call arities 0..=3, three-argument `const_eval_select`, and
/// `RigidTy.param` / indirect call targets.
fn variant_sweep_cases(rng: &mut ParityRng, first_case_idx: usize) -> Vec<IrCapturedMir> {
    let mut bodies: Vec<Vec<IrBasicBlockData>> = Vec::new();
    let assign = |rv: IrRvalue| IrStatementKind::Assign(local(0), rv);
    for op in BIN_OPS_ALL {
        bodies.push(vec![block(
            vec![assign(IrRvalue::BinaryOp(op, IrOperand::Copy(local(1)), const_u32(3)))],
            IrTerminatorKind::Return,
        )]);
    }
    for which in 0..5 {
        bodies.push(vec![block(
            vec![assign(IrRvalue::NullaryOp(null_op_variant(which), ty_of(IrRigidTy::Uint(IrUintTy::U32))))],
            IrTerminatorKind::Return,
        )]);
    }
    for which in 0..11 {
        let ck = cast_kind_variant(rng, which);
        bodies.push(vec![block(
            vec![assign(IrRvalue::Cast(ck, IrOperand::Copy(local(1)), ty_of(IrRigidTy::Uint(IrUintTy::U32))))],
            IrTerminatorKind::Return,
        )]);
    }
    for coercion in COERCION_POOL {
        bodies.push(vec![block(
            vec![
                assign(IrRvalue::Cast(
                    IrCastKind::PointerCoercion(coercion.to_string()),
                    fn_item("parity::helper", Vec::new()),
                    ty_of(IrRigidTy::FnPtr(Vec::new(), Box::new(IrRigidTy::Bool), IrSafety::Safe, IrCallConv::Rust)),
                )),
                assign(IrRvalue::Cast(
                    IrCastKind::PointerCoercion(coercion.to_string()),
                    IrOperand::Copy(local(2)),
                    ty_of(IrRigidTy::RawPtr(IrMutability::Not, Box::new(IrRigidTy::Uint(IrUintTy::U32)))),
                )),
            ],
            IrTerminatorKind::Return,
        )]);
    }
    for which in 0..7 {
        let ak = aggregate_kind_variant(rng, which);
        bodies.push(vec![block(
            vec![assign(IrRvalue::Aggregate(ak, vec![IrOperand::Copy(local(1)), const_u32(1)]))],
            IrTerminatorKind::Return,
        )]);
    }
    for which in 0..15 {
        let rv = rvalue_variant(rng, which);
        bodies.push(vec![block(vec![assign(rv)], IrTerminatorKind::Return)]);
    }
    for which in 0..13 {
        let sk = statement_variant(rng, which);
        bodies.push(vec![block(vec![sk], IrTerminatorKind::Return)]);
    }
    for which in 0..4 {
        bodies.push(vec![block(
            vec![IrStatementKind::Retag(retag_kind_variant(which), local(1))],
            IrTerminatorKind::Return,
        )]);
    }
    for which in 0..11 {
        let tk = terminator_variant(rng, which, 2);
        bodies.push(vec![block(Vec::new(), tk), block(Vec::new(), IrTerminatorKind::Return)]);
    }
    for which in 0..6 {
        let val = match which {
            0 => IrConstValue::ZeroSized,
            1 => IrConstValue::Scalar(IrConstScalar::Int(IrScalarInt { bits: 7, size_bytes: 4 })),
            2 => IrConstValue::Scalar(IrConstScalar::Ptr(IrProvenancePtr { alloc_id: 1, offset_bytes: 0 }, 8)),
            3 => IrConstValue::Slice {
                data: IrConstScalar::Ptr(IrProvenancePtr { alloc_id: 0, offset_bytes: 0 }, 8),
                meta: 3,
            },
            4 => IrConstValue::Indirect { alloc_id: 2, offset_bytes: 4 },
            _ => IrConstValue::Unevaluated("parity::CONST".to_string()),
        };
        for param_typed in [false, true] {
            let ty = if param_typed {
                ty_of(IrRigidTy::Param { index: 0, name: "T".to_string() })
            } else {
                ty_of(IrRigidTy::Uint(IrUintTy::U32))
            };
            bodies.push(vec![block(
                vec![assign(IrRvalue::Use(IrOperand::Constant(IrConstOperand { ty, val: val.clone() })))],
                IrTerminatorKind::Return,
            )]);
        }
    }
    for which in 0..RIGID_TY_KINDS {
        let kind = rigid_ty_variant(rng, which, 0);
        bodies.push(vec![block(
            vec![
                assign(IrRvalue::Use(IrOperand::Constant(IrConstOperand {
                    ty: ty_of(kind.clone()),
                    val: IrConstValue::ZeroSized,
                }))),
                IrStatementKind::Assign(
                    IrPlace {
                        local_: 1,
                        projection: vec![IrProjectionElem::Field(0, ty_of(kind))],
                    },
                    IrRvalue::Use(const_u32(1)),
                ),
            ],
            IrTerminatorKind::Return,
        )]);
    }
    for callee in CALLEE_POOL {
        for arity in 0..=3usize {
            for converging in [true, false] {
                let args = (0..arity)
                    .map(|i| if i == 0 { IrOperand::Move(local(1)) } else { fn_item("parity::helper", Vec::new()) })
                    .collect();
                bodies.push(vec![
                    block(
                        Vec::new(),
                        IrTerminatorKind::Call {
                            func: fn_item(callee, Vec::new()),
                            args,
                            destination: local(0),
                            target: if converging { Some(1) } else { None },
                            unwind: IrUnwindAction::Continue,
                        },
                    ),
                    block(Vec::new(), IrTerminatorKind::Return),
                ]);
            }
        }
    }
    for rt in ["parity::helper", "core::panicking::panic", "core::intrinsics::unchecked_add"] {
        for rt_operand in [fn_item(rt, Vec::new()), IrOperand::Copy(local(2))] {
            bodies.push(vec![
                block(
                    Vec::new(),
                    IrTerminatorKind::Call {
                        func: fn_item("core::intrinsics::const_eval_select", Vec::new()),
                        args: vec![IrOperand::Move(local(1)), fn_item("parity::const_impl", Vec::new()), rt_operand],
                        destination: local(0),
                        target: Some(1),
                        unwind: IrUnwindAction::Unreachable,
                    },
                ),
                block(Vec::new(), IrTerminatorKind::Return),
            ]);
        }
    }
    // Strict-parser rejections both sides must agree on: an `RigidTy.fnDef`-typed constant
    // whose value is not zero-sized (`extractCalleeDefPath?` would read the callee from the
    // type), as a plain operand and as a call target.
    for val in [
        IrConstValue::Scalar(IrConstScalar::Int(IrScalarInt { bits: 1, size_bytes: 4 })),
        IrConstValue::Indirect { alloc_id: 0, offset_bytes: 0 },
        IrConstValue::Unevaluated("parity::CONST".to_string()),
    ] {
        let fn_def_const = IrOperand::Constant(IrConstOperand {
            ty: ty_of(IrRigidTy::FnDef("parity::helper".to_string(), Vec::new())),
            val,
        });
        bodies.push(vec![block(vec![assign(IrRvalue::Use(fn_def_const.clone()))], IrTerminatorKind::Return)]);
        bodies.push(vec![
            block(
                Vec::new(),
                IrTerminatorKind::Call {
                    func: fn_def_const,
                    args: Vec::new(),
                    destination: local(0),
                    target: Some(1),
                    unwind: IrUnwindAction::Continue,
                },
            ),
            block(Vec::new(), IrTerminatorKind::Return),
        ]);
    }
    bodies
        .into_iter()
        .enumerate()
        .map(|(i, blocks)| captured_mir_from_blocks(first_case_idx + i, blocks))
        .collect()
}

fn json_str(s: &str) -> String {
    let mut out = String::from("\"");
    for ch in s.chars() {
        match ch {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if (c as u32) < 0x20 => out.push_str(&format!("\\u{:04x}", c as u32)),
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

fn str_list_json(items: &[String]) -> String {
    format!(
        "[{}]",
        items.iter().map(|s| json_str(s)).collect::<Vec<_>>().join(", ")
    )
}

fn sites_json(sites: &[FaultSite]) -> String {
    format!(
        "[{}]",
        sites
            .iter()
            .map(|s| format!("[{}, {}, \"{}\"]", s.block_idx, s.stmt_idx, s.fault_class.as_str()))
            .collect::<Vec<_>>()
            .join(", ")
    )
}

#[test]
fn python_census_and_audit_fault_coverage_match_rust_and_lean_end_to_end() {
    let checkout_root = anneal_checkout_root();
    let check_trusted_py = checkout_root.join("trusted/audit/check_trusted.py");

    // 1. Differential parity across an exhaustive IR-variant sweep plus 300 randomized
    //    emitted `Mir/<Item>.lean` modules between Rust (`census_lean_mir_module`,
    //    `census_ir_captured_mir`, `direct_callee_def_paths`, `reified_fn_def_paths`,
    //    `reconcile_multi_item_coverage`) and Python (`census_lean_mir_module`,
    //    `emit_mir_obligation_fault_sites`, `direct_callee_def_paths`,
    //    `reified_fn_def_paths`, `reconcile_multi_item_coverage`). A module the Rust strict
    //    parser rejects must be rejected by the Python strict parser too.
    let diff_dir = unique_temp_dir("diff-sweep");
    let mut rng = ParityRng(0xE2_FA01_7C0D_E123);
    let mut irs = variant_sweep_cases(&mut rng, 0);
    let sweep_len = irs.len();
    for idx in 0..300 {
        irs.push(random_captured_mir(&mut rng, sweep_len + idx));
    }
    let registry = PropertyRegistry::all_verified();
    let mut cases_json = Vec::new();
    let mut accepted = 0usize;
    let mut rejected = 0usize;
    let mut verified_strict = 0usize;
    let mut unverified_strict = 0usize;
    for (idx, ir) in irs.iter().enumerate() {
        let lean_src = emit_mir_lean_module(&format!("Mir.Parity.case_{idx}"), ir);
        let mir_file = diff_dir.join(format!("case_{idx}.lean"));
        fs::write(&mir_file, &lean_src).expect("write Mir case");
        let path_json = json_str(&mir_file.to_string_lossy());
        let rust_sites = match census_lean_mir_module(&lean_src) {
            Ok(sites) => sites,
            Err(err) => {
                rejected += 1;
                cases_json.push(format!(
                    "{{\"path\": {path_json}, \"ok\": false, \"rust_error\": {}}}",
                    json_str(&format!("{err:?}"))
                ));
                continue;
            }
        };
        accepted += 1;
        assert_eq!(
            census_ir_captured_mir(ir),
            rust_sites,
            "Rust IR vs Lean-text census mismatch on case {idx}:\n{lean_src}"
        );
        let body = parse_lean_mir_module_body_strict(&lean_src).expect("strict Rust body parse");
        assert_eq!(census_mir_fault_sites(&body), rust_sites);
        let direct = direct_callee_def_paths(&body);
        let reified = reified_fn_def_paths(&body);
        let all_external: Vec<String> = direct
            .iter()
            .chain(reified.iter())
            .cloned()
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect();
        let verdict = |external: &[String], allow: bool| {
            matches!(
                reconcile_multi_item_coverage(
                    &[ItemCoverageInput::from_body(body.clone(), rust_sites.clone())],
                    &CalleeClosure {
                        inline_callees: Vec::new(),
                        external_callees: external.to_vec(),
                        allow_unresolved_indirect_calls: allow,
                    },
                    &registry,
                ),
                MultiItemCoverageVerdict::Verified
            )
        };
        let strict = verdict(&[], false);
        if strict {
            verified_strict += 1;
        } else {
            unverified_strict += 1;
        }
        cases_json.push(format!(
            "{{\"path\": {path_json}, \"ok\": true, \"sites\": {}, \"direct\": {}, \"reified\": {}, \
             \"external\": {}, \"strict\": {strict}, \"unresolved\": {}, \"external_closed\": {}, \
             \"external_closed_unresolved\": {}}}",
            sites_json(&rust_sites),
            str_list_json(&direct),
            str_list_json(&reified),
            str_list_json(&all_external),
            verdict(&[], true),
            verdict(&all_external, false),
            verdict(&all_external, true),
        ));
    }
    // The sweep must stay meaningful: most bodies parse, and both verified and
    // fail-closed reconciliation outcomes (and strict rejections) are exercised.
    assert!(accepted >= (irs.len() * 3) / 4, "too many strict rejections: {rejected}/{}", irs.len());
    assert!(rejected > 0, "expected some strict-parser rejections (fnDef-typed non-ZST constants)");
    assert!(verified_strict > 0 && unverified_strict > 0);

    let manifest_cases_path = diff_dir.join("cases.json");
    fs::write(&manifest_cases_path, format!("[\n{}\n]\n", cases_json.join(",\n")))
        .expect("write cases.json");

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

# Verify 4+2 false-proof mutation probes (registry probe sweeps all 12 classes)
probes = ct.run_false_proof_mutation_probes()
assert probes["faultClasses"] == 12
assert len(probes["probesPassed"]) == 6
reg_probe = ct.run_property_registry_unemitted_probe()
assert reg_probe["witnessClasses"] == expected_classes, reg_probe["witnessClasses"]

def closure(external, allow):
    return {{"inline_callees": [], "external_callees": list(external), "allow_unresolved_indirect_calls": allow}}

cases = json.loads(Path({cases_path:?}).read_text())
failures = []
for idx, entry in enumerate(cases):
    src = Path(entry["path"]).read_text()
    if not entry["ok"]:
        try:
            ct.census_lean_mir_module(src)
        except ct.CensusScanError:
            continue
        failures.append(f"case {{idx}}: Rust rejected ({{entry['rust_error']}}) but Python accepted")
        continue
    try:
        body = ct.parse_lean_mir_module_body_strict(src)
        py_sites = [[s.block_idx, s.stmt_idx, s.fault_class] for s in ct.census_lean_mir_module(src)]
    except ct.CensusScanError as err:
        failures.append(f"case {{idx}}: Rust accepted but Python rejected: {{err}}")
        continue
    if py_sites != entry["sites"]:
        failures.append(f"case {{idx}} census mismatch: py={{py_sites}} vs rust={{entry['sites']}}")
    ob_sites = [[s.block_idx, s.stmt_idx, s.fault_class] for s in ct.emit_mir_obligation_fault_sites(body)]
    if ob_sites != entry["sites"]:
        failures.append(f"case {{idx}} obligation emitter mismatch: ob={{ob_sites}} vs census={{entry['sites']}}")
    if ct.direct_callee_def_paths(body) != entry["direct"]:
        failures.append(f"case {{idx}} direct callees mismatch: {{ct.direct_callee_def_paths(body)}} vs {{entry['direct']}}")
    if ct.reified_fn_def_paths(body) != entry["reified"]:
        failures.append(f"case {{idx}} reified fn mismatch: {{ct.reified_fn_def_paths(body)}} vs {{entry['reified']}}")
    census = ct.census_mir_fault_sites(body)
    items = [{{"def_path": body["def_path"], "body": body, "discharged": census}}]
    for key, ext, allow in (
        ("strict", [], False),
        ("unresolved", [], True),
        ("external_closed", entry["external"], False),
        ("external_closed_unresolved", entry["external"], True),
    ):
        got = ct.reconcile_multi_item_coverage(items, closure(ext, allow), ct.PROPERTY_REGISTRY)["is_verified"]
        if got != entry[key]:
            failures.append(f"case {{idx}} reconcile `{{key}}` mismatch: py={{got}} vs rust={{entry[key]}}")
assert not failures, "\n".join(failures[:40])
print(f"PYTHON_SWEEP_PARITY_OK {{len(cases)}}")
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
            && String::from_utf8_lossy(&out.stdout)
                .contains(&format!("PYTHON_SWEEP_PARITY_OK {}", irs.len())),
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

fn run_python_audit(check_trusted_py: &Path, target: &Path) -> Output {
    Command::new("python3")
        .arg("-B")
        .arg(check_trusted_py)
        .arg("--audit-fault-coverage")
        .arg(target)
        .output()
        .expect("invoke check_trusted.py --audit-fault-coverage")
}

fn assert_audit_rejects(check_trusted_py: &Path, target: &Path, label: &str, needle: &str) {
    let out = run_python_audit(check_trusted_py, target);
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(
        !out.status.success()
            && stderr.contains("Trusted check failed (fault-coverage)")
            && stderr.contains(needle),
        "{label}: expected --audit-fault-coverage to fail closed with `{needle}`:\nstdout: {}\nstderr: {stderr}",
        String::from_utf8_lossy(&out.stdout),
    );
}

/// Byte span `(open, close)` of the JSON array value of the first `"key": [...]` in a
/// cargo-anneal-rendered FaultCensus receipt. Brackets inside JSON strings (e.g. the
/// sysroot callee `core::slice::<impl [T]>::len`) are skipped.
fn json_array_span(receipt: &str, key: &str) -> (usize, usize) {
    let needle = format!("\"{key}\": [");
    let start = receipt
        .find(&needle)
        .unwrap_or_else(|| panic!("`{key}` array in receipt:\n{receipt}"));
    let open = start + needle.len() - 1;
    let bytes = receipt.as_bytes();
    let (mut depth, mut in_str, mut escaped) = (0usize, false, false);
    for (idx, &b) in bytes.iter().enumerate().skip(open) {
        if in_str {
            match (escaped, b) {
                (true, _) => escaped = false,
                (false, b'\\') => escaped = true,
                (false, b'"') => in_str = false,
                _ => {}
            }
            continue;
        }
        match b {
            b'"' => in_str = true,
            b'[' => depth += 1,
            b']' => {
                depth -= 1;
                if depth == 0 {
                    return (open, idx);
                }
            }
            _ => {}
        }
    }
    panic!("unbalanced `{key}` array in receipt:\n{receipt}");
}

fn with_json_array(receipt: &str, key: &str, new_array: &str) -> String {
    let (open, close) = json_array_span(receipt, key);
    format!("{}{}{}", &receipt[..open], new_array, &receipt[close + 1..])
}

/// The string items of a flat JSON string array (`inline_callees` / `external_callees`).
fn json_array_items(receipt: &str, key: &str) -> Vec<String> {
    let (open, close) = json_array_span(receipt, key);
    let mut items = Vec::new();
    let mut chars = receipt[open + 1..close].chars();
    while let Some(ch) = chars.next() {
        if ch != '"' {
            continue;
        }
        let mut item = String::new();
        while let Some(c) = chars.next() {
            match c {
                '\\' => item.push(chars.next().expect("escaped char")),
                '"' => break,
                c => item.push(c),
            }
        }
        items.push(item);
    }
    items
}

/// `[adv ep2-B1]` A scaffold-only (no Lean) real multi-crate workspace whose receipts carry
/// real inline callees (cross-crate, same-crate and sysroot bodies), a modular
/// `externalSpecCallContract` surface, and an assumed `spec(trusted)` subject with an
/// unresolved indirect call. The pure-Python gate must accept it, agree with the Rust
/// census on every generated `Mir/` module (callees included), and fail closed on every
/// callee-closure, discharged-site, `Obligations/` and `Verify/` tamper.
#[test]
fn python_audit_fault_coverage_rejects_callee_closure_tampering_on_real_multi_crate_workspace() {
    let checkout_root = anneal_checkout_root();
    let check_trusted_py = checkout_root.join("trusted/audit/check_trusted.py");
    let wrapper_bin = ensure_rustc_capture_binary(&checkout_root);
    let root = unique_temp_dir("multi-crate-closure");
    let crate_a = root.join("crate_a");
    let crate_b = root.join("crate_b");
    fs::create_dir_all(crate_a.join("src")).expect("create crate_a/src");
    fs::create_dir_all(crate_b.join("src")).expect("create crate_b/src");
    fs::write(
        crate_b.join("Cargo.toml"),
        "[package]\nname = \"crate_b\"\nversion = \"0.1.0\"\nedition = \"2024\"\npublish = false\n",
    )
    .expect("write crate_b/Cargo.toml");
    fs::write(
        crate_b.join("src/lib.rs"),
        r#"#![no_std]

pub fn inner_leaf(x: usize) -> usize {
    x.wrapping_add(1)
}

pub fn helper_add(x: usize, y: usize) -> usize {
    if x < 1024 { inner_leaf(x).wrapping_add(y) } else { y }
}

pub fn overridden_dep(x: usize) -> usize {
    x.wrapping_add(5)
}
"#,
    )
    .expect("write crate_b/src/lib.rs");
    fs::write(
        crate_a.join("Cargo.toml"),
        format!(
            "[package]\nname = \"crate_a\"\nversion = \"0.1.0\"\nedition = \"2024\"\npublish = false\n\n\
             [dependencies]\ncrate_b = {{ path = \"../crate_b\" }}\nanneal-spec = {{ path = \"{}\" }}\n",
            checkout_root.join("crates/anneal-spec").display()
        ),
    )
    .expect("write crate_a/Cargo.toml");
    fs::write(
        crate_a.join("src/lib.rs"),
        r#"#![allow(dead_code, non_snake_case, non_upper_case_globals)]
use anneal_spec::*;

pub const __ANNEAL_EXT_SPEC_TARGET_ext_overridden_dep: &str = "crate_b::overridden_dep";
pub fn ext_overridden_dep(x: usize) -> usize {
    let _: fn(usize) -> usize = *::core::hint::black_box(&crate_b::overridden_dep);
    let _ = (x,);
    unreachable!()
}
pub fn __anodized_fn_requires_ext_overridden_dep(x: usize) -> bool {
    x < 100
}
pub fn __anodized_fn_ensures_ext_overridden_dep(x: usize, ret: usize) -> bool {
    ret == x.wrapping_add(5)
}

pub fn caller_default_callees(s: &[u8], extra: usize) -> usize {
    crate_b::helper_add(s.len(), extra)
}

pub fn caller_with_external_specs(x: usize) -> usize {
    crate_b::overridden_dep(x).wrapping_add(crate_b::inner_leaf(1))
}

fn local_helper(x: u32) -> u32 {
    x.wrapping_mul(3)
}

#[anneal_spec::spec(requires: x < 100, ensures: |ref ret| *ret == x.wrapping_mul(3))]
pub fn calls_local_helper(x: u32) -> u32 {
    local_helper(x)
}

#[anneal_spec::spec(trusted, requires: true, ensures: |ref ret| *ret == 0)]
pub fn trusted_indirect(f: fn() -> u32) -> u32 {
    f();
    0
}
"#,
    )
    .expect("write crate_a/src/lib.rs");

    let mut driver_cfg = CaptureDriverConfig::new(&crate_a);
    driver_cfg.manifest_path = Some(crate_a.join("Cargo.toml"));
    driver_cfg.rustc_wrapper = Some(wrapper_bin);
    let (manifest, records) = run_cargo_capture(&driver_cfg).expect("run_cargo_capture");
    assert!(manifest.compilation_succeeded);
    let scaffold_cfg = ScaffoldConfig {
        workspace_root: crate_a.clone(),
        units_dir: Some(driver_cfg.units_dir.clone()),
        anneal_repo_root: Some(checkout_root.clone()),
        init_spec_templates: false,
        init_proof_templates: false,
    };
    scaffold_workspace_with_config(&scaffold_cfg, &records).expect("scaffold_workspace_with_config");
    let gen_dir = crate_a.join(".anneal/generated");
    let receipt = |stem: &str| gen_dir.join(format!("FaultCensus/CrateA/{stem}.json"));
    let read = |p: &Path| fs::read_to_string(p).unwrap_or_else(|e| panic!("read {}: {e}", p.display()));

    // Real receipts carry the closure shapes this test is about.
    let default_receipt = read(&receipt("caller_default_callees"));
    let inline = json_array_items(&default_receipt, "inline_callees");
    for callee in ["crate_b::helper_add", "crate_b::inner_leaf", "core::num::<impl usize>::wrapping_add"] {
        assert!(inline.iter().any(|c| c == callee), "inline callee {callee} in {inline:?}");
    }
    let ext_receipt = read(&receipt("caller_with_external_specs"));
    assert_eq!(json_array_items(&ext_receipt, "external_callees"), vec!["crate_b::overridden_dep"]);
    assert!(read(&gen_dir.join("Verify/CrateA/caller_with_external_specs.lean")).contains("ModularVerificationResult"));
    let trusted_receipt = read(&receipt("trusted_indirect"));
    assert!(trusted_receipt.contains("\"allow_unresolved_indirect_calls\": true"));
    assert!(read(&gen_dir.join("Verify/CrateA/trusted_indirect.lean")).contains("rust_trusted_contract"));
    let helper_receipt = read(&receipt("calls_local_helper"));
    assert!(json_array_items(&helper_receipt, "inline_callees").iter().any(|c| c == "crate_a::local_helper"));

    // Positive: the hardened pure-Python gate accepts the honest workspace.
    let ok = run_python_audit(&check_trusted_py, &crate_a);
    assert!(
        ok.status.success() && String::from_utf8_lossy(&ok.stdout).contains("PASS: fault-site coverage audit"),
        "expected --audit-fault-coverage to accept the real multi-crate workspace:\nstdout: {}\nstderr: {}",
        String::from_utf8_lossy(&ok.stdout),
        String::from_utf8_lossy(&ok.stderr)
    );

    // Rust vs Python census on every generated `Mir/` module (subjects, same-crate,
    // cross-crate and sysroot callees, and spec companions).
    let mut mir_files = Vec::new();
    let mut stack = vec![gen_dir.join("Mir")];
    while let Some(dir) = stack.pop() {
        for entry in fs::read_dir(&dir).expect("read Mir dir") {
            let path = entry.expect("Mir entry").path();
            if path.is_dir() {
                stack.push(path);
            } else if path.extension().is_some_and(|e| e == "lean") {
                mir_files.push(path);
            }
        }
    }
    mir_files.sort();
    assert!(mir_files.len() >= 10, "expected callee Mir modules, got {mir_files:?}");
    let mut census_cases = Vec::new();
    for path in &mir_files {
        let sites = census_lean_mir_module(&read(path))
            .unwrap_or_else(|e| panic!("Rust strict census of {}: {e:?}", path.display()));
        census_cases.push(format!(
            "{{\"path\": {}, \"sites\": {}}}",
            json_str(&path.to_string_lossy()),
            sites_json(&sites)
        ));
    }
    let census_path = root.join("mir-census.json");
    fs::write(&census_path, format!("[{}]", census_cases.join(",\n"))).expect("write mir-census.json");
    let census_py = format!(
        r#"
import importlib.util, json
from pathlib import Path
spec = importlib.util.spec_from_file_location("ct", Path({check:?}))
ct = importlib.util.module_from_spec(spec)
spec.loader.exec_module(ct)
cases = json.loads(Path({cases:?}).read_text())
for entry in cases:
    src = Path(entry["path"]).read_text()
    got = [[s.block_idx, s.stmt_idx, s.fault_class] for s in ct.census_lean_mir_module(src)]
    assert got == entry["sites"], (entry["path"], got, entry["sites"])
    body = ct.parse_lean_mir_module_body_strict(src)
    ob = [[s.block_idx, s.stmt_idx, s.fault_class] for s in ct.emit_mir_obligation_fault_sites(body)]
    assert ob == entry["sites"], ("emitter", entry["path"], ob, entry["sites"])
print(f"REAL_MIR_CENSUS_PARITY_OK {{len(cases)}}")
"#,
        check = check_trusted_py.to_string_lossy(),
        cases = census_path.to_string_lossy(),
    );
    let out = Command::new("python3").arg("-B").arg("-c").arg(&census_py).output().expect("python census parity");
    assert!(
        out.status.success()
            && String::from_utf8_lossy(&out.stdout).contains(&format!("REAL_MIR_CENSUS_PARITY_OK {}", mir_files.len())),
        "real Mir census parity failed:\nstdout: {}\nstderr: {}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );

    // Negative: every receipt / Obligations / Verify tamper fails closed, and restoring
    // the original bytes makes the gate pass again.
    let tamper = |path: PathBuf, edited: String, label: &str, needle: &str| {
        let original = read(&path);
        assert_ne!(original, edited, "{label}: tamper must change {}", path.display());
        fs::write(&path, &edited).expect("write tamper");
        assert_audit_rejects(&check_trusted_py, &crate_a, label, needle);
        fs::write(&path, &original).expect("restore");
    };
    let without = |items: &[String], drop: &str| -> String {
        str_list_json(&items.iter().filter(|c| c.as_str() != drop).cloned().collect::<Vec<_>>())
    };
    let with_extra = |items: &[String], extra: &str| -> String {
        let mut v = items.to_vec();
        v.push(extra.to_string());
        str_list_json(&v)
    };
    tamper(
        receipt("caller_default_callees"),
        with_json_array(&default_receipt, "inline_callees", &without(&inline, "crate_b::inner_leaf")),
        "dropped inline callee",
        "missing from FaultCensus `callee_closure.inline_callees`",
    );
    tamper(
        receipt("caller_default_callees"),
        with_json_array(&default_receipt, "inline_callees", &with_extra(&inline, "crate_b::overridden_dep")),
        "extra inline callee",
        "never installs",
    );
    tamper(
        receipt("caller_default_callees"),
        with_json_array(&default_receipt, "external_callees", "[\"crate_b::ghost\"]"),
        "external callee on a non-modular surface",
        "non-modular",
    );
    tamper(
        receipt("caller_with_external_specs"),
        with_json_array(&ext_receipt, "external_callees", "[\"crate_b::overridden_dep\", \"crate_b::ghost\"]"),
        "unjustified modular external callee",
        "backed by neither",
    );
    tamper(
        receipt("calls_local_helper"),
        helper_receipt.replacen(
            "\"allow_unresolved_indirect_calls\": false",
            "\"allow_unresolved_indirect_calls\": true",
            1,
        ),
        "allow_unresolved_indirect_calls on a verified surface",
        "allow_unresolved_indirect_calls",
    );
    tamper(
        receipt("calls_local_helper"),
        with_json_array(&helper_receipt, "discharged_sites", "[]"),
        "empty discharged_sites",
        "independent obligation emitter",
    );
    let (d_open, d_close) = json_array_span(&helper_receipt, "discharged_sites");
    let discharged_inner = helper_receipt[d_open + 1..d_close].trim();
    assert!(!discharged_inner.is_empty(), "calls_local_helper discharges its call-site obligations");
    let unbacked = format!(
        "[{discharged_inner}, {{\"block_idx\": 0, \"stmt_idx\": 0, \"fault_class\": \"shift_overflow\"}}]"
    );
    tamper(
        receipt("calls_local_helper"),
        with_json_array(&helper_receipt, "discharged_sites", &unbacked),
        "unbacked discharged site",
        "independent obligation emitter",
    );
    let ob_default_path = gen_dir.join("Obligations/CrateA/caller_default_callees.lean");
    let ob_default = read(&ob_default_path);
    let pruned_ob = ob_default
        .replacen("Mir.CrateB.inner_leaf.body, ", "", 1)
        .replacen(", Mir.CrateB.inner_leaf.body", "", 1);
    fs::write(&ob_default_path, &pruned_ob).expect("prune defaultCallees");
    tamper(
        receipt("caller_default_callees"),
        with_json_array(&default_receipt, "inline_callees", &without(&inline, "crate_b::inner_leaf")),
        "transitive callee dropped from both defaultCallees and the receipt",
        "direct callee `crate_b::inner_leaf`",
    );
    fs::write(&ob_default_path, &ob_default).expect("restore defaultCallees");
    tamper(
        ob_default_path.clone(),
        ob_default.replacen("def defaultCallees", "abbrev defaultCallees", 1),
        "abbrev defaultCallees",
        "via `abbrev`",
    );
    let ob_helper_path = gen_dir.join("Obligations/CrateA/local_helper.lean");
    let ob_helper = read(&ob_helper_path);
    fs::remove_file(&ob_helper_path).expect("delete Obligations module");
    assert_audit_rejects(&check_trusted_py, &crate_a, "deleted Obligations module", "missing Obligations module");
    fs::write(&ob_helper_path, &ob_helper).expect("restore Obligations module");
    let verify_trusted_path = gen_dir.join("Verify/CrateA/trusted_indirect.lean");
    tamper(
        verify_trusted_path.clone(),
        read(&verify_trusted_path).replace("Assumptions.CrateA.trusted_indirect.rust_trusted_contract", "sorry"),
        "trusted surface dropped while the receipt keeps unresolved indirect calls",
        "allow_unresolved_indirect_calls",
    );
    let verify_helper_path = gen_dir.join("Verify/CrateA/local_helper.lean");
    let verify_helper = read(&verify_helper_path);
    fs::remove_file(&verify_helper_path).expect("delete Verify module");
    assert_audit_rejects(&check_trusted_py, &crate_a, "deleted Verify module", "Verify/CrateA/local_helper.lean");
    fs::write(&verify_helper_path, &verify_helper).expect("restore Verify module");

    // Detached `Obligations` claim (`callees := []` while `defaultCallees` stays intact) fails closed.
    let ob_calls_helper_path = gen_dir.join("Obligations/CrateA/calls_local_helper.lean");
    let ob_calls_helper = read(&ob_calls_helper_path);
    tamper(
        ob_calls_helper_path.clone(),
        ob_calls_helper.replacen("callees := defaultCallees", "callees := []", 1),
        "detached Obligations claim callees",
        "overrides claim `callees :=",
    );
    // `[adv ep2-B2]` A claim keeping `body` / `callees` but binding a vacuous `pre` (which
    // `Verify` would prove trivially) fails closed against the generated claim template.
    tamper(
        ob_calls_helper_path.clone(),
        ob_calls_helper.replacen("pre := spec.pre, post := spec.post", "pre := fun _ => False, post := spec.post", 1),
        "vacuous Obligations claim precondition",
        "differs from its generated form",
    );
    // `[adv ep2-A2]` Guillemet-dot spoofing (`«spec.pre»`), guillemet-keyword (`«section»`)
    // root-namespace hijack, unpinned spec-chain tampers below canonical claims (`defaultPre := False`,
    // `sigPre := False`, `rustRequires := fun _ => False`, `defaultSpec` without `(priority := low)`),
    // and tampered `externalSpecCallContract` `extraPost := (fun _ _ => False)` all fail closed!
    tamper(
        ob_calls_helper_path.clone(),
        ob_calls_helper.replacen("pre := spec.pre, post := spec.post", "pre := «spec.pre», post := spec.post", 1),
        "guillemet-dot «spec.pre» spoof in Obligations claim",
        "guillemet",
    );
    tamper(
        ob_calls_helper_path.clone(),
        ob_calls_helper.replacen(
            "def sigPre\n    (typeArgs : Trusted.MirAst.TypeSubst)\n    (args : List Value)\n    (mem : Memory) : Prop :=",
            "def sigPre\n    (typeArgs : Trusted.MirAst.TypeSubst)\n    (args : List Value)\n    (mem : Memory) : Prop := False --",
            1,
        ),
        "vacuous sigPre := False in Obligations",
        "sigPre",
    );
    tamper(
        ob_calls_helper_path.clone(),
        ob_calls_helper.replacen(
            "instance (priority := low) defaultSpec",
            "instance defaultSpec",
            1,
        ),
        "defaultSpec without (priority := low) in Obligations",
        "defaultSpec",
    );
    tamper(
        ob_calls_helper_path.clone(),
        ob_calls_helper.replacen(
            "pre args := And (rustRequires args) (extraPre args)",
            "pre args := False",
            1,
        ),
        "tampered refineSpec pre := False in Obligations",
        "refineSpec",
    );
    let ob_ext_for_tamper = gen_dir.join("Obligations/CrateA/caller_with_external_specs.lean");
    let ob_ext_orig_for_tamper = read(&ob_ext_for_tamper);
    tamper(
        ob_ext_for_tamper,
        ob_ext_orig_for_tamper.replacen(
            "(List.append args (List.cons ret List.nil)))",
            "[])",
            1,
        ),
        "externalSpecCallContract extraPost tampered",
        "externalCallContract_",
    );
    // `[adv ep2-B3]` `defaultPre` may only evaluate the subject's own `requires` companion:
    // pointing it at another function's companion (e.g. one whose predicate is always false)
    // keeps the generated `MirBoolPredicateHolds Mir.<companion>.body args` shape but would make
    // every claim vacuous.
    tamper(
        ob_calls_helper_path.clone(),
        ob_calls_helper.replace(
            "__anodized_fn_requires_calls_local_helper",
            "__anodized_fn_requires_trusted_indirect",
        ),
        "defaultPre evaluating another subject's requires companion",
        "instead of `ContractRole.requires \"crate_a::calls_local_helper\"`",
    );
    // Declarations outside `namespace Obligations.<Item>` can shadow the certificate type
    // that Lean resolves inside `namespace Verify.<Item>` (namespace prefixes win over `open`).
    tamper(
        ob_calls_helper_path.clone(),
        ob_calls_helper.replacen(
            "namespace Obligations.CrateA.calls_local_helper\n",
            "def Verify.CrateA.calls_local_helper.VerificationResult (_ : Nat) : Prop := True\n\
             namespace Obligations.CrateA.calls_local_helper\n",
            1,
        ),
        "Verify certificate hijack declared outside the Obligations namespace",
        "outside `namespace Obligations.CrateA.calls_local_helper`",
    );
    // A callee `Mir/` module declaring a different namespace than its own stem could
    // define another module's `Mir.<X>.body`; every Mir module is bound to its stem.
    let mir_leaf_path = gen_dir.join("Mir/CrateB/inner_leaf.lean");
    let mir_leaf = read(&mir_leaf_path);
    tamper(
        mir_leaf_path.clone(),
        mir_leaf
            .replace("namespace Mir.CrateB.inner_leaf\n", "namespace Mir.CrateB.inner_leaf_spoof\n")
            .replace("end Mir.CrateB.inner_leaf\n", "end Mir.CrateB.inner_leaf_spoof\n"),
        "callee Mir module namespace not bound to its file stem",
        "escapes its own namespace `Mir.CrateB.inner_leaf`",
    );
    // Unlinked `externalSpecCallContract` (dropped from `defaultModularSpec.envAssumed`) fails closed.
    let ob_ext_path = gen_dir.join("Obligations/CrateA/caller_with_external_specs.lean");
    let ob_ext_src = read(&ob_ext_path);
    let unlinked_ob_ext = ob_ext_src.replacen(
        "envAssumed := externalCallContract_",
        "envAssumed := fun _ => True -- externalCallContract_",
        1,
    );
    tamper(
        ob_ext_path,
        unlinked_ob_ext,
        "unlinked externalSpecCallContract in defaultModularSpec.envAssumed",
        "without referencing",
    );
    // `Specs/<Item>.lean` overriding `ModularItemSpec.envAssumed` fails closed when `external_callees` is non-empty.
    let specs_ext_path = crate_a.join("anneal/proofs/Specs/CrateA/caller_with_external_specs.lean");
    fs::create_dir_all(specs_ext_path.parent().unwrap()).expect("create Specs/CrateA");
    let verify_ext_path = gen_dir.join("Verify/CrateA/caller_with_external_specs.lean");
    let verify_ext_orig = read(&verify_ext_path);
    let specs_ext_orig = specs_ext_path.is_file().then(|| read(&specs_ext_path));
    fs::write(
        &specs_ext_path,
        "import Trusted\nnamespace Specs.CrateA.caller_with_external_specs\n\
         instance : ModularItemSpec \"crate_a::caller_with_external_specs\" where\n\
           pre := fun _ => True\n  post := fun _ _ => True\n  envAssumed := fun _ => True\n\
         end Specs.CrateA.caller_with_external_specs\n",
    )
    .expect("write Specs override");
    if !verify_ext_orig.contains("import Specs.CrateA.caller_with_external_specs") {
        fs::write(
            &verify_ext_path,
            verify_ext_orig.replacen(
                "import Trusted\n",
                "import Trusted\nimport Specs.CrateA.caller_with_external_specs\n",
                1,
            ),
        )
        .expect("import Specs in Verify");
    }
    assert_audit_rejects(
        &check_trusted_py,
        &crate_a,
        "Specs ModularItemSpec.envAssumed override with external_callees",
        "backed by neither",
    );
    fs::write(&verify_ext_path, &verify_ext_orig).expect("restore Verify ext");
    match specs_ext_orig {
        Some(orig) => fs::write(&specs_ext_path, orig).expect("restore Specs ext"),
        None => {
            let _ = fs::remove_file(&specs_ext_path);
        }
    }

    // Spec-override smuggling inside `Proof/<Item>.lean` fails closed.
    let proof_calls_helper_path = crate_a.join("anneal/proofs/Proof/CrateA/calls_local_helper.lean");
    fs::create_dir_all(proof_calls_helper_path.parent().unwrap()).expect("create Proof/CrateA");
    let verify_calls_helper_path = gen_dir.join("Verify/CrateA/calls_local_helper.lean");
    let verify_calls_helper_orig = read(&verify_calls_helper_path);
    let proof_calls_helper_orig = proof_calls_helper_path.is_file().then(|| read(&proof_calls_helper_path));
    fs::write(
        &proof_calls_helper_path,
        "import Trusted\nimport Obligations.CrateA.calls_local_helper\n\
         namespace Proof.CrateA.calls_local_helper\n\
         instance : ItemSpec \"crate_a::calls_local_helper\" where\n\
           pre := fun _ => False\n  post := fun _ _ => True\n\
         end Proof.CrateA.calls_local_helper\n",
    )
    .expect("write smuggled Proof override");
    if !verify_calls_helper_orig.contains("import Proof.CrateA.calls_local_helper") {
        fs::write(
            &verify_calls_helper_path,
            verify_calls_helper_orig.replacen(
                "import Trusted\n",
                "import Trusted\nimport Proof.CrateA.calls_local_helper\n",
                1,
            ),
        )
        .expect("import Proof in Verify");
    }
    assert_audit_rejects(
        &check_trusted_py,
        &crate_a,
        "Proof ItemSpec smuggling",
        "specification override instance",
    );
    fs::write(&verify_calls_helper_path, &verify_calls_helper_orig).expect("restore Verify");
    match proof_calls_helper_orig {
        Some(orig) => fs::write(&proof_calls_helper_path, orig).expect("restore Proof"),
        None => {
            let _ = fs::remove_file(&proof_calls_helper_path);
        }
    }

    let restored = run_python_audit(&check_trusted_py, &crate_a);
    assert!(
        restored.status.success(),
        "expected restored workspace to pass:\nstderr: {}",
        String::from_utf8_lossy(&restored.stderr)
    );
    let _ = fs::remove_dir_all(&root);
}
