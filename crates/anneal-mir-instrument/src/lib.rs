// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Untrusted `rustc` driver (`anneal-mir-instrument`) that instruments
//! `optimized_mir` in place so compiled binaries emit real runtime
//! `SwitchInt` branch (`MirObs.event tag`), external call (`MirCallE`), and
//! root return (`_0`) observations for Anneal ITree differential testing.
//!
//! Because this crate lives under `crates/anneal-mir-instrument` (outside
//! `trusted/`), the trusted MIR extractor `anneal-rustc-capture` remains
//! completely untouched.

#![feature(rustc_private)]

extern crate rustc_abi;
extern crate rustc_ast;
extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_parse;
extern crate rustc_session;
extern crate rustc_span;
extern crate rustc_type_ir;

use std::env;
use std::path::Path;
use std::process::{Command, ExitCode};

use rustc_abi::{FieldsShape, HasDataLayout, Size, Variants};
use rustc_ast::ItemKind;
use rustc_driver::{Callbacks, Compilation};
use rustc_hir::def::DefKind;
use rustc_hir::def_id::{DefId, LOCAL_CRATE, LocalDefId};
use rustc_interface::interface;
use rustc_middle::mir::interpret::Scalar;
use rustc_middle::mir::{
    BasicBlock, BasicBlockData, BinOp, Body, CallSource, CastKind, Const, ConstOperand, ConstValue,
    Local, LocalDecl, Mutability, Operand, Place, RawPtrKind, Rvalue, SourceInfo, Statement,
    StatementKind, SwitchTargets, Terminator, TerminatorKind, UnwindAction, WithRetag,
};
use rustc_middle::ty::layout::{LayoutCx, TyAndLayout};
use rustc_middle::ty::{IntTy, ScalarInt, Ty, TyCtxt, TyKind, TypingEnv, UintTy};
use rustc_middle::util::Providers;
use rustc_parse::lexer::StripTokens;
use rustc_parse::parser::{AllowConstBlockItems, ForceCollect};
use rustc_session::Session;
use rustc_span::{DUMMY_SP, FileName, Spanned};
use rustc_type_ir::TypeVisitableExt;

/// Environment variable that, when set to `"1"`, leaves `rustc`'s default
/// `-Zmir-opt-level` unchanged at `-C opt-level=2` instead of pinning
/// `-Zmir-opt-level=1 -Coverflow-checks=on`.
pub const RAW_MIR_OPTS_ENV: &str = "ANNEAL_MIR_INSTRUMENT_RAW_MIR_OPTS";

/// Sentinel token returned by `__anneal_mir_rt_call_begin` when an
/// `EnvSchedule::ReturnBytes` entry wrote the scheduled return value directly
/// to the destination local and the underlying callee body should be skipped.
pub const MIR_CALL_TOKEN_SCHEDULED_RETURN: u128 = u32::MAX as u128;

#[derive(Clone, Copy)]
struct RuntimeHookDefs {
    branch: DefId,
    push_arg: DefId,
    call_begin: DefId,
    call_end_normal: DefId,
    ret: DefId,
}

fn find_runtime_hooks(tcx: TyCtxt<'_>) -> Option<RuntimeHookDefs> {
    let mut branch = None;
    let mut push_arg = None;
    let mut call_begin = None;
    let mut call_end_normal = None;
    let mut ret = None;

    for local_id in tcx.mir_keys(()) {
        let def_id = local_id.to_def_id();
        if tcx.def_kind(def_id) != DefKind::Fn {
            continue;
        }
        let path = tcx.def_path_str(def_id);
        if path.ends_with("__anneal_mir_rt_hooks::branch") {
            branch = Some(def_id);
        } else if path.ends_with("__anneal_mir_rt_hooks::push_arg") {
            push_arg = Some(def_id);
        } else if path.ends_with("__anneal_mir_rt_hooks::call_begin") {
            call_begin = Some(def_id);
        } else if path.ends_with("__anneal_mir_rt_hooks::call_end_normal") {
            call_end_normal = Some(def_id);
        } else if path.ends_with("__anneal_mir_rt_hooks::ret") {
            ret = Some(def_id);
        }
    }

    Some(RuntimeHookDefs {
        branch: branch?,
        push_arg: push_arg?,
        call_begin: call_begin?,
        call_end_normal: call_end_normal?,
        ret: ret?,
    })
}

fn canonical_def_path(tcx: TyCtxt<'_>, def_id: DefId) -> String {
    let raw = tcx.def_path_str(def_id);
    if def_id.is_local() {
        let crate_name = tcx.crate_name(LOCAL_CRATE).to_string();
        if raw.is_empty() {
            crate_name
        } else if raw.starts_with(&format!("{crate_name}::")) {
            raw
        } else {
            format!("{crate_name}::{raw}")
        }
    } else {
        raw
    }
}

/// Computes a 64-bit byte-initialization bitmask for `layout` where bit `i`
/// (`0 <= i < 64`) is `1` iff byte offset `i` lies inside a non-padding scalar
/// field, and `0` at inter-field or trailing struct/tuple/enum padding offsets.
fn compute_layout_mask<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: TypingEnv<'tcx>,
    layout: TyAndLayout<'tcx>,
) -> u64 {
    let size = layout.size.bytes_usize();
    if size == 0 {
        return 0;
    }
    let layout_cx = LayoutCx::new(tcx, typing_env);
    let full_mask = |sz: usize| -> u64 {
        if sz >= 64 {
            u64::MAX
        } else {
            (1u64 << sz) - 1
        }
    };
    match layout.ty.kind() {
        TyKind::Bool
        | TyKind::Char
        | TyKind::Int(_)
        | TyKind::Uint(_)
        | TyKind::Float(_)
        | TyKind::Ref(..)
        | TyKind::RawPtr(..)
        | TyKind::FnPtr(..) => full_mask(size),
        TyKind::Tuple(_) | TyKind::Adt(_, _) | TyKind::Array(_, _) => {
            if let Variants::Multiple { tag, tag_field, .. } = &layout.variants {
                let tag_off = layout.fields.offset(tag_field.as_usize()).bytes_usize();
                let tag_sz = tag.size(&tcx).bytes_usize();
                let mut mask = if tag_off < 64 {
                    full_mask(tag_sz) << tag_off
                } else {
                    0
                };
                for i in 0..layout.fields.count() {
                    let off = layout.fields.offset(i).bytes_usize();
                    let fl = layout.field(&layout_cx, i);
                    let fm = compute_layout_mask(tcx, typing_env, fl);
                    if off < 64 {
                        mask |= fm << off;
                    }
                }
                mask
            } else {
                match &layout.fields {
                    FieldsShape::Primitive => full_mask(size),
                    FieldsShape::Array { stride, count } => {
                        let mut mask = 0u64;
                        let elem_layout = layout.field(&layout_cx, 0);
                        let em = compute_layout_mask(tcx, typing_env, elem_layout);
                        let st = stride.bytes_usize();
                        for idx in 0..(*count as usize) {
                            let off = idx * st;
                            if off < 64 {
                                mask |= em << off;
                            }
                        }
                        mask
                    }
                    FieldsShape::Arbitrary { .. } => {
                        let mut mask = 0u64;
                        for i in 0..layout.fields.count() {
                            let off = layout.fields.offset(i).bytes_usize();
                            let fl = layout.field(&layout_cx, i);
                            let fm = compute_layout_mask(tcx, typing_env, fl);
                            if off < 64 {
                                mask |= fm << off;
                            }
                        }
                        mask
                    }
                    FieldsShape::Union(_) => full_mask(size),
                }
            }
        }
        _ => full_mask(size),
    }
}

fn layout_size_and_mask<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: TypingEnv<'tcx>,
    ty: Ty<'tcx>,
) -> Option<(usize, u64)> {
    if ty.has_non_region_param() {
        return None;
    }
    let layout = tcx.layout_of(typing_env.as_query_input(ty)).ok()?;
    let size = layout.size.bytes_usize();
    let mask = compute_layout_mask(tcx, typing_env, layout);
    Some((size, mask))
}

fn new_temp_local<'tcx>(body: &mut Body<'tcx>, ty: Ty<'tcx>, mutability: Mutability) -> Local {
    let mut decl = LocalDecl::with_source_info(ty, SourceInfo::outermost(body.span));
    decl.mutability = mutability;
    body.local_decls.push(decl)
}

fn const_u64<'tcx>(tcx: TyCtxt<'tcx>, val: u64) -> Operand<'tcx> {
    let si = ScalarInt::try_from_uint(u128::from(val), Size::from_bytes(8)).unwrap();
    Operand::const_from_scalar(tcx, tcx.types.u64, Scalar::Int(si), DUMMY_SP)
}

fn const_usize<'tcx>(tcx: TyCtxt<'tcx>, val: usize) -> Operand<'tcx> {
    let ptr_size = tcx.data_layout().pointer_size();
    let si = ScalarInt::try_from_uint(val as u128, ptr_size).unwrap();
    Operand::const_from_scalar(tcx, tcx.types.usize, Scalar::Int(si), DUMMY_SP)
}

fn const_static_str<'tcx>(tcx: TyCtxt<'tcx>, s: &str) -> Operand<'tcx> {
    let alloc_id = tcx.allocate_bytes_dedup(s.as_bytes().to_vec(), 0);
    let str_ty = Ty::new_static_str(tcx);
    let const_val = ConstValue::Slice {
        alloc_id,
        meta: s.len() as u64,
    };
    Operand::Constant(Box::new(ConstOperand {
        span: DUMMY_SP,
        user_ty: None,
        const_: Const::Val(const_val, str_ty),
    }))
}

fn should_skip_instrumenting_fn(raw_path: &str) -> bool {
    raw_path == "main"
        || raw_path.starts_with("main::")
        || raw_path.contains("__anneal_mir_rt_hooks")
        || raw_path.contains("trace_observer")
        || raw_path.contains("__anneal_no_instrument")
}

fn should_skip_instrumenting_call(tcx: TyCtxt<'_>, callee_def_id: DefId, callee_path: &str) -> bool {
    if tcx.is_intrinsic(callee_def_id, tcx.item_name(callee_def_id)) {
        return true;
    }
    let krate = tcx.crate_name(callee_def_id.krate);
    let krate_str = krate.as_str();
    if matches!(
        krate_str,
        "core"
            | "std"
            | "alloc"
            | "proc_macro"
            | "test"
            | "compiler_builtins"
            | "cargo_anneal"
            | "anneal_trace"
    ) {
        return true;
    }
    callee_path.contains("__anneal_mir_rt_hooks")
        || callee_path.contains("trace_observer")
        || callee_path.contains("anodized::__")
        || callee_path.ends_with("::transmute")
        || callee_path.ends_with("::add_with_overflow")
        || callee_path.ends_with("::exact_div")
}

fn instrumented_optimized_mir<'tcx>(tcx: TyCtxt<'tcx>, did: LocalDefId) -> &'tcx Body<'tcx> {
    let orig = (rustc_interface::DEFAULT_QUERY_PROVIDERS.queries.optimized_mir)(tcx, did);
    let def_id = did.to_def_id();
    if !matches!(tcx.def_kind(def_id), DefKind::Fn | DefKind::AssocFn) {
        return orig;
    }
    let raw_path = tcx.def_path_str(def_id);
    if should_skip_instrumenting_fn(&raw_path) {
        return orig;
    }
    let Some(hooks) = find_runtime_hooks(tcx) else {
        return orig;
    };

    let mut body = orig.clone();
    let typing_env = body.typing_env(tcx);
    let fn_def_path = canonical_def_path(tcx, def_id);
    let src_info = SourceInfo::outermost(body.span);
    let ptr_const_u8_ty = Ty::new_imm_ptr(tcx, tcx.types.u8);
    let ptr_mut_u8_ty = Ty::new_mut_ptr(tcx, tcx.types.u8);

    let orig_len = body.basic_blocks.len();
    for bb_idx in 0..orig_len {
        let bb = BasicBlock::from_usize(bb_idx);
        if body.basic_blocks[bb].is_cleanup {
            continue;
        }
        let term = body.basic_blocks[bb].terminator().clone();
        match term.kind {
            TerminatorKind::SwitchInt { discr, targets } => {
                let discr_ty = discr.ty(&body.local_decls, tcx);
                let tmp_discr = new_temp_local(&mut body, discr_ty, Mutability::Mut);
                body.basic_blocks_mut()[bb].statements.push(Statement::new(
                    src_info,
                    StatementKind::Assign(Box::new((
                        Place::from(tmp_discr),
                        Rvalue::Use(discr, WithRetag::No),
                    ))),
                ));
                let tmp_lo = new_temp_local(&mut body, tcx.types.u64, Mutability::Mut);
                let tmp_hi = new_temp_local(&mut body, tcx.types.u64, Mutability::Mut);
                let discr_copy = Operand::Copy(Place::from(tmp_discr));
                match discr_ty.kind() {
                    TyKind::Int(int_ty) => {
                        let uint_ty = match int_ty {
                            IntTy::I8 => tcx.types.u8,
                            IntTy::I16 => tcx.types.u16,
                            IntTy::I32 => tcx.types.u32,
                            IntTy::I64 => tcx.types.u64,
                            IntTy::Isize => tcx.types.usize,
                            IntTy::I128 => tcx.types.u128,
                        };
                        let tmp_u = new_temp_local(&mut body, uint_ty, Mutability::Mut);
                        body.basic_blocks_mut()[bb].statements.push(Statement::new(
                            src_info,
                            StatementKind::Assign(Box::new((
                                Place::from(tmp_u),
                                Rvalue::Cast(CastKind::IntToInt, discr_copy, uint_ty),
                            ))),
                        ));
                        body.basic_blocks_mut()[bb].statements.push(Statement::new(
                            src_info,
                            StatementKind::Assign(Box::new((
                                Place::from(tmp_lo),
                                Rvalue::Cast(
                                    CastKind::IntToInt,
                                    Operand::Copy(Place::from(tmp_u)),
                                    tcx.types.u64,
                                ),
                            ))),
                        ));
                        if matches!(int_ty, IntTy::I128) {
                            let tmp_shifted =
                                new_temp_local(&mut body, tcx.types.u128, Mutability::Mut);
                            body.basic_blocks_mut()[bb].statements.push(Statement::new(
                                src_info,
                                StatementKind::Assign(Box::new((
                                    Place::from(tmp_shifted),
                                    Rvalue::BinaryOp(
                                        BinOp::Shr,
                                        Box::new((
                                            Operand::Copy(Place::from(tmp_u)),
                                            const_u64(tcx, 64),
                                        )),
                                    ),
                                ))),
                            ));
                            body.basic_blocks_mut()[bb].statements.push(Statement::new(
                                src_info,
                                StatementKind::Assign(Box::new((
                                    Place::from(tmp_hi),
                                    Rvalue::Cast(
                                        CastKind::IntToInt,
                                        Operand::Copy(Place::from(tmp_shifted)),
                                        tcx.types.u64,
                                    ),
                                ))),
                            ));
                        } else {
                            body.basic_blocks_mut()[bb].statements.push(Statement::new(
                                src_info,
                                StatementKind::Assign(Box::new((
                                    Place::from(tmp_hi),
                                    Rvalue::Use(const_u64(tcx, 0), WithRetag::No),
                                ))),
                            ));
                        }
                    }
                    TyKind::Uint(UintTy::U128) => {
                        body.basic_blocks_mut()[bb].statements.push(Statement::new(
                            src_info,
                            StatementKind::Assign(Box::new((
                                Place::from(tmp_lo),
                                Rvalue::Cast(
                                    CastKind::IntToInt,
                                    discr_copy.clone(),
                                    tcx.types.u64,
                                ),
                            ))),
                        ));
                        let tmp_shifted =
                            new_temp_local(&mut body, tcx.types.u128, Mutability::Mut);
                        body.basic_blocks_mut()[bb].statements.push(Statement::new(
                            src_info,
                            StatementKind::Assign(Box::new((
                                Place::from(tmp_shifted),
                                Rvalue::BinaryOp(
                                    BinOp::Shr,
                                    Box::new((discr_copy, const_u64(tcx, 64))),
                                ),
                            ))),
                        ));
                        body.basic_blocks_mut()[bb].statements.push(Statement::new(
                            src_info,
                            StatementKind::Assign(Box::new((
                                Place::from(tmp_hi),
                                Rvalue::Cast(
                                    CastKind::IntToInt,
                                    Operand::Copy(Place::from(tmp_shifted)),
                                    tcx.types.u64,
                                ),
                            ))),
                        ));
                    }
                    _ => {
                        body.basic_blocks_mut()[bb].statements.push(Statement::new(
                            src_info,
                            StatementKind::Assign(Box::new((
                                Place::from(tmp_lo),
                                Rvalue::Cast(CastKind::IntToInt, discr_copy, tcx.types.u64),
                            ))),
                        ));
                        body.basic_blocks_mut()[bb].statements.push(Statement::new(
                            src_info,
                            StatementKind::Assign(Box::new((
                                Place::from(tmp_hi),
                                Rvalue::Use(const_u64(tcx, 0), WithRetag::No),
                            ))),
                        ));
                    }
                }
                let tmp_unit = new_temp_local(&mut body, tcx.types.unit, Mutability::Mut);
                let cont_bb_data = BasicBlockData::new(
                    Some(Terminator {
                        source_info: term.source_info,
                        kind: TerminatorKind::SwitchInt {
                            discr: Operand::Copy(Place::from(tmp_discr)),
                            targets,
                        },
                    }),
                    false,
                );
                let cont_bb = body.basic_blocks_mut().push(cont_bb_data);
                body.basic_blocks_mut()[bb].terminator = Some(Terminator {
                    source_info: term.source_info,
                    kind: TerminatorKind::Call {
                        func: Operand::function_handle(tcx, hooks.branch, [], DUMMY_SP),
                        args: Box::new([
                            Spanned {
                                node: Operand::Copy(Place::from(tmp_lo)),
                                span: DUMMY_SP,
                            },
                            Spanned {
                                node: Operand::Copy(Place::from(tmp_hi)),
                                span: DUMMY_SP,
                            },
                        ]),
                        destination: Place::from(tmp_unit),
                        target: Some(cont_bb),
                        unwind: UnwindAction::Continue,
                        call_source: CallSource::Misc,
                        fn_span: DUMMY_SP,
                    },
                });
            }
            TerminatorKind::Return => {
                let ret_ty = body.local_decls[Local::from_usize(0)].ty;
                let Some((ret_size, ret_mask)) = layout_size_and_mask(tcx, typing_env, ret_ty)
                else {
                    continue;
                };
                let tmp_ret_ptr = new_temp_local(&mut body, ptr_const_u8_ty, Mutability::Mut);
                if ret_size == 0 {
                    body.basic_blocks_mut()[bb].statements.push(Statement::new(
                        src_info,
                        StatementKind::Assign(Box::new((
                            Place::from(tmp_ret_ptr),
                            Rvalue::Cast(
                                CastKind::PointerWithExposedProvenance,
                                const_usize(tcx, 0),
                                ptr_const_u8_ty,
                            ),
                        ))),
                    ));
                } else {
                    let raw_ty = Ty::new_imm_ptr(tcx, ret_ty);
                    let tmp_raw = new_temp_local(&mut body, raw_ty, Mutability::Mut);
                    body.basic_blocks_mut()[bb].statements.push(Statement::new(
                        src_info,
                        StatementKind::Assign(Box::new((
                            Place::from(tmp_raw),
                            Rvalue::RawPtr(RawPtrKind::Const, Place::from(Local::from_usize(0))),
                        ))),
                    ));
                    body.basic_blocks_mut()[bb].statements.push(Statement::new(
                        src_info,
                        StatementKind::Assign(Box::new((
                            Place::from(tmp_ret_ptr),
                            Rvalue::Cast(
                                CastKind::PtrToPtr,
                                Operand::Copy(Place::from(tmp_raw)),
                                ptr_const_u8_ty,
                            ),
                        ))),
                    ));
                }
                let tmp_unit = new_temp_local(&mut body, tcx.types.unit, Mutability::Mut);
                let cont_bb = body.basic_blocks_mut().push(BasicBlockData::new(
                    Some(Terminator {
                        source_info: term.source_info,
                        kind: TerminatorKind::Return,
                    }),
                    false,
                ));
                body.basic_blocks_mut()[bb].terminator = Some(Terminator {
                    source_info: term.source_info,
                    kind: TerminatorKind::Call {
                        func: Operand::function_handle(tcx, hooks.ret, [], DUMMY_SP),
                        args: Box::new([
                            Spanned {
                                node: const_static_str(tcx, &fn_def_path),
                                span: DUMMY_SP,
                            },
                            Spanned {
                                node: Operand::Copy(Place::from(tmp_ret_ptr)),
                                span: DUMMY_SP,
                            },
                            Spanned {
                                node: const_usize(tcx, ret_size),
                                span: DUMMY_SP,
                            },
                            Spanned {
                                node: const_u64(tcx, ret_mask),
                                span: DUMMY_SP,
                            },
                        ]),
                        destination: Place::from(tmp_unit),
                        target: Some(cont_bb),
                        unwind: UnwindAction::Continue,
                        call_source: CallSource::Misc,
                        fn_span: DUMMY_SP,
                    },
                });
            }
            TerminatorKind::Call {
                func,
                args,
                destination,
                target: Some(target_bb),
                unwind,
                call_source,
                fn_span,
            } => {
                let Some((callee_def_id, substs)) = func.const_fn_def() else {
                    continue;
                };
                if substs.has_non_region_param() {
                    continue;
                }
                let callee_def_path = canonical_def_path(tcx, callee_def_id);
                if should_skip_instrumenting_call(tcx, callee_def_id, &callee_def_path) {
                    continue;
                }
                let dst_ty = destination.ty(&body.local_decls, tcx).ty;
                let Some((dst_size, dst_mask)) = layout_size_and_mask(tcx, typing_env, dst_ty)
                else {
                    continue;
                };

                let mut arg_infos = Vec::with_capacity(args.len());
                let mut all_args_ok = true;
                for sp_arg in args.iter() {
                    let arg_ty = sp_arg.node.ty(&body.local_decls, tcx);
                    if let Some((sz, msk)) = layout_size_and_mask(tcx, typing_env, arg_ty) {
                        arg_infos.push((sp_arg.node.clone(), sp_arg.span, arg_ty, sz, msk));
                    } else {
                        all_args_ok = false;
                        break;
                    }
                }
                if !all_args_ok {
                    continue;
                }

                let mut tmp_arg_locals = Vec::with_capacity(arg_infos.len());
                let mut tmp_arg_ptrs = Vec::with_capacity(arg_infos.len());
                for (arg_op, _span, arg_ty, arg_size, arg_mask) in &arg_infos {
                    let tmp_arg = new_temp_local(&mut body, *arg_ty, Mutability::Mut);
                    body.basic_blocks_mut()[bb].statements.push(Statement::new(
                        src_info,
                        StatementKind::Assign(Box::new((
                            Place::from(tmp_arg),
                            Rvalue::Use(arg_op.clone(), WithRetag::No),
                        ))),
                    ));
                    let tmp_ptr = new_temp_local(&mut body, ptr_const_u8_ty, Mutability::Mut);
                    if *arg_size == 0 {
                        body.basic_blocks_mut()[bb].statements.push(Statement::new(
                            src_info,
                            StatementKind::Assign(Box::new((
                                Place::from(tmp_ptr),
                                Rvalue::Cast(
                                    CastKind::PointerWithExposedProvenance,
                                    const_usize(tcx, 0),
                                    ptr_const_u8_ty,
                                ),
                            ))),
                        ));
                    } else {
                        let raw_ty = Ty::new_imm_ptr(tcx, *arg_ty);
                        let tmp_raw = new_temp_local(&mut body, raw_ty, Mutability::Mut);
                        body.basic_blocks_mut()[bb].statements.push(Statement::new(
                            src_info,
                            StatementKind::Assign(Box::new((
                                Place::from(tmp_raw),
                                Rvalue::RawPtr(RawPtrKind::Const, Place::from(tmp_arg)),
                            ))),
                        ));
                        body.basic_blocks_mut()[bb].statements.push(Statement::new(
                            src_info,
                            StatementKind::Assign(Box::new((
                                Place::from(tmp_ptr),
                                Rvalue::Cast(
                                    CastKind::PtrToPtr,
                                    Operand::Copy(Place::from(tmp_raw)),
                                    ptr_const_u8_ty,
                                ),
                            ))),
                        ));
                    }
                    tmp_arg_locals.push(tmp_arg);
                    tmp_arg_ptrs.push((tmp_ptr, *arg_size, *arg_mask));
                }

                let bb_assign_dst = body.basic_blocks_mut().push(BasicBlockData::new(None, false));
                let bb_call_end = body.basic_blocks_mut().push(BasicBlockData::new(None, false));
                let bb_real_call = body.basic_blocks_mut().push(BasicBlockData::new(None, false));
                let bb_check_sched = body.basic_blocks_mut().push(BasicBlockData::new(None, false));
                let bb_call_begin = body.basic_blocks_mut().push(BasicBlockData::new(None, false));

                let mut push_bbs = Vec::with_capacity(tmp_arg_ptrs.len());
                for i in 0..tmp_arg_ptrs.len() {
                    if i == 0 {
                        push_bbs.push(bb);
                    } else {
                        push_bbs.push(body.basic_blocks_mut().push(BasicBlockData::new(None, false)));
                    }
                }

                if tmp_arg_ptrs.is_empty() {
                    body.basic_blocks_mut()[bb].terminator = Some(Terminator {
                        source_info: term.source_info,
                        kind: TerminatorKind::Goto {
                            target: bb_call_begin,
                        },
                    });
                } else {
                    for i in 0..tmp_arg_ptrs.len() {
                        let cur_bb = push_bbs[i];
                        let next_bb = if i + 1 < push_bbs.len() {
                            push_bbs[i + 1]
                        } else {
                            bb_call_begin
                        };
                        let (tmp_ptr, arg_sz, arg_msk) = tmp_arg_ptrs[i];
                        let tmp_unit = new_temp_local(&mut body, tcx.types.unit, Mutability::Mut);
                        body.basic_blocks_mut()[cur_bb].terminator = Some(Terminator {
                            source_info: term.source_info,
                            kind: TerminatorKind::Call {
                                func: Operand::function_handle(tcx, hooks.push_arg, [], DUMMY_SP),
                                args: Box::new([
                                    Spanned {
                                        node: Operand::Copy(Place::from(tmp_ptr)),
                                        span: DUMMY_SP,
                                    },
                                    Spanned {
                                        node: const_usize(tcx, arg_sz),
                                        span: DUMMY_SP,
                                    },
                                    Spanned {
                                        node: const_u64(tcx, arg_msk),
                                        span: DUMMY_SP,
                                    },
                                ]),
                                destination: Place::from(tmp_unit),
                                target: Some(next_bb),
                                unwind: UnwindAction::Continue,
                                call_source: CallSource::Misc,
                                fn_span: DUMMY_SP,
                            },
                        });
                    }
                }

                let tmp_dst = new_temp_local(&mut body, dst_ty, Mutability::Mut);
                let tmp_dst_ptr = new_temp_local(&mut body, ptr_mut_u8_ty, Mutability::Mut);
                if dst_size == 0 {
                    body.basic_blocks_mut()[bb_call_begin]
                        .statements
                        .push(Statement::new(
                            src_info,
                            StatementKind::Assign(Box::new((
                                Place::from(tmp_dst_ptr),
                                Rvalue::Cast(
                                    CastKind::PointerWithExposedProvenance,
                                    const_usize(tcx, 0),
                                    ptr_mut_u8_ty,
                                ),
                            ))),
                        ));
                } else {
                    let raw_dst_ty = Ty::new_mut_ptr(tcx, dst_ty);
                    let tmp_raw_dst = new_temp_local(&mut body, raw_dst_ty, Mutability::Mut);
                    body.basic_blocks_mut()[bb_call_begin]
                        .statements
                        .push(Statement::new(
                            src_info,
                            StatementKind::Assign(Box::new((
                                Place::from(tmp_raw_dst),
                                Rvalue::RawPtr(RawPtrKind::Mut, Place::from(tmp_dst)),
                            ))),
                        ));
                    body.basic_blocks_mut()[bb_call_begin]
                        .statements
                        .push(Statement::new(
                            src_info,
                            StatementKind::Assign(Box::new((
                                Place::from(tmp_dst_ptr),
                                Rvalue::Cast(
                                    CastKind::PtrToPtr,
                                    Operand::Copy(Place::from(tmp_raw_dst)),
                                    ptr_mut_u8_ty,
                                ),
                            ))),
                        ));
                }

                let tmp_token = new_temp_local(&mut body, tcx.types.u32, Mutability::Mut);
                body.basic_blocks_mut()[bb_call_begin].terminator = Some(Terminator {
                    source_info: term.source_info,
                    kind: TerminatorKind::Call {
                        func: Operand::function_handle(tcx, hooks.call_begin, [], DUMMY_SP),
                        args: Box::new([
                            Spanned {
                                node: const_static_str(tcx, &callee_def_path),
                                span: DUMMY_SP,
                            },
                            Spanned {
                                node: Operand::Copy(Place::from(tmp_dst_ptr)),
                                span: DUMMY_SP,
                            },
                            Spanned {
                                node: const_usize(tcx, dst_size),
                                span: DUMMY_SP,
                            },
                            Spanned {
                                node: const_u64(tcx, dst_mask),
                                span: DUMMY_SP,
                            },
                        ]),
                        destination: Place::from(tmp_token),
                        target: Some(bb_check_sched),
                        unwind,
                        call_source: CallSource::Misc,
                        fn_span: DUMMY_SP,
                    },
                });

                let sched_targets = SwitchTargets::new(
                    std::iter::once((MIR_CALL_TOKEN_SCHEDULED_RETURN, bb_assign_dst)),
                    bb_real_call,
                );
                body.basic_blocks_mut()[bb_check_sched].terminator = Some(Terminator {
                    source_info: term.source_info,
                    kind: TerminatorKind::SwitchInt {
                        discr: Operand::Copy(Place::from(tmp_token)),
                        targets: sched_targets,
                    },
                });

                let new_call_args: Vec<Spanned<Operand<'tcx>>> = tmp_arg_locals
                    .iter()
                    .zip(arg_infos.iter())
                    .map(|(&loc, (_, sp, _, _, _))| Spanned {
                        node: Operand::Move(Place::from(loc)),
                        span: *sp,
                    })
                    .collect();
                body.basic_blocks_mut()[bb_real_call].terminator = Some(Terminator {
                    source_info: term.source_info,
                    kind: TerminatorKind::Call {
                        func,
                        args: new_call_args.into_boxed_slice(),
                        destination: Place::from(tmp_dst),
                        target: Some(bb_call_end),
                        unwind,
                        call_source,
                        fn_span,
                    },
                });

                let tmp_unit_end = new_temp_local(&mut body, tcx.types.unit, Mutability::Mut);
                body.basic_blocks_mut()[bb_call_end].terminator = Some(Terminator {
                    source_info: term.source_info,
                    kind: TerminatorKind::Call {
                        func: Operand::function_handle(tcx, hooks.call_end_normal, [], DUMMY_SP),
                        args: Box::new([
                            Spanned {
                                node: Operand::Copy(Place::from(tmp_token)),
                                span: DUMMY_SP,
                            },
                            Spanned {
                                node: Operand::Copy(Place::from(tmp_dst_ptr)),
                                span: DUMMY_SP,
                            },
                            Spanned {
                                node: const_usize(tcx, dst_size),
                                span: DUMMY_SP,
                            },
                            Spanned {
                                node: const_u64(tcx, dst_mask),
                                span: DUMMY_SP,
                            },
                        ]),
                        destination: Place::from(tmp_unit_end),
                        target: Some(bb_assign_dst),
                        unwind: UnwindAction::Continue,
                        call_source: CallSource::Misc,
                        fn_span: DUMMY_SP,
                    },
                });

                body.basic_blocks_mut()[bb_assign_dst]
                    .statements
                    .push(Statement::new(
                        src_info,
                        StatementKind::Assign(Box::new((
                            destination,
                            Rvalue::Use(Operand::Move(Place::from(tmp_dst)), WithRetag::No),
                        ))),
                    ));
                body.basic_blocks_mut()[bb_assign_dst].terminator = Some(Terminator {
                    source_info: term.source_info,
                    kind: TerminatorKind::Goto { target: target_bb },
                });
            }
            _ => {}
        }
    }

    tcx.arena.alloc(body)
}

fn override_queries(_session: &Session, providers: &mut Providers) {
    providers.queries.optimized_mir = instrumented_optimized_mir;
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum HookDelegationMode {
    CrateTraceObserver,
    ExternCargoAnneal,
    NoOpStandalone,
}

fn render_injected_hooks_module(mode: HookDelegationMode) -> &'static str {
    match mode {
        HookDelegationMode::CrateTraceObserver => {
            r#"
#[doc(hidden)]
#[allow(dead_code, unused_variables, non_snake_case)]
pub mod __anneal_mir_rt_hooks {
    #[inline(never)]
    pub fn branch(tag_lo: u64, tag_hi: u64) {
        crate::trace_observer::__anneal_mir_rt_branch(tag_lo, tag_hi);
    }
    #[inline(never)]
    pub fn push_arg(ptr: *const u8, len: usize, init_mask: u64) {
        crate::trace_observer::__anneal_mir_rt_push_arg(ptr, len, init_mask);
    }
    #[inline(never)]
    pub fn call_begin(def_path: &'static str, dst_ptr: *mut u8, dst_len: usize, dst_mask: u64) -> u32 {
        crate::trace_observer::__anneal_mir_rt_call_begin(def_path, dst_ptr, dst_len, dst_mask)
    }
    #[inline(never)]
    pub fn call_end_normal(token: u32, ret_ptr: *mut u8, ret_len: usize, init_mask: u64) {
        crate::trace_observer::__anneal_mir_rt_call_end_normal(token, ret_ptr, ret_len, init_mask);
    }
    #[inline(never)]
    pub fn ret(def_path: &'static str, ret_ptr: *const u8, ret_len: usize, init_mask: u64) {
        crate::trace_observer::__anneal_mir_rt_ret(def_path, ret_ptr, ret_len, init_mask);
    }
}
"#
        }
        HookDelegationMode::ExternCargoAnneal => {
            r#"
#[doc(hidden)]
#[allow(dead_code, unused_variables, non_snake_case)]
pub mod __anneal_mir_rt_hooks {
    #[inline(never)]
    pub fn branch(tag_lo: u64, tag_hi: u64) {
        ::cargo_anneal::trace_observer::__anneal_mir_rt_branch(tag_lo, tag_hi);
    }
    #[inline(never)]
    pub fn push_arg(ptr: *const u8, len: usize, init_mask: u64) {
        ::cargo_anneal::trace_observer::__anneal_mir_rt_push_arg(ptr, len, init_mask);
    }
    #[inline(never)]
    pub fn call_begin(def_path: &'static str, dst_ptr: *mut u8, dst_len: usize, dst_mask: u64) -> u32 {
        ::cargo_anneal::trace_observer::__anneal_mir_rt_call_begin(def_path, dst_ptr, dst_len, dst_mask)
    }
    #[inline(never)]
    pub fn call_end_normal(token: u32, ret_ptr: *mut u8, ret_len: usize, init_mask: u64) {
        ::cargo_anneal::trace_observer::__anneal_mir_rt_call_end_normal(token, ret_ptr, ret_len, init_mask);
    }
    #[inline(never)]
    pub fn ret(def_path: &'static str, ret_ptr: *const u8, ret_len: usize, init_mask: u64) {
        ::cargo_anneal::trace_observer::__anneal_mir_rt_ret(def_path, ret_ptr, ret_len, init_mask);
    }
}
"#
        }
        HookDelegationMode::NoOpStandalone => {
            r#"
#[doc(hidden)]
#[allow(dead_code, unused_variables, non_snake_case)]
pub mod __anneal_mir_rt_hooks {
    #[inline(never)]
    pub fn branch(_tag_lo: u64, _tag_hi: u64) {}
    #[inline(never)]
    pub fn push_arg(_ptr: *const u8, _len: usize, _init_mask: u64) {}
    #[inline(never)]
    pub fn call_begin(_def_path: &'static str, _dst_ptr: *mut u8, _dst_len: usize, _dst_mask: u64) -> u32 {
        0
    }
    #[inline(never)]
    pub fn call_end_normal(_token: u32, _ret_ptr: *mut u8, _ret_len: usize, _init_mask: u64) {}
    #[inline(never)]
    pub fn ret(_def_path: &'static str, _ret_ptr: *const u8, _ret_len: usize, _init_mask: u64) {}
}
"#
        }
    }
}

struct InstrumentCallbacks {
    has_extern_cargo_anneal: bool,
}

impl Callbacks for InstrumentCallbacks {
    fn config(&mut self, config: &mut interface::Config) {
        config.override_queries = Some(override_queries);
    }

    fn after_crate_root_parsing(
        &mut self,
        compiler: &interface::Compiler,
        krate: &mut rustc_ast::Crate,
    ) -> Compilation {
        let already_injected = krate.items.iter().any(|item| {
            matches!(&item.kind, ItemKind::Mod(_, ident, _) if ident.name.as_str() == "__anneal_mir_rt_hooks")
        });
        if already_injected {
            return Compilation::Continue;
        }

        let has_crate_trace_observer = krate.items.iter().any(|item| {
            matches!(&item.kind, ItemKind::Mod(_, ident, _) if ident.name.as_str() == "trace_observer")
        });
        let mode = if has_crate_trace_observer {
            HookDelegationMode::CrateTraceObserver
        } else if self.has_extern_cargo_anneal {
            HookDelegationMode::ExternCargoAnneal
        } else {
            HookDelegationMode::NoOpStandalone
        };

        let rt_src = render_injected_hooks_module(mode);
        let psess = &compiler.sess.psess;
        let mut parser = rustc_parse::new_parser_from_source_str(
            psess,
            FileName::Custom("anneal_mir_rt_hooks.rs".to_string()),
            rt_src.to_string(),
            StripTokens::Nothing,
        )
        .expect("create parser for __anneal_mir_rt_hooks");
        let item = parser
            .parse_item(ForceCollect::No, AllowConstBlockItems::Yes)
            .expect("parse __anneal_mir_rt_hooks module")
            .expect("__anneal_mir_rt_hooks module item must exist");
        krate.items.push(item);
        Compilation::Continue
    }
}

struct PassthroughCallbacks;
impl Callbacks for PassthroughCallbacks {}

fn is_rustc_binary_arg(arg: &str) -> bool {
    let file_name = Path::new(arg)
        .file_name()
        .and_then(|s| s.to_str())
        .unwrap_or(arg);
    file_name == "rustc" || file_name.starts_with("rustc-") || file_name == "rustdoc"
}

/// Normalizes command-line arguments when invoked either directly
/// (`anneal-mir-instrument <rustc-args>`) or as a Cargo `RUSTC_WRAPPER`
/// (`anneal-mir-instrument <path/to/rustc> <rustc-args>`).
pub fn normalize_wrapper_args(raw_args: Vec<String>) -> Vec<String> {
    if raw_args.len() >= 2 && is_rustc_binary_arg(&raw_args[1]) {
        let mut normalized = Vec::with_capacity(raw_args.len() - 1);
        normalized.push(raw_args[0].clone());
        normalized.extend_from_slice(&raw_args[2..]);
        normalized
    } else {
        raw_args
    }
}

fn has_sysroot_arg(args: &[String]) -> bool {
    args.iter()
        .any(|arg| arg == "--sysroot" || arg.starts_with("--sysroot="))
}

fn detect_sysroot() -> Option<String> {
    if let Ok(sysroot) = env::var("ANNEAL_SYSROOT")
        && !sysroot.trim().is_empty()
    {
        return Some(sysroot);
    }
    let rustc_bin = env::var("RUSTC").unwrap_or_else(|_| "rustc".to_string());
    let output = Command::new(rustc_bin)
        .arg("--print")
        .arg("sysroot")
        .output()
        .ok()?;
    if !output.status.success() {
        return None;
    }
    let s = String::from_utf8(output.stdout).ok()?;
    let trimmed = s.trim();
    if trimmed.is_empty() {
        None
    } else {
        Some(trimmed.to_string())
    }
}

fn extract_crate_name(args: &[String]) -> Option<String> {
    let mut iter = args.iter().skip(1);
    while let Some(arg) = iter.next() {
        if arg == "--crate-name" {
            return iter.next().cloned();
        }
        if let Some(val) = arg.strip_prefix("--crate-name=") {
            return Some(val.to_string());
        }
    }
    None
}

fn is_info_or_proc_macro_invocation(args: &[String]) -> bool {
    let mut iter = args.iter().skip(1);
    while let Some(arg) = iter.next() {
        if arg == "-vV"
            || arg == "--version"
            || arg == "-V"
            || arg == "--print"
            || arg.starts_with("--print=")
        {
            return true;
        }
        if arg == "--crate-type" {
            if let Some(ct) = iter.next()
                && ct.contains("proc-macro")
            {
                return true;
            }
        } else if let Some(ct) = arg.strip_prefix("--crate-type=")
            && ct.contains("proc-macro")
        {
            return true;
        }
    }
    matches!(
        extract_crate_name(args).as_deref(),
        Some("build_script_build" | "anneal_trace")
    )
}

fn has_extern_cargo_anneal(args: &[String]) -> bool {
    let mut iter = args.iter().skip(1);
    while let Some(arg) = iter.next() {
        if arg == "--extern" {
            if let Some(ext) = iter.next()
                && (ext == "cargo_anneal" || ext.starts_with("cargo_anneal="))
            {
                return true;
            }
        } else if let Some(ext) = arg.strip_prefix("--extern=")
            && (ext == "cargo_anneal" || ext.starts_with("cargo_anneal="))
        {
            return true;
        }
    }
    false
}

fn has_non_zero_opt_level(args: &[String]) -> bool {
    let mut iter = args.iter().skip(1);
    while let Some(arg) = iter.next() {
        if arg == "-O" {
            return true;
        }
        if arg == "-C" {
            if let Some(val) = iter.next()
                && let Some(lvl) = val.strip_prefix("opt-level=")
                && lvl != "0"
            {
                return true;
            }
        } else if let Some(lvl) = arg.strip_prefix("-Copt-level=")
            && lvl != "0"
        {
            return true;
        }
    }
    false
}

/// Runs the `anneal-mir-instrument` compiler driver on `raw_args`.
pub fn run_instrument_driver(raw_args: Vec<String>) -> ExitCode {
    let mut args = normalize_wrapper_args(raw_args);
    if !has_sysroot_arg(&args)
        && let Some(sysroot) = detect_sysroot()
    {
        args.push("--sysroot".to_string());
        args.push(sysroot);
    }

    if is_info_or_proc_macro_invocation(&args) {
        let mut callbacks = PassthroughCallbacks;
        return rustc_driver::catch_with_exit_code(|| {
            rustc_driver::run_compiler(&args, &mut callbacks);
        });
    }

    if !args.iter().any(|a| a == "anneal_mir_instrument") {
        args.push("--cfg".to_string());
        args.push("anneal_mir_instrument".to_string());
    }

    let raw_mir_opts = env::var(RAW_MIR_OPTS_ENV).as_deref() == Ok("1");
    if has_non_zero_opt_level(&args) && !raw_mir_opts {
        args.push("-Zmir-opt-level=1".to_string());
        args.push("-Coverflow-checks=on".to_string());
    }

    let mut callbacks = InstrumentCallbacks {
        has_extern_cargo_anneal: has_extern_cargo_anneal(&args),
    };
    rustc_driver::catch_with_exit_code(|| {
        rustc_driver::run_compiler(&args, &mut callbacks);
    })
}
