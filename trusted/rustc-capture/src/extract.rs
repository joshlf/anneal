// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Direct translation of the admitted pointer-free MIR syntax. Unsupported
//! variants remain errors; this adapter performs no control-flow or expression
//! simplification.

use rustc_abi::ExternAbi;
use rustc_middle::mir::{self, MirPhase, RuntimePhase};
use rustc_middle::ty::{self, TyCtxt};
use rustc_span::def_id::LocalDefId;

use crate::ir;

pub type Result<T> = std::result::Result<T, String>;

/// The type grammar is `TyKind` at the pinned compiler revision:
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_type_ir/src/ty_kind.rs
///
/// Enum values in the owned syntax carry logical variant indices. The table
/// below records the compiler's discriminants separately because MIR warns:
/// "the value of the discriminant is not the same thing as the variant index."
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/mir/syntax.rs#L1433-L1443
pub fn ty<'tcx>(tcx: TyCtxt<'tcx>, t: ty::Ty<'tcx>) -> Result<ir::Ty> {
    // Every admitted value must fit the owned scalar representation. Rejecting
    // a type is deliberate: replacing a pointer, payload, or wider integer with
    // a machine word would assign semantics the proof model does not provide.
    // The fallback width for usize/isize is the separately checked 64-bit
    // target width, never the host process's usize width.
    let (bits, signed) = match *t.kind() {
        ty::Bool => return Ok(ir::Ty::Bool),
        ty::Never => return Ok(ir::Ty::Never),
        ty::Tuple(elements) if elements.is_empty() => return Ok(ir::Ty::Unit),
        ty::Uint(u) => (u.bit_width().unwrap_or(64), false),
        ty::Int(i) => (i.bit_width().unwrap_or(64), true),
        ty::Adt(adt, args) if adt.did().is_local() && adt.is_enum() && args.is_empty() => {
            if !matches!(
                adt.repr().discr_type(),
                rustc_abi::IntegerType::Pointer(true)
            ) {
                return Err("only isize enum discriminants are modeled".into());
            }
            if adt
                .variants()
                .iter()
                .any(|variant| !variant.fields.is_empty())
            {
                return Err(format!("enum payloads are unsupported: {t:?}"));
            }
            // `discriminants` computes explicit and implicit discriminants;
            // it is not safe to substitute the enumeration index here.
            // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/ty/adt.rs#L660-L679
            let discriminants = adt
                .discriminants(tcx)
                .map(|(_, discr)| {
                    if !matches!(discr.ty.kind(), ty::Int(ty::IntTy::Isize)) {
                        return Err("only isize enum discriminants are modeled".into());
                    }
                    u64::try_from(discr.val)
                        .map_err(|_| "enum discriminant exceeds 64 bits".to_string())
                })
                .collect::<Result<Vec<_>>>()?;
            return Ok(ir::Ty::Enum {
                id: adt.did().index.as_u32(),
                discriminants,
            });
        }
        _ => return Err(format!("unsupported type: {t:?}")),
    };
    if bits > 64 {
        return Err(format!("integer width {bits} exceeds the modeled 64 bits"));
    }
    Ok(ir::Ty::Int {
        bits: bits as u32,
        signed,
    })
}

/// `Place` has a local plus projections. This fragment admits the empty
/// projection only, preserving the compiler local index without renumbering.
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/mir/syntax.rs#L1182-L1188
fn local(place: &mir::Place<'_>) -> Result<u32> {
    if !place.projection.is_empty() {
        return Err(format!("place projections are unsupported: {place:?}"));
    }
    Ok(place.local.as_u32())
}

/// Copy and move are distinct constructors. The source says a move "may
/// additionally overwrite the place with `uninit` bytes"; the model owns that
/// operational choice rather than having the adapter erase the distinction.
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/mir/syntax.rs#L1303-L1330
fn operand<'tcx>(tcx: TyCtxt<'tcx>, op: &mir::Operand<'tcx>) -> Result<ir::Operand> {
    match op {
        mir::Operand::Copy(place) => Ok(ir::Operand::Copy {
            local: local(place)?,
        }),
        mir::Operand::Move(place) => Ok(ir::Operand::Move {
            local: local(place)?,
        }),
        mir::Operand::Constant(constant) => {
            let t = ty(tcx, constant.const_.ty())?;
            let width = match t {
                ir::Ty::Bool => 8,
                ir::Ty::Unit => {
                    // `ZeroSized` is documented as "Only for ZSTs." The
                    // source type must independently be the empty tuple;
                    // other zero-sized types do not acquire unit semantics.
                    // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/mir/consts.rs#L38-L39
                    if matches!(
                        constant.const_,
                        mir::Const::Val(mir::ConstValue::ZeroSized, _)
                    ) {
                        return Ok(ir::Operand::Constant { ty: t, bits: 0 });
                    }
                    return Err("unit constant lacks the compiler ZeroSized representation".into());
                }
                ir::Ty::Never => return Err("the never type has no scalar constants".into()),
                ir::Ty::Int { bits, .. } => bits,
                ir::Ty::Enum { .. } => {
                    return Err("enum constants require a representation adapter".into());
                }
            };
            // Only already-valued integer scalars are admitted. In particular,
            // do not evaluate an Unevaluated constant and silently substitute
            // its result for an unrepresented constant obligation.
            // `Scalar::Int` denotes "The raw bytes of a simple value";
            // `try_to_scalar_int` excludes provenance-bearing pointers.
            // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/mir/consts.rs
            // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/mir/interpret/value.rs
            let mir::Const::Val(value, _) = constant.const_ else {
                return Err(format!("unsupported constant: {:?}", constant.const_));
            };
            let value = value
                .try_to_scalar_int()
                .ok_or("only integer scalar constants are modeled")?;
            if value.size().bits() != u64::from(width) {
                return Err("scalar constant width disagrees with its type".into());
            }
            let bits = u64::try_from(value.to_bits_unchecked())
                .map_err(|_| "scalar constant exceeds 64 bits")?;
            if matches!(t, ir::Ty::Bool) && bits > 1 {
                return Err("invalid Boolean constant".into());
            }
            Ok(ir::Operand::Constant { ty: t, bits })
        }
        other => Err(format!("unsupported operand: {other:?}")),
    }
}

/// Preserve the ordinary MIR operators. In particular, ordinary shifts use
/// "RHS.rem_euclid(LHS::BITS)"; the unchecked variants have a different UB
/// contract and are rejected. The model interprets these operators, including
/// signed comparisons and wrapping arithmetic, rather than the adapter.
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/mir/syntax.rs#L1621-L1708
fn bin_op(op: mir::BinOp) -> Result<ir::BinOp> {
    Ok(match op {
        mir::BinOp::BitAnd => ir::BinOp::BitAnd,
        mir::BinOp::BitOr => ir::BinOp::BitOr,
        mir::BinOp::BitXor => ir::BinOp::BitXor,
        mir::BinOp::Shl => ir::BinOp::Shl,
        mir::BinOp::Shr => ir::BinOp::Shr,
        mir::BinOp::Add => ir::BinOp::Add,
        mir::BinOp::Sub => ir::BinOp::Sub,
        mir::BinOp::Mul => ir::BinOp::Mul,
        mir::BinOp::Eq => ir::BinOp::Eq,
        mir::BinOp::Ne => ir::BinOp::Ne,
        mir::BinOp::Lt => ir::BinOp::Lt,
        mir::BinOp::Le => ir::BinOp::Le,
        mir::BinOp::Gt => ir::BinOp::Gt,
        mir::BinOp::Ge => ir::BinOp::Ge,
        other => return Err(format!("unsupported binary operator: {other:?}")),
    })
}

/// `Use` "yields the operand unchanged, except for a potential retag."
/// Preserve `WithRetag`, even though admitted values contain no pointers.
/// Binary operands may have different types for shifts; no casts are inserted.
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/mir/syntax.rs#L1363-L1365
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/mir/syntax.rs#L1410-L1443
fn rvalue<'tcx>(tcx: TyCtxt<'tcx>, value: &mir::Rvalue<'tcx>) -> Result<ir::Rvalue> {
    Ok(match value {
        // Tuple aggregates preserve the exact empty tuple constructor. No
        // general aggregate, enum payload or unused local is erased here.
        // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/mir/syntax.rs#L1445-L1453
        mir::Rvalue::Aggregate(kind, operands)
            if matches!(&**kind, mir::AggregateKind::Tuple) && operands.is_empty() =>
        {
            ir::Rvalue::Unit
        }
        mir::Rvalue::Use(op, with_retag) => ir::Rvalue::Use {
            operand: operand(tcx, op)?,
            with_retag: with_retag.yes(),
        },
        mir::Rvalue::BinaryOp(op, values) => ir::Rvalue::Binary {
            op: bin_op(*op)?,
            left: operand(tcx, &values.0)?,
            right: operand(tcx, &values.1)?,
        },
        mir::Rvalue::Discriminant(place) => ir::Rvalue::Discriminant {
            local: local(place)?,
        },
        other => return Err(format!("unsupported rvalue: {other:?}")),
    })
}

/// Storage markers survive capture. Their documented effect is that
/// "Using a local ... while it is unallocated is UB."
/// `Nop` alone has no effect.
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/mir/syntax.rs#L364-L385
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/mir/syntax.rs#L442-L443
fn statement<'tcx>(tcx: TyCtxt<'tcx>, stmt: &mir::StatementKind<'tcx>) -> Result<ir::Statement> {
    Ok(match stmt {
        mir::StatementKind::Assign(value) => ir::Statement::Assign {
            local: local(&value.0)?,
            value: rvalue(tcx, &value.1)?,
        },
        mir::StatementKind::StorageLive(local) => ir::Statement::StorageLive {
            local: local.as_u32(),
        },
        mir::StatementKind::StorageDead(local) => ir::Statement::StorageDead {
            local: local.as_u32(),
        },
        mir::StatementKind::Nop => ir::Statement::Nop,
        other => return Err(format!("unsupported statement: {other:?}")),
    })
}

/// `SwitchInt` evaluates its operand and selects an explicit or otherwise edge.
/// `Unreachable` is retained because "Executing this terminator is UB."
/// Calls, drop, unwind, assembly and all other terminators are refused. They
/// need interprocedural, memory, or unwinding rules absent from this syntax;
/// an apparently unreachable occurrence is not permission to erase it.
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/mir/syntax.rs#L692-L740
fn terminator<'tcx>(tcx: TyCtxt<'tcx>, term: &mir::TerminatorKind<'tcx>) -> Result<ir::Terminator> {
    Ok(match term {
        mir::TerminatorKind::Goto { target } => ir::Terminator::Goto {
            block: target.as_u32(),
        },
        mir::TerminatorKind::SwitchInt { discr, targets } => ir::Terminator::SwitchInt {
            operand: operand(tcx, discr)?,
            targets: targets
                .iter()
                .map(|(value, block)| {
                    Ok((
                        u64::try_from(value).map_err(|_| "switch value exceeds 64 bits")?,
                        block.as_u32(),
                    ))
                })
                .collect::<Result<Vec<_>>>()?,
            otherwise: targets.otherwise().as_u32(),
        },
        mir::TerminatorKind::Return => ir::Terminator::Ret,
        mir::TerminatorKind::Unreachable => ir::Terminator::Unreachable,
        other => return Err(format!("unsupported terminator: {other:?}")),
    })
}

/// Bind a function to an owned, versioned source identity for this compiler.
///
/// The pinned compiler calls `def_path_str` a string "suitable for user output";
/// it is not a stable identifier contract. Anneal's v1 scheme fixes that pinned
/// semantic path printer with trimming and visible reexports disabled. Thus a
/// public alias cannot replace the defining path. In this phase impl paths use
/// their self/trait types rather than file positions.
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/ty/print/pretty.rs#L115-L124
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/ty/print/pretty.rs#L2191-L2210
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/ty/print/pretty.rs#L2266-L2306
///
/// Raw compiler indices cannot identify a contract across source edits. Even a
/// raw DefPath disambiguator has "some artificial ordering dependency", notably
/// for impl blocks, so v1 uses the pinned semantic owner/type path instead.
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_hir/src/definitions.rs#L103-L109
///
/// Identities are crate-relative and tied to this scheme and compiler pin.
/// Item renames and owner changes change the key. Toolchain changes require
/// reviewing the scheme and its specifications; this is an Anneal format, not
/// an assumption that Rust's diagnostic formatter remains stable forever.
///
/// Anonymous-owner components can still depend on source order. Such functions
/// are admitted only through selected scope today, whose reviewed roots already
/// expose selectors such as `outer::{closure#0}::inner`. This v1 key exposes the
/// same selector; persistent identity across anonymous-owner edits needs a
/// reviewed stable anchor or a separate binding protocol. It is not established
/// by prefixing a diagnostic path with a version number.
///
/// Capture separately refuses duplicate identities before publishing a subject,
/// so a printer collision cannot share one contract between distinct items.
fn function_identity(tcx: TyCtxt<'_>, def: LocalDefId) -> String {
    let path = rustc_middle::ty::print::with_no_trimmed_paths!(
        rustc_middle::ty::print::with_no_visible_paths!(tcx.def_path_str(def))
    );
    format!("rust-path-v1::{path}")
}

/// Translate the provider's exact body. `required_consts` is explicitly
/// "soundness-critical"; an unrepresented required constant is a refusal,
/// independent of runtime preconditions or whether any return is reachable.
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/mir/mod.rs#L265-L271
pub fn body<'tcx>(tcx: TyCtxt<'tcx>, def: LocalDefId, body: &mir::Body<'tcx>) -> Result<ir::Body> {
    // The phase determines the meaning and allowed grammar of MIR. The
    // compiler's phase field records progress through "desugaring and
    // optimization". Refuse another phase instead of guessing how to normalize
    // it into the syntax modeled here.
    // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/mir/mod.rs#L211-L216
    if body.phase != MirPhase::Runtime(RuntimePhase::PostCleanup) {
        return Err(format!("unexpected MIR phase: {:?}", body.phase));
    }
    // An error-tainted body is not compiler approval. Coroutine state and
    // rust-call tuple spreading need entry/continuation rules absent from this
    // IR. `spread_arg` passes "its individual components at the LLVM level";
    // treating that as ordinary flat arguments would change the call contract.
    // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/mir/mod.rs#L227-L257
    if body.tainted_by_errors.is_some() || body.coroutine.is_some() || body.spread_arg.is_some() {
        return Err("tainted, coroutine or spread-argument body is unsupported".into());
    }
    // `None` means "the list has not been computed yet", not an empty set of
    // obligations. Even a valid scalar runtime body cannot waive a missing or
    // nonempty compile-time obligation inventory.
    // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/mir/mod.rs#L265-L271
    if !matches!(body.required_consts.as_deref(), Some([])) {
        return Err("required constants are unavailable in the scalar model".into());
    }
    // One captured body has one concrete scalar argument/type interpretation.
    // Generic entry points would require quantified instantiation obligations;
    // compiler completion alone does not prove every future instantiation.
    if tcx.generics_of(def).count() != 0 {
        return Err("generic functions require quantified instantiation obligations".into());
    }
    let signature = tcx.fn_sig(def).instantiate_identity().skip_binder();
    // The model has ordinary Rust arguments and no foreign/variadic calling
    // convention or hardware-feature entry conditions. Do not infer those
    // missing preconditions merely because the body happens to use scalars.
    if signature.abi() != ExternAbi::Rust || signature.c_variadic() {
        return Err("only non-variadic Rust ABI functions are admitted".into());
    }
    if !tcx.codegen_fn_attrs(def).target_features.is_empty() {
        return Err("target-feature entry obligations are unsupported".into());
    }
    // Preserve all compiler locals and blocks, including unused locals and
    // unreachable blocks. The compiler places arguments "Starting at local 1"
    // and block references index its basic-block vector. Filtering or
    // renumbering would change the subject and require a separate proof.
    // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/mir/mod.rs#L207-L209
    // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/mir/mod.rs#L235-L251
    let local_tys = body
        .local_decls
        .iter()
        .map(|decl| ty(tcx, decl.ty))
        .collect::<Result<Vec<_>>>()?;
    let blocks = body
        .basic_blocks
        .iter_enumerated()
        .map(|(id, block)| {
            // Cleanup blocks need an unwinding interpretation even when their
            // ordinary edges are unreachable. The scalar fragment has none.
            if block.is_cleanup {
                return Err(format!("cleanup block {id:?} is unsupported"));
            }
            let statements = block
                .statements
                .iter()
                .enumerate()
                .map(|(index, stmt)| {
                    statement(tcx, &stmt.kind)
                        .map_err(|error| format!("{id:?} statement {index}: {error}"))
                })
                .collect::<Result<Vec<_>>>()?;
            let term = block.terminator.as_ref().ok_or("missing terminator")?;
            let terminator = terminator(tcx, &term.kind)
                .map_err(|error| format!("{id:?} terminator: {error}"))?;
            Ok(ir::Block {
                statements,
                terminator,
            })
        })
        .collect::<Result<Vec<_>>>()?;
    Ok(ir::Body {
        arg_count: body.arg_count,
        // fn_sig lowers ordinary declarations with "sig.header.safety()";
        // lower_fn_ty preserves it with ".set_safety(safety)". FnSig::safety
        // delegates to the getter documented as "Returns the safety mode."
        // hir::Safety::is_unsafe is "!self.is_safe()", with Unsafe/Safe mapped
        // to false/true by is_safe. Read declaration safety from that signature,
        // not from whether this scalar MIR happens to contain unsafe operations.
        // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_hir_analysis/src/collect.rs#L1066-L1084
        // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_hir_analysis/src/hir_ty_lowering/mod.rs#L3434-L3458
        // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_type_ir/src/ty_kind.rs#L882-L885
        // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_type_ir/src/ty_kind.rs#L925-L927
        // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_hir/src/hir.rs#L4610-L4621
        //
        // The model uses this bit to decide whether reviewed caller
        // requirements apply. Target-feature entry points are excluded above;
        // pointer-free syntax alone does not authorize treating an unsafe
        // declaration as an unrestricted safe entry point.
        is_unsafe: signature.safety().is_unsafe(),
        local_tys,
        blocks,
        identity: function_identity(tcx, def),
    })
}
