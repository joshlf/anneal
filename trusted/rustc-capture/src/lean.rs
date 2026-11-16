// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Pure rendering of the owned syntax. Every emitted token is fixed here or is
//! a numeric/Boolean literal. Function identities use numeric Unicode scalar
//! constructors, so names never enter the emitted command or literal syntax.

use crate::ir::{self, BinOp, Operand, Rvalue, Statement, Terminator, Ty};

const HEADER: &str = "-- Copyright 2026 The Fuchsia Authors\n--\n\
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0\n\
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT\n\
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.\n\
-- This file may not be copied, modified, or distributed except according to\n\
-- those terms.\n\n\
prelude\nimport Trusted.MirAst\n\nnamespace Captured\n\n";

fn list<T>(values: &[T], render: impl Fn(&T) -> String) -> String {
    format!(
        "[{}]",
        values.iter().map(render).collect::<Vec<_>>().join(", ")
    )
}

fn int_width(bits: u32, is_size: bool) -> &'static str {
    if is_size {
        "isize"
    } else {
        match bits {
            8 => "i8",
            16 => "i16",
            32 => "i32",
            64 => "i64",
            _ => unreachable!("validated integer width {bits}"),
        }
    }
}

fn ty(t: &Ty) -> String {
    match t {
        Ty::Bool => "Trusted.MirAst.MirTy.bool".into(),
        Ty::Unit => "Trusted.MirAst.MirTy.unit".into(),
        Ty::Never => "Trusted.MirAst.MirTy.never".into(),
        Ty::Int {
            bits,
            signed,
            is_size,
        } => format!(
            "(Trusted.MirAst.MirTy.int Trusted.MirAst.IntWidth.{} {signed})",
            int_width(*bits, *is_size)
        ),
        Ty::Enum(ety) => {
            let tag_repr = match ety.tag_repr {
                ir::EnumTagRepr::ZeroSized => "Trusted.MirAst.EnumTagRepr.zeroSized".into(),
                ir::EnumTagRepr::Scalar {
                    bits,
                    signed,
                    is_size,
                } => format!(
                    "(Trusted.MirAst.EnumTagRepr.scalar Trusted.MirAst.IntWidth.{} {signed})",
                    int_width(bits, is_size)
                ),
            };
            format!(
                "(Trusted.MirAst.MirTy.enum {{ id := {}, discrWidth := Trusted.MirAst.IntWidth.{}, discrSigned := {}, tagRepr := {tag_repr}, discriminants := {} }})",
                ety.id,
                int_width(ety.discr_bits, ety.discr_is_size),
                ety.discr_signed,
                list(&ety.discriminants, u64::to_string)
            )
        }
    }
}

fn operand(op: &Operand) -> String {
    match op {
        Operand::Copy { local } => {
            format!("(Trusted.MirAst.Operand.copy (Trusted.MirAst.Place.mk {local} []))")
        }
        Operand::Move { local } => {
            format!("(Trusted.MirAst.Operand.move (Trusted.MirAst.Place.mk {local} []))")
        }
        Operand::Constant { ty: Ty::Unit, .. } => {
            "(Trusted.MirAst.Operand.constant (Trusted.MirAst.ConstOperand.mk Trusted.MirAst.MirTy.unit Trusted.MirAst.ConstLit.zeroSized))".into()
        }
        Operand::Constant {
            ty:
                t @ Ty::Enum(ir::EnumTy {
                    tag_repr: ir::EnumTagRepr::ZeroSized,
                    ..
                }),
            ..
        } => format!(
            "(Trusted.MirAst.Operand.constant (Trusted.MirAst.ConstOperand.mk {} Trusted.MirAst.ConstLit.zeroSized))",
            ty(t)
        ),
        Operand::Constant { ty: t, bits } => format!(
            "(Trusted.MirAst.Operand.constant (Trusted.MirAst.ConstOperand.mk {} (Trusted.MirAst.ConstLit.scalar (BitVec.ofNat 128 {bits}))))",
            ty(t)
        ),
    }
}

fn bin_op(op: BinOp) -> &'static str {
    match op {
        BinOp::BitAnd => "bitAnd",
        BinOp::BitOr => "bitOr",
        BinOp::BitXor => "bitXor",
        BinOp::Shl => "shl",
        BinOp::Shr => "shr",
        BinOp::Add => "add",
        BinOp::Sub => "sub",
        BinOp::Mul => "mul",
        BinOp::Eq => "eq",
        BinOp::Ne => "ne",
        BinOp::Lt => "lt",
        BinOp::Le => "le",
        BinOp::Gt => "gt",
        BinOp::Ge => "ge",
    }
}

fn rvalue(dst_ty: Option<&Ty>, value: &Rvalue) -> String {
    match value {
        Rvalue::Unit => {
            "(Trusted.MirAst.Rvalue.use (Trusted.MirAst.Operand.constant (Trusted.MirAst.ConstOperand.mk Trusted.MirAst.MirTy.unit Trusted.MirAst.ConstLit.zeroSized)))".into()
        }
        Rvalue::Use {
            operand: op,
            with_retag,
        } => {
            if *with_retag && !dst_ty.is_some_and(Ty::is_retag_noop) {
                "Trusted.MirAst.Rvalue.unsupported".into()
            } else {
                format!("(Trusted.MirAst.Rvalue.use {})", operand(op))
            }
        }
        Rvalue::Binary { op, left, right } => format!(
            "(Trusted.MirAst.Rvalue.binaryOp Trusted.MirAst.BinOp.{} {} {})",
            bin_op(*op),
            operand(left),
            operand(right)
        ),
        Rvalue::Discriminant { local } => {
            format!("(Trusted.MirAst.Rvalue.discriminant (Trusted.MirAst.Place.mk {local} []))")
        }
    }
}

fn statement(local_tys: &[Ty], stmt: &Statement) -> String {
    match stmt {
        Statement::Assign { local, value } => {
            let dst_ty = local_tys.get(*local as usize);
            format!(
                "(Trusted.MirAst.StatementKind.assign (Trusted.MirAst.Place.mk {local} []) {})",
                rvalue(dst_ty, value)
            )
        }
        Statement::StorageLive { local } => {
            format!("(Trusted.MirAst.StatementKind.storageLive {local})")
        }
        Statement::StorageDead { local } => {
            format!("(Trusted.MirAst.StatementKind.storageDead {local})")
        }
        Statement::Nop => "Trusted.MirAst.StatementKind.nop".into(),
    }
}

fn terminator(term: &Terminator) -> String {
    match term {
        Terminator::Goto { block } => format!("(Trusted.MirAst.TerminatorKind.goto {block})"),
        Terminator::SwitchInt {
            operand: op,
            targets,
            otherwise,
        } => format!(
            "(Trusted.MirAst.TerminatorKind.switchInt {} (Trusted.MirAst.SwitchTargets.mk {} {otherwise}))",
            operand(op),
            list(targets, |(value, block)| format!(
                "((BitVec.ofNat 128 {value}), {block})"
            ))
        ),
        Terminator::Ret => "Trusted.MirAst.TerminatorKind.return_".into(),
        Terminator::Unreachable => "Trusted.MirAst.TerminatorKind.unreachable".into(),
    }
}

/// Construct a Lean string without interpolating its contents into Lean syntax.
/// The identity selects a reviewed safety predicate, so it must enter the
/// logical subject without gaining authority to add commands or change names.
/// Rust characters are Unicode scalar values; numeric Char constructors retain
/// them even when a name contains quotes, backslashes or other syntax. This
/// keeps every emitted token fixed or numeric and requires no escaping grammar.
fn identity(value: &str) -> String {
    let characters: Vec<_> = value.chars().collect();
    format!(
        "(_root_.String.ofList {})",
        list(&characters, |ch| format!(
            "(_root_.Char.ofNat {})",
            u32::from(*ch)
        ))
    )
}

fn body(body: &ir::Body) -> String {
    format!(
        "({{ argumentCount := {}, isUnsafe := {}, locals := {}, basicBlocks := {}, identity := {} }} : Trusted.MirAst.Body)",
        body.arg_count,
        body.is_unsafe,
        list(&body.local_tys, ty),
        list(&body.blocks, |block| format!(
            "({{ statements := {}, terminator := {}, cleanup := false }} : Trusted.MirAst.BasicBlock)",
            list(&block.statements, |stmt| statement(&body.local_tys, stmt)),
            terminator(&block.terminator)
        )),
        identity(&body.identity)
    )
}

/// Render data constructors under one fixed module/definition skeleton.
/// Capture emits a subject, not a proof or a dynamically chosen theorem. The
/// verifier separately authenticates this source and checks the authored root;
/// neither diagnostics nor census text can add commands through this renderer.
pub fn render(program: &ir::Program) -> String {
    let scope = match program.scope {
        ir::VerificationScope::Unit => "unit",
        ir::VerificationScope::Crate => "crate",
    };
    format!(
        "{HEADER}def program : Trusted.MirAst.Program :=\n  {{ scope := Trusted.MirAst.VerificationScope.{scope}, bodies := {} }}\n\nend Captured\n",
        list(&program.bodies, body)
    )
}

#[cfg(test)]
mod identity_tests {
    use super::{identity, rvalue};
    use crate::ir::{Operand, Rvalue, Ty};

    #[test]
    fn identity_names_are_only_numeric_character_data() {
        assert_eq!(
            identity("a\"\\\nλ"),
            "(_root_.String.ofList [(_root_.Char.ofNat 97), (_root_.Char.ofNat 34), (_root_.Char.ofNat 92), (_root_.Char.ofNat 10), (_root_.Char.ofNat 955)])"
        );
    }

    #[test]
    fn retagging_use_without_confirmed_retag_noop_destination_emits_unsupported() {
        let rv = Rvalue::Use {
            operand: Operand::Copy { local: 1 },
            with_retag: true,
        };
        assert_eq!(rvalue(None, &rv), "Trusted.MirAst.Rvalue.unsupported");
        assert_eq!(
            rvalue(Some(&Ty::Bool), &rv),
            "(Trusted.MirAst.Rvalue.use (Trusted.MirAst.Operand.copy (Trusted.MirAst.Place.mk 1 [])))"
        );
    }
}
