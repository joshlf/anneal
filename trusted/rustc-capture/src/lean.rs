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

const COPYRIGHT_HEADER: &str = "-- Copyright 2026 The Fuchsia Authors\n--\n\
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0\n\
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT\n\
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.\n\
-- This file may not be copied, modified, or distributed except according to\n\
-- those terms.\n\n";

/// The Lean syntax module for the linked compiler's MIR dialect.
///
/// Each dialect has its own reviewed `Trusted.Rustc.<Dialect>.MirAst`, so the
/// constructors below must exist in the module named here. Selecting the name
/// by `anneal_mir_dialect` ties it to the compiler `build.rs` identified; a
/// dialect without an entry stops the build instead of borrowing another
/// dialect's syntax.
#[cfg(anneal_mir_dialect = "V2026_10_22_R7189d39d9")]
const MIR_AST: &str = "Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst";
#[cfg(anneal_mir_dialect = "V2026_05_31_R14210df0e")]
const MIR_AST: &str = "Trusted.Rustc.V2026_05_31_R14210df0e.MirAst";
#[cfg(anneal_mir_dialect = "V2026_05_30_Rf8a08b688")]
const MIR_AST: &str = "Trusted.Rustc.V2026_05_30_Rf8a08b688.MirAst";

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

fn ty(ast: &str, t: &Ty) -> String {
    match t {
        Ty::Bool => format!("{ast}.MirTy.bool"),
        Ty::Unit => format!("{ast}.MirTy.unit"),
        Ty::Never => format!("{ast}.MirTy.never"),
        Ty::Int {
            bits,
            signed,
            is_size,
        } => format!(
            "({ast}.MirTy.int {ast}.IntWidth.{} {signed})",
            int_width(*bits, *is_size)
        ),
        Ty::Enum(ety) => {
            let tag_repr = match ety.tag_repr {
                ir::EnumTagRepr::ZeroSized => format!("{ast}.EnumTagRepr.zeroSized"),
                ir::EnumTagRepr::Scalar {
                    bits,
                    signed,
                    is_size,
                } => format!(
                    "({ast}.EnumTagRepr.scalar {ast}.IntWidth.{} {signed})",
                    int_width(bits, is_size)
                ),
            };
            format!(
                "({ast}.MirTy.enum {{ id := {}, discrWidth := {ast}.IntWidth.{}, discrSigned := {}, tagRepr := {tag_repr}, discriminants := {} }})",
                ety.id,
                int_width(ety.discr_bits, ety.discr_is_size),
                ety.discr_signed,
                list(&ety.discriminants, u64::to_string)
            )
        }
    }
}

fn operand(ast: &str, op: &Operand) -> String {
    match op {
        Operand::Copy { local } => {
            format!("({ast}.Operand.copy ({ast}.Place.mk {local} []))")
        }
        Operand::Move { local } => {
            format!("({ast}.Operand.move ({ast}.Place.mk {local} []))")
        }
        Operand::Constant { ty: Ty::Unit, .. } => {
            format!(
                "({ast}.Operand.constant ({ast}.ConstOperand.mk {ast}.MirTy.unit {ast}.ConstLit.zeroSized))"
            )
        }
        Operand::Constant {
            ty:
                t @ Ty::Enum(ir::EnumTy {
                    tag_repr: ir::EnumTagRepr::ZeroSized,
                    ..
                }),
            ..
        } => format!(
            "({ast}.Operand.constant ({ast}.ConstOperand.mk {} {ast}.ConstLit.zeroSized))",
            ty(ast, t)
        ),
        Operand::Constant { ty: t, bits } => format!(
            "({ast}.Operand.constant ({ast}.ConstOperand.mk {} ({ast}.ConstLit.scalar (BitVec.ofNat 128 {bits}))))",
            ty(ast, t)
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

fn rvalue(ast: &str, dst_ty: Option<&Ty>, value: &Rvalue) -> String {
    match value {
        Rvalue::Unit => {
            format!(
                "({ast}.Rvalue.use ({ast}.Operand.constant ({ast}.ConstOperand.mk {ast}.MirTy.unit {ast}.ConstLit.zeroSized)))"
            )
        }
        Rvalue::Use {
            operand: op,
            with_retag,
        } => {
            if *with_retag && !dst_ty.is_some_and(Ty::is_retag_noop) {
                format!("{ast}.Rvalue.unsupported")
            } else {
                format!("({ast}.Rvalue.use {})", operand(ast, op))
            }
        }
        Rvalue::Binary { op, left, right } => format!(
            "({ast}.Rvalue.binaryOp {ast}.BinOp.{} {} {})",
            bin_op(*op),
            operand(ast, left),
            operand(ast, right)
        ),
        Rvalue::Discriminant { local } => {
            format!("({ast}.Rvalue.discriminant ({ast}.Place.mk {local} []))")
        }
    }
}

fn statement(ast: &str, local_tys: &[Ty], stmt: &Statement) -> String {
    match stmt {
        Statement::Assign { local, value } => {
            let dst_ty = local_tys.get(*local as usize);
            format!(
                "({ast}.StatementKind.assign ({ast}.Place.mk {local} []) {})",
                rvalue(ast, dst_ty, value)
            )
        }
        Statement::StorageLive { local } => {
            format!("({ast}.StatementKind.storageLive {local})")
        }
        Statement::StorageDead { local } => {
            format!("({ast}.StatementKind.storageDead {local})")
        }
        Statement::Nop => format!("{ast}.StatementKind.nop"),
    }
}

fn terminator(ast: &str, term: &Terminator) -> String {
    match term {
        Terminator::Goto { block } => format!("({ast}.TerminatorKind.goto {block})"),
        Terminator::SwitchInt {
            operand: op,
            targets,
            otherwise,
        } => format!(
            "({ast}.TerminatorKind.switchInt {} ({ast}.SwitchTargets.mk {} {otherwise}))",
            operand(ast, op),
            list(targets, |(value, block)| format!(
                "((BitVec.ofNat 128 {value}), {block})"
            ))
        ),
        Terminator::Ret => format!("{ast}.TerminatorKind.return_"),
        Terminator::Unreachable => format!("{ast}.TerminatorKind.unreachable"),
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

fn body(ast: &str, body: &ir::Body) -> String {
    format!(
        "({{ argumentCount := {}, isUnsafe := {}, locals := {}, basicBlocks := {}, identity := {} }} : {ast}.Body)",
        body.arg_count,
        body.is_unsafe,
        list(&body.local_tys, |t| ty(ast, t)),
        list(&body.blocks, |block| format!(
            "({{ statements := {}, terminator := {}, cleanup := false }} : {ast}.BasicBlock)",
            list(&block.statements, |stmt| statement(
                ast,
                &body.local_tys,
                stmt
            )),
            terminator(ast, &block.terminator)
        )),
        identity(&body.identity)
    )
}

/// Render data constructors under one fixed module/definition skeleton.
/// Capture emits a subject, not a proof or a dynamically chosen theorem. The
/// verifier separately authenticates this source and checks the authored root;
/// neither diagnostics nor census text can add commands through this renderer.
pub fn render(program: &ir::Program) -> String {
    let ast = MIR_AST;
    let scope = match program.scope {
        ir::VerificationScope::Unit => "unit",
        ir::VerificationScope::Crate => "crate",
    };
    format!(
        "{COPYRIGHT_HEADER}prelude\nimport {ast}\n\nnamespace Captured\n\ndef program : {ast}.Program :=\n  {{ scope := {ast}.VerificationScope.{scope}, bodies := {} }}\n\nend Captured\n",
        list(&program.bodies, |b| body(ast, b))
    )
}

#[cfg(test)]
mod identity_tests {
    use super::{MIR_AST, identity, rvalue};
    use crate::ir::{LINKED_COMPILER, Operand, Rvalue, Ty};

    #[test]
    fn emission_uses_the_linked_dialect_syntax_module() {
        assert_eq!(
            MIR_AST,
            format!("Trusted.Rustc.{}.MirAst", LINKED_COMPILER.mir_dialect)
        );
    }

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
        assert_eq!(
            rvalue(MIR_AST, None, &rv),
            format!("{MIR_AST}.Rvalue.unsupported")
        );
        assert_eq!(
            rvalue(MIR_AST, Some(&Ty::Bool), &rv),
            format!("({MIR_AST}.Rvalue.use ({MIR_AST}.Operand.copy ({MIR_AST}.Place.mk 1 [])))")
        );
    }
}
