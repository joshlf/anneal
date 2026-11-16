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
prelude\nimport Trusted.Mvp\n\nnamespace Captured\n\n";

fn list<T>(values: &[T], render: impl Fn(&T) -> String) -> String {
    format!(
        "[{}]",
        values.iter().map(render).collect::<Vec<_>>().join(", ")
    )
}

fn ty(t: &Ty) -> String {
    match t {
        Ty::Bool => "Trusted.Mvp.Ty.bool".into(),
        Ty::Unit => "Trusted.Mvp.Ty.unit".into(),
        Ty::Never => "Trusted.Mvp.Ty.never".into(),
        Ty::Int { bits, signed } => format!("(Trusted.Mvp.Ty.int {bits} {signed})"),
        Ty::Enum { id, discriminants } => format!(
            "(Trusted.Mvp.Ty.enum {id} {})",
            list(discriminants, u64::to_string)
        ),
    }
}

fn operand(op: &Operand) -> String {
    match op {
        Operand::Copy { local } => format!("(Trusted.Mvp.Operand.copy {local})"),
        Operand::Move { local } => format!("(Trusted.Mvp.Operand.move {local})"),
        Operand::Constant { ty: t, bits } => {
            format!("(Trusted.Mvp.Operand.constant {} {bits})", ty(t))
        }
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

fn rvalue(value: &Rvalue) -> String {
    match value {
        Rvalue::Unit => "Trusted.Mvp.Rvalue.unit".into(),
        Rvalue::Use {
            operand: op,
            with_retag,
        } => format!("(Trusted.Mvp.Rvalue.use {} {with_retag})", operand(op)),
        Rvalue::Binary { op, left, right } => format!(
            "(Trusted.Mvp.Rvalue.binary Trusted.Mvp.BinOp.{} {} {})",
            bin_op(*op),
            operand(left),
            operand(right)
        ),
        Rvalue::Discriminant { local } => {
            format!("(Trusted.Mvp.Rvalue.discriminant {local})")
        }
    }
}

fn statement(stmt: &Statement) -> String {
    match stmt {
        Statement::Assign { local, value } => {
            format!("(Trusted.Mvp.Statement.assign {local} {})", rvalue(value))
        }
        Statement::StorageLive { local } => {
            format!("(Trusted.Mvp.Statement.storageLive {local})")
        }
        Statement::StorageDead { local } => {
            format!("(Trusted.Mvp.Statement.storageDead {local})")
        }
        Statement::Nop => "Trusted.Mvp.Statement.nop".into(),
    }
}

fn terminator(term: &Terminator) -> String {
    match term {
        Terminator::Goto { block } => format!("(Trusted.Mvp.Terminator.goto {block})"),
        Terminator::SwitchInt {
            operand: op,
            targets,
            otherwise,
        } => format!(
            "(Trusted.Mvp.Terminator.switchInt {} {} {otherwise})",
            operand(op),
            list(targets, |(value, block)| format!("({value}, {block})"))
        ),
        Terminator::Ret => "Trusted.Mvp.Terminator.ret".into(),
        Terminator::Unreachable => "Trusted.Mvp.Terminator.unreachable".into(),
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
        "({{ argCount := {}, isUnsafe := {}, localTys := {}, blocks := {}, identity := {} }} : Trusted.Mvp.Body)",
        body.arg_count,
        body.is_unsafe,
        list(&body.local_tys, ty),
        list(&body.blocks, |block| format!(
            "({{ statements := {}, terminator := {} }} : Trusted.Mvp.Block)",
            list(&block.statements, statement),
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
        "{HEADER}def program : Trusted.Mvp.Program :=\n  {{ scope := Trusted.Mvp.VerificationScope.{scope}, bodies := {} }}\n\nend Captured\n",
        list(&program.bodies, body)
    )
}

#[cfg(test)]
mod identity_tests {
    use super::identity;

    #[test]
    fn identity_names_are_only_numeric_character_data() {
        assert_eq!(
            identity("a\"\\\nλ"),
            "(_root_.String.ofList [(_root_.Char.ofNat 97), (_root_.Char.ofNat 34), (_root_.Char.ofNat 92), (_root_.Char.ofNat 10), (_root_.Char.ofNat 955)])"
        );
    }
}
