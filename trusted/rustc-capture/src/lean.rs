// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Rendering of `ir::Crate` as the Lean module `Mir.lean`.
//!
//! This is a pure function from the IR to text. The first section is the
//! complete mapping from IR constructors to Lean constructors, one match arm
//! per constructor; it is the only place that names the Lean vocabulary of
//! `Trusted/MirAst.lean` and `Trusted/MirSemantics.lean`, so a change to that
//! vocabulary is a change to this table. The second section lays out
//! definitions.
//!
//! Every emitted term is fully qualified (`Trusted.MirTy.usize`, not
//! `.usize`), so its meaning does not depend on Lean's expected-type
//! elaboration.

use std::collections::BTreeMap;
use std::fmt::Write;

use crate::ir::{self, DefIdx};

/// Names and dense IDs assigned to crate items for rendering.
struct Names {
    /// Lean definition name of each body.
    body: BTreeMap<DefIdx, String>,
    /// Dense `BodyId.index` of each body, in `Crate::bodies` order.
    body_id: BTreeMap<DefIdx, usize>,
    /// Dense `AdtDecl.id` of each struct, in declaration order.
    adt: BTreeMap<DefIdx, usize>,
}

// ---------------------------------------------------------------------------
// The IR-to-Lean table.
// ---------------------------------------------------------------------------

impl Names {
    fn ty(&self, t: &ir::Ty) -> String {
        match t {
            ir::Ty::Usize => "Trusted.MirTy.usize".into(),
            ir::Ty::Bool => "Trusted.MirTy.bool".into(),
            ir::Ty::Unit => "Trusted.MirTy.unit".into(),
            ir::Ty::Adt(d) => format!("(Trusted.MirTy.adt {})", self.adt[d]),
            ir::Ty::Param(i) => format!("(Trusted.MirTy.param {i})"),
            ir::Ty::Ref(inner) => {
                format!("(Trusted.MirTy.ref {})", self.ty(inner))
            }
        }
    }

    fn val(&self, v: &ir::Val) -> String {
        match v {
            ir::Val::Usize(n) => format!("(Trusted.MirVal.usize {n})"),
            ir::Val::Bool(b) => format!("(Trusted.MirVal.bool {b})"),
            ir::Val::Unit => "Trusted.MirVal.unit".into(),
        }
    }

    fn place_elem(e: &ir::PlaceElem) -> String {
        match e {
            ir::PlaceElem::Deref => "Trusted.PlaceElem.deref".into(),
            ir::PlaceElem::Field(f) => format!("(Trusted.PlaceElem.field {f})"),
        }
    }

    fn place(p: &ir::Place) -> String {
        format!(
            "{{ loc := ⟨{}⟩, projection := {} }}",
            p.loc,
            list(p.projection.iter().map(Self::place_elem))
        )
    }

    fn operand(&self, o: &ir::Operand) -> String {
        match o {
            ir::Operand::Copy(p) => {
                format!("(Trusted.Operand.copy {})", Self::place(p))
            }
            ir::Operand::Move(p) => {
                format!("(Trusted.Operand.move {})", Self::place(p))
            }
            ir::Operand::Const(v) => {
                format!("(Trusted.Operand.constVal {})", self.val(v))
            }
        }
    }

    fn rvalue(&self, r: &ir::Rvalue) -> String {
        match r {
            ir::Rvalue::Use(o) => {
                format!("(Trusted.Rvalue.use {})", self.operand(o))
            }
            ir::Rvalue::Eq(a, b) => format!(
                "(Trusted.Rvalue.binaryOp Trusted.BinOp.eq {} {})",
                self.operand(a),
                self.operand(b)
            ),
            ir::Rvalue::Aggregate(d, o) => {
                format!(
                    "(Trusted.Rvalue.aggregate {} {})",
                    self.adt[d],
                    self.operand(o)
                )
            }
            ir::Rvalue::Ref(p) => {
                format!("(Trusted.Rvalue.ref {})", Self::place(p))
            }
        }
    }

    fn stmt(&self, s: &ir::Stmt) -> String {
        match s {
            ir::Stmt::Assign(p, r) => {
                format!(
                    "Trusted.Stmt.assign {} {}",
                    Self::place(p),
                    self.rvalue(r)
                )
            }
            ir::Stmt::PlaceMention(p) => {
                format!("Trusted.Stmt.placeMention {}", Self::place(p))
            }
            ir::Stmt::StorageLive(l) => {
                format!("Trusted.Stmt.storageLive ⟨{l}⟩")
            }
            ir::Stmt::StorageDead(l) => {
                format!("Trusted.Stmt.storageDead ⟨{l}⟩")
            }
            ir::Stmt::Nop => "Trusted.Stmt.nop".into(),
        }
    }

    fn terminator(&self, t: &ir::Terminator) -> String {
        match t {
            ir::Terminator::Return => "Trusted.Terminator.return_".into(),
            ir::Terminator::Goto(b) => format!("Trusted.Terminator.goto ⟨{b}⟩"),
            ir::Terminator::Unreachable => {
                "Trusted.Terminator.unreachable".into()
            }
            ir::Terminator::Panic => "Trusted.Terminator.panic".into(),
            ir::Terminator::Assert { cond, expected, target } => {
                format!(
                    "Trusted.Terminator.assert {} {expected} ⟨{target}⟩",
                    self.operand(cond)
                )
            }
            ir::Terminator::SwitchInt { discr, false_target, true_target } => {
                format!(
                    "Trusted.Terminator.switchInt {} ⟨{false_target}⟩ ⟨{true_target}⟩",
                    self.operand(discr)
                )
            }
            ir::Terminator::SizeOf { dst, ty, target } => {
                format!(
                    "Trusted.Terminator.callSizeOf {} {} ⟨{target}⟩",
                    Self::place(dst),
                    self.ty(ty)
                )
            }
            ir::Terminator::TransmuteCopy {
                dst,
                src_ty,
                dst_ty,
                op,
                target,
            } => format!(
                "Trusted.Terminator.callTransmuteCopy {} {} {} {} ⟨{target}⟩",
                Self::place(dst),
                self.ty(src_ty),
                self.ty(dst_ty),
                self.operand(op)
            ),
            ir::Terminator::Call1 { dst, callee, arg, target, type_args } => {
                format!(
                    "Trusted.Terminator.call1 {} ⟨{}⟩ {} ⟨{target}⟩ {}",
                    Self::place(dst),
                    self.body_id[callee],
                    self.operand(arg),
                    self.ty_list(type_args)
                )
            }
        }
    }

    fn access(a: ir::FieldAccess) -> &'static str {
        match a {
            ir::FieldAccess::PubSafe => "Trusted.FieldAccess.pubSafe",
            ir::FieldAccess::Priv => "Trusted.FieldAccess.priv",
        }
    }

    fn spec(s: &ir::Spec) -> String {
        match s {
            ir::Spec::EnsuresEqArg(l) => {
                format!("Trusted.PostSpec.ensuresEqArg {l}")
            }
        }
    }

    /// First-order `AdtDecl.invariant` field, if the struct declares one.
    fn invariant_field(inv: &Option<ir::InvariantSpec>) -> String {
        match inv {
            Some(ir::InvariantSpec { ne }) => {
                format!("\n      invariant := some {{ ne := {ne} }}")
            }
            None => String::new(),
        }
    }

    /// First-order `CapturedFn.requires` field, if the function declares one.
    fn requires_field(k: &ir::FnKind) -> String {
        match k {
            ir::FnKind::PubUnsafe {
                requires: Some(ir::RequiresSpec { arg_local, ne }),
            } => format!(
                "\n      requires := some {{ argLocal := {arg_local}, ne := {ne} }}"
            ),
            _ => String::new(),
        }
    }

    fn ty_list(&self, ts: &[ir::Ty]) -> String {
        list(ts.iter().map(|t| self.ty(t)))
    }
}

fn list(items: impl Iterator<Item = String>) -> String {
    format!("[{}]", items.collect::<Vec<_>>().join(", "))
}

/// Lean string literal denoting exactly `s`.
///
/// Lean's escapes are `\\`, `\"`, `\n`, `\t`, `\r`, `\xHH`, and `\uHHHH`
/// (four hex digits). Every other control character is written as `\uHHHH`;
/// all of them (Unicode category `Cc`) are below U+0100, so four digits
/// suffice. All other characters stand for themselves.
fn string_lit(s: &str) -> String {
    let mut out = String::from("\"");
    for c in s.chars() {
        match c {
            '\\' => out.push_str("\\\\"),
            '"' => out.push_str("\\\""),
            '\n' => out.push_str("\\n"),
            '\t' => out.push_str("\\t"),
            '\r' => out.push_str("\\r"),
            c if c.is_control() => {
                let _ = write!(out, "\\u{:04x}", c as u32);
            }
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

// ---------------------------------------------------------------------------
// Layout.
// ---------------------------------------------------------------------------

/// Renders `c` as `Mir.lean`, defining `Mir.crate : Trusted.Crate`.
pub fn render(c: &ir::Crate) -> String {
    let mut names = Names {
        body: BTreeMap::new(),
        body_id: BTreeMap::new(),
        adt: BTreeMap::new(),
    };
    for (i, a) in c.adts.iter().enumerate() {
        names.adt.insert(a.def, i);
    }
    for (i, (d, _)) in c.bodies.iter().enumerate() {
        names.body_id.insert(*d, i);
    }
    // Function bodies are `Mir.Fn.«name»`, constant bodies `Mir.Const.cN`
    // (N is the `DefIndex`). The namespaces keep the two kinds of name and
    // `Mir.crate` from colliding; the guillemets make any Rust identifier a
    // valid Lean name, including Lean keywords such as `def` or `end`.
    for f in &c.functions {
        names.body.insert(f.def, format!("Fn.«{}»", f.name));
    }
    for k in &c.constants {
        names.body.insert(k.def, format!("Const.c{}", k.def));
    }
    let const_path: BTreeMap<_, _> =
        c.constants.iter().map(|k| (k.def, &k.path)).collect();

    let mut out = String::new();
    out.push_str(
        "-- Generated by anneal-rustc-capture from rustc's Runtime(PostCleanup) \
         MIR.\n-- Do not edit.\n\nprelude\nimport Trusted\n\nnamespace Mir\n\n",
    );

    for (d, b) in &c.bodies {
        if let Some(p) = const_path.get(d) {
            let _ = writeln!(out, "/-- Constant body of `{p}`. -/");
        }
        let _ = writeln!(out, "def {} : Trusted.MirBody where", names.body[d]);
        let _ = writeln!(out, "  argTys := {}", names.ty_list(&b.arg_tys));
        let _ = writeln!(out, "  retTy := {}", names.ty(&b.ret_ty));
        let _ = writeln!(out, "  localCount := {}", b.local_count);
        out.push_str("  blocks := [\n");
        for (i, blk) in b.blocks.iter().enumerate() {
            let stmts: Vec<_> =
                blk.stmts.iter().map(|s| names.stmt(s)).collect();
            let sep = if i + 1 == b.blocks.len() { "" } else { "," };
            let _ = writeln!(
                out,
                "    {{ stmts := [{}]\n      terminator := {} }}{sep}",
                if stmts.is_empty() {
                    String::new()
                } else {
                    format!("\n        {}\n      ", stmts.join(",\n        "))
                },
                names.terminator(&blk.terminator)
            );
        }
        out.push_str("  ]\n");
        let rcs = b.required_consts.iter().map(|(k, args)| {
            format!("(⟨{}⟩, {})", names.body_id[k], names.ty_list(args))
        });
        let _ = writeln!(out, "  requiredConsts := {}\n", list(rcs));
    }

    out.push_str("def crate : Trusted.Crate where\n");
    if !c.adts.is_empty() {
        let decls = c.adts.iter().enumerate().map(|(i, a)| {
            format!(
                "\n    {{ id := {i}\n      fields := [{{ ty := {}, access := {} }}]{} }}",
                names.ty(&a.field_ty),
                Names::access(a.access),
                Names::invariant_field(&a.invariant),
            )
        });
        let _ = writeln!(
            out,
            "  adts := [{}\n  ]",
            decls.collect::<Vec<_>>().join(",")
        );
    }
    let body_decls = c.bodies.iter().map(|(d, _)| {
        format!(
            "\n    {{ id := ⟨{}⟩, body := {} }}",
            names.body_id[d], names.body[d]
        )
    });
    let _ = writeln!(
        out,
        "  bodies := [{}\n  ]",
        body_decls.collect::<Vec<_>>().join(",")
    );
    // Only public functions are roots; private ones appear as callees in
    // `bodies`.
    let roots: Vec<_> =
        c.functions.iter().filter(|f| f.kind != ir::FnKind::Private).collect();
    let fns = roots.iter().map(|f| {
        let req = Names::requires_field(&f.kind);
        format!(
            "\n    {{ name := {}\n      bodyId := ⟨{}⟩{req}\n      specs := {} }}",
            string_lit(&f.name),
            names.body_id[&f.def],
            list(f.specs.iter().map(Names::spec))
        )
    });
    let _ = writeln!(
        out,
        "  functions := [{}\n  ]",
        fns.collect::<Vec<_>>().join(",")
    );
    // One `rustcLowering` waiver per root function: the compilation
    // obligation can only be waived, never proved (its target semantics is
    // opaque), so trusting `rustc` is an explicit entry per function.
    let tcb = roots.iter().map(|f| {
        format!(
            "\n    Trusted.TCBItem.rustcLowering {} ⟨{}⟩",
            string_lit(&f.name),
            names.body_id[&f.def]
        )
    });
    let _ =
        writeln!(out, "  tcb := [{}\n  ]", tcb.collect::<Vec<_>>().join(","));
    out.push_str("\nend Mir\n");
    out
}
