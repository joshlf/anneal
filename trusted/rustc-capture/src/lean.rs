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
            ir::Ty::Isize => "Trusted.MirTy.isize".into(),
            ir::Ty::Uint(b) => format!("(Trusted.MirTy.uint {b})"),
            ir::Ty::Int(b) => format!("(Trusted.MirTy.int {b})"),
            ir::Ty::Float(b) => format!("(Trusted.MirTy.float {b})"),
            ir::Ty::Bool => "Trusted.MirTy.bool".into(),
            ir::Ty::Char => "Trusted.MirTy.char".into(),
            ir::Ty::Str => "Trusted.MirTy.str".into(),
            ir::Ty::Unit => "Trusted.MirTy.unit".into(),
            ir::Ty::Never => "Trusted.MirTy.never".into(),
            ir::Ty::Adt(d) => format!("(Trusted.MirTy.adt {})", self.adt[d]),
            ir::Ty::Param(i) => format!("(Trusted.MirTy.param {i})"),
            ir::Ty::Ref(inner) => {
                format!("(Trusted.MirTy.ref {})", self.ty(inner))
            }
            ir::Ty::RefMut(inner) => {
                format!("(Trusted.MirTy.refMut {})", self.ty(inner))
            }
            ir::Ty::RawPtr(inner, m) => {
                format!("(Trusted.MirTy.rawPtr {} {m})", self.ty(inner))
            }
            ir::Ty::Array(elem, len) => {
                format!("(Trusted.MirTy.array {} {len})", self.ty(elem))
            }
            ir::Ty::Slice(elem) => {
                format!("(Trusted.MirTy.slice {})", self.ty(elem))
            }
            ir::Ty::Tuple(elems) => {
                format!("(Trusted.MirTy.tuple {})", self.ty_list(elems))
            }
            ir::Ty::FnDef(name) => {
                format!("(Trusted.MirTy.fnDef {})", string_lit(name))
            }
            ir::Ty::FnPtr => "Trusted.MirTy.fnPtr".into(),
            ir::Ty::Unmodeled => "Trusted.MirTy.unmodeled".into(),
        }
    }

    fn val(&self, v: &ir::Val) -> String {
        match v {
            ir::Val::Uninit => "Trusted.MirVal.uninit".into(),
            ir::Val::Usize(n) => format!("(Trusted.MirVal.usize {n})"),
            ir::Val::Bool(b) => format!("(Trusted.MirVal.bool {b})"),
            ir::Val::Unit => "Trusted.MirVal.unit".into(),
        }
    }

    fn place_elem(&self, e: &ir::PlaceElem) -> String {
        match e {
            ir::PlaceElem::Deref => "Trusted.PlaceElem.deref".into(),
            ir::PlaceElem::Field(f) => format!("(Trusted.PlaceElem.field {f})"),
            ir::PlaceElem::Index(l) => {
                format!("(Trusted.PlaceElem.index ⟨{l}⟩)")
            }
            ir::PlaceElem::ConstantIndex {
                offset,
                min_length,
                from_end,
            } => format!(
                "(Trusted.PlaceElem.constantIndex {offset} {min_length} {from_end})"
            ),
            ir::PlaceElem::Subslice { from, to, from_end } => {
                format!("(Trusted.PlaceElem.subslice {from} {to} {from_end})")
            }
            ir::PlaceElem::Downcast(v) => {
                format!("(Trusted.PlaceElem.downcast {v})")
            }
            ir::PlaceElem::OpaqueCast(t) => {
                format!("(Trusted.PlaceElem.opaqueCast {})", self.ty(t))
            }
            ir::PlaceElem::UnwrapUnsafeBinder(t) => {
                format!("(Trusted.PlaceElem.unwrapUnsafeBinder {})", self.ty(t))
            }
        }
    }

    fn place(&self, p: &ir::Place) -> String {
        format!(
            "{{ loc := ⟨{}⟩, projection := {} }}",
            p.loc,
            list(p.projection.iter().map(|e| self.place_elem(e)))
        )
    }

    fn runtime_checks(chk: ir::RuntimeChecks) -> &'static str {
        match chk {
            ir::RuntimeChecks::UbChecks => "Trusted.RuntimeChecks.ubChecks",
            ir::RuntimeChecks::ContractChecks => {
                "Trusted.RuntimeChecks.contractChecks"
            }
            ir::RuntimeChecks::OverflowChecks => {
                "Trusted.RuntimeChecks.overflowChecks"
            }
        }
    }

    fn operand(&self, o: &ir::Operand) -> String {
        match o {
            ir::Operand::Copy(p) => {
                format!("(Trusted.Operand.copy {})", self.place(p))
            }
            ir::Operand::Move(p) => {
                format!("(Trusted.Operand.move {})", self.place(p))
            }
            ir::Operand::Const(v) => {
                format!("(Trusted.Operand.constVal {})", self.val(v))
            }
            ir::Operand::RuntimeChecks(chk) => format!(
                "(Trusted.Operand.runtimeChecks {})",
                Self::runtime_checks(*chk)
            ),
        }
    }

    fn raw_ptr_kind(k: ir::RawPtrKind) -> &'static str {
        match k {
            ir::RawPtrKind::Mut => "Trusted.RawPtrKind.mut_",
            ir::RawPtrKind::Const => "Trusted.RawPtrKind.const_",
            ir::RawPtrKind::FakeForPtrMetadata => {
                "Trusted.RawPtrKind.fakeForPtrMetadata"
            }
        }
    }

    fn cast_kind(k: ir::CastKind) -> &'static str {
        match k {
            ir::CastKind::PointerExposeProvenance => {
                "Trusted.CastKind.pointerExposeProvenance"
            }
            ir::CastKind::PointerWithExposedProvenance => {
                "Trusted.CastKind.pointerWithExposedProvenance"
            }
            ir::CastKind::PointerCoercion => "Trusted.CastKind.pointerCoercion",
            ir::CastKind::IntToInt => "Trusted.CastKind.intToInt",
            ir::CastKind::FloatToInt => "Trusted.CastKind.floatToInt",
            ir::CastKind::FloatToFloat => "Trusted.CastKind.floatToFloat",
            ir::CastKind::IntToFloat => "Trusted.CastKind.intToFloat",
            ir::CastKind::PtrToPtr => "Trusted.CastKind.ptrToPtr",
            ir::CastKind::FnPtrToPtr => "Trusted.CastKind.fnPtrToPtr",
            ir::CastKind::Transmute => "Trusted.CastKind.transmute",
            ir::CastKind::Subtype => "Trusted.CastKind.subtype",
        }
    }

    fn un_op(op: ir::UnOp) -> &'static str {
        match op {
            ir::UnOp::Not => "Trusted.UnOp.not",
            ir::UnOp::Neg => "Trusted.UnOp.neg",
            ir::UnOp::PtrMetadata => "Trusted.UnOp.ptrMetadata",
        }
    }

    fn bin_op(op: ir::BinOp) -> &'static str {
        match op {
            ir::BinOp::Add => "Trusted.BinOp.add",
            ir::BinOp::AddUnchecked => "Trusted.BinOp.addUnchecked",
            ir::BinOp::AddWithOverflow => "Trusted.BinOp.addWithOverflow",
            ir::BinOp::Sub => "Trusted.BinOp.sub",
            ir::BinOp::SubUnchecked => "Trusted.BinOp.subUnchecked",
            ir::BinOp::SubWithOverflow => "Trusted.BinOp.subWithOverflow",
            ir::BinOp::Mul => "Trusted.BinOp.mul",
            ir::BinOp::MulUnchecked => "Trusted.BinOp.mulUnchecked",
            ir::BinOp::MulWithOverflow => "Trusted.BinOp.mulWithOverflow",
            ir::BinOp::Div => "Trusted.BinOp.div",
            ir::BinOp::Rem => "Trusted.BinOp.rem",
            ir::BinOp::BitXor => "Trusted.BinOp.bitXor",
            ir::BinOp::BitAnd => "Trusted.BinOp.bitAnd",
            ir::BinOp::BitOr => "Trusted.BinOp.bitOr",
            ir::BinOp::Shl => "Trusted.BinOp.shl",
            ir::BinOp::ShlUnchecked => "Trusted.BinOp.shlUnchecked",
            ir::BinOp::Shr => "Trusted.BinOp.shr",
            ir::BinOp::ShrUnchecked => "Trusted.BinOp.shrUnchecked",
            ir::BinOp::Eq => "Trusted.BinOp.eq",
            ir::BinOp::Lt => "Trusted.BinOp.lt",
            ir::BinOp::Le => "Trusted.BinOp.le",
            ir::BinOp::Ne => "Trusted.BinOp.ne",
            ir::BinOp::Ge => "Trusted.BinOp.ge",
            ir::BinOp::Gt => "Trusted.BinOp.gt",
            ir::BinOp::Cmp => "Trusted.BinOp.cmp",
            ir::BinOp::Offset => "Trusted.BinOp.offset",
        }
    }

    fn rvalue(&self, r: &ir::Rvalue) -> String {
        match r {
            ir::Rvalue::Use(o) => {
                format!("(Trusted.Rvalue.use {})", self.operand(o))
            }
            ir::Rvalue::Repeat(o, len) => {
                format!("(Trusted.Rvalue.repeat {} {len})", self.operand(o))
            }
            ir::Rvalue::Ref(p) => {
                format!("(Trusted.Rvalue.ref {})", self.place(p))
            }
            ir::Rvalue::RefMut(p) => {
                format!("(Trusted.Rvalue.refMut {})", self.place(p))
            }
            ir::Rvalue::RefFake(p) => {
                format!("(Trusted.Rvalue.refFake {})", self.place(p))
            }
            ir::Rvalue::ThreadLocalRef(d) => {
                format!("(Trusted.Rvalue.threadLocalRef {d})")
            }
            ir::Rvalue::RawPtr(k, p) => format!(
                "(Trusted.Rvalue.rawPtr {} {})",
                Self::raw_ptr_kind(*k),
                self.place(p)
            ),
            ir::Rvalue::Cast(k, o, t) => format!(
                "(Trusted.Rvalue.cast {} {} {})",
                Self::cast_kind(*k),
                self.operand(o),
                self.ty(t)
            ),
            ir::Rvalue::BinaryOp(op, a, b) => format!(
                "(Trusted.Rvalue.binaryOp {} {} {})",
                Self::bin_op(*op),
                self.operand(a),
                self.operand(b)
            ),
            ir::Rvalue::UnaryOp(op, o) => format!(
                "(Trusted.Rvalue.unaryOp {} {})",
                Self::un_op(*op),
                self.operand(o)
            ),
            ir::Rvalue::Discriminant(p) => {
                format!("(Trusted.Rvalue.discriminant {})", self.place(p))
            }
            ir::Rvalue::Aggregate(d, o) => {
                format!(
                    "(Trusted.Rvalue.aggregate {} {})",
                    self.adt[d],
                    self.operand(o)
                )
            }
            ir::Rvalue::AggregateFields(ops) => format!(
                "(Trusted.Rvalue.aggregateFields {})",
                list(ops.iter().map(|o| self.operand(o)))
            ),
            ir::Rvalue::CopyForDeref(p) => {
                format!("(Trusted.Rvalue.copyForDeref {})", self.place(p))
            }
            ir::Rvalue::WrapUnsafeBinder(o, t) => format!(
                "(Trusted.Rvalue.wrapUnsafeBinder {} {})",
                self.operand(o),
                self.ty(t)
            ),
            ir::Rvalue::Reborrow(t, m, p) => format!(
                "(Trusted.Rvalue.reborrow {} {m} {})",
                self.ty(t),
                self.place(p)
            ),
        }
    }

    fn stmt(&self, s: &ir::Stmt) -> String {
        match s {
            ir::Stmt::Assign(p, r) => {
                format!(
                    "Trusted.Stmt.assign {} {}",
                    self.place(p),
                    self.rvalue(r)
                )
            }
            ir::Stmt::FakeRead(p) => {
                format!("Trusted.Stmt.fakeRead {}", self.place(p))
            }
            ir::Stmt::SetDiscriminant(p, v) => {
                format!("Trusted.Stmt.setDiscriminant {} {v}", self.place(p))
            }
            ir::Stmt::StorageLive(l) => {
                format!("Trusted.Stmt.storageLive ⟨{l}⟩")
            }
            ir::Stmt::StorageDead(l) => {
                format!("Trusted.Stmt.storageDead ⟨{l}⟩")
            }
            ir::Stmt::PlaceMention(p) => {
                format!("Trusted.Stmt.placeMention {}", self.place(p))
            }
            ir::Stmt::AscribeUserType(p) => {
                format!("Trusted.Stmt.ascribeUserType {}", self.place(p))
            }
            ir::Stmt::Coverage => "Trusted.Stmt.coverage".into(),
            ir::Stmt::Intrinsic(intr) => {
                let i = match intr {
                    ir::NonDivergingIntrinsic::Assume(o) => format!(
                        "(Trusted.NonDivergingIntrinsic.assume {})",
                        self.operand(o)
                    ),
                    ir::NonDivergingIntrinsic::CopyNonOverlapping {
                        src,
                        dst,
                        count,
                    } => format!(
                        "(Trusted.NonDivergingIntrinsic.copyNonOverlapping {} {} {})",
                        self.operand(src),
                        self.operand(dst),
                        self.operand(count)
                    ),
                };
                format!("Trusted.Stmt.intrinsic {i}")
            }
            ir::Stmt::ConstEvalCounter => {
                "Trusted.Stmt.constEvalCounter".into()
            }
            ir::Stmt::Nop => "Trusted.Stmt.nop".into(),
            ir::Stmt::BackwardIncompatibleDropHint(p) => format!(
                "Trusted.Stmt.backwardIncompatibleDropHint {}",
                self.place(p)
            ),
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
            ir::Terminator::UnwindResume => {
                "Trusted.Terminator.unwindResume".into()
            }
            ir::Terminator::UnwindTerminate => {
                "Trusted.Terminator.unwindTerminate".into()
            }
            ir::Terminator::Drop { place, target } => format!(
                "Trusted.Terminator.drop {} ⟨{target}⟩",
                self.place(place)
            ),
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
            ir::Terminator::SwitchIntGeneral {
                discr,
                targets,
                otherwise,
            } => format!(
                "Trusted.Terminator.switchIntGeneral {} {} ⟨{otherwise}⟩",
                self.operand(discr),
                list(
                    targets
                        .iter()
                        .map(|(v, b)| format!("({v}, ⟨{b}⟩)"))
                )
            ),
            ir::Terminator::SizeOf { dst, ty, target } => {
                format!(
                    "Trusted.Terminator.callSizeOf {} {} ⟨{target}⟩",
                    self.place(dst),
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
                self.place(dst),
                self.ty(src_ty),
                self.ty(dst_ty),
                self.operand(op)
            ),
            ir::Terminator::Call1 { dst, callee, arg, target, type_args } => {
                format!(
                    "Trusted.Terminator.call1 {} ⟨{}⟩ {} ⟨{target}⟩ {}",
                    self.place(dst),
                    self.body_id[callee],
                    self.operand(arg),
                    self.ty_list(type_args)
                )
            }
            ir::Terminator::Call { dst, args, target } => format!(
                "Trusted.Terminator.call {} {} {}",
                self.place(dst),
                list(args.iter().map(|o| self.operand(o))),
                match target {
                    Some(b) => format!("(some ⟨{b}⟩)"),
                    None => "none".into(),
                }
            ),
            ir::Terminator::TailCall { args } => format!(
                "Trusted.Terminator.tailCall {}",
                list(args.iter().map(|o| self.operand(o)))
            ),
            ir::Terminator::Yield { val, resume, resume_arg } => format!(
                "Trusted.Terminator.yield {} ⟨{resume}⟩ {}",
                self.operand(val),
                self.place(resume_arg)
            ),
            ir::Terminator::CoroutineDrop => {
                "Trusted.Terminator.coroutineDrop".into()
            }
            ir::Terminator::FalseEdge {
                real_target,
                imaginary_target,
            } => format!(
                "Trusted.Terminator.falseEdge ⟨{real_target}⟩ ⟨{imaginary_target}⟩"
            ),
            ir::Terminator::FalseUnwind { real_target } => {
                format!("Trusted.Terminator.falseUnwind ⟨{real_target}⟩")
            }
            ir::Terminator::InlineAsm => "Trusted.Terminator.inlineAsm".into(),
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
    fn requires_field(req: &Option<ir::RequiresSpec>) -> String {
        match req {
            Some(ir::RequiresSpec { arg_local, ne }) => format!(
                "\n      requires := some {{ argLocal := {arg_local}, ne := {ne} }}"
            ),
            None => String::new(),
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
    // `bodies`. Sort by function name so `functions` and `tcb` have a canonical
    // deterministic order independent of source declaration order.
    let mut roots: Vec<_> = c
        .functions
        .iter()
        .filter_map(|f| match &f.kind {
            ir::FnKind::Private => None,
            ir::FnKind::Exported { requires, specs } => {
                Some((f, requires, specs))
            }
        })
        .collect();
    roots.sort_by(|a, b| a.0.name.cmp(&b.0.name));
    let fns = roots.iter().map(|(f, requires, specs)| {
        let req = Names::requires_field(requires);
        format!(
            "\n    {{ name := {}\n      bodyId := ⟨{}⟩{req}\n      specs := {} }}",
            string_lit(&f.name),
            names.body_id[&f.def],
            list(specs.iter().map(Names::spec))
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
    let tcb = roots.iter().map(|(f, _, _)| {
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
