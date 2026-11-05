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
//! Every emitted term is root-anchored (`_root_.Trusted.MirTy.usize`,
//! `_root_.Bool.true`, `_root_.Option.some`), so its meaning does not depend
//! on Lean's expected-type elaboration or ambient namespace imports.

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
    fn bool_lit(b: bool) -> &'static str {
        if b {
            "_root_.Bool.true"
        } else {
            "_root_.Bool.false"
        }
    }

    fn ty(&self, t: &ir::Ty) -> String {
        match t {
            ir::Ty::Usize => "_root_.Trusted.MirTy.usize".into(),
            ir::Ty::Isize => "_root_.Trusted.MirTy.isize".into(),
            ir::Ty::Uint(b) => format!("(_root_.Trusted.MirTy.uint {b})"),
            ir::Ty::Int(b) => format!("(_root_.Trusted.MirTy.int {b})"),
            ir::Ty::Float(b) => format!("(_root_.Trusted.MirTy.float {b})"),
            ir::Ty::Bool => "_root_.Trusted.MirTy.bool".into(),
            ir::Ty::Char => "_root_.Trusted.MirTy.char".into(),
            ir::Ty::Str => "_root_.Trusted.MirTy.str".into(),
            ir::Ty::Unit => "_root_.Trusted.MirTy.unit".into(),
            ir::Ty::Never => "_root_.Trusted.MirTy.never".into(),
            ir::Ty::Adt(d) => {
                format!("(_root_.Trusted.MirTy.adt {})", self.adt[d])
            }
            ir::Ty::Param(i) => format!("(_root_.Trusted.MirTy.param {i})"),
            ir::Ty::Ref(inner) => {
                format!("(_root_.Trusted.MirTy.ref {})", self.ty(inner))
            }
            ir::Ty::RefMut(inner) => {
                format!("(_root_.Trusted.MirTy.refMut {})", self.ty(inner))
            }
            ir::Ty::RawPtr(inner, m) => format!(
                "(_root_.Trusted.MirTy.rawPtr {} {})",
                self.ty(inner),
                Self::bool_lit(*m)
            ),
            ir::Ty::Array(elem, len) => {
                format!("(_root_.Trusted.MirTy.array {} {len})", self.ty(elem))
            }
            ir::Ty::Slice(elem) => {
                format!("(_root_.Trusted.MirTy.slice {})", self.ty(elem))
            }
            ir::Ty::Tuple(elems) => {
                format!("(_root_.Trusted.MirTy.tuple {})", self.ty_list(elems))
            }
            ir::Ty::FnDef(name) => {
                format!("(_root_.Trusted.MirTy.fnDef {})", string_lit(name))
            }
            ir::Ty::FnPtr => "_root_.Trusted.MirTy.fnPtr".into(),
            ir::Ty::Unmodeled => "_root_.Trusted.MirTy.unmodeled".into(),
        }
    }

    fn val(&self, v: &ir::Val) -> String {
        match v {
            ir::Val::Uninit => "_root_.Trusted.MirVal.uninit".into(),
            ir::Val::Usize(n) => format!("(_root_.Trusted.MirVal.usize {n})"),
            ir::Val::Bool(b) => {
                format!("(_root_.Trusted.MirVal.bool {})", Self::bool_lit(*b))
            }
            ir::Val::Unit => "_root_.Trusted.MirVal.unit".into(),
        }
    }

    fn place_elem(&self, e: &ir::PlaceElem) -> String {
        match e {
            ir::PlaceElem::Deref => "_root_.Trusted.PlaceElem.deref".into(),
            ir::PlaceElem::Field(f) => {
                format!("(_root_.Trusted.PlaceElem.field {f})")
            }
            ir::PlaceElem::Index(l) => {
                format!("(_root_.Trusted.PlaceElem.index ⟨{l}⟩)")
            }
            ir::PlaceElem::ConstantIndex {
                offset,
                min_length,
                from_end,
            } => format!(
                "(_root_.Trusted.PlaceElem.constantIndex {offset} {min_length} {})",
                Self::bool_lit(*from_end)
            ),
            ir::PlaceElem::Subslice { from, to, from_end } => format!(
                "(_root_.Trusted.PlaceElem.subslice {from} {to} {})",
                Self::bool_lit(*from_end)
            ),
            ir::PlaceElem::Downcast(v) => {
                format!("(_root_.Trusted.PlaceElem.downcast {v})")
            }
            ir::PlaceElem::OpaqueCast(t) => {
                format!("(_root_.Trusted.PlaceElem.opaqueCast {})", self.ty(t))
            }
            ir::PlaceElem::UnwrapUnsafeBinder(t) => format!(
                "(_root_.Trusted.PlaceElem.unwrapUnsafeBinder {})",
                self.ty(t)
            ),
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
            ir::RuntimeChecks::UbChecks => {
                "_root_.Trusted.RuntimeChecks.ubChecks"
            }
            ir::RuntimeChecks::ContractChecks => {
                "_root_.Trusted.RuntimeChecks.contractChecks"
            }
            ir::RuntimeChecks::OverflowChecks => {
                "_root_.Trusted.RuntimeChecks.overflowChecks"
            }
        }
    }

    fn operand(&self, o: &ir::Operand) -> String {
        match o {
            ir::Operand::Copy(p) => {
                format!("(_root_.Trusted.Operand.copy {})", self.place(p))
            }
            ir::Operand::Move(p) => {
                format!("(_root_.Trusted.Operand.move {})", self.place(p))
            }
            ir::Operand::Const(v) => {
                format!("(_root_.Trusted.Operand.constVal {})", self.val(v))
            }
            ir::Operand::RuntimeChecks(chk) => format!(
                "(_root_.Trusted.Operand.runtimeChecks {})",
                Self::runtime_checks(*chk)
            ),
        }
    }

    fn raw_ptr_kind(k: ir::RawPtrKind) -> &'static str {
        match k {
            ir::RawPtrKind::Mut => "_root_.Trusted.RawPtrKind.mut_",
            ir::RawPtrKind::Const => "_root_.Trusted.RawPtrKind.const_",
            ir::RawPtrKind::FakeForPtrMetadata => {
                "_root_.Trusted.RawPtrKind.fakeForPtrMetadata"
            }
        }
    }

    fn cast_kind(k: ir::CastKind) -> &'static str {
        match k {
            ir::CastKind::PointerExposeProvenance => {
                "_root_.Trusted.CastKind.pointerExposeProvenance"
            }
            ir::CastKind::PointerWithExposedProvenance => {
                "_root_.Trusted.CastKind.pointerWithExposedProvenance"
            }
            ir::CastKind::PointerCoercion => {
                "_root_.Trusted.CastKind.pointerCoercion"
            }
            ir::CastKind::IntToInt => "_root_.Trusted.CastKind.intToInt",
            ir::CastKind::FloatToInt => "_root_.Trusted.CastKind.floatToInt",
            ir::CastKind::FloatToFloat => {
                "_root_.Trusted.CastKind.floatToFloat"
            }
            ir::CastKind::IntToFloat => "_root_.Trusted.CastKind.intToFloat",
            ir::CastKind::PtrToPtr => "_root_.Trusted.CastKind.ptrToPtr",
            ir::CastKind::FnPtrToPtr => "_root_.Trusted.CastKind.fnPtrToPtr",
            ir::CastKind::Transmute => "_root_.Trusted.CastKind.transmute",
            ir::CastKind::Subtype => "_root_.Trusted.CastKind.subtype",
        }
    }

    fn un_op(op: ir::UnOp) -> &'static str {
        match op {
            ir::UnOp::Not => "_root_.Trusted.UnOp.not",
            ir::UnOp::Neg => "_root_.Trusted.UnOp.neg",
            ir::UnOp::PtrMetadata => "_root_.Trusted.UnOp.ptrMetadata",
        }
    }

    fn bin_op(op: ir::BinOp) -> &'static str {
        match op {
            ir::BinOp::Add => "_root_.Trusted.BinOp.add",
            ir::BinOp::AddUnchecked => "_root_.Trusted.BinOp.addUnchecked",
            ir::BinOp::AddWithOverflow => {
                "_root_.Trusted.BinOp.addWithOverflow"
            }
            ir::BinOp::Sub => "_root_.Trusted.BinOp.sub",
            ir::BinOp::SubUnchecked => "_root_.Trusted.BinOp.subUnchecked",
            ir::BinOp::SubWithOverflow => {
                "_root_.Trusted.BinOp.subWithOverflow"
            }
            ir::BinOp::Mul => "_root_.Trusted.BinOp.mul",
            ir::BinOp::MulUnchecked => "_root_.Trusted.BinOp.mulUnchecked",
            ir::BinOp::MulWithOverflow => {
                "_root_.Trusted.BinOp.mulWithOverflow"
            }
            ir::BinOp::Div => "_root_.Trusted.BinOp.div",
            ir::BinOp::Rem => "_root_.Trusted.BinOp.rem",
            ir::BinOp::BitXor => "_root_.Trusted.BinOp.bitXor",
            ir::BinOp::BitAnd => "_root_.Trusted.BinOp.bitAnd",
            ir::BinOp::BitOr => "_root_.Trusted.BinOp.bitOr",
            ir::BinOp::Shl => "_root_.Trusted.BinOp.shl",
            ir::BinOp::ShlUnchecked => "_root_.Trusted.BinOp.shlUnchecked",
            ir::BinOp::Shr => "_root_.Trusted.BinOp.shr",
            ir::BinOp::ShrUnchecked => "_root_.Trusted.BinOp.shrUnchecked",
            ir::BinOp::Eq => "_root_.Trusted.BinOp.eq",
            ir::BinOp::Lt => "_root_.Trusted.BinOp.lt",
            ir::BinOp::Le => "_root_.Trusted.BinOp.le",
            ir::BinOp::Ne => "_root_.Trusted.BinOp.ne",
            ir::BinOp::Ge => "_root_.Trusted.BinOp.ge",
            ir::BinOp::Gt => "_root_.Trusted.BinOp.gt",
            ir::BinOp::Cmp => "_root_.Trusted.BinOp.cmp",
            ir::BinOp::Offset => "_root_.Trusted.BinOp.offset",
        }
    }

    fn rvalue(&self, r: &ir::Rvalue) -> String {
        match r {
            ir::Rvalue::Use(o) => {
                format!("(_root_.Trusted.Rvalue.use {})", self.operand(o))
            }
            ir::Rvalue::Repeat(o, len) => format!(
                "(_root_.Trusted.Rvalue.repeat {} {len})",
                self.operand(o)
            ),
            ir::Rvalue::Ref(p) => {
                format!("(_root_.Trusted.Rvalue.ref {})", self.place(p))
            }
            ir::Rvalue::RefMut(p) => {
                format!("(_root_.Trusted.Rvalue.refMut {})", self.place(p))
            }
            ir::Rvalue::RefFake(p) => {
                format!("(_root_.Trusted.Rvalue.refFake {})", self.place(p))
            }
            ir::Rvalue::ThreadLocalRef(d) => {
                format!("(_root_.Trusted.Rvalue.threadLocalRef {d})")
            }
            ir::Rvalue::RawPtr(k, p) => format!(
                "(_root_.Trusted.Rvalue.rawPtr {} {})",
                Self::raw_ptr_kind(*k),
                self.place(p)
            ),
            ir::Rvalue::Cast(k, o, t) => format!(
                "(_root_.Trusted.Rvalue.cast {} {} {})",
                Self::cast_kind(*k),
                self.operand(o),
                self.ty(t)
            ),
            ir::Rvalue::BinaryOp(op, a, b) => format!(
                "(_root_.Trusted.Rvalue.binaryOp {} {} {})",
                Self::bin_op(*op),
                self.operand(a),
                self.operand(b)
            ),
            ir::Rvalue::UnaryOp(op, o) => format!(
                "(_root_.Trusted.Rvalue.unaryOp {} {})",
                Self::un_op(*op),
                self.operand(o)
            ),
            ir::Rvalue::Discriminant(p) => format!(
                "(_root_.Trusted.Rvalue.discriminant {})",
                self.place(p)
            ),
            ir::Rvalue::Aggregate(d, o) => format!(
                "(_root_.Trusted.Rvalue.aggregate {} {})",
                self.adt[d],
                self.operand(o)
            ),
            ir::Rvalue::AggregateFields(ops) => format!(
                "(_root_.Trusted.Rvalue.aggregateFields {})",
                list(ops.iter().map(|o| self.operand(o)))
            ),
            ir::Rvalue::CopyForDeref(p) => format!(
                "(_root_.Trusted.Rvalue.copyForDeref {})",
                self.place(p)
            ),
            ir::Rvalue::WrapUnsafeBinder(o, t) => format!(
                "(_root_.Trusted.Rvalue.wrapUnsafeBinder {} {})",
                self.operand(o),
                self.ty(t)
            ),
            ir::Rvalue::Reborrow(t, m, p) => format!(
                "(_root_.Trusted.Rvalue.reborrow {} {} {})",
                self.ty(t),
                Self::bool_lit(*m),
                self.place(p)
            ),
        }
    }

    fn stmt(&self, s: &ir::Stmt) -> String {
        match s {
            ir::Stmt::Assign(p, r) => format!(
                "_root_.Trusted.Stmt.assign {} {}",
                self.place(p),
                self.rvalue(r)
            ),
            ir::Stmt::FakeRead(p) => {
                format!("_root_.Trusted.Stmt.fakeRead {}", self.place(p))
            }
            ir::Stmt::SetDiscriminant(p, v) => format!(
                "_root_.Trusted.Stmt.setDiscriminant {} {v}",
                self.place(p)
            ),
            ir::Stmt::StorageLive(l) => {
                format!("_root_.Trusted.Stmt.storageLive ⟨{l}⟩")
            }
            ir::Stmt::StorageDead(l) => {
                format!("_root_.Trusted.Stmt.storageDead ⟨{l}⟩")
            }
            ir::Stmt::PlaceMention(p) => {
                format!("_root_.Trusted.Stmt.placeMention {}", self.place(p))
            }
            ir::Stmt::AscribeUserType(p) => {
                format!("_root_.Trusted.Stmt.ascribeUserType {}", self.place(p))
            }
            ir::Stmt::Coverage => "_root_.Trusted.Stmt.coverage".into(),
            ir::Stmt::Intrinsic(intr) => {
                let i = match intr {
                    ir::NonDivergingIntrinsic::Assume(o) => format!(
                        "(_root_.Trusted.NonDivergingIntrinsic.assume {})",
                        self.operand(o)
                    ),
                    ir::NonDivergingIntrinsic::CopyNonOverlapping {
                        src,
                        dst,
                        count,
                    } => format!(
                        "(_root_.Trusted.NonDivergingIntrinsic.copyNonOverlapping {} {} {})",
                        self.operand(src),
                        self.operand(dst),
                        self.operand(count)
                    ),
                };
                format!("_root_.Trusted.Stmt.intrinsic {i}")
            }
            ir::Stmt::ConstEvalCounter => {
                "_root_.Trusted.Stmt.constEvalCounter".into()
            }
            ir::Stmt::Nop => "_root_.Trusted.Stmt.nop".into(),
            ir::Stmt::BackwardIncompatibleDropHint(p) => format!(
                "_root_.Trusted.Stmt.backwardIncompatibleDropHint {}",
                self.place(p)
            ),
        }
    }

    fn terminator(&self, t: &ir::Terminator) -> String {
        match t {
            ir::Terminator::Return => {
                "_root_.Trusted.Terminator.return_".into()
            }
            ir::Terminator::Goto(b) => {
                format!("_root_.Trusted.Terminator.goto ⟨{b}⟩")
            }
            ir::Terminator::Unreachable => {
                "_root_.Trusted.Terminator.unreachable".into()
            }
            ir::Terminator::Panic => "_root_.Trusted.Terminator.panic".into(),
            ir::Terminator::UnwindResume => {
                "_root_.Trusted.Terminator.unwindResume".into()
            }
            ir::Terminator::UnwindTerminate => {
                "_root_.Trusted.Terminator.unwindTerminate".into()
            }
            ir::Terminator::Drop { place, target } => format!(
                "_root_.Trusted.Terminator.drop {} ⟨{target}⟩",
                self.place(place)
            ),
            ir::Terminator::Assert { cond, expected, target } => format!(
                "_root_.Trusted.Terminator.assert {} {} ⟨{target}⟩",
                self.operand(cond),
                Self::bool_lit(*expected)
            ),
            ir::Terminator::SwitchInt { discr, false_target, true_target } => {
                format!(
                    "_root_.Trusted.Terminator.switchInt {} ⟨{false_target}⟩ ⟨{true_target}⟩",
                    self.operand(discr)
                )
            }
            ir::Terminator::SwitchIntGeneral {
                discr,
                targets,
                otherwise,
            } => format!(
                "_root_.Trusted.Terminator.switchIntGeneral {} {} ⟨{otherwise}⟩",
                self.operand(discr),
                list(
                    targets
                        .iter()
                        .map(|(v, b)| format!("({v}, ⟨{b}⟩)"))
                )
            ),
            ir::Terminator::SizeOf { dst, ty, target } => format!(
                "_root_.Trusted.Terminator.callSizeOf {} {} ⟨{target}⟩",
                self.place(dst),
                self.ty(ty)
            ),
            ir::Terminator::TransmuteCopy {
                dst,
                src_ty,
                dst_ty,
                op,
                target,
            } => format!(
                "_root_.Trusted.Terminator.callTransmuteCopy {} {} {} {} ⟨{target}⟩",
                self.place(dst),
                self.ty(src_ty),
                self.ty(dst_ty),
                self.operand(op)
            ),
            ir::Terminator::Call1 { dst, callee, arg, target, type_args } => {
                format!(
                    "_root_.Trusted.Terminator.call1 {} ⟨{}⟩ {} ⟨{target}⟩ {}",
                    self.place(dst),
                    self.body_id[callee],
                    self.operand(arg),
                    self.ty_list(type_args)
                )
            }
            ir::Terminator::Call { dst, args, target } => format!(
                "_root_.Trusted.Terminator.call {} {} {}",
                self.place(dst),
                list(args.iter().map(|o| self.operand(o))),
                match target {
                    Some(b) => format!("(_root_.Option.some ⟨{b}⟩)"),
                    None => "_root_.Option.none".into(),
                }
            ),
            ir::Terminator::TailCall { args } => format!(
                "_root_.Trusted.Terminator.tailCall {}",
                list(args.iter().map(|o| self.operand(o)))
            ),
            ir::Terminator::Yield { val, resume, resume_arg } => format!(
                "_root_.Trusted.Terminator.yield {} ⟨{resume}⟩ {}",
                self.operand(val),
                self.place(resume_arg)
            ),
            ir::Terminator::CoroutineDrop => {
                "_root_.Trusted.Terminator.coroutineDrop".into()
            }
            ir::Terminator::FalseEdge {
                real_target,
                imaginary_target,
            } => format!(
                "_root_.Trusted.Terminator.falseEdge ⟨{real_target}⟩ ⟨{imaginary_target}⟩"
            ),
            ir::Terminator::FalseUnwind { real_target } => {
                format!("_root_.Trusted.Terminator.falseUnwind ⟨{real_target}⟩")
            }
            ir::Terminator::InlineAsm => {
                "_root_.Trusted.Terminator.inlineAsm".into()
            }
        }
    }

    fn access(a: ir::FieldAccess) -> &'static str {
        match a {
            ir::FieldAccess::PubSafe => "_root_.Trusted.FieldAccess.pubSafe",
            ir::FieldAccess::Priv => "_root_.Trusted.FieldAccess.priv",
        }
    }

    fn spec(s: &ir::Spec) -> String {
        match s {
            ir::Spec::EnsuresEqArg(l) => {
                format!("_root_.Trusted.PostSpec.ensuresEqArg {l}")
            }
        }
    }

    /// First-order `AdtDecl.invariant` field, if the struct declares one.
    fn invariant_field(inv: &Option<ir::InvariantSpec>) -> String {
        match inv {
            Some(ir::InvariantSpec { ne }) => {
                format!("\n      invariant := _root_.Option.some {{ ne := {ne} }}")
            }
            None => String::new(),
        }
    }

    /// First-order `CapturedFn.requires` field, if the function declares one.
    fn requires_field(req: &Option<ir::RequiresSpec>) -> String {
        match req {
            Some(ir::RequiresSpec { arg_local, ne }) => format!(
                "\n      requires := _root_.Option.some {{ argLocal := {arg_local}, ne := {ne} }}"
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
    // Function bodies are `Mir.Fn.«name»` (and `Mir.Fn.«name».debug` when the
    // debug profile produces a distinct body), constant bodies `Mir.Const.cN`
    // (N is the `DefIndex`). The namespaces keep the two kinds of name and
    // `Mir.crate` from colliding; the guillemets make any Rust identifier a
    // valid Lean name, including Lean keywords such as `def` or `end`.
    for f in &c.functions {
        names.body.insert(f.def, format!("Fn.«{}»", f.name));
        if let Some(dbg_def) = f.debug_body {
            names.body.insert(dbg_def, format!("Fn.«{}».debug", f.name));
        }
    }
    for k in &c.constants {
        names.body.insert(k.def, format!("Const.c{}", k.def));
    }
    let const_path: BTreeMap<_, _> =
        c.constants.iter().map(|k| (k.def, &k.path)).collect();

    // Only public functions are roots; private ones appear as callees in
    // `bodies`.
    let roots: Vec<_> = c
        .functions
        .iter()
        .filter_map(|f| match &f.kind {
            ir::FnKind::Private => None,
            ir::FnKind::Exported {
                requires,
                specs,
                trusted_reason,
            } => Some((f, requires, specs, trusted_reason)),
        })
        .collect();

    let mut out = String::new();
    out.push_str(
        "-- Generated by anneal-rustc-capture from rustc's Runtime(PostCleanup) \
         MIR.\n-- Do not edit.\n",
    );
    for (f, _, _, trusted_reason) in &roots {
        if let Some(reason) = trusted_reason {
            let _ = writeln!(
                out,
                "-- anneal-waiver: fnBody {} reason = {}",
                string_lit(&f.name),
                string_lit(reason)
            );
        }
    }
    out.push_str("\nprelude\nimport Trusted\n\nnamespace Mir\n\n");

    for (d, b) in &c.bodies {
        if let Some(p) = const_path.get(d) {
            let _ = writeln!(out, "/-- Constant body of `{p}`. -/");
        }
        let _ = writeln!(
            out,
            "def {} : _root_.Trusted.MirBody where",
            names.body[d]
        );
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
        let _ = writeln!(out, "  requiredConsts := {}", list(rcs));
        if !b.required_layouts.is_empty() {
            let _ = writeln!(
                out,
                "  requiredLayouts := {}",
                names.ty_list(&b.required_layouts)
            );
        }
        out.push('\n');
    }

    out.push_str("def crate : _root_.Trusted.Crate where\n");
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
    let fns = roots.iter().map(|(f, requires, specs, _)| {
        let dbg = match f.debug_body {
            Some(dbg_def) => format!(
                "\n      debugBodyId := _root_.Option.some ⟨{}⟩",
                names.body_id[&dbg_def]
            ),
            None => String::new(),
        };
        let is_unsafe = if f.is_unsafe {
            "\n      isUnsafe := _root_.Bool.true"
        } else {
            ""
        };
        let req = Names::requires_field(requires);
        format!(
            "\n    {{ name := {}\n      bodyId := ⟨{}⟩{dbg}{is_unsafe}{req}\n      specs := {} }}",
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
    let waived: Vec<_> = roots
        .iter()
        .filter_map(|(f, _, _, trusted_reason)| {
            trusted_reason.as_ref().map(|_| {
                format!(
                    "\n    _root_.Trusted.ObligationId.fnBody {}",
                    string_lit(&f.name)
                )
            })
        })
        .collect();
    if waived.is_empty() {
        out.push_str("  tcbWaivedIds := []\n");
    } else {
        let _ = writeln!(out, "  tcbWaivedIds := [{}\n  ]", waived.join(","));
    }
    out.push_str("\nend Mir\n");
    out
}
