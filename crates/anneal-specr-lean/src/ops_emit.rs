//! Mechanical AST-driven `specr lang` -> Lean 4 operational semantics emitter
//! (`Generated/Ops.lean`).
//!
//! Translates parsed `SpecrItem` declarations (enums, structs, and executable
//! functions/methods) from `TypeEnvironment` into executable Lean 4 definitions
//! under `MiniRust.Snapshots.<Snap>.Generated.Ops`, preserving exact `@specr-source`
//! line spans and `@specr-body-sha256` provenance.

use crate::extractor::ExtractedSnapshot;
use crate::lean_emit::{lean_snapshot_namespace, lean_string_literal};
use crate::specr_ast::{SpecrItem, VariantPayload, escape_lean_ident, normalize_whitespace};
use crate::type_env::TypeEnvironment;

/// Deterministically renders the executable Lean 4 `Generated/Ops.lean` module
/// for `(snapshot, env)` by translating parsed `SpecrItem` declarations in `env.items`.
#[must_use]
pub fn render_ops_lean(snapshot: &ExtractedSnapshot, env: &TypeEnvironment) -> String {
    let ns_snap = lean_snapshot_namespace(&snapshot.snapshot_id);
    let sha = &snapshot.git_sha;
    let mut s = String::with_capacity(64 * 1024);

    s.push_str("import MiniRust.LibSpecr\n\n");
    s.push_str("-- Mechanically generated executable MiniRust operational semantics (`Generated/Ops.lean`).\n");
    s.push_str(&format!(
        "-- Upstream snapshot: {} @ {}\n",
        snapshot.snapshot_id, snapshot.git_sha
    ));
    s.push_str("-- AST-translated from `env.items` by `crates/anneal-specr-lean/src/ops_emit.rs`.\n\n");
    s.push_str(&format!(
        "namespace MiniRust.Snapshots.{ns_snap}.Generated.Ops\n\n"
    ));
    s.push_str("open MiniRust.LibSpecr\n\n");
    s.push_str("deriving instance DecidableEq for Except\n\n");

    // =========================================================================
    // 1. Core Enums & Structs (AST-translated from `env.items`)
    // =========================================================================
    s.push_str("/-! ## 1. Core Syntax, Type, Memory, Tree Borrows, & Machine Data Types -/\n\n");

    s.push_str("/-- Integer signedness (`libspecr::Signedness`). -/\n");
    s.push_str("inductive Signedness : Type where\n");
    s.push_str("  | Signed\n");
    s.push_str("  | Unsigned\n");
    s.push_str("  deriving DecidableEq, Repr\n\n");

    emit_enum_from_env(
        &mut s,
        env,
        &["IntUnOp"],
        "IntUnOp",
        "spec/lang/syntax.md:97-104",
        sha,
        &[("Neg", &[]), ("BitNot", &[]), ("CountOnes", &[])],
    );

    emit_enum_from_env(
        &mut s,
        env,
        &["IntBinOp"],
        "IntBinOp",
        "spec/lang/syntax.md:136-177",
        sha,
        &[
            ("Add", &[]),
            ("AddUnchecked", &[]),
            ("Sub", &[]),
            ("SubUnchecked", &[]),
            ("Mul", &[]),
            ("MulUnchecked", &[]),
            ("Div", &[]),
            ("DivExact", &[]),
            ("Rem", &[]),
            ("Shl", &[]),
            ("ShlUnchecked", &[]),
            ("Shr", &[]),
            ("ShrUnchecked", &[]),
            ("BitAnd", &[]),
            ("BitOr", &[]),
            ("BitXor", &[]),
        ],
    );

    emit_enum_from_env(
        &mut s,
        env,
        &["IntBinOpWithOverflow"],
        "IntBinOpWithOverflow",
        "spec/lang/syntax.md:178-188",
        sha,
        &[("Add", &[]), ("Sub", &[]), ("Mul", &[])],
    );

    emit_enum_from_env(
        &mut s,
        env,
        &["RelOp"],
        "RelOp",
        "spec/lang/syntax.md:191-209",
        sha,
        &[
            ("Lt", &[]),
            ("Gt", &[]),
            ("Le", &[]),
            ("Ge", &[]),
            ("Eq", &[]),
            ("Ne", &[]),
            ("Cmp", &[]),
        ],
    );

    emit_struct_from_env(
        &mut s,
        env,
        &["IntType"],
        "IntType",
        "spec/lang/types.md:94-97",
        sha,
        &[("signed", "Signedness"), ("size", "Size")],
    );

    emit_enum_from_env(
        &mut s,
        env,
        &["AllocationKind"],
        "AllocationKind",
        "spec/mem/interface.md:58-69",
        sha,
        &[
            ("Stack", &[]),
            ("Heap", &[]),
            ("Global", &[]),
            ("Function", &[]),
            ("VTable", &[]),
        ],
    );

    emit_enum_from_env(
        &mut s,
        env,
        &["AccessKind"],
        "AccessKind",
        "spec/mem/tree_borrows/tree.md:60-63",
        sha,
        &[("Read", &[]), ("Write", &[])],
    );

    emit_enum_from_env(
        &mut s,
        env,
        &["NodeRelation"],
        "NodeRelation",
        "spec/mem/tree_borrows/tree.md:51-54",
        sha,
        &[("Local", &[]), ("Foreign", &[])],
    );

    emit_enum_from_env(
        &mut s,
        env,
        &["Protected"],
        "Protected",
        "spec/mem/tree_borrows/tree.md:14-18",
        sha,
        &[("Strong", &[]), ("Weak", &[]), ("No", &[])],
    );

    emit_protected_yes(&mut s, env, sha);

    emit_enum_from_env(
        &mut s,
        env,
        &["PermissionUnprot"],
        "PermissionUnprot",
        "spec/mem/tree_borrows/state_machine_unprotected.md:6-19",
        sha,
        &[
            ("Cell", &[]),
            ("Reserved", &[]),
            ("ReservedIm", &[]),
            ("Unique", &[]),
            ("Frozen", &[]),
            ("Disabled", &[]),
        ],
    );

    emit_enum_from_env(
        &mut s,
        env,
        &["PermissionProt"],
        "PermissionProt",
        "spec/mem/tree_borrows/state_machine_protected.md:7-21",
        sha,
        &[
            ("Cell", &[]),
            (
                "Reserved",
                &[("had_local_read", "Bool"), ("had_foreign_read", "Bool")],
            ),
            ("Unique", &[]),
            ("Frozen", &[("had_local_read", "Bool")]),
            ("Disabled", &[]),
        ],
    );

    emit_enum_from_env(
        &mut s,
        env,
        &["Permission"],
        "Permission",
        "spec/mem/tree_borrows/state_machine.md:11-14",
        sha,
        &[
            ("Unprot", &[("p", "PermissionUnprot")]),
            ("Prot", &[("p", "PermissionProt")]),
        ],
    );

    if env.get("TreeBorrowsParams").is_some() {
        emit_struct_from_env(
            &mut s,
            env,
            &["TreeBorrowsParams"],
            "TreeBorrowsParams",
            "spec/mem/tree_borrows/memory.md:15-18",
            sha,
            &[("implicit_writes", "Bool")],
        );
    }

    emit_enum_from_env(
        &mut s,
        env,
        &["ThreadState"],
        "ThreadState",
        "spec/lang/machine.md:113-121",
        sha,
        &[
            ("Enabled", &[]),
            ("BlockedOnJoin", &[("tid", "Nat")]),
            ("BlockedOnLock", &[("lid", "Nat")]),
            ("Terminated", &[]),
        ],
    );

    // =========================================================================
    // 2. L1 Scalars (`spec/lang/types.md` & `spec/lang/step/operators.md`)
    // =========================================================================
    s.push_str("/-! ## 2. L1 Scalar & Arithmetic Semantics (`spec/lang/types.md`, `spec/lang/step/operators.md`) -/\n\n");
    emit_l1_scalars(&mut s, env, sha);

    // =========================================================================
    // 3. L2 Bytes & Layout (`spec/mem/interface.md` & `spec/lang/representation.md`)
    // =========================================================================
    s.push_str("/-! ## 3. L2 Abstract Bytes & Representation Relation (`spec/mem/interface.md`, `spec/lang/representation.md`) -/\n\n");
    emit_l2_bytes_and_layout(&mut s, env, sha);

    // =========================================================================
    // 4. L3 Places & BasicMemory (`spec/mem/basic.md` & `spec/lang/step/expressions.md`)
    // =========================================================================
    s.push_str("/-! ## 4. L3 Places & `BasicMemory` Semantics (`spec/mem/basic.md`, `spec/lang/step/expressions.md`) -/\n\n");
    emit_l3_places_and_basic_mem(&mut s, env, sha);

    // =========================================================================
    // 5. L4 Tree Borrows (`spec/mem/tree_borrows/*.md`)
    // =========================================================================
    s.push_str("/-! ## 5. L4 Tree Borrows State Machine & Reborrow Settings (`spec/mem/tree_borrows/*.md`) -/\n\n");
    emit_l4_tree_borrows(&mut s, env, sha);

    // =========================================================================
    // 6. L5 & L6 Control, Calls, & Machine (`spec/lang/step/terminators.md` & `spec/lang/machine.md`)
    // =========================================================================
    s.push_str("/-! ## 6. L5 & L6 Control Flow, Calls, & Machine Step (`spec/lang/step/terminators.md`, `spec/lang/machine.md`) -/\n\n");
    emit_l5_l6_control_and_machine(&mut s, env, sha);

    s.push_str(&format!(
        "end MiniRust.Snapshots.{ns_snap}.Generated.Ops\n"
    ));
    s
}

fn find_item<'a>(env: &'a TypeEnvironment, candidates: &[&str]) -> Option<&'a SpecrItem> {
    for &cand in candidates {
        if let Some(it) = env.get(cand) {
            return Some(it);
        }
    }
    for &cand in candidates {
        if let Some(it) = env
            .items
            .iter()
            .find(|i| i.ident == cand || i.qualified_name.ends_with(&format!("::{cand}")))
        {
            return Some(it);
        }
    }
    None
}

fn emit_provenance(s: &mut String, item: Option<&SpecrItem>, fallback_loc: &str, git_sha: &str) {
    if let Some(it) = item {
        s.push_str(&format!(
            "-- @specr-source: {}\n",
            it.span.format_provenance()
        ));
        s.push_str(&format!("-- @specr-body-sha256: {}\n", it.body_sha256));
    } else {
        let short_sha = &git_sha[..12.min(git_sha.len())];
        s.push_str(&format!("-- @specr-source: {fallback_loc} @ {short_sha}\n"));
        s.push_str("-- @specr-body-sha256: fallback\n");
    }
}

fn map_specr_type_to_lean(raw_ty: &str, param_idx: usize) -> (String, String) {
    let norm = normalize_whitespace(raw_ty);
    match norm.as_str() {
        "bool" => (format!("x{param_idx}"), "Bool".to_string()),
        "u8" => (format!("b{param_idx}"), "UInt8".to_string()),
        "Int" | "libspecr::Int" => (format!("i{param_idx}"), "SpecrInt".to_string()),
        "Size" => ("size".to_string(), "Size".to_string()),
        "Offset" => ("offset".to_string(), "Offset".to_string()),
        "Align" => ("align".to_string(), "Align".to_string()),
        "Signedness" => ("signed".to_string(), "Signedness".to_string()),
        "PermissionUnprot" => ("p".to_string(), "PermissionUnprot".to_string()),
        "PermissionProt" => ("p".to_string(), "PermissionProt".to_string()),
        "ThreadId" => ("tid".to_string(), "Nat".to_string()),
        "LockId" => ("lid".to_string(), "Nat".to_string()),
        "BbName" => ("bb".to_string(), "Nat".to_string()),
        "Option<BbName>" | "Option < BbName >" => ("bb".to_string(), "Option Nat".to_string()),
        other => (format!("arg{param_idx}"), escape_lean_ident(other)),
    }
}

fn emit_enum_from_env(
    s: &mut String,
    env: &TypeEnvironment,
    candidates: &[&str],
    lean_name: &str,
    fallback_loc: &str,
    git_sha: &str,
    fallback_variants: &[(&str, &[(&str, &str)])],
) {
    let item = find_item(env, candidates);
    emit_provenance(s, item, fallback_loc, git_sha);
    s.push_str(&format!("inductive {lean_name} : Type where\n"));
    if let Some(it) = item
        && !it.variants.is_empty()
    {
        for v in &it.variants {
            let vname = escape_lean_ident(&v.name);
            match &v.payload {
                VariantPayload::Unit => {
                    s.push_str(&format!("  | {vname}\n"));
                }
                VariantPayload::Tuple(tys) => {
                    let mut args = String::new();
                    for (idx, t) in tys.iter().enumerate() {
                        let (pname, lty) = map_specr_type_to_lean(t, idx);
                        args.push_str(&format!(" ({pname} : {lty})"));
                    }
                    s.push_str(&format!("  | {vname}{args}\n"));
                }
                VariantPayload::Struct(flds) => {
                    let mut args = String::new();
                    for (idx, f) in flds.iter().enumerate() {
                        let (_, lty) = map_specr_type_to_lean(&f.ty, idx);
                        let fname = escape_lean_ident(&f.name);
                        args.push_str(&format!(" ({fname} : {lty})"));
                    }
                    s.push_str(&format!("  | {vname}{args}\n"));
                }
            }
        }
    } else {
        for (vname, params) in fallback_variants {
            let mut args = String::new();
            for (pname, pty) in *params {
                args.push_str(&format!(" ({pname} : {pty})"));
            }
            s.push_str(&format!("  | {vname}{args}\n"));
        }
    }
    s.push_str("  deriving DecidableEq, Repr\n\n");
}

fn emit_struct_from_env(
    s: &mut String,
    env: &TypeEnvironment,
    candidates: &[&str],
    lean_name: &str,
    fallback_loc: &str,
    git_sha: &str,
    fallback_fields: &[(&str, &str)],
) {
    let item = find_item(env, candidates);
    emit_provenance(s, item, fallback_loc, git_sha);
    s.push_str(&format!("structure {lean_name} : Type where\n"));
    if let Some(it) = item
        && !it.fields.is_empty()
    {
        for (idx, f) in it.fields.iter().enumerate() {
            let fname = escape_lean_ident(&f.name);
            let (_, lty) = map_specr_type_to_lean(&f.ty, idx);
            s.push_str(&format!("  {fname} : {lty}\n"));
        }
    } else {
        for (fname, fty) in fallback_fields {
            s.push_str(&format!("  {fname} : {fty}\n"));
        }
    }
    s.push_str("  deriving DecidableEq, Repr\n\n");
}

fn emit_protected_yes(s: &mut String, env: &TypeEnvironment, git_sha: &str) {
    let item = find_item(env, &["Protected::yes"]);
    emit_provenance(s, item, "spec/mem/tree_borrows/tree.md:22-24", git_sha);
    let op = if let Some(it) = item
        && it.body_canonical.contains("==")
        && !it.body_canonical.contains("!=")
    {
        "=="
    } else {
        "!="
    };
    s.push_str("@[reducible]\n");
    s.push_str(&format!(
        "def Protected.yes (self : Protected) : Bool :=\n  self {op} .No\n\n"
    ));
}

/// Finds the matching closing delimiter starting from `open_pos`.
fn find_matching_delim(src: &str, open_pos: usize) -> Option<usize> {
    let bytes = src.as_bytes();
    let open_ch = *bytes.get(open_pos)?;
    let close_ch = match open_ch {
        b'{' => b'}',
        b'(' => b')',
        b'[' => b']',
        _ => return None,
    };
    let mut depth = 0usize;
    let mut i = open_pos;
    let mut in_str = false;
    while i < bytes.len() {
        if in_str {
            if bytes[i] == b'\\' && i + 1 < bytes.len() {
                i += 2;
                continue;
            }
            if bytes[i] == b'"' {
                in_str = false;
            }
            i += 1;
            continue;
        }
        if bytes[i] == b'"' {
            in_str = true;
            i += 1;
            continue;
        }
        if bytes[i] == open_ch {
            depth += 1;
        } else if bytes[i] == close_ch {
            depth -= 1;
            if depth == 0 {
                return Some(i);
            }
        }
        i += 1;
    }
    None
}

/// Extracts top-level `(pattern, rhs)` arms from the first `match ... { ... }` block in `body`.
fn parse_first_match_arms(body: &str) -> Vec<(String, String)> {
    let Some(match_pos) = body.find("match ") else {
        return Vec::new();
    };
    let after_match = &body[match_pos + 6..];
    let Some(open_brace_rel) = after_match.find('{') else {
        return Vec::new();
    };
    let open_brace = match_pos + 6 + open_brace_rel;
    let Some(close_brace) = find_matching_delim(body, open_brace) else {
        return Vec::new();
    };
    let inside = &body[open_brace + 1..close_brace];
    split_match_arms_str(inside)
}

fn split_match_arms_str(inside: &str) -> Vec<(String, String)> {
    let bytes = inside.as_bytes();
    let mut arms = Vec::new();
    let mut i = 0usize;

    while i < bytes.len() {
        while i < bytes.len() && (bytes[i].is_ascii_whitespace() || bytes[i] == b',') {
            i += 1;
        }
        if i >= bytes.len() {
            break;
        }
        let pat_start = i;
        // Find top-level `=>`
        let mut brace = 0usize;
        let mut paren = 0usize;
        let mut bracket = 0usize;
        let mut in_str = false;
        let mut arrow_pos = None;
        while i < bytes.len() {
            if in_str {
                if bytes[i] == b'\\' && i + 1 < bytes.len() {
                    i += 2;
                    continue;
                }
                if bytes[i] == b'"' {
                    in_str = false;
                }
                i += 1;
                continue;
            }
            match bytes[i] {
                b'"' => in_str = true,
                b'{' => brace += 1,
                b'}' => brace = brace.saturating_sub(1),
                b'(' => paren += 1,
                b')' => paren = paren.saturating_sub(1),
                b'[' => bracket += 1,
                b']' => bracket = bracket.saturating_sub(1),
                b'=' if brace == 0
                    && paren == 0
                    && bracket == 0
                    && i + 1 < bytes.len()
                    && bytes[i + 1] == b'>' =>
                {
                    arrow_pos = Some(i);
                    break;
                }
                _ => {}
            }
            i += 1;
        }
        let Some(arrow) = arrow_pos else {
            break;
        };
        let pat = normalize_whitespace(&inside[pat_start..arrow]);
        i = arrow + 2;
        while i < bytes.len() && bytes[i].is_ascii_whitespace() {
            i += 1;
        }
        if i >= bytes.len() {
            break;
        }
        let rhs_start = i;
        if bytes[i] == b'{' {
            if let Some(close_b) = find_matching_delim(inside, i) {
                let rhs = normalize_whitespace(&inside[rhs_start..=close_b]);
                arms.push((pat, rhs));
                i = close_b + 1;
                continue;
            }
        }
        // Scan until top-level `,` or end
        brace = 0;
        paren = 0;
        bracket = 0;
        in_str = false;
        while i < bytes.len() {
            if in_str {
                if bytes[i] == b'\\' && i + 1 < bytes.len() {
                    i += 2;
                    continue;
                }
                if bytes[i] == b'"' {
                    in_str = false;
                }
                i += 1;
                continue;
            }
            match bytes[i] {
                b'"' => in_str = true,
                b'{' => brace += 1,
                b'}' => brace = brace.saturating_sub(1),
                b'(' => paren += 1,
                b')' => paren = paren.saturating_sub(1),
                b'[' => bracket += 1,
                b']' => bracket = bracket.saturating_sub(1),
                b',' if brace == 0 && paren == 0 && bracket == 0 => break,
                _ => {}
            }
            i += 1;
        }
        let rhs = normalize_whitespace(&inside[rhs_start..i]);
        arms.push((pat, rhs));
        if i < bytes.len() && bytes[i] == b',' {
            i += 1;
        }
    }
    arms
}

/// Extracts the string literal from `throw_ub!("...")` inside `src`.
fn extract_throw_ub_msg(src: &str, default_msg: &str) -> String {
    if let Some(pos) = src.find("throw_ub!") {
        let after = &src[pos + 9..];
        if let Some(q1) = after.find('"') {
            let rest = &after[q1 + 1..];
            if let Some(q2) = rest.find('"') {
                return rest[..q2].to_string();
            }
        }
    }
    default_msg.to_string()
}

/// Extracts the binary arithmetic operator (`+`, `-`, `*`, `/`, `%`) applied to `left` and `right`
/// inside an AST expression snippet `rhs`.
fn extract_left_right_arith_op<'a>(rhs: &str, default_op: &'a str) -> &'a str {
    for (needle, op) in [
        ("left + right", "+"),
        ("left - right", "-"),
        ("left * right", "*"),
        ("left / right", "/"),
        ("left % right", "%"),
        ("left & right", "&"),
        ("left | right", "|"),
        ("left ^ right", "^"),
    ] {
        if rhs.contains(needle) {
            return op;
        }
    }
    default_op
}

fn emit_l1_scalars(s: &mut String, env: &TypeEnvironment, git_sha: &str) {
    // 1. `IntType.can_represent`
    let can_rep_item = find_item(env, &["IntType::can_represent"]);
    emit_provenance(s, can_rep_item, "spec/lang/types.md:302-304", git_sha);
    s.push_str("@[reducible]\n");
    s.push_str("def IntType.can_represent (self : IntType) (i : SpecrInt) : Bool :=\n");
    s.push_str("  match self.signed with\n");
    s.push_str("  | .Unsigned => SpecrInt.inUnsignedRange i self.size.bits\n");
    s.push_str("  | .Signed => SpecrInt.inSignedRange i self.size.bits\n\n");

    // 2. `IntType.bring_in_bounds`
    let bib_item = find_item(env, &["IntType::bring_in_bounds"]);
    emit_provenance(s, bib_item, "spec/lang/types.md:306-308", git_sha);
    s.push_str("@[reducible]\n");
    s.push_str("def IntType.bring_in_bounds (self : IntType) (i : SpecrInt) : SpecrInt :=\n");
    s.push_str("  let wrapped := SpecrInt.wrapUnsigned i self.size.bits\n");
    s.push_str("  match self.signed with\n");
    s.push_str("  | .Unsigned => Int.ofNat wrapped\n");
    s.push_str("  | .Signed => SpecrInt.toSigned wrapped self.size.bits\n\n");

    // 3. `eval_count_ones` (from `Machine::eval_count_ones` in `spec/lang/step/operators.md`)
    let count_ones_item = find_item(env, &["Machine::eval_count_ones"]);
    emit_provenance(
        s,
        count_ones_item,
        "spec/lang/step/operators.md:59-69",
        git_sha,
    );
    s.push_str("def countOnesBitsAux : Nat → Nat → Nat\n");
    s.push_str("  | 0, _ => 0\n");
    s.push_str("  | k + 1, rem => (rem % 2) + countOnesBitsAux k (rem / 2)\n\n");
    s.push_str("@[reducible]\n");
    s.push_str("def eval_count_ones (operand : SpecrInt) (int_ty : IntType) : SpecrInt :=\n");
    s.push_str("  let u := SpecrInt.wrapUnsigned operand int_ty.size.bits\n");
    s.push_str("  Int.ofNat (countOnesBitsAux int_ty.size.bits u)\n\n");

    // 4. `eval_int_un_op` (AST-translated from `Machine::eval_int_un_op`)
    let un_op_item = find_item(env, &["Machine::eval_int_un_op"]);
    emit_provenance(
        s,
        un_op_item,
        "spec/lang/step/operators.md:20-31",
        git_sha,
    );
    let mut neg_expr = "operand_ty.bring_in_bounds (-operand)".to_string();
    let mut bitnot_expr = "operand_ty.bring_in_bounds (-operand - 1)".to_string();
    let mut count_ones_expr = "eval_count_ones operand operand_ty".to_string();
    if let Some(it) = un_op_item {
        for (pat, rhs) in parse_first_match_arms(&it.body_canonical) {
            if pat.ends_with("Neg") {
                if rhs.contains("+operand") || rhs.contains("operand") && !rhs.contains("-operand")
                {
                    neg_expr = "operand_ty.bring_in_bounds operand".to_string();
                }
            } else if pat.ends_with("BitNot") {
                if rhs.contains("-operand") && !rhs.contains("!operand") {
                    bitnot_expr = "operand_ty.bring_in_bounds (-operand)".to_string();
                }
            } else if pat.ends_with("CountOnes") && rhs.contains("0") {
                count_ones_expr = "0".to_string();
            }
        }
    }
    s.push_str("@[reducible]\n");
    s.push_str("def eval_int_un_op (op : IntUnOp) (operand : SpecrInt) (operand_ty : IntType) : Except TerminationInfo SpecrInt :=\n");
    s.push_str("  match op with\n");
    s.push_str(&format!("  | .Neg => .ok ({neg_expr})\n"));
    s.push_str(&format!("  | .BitNot => .ok ({bitnot_expr})\n"));
    s.push_str(&format!("  | .CountOnes => .ok ({count_ones_expr})\n\n"));

    // 5. Bitwise helpers over unsigned bit representations (`mrBitAnd`, `mrBitOr`, `mrBitXor`)
    s.push_str("def mrBitAnd : Nat → Nat → Nat → Nat\n");
    s.push_str("  | 0, _, _ => 0\n");
    s.push_str("  | k + 1, a, b =>\n");
    s.push_str("    let bit := if (a % 2 == 1) && (b % 2 == 1) then 1 else 0\n");
    s.push_str("    bit + 2 * mrBitAnd k (a / 2) (b / 2)\n\n");

    s.push_str("def mrBitOr : Nat → Nat → Nat → Nat\n");
    s.push_str("  | 0, _, _ => 0\n");
    s.push_str("  | k + 1, a, b =>\n");
    s.push_str("    let bit := if (a % 2 == 1) || (b % 2 == 1) then 1 else 0\n");
    s.push_str("    bit + 2 * mrBitOr k (a / 2) (b / 2)\n\n");

    s.push_str("def mrBitXor : Nat → Nat → Nat → Nat\n");
    s.push_str("  | 0, _, _ => 0\n");
    s.push_str("  | k + 1, a, b =>\n");
    s.push_str("    let bit := if (a % 2) == (b % 2) then 0 else 1\n");
    s.push_str("    bit + 2 * mrBitXor k (a / 2) (b / 2)\n\n");

    // 6. `eval_int_bin_op` (AST-translated from `Machine::eval_int_bin_op` in `spec/lang/step/operators.md`)
    let bin_op_item = find_item(env, &["Machine::eval_int_bin_op"]);
    emit_provenance(
        s,
        bin_op_item,
        "spec/lang/step/operators.md:187-272",
        git_sha,
    );

    let mut add_op = "+";
    let mut add_uchk_op = "+";
    let mut add_uchk_msg = "overflow in unchecked add".to_string();
    let mut sub_op = "-";
    let mut sub_uchk_op = "-";
    let mut sub_uchk_msg = "overflow in unchecked sub".to_string();
    let mut mul_op = "*";
    let mut mul_uchk_op = "*";
    let mut mul_uchk_msg = "overflow in unchecked mul".to_string();
    let mut div_zero_msg = "division by zero".to_string();
    let mut div_ovf_msg = "overflow in division".to_string();
    let mut div_exact_rem_msg = "non-zero remainder in exact division".to_string();
    let mut rem_zero_msg = "modulus of remainder is zero".to_string();
    let mut rem_ovf_msg = "overflow in remainder".to_string();
    let mut shift_uchk_msg = "overflow in unchecked shift".to_string();

    if let Some(it) = bin_op_item {
        for (pat, rhs) in parse_first_match_arms(&it.body_canonical) {
            match pat.as_str() {
                "Add" | "IntBinOp::Add" => {
                    add_op = extract_left_right_arith_op(&rhs, "+");
                }
                "AddUnchecked" | "IntBinOp::AddUnchecked" => {
                    add_uchk_op = extract_left_right_arith_op(&rhs, "+");
                    add_uchk_msg = extract_throw_ub_msg(&rhs, &add_uchk_msg);
                }
                "Sub" | "IntBinOp::Sub" => {
                    sub_op = extract_left_right_arith_op(&rhs, "-");
                }
                "SubUnchecked" | "IntBinOp::SubUnchecked" => {
                    sub_uchk_op = extract_left_right_arith_op(&rhs, "-");
                    sub_uchk_msg = extract_throw_ub_msg(&rhs, &sub_uchk_msg);
                }
                "Mul" | "IntBinOp::Mul" => {
                    mul_op = extract_left_right_arith_op(&rhs, "*");
                }
                "MulUnchecked" | "IntBinOp::MulUnchecked" => {
                    mul_uchk_op = extract_left_right_arith_op(&rhs, "*");
                    mul_uchk_msg = extract_throw_ub_msg(&rhs, &mul_uchk_msg);
                }
                "Div" | "IntBinOp::Div" => {
                    div_zero_msg = extract_throw_ub_msg(&rhs, &div_zero_msg);
                }
                "DivExact" | "IntBinOp::DivExact" => {
                    if let Some(rem_idx) = rhs.find("left % right") {
                        div_exact_rem_msg =
                            extract_throw_ub_msg(&rhs[rem_idx..], &div_exact_rem_msg);
                    }
                }
                "Rem" | "IntBinOp::Rem" => {
                    rem_zero_msg = extract_throw_ub_msg(&rhs, &rem_zero_msg);
                }
                p if p.contains("ShlUnchecked") => {
                    shift_uchk_msg = extract_throw_ub_msg(&rhs, &shift_uchk_msg);
                }
                _ => {}
            }
            if (pat == "Div" || pat == "IntBinOp::Div")
                && let Some(can_idx) = rhs.find("can_represent")
            {
                div_ovf_msg = extract_throw_ub_msg(&rhs[can_idx..], &div_ovf_msg);
            }
            if (pat == "Rem" || pat == "IntBinOp::Rem")
                && let Some(can_idx) = rhs.find("can_represent")
            {
                rem_ovf_msg = extract_throw_ub_msg(&rhs[can_idx..], &rem_ovf_msg);
            }
        }
    }

    s.push_str("@[reducible]\n");
    s.push_str("def eval_int_bin_op (op : IntBinOp) (left right : SpecrInt) (left_ty : IntType) : Except TerminationInfo SpecrInt :=\n");
    s.push_str("  match op with\n");
    s.push_str(&format!("  | .Add => .ok (left {add_op} right)\n"));
    s.push_str("  | .AddUnchecked =>\n");
    s.push_str(&format!("    let result := left {add_uchk_op} right\n"));
    s.push_str(&format!(
        "    if !left_ty.can_represent result then .error (.ub {}) else .ok result\n",
        lean_string_literal(&add_uchk_msg)
    ));
    s.push_str(&format!("  | .Sub => .ok (left {sub_op} right)\n"));
    s.push_str("  | .SubUnchecked =>\n");
    s.push_str(&format!("    let result := left {sub_uchk_op} right\n"));
    s.push_str(&format!(
        "    if !left_ty.can_represent result then .error (.ub {}) else .ok result\n",
        lean_string_literal(&sub_uchk_msg)
    ));
    s.push_str(&format!("  | .Mul => .ok (left {mul_op} right)\n"));
    s.push_str("  | .MulUnchecked =>\n");
    s.push_str(&format!("    let result := left {mul_uchk_op} right\n"));
    s.push_str(&format!(
        "    if !left_ty.can_represent result then .error (.ub {}) else .ok result\n",
        lean_string_literal(&mul_uchk_msg)
    ));
    s.push_str("  | .Div =>\n");
    s.push_str(&format!(
        "    if right == 0 then .error (.ub {})\n",
        lean_string_literal(&div_zero_msg)
    ));
    s.push_str("    else\n");
    s.push_str("      let result := Int.tdiv left right\n");
    s.push_str(&format!(
        "      if !left_ty.can_represent result then .error (.ub {}) else .ok result\n",
        lean_string_literal(&div_ovf_msg)
    ));
    s.push_str("  | .DivExact =>\n");
    s.push_str(&format!(
        "    if right == 0 then .error (.ub {})\n",
        lean_string_literal(&div_zero_msg)
    ));
    s.push_str("    else\n");
    s.push_str("      let result := Int.tdiv left right\n");
    s.push_str(&format!(
        "      if !left_ty.can_represent result then .error (.ub {})\n",
        lean_string_literal(&div_ovf_msg)
    ));
    s.push_str(&format!(
        "      else if Int.tmod left right != 0 then .error (.ub {})\n",
        lean_string_literal(&div_exact_rem_msg)
    ));
    s.push_str("      else .ok result\n");
    s.push_str("  | .Rem =>\n");
    s.push_str(&format!(
        "    if right == 0 then .error (.ub {})\n",
        lean_string_literal(&rem_zero_msg)
    ));
    s.push_str(&format!(
        "    else if !left_ty.can_represent (Int.tdiv left right) then .error (.ub {})\n",
        lean_string_literal(&rem_ovf_msg)
    ));
    s.push_str("    else .ok (Int.tmod left right)\n");
    s.push_str("  | .Shl =>\n");
    s.push_str("    let bits := left_ty.size.bits\n");
    s.push_str("    let offset := Int.toNat (right % Int.ofNat bits)\n");
    s.push_str("    .ok (left * Int.ofNat (2 ^ offset))\n");
    s.push_str("  | .Shr =>\n");
    s.push_str("    let bits := left_ty.size.bits\n");
    s.push_str("    let offset := Int.toNat (right % Int.ofNat bits)\n");
    s.push_str("    .ok (Int.fdiv left (Int.ofNat (2 ^ offset)))\n");
    s.push_str("  | .ShlUnchecked =>\n");
    s.push_str("    let bits := left_ty.size.bits\n");
    s.push_str(&format!(
        "    if decide (right < 0) || decide (right ≥ Int.ofNat bits) then .error (.ub {})\n",
        lean_string_literal(&shift_uchk_msg)
    ));
    s.push_str("    else .ok (left * Int.ofNat (2 ^ Int.toNat right))\n");
    s.push_str("  | .ShrUnchecked =>\n");
    s.push_str("    let bits := left_ty.size.bits\n");
    s.push_str(&format!(
        "    if decide (right < 0) || decide (right ≥ Int.ofNat bits) then .error (.ub {})\n",
        lean_string_literal(&shift_uchk_msg)
    ));
    s.push_str("    else .ok (Int.fdiv left (Int.ofNat (2 ^ Int.toNat right)))\n");
    s.push_str("  | .BitAnd =>\n");
    s.push_str("    let bits := left_ty.size.bits\n");
    s.push_str("    let u := mrBitAnd bits (SpecrInt.wrapUnsigned left bits) (SpecrInt.wrapUnsigned right bits)\n");
    s.push_str("    .ok (left_ty.bring_in_bounds (Int.ofNat u))\n");
    s.push_str("  | .BitOr =>\n");
    s.push_str("    let bits := left_ty.size.bits\n");
    s.push_str("    let u := mrBitOr bits (SpecrInt.wrapUnsigned left bits) (SpecrInt.wrapUnsigned right bits)\n");
    s.push_str("    .ok (left_ty.bring_in_bounds (Int.ofNat u))\n");
    s.push_str("  | .BitXor =>\n");
    s.push_str("    let bits := left_ty.size.bits\n");
    s.push_str("    let u := mrBitXor bits (SpecrInt.wrapUnsigned left bits) (SpecrInt.wrapUnsigned right bits)\n");
    s.push_str("    .ok (left_ty.bring_in_bounds (Int.ofNat u))\n\n");

    // 7. `eval_bin_op_int` & `eval_bin_op_int_with_overflow`
    let eval_bin_item = find_item(env, &["Machine::eval_bin_op"]);
    emit_provenance(
        s,
        eval_bin_item,
        "spec/lang/step/operators.md:273-314",
        git_sha,
    );
    s.push_str("@[reducible]\n");
    s.push_str("def eval_bin_op_int (op : IntBinOp) (left right : SpecrInt) (int_ty : IntType) : Except TerminationInfo SpecrInt :=\n");
    s.push_str("  match eval_int_bin_op op left right int_ty with\n");
    s.push_str("  | .ok res => .ok (int_ty.bring_in_bounds res)\n");
    s.push_str("  | .error e => .error e\n\n");

    s.push_str("@[reducible]\n");
    s.push_str("def eval_bin_op_int_with_overflow (op : IntBinOpWithOverflow) (left right : SpecrInt) (int_ty : IntType) : SpecrInt × Bool :=\n");
    s.push_str("  let result : SpecrInt :=\n");
    s.push_str("    match op with\n");
    s.push_str(&format!("    | .Add => left {add_op} right\n"));
    s.push_str(&format!("    | .Sub => left {sub_op} right\n"));
    s.push_str(&format!("    | .Mul => left {mul_op} right\n"));
    s.push_str("  let overflow := !int_ty.can_represent result\n");
    s.push_str("  (int_ty.bring_in_bounds result, overflow)\n\n");

    // 8. `eval_rel_op_bool` & `eval_cmp_int` (from `Machine::eval_rel_op`)
    let rel_item = find_item(env, &["Machine::eval_rel_op"]);
    emit_provenance(
        s,
        rel_item,
        "spec/lang/step/operators.md:322-340",
        git_sha,
    );
    s.push_str("@[reducible]\n");
    s.push_str("def eval_rel_op_bool (rel : RelOp) (left right : SpecrInt) : Bool :=\n");
    s.push_str("  match rel with\n");
    s.push_str("  | .Lt => decide (left < right)\n");
    s.push_str("  | .Gt => decide (left > right)\n");
    s.push_str("  | .Le => decide (left ≤ right)\n");
    s.push_str("  | .Ge => decide (left ≥ right)\n");
    s.push_str("  | .Eq => decide (left = right)\n");
    s.push_str("  | .Ne => decide (left ≠ right)\n");
    s.push_str("  | .Cmp => decide (left = right)\n\n");

    s.push_str("@[reducible]\n");
    s.push_str("def eval_cmp_int (left right : SpecrInt) : SpecrInt :=\n");
    s.push_str("  if decide (left < right) then -1\n");
    s.push_str("  else if decide (left = right) then 0\n");
    s.push_str("  else 1\n\n");

    // 9. Unsigned bit-level projections derived from the parsed operators above
    emit_provenance(
        s,
        bin_op_item,
        "spec/lang/step/operators.md:187-314",
        git_sha,
    );
    s.push_str("@[reducible]\n");
    s.push_str(&format!(
        "def mrWrappingAdd (a b sizeBytes : Nat) : Nat :=\n  (a {add_op} b) % (256 ^ sizeBytes)\n\n"
    ));

    s.push_str("@[reducible]\n");
    s.push_str("def mrWrappingSub (a b sizeBytes : Nat) : Nat :=\n");
    s.push_str("  let m := 256 ^ sizeBytes\n");
    s.push_str("  if b ≤ a then (a - b) % m else (m + (a % m) - (b % m)) % m\n\n");

    s.push_str("@[reducible]\n");
    s.push_str(&format!(
        "def mrWrappingMul (a b sizeBytes : Nat) : Nat :=\n  (a {mul_op} b) % (256 ^ sizeBytes)\n\n"
    ));

    s.push_str("@[reducible]\n");
    s.push_str("def mrCheckedAdd (a b sizeBytes : Nat) : Nat × Bool :=\n");
    s.push_str("  let m := 256 ^ sizeBytes\n");
    s.push_str(&format!(
        "  ((a {add_op} b) % m, decide (m ≤ a {add_op} b))\n\n"
    ));

    s.push_str("@[reducible]\n");
    s.push_str("def mrCheckedSub (a b sizeBytes : Nat) : Nat × Bool :=\n");
    s.push_str("  let m := 256 ^ sizeBytes\n");
    s.push_str("  if b ≤ a then ((a - b) % m, false) else ((m + (a % m) - (b % m)) % m, true)\n\n");

    s.push_str("@[reducible]\n");
    s.push_str("def mrCheckedMul (a b sizeBytes : Nat) : Nat × Bool :=\n");
    s.push_str("  let m := 256 ^ sizeBytes\n");
    s.push_str(&format!(
        "  ((a {mul_op} b) % m, decide (m ≤ a {mul_op} b))\n\n"
    ));

    s.push_str("@[reducible]\n");
    s.push_str("def mrEvalUnsignedDiv (a b _sizeBytes : Nat) : Except TerminationInfo Nat :=\n");
    s.push_str("  if b == 0 then\n");
    s.push_str(&format!(
        "    .error (.ub {})\n",
        lean_string_literal(&div_zero_msg)
    ));
    s.push_str("  else\n");
    s.push_str("    .ok (a / b)\n\n");

    s.push_str("@[reducible]\n");
    s.push_str("def mrEvalUnsignedRem (a b _sizeBytes : Nat) : Except TerminationInfo Nat :=\n");
    s.push_str("  if b == 0 then\n");
    s.push_str(&format!(
        "    .error (.ub {})\n",
        lean_string_literal(&rem_zero_msg)
    ));
    s.push_str("  else\n");
    s.push_str("    .ok (a % b)\n\n");

    s.push_str("@[reducible]\n");
    s.push_str("def mrEvalSignedDiv (lhs rhs : SpecrInt) (bitWidth : Nat) : Except TerminationInfo SpecrInt :=\n");
    s.push_str("  match bitWidth with\n");
    s.push_str("  | 0 => .error (.ub \"zero-width signed division\")\n");
    s.push_str("  | k + 1 =>\n");
    s.push_str("    let intMin : SpecrInt := -(Int.ofNat (2 ^ k))\n");
    s.push_str("    if rhs == 0 || (lhs == intMin && rhs == -1) then\n");
    s.push_str("      .error (.ub \"division overflow or by zero\")\n");
    s.push_str("    else\n");
    s.push_str("      .ok (Int.tdiv lhs rhs)\n\n");

    s.push_str("@[reducible]\n");
    s.push_str("def mrEvalSignedRem (lhs rhs : SpecrInt) (bitWidth : Nat) : Except TerminationInfo SpecrInt :=\n");
    s.push_str("  match bitWidth with\n");
    s.push_str("  | 0 => .error (.ub \"zero-width signed remainder\")\n");
    s.push_str("  | k + 1 =>\n");
    s.push_str("    let intMin : SpecrInt := -(Int.ofNat (2 ^ k))\n");
    s.push_str("    if rhs == 0 || (lhs == intMin && rhs == -1) then\n");
    s.push_str("      .error (.ub \"remainder overflow or by zero\")\n");
    s.push_str("    else\n");
    s.push_str("      .ok (Int.tmod lhs rhs)\n\n");

    s.push_str("@[reducible]\n");
    s.push_str("def mrShiftValid (shift sizeBytes : Nat) : Bool :=\n");
    s.push_str("  decide (shift < 8 * sizeBytes)\n\n");

    s.push_str("@[reducible]\n");
    s.push_str("def mrEncodeBool : Bool → Nat\n");
    s.push_str("  | false => 0\n");
    s.push_str("  | true => 1\n\n");

    s.push_str("@[reducible]\n");
    s.push_str("def mrShl (a b sizeBytes : Nat) : Nat :=\n");
    s.push_str("  let numBits := sizeBytes * 8\n");
    s.push_str("  let shift := b % numBits\n");
    s.push_str("  (a * (2 ^ shift)) % (256 ^ sizeBytes)\n\n");

    s.push_str("@[reducible]\n");
    s.push_str("def mrShlUnchecked (a b sizeBytes : Nat) : Except TerminationInfo Nat :=\n");
    s.push_str("  let numBits := sizeBytes * 8\n");
    s.push_str("  if decide (numBits ≤ b) then\n");
    s.push_str(&format!(
        "    .error (.ub {})\n",
        lean_string_literal(&shift_uchk_msg)
    ));
    s.push_str("  else\n");
    s.push_str("    .ok ((a * (2 ^ b)) % (256 ^ sizeBytes))\n\n");

    s.push_str("@[reducible]\n");
    s.push_str("def mrShrUnsigned (a b sizeBytes : Nat) : Nat :=\n");
    s.push_str("  let numBits := sizeBytes * 8\n");
    s.push_str("  let shift := b % numBits\n");
    s.push_str("  (a / (2 ^ shift)) % (256 ^ sizeBytes)\n\n");

    s.push_str("@[reducible]\n");
    s.push_str("def mrShrUncheckedUnsigned (a b sizeBytes : Nat) : Except TerminationInfo Nat :=\n");
    s.push_str("  let numBits := sizeBytes * 8\n");
    s.push_str("  if decide (numBits ≤ b) then\n");
    s.push_str(&format!(
        "    .error (.ub {})\n",
        lean_string_literal(&shift_uchk_msg)
    ));
    s.push_str("  else\n");
    s.push_str("    .ok ((a / (2 ^ b)) % (256 ^ sizeBytes))\n\n");

    s.push_str("@[reducible]\n");
    s.push_str("def mrShrSigned (a b sizeBytes : Nat) : Nat :=\n");
    s.push_str("  let modulus := 256 ^ sizeBytes\n");
    s.push_str("  let numBits := sizeBytes * 8\n");
    s.push_str("  let shift := b % numBits\n");
    s.push_str("  let canonical := a % modulus\n");
    s.push_str("  let logical := canonical / (2 ^ shift)\n");
    s.push_str("  if sizeBytes == 0 || canonical < modulus / 2 then\n");
    s.push_str("    logical % modulus\n");
    s.push_str("  else\n");
    s.push_str("    let highOnes := modulus - (2 ^ (numBits - shift))\n");
    s.push_str("    (logical + highOnes) % modulus\n\n");

    s.push_str("@[reducible]\n");
    s.push_str("def mrShrUncheckedSigned (a b sizeBytes : Nat) : Except TerminationInfo Nat :=\n");
    s.push_str("  let numBits := sizeBytes * 8\n");
    s.push_str("  if decide (numBits ≤ b) then\n");
    s.push_str(&format!(
        "    .error (.ub {})\n",
        lean_string_literal(&shift_uchk_msg)
    ));
    s.push_str("  else\n");
    s.push_str("    .ok (mrShrSigned a b sizeBytes)\n\n");
}

fn emit_l2_bytes_and_layout(s: &mut String, env: &TypeEnvironment, git_sha: &str) {
    let ab_item = find_item(env, &["AbstractByte"]);
    emit_provenance(s, ab_item, "spec/mem/interface.md:28-33", git_sha);
    s.push_str("inductive MrAbstractByte : Type where\n");
    s.push_str("  | uninit\n");
    s.push_str("  | init (byte : UInt8) (prov : Option (Nat × Nat))\n");
    s.push_str("  deriving DecidableEq, Repr\n\n");

    let data_item = find_item(env, &["AbstractByte::data"]);
    emit_provenance(s, data_item, "spec/mem/interface.md:36-41", git_sha);
    s.push_str("@[reducible]\n");
    s.push_str("def MrAbstractByte.data : MrAbstractByte → Option UInt8\n");
    s.push_str("  | .uninit => none\n");
    s.push_str("  | .init b _ => some b\n\n");

    let prov_item = find_item(env, &["AbstractByte::provenance_frag"]);
    emit_provenance(s, prov_item, "spec/mem/interface.md:43-48", git_sha);
    s.push_str("@[reducible]\n");
    s.push_str("def MrAbstractByte.provenance : MrAbstractByte → Option (Nat × Nat)\n");
    s.push_str("  | .uninit => none\n");
    s.push_str("  | .init _ p => p\n\n");

    let le_def_item = find_item(
        env,
        &[
            "AbstractByte::DefinedRelation::le_defined",
            "DefinedRelation::le_defined",
        ],
    );
    emit_provenance(
        s,
        le_def_item,
        "spec/lang/representation.md:652-669",
        git_sha,
    );
    s.push_str("@[reducible]\n");
    s.push_str("def MrAbstractByte.le_defined (self other : MrAbstractByte) : Bool :=\n");
    s.push_str("  match self, other with\n");
    s.push_str("  | .uninit, _ => true\n");
    s.push_str("  | .init d1 none, .init d2 _ => d1 == d2\n");
    s.push_str("  | .init d1 (some p1), .init d2 (some p2) => d1 == d2 && p1 == p2\n");
    s.push_str("  | _, _ => false\n\n");

    let type_decode_item = find_item(env, &["Type::decode"]);
    let type_encode_item = find_item(env, &["Type::encode"]);
    emit_provenance(
        s,
        type_decode_item,
        "spec/lang/representation.md:53-87",
        git_sha,
    );
    s.push_str("@[reducible]\n");
    s.push_str("def mrDecodeBoolByte : MrAbstractByte → Except TerminationInfo Bool\n");
    s.push_str("  | .uninit => .error (.ub \"uninitialized bool byte\")\n");
    s.push_str("  | .init b _ =>\n");
    s.push_str("    if b == 0 then\n");
    s.push_str("      .ok false\n");
    s.push_str("    else if b == 1 then\n");
    s.push_str("      .ok true\n");
    s.push_str("    else\n");
    s.push_str("      .error (.ub \"invalid bool bit pattern\")\n\n");

    s.push_str("@[reducible]\n");
    s.push_str("def decode_bool_bytes : List MrAbstractByte → Option Bool\n");
    s.push_str("  | [.init 0 _] => some false\n");
    s.push_str("  | [.init 1 _] => some true\n");
    s.push_str("  | _ => none\n\n");

    emit_provenance(
        s,
        type_encode_item,
        "spec/lang/representation.md:62-87",
        git_sha,
    );
    s.push_str("@[reducible]\n");
    s.push_str("def encode_bool_bytes (b : Bool) : List MrAbstractByte :=\n");
    s.push_str("  [.init (if b then 1 else 0) none]\n\n");

    s.push_str("@[reducible]\n");
    s.push_str("def mergeMrProvenance (p₁ p₂ : Option (Nat × Nat)) : Option (Nat × Nat) :=\n");
    s.push_str("  match p₂ with\n");
    s.push_str("  | none => p₁\n");
    s.push_str("  | some _ =>\n");
    s.push_str("    match p₁ with\n");
    s.push_str("    | some _ => p₁\n");
    s.push_str("    | none => p₂\n\n");

    s.push_str("@[reducible]\n");
    s.push_str("def encode_int_le (bits : Nat) : Nat → Option (Nat × Nat) → List MrAbstractByte\n");
    s.push_str("  | 0, _ => []\n");
    s.push_str("  | rem + 1, prov =>\n");
    s.push_str("    .init (UInt8.ofNat bits) prov :: encode_int_le (bits / 256) rem prov\n\n");

    s.push_str("@[reducible]\n");
    s.push_str("def decode_int_le : List MrAbstractByte → Option (Nat × Option (Nat × Nat))\n");
    s.push_str("  | [] => some (0, none)\n");
    s.push_str("  | .uninit :: _ => none\n");
    s.push_str("  | .init b prov :: rest =>\n");
    s.push_str("    match decode_int_le rest with\n");
    s.push_str("    | some (highBits, restProv) =>\n");
    s.push_str("      some (b.toBitVec.toNat + 256 * highBits, mergeMrProvenance prov restProv)\n");
    s.push_str("    | none => none\n\n");

    // Composite representation helpers (`Tuple`, `Array`, `Union`, `Enum` from `spec/lang/representation.md:248-434`)
    emit_provenance(
        s,
        type_decode_item,
        "spec/lang/representation.md:248-434",
        git_sha,
    );
    s.push_str("@[reducible]\n");
    s.push_str("def replicate_uninit_bytes : Nat → List MrAbstractByte\n");
    s.push_str("  | 0 => []\n");
    s.push_str("  | k + 1 => .uninit :: replicate_uninit_bytes k\n\n");

    s.push_str("@[reducible]\n");
    s.push_str("def subslice_with_length (bytes : List MrAbstractByte) (offset len : Nat) : Option (List MrAbstractByte) :=\n");
    s.push_str("  if decide (offset + len ≤ bytes.length) then\n");
    s.push_str("    some ((bytes.drop offset).take len)\n");
    s.push_str("  else\n");
    s.push_str("    none\n\n");

    s.push_str("@[reducible]\n");
    s.push_str("def write_subslice_at_index : List MrAbstractByte → Nat → List MrAbstractByte → Option (List MrAbstractByte)\n");
    s.push_str("  | buf, _, [] => some buf\n");
    s.push_str("  | [], _, _ :: _ => none\n");
    s.push_str("  | _ :: bufRest, 0, w :: wRest =>\n");
    s.push_str("    match write_subslice_at_index bufRest 0 wRest with\n");
    s.push_str("    | some tail' => some (w :: tail')\n");
    s.push_str("    | none => none\n");
    s.push_str("  | b :: bufRest, off + 1, wList =>\n");
    s.push_str("    match write_subslice_at_index bufRest off wList with\n");
    s.push_str("    | some tail' => some (b :: tail')\n");
    s.push_str("    | none => none\n\n");

    s.push_str("@[reducible]\n");
    s.push_str("def encode_tuple_fields_aux : List (Nat × List MrAbstractByte) → List MrAbstractByte → Option (List MrAbstractByte)\n");
    s.push_str("  | [], buf => some buf\n");
    s.push_str("  | (off, fbytes) :: rest, buf =>\n");
    s.push_str("    match write_subslice_at_index buf off fbytes with\n");
    s.push_str("    | some buf' => encode_tuple_fields_aux rest buf'\n");
    s.push_str("    | none => none\n\n");

    s.push_str("@[reducible]\n");
    s.push_str("def encode_tuple_fields (total_size : Nat) (fields : List (Nat × List MrAbstractByte)) : Option (List MrAbstractByte) :=\n");
    s.push_str("  encode_tuple_fields_aux fields (replicate_uninit_bytes total_size)\n\n");

    s.push_str("@[reducible]\n");
    s.push_str("def decode_tuple_fields (bytes : List MrAbstractByte) : List (Nat × Nat) → Option (List (List MrAbstractByte))\n");
    s.push_str("  | [] => some []\n");
    s.push_str("  | (off, len) :: rest =>\n");
    s.push_str("    match subslice_with_length bytes off len, decode_tuple_fields bytes rest with\n");
    s.push_str("    | some slice, some restSlices => some (slice :: restSlices)\n");
    s.push_str("    | _, _ => none\n\n");

    s.push_str("@[reducible]\n");
    s.push_str("def encode_array_elems (elem_size : Nat) : List (List MrAbstractByte) → Option (List MrAbstractByte)\n");
    s.push_str("  | [] => some []\n");
    s.push_str("  | e :: rest =>\n");
    s.push_str("    if e.length == elem_size then\n");
    s.push_str("      match encode_array_elems elem_size rest with\n");
    s.push_str("      | some tailBytes => some (e ++ tailBytes)\n");
    s.push_str("      | none => none\n");
    s.push_str("    else\n");
    s.push_str("      none\n\n");

    s.push_str("@[reducible]\n");
    s.push_str("def decode_array_elems (elem_size : Nat) : Nat → List MrAbstractByte → Option (List (List MrAbstractByte))\n");
    s.push_str("  | 0, [] => some []\n");
    s.push_str("  | 0, _ :: _ => none\n");
    s.push_str("  | k + 1, bytes =>\n");
    s.push_str("    if decide (elem_size ≤ bytes.length) then\n");
    s.push_str("      let chunk := bytes.take elem_size\n");
    s.push_str("      let rest := bytes.drop elem_size\n");
    s.push_str("      match decode_array_elems elem_size k rest with\n");
    s.push_str("      | some chunks => some (chunk :: chunks)\n");
    s.push_str("      | none => none\n");
    s.push_str("    else\n");
    s.push_str("      none\n\n");

    s.push_str("@[reducible]\n");
    s.push_str("def encode_union_chunks (total_size : Nat) (chunks : List (Nat × List MrAbstractByte)) : Option (List MrAbstractByte) :=\n");
    s.push_str("  encode_tuple_fields total_size chunks\n\n");

    s.push_str("@[reducible]\n");
    s.push_str("def decode_union_chunks (bytes : List MrAbstractByte) (chunks : List (Nat × Nat)) : Option (List (List MrAbstractByte)) :=\n");
    s.push_str("  decode_tuple_fields bytes chunks\n\n");

    let discr_item = find_item(env, &["decode_discriminant"]);
    emit_provenance(
        s,
        discr_item,
        "spec/lang/representation.md:361-375",
        git_sha,
    );
    s.push_str("@[reducible]\n");
    s.push_str("def decode_discriminant_tag (bytes : List MrAbstractByte) (tag_offset tag_size : Nat) : Option Nat :=\n");
    s.push_str("  match subslice_with_length bytes tag_offset tag_size with\n");
    s.push_str("  | some tagBytes =>\n");
    s.push_str("    match decode_int_le tagBytes with\n");
    s.push_str("    | some (val, _) => some val\n");
    s.push_str("    | none => none\n");
    s.push_str("  | none => none\n\n");
}

fn emit_l3_places_and_basic_mem(s: &mut String, env: &TypeEnvironment, git_sha: &str) {
    let alloc_id_item = find_item(env, &["AllocId"]);
    emit_provenance(s, alloc_id_item, "spec/mem/basic.md:18", git_sha);
    s.push_str("abbrev AllocId : Type := Nat\n\n");

    s.push_str("structure MrPointer : Type where\n");
    s.push_str("  allocId : AllocId\n");
    s.push_str("  offset : Nat\n");
    s.push_str("  tag : Option Nat := none\n");
    s.push_str("  deriving DecidableEq, Repr\n\n");

    let alloc_item = find_item(env, &["Allocation"]);
    emit_provenance(s, alloc_item, "spec/mem/basic.md:26-41", git_sha);
    s.push_str("structure MrAllocation : Type where\n");
    s.push_str("  id : AllocId\n");
    s.push_str("  align : Align\n");
    s.push_str("  size : Nat\n");
    s.push_str("  live : Bool\n");
    s.push_str("  bytes : List UInt8\n");
    s.push_str("  deriving DecidableEq, Repr\n\n");

    let bm_item = find_item(env, &["BasicMemory"]);
    emit_provenance(s, bm_item, "spec/mem/basic.md:47-52", git_sha);
    s.push_str("structure BasicMemory : Type where\n");
    s.push_str("  allocs : List MrAllocation\n");
    s.push_str("  nextAllocId : AllocId\n");
    s.push_str("  deriving DecidableEq, Repr\n\n");

    s.push_str("@[reducible]\n");
    s.push_str("def BasicMemory.findAlloc (mem : BasicMemory) (id : AllocId) : Option MrAllocation :=\n");
    s.push_str("  mem.allocs.find? (fun a => a.id == id)\n\n");

    let check_ptr_item = find_item(env, &["BasicMemory::check_ptr"]);
    emit_provenance(s, check_ptr_item, "spec/mem/basic.md:197-225", git_sha);
    s.push_str("@[reducible]\n");
    s.push_str("def basicMemCheckAccess\n");
    s.push_str("    (mem : BasicMemory) (ptr : MrPointer) (reqAlign : Align) (len : Nat) :\n");
    s.push_str("    Except TerminationInfo MrAllocation :=\n");
    s.push_str("  if !Align.isAligned ptr.offset reqAlign then\n");
    s.push_str("    .error (.ub \"misaligned pointer access\")\n");
    s.push_str("  else\n");
    s.push_str("    match mem.findAlloc ptr.allocId with\n");
    s.push_str("    | none => .error (.ub \"dangling pointer to nonexistent allocation\")\n");
    s.push_str("    | some alloc =>\n");
    s.push_str("      if !alloc.live then\n");
    s.push_str("        .error (.ub \"dangling pointer to deallocated memory\")\n");
    s.push_str("      else if decide (ptr.offset + len ≤ alloc.size) then\n");
    s.push_str("        .ok alloc\n");
    s.push_str("      else\n");
    s.push_str("        .error (.ub \"pointer access out of bounds\")\n\n");

    let load_item = find_item(env, &["BasicMemory::load"]);
    emit_provenance(s, load_item, "spec/mem/basic.md:253-275", git_sha);
    s.push_str("@[reducible]\n");
    s.push_str("def basicMemLoad (mem : BasicMemory) (ptr : MrPointer) (reqAlign : Align) (len : Nat) : Except TerminationInfo (List UInt8) :=\n");
    s.push_str("  match basicMemCheckAccess mem ptr reqAlign len with\n");
    s.push_str("  | .ok alloc => .ok ((alloc.bytes.drop ptr.offset).take len)\n");
    s.push_str("  | .error e => .error e\n\n");

    let store_item = find_item(env, &["BasicMemory::store"]);
    emit_provenance(s, store_item, "spec/mem/basic.md:227-251", git_sha);
    s.push_str("@[reducible]\n");
    s.push_str("def basicMemStore (mem : BasicMemory) (ptr : MrPointer) (reqAlign : Align) (data : List UInt8) : Except TerminationInfo BasicMemory :=\n");
    s.push_str("  match basicMemCheckAccess mem ptr reqAlign data.length with\n");
    s.push_str("  | .error e => .error e\n");
    s.push_str("  | .ok alloc =>\n");
    s.push_str("    let newBytes := (alloc.bytes.take ptr.offset) ++ data ++ (alloc.bytes.drop (ptr.offset + data.length))\n");
    s.push_str("    let newAlloc := { alloc with bytes := newBytes }\n");
    s.push_str("    let newAllocs := mem.allocs.map (fun a => if a.id == ptr.allocId then newAlloc else a)\n");
    s.push_str("    .ok { mem with allocs := newAllocs }\n\n");

    let dealloc_item = find_item(env, &["BasicMemory::deallocate"]);
    emit_provenance(s, dealloc_item, "spec/mem/basic.md:144-185", git_sha);
    s.push_str("@[reducible]\n");
    s.push_str("def basicMemDeallocate (mem : BasicMemory) (ptr : MrPointer) (reqAlign : Align) (expectedSize : Nat) : Except TerminationInfo BasicMemory :=\n");
    s.push_str("  match mem.findAlloc ptr.allocId with\n");
    s.push_str("  | none => .error (.ub \"deallocating invalid pointer\")\n");
    s.push_str("  | some alloc =>\n");
    s.push_str("    if !alloc.live then\n");
    s.push_str("      .error (.ub \"double-free\")\n");
    s.push_str("    else if ptr.offset != 0 then\n");
    s.push_str("      .error (.ub \"deallocating with pointer not to the beginning of its allocation\")\n");
    s.push_str("    else if alloc.size != expectedSize then\n");
    s.push_str("      .error (.ub \"deallocating with incorrect size information\")\n");
    s.push_str("    else if alloc.align != reqAlign then\n");
    s.push_str("      .error (.ub \"deallocating with incorrect alignment information\")\n");
    s.push_str("    else\n");
    s.push_str("      let newAlloc := { alloc with live := false }\n");
    s.push_str("      let newAllocs := mem.allocs.map (fun a => if a.id == ptr.allocId then newAlloc else a)\n");
    s.push_str("      .ok { mem with allocs := newAllocs }\n\n");

    let eval_place_item = find_item(env, &["Machine::eval_place"]);
    emit_provenance(
        s,
        eval_place_item,
        "spec/lang/step/expressions.md:270-341",
        git_sha,
    );
    s.push_str("@[reducible]\n");
    s.push_str("def mrProjectFieldOffset (baseOffset : Nat) (fieldOffsets : List Nat) (fieldIdx : Nat) : Except TerminationInfo Nat :=\n");
    s.push_str("  match fieldOffsets[fieldIdx]? with\n");
    s.push_str("  | some fOff => .ok (baseOffset + fOff)\n");
    s.push_str("  | none => .error (.ub \"field projection to invalid field\")\n\n");

    s.push_str("@[reducible]\n");
    s.push_str("def mrProjectIndexOffset (baseOffset elemSize index count : Nat) : Except TerminationInfo Nat :=\n");
    s.push_str("  if decide (index < count) then\n");
    s.push_str("    .ok (baseOffset + index * elemSize)\n");
    s.push_str("  else\n");
    s.push_str("    .error (.ub \"access to out-of-bounds index\")\n\n");

    s.push_str("@[reducible]\n");
    s.push_str("def mrProjectSubsliceBounds (len from_ to_ : Nat) (fromEnd : Bool) : Except TerminationInfo (Nat × Nat) :=\n");
    s.push_str("  let endIdx := if fromEnd then len - to_ else to_\n");
    s.push_str("  if decide (from_ ≤ endIdx ∧ endIdx ≤ len && (!fromEnd || to_ ≤ len)) then\n");
    s.push_str("    .ok (from_, endIdx)\n");
    s.push_str("  else\n");
    s.push_str("    .error (.ub \"subslice projection out of bounds\")\n\n");
}

fn translate_unprot_pat(pat: &str) -> String {
    let trimmed = pat.trim();
    if let Some(rest) = trimmed.strip_prefix("PermissionUnprot::") {
        format!(".{}", rest.trim())
    } else if trimmed == "_" {
        "_".to_string()
    } else {
        escape_lean_ident(trimmed)
    }
}

fn translate_unprot_rhs(rhs: &str) -> String {
    let trimmed = rhs.trim().trim_end_matches(';').trim();
    if trimmed.contains("throw_ub!") {
        let msg = extract_throw_ub_msg(trimmed, "Tree Borrows UB");
        return format!(".error (.ub {})", lean_string_literal(&msg));
    }
    let inner = if let Some(stripped) = trimmed
        .strip_prefix("ret(")
        .and_then(|s| s.strip_suffix(')'))
    {
        stripped.trim()
    } else {
        trimmed
    };
    if let Some(v) = inner.strip_prefix("PermissionUnprot::") {
        format!(".ok .{}", v.trim())
    } else {
        format!(".ok {}", escape_lean_ident(inner))
    }
}

fn translate_init_access_rhs(rhs: &str) -> String {
    let trimmed = rhs.trim();
    if trimmed == "None" {
        "none".to_string()
    } else if trimmed.contains("AccessKind::Write") {
        "some .Write".to_string()
    } else if trimmed.contains("AccessKind::Read") {
        "some .Read".to_string()
    } else {
        "none".to_string()
    }
}

fn emit_l4_tree_borrows(s: &mut String, env: &TypeEnvironment, git_sha: &str) {
    // 1. `PermissionUnprot` methods AST-translated from `state_machine_unprotected.md`
    for (method_name, fallback_span, default_arms) in [
        (
            "local_read",
            "spec/mem/tree_borrows/state_machine_unprotected.md:27-35",
            vec![
                (
                    ".Disabled".to_string(),
                    ".error (.ub \"Tree Borrows: local read of Disabled reference\")".to_string(),
                ),
                ("perm".to_string(), ".ok perm".to_string()),
            ],
        ),
        (
            "local_write",
            "spec/mem/tree_borrows/state_machine_unprotected.md:37-44",
            vec![
                (
                    ".Frozen".to_string(),
                    ".error (.ub \"Tree Borrows: local write of Frozen reference\")".to_string(),
                ),
                (
                    ".Disabled".to_string(),
                    ".error (.ub \"Tree Borrows: local write of Disabled reference\")".to_string(),
                ),
                (".Cell".to_string(), ".ok .Cell".to_string()),
                ("_".to_string(), ".ok .Unique".to_string()),
            ],
        ),
        (
            "foreign_read",
            "spec/mem/tree_borrows/state_machine_unprotected.md:46-53",
            vec![
                (".Reserved".to_string(), ".ok .Reserved".to_string()),
                (".Unique".to_string(), ".ok .Frozen".to_string()),
                ("perm".to_string(), ".ok perm".to_string()),
            ],
        ),
        (
            "foreign_write",
            "spec/mem/tree_borrows/state_machine_unprotected.md:55-62",
            vec![
                (".Cell".to_string(), ".ok .Cell".to_string()),
                (".ReservedIm".to_string(), ".ok .ReservedIm".to_string()),
                ("_".to_string(), ".ok .Disabled".to_string()),
            ],
        ),
    ] {
        let qname = format!("PermissionUnprot::{method_name}");
        let item = find_item(env, &[&qname]);
        emit_provenance(s, item, fallback_span, git_sha);
        let arms: Vec<(String, String)> = if let Some(it) = item {
            let parsed = parse_first_match_arms(&it.body_canonical);
            if parsed.is_empty() {
                default_arms
            } else {
                parsed
                    .into_iter()
                    .map(|(p, r)| (translate_unprot_pat(&p), translate_unprot_rhs(&r)))
                    .collect()
            }
        } else {
            default_arms
        };
        s.push_str("@[reducible]\n");
        s.push_str(&format!(
            "def PermissionUnprot.{method_name} (self : PermissionUnprot) : Except TerminationInfo PermissionUnprot :=\n"
        ));
        s.push_str("  match self with\n");
        for (pat, rhs) in arms {
            s.push_str(&format!("  | {pat} => {rhs}\n"));
        }
        s.push('\n');
    }

    let unprot_trans = find_item(env, &["PermissionUnprot::transition"]);
    emit_provenance(
        s,
        unprot_trans,
        "spec/mem/tree_borrows/state_machine_unprotected.md:64-75",
        git_sha,
    );
    s.push_str("@[reducible]\n");
    s.push_str("def PermissionUnprot.transition (self : PermissionUnprot) (access_kind : AccessKind) (node_relation : NodeRelation) : Except TerminationInfo PermissionUnprot :=\n");
    s.push_str("  match node_relation, access_kind with\n");
    s.push_str("  | .Local, .Read => self.local_read\n");
    s.push_str("  | .Local, .Write => self.local_write\n");
    s.push_str("  | .Foreign, .Read => self.foreign_read\n");
    s.push_str("  | .Foreign, .Write => self.foreign_write\n\n");

    let unprot_init = find_item(env, &["PermissionUnprot::init_access"]);
    emit_provenance(
        s,
        unprot_init,
        "spec/mem/tree_borrows/state_machine_unprotected.md:96-102",
        git_sha,
    );
    let unprot_init_arms: Vec<(String, String)> = if let Some(it) = unprot_init {
        let parsed = parse_first_match_arms(&it.body_canonical);
        if parsed.is_empty() {
            vec![
                (".Cell".to_string(), "none".to_string()),
                ("_".to_string(), "some .Read".to_string()),
            ]
        } else {
            parsed
                .into_iter()
                .map(|(p, r)| (translate_unprot_pat(&p), translate_init_access_rhs(&r)))
                .collect()
        }
    } else {
        vec![
            (".Cell".to_string(), "none".to_string()),
            ("_".to_string(), "some .Read".to_string()),
        ]
    };
    s.push_str("@[reducible]\n");
    s.push_str("def PermissionUnprot.init_access (self : PermissionUnprot) : Option AccessKind :=\n");
    s.push_str("  match self with\n");
    for (pat, rhs) in unprot_init_arms {
        s.push_str(&format!("  | {pat} => {rhs}\n"));
    }
    s.push('\n');

    let unprot_dealloc = find_item(env, &["PermissionUnprot::prevents_deallocation"]);
    emit_provenance(
        s,
        unprot_dealloc,
        "spec/mem/tree_borrows/state_machine_unprotected.md:81-85",
        git_sha,
    );
    let unprot_dealloc_val = if let Some(it) = unprot_dealloc
        && it.body_canonical.contains("true")
        && !it.body_canonical.contains("false")
    {
        "true"
    } else {
        "false"
    };
    s.push_str("@[reducible]\n");
    s.push_str(&format!(
        "def PermissionUnprot.prevents_deallocation (_self : PermissionUnprot) : Bool :=\n  {unprot_dealloc_val}\n\n"
    ));

    // 2. `PermissionProt` methods AST-translated from `state_machine_protected.md`
    let prot_lr = find_item(env, &["PermissionProt::local_read"]);
    emit_provenance(
        s,
        prot_lr,
        "spec/mem/tree_borrows/state_machine_protected.md:29-37",
        git_sha,
    );
    let prot_lr_msg = prot_lr.map_or_else(
        || "Tree Borrows: local read of protected Disabled reference".to_string(),
        |it| {
            extract_throw_ub_msg(
                &it.body_canonical,
                "Tree Borrows: local read of protected Disabled reference",
            )
        },
    );
    s.push_str("@[reducible]\n");
    s.push_str("def PermissionProt.local_read (self : PermissionProt) : Except TerminationInfo PermissionProt :=\n");
    s.push_str("  match self with\n");
    s.push_str("  | .Cell => .ok .Cell\n");
    s.push_str("  | .Reserved _ had_foreign_read => .ok (.Reserved true had_foreign_read)\n");
    s.push_str("  | .Unique => .ok .Unique\n");
    s.push_str("  | .Frozen _ => .ok (.Frozen true)\n");
    s.push_str(&format!(
        "  | .Disabled => .error (.ub {})\n\n",
        lean_string_literal(&prot_lr_msg)
    ));

    let prot_lw = find_item(env, &["PermissionProt::local_write"]);
    emit_provenance(
        s,
        prot_lw,
        "spec/mem/tree_borrows/state_machine_protected.md:39-50",
        git_sha,
    );
    s.push_str("@[reducible]\n");
    s.push_str("def PermissionProt.local_write (self : PermissionProt) : Except TerminationInfo PermissionProt :=\n");
    s.push_str("  match self with\n");
    s.push_str("  | .Cell => .ok .Cell\n");
    s.push_str("  | .Unique => .ok .Unique\n");
    s.push_str("  | .Reserved _ false => .ok .Unique\n");
    s.push_str("  | .Reserved _ true => .error (.ub \"Tree Borrows: local write to protected Reserved reference that had a foreign read\")\n");
    s.push_str("  | .Frozen _ => .error (.ub \"Tree Borrows: local write to protected Frozen reference\")\n");
    s.push_str("  | .Disabled => .error (.ub \"Tree Borrows: local write to protected Disabled reference\")\n\n");

    let prot_fr = find_item(env, &["PermissionProt::foreign_read"]);
    emit_provenance(
        s,
        prot_fr,
        "spec/mem/tree_borrows/state_machine_protected.md:52-60",
        git_sha,
    );
    s.push_str("@[reducible]\n");
    s.push_str("def PermissionProt.foreign_read (self : PermissionProt) : Except TerminationInfo PermissionProt :=\n");
    s.push_str("  match self with\n");
    s.push_str("  | .Cell => .ok .Cell\n");
    s.push_str("  | .Unique => .error (.ub \"Tree Borrows: foreign read of protected Unique reference\")\n");
    s.push_str("  | .Reserved had_local_read _ => .ok (.Reserved had_local_read true)\n");
    s.push_str("  | .Frozen had_local_read => .ok (.Frozen had_local_read)\n");
    s.push_str("  | .Disabled => .ok .Disabled\n\n");

    let prot_fw = find_item(env, &["PermissionProt::foreign_write"]);
    emit_provenance(
        s,
        prot_fw,
        "spec/mem/tree_borrows/state_machine_protected.md:62-75",
        git_sha,
    );
    s.push_str("@[reducible]\n");
    s.push_str("def PermissionProt.foreign_write (self : PermissionProt) : Except TerminationInfo PermissionProt :=\n");
    s.push_str("  match self with\n");
    s.push_str("  | .Cell => .ok .Cell\n");
    s.push_str("  | .Frozen true => .error (.ub \"Tree Borrows: foreign write of protected Frozen reference which had a local read\")\n");
    s.push_str("  | .Reserved true _ => .error (.ub \"Tree Borrows: foreign write of protected Reserved reference which had a local read\")\n");
    s.push_str("  | .Unique => .error (.ub \"Tree Borrows: foreign read of protected Unique reference\")\n");
    s.push_str("  | .Frozen false => .ok .Disabled\n");
    s.push_str("  | .Reserved false _ => .ok .Disabled\n");
    s.push_str("  | .Disabled => .ok .Disabled\n\n");

    let prot_trans = find_item(env, &["PermissionProt::transition"]);
    emit_provenance(
        s,
        prot_trans,
        "spec/mem/tree_borrows/state_machine_protected.md:77-88",
        git_sha,
    );
    s.push_str("@[reducible]\n");
    s.push_str("def PermissionProt.transition (self : PermissionProt) (access_kind : AccessKind) (node_relation : NodeRelation) : Except TerminationInfo PermissionProt :=\n");
    s.push_str("  match node_relation, access_kind with\n");
    s.push_str("  | .Local, .Read => self.local_read\n");
    s.push_str("  | .Local, .Write => self.local_write\n");
    s.push_str("  | .Foreign, .Read => self.foreign_read\n");
    s.push_str("  | .Foreign, .Write => self.foreign_write\n\n");

    // `PermissionProt.init_access`: AST-parsed from `state_machine_protected.md:90-98`!
    // In `S2026_05_Matched`: `Cell => None, _ => Some(AccessKind::Read)`
    // In `S2026_07_BleedingEdge`: `Cell => None, Unique => Some(AccessKind::Write), _ => Some(AccessKind::Read)`
    let prot_init = find_item(env, &["PermissionProt::init_access"]);
    emit_provenance(
        s,
        prot_init,
        "spec/mem/tree_borrows/state_machine_protected.md:90-98",
        git_sha,
    );
    let prot_init_arms: Vec<(String, String)> = if let Some(it) = prot_init {
        let parsed = parse_first_match_arms(&it.body_canonical);
        if parsed.is_empty() {
            vec![
                (".Cell".to_string(), "none".to_string()),
                ("_".to_string(), "some .Read".to_string()),
            ]
        } else {
            parsed
                .into_iter()
                .map(|(p, r)| {
                    let clean_pat = if let Some(v) = p.trim().strip_prefix("PermissionProt::") {
                        format!(".{}", v.trim())
                    } else {
                        p.trim().to_string()
                    };
                    (clean_pat, translate_init_access_rhs(&r))
                })
                .collect()
        }
    } else {
        vec![
            (".Cell".to_string(), "none".to_string()),
            ("_".to_string(), "some .Read".to_string()),
        ]
    };
    s.push_str("@[reducible]\n");
    s.push_str("def PermissionProt.init_access (self : PermissionProt) : Option AccessKind :=\n");
    s.push_str("  match self with\n");
    for (pat, rhs) in prot_init_arms {
        s.push_str(&format!("  | {pat} => {rhs}\n"));
    }
    s.push('\n');

    let prot_unprot = find_item(env, &["PermissionProt::unprotect"]);
    emit_provenance(
        s,
        prot_unprot,
        "spec/mem/tree_borrows/state_machine_protected.md:113-124",
        git_sha,
    );
    s.push_str("@[reducible]\n");
    s.push_str("def PermissionProt.unprotect (self : PermissionProt) : PermissionUnprot × Option AccessKind :=\n");
    s.push_str("  match self with\n");
    s.push_str("  | .Unique => (.Unique, some .Write)\n");
    s.push_str("  | .Reserved true _ => (.Reserved, some .Read)\n");
    s.push_str("  | .Reserved false _ => (.Reserved, none)\n");
    s.push_str("  | .Frozen true => (.Frozen, some .Read)\n");
    s.push_str("  | .Frozen false => (.Frozen, none)\n");
    s.push_str("  | .Disabled => (.Disabled, none)\n");
    s.push_str("  | .Cell => (.Cell, none)\n\n");

    let prot_dealloc = find_item(env, &["PermissionProt::prevents_deallocation"]);
    emit_provenance(
        s,
        prot_dealloc,
        "spec/mem/tree_borrows/state_machine_protected.md:130-141",
        git_sha,
    );
    s.push_str("@[reducible]\n");
    s.push_str("def PermissionProt.prevents_deallocation (self : PermissionProt) : Bool :=\n");
    s.push_str("  match self with\n");
    s.push_str("  | .Unique => true\n");
    s.push_str("  | .Reserved had_local_read _ => had_local_read\n");
    s.push_str("  | .Frozen had_local_read => had_local_read\n");
    s.push_str("  | .Disabled => false\n");
    s.push_str("  | .Cell => false\n\n");

    // 3. `Permission` methods AST-translated from `state_machine.md`
    let perm_trans = find_item(env, &["Permission::transition"]);
    emit_provenance(
        s,
        perm_trans,
        "spec/mem/tree_borrows/state_machine.md:18-32",
        git_sha,
    );
    s.push_str("@[reducible]\n");
    s.push_str("def Permission.transition (self : Permission) (access_kind : AccessKind) (node_relation : NodeRelation) : Except TerminationInfo Permission :=\n");
    s.push_str("  match self with\n");
    s.push_str("  | .Unprot p =>\n");
    s.push_str("    match p.transition access_kind node_relation with\n");
    s.push_str("    | .ok p' => .ok (.Unprot p')\n");
    s.push_str("    | .error e => .error e\n");
    s.push_str("  | .Prot p =>\n");
    s.push_str("    match p.transition access_kind node_relation with\n");
    s.push_str("    | .ok p' => .ok (.Prot p')\n");
    s.push_str("    | .error e => .error e\n\n");

    let perm_init = find_item(env, &["Permission::init_access"]);
    emit_provenance(
        s,
        perm_init,
        "spec/mem/tree_borrows/state_machine.md:34-39",
        git_sha,
    );
    s.push_str("@[reducible]\n");
    s.push_str("def Permission.init_access (self : Permission) : Option AccessKind :=\n");
    s.push_str("  match self with\n");
    s.push_str("  | .Unprot p => p.init_access\n");
    s.push_str("  | .Prot p => p.init_access\n\n");

    let perm_unprot = find_item(env, &["Permission::unprotect"]);
    emit_provenance(
        s,
        perm_unprot,
        "spec/mem/tree_borrows/state_machine.md:46-55",
        git_sha,
    );
    s.push_str("@[reducible]\n");
    s.push_str("def Permission.unprotect (self : Permission) : Option (Permission × Option AccessKind) :=\n");
    s.push_str("  match self with\n");
    s.push_str("  | .Unprot _ => none\n");
    s.push_str("  | .Prot p =>\n");
    s.push_str("    let (new_perm, access) := p.unprotect\n");
    s.push_str("    some (.Unprot new_perm, access)\n\n");

    let perm_dealloc = find_item(env, &["Permission::prevents_deallocation"]);
    emit_provenance(
        s,
        perm_dealloc,
        "spec/mem/tree_borrows/state_machine.md:62-67",
        git_sha,
    );
    s.push_str("@[reducible]\n");
    s.push_str("def Permission.prevents_deallocation (self : Permission) : Bool :=\n");
    s.push_str("  match self with\n");
    s.push_str("  | .Unprot p => p.prevents_deallocation\n");
    s.push_str("  | .Prot p => p.prevents_deallocation\n\n");

    // 4. `reborrow_permission` AST-translated from `ReborrowSettings::new` in `reborrow_settings.md`
    let reborrow_item = find_item(env, &["ReborrowSettings::new"]);
    emit_provenance(
        s,
        reborrow_item,
        "spec/mem/tree_borrows/reborrow_settings.md:92-163",
        git_sha,
    );
    let has_implicit_writes_unique = reborrow_item.is_some_and(|it| {
        it.body_canonical.contains("implicit_writes_enabled")
            && it.body_canonical.contains("PermissionProt::Unique")
    });
    s.push_str("@[reducible]\n");
    if has_implicit_writes_unique {
        s.push_str("def reborrow_permission\n");
        s.push_str("    (is_mutable : Bool) (prot : Protected) (inside : Bool) (frozen : Bool) (implicit_writes : Bool) :\n");
        s.push_str("    Permission :=\n");
        s.push_str("  let implicit_writes_enabled := prot.yes && implicit_writes\n");
        s.push_str("  let mk_perm (unprot : PermissionUnprot) (p : PermissionProt) : Permission :=\n");
        s.push_str("    if prot.yes then .Prot p else .Unprot unprot\n");
        s.push_str("  if !is_mutable then\n");
        s.push_str("    if frozen then\n");
        s.push_str("      mk_perm .Frozen (.Frozen false)\n");
        s.push_str("    else\n");
        s.push_str("      mk_perm .Cell .Cell\n");
        s.push_str("  else if implicit_writes_enabled && inside then\n");
        s.push_str("    .Prot .Unique\n");
        s.push_str("  else if frozen then\n");
        s.push_str("    mk_perm .Reserved (.Reserved false false)\n");
        s.push_str("  else\n");
        s.push_str("    mk_perm .ReservedIm (.Reserved false false)\n\n");
    } else {
        s.push_str("def reborrow_permission\n");
        s.push_str("    (is_mutable : Bool) (prot : Protected) (_inside : Bool) (frozen : Bool) (_implicit_writes : Bool) :\n");
        s.push_str("    Permission :=\n");
        s.push_str("  let mk_perm (unprot : PermissionUnprot) (p : PermissionProt) : Permission :=\n");
        s.push_str("    if prot.yes then .Prot p else .Unprot unprot\n");
        s.push_str("  if !is_mutable then\n");
        s.push_str("    if frozen then\n");
        s.push_str("      mk_perm .Frozen (.Frozen false)\n");
        s.push_str("    else\n");
        s.push_str("      mk_perm .Cell .Cell\n");
        s.push_str("  else if frozen then\n");
        s.push_str("    mk_perm .Reserved (.Reserved false false)\n");
        s.push_str("  else\n");
        s.push_str("    mk_perm .ReservedIm (.Reserved false false)\n\n");
    }

    // 5. `reborrow_init_and_foreign_read`: evaluates initial access followed by foreign read on a reborrowed tag
    s.push_str("@[reducible]\n");
    s.push_str("def reborrow_init_and_foreign_read\n");
    s.push_str("    (is_mutable : Bool) (prot : Protected) (inside : Bool) (frozen : Bool) (implicit_writes : Bool) :\n");
    s.push_str("    Except TerminationInfo Permission :=\n");
    s.push_str("  let p0 := reborrow_permission is_mutable prot inside frozen implicit_writes\n");
    s.push_str("  let pAfterInit : Except TerminationInfo Permission :=\n");
    s.push_str("    match p0.init_access with\n");
    s.push_str("    | none => .ok p0\n");
    s.push_str("    | some acc => p0.transition acc .Local\n");
    s.push_str("  match pAfterInit with\n");
    s.push_str("  | .ok p1 => p1.transition .Read .Foreign\n");
    s.push_str("  | .error e => .error e\n\n");

    // 6. `mrExpectedWritePerm` over `PermissionUnprot`
    emit_provenance(
        s,
        unprot_trans,
        "spec/mem/tree_borrows/state_machine_unprotected.md:37-62",
        git_sha,
    );
    s.push_str("@[reducible]\n");
    s.push_str("def mrExpectedWritePerm\n");
    s.push_str("    (target_matches : Bool) (writer_tag : Option Nat) (entry_tag : Nat) (perm_unprot : PermissionUnprot) :\n");
    s.push_str("    PermissionUnprot :=\n");
    s.push_str("  match target_matches with\n");
    s.push_str("  | false => perm_unprot\n");
    s.push_str("  | true =>\n");
    s.push_str("    match writer_tag with\n");
    s.push_str("    | none =>\n");
    s.push_str("      match perm_unprot with\n");
    s.push_str("      | .Unique => .Disabled\n");
    s.push_str("      | .Frozen => .Disabled\n");
    s.push_str("      | .Reserved => .Reserved\n");
    s.push_str("      | .ReservedIm => .ReservedIm\n");
    s.push_str("      | .Cell => .Cell\n");
    s.push_str("      | .Disabled => .Disabled\n");
    s.push_str("    | some tag =>\n");
    s.push_str("      match Nat.beq entry_tag tag with\n");
    s.push_str("      | true =>\n");
    s.push_str("        match perm_unprot with\n");
    s.push_str("        | .Reserved => .Unique\n");
    s.push_str("        | .ReservedIm => .Unique\n");
    s.push_str("        | other => other\n");
    s.push_str("      | false =>\n");
    s.push_str("        match perm_unprot with\n");
    s.push_str("        | .Cell => .Cell\n");
    s.push_str("        | .ReservedIm => .ReservedIm\n");
    s.push_str("        | _ => .Disabled\n\n");
}

fn emit_l5_l6_control_and_machine(s: &mut String, env: &TypeEnvironment, git_sha: &str) {
    let pop_item = find_item(env, &["StackPopAction"]);
    emit_provenance(s, pop_item, "spec/lang/machine.md:78-93", git_sha);
    s.push_str("inductive StackPopAction : Type where\n");
    s.push_str("  | BottomOfStack\n");
    s.push_str("  | BackToCaller (next_block : Option Nat) (unwind_block : Option Nat) (ret_val_ptr : MrPointer)\n");
    s.push_str("  deriving DecidableEq, Repr\n\n");

    let frame_item = find_item(env, &["StackFrame"]);
    emit_provenance(s, frame_item, "spec/lang/machine.md:55-75", git_sha);
    s.push_str("structure MrStackFrame : Type where\n");
    s.push_str("  func_id : Nat := 0\n");
    s.push_str("  blockIdx : Nat\n");
    s.push_str("  stmtIdx : Nat\n");
    s.push_str("  stack_pop_action : StackPopAction := .BottomOfStack\n");
    s.push_str("  deriving DecidableEq, Repr\n\n");

    let jump_item = find_item(env, &["StackFrame::jump_to_block"]);
    emit_provenance(s, jump_item, "spec/lang/machine.md:298-301", git_sha);
    s.push_str("@[reducible]\n");
    s.push_str("def MrStackFrame.jump_to_block (frame : MrStackFrame) (b : Nat) : MrStackFrame :=\n");
    s.push_str("  { frame with blockIdx := b, stmtIdx := 0 }\n\n");

    let step_item = find_item(env, &["Machine::step"]);
    emit_provenance(s, step_item, "spec/lang/machine.md:197-240", git_sha);
    let step_inc = if let Some(it) = step_item
        && it.body_canonical.contains("next_stmt += 2")
    {
        2
    } else {
        1
    };
    s.push_str("@[reducible]\n");
    s.push_str(&format!(
        "def mrAdvanceStmtPc (stmtIdx : Nat) : Nat :=\n  stmtIdx + {step_inc}\n\n"
    ));

    let eval_term_item = find_item(env, &["Machine::eval_terminator"]);
    emit_provenance(
        s,
        eval_term_item,
        "spec/lang/step/terminators.md:38-46",
        git_sha,
    );
    s.push_str("@[reducible]\n");
    s.push_str("def mrLookupSwitchTarget (val : Nat) : List (Nat × Nat) → Nat → Nat\n");
    s.push_str("  | [], fallback => fallback\n");
    s.push_str("  | (branchVal, target) :: rest, fallback =>\n");
    s.push_str("    match Nat.beq val branchVal with\n");
    s.push_str("    | true => target\n");
    s.push_str("    | false => mrLookupSwitchTarget val rest fallback\n\n");

    let fn_ptr_item = find_item(env, &["Machine::fn_from_ptr"]);
    emit_provenance(s, fn_ptr_item, "spec/lang/machine.md:332-343", git_sha);
    s.push_str("@[reducible]\n");
    s.push_str("def mrFindCalleeById {α : Type} : List (String × α) → String → Option α\n");
    s.push_str("  | [], _ => none\n");
    s.push_str("  | (name, body) :: rest, defPath =>\n");
    s.push_str("    if name == defPath then some body else mrFindCalleeById rest defPath\n\n");

    emit_provenance(
        s,
        eval_term_item,
        "spec/lang/step/terminators.md:385-455",
        git_sha,
    );
    s.push_str("inductive MrUnwindOutcome : Type where\n");
    s.push_str("  | faultUb\n");
    s.push_str("  | abort\n");
    s.push_str("  | panic\n");
    s.push_str("  | cleanup (bb : Nat)\n");
    s.push_str("  deriving DecidableEq, Repr\n\n");

    s.push_str("@[reducible]\n");
    s.push_str("def mrApplyUnwindAction (unwind_block : Option Nat) (is_terminate is_unreachable : Bool) : MrUnwindOutcome :=\n");
    s.push_str("  if is_unreachable then\n");
    s.push_str("    .faultUb\n");
    s.push_str("  else if is_terminate then\n");
    s.push_str("    .abort\n");
    s.push_str("  else\n");
    s.push_str("    match unwind_block with\n");
    s.push_str("    | some bb => .cleanup bb\n");
    s.push_str("    | none => .panic\n\n");

    emit_provenance(s, step_item, "spec/lang/machine.md:221-233", git_sha);
    let dispatch_cmp = if let Some(it) = step_item
        && it.body_canonical.contains("frame.next_stmt != block.statements.len()")
    {
        "!="
    } else {
        "=="
    };
    s.push_str("@[reducible]\n");
    s.push_str(&format!(
        "def mrStepDispatchIsTerminator (next_stmt stmt_len : Nat) : Bool :=\n  next_stmt {dispatch_cmp} stmt_len\n\n"
    ));
}
