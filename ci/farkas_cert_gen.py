# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Synthesize verified `Anneal.LinearArith` Farkas and cut certificates."""

from __future__ import annotations

import argparse
from collections import deque
from functools import reduce
import json
import math
import re
import sys
from typing import Any

_TOK_RE = re.compile(r"\s*(<=|<|>=|>|==|=|\+|-|\*|\(|\)|[A-Za-z_][A-Za-z0-9_']*|\d+)")
_IDENT_RE = re.compile(r"\A[A-Za-z_][A-Za-z0-9_']*\Z")
_REL_OPS = frozenset({"<=", "<", ">=", ">", "=", "=="})
_MAG_CAP_128, _MAX_LITERAL_DIGITS = 1 << 128, 40
_MAX_AST_DEPTH, _MAX_EXPR_NODES, _MAX_PARSE_NESTING, _MAX_CERT_DEPTH = 16, 48, 32, 16
_KERNEL_CAPS = {"nat": (30, 30, 176, 88, 68), "int": (44, 44, 1000, 500, 96)}
_NAT_MAX_JOINT_WORK = 360
_LEAN_KEYWORDS = frozenset((
    "Prop Sort StateRefT Type _ abbrev add_decl_doc admit assert_not_exists assert_not_imported at "
    "attribute axiom bif binder_predicate break builtin_cbv_simproc builtin_cbv_simproc_decl "
    "builtin_dsimproc builtin_dsimproc_decl builtin_grind_propagator builtin_initialize "
    "builtin_simproc builtin_simproc_decl by by_elab calc catch cbv_eval cbv_simproc "
    "cbv_simproc_decl class coinductive coinductive_fixpoint continue dbg_trace "
    "declare_bitwise_int_theorems declare_bitwise_uint_theorems declare_command_config_elab "
    "declare_command_config_elab_legacy declare_config_elab declare_config_elab_legacy "
    "declare_core_config_elab declare_eval_bin declare_eval_bin_bitwise declare_eval_bin_bool_pred "
    "declare_int_theorems declare_simp_like_tactic declare_sint_simprocs declare_syntax_cat "
    "declare_term_config_elab declare_uint_simprocs declare_uint_theorems decreasing_by def "
    "def_eval_config_item deprecated_module deprecated_syntax deriving do docs_to_verso dsimproc "
    "dsimproc_decl elab elab_rules elab_stx_quot else end eval_prec eval_prio example exists "
    "export extends false finally for forall from fun generalizing grind_annotated grind_pattern "
    "grind_propagator have haveI hiding idbg if import in include include_str inductive "
    "inductive_fixpoint inferInstanceAs infix infixl infixr init_grind_norm init_quot initialize "
    "instance leading_parser lemma let letI let_delayed let_expr let_fun let_tmp local "
    "logNamedError logNamedErrorAt logNamedWarning logNamedWarningAt macro macro_rules match "
    "match_expr matches max_prec meta mod_cast module mut mutual namespace nat_lit no_index nofun "
    "nomatch noncomputable nonrec norm_cast_add_elim notation omit opaque open partial "
    "partial_fixpoint postfix prefix prelude private protected public rec recommended_spelling "
    "register_builtin_option register_error_explanation register_grind_attr register_label_attr "
    "register_linter_set register_option register_parser_alias register_simp_attr "
    "register_sym_dsimp register_sym_simp register_sym_simp_attr register_tactic_tag renaming "
    "repeat reprove return rfl run_cmd run_elab run_meta scoped seal section "
    "set_library_suggestions set_option show show_panel_widgets show_term show_term_elab simproc "
    "simproc_decl sorry sorryAx structure suffices syntax tactic_alt tactic_extension tactic_name "
    "tactic_tag termination_by test_extern then theorem throwError throwErrorAt throwNamedError "
    "throwNamedErrorAt trailing_parser true try unif_hint universe unless unlock_limits unsafe "
    "unseal until using variable where while with with_annotate_term with_weak_namespace "
    "without_expected_type Nat Int List CutStep NatCutGoal IntCutGoal checkNatCutGoal_sound "
    "checkIntCutGoal_sound Anneal LinearArith Init Lean"
).split())


class ParseError(ValueError):
    """Raised on unsupported or malformed linear arithmetic input."""


def _as_const(n: tuple[Any, ...]) -> int | None:
    if n[0] in ("cst", "var"):
        return n[1] if n[0] == "cst" else None
    if n[0] in ("neg", "mulC"):
        return None if (v := _as_const(n[-1])) is None else (-v if n[0] == "neg" else n[1] * v)
    a, b = _as_const(n[1]), _as_const(n[2])
    return None if (a is None or b is None) else (a + b if n[0] == "add" else a - b)


def _eval_linear(n: tuple[Any, ...]) -> tuple[dict[str, int], int]:
    if n[0] in ("cst", "var"):
        return ({}, n[1]) if n[0] == "cst" else ({n[1]: 1}, 0)
    if n[0] in ("neg", "mulC"):
        c, c0 = _eval_linear(n[-1])
        s = -1 if n[0] == "neg" else n[1]
        return {v: s * w for v, w in c.items() if s * w}, s * c0
    lc, lk = _eval_linear(n[1])
    rc, rk = _eval_linear(n[2])
    sgn = 1 if n[0] == "add" else -1
    return {v: nv for v in (*lc, *rc) if (nv := lc.get(v, 0) + sgn * rc.get(v, 0))}, lk + sgn * rk


def _walk_ast(
    n: tuple[Any, ...], domain: str, vars_out: dict[str, None] | None = None, *, caps: bool = False
) -> tuple[int, int, int, bool]:
    k = n[0]
    if k == "cst":
        if caps and ((domain == "nat" and n[1] < 0) or abs(n[1]) > _MAG_CAP_128):
            raise ParseError("Constant out of range (`< 0` in nat or `> 2^128`).")
        d, cnt, vo, hv = 0, 1, 0, False
    elif k == "var":
        if vars_out is not None:
            vars_out.setdefault(n[1], None)
        d, cnt, vo, hv = 0, 1, 1, True
    elif k in ("neg", "mulC"):
        if caps and k == "mulC" and abs(n[1]) > _MAG_CAP_128:
            raise ParseError("Multiplier exceeds `magCap128` (`2^128`).")
        sd, sc, vo, hv = _walk_ast(n[-1], domain, vars_out, caps=caps)
        d, cnt = 1 + sd, 1 + sc
    else:
        ld, lc, lv, lhv = _walk_ast(n[1], domain, vars_out, caps=caps)
        rd, rc, rv, rhv = _walk_ast(n[2], domain, vars_out, caps=caps)
        d, cnt, vo, hv = 1 + max(ld, rd), 1 + lc + rc, lv + rv, lhv or rhv
    if caps and (d > _MAX_AST_DEPTH or cnt > _MAX_EXPR_NODES):
        raise ParseError(f"Expression exceeds kernel limits (depth {d}, nodes {cnt}).")
    return d, cnt, vo, hv


def _parse_expr(tokens: list[str], domain: str, *, reserved: frozenset[str]) -> tuple[Any, ...]:
    pos = 0

    def pop(exp: str | None = None) -> str:
        nonlocal pos
        tok = tokens[pos] if pos < len(tokens) else None
        if tok is None or (exp is not None and tok != exp):
            raise ParseError(f"Expected `{exp or 'expr'}`, got {tok or 'EOF'}")
        pos += 1
        return tok

    def int_lit(tok: str, neg: bool = False) -> int:
        if len(tok) > _MAX_LITERAL_DIGITS:
            raise ParseError("Constant exceeds `magCap128` (`2^128`).")
        return -int(tok) if neg else int(tok)

    def expr(depth: int = 0) -> tuple[Any, ...]:
        if depth > _MAX_PARSE_NESTING:
            raise ParseError("Expression nesting depth exceeded.")
        acc = term(depth)
        while pos < len(tokens) and tokens[pos] in ("+", "-"):
            if (op := pop()) == "-" and domain == "nat":
                raise ParseError("Subtraction disallowed in `--domain nat`; use `--domain int`.")
            acc = ("add" if op == "+" else "sub", acc, term(depth))
        return acc

    def term(depth: int) -> tuple[Any, ...]:
        acc = unary(depth)
        while pos < len(tokens) and tokens[pos] == "*":
            pop("*")
            lc, rc = _as_const(acc), _as_const(rhs := unary(depth))
            if lc is not None and rc is not None:
                if abs(prod := lc * rc) > _MAG_CAP_128:
                    raise ParseError("Constant exceeds `magCap128` (`2^128`).")
                acc = ("cst", prod)
            elif lc is not None:
                acc = ("mulC", lc, rhs)
            else:
                raise ParseError("Put scalar multiplier on left (`2 * x`), no var*var.")
        return acc

    def unary(depth: int) -> tuple[Any, ...]:
        if depth > _MAX_PARSE_NESTING:
            raise ParseError("Expression nesting depth exceeded.")
        nxt = tokens[pos] if pos < len(tokens) else None
        if nxt == "+":
            return pop("+") and unary(depth + 1)
        if nxt == "-":
            if domain == "nat":
                raise ParseError("Unary `-` disallowed in `--domain nat`; use `--domain int`.")
            pop("-")
            if pos < len(tokens) and tokens[pos].isdigit():
                return ("cst", int_lit(pop(), True))
            return ("neg", unary(depth + 1))
        if nxt == "(":
            pop("(")
            res = expr(depth + 1)
            pop(")")
            return res
        tok = pop()
        if tok.isdigit():
            return ("cst", int_lit(tok))
        if (not _IDENT_RE.match(tok) or tok in _LEAN_KEYWORDS
                or tok in reserved or re.match(r"\Ah\d+\Z", tok)):
            raise ParseError(f"Unsupported or reserved Lean variable: `{tok}`")
        return ("var", tok)

    out = expr()
    if pos != len(tokens):
        raise ParseError(f"Trailing token `{tokens[pos]}`")
    return out


def parse_inequalities(
    text: str, domain: str, *, reserved: frozenset[str] = frozenset()
) -> list[tuple[tuple[Any, ...], str, tuple[Any, ...]]]:
    """Parse linear relation(s) into `(lhs_ast, rel_op, rhs_ast)` tuples."""
    pos, toks = 0, []
    while pos < len(text):
        if text[pos].isspace():
            pos += 1
        elif m := _TOK_RE.match(text, pos):
            toks.append(m.group(1))
            pos = m.end()
        else:
            raise ParseError(f"Unexpected syntax at col {pos + 1} in `{text}`")
    rels = [i for i, t in enumerate(toks) if t in _REL_OPS]
    if len(rels) != 1:
        raise ParseError(f"Expected one comparison operator in `{text}`")
    rpos, op = rels[0], toks[rels[0]]
    lhs = _parse_expr(toks[:rpos], domain, reserved=reserved)
    rhs = _parse_expr(toks[rpos + 1 :], domain, reserved=reserved)
    _walk_ast(lhs, domain, caps=True)
    _walk_ast(rhs, domain, caps=True)
    return [(lhs, "<=", rhs), (rhs, "<=", lhs)] if op in ("=", "==") else [(lhs, op, rhs)]


def _ast_to_le(lhs: tuple[Any, ...], op: str, rhs: tuple[Any, ...]) -> tuple[Any, Any, str]:
    if op in ("<=", "<"):
        return (lhs, rhs, "≤") if op == "<=" else (("add", lhs, ("cst", 1)), rhs, "<")
    return (rhs, lhs, "≤") if op == ">=" else (("add", rhs, ("cst", 1)), lhs, "<")


def _sint(k: int, *, ascii_lean: bool = False) -> str:
    neg = "true" if k < 0 else "false"
    return f"{{ neg := {neg}, mag := {abs(k)} }}" if ascii_lean else f"⟨{neg}, {abs(k)}⟩"


def _render_pair(
    n: tuple[Any, ...], vidx: dict[str, int], domain: str,
    *, min_prec: int = 0, ascii_lean: bool = False,
) -> tuple[str, str]:
    op = n[0]
    if op == "cst":
        if domain == "nat":
            return f".cst {n[1]}", str(n[1])
        surf = f"Int.negOfNat {abs(n[1])}" if n[1] < 0 else str(n[1])
        if n[1] < 0 and min_prec >= 90:
            surf = f"({surf})"
        return f".cst {_sint(n[1], ascii_lean=ascii_lean)}", surf
    if op == "var":
        return f".var {vidx[n[1]]}", n[1]
    if op == "neg":
        sa, sp = _render_pair(n[1], vidx, domain, min_prec=100, ascii_lean=ascii_lean)
        p = f"Int.neg {sp}"
        return f".neg ({sa})", f"({p})" if min_prec >= 90 else p
    if op == "mulC":
        sa, sp = _render_pair(n[2], vidx, domain, min_prec=75, ascii_lean=ascii_lean)
        ka = str(n[1]) if domain == "nat" else _sint(n[1], ascii_lean=ascii_lean)
        kp = str(n[1]) if (domain == "nat" or n[1] >= 0) else f"Int.negOfNat {abs(n[1])}"
        p = f"{kp} * {sp}"
        return f".mulC {ka} ({sa})", f"({p})" if 70 < min_prec else p
    la, lp = _render_pair(n[1], vidx, domain, min_prec=65, ascii_lean=ascii_lean)
    ra, rp = _render_pair(n[2], vidx, domain, min_prec=66, ascii_lean=ascii_lean)
    sym, ctor = ("+", ".add") if op == "add" else ("-", ".sub")
    p = f"{lp} {sym} {rp}"
    return f"{ctor} ({la}) ({ra})", f"({p})" if 65 < min_prec else p


def _comb_rows(
    r1: tuple[tuple[tuple[int, int], ...], int], k1: int,
    r2: tuple[tuple[tuple[int, int], ...], int], k2: int,
) -> tuple[tuple[tuple[int, int], ...], int] | None:
    if k1 > _MAG_CAP_128 or k2 > _MAG_CAP_128:
        return None
    m: dict[int, int] = {}
    for row, k in ((r1, k1), (r2, k2)):
        for i, c in row[0]:
            m[i] = m.get(i, 0) + k * c
    terms = tuple(sorted((i, c) for i, c in m.items() if c))
    rhs = k1 * r1[1] + k2 * r2[1]
    if abs(rhs) > _MAG_CAP_128 or any(abs(c) > _MAG_CAP_128 for _, c in terms):
        return None
    return terms, rhs


def _step_dict(st: tuple[Any, ...]) -> dict[str, Any]:
    return {"op": st[0], **(
        {"idx": st[1]} if st[0] == "hyp"
        else {"g": st[1], "s": st[2]} if st[0] == "divCut"
        else {"s1": st[1], "k1": st[2], "s2": st[3], "k2": st[4]}
    )}


def _rebalance_steps(
    raw: list[tuple[Any, ...]], hyp_map: dict[int, tuple[tuple[tuple[int, int], ...], int]]
) -> list[dict[str, Any]]:
    """Collapse `.comb` subtrees into balanced `O(log n)` binary reductions."""
    weights: list[dict[int, int]] = []
    for sid, st in enumerate(raw):
        if st[0] != "comb":
            weights.append({sid: 1})
            continue
        w: dict[int, int] = {}
        for ch, mult in ((st[1], st[2]), (st[3], st[4])):
            for aid, aw in weights[ch].items():
                if (nw := w.get(aid, 0) + mult * aw) > _MAG_CAP_128:
                    return [_step_dict(s) for s in raw]
                if nw:
                    w[aid] = nw
        weights.append(w)
    out_steps, out_rows, emitted = [], [], {}

    def emit(step: tuple[Any, ...], row: Any) -> int:
        out_steps.append(step)
        out_rows.append(row)
        return len(out_steps) - 1

    def mat(sid: int) -> int | None:
        if sid in emitted:
            return emitted[sid]
        st = raw[sid]
        if st[0] == "hyp":
            return emitted.setdefault(sid, emit(st, hyp_map[st[1]]))
        if st[0] == "divCut":
            if (cid := mat(st[2])) is None:
                return None
            t, r, g = *out_rows[cid], st[1]
            return emitted.setdefault(
                sid, emit(("divCut", g, cid), (tuple((i, c // g) for i, c in t if c // g), r // g))
            )
        layer = []
        for aid, w in sorted(weights[sid].items()):
            if (eid := mat(aid)) is None:
                return None
            layer.append((eid, w))
        if len(layer) == 1:
            eid, w = layer[0]
            if w == 1:
                return emitted.setdefault(sid, eid)
            layer = [(eid, w - 1), (eid, 1)]
        while len(layer) > 1:
            nxt = []
            for j in range(0, len(layer), 2):
                if j + 1 >= len(layer):
                    nxt.append(layer[j])
                else:
                    (s1, k1), (s2, k2) = layer[j], layer[j + 1]
                    if (row := _comb_rows(out_rows[s1], k1, out_rows[s2], k2)) is None:
                        return None
                    nxt.append((emit(("comb", s1, k1, s2, k2), row), 1))
            layer = nxt
        return emitted.setdefault(sid, layer[0][0])

    rid = mat(len(raw) - 1) if raw else None
    final = raw if (rid is None or out_rows[rid][0] or out_rows[rid][1] >= 0) else out_steps
    return [_step_dict(s) for s in final]


def solve_cut_refutation(
    indexed_rows: list[tuple[int, tuple[tuple[tuple[int, int], ...], int]]], max_nodes: int = 2500
) -> list[dict[str, Any]] | None:
    """Search Fourier-Motzkin + Chvatal-Gomory steps deriving `0 <= -1`."""
    nodes, best, q, hyp_map = [], {}, deque(), dict(indexed_rows)

    def push(t: tuple[tuple[int, int], ...], r: int, st: tuple[Any, ...]) -> int | None:
        if abs(r) > _MAG_CAP_128 or any(abs(c) > _MAG_CAP_128 for _, c in t):
            return None
        if (prev := best.get(t)) is not None and prev[0] <= r:
            return None
        nodes.append((t, r, st))
        nid = len(nodes) - 1
        best[t] = (r, nid)
        q.append(nid)
        return nid

    def replay(gid: int) -> list[dict[str, Any]]:
        need, stack = set(), [gid]
        while stack:
            if (cur := stack.pop()) not in need:
                need.add(cur)
                st = nodes[cur][2]
                if st[0] != "hyp":
                    stack.extend((st[1], st[3]) if st[0] == "comb" else (st[2],))
        remap, out = {}, []
        for idx, oid in enumerate(sorted(need)):
            remap[oid], st = idx, nodes[oid][2]
            out.append(st if st[0] == "hyp" else (
                ("comb", remap[st[1]], st[2], remap[st[3]], st[4]) if st[0] == "comb"
                else ("divCut", st[1], remap[st[2]])
            ))
        return _rebalance_steps(out, hyp_map)

    for hyp_idx, (t, r) in indexed_rows:
        if (nid := push(t, r, ("hyp", hyp_idx))) is not None and not t and r < 0:
            return replay(nid)
    while q and len(nodes) < max_nodes:
        nid = q.popleft()
        terms, rhs, _ = nodes[nid]
        if terms and (g := reduce(math.gcd, (abs(c) for _, c in terms))) > 1:
            push(tuple((i, c // g) for i, c in terms), rhs // g, ("divCut", g, nid))
        tmap = dict(terms)
        for _, oid in list(best.values()):
            if oid == nid or len(nodes) >= max_nodes:
                continue
            ot, orhs, _ = nodes[oid]
            otmap = dict(ot)
            for vid, c1 in tmap.items():
                if not ((c2 := otmap.get(vid, 0)) and ((c1 > 0) != (c2 > 0))):
                    continue
                g = math.gcd(abs(c1), abs(c2))
                k1, k2 = abs(c2) // g, abs(c1) // g
                comb = _comb_rows((terms, rhs), k1, (ot, orhs), k2)
                if comb and len(comb[0]) <= max(len(terms), len(ot)) + 2:
                    if (cid := push(*comb, ("comb", nid, k1, oid, k2))) is not None:
                        if not comb[0] and comb[1] < 0:
                            return replay(cid)
                if len(nodes) >= max_nodes:
                    break
    return None


def _goal_stats(
    hyps: list[tuple[Any, ...]], gl: Any, gr: Any, domain: str
) -> tuple[list[str], int, int]:
    vset: dict[str, None] = {}
    nodes = voccs = 0
    for la, ra in [*((r[1], r[2]) for r in hyps), (gl, gr)]:
        _, ln, lv, _ = _walk_ast(la, domain, vset)
        _, rn, rv, _ = _walk_ast(ra, domain, vset)
        nodes, voccs = nodes + ln + rn, voccs + lv + rv
    return list(vset), nodes, voccs


def _prune_and_check(
    le_hyps: list[tuple[Any, ...]], gl_le: Any, gr_le: Any,
    orig_vars: list[str], steps: list[dict[str, Any]], domain: str,
) -> tuple[list[tuple[Any, ...]], list[str], dict[str, int], list[dict[str, Any]], list[int]]:
    orig_n = len(le_hyps)
    orig_neg = orig_n + (len(orig_vars) if domain == "nat" else 0)
    used = sorted({s["idx"] for s in steps if s["op"] == "hyp" and s["idx"] < orig_n})
    pruned = [le_hyps[i] for i in used]
    vars_, nodes, voccs = _goal_stats(pruned, gl_le, gr_le, domain)
    umap, vidx = {old: new for new, old in enumerate(used)}, {nm: i for i, nm in enumerate(vars_)}
    new_neg = len(pruned) + (len(vars_) if domain == "nat" else 0)
    depths: list[int] = []
    for st in steps:
        if st["op"] == "hyp":
            si = st["idx"]
            st["idx"] = (umap[si] if si < orig_n else
                         len(pruned) + vidx[orig_vars[si - orig_n]] if si < orig_neg else new_neg)
        depths.append(1 if st["op"] == "hyp" else (
            1 + depths[st["s"]] if st["op"] == "divCut"
            else 1 + max(depths[st["s1"]], depths[st["s2"]])
        ))
    mv, mh, mn, mvo, ms = _KERNEL_CAPS[domain]
    jwork = 2 * len(vars_) + 2 * len(pruned) + nodes + voccs + len(steps)
    if (len(vars_) > mv or len(pruned) > mh or nodes > mn or voccs > mvo
            or len(steps) > ms or max(depths, default=0) > _MAX_CERT_DEPTH
            or (domain == "nat" and jwork > _NAT_MAX_JOINT_WORK)):
        raise ParseError(f"Certificate exceeds Lean maxRecDepth bounds (`--domain {domain}`: "
                         f"vars {len(vars_)}/{mv}, hyps {len(pruned)}/{mh}, nodes {nodes}/{mn}).")
    return pruned, vars_, vidx, steps, sorted({le_hyps[i][0] for i in used})


def generate_certificate(
    domain: str, hyp_strings: list[str], goal_string: str,
    thm_name: str = "linear_bound", max_nodes: int = 2500, *, ascii_lean: bool = False,
) -> dict[str, Any]:
    """Synthesize a `CutStep` certificate and `Anneal.LinearArith` snippet."""
    if max_nodes < 1:
        raise ParseError("`--max-nodes` must be >= 1.")
    if not _IDENT_RE.match(thm_name) or thm_name in _LEAN_KEYWORDS:
        raise ParseError(f"Unsupported or reserved Lean name: `{thm_name}`")
    reserved = frozenset({thm_name, f"{thm_name}_goal", f"{thm_name}_cert"})
    parsed_hyps = [(i, iq) for i, hs in enumerate(hyp_strings)
                   for iq in parse_inequalities(hs, domain, reserved=reserved)]
    goals = parse_inequalities(goal_string, domain, reserved=reserved)
    if len(goals) != 1:
        raise ParseError("`--goal` must be a single inequality (`<=`, `<`, `>=`, or `>`).")
    le_hyps = [(i, *_ast_to_le(l, op, r), l, op, r) for i, (l, op, r) in parsed_hyps]
    gl_le, gr_le, g_sym, gl_orig, g_op, gr_orig = (*_ast_to_le(*goals[0]), *goals[0])
    vars_, _, _ = _goal_stats(le_hyps, gl_le, gr_le, domain)
    vidx = {nm: i for i, nm in enumerate(vars_)}

    def to_sparse(lhs: Any, rhs: Any) -> tuple[tuple[tuple[int, int], ...], int]:
        lc, lk = _eval_linear(lhs)
        rc, rk = _eval_linear(rhs)
        m = {vidx[nm]: lc.get(nm, 0) - rc.get(nm, 0) for nm in (*lc, *rc)}
        terms, delta = tuple(sorted((i, c) for i, c in m.items() if c)), rk - lk
        if abs(delta) > _MAG_CAP_128 or any(abs(c) > _MAG_CAP_128 for _, c in terms):
            raise ParseError("Normalized row exceeds `magCap128` (`2^128`).")
        return terms, delta

    hyp_rows = [to_sparse(la, ra) for _, la, ra, *_ in le_hyps]
    neg_row = to_sparse(("add", gr_le, ("cst", 1)), gl_le)
    neg_idx = len(le_hyps) + (len(vars_) if domain == "nat" else 0)
    steps = solve_cut_refutation([*enumerate(hyp_rows), (neg_idx, neg_row)], max_nodes)
    if steps is None and domain == "nat" and vars_:
        nn = [to_sparse(("cst", 0), ("var", nm)) for nm in vars_]
        steps = solve_cut_refutation(list(enumerate([*hyp_rows, *nn, neg_row])), max_nodes)
    if steps is None:
        return {"solved": False, "domain": domain, "variables": vars_,
                "error": f"No Farkas/Chvatal-Gomory refutation found within max_nodes={max_nodes}."}
    le_hyps, vars_, vidx, steps, kept = _prune_and_check(
        le_hyps, gl_le, gr_le, vars_, steps, domain
    )
    rp = lambda node: _render_pair(node, vidx, domain, ascii_lean=ascii_lean)  # noqa: E731
    pair = lambda a, b: f"{{ lhs := {a}, rhs := {b} }}" if ascii_lean else f"⟨{a}, {b}⟩"

    def prop_rel(ol: Any, op: str, or_: Any, sym: str) -> str:
        ln, rn = (or_, ol) if op in (">=", ">") else (ol, or_)
        osym = "<=" if (ascii_lean and sym == "≤") else sym
        if domain == "int" and not _walk_ast(ln, domain)[3] and not _walk_ast(rn, domain)[3]:
            return f"({rp(ln)[1]} : Int) {osym} ({rp(rn)[1]} : Int)"
        return f"{rp(ln)[1]} {osym} {rp(rn)[1]}"

    hyp_lits = ", ".join(pair(rp(la)[0], rp(ra)[0]) for _, la, ra, *_ in le_hyps)
    step_lits = ", ".join(
        f".hyp {s['idx']}" if s["op"] == "hyp"
        else f".comb {s['s1']} {s['k1']} {s['s2']} {s['k2']}" if s["op"] == "comb"
        else f".divCut {s['g']} {s['s']}" for s in steps
    )
    gty, thm, vty = (("NatCutGoal", "checkNatCutGoal_sound", "Nat") if domain == "nat"
                     else ("IntCutGoal", "checkIntCutGoal_sound", "Int"))
    h_bind = "".join(f" (h{i} : {prop_rel(lo, op, ro, sym)})"
                     for i, (_, _, _, sym, lo, op, ro) in enumerate(le_hyps))
    p_args = " ".join(f"h{i}" for i in range(len(le_hyps)))
    v_bind = f"({' '.join(vars_)} : {vty})" if vars_ else ""
    tail = f"[{', '.join(vars_)}]{(' ' + p_args) if p_args else ''}"
    snippet = (
        f"import Anneal.LinearArith\nopen Anneal.LinearArith\n\n"
        f"private def {thm_name}_goal : {gty} :=\n"
        f"  {{ hyps := [{hyp_lits}],\n    concl := {pair(rp(gl_le)[0], rp(gr_le)[0])} }}\n\n"
        f"private def {thm_name}_cert : List CutStep :=\n  [{step_lits}]\n\n"
        f"private theorem {thm_name} {v_bind}{h_bind} :\n"
        f"    {prop_rel(gl_orig, g_op, gr_orig, g_sym)} :=\n"
        f"  {thm} {thm_name}_goal {thm_name}_cert rfl {tail}"
    )
    return {"solved": True, "domain": domain, "variables": vars_,
            "kept_hyp_indices": kept, "steps": steps, "lean_snippet": snippet}


_SUPPORTED_WIDTHS = frozenset({8, 16, 32, 64, 128})
# Global Lean identifiers referenced by `--mir-bounds` snippets. User variables
# are bound as theorem binders, so a variable with one of these names would
# shadow the global and make the emitted snippet ill-typed.
_MIR_SNIPPET_RESERVED = frozenset((
    "modPow2 uintWidth uintBytes scalarModulus evalScalarBinOp ValidSliceRange "
    "evalPtrOffset AlignedPtr NonOverlappingPtrs WrappedInterval RawPtrVal LocalSlot "
    "Memory NatCutIneq NatLinExpr ScalarInt UintTy UintScalarInRange some none "
    "Bool Option And Or Not True False Eq FarkasMirCert wrappedInterval_denote_bounds "
    "farkas_discharges_slice_bounds farkas_discharges_aligned_stride "
    "farkas_discharges_u64_add_no_overflow farkas_discharges_uint_add_no_overflow "
    "farkas_discharges_uint_sub_no_underflow farkas_discharges_uint_sub_no_underflow_certified "
    "farkas_discharges_uint_mul_const_no_overflow farkas_discharges_non_overlapping_ptrs "
    "farkas_discharges_aipcc_interval_refinement"
).split())
_ENTAILMENT_SNIPPET_RESERVED = frozenset((
    "NatLinSpec IntLinSpec NatAdequacyMode IntAdequacyMode "
    "NatEntailmentAdequacyProp IntEntailmentAdequacyProp "
    "farkas_entailment_adequacy_cert farkas_int_entailment_adequacy_cert "
    "NatCutIneq IntCutIneq NatLinExpr IntLinExpr SInt FarkasMirCert"
).split())
_MIR_BOUNDS_PRESETS = (
    "slice-range",
    "aligned-stride",
    "uint-add-no-overflow",
    "uint-sub-no-underflow",
    "aipcc-interval-refine",
    "uint-mul-const-no-overflow",
    "non-overlapping-ptrs",
)


def _tokenize(text: str) -> list[str]:
    pos, toks = 0, []
    while pos < len(text):
        if text[pos].isspace():
            pos += 1
        elif m := _TOK_RE.match(text, pos):
            toks.append(m.group(1))
            pos = m.end()
        else:
            raise ParseError(f"Unexpected syntax at col {pos + 1} in `{text}`")
    return toks


def _parse_expr_str(
    text: str, domain: str, *, reserved: frozenset[str] = frozenset()
) -> tuple[Any, ...]:
    toks = _tokenize(text)
    if not toks:
        raise ParseError("Empty linear expression.")
    if any(t in _REL_OPS for t in toks):
        raise ParseError(f"Expected expression without comparison operator, got `{text}`")
    ast = _parse_expr(toks, domain, reserved=reserved)
    _walk_ast(ast, domain, caps=True)
    return ast


def _collect_vars(asts: list[tuple[Any, ...]], domain: str) -> list[str]:
    vset: dict[str, None] = {}
    for node in asts:
        _walk_ast(node, domain, vset)
    return list(vset)


def _nat_goal_var_order(
    le_hyps: list[tuple[Any, Any]], gl_le: Any, gr_le: Any, vidx: dict[str, int]
) -> list[int]:
    """Mirror `Anneal.LinearArith.natGoalVars` exact first-occurrence order."""
    seen: dict[int, None] = {}

    def visit(n: tuple[Any, ...]) -> None:
        k = n[0]
        if k == "var":
            seen.setdefault(vidx[n[1]], None)
        elif k in ("neg", "mulC"):
            visit(n[-1])
        elif k in ("add", "sub"):
            visit(n[1])
            visit(n[2])

    for la, ra in le_hyps:
        visit(la)
        visit(ra)
    visit(gl_le)
    visit(gr_le)
    return list(seen)


def _to_sparse_fixed(
    lhs: Any, rhs: Any, vidx: dict[str, int]
) -> tuple[tuple[tuple[int, int], ...], int]:
    lc, lk = _eval_linear(lhs)
    rc, rk = _eval_linear(rhs)
    m = {vidx[nm]: lc.get(nm, 0) - rc.get(nm, 0) for nm in (*lc, *rc)}
    terms, delta = tuple(sorted((i, c) for i, c in m.items() if c)), rk - lk
    if abs(delta) > _MAG_CAP_128 or any(abs(c) > _MAG_CAP_128 for _, c in terms):
        raise ParseError("Normalized row exceeds `magCap128` (`2^128`).")
    return terms, delta


def _check_fixed_goal_caps(
    le_hyps: list[tuple[Any, Any]], gl_le: Any, gr_le: Any,
    steps: list[dict[str, Any]], domain: str,
) -> None:
    vset: dict[str, None] = {}
    nodes = voccs = 0
    for la, ra in [*le_hyps, (gl_le, gr_le)]:
        _, ln, lv, _ = _walk_ast(la, domain, vset, caps=True)
        _, rn, rv, _ = _walk_ast(ra, domain, vset, caps=True)
        nodes, voccs = nodes + ln + rn, voccs + lv + rv
    depths: list[int] = []
    for st in steps:
        depths.append(
            1 if st["op"] == "hyp"
            else (1 + depths[st["s"]] if st["op"] == "divCut"
                  else 1 + max(depths[st["s1"]], depths[st["s2"]]))
        )
    mv, mh, mn, mvo, ms = _KERNEL_CAPS[domain]
    jwork = 2 * len(vset) + 2 * len(le_hyps) + nodes + voccs + len(steps)
    if (len(vset) > mv or len(le_hyps) > mh or nodes > mn or voccs > mvo
            or len(steps) > ms or max(depths, default=0) > _MAX_CERT_DEPTH
            or (domain == "nat" and jwork > _NAT_MAX_JOINT_WORK)):
        raise ParseError(
            f"Certificate exceeds Lean maxRecDepth bounds (`--domain {domain}`: "
            f"vars {len(vset)}/{mv}, hyps {len(le_hyps)}/{mh}, nodes {nodes}/{mn})."
        )


def _solve_fixed_goal(
    domain: str, le_hyps: list[tuple[Any, Any]], gl_le: Any, gr_le: Any,
    vidx: dict[str, int], max_nodes: int,
) -> list[dict[str, Any]] | None:
    hyp_rows = [_to_sparse_fixed(la, ra, vidx) for la, ra in le_hyps]
    neg_row = _to_sparse_fixed(("add", gr_le, ("cst", 1)), gl_le, vidx)
    g_var_ids = _nat_goal_var_order(le_hyps, gl_le, gr_le, vidx) if domain == "nat" else []
    neg_idx = len(le_hyps) + (len(g_var_ids) if domain == "nat" else 0)
    steps = solve_cut_refutation([*enumerate(hyp_rows), (neg_idx, neg_row)], max_nodes)
    if steps is None and domain == "nat" and g_var_ids:
        nn = [(((vid, -1),), 0) for vid in g_var_ids]
        steps = solve_cut_refutation(list(enumerate([*hyp_rows, *nn, neg_row])), max_nodes)
    if steps is not None:
        _check_fixed_goal_caps(le_hyps, gl_le, gr_le, steps, domain)
    return steps


def _format_steps(steps: list[dict[str, Any]]) -> str:
    return ", ".join(
        f".hyp {s['idx']}" if s["op"] == "hyp"
        else f".comb {s['s1']} {s['k1']} {s['s2']} {s['k2']}" if s["op"] == "comb"
        else f".divCut {s['g']} {s['s']}" for s in steps
    )


def _format_ineq_pair(a: str, b: str, *, ascii_lean: bool) -> str:
    return f"{{ lhs := {a}, rhs := {b} }}" if ascii_lean else f"⟨{a}, {b}⟩"


def _format_scalar(bits_expr: str, sz_expr: str, *, ascii_lean: bool) -> str:
    if ascii_lean:
        return f"{{ bits := {bits_expr}, sizeBytes := {sz_expr} }}"
    return f"⟨{bits_expr}, {sz_expr}⟩"


def _render_int_val(val: int) -> str:
    return f"Int.negOfNat {abs(val)}" if val < 0 else f"Int.ofNat {val}"


def _eval_ast_env(ast: tuple[Any, ...], env_map: dict[str, int]) -> int:
    coeffs, const = _eval_linear(ast)
    return const + sum(c * env_map[v] for v, c in coeffs.items())


def _validate_common_args(thm_name: str, max_nodes: int) -> None:
    if max_nodes < 1:
        raise ParseError("`--max-nodes` must be >= 1.")
    if not _IDENT_RE.match(thm_name) or thm_name in _LEAN_KEYWORDS:
        raise ParseError(f"Unsupported or reserved Lean name: `{thm_name}`")


def _mir_header() -> str:
    return (
        "import Anneal.FarkasMirCert\n"
        "open Anneal.LinearArith Anneal.AiPcc Anneal.UnsafeObligations Anneal.FarkasMirCert\n"
        "open Trusted.Rustc.V2026_06_01.MirAst Trusted.Rustc.V2026_06_01.MirSemantics\n\n"
    )


def _format_nat_prop_rel(
    ol: Any, op: str, or_: Any, sym: str, vidx: dict[str, int], *, ascii_lean: bool
) -> str:
    ln, rn = (or_, ol) if op in (">=", ">") else (ol, or_)
    osym = "<=" if (ascii_lean and sym == "≤") else sym
    lp = _render_pair(ln, vidx, "nat", ascii_lean=ascii_lean)[1]
    rp_ = _render_pair(rn, vidx, "nat", ascii_lean=ascii_lean)[1]
    return f"{lp} {osym} {rp_}"


def parse_witness(
    text: str, vars_: list[str], domain: str
) -> tuple[list[int] | None, str | None]:
    """Parse `v0=c0,v1=c1` into an ordered environment matching `vars_`."""
    stripped = text.strip()
    assigned: dict[str, int] = {}
    if stripped:
        for raw_entry in stripped.split(","):
            entry = raw_entry.strip()
            if not entry or "=" not in entry:
                raise ParseError(f"Malformed witness entry `{raw_entry}`; expected `var=int`.")
            lhs_s, rhs_s = entry.split("=", 1)
            vname, val_s = lhs_s.strip(), rhs_s.strip()
            if not _IDENT_RE.match(vname):
                raise ParseError(f"Invalid witness variable name `{vname}`.")
            if vname in assigned:
                raise ParseError(f"Duplicate witness assignment for `{vname}`.")
            if not re.match(r"\A[+-]?\d+\Z", val_s):
                raise ParseError(f"Invalid integer witness value `{val_s}` for `{vname}`.")
            digits = val_s.lstrip("+-")
            if len(digits) > _MAX_LITERAL_DIGITS:
                raise ParseError(f"Witness literal for `{vname}` exceeds digit limit.")
            assigned[vname] = int(val_s)
    var_set = set(vars_)
    extra = [v for v in assigned if v not in var_set]
    if extra:
        raise ParseError(f"Witness assigns unknown variable(s): {', '.join(extra)}.")
    missing = [v for v in vars_ if v not in assigned]
    if missing:
        raise ParseError(f"Witness is missing variable(s): {', '.join(missing)}.")
    if domain == "nat":
        for v in vars_:
            if assigned[v] < 0:
                return None, (
                    f"Witness assigns negative value {assigned[v]} to `{v}` in `--domain nat`."
                )
    return [assigned[v] for v in vars_], None


def generate_mir_bounds_certificate(
    preset: str,
    hyp_strings: list[str],
    thm_name: str = "mir_bound",
    max_nodes: int = 2500,
    *,
    width: int = 64,
    align: int = 8,
    scale: int = 1,
    offset_expr: str = "off",
    len_expr: str = "len",
    total_expr: str = "total",
    quot_expr: str = "q",
    lhs_expr: str = "a",
    rhs_expr: str = "b",
    var_name: str = "x",
    target_lo: int | None = None,
    target_hi: int | None = None,
    src_lo: int | None = None,
    src_hi: int | None = None,
    src_offset_expr: str = "src_off",
    dst_offset_expr: str = "dst_off",
    count_expr: str = "count",
    direction: str = "src-before-dst",
    ascii_lean: bool = False,
) -> dict[str, Any]:
    """Synthesize verified `Anneal.FarkasMirCert` MIR/UnsafeObligations/AiPcc certificates."""
    _validate_common_args(thm_name, max_nodes)
    if preset not in _MIR_BOUNDS_PRESETS:
        raise ParseError(f"Unsupported `--mir-bounds` preset: `{preset}`")
    base_reserved = _MIR_SNIPPET_RESERVED
    if thm_name in base_reserved:
        raise ParseError(f"Unsupported or reserved Lean name: `{thm_name}`")
    conj = "/\\" if ascii_lean else "∧"
    le_sym = "<=" if ascii_lean else "≤"

    if preset == "slice-range":
        reserved = base_reserved | frozenset({thm_name, f"{thm_name}_hyps", f"{thm_name}_cert", "rp", "hOff"})
        off_ast = _parse_expr_str(offset_expr, "nat", reserved=reserved)
        len_ast = _parse_expr_str(len_expr, "nat", reserved=reserved)
        tot_ast = _parse_expr_str(total_expr, "nat", reserved=reserved)
        gl_le = ("add", off_ast, len_ast)
        _walk_ast(gl_le, "nat", caps=True)
        parsed = [iq for hs in hyp_strings for iq in parse_inequalities(hs, "nat", reserved=reserved)]
        le_hyps_full = [(*_ast_to_le(l, op, r), l, op, r) for l, op, r in parsed]
        le_hyps_ast = [(la, ra) for la, ra, *_ in le_hyps_full]
        vars_ = _collect_vars(
            [off_ast, len_ast, tot_ast, *[x for pair in le_hyps_ast for x in pair]], "nat"
        )
        vidx = {nm: i for i, nm in enumerate(vars_)}
        steps = _solve_fixed_goal("nat", le_hyps_ast, gl_le, tot_ast, vidx, max_nodes)
        if steps is None:
            return {
                "solved": False, "mode": "mir-bounds", "preset": preset, "domain": "nat",
                "variables": vars_,
                "error": f"No Farkas/Chvatal-Gomory refutation found within max_nodes={max_nodes}.",
            }
        rp_ast = lambda n: _render_pair(n, vidx, "nat", ascii_lean=ascii_lean)[0]  # noqa: E731
        off_s = _render_pair(off_ast, vidx, "nat", ascii_lean=ascii_lean)[1]
        len_arg = _render_pair(len_ast, vidx, "nat", min_prec=100, ascii_lean=ascii_lean)[1]
        len_rhs = _render_pair(len_ast, vidx, "nat", min_prec=66, ascii_lean=ascii_lean)[1]
        tot_arg = _render_pair(tot_ast, vidx, "nat", min_prec=100, ascii_lean=ascii_lean)[1]
        hyp_lits = ", ".join(
            _format_ineq_pair(rp_ast(la), rp_ast(ra), ascii_lean=ascii_lean) for la, ra in le_hyps_ast
        )
        v_bind = f"({' '.join(vars_)} : Nat) " if vars_ else ""
        h_bind = "".join(
            f" (h{i} : {_format_nat_prop_rel(lo, op, ro, sym, vidx, ascii_lean=ascii_lean)})"
            for i, (_, _, sym, lo, op, ro) in enumerate(le_hyps_full)
        )
        p_args = "".join(f" h{i}" for i in range(len(le_hyps_full)))
        snippet = (
            f"{_mir_header()}"
            f"private def {thm_name}_hyps : List NatCutIneq :=\n  [{hyp_lits}]\n\n"
            f"private def {thm_name}_cert : List CutStep :=\n  [{_format_steps(steps)}]\n\n"
            f"private theorem {thm_name} {v_bind}(rp : RawPtrVal) (hOff : rp.offset = {off_s}){h_bind} :\n"
            f"    ValidSliceRange rp {len_arg} {tot_arg} {conj}\n"
            f"    evalPtrOffset rp {len_arg} {tot_arg} =\n"
            f"      some {{ rp with offset := rp.offset + {len_rhs} }} :=\n"
            f"  farkas_discharges_slice_bounds {thm_name}_hyps\n"
            f"    ({rp_ast(off_ast)}) ({rp_ast(len_ast)}) ({rp_ast(tot_ast)})\n"
            f"    {thm_name}_cert rfl [{', '.join(vars_)}] rp hOff{p_args}"
        )
        return {
            "solved": True, "mode": "mir-bounds", "preset": preset, "domain": "nat",
            "variables": vars_, "steps": steps, "lean_snippet": snippet,
        }

    if preset == "aligned-stride":
        if align < 1 or align > _MAG_CAP_128:
            raise ParseError("`--align` must satisfy `1 <= align <= 2^128`.")
        reserved = base_reserved | frozenset({
            thm_name, f"{thm_name}_hyps", f"{thm_name}_cert_le", f"{thm_name}_cert_ge", "rp", "hOff"
        })
        off_ast = _parse_expr_str(offset_expr, "nat", reserved=reserved)
        quot_ast = _parse_expr_str(quot_expr, "nat", reserved=reserved)
        scaled_ast = ("mulC", align, quot_ast)
        _walk_ast(scaled_ast, "nat", caps=True)
        parsed = [iq for hs in hyp_strings for iq in parse_inequalities(hs, "nat", reserved=reserved)]
        le_hyps_full = [(*_ast_to_le(l, op, r), l, op, r) for l, op, r in parsed]
        le_hyps_ast = [(la, ra) for la, ra, *_ in le_hyps_full]
        vars_ = _collect_vars(
            [off_ast, quot_ast, *[x for pair in le_hyps_ast for x in pair]], "nat"
        )
        vidx = {nm: i for i, nm in enumerate(vars_)}
        steps_le = _solve_fixed_goal("nat", le_hyps_ast, scaled_ast, off_ast, vidx, max_nodes)
        steps_ge = (
            _solve_fixed_goal("nat", le_hyps_ast, off_ast, scaled_ast, vidx, max_nodes)
            if steps_le is not None else None
        )
        if steps_le is None or steps_ge is None:
            which = "lower (`align * quot <= off`)" if steps_le is None else "upper (`off <= align * quot`)"
            return {
                "solved": False, "mode": "mir-bounds", "preset": preset, "domain": "nat",
                "align": align, "variables": vars_,
                "error": f"No Farkas/Chvatal-Gomory refutation found for {which} within max_nodes={max_nodes}.",
            }
        rp_ast = lambda n: _render_pair(n, vidx, "nat", ascii_lean=ascii_lean)[0]  # noqa: E731
        off_s = _render_pair(off_ast, vidx, "nat", ascii_lean=ascii_lean)[1]
        hyp_lits = ", ".join(
            _format_ineq_pair(rp_ast(la), rp_ast(ra), ascii_lean=ascii_lean) for la, ra in le_hyps_ast
        )
        v_bind = f"({' '.join(vars_)} : Nat) " if vars_ else ""
        h_bind = "".join(
            f" (h{i} : {_format_nat_prop_rel(lo, op, ro, sym, vidx, ascii_lean=ascii_lean)})"
            for i, (_, _, sym, lo, op, ro) in enumerate(le_hyps_full)
        )
        p_args = "".join(f" h{i}" for i in range(len(le_hyps_full)))
        snippet = (
            f"{_mir_header()}"
            f"private def {thm_name}_hyps : List NatCutIneq :=\n  [{hyp_lits}]\n\n"
            f"private def {thm_name}_cert_le : List CutStep :=\n  [{_format_steps(steps_le)}]\n\n"
            f"private def {thm_name}_cert_ge : List CutStep :=\n  [{_format_steps(steps_ge)}]\n\n"
            f"private theorem {thm_name} {v_bind}(rp : RawPtrVal) (hOff : rp.offset = {off_s}){h_bind} :\n"
            f"    AlignedPtr rp {align} :=\n"
            f"  farkas_discharges_aligned_stride {thm_name}_hyps {align}\n"
            f"    ({rp_ast(off_ast)}) ({rp_ast(quot_ast)})\n"
            f"    {thm_name}_cert_le {thm_name}_cert_ge rfl rfl rfl [{', '.join(vars_)}] rp hOff{p_args}"
        )
        return {
            "solved": True, "mode": "mir-bounds", "preset": preset, "domain": "nat",
            "align": align, "variables": vars_,
            "steps_le": steps_le, "steps_ge": steps_ge, "lean_snippet": snippet,
        }

    if preset == "uint-add-no-overflow":
        if width not in _SUPPORTED_WIDTHS:
            raise ParseError(f"Unsupported `--width {width}`; expected one of 8, 16, 32, 64, 128.")
        reserved = base_reserved | frozenset({thm_name, f"{thm_name}_hyps", f"{thm_name}_cert", "locals", "mem"})
        lhs_ast = _parse_expr_str(lhs_expr, "nat", reserved=reserved)
        rhs_ast = _parse_expr_str(rhs_expr, "nat", reserved=reserved)
        sum_ast = ("add", lhs_ast, rhs_ast)
        gl_le = ("add", sum_ast, ("cst", 1))
        gr_le = ("cst", 1 << width)
        _walk_ast(gl_le, "nat", caps=True)
        _walk_ast(gr_le, "nat", caps=True)
        parsed = [iq for hs in hyp_strings for iq in parse_inequalities(hs, "nat", reserved=reserved)]
        le_hyps_full = [(*_ast_to_le(l, op, r), l, op, r) for l, op, r in parsed]
        le_hyps_ast = [(la, ra) for la, ra, *_ in le_hyps_full]
        vars_ = _collect_vars(
            [lhs_ast, rhs_ast, *[x for pair in le_hyps_ast for x in pair]], "nat"
        )
        vidx = {nm: i for i, nm in enumerate(vars_)}
        steps = _solve_fixed_goal("nat", le_hyps_ast, gl_le, gr_le, vidx, max_nodes)
        if steps is None:
            return {
                "solved": False, "mode": "mir-bounds", "preset": preset, "domain": "nat",
                "width": width, "variables": vars_,
                "error": f"No Farkas/Chvatal-Gomory refutation found within max_nodes={max_nodes}.",
            }
        rp_ast = lambda n: _render_pair(n, vidx, "nat", ascii_lean=ascii_lean)[0]  # noqa: E731
        lhs_s = _render_pair(lhs_ast, vidx, "nat", min_prec=65, ascii_lean=ascii_lean)[1]
        rhs_s = _render_pair(rhs_ast, vidx, "nat", min_prec=66, ascii_lean=ascii_lean)[1]
        lhs_raw = _render_pair(lhs_ast, vidx, "nat", ascii_lean=ascii_lean)[1]
        rhs_raw = _render_pair(rhs_ast, vidx, "nat", ascii_lean=ascii_lean)[1]
        sum_s = f"{lhs_s} + {rhs_s}"
        uty = f".u{width}"
        hyp_lits = ", ".join(
            _format_ineq_pair(rp_ast(la), rp_ast(ra), ascii_lean=ascii_lean) for la, ra in le_hyps_ast
        )
        v_bind = f"({' '.join(vars_)} : Nat) " if vars_ else ""
        h_bind = "".join(
            f" (h{i} : {_format_nat_prop_rel(lo, op, ro, sym, vidx, ascii_lean=ascii_lean)})"
            for i, (_, _, sym, lo, op, ro) in enumerate(le_hyps_full)
        )
        p_args = "".join(f" h{i}" for i in range(len(le_hyps_full)))
        sc_l = _format_scalar(lhs_raw, f"uintBytes {uty}", ascii_lean=ascii_lean)
        sc_r = _format_scalar(rhs_raw, f"uintBytes {uty}", ascii_lean=ascii_lean)
        sc_sum = _format_scalar(sum_s, f"uintBytes {uty}", ascii_lean=ascii_lean)
        sc_z = _format_scalar("0", "1", ascii_lean=ascii_lean)
        call = (
            f"farkas_discharges_u64_add_no_overflow {thm_name}_hyps"
            if width == 64
            else f"farkas_discharges_uint_add_no_overflow {uty} {thm_name}_hyps"
        )
        snippet = (
            f"{_mir_header()}"
            f"private def {thm_name}_hyps : List NatCutIneq :=\n  [{hyp_lits}]\n\n"
            f"private def {thm_name}_cert : List CutStep :=\n  [{_format_steps(steps)}]\n\n"
            f"private theorem {thm_name} {v_bind}(locals : List LocalSlot) (mem : Memory){h_bind} :\n"
            f"    {sum_s} < modPow2 (uintWidth {uty}) {conj}\n"
            f"    {sum_s} < scalarModulus (uintBytes {uty}) {conj}\n"
            f"    evalScalarBinOp .addUnchecked {sc_l} {sc_r} locals mem false =\n"
            f"      .ok (.scalar {sc_sum}) locals mem {conj}\n"
            f"    evalScalarBinOp .addWithOverflow {sc_l} {sc_r} locals mem false =\n"
            f"      .ok (.aggregate 0 [.scalar {sc_sum}, .scalar {sc_z}]) locals mem :=\n"
            f"  {call}\n"
            f"    ({rp_ast(lhs_ast)}) ({rp_ast(rhs_ast)})\n"
            f"    {thm_name}_cert rfl [{', '.join(vars_)}] locals mem{p_args}"
        )
        return {
            "solved": True, "mode": "mir-bounds", "preset": preset, "domain": "nat",
            "width": width, "variables": vars_, "steps": steps, "lean_snippet": snippet,
        }

    if preset == "uint-sub-no-underflow":
        if width not in _SUPPORTED_WIDTHS:
            raise ParseError(f"Unsupported `--width {width}`; expected one of 8, 16, 32, 64, 128.")
        reserved = base_reserved | frozenset({
            thm_name, f"{thm_name}_hyps", f"{thm_name}_cert", f"{thm_name}_cert_range",
            "locals", "mem", "hRange"
        })
        lhs_ast = _parse_expr_str(lhs_expr, "nat", reserved=reserved)
        rhs_ast = _parse_expr_str(rhs_expr, "nat", reserved=reserved)
        parsed = [iq for hs in hyp_strings for iq in parse_inequalities(hs, "nat", reserved=reserved)]
        le_hyps_full = [(*_ast_to_le(l, op, r), l, op, r) for l, op, r in parsed]
        le_hyps_ast = [(la, ra) for la, ra, *_ in le_hyps_full]
        vars_ = _collect_vars(
            [lhs_ast, rhs_ast, *[x for pair in le_hyps_ast for x in pair]], "nat"
        )
        vidx = {nm: i for i, nm in enumerate(vars_)}
        steps = _solve_fixed_goal("nat", le_hyps_ast, rhs_ast, lhs_ast, vidx, max_nodes)
        if steps is None:
            return {
                "solved": False, "mode": "mir-bounds", "preset": preset, "domain": "nat",
                "width": width, "variables": vars_,
                "error": f"No Farkas/Chvatal-Gomory refutation found within max_nodes={max_nodes}.",
            }
        rp_ast = lambda n: _render_pair(n, vidx, "nat", ascii_lean=ascii_lean)[0]  # noqa: E731
        lhs_s = _render_pair(lhs_ast, vidx, "nat", min_prec=65, ascii_lean=ascii_lean)[1]
        rhs_s = _render_pair(rhs_ast, vidx, "nat", min_prec=66, ascii_lean=ascii_lean)[1]
        lhs_raw = _render_pair(lhs_ast, vidx, "nat", ascii_lean=ascii_lean)[1]
        rhs_raw = _render_pair(rhs_ast, vidx, "nat", ascii_lean=ascii_lean)[1]
        diff_s = f"{lhs_s} - {rhs_s}"
        uty = f".u{width}"
        hyp_lits = ", ".join(
            _format_ineq_pair(rp_ast(la), rp_ast(ra), ascii_lean=ascii_lean) for la, ra in le_hyps_ast
        )
        v_bind = f"({' '.join(vars_)} : Nat) " if vars_ else ""
        h_bind = "".join(
            f" (h{i} : {_format_nat_prop_rel(lo, op, ro, sym, vidx, ascii_lean=ascii_lean)})"
            for i, (_, _, sym, lo, op, ro) in enumerate(le_hyps_full)
        )
        p_args = "".join(f" h{i}" for i in range(len(le_hyps_full)))
        sc_l = _format_scalar(lhs_raw, f"uintBytes {uty}", ascii_lean=ascii_lean)
        sc_r = _format_scalar(rhs_raw, f"uintBytes {uty}", ascii_lean=ascii_lean)
        sc_diff = _format_scalar(diff_s, f"uintBytes {uty}", ascii_lean=ascii_lean)
        sc_z = _format_scalar("0", "1", ascii_lean=ascii_lean)
        # Try to also certify the operand range `lhs + 1 <= 2^width` from the same
        # hypotheses; when found, the emitted theorem needs no external `hRange`.
        try:
            steps_rng = _solve_fixed_goal(
                "nat", le_hyps_ast, ("add", lhs_ast, ("cst", 1)), ("cst", 1 << width),
                vidx, max_nodes,
            )
        except ParseError:
            steps_rng = None
        concl = (
            f"    {rhs_raw} {le_sym} {lhs_raw} {conj}\n"
            f"    {diff_s} < modPow2 (uintWidth {uty}) {conj}\n"
            f"    evalScalarBinOp .subUnchecked {sc_l} {sc_r} locals mem false =\n"
            f"      .ok (.scalar {sc_diff}) locals mem {conj}\n"
            f"    evalScalarBinOp .subWithOverflow {sc_l} {sc_r} locals mem false =\n"
            f"      .ok (.aggregate 0 [.scalar {sc_diff}, .scalar {sc_z}]) locals mem :=\n"
        )
        if steps_rng is not None:
            snippet = (
                f"{_mir_header()}"
                f"private def {thm_name}_hyps : List NatCutIneq :=\n  [{hyp_lits}]\n\n"
                f"private def {thm_name}_cert : List CutStep :=\n  [{_format_steps(steps)}]\n\n"
                f"private def {thm_name}_cert_range : List CutStep :=\n  [{_format_steps(steps_rng)}]\n\n"
                f"private theorem {thm_name} {v_bind}(locals : List LocalSlot) (mem : Memory){h_bind} :\n"
                f"    {lhs_raw} < modPow2 (uintWidth {uty}) {conj}\n"
                f"{concl}"
                f"  farkas_discharges_uint_sub_no_underflow_certified {uty} {thm_name}_hyps\n"
                f"    ({rp_ast(lhs_ast)}) ({rp_ast(rhs_ast)})\n"
                f"    {thm_name}_cert {thm_name}_cert_range rfl rfl [{', '.join(vars_)}] locals mem{p_args}"
            )
            return {
                "solved": True, "mode": "mir-bounds", "preset": preset, "domain": "nat",
                "width": width, "variables": vars_, "steps": steps,
                "range_certified": True, "steps_range": steps_rng, "lean_snippet": snippet,
            }
        snippet = (
            f"{_mir_header()}"
            f"private def {thm_name}_hyps : List NatCutIneq :=\n  [{hyp_lits}]\n\n"
            f"private def {thm_name}_cert : List CutStep :=\n  [{_format_steps(steps)}]\n\n"
            f"private theorem {thm_name} {v_bind}(locals : List LocalSlot) (mem : Memory)\n"
            f"    (hRange : {lhs_raw} < modPow2 (uintWidth {uty})){h_bind} :\n"
            f"{concl}"
            f"  farkas_discharges_uint_sub_no_underflow {uty} {thm_name}_hyps\n"
            f"    ({rp_ast(lhs_ast)}) ({rp_ast(rhs_ast)})\n"
            f"    {thm_name}_cert rfl [{', '.join(vars_)}] locals mem hRange{p_args}"
        )
        return {
            "solved": True, "mode": "mir-bounds", "preset": preset, "domain": "nat",
            "width": width, "variables": vars_, "steps": steps,
            "range_certified": False, "lean_snippet": snippet,
        }

    if preset == "aipcc-interval-refine":
        if width not in _SUPPORTED_WIDTHS:
            raise ParseError(f"Unsupported `--width {width}`; expected one of 8, 16, 32, 64, 128.")
        if target_lo is None or target_hi is None:
            raise ParseError("`aipcc-interval-refine` requires both `--target-lo` and `--target-hi`.")
        modulus = 1 << width
        if target_lo < 0 or target_hi < target_lo or target_hi >= modulus:
            raise ParseError(
                f"Target interval [{target_lo}, {target_hi}] must satisfy 0 <= lo <= hi < 2^{width}."
            )
        if (src_lo is None) != (src_hi is None):
            raise ParseError("Specify both `--src-lo` and `--src-hi` together, or omit both.")
        has_src = src_lo is not None and src_hi is not None
        if has_src:
            assert src_lo is not None and src_hi is not None
            if src_lo < 0 or src_hi < src_lo or src_hi >= modulus:
                raise ParseError(
                    f"Source interval [{src_lo}, {src_hi}] must satisfy 0 <= lo <= hi < 2^{width}."
                )
        reserved = base_reserved | frozenset({
            thm_name, f"{thm_name}_hyps", f"{thm_name}_cert_lo", f"{thm_name}_cert_hi", "hSrc"
        })
        x_ast = _parse_expr_str(var_name, "nat", reserved=reserved)
        if x_ast[0] != "var":
            raise ParseError(f"`--var` must be a single Lean variable identifier, got `{var_name}`.")
        user_parsed = [iq for hs in hyp_strings for iq in parse_inequalities(hs, "nat", reserved=reserved)]
        user_le_full = [(*_ast_to_le(l, op, r), l, op, r) for l, op, r in user_parsed]
        src_le_ast: list[tuple[Any, Any]] = []
        if has_src:
            assert src_lo is not None and src_hi is not None
            src_le_ast = [(("cst", src_lo), x_ast), (x_ast, ("cst", src_hi))]
        le_hyps_ast = [*src_le_ast, *[(la, ra) for la, ra, *_ in user_le_full]]
        vars_ = _collect_vars([x_ast, *[x for pair in le_hyps_ast for x in pair]], "nat")
        vidx = {nm: i for i, nm in enumerate(vars_)}
        steps_lo = _solve_fixed_goal("nat", le_hyps_ast, ("cst", target_lo), x_ast, vidx, max_nodes)
        steps_hi = (
            _solve_fixed_goal("nat", le_hyps_ast, x_ast, ("cst", target_hi), vidx, max_nodes)
            if steps_lo is not None else None
        )
        if steps_lo is None or steps_hi is None:
            which = f"lower (`{target_lo} <= {var_name}`)" if steps_lo is None else f"upper (`{var_name} <= {target_hi}`)"
            return {
                "solved": False, "mode": "mir-bounds", "preset": preset, "domain": "nat",
                "width": width, "target_lo": target_lo, "target_hi": target_hi, "variables": vars_,
                "error": f"No Farkas/Chvatal-Gomory refutation found for {which} within max_nodes={max_nodes}.",
            }
        rp_ast = lambda n: _render_pair(n, vidx, "nat", ascii_lean=ascii_lean)[0]  # noqa: E731
        uty = f".u{width}"
        hyp_lits = ", ".join(
            _format_ineq_pair(rp_ast(la), rp_ast(ra), ascii_lean=ascii_lean) for la, ra in le_hyps_ast
        )
        v_bind = f"({' '.join(vars_)} : Nat)"
        src_bind = (
            f" (hSrc : WrappedInterval.denote (modPow2 (uintWidth {uty})) (.iv {src_lo} {src_hi}) {x_ast[1]})"
            if has_src else ""
        )
        h_bind = "".join(
            f" (h{i} : {_format_nat_prop_rel(lo, op, ro, sym, vidx, ascii_lean=ascii_lean)})"
            for i, (_, _, sym, lo, op, ro) in enumerate(user_le_full)
        )
        src_args = (
            " (wrappedInterval_denote_bounds rfl hSrc).1 (wrappedInterval_denote_bounds rfl hSrc).2.1"
            if has_src else ""
        )
        p_args = src_args + "".join(f" h{i}" for i in range(len(user_le_full)))
        snippet = (
            f"{_mir_header()}"
            f"private def {thm_name}_hyps : List NatCutIneq :=\n  [{hyp_lits}]\n\n"
            f"private def {thm_name}_cert_lo : List CutStep :=\n  [{_format_steps(steps_lo)}]\n\n"
            f"private def {thm_name}_cert_hi : List CutStep :=\n  [{_format_steps(steps_hi)}]\n\n"
            f"private theorem {thm_name} {v_bind}{src_bind}{h_bind} :\n"
            f"    WrappedInterval.denote (modPow2 (uintWidth {uty})) (.iv {target_lo} {target_hi}) {x_ast[1]} :=\n"
            f"  farkas_discharges_aipcc_interval_refinement {thm_name}_hyps\n"
            f"    (modPow2 (uintWidth {uty})) {target_lo} {target_hi} ({rp_ast(x_ast)})\n"
            f"    {thm_name}_cert_lo {thm_name}_cert_hi rfl rfl rfl rfl [{', '.join(vars_)}]{p_args}"
        )
        out: dict[str, Any] = {
            "solved": True, "mode": "mir-bounds", "preset": preset, "domain": "nat",
            "width": width, "var": x_ast[1], "target_lo": target_lo, "target_hi": target_hi,
            "variables": vars_, "steps_lo": steps_lo, "steps_hi": steps_hi, "lean_snippet": snippet,
        }
        if has_src:
            out["src_lo"] = src_lo
            out["src_hi"] = src_hi
        return out

    if preset == "uint-mul-const-no-overflow":
        if width not in _SUPPORTED_WIDTHS:
            raise ParseError(f"Unsupported `--width {width}`; expected one of 8, 16, 32, 64, 128.")
        if scale < 0 or scale > _MAG_CAP_128:
            raise ParseError("`--scale` must satisfy `0 <= scale <= 2^128`.")
        if scale >= (1 << width):
            raise ParseError(
                f"`--scale {scale}` is not a valid `u{width}` operand (must be < 2^{width})."
            )
        reserved = base_reserved | frozenset({thm_name, f"{thm_name}_hyps", f"{thm_name}_cert", "locals", "mem"})
        x_ast = _parse_expr_str(var_name, "nat", reserved=reserved)
        prod_ast = ("mulC", scale, x_ast)
        gl_le = ("add", prod_ast, ("cst", 1))
        gr_le = ("cst", 1 << width)
        _walk_ast(gl_le, "nat", caps=True)
        parsed = [iq for hs in hyp_strings for iq in parse_inequalities(hs, "nat", reserved=reserved)]
        le_hyps_full = [(*_ast_to_le(l, op, r), l, op, r) for l, op, r in parsed]
        le_hyps_ast = [(la, ra) for la, ra, *_ in le_hyps_full]
        vars_ = _collect_vars([x_ast, *[x for pair in le_hyps_ast for x in pair]], "nat")
        vidx = {nm: i for i, nm in enumerate(vars_)}
        steps = _solve_fixed_goal("nat", le_hyps_ast, gl_le, gr_le, vidx, max_nodes)
        if steps is None:
            return {
                "solved": False, "mode": "mir-bounds", "preset": preset, "domain": "nat",
                "width": width, "scale": scale, "variables": vars_,
                "error": f"No Farkas/Chvatal-Gomory refutation found within max_nodes={max_nodes}.",
            }
        rp_ast = lambda n: _render_pair(n, vidx, "nat", ascii_lean=ascii_lean)[0]  # noqa: E731
        x_s = _render_pair(x_ast, vidx, "nat", min_prec=75, ascii_lean=ascii_lean)[1]
        x_raw = _render_pair(x_ast, vidx, "nat", ascii_lean=ascii_lean)[1]
        prod_s = f"{scale} * {x_s}"
        uty = f".u{width}"
        hyp_lits = ", ".join(
            _format_ineq_pair(rp_ast(la), rp_ast(ra), ascii_lean=ascii_lean) for la, ra in le_hyps_ast
        )
        v_bind = f"({' '.join(vars_)} : Nat) " if vars_ else ""
        h_bind = "".join(
            f" (h{i} : {_format_nat_prop_rel(lo, op, ro, sym, vidx, ascii_lean=ascii_lean)})"
            for i, (_, _, sym, lo, op, ro) in enumerate(le_hyps_full)
        )
        p_args = "".join(f" h{i}" for i in range(len(le_hyps_full)))
        sc_k = _format_scalar(str(scale), f"uintBytes {uty}", ascii_lean=ascii_lean)
        sc_x = _format_scalar(x_raw, f"uintBytes {uty}", ascii_lean=ascii_lean)
        sc_p = _format_scalar(prod_s, f"uintBytes {uty}", ascii_lean=ascii_lean)
        sc_z = _format_scalar("0", "1", ascii_lean=ascii_lean)
        snippet = (
            f"{_mir_header()}"
            f"private def {thm_name}_hyps : List NatCutIneq :=\n  [{hyp_lits}]\n\n"
            f"private def {thm_name}_cert : List CutStep :=\n  [{_format_steps(steps)}]\n\n"
            f"private theorem {thm_name} {v_bind}(locals : List LocalSlot) (mem : Memory){h_bind} :\n"
            f"    UintScalarInRange {uty} {sc_k} {conj}\n"
            f"    {prod_s} < modPow2 (uintWidth {uty}) {conj}\n"
            f"    {prod_s} < scalarModulus (uintBytes {uty}) {conj}\n"
            f"    evalScalarBinOp .mulUnchecked {sc_k} {sc_x} locals mem false =\n"
            f"      .ok (.scalar {sc_p}) locals mem {conj}\n"
            f"    evalScalarBinOp .mulWithOverflow {sc_k} {sc_x} locals mem false =\n"
            f"      .ok (.aggregate 0 [.scalar {sc_p}, .scalar {sc_z}]) locals mem :=\n"
            f"  farkas_discharges_uint_mul_const_no_overflow {uty} {thm_name}_hyps\n"
            f"    {scale} ({rp_ast(x_ast)}) {thm_name}_cert rfl rfl [{', '.join(vars_)}] locals mem{p_args}"
        )
        return {
            "solved": True, "mode": "mir-bounds", "preset": preset, "domain": "nat",
            "width": width, "scale": scale, "variables": vars_, "steps": steps, "lean_snippet": snippet,
        }

    # preset == "non-overlapping-ptrs"
    if direction not in ("src-before-dst", "dst-before-src"):
        raise ParseError(f"Unsupported `--direction`: `{direction}`")
    reserved = base_reserved | frozenset({
        thm_name, f"{thm_name}_hyps", f"{thm_name}_cert", "src", "dst", "hSrcOff", "hDstOff"
    })
    src_ast = _parse_expr_str(src_offset_expr, "nat", reserved=reserved)
    dst_ast = _parse_expr_str(dst_offset_expr, "nat", reserved=reserved)
    cnt_ast = _parse_expr_str(count_expr, "nat", reserved=reserved)
    parsed = [iq for hs in hyp_strings for iq in parse_inequalities(hs, "nat", reserved=reserved)]
    le_hyps_full = [(*_ast_to_le(l, op, r), l, op, r) for l, op, r in parsed]
    le_hyps_ast = [(la, ra) for la, ra, *_ in le_hyps_full]
    vars_ = _collect_vars(
        [src_ast, dst_ast, cnt_ast, *[x for pair in le_hyps_ast for x in pair]], "nat"
    )
    vidx = {nm: i for i, nm in enumerate(vars_)}
    gl_le = ("add", src_ast, cnt_ast) if direction == "src-before-dst" else ("add", dst_ast, cnt_ast)
    gr_le = dst_ast if direction == "src-before-dst" else src_ast
    _walk_ast(gl_le, "nat", caps=True)
    steps = _solve_fixed_goal("nat", le_hyps_ast, gl_le, gr_le, vidx, max_nodes)
    if steps is None:
        return {
            "solved": False, "mode": "mir-bounds", "preset": preset, "domain": "nat",
            "direction": direction, "variables": vars_,
            "error": f"No Farkas/Chvatal-Gomory refutation found within max_nodes={max_nodes}.",
        }
    rp_ast = lambda n: _render_pair(n, vidx, "nat", ascii_lean=ascii_lean)[0]  # noqa: E731
    src_s = _render_pair(src_ast, vidx, "nat", ascii_lean=ascii_lean)[1]
    dst_s = _render_pair(dst_ast, vidx, "nat", ascii_lean=ascii_lean)[1]
    cnt_arg = _render_pair(cnt_ast, vidx, "nat", min_prec=100, ascii_lean=ascii_lean)[1]
    dir_ctor = ".srcBeforeDst" if direction == "src-before-dst" else ".dstBeforeSrc"
    hyp_lits = ", ".join(
        _format_ineq_pair(rp_ast(la), rp_ast(ra), ascii_lean=ascii_lean) for la, ra in le_hyps_ast
    )
    v_bind = f"({' '.join(vars_)} : Nat) " if vars_ else ""
    h_bind = "".join(
        f" (h{i} : {_format_nat_prop_rel(lo, op, ro, sym, vidx, ascii_lean=ascii_lean)})"
        for i, (_, _, sym, lo, op, ro) in enumerate(le_hyps_full)
    )
    p_args = "".join(f" h{i}" for i in range(len(le_hyps_full)))
    snippet = (
        f"{_mir_header()}"
        f"private def {thm_name}_hyps : List NatCutIneq :=\n  [{hyp_lits}]\n\n"
        f"private def {thm_name}_cert : List CutStep :=\n  [{_format_steps(steps)}]\n\n"
        f"private theorem {thm_name} {v_bind}(src dst : RawPtrVal)\n"
        f"    (hSrcOff : src.offset = {src_s}) (hDstOff : dst.offset = {dst_s}){h_bind} :\n"
        f"    NonOverlappingPtrs src dst {cnt_arg} :=\n"
        f"  farkas_discharges_non_overlapping_ptrs {thm_name}_hyps\n"
        f"    ({rp_ast(src_ast)}) ({rp_ast(dst_ast)}) ({rp_ast(cnt_ast)}) {dir_ctor}\n"
        f"    {thm_name}_cert rfl [{', '.join(vars_)}] src dst hSrcOff hDstOff{p_args}"
    )
    return {
        "solved": True, "mode": "mir-bounds", "preset": preset, "domain": "nat",
        "direction": direction, "variables": vars_, "steps": steps, "lean_snippet": snippet,
    }


def generate_entailment_certificate(
    domain: str,
    pre_strings: list[str],
    obligation_strings: list[str],
    witness_str: str,
    *,
    strict_witness_str: str | None = None,
    check_equiv: bool = False,
    thm_name: str = "entailment_adequacy",
    max_nodes: int = 2500,
    ascii_lean: bool = False,
) -> dict[str, Any]:
    """Synthesize a reflective Entailment-Graph adequacy certificate."""
    _validate_common_args(thm_name, max_nodes)
    if thm_name in _ENTAILMENT_SNIPPET_RESERVED:
        raise ParseError(f"Unsupported or reserved Lean name: `{thm_name}`")
    if domain not in ("nat", "int"):
        raise ParseError(f"Unsupported `--domain`: `{domain}`")
    if not obligation_strings:
        raise ParseError("`--entailment-check` requires at least one `--obligation`.")
    if strict_witness_str is not None and check_equiv:
        raise ParseError("`--strict-witness` and `--check-equiv` are mutually exclusive.")
    reserved = _ENTAILMENT_SNIPPET_RESERVED | frozenset({
        thm_name, f"{thm_name}_pre", f"{thm_name}_obligation",
        f"{thm_name}_fwd_certs", f"{thm_name}_sat_witness", f"{thm_name}_mode",
    })
    pre_parsed = [iq for s in pre_strings for iq in parse_inequalities(s, domain, reserved=reserved)]
    obl_parsed = [iq for s in obligation_strings for iq in parse_inequalities(s, domain, reserved=reserved)]
    pre_le = [(_ast_to_le(l, op, r)[0], _ast_to_le(l, op, r)[1]) for l, op, r in pre_parsed]
    obl_le = [(_ast_to_le(l, op, r)[0], _ast_to_le(l, op, r)[1]) for l, op, r in obl_parsed]
    vars_ = _collect_vars(
        [node for pair in (*pre_le, *obl_le) for node in pair], domain
    )
    vidx = {nm: i for i, nm in enumerate(vars_)}

    # Validate non-vacuity satisfiability witness against every `pre` inequality.
    sat_env, sat_err = parse_witness(witness_str, vars_, domain)
    if sat_err is not None or sat_env is None:
        return {
            "solved": False, "mode": "entailment-check", "domain": domain,
            "variables": vars_, "error": sat_err or "Invalid satisfaction witness.",
        }
    sat_map = dict(zip(vars_, sat_env))
    for i, (la, ra) in enumerate(pre_le):
        lv, rv = _eval_ast_env(la, sat_map), _eval_ast_env(ra, sat_map)
        if lv > rv:
            return {
                "solved": False, "mode": "entailment-check", "domain": domain,
                "variables": vars_, "sat_witness": sat_map,
                "error": f"Satisfaction witness violates precondition inequality #{i} ({lv} > {rv}).",
            }

    # Validate strictness witness if provided.
    strict_env: list[int] | None = None
    strict_map: dict[str, int] | None = None
    if strict_witness_str is not None:
        strict_env, st_err = parse_witness(strict_witness_str, vars_, domain)
        if st_err is not None or strict_env is None:
            return {
                "solved": False, "mode": "entailment-check", "domain": domain,
                "variables": vars_, "error": st_err or "Invalid strictness witness.",
            }
        strict_map = dict(zip(vars_, strict_env))
        for j, (la, ra) in enumerate(obl_le):
            lv, rv = _eval_ast_env(la, strict_map), _eval_ast_env(ra, strict_map)
            if lv > rv:
                return {
                    "solved": False, "mode": "entailment-check", "domain": domain,
                    "variables": vars_, "strict_witness": strict_map,
                    "error": f"Strictness witness violates obligation inequality #{j} ({lv} > {rv}).",
                }
        if not any(_eval_ast_env(la, strict_map) > _eval_ast_env(ra, strict_map) for la, ra in pre_le):
            return {
                "solved": False, "mode": "entailment-check", "domain": domain,
                "variables": vars_, "strict_witness": strict_map,
                "error": "Strictness witness satisfies precondition (does not witness strict strengthening).",
            }

    # Synthesize forward entailment certificates sharing one unified `vidx` and `pre_le`.
    fwd_certs: list[list[dict[str, Any]]] = []
    for j, (gl, gr) in enumerate(obl_le):
        cert = _solve_fixed_goal(domain, pre_le, gl, gr, vidx, max_nodes)
        if cert is None:
            return {
                "solved": False, "mode": "entailment-check", "domain": domain,
                "variables": vars_, "failed_obligation_index": j,
                "error": f"Precondition does not entail obligation inequality #{j} within max_nodes={max_nodes}.",
            }
        fwd_certs.append(cert)

    # Synthesize reverse entailment certificates if `--check-equiv`.
    rev_certs: list[list[dict[str, Any]]] | None = None
    if check_equiv:
        rev_certs = []
        for i, (gl, gr) in enumerate(pre_le):
            cert = _solve_fixed_goal(domain, obl_le, gl, gr, vidx, max_nodes)
            if cert is None:
                return {
                    "solved": False, "mode": "entailment-check", "domain": domain,
                    "variables": vars_, "failed_pre_index": i,
                    "error": f"Obligation does not entail precondition inequality #{i} within max_nodes={max_nodes}.",
                }
            rev_certs.append(cert)

    rp_ast = lambda n: _render_pair(n, vidx, domain, ascii_lean=ascii_lean)[0]  # noqa: E731
    pre_lits = ", ".join(
        _format_ineq_pair(rp_ast(la), rp_ast(ra), ascii_lean=ascii_lean) for la, ra in pre_le
    )
    obl_lits = ", ".join(
        _format_ineq_pair(rp_ast(la), rp_ast(ra), ascii_lean=ascii_lean) for la, ra in obl_le
    )
    fwd_lits = ", ".join(f"[{_format_steps(c)}]" for c in fwd_certs)

    def fmt_env(env: list[int]) -> str:
        return ", ".join(str(v) if domain == "nat" else _render_int_val(v) for v in env)

    if domain == "nat":
        spec_ty, v_ty, mode_ty = "NatLinSpec", "Nat", "NatAdequacyMode"
        prop_ty, thm_ref = "NatEntailmentAdequacyProp", "farkas_entailment_adequacy_cert"
    else:
        spec_ty, v_ty, mode_ty = "IntLinSpec", "Int", "IntAdequacyMode"
        prop_ty, thm_ref = "IntEntailmentAdequacyProp", "farkas_int_entailment_adequacy_cert"

    if strict_env is not None:
        adequacy_mode = "strict"
        mode_expr = f".strict [{fmt_env(strict_env)}]"
    elif rev_certs is not None:
        adequacy_mode = "equiv"
        rev_lits = ", ".join(f"[{_format_steps(c)}]" for c in rev_certs)
        mode_expr = f".equiv [{rev_lits}]"
    else:
        adequacy_mode = "sufficient_only"
        mode_expr = ".sufficientOnly"

    snippet = (
        f"{_mir_header()}"
        f"private def {thm_name}_pre : {spec_ty} :=\n  [{pre_lits}]\n\n"
        f"private def {thm_name}_obligation : {spec_ty} :=\n  [{obl_lits}]\n\n"
        f"private def {thm_name}_fwd_certs : List (List CutStep) :=\n  [{fwd_lits}]\n\n"
        f"private def {thm_name}_sat_witness : List {v_ty} :=\n  [{fmt_env(sat_env)}]\n\n"
        f"private def {thm_name}_mode : {mode_ty} :=\n  {mode_expr}\n\n"
        f"private theorem {thm_name} :\n"
        f"    {prop_ty} {thm_name}_pre {thm_name}_obligation {thm_name}_mode :=\n"
        f"  {thm_ref} {thm_name}_pre {thm_name}_obligation\n"
        f"    {thm_name}_fwd_certs {thm_name}_sat_witness {thm_name}_mode rfl"
    )
    res: dict[str, Any] = {
        "solved": True,
        "mode": "entailment-check",
        "domain": domain,
        "adequacy_mode": adequacy_mode,
        "variables": vars_,
        "sat_witness": sat_map,
        "fwd_certs": fwd_certs,
        "lean_snippet": snippet,
    }
    if strict_map is not None:
        res["strict_witness"] = strict_map
    if rev_certs is not None:
        res["rev_certs"] = rev_certs
    return res


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description=__doc__, allow_abbrev=False)
    p.add_argument("--domain", choices=("nat", "int"), default="nat")
    p.add_argument("--hyp", action="append", default=[], dest="hyps")
    p.add_argument("--goal", default=None)
    p.add_argument("--name", default="linear_bound")
    p.add_argument("--max-nodes", type=int, default=2500)
    p.add_argument("--json", action="store_true")
    p.add_argument("--mir-bounds", choices=_MIR_BOUNDS_PRESETS, default=None)
    p.add_argument("--width", type=int, default=64)
    p.add_argument("--align", type=int, default=8)
    p.add_argument("--scale", type=int, default=1)
    p.add_argument("--offset-expr", default="off")
    p.add_argument("--len-expr", default="len")
    p.add_argument("--total-expr", default="total")
    p.add_argument("--quot-expr", default="q")
    p.add_argument("--lhs-expr", default="a")
    p.add_argument("--rhs-expr", default="b")
    p.add_argument("--var", default="x")
    p.add_argument("--target-lo", type=int, default=None)
    p.add_argument("--target-hi", type=int, default=None)
    p.add_argument("--src-lo", type=int, default=None)
    p.add_argument("--src-hi", type=int, default=None)
    p.add_argument("--src-offset-expr", default="src_off")
    p.add_argument("--dst-offset-expr", default="dst_off")
    p.add_argument("--count-expr", default="count")
    p.add_argument("--direction", choices=("src-before-dst", "dst-before-src"), default="src-before-dst")
    p.add_argument("--entailment-check", action="store_true")
    p.add_argument("--pre", action="append", default=[], dest="pres")
    p.add_argument("--obligation", action="append", default=[], dest="obligations")
    p.add_argument("--witness", default=None)
    p.add_argument("--strict-witness", default=None)
    p.add_argument("--check-equiv", action="store_true")
    raw = sys.argv[1:] if argv is None else list(argv)
    stops = {
        "-h", "--help", "--domain", "--hyp", "--goal", "--name", "--max-nodes", "--json",
        "--mir-bounds", "--width", "--align", "--scale", "--offset-expr", "--len-expr",
        "--total-expr", "--quot-expr", "--lhs-expr", "--rhs-expr", "--var",
        "--target-lo", "--target-hi", "--src-lo", "--src-hi",
        "--src-offset-expr", "--dst-offset-expr", "--count-expr", "--direction",
        "--entailment-check", "--pre", "--obligation", "--witness", "--strict-witness",
        "--check-equiv", "--",
    }
    neg_flags = {
        "--hyp", "--goal", "--pre", "--obligation", "--witness", "--strict-witness",
        "--offset-expr", "--len-expr", "--total-expr", "--quot-expr",
        "--lhs-expr", "--rhs-expr", "--var", "--src-offset-expr",
        "--dst-offset-expr", "--count-expr",
    }
    norm, i = [], 0
    while i < len(raw):
        tok, nxt = raw[i], (raw[i + 1] if i + 1 < len(raw) else "")
        if tok == "--":
            norm.extend(raw[i:])
            break
        pair_neg = (tok in neg_flags and nxt.startswith("-")
                    and not nxt.startswith("--") and nxt not in stops)
        norm.append(f"{tok}={nxt}" if pair_neg else tok)
        i += 2 if pair_neg else 1
    ns, utf8_out = p.parse_args(norm), True
    try:
        "⟨≤∧".encode(getattr(sys.stdout, "encoding", None) or "utf-8")
    except (UnicodeEncodeError, LookupError):
        utf8_out = False

    def fail(rc: int, msg: Any) -> int:
        err = str(msg).encode("utf-8", "replace").decode("utf-8")
        out = json.dumps({"solved": False, "error": err}, indent=2, ensure_ascii=not utf8_out)
        print(out if ns.json else f"[ERROR] {err}", file=(sys.stdout if ns.json else sys.stderr))
        return rc

    try:
        for tok in raw:
            tok.encode("utf-8", errors="strict")
        ascii_lean = not ns.json and not utf8_out
        if ns.mir_bounds is not None and ns.entailment_check:
            raise ParseError("`--mir-bounds` and `--entailment-check` are mutually exclusive.")
        if ns.mir_bounds is not None:
            if ns.goal is not None:
                raise ParseError("`--goal` cannot be combined with `--mir-bounds`.")
            if ns.domain != "nat":
                raise ParseError("`--mir-bounds` presets require `--domain nat`.")
            if ns.pres or ns.obligations or ns.witness is not None or ns.strict_witness is not None or ns.check_equiv:
                raise ParseError("Entailment flags cannot be combined with `--mir-bounds`.")
            res = generate_mir_bounds_certificate(
                ns.mir_bounds, ns.hyps, ns.name, max_nodes=ns.max_nodes,
                width=ns.width, align=ns.align, scale=ns.scale,
                offset_expr=ns.offset_expr, len_expr=ns.len_expr,
                total_expr=ns.total_expr, quot_expr=ns.quot_expr,
                lhs_expr=ns.lhs_expr, rhs_expr=ns.rhs_expr, var_name=ns.var,
                target_lo=ns.target_lo, target_hi=ns.target_hi,
                src_lo=ns.src_lo, src_hi=ns.src_hi,
                src_offset_expr=ns.src_offset_expr, dst_offset_expr=ns.dst_offset_expr,
                count_expr=ns.count_expr, direction=ns.direction,
                ascii_lean=ascii_lean,
            )
        elif ns.entailment_check:
            if ns.goal is not None:
                raise ParseError("`--goal` cannot be combined with `--entailment-check`.")
            if ns.pres and ns.hyps:
                raise ParseError("Use either `--pre` or `--hyp` with `--entailment-check`, not both.")
            if ns.witness is None:
                raise ParseError("`--entailment-check` requires `--witness`.")
            pre_list = ns.pres if ns.pres else ns.hyps
            res = generate_entailment_certificate(
                ns.domain, pre_list, ns.obligations, ns.witness,
                strict_witness_str=ns.strict_witness, check_equiv=ns.check_equiv,
                thm_name=ns.name, max_nodes=ns.max_nodes, ascii_lean=ascii_lean,
            )
        else:
            if ns.pres or ns.obligations or ns.witness is not None or ns.strict_witness is not None or ns.check_equiv:
                raise ParseError("Entailment flags require `--entailment-check`.")
            if ns.goal is None:
                # Preserve baseline argparse semantics (`--goal` was `required=True`).
                p.error("the following arguments are required: --goal")
            res = generate_certificate(
                ns.domain, ns.hyps, ns.goal, ns.name,
                max_nodes=ns.max_nodes, ascii_lean=ascii_lean,
            )
    except Exception as exc:
        return fail(2, exc)
    if ns.json:
        print(json.dumps(res, indent=2, ensure_ascii=not utf8_out))
        return 0 if res["solved"] else 1
    return (print(res["lean_snippet"]) or 0) if res["solved"] else fail(1, res["error"])


if __name__ == "__main__":
    sys.exit(main())
