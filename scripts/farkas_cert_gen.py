#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.
"""Synthesizes verified Pass-1 `Workbench.Pass1.LinearArith` certificates (replacing `omega`)."""

from __future__ import annotations

import argparse
from collections import deque
from functools import reduce
import json
import math
import re
import sys
from typing import Any

TOKEN_RE = re.compile(r"\s*(<=|<|>=|>|==|=|\+|-|\*|\(|\)|[A-Za-z_][A-Za-z0-9_']*|\d+)")


class ParseError(ValueError):
    pass


def tokenize(text: str) -> list[str]:
    pos = 0
    tokens: list[str] = []
    while pos < len(text):
        if text[pos].isspace():
            pos += 1
            continue
        m = TOKEN_RE.match(text, pos)
        if not m:
            raise ParseError(f"Unexpected syntax at column {pos + 1} in `{text}`")
        tokens.append(m.group(1))
        pos = m.end()
    return tokens


class LinearFormParser:
    """Parses linear expressions into `{var_name: coeff}` + integer constant."""

    def __init__(self, tokens: list[str]) -> None:
        self.tokens = tokens
        self.idx = 0

    def peek(self) -> str | None:
        return self.tokens[self.idx] if self.idx < len(self.tokens) else None

    def consume(self, expected: str | None = None) -> str:
        tok = self.peek()
        if tok is None:
            raise ParseError("Unexpected end of expression")
        if expected is not None and tok != expected:
            raise ParseError(f"Expected `{expected}`, got `{tok}`")
        self.idx += 1
        return tok

    def parse_expr(self) -> tuple[dict[str, int], int]:
        coeffs, cst = self.parse_term()
        while self.peek() in {"+", "-"}:
            op = self.consume()
            rc, rk = self.parse_term()
            sign = 1 if op == "+" else -1
            cst += sign * rk
            for v, k in rc.items():
                coeffs[v] = coeffs.get(v, 0) + sign * k
                if coeffs[v] == 0:
                    del coeffs[v]
        return coeffs, cst

    def parse_term(self) -> tuple[dict[str, int], int]:
        coeffs, cst = self.parse_unary()
        while self.peek() == "*":
            self.consume("*")
            rc, rk = self.parse_unary()
            if not coeffs:
                coeffs = {v: cst * k for v, k in rc.items() if cst * k != 0}
                cst = cst * rk
            elif not rc:
                coeffs = {v: k * rk for v, k in coeffs.items() if k * rk != 0}
                cst = cst * rk
            else:
                raise ParseError("Nonlinear variable*variable product is unsupported")
        return coeffs, cst

    def parse_unary(self) -> tuple[dict[str, int], int]:
        if self.peek() == "+":
            self.consume("+")
            return self.parse_unary()
        if self.peek() == "-":
            self.consume("-")
            c, k = self.parse_unary()
            return ({v: -val for v, val in c.items()}, -k)
        if self.peek() == "(":
            self.consume("(")
            res = self.parse_expr()
            self.consume(")")
            return res
        tok = self.consume()
        if tok.isdigit():
            return ({}, int(tok))
        if re.match(r"^[A-Za-z_][A-Za-z0-9_']*$", tok):
            return ({tok: 1}, 0)
        raise ParseError(f"Unexpected token `{tok}`")


def parse_inequalities(text: str) -> list[tuple[dict[str, int], int, dict[str, int], int]]:
    """Returns list of `(lhs_coeffs, lhs_const, rhs_coeffs, rhs_const)` for `lhs <= rhs`."""
    toks = tokenize(text)
    rel_ops = {"<=", "<", ">=", ">", "=", "=="}
    rel_positions = [i for i, t in enumerate(toks) if t in rel_ops]
    if len(rel_positions) != 1:
        raise ParseError(f"Expected exactly one relational operator in `{text}`")
    rpos = rel_positions[0]
    op = toks[rpos]
    lp = LinearFormParser(toks[:rpos])
    lc, lk = lp.parse_expr()
    if lp.peek() is not None:
        raise ParseError(f"Trailing token `{lp.peek()}` on LHS of `{text}`")
    rp = LinearFormParser(toks[rpos + 1 :])
    rc, rk = rp.parse_expr()
    if rp.peek() is not None:
        raise ParseError(f"Trailing token `{rp.peek()}` on RHS of `{text}`")

    if op == "<=":
        return [(lc, lk, rc, rk)]
    if op == "<":
        return [(lc, lk + 1, rc, rk)]
    if op == ">=":
        return [(rc, rk, lc, lk)]
    if op == ">":
        return [(rc, rk + 1, lc, lk)]
    # Equality `a = b` expands to `a <= b` and `b <= a`
    return [(lc, lk, rc, rk), (rc, rk, lc, lk)]


RowCoeffs = tuple[tuple[int, int], ...]


def normalize_to_sparse_le(
    lc: dict[str, int],
    lk: int,
    rc: dict[str, int],
    rk: int,
    var_index: dict[str, int],
) -> tuple[RowCoeffs, int]:
    """Normalizes `lhs <= rhs` into `sum(c_i * x_i) <= rhs_const`."""
    merged: dict[int, int] = {}
    for name, c in lc.items():
        idx = var_index[name]
        merged[idx] = merged.get(idx, 0) + c
    for name, c in rc.items():
        idx = var_index[name]
        merged[idx] = merged.get(idx, 0) - c
    terms = tuple(sorted((i, c) for i, c in merged.items() if c != 0))
    rhs = rk - lk
    return terms, rhs


def add_scaled_rows(
    t1: RowCoeffs, r1: int, k1: int, t2: RowCoeffs, r2: int, k2: int
) -> tuple[RowCoeffs, int]:
    merged: dict[int, int] = {}
    for i, c in t1:
        if k1 * c != 0:
            merged[i] = merged.get(i, 0) + k1 * c
    for i, c in t2:
        if k2 * c != 0:
            merged[i] = merged.get(i, 0) + k2 * c
    terms = tuple(sorted((i, c) for i, c in merged.items() if c != 0))
    return terms, k1 * r1 + k2 * r2


def maybe_div_cut(terms: RowCoeffs, rhs: int) -> tuple[int, RowCoeffs, int] | None:
    if not terms:
        return None
    g = reduce(math.gcd, (abs(c) for _, c in terms))
    if g <= 1:
        return None
    new_terms = tuple((i, c // g) for i, c in terms)
    # Exact floor division matching SInt.fdiv
    new_rhs = rhs // g
    return g, new_terms, new_rhs


def solve_cut_refutation(
    sparse_hyps: list[tuple[RowCoeffs, int]],
    max_nodes: int = 2500,
) -> list[dict[str, Any]] | None:
    """Searches Fourier-Motzkin + Chvatal-Gomory cuts for `0 <= -k` (`k >= 1`)."""
    # Each derived node stores: (terms, rhs, step_kind, args)
    nodes: list[tuple[RowCoeffs, int, str, tuple[int, ...]]] = []
    best_rhs: dict[RowCoeffs, tuple[int, int]] = {}  # terms -> (rhs, node_id)
    queue: deque[int] = deque()

    def register_node(terms: RowCoeffs, rhs: int, kind: str, args: tuple[int, ...]) -> int | None:
        prev = best_rhs.get(terms)
        if prev is not None and prev[0] <= rhs:
            return None
        nid = len(nodes)
        nodes.append((terms, rhs, kind, args))
        best_rhs[terms] = (rhs, nid)
        queue.append(nid)
        return nid

    def extract_steps(goal_nid: int) -> list[dict[str, Any]]:
        needed: set[int] = set()
        stack = [goal_nid]
        while stack:
            cur = stack.pop()
            if cur in needed:
                continue
            needed.add(cur)
            _, _, kind, args = nodes[cur]
            if kind == "comb":
                stack.extend([args[0], args[2]])
            elif kind == "divCut":
                stack.append(args[1])
        ordered = sorted(needed)
        remap: dict[int, int] = {}
        steps: list[dict[str, Any]] = []
        for out_idx, old_id in enumerate(ordered):
            remap[old_id] = out_idx
            _, _, kind, args = nodes[old_id]
            if kind == "hyp":
                steps.append({"op": "hyp", "idx": args[0]})
            elif kind == "comb":
                steps.append({
                    "op": "comb",
                    "s1": remap[args[0]],
                    "k1": args[1],
                    "s2": remap[args[2]],
                    "k2": args[3],
                })
            elif kind == "divCut":
                steps.append({
                    "op": "divCut",
                    "g": args[0],
                    "s": remap[args[1]],
                })
        return steps

    for h_idx, (terms, rhs) in enumerate(sparse_hyps):
        nid = register_node(terms, rhs, "hyp", (h_idx,))
        if nid is not None and not terms and rhs < 0:
            return extract_steps(nid)

    while queue and len(nodes) < max_nodes:
        nid = queue.popleft()
        terms, rhs, _, _ = nodes[nid]
        if not terms and rhs < 0:
            return extract_steps(nid)

        # 1. Try Chvatal-Gomory GCD floor cut on `nid`
        cut = maybe_div_cut(terms, rhs)
        if cut is not None:
            g, c_terms, c_rhs = cut
            cid = register_node(c_terms, c_rhs, "divCut", (g, nid))
            if cid is not None and not c_terms and c_rhs < 0:
                return extract_steps(cid)

        # 2. Fourier-Motzkin variable elimination against active best rows
        term_map = dict(terms)
        snapshot = list(best_rhs.values())
        for _, other_id in snapshot:
            if other_id == nid:
                continue
            o_terms, o_rhs, _, _ = nodes[other_id]
            for var_id, c1 in term_map.items():
                c2 = dict(o_terms).get(var_id, 0)
                if (c1 > 0 and c2 < 0) or (c1 < 0 and c2 > 0):
                    g = math.gcd(abs(c1), abs(c2))
                    k1 = abs(c2) // g
                    k2 = abs(c1) // g
                    comb_terms, comb_rhs = add_scaled_rows(terms, rhs, k1, o_terms, o_rhs, k2)
                    if len(comb_terms) <= max(len(terms), len(o_terms)) + 2:
                        cid = register_node(comb_terms, comb_rhs, "comb", (nid, k1, other_id, k2))
                        if cid is not None and not comb_terms and comb_rhs < 0:
                            return extract_steps(cid)
                    break
            if len(nodes) >= max_nodes:
                break

    return None


def verify_steps_exact(
    sparse_hyps: list[tuple[RowCoeffs, int]],
    steps: list[dict[str, Any]],
) -> bool:
    """Exact Python mirror of `Workbench.Pass1.LinearArith.checkCutRefute`."""
    cap = 1 << 128
    derived: list[tuple[RowCoeffs, int]] = []
    for st in steps:
        op = st["op"]
        if op == "hyp":
            idx = st["idx"]
            if idx < 0 or idx >= len(sparse_hyps):
                return False
            derived.append(sparse_hyps[idx])
        elif op == "comb":
            s1, k1, s2, k2 = st["s1"], st["k1"], st["s2"], st["k2"]
            if not (0 <= k1 <= cap and 0 <= k2 <= cap):
                return False
            if not (0 <= s1 < len(derived) and 0 <= s2 < len(derived)):
                return False
            t, r = add_scaled_rows(derived[s1][0], derived[s1][1], k1,
                                   derived[s2][0], derived[s2][1], k2)
            if abs(r) > cap:
                return False
            derived.append((t, r))
        elif op == "divCut":
            g, s = st["g"], st["s"]
            if not (1 <= g <= cap and 0 <= s < len(derived)):
                return False
            t0, r0 = derived[s]
            if any(abs(c) % g != 0 for _, c in t0):
                return False
            t = tuple((i, c // g) for i, c in t0 if (c // g) != 0)
            r = r0 // g
            if abs(r) > cap:
                return False
            derived.append((t, r))
        else:
            return False
    return bool(derived) and len(derived[-1][0]) == 0 and derived[-1][1] <= -1


def render_nat_expr(coeffs: dict[str, int], cst: int, var_index: dict[str, int]) -> str:
    parts: list[str] = []
    for name in sorted(coeffs, key=lambda n: var_index[n]):
        k = coeffs[name]
        if k < 0:
            raise ParseError(
                f"Negative coefficient `{k}*{name}` in `--domain nat`; "
                "move subtracted terms to the opposite side or use `--domain int`."
            )
        if k == 0:
            continue
        v_expr = f".var {var_index[name]}"
        parts.append(v_expr if k == 1 else f".mulC {k} ({v_expr})")
    if cst < 0:
        raise ParseError("Negative constant in `--domain nat`; move to opposite side or use `--domain int`.")
    if cst > 0 or not parts:
        parts.append(f".cst {cst}")
    acc = parts[0]
    for p in parts[1:]:
        acc = f".add ({acc}) ({p})"
    return acc


def sint_lit(val: int) -> str:
    return f"⟨{'true' if val < 0 else 'false'}, {abs(val)}⟩"


def render_int_expr(coeffs: dict[str, int], cst: int, var_index: dict[str, int]) -> str:
    parts: list[str] = []
    for name in sorted(coeffs, key=lambda n: var_index[n]):
        k = coeffs[name]
        if k == 0:
            continue
        v_expr = f".var {var_index[name]}"
        parts.append(v_expr if k == 1 else f".mulC {sint_lit(k)} ({v_expr})")
    if cst != 0 or not parts:
        parts.append(f".cst {sint_lit(cst)}")
    acc = parts[0]
    for p in parts[1:]:
        acc = f".add ({acc}) ({p})"
    return acc


def render_step(st: dict[str, Any]) -> str:
    if st["op"] == "hyp":
        return f".hyp {st['idx']}"
    if st["op"] == "comb":
        return f".comb {st['s1']} {st['k1']} {st['s2']} {st['k2']}"
    return f".divCut {st['g']} {st['s']}"


def generate_certificate(
    domain: str,
    hyp_strings: list[str],
    goal_string: str,
    thm_name: str = "linear_bound_verified",
) -> dict[str, Any]:
    parsed_hyps: list[tuple[dict[str, int], int, dict[str, int], int]] = []
    for hs in hyp_strings:
        parsed_hyps.extend(parse_inequalities(hs))
    parsed_goals = parse_inequalities(goal_string)
    if len(parsed_goals) != 1:
        raise ParseError("`--goal` must be a single inequality (`<=`, `<`, `>=`, or `>`).")
    glc, glk, grc, grk = parsed_goals[0]

    var_names: list[str] = []
    for lc, _, rc, _ in [*parsed_hyps, (glc, glk, grc, grk)]:
        for nm in (*lc.keys(), *rc.keys()):
            if nm not in var_names:
                var_names.append(nm)
    var_index = {nm: idx for idx, nm in enumerate(var_names)}

    # First try without implicit `0 <= v` hypotheses; if `--domain nat` needs
    # non-negativity of a variable, append `0 <= v` hypotheses cleanly.
    active_hyps = list(parsed_hyps)
    neg_concl = (grc, grk + 1, glc, glk)

    def build_sparse(hyps_list: list[tuple[dict[str, int], int, dict[str, int], int]]) -> list[tuple[RowCoeffs, int]]:
        return [
            normalize_to_sparse_le(lc, lk, rc, rk, var_index)
            for lc, lk, rc, rk in [*hyps_list, neg_concl]
        ]

    sparse_all = build_sparse(active_hyps)
    steps = solve_cut_refutation(sparse_all)
    added_nonneg_vars: list[str] = []
    if steps is None and domain == "nat":
        for nm in var_names:
            active_hyps.append(({}, 0, {nm: 1}, 0))
            added_nonneg_vars.append(nm)
        sparse_all = build_sparse(active_hyps)
        steps = solve_cut_refutation(sparse_all)

    if steps is None or not verify_steps_exact(sparse_all, steps):
        return {
            "solved": False,
            "domain": domain,
            "variables": var_names,
            "error": "No Farkas / Chvatal-Gomory refutation found (goal may be invalid or underconstrained).",
        }

    step_lits = ", ".join(render_step(s) for s in steps)
    if domain == "nat":
        hyp_lits = [
            f"⟨{render_nat_expr(lc, lk, var_index)}, {render_nat_expr(rc, rk, var_index)}⟩"
            for lc, lk, rc, rk in active_hyps
        ]
        concl_lit = f"⟨{render_nat_expr(glc, glk, var_index)}, {render_nat_expr(grc, grk, var_index)}⟩"
        goal_ty = "NatCutGoal"
        checker_thm = "checkNatCutGoal_sound"
        var_ty = "Nat"
        extra_zero_proofs = " ".join("(Nat.zero_le _)" for _ in added_nonneg_vars)
    else:
        hyp_lits = [
            f"⟨{render_int_expr(lc, lk, var_index)}, {render_int_expr(rc, rk, var_index)}⟩"
            for lc, lk, rc, rk in active_hyps
        ]
        concl_lit = f"⟨{render_int_expr(glc, glk, var_index)}, {render_int_expr(grc, grk, var_index)}⟩"
        goal_ty = "IntCutGoal"
        checker_thm = "checkIntCutGoal_sound"
        var_ty = "Int"
        extra_zero_proofs = ""

    hyp_binders = " ".join(f"(h{i} : _)" for i in range(len(parsed_hyps)))
    hyp_args = " ".join(f"h{i}" for i in range(len(parsed_hyps)))
    all_proof_args = " ".join(x for x in (hyp_args, extra_zero_proofs) if x)
    env_list = "[" + ", ".join(var_names) + "]"
    var_decl = f"({' '.join(var_names)} : {var_ty})" if var_names else ""

    hyps_formatted = "\n    , ".join(hyp_lits) if hyp_lits else ""
    hyps_list_code = f"[ {hyps_formatted} ]" if hyp_lits else "[]"

    lean_snippet = (
        f"def {thm_name}_goal : {goal_ty} :=\n"
        f"  {{ hyps := {hyps_list_code}\n"
        f"  , concl := {concl_lit} }}\n\n"
        f"def {thm_name}_cert : List CutStep :=\n"
        f"  [{step_lits}]\n\n"
        f"-- Proof term: {checker_thm} {thm_name}_goal {thm_name}_cert rfl "
        f"{env_list}{(' ' + all_proof_args) if all_proof_args else ''}\n"
        f"-- Variables ({var_ty}): {var_decl} {hyp_binders}"
    )

    return {
        "solved": True,
        "domain": domain,
        "variables": var_names,
        "implicit_nat_zero_le_vars": added_nonneg_vars,
        "steps": steps,
        "lean_snippet": lean_snippet,
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--domain", choices=["nat", "int"], default="nat",
                        help="Variable domain (`nat` or `int`; default: `nat`).")
    parser.add_argument("--hyp", action="append", default=[], dest="hyps",
                        help="Linear hypothesis inequality, e.g. `2*i + 1 <= 2*n` (repeatable).")
    parser.add_argument("--goal", required=True,
                        help="Target linear inequality, e.g. `i < n` or `i + 1 <= n`.")
    parser.add_argument("--name", default="linear_bound",
                        help="Base identifier for generated Lean snippet.")
    parser.add_argument("--json", action="store_true", help="Emit JSON output.")
    args = parser.parse_args(argv)

    try:
        res = generate_certificate(args.domain, args.hyps, args.goal, args.name)
    except ParseError as exc:
        if args.json:
            print(json.dumps({"solved": False, "error": str(exc)}, indent=2))
        else:
            print(f"[ERROR] {exc}", file=sys.stderr)
        return 2

    if args.json:
        print(json.dumps(res, indent=2))
    else:
        if not res["solved"]:
            print(f"[UNSOLVED] {res['error']}", file=sys.stderr)
            return 1
        print(res["lean_snippet"])
    return 0 if res["solved"] else 1


if __name__ == "__main__":
    sys.exit(main())
