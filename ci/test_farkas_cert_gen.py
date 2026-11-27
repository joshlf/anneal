# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Unit and live-Lean kernel tests for `ci/farkas_cert_gen.py`."""

from __future__ import annotations

import contextlib
import io
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

_CI_DIR = Path(__file__).resolve().parent
_ANNEAL_ROOT = _CI_DIR.parent
if str(_CI_DIR) not in sys.path:
    sys.path.insert(0, str(_CI_DIR))

from farkas_cert_gen import (  # noqa: E402
    _MAG_CAP_128,
    ParseError,
    generate_certificate,
    generate_entailment_certificate,
    generate_mir_bounds_certificate,
    main as cli_main,
    parse_inequalities,
    parse_witness,
)


def _scrubbed_env(extra: dict[str, str] | None = None) -> dict[str, str]:
    clean = {
        k: v for k, v in os.environ.items()
        if not k.startswith("ANNEAL_") and k != "CARGO_TARGET_DIR"
    }
    if extra:
        clean.update(extra)
    return clean


def _pinned_lean_version() -> str:
    raw = (_ANNEAL_ROOT / "lean-toolchain").read_text("utf-8").strip()
    return raw.split(":v", 1)[1] if ":v" in raw else raw.rsplit(":", 1)[-1]


def _verify_lean_version(cand: Path, expected_ver: str) -> bool:
    try:
        ver = subprocess.run([str(cand), "--version"], capture_output=True, text=True, timeout=5)
        pat = rf"\bversion\s+{re.escape(expected_ver)}(?:[^0-9A-Za-z._-]|$)"
        return ver.returncode == 0 and bool(re.search(pat, ver.stdout))
    except (OSError, subprocess.SubprocessError):
        return False


def _find_pinned_lean() -> Path | None:
    expected_ver = _pinned_lean_version()
    explicit = next(
        (v for k in ("ANNEAL_LEAN", "LEAN") if (v := os.environ.get(k, "").strip())),
        None,
    )
    if explicit:
        if not (p := Path(explicit).expanduser()).is_file():
            raise FileNotFoundError(f"Configured Lean binary not found: {p}")
        if not _verify_lean_version(res := p.resolve(), expected_ver):
            raise RuntimeError(f"Configured Lean binary is not v{expected_ver}: {res}")
        return res
    home = Path.home()
    xdg = os.environ.get("XDG_CACHE_HOME", "").strip()
    cache = (Path(xdg).expanduser() if xdg else home / ".cache") / "anneal/toolchain"
    if cache.is_dir():
        entries = []
        for entry in cache.iterdir():
            cand = entry / "lean/bin/lean"
            with contextlib.suppress(OSError):
                if cand.is_file():
                    entries.append((entry.stat().st_mtime, cand.resolve()))
        for _, cand in sorted(entries, key=lambda item: item[0], reverse=True):
            if _verify_lean_version(cand, expected_ver):
                return cand
    elan = home / f".elan/toolchains/leanprover--lean4---v{expected_ver}/bin/lean"
    if elan.is_file() and _verify_lean_version(elan.resolve(), expected_ver):
        return elan.resolve()
    if found := shutil.which("lean"):
        if _verify_lean_version(cand := Path(found).resolve(), expected_ver):
            return cand
    ci_lean = Path("/opt/anneal-nix/lean-toolchain/bin/lean")
    if ci_lean.is_file() and _verify_lean_version(ci_lean.resolve(), expected_ver):
        return ci_lean.resolve()
    return None


def _comb_tree_height(steps: list[dict[str, int | str]]) -> int:
    heights: list[int] = []
    for st in steps:
        if st["op"] == "hyp":
            heights.append(0)
        elif st["op"] == "comb":
            heights.append(1 + max(heights[int(st["s1"])], heights[int(st["s2"])]))
        else:
            heights.append(1 + heights[int(st["s"])])
    return heights[-1]


class FarkasCertGenTests(unittest.TestCase):
    def test_grammar_domain_rules_and_bounds(self) -> None:
        # Equality expands to 2 bounds; `<` desugars; AST structure preserved.
        eqs = parse_inequalities("x = y + 1", "nat")
        self.assertEqual(len(eqs), 2)
        self.assertEqual([op for _, op, _ in eqs], ["<=", "<="])
        res = generate_certificate(
            "nat", ["1 + n <= i", "i + 1 <= b + a"], "n + 1 < b + a", "nat_ok"
        )
        self.assertTrue(res["solved"])
        self.assertIn("1 + n ≤ i", res["lean_snippet"])
        self.assertIn("n + 1 < b + a", res["lean_snippet"])

        # Nat rejects subtraction/negative constants; right-scalar rejected.
        for dom, hyps, goal in (
            ("nat", ["x - 1 <= y"], "x <= y"),
            ("nat", ["-x <= 1"], "0 <= 1"),
            ("nat", ["x <= -1"], "0 <= 1"),
            ("nat", ["x * 2 <= 4"], "x <= 2"),
            ("nat", ["x * y <= 4"], "0 <= 1"),
            ("int", ["x <= 1"], "x = 1"),
            ("int", ["def <= 1"], "def <= 2"),
            ("int", ["then <= 1"], "then <= 2"),
            ("int", ["syntax <= 1"], "syntax <= 2"),
            ("int", ["macro <= 1"], "macro <= 2"),
            ("int", ["unsafe <= 1"], "unsafe <= 2"),
            ("int", ["using <= 1"], "using <= 2"),
            ("int", ["h0 <= 1"], "h0 <= 2"),
            ("int", ["mythm <= 1"], "mythm <= 2"),
            ("int", ["x <= " + str(_MAG_CAP_128 + 1)], "0 <= 1"),
            ("int", ["x <= " + "9" * 45], "0 <= 1"),
        ):
            with self.assertRaises(ParseError, msg=(dom, hyps, goal)):
                generate_certificate(dom, hyps, goal, "mythm")
        for bad_name in ("then", "syntax", "macro", "unsafe"):
            with self.assertRaises(ParseError, msg=bad_name):
                generate_certificate("int", ["x <= 1"], "x <= 2", bad_name)

        # Deep expressions and large systems fail bounds upfront.
        deep_lhs = " + ".join(["x"] * 20)
        with self.assertRaisesRegex(ParseError, "kernel limits"):
            generate_certificate("nat", [f"{deep_lhs} <= y"], "x <= y", "deep")
        chain49 = [f"v{i} <= v{i + 1}" for i in range(49)]
        with self.assertRaisesRegex(ParseError, "maxRecDepth"):
            generate_certificate("nat", chain49, "v0 <= v49", "over_nat", max_nodes=20000)

        # Unsatisfiable search budget vs unprovable constraints.
        uns = generate_certificate("int", ["a <= 5"], "a <= 4", "nope")
        self.assertFalse(uns["solved"])
        self.assertIn("No Farkas", uns["error"])

    def test_balanced_comb_pruning_and_cli_surface(self) -> None:
        chain = [f"v{i} <= v{i + 1}" for i in range(40)]
        res = generate_certificate("int", chain, "v0 <= v40", "chain40")
        self.assertTrue(res["solved"])
        self.assertLessEqual(_comb_tree_height(res["steps"]), 8)

        noise = [f"u{i} <= 10" for i in range(50)]
        pruned = generate_certificate("nat", [*noise, "x + 1 <= y", "y <= z"], "x < z", "pruned")
        self.assertTrue(pruned["solved"])
        self.assertEqual(pruned["kept_hyp_indices"], [50, 51])
        self.assertEqual(pruned["variables"], ["x", "y", "z"])

        eq_p = generate_certificate("nat", ["u <= 1", "a = b", "b <= c"], "a <= c", "eq_p")
        self.assertEqual(eq_p["kept_hyp_indices"], [1, 2])

        # CLI negative args, JSON/text exit codes, ASCII output, bad UTF-8.
        out = io.StringIO()
        with mock.patch.dict(os.environ, _scrubbed_env(), clear=True):
            with contextlib.redirect_stdout(out):
                rc = cli_main([
                    "--domain", "int", "--hyp", "-x<=5",
                    "--hyp", "x<=-10", "--goal", "-9<=1", "--json",
                ])
        self.assertEqual(rc, 0)
        self.assertTrue(json.loads(out.getvalue())["solved"])

        for bad_hyp in ("x \udcff <= 1", "x <= " + "9" * 5000):
            o2, e2 = io.StringIO(), io.StringIO()
            with mock.patch.dict(os.environ, _scrubbed_env(), clear=True):
                with contextlib.redirect_stdout(o2), contextlib.redirect_stderr(e2):
                    argv2 = ["--domain", "int", "--hyp", bad_hyp, "--goal", "0 <= 1", "--json"]
                    rc2 = cli_main(argv2)
            self.assertEqual(rc2, 2)
            self.assertEqual(e2.getvalue(), "")
            self.assertFalse(json.loads(o2.getvalue())["solved"])

        o3, e3 = io.StringIO(), io.StringIO()
        with mock.patch.dict(os.environ, _scrubbed_env(), clear=True):
            with contextlib.redirect_stdout(o3), contextlib.redirect_stderr(e3):
                rc3 = cli_main(["--domain", "int", "--hyp", "a <= 5", "--goal", "a <= 4"])
        self.assertEqual(rc3, 1)
        self.assertEqual(o3.getvalue(), "")
        self.assertIn("No Farkas", e3.getvalue())

        ascii_run = subprocess.run(
            [sys.executable, "-B", str(_CI_DIR / "farkas_cert_gen.py"),
             "--domain", "int", "--hyp", "a <= b", "--goal", "a <= b"],
            env={**_scrubbed_env(), "PYTHONIOENCODING": "ascii"},
            capture_output=True, text=True, timeout=15,
        )
        self.assertEqual(ascii_run.returncode, 0, ascii_run.stderr)
        self.assertIn("<=", ascii_run.stdout)
        self.assertIn("{ lhs :=", ascii_run.stdout)

    def test_lean_discovery_error_handling(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            stub_dir = root / "cache/anneal/toolchain/wrong/lean/bin"
            stub_dir.mkdir(parents=True)
            stub = stub_dir / "lean"
            stub.write_text("#!/bin/sh\necho 'Lean (version 0.0.0)'\n", encoding="utf-8")
            stub.chmod(0o755)
            with mock.patch.dict(os.environ, _scrubbed_env({"ANNEAL_LEAN": str(stub)}), clear=True):
                with self.assertRaises(RuntimeError):
                    _find_pinned_lean()
            with mock.patch.dict(
                os.environ, _scrubbed_env({"ANNEAL_LEAN": str(root / "missing")}), clear=True
            ):
                with self.assertRaises(FileNotFoundError):
                    _find_pinned_lean()
            ci_bin = Path("/opt/anneal-nix/lean-toolchain/bin/lean")
            with mock.patch.dict(os.environ, {"HOME": str(root / "nohome")}, clear=True):
                with mock.patch("shutil.which", return_value=None):
                    with mock.patch.object(
                        Path, "is_file",
                        autospec=True,
                        side_effect=lambda self_p: self_p == ci_bin,
                    ):
                        with mock.patch.object(
                            Path, "resolve",
                            autospec=True,
                            side_effect=lambda self_p: stub if self_p == ci_bin else self_p,
                        ):
                            with mock.patch(
                                f"{__name__}._verify_lean_version",
                                side_effect=lambda cand, _v: cand == stub,
                            ):
                                self.assertEqual(_find_pinned_lean(), stub)

    def test_pass1_int_syntax_and_ci_strict_mode(self) -> None:
        # `--domain int` negatives avoid unary `-` (`«term-_»`).
        int_sig = generate_certificate(
            "int", ["-2*x - y <= 5", "-3 <= -y"], "-4 <= x", "sig_chk"
        )
        self.assertTrue(int_sig["solved"])
        self.assertIn("Int.negOfNat 2 * x - y", int_sig["lean_snippet"])
        self.assertIn("Int.neg y", int_sig["lean_snippet"])
        self.assertIn("Int.negOfNat 4 ≤ x", int_sig["lean_snippet"])
        grp_sig = generate_certificate(
            "int", ["-(x + z) <= -(-1)", "x <= -2", "z <= 0"], "1 <= 0", "grp_chk"
        )
        self.assertTrue(grp_sig["solved"])
        self.assertIn("Int.neg (x + z) ≤ Int.neg (Int.negOfNat 1)", grp_sig["lean_snippet"])
        for snip in (int_sig["lean_snippet"], grp_sig["lean_snippet"]):
            for ln in snip.splitlines():
                self.assertNotRegex(ln, r"(?:^|[\s(\[≤<])-[0-9A-Za-z_(]")

        # Missing pinned Lean fails under ANNEAL_CI_STRICT=1 (no skip).
        with mock.patch(f"{__name__}._find_pinned_lean", return_value=None):
            with mock.patch.dict(os.environ, {"ANNEAL_CI_STRICT": "1"}, clear=False):
                with self.assertRaises(AssertionError):
                    self.test_live_lean_kernel_checks_emitted_snippets()
            with mock.patch.dict(
                os.environ, {k: v for k, v in os.environ.items() if k != "ANNEAL_CI_STRICT"},
                clear=True,
            ):
                with self.assertRaises(unittest.SkipTest):
                    self.test_live_lean_kernel_checks_emitted_snippets()

    def test_live_lean_kernel_checks_emitted_snippets(self) -> None:
        lean_bin = _find_pinned_lean()
        if lean_bin is None:
            msg = f"no pinned Lean {_pinned_lean_version()} toolchain installed"
            if os.environ.get("ANNEAL_CI_STRICT") == "1":
                self.fail(msg)
            self.skipTest(msg)
        noise = [f"u{i} <= 10" for i in range(50)]
        chain40 = [f"v{i} <= v{i + 1}" for i in range(40)]
        lad14 = ["3 * x1 <= 2", *[f"3 * x{i + 1} <= 2 * x{i} + 2" for i in range(1, 14)]]
        cases = [
            ("nat", ["2*i <= 2*n + 1", "2*n + 1 <= 2*i"], "1 <= 0", "parity_false", False),
            ("int", ["-2*x - y <= 5", "-3 <= -y"], "-4 <= x", "int_bound", False),
            ("int", ["-2*x - y <= 5", "-3 <= -y"], "-4 <= x", "int_bound_asc", True),
            ("int", ["2*i <= 2*n + 1", "2*n + 1 <= 2*i"], "1 <= 0", "int_parity", False),
            ("int", ["x - y <= 5", "y <= 2"], "x < 8", "int_sub_lt", False),
            ("int", ["1 <= 0"], "2 <= 0", "int_const", False),
            ("int", ["-9 <= 1", "1 <= 0"], "-2 <= 0", "int_neg_const", False),
            ("nat", ["a = b"], "a <= b", "eq_bound", False),
            ("nat", ["x + 2*y <= 10"], "x <= 10", "nonneg_x", False),
            ("nat", ["1 + n <= i", "i + 1 <= b + a"], "n + 1 < b + a", "nat_shape", False),
            ("nat", ["a + 1 <= b"], "b > a", "nat_gt", False),
            ("nat", lad14, "x14 <= 0", "lad_14_nat", False),
            ("int", lad14, "x14 <= 0", "lad_14_int", False),
            ("int", ["x <= -(3)"], "x <= -(2)", "int_neg_paren", False),
            ("int", ["-(2*x + y) <= -(-1)", "y <= 1"], "-x <= 1", "int_neg_grp", False),
            ("nat", [*noise, "x + 1 <= y", "y <= z"], "x < z", "pruned_50", False),
            ("int", chain40, "v0 <= v40", "chain_40", False),
            ("int", ["x <= 5"], "x <= 5", "ascii_check", True),
        ]
        snippets = [
            generate_certificate(d, h, g, nm, ascii_lean=asc)["lean_snippet"]
            for d, h, g, nm, asc in cases
        ]
        with tempfile.TemporaryDirectory() as tmp:
            t = Path(tmp)
            (t / "Anneal").mkdir()
            lean_env = {"PATH": f"{lean_bin.parent}:/usr/bin:/bin"}
            if ld := os.environ.get("LD_LIBRARY_PATH"):
                lean_env["LD_LIBRARY_PATH"] = ld
            subprocess.check_call(
                [
                    str(lean_bin), "-R", str(_ANNEAL_ROOT / "theory"),
                    "-o", str(t / "Anneal/LinearArith.olean"),
                    str(_ANNEAL_ROOT / "theory/Anneal/LinearArith.lean"),
                ],
                env=lean_env, timeout=120,
            )
            lean_env["LEAN_PATH"] = f"{t}:{lean_bin.parent.parent / 'lib/lean'}"
            probe = t / "Probe.lean"
            hdr = (
                "prelude\nimport Anneal.LinearArith\n"
                "open Anneal.LinearArith\n"
            )
            body = "\n".join(
                ln for snip in snippets for ln in snip.splitlines()
                if not ln.startswith(("import ", "open "))
            )
            probe.write_text(hdr + body + "\n", encoding="utf-8")
            res = subprocess.run(
                [str(lean_bin), str(probe)], env=lean_env,
                text=True, capture_output=True, timeout=120,
            )
            self.assertEqual(res.returncode, 0, res.stdout + res.stderr)
            self.assertEqual(res.stdout.strip() + res.stderr.strip(), "")

            neg_probe = t / "NegControl.lean"
            neg_probe.write_text(
                "import Anneal.LinearArith\nprivate theorem bad_ctrl : (1 : Nat) = 2 := rfl\n",
                encoding="utf-8",
            )
            neg_res = subprocess.run(
                [str(lean_bin), str(neg_probe)], env=lean_env,
                text=True, capture_output=True, timeout=60,
            )
            self.assertNotEqual(neg_res.returncode, 0)

            # Confirm emitted snippets also pass Pass-1 preflight.
            tb = _ANNEAL_ROOT / "trusted/audit/TrustedBoundary.lean"
            sysroot = str(lean_bin.parent.parent)
            lock = json.loads(
                (_ANNEAL_ROOT / "trusted/lean/foundation-lock.json").read_text("utf-8")
            )
            pf_env = {**lean_env, "LEAN_PATH": f"{_ANNEAL_ROOT / 'theory'}:{sysroot}/lib/lean"}
            parts = ("olean", "olean.server", "olean.private", "ir.sig", "ir")
            arts = []
            for mod, rec in sorted(lock["modules"].items()):
                rel = mod.replace(".", "/")
                avail = [str(Path(sysroot) / "lib/lean" / f"{rel}.{pt}")
                         for pt in parts if rec["parts"].get(pt) is not None]
                arts.append([mod, [avail[:3], avail[3:]]])
            p_req, p_out = t / "preq.json", t / "pout.json"
            p_req.write_text(json.dumps({
                "mode": "preflight", "sysroot": sysroot, "artifacts": arts,
                "foundation": list(lock["modules"]), "graph": lock["graph"],
                "axioms": lock["axioms"],
                "sources": [
                    ["Anneal.LinearArith", str(_ANNEAL_ROOT / "theory/Anneal/LinearArith.lean")],
                    ["Anneal.TestFarkasPreflight", str(probe)],
                ],
            }), encoding="utf-8")
            pf = subprocess.run(
                [str(lean_bin), "--run", str(tb), str(p_req), str(p_out)],
                env=pf_env, text=True, capture_output=True, timeout=60,
            )
            self.assertEqual(pf.returncode, 0, pf.stdout + pf.stderr)
            self.assertTrue(json.loads(p_out.read_text(encoding="utf-8"))["ok"])


def _tamper_all_cert_slots(snip: str) -> list[str]:
    """Produce one tampered copy per certificate slot (`_cert*`, each `_fwd_certs`
    entry, and each `.equiv` reverse cert), replacing that single slot with `[]`."""
    m_name = re.search(r"(?m)^private theorem ([A-Za-z_][A-Za-z0-9_']*)\b", snip)
    assert m_name is not None, snip
    base = m_name.group(1)

    def rename(code: str, idx: int) -> str:
        suf = (
            r"(?=(?:_(?:hyps|cert(?:_le|_ge|_lo|_hi|_range)?|"
            r"pre|obligation|fwd_certs|sat_witness|mode))?\b)"
        )
        return re.sub(rf"\b{re.escape(base)}{suf}", f"{base}_t{idx}", code)

    variants: list[str] = []
    # 1. Every standalone `List CutStep` cert (`_cert`, `_cert_le`, `_cert_ge`, `_cert_lo`, `_cert_hi`, `_cert_range`)
    cert_pat = re.compile(r"(_cert(?:_le|_ge|_lo|_hi|_range)? : List CutStep :=\n  )(\[[^\]]*\])")
    for m in cert_pat.finditer(snip):
        tampered = snip[: m.start(2)] + "[]" + snip[m.end(2) :]
        assert tampered != snip, snip
        variants.append(rename(tampered, len(variants)))

    # 2. Every individual obligation cert inside `_fwd_certs` and `.equiv [...]`
    for list_pat in (
        re.compile(r"(_fwd_certs : List \(List CutStep\) :=\n  \[)(.*)(\])"),
        re.compile(r"(\.equiv \[)(.*)(\])"),
    ):
        for lm in list_pat.finditer(snip):
            inner_start = lm.start(2)
            inner = lm.group(2)
            for sm in re.finditer(r"\[[^\]]*\]", inner):
                s_abs = inner_start + sm.start()
                e_abs = inner_start + sm.end()
                tampered = snip[:s_abs] + "[]" + snip[e_abs:]
                assert tampered != snip, snip
                variants.append(rename(tampered, len(variants)))

    assert variants, snip
    return variants


def _semantic_tamper_variants(snip: str) -> list[str]:
    """Produce *non-trivial* tampered copies whose certificates / witnesses are
    real, well-formed data that is valid for a DIFFERENT obligation:

    * swap the two certificates of a two-sided preset (`_cert_le`/`_cert_ge`,
      `_cert_lo`/`_cert_hi`, `_cert`/`_cert_range`),
    * swap the first two forward certificates of a multi-obligation edge,
    * in `.strict` mode, reuse the satisfaction witness as the strictness witness
      (it satisfies `pre`, so it cannot falsify it) and vice versa (the strictness
      witness falsifies `pre`, so it cannot be a satisfaction witness).

    Unlike `[]` slots (rejected merely for being empty), these exercise the
    kernel's semantic row arithmetic and witness evaluation.
    """
    m_name = re.search(r"(?m)^private theorem ([A-Za-z_][A-Za-z0-9_']*)\b", snip)
    assert m_name is not None, snip
    base = m_name.group(1)
    suf = (r"(?=(?:_(?:hyps|cert(?:_le|_ge|_lo|_hi|_range)?|"
           r"pre|obligation|fwd_certs|sat_witness|mode))?\b)")
    out: list[str] = []

    def emit(code: str) -> None:
        assert code != snip, snip
        out.append(re.sub(rf"\b{re.escape(base)}{suf}", f"{base}_s{len(out)}", code))

    def slot(name: str) -> re.Match[str] | None:
        return re.search(rf"({re.escape(base)}_{name} : List CutStep :=\n  )(\[[^\]]*\])", snip)

    for a, b in (("cert_le", "cert_ge"), ("cert_lo", "cert_hi"), ("cert", "cert_range")):
        ma, mb = slot(a), slot(b)
        if ma and mb and ma.group(2) != mb.group(2):
            (m1, m2) = (ma, mb) if ma.start() < mb.start() else (mb, ma)
            emit(snip[: m1.start(2)] + m2.group(2) + snip[m1.end(2) : m2.start(2)]
                 + m1.group(2) + snip[m2.end(2) :])
    fm = re.search(r"(_fwd_certs : List \(List CutStep\) :=\n  \[)(.*)(\])", snip)
    if fm:
        items = list(re.finditer(r"\[[^\]]*\]", fm.group(2)))
        if len(items) >= 2 and items[0].group(0) != items[1].group(0):
            off = fm.start(2)
            i0, i1 = items[0], items[1]
            emit(snip[: off + i0.start()] + i1.group(0) + snip[off + i0.end() : off + i1.start()]
                 + i0.group(0) + snip[off + i1.end() :])
    sw = re.search(r"(_sat_witness : List (?:Nat|Int) :=\n  )(\[[^\]]*\])", snip)
    st = re.search(r"(\.strict )(\[[^\]]*\])", snip)
    if sw and st:
        emit(snip[: st.start(2)] + sw.group(2) + snip[st.end(2) :])
        emit(snip[: sw.start(2)] + st.group(2) + snip[sw.end(2) :])
    eq = re.search(r"(\.equiv \[)(.*)(\])", snip)
    if fm and eq and fm.group(2) != eq.group(2):
        # Asymmetric `.equiv`: swapping forward and reverse cert lists must fail at `rfl`.
        (m1, m2) = (fm, eq) if fm.start(2) < eq.start(2) else (eq, fm)
        emit(snip[: m1.start(2)] + m2.group(2) + snip[m1.end(2) : m2.start(2)]
             + m1.group(2) + snip[m2.end(2) :])
    if "farkas_discharges_uint_add_no_overflow .u128" in snip:
        # Narrowing the target width `.u128` -> `.u8` invalidates the overflow bound at `rfl`.
        emit(snip.replace(".u128", ".u8"))
    if "farkas_discharges_uint_add_no_overflow .u16" in snip:
        emit(snip.replace(".u16", ".u8"))
    return out


class FarkasMirCertGenTests(unittest.TestCase):
    def _run_cli(self, argv: list[str]) -> tuple[int, str, str]:
        out, err = io.StringIO(), io.StringIO()
        with mock.patch.dict(os.environ, _scrubbed_env(), clear=True):
            with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
                rc = cli_main(argv)
        return rc, out.getvalue(), err.getvalue()

    def test_mir_bounds_presets_and_cli_surface(self) -> None:
        # 1. slice-range
        rc, out, err = self._run_cli([
            "--mir-bounds", "slice-range",
            "--offset-expr", "base + 4", "--len-expr", "n", "--total-expr", "cap",
            "--hyp", "base <= 12", "--hyp", "n <= 32", "--hyp", "48 <= cap",
            "--name", "slice_ok", "--json",
        ])
        self.assertEqual(rc, 0, err)
        data = json.loads(out)
        self.assertTrue(data["solved"])
        self.assertEqual(data["mode"], "mir-bounds")
        self.assertEqual(data["preset"], "slice-range")
        self.assertIn("farkas_discharges_slice_bounds", data["lean_snippet"])

        # 2. aligned-stride (genuinely cut-required Chvatal-Gomory divCut:
        # at z = 1/2, off = 8 * q +/- 1 satisfies all hyps over Q, so cut-free Farkas fails)
        rc, out, err = self._run_cli([
            "--mir-bounds", "aligned-stride",
            "--align", "8", "--offset-expr", "off", "--quot-expr", "q",
            "--hyp", "2 * z <= 1",
            "--hyp", "8 * q <= off + 2 * z",
            "--hyp", "off <= 8 * q + 2 * z",
            "--name", "align_divcut", "--json",
        ])
        self.assertEqual(rc, 0, err)
        data = json.loads(out)
        self.assertTrue(data["solved"])
        self.assertEqual(data["align"], 8)
        self.assertIn("farkas_discharges_aligned_stride", data["lean_snippet"])
        self.assertTrue(any(s["op"] == "divCut" for s in data["steps_le"]))
        self.assertTrue(any(s["op"] == "divCut" for s in data["steps_ge"]))

        # 3. uint-add-no-overflow: u64 specialization and u128 boundary (2^128 = magCap128)
        u64 = generate_mir_bounds_certificate(
            "uint-add-no-overflow", ["a <= 1000", "b <= 2000"], "u64_add", width=64
        )
        self.assertTrue(u64["solved"])
        self.assertIn("farkas_discharges_u64_add_no_overflow", u64["lean_snippet"])

        u128_max_minus_10 = (1 << 128) - 10
        u128 = generate_mir_bounds_certificate(
            "uint-add-no-overflow",
            [f"a <= {u128_max_minus_10}", "b <= 9"],
            "u128_add_edge", width=128,
        )
        self.assertTrue(u128["solved"])
        self.assertIn("farkas_discharges_uint_add_no_overflow .u128", u128["lean_snippet"])

        # Unprovable u128 overflow (sum can reach 2^128) fails with solved=False / exit 1
        rc_ov, out_ov, err_ov = self._run_cli([
            "--mir-bounds", "uint-add-no-overflow", "--width", "128",
            "--hyp", f"a <= {u128_max_minus_10}", "--hyp", "b <= 10",
            "--json",
        ])
        self.assertEqual(rc_ov, 1, err_ov)
        self.assertFalse(json.loads(out_ov)["solved"])

        # 4. uint-sub-no-underflow
        rc, out, err = self._run_cli([
            "--mir-bounds", "uint-sub-no-underflow", "--width", "32",
            "--lhs-expr", "hi", "--rhs-expr", "lo",
            "--hyp", "lo + 4 <= hi", "--name", "u32_sub", "--json",
        ])
        self.assertEqual(rc, 0, err)
        self.assertIn("farkas_discharges_uint_sub_no_underflow .u32", json.loads(out)["lean_snippet"])

        # 5. aipcc-interval-refine (with and without src interval)
        rc, out, err = self._run_cli([
            "--mir-bounds", "aipcc-interval-refine", "--width", "32",
            "--var", "x", "--src-lo", "10", "--src-hi", "100",
            "--target-lo", "10", "--target-hi", "50",
            "--hyp", "x <= 50", "--name", "iv_ref", "--json",
        ])
        self.assertEqual(rc, 0, err)
        iv_data = json.loads(out)
        self.assertTrue(iv_data["solved"])
        self.assertIn("farkas_discharges_aipcc_interval_refinement", iv_data["lean_snippet"])
        self.assertIn("wrappedInterval_denote_bounds rfl hSrc", iv_data["lean_snippet"])

        # 6. uint-mul-const-no-overflow & non-overlapping-ptrs
        mul_res = generate_mir_bounds_certificate(
            "uint-mul-const-no-overflow", ["x <= 1024"], "mul_ok", width=64, scale=8, var_name="x"
        )
        self.assertTrue(mul_res["solved"])
        self.assertIn("farkas_discharges_uint_mul_const_no_overflow", mul_res["lean_snippet"])

        no_res = generate_mir_bounds_certificate(
            "non-overlapping-ptrs",
            ["dst_off + count <= 32", "32 <= src_off"],
            "no_ok", direction="dst-before-src",
        )
        self.assertTrue(no_res["solved"])
        self.assertIn(".dstBeforeSrc", no_res["lean_snippet"])

        # ASCII-safe CLI output
        ascii_run = subprocess.run(
            [
                sys.executable, "-B", str(_CI_DIR / "farkas_cert_gen.py"),
                "--mir-bounds", "slice-range",
                "--hyp", "off <= 8", "--hyp", "len <= 8", "--hyp", "16 <= total",
            ],
            env={**_scrubbed_env(), "PYTHONIOENCODING": "ascii"},
            capture_output=True, text=True, timeout=15,
        )
        self.assertEqual(ascii_run.returncode, 0, ascii_run.stderr)
        self.assertIn("/\\", ascii_run.stdout)
        self.assertIn("{ lhs :=", ascii_run.stdout)
        self.assertTrue(ascii_run.stdout.isascii())

    def test_mir_bounds_validation_and_caps(self) -> None:
        # Over-cap u128 constant fails closed with ParseError / exit 2
        with self.assertRaises(ParseError):
            generate_mir_bounds_certificate(
                "uint-add-no-overflow",
                [f"a <= {_MAG_CAP_128 + 1}", "b <= 0"],
                "over_cap", width=128,
            )
        # Invalid width, align=0, reversed interval, hi >= 2^width, partial src interval, reserved vars
        for kwargs in (
            {"preset": "uint-add-no-overflow", "hyp_strings": [], "width": 24},
            {"preset": "aligned-stride", "hyp_strings": [], "align": 0},
            {"preset": "aipcc-interval-refine", "hyp_strings": [], "width": 8, "target_lo": 10, "target_hi": 5},
            {"preset": "aipcc-interval-refine", "hyp_strings": [], "width": 8, "target_lo": 0, "target_hi": 256},
            {"preset": "aipcc-interval-refine", "hyp_strings": [], "width": 8, "target_lo": 0, "target_hi": 10, "src_lo": 0},
            {"preset": "slice-range", "hyp_strings": ["rp <= 10"], "offset_expr": "off"},
            {"preset": "uint-add-no-overflow", "hyp_strings": ["locals <= 5"]},
        ):
            with self.assertRaises(ParseError, msg=kwargs):
                generate_mir_bounds_certificate(**kwargs)

        # CLI mutual exclusion, stray mode/preset flags, & domain guard -> exit 2
        for bad_argv in (
            ["--mir-bounds", "slice-range", "--entailment-check", "--obligation", "0 <= 1", "--witness", ""],
            ["--mir-bounds", "slice-range", "--domain", "int", "--hyp", "off <= 1"],
            ["--mir-bounds", "slice-range", "--goal", "0 <= 1"],
            ["--mir-bounds", "slice-range", "--width", "32"],
            ["--mir-bounds", "uint-add-no-overflow", "--target-lo", "0"],
            ["--mir-bounds", "aligned-stride", "--scale", "4"],
            ["--entailment-check", "--pre", "x <= 1", "--obligation", "x <= 2",
             "--witness", "x=0", "--width", "32"],
            ["--goal", "x <= 1", "--width", "32"],
        ):
            rc, out, _ = self._run_cli([*bad_argv, "--json"])
            self.assertEqual(rc, 2, bad_argv)
            self.assertFalse(json.loads(out)["solved"])

        # Oversized MIR-bounds system (>30 hyps) fails closed upfront with ParseError
        # even when the goal is unprovable (rather than returning solved=False).
        too_many_hyps = [f"v{i} <= 1" for i in range(35)]
        with self.assertRaisesRegex(ParseError, "maxRecDepth"):
            generate_mir_bounds_certificate(
                "uint-add-no-overflow", too_many_hyps, "too_many", width=8
            )
        # Missing `--goal` in default mode keeps the baseline argparse contract
        # (`required=True`): usage error on stderr and `SystemExit(2)`, no JSON.
        for argv in (["--hyp", "x <= 1", "--json"], ["--hyp", "x <= 1"]):
            out, err = io.StringIO(), io.StringIO()
            with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
                with self.assertRaises(SystemExit) as cm:
                    cli_main(argv)
            self.assertEqual(cm.exception.code, 2)
            self.assertEqual(out.getvalue(), "")
            self.assertIn("the following arguments are required: --goal", err.getvalue())

        # Variables (and theorem names) that would shadow globals referenced by the
        # emitted snippet are rejected up front instead of producing ill-typed Lean.
        for kwargs in (
            {"preset": "uint-add-no-overflow", "hyp_strings": ["modPow2 <= 5"], "lhs_expr": "modPow2"},
            {"preset": "slice-range", "hyp_strings": [], "len_expr": "some"},
            {"preset": "non-overlapping-ptrs", "hyp_strings": ["NonOverlappingPtrs <= 1"]},
            {"preset": "slice-range", "hyp_strings": [], "thm_name": "evalPtrOffset"},
            {"preset": "uint-mul-const-no-overflow", "hyp_strings": ["UintScalarInRange <= 1"]},
        ):
            with self.assertRaises(ParseError, msg=kwargs):
                generate_mir_bounds_certificate(**kwargs)

        # Synthesized compound goal ASTs exceeding `_MAX_AST_DEPTH` (16) fail closed:
        # 17-term sum has depth 16; adding `len` makes depth 17 > 16.
        depth16 = " + ".join(["x"] * 17)
        with self.assertRaisesRegex(ParseError, "kernel limits"):
            generate_mir_bounds_certificate(
                "slice-range", [f"{depth16} + len <= total"],
                offset_expr=depth16, len_expr="len", total_expr="total",
            )
        # In `uint-sub-no-underflow`, depth-16 `lhs` makes `lhs + 1` depth 17, so
        # range certification cleanly falls back to `hRange` without exceeding caps.
        sub_deep = generate_mir_bounds_certificate(
            "uint-sub-no-underflow", [f"b <= {depth16}", f"{depth16} <= 100"],
            "sub_deep_fallback", width=32, lhs_expr=depth16, rhs_expr="b",
        )
        self.assertTrue(sub_deep["solved"])
        self.assertFalse(sub_deep["range_certified"])

        # Negative expression CLI arg returns clean JSON exit 2 (no argparse crash).
        rc_neg, out_neg, err_neg = self._run_cli([
            "--mir-bounds", "uint-add-no-overflow", "--width", "8",
            "--lhs-expr", "-a", "--json",
        ])
        self.assertEqual(rc_neg, 2, err_neg)
        self.assertEqual(err_neg, "")
        self.assertFalse(json.loads(out_neg)["solved"])

        # Entailment reserved global names cannot be shadowed by `--name` or vars.
        for bad_ent_name in ("farkas_entailment_adequacy_cert", "NatLinSpec", "IntLinSpec"):
            with self.assertRaises(ParseError, msg=bad_ent_name):
                generate_entailment_certificate(
                    "nat", ["x <= 5"], ["x <= 10"], "x=0", thm_name=bad_ent_name
                )

        # A constant multiplier must itself be a valid `uN` operand (`< 2^width`):
        # `256 * x` with `x <= 0` is overflow-free but `256` is not a `u8`.
        with self.assertRaises(ParseError):
            generate_mir_bounds_certificate(
                "uint-mul-const-no-overflow", ["x <= 0"], "mul_bad_k", width=8, scale=256
            )
        ok_k = generate_mir_bounds_certificate(
            "uint-mul-const-no-overflow", ["x <= 1"], "mul_max_k", width=8, scale=255
        )
        self.assertTrue(ok_k["solved"])
        rc, out, _ = self._run_cli([
            "--mir-bounds", "uint-mul-const-no-overflow", "--width", "8", "--scale", "256",
            "--hyp", "x <= 0", "--json",
        ])
        self.assertEqual(rc, 2)
        self.assertFalse(json.loads(out)["solved"])

    def test_uint_sub_range_certification(self) -> None:
        # Operand range derivable from hyps -> fully certified theorem, no `hRange`.
        cert = generate_mir_bounds_certificate(
            "uint-sub-no-underflow", ["b + 4 <= a", "a <= 1000"], "sub_cert", width=32
        )
        self.assertTrue(cert["solved"])
        self.assertTrue(cert["range_certified"])
        self.assertTrue(cert["steps_range"])
        self.assertIn("farkas_discharges_uint_sub_no_underflow_certified .u32", cert["lean_snippet"])
        self.assertNotIn("hRange", cert["lean_snippet"])
        self.assertIn("sub_cert_cert_range", cert["lean_snippet"])
        # Range NOT derivable (`a <= 2^32` admits `a = 2^32`) -> fall back to `hRange`.
        unc = generate_mir_bounds_certificate(
            "uint-sub-no-underflow", ["b + 4 <= a", f"a <= {1 << 32}"], "sub_unc", width=32
        )
        self.assertTrue(unc["solved"])
        self.assertFalse(unc["range_certified"])
        self.assertNotIn("steps_range", unc)
        self.assertIn("(hRange : a < modPow2 (uintWidth .u32))", unc["lean_snippet"])
        self.assertNotIn("_certified", unc["lean_snippet"])

    def test_entailment_check_modes_and_negative_controls(self) -> None:
        # 1. Nat sufficient-only with heterogeneous obligation variable subsets
        nat_multi = generate_entailment_certificate(
            "nat",
            ["x <= 4", "y <= 6", "z <= 10"],
            ["x <= 10", "x + y <= 10", "y + z <= 20"],
            "x=1,y=2,z=3",
            thm_name="nat_multi",
        )
        self.assertTrue(nat_multi["solved"])
        self.assertEqual(nat_multi["adequacy_mode"], "sufficient_only")
        self.assertEqual(nat_multi["variables"], ["x", "y", "z"])
        self.assertEqual(len(nat_multi["fwd_certs"]), 3)
        self.assertIn("farkas_entailment_adequacy_cert", nat_multi["lean_snippet"])

        # 2. Nat strict strengthening
        nat_strict = generate_entailment_certificate(
            "nat",
            ["x <= 5", "y <= 5"],
            ["x + y <= 12"],
            "x=0,y=0",
            strict_witness_str="x=6,y=6",
            thm_name="nat_strict",
        )
        self.assertTrue(nat_strict["solved"])
        self.assertEqual(nat_strict["adequacy_mode"], "strict")
        self.assertIn(".strict [6, 6]", nat_strict["lean_snippet"])

        # 3. Nat bidirectional equivalence
        nat_equiv = generate_entailment_certificate(
            "nat",
            ["x + 1 <= y"],
            ["x + 2 <= y + 1"],
            "x=0,y=1",
            check_equiv=True,
            thm_name="nat_equiv",
        )
        self.assertTrue(nat_equiv["solved"])
        self.assertEqual(nat_equiv["adequacy_mode"], "equiv")
        self.assertIn(".equiv", nat_equiv["lean_snippet"])

        # 4. Int strict with negative witnesses (Pass-1 Int syntax: no unary `-`)
        rc, out, err = self._run_cli([
            "--entailment-check", "--domain", "int",
            "--pre", "-3 <= x", "--pre", "x <= 2",
            "--obligation", "-5 <= x",
            "--witness", "x=-1", "--strict-witness", "x=-4",
            "--name", "int_strict_cli", "--json",
        ])
        self.assertEqual(rc, 0, err)
        idata = json.loads(out)
        self.assertTrue(idata["solved"])
        self.assertIn("Int.negOfNat 1", idata["lean_snippet"])
        self.assertIn("Int.negOfNat 4", idata["lean_snippet"])
        for ln in idata["lean_snippet"].splitlines():
            self.assertNotRegex(ln, r"(?:^|[\s(\[≤<])-[0-9A-Za-z_(]")

        # 5. Zero-variable spec with empty witness ""
        z_res = generate_entailment_certificate("nat", ["0 <= 1"], ["0 <= 2"], "", thm_name="z_ok")
        self.assertTrue(z_res["solved"])
        self.assertEqual(z_res["variables"], [])

        # 6. Negative semantic controls -> solved=False / exit 1
        # (a) Vacuous pre (1 <= 0)
        rc, out, _ = self._run_cli([
            "--entailment-check", "--pre", "1 <= 0", "--obligation", "x <= 0",
            "--witness", "x=0", "--json",
        ])
        self.assertEqual(rc, 1)
        self.assertFalse(json.loads(out)["solved"])
        self.assertIn("violates precondition", json.loads(out)["error"])

        # (b) Negative witness value in --domain nat
        rc, out, _ = self._run_cli([
            "--entailment-check", "--domain", "nat",
            "--pre", "x <= 5", "--obligation", "x <= 10",
            "--witness", "x=-1", "--json",
        ])
        self.assertEqual(rc, 1)
        self.assertIn("negative value", json.loads(out)["error"])

        # (c) Non-entailing obligation
        non_ent = generate_entailment_certificate("nat", ["x <= 10"], ["x <= 5"], "x=0")
        self.assertFalse(non_ent["solved"])
        self.assertEqual(non_ent["failed_obligation_index"], 0)

        # (d) Strict witness satisfies pre (fails to prove strictness)
        bad_st1 = generate_entailment_certificate(
            "nat", ["x <= 5"], ["x <= 10"], "x=0", strict_witness_str="x=4"
        )
        self.assertFalse(bad_st1["solved"])
        self.assertIn("satisfies precondition", bad_st1["error"])

        # (e) Strict witness violates obligation
        bad_st2 = generate_entailment_certificate(
            "nat", ["x <= 5"], ["x <= 10"], "x=0", strict_witness_str="x=11"
        )
        self.assertFalse(bad_st2["solved"])
        self.assertIn("violates obligation", bad_st2["error"])

        # (f) False equivalence
        bad_eq = generate_entailment_certificate(
            "nat", ["x <= 5"], ["x <= 10"], "x=0", check_equiv=True
        )
        self.assertFalse(bad_eq["solved"])
        self.assertEqual(bad_eq["failed_pre_index"], 0)

        # 7. Parse / CLI misuse -> ParseError / exit 2
        for bad_w in ("x=abc", "y=1", "", "x=1,x=2"):
            with self.assertRaises(ParseError, msg=bad_w):
                parse_witness(bad_w, ["x"], "nat")
        for bad_argv in (
            ["--entailment-check", "--pre", "x <= 5", "--witness", "x=0"],
            ["--entailment-check", "--pre", "x <= 5", "--obligation", "x <= 10"],
            ["--entailment-check", "--pre", "x <= 5", "--obligation", "x <= 10",
             "--witness", "x=0", "--strict-witness", "x=6", "--check-equiv"],
            ["--entailment-check", "--pre", "x <= 5", "--hyp", "x <= 4",
             "--obligation", "x <= 10", "--witness", "x=0"],
        ):
            rc, out, _ = self._run_cli([*bad_argv, "--json"])
            self.assertEqual(rc, 2, bad_argv)
            self.assertFalse(json.loads(out)["solved"])

        # 8. ASCII-safe output for --entailment-check
        ascii_run = subprocess.run(
            [
                sys.executable, "-B", str(_CI_DIR / "farkas_cert_gen.py"),
                "--entailment-check", "--domain", "int",
                "--pre", "-3 <= x", "--obligation", "-5 <= x",
                "--witness", "x=-1", "--strict-witness", "x=-4",
            ],
            env={**_scrubbed_env(), "PYTHONIOENCODING": "ascii"},
            capture_output=True, text=True, timeout=15,
        )
        self.assertEqual(ascii_run.returncode, 0, ascii_run.stderr)
        self.assertTrue(ascii_run.stdout.isascii())
        self.assertIn("{ lhs :=", ascii_run.stdout)

    def _assert_fails_only_at_rfl(self, output: str, expected: int, label: str) -> None:
        chunks = re.split(r"(?m)^\S+?:\d+:\d+: (?=error)", output)[1:]
        self.assertEqual(len(chunks), expected, f"{label}: unexpected error count\n{output}")
        for ch in chunks:
            self.assertNotRegex(ch, r"(?i)unknown (identifier|constant)", f"{label}:\n{output}")
            self.assertRegex(ch, r"\brfl\b", f"{label}: error is not a rejected `rfl`\n{output}")

    def test_live_lean_kernel_checks_mir_bounds_and_entailment(self) -> None:
        lean_bin = _find_pinned_lean()
        if lean_bin is None:
            msg = f"no pinned Lean {_pinned_lean_version()} toolchain installed"
            if os.environ.get("ANNEAL_CI_STRICT") == "1":
                self.fail(msg)
            self.skipTest(msg)

        # Always (incrementally) rebuild: a pre-existing but stale `.olean` would
        # otherwise make the kernel checks below test an outdated library.
        olean_path = _ANNEAL_ROOT / ".lake/build/lib/lean/Anneal/FarkasMirCert.olean"
        lake_bin = lean_bin.parent / "lake"
        if not lake_bin.is_file():
            found_lake = shutil.which("lake")
            lake_bin = Path(found_lake) if found_lake else lake_bin
        if not lake_bin.is_file():
            if not olean_path.is_file() or os.environ.get("ANNEAL_CI_STRICT") == "1":
                self.fail("`lake` not found; cannot (re)build Anneal.FarkasMirCert.")
        else:
            build_env = {**os.environ, "PATH": f"{lean_bin.parent}:{os.environ.get('PATH', '')}"}
            subprocess.check_call(
                [str(lake_bin), "build", "Anneal.FarkasMirCert"],
                cwd=str(_ANNEAL_ROOT), env=build_env, timeout=300,
            )

        u128_max_minus_10 = (1 << 128) - 10
        snippets = [
            generate_mir_bounds_certificate(
                "slice-range",
                ["base <= 12", "n <= 32", "48 <= cap"],
                "live_slice_range",
                offset_expr="base + 4", len_expr="n", total_expr="cap",
            )["lean_snippet"],
            generate_mir_bounds_certificate(
                "slice-range",
                ["off <= 8", "len <= 8", "16 <= total"],
                "live_slice_ascii", ascii_lean=True,
            )["lean_snippet"],
            generate_mir_bounds_certificate(
                "aligned-stride",
                ["2 * z <= 1", "8 * q <= off + 2 * z", "off <= 8 * q + 2 * z"],
                "live_aligned_divcut", align=8, offset_expr="off", quot_expr="q",
            )["lean_snippet"],
            generate_mir_bounds_certificate(
                "uint-add-no-overflow",
                ["a <= 1000", "b <= 2000"],
                "live_u64_add", width=64,
            )["lean_snippet"],
            generate_mir_bounds_certificate(
                "uint-add-no-overflow",
                [f"a <= {u128_max_minus_10}", "b <= 9"],
                "live_u128_add_boundary", width=128,
            )["lean_snippet"],
            generate_mir_bounds_certificate(
                "uint-add-no-overflow",
                ["a <= 100", "b <= 150"],
                "live_u8_add_ascii", width=8, ascii_lean=True,
            )["lean_snippet"],
            generate_mir_bounds_certificate(
                "uint-sub-no-underflow",
                ["b + 4 <= a"],
                "live_u32_sub", width=32,
            )["lean_snippet"],
            generate_mir_bounds_certificate(
                "uint-sub-no-underflow",
                ["b <= a"],
                "live_u128_sub", width=128,
            )["lean_snippet"],
            generate_mir_bounds_certificate(
                "aipcc-interval-refine",
                ["x <= 50"],
                "live_aipcc_with_src", width=32, var_name="x",
                src_lo=10, src_hi=100, target_lo=10, target_hi=50,
            )["lean_snippet"],
            generate_mir_bounds_certificate(
                "aipcc-interval-refine",
                ["10 <= x", "x <= 20"],
                "live_aipcc_no_src", width=16, var_name="x",
                target_lo=5, target_hi=25, ascii_lean=True,
            )["lean_snippet"],
            generate_mir_bounds_certificate(
                "uint-mul-const-no-overflow",
                ["x <= 1024"],
                "live_u64_mul", width=64, scale=8, var_name="x",
            )["lean_snippet"],
            generate_mir_bounds_certificate(
                "uint-mul-const-no-overflow",
                ["x <= 1"],
                "live_u8_mul_max_k", width=8, scale=255, var_name="x",
            )["lean_snippet"],
            generate_mir_bounds_certificate(
                "uint-sub-no-underflow",
                ["b + 4 <= a", "a <= 1000"],
                "live_u32_sub_certified", width=32,
            )["lean_snippet"],
            generate_mir_bounds_certificate(
                "uint-sub-no-underflow",
                ["b <= a", f"a + 1 <= {1 << 128}"],
                "live_u128_sub_certified_ascii", width=128, ascii_lean=True,
            )["lean_snippet"],
            generate_mir_bounds_certificate(
                "non-overlapping-ptrs",
                ["src_off + count <= 64", "64 <= dst_off"],
                "live_nonoverlap_left", direction="src-before-dst",
            )["lean_snippet"],
            generate_mir_bounds_certificate(
                "non-overlapping-ptrs",
                ["dst_off + count <= 32", "32 <= src_off"],
                "live_nonoverlap_right", direction="dst-before-src", ascii_lean=True,
            )["lean_snippet"],
            generate_entailment_certificate(
                "nat",
                ["x <= 4", "y <= 6", "z <= 10"],
                ["x <= 10", "x + y <= 10", "y + z <= 20"],
                "x=1,y=2,z=3",
                thm_name="live_ent_nat_multi",
            )["lean_snippet"],
            generate_entailment_certificate(
                "nat",
                ["x <= 5", "y <= 5"],
                ["x + y <= 12"],
                "x=0,y=0",
                strict_witness_str="x=6,y=6",
                thm_name="live_ent_nat_strict",
            )["lean_snippet"],
            generate_entailment_certificate(
                "nat",
                ["x + 1 <= y"],
                ["x + 2 <= y + 1"],
                "x=0,y=1",
                check_equiv=True,
                thm_name="live_ent_nat_equiv",
            )["lean_snippet"],
            generate_entailment_certificate(
                "int",
                ["-3 <= x", "x <= 2"],
                ["-5 <= x", "x <= 4"],
                "x=-1",
                strict_witness_str="x=-4",
                thm_name="live_ent_int_strict",
            )["lean_snippet"],
            generate_entailment_certificate(
                "int",
                ["x - y <= 3"],
                ["2 * x - 2 * y <= 6"],
                "x=0,y=0",
                check_equiv=True,
                thm_name="live_ent_int_equiv_ascii",
                ascii_lean=True,
            )["lean_snippet"],
            # Compound (non-atomic) operand expressions: exercises rendering
            # precedence and defeq of the emitted statement vs `NatLinExpr.eval`.
            generate_mir_bounds_certificate(
                "uint-add-no-overflow", ["a <= 100", "c <= 50", "b <= 1000"],
                "live_u16_add_compound", width=16, lhs_expr="a + 2 * c", rhs_expr="b + 1",
            )["lean_snippet"],
            generate_mir_bounds_certificate(
                "uint-sub-no-underflow", ["c + 1 <= a", "a <= 1000", "b <= 1000"],
                "live_u64_sub_compound_certified", width=64, lhs_expr="a + b", rhs_expr="c + 1",
            )["lean_snippet"],
            generate_mir_bounds_certificate(
                "uint-mul-const-no-overflow", ["a <= 10", "b <= 10"],
                "live_u32_mul_compound", width=32, scale=3, var_name="a + 2 * b",
            )["lean_snippet"],
            generate_mir_bounds_certificate(
                "slice-range", ["base <= 4", "n <= 7", "20 <= cap"],
                "live_slice_compound", offset_expr="2 * base + 4", len_expr="n + 1",
                total_expr="cap",
            )["lean_snippet"],
            generate_mir_bounds_certificate(
                "non-overlapping-ptrs", ["s + 1 + 2 * k <= d"],
                "live_nonoverlap_compound", src_offset_expr="s + 1", dst_offset_expr="d",
                count_expr="2 * k",
            )["lean_snippet"],
            # 0-variable constant MIR bounds and empty-pre entailment checks
            generate_mir_bounds_certificate(
                "slice-range", [], "live_slice_const",
                offset_expr="4", len_expr="8", total_expr="16",
            )["lean_snippet"],
            generate_mir_bounds_certificate(
                "aligned-stride", [], "live_aligned_const",
                align=8, offset_expr="16", quot_expr="2",
            )["lean_snippet"],
            generate_mir_bounds_certificate(
                "uint-add-no-overflow", [], "live_u8_add_const",
                width=8, lhs_expr="100", rhs_expr="150",
            )["lean_snippet"],
            generate_mir_bounds_certificate(
                "uint-sub-no-underflow", [], "live_u8_sub_const_certified",
                width=8, lhs_expr="100", rhs_expr="40",
            )["lean_snippet"],
            generate_entailment_certificate(
                "nat", [], ["0 <= x"], "x=0",
                check_equiv=True, thm_name="live_ent_empty_pre_equiv",
            )["lean_snippet"],
            # 128-bit max WrappedInterval refinement and signed 128-bit entailment boundaries
            generate_mir_bounds_certificate(
                "aipcc-interval-refine",
                ["100 <= x"],
                "live_aipcc_u128_max", width=128, var_name="x",
                src_lo=0, src_hi=(1 << 128) - 1,
                target_lo=100, target_hi=(1 << 128) - 1,
            )["lean_snippet"],
            generate_entailment_certificate(
                "int",
                [f"-{(1 << 128) - 1} <= x", f"x <= {(1 << 128) - 2}"],
                [f"-{(1 << 128) - 1} <= x", f"x <= {(1 << 128) - 1}"],
                "x=0",
                strict_witness_str=f"x={(1 << 128) - 1}",
                thm_name="live_ent_int_128bit_boundary",
            )["lean_snippet"],
        ]

        with tempfile.TemporaryDirectory() as tmp:
            t = Path(tmp)
            lean_env = {
                "PATH": f"{lean_bin.parent}:/usr/bin:/bin",
                "LEAN_PATH": (
                    f"{_ANNEAL_ROOT / '.lake/build/lib/lean'}:"
                    f"{lean_bin.parent.parent / 'lib/lean'}"
                ),
            }
            if ld := os.environ.get("LD_LIBRARY_PATH"):
                lean_env["LD_LIBRARY_PATH"] = ld

            hdr = (
                "prelude\n"
                "import Anneal.FarkasMirCert\n"
                "open Anneal.LinearArith Anneal.AiPcc Anneal.UnsafeObligations Anneal.FarkasMirCert\n"
                "open Trusted.Rustc.V2026_06_01.MirAst Trusted.Rustc.V2026_06_01.MirSemantics\n"
            )
            body = "\n".join(
                ln for snip in snippets for ln in snip.splitlines()
                if not ln.startswith(("import ", "open "))
            )
            probe = t / "ProbeMir.lean"
            probe.write_text(hdr + body + "\n", encoding="utf-8")
            res = subprocess.run(
                [str(lean_bin), "-DwarningAsError=true", str(probe)],
                env=lean_env, text=True, capture_output=True, timeout=180,
            )
            self.assertEqual(res.returncode, 0, res.stdout + res.stderr)
            self.assertEqual(res.stdout.strip() + res.stderr.strip(), "")

            # Negative Lean controls: tampered cert, tampered sat witness, tampered strict witness, truncated edge
            neg_cases = [
                (
                    "NegTamperedCert.lean",
                    "import Anneal.FarkasMirCert\n"
                    "open Anneal.LinearArith Anneal.AiPcc Anneal.UnsafeObligations Anneal.FarkasMirCert\n"
                    "open Trusted.Rustc.V2026_06_01.MirAst Trusted.Rustc.V2026_06_01.MirSemantics\n"
                    "private theorem bad_cert (a b : Nat) (locals : List LocalSlot)\n"
                    "    (mem : Memory) (ha : a <= 10) :\n"
                    "    a + b < modPow2 (uintWidth .u64) /\\ a + b < scalarModulus (uintBytes .u64) /\\\n"
                    "    evalScalarBinOp .addUnchecked ⟨a, uintBytes .u64⟩ ⟨b, uintBytes .u64⟩ locals mem false =\n"
                    "      .ok (.scalar ⟨a + b, uintBytes .u64⟩) locals mem /\\\n"
                    "    evalScalarBinOp .addWithOverflow ⟨a, uintBytes .u64⟩ ⟨b, uintBytes .u64⟩ locals mem false =\n"
                    "      .ok (.aggregate 0 [.scalar ⟨a + b, uintBytes .u64⟩, .scalar ⟨0, 1⟩]) locals mem :=\n"
                    "  farkas_discharges_u64_add_no_overflow [⟨.var 0, .cst 10⟩] (.var 0) (.var 1) [.hyp 0] rfl [a, b] locals mem ha\n",
                ),
                (
                    "NegBadSatWitness.lean",
                    "import Anneal.FarkasMirCert\n"
                    "open Anneal.LinearArith Anneal.FarkasMirCert\n"
                    "private theorem bad_sat :\n"
                    "    NatEntailmentAdequacyProp [⟨.var 0, .cst 5⟩] [⟨.var 0, .cst 10⟩] .sufficientOnly :=\n"
                    "  farkas_entailment_adequacy_cert [⟨.var 0, .cst 5⟩] [⟨.var 0, .cst 10⟩]\n"
                    "    [[.hyp 0, .hyp 2, .comb 0 1 1 1]] [6] .sufficientOnly rfl\n",
                ),
                (
                    "NegBadStrictWitness.lean",
                    "import Anneal.FarkasMirCert\n"
                    "open Anneal.LinearArith Anneal.FarkasMirCert\n"
                    "private theorem bad_strict :\n"
                    "    NatEntailmentAdequacyProp [⟨.var 0, .cst 5⟩] [⟨.var 0, .cst 10⟩] (.strict [4]) :=\n"
                    "  farkas_entailment_adequacy_cert [⟨.var 0, .cst 5⟩] [⟨.var 0, .cst 10⟩]\n"
                    "    [[.hyp 0, .hyp 2, .comb 0 1 1 1]] [0] (.strict [4]) rfl\n",
                ),
                (
                    "NegTruncatedEdge.lean",
                    "import Anneal.FarkasMirCert\n"
                    "open Anneal.LinearArith Anneal.FarkasMirCert\n"
                    "private theorem bad_trunc : ∀ env, NatLinSpec.holds env [⟨.var 0, .cst 5⟩] →\n"
                    "    NatLinSpec.holds env [⟨.var 0, .cst 5⟩, ⟨.var 0, .cst 0⟩] :=\n"
                    "  checkNatEntailmentEdge_sound (certs := [[.hyp 0, .hyp 2, .comb 0 1 1 1]]) rfl\n",
                ),
                (
                    "NegMulScaleOutOfRange.lean",
                    "import Anneal.FarkasMirCert\n"
                    "open Anneal.LinearArith Anneal.AiPcc Anneal.FarkasMirCert\n"
                    "open Trusted.Rustc.V2026_06_01.MirAst Trusted.Rustc.V2026_06_01.MirSemantics\n"
                    "private theorem bad_mul_k (x : Nat) (locals : List LocalSlot) (mem : Memory) (hx : x <= 0) :\n"
                    "    UintScalarInRange .u8 ⟨256, uintBytes .u8⟩ /\\\n"
                    "    256 * x < modPow2 (uintWidth .u8) /\\ 256 * x < scalarModulus (uintBytes .u8) /\\\n"
                    "    evalScalarBinOp .mulUnchecked ⟨256, uintBytes .u8⟩ ⟨x, uintBytes .u8⟩ locals mem false =\n"
                    "      .ok (.scalar ⟨256 * x, uintBytes .u8⟩) locals mem /\\\n"
                    "    evalScalarBinOp .mulWithOverflow ⟨256, uintBytes .u8⟩ ⟨x, uintBytes .u8⟩ locals mem false =\n"
                    "      .ok (.aggregate 0 [.scalar ⟨256 * x, uintBytes .u8⟩, .scalar ⟨0, 1⟩]) locals mem :=\n"
                    "  farkas_discharges_uint_mul_const_no_overflow .u8 [⟨.var 0, .cst 0⟩] 256 (.var 0)\n"
                    "    [.hyp 0, .hyp 2, .comb 0 256 1 1] rfl rfl [x] locals mem hx\n",
                ),
            ]
            for fname, content in neg_cases:
                nf = t / fname
                nf.write_text(content, encoding="utf-8")
                nres = subprocess.run(
                    [str(lean_bin), str(nf)], env=lean_env,
                    text=True, capture_output=True, timeout=60,
                )
                self.assertNotEqual(nres.returncode, 0, f"Negative control unexpectedly passed: {fname}")
                self._assert_fails_only_at_rfl(nres.stdout + nres.stderr, 1, fname)

            # Systematic tampering of EVERY certificate slot across EVERY generated
            # snippet (`_cert`, `_cert_le`, `_cert_ge`, `_cert_lo`, `_cert_hi`,
            # `_cert_range`, every `_fwd_certs` entry, and every `.equiv` reverse cert):
            # corrupt each slot individually to `[]` and require the kernel to reject
            # every single variant ONLY at `rfl`.
            tampered: list[str] = []
            for snip in snippets:
                tampered.extend(_tamper_all_cert_slots(snip))
            self.assertGreater(len(tampered), len(snippets))
            tbody = "\n".join(
                ln for snip in tampered for ln in snip.splitlines()
                if not ln.startswith(("import ", "open "))
            )
            tfile = t / "NegTamperedAll.lean"
            tfile.write_text(hdr + tbody + "\n", encoding="utf-8")
            tres = subprocess.run(
                [str(lean_bin), str(tfile)], env=lean_env,
                text=True, capture_output=True, timeout=240,
            )
            self.assertNotEqual(tres.returncode, 0)
            self._assert_fails_only_at_rfl(tres.stdout + tres.stderr, len(tampered), "NegTamperedAll")

            # Semantic tampering (swapped certificates / witnesses that are valid
            # data for a different obligation) must also be rejected at `rfl`.
            semantic: list[str] = []
            for snip in snippets:
                semantic.extend(_semantic_tamper_variants(snip))
            self.assertGreaterEqual(len(semantic), 8)
            sbody = "\n".join(
                ln for snip in semantic for ln in snip.splitlines()
                if not ln.startswith(("import ", "open "))
            )
            sfile = t / "NegSemanticTamper.lean"
            sfile.write_text(hdr + sbody + "\n", encoding="utf-8")
            sres = subprocess.run(
                [str(lean_bin), str(sfile)], env=lean_env,
                text=True, capture_output=True, timeout=240,
            )
            self.assertNotEqual(sres.returncode, 0)
            self._assert_fails_only_at_rfl(sres.stdout + sres.stderr, len(semantic), "NegSemanticTamper")

            # Confirm Anneal.FarkasMirCert and emitted ProbeMir.lean pass Pass-1 preflight.
            tb = _ANNEAL_ROOT / "trusted/audit/TrustedBoundary.lean"
            sysroot = str(lean_bin.parent.parent)
            lock = json.loads(
                (_ANNEAL_ROOT / "trusted/lean/foundation-lock.json").read_text("utf-8")
            )
            pf_env = {**lean_env, "LEAN_PATH": f"{_ANNEAL_ROOT / 'theory'}:{sysroot}/lib/lean"}
            parts = ("olean", "olean.server", "olean.private", "ir.sig", "ir")
            arts = []
            for mod, rec in sorted(lock["modules"].items()):
                rel = mod.replace(".", "/")
                avail = [str(Path(sysroot) / "lib/lean" / f"{rel}.{pt}")
                         for pt in parts if rec["parts"].get(pt) is not None]
                arts.append([mod, [avail[:3], avail[3:]]])
            p_req, p_out = t / "preq_mir.json", t / "pout_mir.json"
            p_req.write_text(json.dumps({
                "mode": "preflight", "sysroot": sysroot, "artifacts": arts,
                "foundation": list(lock["modules"]), "graph": lock["graph"],
                "axioms": lock["axioms"],
                "sources": [
                    ["Anneal.FarkasMirCert", str(_ANNEAL_ROOT / "theory/Anneal/FarkasMirCert.lean")],
                    ["Anneal.TestFarkasMirPreflight", str(probe)],
                ],
            }), encoding="utf-8")
            pf = subprocess.run(
                [str(lean_bin), "--run", str(tb), str(p_req), str(p_out)],
                env=pf_env, text=True, capture_output=True, timeout=60,
            )
            self.assertEqual(pf.returncode, 0, pf.stdout + pf.stderr)
            self.assertTrue(json.loads(p_out.read_text(encoding="utf-8"))["ok"])


if __name__ == "__main__":
    unittest.main()
