#!/usr/bin/env python3
"""Fast CLI client (`anneal-lsp`) for the warm `anneal_lsp_daemon.py` Unix socket pool.

Provides ~15-50ms warm `lake serve` LSP queries (`diagnostics`, `goal`, `multi-attempt`,
`hover`, `definition`, `completions`, `outline`, `search`, `audit-preview`, `item-bridge`,
`rust-diagnostics`, `rust-symbols`, `restart`) via `run_command` in contexts where MCP
servers or PostToolUse hooks are unavailable (such as standalone shells or subagents).
"""

from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import sys
from typing import Any

SERVER_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(SERVER_DIR))
import anneal_lsp_daemon as daemon  # noqa: E402


def _abs(p: str) -> str:
    return os.path.abspath(os.path.expanduser(p))


def _invoke(action: str, payload: dict[str, Any], as_json: bool = False, timeout_s: float = 150.0) -> int:
    resp = daemon.daemon_rpc(action, payload, timeout_s=timeout_s)
    if as_json:
        print(json.dumps(resp, indent=2))
        return 0 if resp.get("ok") else 1
    if not resp.get("ok"):
        sys.stderr.write(f"Error: {resp.get('error', 'unknown daemon error')}\n")
        return 1
    result_obj = resp.get("result") or {}
    text = result_obj.get("text") if isinstance(result_obj, dict) else str(result_obj)
    if not text:
        text = json.dumps(result_obj, indent=2)
    print(text)
    return 0


def build_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(
        prog="anneal-lsp",
        description="Warm Lean 4 (`lake serve`) & Rust LSP CLI client (~15-50ms incremental queries).",
    )
    p.add_argument("--json", action="store_true", help="Print raw daemon JSON response.")
    sub = p.add_subparsers(dest="cmd", required=True)

    d = sub.add_parser("diagnostics", aliases=["diag", "check"], help="Check a .lean file via warm lake serve.")
    d.add_argument("file", help="Path to .lean file.")
    d.add_argument("--severity", choices=("all", "warning", "error"), default="all")

    g = sub.add_parser("goal", help="Inspect tactic proof goal before & after 1-based line.")
    g.add_argument("file", help="Path to .lean file.")
    g.add_argument("line", type=int, help="1-based line number.")
    g.add_argument("--column", type=int, default=None, help="Optional 1-based column.")
    g.add_argument("--snippet", default=None, help="Optional substring on line to anchor cursor.")

    m = sub.add_parser("multi-attempt", aliases=["try"], help="Test up to 12 candidate tactics in memory at line.")
    m.add_argument("file", help="Path to .lean file.")
    m.add_argument("line", type=int, help="1-based line number.")
    m.add_argument("tactics", nargs="+", help="Candidate tactic snippets to test.")

    h = sub.add_parser("hover", help="Get type signature and docstring hover at line.")
    h.add_argument("file", help="Path to .lean file.")
    h.add_argument("line", type=int, help="1-based line number.")
    h.add_argument("symbol", nargs="?", default=None, help="Optional symbol substring on line.")
    h.add_argument("--column", type=int, default=None, help="Optional 1-based column.")

    df = sub.add_parser("definition", aliases=["def"], help="Jump to Lean 4 definition of symbol at line.")
    df.add_argument("file", help="Path to .lean file.")
    df.add_argument("line", type=int, help="1-based line number.")
    df.add_argument("symbol", nargs="?", default=None, help="Optional symbol substring on line.")
    df.add_argument("--column", type=int, default=None, help="Optional 1-based column.")

    cp = sub.add_parser("completions", help="List Lean 4 completions at line.")
    cp.add_argument("file", help="Path to .lean file.")
    cp.add_argument("line", type=int, help="1-based line number.")
    cp.add_argument("--column", type=int, default=None, help="Optional 1-based column.")

    ol = sub.add_parser("outline", help="Declaration and signature outline of a .lean file or directory.")
    ol.add_argument("file", help="Path to .lean file or directory.")

    sr = sub.add_parser("search", help="Search Lean 4 declarations across workspace.")
    sr.add_argument("query", help="Substring or regex query.")
    sr.add_argument("--workspace", default=None, help="Optional crate or repo directory.")

    apv = sub.add_parser("audit-preview", aliases=["audit"], help="Pre-flight TrustedBoundary & #print axioms check.")
    apv.add_argument("file", help="Path to .lean theorem module.")

    ib = sub.add_parser("item-bridge", help="Map Rust DefId/items to generated & authored Lean modules.")
    ib.add_argument("query", nargs="?", default="", help="Optional item substring filter.")
    ib.add_argument("--workspace", default=".", help="Anneal Rust crate directory.")

    rd = sub.add_parser("rust-diagnostics", help="Check Rust compiler diagnostics.")
    rd.add_argument("file", help="Path to .rs file, Cargo.toml, or crate directory.")

    rs = sub.add_parser("rust-symbols", help="Inspect Rust symbols and #[anneal...] / #[spec] attributes.")
    rs.add_argument("file", help="Path to .rs file or crate directory.")
    rs.add_argument("--query", default=None, help="Optional symbol substring.")
    rs.add_argument("--line", type=int, default=None, help="Optional 1-based line.")
    rs.add_argument("--column", type=int, default=None, help="Optional 1-based column.")

    rt = sub.add_parser("restart", help="Restart warm lake serve / rust-analyzer worker(s).")
    rt.add_argument("root", nargs="?", default="all", help="Workspace path or 'all'.")

    return p


def main() -> int:
    ns = build_parser().parse_args()
    cmd = ns.cmd
    if cmd in ("diagnostics", "diag", "check"):
        return _invoke("lean_diagnostics", {"file": _abs(ns.file), "severity": ns.severity}, ns.json)
    if cmd == "goal":
        args: dict[str, Any] = {"file": _abs(ns.file), "line": ns.line}
        if ns.column is not None:
            args["column"] = ns.column
        if ns.snippet:
            args["snippet"] = ns.snippet
        return _invoke("lean_goal", args, ns.json)
    if cmd in ("multi-attempt", "try"):
        return _invoke("lean_multi_attempt", {"file": _abs(ns.file), "line": ns.line, "tactics": ns.tactics}, ns.json)
    if cmd == "hover":
        args = {"file": _abs(ns.file), "line": ns.line}
        if ns.symbol:
            args["symbol"] = ns.symbol
        if ns.column is not None:
            args["column"] = ns.column
        return _invoke("lean_hover", args, ns.json)
    if cmd in ("definition", "def"):
        args = {"file": _abs(ns.file), "line": ns.line}
        if ns.symbol:
            args["symbol"] = ns.symbol
        if ns.column is not None:
            args["column"] = ns.column
        return _invoke("lean_definition", args, ns.json)
    if cmd == "completions":
        args = {"file": _abs(ns.file), "line": ns.line}
        if ns.column is not None:
            args["column"] = ns.column
        return _invoke("lean_completions", args, ns.json)
    if cmd == "outline":
        return _invoke("lean_outline", {"file": _abs(ns.file)}, ns.json)
    if cmd == "search":
        args = {"query": ns.query}
        if ns.workspace:
            args["workspace"] = _abs(ns.workspace)
        return _invoke("lean_local_search", args, ns.json)
    if cmd in ("audit-preview", "audit"):
        return _invoke("anneal_audit_preview", {"file": _abs(ns.file)}, ns.json)
    if cmd == "item-bridge":
        return _invoke("anneal_item_bridge", {"query": ns.query, "workspace": _abs(ns.workspace)}, ns.json)
    if cmd == "rust-diagnostics":
        return _invoke("rust_diagnostics", {"file": _abs(ns.file)}, ns.json)
    if cmd == "rust-symbols":
        args = {"file": _abs(ns.file)}
        if ns.query:
            args["query"] = ns.query
        if ns.line is not None:
            args["line"] = ns.line
        if ns.column is not None:
            args["column"] = ns.column
        return _invoke("rust_symbols_and_def", args, ns.json)
    if cmd == "restart":
        root = "all" if ns.root == "all" else _abs(ns.root)
        return _invoke("lean_restart_workspace", {"root": root}, ns.json)
    return 1


if __name__ == "__main__":
    sys.exit(main())
