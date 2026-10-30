#!/usr/bin/env python3
"""Zero-dependency MCP stdio JSON-RPC server for Anneal Lean 4 + Rust tooling.

Speaks newline-delimited JSON-RPC 2.0 (`modelcontextprotocol/go-sdk` CommandTransport)
and routes all tool invocations to the shared warm daemon (`anneal_lsp_daemon.py`).
"""

from __future__ import annotations

import concurrent.futures
import json
import os
import sys
import threading
from typing import Any

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import anneal_lsp_daemon as daemon  # noqa: E402

SERVER_NAME = "anneal-lean-lsp"
SERVER_VERSION = "0.1.0"
SUPPORTED_PROTOCOLS = {"2024-11-05", "2025-03-26", "2025-06-18"}

TOOLS: list[dict[str, Any]] = [
    {
        "name": "lean_diagnostics",
        "description": (
            "Check a Lean 4 file using the warm `lake serve` LSP worker pool (~15-50ms warm). "
            "Returns compiler errors, warnings, `sorry` counts, and open `sorry` proof goals compacted <4 KiB."
        ),
        "inputSchema": {
            "type": "object",
            "properties": {
                "file": {"type": "string", "description": "Absolute path to the `.lean` file."},
                "severity": {
                    "type": "string",
                    "enum": ["all", "warning", "error"],
                    "description": "Optional diagnostic filter (`all` default, `warning` for errors+warnings, `error` for errors only).",
                },
            },
            "required": ["file"],
        },
    },
    {
        "name": "lean_goal",
        "description": (
            "Query Lean 4 tactic proof state (`$/lean/plainGoal`) and expected expression type (`$/lean/plainTermGoal`) "
            "at 1-based `line`. Automatically probes BOTH before and after the tactic on `line` to eliminate column fragility."
        ),
        "inputSchema": {
            "type": "object",
            "properties": {
                "file": {"type": "string", "description": "Absolute path to the `.lean` file."},
                "line": {"type": "integer", "description": "1-based line number in the file."},
                "column": {"type": "integer", "description": "Optional 1-based column number."},
                "snippet": {"type": "string", "description": "Optional substring on `line` to anchor the cursor."},
            },
            "required": ["file", "line"],
        },
    },
    {
        "name": "lean_multi_attempt",
        "description": (
            "Evaluate multiple candidate Lean 4 tactic snippets at 1-based `line` purely in memory via LSP `didChange` overlays "
            "(~12-25ms per candidate, ZERO disk writes, never touches `.anneal/spec-lock.json`). Restores exact on-disk state afterward."
        ),
        "inputSchema": {
            "type": "object",
            "properties": {
                "file": {"type": "string", "description": "Absolute path to the `.lean` file."},
                "line": {"type": "integer", "description": "1-based line number (e.g., a `sorry` line or existing tactic line)."},
                "tactics": {
                    "type": "array",
                    "items": {"type": "string"},
                    "description": "Candidate tactic snippets to test (up to 12), e.g. `[\"rfl\", \"simp\", \"omega\", \"exact ⟨rfl, rfl⟩\"]`.",
                },
            },
            "required": ["file", "line", "tactics"],
        },
    },
    {
        "name": "lean_hover",
        "description": "Get Lean 4 type signature and docstring hover info at `line` (by symbol substring or 1-based column).",
        "inputSchema": {
            "type": "object",
            "properties": {
                "file": {"type": "string", "description": "Absolute path to the `.lean` file."},
                "line": {"type": "integer", "description": "1-based line number."},
                "symbol": {"type": "string", "description": "Identifier/symbol substring on `line` (or 1-based column string)."},
                "column": {"type": "integer", "description": "Optional 1-based column if `symbol` is omitted."},
            },
            "required": ["file", "line"],
        },
    },
    {
        "name": "lean_definition",
        "description": "Jump to the Lean 4 definition of a symbol (`Trusted.*`, `Anneal.*`, `Mir.*`, `Specs.*`, `Obligations.*`) and return its source snippet.",
        "inputSchema": {
            "type": "object",
            "properties": {
                "file": {"type": "string", "description": "Absolute path to the `.lean` file."},
                "line": {"type": "integer", "description": "1-based line number."},
                "symbol": {"type": "string", "description": "Identifier substring on `line` to look up."},
                "column": {"type": "integer", "description": "Optional 1-based column if `symbol` is omitted."},
            },
            "required": ["file", "line"],
        },
    },
    {
        "name": "lean_completions",
        "description": "List context-aware Lean 4 identifier/tactic completions at `file:line:column`.",
        "inputSchema": {
            "type": "object",
            "properties": {
                "file": {"type": "string", "description": "Absolute path to the `.lean` file."},
                "line": {"type": "integer", "description": "1-based line number."},
                "column": {"type": "integer", "description": "Optional 1-based column (defaults to end of code on `line`)."},
            },
            "required": ["file", "line"],
        },
    },
    {
        "name": "lean_outline",
        "description": "Fast, zero-timeout declaration and type-signature outline of a `.lean` file or directory (saves reading full proof bodies).",
        "inputSchema": {
            "type": "object",
            "properties": {
                "file": {"type": "string", "description": "Absolute path to a `.lean` file or directory."},
            },
            "required": ["file"],
        },
    },
    {
        "name": "lean_local_search",
        "description": "Search Lean 4 theorem/def/structure declarations across `trusted/lean/`, `theory/Anneal/`, `.anneal/generated/`, and `anneal/proofs/`.",
        "inputSchema": {
            "type": "object",
            "properties": {
                "query": {"type": "string", "description": "Substring or regex matching declaration names or signatures (e.g. `verifyByWP`, `swapBytes16`)."},
                "workspace": {"type": "string", "description": "Optional absolute path to crate or repo directory to scope the search."},
            },
            "required": ["query"],
        },
    },
    {
        "name": "anneal_audit_preview",
        "description": (
            "Fast pre-flight `TrustedBoundary` check on an Anneal `Proof` module before running `cargo anneal agent-verify`: "
            "verifies 0 compiler errors, 0 `sorry` tokens, `Anneal.*` statement-origin isolation, `.anneal/spec-lock.json` status, "
            "and runs `#print axioms` in memory to catch `sorryAx` or `Lean.ofReduceBool` (`native_decide`)."
        ),
        "inputSchema": {
            "type": "object",
            "properties": {
                "file": {"type": "string", "description": "Absolute path to `anneal/proofs/Proof/<Crate>/<Item>.lean` (or any Lean theorem module)."},
            },
            "required": ["file"],
        },
    },
    {
        "name": "anneal_item_bridge",
        "description": (
            "Cross-language Rust <-> Lean 4 verification bridge: maps Rust `DefId`/item names to `.anneal/generated/{Mir,Obligations}`, "
            "`anneal/proofs/{Specs,Proof}`, stateful vs stateless claim kind, spec-lock status, and open `sorry` counts."
        ),
        "inputSchema": {
            "type": "object",
            "properties": {
                "query": {"type": "string", "description": "Optional item/function substring filter (omit or `\"\"` to list crate summary)."},
                "workspace": {"type": "string", "description": "Absolute path to the Anneal Rust crate directory (e.g. `.../anneal-slice`)."},
            },
        },
    },
    {
        "name": "rust_diagnostics",
        "description": "Check Rust compiler diagnostics for an Anneal/zerocopy crate (`rust-analyzer` LSP if installed, otherwise `cargo check --offline --message-format=json`).",
        "inputSchema": {
            "type": "object",
            "properties": {
                "file": {"type": "string", "description": "Absolute path to a `.rs` file, `Cargo.toml`, or crate directory."},
            },
            "required": ["file"],
        },
    },
    {
        "name": "rust_symbols_and_def",
        "description": "Inspect Rust symbols, `#[anneal...]` / `#[spec]` attributes, doc comments, and definitions across a Rust file or Cargo workspace.",
        "inputSchema": {
            "type": "object",
            "properties": {
                "file": {"type": "string", "description": "Absolute path to a `.rs` file or Cargo crate directory."},
                "query": {"type": "string", "description": "Optional symbol name substring to find/inspect."},
                "line": {"type": "integer", "description": "Optional 1-based line number for cursor hover/definition."},
                "column": {"type": "integer", "description": "Optional 1-based column number."},
            },
            "required": ["file"],
        },
    },
    {
        "name": "lean_restart_workspace",
        "description": "Explicitly restart warm `lake serve` / `rust-analyzer` worker(s) for a workspace root (or `\"all\"`).",
        "inputSchema": {
            "type": "object",
            "properties": {
                "root": {"type": "string", "description": "Absolute path to workspace/file, or `\"all\"`."},
            },
        },
    },
]


class StdioMcpServer:
    def __init__(self) -> None:
        self._write_lock = threading.Lock()
        self._pool = concurrent.futures.ThreadPoolExecutor(max_workers=6)

    def send(self, msg: dict[str, Any]) -> None:
        encoded = json.dumps(msg, separators=(",", ":")) + "\n"
        with self._write_lock:
            sys.stdout.write(encoded)
            sys.stdout.flush()

    def handle_tool_call(self, req_id: Any, params: dict[str, Any]) -> None:
        name = params.get("name", "")
        arguments = params.get("arguments") or {}
        try:
            resp = daemon.daemon_rpc(name, arguments, timeout_s=150.0)
            if not resp.get("ok"):
                self.send(
                    {
                        "jsonrpc": "2.0",
                        "id": req_id,
                        "result": {
                            "content": [{"type": "text", "text": f"Error: {resp.get('error', 'unknown daemon error')}"}],
                            "isError": True,
                        },
                    }
                )
                return
            result_obj = resp.get("result") or {}
            text = result_obj.get("text") if isinstance(result_obj, dict) else str(result_obj)
            if not text:
                text = json.dumps(result_obj, indent=2)
            self.send(
                {
                    "jsonrpc": "2.0",
                    "id": req_id,
                    "result": {
                        "content": [{"type": "text", "text": text}],
                        "isError": False,
                    },
                }
            )
        except Exception as exc:
            self.send(
                {
                    "jsonrpc": "2.0",
                    "id": req_id,
                    "result": {
                        "content": [{"type": "text", "text": f"Tool execution error ({type(exc).__name__}): {exc}"}],
                        "isError": True,
                    },
                }
            )

    def handle_message(self, msg: dict[str, Any]) -> None:
        method = msg.get("method")
        req_id = msg.get("id")
        params = msg.get("params") or {}

        # Notifications have no `id`
        if req_id is None:
            return

        if method == "initialize":
            client_proto = str(params.get("protocolVersion") or "2024-11-05")
            proto = client_proto if client_proto in SUPPORTED_PROTOCOLS else "2024-11-05"
            # Warm-start the background Unix-socket daemon immediately on MCP initialize.
            self._pool.submit(daemon.ensure_daemon_running)
            self.send(
                {
                    "jsonrpc": "2.0",
                    "id": req_id,
                    "result": {
                        "protocolVersion": proto,
                        "capabilities": {"tools": {"listChanged": False}},
                        "serverInfo": {"name": SERVER_NAME, "version": SERVER_VERSION},
                    },
                }
            )
        elif method == "ping":
            self.send({"jsonrpc": "2.0", "id": req_id, "result": {}})
        elif method == "tools/list":
            self.send({"jsonrpc": "2.0", "id": req_id, "result": {"tools": TOOLS}})
        elif method == "resources/list":
            self.send({"jsonrpc": "2.0", "id": req_id, "result": {"resources": []}})
        elif method == "prompts/list":
            self.send({"jsonrpc": "2.0", "id": req_id, "result": {"prompts": []}})
        elif method == "tools/call":
            self._pool.submit(self.handle_tool_call, req_id, params)
        else:
            self.send(
                {
                    "jsonrpc": "2.0",
                    "id": req_id,
                    "error": {"code": -32601, "message": f"Method not found: {method}"},
                }
            )

    def run(self) -> None:
        for raw_line in sys.stdin:
            line = raw_line.strip()
            if not line:
                continue
            try:
                msg = json.loads(line)
            except json.JSONDecodeError as exc:
                sys.stderr.write(f"[anneal-lean-mcp] ignoring invalid JSON line: {exc}\n")
                continue
            if isinstance(msg, dict):
                self.handle_message(msg)


if __name__ == "__main__":
    StdioMcpServer().run()
