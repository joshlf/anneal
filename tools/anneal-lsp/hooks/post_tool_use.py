#!/usr/bin/env python3
"""PostToolUse hook appending warm Lean 4 LSP diagnostics, open `sorry` goals, and
delta-only `[Anneal Proof Health]` warnings on `*.lean` edits.

Compatible with both Jetski / Gemini CLI (`toolCall.args`, `overwriteResult`)
and Claude Code (`tool_input`, `additionalContext`) PostToolUse hook payloads.
"""

from __future__ import annotations

import sys

sys.dont_write_bytecode = True

import json
import os
from pathlib import Path

PLUGIN_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(PLUGIN_ROOT / "server"))


def extract_target_path(payload: dict) -> str | None:
    candidates: list[dict] = []
    tool_call = payload.get("toolCall")
    if isinstance(tool_call, dict) and isinstance(tool_call.get("args"), dict):
        candidates.append(tool_call["args"])
    if isinstance(payload.get("tool_input"), dict):
        candidates.append(payload["tool_input"])
    if isinstance(payload.get("args"), dict):
        candidates.append(payload["args"])
    candidates.append(payload)
    for args in candidates:
        for key in ("Path", "TargetFile", "path", "file_path", "file"):
            val = args.get(key)
            if isinstance(val, str) and val.strip():
                return os.path.abspath(os.path.expanduser(val.strip()))
    return None


def _collect_lsp_feedback(target: str) -> str:
    try:
        import anneal_lsp_daemon as daemon  # noqa: E402

        if daemon.resolve_lake_root(target) is None:
            return ""
        resp = daemon.daemon_rpc(
            "hook_post_edit", {"file": target, "timeout_s": 3.5}, timeout_s=4.8
        )
        if not isinstance(resp, dict) or not resp.get("ok"):
            return ""
        return ((resp.get("result") or {}).get("feedback") or "").strip()
    except Exception:
        return ""


def _collect_proof_health_feedback(target: str, payload: dict) -> str:
    try:
        import proof_health  # noqa: E402

        return proof_health.check_post_edit_proof_health(target, payload).strip()
    except Exception:
        return ""


def main() -> None:
    try:
        raw = sys.stdin.read()
        if not raw.strip():
            print("{}")
            return
        payload = json.loads(raw)
        if not isinstance(payload, dict) or payload.get("error"):
            print("{}")
            return

        target = extract_target_path(payload)
        if not target or not target.endswith(".lean") or not os.path.isfile(target):
            print("{}")
            return
        if "no_lsp" in target or os.environ.get("ANNEAL_DISABLE_LSP_HOOK") == "1":
            print("{}")
            return

        health_feedback = _collect_proof_health_feedback(target, payload)
        lsp_feedback = _collect_lsp_feedback(target)

        sections = [s for s in (lsp_feedback, health_feedback) if s]
        if not sections:
            print("{}")
            return

        feedback = "\n\n".join(sections)
        orig_result = str(payload.get("result") or "Updated file.")
        combined = f"{orig_result.rstrip()}\n\n{feedback}"
        print(
            json.dumps(
                {
                    "overwriteResult": combined,
                    "hookSpecificOutput": {
                        "hookEventName": "PostToolUse",
                        "additionalContext": feedback,
                    },
                }
            )
        )
    except Exception:
        print("{}")


if __name__ == "__main__":
    main()
