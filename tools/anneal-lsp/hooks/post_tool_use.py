#!/usr/bin/env python3
"""PostToolUse hook appending warm Lean 4 LSP diagnostics & open `sorry` goals on `*.lean` edits.

Compatible with both Jetski / Gemini CLI (`toolCall.args`, `overwriteResult`)
and Claude Code (`tool_input`, `additionalContext`) PostToolUse hook payloads.
"""

from __future__ import annotations

import json
import os
from pathlib import Path
import sys

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
    for args in candidates:
        for key in ("Path", "TargetFile", "path", "file_path", "file"):
            val = args.get(key)
            if isinstance(val, str) and val.strip():
                return os.path.abspath(os.path.expanduser(val.strip()))
    return None


def main() -> None:
    try:
        raw = sys.stdin.read()
        if not raw.strip():
            print("{}")
            return
        payload = json.loads(raw)
        if payload.get("error"):
            print("{}")
            return

        target = extract_target_path(payload)
        if not target or not target.endswith(".lean") or not os.path.isfile(target):
            print("{}")
            return
        if "no_lsp" in target or os.environ.get("ANNEAL_DISABLE_LSP_HOOK") == "1":
            print("{}")
            return

        import anneal_lsp_daemon as daemon  # noqa: E402

        if daemon.resolve_lake_root(target) is None:
            print("{}")
            return

        resp = daemon.daemon_rpc("hook_post_edit", {"file": target, "timeout_s": 3.5}, timeout_s=4.8)
        if not resp.get("ok"):
            print("{}")
            return
        feedback = ((resp.get("result") or {}).get("feedback") or "").strip()
        if not feedback:
            print("{}")
            return

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
