#!/usr/bin/env python3
"""PreToolUse hook enforcing Anneal `.anneal/spec-lock.json` write boundaries in <5 ms.

Compatible with both Jetski / Gemini CLI (`toolCall.args`) and Claude Code
(`tool_input`) PreToolUse hook payloads. Respects `mutable_subjects` recorded by
`cargo anneal lock-specs --allow-impl-edit <item>` so locked implementation
authoring can edit `src/**/*.rs` while `Specs/**`, `Assumptions/**`,
`.anneal/**`, and `Cargo.toml` remain write-protected.
"""

from __future__ import annotations

import json
import os
from pathlib import Path
import sys


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


def find_locked_crate(abs_target: str) -> Path | None:
    cur = Path(abs_target).parent
    while True:
        if (cur / ".anneal" / "spec-lock.json").is_file():
            return cur
        if cur.parent == cur:
            return None
        cur = cur.parent


def load_mutable_subjects(crate_root: Path) -> list[str]:
    lock_path = crate_root / ".anneal" / "spec-lock.json"
    try:
        data = json.loads(lock_path.read_text(encoding="utf-8"))
        subjects = data.get("mutable_subjects")
        if isinstance(subjects, list):
            return [s for s in subjects if isinstance(s, str) and s.strip()]
    except Exception:
        pass
    return []


def emit_decision(payload: dict, allow: bool, reason: str = "") -> None:
    if allow:
        print('{"decision":"allow"}')
        return
    # Emit both standard `decision`/`reason` and Claude Code `hookSpecificOutput`
    # fields so either harness blocks the write with a clear diagnostic.
    out: dict = {
        "decision": "deny",
        "reason": reason,
        "hookSpecificOutput": {
            "hookEventName": "PreToolUse",
            "permissionDecision": "deny",
            "permissionDecisionReason": reason,
        },
    }
    print(json.dumps(out))


def main() -> None:
    try:
        raw = sys.stdin.read()
        if not raw.strip():
            print('{"decision":"allow"}')
            return
        payload = json.loads(raw)
        target = extract_target_path(payload)
        if not target:
            print('{"decision":"allow"}')
            return

        crate_root = find_locked_crate(target)
        if crate_root is None:
            print('{"decision":"allow"}')
            return

        allowed_proof_dir = os.path.abspath(str(crate_root / "anneal" / "proofs" / "Proof"))
        if target == allowed_proof_dir or target.startswith(allowed_proof_dir + os.sep):
            emit_decision(payload, True)
            return

        mutable_subjects = load_mutable_subjects(crate_root)
        allowed_src_dir = os.path.abspath(str(crate_root / "src"))
        if (
            mutable_subjects
            and target.endswith(".rs")
            and target.startswith(allowed_src_dir + os.sep)
        ):
            emit_decision(payload, True)
            return

        rel = os.path.relpath(target, str(crate_root))
        if mutable_subjects:
            allowed_desc = (
                "`anneal/proofs/Proof/<Crate>/<Item>.lean` and the designated mutable "
                f"subject implementation in `src/**/*.rs` ({', '.join(mutable_subjects)})"
            )
        else:
            allowed_desc = "`anneal/proofs/Proof/<Crate>/<Item>.lean`"
        reason = (
            f"Blocked by Anneal spec-lock guard (`{crate_root / '.anneal/spec-lock.json'}` is active): "
            f"attempted to modify `{rel}`, which is outside {allowed_desc}. "
            "During locked verification, specifications (`Specs/**`), assumptions (`Assumptions/**`), "
            "and `.anneal/spec-lock.json` are immutable (use `lean_multi_attempt` for zero-disk tactic testing). "
            "If the user explicitly asked to change specifications, unlock the session before editing outside `Proof/`."
        )
        emit_decision(payload, False, reason)
    except Exception:
        # Fail-open on malformed payloads so non-Anneal edits are never disrupted.
        print('{"decision":"allow"}')


if __name__ == "__main__":
    main()
