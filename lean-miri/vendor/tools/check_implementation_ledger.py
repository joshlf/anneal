#!/usr/bin/env python3
"""Validate and summarize the manually reviewed Rust-to-Lean mapping ledger.

This tool checks links and denominators only. It does not infer semantic
equivalence from a Lean name, a test result, or a source-file inventory row.
"""

from __future__ import annotations

import argparse
import gzip
import hashlib
import json
from pathlib import Path
from typing import Any


AST_KINDS = {"function", "method"}
EVIDENCE_KINDS = {
    "byte_exact_body_differential",
    "finite_source_differential",
    "pinned_api_differential",
    "finite_model_proof",
    "adapter_reporting",
    "source_audit_boundary",
}


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read_json(path: Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8"))


def load_inventory(path: Path) -> dict[str, Any]:
    with gzip.open(path, "rt", encoding="utf-8") as stream:
        return json.load(stream)


def validate_objects(
    root: Path,
    ledger: dict[str, Any],
    inventory: dict[str, Any],
    source_lock: dict[str, Any],
) -> tuple[dict[str, Any], list[str]]:
    errors: list[str] = []
    lock_path = root / "upstream/source-lock.json"
    inventory_lock = inventory.get("source_lock", {}).get("sha256")
    ledger_lock = ledger.get("source_lock_sha256")
    actual_lock = sha256(lock_path)
    if ledger_lock != actual_lock:
        errors.append(
            f"ledger source-lock SHA-256 is stale: {ledger_lock!r} != {actual_lock}"
        )
    if inventory_lock != actual_lock:
        errors.append(
            f"AST inventory source-lock SHA-256 is stale: {inventory_lock!r} != {actual_lock}"
        )

    ast_by_id = {row.get("id"): row for row in inventory.get("symbols", [])}
    source_rows = {row.get("path"): row for row in source_lock.get("files", [])}
    feature_ids = {
        row.get("id")
        for row in read_json(root / "tracking/features.json").get("features", [])
    }
    scopes = {row.get("id"): row for row in ledger.get("scopes", [])}
    if len(scopes) != len(ledger.get("scopes", [])):
        errors.append("scope ids must be unique")
    entries = ledger.get("entries", [])
    entry_ids = [row.get("id") for row in entries]
    if len(set(entry_ids)) != len(entry_ids):
        errors.append("entry ids must be unique")

    reviewed_by_scope: dict[str, set[str]] = {scope_id: set() for scope_id in scopes}
    candidates_by_scope: dict[str, set[str]] = {}
    for scope_id, scope in scopes.items():
        source_paths = set(scope.get("source_paths", []))
        candidates_by_scope[scope_id] = {
            row["id"]
            for row in inventory.get("symbols", [])
            if row.get("path") in source_paths and row.get("kind") in AST_KINDS
        }
        if not source_paths:
            errors.append(f"scope {scope_id}: source_paths is empty")
        for source_path in source_paths:
            if source_path not in source_rows:
                errors.append(f"scope {scope_id}: path is absent from source-lock: {source_path}")

    for entry in entries:
        entry_id = entry.get("id", "<missing-id>")
        scope_id = entry.get("scope_id")
        scope = scopes.get(scope_id)
        if scope is None:
            errors.append(f"entry {entry_id}: unknown scope {scope_id!r}")
            continue

        source = entry.get("source", {})
        ast_id = source.get("ast_symbol_id")
        ast = ast_by_id.get(ast_id)
        if ast is None:
            errors.append(f"entry {entry_id}: unknown AST symbol id {ast_id!r}")
            continue
        path = source.get("path")
        if path not in scope.get("source_paths", []):
            errors.append(f"entry {entry_id}: source path is outside scope: {path}")
        if ast.get("path") != path:
            errors.append(f"entry {entry_id}: AST path {ast.get('path')!r} != source path {path!r}")
        if ast.get("kind") not in AST_KINDS:
            errors.append(f"entry {entry_id}: AST id is not a function/method: {ast.get('kind')!r}")
        span = ast.get("span", {})
        if span.get("line") != source.get("line"):
            errors.append(
                f"entry {entry_id}: AST start line {span.get('line')!r} != source line {source.get('line')!r}"
            )
        if ast.get("symbol") != source.get("ast_symbol"):
            errors.append(f"entry {entry_id}: AST canonical symbol does not match")
        if source.get("symbol") is None or source.get("sha256") is None:
            errors.append(f"entry {entry_id}: source symbol and SHA-256 are required")

        lock_row = source_rows.get(path)
        if lock_row is None:
            errors.append(f"entry {entry_id}: source path is absent from source-lock: {path}")
        else:
            if source.get("sha256") != lock_row.get("sha256"):
                errors.append(f"entry {entry_id}: source SHA-256 does not match source-lock")
            local_source = root / path
            if not local_source.is_file():
                errors.append(f"entry {entry_id}: source file is missing: {path}")
            elif sha256(local_source) != lock_row.get("sha256"):
                errors.append(f"entry {entry_id}: local source file hash does not match source-lock")

        reviewed_by_scope[scope_id].add(ast_id)
        if ast_id not in candidates_by_scope[scope_id]:
            errors.append(f"entry {entry_id}: AST id is not in its scope denominator")

        if entry.get("source_function_complete") is not False:
            errors.append(f"entry {entry_id}: whole-function completion claims are forbidden")
        if not entry.get("slice_claim"):
            errors.append(f"entry {entry_id}: slice_claim must describe the mapped behavior")
        if not entry.get("limitations"):
            errors.append(f"entry {entry_id}: limitations must be explicit")
        evidence = entry.get("evidence", {})
        if evidence.get("kind") not in EVIDENCE_KINDS:
            errors.append(f"entry {entry_id}: unknown evidence kind {evidence.get('kind')!r}")
        if evidence.get("source_body_extracted") is True:
            if evidence.get("kind") not in {
                "byte_exact_body_differential",
                "finite_source_differential",
            }:
                errors.append(f"entry {entry_id}: body extraction conflicts with evidence kind")
        for evidence_path in evidence.get("files", []):
            if not (root / evidence_path).is_file():
                errors.append(f"entry {entry_id}: evidence file is missing: {evidence_path}")
        for feature_id in entry.get("manual_feature_ids", []):
            if feature_id not in feature_ids:
                errors.append(f"entry {entry_id}: unknown manual feature id {feature_id!r}")
        if not entry.get("lean_definitions"):
            errors.append(f"entry {entry_id}: lean_definitions must be explicit (use [] only for an unmapped boundary)")
        if not entry.get("review_disposition"):
            errors.append(f"entry {entry_id}: review_disposition is required")

    reports: list[dict[str, Any]] = []
    for scope_id, scope in scopes.items():
        candidates = candidates_by_scope[scope_id]
        reviewed = reviewed_by_scope[scope_id]
        unreviewed = sorted(candidates - reviewed)
        reports.append({
            "scope_id": scope_id,
            "description": scope.get("description"),
            "source_paths": sorted(scope.get("source_paths", [])),
            "ast_function_or_method_candidates": len(candidates),
            "reviewed_ast_symbols": len(reviewed),
            "unreviewed_ast_symbols": len(unreviewed),
            "unreviewed_ids": unreviewed,
            "reviewed_ids": sorted(reviewed),
        })
    report = {
        "source_lock_sha256": actual_lock,
        "scope_reports": reports,
        "entry_count": len(entries),
        "repository_wide_percentage": None,
        "note": "Counts are limited to the named source files; no repository-wide completion percentage is computed.",
    }
    return report, errors


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--json", action="store_true", help="print the full report, including unreviewed AST ids")
    args = parser.parse_args()
    root = args.root.resolve()
    ledger = read_json(root / "tracking/implementation-ledger.json")
    inventory = load_inventory(root / "tools/source-analysis/inventory.json.gz")
    source_lock = read_json(root / "upstream/source-lock.json")
    report, errors = validate_objects(root, ledger, inventory, source_lock)
    if errors:
        for error in errors:
            print(f"ERROR: {error}")
        return 1
    if args.json:
        print(json.dumps(report, indent=2, sort_keys=True))
    else:
        print("Granular implementation ledger (named files only; no overall percentage):")
        for scope in report["scope_reports"]:
            print(
                f"- {scope['scope_id']}: reviewed {scope['reviewed_ast_symbols']} / "
                f"{scope['ast_function_or_method_candidates']} AST functions/methods; "
                f"unreviewed {scope['unreviewed_ast_symbols']}"
            )
        print(f"- linked mapping entries: {report['entry_count']}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
