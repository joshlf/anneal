#!/usr/bin/env python3
"""Keep the Anneal Tutor (`docs/tutor/`) in lockstep with `cargo anneal`.

`tutor.toml` describes the tutorial as an ordered list of steps over the
chapter crates `examples/tutor-ch1/` ... `examples/tutor-ch4/` and
`examples/tutor/`. This script executes those steps against disposable copies
of the crates, records what each command printed and which files it left
behind, and renders those records into the fenced code blocks that the
chapters mark with `<!-- tutor: ... -->` directives. A chapter therefore cannot
cite a command, an exit status, a report, an error message, or a file listing
that the current `cargo anneal` did not actually produce, and each checked-in
chapter crate is verified to be the previous chapter's crate plus the edits the
chapter describes.

Subcommands:

  lint    Parse `tutor.toml` and the chapter directives without executing
          anything. Rejects unknown steps or crates, malformed directives,
          missing fixtures, and command or report blocks that no directive
          manages.
  run     Execute the workflow in a temporary checkout mirror and write one
          record per step under `--artifacts` (default `target/tutor-workflow`).
  check   `run`, then fail if any managed block in the chapters differs from
          the freshly rendered text. This is what `cargo test` invokes.
  render  `run`, then rewrite the managed blocks in place. Review the resulting
          `git diff` before committing.

Pass `--reuse-artifacts` to `check` or `render` to skip the run and reuse the
records of the previous one, which is useful while editing directives or prose.

Only the interior of a managed fenced block is ever rewritten: prose, the
directive line, and the fence lines themselves are preserved byte for byte, so
a rendering bug can at worst produce a wrong code block, never lost prose.

The script depends only on the Python standard library (3.11+ for `tomllib`),
the compiled `cargo-anneal` and `anneal-rustc-capture` binaries, and the Lean
toolchain that `cargo anneal verify` already requires.
"""

from __future__ import annotations

import argparse
import dataclasses
import difflib
import json
import os
import re
import shlex
import shutil
import subprocess
import sys
import tempfile
import tomllib
from pathlib import Path

sys.dont_write_bytecode = True

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]
DOCS_DIR = HERE.parent
WORKFLOW_PATH = HERE / "tutor.toml"
FIXTURES_DIR = HERE / "fixtures"
# Chapter files whose command, report, and error blocks must be generated.
CHAPTER_GLOB = "0[0-9]-*.md"
# Read-only parts of a checkout that the tutor crates' relative paths rely on
# (`../../crates/anneal-spec` in `Cargo.toml`, `trusted/lean` and `theory` for
# the generated Lakefile, and `trusted/audit/TrustedBoundary.lean`).
MIRRORED_DIRS = ("crates", "trusted", "theory")
# Crate-relative paths that make up a crate's durable state: what a chapter
# crate commits, what a probe step restores, and what the delta between two
# chapter crates is checked against.
DURABLE_PATHS = ("Cargo.toml", "src", "anneal")
# Artifacts that `cargo anneal` leaves inside a crate; never copied between
# crates or into records.
CRATE_ARTIFACTS = ("target", ".anneal", "Cargo.lock")
SPEC_LOCK = ".anneal/spec-lock.json"
DIRECTIVE_OPEN = "<!-- tutor:"
DIRECTIVE_CLOSE = "-->"
KINDS = {"command", "report", "errors", "stdout", "stderr", "file", "rm", "static"}
BLOCK_ARGS = {
    "command": {"step"},
    "report": {"step"},
    "errors": {"step"},
    "stdout": {"step"},
    "stderr": {"step"},
    "file": {"step", "path", "strip_module_doc", "item", "items", "docs"},
    "rm": {"step"},
    "static": set(),
}
REPORT_HEADER = re.compile(r"^Anneal [A-Za-z-]+ Summary:$")
# Lines that `lake build` and `cargo check` print around the diagnostics the
# chapters quote. They carry timings and job counters, so they are never
# rendered verbatim.
LAKE_NOISE_PREFIXES = ("✔", "⚠", "✖", "trace:", "info:", "warning:",
                       "Build completed successfully",
                       "Some required targets logged failures:")
CARGO_NOISE = re.compile(r"^\s+(Checking|Compiling|Finished|Downloading|Downloaded|"
                         r"Updating|Locking|Adding|Blocking|Running)\b")


class WorkflowError(Exception):
    """A problem in `tutor.toml`, a fixture, a directive, or a step outcome."""


# --------------------------------------------------------------------------
# Workflow definition
# --------------------------------------------------------------------------

@dataclasses.dataclass(frozen=True)
class FileOp:
    kind: str  # "write" | "append" | "remove"
    path: str  # crate-relative destination
    source: Path | None = None  # absolute source file for "write"
    text: str | None = None  # text for "append"


@dataclasses.dataclass(frozen=True)
class Step:
    id: str
    chapter: int
    note: str
    crate: str  # checkout-relative crate directory, e.g. "examples/tutor-ch2"
    derive_from: str | None  # previous chapter crate this crate is a delta of
    ops: tuple[FileOp, ...]
    run: tuple[str, ...] | None
    cwd: str  # "root" | "crate"
    expect: str  # "success" | "failure"
    probe: bool
    stdout_contains: tuple[str, ...]
    stderr_contains: tuple[str, ...]

    @property
    def is_crate_step(self) -> bool:
        """A step that introduces a chapter crate instead of running a command."""
        return self.run is None

    def display_args(self) -> str:
        """The argument list as the chapters print it after `cargo anneal`."""
        assert self.run is not None
        return f"{' '.join(self.run)} --manifest-path {self.crate}/Cargo.toml"


def _expect_keys(table: dict, allowed: set[str], where: str) -> None:
    unknown = sorted(set(table) - allowed)
    if unknown:
        raise WorkflowError(f"{where}: unknown key(s) {unknown}; allowed: {sorted(allowed)}")


def load_workflow(path: Path = WORKFLOW_PATH) -> list[Step]:
    try:
        data = tomllib.loads(path.read_text(encoding="utf-8"))
    except (OSError, tomllib.TOMLDecodeError) as error:
        raise WorkflowError(f"cannot read {path}: {error}") from error
    _expect_keys(data, {"step"}, str(path))
    raw_steps = data.get("step", [])
    # Every crate a step names, so `write` entries can default their `path`
    # from a source inside any chapter crate.
    crates = []
    for raw in raw_steps:
        crate = raw.get("crate")
        if isinstance(crate, str) and crate not in crates:
            crates.append(crate)
    steps: list[Step] = []
    seen: set[str] = set()
    introduced: set[str] = set()
    for index, raw in enumerate(raw_steps):
        where = f"{path.name} [[step]] #{index + 1}"
        _expect_keys(raw, {"id", "chapter", "note", "crate", "derive_from", "remove", "write",
                           "append", "run", "cwd", "expect", "probe", "stdout_contains",
                           "stderr_contains"}, where)
        step_id = raw.get("id")
        if not isinstance(step_id, str) or not re.fullmatch(r"[a-z0-9][a-z0-9-]*", step_id):
            raise WorkflowError(f"{where}: `id` must be a kebab-case string")
        if step_id in seen:
            raise WorkflowError(f"{where}: duplicate step id {step_id!r}")
        seen.add(step_id)
        where = f"{path.name} step {step_id!r}"

        crate = raw.get("crate")
        if not isinstance(crate, str) or not (REPO / crate / "Cargo.toml").is_file():
            raise WorkflowError(f"{where}: `crate` must name a checkout-relative directory "
                                "containing Cargo.toml (for example \"examples/tutor-ch1\")")
        derive_from = raw.get("derive_from")
        if derive_from is not None and derive_from not in introduced:
            raise WorkflowError(f"{where}: `derive_from` must name a crate introduced by an "
                                f"earlier step without `run`; got {derive_from!r}")

        ops: list[FileOp] = []
        for rel in raw.get("remove", []):
            ops.append(FileOp("remove", _crate_rel(rel, where)))
        for entry in raw.get("write", []):
            _expect_keys(entry, {"path", "fixture", "from"}, f"{where} write")
            if ("fixture" in entry) == ("from" in entry):
                raise WorkflowError(f"{where}: each `write` entry needs exactly one of "
                                    "`fixture` (relative to fixtures/) or `from` (relative "
                                    "to the checkout)")
            if "fixture" in entry:
                source = FIXTURES_DIR / entry["fixture"]
                if "path" not in entry:
                    raise WorkflowError(f"{where}: `fixture` writes need an explicit `path`")
                dest = entry["path"]
            else:
                source = REPO / entry["from"]
                dest = entry.get("path") or _strip_crate_prefix(entry["from"], crates, where)
            if not source.is_file():
                raise WorkflowError(f"{where}: source file {source} does not exist")
            ops.append(FileOp("write", _crate_rel(dest, where), source=source))
        for entry in raw.get("append", []):
            _expect_keys(entry, {"path", "text"}, f"{where} append")
            ops.append(FileOp("append", _crate_rel(entry["path"], where), text=entry["text"]))

        run = raw.get("run")
        if run is not None:
            run_args = tuple(shlex.split(run))
            if not run_args:
                raise WorkflowError(f"{where}: `run` must name a subcommand")
            if any(a.startswith("--manifest-path") or a.startswith("--workspace-root")
                   for a in run_args):
                raise WorkflowError(f"{where}: `run` must not set --manifest-path or "
                                    "--workspace-root; `crate` and `cwd` select them")
            if crate not in introduced:
                raise WorkflowError(f"{where}: crate {crate!r} must be introduced by an earlier "
                                    "step without `run` before a command runs in it")
        else:
            run_args = None
            if raw.get("probe") or raw.get("cwd") or raw.get("expect") \
                    or raw.get("stdout_contains") or raw.get("stderr_contains"):
                raise WorkflowError(f"{where}: a step without `run` introduces a crate and "
                                    "takes no execution options")
            if crate in introduced:
                raise WorkflowError(f"{where}: crate {crate!r} was already introduced")
            introduced.add(crate)
        cwd = raw.get("cwd", "root")
        if cwd not in ("root", "crate"):
            raise WorkflowError(f"{where}: `cwd` must be \"root\" or \"crate\"")
        expect = raw.get("expect", "success")
        if expect not in ("success", "failure"):
            raise WorkflowError(f"{where}: `expect` must be \"success\" or \"failure\"")
        if run_args is not None and not raw.get("probe") and ops:
            raise WorkflowError(f"{where}: only crate steps (no `run`) and probe steps may "
                                "change files; make this step a probe or move the edit into "
                                "the next chapter's crate step")

        steps.append(Step(
            id=step_id,
            chapter=int(raw.get("chapter", 0)),
            note=str(raw.get("note", "")),
            crate=crate,
            derive_from=derive_from,
            ops=tuple(ops),
            run=run_args,
            cwd=cwd,
            expect=expect,
            probe=bool(raw.get("probe", False)),
            stdout_contains=tuple(raw.get("stdout_contains", [])),
            stderr_contains=tuple(raw.get("stderr_contains", [])),
        ))
    if not steps:
        raise WorkflowError(f"{path}: no [[step]] tables")
    return steps


def _crate_rel(rel: str, where: str) -> str:
    p = Path(rel)
    if p.is_absolute() or ".." in p.parts or not rel:
        raise WorkflowError(f"{where}: path {rel!r} must be relative to the crate root")
    return p.as_posix()


def _strip_crate_prefix(source: str, crates: list[str], where: str) -> str:
    for crate in sorted(crates, key=len, reverse=True):
        if source.startswith(crate + "/"):
            return source[len(crate) + 1:]
    raise WorkflowError(f"{where}: cannot infer `path` for {source!r}; it is not inside a "
                        "crate named by any step, so give `path` explicitly")


# --------------------------------------------------------------------------
# Execution
# --------------------------------------------------------------------------

@dataclasses.dataclass
class StepRecord:
    """What a step produced, as read back from the artifacts directory."""
    step: Step
    status: int | None
    stdout: str
    stderr: str
    files: Path  # snapshot root (crate layout)


class Runner:
    def __init__(self, steps: list[Step], cli_bin: Path, artifacts: Path, root: Path,
                 log=print):
        self.steps = steps
        self.cli_bin = cli_bin
        self.artifacts = artifacts
        self.root = root
        self.log = log
        self.env = os.environ.copy()
        self.env["PATH"] = f"{cli_bin.parent}{os.pathsep}{self.env.get('PATH', '')}"
        # The chapters are written for a reader inside a checkout, where the
        # Lakefile and the audit locate `trusted/` and `theory/` by walking up
        # from the crate. An inherited ANNEAL_ROOT would short-circuit that path.
        self.env.pop("ANNEAL_ROOT", None)

    def prepare(self) -> None:
        for name in MIRRORED_DIRS:
            os.symlink(REPO / name, self.root / name, target_is_directory=True)
        if self.artifacts.exists():
            shutil.rmtree(self.artifacts)
        self.artifacts.mkdir(parents=True)

    def run_all(self) -> None:
        for step in self.steps:
            self.run_step(step)

    def crate_dir(self, step: Step) -> Path:
        return self.root / step.crate

    # -- one step -----------------------------------------------------------

    def run_step(self, step: Step) -> None:
        self.log(f"[{step.id}]")
        if step.is_crate_step:
            check_crate_delta(step)
            self._materialize(step)
            self._write_artifacts(step, None, "", "", [], "")
            return
        crate = self.crate_dir(step)
        backup = self._backup_durable(step) if step.probe else None
        try:
            for op in step.ops:
                self._apply(op, crate)
            argv, cwd = self._argv(step)
            proc = subprocess.run(argv, cwd=cwd, env=self.env, capture_output=True,
                                  text=True, errors="replace")
            stdout, stderr = self._normalize(proc.stdout), self._normalize(proc.stderr)
            self._write_artifacts(step, proc.returncode, stdout, stderr, argv, cwd)
            self._check_expectations(step, proc.returncode, stdout, stderr)
        finally:
            if backup is not None:
                self._restore_durable(step, backup)

    def _materialize(self, step: Step) -> None:
        """Copy the committed chapter crate into the mirror, as a reader would.

        Each crate gets a fresh `.anneal/`; the `Trusted` and `Anneal` libraries
        still compile only once per run because the `lake build` that
        `cargo anneal` spawns uses Lake's local artifact cache.
        """
        dest = self.crate_dir(step)
        if dest.exists():
            raise WorkflowError(f"crate {step.crate!r} was already materialized")
        shutil.copytree(REPO / step.crate, dest, symlinks=True,
                        ignore=shutil.ignore_patterns(*CRATE_ARTIFACTS, ".lake"))

    def _argv(self, step: Step) -> tuple[list[str], Path]:
        assert step.run is not None
        if step.cwd == "root":
            # Flavour A: what `cargo run -p cargo-anneal -- ...` execs.
            return ([str(self.cli_bin), *step.run, "--manifest-path", f"{step.crate}/Cargo.toml"],
                    self.root)
        # Flavour B inside the crate: what `cargo anneal ...` execs.
        return [str(self.cli_bin), "anneal", *step.run], self.crate_dir(step)

    def _apply(self, op: FileOp, crate: Path) -> None:
        dest = crate / op.path
        if op.kind == "remove":
            if not dest.is_file():
                raise WorkflowError(f"cannot remove {op.path}: not present in {crate.name}")
            dest.unlink()
            return
        dest.parent.mkdir(parents=True, exist_ok=True)
        if op.kind == "write":
            assert op.source is not None
            shutil.copyfile(op.source, dest)
        elif op.kind == "append":
            if not dest.is_file():
                raise WorkflowError(f"cannot append to {op.path}: not present in {crate.name}")
            with dest.open("a", encoding="utf-8") as handle:
                handle.write(op.text or "")

    def _normalize(self, text: str) -> str:
        text = text.replace("\r\n", "\n")
        for root in {str(self.root), str(self.root.resolve())}:
            text = text.replace(root + "/", "").replace(root, "<root>")
        return text

    def _check_expectations(self, step: Step, status: int, stdout: str, stderr: str) -> None:
        problems = []
        if step.expect == "success" and status != 0:
            problems.append(f"expected success, exit status {status}")
        if step.expect == "failure" and status == 0:
            problems.append("expected failure, exit status 0")
        for needle in step.stdout_contains:
            if needle not in stdout:
                problems.append(f"stdout lacks {needle!r}")
        for needle in step.stderr_contains:
            if needle not in stderr:
                problems.append(f"stderr lacks {needle!r}")
        if problems:
            detail = "\n".join(f"  - {p}" for p in problems)
            raise WorkflowError(
                f"step {step.id!r} did not behave as tutor.toml expects:\n{detail}\n"
                f"  command: {' '.join(shlex.quote(a) for a in step.run or ())}\n"
                f"  crate:   {step.crate}\n"
                f"  records: {self.artifacts / step.id}\n"
                f"--- stdout (tail) ---\n{_tail(stdout)}\n--- stderr (tail) ---\n{_tail(stderr)}")

    def _write_artifacts(self, step: Step, status, stdout, stderr, argv, cwd) -> None:
        out = self.artifacts / step.id
        out.mkdir(parents=True)
        (out / "stdout.txt").write_text(stdout, encoding="utf-8")
        (out / "stderr.txt").write_text(stderr, encoding="utf-8")
        meta = {
            "id": step.id,
            "crate": step.crate,
            "argv": argv,
            "cwd": self._normalize(str(cwd)) if cwd else "",
            "status": status,
            "expect": step.expect,
            "probe": step.probe,
        }
        (out / "meta.json").write_text(json.dumps(meta, indent=2) + "\n", encoding="utf-8")
        shutil.copytree(self.crate_dir(step), out / "files", symlinks=True,
                        ignore=shutil.ignore_patterns("target", ".lake", "Cargo.lock"))

    # -- probes ---------------------------------------------------------------

    def _backup_durable(self, step: Step) -> Path:
        crate = self.crate_dir(step)
        backup = self.root / f".backup-{step.id}"
        backup.mkdir()
        for rel in (*DURABLE_PATHS, SPEC_LOCK):
            src = crate / rel
            if src.is_dir():
                shutil.copytree(src, backup / rel, symlinks=True)
            elif src.is_file():
                (backup / rel).parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(src, backup / rel)
        return backup

    def _restore_durable(self, step: Step, backup: Path) -> None:
        crate = self.crate_dir(step)
        for rel in (*DURABLE_PATHS, SPEC_LOCK):
            dest = crate / rel
            if dest.is_dir():
                shutil.rmtree(dest)
            elif dest.exists():
                dest.unlink()
            src = backup / rel
            if src.is_dir():
                shutil.copytree(src, dest, symlinks=True)
            elif src.is_file():
                dest.parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(src, dest)
        # Generated assembly reflects the probe's authored files; drop it so the
        # next step re-scaffolds from the restored state rather than from a
        # Verify module that imports a Specs or Assumptions file that no longer
        # exists.
        for rel in ("Obligations", "Verify"):
            shutil.rmtree(crate / ".anneal" / "generated" / rel, ignore_errors=True)
        shutil.rmtree(backup)


def check_crate_delta(step: Step) -> None:
    """Require the committed crate to equal `derive_from` plus the step's ops.

    This is what lets identical files exist in several chapter crates: a copy
    that drifts from the file the step says it comes from fails here, naming
    the file. The check reads only committed trees, so `lint` runs it too.
    """
    if step.derive_from is None:
        return
    expected = _durable_files(REPO / step.derive_from)
    for op in step.ops:
        if op.kind == "remove":
            if op.path not in expected:
                raise WorkflowError(f"step {step.id!r} removes {op.path}, which "
                                    f"{step.derive_from} does not contain")
            del expected[op.path]
        elif op.kind == "write":
            assert op.source is not None
            expected[op.path] = op.source.read_bytes()
        elif op.kind == "append":
            if op.path not in expected:
                raise WorkflowError(f"step {step.id!r} appends to {op.path}, which "
                                    f"{step.derive_from} does not contain")
            expected[op.path] += (op.text or "").encode("utf-8")
    actual = _durable_files(REPO / step.crate)
    differences = []
    for rel in sorted(set(expected) | set(actual)):
        if rel not in actual:
            differences.append(f"{step.derive_from} + edits has {rel}; {step.crate} lacks it")
        elif rel not in expected:
            differences.append(f"{step.crate} has {rel}, which neither {step.derive_from} "
                               f"nor the step's edits produce")
        elif expected[rel] != actual[rel]:
            differences.append(f"{rel} differs between {step.crate} and "
                               f"{step.derive_from} + edits")
    if differences:
        raise WorkflowError(
            f"step {step.id!r}: {step.crate} is not {step.derive_from} plus the edits "
            f"tutor.toml declares:\n" + "\n".join(f"  - {d}" for d in differences))


def _durable_files(crate: Path) -> dict[str, bytes]:
    files: dict[str, bytes] = {}
    for rel in DURABLE_PATHS:
        files.update(_file_map(crate / rel, rel))
    return files


def _file_map(path: Path, rel: str) -> dict[str, bytes]:
    if path.is_file():
        return {rel: path.read_bytes()}
    if not path.is_dir():
        return {}
    return {f"{rel}/{p.relative_to(path).as_posix()}": p.read_bytes()
            for p in sorted(path.rglob("*")) if p.is_file()}


def _tail(text: str, lines: int = 40) -> str:
    parts = text.splitlines()
    if len(parts) > lines:
        parts = ["..."] + parts[-lines:]
    return "\n".join(parts)


def load_records(steps: list[Step], artifacts: Path) -> dict[str, StepRecord]:
    records = {}
    for step in steps:
        out = artifacts / step.id
        meta_path = out / "meta.json"
        if not meta_path.is_file():
            raise WorkflowError(f"no record for step {step.id!r} under {artifacts}; run the "
                                "workflow first")
        meta = json.loads(meta_path.read_text(encoding="utf-8"))
        records[step.id] = StepRecord(
            step=step,
            status=meta["status"],
            stdout=(out / "stdout.txt").read_text(encoding="utf-8"),
            stderr=(out / "stderr.txt").read_text(encoding="utf-8"),
            files=out / "files",
        )
    return records


# --------------------------------------------------------------------------
# Markdown directives
# --------------------------------------------------------------------------

@dataclasses.dataclass
class Fence:
    open_line: int  # index of the opening fence line
    close_line: int  # index of the closing fence line
    indent: str
    marker: str  # the backtick run, e.g. "```"
    info: str  # e.g. "bash"
    directive_line: int | None = None
    kind: str | None = None
    args: dict[str, str | bool] = dataclasses.field(default_factory=dict)

    @property
    def body(self) -> slice:
        return slice(self.open_line + 1, self.close_line)


def scan_fences(lines: list[str], where: str) -> list[Fence]:
    """Find every fenced block and attach the directive that precedes it."""
    fences: list[Fence] = []
    pending: tuple[int, str, dict] | None = None
    i = 0
    while i < len(lines):
        stripped = lines[i].strip()
        if stripped.startswith(DIRECTIVE_OPEN) and stripped.endswith(DIRECTIVE_CLOSE):
            kind, args = parse_directive(stripped, f"{where}:{i + 1}")
            pending = (i, kind, args)
            i += 1
            if i >= len(lines) or not lines[i].lstrip().startswith("```"):
                raise WorkflowError(f"{where}:{i}: a `<!-- tutor: ... -->` directive must be "
                                    "immediately followed by an opening ``` fence")
            continue
        if stripped.startswith("```"):
            indent = lines[i][: len(lines[i]) - len(lines[i].lstrip())]
            marker = stripped[: len(stripped) - len(stripped.lstrip("`"))]
            info = stripped[len(marker):].strip()
            close = i + 1
            while close < len(lines):
                candidate = lines[close].strip()
                if candidate.startswith(marker) and candidate.strip("`") == "" \
                        and len(candidate) >= len(marker):
                    break
                close += 1
            if close >= len(lines):
                raise WorkflowError(f"{where}:{i + 1}: unterminated code fence")
            fence = Fence(i, close, indent, marker, info)
            if pending is not None:
                fence.directive_line, fence.kind, fence.args = pending
                pending = None
            fences.append(fence)
            i = close + 1
            continue
        i += 1
    return fences


def parse_directive(text: str, where: str) -> tuple[str, dict[str, str | bool]]:
    inner = text[len(DIRECTIVE_OPEN): -len(DIRECTIVE_CLOSE)].strip()
    try:
        tokens = shlex.split(inner)
    except ValueError as error:
        raise WorkflowError(f"{where}: cannot parse directive: {error}") from error
    if not tokens or tokens[0] not in KINDS:
        raise WorkflowError(f"{where}: directive must start with one of {sorted(KINDS)}")
    kind = tokens[0]
    args: dict[str, str | bool] = {}
    for token in tokens[1:]:
        key, sep, value = token.partition("=")
        if key in args:
            raise WorkflowError(f"{where}: duplicate directive argument {key!r}")
        args[key] = value if sep else True
    unknown = sorted(set(args) - BLOCK_ARGS[kind])
    if unknown:
        raise WorkflowError(f"{where}: `{kind}` does not accept {unknown}; "
                            f"allowed: {sorted(BLOCK_ARGS[kind])}")
    if kind != "static" and not isinstance(args.get("step"), str):
        raise WorkflowError(f"{where}: `{kind}` needs step=<id>")
    if kind == "file" and not isinstance(args.get("path"), str):
        raise WorkflowError(f"{where}: `file` needs path=<crate-relative path>")
    if kind == "file" and "item" in args and "items" in args:
        raise WorkflowError(f"{where}: use either item= or items=, not both")
    if "," in str(args.get("step", "")) and kind != "command":
        raise WorkflowError(f"{where}: only `command` accepts several steps")
    return kind, args


def chapter_files() -> list[Path]:
    return sorted(DOCS_DIR.glob(CHAPTER_GLOB))


def lint_docs(steps: list[Step]) -> list[tuple[Path, list[str], list[Fence]]]:
    """Validate directives and coverage; return each chapter's lines and fences."""
    by_id = {s.id: s for s in steps}
    result = []
    for doc in chapter_files():
        where = doc.relative_to(REPO).as_posix()
        lines = doc.read_text(encoding="utf-8").split("\n")
        fences = scan_fences(lines, where)
        for fence in fences:
            line_no = fence.open_line + 1
            if fence.kind is None:
                if looks_generated(lines[fence.body]):
                    raise WorkflowError(
                        f"{where}:{line_no}: this block quotes a command, report, or error "
                        "but no `<!-- tutor: ... -->` directive generates it (use "
                        "`<!-- tutor: static -->` to exempt it deliberately)")
                continue
            if fence.kind == "static":
                continue
            step_ids = str(fence.args["step"]).split(",")
            for step_id in step_ids:
                if step_id not in by_id:
                    raise WorkflowError(f"{where}:{line_no}: unknown step {step_id!r}")
                if fence.kind in ("command", "report", "errors", "stdout", "stderr") \
                        and by_id[step_id].run is None:
                    raise WorkflowError(f"{where}:{line_no}: step {step_id!r} runs no command")
                if fence.kind == "rm" and not any(op.kind == "remove"
                                                  for op in by_id[step_id].ops):
                    raise WorkflowError(f"{where}:{line_no}: step {step_id!r} removes nothing")
            if len({by_id[s].crate for s in step_ids}) > 1:
                raise WorkflowError(f"{where}:{line_no}: a command block must not mix steps "
                                    "that run in different crates")
        result.append((doc, lines, fences))
    return result


def looks_generated(body: list[str]) -> bool:
    for raw in body:
        line = raw.strip()
        if line.startswith(("cargo anneal ", "cargo run -p cargo-anneal", "cargo-anneal ",
                            "rm ", "error:", "cargo-anneal error:", "FAIL ")):
            return True
        if REPORT_HEADER.match(line):
            return True
    return False


# --------------------------------------------------------------------------
# Rendering
# --------------------------------------------------------------------------

def render_fence(fence: Fence, records: dict[str, StepRecord], where: str) -> list[str]:
    kind, args = fence.kind, fence.args
    step_ids = str(args.get("step", "")).split(",") if kind != "static" else []
    recs = [records[s] for s in step_ids]
    if kind == "command":
        body = render_command([r.step for r in recs])
    elif kind == "report":
        body = extract_report(recs[0].stdout, where)
    elif kind == "errors":
        body = extract_errors(recs[0].stdout, recs[0].stderr, where)
    elif kind == "stdout":
        body = recs[0].stdout.rstrip("\n").split("\n")
    elif kind == "stderr":
        body = recs[0].stderr.rstrip("\n").split("\n")
    elif kind == "file":
        body = render_file(recs[0], args, where)
    elif kind == "rm":
        body = [f"rm {op.path}" for op in recs[0].step.ops if op.kind == "remove"]
    else:
        raise AssertionError(kind)
    body = [line.rstrip() for line in body]
    for line in body:
        if line.lstrip().startswith(fence.marker):
            raise WorkflowError(f"{where}: rendered content contains a {fence.marker} line; "
                                "use a longer fence for this block")
    return [fence.indent + line if line else "" for line in body]


def render_command(steps: list[Step]) -> list[str]:
    crate = steps[0].crate
    flavour_a = [f"cargo run -p cargo-anneal -- {s.display_args()}" for s in steps]
    flavour_b = [f"cargo anneal {s.display_args()}" for s in steps]
    if len(steps) == 1:
        in_crate = f"`cd {crate} && cargo anneal {' '.join(steps[0].run or ())}`"
        comment = f"# Flavour B — Using installed `cargo anneal` (or {in_crate}):"
    else:
        comment = ("# Flavour B — Using installed `cargo anneal` (or the same subcommands "
                   f"inside `{crate}/`):")
    return ["# Flavour A — Inside an Anneal checkout:", *flavour_a, "", comment, *flavour_b]


def extract_report(stdout: str, where: str) -> list[str]:
    lines = stdout.split("\n")
    for index, line in enumerate(lines):
        if REPORT_HEADER.match(line):
            end = index + 1
            while end < len(lines) and lines[end].startswith("  "):
                end += 1
            return lines[index:end]
    raise WorkflowError(f"{where}: the step printed no `Anneal ... Summary:` report")


def extract_errors(stdout: str, stderr: str, where: str) -> list[str]:
    """Collect the diagnostics of a failing step.

    Lake prints Lean errors on stdout between progress lines; `cargo-anneal`
    prints its own `error:` lines on stderr after `cargo check` chatter. The
    result keeps every `error:` message and its continuation lines in order,
    first from stdout and then from stderr.
    """
    out: list[str] = []
    lines = stdout.split("\n")
    i = 0
    while i < len(lines):
        if lines[i].startswith("error:"):
            out.append(lines[i])
            i += 1
            while i < len(lines) and lines[i].strip() and not lines[i].startswith("error:") \
                    and not lines[i].startswith(LAKE_NOISE_PREFIXES) \
                    and not lines[i].startswith("- "):
                out.append(lines[i])
                i += 1
            continue
        i += 1
    err_lines = stderr.split("\n")
    start = next((k for k, line in enumerate(err_lines)
                  if line.startswith(("error", "cargo-anneal error:"))), None)
    if start is not None:
        out.extend(line for line in err_lines[start:]
                   if line.strip() and not CARGO_NOISE.match(line)
                   and not line.startswith("info:"))
    if not out:
        raise WorkflowError(f"{where}: the step printed no error diagnostics")
    return out


def render_file(record: StepRecord, args: dict, where: str) -> list[str]:
    rel = str(args["path"])
    path = record.files / rel
    if not path.is_file():
        raise WorkflowError(f"{where}: {rel} does not exist after step {record.step.id!r}")
    text = path.read_text(encoding="utf-8")
    if args.get("strip_module_doc"):
        text = strip_lean_module_doc(text)
    names = args.get("item") or args.get("items")
    if names:
        text = extract_rust_items(text, str(names).split(","), bool(args.get("docs")), where)
    return text.rstrip("\n").split("\n")


def strip_lean_module_doc(text: str) -> str:
    """Remove `/-! ... -/` module docs, which generated modules repeat verbatim."""
    out = []
    pos = 0
    while True:
        start = text.find("/-!", pos)
        if start < 0:
            out.append(text[pos:])
            break
        end = text.find("-/", start + 3)
        if end < 0:
            out.append(text[pos:])
            break
        out.append(text[pos:start])
        pos = end + 2
    return re.sub(r"\n{3,}", "\n\n", "".join(out)).lstrip("\n")


RUST_QUALIFIERS = ("pub(crate) ", "pub ", "const ", "unsafe ", "async ", "extern \"C\" ")
RUST_ITEM_KEYWORDS = ("fn", "struct", "enum", "trait", "type", "union", "mod", "const",
                      "static")


def extract_rust_items(text: str, names: list[str], docs: bool, where: str) -> str:
    """Cut the named items (with their attributes) out of a Rust source file.

    A name that is a bare identifier matches the item that declares it; a name
    containing spaces matches the first line whose text starts with it (for
    `impl` blocks such as `unsafe impl WireHeader for FrameLen`). Doc comments
    are dropped unless `docs` is set, because the chapters quote items to show
    their contracts rather than their documentation.
    """
    lines = text.split("\n")
    pieces = []
    for name in names:
        header = _find_rust_item(lines, name.strip(), where)
        start = header
        in_attribute = False
        while start > 0:
            previous = lines[start - 1].strip()
            if in_attribute:
                start -= 1
                if previous.startswith("#["):
                    in_attribute = False
            elif previous.startswith("#["):
                start -= 1
            elif previous.endswith("]") and not previous.startswith("//"):
                start -= 1
                in_attribute = True
            elif previous.startswith("///"):
                if not docs:
                    break
                start -= 1
            else:
                break
        end = header
        if not lines[header].rstrip().endswith(";"):
            depth = 0
            opened = False
            for end in range(header, len(lines)):
                depth += lines[end].count("{") - lines[end].count("}")
                opened = opened or "{" in lines[end]
                if opened and depth == 0:
                    break
            else:
                raise WorkflowError(f"{where}: unbalanced braces after item {name!r}")
        pieces.append("\n".join(lines[start:end + 1]))
    return "\n\n".join(pieces)


def _find_rust_item(lines: list[str], name: str, where: str) -> int:
    for index, raw in enumerate(lines):
        line = raw.strip()
        if " " in name:
            if line.startswith(name):
                return index
            continue
        changed = True
        while changed:
            changed = False
            for qualifier in RUST_QUALIFIERS:
                if line.startswith(qualifier):
                    line = line[len(qualifier):]
                    changed = True
        for keyword in RUST_ITEM_KEYWORDS:
            prefix = f"{keyword} {name}"
            if line.startswith(prefix):
                rest = line[len(prefix):]
                if not rest or not (rest[0].isalnum() or rest[0] == "_"):
                    return index
    raise WorkflowError(f"{where}: no Rust item named {name!r} in the snapshot")


def render_docs(steps: list[Step], records: dict[str, StepRecord]) -> dict[Path, str]:
    """Return the rendered text of every chapter, keyed by path."""
    rendered = {}
    for doc, lines, fences in lint_docs(steps):
        where = doc.relative_to(REPO).as_posix()
        out = list(lines)
        # Replace from the bottom up so earlier line indices stay valid.
        for fence in sorted(fences, key=lambda f: f.open_line, reverse=True):
            if fence.kind is None or fence.kind == "static":
                continue
            body = render_fence(fence, records, f"{where}:{fence.open_line + 1}")
            out[fence.body] = body
        rendered[doc] = "\n".join(out)
    return rendered


# --------------------------------------------------------------------------
# Command line
# --------------------------------------------------------------------------

def ensure_binaries(args) -> Path:
    bin_dir = Path(args.bin_dir) if args.bin_dir else \
        Path(os.environ.get("CARGO_TARGET_DIR", REPO / "target")) / "debug"
    if not args.no_build:
        cmd = ["cargo", "build", "-p", "anneal-rustc-capture", "--bin", "anneal-rustc-capture",
               "-p", "cargo-anneal", "--bin", "cargo-anneal"]
        subprocess.run(cmd, cwd=REPO, check=True)
    cli = bin_dir / "cargo-anneal"
    wrapper = bin_dir / "anneal-rustc-capture"
    for binary in (cli, wrapper):
        if not binary.is_file():
            raise WorkflowError(f"missing {binary}; build with `cargo build -p "
                                "anneal-rustc-capture -p cargo-anneal` or pass --bin-dir")
    return cli


def run_workflow(args, steps: list[Step]) -> None:
    cli = ensure_binaries(args)
    artifacts = Path(args.artifacts).resolve()
    root = Path(tempfile.mkdtemp(prefix="anneal-tutor-"))
    runner = Runner(steps, cli, artifacts, root, log=lambda m: print(m, file=sys.stderr))
    try:
        runner.prepare()
        runner.run_all()
    except BaseException:
        print(f"workflow root kept for inspection: {root}", file=sys.stderr)
        raise
    if args.keep_root:
        print(f"workflow root: {root}", file=sys.stderr)
    else:
        shutil.rmtree(root, ignore_errors=True)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("command", choices=["lint", "run", "check", "render"])
    parser.add_argument("--artifacts", default=str(REPO / "target" / "tutor-workflow"),
                        help="directory for per-step records (default: target/tutor-workflow)")
    parser.add_argument("--reuse-artifacts", action="store_true",
                        help="render or check from existing records instead of re-running")
    parser.add_argument("--bin-dir", help="directory containing cargo-anneal and "
                        "anneal-rustc-capture (default: target/debug)")
    parser.add_argument("--no-build", action="store_true",
                        help="do not run `cargo build` for the CLI binaries first")
    parser.add_argument("--keep-root", action="store_true",
                        help="keep the temporary checkout mirror after a successful run")
    args = parser.parse_args(argv)

    try:
        steps = load_workflow()
        if args.command != "run":
            # Fail on directive and crate-delta problems before spending
            # minutes on Lake.
            for step in steps:
                check_crate_delta(step)
            lint_docs(steps)
        if args.command == "lint":
            crates = len({s.crate for s in steps})
            print(f"ok: {len(steps)} steps over {crates} crates, {len(chapter_files())} chapters")
            return 0
        if args.command == "run" or not args.reuse_artifacts:
            run_workflow(args, steps)
            if args.command == "run":
                print(f"ok: records written to {args.artifacts}")
                return 0
        records = load_records(steps, Path(args.artifacts).resolve())
        rendered = render_docs(steps, records)
        stale = []
        for doc, text in rendered.items():
            current = doc.read_text(encoding="utf-8")
            if current == text:
                continue
            stale.append(doc)
            if args.command == "render":
                doc.write_text(text, encoding="utf-8")
                print(f"updated {doc.relative_to(REPO).as_posix()}")
            else:
                rel = doc.relative_to(REPO).as_posix()
                sys.stdout.writelines(difflib.unified_diff(
                    current.splitlines(keepends=True), text.splitlines(keepends=True),
                    fromfile=f"{rel} (committed)", tofile=f"{rel} (rendered)"))
        if args.command == "check" and stale:
            names = ", ".join(d.relative_to(REPO).as_posix() for d in stale)
            print(f"\nerror: {names} no longer match the tutor workflow; run\n"
                  f"  python3 {Path(__file__).relative_to(REPO).as_posix()} render\n"
                  "and review the diff", file=sys.stderr)
            return 1
        if not stale:
            print("ok: docs/tutor chapters match the tutor workflow")
        return 0
    except WorkflowError as error:
        print(f"error: {error}", file=sys.stderr)
        return 1
    except subprocess.CalledProcessError as error:
        print(f"error: {' '.join(map(str, error.cmd))} failed with status {error.returncode}",
              file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
