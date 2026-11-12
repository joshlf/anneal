# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Exercise static gates and the release workflow's authority boundaries."""

import os
from pathlib import Path
import shutil
import shlex
import subprocess
import sys
import tempfile
import textwrap
import unittest

from workflow_yaml import load_workflow_yaml


SOURCE = Path(__file__).resolve().parent


class CheckScriptFixture(unittest.TestCase):
    def setUp(self):
        directory = tempfile.TemporaryDirectory(prefix="anneal-check-scripts-")
        self.addCleanup(directory.cleanup)
        self.root = Path(directory.name)
        (self.root / "ci").mkdir()
        for name in (
            "check_non_stable_version.sh",
            "check_workflow_dependencies.py",
            "workflow_yaml.py",
        ):
            shutil.copyfile(SOURCE / name, self.root / "ci" / name)
        self.workflows = self.root / ".github/workflows"
        self.workflows.mkdir(parents=True)
        self.manifest = self.root / "trusted/cargo-anneal/Cargo.toml"
        self.manifest.parent.mkdir(parents=True)

    def run_check(self, name):
        environment = {
            "PATH": os.environ["PATH"],
            "HOME": str(self.root),
            "GITHUB_STEP_SUMMARY": str(self.root / "step-summary"),
        }
        return subprocess.run(
            ([sys.executable, "-B"] if name.endswith(".py") else ["bash"])
            + [str(self.root / "ci" / name)],
            cwd=self.root,
            env=environment,
            capture_output=True,
            text=True,
            timeout=15,
        )

    def assert_accepted(self, result):
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def assert_rejected(self, result, message=None):
        self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertTrue(result.stderr.strip(), "rejection needs a diagnostic")
        if message is not None:
            self.assertIn(message, result.stderr)


class PrereleaseVersionTests(CheckScriptFixture):
    def check_manifest(self, text):
        self.manifest.write_text(text, encoding="utf-8")
        return self.run_check("check_non_stable_version.sh")

    def test_accepts_prerelease_versions(self):
        for version in ("0.1.0-alpha.1", "1.2.3-rc.2", "10.20.30-dev"):
            with self.subTest(version=version):
                result = self.check_manifest(
                    f'[package]\nversion = "{version}"\n'
                )
                self.assert_accepted(result)
                self.assertIn(version, result.stdout)

    def test_rejects_stable_and_non_version_values(self):
        for version in ("0.1.0", "1.0.0", "not-a-version"):
            with self.subTest(version=version):
                result = self.check_manifest(
                    f'[package]\nversion = "{version}"\n'
                )
                self.assert_rejected(result, "not a pre-release version")

    def test_rejects_missing_package_version(self):
        for text in (
            "",
            "[package]\nname = 'fixture'\n",
            "[package]\nversion = ''\n",
        ):
            with self.subTest(manifest=text):
                self.assert_rejected(
                    self.check_manifest(text),
                    "does not specify package.version",
                )

    def test_rejects_missing_and_malformed_manifest(self):
        self.assert_rejected(
            self.run_check("check_non_stable_version.sh"), "Error reading"
        )
        self.assert_rejected(self.check_manifest("[package\n"), "Error reading")


class WorkflowDependencyTests(CheckScriptFixture):
    # GitHub accepts scalar, sequence, and mapping event declarations, and
    # either a scalar or sequence of prerequisite jobs:
    # https://docs.github.com/en/actions/reference/workflows-and-actions/workflow-syntax#on
    # https://docs.github.com/en/actions/reference/workflows-and-actions/workflow-syntax#jobsjob_idneeds
    PR_EVENTS = (
        "on: pull_request",
        "on: [push, pull_request]",
        "on:\n  push:\n  pull_request:",
        "'on':\n  pull_request:\n    branches: [main]",
    )

    def write_workflow(self, trigger, needs="[build, test]", gate=True,
                       jobs=("build", "test"), filename="fixture.yml"):
        content = trigger + "\njobs:\n"
        for job in jobs:
            content += textwrap.indent(
                f"{job}:\n  runs-on: ubuntu-latest\n"
                "  steps:\n    - run: 'true'\n",
                "  ",
            )
        if gate:
            content += "  all-jobs-succeed:\n"
            if needs is not None:
                content += f"    needs: {needs}\n"
            content += (
                "    runs-on: ubuntu-latest\n"
                "    steps:\n      - run: 'true'\n"
            )
        (self.workflows / filename).write_text(content, encoding="utf-8")

    def check(self):
        return self.run_check("check_workflow_dependencies.py")

    def test_accepts_complete_gate_for_every_event_form(self):
        for trigger in self.PR_EVENTS:
            with self.subTest(trigger=trigger):
                self.write_workflow(trigger)
                self.assert_accepted(self.check())

    def test_accepts_scalar_needs_for_one_prerequisite(self):
        self.write_workflow(
            "on:\n  pull_request:", needs="build", jobs=("build",)
        )
        self.assert_accepted(self.check())

    def test_rejects_missing_gate_for_every_event_form(self):
        for trigger in self.PR_EVENTS:
            with self.subTest(trigger=trigger):
                self.write_workflow(trigger, gate=False)
                self.assert_rejected(self.check(), "all-jobs-succeed")

    def test_rejects_incomplete_or_absent_needs(self):
        for needs in ("[build]", "[]", None):
            with self.subTest(needs=needs):
                self.write_workflow("on:\n  pull_request:", needs=needs)
                self.assert_rejected(self.check(), "test")

    def test_rejects_malformed_event_and_needs_containers(self):
        for trigger in ("on: [[pull_request]]", "on: [pull_request, {}]"):
            with self.subTest(trigger=trigger):
                self.write_workflow(trigger)
                self.assert_rejected(self.check(), "on")
        for needs in ("{}", "[[build], test]"):
            with self.subTest(needs=needs):
                self.write_workflow("on: pull_request", needs=needs)
                self.assert_rejected(self.check(), "needs")

    def test_checks_both_workflow_extensions(self):
        self.write_workflow("on:\n  pull_request:")
        self.write_workflow(
            "on:\n  pull_request:", gate=False, filename="other.yaml"
        )
        self.assert_rejected(self.check(), "other.yaml")

    def test_does_not_require_pr_gate_for_other_events(self):
        for trigger in (
            "on: push", "on: [push, workflow_dispatch]", "on:\n  push:"
        ):
            with self.subTest(trigger=trigger):
                self.write_workflow(trigger, gate=False)
                self.assert_accepted(self.check())

    def test_accepts_no_workflow_files(self):
        self.assert_accepted(self.check())

    def test_rejects_malformed_yaml(self):
        (self.workflows / "fixture.yml").write_text(
            "on: [\njobs:\n", encoding="utf-8"
        )
        self.assert_rejected(self.check())

    def test_rejects_invalid_workflow_encoding(self):
        (self.workflows / "fixture.yml").write_bytes(b"on: pull_request\n\xff")
        self.assert_rejected(self.check())

    def test_rejects_malformed_workflow_shapes(self):
        for content in (
            "[]\n",
            "on: [[pull_request]]\njobs: {}\n",
            "on: [pull_request, {}]\njobs: {}\n",
            "on: {}\njobs: {}\n",
            "jobs: {}\n",
            "on:\n  pull_request:\njobs: []\n",
            "on:\n  pull_request:\njobs: null\n",
        ):
            with self.subTest(workflow=content):
                (self.workflows / "fixture.yml").write_text(
                    content, encoding="utf-8"
                )
                self.assert_rejected(self.check())

    def test_rejects_duplicate_keys_and_multiple_documents(self):
        for content in (
            "on: push\non: pull_request\njobs: {}\n",
            "on: pull_request\njobs: {}\njobs: {}\n",
            "on: push\njobs: {}\n---\non: pull_request\njobs: {}\n",
        ):
            with self.subTest(workflow=content):
                (self.workflows / "fixture.yml").write_text(
                    content, encoding="utf-8"
                )
                self.assert_rejected(self.check())

    def test_accepts_aliased_events_and_dependencies(self):
        self.write_workflow(
            "run-name: &event pull_request\non: *event",
            needs="*dependency", jobs=("build",),
        )
        path = self.workflows / "fixture.yml"
        path.write_text(path.read_text().replace(
            "  build:\n", "  build:\n    name: &dependency build\n"
        ))
        self.assert_accepted(self.check())

    def test_preserves_names_that_yaml_11_treats_as_booleans_or_null(self):
        self.write_workflow(
            "on: pull_request", needs="[on, yes, null]",
            jobs=("on", "yes", "null"),
        )
        self.assert_accepted(self.check())

    def test_rejects_nonscalar_merge_and_recursive_yaml_keys(self):
        for content, message in (
            ("? [one, two]\n: value\non: push\n", "keys must be scalars"),
            ("on: push\n<<: {jobs: {}}\n", "merge keys"),
            ("on: push\n'<<': {jobs: {}}\n", "merge keys"),
            ("on: &events [*events]\n", "recursive node"),
            ("on: &events {pull_request: *events}\n", "recursive node"),
        ):
            with self.subTest(content=content):
                (self.workflows / "fixture.yml").write_text(content)
                result = self.check()
                self.assert_rejected(result, message)
                self.assertNotIn("Traceback", result.stderr)

    def test_reports_missing_job_in_workflow_summary(self):
        self.write_workflow("on:\n  pull_request:", needs="[build]")
        result = self.check()
        self.assert_rejected(result, "test")
        self.assertEqual(
            (self.root / "step-summary").read_text(encoding="utf-8"),
            result.stderr,
        )


class ReleaseWorkflowTests(unittest.TestCase):
    # These checks guard the known release roles and data handoff. They do
    # not classify arbitrary shell commands or establish artifact correctness.
    RELEASE_FILES = {
        "Cargo.lock",
        "trusted/cargo-anneal/Cargo.toml",
        "trusted/root-manifest.sha256",
    }

    def setUp(self):
        self.jobs = load_workflow_yaml(
            (SOURCE.parent / ".github/workflows/release.yml").read_text()
        )["jobs"]

    def test_known_helpers_run_without_write_or_oidc_authority(self):
        helpers = {
            "ci/check_non_stable_version.sh",
            "ci/probe_toolchain.sh",
            "ci/update_root_manifest.py",
        }
        seen = set()
        for name, job in self.jobs.items():
            for step in job.get("steps", []):
                used = {path for path in helpers if path in step.get("run", "")}
                if used:
                    self.assertEqual(job["permissions"], {"contents": "read"}, name)
                    seen.update(used)
        self.assertEqual(seen, helpers)

    def test_publishers_require_successful_read_only_producers(self):
        prerequisites = {
            "release": {"check-version", "validate-cli-release"},
            "publish-artifacts": {"create-release", "build-artifacts"},
            "finalize-release": {"create-release", "publish-artifacts"},
            "prepare-release-pr": {"create-release", "finalize-release"},
            "open-release-pr": {"create-release", "prepare-release-pr"},
        }
        for name, needs in prerequisites.items():
            job = self.jobs[name]
            self.assertEqual(set(job["needs"]), needs, name)
            self.assertNotIn("always(", job.get("if", ""), name)
            self.assertNotIn("continue-on-error", job, name)
            for step in job["steps"]:
                self.assertNotIn("continue-on-error", step, name)
                self.assertNotIn("always(", step.get("if", ""), name)
        for name in ("release", "publish-artifacts", "finalize-release", "open-release-pr"):
            self.assertEqual(self.jobs[name]["runs-on"], "ubuntu-latest", name)
        self.assertIs(
            self.jobs["build-artifacts"]["strategy"]["matrix"],
            self.jobs["publish-artifacts"]["strategy"]["matrix"],
        )

    def test_validation_and_publication_keep_their_source_and_checks(self):
        for name, revision in {
            "validate-cli-release": "${{ github.sha }}",
            "release": "${{ github.sha }}",
            "prepare-release-pr": "${{ needs.create-release.outputs.base_sha }}",
            "open-release-pr": "${{ needs.create-release.outputs.base_sha }}",
        }.items():
            checkouts = [step for step in self.jobs[name]["steps"]
                         if step.get("uses", "").startswith("actions/checkout@")]
            self.assertEqual(len(checkouts), 1, name)
            self.assertEqual(checkouts[0]["with"]["ref"], revision, name)
            self.assertEqual(checkouts[0]["with"]["persist-credentials"], "false", name)
        restore = next(step for step in self.jobs["open-release-pr"]["steps"]
                       if step["name"] == "Restore prepared release files")
        self.assertEqual(restore["env"]["RELEASE_CHECKOUT"], "${{ github.workspace }}")
        self.assertEqual(self.jobs["release"]["environment"], "release")
        publisher = "\n".join(step.get("run", "") for step in self.jobs["release"]["steps"])
        self.assertIn("cargo publish -p cargo-anneal --registry crates-io\n", publisher)
        self.assertNotIn("--no-verify", publisher)
        preparation = "\n".join(step.get("run", "") for step in self.jobs["prepare-release-pr"]["steps"])
        self.assertIn("cargo publish --dry-run -p cargo-anneal --allow-dirty\n", preparation)
        self.assertNotIn("--no-verify", preparation)
        for name in ("publish-artifacts", "finalize-release"):
            self.assertFalse(any(step.get("uses", "").startswith("actions/checkout@")
                                 for step in self.jobs[name]["steps"]), name)

    def test_prepared_release_handoff_copies_only_regular_known_files(self):
        prepare = self.jobs["prepare-release-pr"]["steps"]
        handoff = next(step for step in prepare if step.get("uses", "").startswith("actions/upload-artifact@"))
        opener = self.jobs["open-release-pr"]["steps"]
        creator = next(step for step in opener if step.get("uses", "").startswith("peter-evans/create-pull-request@"))
        self.assertEqual(set(handoff["with"]["path"].splitlines()), self.RELEASE_FILES)
        self.assertEqual(set(creator["with"]["add-paths"].splitlines()), self.RELEASE_FILES)
        self.assertEqual(handoff["with"]["if-no-files-found"], "error")
        restore_index = next(index for index, step in enumerate(opener)
                             if step["name"] == "Restore prepared release files")
        self.assertEqual(opener[restore_index + 1:], [creator])
        restore = opener[restore_index]["run"]
        cases = [
            ("source", "regular", ""),
            ("source", "leaf-link", "Cargo.lock"),
            ("source", "leaf-link", "trusted/root-manifest.sha256"),
            ("source", "parent-link", "trusted"),
            ("source", "directory", "Cargo.lock"),
            ("source", "fifo", "Cargo.lock"),
            ("source", "root-link", ""),
            ("destination", "parent-link", "trusted"),
            ("destination", "parent-link", "trusted/cargo-anneal"),
            ("destination", "root-link", ""),
            ("destination", "missing", "trusted/root-manifest.sha256"),
            ("destination", "directory", "trusted/root-manifest.sha256"),
            ("destination", "fifo", "trusted/root-manifest.sha256"),
            ("destination", "nondirectory", "trusted"),
        ]
        cases.extend(("destination", "leaf-link", path)
                     for path in sorted(self.RELEASE_FILES))
        # A late invalid path must fail before even an earlier valid path is
        # copied. Destination links matter independently of artifact links:
        # cp would otherwise follow checkout paths into Git state or outside
        # the checkout. These fixtures assume stable trees, as the job does.
        for location, kind, subject in cases:
            with self.subTest(location=location, kind=kind, path=subject), tempfile.TemporaryDirectory(prefix="anneal-release-restore-") as directory:
                root = Path(directory)
                source, target = root / "prepared", root / "checkout"
                for path in self.RELEASE_FILES:
                    for base, contents in ((source, "prepared"), (target, "original")):
                        file = base / path
                        file.parent.mkdir(parents=True, exist_ok=True)
                        file.write_text(contents + path)
                        file.chmod(0o700 if base == source else 0o640)
                (source / "unrequested-code.sh").write_text("exit 99\n")
                outside = root / "outside-data"
                outside.write_text("outside checkout")
                git_config = target / ".git/config"
                git_config.parent.mkdir()
                git_config.write_text("original Git configuration")
                node = (source if location == "source" else target) / subject
                if kind == "leaf-link":
                    node.unlink()
                    referent = git_config if subject == "trusted/root-manifest.sha256" else outside
                    node.symlink_to(referent)
                elif kind in ("parent-link", "root-link"):
                    node.rename(root / "outside-tree")
                    node.symlink_to(root / "outside-tree", target_is_directory=True)
                elif kind in ("directory", "fifo", "missing"):
                    node.unlink()
                    if kind == "directory":
                        node.mkdir()
                    elif kind == "fifo":
                        os.mkfifo(node)
                elif kind == "nondirectory":
                    shutil.rmtree(node)
                    node.write_text("not a directory")
                # Save regular-file bytes after installing the malformed
                # layout. Rejection must preserve both checkout data and any
                # external referent; no real hooks or credentials are needed.
                original_files = {file: file.read_bytes()
                                  for file in root.rglob("*")
                                  if file.is_file() and not file.is_symlink()}
                # The spy prevents a broken guard from blocking on the FIFO.
                # Rejected inputs must stop before invoking any copy at all.
                tools = root / "tools"
                tools.mkdir()
                copier = tools / "cp"
                copier.write_text(
                    '#!/bin/sh\nprintf invoked >> "$COPY_LOG"\n'
                    'if [ "$COPY_ALLOWED" != true ]; then exit 99; fi\n'
                    + "exec " + shlex.quote(shutil.which("cp")) + ' "$@"\n'
                )
                copier.chmod(0o700)
                copy_log = root / "copy.log"
                result = subprocess.run(
                    ["bash", "--noprofile", "--norc", "-e", "-o", "pipefail", "-c", restore],
                    cwd=target,
                    env={"PATH": str(tools) + os.pathsep + os.environ["PATH"],
                         "PREPARED_RELEASE": str(source), "RELEASE_CHECKOUT": str(target),
                         "COPY_LOG": str(copy_log),
                         "COPY_ALLOWED": "true" if kind == "regular" else "false"},
                    capture_output=True, text=True, timeout=15,
                )
                self.assertEqual(result.returncode == 0, kind == "regular", result.stderr)
                if kind == "regular":
                    for path in self.RELEASE_FILES:
                        self.assertEqual((target / path).read_text(), "prepared" + path)
                        self.assertEqual((target / path).stat().st_mode & 0o777, 0o640)
                    self.assertFalse((target / "unrequested-code.sh").exists())
                else:
                    self.assertFalse(copy_log.exists(), "invalid input reached cp")
                    for file, contents in original_files.items():
                        self.assertEqual(file.read_bytes(), contents, str(file))
                self.assertEqual(outside.read_text(), "outside checkout")
                self.assertEqual(git_config.read_text(), "original Git configuration")


if __name__ == "__main__":
    unittest.main()
