# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Exercise fail-closed root override checks in .github/workflows/ci.yml."""

import hashlib
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

from workflow_yaml import load_workflow_yaml


SOURCE = Path(__file__).resolve().parent


class CiWorkflowManifestGuardTests(unittest.TestCase):
    def setUp(self):
        workflow = load_workflow_yaml(
            (SOURCE.parent / ".github/workflows/ci.yml").read_text()
        )
        self.manifest_steps = {}
        for job_name in ("build-exocrate", "test-and-verify"):
            steps = workflow["jobs"][job_name]["steps"]
            matches = [
                step["run"]
                for step in steps
                if step.get("name") == "Verify root TCB manifest"
            ]
            self.assertEqual(len(matches), 1, job_name)
            self.manifest_steps[job_name] = matches[0]

    def run_manifest_step(self, job_name, mutate=None):
        with tempfile.TemporaryDirectory(prefix="anneal-ci-guard-") as tmp:
            root = Path(tmp) / "repo"
            root.mkdir()
            diag = Path(tmp) / "diag"
            diag.mkdir()
            github_env = Path(tmp) / "github_env"
            github_env.write_text("")

            (root / "trusted").mkdir()
            cargo_toml = root / "Cargo.toml"
            cargo_toml.write_bytes(b"[workspace]\n")
            digest = hashlib.sha256(cargo_toml.read_bytes()).hexdigest()
            (root / "trusted/root-manifest.sha256").write_text(
                f"{digest}  Cargo.toml\n"
            )

            subprocess.run(
                ["git", "-c", "core.hooksPath=/dev/null",
                 "-c", "core.fsmonitor=false", "init", "-q"],
                cwd=root,
                check=True,
            )
            subprocess.run(
                ["git", "config", "user.email", "test@example.com"],
                cwd=root,
                check=True,
            )
            subprocess.run(
                ["git", "config", "user.name", "Test"],
                cwd=root,
                check=True,
            )
            subprocess.run(
                ["git", "-c", "core.hooksPath=/dev/null",
                 "-c", "core.fsmonitor=false",
                 "add", "Cargo.toml", "trusted/root-manifest.sha256"],
                cwd=root,
                check=True,
            )
            subprocess.run(
                ["git", "-c", "core.hooksPath=/dev/null",
                 "-c", "core.fsmonitor=false", "commit", "-qm", "init"],
                cwd=root,
                check=True,
            )

            if mutate is not None:
                mutate(root)

            env = os.environ.copy()
            env["ANNEAL_BUILD_DIAGNOSTICS"] = str(diag)
            env["ANNEAL_TEST_DIAGNOSTICS"] = str(diag)
            env["GITHUB_ENV"] = str(github_env)
            return subprocess.run(
                ["bash", "--noprofile", "--norc", "-eo", "pipefail", "-c",
                 self.manifest_steps[job_name]],
                cwd=root,
                env=env,
                capture_output=True,
                text=True,
            )

    def test_clean_tree_passes_manifest_guard(self):
        for job_name in self.manifest_steps:
            with self.subTest(job=job_name):
                res = self.run_manifest_step(job_name)
                self.assertEqual(res.returncode, 0, res.stdout + res.stderr)

    def test_root_override_paths_and_symlinks_fail_closed(self):
        cases = [
            ("cargo_dir", lambda r: (r / ".cargo").mkdir()),
            ("cargo_file", lambda r: (r / ".cargo").write_text("")),
            ("rust_toolchain", lambda r: (r / "rust-toolchain").write_text("nightly\n")),
            ("rust_toolchain_toml", lambda r: (r / "rust-toolchain.toml").write_text("")),
            ("valid_symlink_cargo", lambda r: (r / ".cargo").symlink_to("Cargo.toml")),
            ("valid_symlink_toolchain", lambda r: (r / "rust-toolchain.toml").symlink_to("Cargo.toml")),
            ("dangling_symlink_cargo", lambda r: (r / ".cargo").symlink_to("missing")),
            ("dangling_symlink_toolchain", lambda r: (r / "rust-toolchain").symlink_to("missing")),
        ]
        for job_name in self.manifest_steps:
            for label, mutate in cases:
                with self.subTest(job=job_name, case=label):
                    res = self.run_manifest_step(job_name, mutate=mutate)
                    self.assertNotEqual(
                        res.returncode,
                        0,
                        f"{job_name} allowed forbidden root override {label}",
                    )
                    self.assertIn(
                        "forbidden root config override:",
                        res.stdout + res.stderr,
                        f"{job_name} failed for unexpected reason on {label}",
                    )


if __name__ == "__main__":
    unittest.main()
