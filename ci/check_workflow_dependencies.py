# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Require each PR workflow's aggregation gate to depend on every other job."""

import os
from pathlib import Path
import sys

import yaml

from workflow_yaml import load_workflow_yaml


GATE = "all-jobs-succeed"


class WorkflowError(ValueError):
    """The workflow cannot establish its required job dependencies."""


def named_values(value, description):
    if isinstance(value, str):
        values = [value]
    elif isinstance(value, list):
        values = value
    else:
        raise WorkflowError(f"{description} must be a name or list of names")
    if not all(isinstance(name, str) and name for name in values):
        raise WorkflowError(f"{description} contains an invalid name")
    return set(values)


def check_workflow(path):
    workflow = load_workflow_yaml(path.read_text(encoding="utf-8"))
    if not isinstance(workflow, dict):
        raise WorkflowError("expected a workflow mapping")
    # GitHub permits scalar, sequence, or mapping event declarations, and
    # scalar or sequence job prerequisites:
    # https://docs.github.com/en/actions/reference/workflows-and-actions/workflow-syntax#on
    # https://docs.github.com/en/actions/reference/workflows-and-actions/workflow-syntax#jobsjob_idneeds
    trigger = workflow.get("on")
    events = (
        set(trigger)
        if isinstance(trigger, dict)
        else named_values(trigger, "on")
    )
    if not events:
        raise WorkflowError("on must name at least one workflow event")
    if "pull_request" not in events:
        return

    jobs = workflow.get("jobs")
    if (not isinstance(jobs, dict) or not jobs
            or not all(isinstance(job, dict) for job in jobs.values())):
        raise WorkflowError("jobs must map job names to job definitions")
    gate = jobs.get(GATE)
    if gate is None:
        raise WorkflowError(f"missing {GATE} gate")
    needs = named_values(gate.get("needs", []), f"{GATE}.needs")
    # The required gate sees results only for its declared prerequisites. A
    # job omitted here could fail without changing the branch-protection
    # result, even when the gate checks every result it receives.
    missing = sorted(set(jobs) - {GATE} - needs)
    if missing:
        raise WorkflowError(
            f"{GATE} missing dependencies on some jobs: {' '.join(missing)}"
        )


def main():
    root = Path(__file__).resolve().parent.parent
    directory = root / ".github/workflows"
    workflows = sorted([*directory.glob("*.yml"), *directory.glob("*.yaml")])
    errors = []
    for path in workflows:
        try:
            check_workflow(path)
        except (OSError, UnicodeError, yaml.YAMLError, WorkflowError) as error:
            errors.append(f"{path.relative_to(root)}: {error}")
    if not errors:
        return 0
    message = "\n".join(errors) + "\n"
    sys.stderr.write(message)
    summary = os.environ.get("GITHUB_STEP_SUMMARY")
    if summary:
        try:
            with open(summary, "a", encoding="utf-8") as destination:
                destination.write(message)
        except OSError as error:
            print(
                f"cannot append workflow check summary: {error}",
                file=sys.stderr,
            )
    return 1


if __name__ == "__main__":
    sys.exit(main())
