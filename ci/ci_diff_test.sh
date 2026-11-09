#!/usr/bin/env bash
# Copyright 2026 The Fuchsia Authors
#
# Use of this source code is governed by a BSD-style license that can be
# found in the LICENSE file or at https://opensource.org/licenses/BSD-3-Clause

# Option B (CI Batch Instances) entrypoint for continuous Anneal differential
# testing campaigns.
#
# Switching from Option A (Shared Agent Host +
# `/remote/teams/anneal-agent/differential-testing/`) to Option B (CI Batch timed
# batch jobs on CI runner) requires no changes to the differential testing
# harnesses or campaign runner (`scripts/run_diff_test_campaign.py`):
# point the CI Batch `.cfg` build_file at `anneal/ci/ci_diff_test.sh` and
# set `ANNEAL_DIFF_TEST_GCS_BUCKET` if using GCS state sync.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"

ARTIFACTS_DIR="${CI_ARTIFACTS_DIR:-/tmp/ci-artifacts}"
mkdir -p "${ARTIFACTS_DIR}"

STATE_DIR="${TMPDIR:-/tmp}/anneal-ci-diff-test-state"
mkdir -p "${STATE_DIR}"

PROFILE="${ANNEAL_DIFF_TEST_PROFILE:-nightly}"
JUNIT_XML="${ARTIFACTS_DIR}/diff_test_report.xml"
REPORT_MD="${ARTIFACTS_DIR}/diff_test_report.md"

if [[ -n "${ANNEAL_DIFF_TEST_GCS_BUCKET:-}" ]]; then
  gcloud storage rsync --recursive \
    "gs://${ANNEAL_DIFF_TEST_GCS_BUCKET}/differential-testing/" \
    "${STATE_DIR}/" || true
fi

python3 "${REPO_ROOT}/scripts/run_diff_test_campaign.py" \
  --profile "${PROFILE}" \
  --state-dir "${STATE_DIR}" \
  --remote-uri "" \
  --junit-xml "${JUNIT_XML}" \
  | tee "${REPORT_MD}"

if [[ -n "${ANNEAL_DIFF_TEST_GCS_BUCKET:-}" ]]; then
  gcloud storage rsync --recursive \
    "${STATE_DIR}/" \
    "gs://${ANNEAL_DIFF_TEST_GCS_BUCKET}/differential-testing/"
fi
