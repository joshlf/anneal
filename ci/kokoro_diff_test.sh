#!/usr/bin/env bash
# Copyright 2026 The Fuchsia Authors
#
# Use of this source code is governed by a BSD-style license that can be
# found in the LICENSE file or at https://opensource.org/licenses/BSD-3-Clause

# Option B (Kokoro V2 Instances) entrypoint for continuous Anneal differential
# testing campaigns.
#
# Switching from Option A (Team Capsule +
# `/x20/teams/anneal-agent/differential-testing/`) to Option B (Kokoro V2 timed
# batch jobs on Gerrit-on-Borg) requires no changes to the differential testing
# harnesses or campaign runner (`scripts/run_diff_test_campaign.py`):
# point the Kokoro V2 `.cfg` build_file at `anneal/ci/kokoro_diff_test.sh` and
# set `ANNEAL_DIFF_TEST_GCS_BUCKET` if using GCS state sync.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"

ARTIFACTS_DIR="${KOKORO_ARTIFACTS_DIR:-/tmp/kokoro-artifacts}"
mkdir -p "${ARTIFACTS_DIR}"

STATE_DIR="${TMPDIR:-/tmp}/anneal-kokoro-diff-test-state"
mkdir -p "${STATE_DIR}"

PROFILE="${ANNEAL_DIFF_TEST_PROFILE:-nightly}"
JUNIT_XML="${ARTIFACTS_DIR}/sponge_log.xml"
REPORT_MD="${ARTIFACTS_DIR}/sponge_log.md"

if [[ -n "${ANNEAL_DIFF_TEST_GCS_BUCKET:-}" ]]; then
  gcloud storage rsync --recursive \
    "gs://${ANNEAL_DIFF_TEST_GCS_BUCKET}/differential-testing/" \
    "${STATE_DIR}/" || true
fi

python3 "${REPO_ROOT}/scripts/run_diff_test_campaign.py" \
  --profile "${PROFILE}" \
  --state-dir "${STATE_DIR}" \
  --x20-uri "" \
  --junit-xml "${JUNIT_XML}" \
  | tee "${REPORT_MD}"

if [[ -n "${ANNEAL_DIFF_TEST_GCS_BUCKET:-}" ]]; then
  gcloud storage rsync --recursive \
    "${STATE_DIR}/" \
    "gs://${ANNEAL_DIFF_TEST_GCS_BUCKET}/differential-testing/"
fi
