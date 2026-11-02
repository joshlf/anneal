#!/usr/bin/env bash
# Option B (Kokoro V2 Instances) Entrypoint for Continuous Anneal Fuzzing Campaigns.
#
# Switching from Option A (Team Capsule + /x20/teams/anneal-agent/fuzzing/) to Option B
# (Kokoro V2 Timed Batch Jobs on Gerrit-on-Borg) requires zero changes to the fuzzer or
# campaign orchestrator: simply point the Kokoro JobConfig `build_file` at
# `anneal/ci/kokoro_fuzz.sh` and set `ANNEAL_FUZZ_GCS_BUCKET` if using GCS state sync.

set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
export PATH="${HOME}/.cargo/bin:${HOME}/.elan/bin:${PATH}"

STATE_DIR="${TMPDIR:-/tmp}/anneal-kokoro-fuzz-state"
mkdir -p "${STATE_DIR}"

PROFILE="${ANNEAL_FUZZ_PROFILE:-nightly}"
ARTIFACTS_DIR="${KOKORO_ARTIFACTS_DIR:-${STATE_DIR}/artifacts}"
mkdir -p "${ARTIFACTS_DIR}"

# 1. Restore persistent evolutionary corpus, coverage ratchet, and quarantine list from GCS
if [[ -n "${ANNEAL_FUZZ_GCS_BUCKET:-}" ]]; then
  gcloud storage rsync --recursive "gs://${ANNEAL_FUZZ_GCS_BUCKET}/fuzzing/" "${STATE_DIR}/" || true
fi

# 2. Run the unified campaign orchestrator and emit Sponge2 / Test Fusion JUnit XML
python3 "${REPO_ROOT}/scripts/run_fuzz_campaign.py" \
  --repo-root "${REPO_ROOT}" \
  --profile "${PROFILE}" \
  --state-dir "${STATE_DIR}" \
  --x20-uri "" \
  --junit-xml "${ARTIFACTS_DIR}/sponge_log.xml"

# 3. Copy minimized reproducer bundles (`findings/<fingerprint>/`) and Markdown report to Sponge2 artifacts
if [[ -d "${STATE_DIR}/findings" ]]; then
  cp -rf "${STATE_DIR}/findings" "${ARTIFACTS_DIR}/"
fi
if [[ -d "${STATE_DIR}/reports" ]]; then
  cp -rf "${STATE_DIR}/reports" "${ARTIFACTS_DIR}/"
fi

# 4. Sync updated ledger, coverage ratchet, and deduplicated findings back to GCS
if [[ -n "${ANNEAL_FUZZ_GCS_BUCKET:-}" ]]; then
  gcloud storage rsync --recursive "${STATE_DIR}/" "gs://${ANNEAL_FUZZ_GCS_BUCKET}/fuzzing/"
fi
