#!/usr/bin/env bash
#
# Copyright 2024 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

set -eo pipefail
cd "$(dirname "$0")/.."
which yq > /dev/null
failed=0

# Verify that every job in a `pull_request` workflow that defines an
# `all-jobs-succeed` gate is listed in `all-jobs-succeed.needs`, so branch
# protection cannot miss a job result.
for i in $(find .github/workflows -iname '*.yaml' -or -iname '*.yml'); do
  if yq -e '.on | has("pull_request")' "$i" 2>/dev/null >/dev/null; then
    if yq -e '.jobs | has("all-jobs-succeed")' "$i" 2>/dev/null >/dev/null; then
      missing=$(comm -23 \
        <(yq -r '.jobs | keys | .[]' "$i" | grep -v '^all-jobs-succeed$' | sort | uniq) \
        <(yq -r '.jobs["all-jobs-succeed"].needs[]?' "$i" | sort | uniq))

      if [ -n "$missing" ]; then
        missing_jobs="$(echo "$missing" | tr '\n' ' ')"
        echo "$i: all-jobs-succeed missing dependencies on some jobs: $missing_jobs" | tee -a "${GITHUB_STEP_SUMMARY:-/dev/null}" >&2
        failed=1
      fi
    fi
  fi
done

if [ "$failed" -eq 1 ]; then
  exit 1
fi
