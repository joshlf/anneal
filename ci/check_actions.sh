#!/usr/bin/env bash
#
# Copyright 2025 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

set -euo pipefail
cd "$(dirname "$0")/.."

# Use the provisioned validators. Installing missing tools here would make
# the check depend on network state and versions outside the pinned shell.
for tool in action-validator actionlint; do
  if ! command -v "$tool" >/dev/null 2>&1; then
    echo "Missing $tool; run: nix develop .#static --command ./ci/check_actions.sh" >&2
    exit 1
  fi
done

shopt -s nullglob
files=(.github/workflows/*.yml .github/workflows/*.yaml)
action-validator "${files[@]}"
actionlint "${files[@]}"
