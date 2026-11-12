#!/usr/bin/env bash
#
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

set -euo pipefail
cd "$(dirname "$0")/.."

sha256sum --check --strict trusted/root-manifest.sha256
python3 -B ci/check_repository.py
# The review-gate tests use fake GitHub responses and make no status writes.
python3 -B -m unittest discover -s ci -p 'test_*.py' -v
./ci/check_todo.sh
python3 -B ci/check_workflow_dependencies.py
./ci/check_actions.sh
./ci/check_format.sh
./ci/check_flake_eval.sh
./ci/check_non_stable_version.sh
