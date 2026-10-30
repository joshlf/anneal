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

ROOT="$(git rev-parse --show-toplevel)"

# Force Nix to instantiate every package derivation across every target
# platform declared in `flake.nix`.
nix eval --json "$ROOT#packages" \
  --apply 'builtins.mapAttrs (_: builtins.mapAttrs (_: pkg: pkg.drvPath))' \
  >/dev/null
