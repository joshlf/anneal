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

systems=(
  aarch64-darwin
  aarch64-linux
  x86_64-darwin
  x86_64-linux
)

packages=(
  anneal-foundation
  default
  lean-toolchain
  omnibus-archive
  omnibus-archive-ci
  omnibus-archive-layout-check
  omnibus-tar
  rust-toolchain
  rustc-capture
)

for system in "${systems[@]}"; do
  for package in "${packages[@]}"; do
    printf 'Evaluating packages.%s.%s...\n' "$system" "$package"
    nix eval --raw "$ROOT#packages.$system.$package.drvPath" >/dev/null
  done
done
