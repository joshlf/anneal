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

if [ $# -ne 1 ]; then
    echo "Usage: $0 <version>" >&2
    exit 1
fi

VERSION="$1"

# Update the package version in `trusted/cargo-anneal/Cargo.toml`.
sed -i -e "s/^version = \"[0-9a-zA-Z\.-]*\"/version = \"$VERSION\"/" trusted/cargo-anneal/Cargo.toml

# Update Cargo.lock for `cargo-anneal` without rolling external dependency versions.
cargo update -p cargo-anneal --precise "$VERSION"
