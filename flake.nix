# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

{
  description = "Anneal Hermetic Toolchain & Exocrate Archive Flake";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils, ... }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs {
          inherit system;
          config.allowUnfree = true;
        };

        rustPlatform =
          if system == "x86_64-linux" then "x86_64-unknown-linux-gnu"
          else if system == "aarch64-linux" then "aarch64-unknown-linux-gnu"
          else if system == "x86_64-darwin" then "x86_64-apple-darwin"
          else if system == "aarch64-darwin" then "aarch64-apple-darwin"
          else throw "Unsupported system: ${system}";

        leanPlatform =
          if system == "x86_64-linux" then "linux"
          else if system == "aarch64-linux" then "linux_aarch64"
          else if system == "x86_64-darwin" then "darwin"
          else if system == "aarch64-darwin" then "darwin_aarch64"
          else throw "Unsupported system: ${system}";

        foundationLockVersion =
          if system == "x86_64-linux" then "Lean (version 4.34.1, x86_64-unknown-linux-gnu, commit 5045d0056413266e57c625dcd7c365b10e377c52, Release)"
          else if system == "aarch64-linux" then "Lean (version 4.34.1, aarch64-unknown-linux-gnu, commit 5045d0056413266e57c625dcd7c365b10e377c52, Release)"
          else if system == "x86_64-darwin" then "Lean (version 4.34.1, x86_64-apple-darwin24.6.0, commit 5045d0056413266e57c625dcd7c365b10e377c52, Release)"
          else if system == "aarch64-darwin" then "Lean (version 4.34.1, arm64-apple-darwin24.6.0, commit 5045d0056413266e57c625dcd7c365b10e377c52, Release)"
          else throw "Unsupported system: ${system}";

        rustDate = "2026-05-31";
        leanVersion = "4.34.1";

        rustToolchainSha256 =
          if system == "x86_64-linux" then "sha256-MmvOgC3shIOVMWT1MTRajw8JuLwRk/P3LsmGVslNGKw="
          else if system == "aarch64-linux" then "sha256-gWFajI7TJyjslQLZm4VWBBsKA6nYe1lNQwrgUp2hwSA="
          else if system == "x86_64-darwin" then "sha256-dBLHRLo3omD7KRq0D8lzg6XiQfDKWOMD6YTrLQhEneo="
          else if system == "aarch64-darwin" then "sha256-X7ndqbjsmnjL6KZzNCxkVFJPzAsAjUqerD/wc1rxK5E="
          else throw "Unsupported system: ${system}";

        leanArchiveSha256 =
          if system == "x86_64-linux" then "47bf4bbd78f70c2e9670598ab7124d92b6efb7330ff33e5fbb4030f6fd72e4e4"
          else if system == "aarch64-linux" then "fdb974c2cdb4627e090d5d4007b913e09d13c4868720fb5594e22808b3de9e37"
          else if system == "x86_64-darwin" then "c2fee70250444e46c1106a27bddfef948d1e563eef431eaac05bb946b2f73d3a"
          else if system == "aarch64-darwin" then "65f22a4f047738ec742667b3247e836a86ebf06eabc12655c3dee00637e37866"
          else throw "Unsupported system: ${system}";

        linuxDynamicLinker =
          if system == "x86_64-linux" then "/lib64/ld-linux-x86-64.so.2"
          else if system == "aarch64-linux" then "/lib/ld-linux-aarch64.so.1"
          else "";

        linuxFhsEnv =
          if pkgs.stdenv.isLinux then pkgs.buildFHSEnv {
            name = "anneal-linux-fhs";
            targetPkgs = pkgs: with pkgs; [
              stdenv.cc.cc
              zlib
              gmp
              libffi
              ncurses
              openssl
            ];
            runScript = "bash";
          } else null;

        runInHostAbi = command:
          if pkgs.stdenv.isLinux
          then "${linuxFhsEnv}/bin/anneal-linux-fhs -c ${pkgs.lib.escapeShellArg command}"
          else command;

        # Download and unpack a multi-component toolchain archive as a
        # fixed-output derivation without patching or stripping binaries.
        fetchToolchainAsset = { pname, version, sha256, buildPhase }:
          pkgs.stdenv.mkDerivation {
            pname = "${pname}-${system}";
            inherit version sha256 buildPhase;

            dontUnpack = true;
            dontPatchShebangs = true;
            dontPatchELF = true;
            dontStrip = true;

            outputHashMode = "recursive";
            outputHashAlgo = "sha256";
            outputHash = sha256;

            nativeBuildInputs = with pkgs; [
              curl
              cacert
              gnutar
              gzip
              zstd
            ];

            SSL_CERT_FILE = "${pkgs.cacert}/etc/ssl/certs/ca-bundle.crt";
          };

        fetchRustToolchain = { rustDate, sha256 }:
          fetchToolchainAsset {
            pname = "rust-toolchain";
            version = rustDate;
            inherit sha256;

            buildPhase = builtins.concatStringsSep "\n" [
              "mkdir -p $out"
              "extract_component() {"
              "  local name=$1"
              "  local url=\"https://static.rust-lang.org/dist/${rustDate}/\${name}-nightly-${rustPlatform}.tar.gz\""
              "  echo \"Downloading and extracting $name from $url...\""
              "  mkdir -p tmp_extract"
              "  curl -sSL \"$url\" | tar -xz -C tmp_extract"
              "  local top_dir=$(ls tmp_extract | head -n 1)"
              "  local comp_dir=$(find \"tmp_extract/$top_dir\" -mindepth 1 -maxdepth 1 -type d | head -n 1)"
              "  cp -r $comp_dir/* $out/"
              "  rm -rf tmp_extract"
              "}"
              "extract_component \"cargo\""
              "extract_component \"rustc\""
              "extract_component \"rust-std\""
              "extract_component \"rustc-dev\""
              "extract_component \"llvm-tools\""
              "extract_component \"miri\""
              "echo \"Downloading and extracting rust-src...\""
              "mkdir -p tmp_extract"
              "curl -sSL \"https://static.rust-lang.org/dist/${rustDate}/rust-src-nightly.tar.gz\" | tar -xz -C tmp_extract"
              "top_dir=$(ls tmp_extract | head -n 1)"
              "cp -r tmp_extract/$top_dir/rust-src/* $out/"
              "rm -rf tmp_extract"
              "rm -f $out/manifest.in"
            ];
          };

        leanArchive = pkgs.fetchurl {
          name = "lean-${leanVersion}-${leanPlatform}.tar.zst";
          url = "https://github.com/leanprover/lean4/releases/download/v${leanVersion}/lean-${leanVersion}-${leanPlatform}.tar.zst";
          sha256 = leanArchiveSha256;
        };

        leanSourceFiles = pkgs.lib.fileset.toSource {
          root = ./.;
          fileset = pkgs.lib.fileset.unions [
            ./trusted/lean
          ];
        };

        rustcCaptureSourceFiles = pkgs.lib.fileset.toSource {
          root = ./.;
          fileset = pkgs.lib.fileset.unions [
            ./trusted/rustc-capture
          ];
        };
      in
      {
        packages.rust-toolchain = fetchRustToolchain {
          inherit rustDate;
          sha256 = rustToolchainSha256;
        };

        # Unpack Lean v4.34.1 without patchelf or strip so bin/lean and Init.*
        # remain byte-for-byte identical to foundation-lock.json.
        packages.lean-toolchain = pkgs.stdenv.mkDerivation {
          pname = "lean-toolchain-${system}";
          version = leanVersion;
          src = leanArchive;

          dontUnpack = true;
          dontPatchELF = true;
          dontStrip = true;
          dontPatchShebangs = true;

          nativeBuildInputs = with pkgs; [
            gnutar
            zstd
          ];

          buildPhase = ''
            mkdir -p $out tmp_extract
            tar --zstd -xf $src -C tmp_extract
            top_dir=$(ls tmp_extract | head -n 1)
            cp -r tmp_extract/$top_dir/* $out/
            rm -rf tmp_extract
          '';
        };

        packages.rustc-capture = pkgs.stdenv.mkDerivation {
          pname = "anneal-rustc-capture";
          version = "0.1.0";
          src = rustcCaptureSourceFiles;

          nativeBuildInputs = [
            pkgs.stdenv.cc
          ];

          rustToolchain = self.packages.${system}.rust-toolchain;

          buildPhase = builtins.concatStringsSep "\n" [
            "mkdir -p $out/bin build"
            (runInHostAbi ''
              set -euo pipefail
              "$rustToolchain/bin/rustc" --edition=2024 --crate-name=anneal_rustc_capture \
                --crate-type=lib -O "$src/trusted/rustc-capture/src/lib.rs" \
                -o build/libanneal_rustc_capture.rlib
              "$rustToolchain/bin/rustc" --edition=2024 --crate-name=anneal_rustc_capture \
                --extern anneal_rustc_capture=build/libanneal_rustc_capture.rlib \
                -L dependency=build -O "$src/trusted/rustc-capture/src/main.rs" \
                -o "$out/bin/anneal-rustc-capture"
            '')
          ];
        };

        packages.anneal-foundation = pkgs.stdenv.mkDerivation {
          pname = "anneal-foundation";
          version = "0.1.0";
          src = leanSourceFiles;

          dontPatchELF = true;
          dontStrip = true;

          nativeBuildInputs = with pkgs; [
            coreutils
            jq
          ];

          leanToolchain = self.packages.${system}.lean-toolchain;

          buildPhase = ''
            set -euo pipefail
            mkdir -p $out/share/anneal/trusted
            cp -r $src/trusted/lean $out/share/anneal/trusted/lean
            chmod -R +w $out/share/anneal

            lock_file="$out/share/anneal/trusted/lean/foundation-lock.json"
            expected_lean_sha=$(jq -er --arg ver "${foundationLockVersion}" '.distributions[$ver]' "$lock_file")
            actual_lean_sha=$(sha256sum "$leanToolchain/bin/lean" | awk '{print $1}')
            if [ "$actual_lean_sha" != "$expected_lean_sha" ]; then
              echo "ERROR: bin/lean SHA-256 mismatch ($actual_lean_sha != $expected_lean_sha)" >&2
              exit 1
            fi

            while IFS=$'\t' read -r mod_name ext expected_sha; do
              mod_rel=$(echo "$mod_name" | tr '.' '/')
              rel_path="lib/lean/$mod_rel.$ext"
              actual_sha=$(sha256sum "$leanToolchain/$rel_path" | awk '{print $1}')
              if [ "$actual_sha" != "$expected_sha" ]; then
                echo "ERROR: foundation artifact $rel_path SHA-256 mismatch ($actual_sha != $expected_sha)" >&2
                exit 1
              fi
            done < <(jq -r '.modules | to_entries[] | .key as $m | .value.parts | to_entries[] | [$m, .key, .value] | @tsv' "$lock_file")
          '';
        };

        packages.omnibus-tar = pkgs.stdenv.mkDerivation {
          pname = "anneal-toolchain-omnibus-tar";
          version = "0.1.0";

          src = pkgs.runCommand "empty-src" {} "mkdir $out";

          dontPatchELF = true;
          dontStrip = true;
          dontPatchShebangs = true;

          nativeBuildInputs = with pkgs; [
            gnutar
            patchelf
            file
            binutils
          ];

          rustToolchain = self.packages.${system}.rust-toolchain;
          leanToolchain = self.packages.${system}.lean-toolchain;
          rustcCapture = self.packages.${system}.rustc-capture;
          annealFoundation = self.packages.${system}.anneal-foundation;

          buildPhase = builtins.concatStringsSep "\n" ([
            "mkdir -p $TMPDIR/dist_staging"

            "echo \"Staging Rust Toolchain...\""
            "mkdir -p $TMPDIR/dist_staging/rust"
            "cp -r $rustToolchain/* $TMPDIR/dist_staging/rust/"
            "chmod -R +w $TMPDIR/dist_staging/rust"
            "rm -rf $TMPDIR/dist_staging/rust/share/doc"

            "echo \"Staging Lean Toolchain...\""
            "mkdir -p $TMPDIR/dist_staging/lean"
            "cp -r $leanToolchain/* $TMPDIR/dist_staging/lean/"
            "chmod -R +w $TMPDIR/dist_staging/lean"

            "echo \"Staging anneal-rustc-capture...\""
            "mkdir -p $TMPDIR/dist_staging/bin"
            "cp $rustcCapture/bin/anneal-rustc-capture $TMPDIR/dist_staging/bin/"
            "chmod -R +w $TMPDIR/dist_staging/bin"

            "echo \"Staging Anneal Foundation...\""
            "mkdir -p $TMPDIR/dist_staging/share"
            "cp -r $annealFoundation/share/* $TMPDIR/dist_staging/share/"
            "chmod -R +w $TMPDIR/dist_staging/share"
          ] ++ pkgs.lib.optionals pkgs.stdenv.isLinux [
            # Configure a standard Linux dynamic linker and relative `$ORIGIN`
            # RPATHs on ELF binaries in `bin/` and `rust/`. Leave `lean/`
            # untouched so `bin/lean` and `Init.*` preserve the SHA-256
            # digests recorded in `foundation-lock.json`.
            "echo \"Setting relocatable ELF interpreter and RPATHs in bin/ and rust/...\""
            "find $TMPDIR/dist_staging/bin $TMPDIR/dist_staging/rust -type f | while read -r file; do"
            "  if file \"\$file\" | grep -q \"ELF 64-bit\"; then"
            "    if patchelf --print-interpreter \"\$file\" >/dev/null 2>&1; then"
            "      patchelf --set-interpreter ${linuxDynamicLinker} \"\$file\" || true"
            "    fi"
            "    case \"\$file\" in"
            "      $TMPDIR/dist_staging/bin/*)"
            "        patchelf --set-rpath '\$ORIGIN/../rust/lib' \"\$file\" || true"
            "        ;;"
            "      $TMPDIR/dist_staging/rust/bin/*)"
            "        patchelf --set-rpath '\$ORIGIN/../lib' \"\$file\" || true"
            "        ;;"
            "      $TMPDIR/dist_staging/rust/lib/*)"
            "        patchelf --set-rpath '\$ORIGIN' \"\$file\" || true"
            "        ;;"
            "    esac"
            "    strip \"\$file\" || true"
            "  fi"
            "done"
          ] ++ [
            "chmod -R a-w $TMPDIR/dist_staging"
            "cd $TMPDIR/dist_staging"
            "tar -cf $out *"
          ]);
        };

        packages.omnibus-archive = pkgs.stdenv.mkDerivation {
          pname = "anneal-toolchain-omnibus";
          version = "0.1.0";

          src = pkgs.runCommand "empty-src" {} "mkdir $out";

          nativeBuildInputs = with pkgs; [
            zstd
          ];

          omnibusTar = self.packages.${system}.omnibus-tar;

          ANNEAL_ZSTD_LEVEL = 1;

          buildPhase = builtins.concatStringsSep "\n" [
            "ZSTD_LEVEL=\${ANNEAL_ZSTD_LEVEL:-1}"
            "echo \"Compressing with Zstd level \$ZSTD_LEVEL...\""
            "zstd -\$ZSTD_LEVEL $omnibusTar -o $out"
          ];
        };

        packages.omnibus-archive-ci = self.packages.${system}.omnibus-archive.overrideAttrs (_: {
          ANNEAL_ZSTD_LEVEL = 6;
        });

        packages.omnibus-archive-layout-check =
          pkgs.runCommand "anneal-toolchain-omnibus-layout-check" {
            nativeBuildInputs = with pkgs; [
              gnutar
              zstd
            ];

            archive = self.packages.${system}.omnibus-archive-ci;
          } ''
            set -euo pipefail

            mkdir -p "$TMPDIR/archive"
            zstd -dc "$archive" | tar -tf - > "$TMPDIR/archive/entries"

            cut -d/ -f1 "$TMPDIR/archive/entries" | sort -u > "$TMPDIR/archive/top-level"
            cat > "$TMPDIR/archive/expected-top-level" <<EOF
            bin
            lean
            rust
            share
            EOF
            if ! diff -u "$TMPDIR/archive/expected-top-level" "$TMPDIR/archive/top-level"; then
              echo "ERROR: unexpected top-level archive layout" >&2
              exit 1
            fi

            for path in \
              bin/anneal-rustc-capture \
              lean/bin/lean \
              rust/bin/cargo \
              rust/bin/rustc \
              share/anneal/trusted/lean/foundation-lock.json \
              share/anneal/trusted/lean/lean-toolchain; do
              if ! grep -Fxq "$path" "$TMPDIR/archive/entries"; then
                echo "ERROR: expected archive entry missing: $path" >&2
                exit 1
              fi
            done

            if grep -E '(^/|(^|/)\.\.(/|$))' "$TMPDIR/archive/entries"; then
              echo "ERROR: archive contains absolute or parent-relative paths" >&2
              exit 1
            fi

            mkdir -p "$out"
            cp "$TMPDIR/archive/entries" "$out/entries"
          '';

        packages.default = self.packages.${system}.omnibus-archive;

        devShells.default = pkgs.mkShell {
          packages = [
            self.packages.${system}.lean-toolchain
            self.packages.${system}.rust-toolchain
            self.packages.${system}.rustc-capture
            pkgs.zstd
            pkgs.jq
          ];
          ANNEAL_LEAN_BIN = "${self.packages.${system}.lean-toolchain}/bin/lean";
          ANNEAL_RUSTC_CAPTURE_BIN = "${self.packages.${system}.rustc-capture}/bin/anneal-rustc-capture";
        };
      });
}
