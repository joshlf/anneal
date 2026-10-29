{
  description = "Anneal Hermentic Toolchain & Exocrate Archive Flake";

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

        # Fixed-output downloader used for Rust toolchain assets (shared with zerocopy/anneal).
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
            ./trusted/audit
            ./theory
            ./trusted/cargo-anneal/src/audit.rs
            ./trusted/cargo-anneal/src/bin/build_verify_prefix.rs
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

          nativeBuildInputs = [
            pkgs.stdenv.cc
          ];

          rustToolchain = self.packages.${system}.rust-toolchain;
          leanToolchain = self.packages.${system}.lean-toolchain;

          buildPhase = builtins.concatStringsSep "\n" [
            "mkdir -p $out/share/anneal/trusted $out/share/anneal/theory build"
            "cp -r $src/trusted/lean $out/share/anneal/trusted/lean"
            "cp -r $src/trusted/audit $out/share/anneal/trusted/audit"
            "cp -r $src/theory/* $out/share/anneal/theory/"
            "chmod -R +w $out/share/anneal"
            (runInHostAbi ''
              set -euo pipefail
              export TMPDIR="''${TMPDIR:-/tmp}"
              "$rustToolchain/bin/rustc" --edition=2024 -O \
                "$src/trusted/cargo-anneal/src/bin/build_verify_prefix.rs" \
                -o build/build-verify-prefix
              ./build/build-verify-prefix \
                --anneal-root "$out/share/anneal" \
                --lean "$leanToolchain/bin/lean" \
                --out-dir "$out/share/anneal/precompiled-prefix"
            '')
          ];
        };

        # Stages the relocatable toolchain bundle before compression.
        packages.omnibus-tar = pkgs.stdenv.mkDerivation {
          pname = "anneal-toolchain-omnibus-tar";
          version = "0.1.0";

          src = pkgs.runCommand "empty-src" {} "mkdir $out";

          dontPatchELF = true;
          dontStrip = true;
          dontPatchShebangs = true;

          nativeBuildInputs = with pkgs; [
            gnutar
          ] ++ pkgs.lib.optionals stdenv.isLinux [
            patchelf
            file
          ];

          rustToolchain = self.packages.${system}.rust-toolchain;
          leanToolchain = self.packages.${system}.lean-toolchain;
          rustcCapture = self.packages.${system}.rustc-capture;
          annealFoundation = self.packages.${system}.anneal-foundation;

          buildPhase = builtins.concatStringsSep "\n" ([
            "mkdir -p $TMPDIR/dist_staging"
            "chmod -R +w $TMPDIR/dist_staging/"
            # Copy Lean unmodified so bin/lean and Init.* match foundation-lock.json,
            # removing only unused static archives (.a).
            "mkdir -p $TMPDIR/dist_staging/lean"
            "cp -r $leanToolchain/* $TMPDIR/dist_staging/lean/"
            "chmod -R +w $TMPDIR/dist_staging/lean"
            "find $TMPDIR/dist_staging/lean/lib -name '*.a' -delete"
            # Copy pinned Rust toolchain and deduplicate shared libraries.
            "mkdir -p $TMPDIR/dist_staging/rust"
            "cp -r $rustToolchain/* $TMPDIR/dist_staging/rust/"
            "chmod -R +w $TMPDIR/dist_staging/rust"
            "rm -rf $TMPDIR/dist_staging/rust/share/doc"
            "for so in $TMPDIR/dist_staging/rust/lib/rustlib/*/lib/*.so* $TMPDIR/dist_staging/rust/lib/rustlib/*/lib/*.dylib; do"
            "  if [ -f \"\$so\" ] && [ -f \"$TMPDIR/dist_staging/rust/lib/\$(basename \"\$so\")\" ]; then"
            "    ln -sf \"../../../\$(basename \"\$so\")\" \"\$so\""
            "  fi"
            "done"
            # Copy standalone anneal-rustc-capture binary.
            "mkdir -p $TMPDIR/dist_staging/bin"
            "cp -r $rustcCapture/bin/* $TMPDIR/dist_staging/bin/"
            "chmod -R +w $TMPDIR/dist_staging/bin"
            # Copy Anneal Lean foundation + precompiled/pre-audited prefix.
            "mkdir -p $TMPDIR/dist_staging/share"
            "cp -r $annealFoundation/share/* $TMPDIR/dist_staging/share/"
            "chmod -R +w $TMPDIR/dist_staging/share"
          ] ++ pkgs.lib.optionals pkgs.stdenv.isLinux [
            # Set relocatable dynamic-linker and $ORIGIN RPATH references on ELF
            # binaries in bin/ and rust/, while leaving lean/ byte-for-byte untouched.
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
              share/anneal/trusted/audit/TrustedBoundary.lean \
              share/anneal/theory/Anneal.lean \
              share/anneal/precompiled-prefix/prefix-manifest.json \
              share/anneal/precompiled-prefix/lib/Trusted.olean \
              share/anneal/precompiled-prefix/crate-lib/Anneal.olean; do
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
