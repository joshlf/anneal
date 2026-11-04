/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.

GENERATED FILE -- DO NOT EDIT. Regenerate with
`cargo run -p anneal-minirust-gen -- generate`.

Pins and input digests of this generation run, as Lean data.
-/

import MiniRustSpec.Meta.Syntax

namespace MiniRustSpec.Generated.Manifest

def upstreamRepository : String := "https://github.com/minirust/minirust"

def upstreamCommit : String := "d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed"

def upstreamTarballSha256 : String := "0b808e620296bde607ed6cf74642f39a023c2dbf9fe842d458fdfb69392913c0"

def upstreamRustToolchain : String := "nightly-2026-05-01"

def upstreamLibspecr : String := "0.1.41"

def annealRustcDialect : String := "V2026_06_01"

def annealRustcVersion : String := "rustc 1.98.0-nightly (14210df0e 2026-05-31)"

def leanToolchain : String := "leanprover/lean4:v4.34.1"

/-- Every vendored upstream file and its SHA-256, as checked against
`minirust/minirust.lock.toml` before generation. -/
def vendoredFiles : List (String × String) :=
  [
    (Prod.mk "LICENSE-APACHE" "a60eea817514531668d7e00765731449fe14d059d3249e0bc93b36de45f759f2"),
    (Prod.mk "LICENSE-MIT" "23f18e03dc49df91622fe2a76176497404e46ced8a715d9d2b67a7446571cca3"),
    (Prod.mk "README.md" "0cf8eef4f7ea8163dc9746e8b148206d4722be5fd3106cb9c16b3f4b7efb4cb8"),
    (Prod.mk
      "rust-toolchain.toml"
      "c9d156d35085df5843c805edf0f530b1e90336f65dae7988f9ba4b20c4b7190b"),
    (Prod.mk
      "spec/lang/machine.md"
      "121c624125adf8d8d988b6d088d8e85687e8a275ee703a80e486dcb05dfbd91c"),
    (Prod.mk
      "spec/lang/prelude.md"
      "15c5e052591700fd24a534aaf016ab2c3e4e9e4cedd20708cf2337e673ecae77"),
    (Prod.mk
      "spec/lang/representation.md"
      "3b101b30e85a6aea580b5b06371116abaab97f87b622f62de7459e0363f37844"),
    (Prod.mk
      "spec/lang/step/expressions.md"
      "cfa01e5f8d30eae252e36dbd1ecca51365f5cc02e90fe73b1b706fc3747cb6cb"),
    (Prod.mk
      "spec/lang/step/intrinsics.md"
      "261fe197e65556bae74cf209c64c5913fdd713f3a57d2bf56f0b1fb0e3a34be8"),
    (Prod.mk
      "spec/lang/step/locks.md"
      "385edb3568484f685f7c6ec9511f0d4f269e27a10d54eef253f2c82865ee73a6"),
    (Prod.mk
      "spec/lang/step/operators.md"
      "075e1e7d0b9fee47ef4a0adea2e9fef9861fb6ccfe98af6d42a0123fce96400d"),
    (Prod.mk
      "spec/lang/step/statements.md"
      "737151ae844720a47d4f224e50c28e8eb54a2dc80f0b450dd2b1f495570716a9"),
    (Prod.mk
      "spec/lang/step/terminators.md"
      "ae0c30634abe041ab520ee647c249489db5aa01e82ee0baa07b783e1d4086360"),
    (Prod.mk
      "spec/lang/syntax.md"
      "fb52bcf504990477daf6928e95b8ccf90f99700fdf17d6bb031fb590728c0674"),
    (Prod.mk
      "spec/lang/types.md"
      "4fef7acaaef6c1e0d14ab65bfd1934b495aa946ec7d23b42f0ab1d2cb30afdc7"),
    (Prod.mk
      "spec/lang/values.md"
      "06cd9f8f0fab58a0d5ff29c1ba25b41a2315d2db1a8413973d95e0f1cb96575d"),
    (Prod.mk
      "spec/lang/well-formed.md"
      "4aef03dfaa6b8e12128951143bb2a0b98c1de2dd8f5c2a762ffeef334b6d0bcb"),
    (Prod.mk "spec/mem/basic.md" "99b80806ce4a14fd1787d9b20d6931bb4756155b9fd74b380508d8c7cf87c072"),
    (Prod.mk
      "spec/mem/concurrent.md"
      "2b3f928517bed4da43739395656c7e24572dae37cb041fb7b77061c47a8e5816"),
    (Prod.mk
      "spec/mem/interface.md"
      "dfe4e0f504fc8892a520c555cb64b82774973b46f9adcaaaf915f4e5610f4708"),
    (Prod.mk
      "spec/mem/intptrcast.md"
      "ddb67b4ef74e05568fced9f1460730b595b4584d73d48c93fd326ff5dd7378b6"),
    (Prod.mk
      "spec/mem/pointer.md"
      "1eb963e5ef08052ba5947bb78debc8356fb91a6fef457247821ddb52f66d87b7"),
    (Prod.mk
      "spec/mem/prelude.md"
      "c1c09b68a5952a7f2c77bbcc2d3a9dbcd915ab7575267551433b6a1693d09b69"),
    (Prod.mk
      "spec/mem/tree_borrows/memory.md"
      "a61ffb69e23c0b0076c09e63ae9d1fa4843d0d5b2258b10c9c8d67bbc652fc2f"),
    (Prod.mk
      "spec/mem/tree_borrows/reborrow_settings.md"
      "ecfe79402f4d11e011ef01c9013e1de1a1866821ec024c97255679af0801d729"),
    (Prod.mk
      "spec/mem/tree_borrows/state_machine.md"
      "548918ad62b98c862b8a5ab9b58483bf6fd865c03d133631273a0b82782e120b"),
    (Prod.mk
      "spec/mem/tree_borrows/state_machine_protected.md"
      "968aa477b32c2e90aec47db517c24bed03a2e5292871b4121aab6a654deb7e51"),
    (Prod.mk
      "spec/mem/tree_borrows/state_machine_unprotected.md"
      "956688821b81db8912a5847730bd9f3aa439e79f727b29dc95e58f8e1b1e9335"),
    (Prod.mk
      "spec/mem/tree_borrows/tree.md"
      "67e3d2e245ffc752ee2ec4f82bdf928a23c6345926436b22a041546aa32ff988"),
    (Prod.mk
      "spec/prelude/main.md"
      "b031f4b168ca826e0713b840415cb69d076299b01d4588fc92cfe89452d18262"),
    (Prod.mk
      "spec/prelude/target.md"
      "28cb80649c97776490cc321c130de53ea12e4dd132043199eadf3b2a6f6cb3f4"),
    (Prod.mk "specr.toml" "a3f167021c4a7f3e9ecc326cd6a87b302e649de1210b220e7cd935bbc0631d04"),
    (Prod.mk
      "tooling/Cargo.lock"
      "713f632f676e23bce95cbfb46454a718a53ec126837ca7d6db3257ee40f450ad"),
    (Prod.mk
      "tooling/minimize/src/bb.rs"
      "5094f4305b1552319867fe25ed03bae20f6875527043074cadd169b84bb9622a"),
    (Prod.mk
      "tooling/minimize/src/chunks.rs"
      "e442c679cd7e2e9f0cb6e536e8f787f7f4aa8f3415caa392ddf7baeb7f932463"),
    (Prod.mk
      "tooling/minimize/src/constant.rs"
      "755ebdeccdfb54007b54cc40e5d13f191dc1825f86bb8377c180f516f9657d74"),
    (Prod.mk
      "tooling/minimize/src/enums.rs"
      "d8d76dd86e907ccd1ae902c603e4529a68d062d8e53895ee8bd4058194c81d22"),
    (Prod.mk
      "tooling/minimize/src/function.rs"
      "b6496e4109d1769987c8676be5f1e9979377ee89a68ab1632895f91385d3542a"),
    (Prod.mk
      "tooling/minimize/src/main.rs"
      "0543923e49cf22e45ad43560a8a9f7ea1219f6254e63138d4afd18bfa4efd7e7"),
    (Prod.mk
      "tooling/minimize/src/program.rs"
      "74f23638f728659efd108f44d830247081fd4d31703aa4383bcf8fa0e4362825"),
    (Prod.mk
      "tooling/minimize/src/rvalue.rs"
      "748d87fe2f48651c6dcf21d2454fa61ce57cc58cb0f7ea80f205a99483b027f1"),
    (Prod.mk
      "tooling/minimize/src/sysroot.rs"
      "036ce2aa0c51a20462d43126caea5d1977416da587e4eeec46fc62d9e27c4fb3"),
    (Prod.mk
      "tooling/minimize/src/ty.rs"
      "aba733b1f138094da6b4477305151aa281c0582c2c876719a24856f81ed2e400"),
    (Prod.mk
      "tooling/minimize/src/vtable.rs"
      "54c883c9213ce5ca4889043af85a7600fb66e53f00d97b497aa50c8cc80ca025")]

end MiniRustSpec.Generated.Manifest
