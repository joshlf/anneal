/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.

GENERATED FILE -- DO NOT EDIT. Regenerate with
`cargo run -p anneal-minirust-gen -- generate`.

Deep (syntax) embedding of every top-level item of upstream MiniRust
`spec/lang/prelude.md` (commit `d821c6e3`), one Lean definition per item, in source order.
-/

import MiniRustSpec.Meta.Syntax

set_option maxRecDepth 100000

namespace MiniRustSpec.Gen.Items.Lang.Prelude

open MiniRustSpec.Syntax

/-- Path of the upstream file these items were extracted from. -/
def sourceFile : String := "spec/lang/prelude.md"

/-- SHA-256 of the upstream file. -/
def sourceSha256 : String := "15c5e052591700fd24a534aaf016ab2c3e4e9e4cedd20708cf2337e673ecae77"

/-- `spec/lang/prelude.md:6` -/
def use_0 : Item :=
  (Item.use
    []
    Visibility.inherited
    false
    (UseTree.path "crate" (UseTree.path "prelude" UseTree.glob)))

/-- `spec/lang/prelude.md:7` -/
def use_1 : Item :=
  (Item.use [] Visibility.inherited false (UseTree.path "mem" UseTree.glob))

/-- All items of `spec/lang/prelude.md`, in source order, with provenance. -/
def items : List SourceItem :=
  [
    (SourceItem.mk
      "use_0"
      6
      "402eca254faf3f259deb0954331586c53493e58dddcb882702c033c71905e5df"
      use_0),
    (SourceItem.mk
      "use_1"
      7
      "0828357212207705b90134087bcbf22ec711a11783f8255051644fd368f40e10"
      use_1)]

end MiniRustSpec.Gen.Items.Lang.Prelude
