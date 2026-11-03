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
`spec/mem/prelude.md` (commit `d821c6e3`), one Lean definition per item, in source order.
-/

import MiniRustSpec.Meta.Syntax

set_option maxRecDepth 100000

namespace MiniRustSpec.Gen.Items.Mem.Prelude

open MiniRustSpec.Syntax

/-- Path of the upstream file these items were extracted from. -/
def sourceFile : String := "spec/mem/prelude.md"

/-- SHA-256 of the upstream file. -/
def sourceSha256 : String := "c1c09b68a5952a7f2c77bbcc2d3a9dbcd915ab7575267551433b6a1693d09b69"

/-- `spec/mem/prelude.md:6` -/
def use : Item :=
  (Item.use
    []
    Visibility.inherited
    false
    (UseTree.path "crate" (UseTree.path "prelude" UseTree.glob)))

/-- All items of `spec/mem/prelude.md`, in source order, with provenance. -/
def items : List SourceItem :=
  [(SourceItem.mk "use" 6 "402eca254faf3f259deb0954331586c53493e58dddcb882702c033c71905e5df" use)]

end MiniRustSpec.Gen.Items.Mem.Prelude
