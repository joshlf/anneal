/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.

GENERATED FILE -- DO NOT EDIT. Regenerate with
`cargo run -p anneal-minirust-gen -- generate`.

Root of the generated MiniRust model.
-/

import MiniRustSpec.Generated.Manifest
import MiniRustSpec.Generated.Types
import MiniRustSpec.Generated.Items.Lang.Machine
import MiniRustSpec.Generated.Items.Lang.Prelude
import MiniRustSpec.Generated.Items.Lang.Representation
import MiniRustSpec.Generated.Items.Lang.Step.Expressions
import MiniRustSpec.Generated.Items.Lang.Step.Intrinsics
import MiniRustSpec.Generated.Items.Lang.Step.Locks
import MiniRustSpec.Generated.Items.Lang.Step.Operators
import MiniRustSpec.Generated.Items.Lang.Step.Statements
import MiniRustSpec.Generated.Items.Lang.Step.Terminators
import MiniRustSpec.Generated.Items.Lang.Syntax
import MiniRustSpec.Generated.Items.Lang.Types
import MiniRustSpec.Generated.Items.Lang.Values
import MiniRustSpec.Generated.Items.Lang.WellFormed
import MiniRustSpec.Generated.Items.Mem.Basic
import MiniRustSpec.Generated.Items.Mem.Concurrent
import MiniRustSpec.Generated.Items.Mem.Interface
import MiniRustSpec.Generated.Items.Mem.Intptrcast
import MiniRustSpec.Generated.Items.Mem.Pointer
import MiniRustSpec.Generated.Items.Mem.Prelude
import MiniRustSpec.Generated.Items.Mem.TreeBorrows.Memory
import MiniRustSpec.Generated.Items.Mem.TreeBorrows.ReborrowSettings
import MiniRustSpec.Generated.Items.Mem.TreeBorrows.StateMachine
import MiniRustSpec.Generated.Items.Mem.TreeBorrows.StateMachineProtected
import MiniRustSpec.Generated.Items.Mem.TreeBorrows.StateMachineUnprotected
import MiniRustSpec.Generated.Items.Mem.TreeBorrows.Tree
import MiniRustSpec.Generated.Items.Prelude.Main
import MiniRustSpec.Generated.Items.Prelude.Target

namespace MiniRustSpec.Generated

open MiniRustSpec.Syntax

/-- Every translated upstream specification file with its items. -/
def allFiles : List (String × List SourceItem) :=
  [
    (Prod.mk "spec/lang/machine.md" MiniRustSpec.Gen.Items.Lang.Machine.items),
    (Prod.mk "spec/lang/prelude.md" MiniRustSpec.Gen.Items.Lang.Prelude.items),
    (Prod.mk "spec/lang/representation.md" MiniRustSpec.Gen.Items.Lang.Representation.items),
    (Prod.mk "spec/lang/step/expressions.md" MiniRustSpec.Gen.Items.Lang.Step.Expressions.items),
    (Prod.mk "spec/lang/step/intrinsics.md" MiniRustSpec.Gen.Items.Lang.Step.Intrinsics.items),
    (Prod.mk "spec/lang/step/locks.md" MiniRustSpec.Gen.Items.Lang.Step.Locks.items),
    (Prod.mk "spec/lang/step/operators.md" MiniRustSpec.Gen.Items.Lang.Step.Operators.items),
    (Prod.mk "spec/lang/step/statements.md" MiniRustSpec.Gen.Items.Lang.Step.Statements.items),
    (Prod.mk "spec/lang/step/terminators.md" MiniRustSpec.Gen.Items.Lang.Step.Terminators.items),
    (Prod.mk "spec/lang/syntax.md" MiniRustSpec.Gen.Items.Lang.Syntax.items),
    (Prod.mk "spec/lang/types.md" MiniRustSpec.Gen.Items.Lang.Types.items),
    (Prod.mk "spec/lang/values.md" MiniRustSpec.Gen.Items.Lang.Values.items),
    (Prod.mk "spec/lang/well-formed.md" MiniRustSpec.Gen.Items.Lang.WellFormed.items),
    (Prod.mk "spec/mem/basic.md" MiniRustSpec.Gen.Items.Mem.Basic.items),
    (Prod.mk "spec/mem/concurrent.md" MiniRustSpec.Gen.Items.Mem.Concurrent.items),
    (Prod.mk "spec/mem/interface.md" MiniRustSpec.Gen.Items.Mem.Interface.items),
    (Prod.mk "spec/mem/intptrcast.md" MiniRustSpec.Gen.Items.Mem.Intptrcast.items),
    (Prod.mk "spec/mem/pointer.md" MiniRustSpec.Gen.Items.Mem.Pointer.items),
    (Prod.mk "spec/mem/prelude.md" MiniRustSpec.Gen.Items.Mem.Prelude.items),
    (Prod.mk "spec/mem/tree_borrows/memory.md" MiniRustSpec.Gen.Items.Mem.TreeBorrows.Memory.items),
    (Prod.mk
      "spec/mem/tree_borrows/reborrow_settings.md"
      MiniRustSpec.Gen.Items.Mem.TreeBorrows.ReborrowSettings.items),
    (Prod.mk
      "spec/mem/tree_borrows/state_machine.md"
      MiniRustSpec.Gen.Items.Mem.TreeBorrows.StateMachine.items),
    (Prod.mk
      "spec/mem/tree_borrows/state_machine_protected.md"
      MiniRustSpec.Gen.Items.Mem.TreeBorrows.StateMachineProtected.items),
    (Prod.mk
      "spec/mem/tree_borrows/state_machine_unprotected.md"
      MiniRustSpec.Gen.Items.Mem.TreeBorrows.StateMachineUnprotected.items),
    (Prod.mk "spec/mem/tree_borrows/tree.md" MiniRustSpec.Gen.Items.Mem.TreeBorrows.Tree.items),
    (Prod.mk "spec/prelude/main.md" MiniRustSpec.Gen.Items.Prelude.Main.items),
    (Prod.mk "spec/prelude/target.md" MiniRustSpec.Gen.Items.Prelude.Target.items)]

end MiniRustSpec.Generated
