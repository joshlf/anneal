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
`spec/lang/machine.md` (commit `d821c6e3`), one Lean definition per item, in source order.
-/

import MiniRustSpec.Meta.Syntax

set_option maxRecDepth 100000

namespace MiniRustSpec.Gen.Items.Lang.Machine

open MiniRustSpec.Syntax

/-- Path of the upstream file these items were extracted from. -/
def sourceFile : String := "spec/lang/machine.md"

/-- SHA-256 of the upstream file. -/
def sourceSha256 : String := "121c624125adf8d8d988b6d088d8e85687e8a275ee703a80e486dcb05dfbd91c"

/-- `spec/lang/machine.md:11` -/
def struct_Machine : Item :=
  (Item.struct
    [
      (Attr.mk
        true
        "doc"
        (AttrMeta.nameValue
          " This type contains everything that needs to be tracked during the execution")),
      (Attr.mk true "doc" (AttrMeta.nameValue " of a MiniRust program.")),
      (Attr.mk true "no_obj" AttrMeta.path)]
    Visibility.pub
    "Machine"
    (Generics.mk
      [
        (GenericParam.type
          []
          "M"
          [
            (TypeParamBound.trait
              false
              false
              []
              (Path.mk false [(PathSegment.mk "Memory" PathArguments.none)]))]
          none)]
      [])
    (Fields.named
      [
        (Field.mk
          [(Attr.mk true "doc" (AttrMeta.nameValue " The program we are executing."))]
          Visibility.inherited
          (some "prog")
          (Ty.path none (Path.mk false [(PathSegment.mk "Program" PathArguments.none)]))),
        (Field.mk
          [(Attr.mk true "doc" (AttrMeta.nameValue " The contents of memory."))]
          Visibility.inherited
          (some "mem")
          (Ty.path
            none
            (Path.mk
              false
              [
                (PathSegment.mk
                  "ConcurrentMemory"
                  (PathArguments.angleBracketed
                    false
                    [
                      (GenericArgument.type
                        (Ty.path none (Path.mk false [(PathSegment.mk "M" PathArguments.none)])))]))]))),
        (Field.mk
          [
            (Attr.mk
              true
              "doc"
              (AttrMeta.nameValue " The state of the integer-pointer cast subsystem."))]
          Visibility.inherited
          (some "intptrcast")
          (Ty.path
            none
            (Path.mk
              false
              [
                (PathSegment.mk
                  "IntPtrCast"
                  (PathArguments.angleBracketed
                    false
                    [
                      (GenericArgument.type
                        (Ty.path
                          none
                          (Path.mk
                            false
                            [
                              (PathSegment.mk "M" PathArguments.none),
                              (PathSegment.mk "Provenance" PathArguments.none)])))]))]))),
        (Field.mk
          [(Attr.mk true "doc" (AttrMeta.nameValue " The threads (in particular, their stacks)."))]
          Visibility.inherited
          (some "threads")
          (Ty.path
            none
            (Path.mk
              false
              [
                (PathSegment.mk
                  "List"
                  (PathArguments.angleBracketed
                    false
                    [
                      (GenericArgument.type
                        (Ty.path
                          none
                          (Path.mk
                            false
                            [
                              (PathSegment.mk
                                "Thread"
                                (PathArguments.angleBracketed
                                  false
                                  [
                                    (GenericArgument.type
                                      (Ty.path
                                        none
                                        (Path.mk false [(PathSegment.mk "M" PathArguments.none)])))]))])))]))]))),
        (Field.mk
          [
            (Attr.mk
              true
              "doc"
              (AttrMeta.nameValue " The currently / most recently active thread."))]
          Visibility.inherited
          (some "active_thread")
          (Ty.path none (Path.mk false [(PathSegment.mk "ThreadId" PathArguments.none)]))),
        (Field.mk
          [
            (Attr.mk
              true
              "doc"
              (AttrMeta.nameValue " A set of threads that have been synchronized.")),
            (Attr.mk
              true
              "doc"
              (AttrMeta.nameValue
                " A thread being added here in a given step means that if the very next step is")),
            (Attr.mk
              true
              "doc"
              (AttrMeta.nameValue
                " by that thread, we do *not* do data race detection: there was synchronization")),
            (Attr.mk
              true
              "doc"
              (AttrMeta.nameValue
                " between these two steps, so any potential accesses are not racing."))]
          Visibility.inherited
          (some "synchronized_threads")
          (Ty.path
            none
            (Path.mk
              false
              [
                (PathSegment.mk
                  "Set"
                  (PathArguments.angleBracketed
                    false
                    [
                      (GenericArgument.type
                        (Ty.path
                          none
                          (Path.mk false [(PathSegment.mk "ThreadId" PathArguments.none)])))]))]))),
        (Field.mk
          [(Attr.mk true "doc" (AttrMeta.nameValue " The Locks"))]
          Visibility.inherited
          (some "locks")
          (Ty.path
            none
            (Path.mk
              false
              [
                (PathSegment.mk
                  "List"
                  (PathArguments.angleBracketed
                    false
                    [
                      (GenericArgument.type
                        (Ty.path
                          none
                          (Path.mk false [(PathSegment.mk "LockState" PathArguments.none)])))]))]))),
        (Field.mk
          [
            (Attr.mk
              true
              "doc"
              (AttrMeta.nameValue
                " Stores a pointer to each of the global allocations, which are all `Sized`."))]
          Visibility.inherited
          (some "global_ptrs")
          (Ty.path
            none
            (Path.mk
              false
              [
                (PathSegment.mk
                  "Map"
                  (PathArguments.angleBracketed
                    false
                    [
                      (GenericArgument.type
                        (Ty.path
                          none
                          (Path.mk false [(PathSegment.mk "GlobalName" PathArguments.none)]))),
                      (GenericArgument.type
                        (Ty.path
                          none
                          (Path.mk
                            false
                            [
                              (PathSegment.mk
                                "ThinPointer"
                                (PathArguments.angleBracketed
                                  false
                                  [
                                    (GenericArgument.type
                                      (Ty.path
                                        none
                                        (Path.mk
                                          false
                                          [
                                            (PathSegment.mk "M" PathArguments.none),
                                            (PathSegment.mk "Provenance" PathArguments.none)])))]))])))]))]))),
        (Field.mk
          [(Attr.mk true "doc" (AttrMeta.nameValue " Stores a pointer for each function name."))]
          Visibility.inherited
          (some "fn_ptrs")
          (Ty.path
            none
            (Path.mk
              false
              [
                (PathSegment.mk
                  "Map"
                  (PathArguments.angleBracketed
                    false
                    [
                      (GenericArgument.type
                        (Ty.path
                          none
                          (Path.mk false [(PathSegment.mk "FnName" PathArguments.none)]))),
                      (GenericArgument.type
                        (Ty.path
                          none
                          (Path.mk
                            false
                            [
                              (PathSegment.mk
                                "ThinPointer"
                                (PathArguments.angleBracketed
                                  false
                                  [
                                    (GenericArgument.type
                                      (Ty.path
                                        none
                                        (Path.mk
                                          false
                                          [
                                            (PathSegment.mk "M" PathArguments.none),
                                            (PathSegment.mk "Provenance" PathArguments.none)])))]))])))]))]))),
        (Field.mk
          [(Attr.mk true "doc" (AttrMeta.nameValue " Stores a pointer for each vtable."))]
          Visibility.inherited
          (some "vtable_ptrs")
          (Ty.path
            none
            (Path.mk
              false
              [
                (PathSegment.mk
                  "Map"
                  (PathArguments.angleBracketed
                    false
                    [
                      (GenericArgument.type
                        (Ty.path
                          none
                          (Path.mk false [(PathSegment.mk "VTableName" PathArguments.none)]))),
                      (GenericArgument.type
                        (Ty.path
                          none
                          (Path.mk
                            false
                            [
                              (PathSegment.mk
                                "ThinPointer"
                                (PathArguments.angleBracketed
                                  false
                                  [
                                    (GenericArgument.type
                                      (Ty.path
                                        none
                                        (Path.mk
                                          false
                                          [
                                            (PathSegment.mk "M" PathArguments.none),
                                            (PathSegment.mk "Provenance" PathArguments.none)])))]))])))]))]))),
        (Field.mk
          [
            (Attr.mk
              true
              "doc"
              (AttrMeta.nameValue " This is where the `PrintStdout` intrinsic writes to."))]
          Visibility.inherited
          (some "stdout")
          (Ty.path none (Path.mk false [(PathSegment.mk "DynWrite" PathArguments.none)]))),
        (Field.mk
          [
            (Attr.mk
              true
              "doc"
              (AttrMeta.nameValue " This is where the `PrintStderr` intrinsic writes to."))]
          Visibility.inherited
          (some "stderr")
          (Ty.path none (Path.mk false [(PathSegment.mk "DynWrite" PathArguments.none)])))]))

/-- `spec/lang/machine.md:54` -/
def struct_StackFrame : Item :=
  (Item.struct
    [(Attr.mk true "doc" (AttrMeta.nameValue " The data that makes up a stack frame."))]
    Visibility.inherited
    "StackFrame"
    (Generics.mk
      [
        (GenericParam.type
          []
          "M"
          [
            (TypeParamBound.trait
              false
              false
              []
              (Path.mk false [(PathSegment.mk "Memory" PathArguments.none)]))]
          none)]
      [])
    (Fields.named
      [
        (Field.mk
          [(Attr.mk true "doc" (AttrMeta.nameValue " The function this stack frame belongs to."))]
          Visibility.inherited
          (some "func")
          (Ty.path none (Path.mk false [(PathSegment.mk "Function" PathArguments.none)]))),
        (Field.mk
          [
            (Attr.mk
              true
              "doc"
              (AttrMeta.nameValue
                " For each live local, the location in memory where its value is stored."))]
          Visibility.inherited
          (some "locals")
          (Ty.path
            none
            (Path.mk
              false
              [
                (PathSegment.mk
                  "Map"
                  (PathArguments.angleBracketed
                    false
                    [
                      (GenericArgument.type
                        (Ty.path
                          none
                          (Path.mk false [(PathSegment.mk "LocalName" PathArguments.none)]))),
                      (GenericArgument.type
                        (Ty.path
                          none
                          (Path.mk
                            false
                            [
                              (PathSegment.mk
                                "ThinPointer"
                                (PathArguments.angleBracketed
                                  false
                                  [
                                    (GenericArgument.type
                                      (Ty.path
                                        none
                                        (Path.mk
                                          false
                                          [
                                            (PathSegment.mk "M" PathArguments.none),
                                            (PathSegment.mk "Provenance" PathArguments.none)])))]))])))]))]))),
        (Field.mk
          [
            (Attr.mk
              true
              "doc"
              (AttrMeta.nameValue
                " Expresses what happens after the callee (this function) returns or resumes unwinding."))]
          Visibility.inherited
          (some "stack_pop_action")
          (Ty.path
            none
            (Path.mk
              false
              [
                (PathSegment.mk
                  "StackPopAction"
                  (PathArguments.angleBracketed
                    false
                    [
                      (GenericArgument.type
                        (Ty.path none (Path.mk false [(PathSegment.mk "M" PathArguments.none)])))]))]))),
        (Field.mk
          [
            (Attr.mk
              true
              "doc"
              (AttrMeta.nameValue
                " `next_block` and `next_stmt` describe the next statement/terminator to execute (the \"program counter\").")),
            (Attr.mk true "doc" (AttrMeta.nameValue " `next_block` identifies the basic block,"))]
          Visibility.inherited
          (some "next_block")
          (Ty.path none (Path.mk false [(PathSegment.mk "BbName" PathArguments.none)]))),
        (Field.mk
          [
            (Attr.mk
              true
              "doc"
              (AttrMeta.nameValue
                " If `next_stmt` is equal to the number of statements in this block (an")),
            (Attr.mk
              true
              "doc"
              (AttrMeta.nameValue
                " out-of-bounds index in the statement list), it refers to the terminator."))]
          Visibility.inherited
          (some "next_stmt")
          (Ty.path none (Path.mk false [(PathSegment.mk "Int" PathArguments.none)]))),
        (Field.mk
          [
            (Attr.mk
              true
              "doc"
              (AttrMeta.nameValue
                " The memory model is given the ability to track some extra per-frame data."))]
          Visibility.inherited
          (some "extra")
          (Ty.path
            none
            (Path.mk
              false
              [
                (PathSegment.mk "M" PathArguments.none),
                (PathSegment.mk "FrameExtra" PathArguments.none)])))]))

/-- `spec/lang/machine.md:77` -/
def enum_StackPopAction : Item :=
  (Item.enum
    [
      (Attr.mk
        true
        "doc"
        (AttrMeta.nameValue " Defines the behavior when the function returns or resumes unwinding."))]
    Visibility.inherited
    "StackPopAction"
    (Generics.mk
      [
        (GenericParam.type
          []
          "M"
          [
            (TypeParamBound.trait
              false
              false
              []
              (Path.mk false [(PathSegment.mk "Memory" PathArguments.none)]))]
          none)]
      [])
    [
      (Variant.mk
        [
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue
              " This is the bottom of the stack, there is nothing left to do in this thread."))]
        "BottomOfStack"
        Fields.unit
        none),
      (Variant.mk
        [(Attr.mk true "doc" (AttrMeta.nameValue " Go back to the caller."))]
        "BackToCaller"
        (Fields.named
          [
            (Field.mk
              [
                (Attr.mk
                  true
                  "doc"
                  (AttrMeta.nameValue " The basic block to jump to when the callee returns.")),
                (Attr.mk
                  true
                  "doc"
                  (AttrMeta.nameValue " If `None`, UB will be raised when the callee returns."))]
              Visibility.inherited
              (some "next_block")
              (Ty.path
                none
                (Path.mk
                  false
                  [
                    (PathSegment.mk
                      "Option"
                      (PathArguments.angleBracketed
                        false
                        [
                          (GenericArgument.type
                            (Ty.path
                              none
                              (Path.mk false [(PathSegment.mk "BbName" PathArguments.none)])))]))]))),
            (Field.mk
              [
                (Attr.mk
                  true
                  "doc"
                  (AttrMeta.nameValue
                    " The basic block to jump to when the callee resumes unwinding.")),
                (Attr.mk
                  true
                  "doc"
                  (AttrMeta.nameValue
                    " If `None`, UB will be raised when the callee resumes unwinding."))]
              Visibility.inherited
              (some "unwind_block")
              (Ty.path
                none
                (Path.mk
                  false
                  [
                    (PathSegment.mk
                      "Option"
                      (PathArguments.angleBracketed
                        false
                        [
                          (GenericArgument.type
                            (Ty.path
                              none
                              (Path.mk false [(PathSegment.mk "BbName" PathArguments.none)])))]))]))),
            (Field.mk
              [
                (Attr.mk
                  true
                  "doc"
                  (AttrMeta.nameValue
                    " The location where the caller wants to see the return value.")),
                (Attr.mk
                  true
                  "doc"
                  (AttrMeta.nameValue
                    " The caller type already been checked to be suitably compatible with the callee return type."))]
              Visibility.inherited
              (some "ret_val_ptr")
              (Ty.path
                none
                (Path.mk
                  false
                  [
                    (PathSegment.mk
                      "ThinPointer"
                      (PathArguments.angleBracketed
                        false
                        [
                          (GenericArgument.type
                            (Ty.path
                              none
                              (Path.mk
                                false
                                [
                                  (PathSegment.mk "M" PathArguments.none),
                                  (PathSegment.mk "Provenance" PathArguments.none)])))]))])))])
        none)])

/-- `spec/lang/machine.md:99` -/
def struct_Thread : Item :=
  (Item.struct
    []
    Visibility.pub
    "Thread"
    (Generics.mk
      [
        (GenericParam.type
          []
          "M"
          [
            (TypeParamBound.trait
              false
              false
              []
              (Path.mk false [(PathSegment.mk "Memory" PathArguments.none)]))]
          none)]
      [])
    (Fields.named
      [
        (Field.mk
          [
            (Attr.mk
              true
              "doc"
              (AttrMeta.nameValue
                " The stack. This is only the \"control\" part of the stack; the \"data\" part")),
            (Attr.mk
              true
              "doc"
              (AttrMeta.nameValue
                " lives in memory (and stack and memory are completely disjoint concepts")),
            (Attr.mk true "doc" (AttrMeta.nameValue " in the Abstract Machine)."))]
          Visibility.inherited
          (some "stack")
          (Ty.path
            none
            (Path.mk
              false
              [
                (PathSegment.mk
                  "List"
                  (PathArguments.angleBracketed
                    false
                    [
                      (GenericArgument.type
                        (Ty.path
                          none
                          (Path.mk
                            false
                            [
                              (PathSegment.mk
                                "StackFrame"
                                (PathArguments.angleBracketed
                                  false
                                  [
                                    (GenericArgument.type
                                      (Ty.path
                                        none
                                        (Path.mk false [(PathSegment.mk "M" PathArguments.none)])))]))])))]))]))),
        (Field.mk
          [
            (Attr.mk
              true
              "doc"
              (AttrMeta.nameValue
                " Stores whether the thread is ready to run, blocked, or terminated."))]
          Visibility.inherited
          (some "state")
          (Ty.path none (Path.mk false [(PathSegment.mk "ThreadState" PathArguments.none)]))),
        (Field.mk
          [(Attr.mk true "doc" (AttrMeta.nameValue " Stores the unwind payloads."))]
          Visibility.inherited
          (some "unwind_payloads")
          (Ty.path
            none
            (Path.mk
              false
              [
                (PathSegment.mk
                  "List"
                  (PathArguments.angleBracketed
                    false
                    [
                      (GenericArgument.type
                        (Ty.path
                          none
                          (Path.mk
                            false
                            [
                              (PathSegment.mk
                                "ThinPointer"
                                (PathArguments.angleBracketed
                                  false
                                  [
                                    (GenericArgument.type
                                      (Ty.path
                                        none
                                        (Path.mk
                                          false
                                          [
                                            (PathSegment.mk "M" PathArguments.none),
                                            (PathSegment.mk "Provenance" PathArguments.none)])))]))])))]))])))]))

/-- `spec/lang/machine.md:112` -/
def enum_ThreadState : Item :=
  (Item.enum
    []
    Visibility.pub
    "ThreadState"
    (Generics.mk [] [])
    [
      (Variant.mk
        [(Attr.mk true "doc" (AttrMeta.nameValue " The thread is enabled and can get executed."))]
        "Enabled"
        Fields.unit
        none),
      (Variant.mk
        [
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue
              " The thread is trying to join another thread and is blocked until that thread finishes."))]
        "BlockedOnJoin"
        (Fields.unnamed
          [
            (Field.mk
              []
              Visibility.inherited
              none
              (Ty.path none (Path.mk false [(PathSegment.mk "ThreadId" PathArguments.none)])))])
        none),
      (Variant.mk
        [(Attr.mk true "doc" (AttrMeta.nameValue " The thread is waiting to acquire a lock."))]
        "BlockedOnLock"
        (Fields.unnamed
          [
            (Field.mk
              []
              Visibility.inherited
              none
              (Ty.path none (Path.mk false [(PathSegment.mk "LockId" PathArguments.none)])))])
        none),
      (Variant.mk
        [(Attr.mk true "doc" (AttrMeta.nameValue " The thread has terminated."))]
        "Terminated"
        Fields.unit
        none)])

/-- `spec/lang/machine.md:128` -/
def impl_Machine__new : Item :=
  (Item.impl
    []
    false
    false
    (Generics.mk
      [
        (GenericParam.type
          []
          "M"
          [
            (TypeParamBound.trait
              false
              false
              []
              (Path.mk false [(PathSegment.mk "Memory" PathArguments.none)]))]
          none)]
      [])
    false
    none
    (Ty.path
      none
      (Path.mk
        false
        [
          (PathSegment.mk
            "Machine"
            (PathArguments.angleBracketed
              false
              [
                (GenericArgument.type
                  (Ty.path none (Path.mk false [(PathSegment.mk "M" PathArguments.none)])))]))]))
    [
      (ImplItem.fn
        []
        Visibility.pub
        false
        (Signature.mk
          false
          false
          false
          none
          "new"
          (Generics.mk [] [])
          [
            (FnArg.typed
              []
              (Pat.ident false false "prog" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "Program" PathArguments.none)]))),
            (FnArg.typed
              []
              (Pat.ident false false "mem_params" none)
              (Ty.path
                none
                (Path.mk
                  false
                  [
                    (PathSegment.mk "M" PathArguments.none),
                    (PathSegment.mk "Params" PathArguments.none)]))),
            (FnArg.typed
              []
              (Pat.ident false false "stdout" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "DynWrite" PathArguments.none)]))),
            (FnArg.typed
              []
              (Pat.ident false false "stderr" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "DynWrite" PathArguments.none)])))]
          false
          (some
            (Ty.path
              none
              (Path.mk
                false
                [
                  (PathSegment.mk
                    "NdResult"
                    (PathArguments.angleBracketed
                      false
                      [
                        (GenericArgument.type
                          (Ty.path
                            none
                            (Path.mk
                              false
                              [
                                (PathSegment.mk
                                  "Machine"
                                  (PathArguments.angleBracketed
                                    false
                                    [
                                      (GenericArgument.type
                                        (Ty.path
                                          none
                                          (Path.mk false [(PathSegment.mk "M" PathArguments.none)])))]))])))]))]))))
        (Block.mk
          [
            (Stmt.expr
              (Expr.tryExpr
                (Expr.methodCall
                  (Expr.path none (Path.mk false [(PathSegment.mk "prog" PathArguments.none)]))
                  "check_wf"
                  (some
                    [
                      (GenericArgument.type
                        (Ty.path
                          none
                          (Path.mk
                            false
                            [
                              (PathSegment.mk "M" PathArguments.none),
                              (PathSegment.mk "T" PathArguments.none)])))])
                  []))
              true),
            (Stmt.letStmt
              []
              (Pat.ident false true "mem" none)
              (some
                (Expr.call
                  (Expr.path
                    none
                    (Path.mk
                      false
                      [
                        (PathSegment.mk
                          "ConcurrentMemory"
                          (PathArguments.angleBracketed
                            true
                            [
                              (GenericArgument.type
                                (Ty.path
                                  none
                                  (Path.mk false [(PathSegment.mk "M" PathArguments.none)])))])),
                        (PathSegment.mk "new" PathArguments.none)]))
                  [
                    (Expr.path
                      none
                      (Path.mk false [(PathSegment.mk "mem_params" PathArguments.none)]))]))
              none),
            (Stmt.letStmt
              []
              (Pat.ident false true "global_ptrs" none)
              (some
                (Expr.call
                  (Expr.path
                    none
                    (Path.mk
                      false
                      [
                        (PathSegment.mk "Map" PathArguments.none),
                        (PathSegment.mk "new" PathArguments.none)]))
                  []))
              none),
            (Stmt.letStmt
              []
              (Pat.ident false true "fn_ptrs" none)
              (some
                (Expr.call
                  (Expr.path
                    none
                    (Path.mk
                      false
                      [
                        (PathSegment.mk "Map" PathArguments.none),
                        (PathSegment.mk "new" PathArguments.none)]))
                  []))
              none),
            (Stmt.letStmt
              []
              (Pat.ident false true "vtable_ptrs" none)
              (some
                (Expr.call
                  (Expr.path
                    none
                    (Path.mk
                      false
                      [
                        (PathSegment.mk "Map" PathArguments.none),
                        (PathSegment.mk "new" PathArguments.none)]))
                  []))
              none),
            (Stmt.expr
              (Expr.forLoop
                none
                (Pat.tuple
                  [
                    (Pat.ident false false "global_name" none),
                    (Pat.ident false false "global" none)])
                (Expr.field
                  (Expr.path none (Path.mk false [(PathSegment.mk "prog" PathArguments.none)]))
                  (Member.named "globals"))
                (Block.mk
                  [
                    (Stmt.letStmt
                      []
                      (Pat.ident false false "size" none)
                      (some
                        (Expr.methodCall
                          (Expr.call
                            (Expr.path
                              none
                              (Path.mk
                                false
                                [
                                  (PathSegment.mk "Size" PathArguments.none),
                                  (PathSegment.mk "from_bytes" PathArguments.none)]))
                            [
                              (Expr.methodCall
                                (Expr.field
                                  (Expr.path
                                    none
                                    (Path.mk false [(PathSegment.mk "global" PathArguments.none)]))
                                  (Member.named "bytes"))
                                "len"
                                none
                                [])])
                          "unwrap"
                          none
                          []))
                      none),
                    (Stmt.letStmt
                      []
                      (Pat.ident false false "alloc" none)
                      (some
                        (Expr.tryExpr
                          (Expr.methodCall
                            (Expr.path
                              none
                              (Path.mk false [(PathSegment.mk "mem" PathArguments.none)]))
                            "allocate"
                            none
                            [
                              (Expr.path
                                none
                                (Path.mk
                                  false
                                  [
                                    (PathSegment.mk "AllocationKind" PathArguments.none),
                                    (PathSegment.mk "Global" PathArguments.none)])),
                              (Expr.path
                                none
                                (Path.mk false [(PathSegment.mk "size" PathArguments.none)])),
                              (Expr.field
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "global" PathArguments.none)]))
                                (Member.named "align"))])))
                      none),
                    (Stmt.expr
                      (Expr.methodCall
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "global_ptrs" PathArguments.none)]))
                        "insert"
                        none
                        [
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "global_name" PathArguments.none)])),
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "alloc" PathArguments.none)]))])
                      true)]))
              false),
            (Stmt.expr
              (Expr.forLoop
                none
                (Pat.tuple
                  [
                    (Pat.ident false false "global_name" none),
                    (Pat.ident false false "global" none)])
                (Expr.field
                  (Expr.path none (Path.mk false [(PathSegment.mk "prog" PathArguments.none)]))
                  (Member.named "globals"))
                (Block.mk
                  [
                    (Stmt.letStmt
                      []
                      (Pat.ident false true "bytes" none)
                      (some
                        (Expr.methodCall
                          (Expr.field
                            (Expr.path
                              none
                              (Path.mk false [(PathSegment.mk "global" PathArguments.none)]))
                            (Member.named "bytes"))
                          "map"
                          none
                          [
                            (Expr.closure
                              false
                              [(Pat.ident false false "b" none)]
                              none
                              (Expr.matchExpr
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "b" PathArguments.none)]))
                                [
                                  (Arm.mk
                                    []
                                    (Pat.tupleStruct
                                      none
                                      (Path.mk false [(PathSegment.mk "Some" PathArguments.none)])
                                      [(Pat.ident false false "x" none)])
                                    none
                                    (Expr.call
                                      (Expr.path
                                        none
                                        (Path.mk
                                          false
                                          [
                                            (PathSegment.mk "AbstractByte" PathArguments.none),
                                            (PathSegment.mk "Init" PathArguments.none)]))
                                      [
                                        (Expr.path
                                          none
                                          (Path.mk false [(PathSegment.mk "x" PathArguments.none)])),
                                        (Expr.path
                                          none
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "None" PathArguments.none)]))])),
                                  (Arm.mk
                                    []
                                    (Pat.ident false false "None" none)
                                    none
                                    (Expr.path
                                      none
                                      (Path.mk
                                        false
                                        [
                                          (PathSegment.mk "AbstractByte" PathArguments.none),
                                          (PathSegment.mk "Uninit" PathArguments.none)])))]))]))
                      none),
                    (Stmt.expr
                      (Expr.forLoop
                        none
                        (Pat.tuple
                          [
                            (Pat.ident false false "i" none),
                            (Pat.ident false false "relocation" none)])
                        (Expr.field
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "global" PathArguments.none)]))
                          (Member.named "relocations"))
                        (Block.mk
                          [
                            (Stmt.letStmt
                              []
                              (Pat.ident false false "ptr" none)
                              (some
                                (Expr.methodCall
                                  (Expr.index
                                    (Expr.path
                                      none
                                      (Path.mk
                                        false
                                        [(PathSegment.mk "global_ptrs" PathArguments.none)]))
                                    (Expr.field
                                      (Expr.path
                                        none
                                        (Path.mk
                                          false
                                          [(PathSegment.mk "relocation" PathArguments.none)]))
                                      (Member.named "name")))
                                  "wrapping_offset"
                                  (some
                                    [
                                      (GenericArgument.type
                                        (Ty.path
                                          none
                                          (Path.mk
                                            false
                                            [
                                              (PathSegment.mk "M" PathArguments.none),
                                              (PathSegment.mk "T" PathArguments.none)])))])
                                  [
                                    (Expr.methodCall
                                      (Expr.field
                                        (Expr.path
                                          none
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "relocation" PathArguments.none)]))
                                        (Member.named "offset"))
                                      "bytes"
                                      none
                                      [])]))
                              none),
                            (Stmt.letStmt
                              []
                              (Pat.ident false false "encoded_ptr" none)
                              (some
                                (Expr.call
                                  (Expr.path
                                    none
                                    (Path.mk
                                      false
                                      [
                                        (PathSegment.mk
                                          "encode_ptr"
                                          (PathArguments.angleBracketed
                                            true
                                            [
                                              (GenericArgument.type
                                                (Ty.path
                                                  none
                                                  (Path.mk
                                                    false
                                                    [(PathSegment.mk "M" PathArguments.none)])))]))]))
                                  [
                                    (Expr.path
                                      none
                                      (Path.mk false [(PathSegment.mk "ptr" PathArguments.none)]))]))
                              none),
                            (Stmt.expr
                              (Expr.methodCall
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "bytes" PathArguments.none)]))
                                "write_subslice_at_index"
                                none
                                [
                                  (Expr.methodCall
                                    (Expr.path
                                      none
                                      (Path.mk false [(PathSegment.mk "i" PathArguments.none)]))
                                    "bytes"
                                    none
                                    []),
                                  (Expr.path
                                    none
                                    (Path.mk
                                      false
                                      [(PathSegment.mk "encoded_ptr" PathArguments.none)]))])
                              true)]))
                      false),
                    (Stmt.expr
                      (Expr.methodCall
                        (Expr.methodCall
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "mem" PathArguments.none)]))
                          "store"
                          none
                          [
                            (Expr.index
                              (Expr.path
                                none
                                (Path.mk false [(PathSegment.mk "global_ptrs" PathArguments.none)]))
                              (Expr.path
                                none
                                (Path.mk false [(PathSegment.mk "global_name" PathArguments.none)]))),
                            (Expr.path
                              none
                              (Path.mk false [(PathSegment.mk "bytes" PathArguments.none)])),
                            (Expr.field
                              (Expr.path
                                none
                                (Path.mk false [(PathSegment.mk "global" PathArguments.none)]))
                              (Member.named "align")),
                            (Expr.path
                              none
                              (Path.mk
                                false
                                [
                                  (PathSegment.mk "Atomicity" PathArguments.none),
                                  (PathSegment.mk "None" PathArguments.none)]))])
                        "unwrap"
                        none
                        [])
                      true)]))
              false),
            (Stmt.expr
              (Expr.forLoop
                none
                (Pat.tuple
                  [(Pat.ident false false "fn_name" none), (Pat.ident false false "_function" none)])
                (Expr.field
                  (Expr.path none (Path.mk false [(PathSegment.mk "prog" PathArguments.none)]))
                  (Member.named "functions"))
                (Block.mk
                  [
                    (Stmt.letStmt
                      []
                      (Pat.ident false false "alloc" none)
                      (some
                        (Expr.tryExpr
                          (Expr.methodCall
                            (Expr.path
                              none
                              (Path.mk false [(PathSegment.mk "mem" PathArguments.none)]))
                            "allocate"
                            none
                            [
                              (Expr.path
                                none
                                (Path.mk
                                  false
                                  [
                                    (PathSegment.mk "AllocationKind" PathArguments.none),
                                    (PathSegment.mk "Function" PathArguments.none)])),
                              (Expr.path
                                none
                                (Path.mk
                                  false
                                  [
                                    (PathSegment.mk "Size" PathArguments.none),
                                    (PathSegment.mk "ZERO" PathArguments.none)])),
                              (Expr.path
                                none
                                (Path.mk
                                  false
                                  [
                                    (PathSegment.mk "Align" PathArguments.none),
                                    (PathSegment.mk "ONE" PathArguments.none)]))])))
                      none),
                    (Stmt.expr
                      (Expr.methodCall
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "fn_ptrs" PathArguments.none)]))
                        "insert"
                        none
                        [
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "fn_name" PathArguments.none)])),
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "alloc" PathArguments.none)]))])
                      true)]))
              false),
            (Stmt.expr
              (Expr.forLoop
                none
                (Pat.tuple
                  [
                    (Pat.ident false false "vtable_name" none),
                    (Pat.ident false false "_vtable" none)])
                (Expr.field
                  (Expr.path none (Path.mk false [(PathSegment.mk "prog" PathArguments.none)]))
                  (Member.named "vtables"))
                (Block.mk
                  [
                    (Stmt.letStmt
                      []
                      (Pat.ident false false "alloc" none)
                      (some
                        (Expr.tryExpr
                          (Expr.methodCall
                            (Expr.path
                              none
                              (Path.mk false [(PathSegment.mk "mem" PathArguments.none)]))
                            "allocate"
                            none
                            [
                              (Expr.path
                                none
                                (Path.mk
                                  false
                                  [
                                    (PathSegment.mk "AllocationKind" PathArguments.none),
                                    (PathSegment.mk "VTable" PathArguments.none)])),
                              (Expr.path
                                none
                                (Path.mk
                                  false
                                  [
                                    (PathSegment.mk "Size" PathArguments.none),
                                    (PathSegment.mk "ZERO" PathArguments.none)])),
                              (Expr.path
                                none
                                (Path.mk
                                  false
                                  [
                                    (PathSegment.mk "Align" PathArguments.none),
                                    (PathSegment.mk "ONE" PathArguments.none)]))])))
                      none),
                    (Stmt.expr
                      (Expr.methodCall
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "vtable_ptrs" PathArguments.none)]))
                        "insert"
                        none
                        [
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "vtable_name" PathArguments.none)])),
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "alloc" PathArguments.none)]))])
                      true)]))
              false),
            (Stmt.letStmt
              []
              (Pat.ident false true "machine" none)
              (some
                (Expr.struct
                  none
                  (Path.mk false [(PathSegment.mk "Machine" PathArguments.none)])
                  [
                    (FieldValue.mk
                      []
                      (Member.named "prog")
                      true
                      (Expr.path none (Path.mk false [(PathSegment.mk "prog" PathArguments.none)]))),
                    (FieldValue.mk
                      []
                      (Member.named "mem")
                      true
                      (Expr.path none (Path.mk false [(PathSegment.mk "mem" PathArguments.none)]))),
                    (FieldValue.mk
                      []
                      (Member.named "intptrcast")
                      false
                      (Expr.call
                        (Expr.path
                          none
                          (Path.mk
                            false
                            [
                              (PathSegment.mk "IntPtrCast" PathArguments.none),
                              (PathSegment.mk "new" PathArguments.none)]))
                        [])),
                    (FieldValue.mk
                      []
                      (Member.named "global_ptrs")
                      true
                      (Expr.path
                        none
                        (Path.mk false [(PathSegment.mk "global_ptrs" PathArguments.none)]))),
                    (FieldValue.mk
                      []
                      (Member.named "fn_ptrs")
                      true
                      (Expr.path
                        none
                        (Path.mk false [(PathSegment.mk "fn_ptrs" PathArguments.none)]))),
                    (FieldValue.mk
                      []
                      (Member.named "vtable_ptrs")
                      true
                      (Expr.path
                        none
                        (Path.mk false [(PathSegment.mk "vtable_ptrs" PathArguments.none)]))),
                    (FieldValue.mk
                      []
                      (Member.named "threads")
                      false
                      (Expr.macro
                        (Macro.mk
                          (Path.mk false [(PathSegment.mk "list" PathArguments.none)])
                          MacroDelimiter.bracket
                          (MacroBody.exprs [] false)))),
                    (FieldValue.mk
                      []
                      (Member.named "locks")
                      false
                      (Expr.call
                        (Expr.path
                          none
                          (Path.mk
                            false
                            [
                              (PathSegment.mk "List" PathArguments.none),
                              (PathSegment.mk "new" PathArguments.none)]))
                        [])),
                    (FieldValue.mk
                      []
                      (Member.named "active_thread")
                      false
                      (Expr.path
                        none
                        (Path.mk
                          false
                          [
                            (PathSegment.mk "ThreadId" PathArguments.none),
                            (PathSegment.mk "ZERO" PathArguments.none)]))),
                    (FieldValue.mk
                      []
                      (Member.named "synchronized_threads")
                      false
                      (Expr.call
                        (Expr.path
                          none
                          (Path.mk
                            false
                            [
                              (PathSegment.mk "Set" PathArguments.none),
                              (PathSegment.mk "new" PathArguments.none)]))
                        [])),
                    (FieldValue.mk
                      []
                      (Member.named "stdout")
                      true
                      (Expr.path
                        none
                        (Path.mk false [(PathSegment.mk "stdout" PathArguments.none)]))),
                    (FieldValue.mk
                      []
                      (Member.named "stderr")
                      true
                      (Expr.path
                        none
                        (Path.mk false [(PathSegment.mk "stderr" PathArguments.none)])))]
                  false
                  none))
              none),
            (Stmt.letStmt
              []
              (Pat.ident false false "start_fn" none)
              (some
                (Expr.index
                  (Expr.field
                    (Expr.path none (Path.mk false [(PathSegment.mk "prog" PathArguments.none)]))
                    (Member.named "functions"))
                  (Expr.field
                    (Expr.path none (Path.mk false [(PathSegment.mk "prog" PathArguments.none)]))
                    (Member.named "start"))))
              none),
            (Stmt.expr
              (Expr.tryExpr
                (Expr.methodCall
                  (Expr.path none (Path.mk false [(PathSegment.mk "machine" PathArguments.none)]))
                  "new_thread"
                  none
                  [
                    (Expr.path
                      none
                      (Path.mk false [(PathSegment.mk "start_fn" PathArguments.none)])),
                    (Expr.macro
                      (Macro.mk
                        (Path.mk false [(PathSegment.mk "list" PathArguments.none)])
                        MacroDelimiter.bracket
                        (MacroBody.exprs [] false)))]))
              true),
            (Stmt.expr
              (Expr.call
                (Expr.path none (Path.mk false [(PathSegment.mk "ret" PathArguments.none)]))
                [(Expr.path none (Path.mk false [(PathSegment.mk "machine" PathArguments.none)]))])
              false)])),
      (ImplItem.fn
        [
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue
              " To run a MiniRust program, call this in a loop until it throws an `Err` (UB or termination)."))]
        Visibility.pub
        false
        (Signature.mk
          false
          false
          false
          none
          "step"
          (Generics.mk [] [])
          [(FnArg.receiver [] true none true none)]
          false
          (some (Ty.path none (Path.mk false [(PathSegment.mk "NdResult" PathArguments.none)]))))
        (Block.mk
          [
            (Stmt.expr
              (Expr.ite
                (Expr.unary
                  UnOp.not
                  (Expr.methodCall
                    (Expr.field
                      (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                      (Member.named "threads"))
                    "any"
                    none
                    [
                      (Expr.closure
                        false
                        [(Pat.ident false false "thread" none)]
                        none
                        (Expr.binary
                          (Expr.field
                            (Expr.path
                              none
                              (Path.mk false [(PathSegment.mk "thread" PathArguments.none)]))
                            (Member.named "state"))
                          BinOp.eq
                          (Expr.path
                            none
                            (Path.mk
                              false
                              [
                                (PathSegment.mk "ThreadState" PathArguments.none),
                                (PathSegment.mk "Enabled" PathArguments.none)]))))]))
                (Block.mk
                  [
                    (Stmt.macro
                      []
                      (Macro.mk
                        (Path.mk false [(PathSegment.mk "throw_deadlock" PathArguments.none)])
                        MacroDelimiter.paren
                        (MacroBody.exprs [] false))
                      true)])
                none)
              false),
            (Stmt.letStmt
              []
              (Pat.ident false false "prev_step_information" none)
              (some
                (Expr.methodCall
                  (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                  "reset_data_race_tracking"
                  none
                  []))
              none),
            (Stmt.letStmt
              []
              (Pat.ident false false "distr" none)
              (some
                (Expr.struct
                  none
                  (Path.mk
                    false
                    [
                      (PathSegment.mk "libspecr" PathArguments.none),
                      (PathSegment.mk "IntDistribution" PathArguments.none)])
                  [
                    (FieldValue.mk
                      []
                      (Member.named "start")
                      false
                      (Expr.path
                        none
                        (Path.mk
                          false
                          [
                            (PathSegment.mk "Int" PathArguments.none),
                            (PathSegment.mk "ZERO" PathArguments.none)]))),
                    (FieldValue.mk
                      []
                      (Member.named "end")
                      false
                      (Expr.call
                        (Expr.path
                          none
                          (Path.mk
                            false
                            [
                              (PathSegment.mk "Int" PathArguments.none),
                              (PathSegment.mk "from" PathArguments.none)]))
                        [
                          (Expr.methodCall
                            (Expr.field
                              (Expr.path
                                none
                                (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                              (Member.named "threads"))
                            "len"
                            none
                            [])])),
                    (FieldValue.mk
                      []
                      (Member.named "divisor")
                      false
                      (Expr.path
                        none
                        (Path.mk
                          false
                          [
                            (PathSegment.mk "Int" PathArguments.none),
                            (PathSegment.mk "ONE" PathArguments.none)])))]
                  false
                  none))
              none),
            (Stmt.expr
              (Expr.assign
                (Expr.field
                  (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                  (Member.named "active_thread"))
                (Expr.tryExpr
                  (Expr.call
                    (Expr.path none (Path.mk false [(PathSegment.mk "pick" PathArguments.none)]))
                    [
                      (Expr.path none (Path.mk false [(PathSegment.mk "distr" PathArguments.none)])),
                      (Expr.closure
                        false
                        [
                          (Pat.typed
                            (Pat.ident false false "id" none)
                            (Ty.path
                              none
                              (Path.mk false [(PathSegment.mk "ThreadId" PathArguments.none)])))]
                        none
                        (Expr.block
                          none
                          (Block.mk
                            [
                              (Stmt.letStmt
                                []
                                (Pat.tupleStruct
                                  none
                                  (Path.mk false [(PathSegment.mk "Some" PathArguments.none)])
                                  [(Pat.ident false false "thread" none)])
                                (some
                                  (Expr.methodCall
                                    (Expr.field
                                      (Expr.path
                                        none
                                        (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                                      (Member.named "threads"))
                                    "get"
                                    none
                                    [
                                      (Expr.path
                                        none
                                        (Path.mk false [(PathSegment.mk "id" PathArguments.none)]))]))
                                (some
                                  (Expr.block
                                    none
                                    (Block.mk
                                      [
                                        (Stmt.expr
                                          (Expr.returnExpr (some (Expr.lit (Lit.bool false))))
                                          true)])))),
                              (Stmt.expr
                                (Expr.binary
                                  (Expr.field
                                    (Expr.path
                                      none
                                      (Path.mk false [(PathSegment.mk "thread" PathArguments.none)]))
                                    (Member.named "state"))
                                  BinOp.eq
                                  (Expr.path
                                    none
                                    (Path.mk
                                      false
                                      [
                                        (PathSegment.mk "ThreadState" PathArguments.none),
                                        (PathSegment.mk "Enabled" PathArguments.none)])))
                                false)])))])))
              true),
            (Stmt.letStmt
              []
              (Pat.ident false false "frame" none)
              (some
                (Expr.methodCall
                  (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                  "cur_frame"
                  none
                  []))
              none),
            (Stmt.letStmt
              []
              (Pat.ident false false "block" none)
              (some
                (Expr.reference
                  false
                  (Expr.index
                    (Expr.field
                      (Expr.field
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "frame" PathArguments.none)]))
                        (Member.named "func"))
                      (Member.named "blocks"))
                    (Expr.field
                      (Expr.path none (Path.mk false [(PathSegment.mk "frame" PathArguments.none)]))
                      (Member.named "next_block")))))
              none),
            (Stmt.expr
              (Expr.ite
                (Expr.binary
                  (Expr.field
                    (Expr.path none (Path.mk false [(PathSegment.mk "frame" PathArguments.none)]))
                    (Member.named "next_stmt"))
                  BinOp.eq
                  (Expr.methodCall
                    (Expr.field
                      (Expr.path none (Path.mk false [(PathSegment.mk "block" PathArguments.none)]))
                      (Member.named "statements"))
                    "len"
                    none
                    []))
                (Block.mk
                  [
                    (Stmt.expr
                      (Expr.tryExpr
                        (Expr.methodCall
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                          "eval_terminator"
                          none
                          [
                            (Expr.field
                              (Expr.path
                                none
                                (Path.mk false [(PathSegment.mk "block" PathArguments.none)]))
                              (Member.named "terminator"))]))
                      true)])
                (some
                  (Expr.block
                    none
                    (Block.mk
                      [
                        (Stmt.letStmt
                          []
                          (Pat.ident false false "stmt" none)
                          (some
                            (Expr.index
                              (Expr.field
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "block" PathArguments.none)]))
                                (Member.named "statements"))
                              (Expr.field
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "frame" PathArguments.none)]))
                                (Member.named "next_stmt"))))
                          none),
                        (Stmt.expr
                          (Expr.tryExpr
                            (Expr.methodCall
                              (Expr.path
                                none
                                (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                              "eval_statement"
                              none
                              [
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "stmt" PathArguments.none)]))]))
                          true),
                        (Stmt.expr
                          (Expr.tryExpr
                            (Expr.methodCall
                              (Expr.path
                                none
                                (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                              "try_mutate_cur_frame"
                              none
                              [
                                (Expr.closure
                                  false
                                  [
                                    (Pat.ident false false "frame" none),
                                    (Pat.ident false false "_mem" none)]
                                  none
                                  (Expr.block
                                    none
                                    (Block.mk
                                      [
                                        (Stmt.expr
                                          (Expr.binary
                                            (Expr.field
                                              (Expr.path
                                                none
                                                (Path.mk
                                                  false
                                                  [(PathSegment.mk "frame" PathArguments.none)]))
                                              (Member.named "next_stmt"))
                                            BinOp.addAssign
                                            (Expr.lit (Lit.int 1 "")))
                                          true),
                                        (Stmt.expr
                                          (Expr.call
                                            (Expr.path
                                              none
                                              (Path.mk
                                                false
                                                [(PathSegment.mk "ret" PathArguments.none)]))
                                            [(Expr.tuple [])])
                                          false)])))]))
                          true)]))))
              false),
            (Stmt.expr
              (Expr.tryExpr
                (Expr.methodCall
                  (Expr.field
                    (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                    (Member.named "mem"))
                  "check_data_races"
                  none
                  [
                    (Expr.field
                      (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                      (Member.named "active_thread")),
                    (Expr.path
                      none
                      (Path.mk false [(PathSegment.mk "prev_step_information" PathArguments.none)]))]))
              true),
            (Stmt.expr
              (Expr.call
                (Expr.path none (Path.mk false [(PathSegment.mk "ret" PathArguments.none)]))
                [(Expr.tuple [])])
              false)]))])

/-- `spec/lang/machine.md:246` -/
def impl_Machine__active_thread : Item :=
  (Item.impl
    []
    false
    false
    (Generics.mk
      [
        (GenericParam.type
          []
          "M"
          [
            (TypeParamBound.trait
              false
              false
              []
              (Path.mk false [(PathSegment.mk "Memory" PathArguments.none)]))]
          none)]
      [])
    false
    none
    (Ty.path
      none
      (Path.mk
        false
        [
          (PathSegment.mk
            "Machine"
            (PathArguments.angleBracketed
              false
              [
                (GenericArgument.type
                  (Ty.path none (Path.mk false [(PathSegment.mk "M" PathArguments.none)])))]))]))
    [
      (ImplItem.fn
        []
        Visibility.inherited
        false
        (Signature.mk
          false
          false
          false
          none
          "active_thread"
          (Generics.mk [] [])
          [(FnArg.receiver [] true none false none)]
          false
          (some
            (Ty.path
              none
              (Path.mk
                false
                [
                  (PathSegment.mk
                    "Thread"
                    (PathArguments.angleBracketed
                      false
                      [
                        (GenericArgument.type
                          (Ty.path none (Path.mk false [(PathSegment.mk "M" PathArguments.none)])))]))]))))
        (Block.mk
          [
            (Stmt.expr
              (Expr.index
                (Expr.field
                  (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                  (Member.named "threads"))
                (Expr.field
                  (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                  (Member.named "active_thread")))
              false)])),
      (ImplItem.fn
        []
        Visibility.inherited
        false
        (Signature.mk
          false
          false
          false
          none
          "mutate_active_thread"
          (Generics.mk [(GenericParam.type [] "O" [] none)] [])
          [
            (FnArg.receiver [] true none true none),
            (FnArg.typed
              []
              (Pat.ident false false "f" none)
              (Ty.implTrait
                [
                  (TypeParamBound.trait
                    false
                    false
                    []
                    (Path.mk
                      false
                      [
                        (PathSegment.mk
                          "FnOnce"
                          (PathArguments.parenthesized
                            [
                              (Ty.reference
                                none
                                true
                                (Ty.path
                                  none
                                  (Path.mk
                                    false
                                    [
                                      (PathSegment.mk
                                        "Thread"
                                        (PathArguments.angleBracketed
                                          false
                                          [
                                            (GenericArgument.type
                                              (Ty.path
                                                none
                                                (Path.mk
                                                  false
                                                  [(PathSegment.mk "M" PathArguments.none)])))]))])))]
                            (some
                              (Ty.path
                                none
                                (Path.mk false [(PathSegment.mk "O" PathArguments.none)])))))]))]))]
          false
          (some (Ty.path none (Path.mk false [(PathSegment.mk "O" PathArguments.none)]))))
        (Block.mk
          [
            (Stmt.expr
              (Expr.methodCall
                (Expr.field
                  (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                  (Member.named "threads"))
                "mutate_at"
                none
                [
                  (Expr.field
                    (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                    (Member.named "active_thread")),
                  (Expr.path none (Path.mk false [(PathSegment.mk "f" PathArguments.none)]))])
              false)])),
      (ImplItem.fn
        []
        Visibility.inherited
        false
        (Signature.mk
          false
          false
          false
          none
          "cur_frame"
          (Generics.mk [] [])
          [(FnArg.receiver [] true none false none)]
          false
          (some
            (Ty.path
              none
              (Path.mk
                false
                [
                  (PathSegment.mk
                    "StackFrame"
                    (PathArguments.angleBracketed
                      false
                      [
                        (GenericArgument.type
                          (Ty.path none (Path.mk false [(PathSegment.mk "M" PathArguments.none)])))]))]))))
        (Block.mk
          [
            (Stmt.expr
              (Expr.methodCall
                (Expr.methodCall
                  (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                  "active_thread"
                  none
                  [])
                "cur_frame"
                none
                [])
              false)])),
      (ImplItem.fn
        []
        Visibility.inherited
        false
        (Signature.mk
          false
          false
          false
          none
          "mutate_cur_frame"
          (Generics.mk [(GenericParam.type [] "O" [] none)] [])
          [
            (FnArg.receiver [] true none true none),
            (FnArg.typed
              []
              (Pat.ident false false "f" none)
              (Ty.implTrait
                [
                  (TypeParamBound.trait
                    false
                    false
                    []
                    (Path.mk
                      false
                      [
                        (PathSegment.mk
                          "FnOnce"
                          (PathArguments.parenthesized
                            [
                              (Ty.reference
                                none
                                true
                                (Ty.path
                                  none
                                  (Path.mk
                                    false
                                    [
                                      (PathSegment.mk
                                        "StackFrame"
                                        (PathArguments.angleBracketed
                                          false
                                          [
                                            (GenericArgument.type
                                              (Ty.path
                                                none
                                                (Path.mk
                                                  false
                                                  [(PathSegment.mk "M" PathArguments.none)])))]))]))),
                              (Ty.reference
                                none
                                true
                                (Ty.path
                                  none
                                  (Path.mk
                                    false
                                    [
                                      (PathSegment.mk
                                        "ConcurrentMemory"
                                        (PathArguments.angleBracketed
                                          false
                                          [
                                            (GenericArgument.type
                                              (Ty.path
                                                none
                                                (Path.mk
                                                  false
                                                  [(PathSegment.mk "M" PathArguments.none)])))]))])))]
                            (some
                              (Ty.path
                                none
                                (Path.mk false [(PathSegment.mk "O" PathArguments.none)])))))]))]))]
          false
          (some (Ty.path none (Path.mk false [(PathSegment.mk "O" PathArguments.none)]))))
        (Block.mk
          [
            (Stmt.expr
              (Expr.methodCall
                (Expr.field
                  (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                  (Member.named "threads"))
                "mutate_at"
                none
                [
                  (Expr.field
                    (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                    (Member.named "active_thread")),
                  (Expr.closure
                    false
                    [(Pat.ident false false "thread" none)]
                    none
                    (Expr.methodCall
                      (Expr.path
                        none
                        (Path.mk false [(PathSegment.mk "thread" PathArguments.none)]))
                      "mutate_cur_frame"
                      none
                      [
                        (Expr.closure
                          false
                          [(Pat.ident false false "frame" none)]
                          none
                          (Expr.call
                            (Expr.path
                              none
                              (Path.mk false [(PathSegment.mk "f" PathArguments.none)]))
                            [
                              (Expr.path
                                none
                                (Path.mk false [(PathSegment.mk "frame" PathArguments.none)])),
                              (Expr.reference
                                true
                                (Expr.field
                                  (Expr.path
                                    none
                                    (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                                  (Member.named "mem")))]))]))])
              false)])),
      (ImplItem.fn
        []
        Visibility.inherited
        false
        (Signature.mk
          false
          false
          false
          none
          "try_mutate_cur_frame"
          (Generics.mk [(GenericParam.type [] "O" [] none)] [])
          [
            (FnArg.receiver [] true none true none),
            (FnArg.typed
              []
              (Pat.ident false false "f" none)
              (Ty.implTrait
                [
                  (TypeParamBound.trait
                    false
                    false
                    []
                    (Path.mk
                      false
                      [
                        (PathSegment.mk
                          "FnOnce"
                          (PathArguments.parenthesized
                            [
                              (Ty.reference
                                none
                                true
                                (Ty.path
                                  none
                                  (Path.mk
                                    false
                                    [
                                      (PathSegment.mk
                                        "StackFrame"
                                        (PathArguments.angleBracketed
                                          false
                                          [
                                            (GenericArgument.type
                                              (Ty.path
                                                none
                                                (Path.mk
                                                  false
                                                  [(PathSegment.mk "M" PathArguments.none)])))]))]))),
                              (Ty.reference
                                none
                                true
                                (Ty.path
                                  none
                                  (Path.mk
                                    false
                                    [
                                      (PathSegment.mk
                                        "ConcurrentMemory"
                                        (PathArguments.angleBracketed
                                          false
                                          [
                                            (GenericArgument.type
                                              (Ty.path
                                                none
                                                (Path.mk
                                                  false
                                                  [(PathSegment.mk "M" PathArguments.none)])))]))])))]
                            (some
                              (Ty.path
                                none
                                (Path.mk
                                  false
                                  [
                                    (PathSegment.mk
                                      "NdResult"
                                      (PathArguments.angleBracketed
                                        false
                                        [
                                          (GenericArgument.type
                                            (Ty.path
                                              none
                                              (Path.mk
                                                false
                                                [(PathSegment.mk "O" PathArguments.none)])))]))])))))]))]))]
          false
          (some
            (Ty.path
              none
              (Path.mk
                false
                [
                  (PathSegment.mk
                    "NdResult"
                    (PathArguments.angleBracketed
                      false
                      [
                        (GenericArgument.type
                          (Ty.path none (Path.mk false [(PathSegment.mk "O" PathArguments.none)])))]))]))))
        (Block.mk
          [
            (Stmt.expr
              (Expr.methodCall
                (Expr.field
                  (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                  (Member.named "threads"))
                "try_mutate_at"
                none
                [
                  (Expr.field
                    (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                    (Member.named "active_thread")),
                  (Expr.closure
                    false
                    [(Pat.ident false false "thread" none)]
                    none
                    (Expr.methodCall
                      (Expr.path
                        none
                        (Path.mk false [(PathSegment.mk "thread" PathArguments.none)]))
                      "try_mutate_cur_frame"
                      none
                      [
                        (Expr.closure
                          false
                          [(Pat.ident false false "frame" none)]
                          none
                          (Expr.call
                            (Expr.path
                              none
                              (Path.mk false [(PathSegment.mk "f" PathArguments.none)]))
                            [
                              (Expr.path
                                none
                                (Path.mk false [(PathSegment.mk "frame" PathArguments.none)])),
                              (Expr.reference
                                true
                                (Expr.field
                                  (Expr.path
                                    none
                                    (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                                  (Member.named "mem")))]))]))])
              false)])),
      (ImplItem.fn
        []
        Visibility.inherited
        false
        (Signature.mk
          false
          false
          false
          none
          "mutate_cur_stack"
          (Generics.mk [(GenericParam.type [] "O" [] none)] [])
          [
            (FnArg.receiver [] true none true none),
            (FnArg.typed
              []
              (Pat.ident false false "f" none)
              (Ty.implTrait
                [
                  (TypeParamBound.trait
                    false
                    false
                    []
                    (Path.mk
                      false
                      [
                        (PathSegment.mk
                          "FnOnce"
                          (PathArguments.parenthesized
                            [
                              (Ty.reference
                                none
                                true
                                (Ty.path
                                  none
                                  (Path.mk
                                    false
                                    [
                                      (PathSegment.mk
                                        "List"
                                        (PathArguments.angleBracketed
                                          false
                                          [
                                            (GenericArgument.type
                                              (Ty.path
                                                none
                                                (Path.mk
                                                  false
                                                  [
                                                    (PathSegment.mk
                                                      "StackFrame"
                                                      (PathArguments.angleBracketed
                                                        false
                                                        [
                                                          (GenericArgument.type
                                                            (Ty.path
                                                              none
                                                              (Path.mk
                                                                false
                                                                [
                                                                  (PathSegment.mk
                                                                    "M"
                                                                    PathArguments.none)])))]))])))]))])))]
                            (some
                              (Ty.path
                                none
                                (Path.mk false [(PathSegment.mk "O" PathArguments.none)])))))]))]))]
          false
          (some (Ty.path none (Path.mk false [(PathSegment.mk "O" PathArguments.none)]))))
        (Block.mk
          [
            (Stmt.expr
              (Expr.methodCall
                (Expr.field
                  (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                  (Member.named "threads"))
                "mutate_at"
                none
                [
                  (Expr.field
                    (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                    (Member.named "active_thread")),
                  (Expr.closure
                    false
                    [(Pat.ident false false "thread" none)]
                    none
                    (Expr.call
                      (Expr.path none (Path.mk false [(PathSegment.mk "f" PathArguments.none)]))
                      [
                        (Expr.reference
                          true
                          (Expr.field
                            (Expr.path
                              none
                              (Path.mk false [(PathSegment.mk "thread" PathArguments.none)]))
                            (Member.named "stack")))]))])
              false)]))])

/-- `spec/lang/machine.md:272` -/
def impl_Thread__cur_frame : Item :=
  (Item.impl
    []
    false
    false
    (Generics.mk
      [
        (GenericParam.type
          []
          "M"
          [
            (TypeParamBound.trait
              false
              false
              []
              (Path.mk false [(PathSegment.mk "Memory" PathArguments.none)]))]
          none)]
      [])
    false
    none
    (Ty.path
      none
      (Path.mk
        false
        [
          (PathSegment.mk
            "Thread"
            (PathArguments.angleBracketed
              false
              [
                (GenericArgument.type
                  (Ty.path none (Path.mk false [(PathSegment.mk "M" PathArguments.none)])))]))]))
    [
      (ImplItem.fn
        []
        Visibility.inherited
        false
        (Signature.mk
          false
          false
          false
          none
          "cur_frame"
          (Generics.mk [] [])
          [(FnArg.receiver [] true none false none)]
          false
          (some
            (Ty.path
              none
              (Path.mk
                false
                [
                  (PathSegment.mk
                    "StackFrame"
                    (PathArguments.angleBracketed
                      false
                      [
                        (GenericArgument.type
                          (Ty.path none (Path.mk false [(PathSegment.mk "M" PathArguments.none)])))]))]))))
        (Block.mk
          [
            (Stmt.expr
              (Expr.methodCall
                (Expr.methodCall
                  (Expr.field
                    (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                    (Member.named "stack"))
                  "last"
                  none
                  [])
                "unwrap"
                none
                [])
              false)])),
      (ImplItem.fn
        []
        Visibility.inherited
        false
        (Signature.mk
          false
          false
          false
          none
          "mutate_cur_frame"
          (Generics.mk [(GenericParam.type [] "O" [] none)] [])
          [
            (FnArg.receiver [] true none true none),
            (FnArg.typed
              []
              (Pat.ident false false "f" none)
              (Ty.implTrait
                [
                  (TypeParamBound.trait
                    false
                    false
                    []
                    (Path.mk
                      false
                      [
                        (PathSegment.mk
                          "FnOnce"
                          (PathArguments.parenthesized
                            [
                              (Ty.reference
                                none
                                true
                                (Ty.path
                                  none
                                  (Path.mk
                                    false
                                    [
                                      (PathSegment.mk
                                        "StackFrame"
                                        (PathArguments.angleBracketed
                                          false
                                          [
                                            (GenericArgument.type
                                              (Ty.path
                                                none
                                                (Path.mk
                                                  false
                                                  [(PathSegment.mk "M" PathArguments.none)])))]))])))]
                            (some
                              (Ty.path
                                none
                                (Path.mk false [(PathSegment.mk "O" PathArguments.none)])))))]))]))]
          false
          (some (Ty.path none (Path.mk false [(PathSegment.mk "O" PathArguments.none)]))))
        (Block.mk
          [
            (Stmt.expr
              (Expr.ite
                (Expr.methodCall
                  (Expr.field
                    (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                    (Member.named "stack"))
                  "is_empty"
                  none
                  [])
                (Block.mk
                  [
                    (Stmt.macro
                      []
                      (Macro.mk
                        (Path.mk false [(PathSegment.mk "panic" PathArguments.none)])
                        MacroDelimiter.paren
                        (MacroBody.exprs
                          [(Expr.lit (Lit.str "`mutate_cur_frame` called on empty stack!"))]
                          false))
                      true)])
                none)
              false),
            (Stmt.letStmt
              []
              (Pat.ident false false "last_idx" none)
              (some
                (Expr.binary
                  (Expr.methodCall
                    (Expr.field
                      (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                      (Member.named "stack"))
                    "len"
                    none
                    [])
                  BinOp.sub
                  (Expr.lit (Lit.int 1 ""))))
              none),
            (Stmt.expr
              (Expr.methodCall
                (Expr.field
                  (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                  (Member.named "stack"))
                "mutate_at"
                none
                [
                  (Expr.path none (Path.mk false [(PathSegment.mk "last_idx" PathArguments.none)])),
                  (Expr.path none (Path.mk false [(PathSegment.mk "f" PathArguments.none)]))])
              false)])),
      (ImplItem.fn
        []
        Visibility.inherited
        false
        (Signature.mk
          false
          false
          false
          none
          "try_mutate_cur_frame"
          (Generics.mk [(GenericParam.type [] "O" [] none)] [])
          [
            (FnArg.receiver [] true none true none),
            (FnArg.typed
              []
              (Pat.ident false false "f" none)
              (Ty.implTrait
                [
                  (TypeParamBound.trait
                    false
                    false
                    []
                    (Path.mk
                      false
                      [
                        (PathSegment.mk
                          "FnOnce"
                          (PathArguments.parenthesized
                            [
                              (Ty.reference
                                none
                                true
                                (Ty.path
                                  none
                                  (Path.mk
                                    false
                                    [
                                      (PathSegment.mk
                                        "StackFrame"
                                        (PathArguments.angleBracketed
                                          false
                                          [
                                            (GenericArgument.type
                                              (Ty.path
                                                none
                                                (Path.mk
                                                  false
                                                  [(PathSegment.mk "M" PathArguments.none)])))]))])))]
                            (some
                              (Ty.path
                                none
                                (Path.mk
                                  false
                                  [
                                    (PathSegment.mk
                                      "NdResult"
                                      (PathArguments.angleBracketed
                                        false
                                        [
                                          (GenericArgument.type
                                            (Ty.path
                                              none
                                              (Path.mk
                                                false
                                                [(PathSegment.mk "O" PathArguments.none)])))]))])))))]))]))]
          false
          (some
            (Ty.path
              none
              (Path.mk
                false
                [
                  (PathSegment.mk
                    "NdResult"
                    (PathArguments.angleBracketed
                      false
                      [
                        (GenericArgument.type
                          (Ty.path none (Path.mk false [(PathSegment.mk "O" PathArguments.none)])))]))]))))
        (Block.mk
          [
            (Stmt.expr
              (Expr.ite
                (Expr.methodCall
                  (Expr.field
                    (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                    (Member.named "stack"))
                  "is_empty"
                  none
                  [])
                (Block.mk
                  [
                    (Stmt.macro
                      []
                      (Macro.mk
                        (Path.mk false [(PathSegment.mk "panic" PathArguments.none)])
                        MacroDelimiter.paren
                        (MacroBody.exprs
                          [(Expr.lit (Lit.str "`try_mutate_cur_frame` called on empty stack!"))]
                          false))
                      true)])
                none)
              false),
            (Stmt.letStmt
              []
              (Pat.ident false false "last_idx" none)
              (some
                (Expr.binary
                  (Expr.methodCall
                    (Expr.field
                      (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                      (Member.named "stack"))
                    "len"
                    none
                    [])
                  BinOp.sub
                  (Expr.lit (Lit.int 1 ""))))
              none),
            (Stmt.expr
              (Expr.methodCall
                (Expr.field
                  (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                  (Member.named "stack"))
                "try_mutate_at"
                none
                [
                  (Expr.path none (Path.mk false [(PathSegment.mk "last_idx" PathArguments.none)])),
                  (Expr.path none (Path.mk false [(PathSegment.mk "f" PathArguments.none)]))])
              false)]))])

/-- `spec/lang/machine.md:296` -/
def impl_StackFrame__jump_to_block : Item :=
  (Item.impl
    []
    false
    false
    (Generics.mk
      [
        (GenericParam.type
          []
          "M"
          [
            (TypeParamBound.trait
              false
              false
              []
              (Path.mk false [(PathSegment.mk "Memory" PathArguments.none)]))]
          none)]
      [])
    false
    none
    (Ty.path
      none
      (Path.mk
        false
        [
          (PathSegment.mk
            "StackFrame"
            (PathArguments.angleBracketed
              false
              [
                (GenericArgument.type
                  (Ty.path none (Path.mk false [(PathSegment.mk "M" PathArguments.none)])))]))]))
    [
      (ImplItem.fn
        [(Attr.mk true "doc" (AttrMeta.nameValue " jump to the beginning of the given block."))]
        Visibility.inherited
        false
        (Signature.mk
          false
          false
          false
          none
          "jump_to_block"
          (Generics.mk [] [])
          [
            (FnArg.receiver [] true none true none),
            (FnArg.typed
              []
              (Pat.ident false false "b" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "BbName" PathArguments.none)])))]
          false
          none)
        (Block.mk
          [
            (Stmt.expr
              (Expr.assign
                (Expr.field
                  (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                  (Member.named "next_block"))
                (Expr.path none (Path.mk false [(PathSegment.mk "b" PathArguments.none)])))
              true),
            (Stmt.expr
              (Expr.assign
                (Expr.field
                  (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                  (Member.named "next_stmt"))
                (Expr.path
                  none
                  (Path.mk
                    false
                    [
                      (PathSegment.mk "Int" PathArguments.none),
                      (PathSegment.mk "ZERO" PathArguments.none)])))
              true)]))])

/-- `spec/lang/machine.md:308` -/
def impl_Machine__new_thread : Item :=
  (Item.impl
    []
    false
    false
    (Generics.mk
      [
        (GenericParam.type
          []
          "M"
          [
            (TypeParamBound.trait
              false
              false
              []
              (Path.mk false [(PathSegment.mk "Memory" PathArguments.none)]))]
          none)]
      [])
    false
    none
    (Ty.path
      none
      (Path.mk
        false
        [
          (PathSegment.mk
            "Machine"
            (PathArguments.angleBracketed
              false
              [
                (GenericArgument.type
                  (Ty.path none (Path.mk false [(PathSegment.mk "M" PathArguments.none)])))]))]))
    [
      (ImplItem.fn
        [
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue
              " Create a new thread where the first frame calls the given function with the given arguments."))]
        Visibility.inherited
        false
        (Signature.mk
          false
          false
          false
          none
          "new_thread"
          (Generics.mk [] [])
          [
            (FnArg.receiver [] true none true none),
            (FnArg.typed
              []
              (Pat.ident false false "func" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "Function" PathArguments.none)]))),
            (FnArg.typed
              []
              (Pat.ident false false "args" none)
              (Ty.path
                none
                (Path.mk
                  false
                  [
                    (PathSegment.mk
                      "List"
                      (PathArguments.angleBracketed
                        false
                        [
                          (GenericArgument.type
                            (Ty.tuple
                              [
                                (Ty.path
                                  none
                                  (Path.mk
                                    false
                                    [
                                      (PathSegment.mk
                                        "Value"
                                        (PathArguments.angleBracketed
                                          false
                                          [
                                            (GenericArgument.type
                                              (Ty.path
                                                none
                                                (Path.mk
                                                  false
                                                  [(PathSegment.mk "M" PathArguments.none)])))]))])),
                                (Ty.path
                                  none
                                  (Path.mk false [(PathSegment.mk "Type" PathArguments.none)]))]))]))])))]
          false
          (some
            (Ty.path
              none
              (Path.mk
                false
                [
                  (PathSegment.mk
                    "NdResult"
                    (PathArguments.angleBracketed
                      false
                      [
                        (GenericArgument.type
                          (Ty.path
                            none
                            (Path.mk false [(PathSegment.mk "ThreadId" PathArguments.none)])))]))]))))
        (Block.mk
          [
            (Stmt.letStmt
              []
              (Pat.ident false false "init_frame" none)
              (some
                (Expr.tryExpr
                  (Expr.methodCall
                    (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                    "create_frame"
                    none
                    [
                      (Expr.path none (Path.mk false [(PathSegment.mk "func" PathArguments.none)])),
                      (Expr.path
                        none
                        (Path.mk
                          false
                          [
                            (PathSegment.mk "StackPopAction" PathArguments.none),
                            (PathSegment.mk "BottomOfStack" PathArguments.none)])),
                      (Expr.path
                        none
                        (Path.mk
                          false
                          [
                            (PathSegment.mk "CallingConvention" PathArguments.none),
                            (PathSegment.mk "C" PathArguments.none)])),
                      (Expr.call
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "unit_type" PathArguments.none)]))
                        []),
                      (Expr.path none (Path.mk false [(PathSegment.mk "args" PathArguments.none)]))])))
              none),
            (Stmt.letStmt
              []
              (Pat.ident false false "thread" none)
              (some
                (Expr.struct
                  none
                  (Path.mk false [(PathSegment.mk "Thread" PathArguments.none)])
                  [
                    (FieldValue.mk
                      []
                      (Member.named "state")
                      false
                      (Expr.path
                        none
                        (Path.mk
                          false
                          [
                            (PathSegment.mk "ThreadState" PathArguments.none),
                            (PathSegment.mk "Enabled" PathArguments.none)]))),
                    (FieldValue.mk
                      []
                      (Member.named "stack")
                      false
                      (Expr.macro
                        (Macro.mk
                          (Path.mk false [(PathSegment.mk "list" PathArguments.none)])
                          MacroDelimiter.bracket
                          (MacroBody.exprs
                            [
                              (Expr.path
                                none
                                (Path.mk false [(PathSegment.mk "init_frame" PathArguments.none)]))]
                            false)))),
                    (FieldValue.mk
                      []
                      (Member.named "unwind_payloads")
                      false
                      (Expr.macro
                        (Macro.mk
                          (Path.mk false [(PathSegment.mk "list" PathArguments.none)])
                          MacroDelimiter.bracket
                          (MacroBody.exprs [] false))))]
                  false
                  none))
              none),
            (Stmt.letStmt
              []
              (Pat.ident false false "thread_id" none)
              (some
                (Expr.call
                  (Expr.path
                    none
                    (Path.mk
                      false
                      [
                        (PathSegment.mk "ThreadId" PathArguments.none),
                        (PathSegment.mk "from" PathArguments.none)]))
                  [
                    (Expr.methodCall
                      (Expr.field
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                        (Member.named "threads"))
                      "len"
                      none
                      [])]))
              none),
            (Stmt.expr
              (Expr.methodCall
                (Expr.field
                  (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                  (Member.named "threads"))
                "push"
                none
                [(Expr.path none (Path.mk false [(PathSegment.mk "thread" PathArguments.none)]))])
              true),
            (Stmt.expr
              (Expr.call
                (Expr.path none (Path.mk false [(PathSegment.mk "ret" PathArguments.none)]))
                [(Expr.path none (Path.mk false [(PathSegment.mk "thread_id" PathArguments.none)]))])
              false)])),
      (ImplItem.fn
        [(Attr.mk true "doc" (AttrMeta.nameValue " Look up a function given a pointer."))]
        Visibility.inherited
        false
        (Signature.mk
          false
          false
          false
          none
          "fn_from_ptr"
          (Generics.mk [] [])
          [
            (FnArg.receiver [] true none false none),
            (FnArg.typed
              []
              (Pat.ident false false "ptr" none)
              (Ty.path
                none
                (Path.mk
                  false
                  [
                    (PathSegment.mk
                      "Value"
                      (PathArguments.angleBracketed
                        false
                        [
                          (GenericArgument.type
                            (Ty.path none (Path.mk false [(PathSegment.mk "M" PathArguments.none)])))]))])))]
          false
          (some
            (Ty.path
              none
              (Path.mk
                false
                [
                  (PathSegment.mk
                    "Result"
                    (PathArguments.angleBracketed
                      false
                      [
                        (GenericArgument.type
                          (Ty.path
                            none
                            (Path.mk false [(PathSegment.mk "Function" PathArguments.none)])))]))]))))
        (Block.mk
          [
            (Stmt.expr
              (Expr.ite
                (Expr.letCond
                  (Pat.tupleStruct
                    none
                    (Path.mk
                      false
                      [
                        (PathSegment.mk "Value" PathArguments.none),
                        (PathSegment.mk "Ptr" PathArguments.none)])
                    [
                      (Pat.struct
                        none
                        (Path.mk false [(PathSegment.mk "Pointer" PathArguments.none)])
                        [
                          (FieldPat.mk
                            []
                            (Member.named "thin_pointer")
                            false
                            (Pat.ident false false "thin_ptr" none)),
                          (FieldPat.mk
                            []
                            (Member.named "metadata")
                            true
                            (Pat.ident false false "metadata" none))]
                        false)])
                  (Expr.path none (Path.mk false [(PathSegment.mk "ptr" PathArguments.none)])))
                (Block.mk
                  [
                    (Stmt.expr
                      (Expr.ite
                        (Expr.methodCall
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "metadata" PathArguments.none)]))
                          "is_some"
                          none
                          [])
                        (Block.mk
                          [
                            (Stmt.macro
                              []
                              (Macro.mk
                                (Path.mk false [(PathSegment.mk "throw_ub" PathArguments.none)])
                                MacroDelimiter.paren
                                (MacroBody.exprs
                                  [(Expr.lit (Lit.str "invalid pointer for function lookup"))]
                                  false))
                              true)])
                        none)
                      false),
                    (Stmt.letStmt
                      []
                      (Pat.tupleStruct
                        none
                        (Path.mk false [(PathSegment.mk "Some" PathArguments.none)])
                        [(Pat.tuple [(Pat.ident false false "func_name" none), Pat.wild])])
                      (some
                        (Expr.methodCall
                          (Expr.methodCall
                            (Expr.field
                              (Expr.path
                                none
                                (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                              (Member.named "fn_ptrs"))
                            "iter"
                            none
                            [])
                          "find"
                          none
                          [
                            (Expr.closure
                              false
                              [(Pat.tuple [Pat.wild, (Pat.ident false false "fn_ptr" none)])]
                              none
                              (Expr.binary
                                (Expr.unary
                                  UnOp.deref
                                  (Expr.path
                                    none
                                    (Path.mk false [(PathSegment.mk "fn_ptr" PathArguments.none)])))
                                BinOp.eq
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "thin_ptr" PathArguments.none)]))))]))
                      (some
                        (Expr.block
                          none
                          (Block.mk
                            [
                              (Stmt.macro
                                []
                                (Macro.mk
                                  (Path.mk false [(PathSegment.mk "throw_ub" PathArguments.none)])
                                  MacroDelimiter.paren
                                  (MacroBody.exprs
                                    [(Expr.lit (Lit.str "invalid pointer for function lookup"))]
                                    false))
                                true)])))),
                    (Stmt.expr
                      (Expr.call
                        (Expr.path none (Path.mk false [(PathSegment.mk "ret" PathArguments.none)]))
                        [
                          (Expr.index
                            (Expr.field
                              (Expr.field
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                                (Member.named "prog"))
                              (Member.named "functions"))
                            (Expr.path
                              none
                              (Path.mk false [(PathSegment.mk "func_name" PathArguments.none)])))])
                      false)])
                (some
                  (Expr.block
                    none
                    (Block.mk
                      [
                        (Stmt.macro
                          []
                          (Macro.mk
                            (Path.mk false [(PathSegment.mk "throw_ub" PathArguments.none)])
                            MacroDelimiter.paren
                            (MacroBody.exprs
                              [
                                (Expr.lit
                                  (Lit.str
                                    "trying to look up a function based on a non-pointer value"))]
                              false))
                          true)]))))
              false)])),
      (ImplItem.fn
        [(Attr.mk true "doc" (AttrMeta.nameValue " Look up a vtable given a pointer."))]
        Visibility.inherited
        false
        (Signature.mk
          false
          false
          false
          none
          "vtable_from_ptr"
          (Generics.mk [] [])
          [
            (FnArg.receiver [] true none false none),
            (FnArg.typed
              []
              (Pat.ident false false "ptr" none)
              (Ty.path
                none
                (Path.mk
                  false
                  [
                    (PathSegment.mk
                      "ThinPointer"
                      (PathArguments.angleBracketed
                        false
                        [
                          (GenericArgument.type
                            (Ty.path
                              none
                              (Path.mk
                                false
                                [
                                  (PathSegment.mk "M" PathArguments.none),
                                  (PathSegment.mk "Provenance" PathArguments.none)])))]))])))]
          false
          (some
            (Ty.path
              none
              (Path.mk
                false
                [
                  (PathSegment.mk
                    "Result"
                    (PathArguments.angleBracketed
                      false
                      [
                        (GenericArgument.type
                          (Ty.path
                            none
                            (Path.mk false [(PathSegment.mk "VTable" PathArguments.none)])))]))]))))
        (Block.mk
          [
            (Stmt.letStmt
              []
              (Pat.tupleStruct
                none
                (Path.mk false [(PathSegment.mk "Some" PathArguments.none)])
                [(Pat.tuple [(Pat.ident false false "vtable_name" none), Pat.wild])])
              (some
                (Expr.methodCall
                  (Expr.methodCall
                    (Expr.field
                      (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                      (Member.named "vtable_ptrs"))
                    "iter"
                    none
                    [])
                  "find"
                  none
                  [
                    (Expr.closure
                      false
                      [(Pat.tuple [Pat.wild, (Pat.ident false false "vtable_ptr" none)])]
                      none
                      (Expr.binary
                        (Expr.unary
                          UnOp.deref
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "vtable_ptr" PathArguments.none)])))
                        BinOp.eq
                        (Expr.path none (Path.mk false [(PathSegment.mk "ptr" PathArguments.none)]))))]))
              (some
                (Expr.block
                  none
                  (Block.mk
                    [
                      (Stmt.macro
                        []
                        (Macro.mk
                          (Path.mk false [(PathSegment.mk "throw_ub" PathArguments.none)])
                          MacroDelimiter.paren
                          (MacroBody.exprs
                            [(Expr.lit (Lit.str "invalid pointer for vtable lookup"))]
                            false))
                        true)])))),
            (Stmt.expr
              (Expr.call
                (Expr.path none (Path.mk false [(PathSegment.mk "ret" PathArguments.none)]))
                [
                  (Expr.index
                    (Expr.field
                      (Expr.field
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                        (Member.named "prog"))
                      (Member.named "vtables"))
                    (Expr.path
                      none
                      (Path.mk false [(PathSegment.mk "vtable_name" PathArguments.none)])))])
              false)])),
      (ImplItem.fn
        [
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue
              " Reset the data race tracking for the next step, and return the information from the previous step.")),
          (Attr.mk true "doc" (AttrMeta.nameValue "")),
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue
              " The first component of the return value is the set of threads that were synchronized by the previous step,")),
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue " the second is the list of accesses in the previous step."))]
        Visibility.inherited
        false
        (Signature.mk
          false
          false
          false
          none
          "reset_data_race_tracking"
          (Generics.mk [] [])
          [(FnArg.receiver [] true none true none)]
          false
          (some
            (Ty.tuple
              [
                (Ty.path
                  none
                  (Path.mk
                    false
                    [
                      (PathSegment.mk
                        "Set"
                        (PathArguments.angleBracketed
                          false
                          [
                            (GenericArgument.type
                              (Ty.path
                                none
                                (Path.mk false [(PathSegment.mk "ThreadId" PathArguments.none)])))]))])),
                (Ty.path
                  none
                  (Path.mk
                    false
                    [
                      (PathSegment.mk
                        "List"
                        (PathArguments.angleBracketed
                          false
                          [
                            (GenericArgument.type
                              (Ty.path
                                none
                                (Path.mk false [(PathSegment.mk "Access" PathArguments.none)])))]))]))])))
        (Block.mk
          [
            (Stmt.letStmt
              []
              (Pat.ident false true "prev_sync" none)
              (some
                (Expr.field
                  (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                  (Member.named "synchronized_threads")))
              none),
            (Stmt.expr
              (Expr.methodCall
                (Expr.path none (Path.mk false [(PathSegment.mk "prev_sync" PathArguments.none)]))
                "insert"
                none
                [
                  (Expr.field
                    (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                    (Member.named "active_thread"))])
              true),
            (Stmt.letStmt
              []
              (Pat.ident false false "prev_accesses" none)
              (some
                (Expr.methodCall
                  (Expr.field
                    (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                    (Member.named "mem"))
                  "reset_accesses"
                  none
                  []))
              none),
            (Stmt.expr
              (Expr.tuple
                [
                  (Expr.path none (Path.mk false [(PathSegment.mk "prev_sync" PathArguments.none)])),
                  (Expr.path
                    none
                    (Path.mk false [(PathSegment.mk "prev_accesses" PathArguments.none)]))])
              false)])),
      (ImplItem.fn
        [
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue
              " All vtable lookups must have well-defined pointers. If this panics it is a spec bug."))]
        Visibility.inherited
        false
        (Signature.mk
          false
          false
          false
          none
          "vtable_lookup"
          (Generics.mk [] [])
          [(FnArg.receiver [] true none false none)]
          false
          (some
            (Ty.implTrait
              [
                (TypeParamBound.trait
                  false
                  false
                  []
                  (Path.mk
                    false
                    [
                      (PathSegment.mk
                        "Fn"
                        (PathArguments.parenthesized
                          [
                            (Ty.path
                              none
                              (Path.mk
                                false
                                [
                                  (PathSegment.mk
                                    "ThinPointer"
                                    (PathArguments.angleBracketed
                                      false
                                      [
                                        (GenericArgument.type
                                          (Ty.path
                                            none
                                            (Path.mk
                                              false
                                              [
                                                (PathSegment.mk "M" PathArguments.none),
                                                (PathSegment.mk "Provenance" PathArguments.none)])))]))]))]
                          (some
                            (Ty.path
                              none
                              (Path.mk false [(PathSegment.mk "VTable" PathArguments.none)])))))])),
                (TypeParamBound.lifetime "static")])))
        (Block.mk
          [
            (Stmt.letStmt
              []
              (Pat.ident false false "ptrs" none)
              (some
                (Expr.field
                  (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                  (Member.named "vtable_ptrs")))
              none),
            (Stmt.letStmt
              []
              (Pat.ident false false "vtables" none)
              (some
                (Expr.field
                  (Expr.field
                    (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                    (Member.named "prog"))
                  (Member.named "vtables")))
              none),
            (Stmt.expr
              (Expr.closure
                true
                [(Pat.ident false false "ptr" none)]
                none
                (Expr.block
                  none
                  (Block.mk
                    [
                      (Stmt.letStmt
                        []
                        (Pat.tuple [(Pat.ident false false "name" none), Pat.wild])
                        (some
                          (Expr.methodCall
                            (Expr.methodCall
                              (Expr.methodCall
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "ptrs" PathArguments.none)]))
                                "iter"
                                none
                                [])
                              "find"
                              none
                              [
                                (Expr.closure
                                  false
                                  [
                                    (Pat.tuple
                                      [Pat.wild, (Pat.ident false false "vtable_ptr" none)])]
                                  none
                                  (Expr.binary
                                    (Expr.unary
                                      UnOp.deref
                                      (Expr.path
                                        none
                                        (Path.mk
                                          false
                                          [(PathSegment.mk "vtable_ptr" PathArguments.none)])))
                                    BinOp.eq
                                    (Expr.path
                                      none
                                      (Path.mk false [(PathSegment.mk "ptr" PathArguments.none)]))))])
                            "unwrap"
                            none
                            []))
                        none),
                      (Stmt.letStmt
                        []
                        (Pat.ident false false "vtable" none)
                        (some
                          (Expr.index
                            (Expr.path
                              none
                              (Path.mk false [(PathSegment.mk "vtables" PathArguments.none)]))
                            (Expr.path
                              none
                              (Path.mk false [(PathSegment.mk "name" PathArguments.none)]))))
                        none),
                      (Stmt.expr
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "vtable" PathArguments.none)]))
                        false)])))
              false)])),
      (ImplItem.fn
        [
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue
              " Helper function to compute the size with the allocated vtables in `self`."))]
        Visibility.inherited
        false
        (Signature.mk
          false
          false
          false
          none
          "compute_size"
          (Generics.mk [] [])
          [
            (FnArg.receiver [] true none false none),
            (FnArg.typed
              []
              (Pat.ident false false "layout" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "LayoutStrategy" PathArguments.none)]))),
            (FnArg.typed
              []
              (Pat.ident false false "meta" none)
              (Ty.path
                none
                (Path.mk
                  false
                  [
                    (PathSegment.mk
                      "Option"
                      (PathArguments.angleBracketed
                        false
                        [
                          (GenericArgument.type
                            (Ty.path
                              none
                              (Path.mk
                                false
                                [
                                  (PathSegment.mk
                                    "PointerMeta"
                                    (PathArguments.angleBracketed
                                      false
                                      [
                                        (GenericArgument.type
                                          (Ty.path
                                            none
                                            (Path.mk
                                              false
                                              [
                                                (PathSegment.mk "M" PathArguments.none),
                                                (PathSegment.mk "Provenance" PathArguments.none)])))]))])))]))])))]
          false
          (some (Ty.path none (Path.mk false [(PathSegment.mk "Size" PathArguments.none)]))))
        (Block.mk
          [
            (Stmt.letStmt
              []
              (Pat.tuple [(Pat.ident false false "size" none), Pat.wild])
              (some
                (Expr.methodCall
                  (Expr.path none (Path.mk false [(PathSegment.mk "layout" PathArguments.none)]))
                  "compute_size_and_align"
                  none
                  [
                    (Expr.path none (Path.mk false [(PathSegment.mk "meta" PathArguments.none)])),
                    (Expr.methodCall
                      (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                      "vtable_lookup"
                      none
                      [])]))
              none),
            (Stmt.expr
              (Expr.path none (Path.mk false [(PathSegment.mk "size" PathArguments.none)]))
              false)])),
      (ImplItem.fn
        [
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue
              " Helper function to compute the alignment with the allocated vtables in `self`."))]
        Visibility.inherited
        false
        (Signature.mk
          false
          false
          false
          none
          "compute_align"
          (Generics.mk [] [])
          [
            (FnArg.receiver [] true none false none),
            (FnArg.typed
              []
              (Pat.ident false false "layout" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "LayoutStrategy" PathArguments.none)]))),
            (FnArg.typed
              []
              (Pat.ident false false "meta" none)
              (Ty.path
                none
                (Path.mk
                  false
                  [
                    (PathSegment.mk
                      "Option"
                      (PathArguments.angleBracketed
                        false
                        [
                          (GenericArgument.type
                            (Ty.path
                              none
                              (Path.mk
                                false
                                [
                                  (PathSegment.mk
                                    "PointerMeta"
                                    (PathArguments.angleBracketed
                                      false
                                      [
                                        (GenericArgument.type
                                          (Ty.path
                                            none
                                            (Path.mk
                                              false
                                              [
                                                (PathSegment.mk "M" PathArguments.none),
                                                (PathSegment.mk "Provenance" PathArguments.none)])))]))])))]))])))]
          false
          (some (Ty.path none (Path.mk false [(PathSegment.mk "Align" PathArguments.none)]))))
        (Block.mk
          [
            (Stmt.letStmt
              []
              (Pat.tuple [Pat.wild, (Pat.ident false false "align" none)])
              (some
                (Expr.methodCall
                  (Expr.path none (Path.mk false [(PathSegment.mk "layout" PathArguments.none)]))
                  "compute_size_and_align"
                  none
                  [
                    (Expr.path none (Path.mk false [(PathSegment.mk "meta" PathArguments.none)])),
                    (Expr.methodCall
                      (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                      "vtable_lookup"
                      none
                      [])]))
              none),
            (Stmt.expr
              (Expr.path none (Path.mk false [(PathSegment.mk "align" PathArguments.none)]))
              false)]))])

/-- All items of `spec/lang/machine.md`, in source order, with provenance. -/
def items : List SourceItem :=
  [
    (SourceItem.mk
      "struct_Machine"
      11
      "a67f1645c0eabd0289bd2fb5ff1dfae28f256c41cf49e44b3e4eab8927cb6aa1"
      struct_Machine),
    (SourceItem.mk
      "struct_StackFrame"
      54
      "b77edba3c4f225e386541841034fd2d1018dbf256c27b252c14ae70e7069eeec"
      struct_StackFrame),
    (SourceItem.mk
      "enum_StackPopAction"
      77
      "7b296963fcc9f21219dbefaf57c87a759e44e2eccffb0b066a11aa0144c68a38"
      enum_StackPopAction),
    (SourceItem.mk
      "struct_Thread"
      99
      "800d8a09fea52ba9f5294bbdeadc627a8cf4011337287ac4cf566c36e2ee006b"
      struct_Thread),
    (SourceItem.mk
      "enum_ThreadState"
      112
      "8fe95525a9d5837515868d2f4ac097a6fd4bf921a6f2429edff0486156cea424"
      enum_ThreadState),
    (SourceItem.mk
      "impl_Machine__new"
      128
      "45ee0382262183b14b28c5fad1005abbbcbb8bcf0f0cc536fb55ad12605190cf"
      impl_Machine__new),
    (SourceItem.mk
      "impl_Machine__active_thread"
      246
      "e1ba15aad87afbb3de6c4aeae1f4639ae48acfdce0be83da8db00a1bbeeb5582"
      impl_Machine__active_thread),
    (SourceItem.mk
      "impl_Thread__cur_frame"
      272
      "9c7c08af8ad7f1407c6daa053b0c84ad9e5a3139be3167f7ed9d1e359825337e"
      impl_Thread__cur_frame),
    (SourceItem.mk
      "impl_StackFrame__jump_to_block"
      296
      "f8853893d8d78e8ee1e51a8c74d59bb1b4d7db3781f20e96b02ec7b86655ae22"
      impl_StackFrame__jump_to_block),
    (SourceItem.mk
      "impl_Machine__new_thread"
      308
      "cb6de376722065548f7d8e61627a4e969d70c5fe7f347b09a55f2512cdbbe185"
      impl_Machine__new_thread)]

end MiniRustSpec.Gen.Items.Lang.Machine
