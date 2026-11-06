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
`spec/mem/concurrent.md` (commit `d821c6e3`), one Lean definition per item, in source order.
-/

import MiniRustSpec.Meta.Syntax

set_option maxRecDepth 100000

namespace MiniRustSpec.Gen.Items.Mem.Concurrent

open MiniRustSpec.Syntax

/-- Path of the upstream file these items were extracted from. -/
def sourceFile : String := "spec/mem/concurrent.md"

/-- SHA-256 of the upstream file. -/
def sourceSha256 : String := "2b3f928517bed4da43739395656c7e24572dae37cb041fb7b77061c47a8e5816"

/-- `spec/mem/concurrent.md:7` -/
def struct_ConcurrentMemory : Item :=
  (Item.struct
    []
    Visibility.pub
    "ConcurrentMemory"
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
          []
          Visibility.inherited
          (some "memory")
          (Ty.path none (Path.mk false [(PathSegment.mk "M" PathArguments.none)]))),
        (Field.mk
          [
            (Attr.mk
              true
              "doc"
              (AttrMeta.nameValue
                " List of all memory access done by the active thread in the current step."))]
          Visibility.inherited
          (some "accesses")
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
                          (Path.mk false [(PathSegment.mk "Access" PathArguments.none)])))]))])))]))

/-- `spec/mem/concurrent.md:14` -/
def enum_Atomicity : Item :=
  (Item.enum
    [(Attr.mk true "doc" (AttrMeta.nameValue " The different kinds of atomicity."))]
    Visibility.pub
    "Atomicity"
    (Generics.mk [] [])
    [
      (Variant.mk
        [(Attr.mk true "doc" (AttrMeta.nameValue " A sequentially consistent atomic access."))]
        "Atomic"
        Fields.unit
        none),
      (Variant.mk
        [(Attr.mk true "doc" (AttrMeta.nameValue " A non-atomic memory access."))]
        "None"
        Fields.unit
        none)])

/-- `spec/mem/concurrent.md:23` -/
def enum_AccessType : Item :=
  (Item.enum
    [
      (Attr.mk
        true
        "doc"
        (AttrMeta.nameValue " Internal type used to track the type of a memory access."))]
    Visibility.inherited
    "AccessType"
    (Generics.mk [] [])
    [(Variant.mk [] "Store" Fields.unit none), (Variant.mk [] "Load" Fields.unit none)])

/-- `spec/mem/concurrent.md:29` -/
def struct_Access : Item :=
  (Item.struct
    [
      (Attr.mk
        true
        "doc"
        (AttrMeta.nameValue
          " Access contains all information the data race detection needs about a single access."))]
    Visibility.pub
    "Access"
    (Generics.mk [] [])
    (Fields.named
      [
        (Field.mk
          []
          Visibility.inherited
          (some "ty")
          (Ty.path none (Path.mk false [(PathSegment.mk "AccessType" PathArguments.none)]))),
        (Field.mk
          []
          Visibility.inherited
          (some "atomicity")
          (Ty.path none (Path.mk false [(PathSegment.mk "Atomicity" PathArguments.none)]))),
        (Field.mk
          []
          Visibility.inherited
          (some "addr")
          (Ty.path none (Path.mk false [(PathSegment.mk "Address" PathArguments.none)]))),
        (Field.mk
          []
          Visibility.inherited
          (some "len")
          (Ty.path none (Path.mk false [(PathSegment.mk "Size" PathArguments.none)])))]))

/-- `spec/mem/concurrent.md:44` -/
def impl_ConcurrentMemory__new : Item :=
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
            "ConcurrentMemory"
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
              (Pat.ident false false "params" none)
              (Ty.path
                none
                (Path.mk
                  false
                  [
                    (PathSegment.mk "M" PathArguments.none),
                    (PathSegment.mk "Params" PathArguments.none)])))]
          false
          (some (Ty.path none (Path.mk false [(PathSegment.mk "Self" PathArguments.none)]))))
        (Block.mk
          [
            (Stmt.expr
              (Expr.struct
                none
                (Path.mk false [(PathSegment.mk "Self" PathArguments.none)])
                [
                  (FieldValue.mk
                    []
                    (Member.named "memory")
                    false
                    (Expr.call
                      (Expr.path
                        none
                        (Path.mk
                          false
                          [
                            (PathSegment.mk "M" PathArguments.none),
                            (PathSegment.mk "new" PathArguments.none)]))
                      [
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "params" PathArguments.none)]))])),
                  (FieldValue.mk
                    []
                    (Member.named "accesses")
                    false
                    (Expr.macro
                      (Macro.mk
                        (Path.mk false [(PathSegment.mk "list" PathArguments.none)])
                        MacroDelimiter.bracket
                        (MacroBody.exprs [] false))))]
                false
                none)
              false)])),
      (ImplItem.fn
        [
          (Attr.mk true "doc" (AttrMeta.nameValue " Create a new allocation.")),
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue
              " The initial contents of the allocation are `AbstractByte::Uninit`."))]
        Visibility.pub
        false
        (Signature.mk
          false
          false
          false
          none
          "allocate"
          (Generics.mk [] [])
          [
            (FnArg.receiver [] true none true none),
            (FnArg.typed
              []
              (Pat.ident false false "kind" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "AllocationKind" PathArguments.none)]))),
            (FnArg.typed
              []
              (Pat.ident false false "size" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "Size" PathArguments.none)]))),
            (FnArg.typed
              []
              (Pat.ident false false "align" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "Align" PathArguments.none)])))]
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
                                              (PathSegment.mk "Provenance" PathArguments.none)])))]))])))]))]))))
        (Block.mk
          [
            (Stmt.expr
              (Expr.methodCall
                (Expr.field
                  (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                  (Member.named "memory"))
                "allocate"
                none
                [
                  (Expr.path none (Path.mk false [(PathSegment.mk "kind" PathArguments.none)])),
                  (Expr.path none (Path.mk false [(PathSegment.mk "size" PathArguments.none)])),
                  (Expr.path none (Path.mk false [(PathSegment.mk "align" PathArguments.none)]))])
              false)])),
      (ImplItem.fn
        [(Attr.mk true "doc" (AttrMeta.nameValue " Remove an allocation."))]
        Visibility.pub
        false
        (Signature.mk
          false
          false
          false
          none
          "deallocate"
          (Generics.mk [] [])
          [
            (FnArg.receiver [] true none true none),
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
                                  (PathSegment.mk "Provenance" PathArguments.none)])))]))]))),
            (FnArg.typed
              []
              (Pat.ident false false "kind" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "AllocationKind" PathArguments.none)]))),
            (FnArg.typed
              []
              (Pat.ident false false "size" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "Size" PathArguments.none)]))),
            (FnArg.typed
              []
              (Pat.ident false false "align" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "Align" PathArguments.none)])))]
          false
          (some (Ty.path none (Path.mk false [(PathSegment.mk "Result" PathArguments.none)]))))
        (Block.mk
          [
            (Stmt.expr
              (Expr.methodCall
                (Expr.field
                  (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                  (Member.named "memory"))
                "deallocate"
                none
                [
                  (Expr.path none (Path.mk false [(PathSegment.mk "ptr" PathArguments.none)])),
                  (Expr.path none (Path.mk false [(PathSegment.mk "kind" PathArguments.none)])),
                  (Expr.path none (Path.mk false [(PathSegment.mk "size" PathArguments.none)])),
                  (Expr.path none (Path.mk false [(PathSegment.mk "align" PathArguments.none)]))])
              false)])),
      (ImplItem.fn
        [
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue " Write some bytes to memory and check for data races."))]
        Visibility.pub
        false
        (Signature.mk
          false
          false
          false
          none
          "store"
          (Generics.mk [] [])
          [
            (FnArg.receiver [] true none true none),
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
                                  (PathSegment.mk "Provenance" PathArguments.none)])))]))]))),
            (FnArg.typed
              []
              (Pat.ident false false "bytes" none)
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
                                    "AbstractByte"
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
            (FnArg.typed
              []
              (Pat.ident false false "align" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "Align" PathArguments.none)]))),
            (FnArg.typed
              []
              (Pat.ident false false "atomicity" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "Atomicity" PathArguments.none)])))]
          false
          (some (Ty.path none (Path.mk false [(PathSegment.mk "Result" PathArguments.none)]))))
        (Block.mk
          [
            (Stmt.letStmt
              []
              (Pat.ident false false "access" none)
              (some
                (Expr.struct
                  none
                  (Path.mk false [(PathSegment.mk "Access" PathArguments.none)])
                  [
                    (FieldValue.mk
                      []
                      (Member.named "ty")
                      false
                      (Expr.path
                        none
                        (Path.mk
                          false
                          [
                            (PathSegment.mk "AccessType" PathArguments.none),
                            (PathSegment.mk "Store" PathArguments.none)]))),
                    (FieldValue.mk
                      []
                      (Member.named "atomicity")
                      true
                      (Expr.path
                        none
                        (Path.mk false [(PathSegment.mk "atomicity" PathArguments.none)]))),
                    (FieldValue.mk
                      []
                      (Member.named "addr")
                      false
                      (Expr.field
                        (Expr.path none (Path.mk false [(PathSegment.mk "ptr" PathArguments.none)]))
                        (Member.named "addr"))),
                    (FieldValue.mk
                      []
                      (Member.named "len")
                      false
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
                              (Expr.path
                                none
                                (Path.mk false [(PathSegment.mk "bytes" PathArguments.none)]))
                              "len"
                              none
                              [])])
                        "unwrap"
                        none
                        []))]
                  false
                  none))
              none),
            (Stmt.expr
              (Expr.methodCall
                (Expr.field
                  (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                  (Member.named "accesses"))
                "push"
                none
                [(Expr.path none (Path.mk false [(PathSegment.mk "access" PathArguments.none)]))])
              true),
            (Stmt.expr
              (Expr.methodCall
                (Expr.field
                  (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                  (Member.named "memory"))
                "store"
                none
                [
                  (Expr.path none (Path.mk false [(PathSegment.mk "ptr" PathArguments.none)])),
                  (Expr.path none (Path.mk false [(PathSegment.mk "bytes" PathArguments.none)])),
                  (Expr.path none (Path.mk false [(PathSegment.mk "align" PathArguments.none)]))])
              false)])),
      (ImplItem.fn
        [
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue " Read some bytes from memory and check for data races."))]
        Visibility.pub
        false
        (Signature.mk
          false
          false
          false
          none
          "load"
          (Generics.mk [] [])
          [
            (FnArg.receiver [] true none true none),
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
                                  (PathSegment.mk "Provenance" PathArguments.none)])))]))]))),
            (FnArg.typed
              []
              (Pat.ident false false "len" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "Size" PathArguments.none)]))),
            (FnArg.typed
              []
              (Pat.ident false false "align" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "Align" PathArguments.none)]))),
            (FnArg.typed
              []
              (Pat.ident false false "atomicity" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "Atomicity" PathArguments.none)])))]
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
                                                "AbstractByte"
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
                                                            (PathSegment.mk
                                                              "Provenance"
                                                              PathArguments.none)])))]))])))]))])))]))]))))
        (Block.mk
          [
            (Stmt.letStmt
              []
              (Pat.ident false false "access" none)
              (some
                (Expr.struct
                  none
                  (Path.mk false [(PathSegment.mk "Access" PathArguments.none)])
                  [
                    (FieldValue.mk
                      []
                      (Member.named "ty")
                      false
                      (Expr.path
                        none
                        (Path.mk
                          false
                          [
                            (PathSegment.mk "AccessType" PathArguments.none),
                            (PathSegment.mk "Load" PathArguments.none)]))),
                    (FieldValue.mk
                      []
                      (Member.named "atomicity")
                      true
                      (Expr.path
                        none
                        (Path.mk false [(PathSegment.mk "atomicity" PathArguments.none)]))),
                    (FieldValue.mk
                      []
                      (Member.named "addr")
                      false
                      (Expr.field
                        (Expr.path none (Path.mk false [(PathSegment.mk "ptr" PathArguments.none)]))
                        (Member.named "addr"))),
                    (FieldValue.mk
                      []
                      (Member.named "len")
                      true
                      (Expr.path none (Path.mk false [(PathSegment.mk "len" PathArguments.none)])))]
                  false
                  none))
              none),
            (Stmt.expr
              (Expr.methodCall
                (Expr.field
                  (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                  (Member.named "accesses"))
                "push"
                none
                [(Expr.path none (Path.mk false [(PathSegment.mk "access" PathArguments.none)]))])
              true),
            (Stmt.expr
              (Expr.methodCall
                (Expr.field
                  (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                  (Member.named "memory"))
                "load"
                none
                [
                  (Expr.path none (Path.mk false [(PathSegment.mk "ptr" PathArguments.none)])),
                  (Expr.path none (Path.mk false [(PathSegment.mk "len" PathArguments.none)])),
                  (Expr.path none (Path.mk false [(PathSegment.mk "align" PathArguments.none)]))])
              false)])),
      (ImplItem.fn
        [
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue
              " Test whether the given pointer is dereferenceable for the given size.")),
          (Attr.mk true "doc" (AttrMeta.nameValue " Raises UB if that is not the case."))]
        Visibility.pub
        false
        (Signature.mk
          false
          false
          false
          none
          "dereferenceable"
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
                                  (PathSegment.mk "Provenance" PathArguments.none)])))]))]))),
            (FnArg.typed
              []
              (Pat.ident false false "len" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "Size" PathArguments.none)])))]
          false
          (some (Ty.path none (Path.mk false [(PathSegment.mk "Result" PathArguments.none)]))))
        (Block.mk
          [
            (Stmt.expr
              (Expr.methodCall
                (Expr.field
                  (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                  (Member.named "memory"))
                "dereferenceable"
                none
                [
                  (Expr.path none (Path.mk false [(PathSegment.mk "ptr" PathArguments.none)])),
                  (Expr.path none (Path.mk false [(PathSegment.mk "len" PathArguments.none)]))])
              false)])),
      (ImplItem.fn
        [
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue
              " A derived form of `dereferenceable` that works with a signed notion on \"length\"."))]
        Visibility.pub
        false
        (Signature.mk
          false
          false
          false
          none
          "signed_dereferenceable"
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
                                  (PathSegment.mk "Provenance" PathArguments.none)])))]))]))),
            (FnArg.typed
              []
              (Pat.ident false false "len" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "Int" PathArguments.none)])))]
          false
          (some (Ty.path none (Path.mk false [(PathSegment.mk "Result" PathArguments.none)]))))
        (Block.mk
          [
            (Stmt.expr
              (Expr.methodCall
                (Expr.field
                  (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                  (Member.named "memory"))
                "signed_dereferenceable"
                none
                [
                  (Expr.path none (Path.mk false [(PathSegment.mk "ptr" PathArguments.none)])),
                  (Expr.path none (Path.mk false [(PathSegment.mk "len" PathArguments.none)]))])
              false)])),
      (ImplItem.fn
        [(Attr.mk true "doc" (AttrMeta.nameValue " Return the retagged pointer."))]
        Visibility.pub
        false
        (Signature.mk
          false
          false
          false
          none
          "retag_ptr"
          (Generics.mk [] [])
          [
            (FnArg.receiver [] true none true none),
            (FnArg.typed
              []
              (Pat.ident false false "frame_extra" none)
              (Ty.reference
                none
                true
                (Ty.path
                  none
                  (Path.mk
                    false
                    [
                      (PathSegment.mk "M" PathArguments.none),
                      (PathSegment.mk "FrameExtra" PathArguments.none)])))),
            (FnArg.typed
              []
              (Pat.ident false false "ptr" none)
              (Ty.path
                none
                (Path.mk
                  false
                  [
                    (PathSegment.mk
                      "Pointer"
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
            (FnArg.typed
              []
              (Pat.ident false false "ptr_type" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "PtrType" PathArguments.none)]))),
            (FnArg.typed
              []
              (Pat.ident false false "fn_entry" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "bool" PathArguments.none)]))),
            (FnArg.typed
              []
              (Pat.ident false false "fn_implicit_writes" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "bool" PathArguments.none)]))),
            (FnArg.typed
              []
              (Pat.ident false false "vtable_lookup" none)
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
                                (Path.mk
                                  false
                                  [
                                    (PathSegment.mk "crate" PathArguments.none),
                                    (PathSegment.mk "lang" PathArguments.none),
                                    (PathSegment.mk "VTable" PathArguments.none)])))))])),
                  (TypeParamBound.lifetime "static")]))]
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
                            (Path.mk
                              false
                              [
                                (PathSegment.mk
                                  "Pointer"
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
                                              (PathSegment.mk "Provenance" PathArguments.none)])))]))])))]))]))))
        (Block.mk
          [
            (Stmt.expr
              (Expr.methodCall
                (Expr.field
                  (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                  (Member.named "memory"))
                "retag_ptr"
                none
                [
                  (Expr.path
                    none
                    (Path.mk false [(PathSegment.mk "frame_extra" PathArguments.none)])),
                  (Expr.path none (Path.mk false [(PathSegment.mk "ptr" PathArguments.none)])),
                  (Expr.path none (Path.mk false [(PathSegment.mk "ptr_type" PathArguments.none)])),
                  (Expr.path none (Path.mk false [(PathSegment.mk "fn_entry" PathArguments.none)])),
                  (Expr.path
                    none
                    (Path.mk false [(PathSegment.mk "fn_implicit_writes" PathArguments.none)])),
                  (Expr.path
                    none
                    (Path.mk false [(PathSegment.mk "vtable_lookup" PathArguments.none)]))])
              false)])),
      (ImplItem.fn
        [
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue " Memory model hook invoked at the end of each function call."))]
        Visibility.pub
        false
        (Signature.mk
          false
          false
          false
          none
          "end_call"
          (Generics.mk [] [])
          [
            (FnArg.receiver [] true none true none),
            (FnArg.typed
              []
              (Pat.ident false false "extra" none)
              (Ty.path
                none
                (Path.mk
                  false
                  [
                    (PathSegment.mk "M" PathArguments.none),
                    (PathSegment.mk "FrameExtra" PathArguments.none)])))]
          false
          (some (Ty.path none (Path.mk false [(PathSegment.mk "Result" PathArguments.none)]))))
        (Block.mk
          [
            (Stmt.expr
              (Expr.methodCall
                (Expr.field
                  (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                  (Member.named "memory"))
                "end_call"
                none
                [(Expr.path none (Path.mk false [(PathSegment.mk "extra" PathArguments.none)]))])
              false)])),
      (ImplItem.fn
        [(Attr.mk true "doc" (AttrMeta.nameValue " Check if there are any memory leaks."))]
        Visibility.pub
        false
        (Signature.mk
          false
          false
          false
          none
          "leak_check"
          (Generics.mk [] [])
          [(FnArg.receiver [] true none false none)]
          false
          (some (Ty.path none (Path.mk false [(PathSegment.mk "Result" PathArguments.none)]))))
        (Block.mk
          [
            (Stmt.expr
              (Expr.methodCall
                (Expr.field
                  (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                  (Member.named "memory"))
                "leak_check"
                none
                [])
              false)]))])

/-- `spec/mem/concurrent.md:131` -/
def type_ThreadId : Item :=
  (Item.type
    [
      (Attr.mk
        true
        "doc"
        (AttrMeta.nameValue " The ID of a thread is an index into the machine's `threads` list."))]
    Visibility.pub
    "ThreadId"
    (Generics.mk [] [])
    (Ty.path none (Path.mk false [(PathSegment.mk "Int" PathArguments.none)])))

/-- `spec/mem/concurrent.md:134` -/
def impl_ConcurrentMemory__check_data_races : Item :=
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
            "ConcurrentMemory"
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
              " Given a list of previous accesses, checks if any of the current accesses is in a data race with any of those."))]
        Visibility.pub
        false
        (Signature.mk
          false
          false
          false
          none
          "check_data_races"
          (Generics.mk [] [])
          [
            (FnArg.receiver [] true none false none),
            (FnArg.typed
              []
              (Pat.ident false false "current_thread" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "ThreadId" PathArguments.none)]))),
            (FnArg.typed
              []
              (Pat.tuple
                [
                  (Pat.ident false false "prev_sync_threads" none),
                  (Pat.ident false false "prev_accesses" none)])
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
                                  (Path.mk false [(PathSegment.mk "Access" PathArguments.none)])))]))]))]))]
          false
          (some (Ty.path none (Path.mk false [(PathSegment.mk "Result" PathArguments.none)]))))
        (Block.mk
          [
            (Stmt.expr
              (Expr.ite
                (Expr.methodCall
                  (Expr.path
                    none
                    (Path.mk false [(PathSegment.mk "prev_sync_threads" PathArguments.none)]))
                  "contains"
                  none
                  [
                    (Expr.path
                      none
                      (Path.mk false [(PathSegment.mk "current_thread" PathArguments.none)]))])
                (Block.mk
                  [
                    (Stmt.expr
                      (Expr.returnExpr
                        (some
                          (Expr.call
                            (Expr.path
                              none
                              (Path.mk false [(PathSegment.mk "Ok" PathArguments.none)]))
                            [(Expr.tuple [])])))
                      false)])
                none)
              false),
            (Stmt.expr
              (Expr.forLoop
                none
                (Pat.ident false false "access" none)
                (Expr.field
                  (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                  (Member.named "accesses"))
                (Block.mk
                  [
                    (Stmt.expr
                      (Expr.ite
                        (Expr.methodCall
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "prev_accesses" PathArguments.none)]))
                          "any"
                          none
                          [
                            (Expr.closure
                              false
                              [(Pat.ident false false "prev_access" none)]
                              none
                              (Expr.methodCall
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "access" PathArguments.none)]))
                                "races"
                                none
                                [
                                  (Expr.path
                                    none
                                    (Path.mk
                                      false
                                      [(PathSegment.mk "prev_access" PathArguments.none)]))]))])
                        (Block.mk
                          [
                            (Stmt.macro
                              []
                              (Macro.mk
                                (Path.mk false [(PathSegment.mk "throw_ub" PathArguments.none)])
                                MacroDelimiter.paren
                                (MacroBody.exprs [(Expr.lit (Lit.str "Data race"))] false))
                              true)])
                        none)
                      false)]))
              false),
            (Stmt.expr
              (Expr.call
                (Expr.path none (Path.mk false [(PathSegment.mk "Ok" PathArguments.none)]))
                [(Expr.tuple [])])
              false)])),
      (ImplItem.fn
        [
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue
              " Prepare memory to track accesses of next step: reset the internal access list to")),
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue " be empty, and return the list of previously collected accesses."))]
        Visibility.pub
        false
        (Signature.mk
          false
          false
          false
          none
          "reset_accesses"
          (Generics.mk [] [])
          [(FnArg.receiver [] true none true none)]
          false
          (some
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
                            (Path.mk false [(PathSegment.mk "Access" PathArguments.none)])))]))]))))
        (Block.mk
          [
            (Stmt.letStmt
              []
              (Pat.ident false false "prev_accesses" none)
              (some
                (Expr.field
                  (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                  (Member.named "accesses")))
              none),
            (Stmt.expr
              (Expr.assign
                (Expr.field
                  (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                  (Member.named "accesses"))
                (Expr.macro
                  (Macro.mk
                    (Path.mk false [(PathSegment.mk "list" PathArguments.none)])
                    MacroDelimiter.bracket
                    (MacroBody.exprs [] false))))
              true),
            (Stmt.expr
              (Expr.path none (Path.mk false [(PathSegment.mk "prev_accesses" PathArguments.none)]))
              false)]))])

/-- `spec/mem/concurrent.md:161` -/
def impl_Access__races : Item :=
  (Item.impl
    []
    false
    false
    (Generics.mk [] [])
    false
    none
    (Ty.path none (Path.mk false [(PathSegment.mk "Access" PathArguments.none)]))
    [
      (ImplItem.fn
        [
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue " Indicates if a races happend between the two given accesses.")),
          (Attr.mk true "doc" (AttrMeta.nameValue " We assume they happen on different threads."))]
        Visibility.inherited
        false
        (Signature.mk
          false
          false
          false
          none
          "races"
          (Generics.mk [] [])
          [
            (FnArg.receiver [] false none false none),
            (FnArg.typed
              []
              (Pat.ident false false "other" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "Self" PathArguments.none)])))]
          false
          (some (Ty.path none (Path.mk false [(PathSegment.mk "bool" PathArguments.none)]))))
        (Block.mk
          [
            (Stmt.expr
              (Expr.ite
                (Expr.binary
                  (Expr.binary
                    (Expr.field
                      (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                      (Member.named "ty"))
                    BinOp.eq
                    (Expr.path
                      none
                      (Path.mk
                        false
                        [
                          (PathSegment.mk "AccessType" PathArguments.none),
                          (PathSegment.mk "Load" PathArguments.none)])))
                  BinOp.and
                  (Expr.binary
                    (Expr.field
                      (Expr.path none (Path.mk false [(PathSegment.mk "other" PathArguments.none)]))
                      (Member.named "ty"))
                    BinOp.eq
                    (Expr.path
                      none
                      (Path.mk
                        false
                        [
                          (PathSegment.mk "AccessType" PathArguments.none),
                          (PathSegment.mk "Load" PathArguments.none)]))))
                (Block.mk [(Stmt.expr (Expr.returnExpr (some (Expr.lit (Lit.bool false)))) true)])
                none)
              false),
            (Stmt.expr
              (Expr.ite
                (Expr.binary
                  (Expr.binary
                    (Expr.field
                      (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                      (Member.named "atomicity"))
                    BinOp.eq
                    (Expr.path
                      none
                      (Path.mk
                        false
                        [
                          (PathSegment.mk "Atomicity" PathArguments.none),
                          (PathSegment.mk "Atomic" PathArguments.none)])))
                  BinOp.and
                  (Expr.binary
                    (Expr.field
                      (Expr.path none (Path.mk false [(PathSegment.mk "other" PathArguments.none)]))
                      (Member.named "atomicity"))
                    BinOp.eq
                    (Expr.path
                      none
                      (Path.mk
                        false
                        [
                          (PathSegment.mk "Atomicity" PathArguments.none),
                          (PathSegment.mk "Atomic" PathArguments.none)]))))
                (Block.mk [(Stmt.expr (Expr.returnExpr (some (Expr.lit (Lit.bool false)))) true)])
                none)
              false),
            (Stmt.letStmt
              []
              (Pat.ident false false "end_addr" none)
              (some
                (Expr.binary
                  (Expr.field
                    (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                    (Member.named "addr"))
                  BinOp.add
                  (Expr.methodCall
                    (Expr.field
                      (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                      (Member.named "len"))
                    "bytes"
                    none
                    [])))
              none),
            (Stmt.letStmt
              []
              (Pat.ident false false "other_end_addr" none)
              (some
                (Expr.binary
                  (Expr.field
                    (Expr.path none (Path.mk false [(PathSegment.mk "other" PathArguments.none)]))
                    (Member.named "addr"))
                  BinOp.add
                  (Expr.methodCall
                    (Expr.field
                      (Expr.path none (Path.mk false [(PathSegment.mk "other" PathArguments.none)]))
                      (Member.named "len"))
                    "bytes"
                    none
                    [])))
              none),
            (Stmt.expr
              (Expr.binary
                (Expr.binary
                  (Expr.path none (Path.mk false [(PathSegment.mk "end_addr" PathArguments.none)]))
                  BinOp.gt
                  (Expr.field
                    (Expr.path none (Path.mk false [(PathSegment.mk "other" PathArguments.none)]))
                    (Member.named "addr")))
                BinOp.and
                (Expr.binary
                  (Expr.path
                    none
                    (Path.mk false [(PathSegment.mk "other_end_addr" PathArguments.none)]))
                  BinOp.gt
                  (Expr.field
                    (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                    (Member.named "addr"))))
              false)]))])

/-- All items of `spec/mem/concurrent.md`, in source order, with provenance. -/
def items : List SourceItem :=
  [
    (SourceItem.mk
      "struct_ConcurrentMemory"
      7
      "763cb464c22090b1766d558c784897bcdd30e21a34288742587dc61a3063b509"
      struct_ConcurrentMemory),
    (SourceItem.mk
      "enum_Atomicity"
      14
      "a8bde11199ede8b0cdbc47e402f42925fbc6b023c6dd987211b062058cd6b57b"
      enum_Atomicity),
    (SourceItem.mk
      "enum_AccessType"
      23
      "a269e39bbaa9f5c3f8963fca60d2e5d8adf091e7fa3a277d3efc0115c4b90ff4"
      enum_AccessType),
    (SourceItem.mk
      "struct_Access"
      29
      "5cfe5e2d9005043d3b15380f45bb34945ea8790310bad87e446649cba435fb71"
      struct_Access),
    (SourceItem.mk
      "impl_ConcurrentMemory__new"
      44
      "3115f9afaf9bca67448e9dbcccda3080a4da794597864e8140dfeb68c26932c2"
      impl_ConcurrentMemory__new),
    (SourceItem.mk
      "type_ThreadId"
      131
      "cc94201425bc141ac2eb4ea6938db964fbba1cad71f34f687766ddd14012a430"
      type_ThreadId),
    (SourceItem.mk
      "impl_ConcurrentMemory__check_data_races"
      134
      "4fd9af133b55d648e6cf0a1e4b226025c24815243741399853395c4d25b63937"
      impl_ConcurrentMemory__check_data_races),
    (SourceItem.mk
      "impl_Access__races"
      161
      "e2a7dd884410223c7cc1841d4ebdd44571280d49e5e09c43d5437dae4ca1e644"
      impl_Access__races)]

end MiniRustSpec.Gen.Items.Mem.Concurrent
