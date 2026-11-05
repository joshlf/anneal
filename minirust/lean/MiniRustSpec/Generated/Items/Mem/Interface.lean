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
`spec/mem/interface.md` (commit `d821c6e3`), one Lean definition per item, in source order.
-/

import MiniRustSpec.Meta.Syntax

set_option maxRecDepth 100000

namespace MiniRustSpec.Gen.Items.Mem.Interface

open MiniRustSpec.Syntax

/-- Path of the upstream file these items were extracted from. -/
def sourceFile : String := "spec/mem/interface.md"

/-- SHA-256 of the upstream file. -/
def sourceSha256 : String := "dfe4e0f504fc8892a520c555cb64b82774973b46f9adcaaaf915f4e5610f4708"

/-- `spec/mem/interface.md:21` -/
def struct_ProvenanceFrag : Item :=
  (Item.struct
    [
      (Attr.mk
        true
        "doc"
        (AttrMeta.nameValue
          " A one-byte provenance fragment stores the provenance and which position")),
      (Attr.mk true "doc" (AttrMeta.nameValue " in the pointer this fragment had."))]
    Visibility.pub
    "ProvenanceFrag"
    (Generics.mk [(GenericParam.type [] "Provenance" [] none)] [])
    (Fields.named
      [
        (Field.mk
          []
          Visibility.pub
          (some "provenance")
          (Ty.path none (Path.mk false [(PathSegment.mk "Provenance" PathArguments.none)]))),
        (Field.mk
          []
          Visibility.pub
          (some "position")
          (Ty.path none (Path.mk false [(PathSegment.mk "Int" PathArguments.none)])))]))

/-- `spec/mem/interface.md:28` -/
def enum_AbstractByte : Item :=
  (Item.enum
    []
    Visibility.pub
    "AbstractByte"
    (Generics.mk [(GenericParam.type [] "Provenance" [] none)] [])
    [
      (Variant.mk
        [(Attr.mk true "doc" (AttrMeta.nameValue " An uninitialized byte."))]
        "Uninit"
        Fields.unit
        none),
      (Variant.mk
        [
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue
              " An initialized byte, optionally with some provenance (if it is encoding a pointer)."))]
        "Init"
        (Fields.unnamed
          [
            (Field.mk
              []
              Visibility.inherited
              none
              (Ty.path none (Path.mk false [(PathSegment.mk "u8" PathArguments.none)]))),
            (Field.mk
              []
              Visibility.inherited
              none
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
                                    "ProvenanceFrag"
                                    (PathArguments.angleBracketed
                                      false
                                      [
                                        (GenericArgument.type
                                          (Ty.path
                                            none
                                            (Path.mk
                                              false
                                              [(PathSegment.mk "Provenance" PathArguments.none)])))]))])))]))])))])
        none)])

/-- `spec/mem/interface.md:35` -/
def impl_AbstractByte__data : Item :=
  (Item.impl
    []
    false
    false
    (Generics.mk [(GenericParam.type [] "Provenance" [] none)] [])
    false
    none
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
                  (Ty.path none (Path.mk false [(PathSegment.mk "Provenance" PathArguments.none)])))]))]))
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
          "data"
          (Generics.mk [] [])
          [(FnArg.receiver [] false none false none)]
          false
          (some
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
                          (Ty.path none (Path.mk false [(PathSegment.mk "u8" PathArguments.none)])))]))]))))
        (Block.mk
          [
            (Stmt.expr
              (Expr.matchExpr
                (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                [
                  (Arm.mk
                    []
                    (Pat.path
                      none
                      (Path.mk
                        false
                        [
                          (PathSegment.mk "AbstractByte" PathArguments.none),
                          (PathSegment.mk "Uninit" PathArguments.none)]))
                    none
                    (Expr.path none (Path.mk false [(PathSegment.mk "None" PathArguments.none)]))),
                  (Arm.mk
                    []
                    (Pat.tupleStruct
                      none
                      (Path.mk
                        false
                        [
                          (PathSegment.mk "AbstractByte" PathArguments.none),
                          (PathSegment.mk "Init" PathArguments.none)])
                      [(Pat.ident false false "data" none), Pat.wild])
                    none
                    (Expr.call
                      (Expr.path none (Path.mk false [(PathSegment.mk "Some" PathArguments.none)]))
                      [
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "data" PathArguments.none)]))]))])
              false)])),
      (ImplItem.fn
        []
        Visibility.pub
        false
        (Signature.mk
          false
          false
          false
          none
          "provenance_frag"
          (Generics.mk [] [])
          [(FnArg.receiver [] false none false none)]
          false
          (some
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
                                  "ProvenanceFrag"
                                  (PathArguments.angleBracketed
                                    false
                                    [
                                      (GenericArgument.type
                                        (Ty.path
                                          none
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "Provenance" PathArguments.none)])))]))])))]))]))))
        (Block.mk
          [
            (Stmt.expr
              (Expr.matchExpr
                (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                [
                  (Arm.mk
                    []
                    (Pat.path
                      none
                      (Path.mk
                        false
                        [
                          (PathSegment.mk "AbstractByte" PathArguments.none),
                          (PathSegment.mk "Uninit" PathArguments.none)]))
                    none
                    (Expr.path none (Path.mk false [(PathSegment.mk "None" PathArguments.none)]))),
                  (Arm.mk
                    []
                    (Pat.tupleStruct
                      none
                      (Path.mk
                        false
                        [
                          (PathSegment.mk "AbstractByte" PathArguments.none),
                          (PathSegment.mk "Init" PathArguments.none)])
                      [Pat.wild, (Pat.ident false false "frag" none)])
                    none
                    (Expr.path none (Path.mk false [(PathSegment.mk "frag" PathArguments.none)])))])
              false)]))])

/-- `spec/mem/interface.md:59` -/
def enum_AllocationKind : Item :=
  (Item.enum
    [
      (Attr.mk
        true
        "doc"
        (AttrMeta.nameValue
          " The \"kind\" of an allocation is used to distinguish, for instance, stack from heap memory."))]
    Visibility.pub
    "AllocationKind"
    (Generics.mk [] [])
    [
      (Variant.mk
        [(Attr.mk true "doc" (AttrMeta.nameValue " Memory for a stack variable."))]
        "Stack"
        Fields.unit
        none),
      (Variant.mk
        [(Attr.mk true "doc" (AttrMeta.nameValue " Memory allocated with the AM heap intrinsics."))]
        "Heap"
        Fields.unit
        none),
      (Variant.mk
        [(Attr.mk true "doc" (AttrMeta.nameValue " Memory for a global variable."))]
        "Global"
        Fields.unit
        none),
      (Variant.mk
        [(Attr.mk true "doc" (AttrMeta.nameValue " Memory for a function."))]
        "Function"
        Fields.unit
        none),
      (Variant.mk
        [(Attr.mk true "doc" (AttrMeta.nameValue " Memory for a vtable."))]
        "VTable"
        Fields.unit
        none)])

/-- `spec/mem/interface.md:73` -/
def trait_Memory : Item :=
  (Item.trait
    [
      (Attr.mk
        true
        "doc"
        (AttrMeta.nameValue
          " *Note*: All memory operations can be non-deterministic, which means that")),
      (Attr.mk
        true
        "doc"
        (AttrMeta.nameValue
          " executing the same operation on the same memory can have different results.")),
      (Attr.mk
        true
        "doc"
        (AttrMeta.nameValue
          " We also let read operations potentially mutate memory (they actually can")),
      (Attr.mk
        true
        "doc"
        (AttrMeta.nameValue
          " change the current state in concurrent memory models and in Stacked Borrows)."))]
    Visibility.pub
    false
    false
    "Memory"
    (Generics.mk [] [])
    []
    [
      (TraitItem.type
        [
          (Attr.mk true "doc" (AttrMeta.nameValue " The target information.")),
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue
              " This doesn't really belong to the memory, but avoids having to quantify over both")),
          (Attr.mk true "doc" (AttrMeta.nameValue " memory and target everywhere."))]
        "T"
        (Generics.mk [] [])
        [
          (TypeParamBound.trait
            false
            false
            []
            (Path.mk false [(PathSegment.mk "Target" PathArguments.none)]))]
        none),
      (TraitItem.type
        [(Attr.mk true "doc" (AttrMeta.nameValue " The type of pointer provenance."))]
        "Provenance"
        (Generics.mk [] [])
        []
        none),
      (TraitItem.type
        [(Attr.mk true "doc" (AttrMeta.nameValue " Extra information for each stack frame."))]
        "FrameExtra"
        (Generics.mk [] [])
        []
        none),
      (TraitItem.type
        [
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue
              " Parameters controlling memory model behavior, passed at construction time."))]
        "Params"
        (Generics.mk [] [])
        [
          (TypeParamBound.trait
            false
            false
            []
            (Path.mk false [(PathSegment.mk "Default" PathArguments.none)]))]
        none),
      (TraitItem.fn
        [
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue
              " Create a new instance of the memory model with the given parameters."))]
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
                    (PathSegment.mk "Self" PathArguments.none),
                    (PathSegment.mk "Params" PathArguments.none)])))]
          false
          (some (Ty.path none (Path.mk false [(PathSegment.mk "Self" PathArguments.none)]))))
        none),
      (TraitItem.fn
        [
          (Attr.mk true "doc" (AttrMeta.nameValue " Create a new allocation.")),
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue
              " The initial contents of the allocation are `AbstractByte::Uninit`.")),
          (Attr.mk true "doc" (AttrMeta.nameValue "")),
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue
              " This is the only non-deterministic operation in the memory interface."))]
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
                                              (PathSegment.mk "Self" PathArguments.none),
                                              (PathSegment.mk "Provenance" PathArguments.none)])))]))])))]))]))))
        none),
      (TraitItem.fn
        [(Attr.mk true "doc" (AttrMeta.nameValue " Remove an allocation."))]
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
                                  (PathSegment.mk "Self" PathArguments.none),
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
        none),
      (TraitItem.fn
        [(Attr.mk true "doc" (AttrMeta.nameValue " Write some bytes to memory."))]
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
                                  (PathSegment.mk "Self" PathArguments.none),
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
                                                (PathSegment.mk "Self" PathArguments.none),
                                                (PathSegment.mk "Provenance" PathArguments.none)])))]))])))]))]))),
            (FnArg.typed
              []
              (Pat.ident false false "align" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "Align" PathArguments.none)])))]
          false
          (some (Ty.path none (Path.mk false [(PathSegment.mk "Result" PathArguments.none)]))))
        none),
      (TraitItem.fn
        [
          (Attr.mk true "doc" (AttrMeta.nameValue " Read some bytes from memory.")),
          (Attr.mk true "doc" (AttrMeta.nameValue "")),
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue
              " Needs `&mut self` because in the aliasing model, reading changes the machine state."))]
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
                                  (PathSegment.mk "Self" PathArguments.none),
                                  (PathSegment.mk "Provenance" PathArguments.none)])))]))]))),
            (FnArg.typed
              []
              (Pat.ident false false "len" none)
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
                                                            (PathSegment.mk
                                                              "Self"
                                                              PathArguments.none),
                                                            (PathSegment.mk
                                                              "Provenance"
                                                              PathArguments.none)])))]))])))]))])))]))]))))
        none),
      (TraitItem.fn
        [
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue
              " Test whether the given pointer is dereferenceable for the given size."))]
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
                                  (PathSegment.mk "Self" PathArguments.none),
                                  (PathSegment.mk "Provenance" PathArguments.none)])))]))]))),
            (FnArg.typed
              []
              (Pat.ident false false "len" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "Size" PathArguments.none)])))]
          false
          (some (Ty.path none (Path.mk false [(PathSegment.mk "Result" PathArguments.none)]))))
        none),
      (TraitItem.fn
        [
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue
              " A derived form of `dereferenceable` that works with a signed notion of \"length\"."))]
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
                                  (PathSegment.mk "Self" PathArguments.none),
                                  (PathSegment.mk "Provenance" PathArguments.none)])))]))]))),
            (FnArg.typed
              []
              (Pat.ident false false "len" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "Int" PathArguments.none)])))]
          false
          (some (Ty.path none (Path.mk false [(PathSegment.mk "Result" PathArguments.none)]))))
        (some
          (Block.mk
            [
              (Stmt.expr
                (Expr.ite
                  (Expr.binary
                    (Expr.path none (Path.mk false [(PathSegment.mk "len" PathArguments.none)]))
                    BinOp.gt
                    (Expr.lit (Lit.int 0 "")))
                  (Block.mk
                    [
                      (Stmt.expr
                        (Expr.methodCall
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                          "dereferenceable"
                          none
                          [
                            (Expr.path
                              none
                              (Path.mk false [(PathSegment.mk "ptr" PathArguments.none)])),
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
                                  (Expr.path
                                    none
                                    (Path.mk false [(PathSegment.mk "len" PathArguments.none)]))])
                              "unwrap"
                              none
                              [])])
                        false)])
                  (some
                    (Expr.block
                      none
                      (Block.mk
                        [
                          (Stmt.letStmt
                            []
                            (Pat.ident false false "begin_ptr" none)
                            (some
                              (Expr.struct
                                none
                                (Path.mk false [(PathSegment.mk "ThinPointer" PathArguments.none)])
                                [
                                  (FieldValue.mk
                                    []
                                    (Member.named "addr")
                                    false
                                    (Expr.binary
                                      (Expr.field
                                        (Expr.path
                                          none
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "ptr" PathArguments.none)]))
                                        (Member.named "addr"))
                                      BinOp.add
                                      (Expr.path
                                        none
                                        (Path.mk false [(PathSegment.mk "len" PathArguments.none)]))))]
                                true
                                (some
                                  (Expr.path
                                    none
                                    (Path.mk false [(PathSegment.mk "ptr" PathArguments.none)])))))
                            none),
                          (Stmt.expr
                            (Expr.methodCall
                              (Expr.path
                                none
                                (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                              "dereferenceable"
                              none
                              [
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "begin_ptr" PathArguments.none)])),
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
                                      (Expr.unary
                                        UnOp.neg
                                        (Expr.path
                                          none
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "len" PathArguments.none)])))])
                                  "unwrap"
                                  none
                                  [])])
                            false)]))))
                false)]))),
      (TraitItem.fn
        [
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue " Retag the given pointer, which has the given type.")),
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue
              " `fn_entry` indicates whether this is one of the special retags that happen")),
          (Attr.mk true "doc" (AttrMeta.nameValue " right at the top of each function.")),
          (Attr.mk true "doc" (AttrMeta.nameValue "")),
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue " This can assume the pointer satisfies the language invariant,")),
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue " in particular, it must be `dereferenceable` for its size.")),
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue
              " Violating this or breaking this for the return value is a spec bug.")),
          (Attr.mk true "doc" (AttrMeta.nameValue "")),
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue
              " The `vtable_lookup` is given, since computing the size and UnsafeCell positions")),
          (Attr.mk true "doc" (AttrMeta.nameValue " requires information about vtables.")),
          (Attr.mk true "doc" (AttrMeta.nameValue "")),
          (Attr.mk true "doc" (AttrMeta.nameValue " Return the retagged pointer."))]
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
              (Pat.ident false false "_frame_extra" none)
              (Ty.reference
                none
                true
                (Ty.path
                  none
                  (Path.mk
                    false
                    [
                      (PathSegment.mk "Self" PathArguments.none),
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
                                  (PathSegment.mk "Self" PathArguments.none),
                                  (PathSegment.mk "Provenance" PathArguments.none)])))]))]))),
            (FnArg.typed
              []
              (Pat.ident false false "_ptr_type" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "PtrType" PathArguments.none)]))),
            (FnArg.typed
              []
              (Pat.ident false false "_fn_entry" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "bool" PathArguments.none)]))),
            (FnArg.typed
              []
              (Pat.ident false false "_fn_implicit_writes" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "bool" PathArguments.none)]))),
            (FnArg.typed
              []
              (Pat.ident false false "_vtable_lookup" none)
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
                                                  (PathSegment.mk "Self" PathArguments.none),
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
                                              (PathSegment.mk "Self" PathArguments.none),
                                              (PathSegment.mk "Provenance" PathArguments.none)])))]))])))]))]))))
        (some
          (Block.mk
            [
              (Stmt.expr
                (Expr.call
                  (Expr.path none (Path.mk false [(PathSegment.mk "ret" PathArguments.none)]))
                  [(Expr.path none (Path.mk false [(PathSegment.mk "ptr" PathArguments.none)]))])
                false)]))),
      (TraitItem.fn
        [
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue " Create the extra information for a stack frame."))]
        (Signature.mk
          false
          false
          false
          none
          "new_call"
          (Generics.mk [] [])
          []
          false
          (some
            (Ty.path
              none
              (Path.mk
                false
                [
                  (PathSegment.mk "Self" PathArguments.none),
                  (PathSegment.mk "FrameExtra" PathArguments.none)]))))
        none),
      (TraitItem.fn
        [
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue " Memory model hook invoked at the end of each function call."))]
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
              (Pat.ident false false "_extra" none)
              (Ty.path
                none
                (Path.mk
                  false
                  [
                    (PathSegment.mk "Self" PathArguments.none),
                    (PathSegment.mk "FrameExtra" PathArguments.none)])))]
          false
          (some (Ty.path none (Path.mk false [(PathSegment.mk "Result" PathArguments.none)]))))
        (some
          (Block.mk
            [
              (Stmt.expr
                (Expr.call
                  (Expr.path none (Path.mk false [(PathSegment.mk "ret" PathArguments.none)]))
                  [(Expr.tuple [])])
                false)]))),
      (TraitItem.fn
        [(Attr.mk true "doc" (AttrMeta.nameValue " Check if there are any memory leaks."))]
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
        none)])

/-- All items of `spec/mem/interface.md`, in source order, with provenance. -/
def items : List SourceItem :=
  [
    (SourceItem.mk
      "struct_ProvenanceFrag"
      21
      "f1c43e27e167f77b1f6f1ae7021ec6affe8c2d38fbf0228c18996452f3315811"
      struct_ProvenanceFrag),
    (SourceItem.mk
      "enum_AbstractByte"
      28
      "1cc3f5589e05cc3232fad46057d3b5660dc2dc998b1a2612fe379e607177b4b6"
      enum_AbstractByte),
    (SourceItem.mk
      "impl_AbstractByte__data"
      35
      "d66c13f7b6681f5079ba957ec27f0e9319ec234f0791723026e2858a606376bb"
      impl_AbstractByte__data),
    (SourceItem.mk
      "enum_AllocationKind"
      59
      "e24a60ac86cb9fce0e3556cf44cca7b6ffd1c10b0152b52757d7ca7f38ae9981"
      enum_AllocationKind),
    (SourceItem.mk
      "trait_Memory"
      73
      "fdf08123b42ead28129fd509b3f84085b0c6501698755a6625540fabcf542427"
      trait_Memory)]

end MiniRustSpec.Gen.Items.Mem.Interface
