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
`spec/lang/types.md` (commit `d821c6e3`), one Lean definition per item, in source order.
-/

import MiniRustSpec.Meta.Syntax

set_option maxRecDepth 100000

namespace MiniRustSpec.Gen.Items.Lang.Types

open MiniRustSpec.Syntax

/-- Path of the upstream file these items were extracted from. -/
def sourceFile : String := "spec/lang/types.md"

/-- SHA-256 of the upstream file. -/
def sourceSha256 : String := "4fef7acaaef6c1e0d14ab65bfd1934b495aa946ec7d23b42f0ab1d2cb30afdc7"

/-- `spec/lang/types.md:20` -/
def enum_Type : Item :=
  (Item.enum
    [(Attr.mk true "doc" (AttrMeta.nameValue " The types of MiniRust."))]
    Visibility.pub
    "Type"
    (Generics.mk [] [])
    [
      (Variant.mk
        []
        "Int"
        (Fields.unnamed
          [
            (Field.mk
              []
              Visibility.inherited
              none
              (Ty.path none (Path.mk false [(PathSegment.mk "IntType" PathArguments.none)])))])
        none),
      (Variant.mk [] "Bool" Fields.unit none),
      (Variant.mk
        [
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue
              " `Ptr` represents all pointer types: references, raw pointers, boxes, function and vtable pointers.")),
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue
              " A pointer type does *not* need the full pointee type, since (de)serializing a pointer does not")),
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue
              " require knowledge about the pointee. We only track the metadata kind and basic pointee information")),
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue
              " like size and alignment that is required to check reference validity. This also means types have a finite")),
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue " representation even when the Rust type is recursive."))]
        "Ptr"
        (Fields.unnamed
          [
            (Field.mk
              []
              Visibility.inherited
              none
              (Ty.path none (Path.mk false [(PathSegment.mk "PtrType" PathArguments.none)])))])
        none),
      (Variant.mk
        [
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue
              " \"Tuple\" is used for all heterogeneous types, i.e., both Rust tuples and structs."))]
        "Tuple"
        (Fields.named
          [
            (Field.mk
              [(Attr.mk true "doc" (AttrMeta.nameValue " Fields must not overlap."))]
              Visibility.inherited
              (some "sized_fields")
              (Ty.path none (Path.mk false [(PathSegment.mk "Fields" PathArguments.none)]))),
            (Field.mk
              [
                (Attr.mk
                  true
                  "doc"
                  (AttrMeta.nameValue " The layout of the sized fiels, i.e., the head."))]
              Visibility.inherited
              (some "sized_head_layout")
              (Ty.path none (Path.mk false [(PathSegment.mk "TupleHeadLayout" PathArguments.none)]))),
            (Field.mk
              [
                (Attr.mk
                  true
                  "doc"
                  (AttrMeta.nameValue
                    " A last field (in terms of offset), i.e., the tail, may contain an unsized type,")),
                (Attr.mk
                  true
                  "doc"
                  (AttrMeta.nameValue
                    " then its offset is given by rounding the `end` of `sized_head_layout` up to the alignment of this type.")),
                (Attr.mk true "specr::indirection" AttrMeta.path)]
              Visibility.inherited
              (some "unsized_field")
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
                              (Path.mk false [(PathSegment.mk "Type" PathArguments.none)])))]))])))])
        none),
      (Variant.mk
        []
        "Array"
        (Fields.named
          [
            (Field.mk
              [(Attr.mk true "specr::indirection" AttrMeta.path)]
              Visibility.inherited
              (some "elem")
              (Ty.path none (Path.mk false [(PathSegment.mk "Type" PathArguments.none)]))),
            (Field.mk
              []
              Visibility.inherited
              (some "count")
              (Ty.path none (Path.mk false [(PathSegment.mk "Int" PathArguments.none)])))])
        none),
      (Variant.mk
        [
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue
              " Slices, i.e. `[T]` are unsized types which therefore cannot be represented as values.")),
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue " This type is also used for strings: `str` are treated as `[u8]`."))]
        "Slice"
        (Fields.named
          [
            (Field.mk
              [(Attr.mk true "specr::indirection" AttrMeta.path)]
              Visibility.inherited
              (some "elem")
              (Ty.path none (Path.mk false [(PathSegment.mk "Type" PathArguments.none)])))])
        none),
      (Variant.mk
        []
        "Union"
        (Fields.named
          [
            (Field.mk
              [
                (Attr.mk
                  true
                  "doc"
                  (AttrMeta.nameValue
                    " Fields *may* overlap. Fields only exist for field access place projections,")),
                (Attr.mk
                  true
                  "doc"
                  (AttrMeta.nameValue " they are irrelevant for the representation relation."))]
              Visibility.inherited
              (some "fields")
              (Ty.path none (Path.mk false [(PathSegment.mk "Fields" PathArguments.none)]))),
            (Field.mk
              [
                (Attr.mk
                  true
                  "doc"
                  (AttrMeta.nameValue
                    " A union can be split into multiple \"chunks\", where only the data inside those chunks is")),
                (Attr.mk
                  true
                  "doc"
                  (AttrMeta.nameValue
                    " preserved, and data between chunks is lost (like padding in a struct).")),
                (Attr.mk
                  true
                  "doc"
                  (AttrMeta.nameValue
                    " This is necessary to model the behavior of some `repr(C)` unions, see")),
                (Attr.mk
                  true
                  "doc"
                  (AttrMeta.nameValue
                    " <https://github.com/rust-lang/unsafe-code-guidelines/issues/156> for details."))]
              Visibility.inherited
              (some "chunks")
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
                                  (Path.mk false [(PathSegment.mk "Offset" PathArguments.none)])),
                                (Ty.path
                                  none
                                  (Path.mk false [(PathSegment.mk "Size" PathArguments.none)]))]))]))]))),
            (Field.mk
              [
                (Attr.mk
                  true
                  "doc"
                  (AttrMeta.nameValue
                    " The total size of the union, can indicate padding after the last chunk."))]
              Visibility.inherited
              (some "size")
              (Ty.path none (Path.mk false [(PathSegment.mk "Size" PathArguments.none)]))),
            (Field.mk
              [
                (Attr.mk
                  true
                  "doc"
                  (AttrMeta.nameValue
                    " Total alignment of the union. Due to `repr(packed)` and `repr(align)`,")),
                (Attr.mk
                  true
                  "doc"
                  (AttrMeta.nameValue " this is independent of the fields' alignment."))]
              Visibility.inherited
              (some "align")
              (Ty.path none (Path.mk false [(PathSegment.mk "Align" PathArguments.none)])))])
        none),
      (Variant.mk
        []
        "Enum"
        (Fields.named
          [
            (Field.mk
              [
                (Attr.mk
                  true
                  "doc"
                  (AttrMeta.nameValue
                    " The map variants, each identified by a discriminant. Each variant is given by a type and its")),
                (Attr.mk
                  true
                  "doc"
                  (AttrMeta.nameValue
                    " tag description. All variants are thought to \"start at offset 0\"; if the")),
                (Attr.mk
                  true
                  "doc"
                  (AttrMeta.nameValue
                    " discriminant is encoded as an explicit tag, then that will be put into the")),
                (Attr.mk
                  true
                  "doc"
                  (AttrMeta.nameValue
                    " padding of the active variant. (This means it is *not* safe to hand out mutable")),
                (Attr.mk
                  true
                  "doc"
                  (AttrMeta.nameValue
                    " references to a variant at that type, as then the tag might be overwritten!)")),
                (Attr.mk
                  true
                  "doc"
                  (AttrMeta.nameValue
                    " The Rust type `!` is encoded as an `Enum` with an empty list of variants."))]
              Visibility.inherited
              (some "variants")
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
                              (Path.mk false [(PathSegment.mk "Int" PathArguments.none)]))),
                          (GenericArgument.type
                            (Ty.path
                              none
                              (Path.mk false [(PathSegment.mk "Variant" PathArguments.none)])))]))]))),
            (Field.mk
              [
                (Attr.mk
                  true
                  "doc"
                  (AttrMeta.nameValue
                    " The `IntType` for the discriminant. This is used for the type of")),
                (Attr.mk
                  true
                  "doc"
                  (AttrMeta.nameValue
                    " `GetDiscriminant` and `SetDiscriminant`. It is entirely independent of how")),
                (Attr.mk
                  true
                  "doc"
                  (AttrMeta.nameValue " the discriminant is represented in memory (the \"tag\")."))]
              Visibility.inherited
              (some "discriminant_ty")
              (Ty.path none (Path.mk false [(PathSegment.mk "IntType" PathArguments.none)]))),
            (Field.mk
              [
                (Attr.mk
                  true
                  "doc"
                  (AttrMeta.nameValue
                    " The decision tree to decode the discriminant from the tag at runtime."))]
              Visibility.inherited
              (some "discriminator")
              (Ty.path none (Path.mk false [(PathSegment.mk "Discriminator" PathArguments.none)]))),
            (Field.mk
              [
                (Attr.mk
                  true
                  "doc"
                  (AttrMeta.nameValue " The total size of the enum can indicate trailing padding.")),
                (Attr.mk
                  true
                  "doc"
                  (AttrMeta.nameValue " Must be large enough to contain all variants."))]
              Visibility.inherited
              (some "size")
              (Ty.path none (Path.mk false [(PathSegment.mk "Size" PathArguments.none)]))),
            (Field.mk
              [
                (Attr.mk
                  true
                  "doc"
                  (AttrMeta.nameValue
                    " Total alignment of the enum. Due to `repr(packed)` and `repr(align)`,")),
                (Attr.mk
                  true
                  "doc"
                  (AttrMeta.nameValue " this is independent of the fields' alignment."))]
              Visibility.inherited
              (some "align")
              (Ty.path none (Path.mk false [(PathSegment.mk "Align" PathArguments.none)])))])
        none),
      (Variant.mk
        [
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue " A `dyn TraitName`. Commonly only used behind a pointer."))]
        "TraitObject"
        (Fields.unnamed
          [
            (Field.mk
              []
              Visibility.inherited
              none
              (Ty.path none (Path.mk false [(PathSegment.mk "TraitName" PathArguments.none)])))])
        none)])

/-- `spec/lang/types.md:94` -/
def struct_IntType : Item :=
  (Item.struct
    []
    Visibility.pub
    "IntType"
    (Generics.mk [] [])
    (Fields.named
      [
        (Field.mk
          []
          Visibility.pub
          (some "signed")
          (Ty.path none (Path.mk false [(PathSegment.mk "Signedness" PathArguments.none)]))),
        (Field.mk
          []
          Visibility.pub
          (some "size")
          (Ty.path none (Path.mk false [(PathSegment.mk "Size" PathArguments.none)])))]))

/-- `spec/lang/types.md:99` -/
def type_Fields : Item :=
  (Item.type
    []
    Visibility.pub
    "Fields"
    (Generics.mk [] [])
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
                      (Ty.path none (Path.mk false [(PathSegment.mk "Offset" PathArguments.none)])),
                      (Ty.path none (Path.mk false [(PathSegment.mk "Type" PathArguments.none)]))]))]))])))

/-- `spec/lang/types.md:101` -/
def struct_Variant : Item :=
  (Item.struct
    []
    Visibility.pub
    "Variant"
    (Generics.mk [] [])
    (Fields.named
      [
        (Field.mk
          [(Attr.mk true "doc" (AttrMeta.nameValue " The actual type of the variant."))]
          Visibility.pub
          (some "ty")
          (Ty.path none (Path.mk false [(PathSegment.mk "Type" PathArguments.none)]))),
        (Field.mk
          [
            (Attr.mk
              true
              "doc"
              (AttrMeta.nameValue
                " The information on where to store which values to write the tag.")),
            (Attr.mk
              true
              "doc"
              (AttrMeta.nameValue
                " MUST NOT touch any bytes written by the actual type of the variant and vice")),
            (Attr.mk
              true
              "doc"
              (AttrMeta.nameValue
                " versa. This is because we allow references/pointers to (enum) fields which")),
            (Attr.mk
              true
              "doc"
              (AttrMeta.nameValue
                " should be able to dereference without having to deal with the tag."))]
          Visibility.pub
          (some "tagger")
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
                          (Path.mk false [(PathSegment.mk "Offset" PathArguments.none)]))),
                      (GenericArgument.type
                        (Ty.tuple
                          [
                            (Ty.path
                              none
                              (Path.mk false [(PathSegment.mk "IntType" PathArguments.none)])),
                            (Ty.path
                              none
                              (Path.mk false [(PathSegment.mk "Int" PathArguments.none)]))]))]))])))]))

/-- `spec/lang/types.md:111` -/
def enum_Discriminator : Item :=
  (Item.enum
    [
      (Attr.mk
        true
        "doc"
        (AttrMeta.nameValue
          " The decision tree that computes the discriminant out of the tag for a specific")),
      (Attr.mk true "doc" (AttrMeta.nameValue " enum type."))]
    Visibility.pub
    "Discriminator"
    (Generics.mk [] [])
    [
      (Variant.mk
        [(Attr.mk true "doc" (AttrMeta.nameValue " We know the discriminant."))]
        "Known"
        (Fields.unnamed
          [
            (Field.mk
              []
              Visibility.inherited
              none
              (Ty.path none (Path.mk false [(PathSegment.mk "Int" PathArguments.none)])))])
        none),
      (Variant.mk
        [
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue " Tag decoding failed, there is no valid discriminant."))]
        "Invalid"
        Fields.unit
        none),
      (Variant.mk
        [
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue
              " We don't know the discriminant, so we branch on the value of a specific value."))]
        "Branch"
        (Fields.named
          [
            (Field.mk
              []
              Visibility.inherited
              (some "offset")
              (Ty.path none (Path.mk false [(PathSegment.mk "Offset" PathArguments.none)]))),
            (Field.mk
              []
              Visibility.inherited
              (some "value_type")
              (Ty.path none (Path.mk false [(PathSegment.mk "IntType" PathArguments.none)]))),
            (Field.mk
              [(Attr.mk true "specr::indirection" AttrMeta.path)]
              Visibility.inherited
              (some "fallback")
              (Ty.path none (Path.mk false [(PathSegment.mk "Discriminator" PathArguments.none)]))),
            (Field.mk
              [
                (Attr.mk
                  true
                  "doc"
                  (AttrMeta.nameValue
                    " An left-inclusive right-exclusive range of values that map to some Discriminator."))]
              Visibility.inherited
              (some "children")
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
                            (Ty.tuple
                              [
                                (Ty.path
                                  none
                                  (Path.mk false [(PathSegment.mk "Int" PathArguments.none)])),
                                (Ty.path
                                  none
                                  (Path.mk false [(PathSegment.mk "Int" PathArguments.none)]))])),
                          (GenericArgument.type
                            (Ty.path
                              none
                              (Path.mk false [(PathSegment.mk "Discriminator" PathArguments.none)])))]))])))])
        none)])

/-- `spec/lang/types.md:138` -/
def impl_IntType__align : Item :=
  (Item.impl
    []
    false
    false
    (Generics.mk [] [])
    false
    none
    (Ty.path none (Path.mk false [(PathSegment.mk "IntType" PathArguments.none)]))
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
          "align"
          (Generics.mk
            [
              (GenericParam.type
                []
                "T"
                [
                  (TypeParamBound.trait
                    false
                    false
                    []
                    (Path.mk false [(PathSegment.mk "Target" PathArguments.none)]))]
                none)]
            [])
          [(FnArg.receiver [] false none false none)]
          false
          (some (Ty.path none (Path.mk false [(PathSegment.mk "Align" PathArguments.none)]))))
        (Block.mk
          [
            (Stmt.letStmt
              []
              (Pat.ident false false "size" none)
              (some
                (Expr.methodCall
                  (Expr.field
                    (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                    (Member.named "size"))
                  "bytes"
                  none
                  []))
              none),
            (Stmt.letStmt
              []
              (Pat.ident false false "natural_align" none)
              (some
                (Expr.methodCall
                  (Expr.call
                    (Expr.path
                      none
                      (Path.mk
                        false
                        [
                          (PathSegment.mk "Align" PathArguments.none),
                          (PathSegment.mk "from_bytes" PathArguments.none)]))
                    [(Expr.path none (Path.mk false [(PathSegment.mk "size" PathArguments.none)]))])
                  "unwrap"
                  none
                  []))
              none),
            (Stmt.expr
              (Expr.methodCall
                (Expr.path
                  none
                  (Path.mk false [(PathSegment.mk "natural_align" PathArguments.none)]))
                "min"
                none
                [
                  (Expr.path
                    none
                    (Path.mk
                      false
                      [
                        (PathSegment.mk "T" PathArguments.none),
                        (PathSegment.mk "INT_MAX_ALIGN" PathArguments.none)]))])
              false)]))])

/-- `spec/lang/types.md:148` -/
def impl_Type__layout : Item :=
  (Item.impl
    []
    false
    false
    (Generics.mk [] [])
    false
    none
    (Ty.path none (Path.mk false [(PathSegment.mk "Type" PathArguments.none)]))
    [
      (ImplItem.fn
        [
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue
              " The layout, i.e. the size and align of the type. For `?Sized` types, this needs to be computed."))]
        Visibility.pub
        false
        (Signature.mk
          false
          false
          false
          none
          "layout"
          (Generics.mk
            [
              (GenericParam.type
                []
                "T"
                [
                  (TypeParamBound.trait
                    false
                    false
                    []
                    (Path.mk false [(PathSegment.mk "Target" PathArguments.none)]))]
                none)]
            [])
          [(FnArg.receiver [] false none false none)]
          false
          (some
            (Ty.path none (Path.mk false [(PathSegment.mk "LayoutStrategy" PathArguments.none)]))))
        (Block.mk
          [
            (Stmt.item (Item.use [] Visibility.inherited false (UseTree.path "Type" UseTree.glob))),
            (Stmt.item
              (Item.use
                []
                Visibility.inherited
                false
                (UseTree.path "LayoutStrategy" (UseTree.name "Sized")))),
            (Stmt.expr
              (Expr.matchExpr
                (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                [
                  (Arm.mk
                    []
                    (Pat.tupleStruct
                      none
                      (Path.mk false [(PathSegment.mk "Int" PathArguments.none)])
                      [(Pat.ident false false "int_type" none)])
                    none
                    (Expr.call
                      (Expr.path none (Path.mk false [(PathSegment.mk "Sized" PathArguments.none)]))
                      [
                        (Expr.field
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "int_type" PathArguments.none)]))
                          (Member.named "size")),
                        (Expr.methodCall
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "int_type" PathArguments.none)]))
                          "align"
                          (some
                            [
                              (GenericArgument.type
                                (Ty.path
                                  none
                                  (Path.mk false [(PathSegment.mk "T" PathArguments.none)])))])
                          [])])),
                  (Arm.mk
                    []
                    (Pat.ident false false "Bool" none)
                    none
                    (Expr.call
                      (Expr.path none (Path.mk false [(PathSegment.mk "Sized" PathArguments.none)]))
                      [
                        (Expr.call
                          (Expr.path
                            none
                            (Path.mk
                              false
                              [
                                (PathSegment.mk "Size" PathArguments.none),
                                (PathSegment.mk "from_bytes_const" PathArguments.none)]))
                          [(Expr.lit (Lit.int 1 ""))]),
                        (Expr.path
                          none
                          (Path.mk
                            false
                            [
                              (PathSegment.mk "Align" PathArguments.none),
                              (PathSegment.mk "ONE" PathArguments.none)]))])),
                  (Arm.mk
                    []
                    (Pat.tupleStruct
                      none
                      (Path.mk false [(PathSegment.mk "Ptr" PathArguments.none)])
                      [(Pat.ident false false "p" none)])
                    (some
                      (Expr.binary
                        (Expr.methodCall
                          (Expr.path none (Path.mk false [(PathSegment.mk "p" PathArguments.none)]))
                          "meta_kind"
                          none
                          [])
                        BinOp.eq
                        (Expr.path
                          none
                          (Path.mk
                            false
                            [
                              (PathSegment.mk "PointerMetaKind" PathArguments.none),
                              (PathSegment.mk "None" PathArguments.none)]))))
                    (Expr.call
                      (Expr.path none (Path.mk false [(PathSegment.mk "Sized" PathArguments.none)]))
                      [
                        (Expr.path
                          none
                          (Path.mk
                            false
                            [
                              (PathSegment.mk "T" PathArguments.none),
                              (PathSegment.mk "PTR_SIZE" PathArguments.none)])),
                        (Expr.path
                          none
                          (Path.mk
                            false
                            [
                              (PathSegment.mk "T" PathArguments.none),
                              (PathSegment.mk "PTR_ALIGN" PathArguments.none)]))])),
                  (Arm.mk
                    []
                    (Pat.tupleStruct
                      none
                      (Path.mk false [(PathSegment.mk "Ptr" PathArguments.none)])
                      [Pat.wild])
                    none
                    (Expr.call
                      (Expr.path none (Path.mk false [(PathSegment.mk "Sized" PathArguments.none)]))
                      [
                        (Expr.binary
                          (Expr.call
                            (Expr.path
                              none
                              (Path.mk
                                false
                                [
                                  (PathSegment.mk "libspecr" PathArguments.none),
                                  (PathSegment.mk "Int" PathArguments.none),
                                  (PathSegment.mk "from" PathArguments.none)]))
                            [(Expr.lit (Lit.int 2 ""))])
                          BinOp.mul
                          (Expr.path
                            none
                            (Path.mk
                              false
                              [
                                (PathSegment.mk "T" PathArguments.none),
                                (PathSegment.mk "PTR_SIZE" PathArguments.none)]))),
                        (Expr.path
                          none
                          (Path.mk
                            false
                            [
                              (PathSegment.mk "T" PathArguments.none),
                              (PathSegment.mk "PTR_ALIGN" PathArguments.none)]))])),
                  (Arm.mk
                    []
                    (Pat.or
                      [
                        (Pat.struct
                          none
                          (Path.mk false [(PathSegment.mk "Union" PathArguments.none)])
                          [
                            (FieldPat.mk
                              []
                              (Member.named "size")
                              true
                              (Pat.ident false false "size" none)),
                            (FieldPat.mk
                              []
                              (Member.named "align")
                              true
                              (Pat.ident false false "align" none))]
                          true),
                        (Pat.struct
                          none
                          (Path.mk false [(PathSegment.mk "Enum" PathArguments.none)])
                          [
                            (FieldPat.mk
                              []
                              (Member.named "size")
                              true
                              (Pat.ident false false "size" none)),
                            (FieldPat.mk
                              []
                              (Member.named "align")
                              true
                              (Pat.ident false false "align" none))]
                          true)])
                    none
                    (Expr.call
                      (Expr.path none (Path.mk false [(PathSegment.mk "Sized" PathArguments.none)]))
                      [
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "size" PathArguments.none)])),
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "align" PathArguments.none)]))])),
                  (Arm.mk
                    []
                    (Pat.struct
                      none
                      (Path.mk false [(PathSegment.mk "Tuple" PathArguments.none)])
                      [
                        (FieldPat.mk
                          []
                          (Member.named "sized_head_layout")
                          true
                          (Pat.ident false false "sized_head_layout" none)),
                        (FieldPat.mk
                          []
                          (Member.named "unsized_field")
                          true
                          (Pat.ident false false "unsized_field" none))]
                      true)
                    none
                    (Expr.matchExpr
                      (Expr.path
                        none
                        (Path.mk false [(PathSegment.mk "unsized_field" PathArguments.none)]))
                      [
                        (Arm.mk
                          []
                          (Pat.ident false false "None" none)
                          none
                          (Expr.block
                            none
                            (Block.mk
                              [
                                (Stmt.letStmt
                                  []
                                  (Pat.tuple
                                    [
                                      (Pat.ident false false "size" none),
                                      (Pat.ident false false "align" none)])
                                  (some
                                    (Expr.methodCall
                                      (Expr.path
                                        none
                                        (Path.mk
                                          false
                                          [(PathSegment.mk "sized_head_layout" PathArguments.none)]))
                                      "head_size_and_align"
                                      none
                                      []))
                                  none),
                                (Stmt.expr
                                  (Expr.call
                                    (Expr.path
                                      none
                                      (Path.mk false [(PathSegment.mk "Sized" PathArguments.none)]))
                                    [
                                      (Expr.path
                                        none
                                        (Path.mk false [(PathSegment.mk "size" PathArguments.none)])),
                                      (Expr.path
                                        none
                                        (Path.mk
                                          false
                                          [(PathSegment.mk "align" PathArguments.none)]))])
                                  false)]))),
                        (Arm.mk
                          []
                          (Pat.tupleStruct
                            none
                            (Path.mk false [(PathSegment.mk "Some" PathArguments.none)])
                            [(Pat.ident false false "tail_ty" none)])
                          none
                          (Expr.struct
                            none
                            (Path.mk
                              false
                              [
                                (PathSegment.mk "LayoutStrategy" PathArguments.none),
                                (PathSegment.mk "Tuple" PathArguments.none)])
                            [
                              (FieldValue.mk
                                []
                                (Member.named "head")
                                false
                                (Expr.path
                                  none
                                  (Path.mk
                                    false
                                    [(PathSegment.mk "sized_head_layout" PathArguments.none)]))),
                              (FieldValue.mk
                                []
                                (Member.named "tail")
                                false
                                (Expr.methodCall
                                  (Expr.path
                                    none
                                    (Path.mk false [(PathSegment.mk "tail_ty" PathArguments.none)]))
                                  "layout"
                                  (some
                                    [
                                      (GenericArgument.type
                                        (Ty.path
                                          none
                                          (Path.mk false [(PathSegment.mk "T" PathArguments.none)])))])
                                  []))]
                            false
                            none))])),
                  (Arm.mk
                    []
                    (Pat.struct
                      none
                      (Path.mk false [(PathSegment.mk "Array" PathArguments.none)])
                      [
                        (FieldPat.mk
                          []
                          (Member.named "elem")
                          true
                          (Pat.ident false false "elem" none)),
                        (FieldPat.mk
                          []
                          (Member.named "count")
                          true
                          (Pat.ident false false "count" none))]
                      false)
                    none
                    (Expr.call
                      (Expr.path none (Path.mk false [(PathSegment.mk "Sized" PathArguments.none)]))
                      [
                        (Expr.binary
                          (Expr.methodCall
                            (Expr.methodCall
                              (Expr.path
                                none
                                (Path.mk false [(PathSegment.mk "elem" PathArguments.none)]))
                              "layout"
                              (some
                                [
                                  (GenericArgument.type
                                    (Ty.path
                                      none
                                      (Path.mk false [(PathSegment.mk "T" PathArguments.none)])))])
                              [])
                            "expect_size"
                            none
                            [(Expr.lit (Lit.str "WF ensures array element is sized"))])
                          BinOp.mul
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "count" PathArguments.none)]))),
                        (Expr.methodCall
                          (Expr.methodCall
                            (Expr.path
                              none
                              (Path.mk false [(PathSegment.mk "elem" PathArguments.none)]))
                            "layout"
                            (some
                              [
                                (GenericArgument.type
                                  (Ty.path
                                    none
                                    (Path.mk false [(PathSegment.mk "T" PathArguments.none)])))])
                            [])
                          "expect_align"
                          none
                          [(Expr.lit (Lit.str "WF ensures array element is sized"))])])),
                  (Arm.mk
                    []
                    (Pat.struct
                      none
                      (Path.mk false [(PathSegment.mk "Slice" PathArguments.none)])
                      [
                        (FieldPat.mk
                          []
                          (Member.named "elem")
                          true
                          (Pat.ident false false "elem" none))]
                      false)
                    none
                    (Expr.call
                      (Expr.path
                        none
                        (Path.mk
                          false
                          [
                            (PathSegment.mk "LayoutStrategy" PathArguments.none),
                            (PathSegment.mk "Slice" PathArguments.none)]))
                      [
                        (Expr.methodCall
                          (Expr.methodCall
                            (Expr.path
                              none
                              (Path.mk false [(PathSegment.mk "elem" PathArguments.none)]))
                            "layout"
                            (some
                              [
                                (GenericArgument.type
                                  (Ty.path
                                    none
                                    (Path.mk false [(PathSegment.mk "T" PathArguments.none)])))])
                            [])
                          "expect_size"
                          none
                          [(Expr.lit (Lit.str "WF ensures slice element is sized"))]),
                        (Expr.methodCall
                          (Expr.methodCall
                            (Expr.path
                              none
                              (Path.mk false [(PathSegment.mk "elem" PathArguments.none)]))
                            "layout"
                            (some
                              [
                                (GenericArgument.type
                                  (Ty.path
                                    none
                                    (Path.mk false [(PathSegment.mk "T" PathArguments.none)])))])
                            [])
                          "expect_align"
                          none
                          [(Expr.lit (Lit.str "WF ensures array element is sized"))])])),
                  (Arm.mk
                    []
                    (Pat.tupleStruct
                      none
                      (Path.mk false [(PathSegment.mk "TraitObject" PathArguments.none)])
                      [(Pat.ident false false "trait_name" none)])
                    none
                    (Expr.call
                      (Expr.path
                        none
                        (Path.mk
                          false
                          [
                            (PathSegment.mk "LayoutStrategy" PathArguments.none),
                            (PathSegment.mk "TraitObject" PathArguments.none)]))
                      [
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "trait_name" PathArguments.none)]))]))])
              false)])),
      (ImplItem.fn
        [
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue " Returns the metadata kind when this type is used as a pointee.")),
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue
              " This matches the meta kind of the layout, but without needing to specify a target."))]
        Visibility.pub
        false
        (Signature.mk
          false
          false
          false
          none
          "meta_kind"
          (Generics.mk [] [])
          [(FnArg.receiver [] false none false none)]
          false
          (some
            (Ty.path none (Path.mk false [(PathSegment.mk "PointerMetaKind" PathArguments.none)]))))
        (Block.mk
          [
            (Stmt.expr
              (Expr.matchExpr
                (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                [
                  (Arm.mk
                    []
                    (Pat.struct
                      none
                      (Path.mk
                        false
                        [
                          (PathSegment.mk "Type" PathArguments.none),
                          (PathSegment.mk "Slice" PathArguments.none)])
                      []
                      true)
                    none
                    (Expr.path
                      none
                      (Path.mk
                        false
                        [
                          (PathSegment.mk "PointerMetaKind" PathArguments.none),
                          (PathSegment.mk "ElementCount" PathArguments.none)]))),
                  (Arm.mk
                    []
                    (Pat.tupleStruct
                      none
                      (Path.mk
                        false
                        [
                          (PathSegment.mk "Type" PathArguments.none),
                          (PathSegment.mk "TraitObject" PathArguments.none)])
                      [(Pat.ident false false "trait_name" none)])
                    none
                    (Expr.call
                      (Expr.path
                        none
                        (Path.mk
                          false
                          [
                            (PathSegment.mk "PointerMetaKind" PathArguments.none),
                            (PathSegment.mk "VTablePointer" PathArguments.none)]))
                      [
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "trait_name" PathArguments.none)]))])),
                  (Arm.mk
                    []
                    (Pat.struct
                      none
                      (Path.mk
                        false
                        [
                          (PathSegment.mk "Type" PathArguments.none),
                          (PathSegment.mk "Tuple" PathArguments.none)])
                      [
                        (FieldPat.mk
                          []
                          (Member.named "unsized_field")
                          true
                          (Pat.ident false false "unsized_field" none))]
                      true)
                    none
                    (Expr.matchExpr
                      (Expr.path
                        none
                        (Path.mk false [(PathSegment.mk "unsized_field" PathArguments.none)]))
                      [
                        (Arm.mk
                          []
                          (Pat.ident false false "None" none)
                          none
                          (Expr.path
                            none
                            (Path.mk
                              false
                              [
                                (PathSegment.mk "PointerMetaKind" PathArguments.none),
                                (PathSegment.mk "None" PathArguments.none)]))),
                        (Arm.mk
                          []
                          (Pat.tupleStruct
                            none
                            (Path.mk false [(PathSegment.mk "Some" PathArguments.none)])
                            [(Pat.ident false false "ty" none)])
                          none
                          (Expr.methodCall
                            (Expr.path
                              none
                              (Path.mk false [(PathSegment.mk "ty" PathArguments.none)]))
                            "meta_kind"
                            none
                            []))])),
                  (Arm.mk
                    []
                    Pat.wild
                    none
                    (Expr.path
                      none
                      (Path.mk
                        false
                        [
                          (PathSegment.mk "PointerMetaKind" PathArguments.none),
                          (PathSegment.mk "None" PathArguments.none)])))])
              false)]))])

/-- `spec/lang/types.md:200` -/
def impl_TupleHeadLayout__capped_tail_align : Item :=
  (Item.impl
    []
    false
    false
    (Generics.mk [] [])
    false
    none
    (Ty.path none (Path.mk false [(PathSegment.mk "TupleHeadLayout" PathArguments.none)]))
    [
      (ImplItem.fn
        [
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue
              " The actual alignment of the tail, considering the packed attribute."))]
        Visibility.inherited
        false
        (Signature.mk
          false
          false
          false
          none
          "capped_tail_align"
          (Generics.mk [] [])
          [
            (FnArg.receiver [] false none false none),
            (FnArg.typed
              []
              (Pat.ident false false "tail_align" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "Align" PathArguments.none)])))]
          false
          (some (Ty.path none (Path.mk false [(PathSegment.mk "Align" PathArguments.none)]))))
        (Block.mk
          [
            (Stmt.expr
              (Expr.matchExpr
                (Expr.field
                  (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                  (Member.named "packed_align"))
                [
                  (Arm.mk
                    []
                    (Pat.tupleStruct
                      none
                      (Path.mk false [(PathSegment.mk "Some" PathArguments.none)])
                      [(Pat.ident false false "packed_align" none)])
                    none
                    (Expr.methodCall
                      (Expr.path
                        none
                        (Path.mk false [(PathSegment.mk "tail_align" PathArguments.none)]))
                      "min"
                      none
                      [
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "packed_align" PathArguments.none)]))])),
                  (Arm.mk
                    []
                    (Pat.ident false false "None" none)
                    none
                    (Expr.path
                      none
                      (Path.mk false [(PathSegment.mk "tail_align" PathArguments.none)])))])
              false)])),
      (ImplItem.fn
        [
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue " Where the tail starts, given the aligment of the tail type."))]
        Visibility.pub
        false
        (Signature.mk
          false
          false
          false
          none
          "tail_offset"
          (Generics.mk [] [])
          [
            (FnArg.receiver [] false none false none),
            (FnArg.typed
              []
              (Pat.ident false false "tail_align" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "Align" PathArguments.none)])))]
          false
          (some (Ty.path none (Path.mk false [(PathSegment.mk "Offset" PathArguments.none)]))))
        (Block.mk
          [
            (Stmt.letStmt
              []
              (Pat.ident false false "capped_tail_align" none)
              (some
                (Expr.methodCall
                  (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                  "capped_tail_align"
                  none
                  [
                    (Expr.path
                      none
                      (Path.mk false [(PathSegment.mk "tail_align" PathArguments.none)]))]))
              none),
            (Stmt.letStmt
              []
              (Pat.ident false false "tail_offset" none)
              (some
                (Expr.methodCall
                  (Expr.field
                    (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                    (Member.named "end"))
                  "align_to"
                  none
                  [
                    (Expr.path
                      none
                      (Path.mk false [(PathSegment.mk "capped_tail_align" PathArguments.none)]))]))
              none),
            (Stmt.expr
              (Expr.path none (Path.mk false [(PathSegment.mk "tail_offset" PathArguments.none)]))
              false)])),
      (ImplItem.fn
        [
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue " The size and alignment of the full tuple, including the tail.")),
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue " Given the size and alignment of the tail type."))]
        Visibility.pub
        false
        (Signature.mk
          false
          false
          false
          none
          "full_size_and_align"
          (Generics.mk [] [])
          [
            (FnArg.receiver [] false none false none),
            (FnArg.typed
              []
              (Pat.ident false false "tail_size" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "Size" PathArguments.none)]))),
            (FnArg.typed
              []
              (Pat.ident false false "tail_align" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "Align" PathArguments.none)])))]
          false
          (some
            (Ty.tuple
              [
                (Ty.path none (Path.mk false [(PathSegment.mk "Size" PathArguments.none)])),
                (Ty.path none (Path.mk false [(PathSegment.mk "Align" PathArguments.none)]))])))
        (Block.mk
          [
            (Stmt.letStmt
              []
              (Pat.ident false false "capped_tail_align" none)
              (some
                (Expr.methodCall
                  (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                  "capped_tail_align"
                  none
                  [
                    (Expr.path
                      none
                      (Path.mk false [(PathSegment.mk "tail_align" PathArguments.none)]))]))
              none),
            (Stmt.letStmt
              []
              (Pat.ident false false "align" none)
              (some
                (Expr.methodCall
                  (Expr.path
                    none
                    (Path.mk false [(PathSegment.mk "capped_tail_align" PathArguments.none)]))
                  "max"
                  none
                  [
                    (Expr.field
                      (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                      (Member.named "align"))]))
              none),
            (Stmt.letStmt
              []
              (Pat.ident false false "tail_offset" none)
              (some
                (Expr.methodCall
                  (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                  "tail_offset"
                  none
                  [
                    (Expr.path
                      none
                      (Path.mk false [(PathSegment.mk "tail_align" PathArguments.none)]))]))
              none),
            (Stmt.letStmt
              []
              (Pat.ident false false "end" none)
              (some
                (Expr.binary
                  (Expr.path
                    none
                    (Path.mk false [(PathSegment.mk "tail_offset" PathArguments.none)]))
                  BinOp.add
                  (Expr.path none (Path.mk false [(PathSegment.mk "tail_size" PathArguments.none)]))))
              none),
            (Stmt.letStmt
              []
              (Pat.ident false false "size" none)
              (some
                (Expr.methodCall
                  (Expr.path none (Path.mk false [(PathSegment.mk "end" PathArguments.none)]))
                  "align_to"
                  none
                  [(Expr.path none (Path.mk false [(PathSegment.mk "align" PathArguments.none)]))]))
              none),
            (Stmt.expr
              (Expr.tuple
                [
                  (Expr.path none (Path.mk false [(PathSegment.mk "size" PathArguments.none)])),
                  (Expr.path none (Path.mk false [(PathSegment.mk "align" PathArguments.none)]))])
              false)])),
      (ImplItem.fn
        [
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue
              " Returns the size and alignment of the tuple when there is no tail."))]
        Visibility.pub
        false
        (Signature.mk
          false
          false
          false
          none
          "head_size_and_align"
          (Generics.mk [] [])
          [(FnArg.receiver [] false none false none)]
          false
          (some
            (Ty.tuple
              [
                (Ty.path none (Path.mk false [(PathSegment.mk "Size" PathArguments.none)])),
                (Ty.path none (Path.mk false [(PathSegment.mk "Align" PathArguments.none)]))])))
        (Block.mk
          [
            (Stmt.expr
              (Expr.tuple
                [
                  (Expr.methodCall
                    (Expr.field
                      (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                      (Member.named "end"))
                    "align_to"
                    none
                    [
                      (Expr.field
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                        (Member.named "align"))]),
                  (Expr.field
                    (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                    (Member.named "align"))])
              false)]))])

/-- `spec/lang/types.md:234` -/
def impl_LayoutStrategy__is_sized : Item :=
  (Item.impl
    []
    false
    false
    (Generics.mk [] [])
    false
    none
    (Ty.path none (Path.mk false [(PathSegment.mk "LayoutStrategy" PathArguments.none)]))
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
          "is_sized"
          (Generics.mk [] [])
          [(FnArg.receiver [] false none false none)]
          false
          (some (Ty.path none (Path.mk false [(PathSegment.mk "bool" PathArguments.none)]))))
        (Block.mk
          [
            (Stmt.expr
              (Expr.macro
                (Macro.mk
                  (Path.mk false [(PathSegment.mk "matches" PathArguments.none)])
                  MacroDelimiter.paren
                  (MacroBody.exprAndPat
                    (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                    (Pat.tupleStruct
                      none
                      (Path.mk
                        false
                        [
                          (PathSegment.mk "LayoutStrategy" PathArguments.none),
                          (PathSegment.mk "Sized" PathArguments.none)])
                      [Pat.rest])
                    none)))
              false)])),
      (ImplItem.fn
        [
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue " Returns the size when the type must be statically sized."))]
        Visibility.pub
        false
        (Signature.mk
          false
          false
          false
          none
          "expect_size"
          (Generics.mk [] [])
          [
            (FnArg.receiver [] false none false none),
            (FnArg.typed
              []
              (Pat.ident false false "msg" none)
              (Ty.reference
                none
                false
                (Ty.path none (Path.mk false [(PathSegment.mk "str" PathArguments.none)]))))]
          false
          (some (Ty.path none (Path.mk false [(PathSegment.mk "Size" PathArguments.none)]))))
        (Block.mk
          [
            (Stmt.expr
              (Expr.matchExpr
                (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                [
                  (Arm.mk
                    []
                    (Pat.tupleStruct
                      none
                      (Path.mk
                        false
                        [
                          (PathSegment.mk "LayoutStrategy" PathArguments.none),
                          (PathSegment.mk "Sized" PathArguments.none)])
                      [(Pat.ident false false "size" none), Pat.wild])
                    none
                    (Expr.path none (Path.mk false [(PathSegment.mk "size" PathArguments.none)]))),
                  (Arm.mk
                    []
                    Pat.wild
                    none
                    (Expr.macro
                      (Macro.mk
                        (Path.mk false [(PathSegment.mk "panic" PathArguments.none)])
                        MacroDelimiter.paren
                        (MacroBody.exprs
                          [(Expr.lit (Lit.str "expect_size called on unsized type: {msg}"))]
                          false))))])
              false)])),
      (ImplItem.fn
        [
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue " Returns the alignment when the type must be statically sized."))]
        Visibility.pub
        false
        (Signature.mk
          false
          false
          false
          none
          "expect_align"
          (Generics.mk [] [])
          [
            (FnArg.receiver [] false none false none),
            (FnArg.typed
              []
              (Pat.ident false false "msg" none)
              (Ty.reference
                none
                false
                (Ty.path none (Path.mk false [(PathSegment.mk "str" PathArguments.none)]))))]
          false
          (some (Ty.path none (Path.mk false [(PathSegment.mk "Align" PathArguments.none)]))))
        (Block.mk
          [
            (Stmt.expr
              (Expr.matchExpr
                (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                [
                  (Arm.mk
                    []
                    (Pat.tupleStruct
                      none
                      (Path.mk
                        false
                        [
                          (PathSegment.mk "LayoutStrategy" PathArguments.none),
                          (PathSegment.mk "Sized" PathArguments.none)])
                      [Pat.wild, (Pat.ident false false "align" none)])
                    none
                    (Expr.path none (Path.mk false [(PathSegment.mk "align" PathArguments.none)]))),
                  (Arm.mk
                    []
                    Pat.wild
                    none
                    (Expr.macro
                      (Macro.mk
                        (Path.mk false [(PathSegment.mk "panic" PathArguments.none)])
                        MacroDelimiter.paren
                        (MacroBody.exprs
                          [(Expr.lit (Lit.str "expect_align called on unsized type: {msg}"))]
                          false))))])
              false)])),
      (ImplItem.fn
        [
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue
              " Computes the dynamic size and alignment, but the caller must provide compatible metadata.")),
          (Attr.mk true "doc" (AttrMeta.nameValue " ")),
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue " The size and align of unsized structs depend on each other,")),
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue " thus we must recursively compute them at the same time."))]
        Visibility.pub
        false
        (Signature.mk
          false
          false
          false
          none
          "compute_size_and_align"
          (Generics.mk [(GenericParam.type [] "Provenance" [] none)] [])
          [
            (FnArg.receiver [] false none false none),
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
                                              [(PathSegment.mk "Provenance" PathArguments.none)])))]))])))]))]))),
            (FnArg.typed
              []
              (Pat.ident false false "vtables" none)
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
                                                [(PathSegment.mk "Provenance" PathArguments.none)])))]))]))]
                            (some
                              (Ty.path
                                none
                                (Path.mk false [(PathSegment.mk "VTable" PathArguments.none)])))))]))]))]
          false
          (some
            (Ty.tuple
              [
                (Ty.path none (Path.mk false [(PathSegment.mk "Size" PathArguments.none)])),
                (Ty.path none (Path.mk false [(PathSegment.mk "Align" PathArguments.none)]))])))
        (Block.mk
          [
            (Stmt.expr
              (Expr.matchExpr
                (Expr.tuple
                  [
                    (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)])),
                    (Expr.path none (Path.mk false [(PathSegment.mk "meta" PathArguments.none)]))])
                [
                  (Arm.mk
                    []
                    (Pat.tuple
                      [
                        (Pat.tupleStruct
                          none
                          (Path.mk
                            false
                            [
                              (PathSegment.mk "LayoutStrategy" PathArguments.none),
                              (PathSegment.mk "Sized" PathArguments.none)])
                          [
                            (Pat.ident false false "size" none),
                            (Pat.ident false false "align" none)]),
                        (Pat.ident false false "None" none)])
                    none
                    (Expr.tuple
                      [
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "size" PathArguments.none)])),
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "align" PathArguments.none)]))])),
                  (Arm.mk
                    []
                    (Pat.tuple
                      [
                        (Pat.tupleStruct
                          none
                          (Path.mk
                            false
                            [
                              (PathSegment.mk "LayoutStrategy" PathArguments.none),
                              (PathSegment.mk "Slice" PathArguments.none)])
                          [
                            (Pat.ident false false "elem_size" none),
                            (Pat.ident false false "align" none)]),
                        (Pat.tupleStruct
                          none
                          (Path.mk false [(PathSegment.mk "Some" PathArguments.none)])
                          [
                            (Pat.tupleStruct
                              none
                              (Path.mk
                                false
                                [
                                  (PathSegment.mk "PointerMeta" PathArguments.none),
                                  (PathSegment.mk "ElementCount" PathArguments.none)])
                              [(Pat.ident false false "count" none)])])])
                    none
                    (Expr.tuple
                      [
                        (Expr.binary
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "count" PathArguments.none)]))
                          BinOp.mul
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "elem_size" PathArguments.none)]))),
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "align" PathArguments.none)]))])),
                  (Arm.mk
                    []
                    (Pat.tuple
                      [
                        (Pat.tupleStruct
                          none
                          (Path.mk
                            false
                            [
                              (PathSegment.mk "LayoutStrategy" PathArguments.none),
                              (PathSegment.mk "TraitObject" PathArguments.none)])
                          [Pat.rest]),
                        (Pat.tupleStruct
                          none
                          (Path.mk false [(PathSegment.mk "Some" PathArguments.none)])
                          [
                            (Pat.tupleStruct
                              none
                              (Path.mk
                                false
                                [
                                  (PathSegment.mk "PointerMeta" PathArguments.none),
                                  (PathSegment.mk "VTablePointer" PathArguments.none)])
                              [(Pat.ident false false "vtable_ptr" none)])])])
                    none
                    (Expr.block
                      none
                      (Block.mk
                        [
                          (Stmt.letStmt
                            []
                            (Pat.ident false false "vtable" none)
                            (some
                              (Expr.call
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "vtables" PathArguments.none)]))
                                [
                                  (Expr.path
                                    none
                                    (Path.mk
                                      false
                                      [(PathSegment.mk "vtable_ptr" PathArguments.none)]))]))
                            none),
                          (Stmt.expr
                            (Expr.tuple
                              [
                                (Expr.field
                                  (Expr.path
                                    none
                                    (Path.mk false [(PathSegment.mk "vtable" PathArguments.none)]))
                                  (Member.named "size")),
                                (Expr.field
                                  (Expr.path
                                    none
                                    (Path.mk false [(PathSegment.mk "vtable" PathArguments.none)]))
                                  (Member.named "align"))])
                            false)]))),
                  (Arm.mk
                    []
                    (Pat.tuple
                      [
                        (Pat.struct
                          none
                          (Path.mk
                            false
                            [
                              (PathSegment.mk "LayoutStrategy" PathArguments.none),
                              (PathSegment.mk "Tuple" PathArguments.none)])
                          [
                            (FieldPat.mk
                              []
                              (Member.named "head")
                              true
                              (Pat.ident false false "head" none)),
                            (FieldPat.mk
                              []
                              (Member.named "tail")
                              true
                              (Pat.ident false false "tail" none))]
                          false),
                        (Pat.tupleStruct
                          none
                          (Path.mk false [(PathSegment.mk "Some" PathArguments.none)])
                          [(Pat.ident false false "meta" none)])])
                    none
                    (Expr.block
                      none
                      (Block.mk
                        [
                          (Stmt.letStmt
                            []
                            (Pat.tuple
                              [
                                (Pat.ident false false "tail_size" none),
                                (Pat.ident false false "tail_align" none)])
                            (some
                              (Expr.methodCall
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "tail" PathArguments.none)]))
                                "compute_size_and_align"
                                none
                                [
                                  (Expr.call
                                    (Expr.path
                                      none
                                      (Path.mk false [(PathSegment.mk "Some" PathArguments.none)]))
                                    [
                                      (Expr.path
                                        none
                                        (Path.mk false [(PathSegment.mk "meta" PathArguments.none)]))]),
                                  (Expr.path
                                    none
                                    (Path.mk false [(PathSegment.mk "vtables" PathArguments.none)]))]))
                            none),
                          (Stmt.expr
                            (Expr.methodCall
                              (Expr.path
                                none
                                (Path.mk false [(PathSegment.mk "head" PathArguments.none)]))
                              "full_size_and_align"
                              none
                              [
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "tail_size" PathArguments.none)])),
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "tail_align" PathArguments.none)]))])
                            false)]))),
                  (Arm.mk
                    []
                    Pat.wild
                    none
                    (Expr.macro
                      (Macro.mk
                        (Path.mk false [(PathSegment.mk "panic" PathArguments.none)])
                        MacroDelimiter.paren
                        (MacroBody.exprs
                          [(Expr.lit (Lit.str "pointer meta data does not match type"))]
                          false))))])
              false)])),
      (ImplItem.fn
        [
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue
              " Returns the metadata kind which is needed to compute this strategy,")),
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue
              " i.e `machine.check_pointer_metadata(meta, self.meta_kind()).is_ok()` implies `machine.compute_*(meta)` is well-defined."))]
        Visibility.pub
        false
        (Signature.mk
          false
          false
          false
          none
          "meta_kind"
          (Generics.mk [] [])
          [(FnArg.receiver [] false none false none)]
          false
          (some
            (Ty.path none (Path.mk false [(PathSegment.mk "PointerMetaKind" PathArguments.none)]))))
        (Block.mk
          [
            (Stmt.expr
              (Expr.matchExpr
                (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                [
                  (Arm.mk
                    []
                    (Pat.tupleStruct
                      none
                      (Path.mk
                        false
                        [
                          (PathSegment.mk "LayoutStrategy" PathArguments.none),
                          (PathSegment.mk "Sized" PathArguments.none)])
                      [Pat.rest])
                    none
                    (Expr.path
                      none
                      (Path.mk
                        false
                        [
                          (PathSegment.mk "PointerMetaKind" PathArguments.none),
                          (PathSegment.mk "None" PathArguments.none)]))),
                  (Arm.mk
                    []
                    (Pat.tupleStruct
                      none
                      (Path.mk
                        false
                        [
                          (PathSegment.mk "LayoutStrategy" PathArguments.none),
                          (PathSegment.mk "Slice" PathArguments.none)])
                      [Pat.rest])
                    none
                    (Expr.path
                      none
                      (Path.mk
                        false
                        [
                          (PathSegment.mk "PointerMetaKind" PathArguments.none),
                          (PathSegment.mk "ElementCount" PathArguments.none)]))),
                  (Arm.mk
                    []
                    (Pat.tupleStruct
                      none
                      (Path.mk
                        false
                        [
                          (PathSegment.mk "LayoutStrategy" PathArguments.none),
                          (PathSegment.mk "TraitObject" PathArguments.none)])
                      [(Pat.ident false false "trait_name" none)])
                    none
                    (Expr.call
                      (Expr.path
                        none
                        (Path.mk
                          false
                          [
                            (PathSegment.mk "PointerMetaKind" PathArguments.none),
                            (PathSegment.mk "VTablePointer" PathArguments.none)]))
                      [
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "trait_name" PathArguments.none)]))])),
                  (Arm.mk
                    []
                    (Pat.struct
                      none
                      (Path.mk
                        false
                        [
                          (PathSegment.mk "LayoutStrategy" PathArguments.none),
                          (PathSegment.mk "Tuple" PathArguments.none)])
                      [
                        (FieldPat.mk
                          []
                          (Member.named "tail")
                          true
                          (Pat.ident false false "tail" none))]
                      true)
                    none
                    (Expr.methodCall
                      (Expr.path none (Path.mk false [(PathSegment.mk "tail" PathArguments.none)]))
                      "meta_kind"
                      none
                      []))])
              false)]))])

/-- `spec/lang/types.md:295` -/
def impl_IntType__I8 : Item :=
  (Item.impl
    []
    false
    false
    (Generics.mk [] [])
    false
    none
    (Ty.path none (Path.mk false [(PathSegment.mk "IntType" PathArguments.none)]))
    [
      (ImplItem.const
        []
        Visibility.pub
        false
        "I8"
        (Generics.mk [] [])
        (Ty.path none (Path.mk false [(PathSegment.mk "IntType" PathArguments.none)]))
        (Expr.struct
          none
          (Path.mk false [(PathSegment.mk "IntType" PathArguments.none)])
          [
            (FieldValue.mk
              []
              (Member.named "signed")
              false
              (Expr.path
                none
                (Path.mk
                  false
                  [
                    (PathSegment.mk "Signedness" PathArguments.none),
                    (PathSegment.mk "Signed" PathArguments.none)]))),
            (FieldValue.mk
              []
              (Member.named "size")
              false
              (Expr.call
                (Expr.path
                  none
                  (Path.mk
                    false
                    [
                      (PathSegment.mk "Size" PathArguments.none),
                      (PathSegment.mk "from_bytes_const" PathArguments.none)]))
                [(Expr.lit (Lit.int 1 ""))]))]
          false
          none)),
      (ImplItem.const
        []
        Visibility.pub
        false
        "I32"
        (Generics.mk [] [])
        (Ty.path none (Path.mk false [(PathSegment.mk "IntType" PathArguments.none)]))
        (Expr.struct
          none
          (Path.mk false [(PathSegment.mk "IntType" PathArguments.none)])
          [
            (FieldValue.mk
              []
              (Member.named "signed")
              false
              (Expr.path
                none
                (Path.mk
                  false
                  [
                    (PathSegment.mk "Signedness" PathArguments.none),
                    (PathSegment.mk "Signed" PathArguments.none)]))),
            (FieldValue.mk
              []
              (Member.named "size")
              false
              (Expr.call
                (Expr.path
                  none
                  (Path.mk
                    false
                    [
                      (PathSegment.mk "Size" PathArguments.none),
                      (PathSegment.mk "from_bytes_const" PathArguments.none)]))
                [(Expr.lit (Lit.int 4 ""))]))]
          false
          none)),
      (ImplItem.fn
        []
        Visibility.pub
        false
        (Signature.mk
          false
          false
          false
          none
          "usize_ty"
          (Generics.mk
            [
              (GenericParam.type
                []
                "T"
                [
                  (TypeParamBound.trait
                    false
                    false
                    []
                    (Path.mk false [(PathSegment.mk "Target" PathArguments.none)]))]
                none)]
            [])
          []
          false
          (some (Ty.path none (Path.mk false [(PathSegment.mk "Self" PathArguments.none)]))))
        (Block.mk
          [
            (Stmt.expr
              (Expr.struct
                none
                (Path.mk false [(PathSegment.mk "IntType" PathArguments.none)])
                [
                  (FieldValue.mk
                    []
                    (Member.named "signed")
                    false
                    (Expr.path
                      none
                      (Path.mk
                        false
                        [
                          (PathSegment.mk "Signedness" PathArguments.none),
                          (PathSegment.mk "Unsigned" PathArguments.none)]))),
                  (FieldValue.mk
                    []
                    (Member.named "size")
                    false
                    (Expr.path
                      none
                      (Path.mk
                        false
                        [
                          (PathSegment.mk "T" PathArguments.none),
                          (PathSegment.mk "PTR_SIZE" PathArguments.none)])))]
                false
                none)
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
          "can_represent"
          (Generics.mk [] [])
          [
            (FnArg.receiver [] true none false none),
            (FnArg.typed
              []
              (Pat.ident false false "i" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "Int" PathArguments.none)])))]
          false
          (some (Ty.path none (Path.mk false [(PathSegment.mk "bool" PathArguments.none)]))))
        (Block.mk
          [
            (Stmt.expr
              (Expr.methodCall
                (Expr.path none (Path.mk false [(PathSegment.mk "i" PathArguments.none)]))
                "in_bounds"
                none
                [
                  (Expr.field
                    (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                    (Member.named "signed")),
                  (Expr.field
                    (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                    (Member.named "size"))])
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
          "bring_in_bounds"
          (Generics.mk [] [])
          [
            (FnArg.receiver [] true none false none),
            (FnArg.typed
              []
              (Pat.ident false false "i" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "Int" PathArguments.none)])))]
          false
          (some (Ty.path none (Path.mk false [(PathSegment.mk "Int" PathArguments.none)]))))
        (Block.mk
          [
            (Stmt.expr
              (Expr.methodCall
                (Expr.path none (Path.mk false [(PathSegment.mk "i" PathArguments.none)]))
                "bring_in_bounds"
                none
                [
                  (Expr.field
                    (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                    (Member.named "signed")),
                  (Expr.field
                    (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                    (Member.named "size"))])
              false)])),
      (ImplItem.fn
        [(Attr.mk true "doc" (AttrMeta.nameValue " Generate the return type for IntWithOverflow"))]
        Visibility.pub
        false
        (Signature.mk
          false
          false
          false
          none
          "with_overflow"
          (Generics.mk
            [
              (GenericParam.type
                []
                "T"
                [
                  (TypeParamBound.trait
                    false
                    false
                    []
                    (Path.mk false [(PathSegment.mk "Target" PathArguments.none)]))]
                none)]
            [])
          [(FnArg.receiver [] true none false none)]
          false
          (some (Ty.path none (Path.mk false [(PathSegment.mk "Type" PathArguments.none)]))))
        (Block.mk
          [
            (Stmt.letStmt
              []
              (Pat.ident false false "fields" none)
              (some
                (Expr.macro
                  (Macro.mk
                    (Path.mk false [(PathSegment.mk "list" PathArguments.none)])
                    MacroDelimiter.bracket
                    (MacroBody.exprs
                      [
                        (Expr.tuple
                          [
                            (Expr.path
                              none
                              (Path.mk
                                false
                                [
                                  (PathSegment.mk "Size" PathArguments.none),
                                  (PathSegment.mk "ZERO" PathArguments.none)])),
                            (Expr.call
                              (Expr.path
                                none
                                (Path.mk
                                  false
                                  [
                                    (PathSegment.mk "Type" PathArguments.none),
                                    (PathSegment.mk "Int" PathArguments.none)]))
                              [
                                (Expr.unary
                                  UnOp.deref
                                  (Expr.path
                                    none
                                    (Path.mk false [(PathSegment.mk "self" PathArguments.none)])))])]),
                        (Expr.tuple
                          [
                            (Expr.field
                              (Expr.path
                                none
                                (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                              (Member.named "size")),
                            (Expr.path
                              none
                              (Path.mk
                                false
                                [
                                  (PathSegment.mk "Type" PathArguments.none),
                                  (PathSegment.mk "Bool" PathArguments.none)]))])]
                      false))))
              none),
            (Stmt.letStmt
              []
              (Pat.ident false false "align" none)
              (some
                (Expr.methodCall
                  (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                  "align"
                  (some
                    [
                      (GenericArgument.type
                        (Ty.path none (Path.mk false [(PathSegment.mk "T" PathArguments.none)])))])
                  []))
              none),
            (Stmt.letStmt
              []
              (Pat.ident false false "size" none)
              (some
                (Expr.binary
                  (Expr.field
                    (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                    (Member.named "size"))
                  BinOp.add
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
                            (Path.mk false [(PathSegment.mk "align" PathArguments.none)]))
                          "bytes"
                          none
                          [])])
                    "unwrap"
                    none
                    [])))
              none),
            (Stmt.expr
              (Expr.struct
                none
                (Path.mk
                  false
                  [
                    (PathSegment.mk "Type" PathArguments.none),
                    (PathSegment.mk "Tuple" PathArguments.none)])
                [
                  (FieldValue.mk
                    []
                    (Member.named "sized_fields")
                    false
                    (Expr.path none (Path.mk false [(PathSegment.mk "fields" PathArguments.none)]))),
                  (FieldValue.mk
                    []
                    (Member.named "sized_head_layout")
                    false
                    (Expr.struct
                      none
                      (Path.mk false [(PathSegment.mk "TupleHeadLayout" PathArguments.none)])
                      [
                        (FieldValue.mk
                          []
                          (Member.named "end")
                          false
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "size" PathArguments.none)]))),
                        (FieldValue.mk
                          []
                          (Member.named "align")
                          true
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "align" PathArguments.none)]))),
                        (FieldValue.mk
                          []
                          (Member.named "packed_align")
                          false
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "None" PathArguments.none)])))]
                      false
                      none)),
                  (FieldValue.mk
                    []
                    (Member.named "unsized_field")
                    false
                    (Expr.path none (Path.mk false [(PathSegment.mk "None" PathArguments.none)])))]
                false
                none)
              false)]))])

/-- `spec/lang/types.md:336` -/
def fn_unit_ty : Item :=
  (Item.fn
    [
      (Attr.mk
        true
        "doc"
        (AttrMeta.nameValue " Returns the type of a zero-sized, one aligned-tuple."))]
    Visibility.pub
    (Signature.mk
      false
      false
      false
      none
      "unit_ty"
      (Generics.mk [] [])
      []
      false
      (some (Ty.path none (Path.mk false [(PathSegment.mk "Type" PathArguments.none)]))))
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
                  (Expr.call
                    (Expr.path
                      (some
                        (QSelf.mk
                          (Ty.path none (Path.mk false [(PathSegment.mk "i32" PathArguments.none)]))
                          1
                          true))
                      (Path.mk
                        false
                        [
                          (PathSegment.mk
                            "Into"
                            (PathArguments.angleBracketed
                              false
                              [
                                (GenericArgument.type
                                  (Ty.path
                                    none
                                    (Path.mk false [(PathSegment.mk "Int" PathArguments.none)])))])),
                          (PathSegment.mk "into" PathArguments.none)]))
                    [(Expr.lit (Lit.int 0 ""))])])
              "unwrap"
              none
              []))
          none),
        (Stmt.letStmt
          []
          (Pat.ident false false "align" none)
          (some
            (Expr.methodCall
              (Expr.call
                (Expr.path
                  none
                  (Path.mk
                    false
                    [
                      (PathSegment.mk "Align" PathArguments.none),
                      (PathSegment.mk "from_bytes" PathArguments.none)]))
                [
                  (Expr.call
                    (Expr.path
                      (some
                        (QSelf.mk
                          (Ty.path none (Path.mk false [(PathSegment.mk "i32" PathArguments.none)]))
                          1
                          true))
                      (Path.mk
                        false
                        [
                          (PathSegment.mk
                            "Into"
                            (PathArguments.angleBracketed
                              false
                              [
                                (GenericArgument.type
                                  (Ty.path
                                    none
                                    (Path.mk false [(PathSegment.mk "Int" PathArguments.none)])))])),
                          (PathSegment.mk "into" PathArguments.none)]))
                    [(Expr.lit (Lit.int 1 ""))])])
              "unwrap"
              none
              []))
          none),
        (Stmt.expr
          (Expr.struct
            none
            (Path.mk
              false
              [
                (PathSegment.mk "Type" PathArguments.none),
                (PathSegment.mk "Tuple" PathArguments.none)])
            [
              (FieldValue.mk
                []
                (Member.named "sized_fields")
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
                (Member.named "sized_head_layout")
                false
                (Expr.struct
                  none
                  (Path.mk false [(PathSegment.mk "TupleHeadLayout" PathArguments.none)])
                  [
                    (FieldValue.mk
                      []
                      (Member.named "end")
                      false
                      (Expr.path none (Path.mk false [(PathSegment.mk "size" PathArguments.none)]))),
                    (FieldValue.mk
                      []
                      (Member.named "align")
                      true
                      (Expr.path none (Path.mk false [(PathSegment.mk "align" PathArguments.none)]))),
                    (FieldValue.mk
                      []
                      (Member.named "packed_align")
                      false
                      (Expr.path none (Path.mk false [(PathSegment.mk "None" PathArguments.none)])))]
                  false
                  none)),
              (FieldValue.mk
                []
                (Member.named "unsized_field")
                false
                (Expr.path none (Path.mk false [(PathSegment.mk "None" PathArguments.none)])))]
            false
            none)
          false)]))

/-- All items of `spec/lang/types.md`, in source order, with provenance. -/
def items : List SourceItem :=
  [
    (SourceItem.mk
      "enum_Type"
      20
      "504eb0fc9f4accd057cc9a0334dd4696ed1500d1cc60daff136ad958c9cc1dc1"
      enum_Type),
    (SourceItem.mk
      "struct_IntType"
      94
      "b96f26e10803e17f17079add1e85dacc7e010d2d22fa624199af68ed55ce78db"
      struct_IntType),
    (SourceItem.mk
      "type_Fields"
      99
      "e065dfae5252c2996f64c656225a104d82883e0c511619c02e6d7e338b60cc6c"
      type_Fields),
    (SourceItem.mk
      "struct_Variant"
      101
      "29afb4e06af9680e9f284f8ffaf8ed39b122d7e7d7137986294bbeba04f10cff"
      struct_Variant),
    (SourceItem.mk
      "enum_Discriminator"
      111
      "4c4a690227a37fcc41bdb9842805b43399a822da5d6def8c8970548a7874c462"
      enum_Discriminator),
    (SourceItem.mk
      "impl_IntType__align"
      138
      "7fe63ee221d67adfee70c4048a1ec290c95d557d77cc0c8bbec2df68ce95041a"
      impl_IntType__align),
    (SourceItem.mk
      "impl_Type__layout"
      148
      "682e0cbfbea24b480557a76f0b8f41b2d286f604a8f6d0b26df81a02fa15cfcd"
      impl_Type__layout),
    (SourceItem.mk
      "impl_TupleHeadLayout__capped_tail_align"
      200
      "b4ae4d20f48c251605379a6d0cb0900922148640cc382899ca7c07957ae94c93"
      impl_TupleHeadLayout__capped_tail_align),
    (SourceItem.mk
      "impl_LayoutStrategy__is_sized"
      234
      "e52080897bef565d064ef299545ac4985b3364e30fb6076be23e24827dbd9bd5"
      impl_LayoutStrategy__is_sized),
    (SourceItem.mk
      "impl_IntType__I8"
      295
      "b0754c0840f7498f21559e09fe5421930c3eaccebff1f87a53ca8e6fc457db66"
      impl_IntType__I8),
    (SourceItem.mk
      "fn_unit_ty"
      336
      "13dd0e23498a3c0c40e2e9ea8f079f2b81c0b01afb88c1e76d516dbebec527c1"
      fn_unit_ty)]

end MiniRustSpec.Gen.Items.Lang.Types
