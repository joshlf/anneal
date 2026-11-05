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
`spec/lang/values.md` (commit `d821c6e3`), one Lean definition per item, in source order.
-/

import MiniRustSpec.Meta.Syntax

set_option maxRecDepth 100000

namespace MiniRustSpec.Gen.Items.Lang.Values

open MiniRustSpec.Syntax

/-- Path of the upstream file these items were extracted from. -/
def sourceFile : String := "spec/lang/values.md"

/-- SHA-256 of the upstream file. -/
def sourceSha256 : String := "06cd9f8f0fab58a0d5ff29c1ba25b41a2315d2db1a8413973d95e0f1cb96575d"

/-- `spec/lang/values.md:7` -/
def enum_Value : Item :=
  (Item.enum
    []
    Visibility.inherited
    "Value"
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
            (AttrMeta.nameValue " A mathematical integer, used for `i*`/`u*` types."))]
        "Int"
        (Fields.unnamed
          [
            (Field.mk
              []
              Visibility.inherited
              none
              (Ty.path none (Path.mk false [(PathSegment.mk "Int" PathArguments.none)])))])
        none),
      (Variant.mk
        [(Attr.mk true "doc" (AttrMeta.nameValue " A Boolean value, used for `bool`."))]
        "Bool"
        (Fields.unnamed
          [
            (Field.mk
              []
              Visibility.inherited
              none
              (Ty.path none (Path.mk false [(PathSegment.mk "bool" PathArguments.none)])))])
        none),
      (Variant.mk
        [
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue " A pointer value, used for references and raw pointers."))]
        "Ptr"
        (Fields.unnamed
          [
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
                                  (PathSegment.mk "Provenance" PathArguments.none)])))]))])))])
        none),
      (Variant.mk
        [
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue " An n-tuple, used for arrays, structs, tuples (including unit)."))]
        "Tuple"
        (Fields.unnamed
          [
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
                                    "Value"
                                    (PathArguments.angleBracketed
                                      false
                                      [
                                        (GenericArgument.type
                                          (Ty.path
                                            none
                                            (Path.mk
                                              false
                                              [(PathSegment.mk "M" PathArguments.none)])))]))])))]))])))])
        none),
      (Variant.mk
        [(Attr.mk true "doc" (AttrMeta.nameValue " A variant of a sum type, used for enums."))]
        "Variant"
        (Fields.named
          [
            (Field.mk
              []
              Visibility.inherited
              (some "discriminant")
              (Ty.path none (Path.mk false [(PathSegment.mk "Int" PathArguments.none)]))),
            (Field.mk
              [(Attr.mk true "specr::indirection" AttrMeta.path)]
              Visibility.inherited
              (some "data")
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
                            (Ty.path none (Path.mk false [(PathSegment.mk "M" PathArguments.none)])))]))])))])
        none),
      (Variant.mk
        [
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue
              " Unions are represented as \"lists of chunks\", where each chunk is just a raw list of bytes."))]
        "Union"
        (Fields.unnamed
          [
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
                                                                "M"
                                                                PathArguments.none),
                                                              (PathSegment.mk
                                                                "Provenance"
                                                                PathArguments.none)])))]))])))]))])))]))])))])
        none)])

/-- `spec/lang/values.md:35` -/
def struct_Place : Item :=
  (Item.struct
    []
    Visibility.inherited
    "Place"
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
          (some "ptr")
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
        (Field.mk
          []
          Visibility.inherited
          (some "aligned")
          (Ty.path none (Path.mk false [(PathSegment.mk "bool" PathArguments.none)])))]))

/-- All items of `spec/lang/values.md`, in source order, with provenance. -/
def items : List SourceItem :=
  [
    (SourceItem.mk
      "enum_Value"
      7
      "5953fafd95a1b8df15e7f598ee2fc02c1e5940ea67ab09e160d31102d6641e0a"
      enum_Value),
    (SourceItem.mk
      "struct_Place"
      35
      "c5f8c90f29b28fe676030dc8264e5d6550c37c0048e0369856dce3db72042fdb"
      struct_Place)]

end MiniRustSpec.Gen.Items.Lang.Values
