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
`spec/prelude/target.md` (commit `d821c6e3`), one Lean definition per item, in source order.
-/

import MiniRustSpec.Meta.Syntax

set_option maxRecDepth 100000

namespace MiniRustSpec.Gen.Items.Prelude.Target

open MiniRustSpec.Syntax

/-- Path of the upstream file these items were extracted from. -/
def sourceFile : String := "spec/prelude/target.md"

/-- SHA-256 of the upstream file. -/
def sourceSha256 : String := "28cb80649c97776490cc321c130de53ea12e4dd132043199eadf3b2a6f6cb3f4"

/-- `spec/prelude/target.md:9` -/
def trait_Target : Item :=
  (Item.trait
    []
    Visibility.pub
    false
    false
    "Target"
    (Generics.mk [] [])
    []
    [
      (TraitItem.const
        [(Attr.mk true "doc" (AttrMeta.nameValue " The size and align of a pointer."))]
        "PTR_SIZE"
        (Generics.mk [] [])
        (Ty.path none (Path.mk false [(PathSegment.mk "Size" PathArguments.none)]))
        none),
      (TraitItem.const
        []
        "PTR_ALIGN"
        (Generics.mk [] [])
        (Ty.path none (Path.mk false [(PathSegment.mk "Align" PathArguments.none)]))
        none),
      (TraitItem.const
        [
          (Attr.mk true "doc" (AttrMeta.nameValue " The maximum alignment of integer types.")),
          (Attr.mk true "doc" (AttrMeta.nameValue " Smaller types are aligned to their size."))]
        "INT_MAX_ALIGN"
        (Generics.mk [] [])
        (Ty.path none (Path.mk false [(PathSegment.mk "Align" PathArguments.none)]))
        none),
      (TraitItem.const
        [
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue
              " The endianess used for encoding multi-byte integer values (and pointers)."))]
        "ENDIANNESS"
        (Generics.mk [] [])
        (Ty.path none (Path.mk false [(PathSegment.mk "Endianness" PathArguments.none)]))
        none),
      (TraitItem.const
        [(Attr.mk true "doc" (AttrMeta.nameValue " Maximum size of an atomic operation."))]
        "MAX_ATOMIC_SIZE"
        (Generics.mk [] [])
        (Ty.path none (Path.mk false [(PathSegment.mk "Size" PathArguments.none)]))
        none),
      (TraitItem.fn
        [
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue " Checks that `size` is not too large for this target."))]
        (Signature.mk
          false
          false
          false
          none
          "valid_size"
          (Generics.mk [] [])
          [
            (FnArg.typed
              []
              (Pat.ident false false "size" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "Size" PathArguments.none)])))]
          false
          (some (Ty.path none (Path.mk false [(PathSegment.mk "bool" PathArguments.none)]))))
        none)])

/-- `spec/prelude/target.md:32` -/
def struct_x86_64 : Item :=
  (Item.struct
    [(Attr.mk true "allow" (AttrMeta.list [(MetaItem.mk "non_camel_case_types" AttrMeta.path)]))]
    Visibility.pub
    "x86_64"
    (Generics.mk [] [])
    Fields.unit)

/-- `spec/prelude/target.md:35` -/
def impl_x86_64_for_Target__PTR_SIZE : Item :=
  (Item.impl
    []
    false
    false
    (Generics.mk [] [])
    false
    (some (Path.mk false [(PathSegment.mk "Target" PathArguments.none)]))
    (Ty.path none (Path.mk false [(PathSegment.mk "x86_64" PathArguments.none)]))
    [
      (ImplItem.const
        []
        Visibility.inherited
        false
        "PTR_SIZE"
        (Generics.mk [] [])
        (Ty.path none (Path.mk false [(PathSegment.mk "Size" PathArguments.none)]))
        (Expr.methodCall
          (Expr.call
            (Expr.path
              none
              (Path.mk
                false
                [
                  (PathSegment.mk "Size" PathArguments.none),
                  (PathSegment.mk "from_bits_const" PathArguments.none)]))
            [(Expr.lit (Lit.int 64 ""))])
          "unwrap"
          none
          [])),
      (ImplItem.const
        []
        Visibility.inherited
        false
        "PTR_ALIGN"
        (Generics.mk [] [])
        (Ty.path none (Path.mk false [(PathSegment.mk "Align" PathArguments.none)]))
        (Expr.methodCall
          (Expr.call
            (Expr.path
              none
              (Path.mk
                false
                [
                  (PathSegment.mk "Align" PathArguments.none),
                  (PathSegment.mk "from_bits_const" PathArguments.none)]))
            [(Expr.lit (Lit.int 64 ""))])
          "unwrap"
          none
          [])),
      (ImplItem.const
        []
        Visibility.inherited
        false
        "INT_MAX_ALIGN"
        (Generics.mk [] [])
        (Ty.path none (Path.mk false [(PathSegment.mk "Align" PathArguments.none)]))
        (Expr.methodCall
          (Expr.call
            (Expr.path
              none
              (Path.mk
                false
                [
                  (PathSegment.mk "Align" PathArguments.none),
                  (PathSegment.mk "from_bits_const" PathArguments.none)]))
            [(Expr.lit (Lit.int 128 ""))])
          "unwrap"
          none
          [])),
      (ImplItem.const
        []
        Visibility.inherited
        false
        "ENDIANNESS"
        (Generics.mk [] [])
        (Ty.path none (Path.mk false [(PathSegment.mk "Endianness" PathArguments.none)]))
        (Expr.path none (Path.mk false [(PathSegment.mk "LittleEndian" PathArguments.none)]))),
      (ImplItem.const
        []
        Visibility.inherited
        false
        "MAX_ATOMIC_SIZE"
        (Generics.mk [] [])
        (Ty.path none (Path.mk false [(PathSegment.mk "Size" PathArguments.none)]))
        (Expr.methodCall
          (Expr.call
            (Expr.path
              none
              (Path.mk
                false
                [
                  (PathSegment.mk "Size" PathArguments.none),
                  (PathSegment.mk "from_bits_const" PathArguments.none)]))
            [(Expr.lit (Lit.int 64 ""))])
          "unwrap"
          none
          [])),
      (ImplItem.fn
        []
        Visibility.inherited
        false
        (Signature.mk
          false
          false
          false
          none
          "valid_size"
          (Generics.mk [] [])
          [
            (FnArg.typed
              []
              (Pat.ident false false "size" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "Size" PathArguments.none)])))]
          false
          (some (Ty.path none (Path.mk false [(PathSegment.mk "bool" PathArguments.none)]))))
        (Block.mk
          [
            (Stmt.expr
              (Expr.methodCall
                (Expr.methodCall
                  (Expr.path none (Path.mk false [(PathSegment.mk "size" PathArguments.none)]))
                  "bytes"
                  none
                  [])
                "in_bounds"
                none
                [
                  (Expr.path none (Path.mk false [(PathSegment.mk "Signed" PathArguments.none)])),
                  (Expr.path
                    none
                    (Path.mk
                      false
                      [
                        (PathSegment.mk "Self" PathArguments.none),
                        (PathSegment.mk "PTR_SIZE" PathArguments.none)]))])
              false)]))])

/-- All items of `spec/prelude/target.md`, in source order, with provenance. -/
def items : List SourceItem :=
  [
    (SourceItem.mk
      "trait_Target"
      9
      "e6a5df64ac3671d924869684b52d8028157e84ced20eb94a621a84331dfb0596"
      trait_Target),
    (SourceItem.mk
      "struct_x86_64"
      32
      "eeed28eeb2694653f8919aa7f486a03c52f1e524ac12e3a5fc4cfed3e6371b99"
      struct_x86_64),
    (SourceItem.mk
      "impl_x86_64_for_Target__PTR_SIZE"
      35
      "af4c702eb751ff89569e4676de009743cced5aaf60295c0964b8bf2567e7ef3d"
      impl_x86_64_for_Target__PTR_SIZE)]

end MiniRustSpec.Gen.Items.Prelude.Target
