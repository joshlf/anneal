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
`spec/mem/pointer.md` (commit `d821c6e3`), one Lean definition per item, in source order.
-/

import MiniRustSpec.Meta.Syntax

set_option maxRecDepth 100000

namespace MiniRustSpec.Gen.Items.Mem.Pointer

open MiniRustSpec.Syntax

/-- Path of the upstream file these items were extracted from. -/
def sourceFile : String := "spec/mem/pointer.md"

/-- SHA-256 of the upstream file. -/
def sourceSha256 : String := "1eb963e5ef08052ba5947bb78debc8356fb91a6fef457247821ddb52f66d87b7"

/-- `spec/mem/pointer.md:22` -/
def type_Address : Item :=
  (Item.type
    [
      (Attr.mk
        true
        "doc"
        (AttrMeta.nameValue
          " An \"address\" is a location in memory. This corresponds to the actual")),
      (Attr.mk true "doc" (AttrMeta.nameValue " location in the real program.")),
      (Attr.mk
        true
        "doc"
        (AttrMeta.nameValue
          " We make it a mathematical integer, but of course it is bounded by the size")),
      (Attr.mk true "doc" (AttrMeta.nameValue " of the address space."))]
    Visibility.pub
    "Address"
    (Generics.mk [] [])
    (Ty.path none (Path.mk false [(PathSegment.mk "Int" PathArguments.none)])))

/-- `spec/mem/pointer.md:28` -/
def struct_ThinPointer : Item :=
  (Item.struct
    [
      (Attr.mk
        true
        "doc"
        (AttrMeta.nameValue " A \"thin pointer\" is an address together with its Provenance.")),
      (Attr.mk true "doc" (AttrMeta.nameValue " Provenance can be absent; those pointers are")),
      (Attr.mk true "doc" (AttrMeta.nameValue " invalid for all non-zero-sized accesses."))]
    Visibility.pub
    "ThinPointer"
    (Generics.mk [(GenericParam.type [] "Provenance" [] none)] [])
    (Fields.named
      [
        (Field.mk
          []
          Visibility.pub
          (some "addr")
          (Ty.path none (Path.mk false [(PathSegment.mk "Address" PathArguments.none)]))),
        (Field.mk
          []
          Visibility.pub
          (some "provenance")
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
                          (Path.mk false [(PathSegment.mk "Provenance" PathArguments.none)])))]))])))]))

/-- `spec/mem/pointer.md:36` -/
def enum_PointerMeta : Item :=
  (Item.enum
    [
      (Attr.mk
        true
        "doc"
        (AttrMeta.nameValue " The runtime metadata that can be stored in a wide pointer."))]
    Visibility.pub
    "PointerMeta"
    (Generics.mk [(GenericParam.type [] "Provenance" [] none)] [])
    [
      (Variant.mk
        [
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue " The metadata counts the number of elements in the slice."))]
        "ElementCount"
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
            (AttrMeta.nameValue " The metadata points to a vtable referred at this location.")),
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue
              " This must point to a valid vtable and it is a spec bug if it doesn't."))]
        "VTablePointer"
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
                      "ThinPointer"
                      (PathArguments.angleBracketed
                        false
                        [
                          (GenericArgument.type
                            (Ty.path
                              none
                              (Path.mk false [(PathSegment.mk "Provenance" PathArguments.none)])))]))])))])
        none)])

/-- `spec/mem/pointer.md:45` -/
def struct_Pointer : Item :=
  (Item.struct
    [
      (Attr.mk
        true
        "doc"
        (AttrMeta.nameValue
          " A \"pointer\" is the thin pointer with optionally some metadata, making it a wide pointer.")),
      (Attr.mk
        true
        "doc"
        (AttrMeta.nameValue
          " This corresponds to the Rust raw pointer types, as well as references and boxes."))]
    Visibility.pub
    "Pointer"
    (Generics.mk [(GenericParam.type [] "Provenance" [] none)] [])
    (Fields.named
      [
        (Field.mk
          []
          Visibility.pub
          (some "thin_pointer")
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
                          (Path.mk false [(PathSegment.mk "Provenance" PathArguments.none)])))]))]))),
        (Field.mk
          []
          Visibility.pub
          (some "metadata")
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
                                          [(PathSegment.mk "Provenance" PathArguments.none)])))]))])))]))])))]))

/-- `spec/mem/pointer.md:52` -/
def impl_ThinPointer__wrapping_offset : Item :=
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
            "ThinPointer"
            (PathArguments.angleBracketed
              false
              [
                (GenericArgument.type
                  (Ty.path none (Path.mk false [(PathSegment.mk "Provenance" PathArguments.none)])))]))]))
    [
      (ImplItem.fn
        [
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue " Offsets a pointer in bytes using wrapping arithmetic.")),
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue
              " This does not check whether the pointer is still in-bounds of its allocation."))]
        Visibility.pub
        false
        (Signature.mk
          false
          false
          false
          none
          "wrapping_offset"
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
          [
            (FnArg.receiver [] false none false none),
            (FnArg.typed
              []
              (Pat.ident false false "offset" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "Int" PathArguments.none)])))]
          false
          (some (Ty.path none (Path.mk false [(PathSegment.mk "Self" PathArguments.none)]))))
        (Block.mk
          [
            (Stmt.letStmt
              []
              (Pat.ident false false "addr" none)
              (some
                (Expr.binary
                  (Expr.field
                    (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                    (Member.named "addr"))
                  BinOp.add
                  (Expr.path none (Path.mk false [(PathSegment.mk "offset" PathArguments.none)]))))
              none),
            (Stmt.letStmt
              []
              (Pat.ident false false "addr" none)
              (some
                (Expr.methodCall
                  (Expr.path none (Path.mk false [(PathSegment.mk "addr" PathArguments.none)]))
                  "bring_in_bounds"
                  none
                  [
                    (Expr.path
                      none
                      (Path.mk false [(PathSegment.mk "Unsigned" PathArguments.none)])),
                    (Expr.path
                      none
                      (Path.mk
                        false
                        [
                          (PathSegment.mk "T" PathArguments.none),
                          (PathSegment.mk "PTR_SIZE" PathArguments.none)]))]))
              none),
            (Stmt.expr
              (Expr.struct
                none
                (Path.mk false [(PathSegment.mk "ThinPointer" PathArguments.none)])
                [
                  (FieldValue.mk
                    []
                    (Member.named "addr")
                    true
                    (Expr.path none (Path.mk false [(PathSegment.mk "addr" PathArguments.none)])))]
                true
                (some (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))))
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
          "widen"
          (Generics.mk [] [])
          [
            (FnArg.receiver [] false none false none),
            (FnArg.typed
              []
              (Pat.ident false false "metadata" none)
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
                                              [(PathSegment.mk "Provenance" PathArguments.none)])))]))])))]))])))]
          false
          (some
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
                            (Path.mk false [(PathSegment.mk "Provenance" PathArguments.none)])))]))]))))
        (Block.mk
          [
            (Stmt.expr
              (Expr.struct
                none
                (Path.mk false [(PathSegment.mk "Pointer" PathArguments.none)])
                [
                  (FieldValue.mk
                    []
                    (Member.named "thin_pointer")
                    false
                    (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))),
                  (FieldValue.mk
                    []
                    (Member.named "metadata")
                    true
                    (Expr.path
                      none
                      (Path.mk false [(PathSegment.mk "metadata" PathArguments.none)])))]
                false
                none)
              false)]))])

/-- `spec/mem/pointer.md:77` -/
def struct_TupleHeadLayout : Item :=
  (Item.struct
    [
      (Attr.mk
        true
        "doc"
        (AttrMeta.nameValue
          " Describes what is needed to define the layout of the sized head of a tuple `(head.., tail)`."))]
    Visibility.pub
    "TupleHeadLayout"
    (Generics.mk [] [])
    (Fields.named
      [
        (Field.mk
          [
            (Attr.mk
              true
              "doc"
              (AttrMeta.nameValue " The offset where the head ends and tail starts.")),
            (Attr.mk
              true
              "doc"
              (AttrMeta.nameValue
                " This is the end of the last sized field; it is *not* necessarily aligned to `align`."))]
          Visibility.pub
          (some "end")
          (Ty.path none (Path.mk false [(PathSegment.mk "Offset" PathArguments.none)]))),
        (Field.mk
          [
            (Attr.mk
              true
              "doc"
              (AttrMeta.nameValue
                " The alignment of the head. This is the maximal alignment of any sized field and capped to the packed alignment."))]
          Visibility.pub
          (some "align")
          (Ty.path none (Path.mk false [(PathSegment.mk "Align" PathArguments.none)]))),
        (Field.mk
          [
            (Attr.mk
              true
              "doc"
              (AttrMeta.nameValue
                " If this is `Some(a)` the alignment of the tail will be capped at this value.")),
            (Attr.mk true "doc" (AttrMeta.nameValue " Must be `None` for sized tuples."))]
          Visibility.pub
          (some "packed_align")
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
                        (Ty.path none (Path.mk false [(PathSegment.mk "Align" PathArguments.none)])))]))])))]))

/-- `spec/mem/pointer.md:91` -/
def enum_LayoutStrategy : Item :=
  (Item.enum
    [
      (Attr.mk
        true
        "doc"
        (AttrMeta.nameValue " Describes how the size and align of the value can be determined."))]
    Visibility.pub
    "LayoutStrategy"
    (Generics.mk [] [])
    [
      (Variant.mk
        [
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue " The type is statically `Sized` with the given size and align."))]
        "Sized"
        (Fields.unnamed
          [
            (Field.mk
              []
              Visibility.inherited
              none
              (Ty.path none (Path.mk false [(PathSegment.mk "Size" PathArguments.none)]))),
            (Field.mk
              []
              Visibility.inherited
              none
              (Ty.path none (Path.mk false [(PathSegment.mk "Align" PathArguments.none)])))])
        none),
      (Variant.mk
        [
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue " The type contains zero or more elements of the inner layout.")),
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue
              " The total size is a multiple of the element size and the align is exactly the element align."))]
        "Slice"
        (Fields.unnamed
          [
            (Field.mk
              []
              Visibility.inherited
              none
              (Ty.path none (Path.mk false [(PathSegment.mk "Size" PathArguments.none)]))),
            (Field.mk
              []
              Visibility.inherited
              none
              (Ty.path none (Path.mk false [(PathSegment.mk "Align" PathArguments.none)])))])
        none),
      (Variant.mk
        [
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue
              " The size of the type must be looked up in the VTable of a wide pointer.")),
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue " Additionally, the vtable must be for the given trait."))]
        "TraitObject"
        (Fields.unnamed
          [
            (Field.mk
              []
              Visibility.inherited
              none
              (Ty.path none (Path.mk false [(PathSegment.mk "TraitName" PathArguments.none)])))])
        none),
      (Variant.mk
        [
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue " The type consists of a sized head an unsized tail."))]
        "Tuple"
        (Fields.named
          [
            (Field.mk
              []
              Visibility.inherited
              (some "head")
              (Ty.path none (Path.mk false [(PathSegment.mk "TupleHeadLayout" PathArguments.none)]))),
            (Field.mk
              [(Attr.mk true "specr::indirection" AttrMeta.path)]
              Visibility.inherited
              (some "tail")
              (Ty.path none (Path.mk false [(PathSegment.mk "LayoutStrategy" PathArguments.none)])))])
        none)])

/-- `spec/mem/pointer.md:109` -/
def enum_UnsafeCellStrategy : Item :=
  (Item.enum
    [
      (Attr.mk
        true
        "doc"
        (AttrMeta.nameValue " Describes where in a potentially unsized type the UnsafeCell are.")),
      (Attr.mk
        true
        "doc"
        (AttrMeta.nameValue
          " Separate from `LayoutStrategy` since we must be able to compute `LayoutStrategy` from a")),
      (Attr.mk
        true
        "doc"
        (AttrMeta.nameValue
          " MiniRust `Type`, but that does not have enough information for an `UnsafeCellStrategy`.")),
      (Attr.mk true "doc" (AttrMeta.nameValue " FIXME: maybe it should?"))]
    Visibility.pub
    "UnsafeCellStrategy"
    (Generics.mk [] [])
    [
      (Variant.mk
        [(Attr.mk true "doc" (AttrMeta.nameValue " List of offsets and sizes of `UnsafeCell`s."))]
        "Sized"
        (Fields.named
          [
            (Field.mk
              []
              Visibility.inherited
              (some "cells")
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
                                  (Path.mk false [(PathSegment.mk "Size" PathArguments.none)]))]))]))])))])
        none),
      (Variant.mk
        [
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue
              " Since the elements of a slice have the same type, we only keep track of the")),
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue
              " UnsafeCell's of one element, we can then \"repeat\" this for the rest of the slice."))]
        "Slice"
        (Fields.named
          [
            (Field.mk
              []
              Visibility.inherited
              (some "element_cells")
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
                                  (Path.mk false [(PathSegment.mk "Size" PathArguments.none)]))]))]))])))])
        none),
      (Variant.mk
        [
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue " The bytes for UnsafeCell's must be looked up in the VTable."))]
        "TraitObject"
        Fields.unit
        none),
      (Variant.mk
        [
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue " A Tuple consists of a sized head an unsized tail."))]
        "Tuple"
        (Fields.named
          [
            (Field.mk
              []
              Visibility.inherited
              (some "head_cells")
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
              [(Attr.mk true "specr::indirection" AttrMeta.path)]
              Visibility.inherited
              (some "tail_cells")
              (Ty.path
                none
                (Path.mk false [(PathSegment.mk "UnsafeCellStrategy" PathArguments.none)])))])
        none)])

/-- `spec/mem/pointer.md:129` -/
def struct_PointeeInfo : Item :=
  (Item.struct
    [
      (Attr.mk
        true
        "doc"
        (AttrMeta.nameValue " Describes what we know about data behind a pointer."))]
    Visibility.pub
    "PointeeInfo"
    (Generics.mk [] [])
    (Fields.named
      [
        (Field.mk
          []
          Visibility.pub
          (some "layout")
          (Ty.path none (Path.mk false [(PathSegment.mk "LayoutStrategy" PathArguments.none)]))),
        (Field.mk
          []
          Visibility.pub
          (some "inhabited")
          (Ty.path none (Path.mk false [(PathSegment.mk "bool" PathArguments.none)]))),
        (Field.mk
          [
            (Attr.mk
              true
              "doc"
              (AttrMeta.nameValue
                " Indicates where the `UnsafeCell` in this type are, which permit interior mutability."))]
          Visibility.pub
          (some "unsafe_cells")
          (Ty.path none (Path.mk false [(PathSegment.mk "UnsafeCellStrategy" PathArguments.none)]))),
        (Field.mk
          [
            (Attr.mk
              true
              "doc"
              (AttrMeta.nameValue
                " Whether the pointee implements the `Freeze` trait. This is used to determine")),
            (Attr.mk
              true
              "doc"
              (AttrMeta.nameValue
                " whether the bytes \"outside\" the pointee have interior mutability."))]
          Visibility.pub
          (some "freeze")
          (Ty.path none (Path.mk false [(PathSegment.mk "bool" PathArguments.none)]))),
        (Field.mk
          []
          Visibility.pub
          (some "unpin")
          (Ty.path none (Path.mk false [(PathSegment.mk "bool" PathArguments.none)])))]))

/-- `spec/mem/pointer.md:141` -/
def struct_TraitName : Item :=
  (Item.struct
    [
      (Attr.mk
        true
        "doc"
        (AttrMeta.nameValue " A \"trait name\" is an identifier for the trait a vtable is for.")),
      (Attr.mk
        true
        "doc"
        (AttrMeta.nameValue " This depends on the defined methods and the marker traits."))]
    Visibility.pub
    "TraitName"
    (Generics.mk [] [])
    (Fields.unnamed
      [
        (Field.mk
          []
          Visibility.pub
          none
          (Ty.path
            none
            (Path.mk
              false
              [
                (PathSegment.mk "libspecr" PathArguments.none),
                (PathSegment.mk "Name" PathArguments.none)])))]))

/-- `spec/mem/pointer.md:145` -/
def enum_PointerMetaKind : Item :=
  (Item.enum
    [
      (Attr.mk
        true
        "doc"
        (AttrMeta.nameValue " The statically known kind of metadata stored in a pointer.")),
      (Attr.mk
        true
        "doc"
        (AttrMeta.nameValue
          " This determines the type of the metadata, while `Option<PointerMeta>` determines its value."))]
    Visibility.pub
    "PointerMetaKind"
    (Generics.mk [] [])
    [
      (Variant.mk [] "None" Fields.unit none),
      (Variant.mk [] "ElementCount" Fields.unit none),
      (Variant.mk
        []
        "VTablePointer"
        (Fields.unnamed
          [
            (Field.mk
              []
              Visibility.inherited
              none
              (Ty.path none (Path.mk false [(PathSegment.mk "TraitName" PathArguments.none)])))])
        none)])

/-- `spec/mem/pointer.md:153` -/
def enum_PtrType : Item :=
  (Item.enum
    [
      (Attr.mk
        true
        "doc"
        (AttrMeta.nameValue " Stores all the information that we need to know about a pointer."))]
    Visibility.pub
    "PtrType"
    (Generics.mk [] [])
    [
      (Variant.mk
        []
        "Ref"
        (Fields.named
          [
            (Field.mk
              [
                (Attr.mk
                  true
                  "doc"
                  (AttrMeta.nameValue " Indicates a shared vs mutable reference."))]
              Visibility.inherited
              (some "mutbl")
              (Ty.path none (Path.mk false [(PathSegment.mk "Mutability" PathArguments.none)]))),
            (Field.mk
              [
                (Attr.mk
                  true
                  "doc"
                  (AttrMeta.nameValue " Describes what we know about the pointee."))]
              Visibility.inherited
              (some "pointee")
              (Ty.path none (Path.mk false [(PathSegment.mk "PointeeInfo" PathArguments.none)])))])
        none),
      (Variant.mk
        []
        "Box"
        (Fields.named
          [
            (Field.mk
              []
              Visibility.inherited
              (some "pointee")
              (Ty.path none (Path.mk false [(PathSegment.mk "PointeeInfo" PathArguments.none)])))])
        none),
      (Variant.mk
        []
        "Raw"
        (Fields.named
          [
            (Field.mk
              [
                (Attr.mk
                  true
                  "doc"
                  (AttrMeta.nameValue " Indicates what kind of metadata this pointer carries."))]
              Visibility.inherited
              (some "meta_kind")
              (Ty.path none (Path.mk false [(PathSegment.mk "PointerMetaKind" PathArguments.none)])))])
        none),
      (Variant.mk [] "FnPtr" Fields.unit none),
      (Variant.mk
        [
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue
              " This is a \"stand-alone\" vtable pointer, something that does not exist in surface Rust."))]
        "VTablePtr"
        (Fields.unnamed
          [
            (Field.mk
              []
              Visibility.inherited
              none
              (Ty.path none (Path.mk false [(PathSegment.mk "TraitName" PathArguments.none)])))])
        none)])

/-- `spec/mem/pointer.md:176` -/
def impl_PtrType__safe_pointee : Item :=
  (Item.impl
    []
    false
    false
    (Generics.mk [] [])
    false
    none
    (Ty.path none (Path.mk false [(PathSegment.mk "PtrType" PathArguments.none)]))
    [
      (ImplItem.fn
        [
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue " If this is a safe pointer, return the pointee information."))]
        Visibility.pub
        false
        (Signature.mk
          false
          false
          false
          none
          "safe_pointee"
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
                            (Path.mk false [(PathSegment.mk "PointeeInfo" PathArguments.none)])))]))]))))
        (Block.mk
          [
            (Stmt.expr
              (Expr.matchExpr
                (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                [
                  (Arm.mk
                    []
                    (Pat.or
                      [
                        (Pat.struct
                          none
                          (Path.mk
                            false
                            [
                              (PathSegment.mk "PtrType" PathArguments.none),
                              (PathSegment.mk "Ref" PathArguments.none)])
                          [
                            (FieldPat.mk
                              []
                              (Member.named "pointee")
                              true
                              (Pat.ident false false "pointee" none))]
                          true),
                        (Pat.struct
                          none
                          (Path.mk
                            false
                            [
                              (PathSegment.mk "PtrType" PathArguments.none),
                              (PathSegment.mk "Box" PathArguments.none)])
                          [
                            (FieldPat.mk
                              []
                              (Member.named "pointee")
                              true
                              (Pat.ident false false "pointee" none))]
                          true)])
                    none
                    (Expr.call
                      (Expr.path none (Path.mk false [(PathSegment.mk "Some" PathArguments.none)]))
                      [
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "pointee" PathArguments.none)]))])),
                  (Arm.mk
                    []
                    (Pat.or
                      [
                        (Pat.struct
                          none
                          (Path.mk
                            false
                            [
                              (PathSegment.mk "PtrType" PathArguments.none),
                              (PathSegment.mk "Raw" PathArguments.none)])
                          []
                          true),
                        (Pat.path
                          none
                          (Path.mk
                            false
                            [
                              (PathSegment.mk "PtrType" PathArguments.none),
                              (PathSegment.mk "FnPtr" PathArguments.none)])),
                        (Pat.tupleStruct
                          none
                          (Path.mk
                            false
                            [
                              (PathSegment.mk "PtrType" PathArguments.none),
                              (PathSegment.mk "VTablePtr" PathArguments.none)])
                          [Pat.wild])])
                    none
                    (Expr.path none (Path.mk false [(PathSegment.mk "None" PathArguments.none)])))])
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
                    (Pat.or
                      [
                        (Pat.struct
                          none
                          (Path.mk
                            false
                            [
                              (PathSegment.mk "PtrType" PathArguments.none),
                              (PathSegment.mk "Ref" PathArguments.none)])
                          [
                            (FieldPat.mk
                              []
                              (Member.named "pointee")
                              true
                              (Pat.ident false false "pointee" none))]
                          true),
                        (Pat.struct
                          none
                          (Path.mk
                            false
                            [
                              (PathSegment.mk "PtrType" PathArguments.none),
                              (PathSegment.mk "Box" PathArguments.none)])
                          [
                            (FieldPat.mk
                              []
                              (Member.named "pointee")
                              true
                              (Pat.ident false false "pointee" none))]
                          true)])
                    none
                    (Expr.methodCall
                      (Expr.field
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "pointee" PathArguments.none)]))
                        (Member.named "layout"))
                      "meta_kind"
                      none
                      [])),
                  (Arm.mk
                    []
                    (Pat.struct
                      none
                      (Path.mk
                        false
                        [
                          (PathSegment.mk "PtrType" PathArguments.none),
                          (PathSegment.mk "Raw" PathArguments.none)])
                      [
                        (FieldPat.mk
                          []
                          (Member.named "meta_kind")
                          true
                          (Pat.ident false false "meta_kind" none))]
                      true)
                    none
                    (Expr.path
                      none
                      (Path.mk false [(PathSegment.mk "meta_kind" PathArguments.none)]))),
                  (Arm.mk
                    []
                    (Pat.or
                      [
                        (Pat.path
                          none
                          (Path.mk
                            false
                            [
                              (PathSegment.mk "PtrType" PathArguments.none),
                              (PathSegment.mk "FnPtr" PathArguments.none)])),
                        (Pat.tupleStruct
                          none
                          (Path.mk
                            false
                            [
                              (PathSegment.mk "PtrType" PathArguments.none),
                              (PathSegment.mk "VTablePtr" PathArguments.none)])
                          [Pat.wild])])
                    none
                    (Expr.path
                      none
                      (Path.mk
                        false
                        [
                          (PathSegment.mk "PointerMetaKind" PathArguments.none),
                          (PathSegment.mk "None" PathArguments.none)])))])
              false)]))])

/-- All items of `spec/mem/pointer.md`, in source order, with provenance. -/
def items : List SourceItem :=
  [
    (SourceItem.mk
      "type_Address"
      22
      "77322aedd29cebdc77d9da253290fd05270fa9e8a0a8273c9bf43fa99b26299c"
      type_Address),
    (SourceItem.mk
      "struct_ThinPointer"
      28
      "da5085600dd053530a94b01932857836dfadbc9338fd2cf97a44d6bf0cf6eec6"
      struct_ThinPointer),
    (SourceItem.mk
      "enum_PointerMeta"
      36
      "09ebc0c3f848dbd308b14832639d103eea54b34ed4fad46169326407c8027b1a"
      enum_PointerMeta),
    (SourceItem.mk
      "struct_Pointer"
      45
      "db7557aa559a0c3bdf0caaa46d10f7d3692a5a2678f6fae52c293c65182dc528"
      struct_Pointer),
    (SourceItem.mk
      "impl_ThinPointer__wrapping_offset"
      52
      "c38fa458a6b70e75e5b108937c9297f0fcbec41b231eac9b7af9b7a59120842f"
      impl_ThinPointer__wrapping_offset),
    (SourceItem.mk
      "struct_TupleHeadLayout"
      77
      "53c4be993ddc54abeb42ad192758cab37ef9ee5a7a7d2b79c74790feb65d43a5"
      struct_TupleHeadLayout),
    (SourceItem.mk
      "enum_LayoutStrategy"
      91
      "dab2eaa1d2a6d43196b022cb43ceacb749d3a80e6b14ce87b4a294a5045fd372"
      enum_LayoutStrategy),
    (SourceItem.mk
      "enum_UnsafeCellStrategy"
      109
      "bcedbc97ff6e4817d0e6edb66d6261de8b511526d24e1d356d19092a6a6b230f"
      enum_UnsafeCellStrategy),
    (SourceItem.mk
      "struct_PointeeInfo"
      129
      "fab307ed3af7179bd5b4f93d40593299b59bb1f73ab753901c6de09bc5c2051a"
      struct_PointeeInfo),
    (SourceItem.mk
      "struct_TraitName"
      141
      "adeb673b26f0d65a0c63cbdc38c43b2c22dbd1228e62ac5ac2ac82f693cf93df"
      struct_TraitName),
    (SourceItem.mk
      "enum_PointerMetaKind"
      145
      "998d33f2edb547bdd6cd8d274b14454945fd7a476758df1e220a3176121be29f"
      enum_PointerMetaKind),
    (SourceItem.mk
      "enum_PtrType"
      153
      "865bbbf42440cacebaa73d8984b0842c2d810b7a25c648a67a38c1dbef486879"
      enum_PtrType),
    (SourceItem.mk
      "impl_PtrType__safe_pointee"
      176
      "0d5cf4db356b5d6be3d35df399e100717b5beee14d81914a7ae354f131d2935a"
      impl_PtrType__safe_pointee)]

end MiniRustSpec.Gen.Items.Mem.Pointer
