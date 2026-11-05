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
`spec/mem/tree_borrows/reborrow_settings.md` (commit `d821c6e3`), one Lean definition per item, in source order.
-/

import MiniRustSpec.Meta.Syntax

set_option maxRecDepth 100000

namespace MiniRustSpec.Gen.Items.Mem.TreeBorrows.ReborrowSettings

open MiniRustSpec.Syntax

/-- Path of the upstream file these items were extracted from. -/
def sourceFile : String := "spec/mem/tree_borrows/reborrow_settings.md"

/-- SHA-256 of the upstream file. -/
def sourceSha256 : String := "ecfe79402f4d11e011ef01c9013e1de1a1866821ec024c97255679af0801d729"

/-- `spec/mem/tree_borrows/reborrow_settings.md:7` -/
def struct_ReborrowSettings : Item :=
  (Item.struct
    []
    Visibility.inherited
    "ReborrowSettings"
    (Generics.mk [] [])
    (Fields.named
      [
        (Field.mk
          [
            (Attr.mk
              true
              "doc"
              (AttrMeta.nameValue
                " The permissions to set \"inside\" the data the reference points to (indexed")),
            (Attr.mk true "doc" (AttrMeta.nameValue " related to the reference)."))]
          Visibility.inherited
          (some "inside")
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
                          (Path.mk false [(PathSegment.mk "Permission" PathArguments.none)])))]))]))),
        (Field.mk
          [
            (Attr.mk
              true
              "doc"
              (AttrMeta.nameValue " The permission to set for the \"outside\" part."))]
          Visibility.inherited
          (some "outside")
          (Ty.path none (Path.mk false [(PathSegment.mk "Permission" PathArguments.none)]))),
        (Field.mk
          [(Attr.mk true "doc" (AttrMeta.nameValue " Whether and which protector to set."))]
          Visibility.inherited
          (some "protected")
          (Ty.path none (Path.mk false [(PathSegment.mk "Protected" PathArguments.none)])))]))

/-- `spec/mem/tree_borrows/reborrow_settings.md:21` -/
def fn_cells_to_freeze_mask : Item :=
  (Item.fn
    [
      (Attr.mk
        true
        "doc"
        (AttrMeta.nameValue " Converts a list of cell locations into a \"freeze mask\",")),
      (Attr.mk
        true
        "doc"
        (AttrMeta.nameValue
          " where each `bool` indicates whether the byte is frozen (i.e., *outside* all cells)."))]
    Visibility.inherited
    (Signature.mk
      false
      false
      false
      none
      "cells_to_freeze_mask"
      (Generics.mk [] [])
      [
        (FnArg.typed
          []
          (Pat.ident false false "cells" none)
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
        (FnArg.typed
          []
          (Pat.ident false false "size" none)
          (Ty.path none (Path.mk false [(PathSegment.mk "Size" PathArguments.none)])))]
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
                      (Ty.path none (Path.mk false [(PathSegment.mk "bool" PathArguments.none)])))]))]))))
    (Block.mk
      [
        (Stmt.letStmt
          []
          (Pat.ident false false "padded_front" none)
          (some
            (Expr.methodCall
              (Expr.call
                (Expr.path
                  none
                  (Path.mk
                    false
                    [
                      (PathSegment.mk "std" PathArguments.none),
                      (PathSegment.mk "iter" PathArguments.none),
                      (PathSegment.mk "once" PathArguments.none)]))
                [
                  (Expr.tuple
                    [
                      (Expr.path
                        none
                        (Path.mk
                          false
                          [
                            (PathSegment.mk "Offset" PathArguments.none),
                            (PathSegment.mk "ZERO" PathArguments.none)])),
                      (Expr.path
                        none
                        (Path.mk
                          false
                          [
                            (PathSegment.mk "Size" PathArguments.none),
                            (PathSegment.mk "ZERO" PathArguments.none)]))])])
              "chain"
              none
              [
                (Expr.methodCall
                  (Expr.path none (Path.mk false [(PathSegment.mk "cells" PathArguments.none)]))
                  "iter"
                  none
                  [])]))
          none),
        (Stmt.letStmt
          []
          (Pat.ident false false "padded_back" none)
          (some
            (Expr.methodCall
              (Expr.methodCall
                (Expr.path none (Path.mk false [(PathSegment.mk "cells" PathArguments.none)]))
                "iter"
                none
                [])
              "chain"
              none
              [
                (Expr.call
                  (Expr.path
                    none
                    (Path.mk
                      false
                      [
                        (PathSegment.mk "std" PathArguments.none),
                        (PathSegment.mk "iter" PathArguments.none),
                        (PathSegment.mk "once" PathArguments.none)]))
                  [
                    (Expr.tuple
                      [
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "size" PathArguments.none)])),
                        (Expr.path
                          none
                          (Path.mk
                            false
                            [
                              (PathSegment.mk "Size" PathArguments.none),
                              (PathSegment.mk "ZERO" PathArguments.none)]))])])]))
          none),
        (Stmt.letStmt
          []
          (Pat.ident false true "mask" none)
          (some
            (Expr.call
              (Expr.path
                none
                (Path.mk
                  false
                  [
                    (PathSegment.mk "List" PathArguments.none),
                    (PathSegment.mk "new" PathArguments.none)]))
              []))
          none),
        (Stmt.expr
          (Expr.forLoop
            none
            (Pat.tuple
              [(Pat.ident false false "current" none), (Pat.ident false false "next" none)])
            (Expr.methodCall
              (Expr.path none (Path.mk false [(PathSegment.mk "padded_front" PathArguments.none)]))
              "zip"
              none
              [(Expr.path none (Path.mk false [(PathSegment.mk "padded_back" PathArguments.none)]))])
            (Block.mk
              [
                (Stmt.expr
                  (Expr.methodCall
                    (Expr.path none (Path.mk false [(PathSegment.mk "mask" PathArguments.none)]))
                    "append"
                    none
                    [
                      (Expr.macro
                        (Macro.mk
                          (Path.mk false [(PathSegment.mk "list" PathArguments.none)])
                          MacroDelimiter.bracket
                          (MacroBody.repeatList
                            (Expr.lit (Lit.bool false))
                            (Expr.methodCall
                              (Expr.field
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "current" PathArguments.none)]))
                                (Member.unnamed 1))
                              "bytes"
                              none
                              []))))])
                  true),
                (Stmt.letStmt
                  []
                  (Pat.ident false false "no_cell_size" none)
                  (some
                    (Expr.binary
                      (Expr.methodCall
                        (Expr.field
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "next" PathArguments.none)]))
                          (Member.unnamed 0))
                        "bytes"
                        none
                        [])
                      BinOp.sub
                      (Expr.methodCall
                        (Expr.paren
                          (Expr.binary
                            (Expr.field
                              (Expr.path
                                none
                                (Path.mk false [(PathSegment.mk "current" PathArguments.none)]))
                              (Member.unnamed 0))
                            BinOp.add
                            (Expr.field
                              (Expr.path
                                none
                                (Path.mk false [(PathSegment.mk "current" PathArguments.none)]))
                              (Member.unnamed 1))))
                        "bytes"
                        none
                        [])))
                  none),
                (Stmt.expr
                  (Expr.methodCall
                    (Expr.path none (Path.mk false [(PathSegment.mk "mask" PathArguments.none)]))
                    "append"
                    none
                    [
                      (Expr.macro
                        (Macro.mk
                          (Path.mk false [(PathSegment.mk "list" PathArguments.none)])
                          MacroDelimiter.bracket
                          (MacroBody.repeatList
                            (Expr.lit (Lit.bool true))
                            (Expr.path
                              none
                              (Path.mk false [(PathSegment.mk "no_cell_size" PathArguments.none)])))))])
                  true)]))
          false),
        (Stmt.macro
          []
          (Macro.mk
            (Path.mk false [(PathSegment.mk "assert" PathArguments.none)])
            MacroDelimiter.paren
            (MacroBody.exprs
              [
                (Expr.binary
                  (Expr.methodCall
                    (Expr.path none (Path.mk false [(PathSegment.mk "mask" PathArguments.none)]))
                    "len"
                    none
                    [])
                  BinOp.eq
                  (Expr.methodCall
                    (Expr.path none (Path.mk false [(PathSegment.mk "size" PathArguments.none)]))
                    "bytes"
                    none
                    []))]
              false))
          true),
        (Stmt.expr
          (Expr.path none (Path.mk false [(PathSegment.mk "mask" PathArguments.none)]))
          false)]))

/-- `spec/mem/tree_borrows/reborrow_settings.md:50` -/
def impl_UnsafeCellStrategy__freeze_mask : Item :=
  (Item.impl
    []
    false
    false
    (Generics.mk [] [])
    false
    none
    (Ty.path none (Path.mk false [(PathSegment.mk "UnsafeCellStrategy" PathArguments.none)]))
    [
      (ImplItem.fn
        [
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue " Converts a list of cell locations into a cell \"mask\",")),
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue " where each `bool` indicates whether the byte is inside a cell."))]
        Visibility.inherited
        false
        (Signature.mk
          false
          false
          false
          none
          "freeze_mask"
          (Generics.mk [] [])
          [
            (FnArg.receiver [] false none false none),
            (FnArg.typed
              []
              (Pat.ident false false "layout" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "LayoutStrategy" PathArguments.none)]))),
            (FnArg.typed
              []
              (Pat.ident false false "ptr_metadata" none)
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
                                                (PathSegment.mk
                                                  "TreeBorrowsProvenance"
                                                  PathArguments.none)])))]))])))]))]))),
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
                                                  (PathSegment.mk
                                                    "TreeBorrowsProvenance"
                                                    PathArguments.none)])))]))]))]
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
                    "List"
                    (PathArguments.angleBracketed
                      false
                      [
                        (GenericArgument.type
                          (Ty.path
                            none
                            (Path.mk false [(PathSegment.mk "bool" PathArguments.none)])))]))]))))
        (Block.mk
          [
            (Stmt.expr
              (Expr.matchExpr
                (Expr.tuple
                  [
                    (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)])),
                    (Expr.path none (Path.mk false [(PathSegment.mk "layout" PathArguments.none)])),
                    (Expr.path
                      none
                      (Path.mk false [(PathSegment.mk "ptr_metadata" PathArguments.none)]))])
                [
                  (Arm.mk
                    []
                    (Pat.tuple
                      [
                        (Pat.struct
                          none
                          (Path.mk
                            false
                            [
                              (PathSegment.mk "UnsafeCellStrategy" PathArguments.none),
                              (PathSegment.mk "Sized" PathArguments.none)])
                          [
                            (FieldPat.mk
                              []
                              (Member.named "cells")
                              true
                              (Pat.ident false false "cells" none))]
                          false),
                        (Pat.tupleStruct
                          none
                          (Path.mk
                            false
                            [
                              (PathSegment.mk "LayoutStrategy" PathArguments.none),
                              (PathSegment.mk "Sized" PathArguments.none)])
                          [
                            (Pat.ident false false "size" none),
                            (Pat.ident false false "_align" none)]),
                        Pat.rest])
                    none
                    (Expr.block
                      none
                      (Block.mk
                        [
                          (Stmt.expr
                            (Expr.call
                              (Expr.path
                                none
                                (Path.mk
                                  false
                                  [(PathSegment.mk "cells_to_freeze_mask" PathArguments.none)]))
                              [
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "cells" PathArguments.none)])),
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "size" PathArguments.none)]))])
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
                              (PathSegment.mk "UnsafeCellStrategy" PathArguments.none),
                              (PathSegment.mk "Slice" PathArguments.none)])
                          [
                            (FieldPat.mk
                              []
                              (Member.named "element_cells")
                              true
                              (Pat.ident false false "element_cells" none))]
                          false),
                        (Pat.tupleStruct
                          none
                          (Path.mk
                            false
                            [
                              (PathSegment.mk "LayoutStrategy" PathArguments.none),
                              (PathSegment.mk "Slice" PathArguments.none)])
                          [
                            (Pat.ident false false "size" none),
                            (Pat.ident false false "_align" none)]),
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
                    (Expr.block
                      none
                      (Block.mk
                        [
                          (Stmt.letStmt
                            []
                            (Pat.ident false false "element_mask" none)
                            (some
                              (Expr.call
                                (Expr.path
                                  none
                                  (Path.mk
                                    false
                                    [(PathSegment.mk "cells_to_freeze_mask" PathArguments.none)]))
                                [
                                  (Expr.path
                                    none
                                    (Path.mk
                                      false
                                      [(PathSegment.mk "element_cells" PathArguments.none)])),
                                  (Expr.path
                                    none
                                    (Path.mk false [(PathSegment.mk "size" PathArguments.none)]))]))
                            none),
                          (Stmt.letStmt
                            []
                            (Pat.ident false true "mask" none)
                            (some
                              (Expr.call
                                (Expr.path
                                  none
                                  (Path.mk
                                    false
                                    [
                                      (PathSegment.mk "List" PathArguments.none),
                                      (PathSegment.mk "new" PathArguments.none)]))
                                []))
                            none),
                          (Stmt.expr
                            (Expr.forLoop
                              none
                              Pat.wild
                              (Expr.range
                                (some
                                  (Expr.path
                                    none
                                    (Path.mk
                                      false
                                      [
                                        (PathSegment.mk "Int" PathArguments.none),
                                        (PathSegment.mk "ZERO" PathArguments.none)])))
                                RangeLimits.halfOpen
                                (some
                                  (Expr.path
                                    none
                                    (Path.mk false [(PathSegment.mk "count" PathArguments.none)]))))
                              (Block.mk
                                [
                                  (Stmt.expr
                                    (Expr.methodCall
                                      (Expr.path
                                        none
                                        (Path.mk false [(PathSegment.mk "mask" PathArguments.none)]))
                                      "append"
                                      none
                                      [
                                        (Expr.path
                                          none
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "element_mask" PathArguments.none)]))])
                                    true)]))
                            true),
                          (Stmt.expr
                            (Expr.path
                              none
                              (Path.mk false [(PathSegment.mk "mask" PathArguments.none)]))
                            false)]))),
                  (Arm.mk
                    []
                    (Pat.tuple
                      [
                        (Pat.path
                          none
                          (Path.mk
                            false
                            [
                              (PathSegment.mk "UnsafeCellStrategy" PathArguments.none),
                              (PathSegment.mk "TraitObject" PathArguments.none)])),
                        (Pat.tupleStruct
                          none
                          (Path.mk
                            false
                            [
                              (PathSegment.mk "LayoutStrategy" PathArguments.none),
                              (PathSegment.mk "TraitObject" PathArguments.none)])
                          [(Pat.ident false false "_trait_name" none)]),
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
                              [(Pat.ident false false "ptr" none)])])])
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
                                  (Path.mk
                                    false
                                    [(PathSegment.mk "vtable_lookup" PathArguments.none)]))
                                [
                                  (Expr.path
                                    none
                                    (Path.mk false [(PathSegment.mk "ptr" PathArguments.none)]))]))
                            none),
                          (Stmt.expr
                            (Expr.call
                              (Expr.path
                                none
                                (Path.mk
                                  false
                                  [(PathSegment.mk "cells_to_freeze_mask" PathArguments.none)]))
                              [
                                (Expr.field
                                  (Expr.path
                                    none
                                    (Path.mk false [(PathSegment.mk "vtable" PathArguments.none)]))
                                  (Member.named "cells")),
                                (Expr.field
                                  (Expr.path
                                    none
                                    (Path.mk false [(PathSegment.mk "vtable" PathArguments.none)]))
                                  (Member.named "size"))])
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
                              (PathSegment.mk "UnsafeCellStrategy" PathArguments.none),
                              (PathSegment.mk "Tuple" PathArguments.none)])
                          [
                            (FieldPat.mk
                              []
                              (Member.named "head_cells")
                              true
                              (Pat.ident false false "head_cells" none)),
                            (FieldPat.mk
                              []
                              (Member.named "tail_cells")
                              true
                              (Pat.ident false false "tail_cells" none))]
                          false),
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
                        Pat.wild])
                    none
                    (Expr.block
                      none
                      (Block.mk
                        [
                          (Stmt.letStmt
                            []
                            (Pat.ident false true "mask" none)
                            (some
                              (Expr.call
                                (Expr.path
                                  none
                                  (Path.mk
                                    false
                                    [(PathSegment.mk "cells_to_freeze_mask" PathArguments.none)]))
                                [
                                  (Expr.path
                                    none
                                    (Path.mk
                                      false
                                      [(PathSegment.mk "head_cells" PathArguments.none)])),
                                  (Expr.field
                                    (Expr.path
                                      none
                                      (Path.mk false [(PathSegment.mk "head" PathArguments.none)]))
                                    (Member.named "end"))]))
                            none),
                          (Stmt.expr
                            (Expr.methodCall
                              (Expr.path
                                none
                                (Path.mk false [(PathSegment.mk "mask" PathArguments.none)]))
                              "append"
                              none
                              [
                                (Expr.methodCall
                                  (Expr.path
                                    none
                                    (Path.mk
                                      false
                                      [(PathSegment.mk "tail_cells" PathArguments.none)]))
                                  "freeze_mask"
                                  none
                                  [
                                    (Expr.path
                                      none
                                      (Path.mk false [(PathSegment.mk "tail" PathArguments.none)])),
                                    (Expr.path
                                      none
                                      (Path.mk
                                        false
                                        [(PathSegment.mk "ptr_metadata" PathArguments.none)])),
                                    (Expr.path
                                      none
                                      (Path.mk
                                        false
                                        [(PathSegment.mk "vtable_lookup" PathArguments.none)]))])])
                            true),
                          (Stmt.expr
                            (Expr.path
                              none
                              (Path.mk false [(PathSegment.mk "mask" PathArguments.none)]))
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
                          [
                            (Expr.lit
                              (Lit.str "Invalid LayoutStrategy and PointerMeta combination"))]
                          false))))])
              false)]))])

/-- `spec/mem/tree_borrows/reborrow_settings.md:89` -/
def impl_ReborrowSettings__new : Item :=
  (Item.impl
    []
    false
    false
    (Generics.mk [] [])
    false
    none
    (Ty.path none (Path.mk false [(PathSegment.mk "ReborrowSettings" PathArguments.none)]))
    [
      (ImplItem.fn
        [
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue
              " Compute the permissions to be assigned when retagging the given pointer.")),
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue " `None` indicates that no retagging should happen."))]
        Visibility.inherited
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
                                [(PathSegment.mk "TreeBorrowsProvenance" PathArguments.none)])))]))]))),
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
              (Pat.ident false false "params" none)
              (Ty.path
                none
                (Path.mk false [(PathSegment.mk "TreeBorrowsParams" PathArguments.none)]))),
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
                                                  (PathSegment.mk
                                                    "TreeBorrowsProvenance"
                                                    PathArguments.none)])))]))]))]
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
                    "Option"
                    (PathArguments.angleBracketed
                      false
                      [
                        (GenericArgument.type
                          (Ty.path
                            none
                            (Path.mk false [(PathSegment.mk "Self" PathArguments.none)])))]))]))))
        (Block.mk
          [
            (Stmt.letStmt
              []
              (Pat.tupleStruct
                none
                (Path.mk false [(PathSegment.mk "Some" PathArguments.none)])
                [(Pat.ident false false "pointee_info" none)])
              (some
                (Expr.methodCall
                  (Expr.path none (Path.mk false [(PathSegment.mk "ptr_type" PathArguments.none)]))
                  "safe_pointee"
                  none
                  []))
              (some
                (Expr.block
                  none
                  (Block.mk
                    [
                      (Stmt.expr
                        (Expr.returnExpr
                          (some
                            (Expr.path
                              none
                              (Path.mk false [(PathSegment.mk "None" PathArguments.none)]))))
                        true)])))),
            (Stmt.expr
              (Expr.ite
                (Expr.macro
                  (Macro.mk
                    (Path.mk false [(PathSegment.mk "matches" PathArguments.none)])
                    MacroDelimiter.paren
                    (MacroBody.exprAndPat
                      (Expr.path
                        none
                        (Path.mk false [(PathSegment.mk "ptr_type" PathArguments.none)]))
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
                                (Member.named "mutbl")
                                false
                                (Pat.path
                                  none
                                  (Path.mk
                                    false
                                    [
                                      (PathSegment.mk "Mutability" PathArguments.none),
                                      (PathSegment.mk "Mutable" PathArguments.none)]))),
                              (FieldPat.mk
                                []
                                (Member.named "pointee")
                                true
                                (Pat.ident false false "pointee" none))]
                            false),
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
                            false)])
                      (some
                        (Expr.unary
                          UnOp.not
                          (Expr.field
                            (Expr.path
                              none
                              (Path.mk false [(PathSegment.mk "pointee" PathArguments.none)]))
                            (Member.named "unpin")))))))
                (Block.mk
                  [
                    (Stmt.expr
                      (Expr.returnExpr
                        (some
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "None" PathArguments.none)]))))
                      true)])
                none)
              false),
            (Stmt.letStmt
              []
              (Pat.ident false false "protected" none)
              (some
                (Expr.ite
                  (Expr.path none (Path.mk false [(PathSegment.mk "fn_entry" PathArguments.none)]))
                  (Block.mk
                    [
                      (Stmt.expr
                        (Expr.matchExpr
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "ptr_type" PathArguments.none)]))
                          [
                            (Arm.mk
                              []
                              (Pat.struct
                                none
                                (Path.mk
                                  false
                                  [
                                    (PathSegment.mk "PtrType" PathArguments.none),
                                    (PathSegment.mk "Box" PathArguments.none)])
                                []
                                true)
                              none
                              (Expr.path
                                none
                                (Path.mk
                                  false
                                  [
                                    (PathSegment.mk "Protected" PathArguments.none),
                                    (PathSegment.mk "Weak" PathArguments.none)]))),
                            (Arm.mk
                              []
                              Pat.wild
                              none
                              (Expr.path
                                none
                                (Path.mk
                                  false
                                  [
                                    (PathSegment.mk "Protected" PathArguments.none),
                                    (PathSegment.mk "Strong" PathArguments.none)])))])
                        false)])
                  (some
                    (Expr.block
                      none
                      (Block.mk
                        [
                          (Stmt.expr
                            (Expr.path
                              none
                              (Path.mk
                                false
                                [
                                  (PathSegment.mk "Protected" PathArguments.none),
                                  (PathSegment.mk "No" PathArguments.none)]))
                            false)])))))
              none),
            (Stmt.letStmt
              []
              (Pat.ident false false "implicit_writes_enabled" none)
              (some
                (Expr.binary
                  (Expr.binary
                    (Expr.methodCall
                      (Expr.path
                        none
                        (Path.mk false [(PathSegment.mk "protected" PathArguments.none)]))
                      "yes"
                      none
                      [])
                    BinOp.and
                    (Expr.field
                      (Expr.path
                        none
                        (Path.mk false [(PathSegment.mk "params" PathArguments.none)]))
                      (Member.named "implicit_writes")))
                  BinOp.and
                  (Expr.path
                    none
                    (Path.mk false [(PathSegment.mk "fn_implicit_writes" PathArguments.none)]))))
              none),
            (Stmt.letStmt
              []
              (Pat.ident false false "perm" none)
              (some
                (Expr.closure
                  false
                  [
                    (Pat.typed
                      (Pat.ident false false "inside" none)
                      (Ty.path none (Path.mk false [(PathSegment.mk "bool" PathArguments.none)]))),
                    (Pat.typed
                      (Pat.ident false false "frozen" none)
                      (Ty.path none (Path.mk false [(PathSegment.mk "bool" PathArguments.none)])))]
                  none
                  (Expr.block
                    none
                    (Block.mk
                      [
                        (Stmt.letStmt
                          []
                          (Pat.ident false false "mk_perm" none)
                          (some
                            (Expr.closure
                              false
                              [
                                (Pat.ident false false "unprot" none),
                                (Pat.ident false false "prot" none)]
                              none
                              (Expr.ite
                                (Expr.methodCall
                                  (Expr.path
                                    none
                                    (Path.mk
                                      false
                                      [(PathSegment.mk "protected" PathArguments.none)]))
                                  "yes"
                                  none
                                  [])
                                (Block.mk
                                  [
                                    (Stmt.expr
                                      (Expr.call
                                        (Expr.path
                                          none
                                          (Path.mk
                                            false
                                            [
                                              (PathSegment.mk "Permission" PathArguments.none),
                                              (PathSegment.mk "Prot" PathArguments.none)]))
                                        [
                                          (Expr.path
                                            none
                                            (Path.mk
                                              false
                                              [(PathSegment.mk "prot" PathArguments.none)]))])
                                      false)])
                                (some
                                  (Expr.block
                                    none
                                    (Block.mk
                                      [
                                        (Stmt.expr
                                          (Expr.call
                                            (Expr.path
                                              none
                                              (Path.mk
                                                false
                                                [
                                                  (PathSegment.mk "Permission" PathArguments.none),
                                                  (PathSegment.mk "Unprot" PathArguments.none)]))
                                            [
                                              (Expr.path
                                                none
                                                (Path.mk
                                                  false
                                                  [(PathSegment.mk "unprot" PathArguments.none)]))])
                                          false)]))))))
                          none),
                        (Stmt.expr
                          (Expr.matchExpr
                            (Expr.path
                              none
                              (Path.mk false [(PathSegment.mk "ptr_type" PathArguments.none)]))
                            [
                              (Arm.mk
                                []
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
                                      (Member.named "mutbl")
                                      false
                                      (Pat.path
                                        none
                                        (Path.mk
                                          false
                                          [
                                            (PathSegment.mk "Mutability" PathArguments.none),
                                            (PathSegment.mk "Immutable" PathArguments.none)])))]
                                  true)
                                none
                                (Expr.ite
                                  (Expr.path
                                    none
                                    (Path.mk false [(PathSegment.mk "frozen" PathArguments.none)]))
                                  (Block.mk
                                    [
                                      (Stmt.expr
                                        (Expr.call
                                          (Expr.path
                                            none
                                            (Path.mk
                                              false
                                              [(PathSegment.mk "mk_perm" PathArguments.none)]))
                                          [
                                            (Expr.path
                                              none
                                              (Path.mk
                                                false
                                                [
                                                  (PathSegment.mk
                                                    "PermissionUnprot"
                                                    PathArguments.none),
                                                  (PathSegment.mk "Frozen" PathArguments.none)])),
                                            (Expr.struct
                                              none
                                              (Path.mk
                                                false
                                                [
                                                  (PathSegment.mk
                                                    "PermissionProt"
                                                    PathArguments.none),
                                                  (PathSegment.mk "Frozen" PathArguments.none)])
                                              [
                                                (FieldValue.mk
                                                  []
                                                  (Member.named "had_local_read")
                                                  false
                                                  (Expr.lit (Lit.bool false)))]
                                              false
                                              none)])
                                        false)])
                                  (some
                                    (Expr.block
                                      none
                                      (Block.mk
                                        [
                                          (Stmt.expr
                                            (Expr.call
                                              (Expr.path
                                                none
                                                (Path.mk
                                                  false
                                                  [(PathSegment.mk "mk_perm" PathArguments.none)]))
                                              [
                                                (Expr.path
                                                  none
                                                  (Path.mk
                                                    false
                                                    [
                                                      (PathSegment.mk
                                                        "PermissionUnprot"
                                                        PathArguments.none),
                                                      (PathSegment.mk "Cell" PathArguments.none)])),
                                                (Expr.path
                                                  none
                                                  (Path.mk
                                                    false
                                                    [
                                                      (PathSegment.mk
                                                        "PermissionProt"
                                                        PathArguments.none),
                                                      (PathSegment.mk "Cell" PathArguments.none)]))])
                                            false)]))))),
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
                                          (Member.named "mutbl")
                                          false
                                          (Pat.path
                                            none
                                            (Path.mk
                                              false
                                              [
                                                (PathSegment.mk "Mutability" PathArguments.none),
                                                (PathSegment.mk "Mutable" PathArguments.none)])))]
                                      true),
                                    (Pat.struct
                                      none
                                      (Path.mk
                                        false
                                        [
                                          (PathSegment.mk "PtrType" PathArguments.none),
                                          (PathSegment.mk "Box" PathArguments.none)])
                                      []
                                      true)])
                                none
                                (Expr.ite
                                  (Expr.binary
                                    (Expr.path
                                      none
                                      (Path.mk
                                        false
                                        [
                                          (PathSegment.mk
                                            "implicit_writes_enabled"
                                            PathArguments.none)]))
                                    BinOp.and
                                    (Expr.path
                                      none
                                      (Path.mk false [(PathSegment.mk "inside" PathArguments.none)])))
                                  (Block.mk
                                    [
                                      (Stmt.macro
                                        []
                                        (Macro.mk
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "assert" PathArguments.none)])
                                          MacroDelimiter.paren
                                          (MacroBody.exprs
                                            [
                                              (Expr.methodCall
                                                (Expr.path
                                                  none
                                                  (Path.mk
                                                    false
                                                    [
                                                      (PathSegment.mk
                                                        "protected"
                                                        PathArguments.none)]))
                                                "yes"
                                                none
                                                [])]
                                            false))
                                        true),
                                      (Stmt.expr
                                        (Expr.call
                                          (Expr.path
                                            none
                                            (Path.mk
                                              false
                                              [
                                                (PathSegment.mk "Permission" PathArguments.none),
                                                (PathSegment.mk "Prot" PathArguments.none)]))
                                          [
                                            (Expr.path
                                              none
                                              (Path.mk
                                                false
                                                [
                                                  (PathSegment.mk
                                                    "PermissionProt"
                                                    PathArguments.none),
                                                  (PathSegment.mk "Unique" PathArguments.none)]))])
                                        false)])
                                  (some
                                    (Expr.block
                                      none
                                      (Block.mk
                                        [
                                          (Stmt.expr
                                            (Expr.call
                                              (Expr.path
                                                none
                                                (Path.mk
                                                  false
                                                  [(PathSegment.mk "mk_perm" PathArguments.none)]))
                                              [
                                                (Expr.ite
                                                  (Expr.path
                                                    none
                                                    (Path.mk
                                                      false
                                                      [(PathSegment.mk "frozen" PathArguments.none)]))
                                                  (Block.mk
                                                    [
                                                      (Stmt.expr
                                                        (Expr.path
                                                          none
                                                          (Path.mk
                                                            false
                                                            [
                                                              (PathSegment.mk
                                                                "PermissionUnprot"
                                                                PathArguments.none),
                                                              (PathSegment.mk
                                                                "Reserved"
                                                                PathArguments.none)]))
                                                        false)])
                                                  (some
                                                    (Expr.block
                                                      none
                                                      (Block.mk
                                                        [
                                                          (Stmt.expr
                                                            (Expr.path
                                                              none
                                                              (Path.mk
                                                                false
                                                                [
                                                                  (PathSegment.mk
                                                                    "PermissionUnprot"
                                                                    PathArguments.none),
                                                                  (PathSegment.mk
                                                                    "ReservedIm"
                                                                    PathArguments.none)]))
                                                            false)])))),
                                                (Expr.struct
                                                  none
                                                  (Path.mk
                                                    false
                                                    [
                                                      (PathSegment.mk
                                                        "PermissionProt"
                                                        PathArguments.none),
                                                      (PathSegment.mk "Reserved" PathArguments.none)])
                                                  [
                                                    (FieldValue.mk
                                                      []
                                                      (Member.named "had_local_read")
                                                      false
                                                      (Expr.lit (Lit.bool false))),
                                                    (FieldValue.mk
                                                      []
                                                      (Member.named "had_foreign_read")
                                                      false
                                                      (Expr.lit (Lit.bool false)))]
                                                  false
                                                  none)])
                                            false)]))))),
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
                                (Expr.macro
                                  (Macro.mk
                                    (Path.mk
                                      false
                                      [(PathSegment.mk "unreachable" PathArguments.none)])
                                    MacroDelimiter.paren
                                    (MacroBody.exprs
                                      [
                                        (Expr.lit
                                          (Lit.str
                                            "safe_pointee() returns None for Raw, FnPtr, and VTablePtr; should have returned early on function entry"))]
                                      false))))])
                          false)]))))
              none),
            (Stmt.letStmt
              []
              (Pat.ident false false "inside" none)
              (some
                (Expr.methodCall
                  (Expr.methodCall
                    (Expr.field
                      (Expr.path
                        none
                        (Path.mk false [(PathSegment.mk "pointee_info" PathArguments.none)]))
                      (Member.named "unsafe_cells"))
                    "freeze_mask"
                    none
                    [
                      (Expr.field
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "pointee_info" PathArguments.none)]))
                        (Member.named "layout")),
                      (Expr.field
                        (Expr.path none (Path.mk false [(PathSegment.mk "ptr" PathArguments.none)]))
                        (Member.named "metadata")),
                      (Expr.path
                        none
                        (Path.mk false [(PathSegment.mk "vtable_lookup" PathArguments.none)]))])
                  "map"
                  none
                  [
                    (Expr.closure
                      false
                      [(Pat.ident false false "freeze" none)]
                      none
                      (Expr.call
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "perm" PathArguments.none)]))
                        [
                          (Expr.lit (Lit.bool true)),
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "freeze" PathArguments.none)]))]))]))
              none),
            (Stmt.letStmt
              []
              (Pat.ident false false "outside" none)
              (some
                (Expr.call
                  (Expr.path none (Path.mk false [(PathSegment.mk "perm" PathArguments.none)]))
                  [
                    (Expr.lit (Lit.bool false)),
                    (Expr.field
                      (Expr.path
                        none
                        (Path.mk false [(PathSegment.mk "pointee_info" PathArguments.none)]))
                      (Member.named "freeze"))]))
              none),
            (Stmt.expr
              (Expr.call
                (Expr.path none (Path.mk false [(PathSegment.mk "Some" PathArguments.none)]))
                [
                  (Expr.struct
                    none
                    (Path.mk false [(PathSegment.mk "ReborrowSettings" PathArguments.none)])
                    [
                      (FieldValue.mk
                        []
                        (Member.named "protected")
                        true
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "protected" PathArguments.none)]))),
                      (FieldValue.mk
                        []
                        (Member.named "inside")
                        true
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "inside" PathArguments.none)]))),
                      (FieldValue.mk
                        []
                        (Member.named "outside")
                        true
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "outside" PathArguments.none)])))]
                    false
                    none)])
              false)]))])

/-- All items of `spec/mem/tree_borrows/reborrow_settings.md`, in source order, with provenance. -/
def items : List SourceItem :=
  [
    (SourceItem.mk
      "struct_ReborrowSettings"
      7
      "1b648fff416008a72648593498636d0ae2781a893523bfed805996d2583b4ff7"
      struct_ReborrowSettings),
    (SourceItem.mk
      "fn_cells_to_freeze_mask"
      21
      "1acec799b4cbb8fdcd2a78e33da1d8db3ff1e8b126597822999bac321ce54bb6"
      fn_cells_to_freeze_mask),
    (SourceItem.mk
      "impl_UnsafeCellStrategy__freeze_mask"
      50
      "76cea78095229da5ba6688d09216185095ce0ea6874edd3b5e92df1d175b0513"
      impl_UnsafeCellStrategy__freeze_mask),
    (SourceItem.mk
      "impl_ReborrowSettings__new"
      89
      "3f4838dfd2a7b703afeef253f7c3c0e4e112a91ab4495291d691f2dae7dbadbe"
      impl_ReborrowSettings__new)]

end MiniRustSpec.Gen.Items.Mem.TreeBorrows.ReborrowSettings
