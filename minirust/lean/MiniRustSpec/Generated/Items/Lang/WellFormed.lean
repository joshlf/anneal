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
`spec/lang/well-formed.md` (commit `d821c6e3`), one Lean definition per item, in source order.
-/

import MiniRustSpec.Meta.Syntax

set_option maxRecDepth 100000

namespace MiniRustSpec.Gen.Items.Lang.WellFormed

open MiniRustSpec.Syntax

/-- Path of the upstream file these items were extracted from. -/
def sourceFile : String := "spec/lang/well-formed.md"

/-- SHA-256 of the upstream file. -/
def sourceSha256 : String := "4aef03dfaa6b8e12128951143bb2a0b98c1de2dd8f5c2a762ffeef334b6d0bcb"

/-- `spec/lang/well-formed.md:12` -/
def fn_ensure_wf : Item :=
  (Item.fn
    []
    Visibility.inherited
    (Signature.mk
      false
      false
      false
      none
      "ensure_wf"
      (Generics.mk [] [])
      [
        (FnArg.typed
          []
          (Pat.ident false false "b" none)
          (Ty.path none (Path.mk false [(PathSegment.mk "bool" PathArguments.none)]))),
        (FnArg.typed
          []
          (Pat.ident false false "msg" none)
          (Ty.reference
            none
            false
            (Ty.path none (Path.mk false [(PathSegment.mk "str" PathArguments.none)]))))]
      false
      (some
        (Ty.path
          none
          (Path.mk
            false
            [
              (PathSegment.mk
                "Result"
                (PathArguments.angleBracketed false [(GenericArgument.type (Ty.tuple []))]))]))))
    (Block.mk
      [
        (Stmt.expr
          (Expr.ite
            (Expr.unary
              UnOp.not
              (Expr.path none (Path.mk false [(PathSegment.mk "b" PathArguments.none)])))
            (Block.mk
              [
                (Stmt.macro
                  []
                  (Macro.mk
                    (Path.mk false [(PathSegment.mk "throw_ill_formed" PathArguments.none)])
                    MacroDelimiter.paren
                    (MacroBody.exprs
                      [
                        (Expr.lit (Lit.str "{}")),
                        (Expr.path none (Path.mk false [(PathSegment.mk "msg" PathArguments.none)]))]
                      false))
                  true)])
            none)
          false),
        (Stmt.expr
          (Expr.call
            (Expr.path none (Path.mk false [(PathSegment.mk "ret" PathArguments.none)]))
            [(Expr.tuple [])])
          false)]))

/-- `spec/lang/well-formed.md:21` -/
def impl_IntType__check_wf : Item :=
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
        Visibility.inherited
        false
        (Signature.mk
          false
          false
          false
          none
          "check_wf"
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
                    "Result"
                    (PathArguments.angleBracketed false [(GenericArgument.type (Ty.tuple []))]))]))))
        (Block.mk
          [
            (Stmt.expr
              (Expr.call
                (Expr.path none (Path.mk false [(PathSegment.mk "ensure_wf" PathArguments.none)]))
                [
                  (Expr.methodCall
                    (Expr.methodCall
                      (Expr.field
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                        (Member.named "size"))
                      "bytes"
                      none
                      [])
                    "is_power_of_two"
                    none
                    []),
                  (Expr.lit (Lit.str "IntType: size is not power of two"))])
              false)]))])

/-- `spec/lang/well-formed.md:28` -/
def impl_TupleHeadLayout__check_wf : Item :=
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
        []
        Visibility.inherited
        false
        (Signature.mk
          false
          false
          false
          none
          "check_wf"
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
            (Ty.path
              none
              (Path.mk
                false
                [
                  (PathSegment.mk
                    "Result"
                    (PathArguments.angleBracketed false [(GenericArgument.type (Ty.tuple []))]))]))))
        (Block.mk
          [
            (Stmt.expr
              (Expr.tryExpr
                (Expr.call
                  (Expr.path none (Path.mk false [(PathSegment.mk "ensure_wf" PathArguments.none)]))
                  [
                    (Expr.call
                      (Expr.path
                        none
                        (Path.mk
                          false
                          [
                            (PathSegment.mk "T" PathArguments.none),
                            (PathSegment.mk "valid_size" PathArguments.none)]))
                      [
                        (Expr.field
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                          (Member.named "end"))]),
                    (Expr.lit (Lit.str "TupleHeadLayout: end not valid"))]))
              true),
            (Stmt.expr
              (Expr.ite
                (Expr.letCond
                  (Pat.tupleStruct
                    none
                    (Path.mk false [(PathSegment.mk "Some" PathArguments.none)])
                    [(Pat.ident false false "packed" none)])
                  (Expr.field
                    (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                    (Member.named "packed_align")))
                (Block.mk
                  [
                    (Stmt.expr
                      (Expr.tryExpr
                        (Expr.call
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "ensure_wf" PathArguments.none)]))
                          [
                            (Expr.binary
                              (Expr.field
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                                (Member.named "align"))
                              BinOp.le
                              (Expr.path
                                none
                                (Path.mk false [(PathSegment.mk "packed" PathArguments.none)]))),
                            (Expr.lit
                              (Lit.str "TupleHeadLayout: align bigger than packed attribute"))]))
                      true)])
                none)
              false),
            (Stmt.expr
              (Expr.call
                (Expr.path none (Path.mk false [(PathSegment.mk "ret" PathArguments.none)]))
                [(Expr.tuple [])])
              false)]))])

/-- `spec/lang/well-formed.md:38` -/
def impl_LayoutStrategy__check_wf : Item :=
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
        [
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue " This does *not* require that size is a multiple of align!"))]
        Visibility.inherited
        false
        (Signature.mk
          false
          false
          false
          none
          "check_wf"
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
              (Pat.ident false false "prog" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "Program" PathArguments.none)])))]
          false
          (some
            (Ty.path
              none
              (Path.mk
                false
                [
                  (PathSegment.mk
                    "Result"
                    (PathArguments.angleBracketed false [(GenericArgument.type (Ty.tuple []))]))]))))
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
                      [(Pat.ident false false "size" none), (Pat.ident false false "_align" none)])
                    none
                    (Expr.block
                      none
                      (Block.mk
                        [
                          (Stmt.expr
                            (Expr.tryExpr
                              (Expr.call
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "ensure_wf" PathArguments.none)]))
                                [
                                  (Expr.call
                                    (Expr.path
                                      none
                                      (Path.mk
                                        false
                                        [
                                          (PathSegment.mk "T" PathArguments.none),
                                          (PathSegment.mk "valid_size" PathArguments.none)]))
                                    [
                                      (Expr.path
                                        none
                                        (Path.mk false [(PathSegment.mk "size" PathArguments.none)]))]),
                                  (Expr.lit (Lit.str "LayoutStrategy: size not valid"))]))
                            true)]))),
                  (Arm.mk
                    []
                    (Pat.tupleStruct
                      none
                      (Path.mk
                        false
                        [
                          (PathSegment.mk "LayoutStrategy" PathArguments.none),
                          (PathSegment.mk "Slice" PathArguments.none)])
                      [(Pat.ident false false "size" none), (Pat.ident false false "_align" none)])
                    none
                    (Expr.block
                      none
                      (Block.mk
                        [
                          (Stmt.expr
                            (Expr.tryExpr
                              (Expr.call
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "ensure_wf" PathArguments.none)]))
                                [
                                  (Expr.call
                                    (Expr.path
                                      none
                                      (Path.mk
                                        false
                                        [
                                          (PathSegment.mk "T" PathArguments.none),
                                          (PathSegment.mk "valid_size" PathArguments.none)]))
                                    [
                                      (Expr.path
                                        none
                                        (Path.mk false [(PathSegment.mk "size" PathArguments.none)]))]),
                                  (Expr.lit (Lit.str "LayoutStrategy: element size not valid"))]))
                            true)]))),
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
                    (Expr.block
                      none
                      (Block.mk
                        [
                          (Stmt.expr
                            (Expr.tryExpr
                              (Expr.call
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "ensure_wf" PathArguments.none)]))
                                [
                                  (Expr.methodCall
                                    (Expr.field
                                      (Expr.path
                                        none
                                        (Path.mk false [(PathSegment.mk "prog" PathArguments.none)]))
                                      (Member.named "traits"))
                                    "contains_key"
                                    none
                                    [
                                      (Expr.path
                                        none
                                        (Path.mk
                                          false
                                          [(PathSegment.mk "trait_name" PathArguments.none)]))]),
                                  (Expr.lit (Lit.str "LayoutStrategy: trait name doesn't exist"))]))
                            true)]))),
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
                          (Member.named "head")
                          true
                          (Pat.ident false false "head" none)),
                        (FieldPat.mk
                          []
                          (Member.named "tail")
                          true
                          (Pat.ident false false "tail" none))]
                      false)
                    none
                    (Expr.block
                      none
                      (Block.mk
                        [
                          (Stmt.expr
                            (Expr.tryExpr
                              (Expr.methodCall
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "head" PathArguments.none)]))
                                "check_wf"
                                (some
                                  [
                                    (GenericArgument.type
                                      (Ty.path
                                        none
                                        (Path.mk false [(PathSegment.mk "T" PathArguments.none)])))])
                                []))
                            true),
                          (Stmt.expr
                            (Expr.tryExpr
                              (Expr.methodCall
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "tail" PathArguments.none)]))
                                "check_wf"
                                (some
                                  [
                                    (GenericArgument.type
                                      (Ty.path
                                        none
                                        (Path.mk false [(PathSegment.mk "T" PathArguments.none)])))])
                                [
                                  (Expr.path
                                    none
                                    (Path.mk false [(PathSegment.mk "prog" PathArguments.none)]))]))
                            true),
                          (Stmt.expr
                            (Expr.tryExpr
                              (Expr.call
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "ensure_wf" PathArguments.none)]))
                                [
                                  (Expr.unary
                                    UnOp.not
                                    (Expr.methodCall
                                      (Expr.path
                                        none
                                        (Path.mk false [(PathSegment.mk "tail" PathArguments.none)]))
                                      "is_sized"
                                      none
                                      [])),
                                  (Expr.lit (Lit.str "LayoutStrategy: tuple with sized tail"))]))
                            true)])))])
              true),
            (Stmt.expr
              (Expr.call
                (Expr.path none (Path.mk false [(PathSegment.mk "ret" PathArguments.none)]))
                [(Expr.tuple [])])
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
          "check_aligned"
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
                    "Result"
                    (PathArguments.angleBracketed false [(GenericArgument.type (Ty.tuple []))]))]))))
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
                      [(Pat.ident false false "size" none), (Pat.ident false false "align" none)])
                    none
                    (Expr.block
                      none
                      (Block.mk
                        [
                          (Stmt.expr
                            (Expr.tryExpr
                              (Expr.call
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "ensure_wf" PathArguments.none)]))
                                [
                                  (Expr.binary
                                    (Expr.binary
                                      (Expr.methodCall
                                        (Expr.path
                                          none
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "size" PathArguments.none)]))
                                        "bytes"
                                        none
                                        [])
                                      BinOp.rem
                                      (Expr.methodCall
                                        (Expr.path
                                          none
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "align" PathArguments.none)]))
                                        "bytes"
                                        none
                                        []))
                                    BinOp.eq
                                    (Expr.lit (Lit.int 0 ""))),
                                  (Expr.lit
                                    (Lit.str "check_aligned: size not a multiple of alignment"))]))
                            true)]))),
                  (Arm.mk
                    []
                    (Pat.tupleStruct
                      none
                      (Path.mk
                        false
                        [
                          (PathSegment.mk "LayoutStrategy" PathArguments.none),
                          (PathSegment.mk "Slice" PathArguments.none)])
                      [(Pat.ident false false "size" none), (Pat.ident false false "align" none)])
                    none
                    (Expr.block
                      none
                      (Block.mk
                        [
                          (Stmt.expr
                            (Expr.tryExpr
                              (Expr.call
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "ensure_wf" PathArguments.none)]))
                                [
                                  (Expr.binary
                                    (Expr.binary
                                      (Expr.methodCall
                                        (Expr.path
                                          none
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "size" PathArguments.none)]))
                                        "bytes"
                                        none
                                        [])
                                      BinOp.rem
                                      (Expr.methodCall
                                        (Expr.path
                                          none
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "align" PathArguments.none)]))
                                        "bytes"
                                        none
                                        []))
                                    BinOp.eq
                                    (Expr.lit (Lit.int 0 ""))),
                                  (Expr.lit
                                    (Lit.str
                                      "check_aligned: element size not a multiple of alignment"))]))
                            true)]))),
                  (Arm.mk
                    []
                    (Pat.tupleStruct
                      none
                      (Path.mk
                        false
                        [
                          (PathSegment.mk "LayoutStrategy" PathArguments.none),
                          (PathSegment.mk "TraitObject" PathArguments.none)])
                      [Pat.rest])
                    none
                    (Expr.tuple [])),
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
                    (Expr.tryExpr
                      (Expr.methodCall
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "tail" PathArguments.none)]))
                        "check_aligned"
                        none
                        [])))])
              true),
            (Stmt.expr
              (Expr.call
                (Expr.path none (Path.mk false [(PathSegment.mk "ret" PathArguments.none)]))
                [(Expr.tuple [])])
              false)]))])

/-- `spec/lang/well-formed.md:80` -/
def impl_UnsafeCellStrategy__check_cells : Item :=
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
        []
        Visibility.inherited
        false
        (Signature.mk
          false
          false
          false
          none
          "check_cells"
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
                    "Result"
                    (PathArguments.angleBracketed false [(GenericArgument.type (Ty.tuple []))]))]))))
        (Block.mk
          [
            (Stmt.letStmt
              []
              (Pat.ident false true "last_end" none)
              (some
                (Expr.path
                  none
                  (Path.mk
                    false
                    [
                      (PathSegment.mk "Size" PathArguments.none),
                      (PathSegment.mk "ZERO" PathArguments.none)])))
              none),
            (Stmt.expr
              (Expr.forLoop
                none
                (Pat.tuple
                  [(Pat.ident false false "start" none), (Pat.ident false false "size" none)])
                (Expr.path none (Path.mk false [(PathSegment.mk "cells" PathArguments.none)]))
                (Block.mk
                  [
                    (Stmt.expr
                      (Expr.tryExpr
                        (Expr.call
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "ensure_wf" PathArguments.none)]))
                          [
                            (Expr.binary
                              (Expr.path
                                none
                                (Path.mk false [(PathSegment.mk "start" PathArguments.none)]))
                              BinOp.ge
                              (Expr.path
                                none
                                (Path.mk false [(PathSegment.mk "last_end" PathArguments.none)]))),
                            (Expr.lit (Lit.str "LayoutStrategy: invalid cells"))]))
                      true),
                    (Stmt.expr
                      (Expr.assign
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "last_end" PathArguments.none)]))
                        (Expr.binary
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "start" PathArguments.none)]))
                          BinOp.add
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "size" PathArguments.none)]))))
                      true)]))
              false),
            (Stmt.expr
              (Expr.tryExpr
                (Expr.call
                  (Expr.path none (Path.mk false [(PathSegment.mk "ensure_wf" PathArguments.none)]))
                  [
                    (Expr.binary
                      (Expr.path
                        none
                        (Path.mk false [(PathSegment.mk "last_end" PathArguments.none)]))
                      BinOp.le
                      (Expr.path none (Path.mk false [(PathSegment.mk "size" PathArguments.none)]))),
                    (Expr.lit (Lit.str "LayoutStrategy: invalid cells"))]))
              true),
            (Stmt.expr
              (Expr.call
                (Expr.path none (Path.mk false [(PathSegment.mk "ret" PathArguments.none)]))
                [(Expr.tuple [])])
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
          "check_wf"
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
              (Pat.ident false false "layout" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "LayoutStrategy" PathArguments.none)])))]
          false
          (some
            (Ty.path
              none
              (Path.mk
                false
                [
                  (PathSegment.mk
                    "Result"
                    (PathArguments.angleBracketed false [(GenericArgument.type (Ty.tuple []))]))]))))
        (Block.mk
          [
            (Stmt.expr
              (Expr.matchExpr
                (Expr.tuple
                  [
                    (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)])),
                    (Expr.path none (Path.mk false [(PathSegment.mk "layout" PathArguments.none)]))])
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
                          [(Pat.ident false false "size" none), Pat.wild])])
                    none
                    (Expr.block
                      none
                      (Block.mk
                        [
                          (Stmt.expr
                            (Expr.tryExpr
                              (Expr.call
                                (Expr.path
                                  none
                                  (Path.mk
                                    false
                                    [
                                      (PathSegment.mk "Self" PathArguments.none),
                                      (PathSegment.mk "check_cells" PathArguments.none)]))
                                [
                                  (Expr.path
                                    none
                                    (Path.mk false [(PathSegment.mk "cells" PathArguments.none)])),
                                  (Expr.path
                                    none
                                    (Path.mk false [(PathSegment.mk "size" PathArguments.none)]))]))
                            true)]))),
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
                          [(Pat.ident false false "size" none), Pat.wild])])
                    none
                    (Expr.block
                      none
                      (Block.mk
                        [
                          (Stmt.expr
                            (Expr.tryExpr
                              (Expr.call
                                (Expr.path
                                  none
                                  (Path.mk
                                    false
                                    [
                                      (PathSegment.mk "Self" PathArguments.none),
                                      (PathSegment.mk "check_cells" PathArguments.none)]))
                                [
                                  (Expr.path
                                    none
                                    (Path.mk
                                      false
                                      [(PathSegment.mk "element_cells" PathArguments.none)])),
                                  (Expr.path
                                    none
                                    (Path.mk false [(PathSegment.mk "size" PathArguments.none)]))]))
                            true)]))),
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
                          [Pat.rest])])
                    none
                    (Expr.block none (Block.mk []))),
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
                          false)])
                    none
                    (Expr.block
                      none
                      (Block.mk
                        [
                          (Stmt.expr
                            (Expr.tryExpr
                              (Expr.call
                                (Expr.path
                                  none
                                  (Path.mk
                                    false
                                    [
                                      (PathSegment.mk "Self" PathArguments.none),
                                      (PathSegment.mk "check_cells" PathArguments.none)]))
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
                            true),
                          (Stmt.expr
                            (Expr.tryExpr
                              (Expr.methodCall
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "tail_cells" PathArguments.none)]))
                                "check_wf"
                                (some
                                  [
                                    (GenericArgument.type
                                      (Ty.path
                                        none
                                        (Path.mk false [(PathSegment.mk "T" PathArguments.none)])))])
                                [
                                  (Expr.path
                                    none
                                    (Path.mk false [(PathSegment.mk "tail" PathArguments.none)]))]))
                            true)]))),
                  (Arm.mk
                    []
                    Pat.wild
                    none
                    (Expr.block
                      none
                      (Block.mk
                        [
                          (Stmt.expr
                            (Expr.tryExpr
                              (Expr.call
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "ensure_wf" PathArguments.none)]))
                                [
                                  (Expr.lit (Lit.bool false)),
                                  (Expr.lit
                                    (Lit.str
                                      "UnsafeCellStrategy and LayoutStrategy variants do not match"))]))
                            true)])))])
              true),
            (Stmt.expr
              (Expr.call
                (Expr.path none (Path.mk false [(PathSegment.mk "ret" PathArguments.none)]))
                [(Expr.tuple [])])
              false)]))])

/-- `spec/lang/well-formed.md:112` -/
def impl_PointeeInfo__check_wf : Item :=
  (Item.impl
    []
    false
    false
    (Generics.mk [] [])
    false
    none
    (Ty.path none (Path.mk false [(PathSegment.mk "PointeeInfo" PathArguments.none)]))
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
          "check_wf"
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
              (Pat.ident false false "prog" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "Program" PathArguments.none)])))]
          false
          (some
            (Ty.path
              none
              (Path.mk
                false
                [
                  (PathSegment.mk
                    "Result"
                    (PathArguments.angleBracketed false [(GenericArgument.type (Ty.tuple []))]))]))))
        (Block.mk
          [
            (Stmt.expr
              (Expr.tryExpr
                (Expr.methodCall
                  (Expr.field
                    (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                    (Member.named "layout"))
                  "check_wf"
                  (some
                    [
                      (GenericArgument.type
                        (Ty.path none (Path.mk false [(PathSegment.mk "T" PathArguments.none)])))])
                  [(Expr.path none (Path.mk false [(PathSegment.mk "prog" PathArguments.none)]))]))
              true),
            (Stmt.expr
              (Expr.tryExpr
                (Expr.methodCall
                  (Expr.field
                    (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                    (Member.named "unsafe_cells"))
                  "check_wf"
                  (some
                    [
                      (GenericArgument.type
                        (Ty.path none (Path.mk false [(PathSegment.mk "T" PathArguments.none)])))])
                  [
                    (Expr.field
                      (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                      (Member.named "layout"))]))
              true),
            (Stmt.expr
              (Expr.call
                (Expr.path none (Path.mk false [(PathSegment.mk "ret" PathArguments.none)]))
                [(Expr.tuple [])])
              false)]))])

/-- `spec/lang/well-formed.md:122` -/
def impl_PtrType__check_wf : Item :=
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
        []
        Visibility.inherited
        false
        (Signature.mk
          false
          false
          false
          none
          "check_wf"
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
              (Pat.ident false false "prog" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "Program" PathArguments.none)])))]
          false
          (some
            (Ty.path
              none
              (Path.mk
                false
                [
                  (PathSegment.mk
                    "Result"
                    (PathArguments.angleBracketed false [(GenericArgument.type (Ty.tuple []))]))]))))
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
                          false)])
                    none
                    (Expr.block
                      none
                      (Block.mk
                        [
                          (Stmt.expr
                            (Expr.tryExpr
                              (Expr.methodCall
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "pointee" PathArguments.none)]))
                                "check_wf"
                                (some
                                  [
                                    (GenericArgument.type
                                      (Ty.path
                                        none
                                        (Path.mk false [(PathSegment.mk "T" PathArguments.none)])))])
                                [
                                  (Expr.path
                                    none
                                    (Path.mk false [(PathSegment.mk "prog" PathArguments.none)]))]))
                            true)]))),
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
                              (PathSegment.mk "FnPtr" PathArguments.none)]))])
                    none
                    (Expr.tuple [])),
                  (Arm.mk
                    []
                    (Pat.tupleStruct
                      none
                      (Path.mk
                        false
                        [
                          (PathSegment.mk "PtrType" PathArguments.none),
                          (PathSegment.mk "VTablePtr" PathArguments.none)])
                      [(Pat.ident false false "trait_name" none)])
                    none
                    (Expr.block
                      none
                      (Block.mk
                        [
                          (Stmt.expr
                            (Expr.tryExpr
                              (Expr.call
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "ensure_wf" PathArguments.none)]))
                                [
                                  (Expr.methodCall
                                    (Expr.field
                                      (Expr.path
                                        none
                                        (Path.mk false [(PathSegment.mk "prog" PathArguments.none)]))
                                      (Member.named "traits"))
                                    "contains_key"
                                    none
                                    [
                                      (Expr.path
                                        none
                                        (Path.mk
                                          false
                                          [(PathSegment.mk "trait_name" PathArguments.none)]))]),
                                  (Expr.lit
                                    (Lit.str "PtrType::VTablePtr: trait name doesn't exist"))]))
                            true)])))])
              false),
            (Stmt.expr
              (Expr.call
                (Expr.path none (Path.mk false [(PathSegment.mk "ret" PathArguments.none)]))
                [(Expr.tuple [])])
              false)]))])

/-- `spec/lang/well-formed.md:138` -/
def impl_Type__check_wf : Item :=
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
        []
        Visibility.inherited
        false
        (Signature.mk
          false
          false
          false
          none
          "check_wf"
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
              (Pat.ident false false "prog" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "Program" PathArguments.none)])))]
          false
          (some
            (Ty.path
              none
              (Path.mk
                false
                [
                  (PathSegment.mk
                    "Result"
                    (PathArguments.angleBracketed false [(GenericArgument.type (Ty.tuple []))]))]))))
        (Block.mk
          [
            (Stmt.item (Item.use [] Visibility.inherited false (UseTree.path "Type" UseTree.glob))),
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
                    (Expr.block
                      none
                      (Block.mk
                        [
                          (Stmt.expr
                            (Expr.tryExpr
                              (Expr.methodCall
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "int_type" PathArguments.none)]))
                                "check_wf"
                                none
                                []))
                            true)]))),
                  (Arm.mk [] (Pat.ident false false "Bool" none) none (Expr.tuple [])),
                  (Arm.mk
                    []
                    (Pat.tupleStruct
                      none
                      (Path.mk false [(PathSegment.mk "Ptr" PathArguments.none)])
                      [(Pat.ident false false "ptr_type" none)])
                    none
                    (Expr.block
                      none
                      (Block.mk
                        [
                          (Stmt.expr
                            (Expr.tryExpr
                              (Expr.methodCall
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "ptr_type" PathArguments.none)]))
                                "check_wf"
                                (some
                                  [
                                    (GenericArgument.type
                                      (Ty.path
                                        none
                                        (Path.mk false [(PathSegment.mk "T" PathArguments.none)])))])
                                [
                                  (Expr.path
                                    none
                                    (Path.mk false [(PathSegment.mk "prog" PathArguments.none)]))]))
                            true)]))),
                  (Arm.mk
                    []
                    (Pat.struct
                      none
                      (Path.mk false [(PathSegment.mk "Tuple" PathArguments.none)])
                      [
                        (FieldPat.mk
                          []
                          (Member.named "sized_fields")
                          true
                          (Pat.ident false true "sized_fields" none)),
                        (FieldPat.mk
                          []
                          (Member.named "unsized_field")
                          true
                          (Pat.ident false false "unsized_field" none)),
                        (FieldPat.mk
                          []
                          (Member.named "sized_head_layout")
                          true
                          (Pat.ident false false "sized_head_layout" none))]
                      false)
                    none
                    (Expr.block
                      none
                      (Block.mk
                        [
                          (Stmt.expr
                            (Expr.methodCall
                              (Expr.path
                                none
                                (Path.mk false [(PathSegment.mk "sized_fields" PathArguments.none)]))
                              "sort_by_key"
                              none
                              [
                                (Expr.closure
                                  false
                                  [
                                    (Pat.tuple
                                      [
                                        (Pat.ident false false "offset" none),
                                        (Pat.ident false false "_ty" none)])]
                                  none
                                  (Expr.path
                                    none
                                    (Path.mk false [(PathSegment.mk "offset" PathArguments.none)])))])
                            true),
                          (Stmt.letStmt
                            []
                            (Pat.ident false true "last_end" none)
                            (some
                              (Expr.path
                                none
                                (Path.mk
                                  false
                                  [
                                    (PathSegment.mk "Size" PathArguments.none),
                                    (PathSegment.mk "ZERO" PathArguments.none)])))
                            none),
                          (Stmt.expr
                            (Expr.forLoop
                              none
                              (Pat.tuple
                                [
                                  (Pat.ident false false "offset" none),
                                  (Pat.ident false false "ty" none)])
                              (Expr.path
                                none
                                (Path.mk false [(PathSegment.mk "sized_fields" PathArguments.none)]))
                              (Block.mk
                                [
                                  (Stmt.expr
                                    (Expr.tryExpr
                                      (Expr.methodCall
                                        (Expr.path
                                          none
                                          (Path.mk false [(PathSegment.mk "ty" PathArguments.none)]))
                                        "check_wf"
                                        (some
                                          [
                                            (GenericArgument.type
                                              (Ty.path
                                                none
                                                (Path.mk
                                                  false
                                                  [(PathSegment.mk "T" PathArguments.none)])))])
                                        [
                                          (Expr.path
                                            none
                                            (Path.mk
                                              false
                                              [(PathSegment.mk "prog" PathArguments.none)]))]))
                                    true),
                                  (Stmt.expr
                                    (Expr.tryExpr
                                      (Expr.call
                                        (Expr.path
                                          none
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "ensure_wf" PathArguments.none)]))
                                        [
                                          (Expr.binary
                                            (Expr.path
                                              none
                                              (Path.mk
                                                false
                                                [(PathSegment.mk "offset" PathArguments.none)]))
                                            BinOp.ge
                                            (Expr.path
                                              none
                                              (Path.mk
                                                false
                                                [(PathSegment.mk "last_end" PathArguments.none)]))),
                                          (Expr.lit (Lit.str "Type::Tuple: overlapping fields"))]))
                                    true),
                                  (Stmt.expr
                                    (Expr.tryExpr
                                      (Expr.call
                                        (Expr.path
                                          none
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "ensure_wf" PathArguments.none)]))
                                        [
                                          (Expr.methodCall
                                            (Expr.methodCall
                                              (Expr.path
                                                none
                                                (Path.mk
                                                  false
                                                  [(PathSegment.mk "ty" PathArguments.none)]))
                                              "layout"
                                              (some
                                                [
                                                  (GenericArgument.type
                                                    (Ty.path
                                                      none
                                                      (Path.mk
                                                        false
                                                        [(PathSegment.mk "T" PathArguments.none)])))])
                                              [])
                                            "is_sized"
                                            none
                                            []),
                                          (Expr.lit
                                            (Lit.str "Type::Tuple: unsized field type in head"))]))
                                    true),
                                  (Stmt.expr
                                    (Expr.assign
                                      (Expr.path
                                        none
                                        (Path.mk
                                          false
                                          [(PathSegment.mk "last_end" PathArguments.none)]))
                                      (Expr.binary
                                        (Expr.path
                                          none
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "offset" PathArguments.none)]))
                                        BinOp.add
                                        (Expr.methodCall
                                          (Expr.methodCall
                                            (Expr.path
                                              none
                                              (Path.mk
                                                false
                                                [(PathSegment.mk "ty" PathArguments.none)]))
                                            "layout"
                                            (some
                                              [
                                                (GenericArgument.type
                                                  (Ty.path
                                                    none
                                                    (Path.mk
                                                      false
                                                      [(PathSegment.mk "T" PathArguments.none)])))])
                                            [])
                                          "expect_size"
                                          none
                                          [(Expr.lit (Lit.str "ensured to be sized above"))])))
                                    true)]))
                            false),
                          (Stmt.expr
                            (Expr.ite
                              (Expr.letCond
                                (Pat.tupleStruct
                                  none
                                  (Path.mk false [(PathSegment.mk "Some" PathArguments.none)])
                                  [(Pat.ident false false "unsized_field" none)])
                                (Expr.path
                                  none
                                  (Path.mk
                                    false
                                    [(PathSegment.mk "unsized_field" PathArguments.none)])))
                              (Block.mk
                                [
                                  (Stmt.expr
                                    (Expr.tryExpr
                                      (Expr.methodCall
                                        (Expr.path
                                          none
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "unsized_field" PathArguments.none)]))
                                        "check_wf"
                                        (some
                                          [
                                            (GenericArgument.type
                                              (Ty.path
                                                none
                                                (Path.mk
                                                  false
                                                  [(PathSegment.mk "T" PathArguments.none)])))])
                                        [
                                          (Expr.path
                                            none
                                            (Path.mk
                                              false
                                              [(PathSegment.mk "prog" PathArguments.none)]))]))
                                    true),
                                  (Stmt.expr
                                    (Expr.tryExpr
                                      (Expr.call
                                        (Expr.path
                                          none
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "ensure_wf" PathArguments.none)]))
                                        [
                                          (Expr.unary
                                            UnOp.not
                                            (Expr.methodCall
                                              (Expr.methodCall
                                                (Expr.path
                                                  none
                                                  (Path.mk
                                                    false
                                                    [
                                                      (PathSegment.mk
                                                        "unsized_field"
                                                        PathArguments.none)]))
                                                "layout"
                                                (some
                                                  [
                                                    (GenericArgument.type
                                                      (Ty.path
                                                        none
                                                        (Path.mk
                                                          false
                                                          [(PathSegment.mk "T" PathArguments.none)])))])
                                                [])
                                              "is_sized"
                                              none
                                              [])),
                                          (Expr.lit
                                            (Lit.str "Type::Tuple: sized unsized field type"))]))
                                    true)])
                              none)
                            false),
                          (Stmt.expr
                            (Expr.tryExpr
                              (Expr.methodCall
                                (Expr.path
                                  none
                                  (Path.mk
                                    false
                                    [(PathSegment.mk "sized_head_layout" PathArguments.none)]))
                                "check_wf"
                                (some
                                  [
                                    (GenericArgument.type
                                      (Ty.path
                                        none
                                        (Path.mk false [(PathSegment.mk "T" PathArguments.none)])))])
                                []))
                            true),
                          (Stmt.expr
                            (Expr.tryExpr
                              (Expr.call
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "ensure_wf" PathArguments.none)]))
                                [
                                  (Expr.binary
                                    (Expr.field
                                      (Expr.path
                                        none
                                        (Path.mk
                                          false
                                          [(PathSegment.mk "sized_head_layout" PathArguments.none)]))
                                      (Member.named "end"))
                                    BinOp.ge
                                    (Expr.path
                                      none
                                      (Path.mk
                                        false
                                        [(PathSegment.mk "last_end" PathArguments.none)]))),
                                  (Expr.lit
                                    (Lit.str
                                      "Type::Tuple: size of fields is bigger than the end of the sized head"))]))
                            true),
                          (Stmt.expr
                            (Expr.ite
                              (Expr.methodCall
                                (Expr.field
                                  (Expr.path
                                    none
                                    (Path.mk
                                      false
                                      [(PathSegment.mk "sized_head_layout" PathArguments.none)]))
                                  (Member.named "packed_align"))
                                "is_some"
                                none
                                [])
                              (Block.mk
                                [
                                  (Stmt.expr
                                    (Expr.tryExpr
                                      (Expr.call
                                        (Expr.path
                                          none
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "ensure_wf" PathArguments.none)]))
                                        [
                                          (Expr.methodCall
                                            (Expr.path
                                              none
                                              (Path.mk
                                                false
                                                [
                                                  (PathSegment.mk
                                                    "unsized_field"
                                                    PathArguments.none)]))
                                            "is_some"
                                            none
                                            []),
                                          (Expr.lit
                                            (Lit.str
                                              "Type::Tuple: meaningless packed align for sized tuple"))]))
                                    true)])
                              none)
                            false)]))),
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
                    (Expr.block
                      none
                      (Block.mk
                        [
                          (Stmt.expr
                            (Expr.tryExpr
                              (Expr.call
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "ensure_wf" PathArguments.none)]))
                                [
                                  (Expr.binary
                                    (Expr.path
                                      none
                                      (Path.mk false [(PathSegment.mk "count" PathArguments.none)]))
                                    BinOp.ge
                                    (Expr.lit (Lit.int 0 ""))),
                                  (Expr.lit (Lit.str "Type::Array: negative amount of elements"))]))
                            true),
                          (Stmt.expr
                            (Expr.tryExpr
                              (Expr.call
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "ensure_wf" PathArguments.none)]))
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
                                              (Path.mk
                                                false
                                                [(PathSegment.mk "T" PathArguments.none)])))])
                                      [])
                                    "is_sized"
                                    none
                                    []),
                                  (Expr.lit (Lit.str "Type::Array: unsized element type"))]))
                            true),
                          (Stmt.expr
                            (Expr.tryExpr
                              (Expr.methodCall
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "elem" PathArguments.none)]))
                                "check_wf"
                                (some
                                  [
                                    (GenericArgument.type
                                      (Ty.path
                                        none
                                        (Path.mk false [(PathSegment.mk "T" PathArguments.none)])))])
                                [
                                  (Expr.path
                                    none
                                    (Path.mk false [(PathSegment.mk "prog" PathArguments.none)]))]))
                            true)]))),
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
                    (Expr.block
                      none
                      (Block.mk
                        [
                          (Stmt.expr
                            (Expr.tryExpr
                              (Expr.call
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "ensure_wf" PathArguments.none)]))
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
                                              (Path.mk
                                                false
                                                [(PathSegment.mk "T" PathArguments.none)])))])
                                      [])
                                    "is_sized"
                                    none
                                    []),
                                  (Expr.lit (Lit.str "Type::Slice: unsized element type"))]))
                            true),
                          (Stmt.expr
                            (Expr.tryExpr
                              (Expr.methodCall
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "elem" PathArguments.none)]))
                                "check_wf"
                                (some
                                  [
                                    (GenericArgument.type
                                      (Ty.path
                                        none
                                        (Path.mk false [(PathSegment.mk "T" PathArguments.none)])))])
                                [
                                  (Expr.path
                                    none
                                    (Path.mk false [(PathSegment.mk "prog" PathArguments.none)]))]))
                            true)]))),
                  (Arm.mk
                    []
                    (Pat.struct
                      none
                      (Path.mk false [(PathSegment.mk "Union" PathArguments.none)])
                      [
                        (FieldPat.mk
                          []
                          (Member.named "fields")
                          true
                          (Pat.ident false false "fields" none)),
                        (FieldPat.mk
                          []
                          (Member.named "size")
                          true
                          (Pat.ident false false "size" none)),
                        (FieldPat.mk
                          []
                          (Member.named "chunks")
                          true
                          (Pat.ident false false "chunks" none)),
                        (FieldPat.mk [] (Member.named "align") false Pat.wild)]
                      false)
                    none
                    (Expr.block
                      none
                      (Block.mk
                        [
                          (Stmt.expr
                            (Expr.forLoop
                              none
                              (Pat.tuple
                                [
                                  (Pat.ident false false "offset" none),
                                  (Pat.ident false false "ty" none)])
                              (Expr.path
                                none
                                (Path.mk false [(PathSegment.mk "fields" PathArguments.none)]))
                              (Block.mk
                                [
                                  (Stmt.expr
                                    (Expr.tryExpr
                                      (Expr.methodCall
                                        (Expr.path
                                          none
                                          (Path.mk false [(PathSegment.mk "ty" PathArguments.none)]))
                                        "check_wf"
                                        (some
                                          [
                                            (GenericArgument.type
                                              (Ty.path
                                                none
                                                (Path.mk
                                                  false
                                                  [(PathSegment.mk "T" PathArguments.none)])))])
                                        [
                                          (Expr.path
                                            none
                                            (Path.mk
                                              false
                                              [(PathSegment.mk "prog" PathArguments.none)]))]))
                                    true),
                                  (Stmt.expr
                                    (Expr.tryExpr
                                      (Expr.call
                                        (Expr.path
                                          none
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "ensure_wf" PathArguments.none)]))
                                        [
                                          (Expr.methodCall
                                            (Expr.methodCall
                                              (Expr.path
                                                none
                                                (Path.mk
                                                  false
                                                  [(PathSegment.mk "ty" PathArguments.none)]))
                                              "layout"
                                              (some
                                                [
                                                  (GenericArgument.type
                                                    (Ty.path
                                                      none
                                                      (Path.mk
                                                        false
                                                        [(PathSegment.mk "T" PathArguments.none)])))])
                                              [])
                                            "is_sized"
                                            none
                                            []),
                                          (Expr.lit (Lit.str "Type::Union: unsized field type"))]))
                                    true),
                                  (Stmt.expr
                                    (Expr.tryExpr
                                      (Expr.call
                                        (Expr.path
                                          none
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "ensure_wf" PathArguments.none)]))
                                        [
                                          (Expr.binary
                                            (Expr.path
                                              none
                                              (Path.mk
                                                false
                                                [(PathSegment.mk "size" PathArguments.none)]))
                                            BinOp.ge
                                            (Expr.binary
                                              (Expr.path
                                                none
                                                (Path.mk
                                                  false
                                                  [(PathSegment.mk "offset" PathArguments.none)]))
                                              BinOp.add
                                              (Expr.methodCall
                                                (Expr.methodCall
                                                  (Expr.path
                                                    none
                                                    (Path.mk
                                                      false
                                                      [(PathSegment.mk "ty" PathArguments.none)]))
                                                  "layout"
                                                  (some
                                                    [
                                                      (GenericArgument.type
                                                        (Ty.path
                                                          none
                                                          (Path.mk
                                                            false
                                                            [
                                                              (PathSegment.mk
                                                                "T"
                                                                PathArguments.none)])))])
                                                  [])
                                                "expect_size"
                                                none
                                                [(Expr.lit (Lit.str "ensured to be sized above"))]))),
                                          (Expr.lit
                                            (Lit.str "Type::Union: field size does not fit union"))]))
                                    true)]))
                            false),
                          (Stmt.letStmt
                            []
                            (Pat.ident false true "last_end" none)
                            (some
                              (Expr.path
                                none
                                (Path.mk
                                  false
                                  [
                                    (PathSegment.mk "Size" PathArguments.none),
                                    (PathSegment.mk "ZERO" PathArguments.none)])))
                            none),
                          (Stmt.expr
                            (Expr.forLoop
                              none
                              (Pat.tuple
                                [
                                  (Pat.ident false false "offset" none),
                                  (Pat.ident false false "size" none)])
                              (Expr.path
                                none
                                (Path.mk false [(PathSegment.mk "chunks" PathArguments.none)]))
                              (Block.mk
                                [
                                  (Stmt.expr
                                    (Expr.tryExpr
                                      (Expr.call
                                        (Expr.path
                                          none
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "ensure_wf" PathArguments.none)]))
                                        [
                                          (Expr.binary
                                            (Expr.path
                                              none
                                              (Path.mk
                                                false
                                                [(PathSegment.mk "offset" PathArguments.none)]))
                                            BinOp.ge
                                            (Expr.path
                                              none
                                              (Path.mk
                                                false
                                                [(PathSegment.mk "last_end" PathArguments.none)]))),
                                          (Expr.lit
                                            (Lit.str
                                              "Type::Union: chunks are not stored in ascending order"))]))
                                    true),
                                  (Stmt.expr
                                    (Expr.assign
                                      (Expr.path
                                        none
                                        (Path.mk
                                          false
                                          [(PathSegment.mk "last_end" PathArguments.none)]))
                                      (Expr.binary
                                        (Expr.path
                                          none
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "offset" PathArguments.none)]))
                                        BinOp.add
                                        (Expr.path
                                          none
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "size" PathArguments.none)]))))
                                    true)]))
                            false),
                          (Stmt.expr
                            (Expr.tryExpr
                              (Expr.call
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "ensure_wf" PathArguments.none)]))
                                [
                                  (Expr.binary
                                    (Expr.path
                                      none
                                      (Path.mk false [(PathSegment.mk "size" PathArguments.none)]))
                                    BinOp.ge
                                    (Expr.path
                                      none
                                      (Path.mk
                                        false
                                        [(PathSegment.mk "last_end" PathArguments.none)]))),
                                  (Expr.lit (Lit.str "Type::Union: chunks do not fit union"))]))
                            true)]))),
                  (Arm.mk
                    []
                    (Pat.struct
                      none
                      (Path.mk false [(PathSegment.mk "Enum" PathArguments.none)])
                      [
                        (FieldPat.mk
                          []
                          (Member.named "variants")
                          true
                          (Pat.ident false false "variants" none)),
                        (FieldPat.mk
                          []
                          (Member.named "size")
                          true
                          (Pat.ident false false "size" none)),
                        (FieldPat.mk
                          []
                          (Member.named "align")
                          true
                          (Pat.ident false false "align" none)),
                        (FieldPat.mk
                          []
                          (Member.named "discriminator")
                          true
                          (Pat.ident false false "discriminator" none)),
                        (FieldPat.mk
                          []
                          (Member.named "discriminant_ty")
                          true
                          (Pat.ident false false "discriminant_ty" none))]
                      false)
                    none
                    (Expr.block
                      none
                      (Block.mk
                        [
                          (Stmt.expr
                            (Expr.forLoop
                              none
                              (Pat.tuple
                                [
                                  (Pat.ident false false "discriminant" none),
                                  (Pat.ident false false "variant" none)])
                              (Expr.path
                                none
                                (Path.mk false [(PathSegment.mk "variants" PathArguments.none)]))
                              (Block.mk
                                [
                                  (Stmt.expr
                                    (Expr.tryExpr
                                      (Expr.call
                                        (Expr.path
                                          none
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "ensure_wf" PathArguments.none)]))
                                        [
                                          (Expr.methodCall
                                            (Expr.path
                                              none
                                              (Path.mk
                                                false
                                                [
                                                  (PathSegment.mk
                                                    "discriminant_ty"
                                                    PathArguments.none)]))
                                            "can_represent"
                                            none
                                            [
                                              (Expr.path
                                                none
                                                (Path.mk
                                                  false
                                                  [
                                                    (PathSegment.mk
                                                      "discriminant"
                                                      PathArguments.none)]))]),
                                          (Expr.lit
                                            (Lit.str "Type::Enum: invalid value for discriminant"))]))
                                    true),
                                  (Stmt.expr
                                    (Expr.tryExpr
                                      (Expr.methodCall
                                        (Expr.field
                                          (Expr.path
                                            none
                                            (Path.mk
                                              false
                                              [(PathSegment.mk "variant" PathArguments.none)]))
                                          (Member.named "ty"))
                                        "check_wf"
                                        (some
                                          [
                                            (GenericArgument.type
                                              (Ty.path
                                                none
                                                (Path.mk
                                                  false
                                                  [(PathSegment.mk "T" PathArguments.none)])))])
                                        [
                                          (Expr.path
                                            none
                                            (Path.mk
                                              false
                                              [(PathSegment.mk "prog" PathArguments.none)]))]))
                                    true),
                                  (Stmt.letStmt
                                    []
                                    (Pat.tupleStruct
                                      none
                                      (Path.mk
                                        false
                                        [
                                          (PathSegment.mk "LayoutStrategy" PathArguments.none),
                                          (PathSegment.mk "Sized" PathArguments.none)])
                                      [
                                        (Pat.ident false false "var_size" none),
                                        (Pat.ident false false "var_align" none)])
                                    (some
                                      (Expr.methodCall
                                        (Expr.field
                                          (Expr.path
                                            none
                                            (Path.mk
                                              false
                                              [(PathSegment.mk "variant" PathArguments.none)]))
                                          (Member.named "ty"))
                                        "layout"
                                        (some
                                          [
                                            (GenericArgument.type
                                              (Ty.path
                                                none
                                                (Path.mk
                                                  false
                                                  [(PathSegment.mk "T" PathArguments.none)])))])
                                        []))
                                    (some
                                      (Expr.block
                                        none
                                        (Block.mk
                                          [
                                            (Stmt.expr
                                              (Expr.macro
                                                (Macro.mk
                                                  (Path.mk
                                                    false
                                                    [
                                                      (PathSegment.mk
                                                        "throw_ill_formed"
                                                        PathArguments.none)])
                                                  MacroDelimiter.paren
                                                  (MacroBody.exprs
                                                    [
                                                      (Expr.lit
                                                        (Lit.str
                                                          "Type::Enum: variant type is unsized"))]
                                                    false)))
                                              false)])))),
                                  (Stmt.expr
                                    (Expr.tryExpr
                                      (Expr.call
                                        (Expr.path
                                          none
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "ensure_wf" PathArguments.none)]))
                                        [
                                          (Expr.binary
                                            (Expr.path
                                              none
                                              (Path.mk
                                                false
                                                [(PathSegment.mk "var_size" PathArguments.none)]))
                                            BinOp.eq
                                            (Expr.path
                                              none
                                              (Path.mk
                                                false
                                                [(PathSegment.mk "size" PathArguments.none)]))),
                                          (Expr.lit
                                            (Lit.str
                                              "Type::Enum: variant size is not the same as enum size"))]))
                                    true),
                                  (Stmt.expr
                                    (Expr.tryExpr
                                      (Expr.call
                                        (Expr.path
                                          none
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "ensure_wf" PathArguments.none)]))
                                        [
                                          (Expr.binary
                                            (Expr.path
                                              none
                                              (Path.mk
                                                false
                                                [(PathSegment.mk "var_align" PathArguments.none)]))
                                            BinOp.le
                                            (Expr.path
                                              none
                                              (Path.mk
                                                false
                                                [(PathSegment.mk "align" PathArguments.none)]))),
                                          (Expr.lit
                                            (Lit.str "Type::Enum: invalid align requirement"))]))
                                    true),
                                  (Stmt.expr
                                    (Expr.forLoop
                                      none
                                      (Pat.tuple
                                        [
                                          (Pat.ident false false "offset" none),
                                          (Pat.tuple
                                            [
                                              (Pat.ident false false "value_type" none),
                                              (Pat.ident false false "value" none)])])
                                      (Expr.field
                                        (Expr.path
                                          none
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "variant" PathArguments.none)]))
                                        (Member.named "tagger"))
                                      (Block.mk
                                        [
                                          (Stmt.expr
                                            (Expr.tryExpr
                                              (Expr.methodCall
                                                (Expr.path
                                                  none
                                                  (Path.mk
                                                    false
                                                    [
                                                      (PathSegment.mk
                                                        "value_type"
                                                        PathArguments.none)]))
                                                "check_wf"
                                                none
                                                []))
                                            true),
                                          (Stmt.expr
                                            (Expr.tryExpr
                                              (Expr.call
                                                (Expr.path
                                                  none
                                                  (Path.mk
                                                    false
                                                    [
                                                      (PathSegment.mk
                                                        "ensure_wf"
                                                        PathArguments.none)]))
                                                [
                                                  (Expr.methodCall
                                                    (Expr.path
                                                      none
                                                      (Path.mk
                                                        false
                                                        [
                                                          (PathSegment.mk
                                                            "value_type"
                                                            PathArguments.none)]))
                                                    "can_represent"
                                                    none
                                                    [
                                                      (Expr.path
                                                        none
                                                        (Path.mk
                                                          false
                                                          [
                                                            (PathSegment.mk
                                                              "value"
                                                              PathArguments.none)]))]),
                                                  (Expr.lit
                                                    (Lit.str "Type::Enum: invalid tagger value"))]))
                                            true),
                                          (Stmt.expr
                                            (Expr.tryExpr
                                              (Expr.call
                                                (Expr.path
                                                  none
                                                  (Path.mk
                                                    false
                                                    [
                                                      (PathSegment.mk
                                                        "ensure_wf"
                                                        PathArguments.none)]))
                                                [
                                                  (Expr.binary
                                                    (Expr.binary
                                                      (Expr.path
                                                        none
                                                        (Path.mk
                                                          false
                                                          [
                                                            (PathSegment.mk
                                                              "offset"
                                                              PathArguments.none)]))
                                                      BinOp.add
                                                      (Expr.field
                                                        (Expr.path
                                                          none
                                                          (Path.mk
                                                            false
                                                            [
                                                              (PathSegment.mk
                                                                "value_type"
                                                                PathArguments.none)]))
                                                        (Member.named "size")))
                                                    BinOp.le
                                                    (Expr.path
                                                      none
                                                      (Path.mk
                                                        false
                                                        [(PathSegment.mk "size" PathArguments.none)]))),
                                                  (Expr.lit
                                                    (Lit.str
                                                      "Type::Enum tagger type size too big for enum"))]))
                                            true)]))
                                    false)]))
                            false),
                          (Stmt.expr
                            (Expr.tryExpr
                              (Expr.methodCall
                                (Expr.path
                                  none
                                  (Path.mk
                                    false
                                    [(PathSegment.mk "discriminator" PathArguments.none)]))
                                "check_wf"
                                (some
                                  [
                                    (GenericArgument.type
                                      (Ty.path
                                        none
                                        (Path.mk false [(PathSegment.mk "T" PathArguments.none)])))])
                                [
                                  (Expr.path
                                    none
                                    (Path.mk false [(PathSegment.mk "size" PathArguments.none)])),
                                  (Expr.path
                                    none
                                    (Path.mk false [(PathSegment.mk "variants" PathArguments.none)]))]))
                            true)]))),
                  (Arm.mk
                    []
                    (Pat.tupleStruct
                      none
                      (Path.mk false [(PathSegment.mk "TraitObject" PathArguments.none)])
                      [(Pat.ident false false "trait_name" none)])
                    none
                    (Expr.block
                      none
                      (Block.mk
                        [
                          (Stmt.expr
                            (Expr.tryExpr
                              (Expr.call
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "ensure_wf" PathArguments.none)]))
                                [
                                  (Expr.methodCall
                                    (Expr.field
                                      (Expr.path
                                        none
                                        (Path.mk false [(PathSegment.mk "prog" PathArguments.none)]))
                                      (Member.named "traits"))
                                    "contains_key"
                                    none
                                    [
                                      (Expr.path
                                        none
                                        (Path.mk
                                          false
                                          [(PathSegment.mk "trait_name" PathArguments.none)]))]),
                                  (Expr.lit (Lit.str "Type::TraitObject: trait name doesn't exist"))]))
                            true)])))])
              false),
            (Stmt.letStmt
              []
              (Pat.ident false false "layout" none)
              (some
                (Expr.methodCall
                  (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                  "layout"
                  (some
                    [
                      (GenericArgument.type
                        (Ty.path none (Path.mk false [(PathSegment.mk "T" PathArguments.none)])))])
                  []))
              none),
            (Stmt.expr
              (Expr.tryExpr
                (Expr.methodCall
                  (Expr.path none (Path.mk false [(PathSegment.mk "layout" PathArguments.none)]))
                  "check_wf"
                  (some
                    [
                      (GenericArgument.type
                        (Ty.path none (Path.mk false [(PathSegment.mk "T" PathArguments.none)])))])
                  [(Expr.path none (Path.mk false [(PathSegment.mk "prog" PathArguments.none)]))]))
              true),
            (Stmt.expr
              (Expr.tryExpr
                (Expr.methodCall
                  (Expr.path none (Path.mk false [(PathSegment.mk "layout" PathArguments.none)]))
                  "check_aligned"
                  none
                  []))
              true),
            (Stmt.macro
              []
              (Macro.mk
                (Path.mk false [(PathSegment.mk "assert_eq" PathArguments.none)])
                MacroDelimiter.paren
                (MacroBody.exprs
                  [
                    (Expr.methodCall
                      (Expr.path
                        none
                        (Path.mk false [(PathSegment.mk "layout" PathArguments.none)]))
                      "meta_kind"
                      none
                      []),
                    (Expr.methodCall
                      (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                      "meta_kind"
                      none
                      []),
                    (Expr.lit (Lit.str "Type::meta_kind() must match the Type::layout()'s kind"))]
                  false))
              true),
            (Stmt.expr
              (Expr.call
                (Expr.path none (Path.mk false [(PathSegment.mk "ret" PathArguments.none)]))
                [(Expr.tuple [])])
              false)]))])

/-- `spec/lang/well-formed.md:262` -/
def impl_Discriminator__check_wf : Item :=
  (Item.impl
    []
    false
    false
    (Generics.mk [] [])
    false
    none
    (Ty.path none (Path.mk false [(PathSegment.mk "Discriminator" PathArguments.none)]))
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
          "check_wf"
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
              (Pat.ident false false "size" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "Size" PathArguments.none)]))),
            (FnArg.typed
              []
              (Pat.ident false false "variants" none)
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
                              (Path.mk false [(PathSegment.mk "Variant" PathArguments.none)])))]))])))]
          false
          (some
            (Ty.path
              none
              (Path.mk
                false
                [
                  (PathSegment.mk
                    "Result"
                    (PathArguments.angleBracketed false [(GenericArgument.type (Ty.tuple []))]))]))))
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
                          (PathSegment.mk "Discriminator" PathArguments.none),
                          (PathSegment.mk "Known" PathArguments.none)])
                      [(Pat.ident false false "discriminant" none)])
                    none
                    (Expr.call
                      (Expr.path
                        none
                        (Path.mk false [(PathSegment.mk "ensure_wf" PathArguments.none)]))
                      [
                        (Expr.methodCall
                          (Expr.methodCall
                            (Expr.path
                              none
                              (Path.mk false [(PathSegment.mk "variants" PathArguments.none)]))
                            "get"
                            none
                            [
                              (Expr.path
                                none
                                (Path.mk false [(PathSegment.mk "discriminant" PathArguments.none)]))])
                          "is_some"
                          none
                          []),
                        (Expr.lit (Lit.str "Discriminator: invalid discriminant"))])),
                  (Arm.mk
                    []
                    (Pat.path
                      none
                      (Path.mk
                        false
                        [
                          (PathSegment.mk "Discriminator" PathArguments.none),
                          (PathSegment.mk "Invalid" PathArguments.none)]))
                    none
                    (Expr.call
                      (Expr.path none (Path.mk false [(PathSegment.mk "ret" PathArguments.none)]))
                      [(Expr.tuple [])])),
                  (Arm.mk
                    []
                    (Pat.struct
                      none
                      (Path.mk
                        false
                        [
                          (PathSegment.mk "Discriminator" PathArguments.none),
                          (PathSegment.mk "Branch" PathArguments.none)])
                      [
                        (FieldPat.mk
                          []
                          (Member.named "offset")
                          true
                          (Pat.ident false false "offset" none)),
                        (FieldPat.mk
                          []
                          (Member.named "value_type")
                          true
                          (Pat.ident false false "value_type" none)),
                        (FieldPat.mk
                          []
                          (Member.named "fallback")
                          true
                          (Pat.ident false false "fallback" none)),
                        (FieldPat.mk
                          []
                          (Member.named "children")
                          true
                          (Pat.ident false false "children" none))]
                      false)
                    none
                    (Expr.block
                      none
                      (Block.mk
                        [
                          (Stmt.expr
                            (Expr.tryExpr
                              (Expr.methodCall
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "value_type" PathArguments.none)]))
                                "check_wf"
                                none
                                []))
                            true),
                          (Stmt.expr
                            (Expr.tryExpr
                              (Expr.call
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "ensure_wf" PathArguments.none)]))
                                [
                                  (Expr.binary
                                    (Expr.binary
                                      (Expr.path
                                        none
                                        (Path.mk
                                          false
                                          [(PathSegment.mk "offset" PathArguments.none)]))
                                      BinOp.add
                                      (Expr.field
                                        (Expr.path
                                          none
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "value_type" PathArguments.none)]))
                                        (Member.named "size")))
                                    BinOp.le
                                    (Expr.path
                                      none
                                      (Path.mk false [(PathSegment.mk "size" PathArguments.none)]))),
                                  (Expr.lit (Lit.str "Discriminator: branch offset exceeds size"))]))
                            true),
                          (Stmt.expr
                            (Expr.tryExpr
                              (Expr.methodCall
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "fallback" PathArguments.none)]))
                                "check_wf"
                                (some
                                  [
                                    (GenericArgument.type
                                      (Ty.path
                                        none
                                        (Path.mk false [(PathSegment.mk "T" PathArguments.none)])))])
                                [
                                  (Expr.path
                                    none
                                    (Path.mk false [(PathSegment.mk "size" PathArguments.none)])),
                                  (Expr.path
                                    none
                                    (Path.mk false [(PathSegment.mk "variants" PathArguments.none)]))]))
                            true),
                          (Stmt.expr
                            (Expr.forLoop
                              none
                              (Pat.tuple
                                [
                                  (Pat.ident false false "idx" none),
                                  (Pat.tuple
                                    [
                                      (Pat.tuple
                                        [
                                          (Pat.ident false false "start" none),
                                          (Pat.ident false false "end" none)]),
                                      (Pat.ident false false "discriminator" none)])])
                              (Expr.methodCall
                                (Expr.methodCall
                                  (Expr.path
                                    none
                                    (Path.mk false [(PathSegment.mk "children" PathArguments.none)]))
                                  "into_iter"
                                  none
                                  [])
                                "enumerate"
                                none
                                [])
                              (Block.mk
                                [
                                  (Stmt.expr
                                    (Expr.tryExpr
                                      (Expr.call
                                        (Expr.path
                                          none
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "ensure_wf" PathArguments.none)]))
                                        [
                                          (Expr.methodCall
                                            (Expr.path
                                              none
                                              (Path.mk
                                                false
                                                [(PathSegment.mk "value_type" PathArguments.none)]))
                                            "can_represent"
                                            none
                                            [
                                              (Expr.path
                                                none
                                                (Path.mk
                                                  false
                                                  [(PathSegment.mk "start" PathArguments.none)]))]),
                                          (Expr.lit
                                            (Lit.str "Discriminator: invalid branch start bound"))]))
                                    true),
                                  (Stmt.expr
                                    (Expr.tryExpr
                                      (Expr.call
                                        (Expr.path
                                          none
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "ensure_wf" PathArguments.none)]))
                                        [
                                          (Expr.methodCall
                                            (Expr.path
                                              none
                                              (Path.mk
                                                false
                                                [(PathSegment.mk "value_type" PathArguments.none)]))
                                            "can_represent"
                                            none
                                            [
                                              (Expr.binary
                                                (Expr.path
                                                  none
                                                  (Path.mk
                                                    false
                                                    [(PathSegment.mk "end" PathArguments.none)]))
                                                BinOp.sub
                                                (Expr.path
                                                  none
                                                  (Path.mk
                                                    false
                                                    [
                                                      (PathSegment.mk "Int" PathArguments.none),
                                                      (PathSegment.mk "ONE" PathArguments.none)])))]),
                                          (Expr.lit
                                            (Lit.str "Discriminator: invalid branch end bound"))]))
                                    true),
                                  (Stmt.expr
                                    (Expr.tryExpr
                                      (Expr.call
                                        (Expr.path
                                          none
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "ensure_wf" PathArguments.none)]))
                                        [
                                          (Expr.binary
                                            (Expr.path
                                              none
                                              (Path.mk
                                                false
                                                [(PathSegment.mk "start" PathArguments.none)]))
                                            BinOp.lt
                                            (Expr.path
                                              none
                                              (Path.mk
                                                false
                                                [(PathSegment.mk "end" PathArguments.none)]))),
                                          (Expr.lit (Lit.str "Discriminator: invalid bound values"))]))
                                    true),
                                  (Stmt.expr
                                    (Expr.tryExpr
                                      (Expr.call
                                        (Expr.path
                                          none
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "ensure_wf" PathArguments.none)]))
                                        [
                                          (Expr.methodCall
                                            (Expr.methodCall
                                              (Expr.methodCall
                                                (Expr.path
                                                  none
                                                  (Path.mk
                                                    false
                                                    [(PathSegment.mk "children" PathArguments.none)]))
                                                "keys"
                                                none
                                                [])
                                              "enumerate"
                                              none
                                              [])
                                            "all"
                                            none
                                            [
                                              (Expr.closure
                                                false
                                                [
                                                  (Pat.tuple
                                                    [
                                                      (Pat.ident false false "other_idx" none),
                                                      (Pat.tuple
                                                        [
                                                          (Pat.ident false false "other_start" none),
                                                          (Pat.ident false false "other_end" none)])])]
                                                none
                                                (Expr.binary
                                                  (Expr.binary
                                                    (Expr.binary
                                                      (Expr.path
                                                        none
                                                        (Path.mk
                                                          false
                                                          [
                                                            (PathSegment.mk
                                                              "other_end"
                                                              PathArguments.none)]))
                                                      BinOp.le
                                                      (Expr.path
                                                        none
                                                        (Path.mk
                                                          false
                                                          [
                                                            (PathSegment.mk
                                                              "start"
                                                              PathArguments.none)])))
                                                    BinOp.or
                                                    (Expr.binary
                                                      (Expr.path
                                                        none
                                                        (Path.mk
                                                          false
                                                          [
                                                            (PathSegment.mk
                                                              "other_start"
                                                              PathArguments.none)]))
                                                      BinOp.ge
                                                      (Expr.path
                                                        none
                                                        (Path.mk
                                                          false
                                                          [
                                                            (PathSegment.mk
                                                              "end"
                                                              PathArguments.none)]))))
                                                  BinOp.or
                                                  (Expr.binary
                                                    (Expr.path
                                                      none
                                                      (Path.mk
                                                        false
                                                        [(PathSegment.mk "idx" PathArguments.none)]))
                                                    BinOp.eq
                                                    (Expr.path
                                                      none
                                                      (Path.mk
                                                        false
                                                        [
                                                          (PathSegment.mk
                                                            "other_idx"
                                                            PathArguments.none)])))))]),
                                          (Expr.lit
                                            (Lit.str "Discriminator: branch ranges overlap"))]))
                                    true),
                                  (Stmt.expr
                                    (Expr.tryExpr
                                      (Expr.methodCall
                                        (Expr.path
                                          none
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "discriminator" PathArguments.none)]))
                                        "check_wf"
                                        (some
                                          [
                                            (GenericArgument.type
                                              (Ty.path
                                                none
                                                (Path.mk
                                                  false
                                                  [(PathSegment.mk "T" PathArguments.none)])))])
                                        [
                                          (Expr.path
                                            none
                                            (Path.mk
                                              false
                                              [(PathSegment.mk "size" PathArguments.none)])),
                                          (Expr.path
                                            none
                                            (Path.mk
                                              false
                                              [(PathSegment.mk "variants" PathArguments.none)]))]))
                                    true)]))
                            false),
                          (Stmt.expr
                            (Expr.call
                              (Expr.path
                                none
                                (Path.mk false [(PathSegment.mk "ret" PathArguments.none)]))
                              [(Expr.tuple [])])
                            false)])))])
              false)]))])

/-- `spec/lang/well-formed.md:292` -/
def impl_Constant__check_wf : Item :=
  (Item.impl
    []
    false
    false
    (Generics.mk [] [])
    false
    none
    (Ty.path none (Path.mk false [(PathSegment.mk "Constant" PathArguments.none)]))
    [
      (ImplItem.fn
        [
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue " Check that the constant has the expected type.")),
          (Attr.mk true "doc" (AttrMeta.nameValue " Assumes that `ty` has already been checked."))]
        Visibility.inherited
        false
        (Signature.mk
          false
          false
          false
          none
          "check_wf"
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
              (Pat.ident false false "ty" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "Type" PathArguments.none)]))),
            (FnArg.typed
              []
              (Pat.ident false false "prog" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "Program" PathArguments.none)])))]
          false
          (some
            (Ty.path
              none
              (Path.mk
                false
                [
                  (PathSegment.mk
                    "Result"
                    (PathArguments.angleBracketed false [(GenericArgument.type (Ty.tuple []))]))]))))
        (Block.mk
          [
            (Stmt.expr
              (Expr.matchExpr
                (Expr.tuple
                  [
                    (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)])),
                    (Expr.path none (Path.mk false [(PathSegment.mk "ty" PathArguments.none)]))])
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
                              (PathSegment.mk "Constant" PathArguments.none),
                              (PathSegment.mk "Int" PathArguments.none)])
                          [(Pat.ident false false "i" none)]),
                        (Pat.tupleStruct
                          none
                          (Path.mk
                            false
                            [
                              (PathSegment.mk "Type" PathArguments.none),
                              (PathSegment.mk "Int" PathArguments.none)])
                          [(Pat.ident false false "int_type" none)])])
                    none
                    (Expr.block
                      none
                      (Block.mk
                        [
                          (Stmt.expr
                            (Expr.tryExpr
                              (Expr.call
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "ensure_wf" PathArguments.none)]))
                                [
                                  (Expr.methodCall
                                    (Expr.path
                                      none
                                      (Path.mk
                                        false
                                        [(PathSegment.mk "int_type" PathArguments.none)]))
                                    "can_represent"
                                    none
                                    [
                                      (Expr.path
                                        none
                                        (Path.mk false [(PathSegment.mk "i" PathArguments.none)]))]),
                                  (Expr.lit (Lit.str "Constant::Int: invalid int value"))]))
                            true)]))),
                  (Arm.mk
                    []
                    (Pat.tuple
                      [
                        (Pat.tupleStruct
                          none
                          (Path.mk
                            false
                            [
                              (PathSegment.mk "Constant" PathArguments.none),
                              (PathSegment.mk "Bool" PathArguments.none)])
                          [Pat.wild]),
                        (Pat.path
                          none
                          (Path.mk
                            false
                            [
                              (PathSegment.mk "Type" PathArguments.none),
                              (PathSegment.mk "Bool" PathArguments.none)]))])
                    none
                    (Expr.tuple [])),
                  (Arm.mk
                    []
                    (Pat.tuple
                      [
                        (Pat.tupleStruct
                          none
                          (Path.mk
                            false
                            [
                              (PathSegment.mk "Constant" PathArguments.none),
                              (PathSegment.mk "GlobalPointer" PathArguments.none)])
                          [(Pat.ident false false "relocation" none)]),
                        (Pat.tupleStruct
                          none
                          (Path.mk
                            false
                            [
                              (PathSegment.mk "Type" PathArguments.none),
                              (PathSegment.mk "Ptr" PathArguments.none)])
                          [Pat.wild])])
                    none
                    (Expr.block
                      none
                      (Block.mk
                        [
                          (Stmt.expr
                            (Expr.tryExpr
                              (Expr.methodCall
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "relocation" PathArguments.none)]))
                                "check_wf"
                                none
                                [
                                  (Expr.field
                                    (Expr.path
                                      none
                                      (Path.mk false [(PathSegment.mk "prog" PathArguments.none)]))
                                    (Member.named "globals"))]))
                            true)]))),
                  (Arm.mk
                    []
                    (Pat.tuple
                      [
                        (Pat.tupleStruct
                          none
                          (Path.mk
                            false
                            [
                              (PathSegment.mk "Constant" PathArguments.none),
                              (PathSegment.mk "FnPointer" PathArguments.none)])
                          [(Pat.ident false false "fn_name" none)]),
                        (Pat.tupleStruct
                          none
                          (Path.mk
                            false
                            [
                              (PathSegment.mk "Type" PathArguments.none),
                              (PathSegment.mk "Ptr" PathArguments.none)])
                          [(Pat.ident false false "ptr_ty" none)])])
                    none
                    (Expr.block
                      none
                      (Block.mk
                        [
                          (Stmt.expr
                            (Expr.tryExpr
                              (Expr.call
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "ensure_wf" PathArguments.none)]))
                                [
                                  (Expr.macro
                                    (Macro.mk
                                      (Path.mk
                                        false
                                        [(PathSegment.mk "matches" PathArguments.none)])
                                      MacroDelimiter.paren
                                      (MacroBody.exprAndPat
                                        (Expr.path
                                          none
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "ptr_ty" PathArguments.none)]))
                                        (Pat.path
                                          none
                                          (Path.mk
                                            false
                                            [
                                              (PathSegment.mk "PtrType" PathArguments.none),
                                              (PathSegment.mk "FnPtr" PathArguments.none)]))
                                        none))),
                                  (Expr.lit
                                    (Lit.str "Constant::FnPointer: non function pointer type"))]))
                            true),
                          (Stmt.expr
                            (Expr.tryExpr
                              (Expr.call
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "ensure_wf" PathArguments.none)]))
                                [
                                  (Expr.methodCall
                                    (Expr.field
                                      (Expr.path
                                        none
                                        (Path.mk false [(PathSegment.mk "prog" PathArguments.none)]))
                                      (Member.named "functions"))
                                    "contains_key"
                                    none
                                    [
                                      (Expr.path
                                        none
                                        (Path.mk
                                          false
                                          [(PathSegment.mk "fn_name" PathArguments.none)]))]),
                                  (Expr.lit (Lit.str "Constant::FnPointer: invalid function name"))]))
                            true)]))),
                  (Arm.mk
                    []
                    (Pat.tuple
                      [
                        (Pat.tupleStruct
                          none
                          (Path.mk
                            false
                            [
                              (PathSegment.mk "Constant" PathArguments.none),
                              (PathSegment.mk "VTablePointer" PathArguments.none)])
                          [(Pat.ident false false "vtable_name" none)]),
                        (Pat.tupleStruct
                          none
                          (Path.mk
                            false
                            [
                              (PathSegment.mk "Type" PathArguments.none),
                              (PathSegment.mk "Ptr" PathArguments.none)])
                          [(Pat.ident false false "ptr_ty" none)])])
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
                              [(Pat.ident false false "vtable" none)])
                            (some
                              (Expr.methodCall
                                (Expr.field
                                  (Expr.path
                                    none
                                    (Path.mk false [(PathSegment.mk "prog" PathArguments.none)]))
                                  (Member.named "vtables"))
                                "get"
                                none
                                [
                                  (Expr.path
                                    none
                                    (Path.mk
                                      false
                                      [(PathSegment.mk "vtable_name" PathArguments.none)]))]))
                            (some
                              (Expr.block
                                none
                                (Block.mk
                                  [
                                    (Stmt.macro
                                      []
                                      (Macro.mk
                                        (Path.mk
                                          false
                                          [(PathSegment.mk "throw_ill_formed" PathArguments.none)])
                                        MacroDelimiter.paren
                                        (MacroBody.exprs
                                          [
                                            (Expr.lit
                                              (Lit.str
                                                "Constant::VTablePointer: invalid vtable name"))]
                                          false))
                                      true)])))),
                          (Stmt.expr
                            (Expr.tryExpr
                              (Expr.call
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "ensure_wf" PathArguments.none)]))
                                [
                                  (Expr.binary
                                    (Expr.path
                                      none
                                      (Path.mk false [(PathSegment.mk "ptr_ty" PathArguments.none)]))
                                    BinOp.eq
                                    (Expr.call
                                      (Expr.path
                                        none
                                        (Path.mk
                                          false
                                          [
                                            (PathSegment.mk "PtrType" PathArguments.none),
                                            (PathSegment.mk "VTablePtr" PathArguments.none)]))
                                      [
                                        (Expr.field
                                          (Expr.path
                                            none
                                            (Path.mk
                                              false
                                              [(PathSegment.mk "vtable" PathArguments.none)]))
                                          (Member.named "trait_name"))])),
                                  (Expr.lit
                                    (Lit.str
                                      "Constant::VTablePointer: non or wrong vtable pointer type"))]))
                            true)]))),
                  (Arm.mk
                    []
                    (Pat.tuple
                      [
                        (Pat.tupleStruct
                          none
                          (Path.mk
                            false
                            [
                              (PathSegment.mk "Constant" PathArguments.none),
                              (PathSegment.mk "PointerWithoutProvenance" PathArguments.none)])
                          [(Pat.ident false false "addr" none)]),
                        (Pat.tupleStruct
                          none
                          (Path.mk
                            false
                            [
                              (PathSegment.mk "Type" PathArguments.none),
                              (PathSegment.mk "Ptr" PathArguments.none)])
                          [Pat.wild])])
                    none
                    (Expr.block
                      none
                      (Block.mk
                        [
                          (Stmt.expr
                            (Expr.tryExpr
                              (Expr.call
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "ensure_wf" PathArguments.none)]))
                                [
                                  (Expr.methodCall
                                    (Expr.path
                                      none
                                      (Path.mk false [(PathSegment.mk "addr" PathArguments.none)]))
                                    "in_bounds"
                                    none
                                    [
                                      (Expr.path
                                        none
                                        (Path.mk
                                          false
                                          [
                                            (PathSegment.mk "Signedness" PathArguments.none),
                                            (PathSegment.mk "Unsigned" PathArguments.none)])),
                                      (Expr.path
                                        none
                                        (Path.mk
                                          false
                                          [
                                            (PathSegment.mk "T" PathArguments.none),
                                            (PathSegment.mk "PTR_SIZE" PathArguments.none)]))]),
                                  (Expr.lit
                                    (Lit.str
                                      "Constant::PointerWithoutProvenance: pointer out-of-bounds"))]))
                            true)]))),
                  (Arm.mk
                    []
                    Pat.wild
                    none
                    (Expr.macro
                      (Macro.mk
                        (Path.mk false [(PathSegment.mk "throw_ill_formed" PathArguments.none)])
                        MacroDelimiter.paren
                        (MacroBody.exprs
                          [(Expr.lit (Lit.str "Constant: value does not match type"))]
                          false))))])
              false),
            (Stmt.expr
              (Expr.call
                (Expr.path none (Path.mk false [(PathSegment.mk "ret" PathArguments.none)]))
                [(Expr.tuple [])])
              false)]))])

/-- `spec/lang/well-formed.md:329` -/
def impl_ValueExpr__check_wf : Item :=
  (Item.impl
    []
    false
    false
    (Generics.mk [] [])
    false
    none
    (Ty.path none (Path.mk false [(PathSegment.mk "ValueExpr" PathArguments.none)]))
    [
      (ImplItem.fn
        [(Attr.mk true "allow" (AttrMeta.list "unused_braces"))]
        Visibility.inherited
        false
        (Signature.mk
          false
          false
          false
          none
          "check_wf"
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
              (Pat.ident false false "locals" none)
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
                              (Path.mk false [(PathSegment.mk "Type" PathArguments.none)])))]))]))),
            (FnArg.typed
              []
              (Pat.ident false false "prog" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "Program" PathArguments.none)])))]
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
                            (Path.mk false [(PathSegment.mk "Type" PathArguments.none)])))]))]))))
        (Block.mk
          [
            (Stmt.item
              (Item.use [] Visibility.inherited false (UseTree.path "ValueExpr" UseTree.glob))),
            (Stmt.expr
              (Expr.call
                (Expr.path none (Path.mk false [(PathSegment.mk "ret" PathArguments.none)]))
                [
                  (Expr.matchExpr
                    (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                    [
                      (Arm.mk
                        []
                        (Pat.tupleStruct
                          none
                          (Path.mk false [(PathSegment.mk "Constant" PathArguments.none)])
                          [(Pat.ident false false "value" none), (Pat.ident false false "ty" none)])
                        none
                        (Expr.block
                          none
                          (Block.mk
                            [
                              (Stmt.expr
                                (Expr.tryExpr
                                  (Expr.methodCall
                                    (Expr.path
                                      none
                                      (Path.mk false [(PathSegment.mk "ty" PathArguments.none)]))
                                    "check_wf"
                                    (some
                                      [
                                        (GenericArgument.type
                                          (Ty.path
                                            none
                                            (Path.mk
                                              false
                                              [(PathSegment.mk "T" PathArguments.none)])))])
                                    [
                                      (Expr.path
                                        none
                                        (Path.mk false [(PathSegment.mk "prog" PathArguments.none)]))]))
                                true),
                              (Stmt.expr
                                (Expr.tryExpr
                                  (Expr.methodCall
                                    (Expr.path
                                      none
                                      (Path.mk false [(PathSegment.mk "value" PathArguments.none)]))
                                    "check_wf"
                                    (some
                                      [
                                        (GenericArgument.type
                                          (Ty.path
                                            none
                                            (Path.mk
                                              false
                                              [(PathSegment.mk "T" PathArguments.none)])))])
                                    [
                                      (Expr.path
                                        none
                                        (Path.mk false [(PathSegment.mk "ty" PathArguments.none)])),
                                      (Expr.path
                                        none
                                        (Path.mk false [(PathSegment.mk "prog" PathArguments.none)]))]))
                                true),
                              (Stmt.expr
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "ty" PathArguments.none)]))
                                false)]))),
                      (Arm.mk
                        []
                        (Pat.tupleStruct
                          none
                          (Path.mk false [(PathSegment.mk "Tuple" PathArguments.none)])
                          [(Pat.ident false false "exprs" none), (Pat.ident false false "t" none)])
                        none
                        (Expr.block
                          none
                          (Block.mk
                            [
                              (Stmt.expr
                                (Expr.tryExpr
                                  (Expr.methodCall
                                    (Expr.path
                                      none
                                      (Path.mk false [(PathSegment.mk "t" PathArguments.none)]))
                                    "check_wf"
                                    (some
                                      [
                                        (GenericArgument.type
                                          (Ty.path
                                            none
                                            (Path.mk
                                              false
                                              [(PathSegment.mk "T" PathArguments.none)])))])
                                    [
                                      (Expr.path
                                        none
                                        (Path.mk false [(PathSegment.mk "prog" PathArguments.none)]))]))
                                true),
                              (Stmt.expr
                                (Expr.matchExpr
                                  (Expr.path
                                    none
                                    (Path.mk false [(PathSegment.mk "t" PathArguments.none)]))
                                  [
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
                                            (Member.named "sized_fields")
                                            true
                                            (Pat.ident false false "sized_fields" none)),
                                          (FieldPat.mk
                                            []
                                            (Member.named "unsized_field")
                                            true
                                            (Pat.ident false false "unsized_field" none))]
                                        true)
                                      none
                                      (Expr.block
                                        none
                                        (Block.mk
                                          [
                                            (Stmt.expr
                                              (Expr.tryExpr
                                                (Expr.call
                                                  (Expr.path
                                                    none
                                                    (Path.mk
                                                      false
                                                      [
                                                        (PathSegment.mk
                                                          "ensure_wf"
                                                          PathArguments.none)]))
                                                  [
                                                    (Expr.methodCall
                                                      (Expr.path
                                                        none
                                                        (Path.mk
                                                          false
                                                          [
                                                            (PathSegment.mk
                                                              "unsized_field"
                                                              PathArguments.none)]))
                                                      "is_none"
                                                      none
                                                      []),
                                                    (Expr.lit
                                                      (Lit.str
                                                        "ValueExpr::Tuple: constructing an unsized tuple value"))]))
                                              true),
                                            (Stmt.expr
                                              (Expr.tryExpr
                                                (Expr.call
                                                  (Expr.path
                                                    none
                                                    (Path.mk
                                                      false
                                                      [
                                                        (PathSegment.mk
                                                          "ensure_wf"
                                                          PathArguments.none)]))
                                                  [
                                                    (Expr.binary
                                                      (Expr.methodCall
                                                        (Expr.path
                                                          none
                                                          (Path.mk
                                                            false
                                                            [
                                                              (PathSegment.mk
                                                                "exprs"
                                                                PathArguments.none)]))
                                                        "len"
                                                        none
                                                        [])
                                                      BinOp.eq
                                                      (Expr.methodCall
                                                        (Expr.path
                                                          none
                                                          (Path.mk
                                                            false
                                                            [
                                                              (PathSegment.mk
                                                                "sized_fields"
                                                                PathArguments.none)]))
                                                        "len"
                                                        none
                                                        [])),
                                                    (Expr.lit
                                                      (Lit.str
                                                        "ValueExpr::Tuple: invalid number of tuple fields"))]))
                                              true),
                                            (Stmt.expr
                                              (Expr.forLoop
                                                none
                                                (Pat.tuple
                                                  [
                                                    (Pat.ident false false "e" none),
                                                    (Pat.tuple
                                                      [
                                                        (Pat.ident false false "_offset" none),
                                                        (Pat.ident false false "ty" none)])])
                                                (Expr.methodCall
                                                  (Expr.path
                                                    none
                                                    (Path.mk
                                                      false
                                                      [(PathSegment.mk "exprs" PathArguments.none)]))
                                                  "zip"
                                                  none
                                                  [
                                                    (Expr.path
                                                      none
                                                      (Path.mk
                                                        false
                                                        [
                                                          (PathSegment.mk
                                                            "sized_fields"
                                                            PathArguments.none)]))])
                                                (Block.mk
                                                  [
                                                    (Stmt.letStmt
                                                      []
                                                      (Pat.ident false false "checked" none)
                                                      (some
                                                        (Expr.tryExpr
                                                          (Expr.methodCall
                                                            (Expr.path
                                                              none
                                                              (Path.mk
                                                                false
                                                                [
                                                                  (PathSegment.mk
                                                                    "e"
                                                                    PathArguments.none)]))
                                                            "check_wf"
                                                            (some
                                                              [
                                                                (GenericArgument.type
                                                                  (Ty.path
                                                                    none
                                                                    (Path.mk
                                                                      false
                                                                      [
                                                                        (PathSegment.mk
                                                                          "T"
                                                                          PathArguments.none)])))])
                                                            [
                                                              (Expr.path
                                                                none
                                                                (Path.mk
                                                                  false
                                                                  [
                                                                    (PathSegment.mk
                                                                      "locals"
                                                                      PathArguments.none)])),
                                                              (Expr.path
                                                                none
                                                                (Path.mk
                                                                  false
                                                                  [
                                                                    (PathSegment.mk
                                                                      "prog"
                                                                      PathArguments.none)]))])))
                                                      none),
                                                    (Stmt.expr
                                                      (Expr.tryExpr
                                                        (Expr.call
                                                          (Expr.path
                                                            none
                                                            (Path.mk
                                                              false
                                                              [
                                                                (PathSegment.mk
                                                                  "ensure_wf"
                                                                  PathArguments.none)]))
                                                          [
                                                            (Expr.binary
                                                              (Expr.path
                                                                none
                                                                (Path.mk
                                                                  false
                                                                  [
                                                                    (PathSegment.mk
                                                                      "checked"
                                                                      PathArguments.none)]))
                                                              BinOp.eq
                                                              (Expr.path
                                                                none
                                                                (Path.mk
                                                                  false
                                                                  [
                                                                    (PathSegment.mk
                                                                      "ty"
                                                                      PathArguments.none)]))),
                                                            (Expr.lit
                                                              (Lit.str
                                                                "ValueExpr::Tuple: invalid tuple field type"))]))
                                                      true)]))
                                              false)]))),
                                    (Arm.mk
                                      []
                                      (Pat.struct
                                        none
                                        (Path.mk
                                          false
                                          [
                                            (PathSegment.mk "Type" PathArguments.none),
                                            (PathSegment.mk "Array" PathArguments.none)])
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
                                      (Expr.block
                                        none
                                        (Block.mk
                                          [
                                            (Stmt.expr
                                              (Expr.tryExpr
                                                (Expr.call
                                                  (Expr.path
                                                    none
                                                    (Path.mk
                                                      false
                                                      [
                                                        (PathSegment.mk
                                                          "ensure_wf"
                                                          PathArguments.none)]))
                                                  [
                                                    (Expr.binary
                                                      (Expr.methodCall
                                                        (Expr.path
                                                          none
                                                          (Path.mk
                                                            false
                                                            [
                                                              (PathSegment.mk
                                                                "exprs"
                                                                PathArguments.none)]))
                                                        "len"
                                                        none
                                                        [])
                                                      BinOp.eq
                                                      (Expr.path
                                                        none
                                                        (Path.mk
                                                          false
                                                          [
                                                            (PathSegment.mk
                                                              "count"
                                                              PathArguments.none)]))),
                                                    (Expr.lit
                                                      (Lit.str
                                                        "ValueExpr::Tuple: invalid number of array elements"))]))
                                              true),
                                            (Stmt.expr
                                              (Expr.forLoop
                                                none
                                                (Pat.ident false false "e" none)
                                                (Expr.path
                                                  none
                                                  (Path.mk
                                                    false
                                                    [(PathSegment.mk "exprs" PathArguments.none)]))
                                                (Block.mk
                                                  [
                                                    (Stmt.letStmt
                                                      []
                                                      (Pat.ident false false "checked" none)
                                                      (some
                                                        (Expr.tryExpr
                                                          (Expr.methodCall
                                                            (Expr.path
                                                              none
                                                              (Path.mk
                                                                false
                                                                [
                                                                  (PathSegment.mk
                                                                    "e"
                                                                    PathArguments.none)]))
                                                            "check_wf"
                                                            (some
                                                              [
                                                                (GenericArgument.type
                                                                  (Ty.path
                                                                    none
                                                                    (Path.mk
                                                                      false
                                                                      [
                                                                        (PathSegment.mk
                                                                          "T"
                                                                          PathArguments.none)])))])
                                                            [
                                                              (Expr.path
                                                                none
                                                                (Path.mk
                                                                  false
                                                                  [
                                                                    (PathSegment.mk
                                                                      "locals"
                                                                      PathArguments.none)])),
                                                              (Expr.path
                                                                none
                                                                (Path.mk
                                                                  false
                                                                  [
                                                                    (PathSegment.mk
                                                                      "prog"
                                                                      PathArguments.none)]))])))
                                                      none),
                                                    (Stmt.expr
                                                      (Expr.tryExpr
                                                        (Expr.call
                                                          (Expr.path
                                                            none
                                                            (Path.mk
                                                              false
                                                              [
                                                                (PathSegment.mk
                                                                  "ensure_wf"
                                                                  PathArguments.none)]))
                                                          [
                                                            (Expr.binary
                                                              (Expr.path
                                                                none
                                                                (Path.mk
                                                                  false
                                                                  [
                                                                    (PathSegment.mk
                                                                      "checked"
                                                                      PathArguments.none)]))
                                                              BinOp.eq
                                                              (Expr.path
                                                                none
                                                                (Path.mk
                                                                  false
                                                                  [
                                                                    (PathSegment.mk
                                                                      "elem"
                                                                      PathArguments.none)]))),
                                                            (Expr.lit
                                                              (Lit.str
                                                                "ValueExpr::Tuple: invalid array element type"))]))
                                                      true)]))
                                              false)]))),
                                    (Arm.mk
                                      []
                                      Pat.wild
                                      none
                                      (Expr.macro
                                        (Macro.mk
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "throw_ill_formed" PathArguments.none)])
                                          MacroDelimiter.paren
                                          (MacroBody.exprs
                                            [
                                              (Expr.lit
                                                (Lit.str
                                                  "ValueExpr::Tuple: expression does not match type"))]
                                            false))))])
                                false),
                              (Stmt.expr
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "t" PathArguments.none)]))
                                false)]))),
                      (Arm.mk
                        []
                        (Pat.struct
                          none
                          (Path.mk false [(PathSegment.mk "Union" PathArguments.none)])
                          [
                            (FieldPat.mk
                              []
                              (Member.named "field")
                              true
                              (Pat.ident false false "field" none)),
                            (FieldPat.mk
                              []
                              (Member.named "expr")
                              true
                              (Pat.ident false false "expr" none)),
                            (FieldPat.mk
                              []
                              (Member.named "union_ty")
                              true
                              (Pat.ident false false "union_ty" none))]
                          false)
                        none
                        (Expr.block
                          none
                          (Block.mk
                            [
                              (Stmt.expr
                                (Expr.tryExpr
                                  (Expr.methodCall
                                    (Expr.path
                                      none
                                      (Path.mk
                                        false
                                        [(PathSegment.mk "union_ty" PathArguments.none)]))
                                    "check_wf"
                                    (some
                                      [
                                        (GenericArgument.type
                                          (Ty.path
                                            none
                                            (Path.mk
                                              false
                                              [(PathSegment.mk "T" PathArguments.none)])))])
                                    [
                                      (Expr.path
                                        none
                                        (Path.mk false [(PathSegment.mk "prog" PathArguments.none)]))]))
                                true),
                              (Stmt.letStmt
                                []
                                (Pat.struct
                                  none
                                  (Path.mk
                                    false
                                    [
                                      (PathSegment.mk "Type" PathArguments.none),
                                      (PathSegment.mk "Union" PathArguments.none)])
                                  [
                                    (FieldPat.mk
                                      []
                                      (Member.named "fields")
                                      true
                                      (Pat.ident false false "fields" none))]
                                  true)
                                (some
                                  (Expr.path
                                    none
                                    (Path.mk false [(PathSegment.mk "union_ty" PathArguments.none)])))
                                (some
                                  (Expr.block
                                    none
                                    (Block.mk
                                      [
                                        (Stmt.expr
                                          (Expr.macro
                                            (Macro.mk
                                              (Path.mk
                                                false
                                                [
                                                  (PathSegment.mk
                                                    "throw_ill_formed"
                                                    PathArguments.none)])
                                              MacroDelimiter.paren
                                              (MacroBody.exprs
                                                [
                                                  (Expr.lit
                                                    (Lit.str "ValueExpr::Union: invalid type"))]
                                                false)))
                                          false)])))),
                              (Stmt.expr
                                (Expr.tryExpr
                                  (Expr.call
                                    (Expr.path
                                      none
                                      (Path.mk
                                        false
                                        [(PathSegment.mk "ensure_wf" PathArguments.none)]))
                                    [
                                      (Expr.binary
                                        (Expr.path
                                          none
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "field" PathArguments.none)]))
                                        BinOp.lt
                                        (Expr.methodCall
                                          (Expr.path
                                            none
                                            (Path.mk
                                              false
                                              [(PathSegment.mk "fields" PathArguments.none)]))
                                          "len"
                                          none
                                          [])),
                                      (Expr.lit (Lit.str "ValueExpr::Union: invalid field length"))]))
                                true),
                              (Stmt.letStmt
                                []
                                (Pat.tuple
                                  [
                                    (Pat.ident false false "_offset" none),
                                    (Pat.ident false false "ty" none)])
                                (some
                                  (Expr.index
                                    (Expr.path
                                      none
                                      (Path.mk false [(PathSegment.mk "fields" PathArguments.none)]))
                                    (Expr.path
                                      none
                                      (Path.mk false [(PathSegment.mk "field" PathArguments.none)]))))
                                none),
                              (Stmt.letStmt
                                []
                                (Pat.ident false false "checked" none)
                                (some
                                  (Expr.tryExpr
                                    (Expr.methodCall
                                      (Expr.path
                                        none
                                        (Path.mk false [(PathSegment.mk "expr" PathArguments.none)]))
                                      "check_wf"
                                      (some
                                        [
                                          (GenericArgument.type
                                            (Ty.path
                                              none
                                              (Path.mk
                                                false
                                                [(PathSegment.mk "T" PathArguments.none)])))])
                                      [
                                        (Expr.path
                                          none
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "locals" PathArguments.none)])),
                                        (Expr.path
                                          none
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "prog" PathArguments.none)]))])))
                                none),
                              (Stmt.expr
                                (Expr.tryExpr
                                  (Expr.call
                                    (Expr.path
                                      none
                                      (Path.mk
                                        false
                                        [(PathSegment.mk "ensure_wf" PathArguments.none)]))
                                    [
                                      (Expr.binary
                                        (Expr.path
                                          none
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "checked" PathArguments.none)]))
                                        BinOp.eq
                                        (Expr.path
                                          none
                                          (Path.mk false [(PathSegment.mk "ty" PathArguments.none)]))),
                                      (Expr.lit (Lit.str "ValueExpr::Union: invalid field type"))]))
                                true),
                              (Stmt.expr
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "union_ty" PathArguments.none)]))
                                false)]))),
                      (Arm.mk
                        []
                        (Pat.struct
                          none
                          (Path.mk false [(PathSegment.mk "Variant" PathArguments.none)])
                          [
                            (FieldPat.mk
                              []
                              (Member.named "discriminant")
                              true
                              (Pat.ident false false "discriminant" none)),
                            (FieldPat.mk
                              []
                              (Member.named "data")
                              true
                              (Pat.ident false false "data" none)),
                            (FieldPat.mk
                              []
                              (Member.named "enum_ty")
                              true
                              (Pat.ident false false "enum_ty" none))]
                          false)
                        none
                        (Expr.block
                          none
                          (Block.mk
                            [
                              (Stmt.letStmt
                                []
                                (Pat.struct
                                  none
                                  (Path.mk
                                    false
                                    [
                                      (PathSegment.mk "Type" PathArguments.none),
                                      (PathSegment.mk "Enum" PathArguments.none)])
                                  [
                                    (FieldPat.mk
                                      []
                                      (Member.named "variants")
                                      true
                                      (Pat.ident false false "variants" none))]
                                  true)
                                (some
                                  (Expr.path
                                    none
                                    (Path.mk false [(PathSegment.mk "enum_ty" PathArguments.none)])))
                                (some
                                  (Expr.block
                                    none
                                    (Block.mk
                                      [
                                        (Stmt.expr
                                          (Expr.macro
                                            (Macro.mk
                                              (Path.mk
                                                false
                                                [
                                                  (PathSegment.mk
                                                    "throw_ill_formed"
                                                    PathArguments.none)])
                                              MacroDelimiter.paren
                                              (MacroBody.exprs
                                                [
                                                  (Expr.lit
                                                    (Lit.str "ValueExpr::Variant: invalid type"))]
                                                false)))
                                          false)])))),
                              (Stmt.expr
                                (Expr.tryExpr
                                  (Expr.methodCall
                                    (Expr.path
                                      none
                                      (Path.mk
                                        false
                                        [(PathSegment.mk "enum_ty" PathArguments.none)]))
                                    "check_wf"
                                    (some
                                      [
                                        (GenericArgument.type
                                          (Ty.path
                                            none
                                            (Path.mk
                                              false
                                              [(PathSegment.mk "T" PathArguments.none)])))])
                                    [
                                      (Expr.path
                                        none
                                        (Path.mk false [(PathSegment.mk "prog" PathArguments.none)]))]))
                                true),
                              (Stmt.letStmt
                                []
                                (Pat.tupleStruct
                                  none
                                  (Path.mk false [(PathSegment.mk "Some" PathArguments.none)])
                                  [(Pat.ident false false "variant" none)])
                                (some
                                  (Expr.methodCall
                                    (Expr.path
                                      none
                                      (Path.mk
                                        false
                                        [(PathSegment.mk "variants" PathArguments.none)]))
                                    "get"
                                    none
                                    [
                                      (Expr.path
                                        none
                                        (Path.mk
                                          false
                                          [(PathSegment.mk "discriminant" PathArguments.none)]))]))
                                (some
                                  (Expr.block
                                    none
                                    (Block.mk
                                      [
                                        (Stmt.macro
                                          []
                                          (Macro.mk
                                            (Path.mk
                                              false
                                              [
                                                (PathSegment.mk
                                                  "throw_ill_formed"
                                                  PathArguments.none)])
                                            MacroDelimiter.paren
                                            (MacroBody.exprs
                                              [
                                                (Expr.lit
                                                  (Lit.str
                                                    "ValueExpr::Variant: invalid discriminant"))]
                                              false))
                                          true)])))),
                              (Stmt.letStmt
                                []
                                (Pat.ident false false "checked" none)
                                (some
                                  (Expr.tryExpr
                                    (Expr.methodCall
                                      (Expr.path
                                        none
                                        (Path.mk false [(PathSegment.mk "data" PathArguments.none)]))
                                      "check_wf"
                                      (some
                                        [
                                          (GenericArgument.type
                                            (Ty.path
                                              none
                                              (Path.mk
                                                false
                                                [(PathSegment.mk "T" PathArguments.none)])))])
                                      [
                                        (Expr.path
                                          none
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "locals" PathArguments.none)])),
                                        (Expr.path
                                          none
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "prog" PathArguments.none)]))])))
                                none),
                              (Stmt.expr
                                (Expr.tryExpr
                                  (Expr.call
                                    (Expr.path
                                      none
                                      (Path.mk
                                        false
                                        [(PathSegment.mk "ensure_wf" PathArguments.none)]))
                                    [
                                      (Expr.binary
                                        (Expr.path
                                          none
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "checked" PathArguments.none)]))
                                        BinOp.eq
                                        (Expr.field
                                          (Expr.path
                                            none
                                            (Path.mk
                                              false
                                              [(PathSegment.mk "variant" PathArguments.none)]))
                                          (Member.named "ty"))),
                                      (Expr.lit (Lit.str "ValueExpr::Variant: invalid type"))]))
                                true),
                              (Stmt.expr
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "enum_ty" PathArguments.none)]))
                                false)]))),
                      (Arm.mk
                        []
                        (Pat.struct
                          none
                          (Path.mk false [(PathSegment.mk "GetDiscriminant" PathArguments.none)])
                          [
                            (FieldPat.mk
                              []
                              (Member.named "place")
                              true
                              (Pat.ident false false "place" none))]
                          false)
                        none
                        (Expr.block
                          none
                          (Block.mk
                            [
                              (Stmt.letStmt
                                []
                                (Pat.struct
                                  none
                                  (Path.mk
                                    false
                                    [
                                      (PathSegment.mk "Type" PathArguments.none),
                                      (PathSegment.mk "Enum" PathArguments.none)])
                                  [
                                    (FieldPat.mk
                                      []
                                      (Member.named "discriminant_ty")
                                      true
                                      (Pat.ident false false "discriminant_ty" none))]
                                  true)
                                (some
                                  (Expr.tryExpr
                                    (Expr.methodCall
                                      (Expr.path
                                        none
                                        (Path.mk
                                          false
                                          [(PathSegment.mk "place" PathArguments.none)]))
                                      "check_wf"
                                      (some
                                        [
                                          (GenericArgument.type
                                            (Ty.path
                                              none
                                              (Path.mk
                                                false
                                                [(PathSegment.mk "T" PathArguments.none)])))])
                                      [
                                        (Expr.path
                                          none
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "locals" PathArguments.none)])),
                                        (Expr.path
                                          none
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "prog" PathArguments.none)]))])))
                                (some
                                  (Expr.block
                                    none
                                    (Block.mk
                                      [
                                        (Stmt.macro
                                          []
                                          (Macro.mk
                                            (Path.mk
                                              false
                                              [
                                                (PathSegment.mk
                                                  "throw_ill_formed"
                                                  PathArguments.none)])
                                            MacroDelimiter.paren
                                            (MacroBody.exprs
                                              [
                                                (Expr.lit
                                                  (Lit.str
                                                    "ValueExpr::GetDiscriminant: invalid type"))]
                                              false))
                                          true)])))),
                              (Stmt.expr
                                (Expr.call
                                  (Expr.path
                                    none
                                    (Path.mk
                                      false
                                      [
                                        (PathSegment.mk "Type" PathArguments.none),
                                        (PathSegment.mk "Int" PathArguments.none)]))
                                  [
                                    (Expr.path
                                      none
                                      (Path.mk
                                        false
                                        [(PathSegment.mk "discriminant_ty" PathArguments.none)]))])
                                false)]))),
                      (Arm.mk
                        []
                        (Pat.struct
                          none
                          (Path.mk false [(PathSegment.mk "Load" PathArguments.none)])
                          [
                            (FieldPat.mk
                              []
                              (Member.named "source")
                              true
                              (Pat.ident false false "source" none))]
                          false)
                        none
                        (Expr.block
                          none
                          (Block.mk
                            [
                              (Stmt.letStmt
                                []
                                (Pat.ident false false "val_ty" none)
                                (some
                                  (Expr.tryExpr
                                    (Expr.methodCall
                                      (Expr.path
                                        none
                                        (Path.mk
                                          false
                                          [(PathSegment.mk "source" PathArguments.none)]))
                                      "check_wf"
                                      (some
                                        [
                                          (GenericArgument.type
                                            (Ty.path
                                              none
                                              (Path.mk
                                                false
                                                [(PathSegment.mk "T" PathArguments.none)])))])
                                      [
                                        (Expr.path
                                          none
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "locals" PathArguments.none)])),
                                        (Expr.path
                                          none
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "prog" PathArguments.none)]))])))
                                none),
                              (Stmt.expr
                                (Expr.tryExpr
                                  (Expr.call
                                    (Expr.path
                                      none
                                      (Path.mk
                                        false
                                        [(PathSegment.mk "ensure_wf" PathArguments.none)]))
                                    [
                                      (Expr.methodCall
                                        (Expr.methodCall
                                          (Expr.path
                                            none
                                            (Path.mk
                                              false
                                              [(PathSegment.mk "val_ty" PathArguments.none)]))
                                          "layout"
                                          (some
                                            [
                                              (GenericArgument.type
                                                (Ty.path
                                                  none
                                                  (Path.mk
                                                    false
                                                    [(PathSegment.mk "T" PathArguments.none)])))])
                                          [])
                                        "is_sized"
                                        none
                                        []),
                                      (Expr.lit (Lit.str "ValueExpr::Load: unsized value type"))]))
                                true),
                              (Stmt.expr
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "val_ty" PathArguments.none)]))
                                false)]))),
                      (Arm.mk
                        []
                        (Pat.struct
                          none
                          (Path.mk false [(PathSegment.mk "AddrOf" PathArguments.none)])
                          [
                            (FieldPat.mk
                              []
                              (Member.named "target")
                              true
                              (Pat.ident false false "target" none)),
                            (FieldPat.mk
                              []
                              (Member.named "ptr_ty")
                              true
                              (Pat.ident false false "ptr_ty" none))]
                          false)
                        none
                        (Expr.block
                          none
                          (Block.mk
                            [
                              (Stmt.expr
                                (Expr.tryExpr
                                  (Expr.methodCall
                                    (Expr.path
                                      none
                                      (Path.mk false [(PathSegment.mk "ptr_ty" PathArguments.none)]))
                                    "check_wf"
                                    (some
                                      [
                                        (GenericArgument.type
                                          (Ty.path
                                            none
                                            (Path.mk
                                              false
                                              [(PathSegment.mk "T" PathArguments.none)])))])
                                    [
                                      (Expr.path
                                        none
                                        (Path.mk false [(PathSegment.mk "prog" PathArguments.none)]))]))
                                true),
                              (Stmt.letStmt
                                []
                                (Pat.ident false false "target_ty" none)
                                (some
                                  (Expr.tryExpr
                                    (Expr.methodCall
                                      (Expr.path
                                        none
                                        (Path.mk
                                          false
                                          [(PathSegment.mk "target" PathArguments.none)]))
                                      "check_wf"
                                      (some
                                        [
                                          (GenericArgument.type
                                            (Ty.path
                                              none
                                              (Path.mk
                                                false
                                                [(PathSegment.mk "T" PathArguments.none)])))])
                                      [
                                        (Expr.path
                                          none
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "locals" PathArguments.none)])),
                                        (Expr.path
                                          none
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "prog" PathArguments.none)]))])))
                                none),
                              (Stmt.expr
                                (Expr.tryExpr
                                  (Expr.call
                                    (Expr.path
                                      none
                                      (Path.mk
                                        false
                                        [(PathSegment.mk "ensure_wf" PathArguments.none)]))
                                    [
                                      (Expr.binary
                                        (Expr.methodCall
                                          (Expr.path
                                            none
                                            (Path.mk
                                              false
                                              [(PathSegment.mk "target_ty" PathArguments.none)]))
                                          "meta_kind"
                                          none
                                          [])
                                        BinOp.eq
                                        (Expr.methodCall
                                          (Expr.path
                                            none
                                            (Path.mk
                                              false
                                              [(PathSegment.mk "ptr_ty" PathArguments.none)]))
                                          "meta_kind"
                                          none
                                          [])),
                                      (Expr.lit
                                        (Lit.str "ValueExpr::AddrOf: mismatched metadata kind"))]))
                                true),
                              (Stmt.expr
                                (Expr.call
                                  (Expr.path
                                    none
                                    (Path.mk
                                      false
                                      [
                                        (PathSegment.mk "Type" PathArguments.none),
                                        (PathSegment.mk "Ptr" PathArguments.none)]))
                                  [
                                    (Expr.path
                                      none
                                      (Path.mk false [(PathSegment.mk "ptr_ty" PathArguments.none)]))])
                                false)]))),
                      (Arm.mk
                        []
                        (Pat.struct
                          none
                          (Path.mk false [(PathSegment.mk "UnOp" PathArguments.none)])
                          [
                            (FieldPat.mk
                              []
                              (Member.named "operator")
                              true
                              (Pat.ident false false "operator" none)),
                            (FieldPat.mk
                              []
                              (Member.named "operand")
                              true
                              (Pat.ident false false "operand" none))]
                          false)
                        none
                        (Expr.block
                          none
                          (Block.mk
                            [
                              (Stmt.item
                                (Item.use
                                  []
                                  Visibility.inherited
                                  false
                                  (UseTree.path "lang" (UseTree.path "UnOp" UseTree.glob)))),
                              (Stmt.letStmt
                                []
                                (Pat.ident false false "operand" none)
                                (some
                                  (Expr.tryExpr
                                    (Expr.methodCall
                                      (Expr.path
                                        none
                                        (Path.mk
                                          false
                                          [(PathSegment.mk "operand" PathArguments.none)]))
                                      "check_wf"
                                      (some
                                        [
                                          (GenericArgument.type
                                            (Ty.path
                                              none
                                              (Path.mk
                                                false
                                                [(PathSegment.mk "T" PathArguments.none)])))])
                                      [
                                        (Expr.path
                                          none
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "locals" PathArguments.none)])),
                                        (Expr.path
                                          none
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "prog" PathArguments.none)]))])))
                                none),
                              (Stmt.expr
                                (Expr.matchExpr
                                  (Expr.path
                                    none
                                    (Path.mk false [(PathSegment.mk "operator" PathArguments.none)]))
                                  [
                                    (Arm.mk
                                      []
                                      (Pat.tupleStruct
                                        none
                                        (Path.mk false [(PathSegment.mk "Int" PathArguments.none)])
                                        [(Pat.ident false false "int_op" none)])
                                      none
                                      (Expr.block
                                        none
                                        (Block.mk
                                          [
                                            (Stmt.letStmt
                                              []
                                              (Pat.tupleStruct
                                                none
                                                (Path.mk
                                                  false
                                                  [
                                                    (PathSegment.mk "Type" PathArguments.none),
                                                    (PathSegment.mk "Int" PathArguments.none)])
                                                [(Pat.ident false false "int_ty" none)])
                                              (some
                                                (Expr.path
                                                  none
                                                  (Path.mk
                                                    false
                                                    [(PathSegment.mk "operand" PathArguments.none)])))
                                              (some
                                                (Expr.block
                                                  none
                                                  (Block.mk
                                                    [
                                                      (Stmt.macro
                                                        []
                                                        (Macro.mk
                                                          (Path.mk
                                                            false
                                                            [
                                                              (PathSegment.mk
                                                                "throw_ill_formed"
                                                                PathArguments.none)])
                                                          MacroDelimiter.paren
                                                          (MacroBody.exprs
                                                            [
                                                              (Expr.lit
                                                                (Lit.str
                                                                  "UnOp::Int: invalid operand"))]
                                                            false))
                                                        true)])))),
                                            (Stmt.letStmt
                                              []
                                              (Pat.ident false false "ret_ty" none)
                                              (some
                                                (Expr.matchExpr
                                                  (Expr.path
                                                    none
                                                    (Path.mk
                                                      false
                                                      [(PathSegment.mk "int_op" PathArguments.none)]))
                                                  [
                                                    (Arm.mk
                                                      []
                                                      (Pat.path
                                                        none
                                                        (Path.mk
                                                          false
                                                          [
                                                            (PathSegment.mk
                                                              "IntUnOp"
                                                              PathArguments.none),
                                                            (PathSegment.mk
                                                              "CountOnes"
                                                              PathArguments.none)]))
                                                      none
                                                      (Expr.struct
                                                        none
                                                        (Path.mk
                                                          false
                                                          [
                                                            (PathSegment.mk
                                                              "IntType"
                                                              PathArguments.none)])
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
                                                                  (PathSegment.mk
                                                                    "Unsigned"
                                                                    PathArguments.none)]))),
                                                          (FieldValue.mk
                                                            []
                                                            (Member.named "size")
                                                            false
                                                            (Expr.methodCall
                                                              (Expr.call
                                                                (Expr.path
                                                                  none
                                                                  (Path.mk
                                                                    false
                                                                    [
                                                                      (PathSegment.mk
                                                                        "Size"
                                                                        PathArguments.none),
                                                                      (PathSegment.mk
                                                                        "from_bytes"
                                                                        PathArguments.none)]))
                                                                [(Expr.lit (Lit.int 4 ""))])
                                                              "unwrap"
                                                              none
                                                              []))]
                                                        false
                                                        none)),
                                                    (Arm.mk
                                                      []
                                                      Pat.wild
                                                      none
                                                      (Expr.path
                                                        none
                                                        (Path.mk
                                                          false
                                                          [
                                                            (PathSegment.mk
                                                              "int_ty"
                                                              PathArguments.none)])))]))
                                              none),
                                            (Stmt.expr
                                              (Expr.call
                                                (Expr.path
                                                  none
                                                  (Path.mk
                                                    false
                                                    [
                                                      (PathSegment.mk "Type" PathArguments.none),
                                                      (PathSegment.mk "Int" PathArguments.none)]))
                                                [
                                                  (Expr.path
                                                    none
                                                    (Path.mk
                                                      false
                                                      [(PathSegment.mk "ret_ty" PathArguments.none)]))])
                                              false)]))),
                                    (Arm.mk
                                      []
                                      (Pat.tupleStruct
                                        none
                                        (Path.mk false [(PathSegment.mk "Cast" PathArguments.none)])
                                        [(Pat.ident false false "cast_op" none)])
                                      none
                                      (Expr.block
                                        none
                                        (Block.mk
                                          [
                                            (Stmt.item
                                              (Item.use
                                                []
                                                Visibility.inherited
                                                false
                                                (UseTree.path
                                                  "lang"
                                                  (UseTree.path "CastOp" UseTree.glob)))),
                                            (Stmt.expr
                                              (Expr.matchExpr
                                                (Expr.path
                                                  none
                                                  (Path.mk
                                                    false
                                                    [(PathSegment.mk "cast_op" PathArguments.none)]))
                                                [
                                                  (Arm.mk
                                                    []
                                                    (Pat.tupleStruct
                                                      none
                                                      (Path.mk
                                                        false
                                                        [
                                                          (PathSegment.mk
                                                            "IntToInt"
                                                            PathArguments.none)])
                                                      [(Pat.ident false false "int_ty" none)])
                                                    none
                                                    (Expr.block
                                                      none
                                                      (Block.mk
                                                        [
                                                          (Stmt.expr
                                                            (Expr.tryExpr
                                                              (Expr.call
                                                                (Expr.path
                                                                  none
                                                                  (Path.mk
                                                                    false
                                                                    [
                                                                      (PathSegment.mk
                                                                        "ensure_wf"
                                                                        PathArguments.none)]))
                                                                [
                                                                  (Expr.macro
                                                                    (Macro.mk
                                                                      (Path.mk
                                                                        false
                                                                        [
                                                                          (PathSegment.mk
                                                                            "matches"
                                                                            PathArguments.none)])
                                                                      MacroDelimiter.paren
                                                                      (MacroBody.exprAndPat
                                                                        (Expr.path
                                                                          none
                                                                          (Path.mk
                                                                            false
                                                                            [
                                                                              (PathSegment.mk
                                                                                "operand"
                                                                                PathArguments.none)]))
                                                                        (Pat.tupleStruct
                                                                          none
                                                                          (Path.mk
                                                                            false
                                                                            [
                                                                              (PathSegment.mk
                                                                                "Type"
                                                                                PathArguments.none),
                                                                              (PathSegment.mk
                                                                                "Int"
                                                                                PathArguments.none)])
                                                                          [Pat.wild])
                                                                        none))),
                                                                  (Expr.lit
                                                                    (Lit.str
                                                                      "Cast::IntToInt: invalid operand"))]))
                                                            true),
                                                          (Stmt.expr
                                                            (Expr.call
                                                              (Expr.path
                                                                none
                                                                (Path.mk
                                                                  false
                                                                  [
                                                                    (PathSegment.mk
                                                                      "Type"
                                                                      PathArguments.none),
                                                                    (PathSegment.mk
                                                                      "Int"
                                                                      PathArguments.none)]))
                                                              [
                                                                (Expr.path
                                                                  none
                                                                  (Path.mk
                                                                    false
                                                                    [
                                                                      (PathSegment.mk
                                                                        "int_ty"
                                                                        PathArguments.none)]))])
                                                            false)]))),
                                                  (Arm.mk
                                                    []
                                                    (Pat.tupleStruct
                                                      none
                                                      (Path.mk
                                                        false
                                                        [
                                                          (PathSegment.mk
                                                            "Transmute"
                                                            PathArguments.none)])
                                                      [(Pat.ident false false "new_ty" none)])
                                                    none
                                                    (Expr.block
                                                      none
                                                      (Block.mk
                                                        [
                                                          (Stmt.expr
                                                            (Expr.tryExpr
                                                              (Expr.call
                                                                (Expr.path
                                                                  none
                                                                  (Path.mk
                                                                    false
                                                                    [
                                                                      (PathSegment.mk
                                                                        "ensure_wf"
                                                                        PathArguments.none)]))
                                                                [
                                                                  (Expr.methodCall
                                                                    (Expr.methodCall
                                                                      (Expr.path
                                                                        none
                                                                        (Path.mk
                                                                          false
                                                                          [
                                                                            (PathSegment.mk
                                                                              "operand"
                                                                              PathArguments.none)]))
                                                                      "layout"
                                                                      (some
                                                                        [
                                                                          (GenericArgument.type
                                                                            (Ty.path
                                                                              none
                                                                              (Path.mk
                                                                                false
                                                                                [
                                                                                  (PathSegment.mk
                                                                                    "T"
                                                                                    PathArguments.none)])))])
                                                                      [])
                                                                    "is_sized"
                                                                    none
                                                                    []),
                                                                  (Expr.lit
                                                                    (Lit.str
                                                                      "Cast::Transmute: unsized source type"))]))
                                                            true),
                                                          (Stmt.expr
                                                            (Expr.tryExpr
                                                              (Expr.call
                                                                (Expr.path
                                                                  none
                                                                  (Path.mk
                                                                    false
                                                                    [
                                                                      (PathSegment.mk
                                                                        "ensure_wf"
                                                                        PathArguments.none)]))
                                                                [
                                                                  (Expr.methodCall
                                                                    (Expr.methodCall
                                                                      (Expr.path
                                                                        none
                                                                        (Path.mk
                                                                          false
                                                                          [
                                                                            (PathSegment.mk
                                                                              "new_ty"
                                                                              PathArguments.none)]))
                                                                      "layout"
                                                                      (some
                                                                        [
                                                                          (GenericArgument.type
                                                                            (Ty.path
                                                                              none
                                                                              (Path.mk
                                                                                false
                                                                                [
                                                                                  (PathSegment.mk
                                                                                    "T"
                                                                                    PathArguments.none)])))])
                                                                      [])
                                                                    "is_sized"
                                                                    none
                                                                    []),
                                                                  (Expr.lit
                                                                    (Lit.str
                                                                      "Cast::Transmute: unsized target type"))]))
                                                            true),
                                                          (Stmt.expr
                                                            (Expr.path
                                                              none
                                                              (Path.mk
                                                                false
                                                                [
                                                                  (PathSegment.mk
                                                                    "new_ty"
                                                                    PathArguments.none)]))
                                                            false)])))])
                                              false)]))),
                                    (Arm.mk
                                      []
                                      (Pat.ident false false "GetThinPointer" none)
                                      none
                                      (Expr.block
                                        none
                                        (Block.mk
                                          [
                                            (Stmt.expr
                                              (Expr.tryExpr
                                                (Expr.call
                                                  (Expr.path
                                                    none
                                                    (Path.mk
                                                      false
                                                      [
                                                        (PathSegment.mk
                                                          "ensure_wf"
                                                          PathArguments.none)]))
                                                  [
                                                    (Expr.macro
                                                      (Macro.mk
                                                        (Path.mk
                                                          false
                                                          [
                                                            (PathSegment.mk
                                                              "matches"
                                                              PathArguments.none)])
                                                        MacroDelimiter.paren
                                                        (MacroBody.exprAndPat
                                                          (Expr.path
                                                            none
                                                            (Path.mk
                                                              false
                                                              [
                                                                (PathSegment.mk
                                                                  "operand"
                                                                  PathArguments.none)]))
                                                          (Pat.tupleStruct
                                                            none
                                                            (Path.mk
                                                              false
                                                              [
                                                                (PathSegment.mk
                                                                  "Type"
                                                                  PathArguments.none),
                                                                (PathSegment.mk
                                                                  "Ptr"
                                                                  PathArguments.none)])
                                                            [Pat.wild])
                                                          none))),
                                                    (Expr.lit
                                                      (Lit.str
                                                        "UnOp::GetThinPointer: invalid operand: not a pointer"))]))
                                              true),
                                            (Stmt.expr
                                              (Expr.call
                                                (Expr.path
                                                  none
                                                  (Path.mk
                                                    false
                                                    [
                                                      (PathSegment.mk "Type" PathArguments.none),
                                                      (PathSegment.mk "Ptr" PathArguments.none)]))
                                                [
                                                  (Expr.struct
                                                    none
                                                    (Path.mk
                                                      false
                                                      [
                                                        (PathSegment.mk
                                                          "PtrType"
                                                          PathArguments.none),
                                                        (PathSegment.mk "Raw" PathArguments.none)])
                                                    [
                                                      (FieldValue.mk
                                                        []
                                                        (Member.named "meta_kind")
                                                        false
                                                        (Expr.path
                                                          none
                                                          (Path.mk
                                                            false
                                                            [
                                                              (PathSegment.mk
                                                                "PointerMetaKind"
                                                                PathArguments.none),
                                                              (PathSegment.mk
                                                                "None"
                                                                PathArguments.none)])))]
                                                    false
                                                    none)])
                                              false)]))),
                                    (Arm.mk
                                      []
                                      (Pat.ident false false "GetMetadata" none)
                                      none
                                      (Expr.block
                                        none
                                        (Block.mk
                                          [
                                            (Stmt.letStmt
                                              []
                                              (Pat.tupleStruct
                                                none
                                                (Path.mk
                                                  false
                                                  [
                                                    (PathSegment.mk "Type" PathArguments.none),
                                                    (PathSegment.mk "Ptr" PathArguments.none)])
                                                [(Pat.ident false false "ptr_ty" none)])
                                              (some
                                                (Expr.path
                                                  none
                                                  (Path.mk
                                                    false
                                                    [(PathSegment.mk "operand" PathArguments.none)])))
                                              (some
                                                (Expr.block
                                                  none
                                                  (Block.mk
                                                    [
                                                      (Stmt.macro
                                                        []
                                                        (Macro.mk
                                                          (Path.mk
                                                            false
                                                            [
                                                              (PathSegment.mk
                                                                "throw_ill_formed"
                                                                PathArguments.none)])
                                                          MacroDelimiter.paren
                                                          (MacroBody.exprs
                                                            [
                                                              (Expr.lit
                                                                (Lit.str
                                                                  "UnOp::GetMetadata: invalid operand: not a pointer"))]
                                                            false))
                                                        true)])))),
                                            (Stmt.expr
                                              (Expr.methodCall
                                                (Expr.methodCall
                                                  (Expr.path
                                                    none
                                                    (Path.mk
                                                      false
                                                      [(PathSegment.mk "ptr_ty" PathArguments.none)]))
                                                  "meta_kind"
                                                  none
                                                  [])
                                                "ty"
                                                (some
                                                  [
                                                    (GenericArgument.type
                                                      (Ty.path
                                                        none
                                                        (Path.mk
                                                          false
                                                          [(PathSegment.mk "T" PathArguments.none)])))])
                                                [])
                                              false)]))),
                                    (Arm.mk
                                      []
                                      (Pat.or
                                        [
                                          (Pat.tupleStruct
                                            none
                                            (Path.mk
                                              false
                                              [(PathSegment.mk "ComputeSize" PathArguments.none)])
                                            [(Pat.ident false false "ty" none)]),
                                          (Pat.tupleStruct
                                            none
                                            (Path.mk
                                              false
                                              [(PathSegment.mk "ComputeAlign" PathArguments.none)])
                                            [(Pat.ident false false "ty" none)])])
                                      none
                                      (Expr.block
                                        none
                                        (Block.mk
                                          [
                                            (Stmt.expr
                                              (Expr.tryExpr
                                                (Expr.methodCall
                                                  (Expr.path
                                                    none
                                                    (Path.mk
                                                      false
                                                      [(PathSegment.mk "ty" PathArguments.none)]))
                                                  "check_wf"
                                                  (some
                                                    [
                                                      (GenericArgument.type
                                                        (Ty.path
                                                          none
                                                          (Path.mk
                                                            false
                                                            [
                                                              (PathSegment.mk
                                                                "T"
                                                                PathArguments.none)])))])
                                                  [
                                                    (Expr.path
                                                      none
                                                      (Path.mk
                                                        false
                                                        [(PathSegment.mk "prog" PathArguments.none)]))]))
                                              true),
                                            (Stmt.letStmt
                                              []
                                              (Pat.ident false false "meta_ty" none)
                                              (some
                                                (Expr.methodCall
                                                  (Expr.methodCall
                                                    (Expr.path
                                                      none
                                                      (Path.mk
                                                        false
                                                        [(PathSegment.mk "ty" PathArguments.none)]))
                                                    "meta_kind"
                                                    none
                                                    [])
                                                  "ty"
                                                  (some
                                                    [
                                                      (GenericArgument.type
                                                        (Ty.path
                                                          none
                                                          (Path.mk
                                                            false
                                                            [
                                                              (PathSegment.mk
                                                                "T"
                                                                PathArguments.none)])))])
                                                  []))
                                              none),
                                            (Stmt.expr
                                              (Expr.ite
                                                (Expr.binary
                                                  (Expr.path
                                                    none
                                                    (Path.mk
                                                      false
                                                      [
                                                        (PathSegment.mk
                                                          "operand"
                                                          PathArguments.none)]))
                                                  BinOp.ne
                                                  (Expr.path
                                                    none
                                                    (Path.mk
                                                      false
                                                      [
                                                        (PathSegment.mk
                                                          "meta_ty"
                                                          PathArguments.none)])))
                                                (Block.mk
                                                  [
                                                    (Stmt.macro
                                                      []
                                                      (Macro.mk
                                                        (Path.mk
                                                          false
                                                          [
                                                            (PathSegment.mk
                                                              "throw_ill_formed"
                                                              PathArguments.none)])
                                                        MacroDelimiter.paren
                                                        (MacroBody.exprs
                                                          [
                                                            (Expr.lit
                                                              (Lit.str
                                                                "UnOp::ComputeSize|ComputeAlign: invalid operand type: not metadata of type"))]
                                                          false))
                                                      true)])
                                                none)
                                              false),
                                            (Stmt.expr
                                              (Expr.call
                                                (Expr.path
                                                  none
                                                  (Path.mk
                                                    false
                                                    [
                                                      (PathSegment.mk "Type" PathArguments.none),
                                                      (PathSegment.mk "Int" PathArguments.none)]))
                                                [
                                                  (Expr.call
                                                    (Expr.path
                                                      none
                                                      (Path.mk
                                                        false
                                                        [
                                                          (PathSegment.mk
                                                            "IntType"
                                                            PathArguments.none),
                                                          (PathSegment.mk
                                                            "usize_ty"
                                                            (PathArguments.angleBracketed
                                                              true
                                                              [
                                                                (GenericArgument.type
                                                                  (Ty.path
                                                                    none
                                                                    (Path.mk
                                                                      false
                                                                      [
                                                                        (PathSegment.mk
                                                                          "T"
                                                                          PathArguments.none)])))]))]))
                                                    [])])
                                              false)]))),
                                    (Arm.mk
                                      []
                                      (Pat.tupleStruct
                                        none
                                        (Path.mk
                                          false
                                          [(PathSegment.mk "VTableMethodLookup" PathArguments.none)])
                                        [(Pat.ident false false "method" none)])
                                      none
                                      (Expr.block
                                        none
                                        (Block.mk
                                          [
                                            (Stmt.letStmt
                                              []
                                              (Pat.tupleStruct
                                                none
                                                (Path.mk
                                                  false
                                                  [
                                                    (PathSegment.mk "Type" PathArguments.none),
                                                    (PathSegment.mk "Ptr" PathArguments.none)])
                                                [
                                                  (Pat.tupleStruct
                                                    none
                                                    (Path.mk
                                                      false
                                                      [
                                                        (PathSegment.mk
                                                          "PtrType"
                                                          PathArguments.none),
                                                        (PathSegment.mk
                                                          "VTablePtr"
                                                          PathArguments.none)])
                                                    [(Pat.ident false false "trait_name" none)])])
                                              (some
                                                (Expr.path
                                                  none
                                                  (Path.mk
                                                    false
                                                    [(PathSegment.mk "operand" PathArguments.none)])))
                                              (some
                                                (Expr.block
                                                  none
                                                  (Block.mk
                                                    [
                                                      (Stmt.macro
                                                        []
                                                        (Macro.mk
                                                          (Path.mk
                                                            false
                                                            [
                                                              (PathSegment.mk
                                                                "throw_ill_formed"
                                                                PathArguments.none)])
                                                          MacroDelimiter.paren
                                                          (MacroBody.exprs
                                                            [
                                                              (Expr.lit
                                                                (Lit.str
                                                                  "UnOp::VTableMethodLookup: invalid operand: not a vtable pointer"))]
                                                            false))
                                                        true)])))),
                                            (Stmt.letStmt
                                              []
                                              (Pat.ident false false "trait_methods" none)
                                              (some
                                                (Expr.index
                                                  (Expr.field
                                                    (Expr.path
                                                      none
                                                      (Path.mk
                                                        false
                                                        [(PathSegment.mk "prog" PathArguments.none)]))
                                                    (Member.named "traits"))
                                                  (Expr.path
                                                    none
                                                    (Path.mk
                                                      false
                                                      [
                                                        (PathSegment.mk
                                                          "trait_name"
                                                          PathArguments.none)]))))
                                              none),
                                            (Stmt.expr
                                              (Expr.tryExpr
                                                (Expr.call
                                                  (Expr.path
                                                    none
                                                    (Path.mk
                                                      false
                                                      [
                                                        (PathSegment.mk
                                                          "ensure_wf"
                                                          PathArguments.none)]))
                                                  [
                                                    (Expr.methodCall
                                                      (Expr.path
                                                        none
                                                        (Path.mk
                                                          false
                                                          [
                                                            (PathSegment.mk
                                                              "trait_methods"
                                                              PathArguments.none)]))
                                                      "contains"
                                                      none
                                                      [
                                                        (Expr.path
                                                          none
                                                          (Path.mk
                                                            false
                                                            [
                                                              (PathSegment.mk
                                                                "method"
                                                                PathArguments.none)]))]),
                                                    (Expr.lit
                                                      (Lit.str
                                                        "UnOp::VTableMethodLookup: invalid operand: method doesn't exist in trait"))]))
                                              true),
                                            (Stmt.expr
                                              (Expr.call
                                                (Expr.path
                                                  none
                                                  (Path.mk
                                                    false
                                                    [
                                                      (PathSegment.mk "Type" PathArguments.none),
                                                      (PathSegment.mk "Ptr" PathArguments.none)]))
                                                [
                                                  (Expr.path
                                                    none
                                                    (Path.mk
                                                      false
                                                      [
                                                        (PathSegment.mk
                                                          "PtrType"
                                                          PathArguments.none),
                                                        (PathSegment.mk "FnPtr" PathArguments.none)]))])
                                              false)])))])
                                false)]))),
                      (Arm.mk
                        []
                        (Pat.struct
                          none
                          (Path.mk false [(PathSegment.mk "BinOp" PathArguments.none)])
                          [
                            (FieldPat.mk
                              []
                              (Member.named "operator")
                              true
                              (Pat.ident false false "operator" none)),
                            (FieldPat.mk
                              []
                              (Member.named "left")
                              true
                              (Pat.ident false false "left" none)),
                            (FieldPat.mk
                              []
                              (Member.named "right")
                              true
                              (Pat.ident false false "right" none))]
                          false)
                        none
                        (Expr.block
                          none
                          (Block.mk
                            [
                              (Stmt.item
                                (Item.use
                                  []
                                  Visibility.inherited
                                  false
                                  (UseTree.path "lang" (UseTree.path "BinOp" UseTree.glob)))),
                              (Stmt.letStmt
                                []
                                (Pat.ident false false "left" none)
                                (some
                                  (Expr.tryExpr
                                    (Expr.methodCall
                                      (Expr.path
                                        none
                                        (Path.mk false [(PathSegment.mk "left" PathArguments.none)]))
                                      "check_wf"
                                      (some
                                        [
                                          (GenericArgument.type
                                            (Ty.path
                                              none
                                              (Path.mk
                                                false
                                                [(PathSegment.mk "T" PathArguments.none)])))])
                                      [
                                        (Expr.path
                                          none
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "locals" PathArguments.none)])),
                                        (Expr.path
                                          none
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "prog" PathArguments.none)]))])))
                                none),
                              (Stmt.letStmt
                                []
                                (Pat.ident false false "right" none)
                                (some
                                  (Expr.tryExpr
                                    (Expr.methodCall
                                      (Expr.path
                                        none
                                        (Path.mk
                                          false
                                          [(PathSegment.mk "right" PathArguments.none)]))
                                      "check_wf"
                                      (some
                                        [
                                          (GenericArgument.type
                                            (Ty.path
                                              none
                                              (Path.mk
                                                false
                                                [(PathSegment.mk "T" PathArguments.none)])))])
                                      [
                                        (Expr.path
                                          none
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "locals" PathArguments.none)])),
                                        (Expr.path
                                          none
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "prog" PathArguments.none)]))])))
                                none),
                              (Stmt.expr
                                (Expr.matchExpr
                                  (Expr.path
                                    none
                                    (Path.mk false [(PathSegment.mk "operator" PathArguments.none)]))
                                  [
                                    (Arm.mk
                                      []
                                      (Pat.tupleStruct
                                        none
                                        (Path.mk false [(PathSegment.mk "Int" PathArguments.none)])
                                        [(Pat.ident false false "int_op" none)])
                                      none
                                      (Expr.block
                                        none
                                        (Block.mk
                                          [
                                            (Stmt.letStmt
                                              []
                                              (Pat.tupleStruct
                                                none
                                                (Path.mk
                                                  false
                                                  [
                                                    (PathSegment.mk "Type" PathArguments.none),
                                                    (PathSegment.mk "Int" PathArguments.none)])
                                                [(Pat.ident false false "left" none)])
                                              (some
                                                (Expr.path
                                                  none
                                                  (Path.mk
                                                    false
                                                    [(PathSegment.mk "left" PathArguments.none)])))
                                              (some
                                                (Expr.block
                                                  none
                                                  (Block.mk
                                                    [
                                                      (Stmt.macro
                                                        []
                                                        (Macro.mk
                                                          (Path.mk
                                                            false
                                                            [
                                                              (PathSegment.mk
                                                                "throw_ill_formed"
                                                                PathArguments.none)])
                                                          MacroDelimiter.paren
                                                          (MacroBody.exprs
                                                            [
                                                              (Expr.lit
                                                                (Lit.str
                                                                  "BinOp::Int: invalid left type"))]
                                                            false))
                                                        true)])))),
                                            (Stmt.letStmt
                                              []
                                              (Pat.tupleStruct
                                                none
                                                (Path.mk
                                                  false
                                                  [
                                                    (PathSegment.mk "Type" PathArguments.none),
                                                    (PathSegment.mk "Int" PathArguments.none)])
                                                [(Pat.ident false false "right" none)])
                                              (some
                                                (Expr.path
                                                  none
                                                  (Path.mk
                                                    false
                                                    [(PathSegment.mk "right" PathArguments.none)])))
                                              (some
                                                (Expr.block
                                                  none
                                                  (Block.mk
                                                    [
                                                      (Stmt.macro
                                                        []
                                                        (Macro.mk
                                                          (Path.mk
                                                            false
                                                            [
                                                              (PathSegment.mk
                                                                "throw_ill_formed"
                                                                PathArguments.none)])
                                                          MacroDelimiter.paren
                                                          (MacroBody.exprs
                                                            [
                                                              (Expr.lit
                                                                (Lit.str
                                                                  "BinOp::Int: invalid right type"))]
                                                            false))
                                                        true)])))),
                                            (Stmt.item
                                              (Item.use
                                                []
                                                Visibility.inherited
                                                false
                                                (UseTree.path "IntBinOp" UseTree.glob))),
                                            (Stmt.expr
                                              (Expr.ite
                                                (Expr.unary
                                                  UnOp.not
                                                  (Expr.macro
                                                    (Macro.mk
                                                      (Path.mk
                                                        false
                                                        [
                                                          (PathSegment.mk
                                                            "matches"
                                                            PathArguments.none)])
                                                      MacroDelimiter.paren
                                                      (MacroBody.exprAndPat
                                                        (Expr.path
                                                          none
                                                          (Path.mk
                                                            false
                                                            [
                                                              (PathSegment.mk
                                                                "int_op"
                                                                PathArguments.none)]))
                                                        (Pat.or
                                                          [
                                                            (Pat.ident false false "Shl" none),
                                                            (Pat.ident false false "Shr" none),
                                                            (Pat.ident
                                                              false
                                                              false
                                                              "ShlUnchecked"
                                                              none),
                                                            (Pat.ident
                                                              false
                                                              false
                                                              "ShrUnchecked"
                                                              none)])
                                                        none))))
                                                (Block.mk
                                                  [
                                                    (Stmt.expr
                                                      (Expr.tryExpr
                                                        (Expr.call
                                                          (Expr.path
                                                            none
                                                            (Path.mk
                                                              false
                                                              [
                                                                (PathSegment.mk
                                                                  "ensure_wf"
                                                                  PathArguments.none)]))
                                                          [
                                                            (Expr.binary
                                                              (Expr.path
                                                                none
                                                                (Path.mk
                                                                  false
                                                                  [
                                                                    (PathSegment.mk
                                                                      "left"
                                                                      PathArguments.none)]))
                                                              BinOp.eq
                                                              (Expr.path
                                                                none
                                                                (Path.mk
                                                                  false
                                                                  [
                                                                    (PathSegment.mk
                                                                      "right"
                                                                      PathArguments.none)]))),
                                                            (Expr.lit
                                                              (Lit.str
                                                                "BinOp:Int: right and left type are not equal"))]))
                                                      true)])
                                                none)
                                              false),
                                            (Stmt.expr
                                              (Expr.call
                                                (Expr.path
                                                  none
                                                  (Path.mk
                                                    false
                                                    [
                                                      (PathSegment.mk "Type" PathArguments.none),
                                                      (PathSegment.mk "Int" PathArguments.none)]))
                                                [
                                                  (Expr.path
                                                    none
                                                    (Path.mk
                                                      false
                                                      [(PathSegment.mk "left" PathArguments.none)]))])
                                              false)]))),
                                    (Arm.mk
                                      []
                                      (Pat.tupleStruct
                                        none
                                        (Path.mk
                                          false
                                          [(PathSegment.mk "IntWithOverflow" PathArguments.none)])
                                        [(Pat.ident false false "_int_op" none)])
                                      none
                                      (Expr.block
                                        none
                                        (Block.mk
                                          [
                                            (Stmt.letStmt
                                              []
                                              (Pat.tupleStruct
                                                none
                                                (Path.mk
                                                  false
                                                  [
                                                    (PathSegment.mk "Type" PathArguments.none),
                                                    (PathSegment.mk "Int" PathArguments.none)])
                                                [(Pat.ident false false "int_ty" none)])
                                              (some
                                                (Expr.path
                                                  none
                                                  (Path.mk
                                                    false
                                                    [(PathSegment.mk "left" PathArguments.none)])))
                                              (some
                                                (Expr.block
                                                  none
                                                  (Block.mk
                                                    [
                                                      (Stmt.macro
                                                        []
                                                        (Macro.mk
                                                          (Path.mk
                                                            false
                                                            [
                                                              (PathSegment.mk
                                                                "throw_ill_formed"
                                                                PathArguments.none)])
                                                          MacroDelimiter.paren
                                                          (MacroBody.exprs
                                                            [
                                                              (Expr.lit
                                                                (Lit.str
                                                                  "BinOp::IntWithOverflow: invalid left type"))]
                                                            false))
                                                        true)])))),
                                            (Stmt.expr
                                              (Expr.tryExpr
                                                (Expr.call
                                                  (Expr.path
                                                    none
                                                    (Path.mk
                                                      false
                                                      [
                                                        (PathSegment.mk
                                                          "ensure_wf"
                                                          PathArguments.none)]))
                                                  [
                                                    (Expr.binary
                                                      (Expr.path
                                                        none
                                                        (Path.mk
                                                          false
                                                          [
                                                            (PathSegment.mk
                                                              "right"
                                                              PathArguments.none)]))
                                                      BinOp.eq
                                                      (Expr.call
                                                        (Expr.path
                                                          none
                                                          (Path.mk
                                                            false
                                                            [
                                                              (PathSegment.mk
                                                                "Type"
                                                                PathArguments.none),
                                                              (PathSegment.mk
                                                                "Int"
                                                                PathArguments.none)]))
                                                        [
                                                          (Expr.path
                                                            none
                                                            (Path.mk
                                                              false
                                                              [
                                                                (PathSegment.mk
                                                                  "int_ty"
                                                                  PathArguments.none)]))])),
                                                    (Expr.lit
                                                      (Lit.str
                                                        "BinOp::IntWithOverflow: invalid right type"))]))
                                              true),
                                            (Stmt.expr
                                              (Expr.methodCall
                                                (Expr.path
                                                  none
                                                  (Path.mk
                                                    false
                                                    [(PathSegment.mk "int_ty" PathArguments.none)]))
                                                "with_overflow"
                                                (some
                                                  [
                                                    (GenericArgument.type
                                                      (Ty.path
                                                        none
                                                        (Path.mk
                                                          false
                                                          [(PathSegment.mk "T" PathArguments.none)])))])
                                                [])
                                              false)]))),
                                    (Arm.mk
                                      []
                                      (Pat.tupleStruct
                                        none
                                        (Path.mk false [(PathSegment.mk "Rel" PathArguments.none)])
                                        [(Pat.ident false false "rel_op" none)])
                                      none
                                      (Expr.block
                                        none
                                        (Block.mk
                                          [
                                            (Stmt.expr
                                              (Expr.tryExpr
                                                (Expr.call
                                                  (Expr.path
                                                    none
                                                    (Path.mk
                                                      false
                                                      [
                                                        (PathSegment.mk
                                                          "ensure_wf"
                                                          PathArguments.none)]))
                                                  [
                                                    (Expr.macro
                                                      (Macro.mk
                                                        (Path.mk
                                                          false
                                                          [
                                                            (PathSegment.mk
                                                              "matches"
                                                              PathArguments.none)])
                                                        MacroDelimiter.paren
                                                        (MacroBody.exprAndPat
                                                          (Expr.path
                                                            none
                                                            (Path.mk
                                                              false
                                                              [
                                                                (PathSegment.mk
                                                                  "left"
                                                                  PathArguments.none)]))
                                                          (Pat.or
                                                            [
                                                              (Pat.tupleStruct
                                                                none
                                                                (Path.mk
                                                                  false
                                                                  [
                                                                    (PathSegment.mk
                                                                      "Type"
                                                                      PathArguments.none),
                                                                    (PathSegment.mk
                                                                      "Int"
                                                                      PathArguments.none)])
                                                                [Pat.wild]),
                                                              (Pat.path
                                                                none
                                                                (Path.mk
                                                                  false
                                                                  [
                                                                    (PathSegment.mk
                                                                      "Type"
                                                                      PathArguments.none),
                                                                    (PathSegment.mk
                                                                      "Bool"
                                                                      PathArguments.none)])),
                                                              (Pat.tupleStruct
                                                                none
                                                                (Path.mk
                                                                  false
                                                                  [
                                                                    (PathSegment.mk
                                                                      "Type"
                                                                      PathArguments.none),
                                                                    (PathSegment.mk
                                                                      "Ptr"
                                                                      PathArguments.none)])
                                                                [Pat.wild])])
                                                          none))),
                                                    (Expr.lit
                                                      (Lit.str "BinOp::Rel: invalid left type"))]))
                                              true),
                                            (Stmt.expr
                                              (Expr.tryExpr
                                                (Expr.call
                                                  (Expr.path
                                                    none
                                                    (Path.mk
                                                      false
                                                      [
                                                        (PathSegment.mk
                                                          "ensure_wf"
                                                          PathArguments.none)]))
                                                  [
                                                    (Expr.binary
                                                      (Expr.path
                                                        none
                                                        (Path.mk
                                                          false
                                                          [
                                                            (PathSegment.mk
                                                              "right"
                                                              PathArguments.none)]))
                                                      BinOp.eq
                                                      (Expr.path
                                                        none
                                                        (Path.mk
                                                          false
                                                          [
                                                            (PathSegment.mk
                                                              "left"
                                                              PathArguments.none)]))),
                                                    (Expr.lit
                                                      (Lit.str "BinOp::Rel: invalid right type"))]))
                                              true),
                                            (Stmt.expr
                                              (Expr.matchExpr
                                                (Expr.path
                                                  none
                                                  (Path.mk
                                                    false
                                                    [(PathSegment.mk "rel_op" PathArguments.none)]))
                                                [
                                                  (Arm.mk
                                                    []
                                                    (Pat.path
                                                      none
                                                      (Path.mk
                                                        false
                                                        [
                                                          (PathSegment.mk
                                                            "RelOp"
                                                            PathArguments.none),
                                                          (PathSegment.mk "Cmp" PathArguments.none)]))
                                                    none
                                                    (Expr.call
                                                      (Expr.path
                                                        none
                                                        (Path.mk
                                                          false
                                                          [
                                                            (PathSegment.mk
                                                              "Type"
                                                              PathArguments.none),
                                                            (PathSegment.mk
                                                              "Int"
                                                              PathArguments.none)]))
                                                      [
                                                        (Expr.path
                                                          none
                                                          (Path.mk
                                                            false
                                                            [
                                                              (PathSegment.mk
                                                                "IntType"
                                                                PathArguments.none),
                                                              (PathSegment.mk
                                                                "I8"
                                                                PathArguments.none)]))])),
                                                  (Arm.mk
                                                    []
                                                    Pat.wild
                                                    none
                                                    (Expr.path
                                                      none
                                                      (Path.mk
                                                        false
                                                        [
                                                          (PathSegment.mk "Type" PathArguments.none),
                                                          (PathSegment.mk "Bool" PathArguments.none)])))])
                                              false)]))),
                                    (Arm.mk
                                      []
                                      (Pat.struct
                                        none
                                        (Path.mk
                                          false
                                          [(PathSegment.mk "PtrOffset" PathArguments.none)])
                                        [(FieldPat.mk [] (Member.named "inbounds") false Pat.wild)]
                                        false)
                                      none
                                      (Expr.block
                                        none
                                        (Block.mk
                                          [
                                            (Stmt.letStmt
                                              []
                                              (Pat.tupleStruct
                                                none
                                                (Path.mk
                                                  false
                                                  [
                                                    (PathSegment.mk "Type" PathArguments.none),
                                                    (PathSegment.mk "Ptr" PathArguments.none)])
                                                [(Pat.ident false false "left_ptr_ty" none)])
                                              (some
                                                (Expr.path
                                                  none
                                                  (Path.mk
                                                    false
                                                    [(PathSegment.mk "left" PathArguments.none)])))
                                              (some
                                                (Expr.block
                                                  none
                                                  (Block.mk
                                                    [
                                                      (Stmt.macro
                                                        []
                                                        (Macro.mk
                                                          (Path.mk
                                                            false
                                                            [
                                                              (PathSegment.mk
                                                                "throw_ill_formed"
                                                                PathArguments.none)])
                                                          MacroDelimiter.paren
                                                          (MacroBody.exprs
                                                            [
                                                              (Expr.lit
                                                                (Lit.str
                                                                  "BinOp::PtrOffset: invalid left type: not a pointer"))]
                                                            false))
                                                        true)])))),
                                            (Stmt.expr
                                              (Expr.ite
                                                (Expr.binary
                                                  (Expr.methodCall
                                                    (Expr.path
                                                      none
                                                      (Path.mk
                                                        false
                                                        [
                                                          (PathSegment.mk
                                                            "left_ptr_ty"
                                                            PathArguments.none)]))
                                                    "meta_kind"
                                                    none
                                                    [])
                                                  BinOp.ne
                                                  (Expr.path
                                                    none
                                                    (Path.mk
                                                      false
                                                      [
                                                        (PathSegment.mk
                                                          "PointerMetaKind"
                                                          PathArguments.none),
                                                        (PathSegment.mk "None" PathArguments.none)])))
                                                (Block.mk
                                                  [
                                                    (Stmt.macro
                                                      []
                                                      (Macro.mk
                                                        (Path.mk
                                                          false
                                                          [
                                                            (PathSegment.mk
                                                              "throw_ill_formed"
                                                              PathArguments.none)])
                                                        MacroDelimiter.paren
                                                        (MacroBody.exprs
                                                          [
                                                            (Expr.lit
                                                              (Lit.str
                                                                "BinOp::PtrOffset: invalid left type: unsized pointee"))]
                                                          false))
                                                      true)])
                                                none)
                                              false),
                                            (Stmt.expr
                                              (Expr.tryExpr
                                                (Expr.call
                                                  (Expr.path
                                                    none
                                                    (Path.mk
                                                      false
                                                      [
                                                        (PathSegment.mk
                                                          "ensure_wf"
                                                          PathArguments.none)]))
                                                  [
                                                    (Expr.macro
                                                      (Macro.mk
                                                        (Path.mk
                                                          false
                                                          [
                                                            (PathSegment.mk
                                                              "matches"
                                                              PathArguments.none)])
                                                        MacroDelimiter.paren
                                                        (MacroBody.exprAndPat
                                                          (Expr.path
                                                            none
                                                            (Path.mk
                                                              false
                                                              [
                                                                (PathSegment.mk
                                                                  "right"
                                                                  PathArguments.none)]))
                                                          (Pat.tupleStruct
                                                            none
                                                            (Path.mk
                                                              false
                                                              [
                                                                (PathSegment.mk
                                                                  "Type"
                                                                  PathArguments.none),
                                                                (PathSegment.mk
                                                                  "Int"
                                                                  PathArguments.none)])
                                                            [Pat.wild])
                                                          none))),
                                                    (Expr.lit
                                                      (Lit.str
                                                        "BinOp::PtrOffset: invalid right type"))]))
                                              true),
                                            (Stmt.expr
                                              (Expr.path
                                                none
                                                (Path.mk
                                                  false
                                                  [(PathSegment.mk "left" PathArguments.none)]))
                                              false)]))),
                                    (Arm.mk
                                      []
                                      (Pat.struct
                                        none
                                        (Path.mk
                                          false
                                          [(PathSegment.mk "PtrOffsetFrom" PathArguments.none)])
                                        [
                                          (FieldPat.mk [] (Member.named "inbounds") false Pat.wild),
                                          (FieldPat.mk [] (Member.named "nonneg") false Pat.wild)]
                                        false)
                                      none
                                      (Expr.block
                                        none
                                        (Block.mk
                                          [
                                            (Stmt.letStmt
                                              []
                                              (Pat.tupleStruct
                                                none
                                                (Path.mk
                                                  false
                                                  [
                                                    (PathSegment.mk "Type" PathArguments.none),
                                                    (PathSegment.mk "Ptr" PathArguments.none)])
                                                [(Pat.ident false false "left_ptr_ty" none)])
                                              (some
                                                (Expr.path
                                                  none
                                                  (Path.mk
                                                    false
                                                    [(PathSegment.mk "left" PathArguments.none)])))
                                              (some
                                                (Expr.block
                                                  none
                                                  (Block.mk
                                                    [
                                                      (Stmt.macro
                                                        []
                                                        (Macro.mk
                                                          (Path.mk
                                                            false
                                                            [
                                                              (PathSegment.mk
                                                                "throw_ill_formed"
                                                                PathArguments.none)])
                                                          MacroDelimiter.paren
                                                          (MacroBody.exprs
                                                            [
                                                              (Expr.lit
                                                                (Lit.str
                                                                  "BinOp::PtrOffsetFrom: invalid left type: not a pointer"))]
                                                            false))
                                                        true)])))),
                                            (Stmt.expr
                                              (Expr.ite
                                                (Expr.binary
                                                  (Expr.methodCall
                                                    (Expr.path
                                                      none
                                                      (Path.mk
                                                        false
                                                        [
                                                          (PathSegment.mk
                                                            "left_ptr_ty"
                                                            PathArguments.none)]))
                                                    "meta_kind"
                                                    none
                                                    [])
                                                  BinOp.ne
                                                  (Expr.path
                                                    none
                                                    (Path.mk
                                                      false
                                                      [
                                                        (PathSegment.mk
                                                          "PointerMetaKind"
                                                          PathArguments.none),
                                                        (PathSegment.mk "None" PathArguments.none)])))
                                                (Block.mk
                                                  [
                                                    (Stmt.macro
                                                      []
                                                      (Macro.mk
                                                        (Path.mk
                                                          false
                                                          [
                                                            (PathSegment.mk
                                                              "throw_ill_formed"
                                                              PathArguments.none)])
                                                        MacroDelimiter.paren
                                                        (MacroBody.exprs
                                                          [
                                                            (Expr.lit
                                                              (Lit.str
                                                                "BinOp::PtrOffsetFrom: invalid left type: unsized pointee"))]
                                                          false))
                                                      true)])
                                                none)
                                              false),
                                            (Stmt.letStmt
                                              []
                                              (Pat.tupleStruct
                                                none
                                                (Path.mk
                                                  false
                                                  [
                                                    (PathSegment.mk "Type" PathArguments.none),
                                                    (PathSegment.mk "Ptr" PathArguments.none)])
                                                [(Pat.ident false false "right_ptr_ty" none)])
                                              (some
                                                (Expr.path
                                                  none
                                                  (Path.mk
                                                    false
                                                    [(PathSegment.mk "right" PathArguments.none)])))
                                              (some
                                                (Expr.block
                                                  none
                                                  (Block.mk
                                                    [
                                                      (Stmt.macro
                                                        []
                                                        (Macro.mk
                                                          (Path.mk
                                                            false
                                                            [
                                                              (PathSegment.mk
                                                                "throw_ill_formed"
                                                                PathArguments.none)])
                                                          MacroDelimiter.paren
                                                          (MacroBody.exprs
                                                            [
                                                              (Expr.lit
                                                                (Lit.str
                                                                  "BinOp::PtrOffsetFrom: invalid right type: not a pointer"))]
                                                            false))
                                                        true)])))),
                                            (Stmt.expr
                                              (Expr.ite
                                                (Expr.binary
                                                  (Expr.methodCall
                                                    (Expr.path
                                                      none
                                                      (Path.mk
                                                        false
                                                        [
                                                          (PathSegment.mk
                                                            "right_ptr_ty"
                                                            PathArguments.none)]))
                                                    "meta_kind"
                                                    none
                                                    [])
                                                  BinOp.ne
                                                  (Expr.path
                                                    none
                                                    (Path.mk
                                                      false
                                                      [
                                                        (PathSegment.mk
                                                          "PointerMetaKind"
                                                          PathArguments.none),
                                                        (PathSegment.mk "None" PathArguments.none)])))
                                                (Block.mk
                                                  [
                                                    (Stmt.macro
                                                      []
                                                      (Macro.mk
                                                        (Path.mk
                                                          false
                                                          [
                                                            (PathSegment.mk
                                                              "throw_ill_formed"
                                                              PathArguments.none)])
                                                        MacroDelimiter.paren
                                                        (MacroBody.exprs
                                                          [
                                                            (Expr.lit
                                                              (Lit.str
                                                                "BinOp::PtrOffsetFrom: invalid right type: unsized pointee"))]
                                                          false))
                                                      true)])
                                                none)
                                              false),
                                            (Stmt.letStmt
                                              []
                                              (Pat.ident false false "isize_int" none)
                                              (some
                                                (Expr.struct
                                                  none
                                                  (Path.mk
                                                    false
                                                    [(PathSegment.mk "IntType" PathArguments.none)])
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
                                                            (PathSegment.mk
                                                              "Signed"
                                                              PathArguments.none)]))),
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
                                                            (PathSegment.mk
                                                              "PTR_SIZE"
                                                              PathArguments.none)])))]
                                                  false
                                                  none))
                                              none),
                                            (Stmt.expr
                                              (Expr.call
                                                (Expr.path
                                                  none
                                                  (Path.mk
                                                    false
                                                    [
                                                      (PathSegment.mk "Type" PathArguments.none),
                                                      (PathSegment.mk "Int" PathArguments.none)]))
                                                [
                                                  (Expr.path
                                                    none
                                                    (Path.mk
                                                      false
                                                      [
                                                        (PathSegment.mk
                                                          "isize_int"
                                                          PathArguments.none)]))])
                                              false)]))),
                                    (Arm.mk
                                      []
                                      (Pat.tupleStruct
                                        none
                                        (Path.mk
                                          false
                                          [
                                            (PathSegment.mk
                                              "ConstructWidePointer"
                                              PathArguments.none)])
                                        [(Pat.ident false false "ptr_ty" none)])
                                      none
                                      (Expr.block
                                        none
                                        (Block.mk
                                          [
                                            (Stmt.letStmt
                                              []
                                              (Pat.tupleStruct
                                                none
                                                (Path.mk
                                                  false
                                                  [
                                                    (PathSegment.mk "Type" PathArguments.none),
                                                    (PathSegment.mk "Ptr" PathArguments.none)])
                                                [(Pat.ident false false "thin_ptr_ty" none)])
                                              (some
                                                (Expr.path
                                                  none
                                                  (Path.mk
                                                    false
                                                    [(PathSegment.mk "left" PathArguments.none)])))
                                              (some
                                                (Expr.block
                                                  none
                                                  (Block.mk
                                                    [
                                                      (Stmt.macro
                                                        []
                                                        (Macro.mk
                                                          (Path.mk
                                                            false
                                                            [
                                                              (PathSegment.mk
                                                                "throw_ill_formed"
                                                                PathArguments.none)])
                                                          MacroDelimiter.paren
                                                          (MacroBody.exprs
                                                            [
                                                              (Expr.lit
                                                                (Lit.str
                                                                  "BinOp::ConstructWidePointer: invalid left type: not a pointer"))]
                                                            false))
                                                        true)])))),
                                            (Stmt.expr
                                              (Expr.ite
                                                (Expr.binary
                                                  (Expr.methodCall
                                                    (Expr.path
                                                      none
                                                      (Path.mk
                                                        false
                                                        [
                                                          (PathSegment.mk
                                                            "thin_ptr_ty"
                                                            PathArguments.none)]))
                                                    "meta_kind"
                                                    none
                                                    [])
                                                  BinOp.ne
                                                  (Expr.path
                                                    none
                                                    (Path.mk
                                                      false
                                                      [
                                                        (PathSegment.mk
                                                          "PointerMetaKind"
                                                          PathArguments.none),
                                                        (PathSegment.mk "None" PathArguments.none)])))
                                                (Block.mk
                                                  [
                                                    (Stmt.macro
                                                      []
                                                      (Macro.mk
                                                        (Path.mk
                                                          false
                                                          [
                                                            (PathSegment.mk
                                                              "throw_ill_formed"
                                                              PathArguments.none)])
                                                        MacroDelimiter.paren
                                                        (MacroBody.exprs
                                                          [
                                                            (Expr.lit
                                                              (Lit.str
                                                                "BinOp::ConstructWidePointer: invalid left type: not a thin pointer"))]
                                                          false))
                                                      true)])
                                                none)
                                              false),
                                            (Stmt.letStmt
                                              []
                                              (Pat.ident false false "meta_ty" none)
                                              (some
                                                (Expr.methodCall
                                                  (Expr.methodCall
                                                    (Expr.path
                                                      none
                                                      (Path.mk
                                                        false
                                                        [
                                                          (PathSegment.mk
                                                            "ptr_ty"
                                                            PathArguments.none)]))
                                                    "meta_kind"
                                                    none
                                                    [])
                                                  "ty"
                                                  (some
                                                    [
                                                      (GenericArgument.type
                                                        (Ty.path
                                                          none
                                                          (Path.mk
                                                            false
                                                            [
                                                              (PathSegment.mk
                                                                "T"
                                                                PathArguments.none)])))])
                                                  []))
                                              none),
                                            (Stmt.expr
                                              (Expr.ite
                                                (Expr.binary
                                                  (Expr.path
                                                    none
                                                    (Path.mk
                                                      false
                                                      [(PathSegment.mk "right" PathArguments.none)]))
                                                  BinOp.ne
                                                  (Expr.path
                                                    none
                                                    (Path.mk
                                                      false
                                                      [
                                                        (PathSegment.mk
                                                          "meta_ty"
                                                          PathArguments.none)])))
                                                (Block.mk
                                                  [
                                                    (Stmt.macro
                                                      []
                                                      (Macro.mk
                                                        (Path.mk
                                                          false
                                                          [
                                                            (PathSegment.mk
                                                              "throw_ill_formed"
                                                              PathArguments.none)])
                                                        MacroDelimiter.paren
                                                        (MacroBody.exprs
                                                          [
                                                            (Expr.lit
                                                              (Lit.str
                                                                "BinOp::ConstructWidePointer: invalid right type: not metadata of target"))]
                                                          false))
                                                      true)])
                                                none)
                                              false),
                                            (Stmt.expr
                                              (Expr.call
                                                (Expr.path
                                                  none
                                                  (Path.mk
                                                    false
                                                    [
                                                      (PathSegment.mk "Type" PathArguments.none),
                                                      (PathSegment.mk "Ptr" PathArguments.none)]))
                                                [
                                                  (Expr.path
                                                    none
                                                    (Path.mk
                                                      false
                                                      [(PathSegment.mk "ptr_ty" PathArguments.none)]))])
                                              false)])))])
                                false)])))])])
              false)]))])

/-- `spec/lang/well-formed.md:556` -/
def impl_PlaceExpr__check_wf : Item :=
  (Item.impl
    []
    false
    false
    (Generics.mk [] [])
    false
    none
    (Ty.path none (Path.mk false [(PathSegment.mk "PlaceExpr" PathArguments.none)]))
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
          "check_wf"
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
              (Pat.ident false false "locals" none)
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
                              (Path.mk false [(PathSegment.mk "Type" PathArguments.none)])))]))]))),
            (FnArg.typed
              []
              (Pat.ident false false "prog" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "Program" PathArguments.none)])))]
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
                            (Path.mk false [(PathSegment.mk "Type" PathArguments.none)])))]))]))))
        (Block.mk
          [
            (Stmt.item
              (Item.use [] Visibility.inherited false (UseTree.path "PlaceExpr" UseTree.glob))),
            (Stmt.expr
              (Expr.call
                (Expr.path none (Path.mk false [(PathSegment.mk "ret" PathArguments.none)]))
                [
                  (Expr.matchExpr
                    (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                    [
                      (Arm.mk
                        []
                        (Pat.tupleStruct
                          none
                          (Path.mk false [(PathSegment.mk "Local" PathArguments.none)])
                          [(Pat.ident false false "name" none)])
                        none
                        (Expr.block
                          none
                          (Block.mk
                            [
                              (Stmt.expr
                                (Expr.matchExpr
                                  (Expr.methodCall
                                    (Expr.path
                                      none
                                      (Path.mk false [(PathSegment.mk "locals" PathArguments.none)]))
                                    "get"
                                    none
                                    [
                                      (Expr.path
                                        none
                                        (Path.mk false [(PathSegment.mk "name" PathArguments.none)]))])
                                  [
                                    (Arm.mk
                                      []
                                      (Pat.ident false false "None" none)
                                      none
                                      (Expr.macro
                                        (Macro.mk
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "throw_ill_formed" PathArguments.none)])
                                          MacroDelimiter.paren
                                          (MacroBody.exprs
                                            [
                                              (Expr.lit
                                                (Lit.str "PlaceExpr::Local: unknown local name"))]
                                            false)))),
                                    (Arm.mk
                                      []
                                      (Pat.tupleStruct
                                        none
                                        (Path.mk false [(PathSegment.mk "Some" PathArguments.none)])
                                        [(Pat.ident false false "local" none)])
                                      none
                                      (Expr.path
                                        none
                                        (Path.mk
                                          false
                                          [(PathSegment.mk "local" PathArguments.none)])))])
                                false)]))),
                      (Arm.mk
                        []
                        (Pat.struct
                          none
                          (Path.mk false [(PathSegment.mk "Deref" PathArguments.none)])
                          [
                            (FieldPat.mk
                              []
                              (Member.named "operand")
                              true
                              (Pat.ident false false "operand" none)),
                            (FieldPat.mk
                              []
                              (Member.named "ty")
                              true
                              (Pat.ident false false "ty" none))]
                          false)
                        none
                        (Expr.block
                          none
                          (Block.mk
                            [
                              (Stmt.expr
                                (Expr.tryExpr
                                  (Expr.methodCall
                                    (Expr.path
                                      none
                                      (Path.mk false [(PathSegment.mk "ty" PathArguments.none)]))
                                    "check_wf"
                                    (some
                                      [
                                        (GenericArgument.type
                                          (Ty.path
                                            none
                                            (Path.mk
                                              false
                                              [(PathSegment.mk "T" PathArguments.none)])))])
                                    [
                                      (Expr.path
                                        none
                                        (Path.mk false [(PathSegment.mk "prog" PathArguments.none)]))]))
                                true),
                              (Stmt.letStmt
                                []
                                (Pat.ident false false "op_ty" none)
                                (some
                                  (Expr.tryExpr
                                    (Expr.methodCall
                                      (Expr.path
                                        none
                                        (Path.mk
                                          false
                                          [(PathSegment.mk "operand" PathArguments.none)]))
                                      "check_wf"
                                      (some
                                        [
                                          (GenericArgument.type
                                            (Ty.path
                                              none
                                              (Path.mk
                                                false
                                                [(PathSegment.mk "T" PathArguments.none)])))])
                                      [
                                        (Expr.path
                                          none
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "locals" PathArguments.none)])),
                                        (Expr.path
                                          none
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "prog" PathArguments.none)]))])))
                                none),
                              (Stmt.letStmt
                                []
                                (Pat.tupleStruct
                                  none
                                  (Path.mk
                                    false
                                    [
                                      (PathSegment.mk "Type" PathArguments.none),
                                      (PathSegment.mk "Ptr" PathArguments.none)])
                                  [(Pat.ident false false "op_ptr_ty" none)])
                                (some
                                  (Expr.path
                                    none
                                    (Path.mk false [(PathSegment.mk "op_ty" PathArguments.none)])))
                                (some
                                  (Expr.block
                                    none
                                    (Block.mk
                                      [
                                        (Stmt.macro
                                          []
                                          (Macro.mk
                                            (Path.mk
                                              false
                                              [
                                                (PathSegment.mk
                                                  "throw_ill_formed"
                                                  PathArguments.none)])
                                            MacroDelimiter.paren
                                            (MacroBody.exprs
                                              [
                                                (Expr.lit
                                                  (Lit.str "PlaceExpr::Deref: invalid operand type"))]
                                              false))
                                          true)])))),
                              (Stmt.expr
                                (Expr.tryExpr
                                  (Expr.call
                                    (Expr.path
                                      none
                                      (Path.mk
                                        false
                                        [(PathSegment.mk "ensure_wf" PathArguments.none)]))
                                    [
                                      (Expr.binary
                                        (Expr.methodCall
                                          (Expr.path
                                            none
                                            (Path.mk
                                              false
                                              [(PathSegment.mk "op_ptr_ty" PathArguments.none)]))
                                          "meta_kind"
                                          none
                                          [])
                                        BinOp.eq
                                        (Expr.methodCall
                                          (Expr.path
                                            none
                                            (Path.mk
                                              false
                                              [(PathSegment.mk "ty" PathArguments.none)]))
                                          "meta_kind"
                                          none
                                          [])),
                                      (Expr.lit
                                        (Lit.str
                                          "PlaceExpr::Deref: metadata kind of operand and type don't match"))]))
                                true),
                              (Stmt.expr
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "ty" PathArguments.none)]))
                                false)]))),
                      (Arm.mk
                        []
                        (Pat.struct
                          none
                          (Path.mk false [(PathSegment.mk "Field" PathArguments.none)])
                          [
                            (FieldPat.mk
                              []
                              (Member.named "root")
                              true
                              (Pat.ident false false "root" none)),
                            (FieldPat.mk
                              []
                              (Member.named "field")
                              true
                              (Pat.ident false false "field" none))]
                          false)
                        none
                        (Expr.block
                          none
                          (Block.mk
                            [
                              (Stmt.letStmt
                                []
                                (Pat.ident false false "root" none)
                                (some
                                  (Expr.tryExpr
                                    (Expr.methodCall
                                      (Expr.path
                                        none
                                        (Path.mk false [(PathSegment.mk "root" PathArguments.none)]))
                                      "check_wf"
                                      (some
                                        [
                                          (GenericArgument.type
                                            (Ty.path
                                              none
                                              (Path.mk
                                                false
                                                [(PathSegment.mk "T" PathArguments.none)])))])
                                      [
                                        (Expr.path
                                          none
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "locals" PathArguments.none)])),
                                        (Expr.path
                                          none
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "prog" PathArguments.none)]))])))
                                none),
                              (Stmt.letStmt
                                []
                                (Pat.ident false false "field_ty" none)
                                (some
                                  (Expr.matchExpr
                                    (Expr.path
                                      none
                                      (Path.mk false [(PathSegment.mk "root" PathArguments.none)]))
                                    [
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
                                              (Member.named "sized_fields")
                                              true
                                              (Pat.ident false false "sized_fields" none)),
                                            (FieldPat.mk
                                              []
                                              (Member.named "unsized_field")
                                              true
                                              (Pat.ident false false "unsized_field" none))]
                                          true)
                                        none
                                        (Expr.block
                                          none
                                          (Block.mk
                                            [
                                              (Stmt.expr
                                                (Expr.ite
                                                  (Expr.binary
                                                    (Expr.binary
                                                      (Expr.path
                                                        none
                                                        (Path.mk
                                                          false
                                                          [
                                                            (PathSegment.mk
                                                              "field"
                                                              PathArguments.none)]))
                                                      BinOp.ge
                                                      (Expr.lit (Lit.int 0 "")))
                                                    BinOp.and
                                                    (Expr.binary
                                                      (Expr.path
                                                        none
                                                        (Path.mk
                                                          false
                                                          [
                                                            (PathSegment.mk
                                                              "field"
                                                              PathArguments.none)]))
                                                      BinOp.lt
                                                      (Expr.methodCall
                                                        (Expr.path
                                                          none
                                                          (Path.mk
                                                            false
                                                            [
                                                              (PathSegment.mk
                                                                "sized_fields"
                                                                PathArguments.none)]))
                                                        "len"
                                                        none
                                                        [])))
                                                  (Block.mk
                                                    [
                                                      (Stmt.expr
                                                        (Expr.field
                                                          (Expr.index
                                                            (Expr.path
                                                              none
                                                              (Path.mk
                                                                false
                                                                [
                                                                  (PathSegment.mk
                                                                    "sized_fields"
                                                                    PathArguments.none)]))
                                                            (Expr.path
                                                              none
                                                              (Path.mk
                                                                false
                                                                [
                                                                  (PathSegment.mk
                                                                    "field"
                                                                    PathArguments.none)])))
                                                          (Member.unnamed 1))
                                                        false)])
                                                  (some
                                                    (Expr.ite
                                                      (Expr.binary
                                                        (Expr.path
                                                          none
                                                          (Path.mk
                                                            false
                                                            [
                                                              (PathSegment.mk
                                                                "field"
                                                                PathArguments.none)]))
                                                        BinOp.eq
                                                        (Expr.methodCall
                                                          (Expr.path
                                                            none
                                                            (Path.mk
                                                              false
                                                              [
                                                                (PathSegment.mk
                                                                  "sized_fields"
                                                                  PathArguments.none)]))
                                                          "len"
                                                          none
                                                          []))
                                                      (Block.mk
                                                        [
                                                          (Stmt.letStmt
                                                            []
                                                            (Pat.tupleStruct
                                                              none
                                                              (Path.mk
                                                                false
                                                                [
                                                                  (PathSegment.mk
                                                                    "Some"
                                                                    PathArguments.none)])
                                                              [
                                                                (Pat.ident
                                                                  false
                                                                  false
                                                                  "unsized_ty"
                                                                  none)])
                                                            (some
                                                              (Expr.path
                                                                none
                                                                (Path.mk
                                                                  false
                                                                  [
                                                                    (PathSegment.mk
                                                                      "unsized_field"
                                                                      PathArguments.none)])))
                                                            (some
                                                              (Expr.block
                                                                none
                                                                (Block.mk
                                                                  [
                                                                    (Stmt.macro
                                                                      []
                                                                      (Macro.mk
                                                                        (Path.mk
                                                                          false
                                                                          [
                                                                            (PathSegment.mk
                                                                              "throw_ill_formed"
                                                                              PathArguments.none)])
                                                                        MacroDelimiter.paren
                                                                        (MacroBody.exprs
                                                                          [
                                                                            (Expr.lit
                                                                              (Lit.str
                                                                                "PlaceExpr::Field: invalid field"))]
                                                                          false))
                                                                      true)])))),
                                                          (Stmt.expr
                                                            (Expr.path
                                                              none
                                                              (Path.mk
                                                                false
                                                                [
                                                                  (PathSegment.mk
                                                                    "unsized_ty"
                                                                    PathArguments.none)]))
                                                            false)])
                                                      (some
                                                        (Expr.block
                                                          none
                                                          (Block.mk
                                                            [
                                                              (Stmt.macro
                                                                []
                                                                (Macro.mk
                                                                  (Path.mk
                                                                    false
                                                                    [
                                                                      (PathSegment.mk
                                                                        "throw_ill_formed"
                                                                        PathArguments.none)])
                                                                  MacroDelimiter.paren
                                                                  (MacroBody.exprs
                                                                    [
                                                                      (Expr.lit
                                                                        (Lit.str
                                                                          "PlaceExpr::Field: invalid field"))]
                                                                    false))
                                                                true)]))))))
                                                false)]))),
                                      (Arm.mk
                                        []
                                        (Pat.struct
                                          none
                                          (Path.mk
                                            false
                                            [
                                              (PathSegment.mk "Type" PathArguments.none),
                                              (PathSegment.mk "Union" PathArguments.none)])
                                          [
                                            (FieldPat.mk
                                              []
                                              (Member.named "fields")
                                              true
                                              (Pat.ident false false "fields" none))]
                                          true)
                                        none
                                        (Expr.block
                                          none
                                          (Block.mk
                                            [
                                              (Stmt.expr
                                                (Expr.matchExpr
                                                  (Expr.methodCall
                                                    (Expr.path
                                                      none
                                                      (Path.mk
                                                        false
                                                        [
                                                          (PathSegment.mk
                                                            "fields"
                                                            PathArguments.none)]))
                                                    "get"
                                                    none
                                                    [
                                                      (Expr.path
                                                        none
                                                        (Path.mk
                                                          false
                                                          [
                                                            (PathSegment.mk
                                                              "field"
                                                              PathArguments.none)]))])
                                                  [
                                                    (Arm.mk
                                                      []
                                                      (Pat.ident false false "None" none)
                                                      none
                                                      (Expr.macro
                                                        (Macro.mk
                                                          (Path.mk
                                                            false
                                                            [
                                                              (PathSegment.mk
                                                                "throw_ill_formed"
                                                                PathArguments.none)])
                                                          MacroDelimiter.paren
                                                          (MacroBody.exprs
                                                            [
                                                              (Expr.lit
                                                                (Lit.str
                                                                  "PlaceExpr::Field: invalid field"))]
                                                            false)))),
                                                    (Arm.mk
                                                      []
                                                      (Pat.tupleStruct
                                                        none
                                                        (Path.mk
                                                          false
                                                          [
                                                            (PathSegment.mk
                                                              "Some"
                                                              PathArguments.none)])
                                                        [(Pat.ident false false "field" none)])
                                                      none
                                                      (Expr.field
                                                        (Expr.path
                                                          none
                                                          (Path.mk
                                                            false
                                                            [
                                                              (PathSegment.mk
                                                                "field"
                                                                PathArguments.none)]))
                                                        (Member.unnamed 1)))])
                                                false)]))),
                                      (Arm.mk
                                        []
                                        Pat.wild
                                        none
                                        (Expr.macro
                                          (Macro.mk
                                            (Path.mk
                                              false
                                              [
                                                (PathSegment.mk
                                                  "throw_ill_formed"
                                                  PathArguments.none)])
                                            MacroDelimiter.paren
                                            (MacroBody.exprs
                                              [
                                                (Expr.lit
                                                  (Lit.str
                                                    "PlaceExpr::Field: expression does not match type"))]
                                              false))))]))
                                none),
                              (Stmt.expr
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "field_ty" PathArguments.none)]))
                                false)]))),
                      (Arm.mk
                        []
                        (Pat.struct
                          none
                          (Path.mk false [(PathSegment.mk "Index" PathArguments.none)])
                          [
                            (FieldPat.mk
                              []
                              (Member.named "root")
                              true
                              (Pat.ident false false "root" none)),
                            (FieldPat.mk
                              []
                              (Member.named "index")
                              true
                              (Pat.ident false false "index" none))]
                          false)
                        none
                        (Expr.block
                          none
                          (Block.mk
                            [
                              (Stmt.letStmt
                                []
                                (Pat.ident false false "root" none)
                                (some
                                  (Expr.tryExpr
                                    (Expr.methodCall
                                      (Expr.path
                                        none
                                        (Path.mk false [(PathSegment.mk "root" PathArguments.none)]))
                                      "check_wf"
                                      (some
                                        [
                                          (GenericArgument.type
                                            (Ty.path
                                              none
                                              (Path.mk
                                                false
                                                [(PathSegment.mk "T" PathArguments.none)])))])
                                      [
                                        (Expr.path
                                          none
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "locals" PathArguments.none)])),
                                        (Expr.path
                                          none
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "prog" PathArguments.none)]))])))
                                none),
                              (Stmt.letStmt
                                []
                                (Pat.ident false false "index" none)
                                (some
                                  (Expr.tryExpr
                                    (Expr.methodCall
                                      (Expr.path
                                        none
                                        (Path.mk
                                          false
                                          [(PathSegment.mk "index" PathArguments.none)]))
                                      "check_wf"
                                      (some
                                        [
                                          (GenericArgument.type
                                            (Ty.path
                                              none
                                              (Path.mk
                                                false
                                                [(PathSegment.mk "T" PathArguments.none)])))])
                                      [
                                        (Expr.path
                                          none
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "locals" PathArguments.none)])),
                                        (Expr.path
                                          none
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "prog" PathArguments.none)]))])))
                                none),
                              (Stmt.expr
                                (Expr.tryExpr
                                  (Expr.call
                                    (Expr.path
                                      none
                                      (Path.mk
                                        false
                                        [(PathSegment.mk "ensure_wf" PathArguments.none)]))
                                    [
                                      (Expr.macro
                                        (Macro.mk
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "matches" PathArguments.none)])
                                          MacroDelimiter.paren
                                          (MacroBody.exprAndPat
                                            (Expr.path
                                              none
                                              (Path.mk
                                                false
                                                [(PathSegment.mk "index" PathArguments.none)]))
                                            (Pat.tupleStruct
                                              none
                                              (Path.mk
                                                false
                                                [
                                                  (PathSegment.mk "Type" PathArguments.none),
                                                  (PathSegment.mk "Int" PathArguments.none)])
                                              [Pat.wild])
                                            none))),
                                      (Expr.lit (Lit.str "PlaceExpr::Index: invalid index type"))]))
                                true),
                              (Stmt.expr
                                (Expr.matchExpr
                                  (Expr.path
                                    none
                                    (Path.mk false [(PathSegment.mk "root" PathArguments.none)]))
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
                                                (PathSegment.mk "Type" PathArguments.none),
                                                (PathSegment.mk "Array" PathArguments.none)])
                                            [
                                              (FieldPat.mk
                                                []
                                                (Member.named "elem")
                                                true
                                                (Pat.ident false false "elem" none))]
                                            true),
                                          (Pat.struct
                                            none
                                            (Path.mk
                                              false
                                              [
                                                (PathSegment.mk "Type" PathArguments.none),
                                                (PathSegment.mk "Slice" PathArguments.none)])
                                            [
                                              (FieldPat.mk
                                                []
                                                (Member.named "elem")
                                                true
                                                (Pat.ident false false "elem" none))]
                                            false)])
                                      none
                                      (Expr.path
                                        none
                                        (Path.mk false [(PathSegment.mk "elem" PathArguments.none)]))),
                                    (Arm.mk
                                      []
                                      Pat.wild
                                      none
                                      (Expr.macro
                                        (Macro.mk
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "throw_ill_formed" PathArguments.none)])
                                          MacroDelimiter.paren
                                          (MacroBody.exprs
                                            [
                                              (Expr.lit
                                                (Lit.str
                                                  "PlaceExpr::Index: expression type is not indexable"))]
                                            false))))])
                                false)]))),
                      (Arm.mk
                        []
                        (Pat.struct
                          none
                          (Path.mk false [(PathSegment.mk "Downcast" PathArguments.none)])
                          [
                            (FieldPat.mk
                              []
                              (Member.named "root")
                              true
                              (Pat.ident false false "root" none)),
                            (FieldPat.mk
                              []
                              (Member.named "discriminant")
                              true
                              (Pat.ident false false "discriminant" none))]
                          false)
                        none
                        (Expr.block
                          none
                          (Block.mk
                            [
                              (Stmt.letStmt
                                []
                                (Pat.ident false false "root" none)
                                (some
                                  (Expr.tryExpr
                                    (Expr.methodCall
                                      (Expr.path
                                        none
                                        (Path.mk false [(PathSegment.mk "root" PathArguments.none)]))
                                      "check_wf"
                                      (some
                                        [
                                          (GenericArgument.type
                                            (Ty.path
                                              none
                                              (Path.mk
                                                false
                                                [(PathSegment.mk "T" PathArguments.none)])))])
                                      [
                                        (Expr.path
                                          none
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "locals" PathArguments.none)])),
                                        (Expr.path
                                          none
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "prog" PathArguments.none)]))])))
                                none),
                              (Stmt.expr
                                (Expr.matchExpr
                                  (Expr.path
                                    none
                                    (Path.mk false [(PathSegment.mk "root" PathArguments.none)]))
                                  [
                                    (Arm.mk
                                      []
                                      (Pat.struct
                                        none
                                        (Path.mk
                                          false
                                          [
                                            (PathSegment.mk "Type" PathArguments.none),
                                            (PathSegment.mk "Enum" PathArguments.none)])
                                        [
                                          (FieldPat.mk
                                            []
                                            (Member.named "variants")
                                            true
                                            (Pat.ident false false "variants" none))]
                                        true)
                                      none
                                      (Expr.block
                                        none
                                        (Block.mk
                                          [
                                            (Stmt.letStmt
                                              []
                                              (Pat.tupleStruct
                                                none
                                                (Path.mk
                                                  false
                                                  [(PathSegment.mk "Some" PathArguments.none)])
                                                [(Pat.ident false false "variant" none)])
                                              (some
                                                (Expr.methodCall
                                                  (Expr.path
                                                    none
                                                    (Path.mk
                                                      false
                                                      [
                                                        (PathSegment.mk
                                                          "variants"
                                                          PathArguments.none)]))
                                                  "get"
                                                  none
                                                  [
                                                    (Expr.path
                                                      none
                                                      (Path.mk
                                                        false
                                                        [
                                                          (PathSegment.mk
                                                            "discriminant"
                                                            PathArguments.none)]))]))
                                              (some
                                                (Expr.block
                                                  none
                                                  (Block.mk
                                                    [
                                                      (Stmt.macro
                                                        []
                                                        (Macro.mk
                                                          (Path.mk
                                                            false
                                                            [
                                                              (PathSegment.mk
                                                                "throw_ill_formed"
                                                                PathArguments.none)])
                                                          MacroDelimiter.paren
                                                          (MacroBody.exprs
                                                            [
                                                              (Expr.lit
                                                                (Lit.str
                                                                  "PlaceExpr::Downcast: invalid discriminant"))]
                                                            false))
                                                        true)])))),
                                            (Stmt.expr
                                              (Expr.field
                                                (Expr.path
                                                  none
                                                  (Path.mk
                                                    false
                                                    [(PathSegment.mk "variant" PathArguments.none)]))
                                                (Member.named "ty"))
                                              false)]))),
                                    (Arm.mk
                                      []
                                      Pat.wild
                                      none
                                      (Expr.macro
                                        (Macro.mk
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "throw_ill_formed" PathArguments.none)])
                                          MacroDelimiter.paren
                                          (MacroBody.exprs
                                            [
                                              (Expr.lit
                                                (Lit.str "PlaceExpr::Downcast: invalid root type"))]
                                            false))))])
                                false)])))])])
              false)]))])

/-- `spec/lang/well-formed.md:627` -/
def impl_ArgumentExpr__check_wf : Item :=
  (Item.impl
    []
    false
    false
    (Generics.mk [] [])
    false
    none
    (Ty.path none (Path.mk false [(PathSegment.mk "ArgumentExpr" PathArguments.none)]))
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
          "check_wf"
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
              (Pat.ident false false "locals" none)
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
                              (Path.mk false [(PathSegment.mk "Type" PathArguments.none)])))]))]))),
            (FnArg.typed
              []
              (Pat.ident false false "prog" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "Program" PathArguments.none)])))]
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
                            (Path.mk false [(PathSegment.mk "Type" PathArguments.none)])))]))]))))
        (Block.mk
          [
            (Stmt.expr
              (Expr.call
                (Expr.path none (Path.mk false [(PathSegment.mk "ret" PathArguments.none)]))
                [
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
                              (PathSegment.mk "ArgumentExpr" PathArguments.none),
                              (PathSegment.mk "ByValue" PathArguments.none)])
                          [(Pat.ident false false "value" none)])
                        none
                        (Expr.tryExpr
                          (Expr.methodCall
                            (Expr.path
                              none
                              (Path.mk false [(PathSegment.mk "value" PathArguments.none)]))
                            "check_wf"
                            (some
                              [
                                (GenericArgument.type
                                  (Ty.path
                                    none
                                    (Path.mk false [(PathSegment.mk "T" PathArguments.none)])))])
                            [
                              (Expr.path
                                none
                                (Path.mk false [(PathSegment.mk "locals" PathArguments.none)])),
                              (Expr.path
                                none
                                (Path.mk false [(PathSegment.mk "prog" PathArguments.none)]))]))),
                      (Arm.mk
                        []
                        (Pat.tupleStruct
                          none
                          (Path.mk
                            false
                            [
                              (PathSegment.mk "ArgumentExpr" PathArguments.none),
                              (PathSegment.mk "InPlace" PathArguments.none)])
                          [(Pat.ident false false "place" none)])
                        none
                        (Expr.tryExpr
                          (Expr.methodCall
                            (Expr.path
                              none
                              (Path.mk false [(PathSegment.mk "place" PathArguments.none)]))
                            "check_wf"
                            (some
                              [
                                (GenericArgument.type
                                  (Ty.path
                                    none
                                    (Path.mk false [(PathSegment.mk "T" PathArguments.none)])))])
                            [
                              (Expr.path
                                none
                                (Path.mk false [(PathSegment.mk "locals" PathArguments.none)])),
                              (Expr.path
                                none
                                (Path.mk false [(PathSegment.mk "prog" PathArguments.none)]))])))])])
              false)]))])

/-- `spec/lang/well-formed.md:640` -/
def impl_Statement__check_wf : Item :=
  (Item.impl
    []
    false
    false
    (Generics.mk [] [])
    false
    none
    (Ty.path none (Path.mk false [(PathSegment.mk "Statement" PathArguments.none)]))
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
          "check_wf"
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
              (Pat.ident false false "func" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "Function" PathArguments.none)]))),
            (FnArg.typed
              []
              (Pat.ident false false "prog" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "Program" PathArguments.none)])))]
          false
          (some
            (Ty.path
              none
              (Path.mk
                false
                [
                  (PathSegment.mk
                    "Result"
                    (PathArguments.angleBracketed false [(GenericArgument.type (Ty.tuple []))]))]))))
        (Block.mk
          [
            (Stmt.item
              (Item.use [] Visibility.inherited false (UseTree.path "Statement" UseTree.glob))),
            (Stmt.expr
              (Expr.matchExpr
                (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                [
                  (Arm.mk
                    []
                    (Pat.struct
                      none
                      (Path.mk false [(PathSegment.mk "Assign" PathArguments.none)])
                      [
                        (FieldPat.mk
                          []
                          (Member.named "destination")
                          true
                          (Pat.ident false false "destination" none)),
                        (FieldPat.mk
                          []
                          (Member.named "source")
                          true
                          (Pat.ident false false "source" none))]
                      false)
                    none
                    (Expr.block
                      none
                      (Block.mk
                        [
                          (Stmt.letStmt
                            []
                            (Pat.ident false false "left" none)
                            (some
                              (Expr.tryExpr
                                (Expr.methodCall
                                  (Expr.path
                                    none
                                    (Path.mk
                                      false
                                      [(PathSegment.mk "destination" PathArguments.none)]))
                                  "check_wf"
                                  (some
                                    [
                                      (GenericArgument.type
                                        (Ty.path
                                          none
                                          (Path.mk false [(PathSegment.mk "T" PathArguments.none)])))])
                                  [
                                    (Expr.field
                                      (Expr.path
                                        none
                                        (Path.mk false [(PathSegment.mk "func" PathArguments.none)]))
                                      (Member.named "locals")),
                                    (Expr.path
                                      none
                                      (Path.mk false [(PathSegment.mk "prog" PathArguments.none)]))])))
                            none),
                          (Stmt.letStmt
                            []
                            (Pat.ident false false "right" none)
                            (some
                              (Expr.tryExpr
                                (Expr.methodCall
                                  (Expr.path
                                    none
                                    (Path.mk false [(PathSegment.mk "source" PathArguments.none)]))
                                  "check_wf"
                                  (some
                                    [
                                      (GenericArgument.type
                                        (Ty.path
                                          none
                                          (Path.mk false [(PathSegment.mk "T" PathArguments.none)])))])
                                  [
                                    (Expr.field
                                      (Expr.path
                                        none
                                        (Path.mk false [(PathSegment.mk "func" PathArguments.none)]))
                                      (Member.named "locals")),
                                    (Expr.path
                                      none
                                      (Path.mk false [(PathSegment.mk "prog" PathArguments.none)]))])))
                            none),
                          (Stmt.expr
                            (Expr.tryExpr
                              (Expr.call
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "ensure_wf" PathArguments.none)]))
                                [
                                  (Expr.binary
                                    (Expr.path
                                      none
                                      (Path.mk false [(PathSegment.mk "left" PathArguments.none)]))
                                    BinOp.eq
                                    (Expr.path
                                      none
                                      (Path.mk false [(PathSegment.mk "right" PathArguments.none)]))),
                                  (Expr.lit
                                    (Lit.str
                                      "Statement::Assign: destination and source type differ"))]))
                            true),
                          (Stmt.macro
                            []
                            (Macro.mk
                              (Path.mk false [(PathSegment.mk "assert" PathArguments.none)])
                              MacroDelimiter.paren
                              (MacroBody.exprs
                                [
                                  (Expr.methodCall
                                    (Expr.methodCall
                                      (Expr.path
                                        none
                                        (Path.mk
                                          false
                                          [(PathSegment.mk "right" PathArguments.none)]))
                                      "layout"
                                      (some
                                        [
                                          (GenericArgument.type
                                            (Ty.path
                                              none
                                              (Path.mk
                                                false
                                                [(PathSegment.mk "T" PathArguments.none)])))])
                                      [])
                                    "is_sized"
                                    none
                                    []),
                                  (Expr.lit (Lit.str "ValueExpr always return sized types"))]
                                false))
                            true)]))),
                  (Arm.mk
                    []
                    (Pat.tupleStruct
                      none
                      (Path.mk false [(PathSegment.mk "PlaceMention" PathArguments.none)])
                      [(Pat.ident false false "place" none)])
                    none
                    (Expr.block
                      none
                      (Block.mk
                        [
                          (Stmt.expr
                            (Expr.tryExpr
                              (Expr.methodCall
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "place" PathArguments.none)]))
                                "check_wf"
                                (some
                                  [
                                    (GenericArgument.type
                                      (Ty.path
                                        none
                                        (Path.mk false [(PathSegment.mk "T" PathArguments.none)])))])
                                [
                                  (Expr.field
                                    (Expr.path
                                      none
                                      (Path.mk false [(PathSegment.mk "func" PathArguments.none)]))
                                    (Member.named "locals")),
                                  (Expr.path
                                    none
                                    (Path.mk false [(PathSegment.mk "prog" PathArguments.none)]))]))
                            true)]))),
                  (Arm.mk
                    []
                    (Pat.struct
                      none
                      (Path.mk false [(PathSegment.mk "SetDiscriminant" PathArguments.none)])
                      [
                        (FieldPat.mk
                          []
                          (Member.named "destination")
                          true
                          (Pat.ident false false "destination" none)),
                        (FieldPat.mk
                          []
                          (Member.named "value")
                          true
                          (Pat.ident false false "value" none))]
                      false)
                    none
                    (Expr.block
                      none
                      (Block.mk
                        [
                          (Stmt.letStmt
                            []
                            (Pat.struct
                              none
                              (Path.mk
                                false
                                [
                                  (PathSegment.mk "Type" PathArguments.none),
                                  (PathSegment.mk "Enum" PathArguments.none)])
                              [
                                (FieldPat.mk
                                  []
                                  (Member.named "variants")
                                  true
                                  (Pat.ident false false "variants" none))]
                              true)
                            (some
                              (Expr.tryExpr
                                (Expr.methodCall
                                  (Expr.path
                                    none
                                    (Path.mk
                                      false
                                      [(PathSegment.mk "destination" PathArguments.none)]))
                                  "check_wf"
                                  (some
                                    [
                                      (GenericArgument.type
                                        (Ty.path
                                          none
                                          (Path.mk false [(PathSegment.mk "T" PathArguments.none)])))])
                                  [
                                    (Expr.field
                                      (Expr.path
                                        none
                                        (Path.mk false [(PathSegment.mk "func" PathArguments.none)]))
                                      (Member.named "locals")),
                                    (Expr.path
                                      none
                                      (Path.mk false [(PathSegment.mk "prog" PathArguments.none)]))])))
                            (some
                              (Expr.block
                                none
                                (Block.mk
                                  [
                                    (Stmt.macro
                                      []
                                      (Macro.mk
                                        (Path.mk
                                          false
                                          [(PathSegment.mk "throw_ill_formed" PathArguments.none)])
                                        MacroDelimiter.paren
                                        (MacroBody.exprs
                                          [
                                            (Expr.lit
                                              (Lit.str "Statement::SetDiscriminant: invalid type"))]
                                          false))
                                      true)])))),
                          (Stmt.expr
                            (Expr.ite
                              (Expr.binary
                                (Expr.methodCall
                                  (Expr.path
                                    none
                                    (Path.mk false [(PathSegment.mk "variants" PathArguments.none)]))
                                  "get"
                                  none
                                  [
                                    (Expr.path
                                      none
                                      (Path.mk false [(PathSegment.mk "value" PathArguments.none)]))])
                                BinOp.eq
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "None" PathArguments.none)])))
                              (Block.mk
                                [
                                  (Stmt.expr
                                    (Expr.macro
                                      (Macro.mk
                                        (Path.mk
                                          false
                                          [(PathSegment.mk "throw_ill_formed" PathArguments.none)])
                                        MacroDelimiter.paren
                                        (MacroBody.exprs
                                          [
                                            (Expr.lit
                                              (Lit.str
                                                "Statement::SetDiscriminant: invalid discriminant write"))]
                                          false)))
                                    false)])
                              none)
                            false)]))),
                  (Arm.mk
                    []
                    (Pat.struct
                      none
                      (Path.mk false [(PathSegment.mk "Validate" PathArguments.none)])
                      [
                        (FieldPat.mk
                          []
                          (Member.named "place")
                          true
                          (Pat.ident false false "place" none)),
                        (FieldPat.mk [] (Member.named "fn_entry") false Pat.wild)]
                      false)
                    none
                    (Expr.block
                      none
                      (Block.mk
                        [
                          (Stmt.letStmt
                            []
                            (Pat.ident false false "ty" none)
                            (some
                              (Expr.tryExpr
                                (Expr.methodCall
                                  (Expr.path
                                    none
                                    (Path.mk false [(PathSegment.mk "place" PathArguments.none)]))
                                  "check_wf"
                                  (some
                                    [
                                      (GenericArgument.type
                                        (Ty.path
                                          none
                                          (Path.mk false [(PathSegment.mk "T" PathArguments.none)])))])
                                  [
                                    (Expr.field
                                      (Expr.path
                                        none
                                        (Path.mk false [(PathSegment.mk "func" PathArguments.none)]))
                                      (Member.named "locals")),
                                    (Expr.path
                                      none
                                      (Path.mk false [(PathSegment.mk "prog" PathArguments.none)]))])))
                            none),
                          (Stmt.expr
                            (Expr.tryExpr
                              (Expr.call
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "ensure_wf" PathArguments.none)]))
                                [
                                  (Expr.methodCall
                                    (Expr.methodCall
                                      (Expr.path
                                        none
                                        (Path.mk false [(PathSegment.mk "ty" PathArguments.none)]))
                                      "layout"
                                      (some
                                        [
                                          (GenericArgument.type
                                            (Ty.path
                                              none
                                              (Path.mk
                                                false
                                                [(PathSegment.mk "T" PathArguments.none)])))])
                                      [])
                                    "is_sized"
                                    none
                                    []),
                                  (Expr.lit (Lit.str "Statement::Validate: unsized place"))]))
                            true)]))),
                  (Arm.mk
                    []
                    (Pat.struct
                      none
                      (Path.mk false [(PathSegment.mk "Deinit" PathArguments.none)])
                      [
                        (FieldPat.mk
                          []
                          (Member.named "place")
                          true
                          (Pat.ident false false "place" none))]
                      false)
                    none
                    (Expr.block
                      none
                      (Block.mk
                        [
                          (Stmt.letStmt
                            []
                            (Pat.ident false false "ty" none)
                            (some
                              (Expr.tryExpr
                                (Expr.methodCall
                                  (Expr.path
                                    none
                                    (Path.mk false [(PathSegment.mk "place" PathArguments.none)]))
                                  "check_wf"
                                  (some
                                    [
                                      (GenericArgument.type
                                        (Ty.path
                                          none
                                          (Path.mk false [(PathSegment.mk "T" PathArguments.none)])))])
                                  [
                                    (Expr.field
                                      (Expr.path
                                        none
                                        (Path.mk false [(PathSegment.mk "func" PathArguments.none)]))
                                      (Member.named "locals")),
                                    (Expr.path
                                      none
                                      (Path.mk false [(PathSegment.mk "prog" PathArguments.none)]))])))
                            none),
                          (Stmt.expr
                            (Expr.tryExpr
                              (Expr.call
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "ensure_wf" PathArguments.none)]))
                                [
                                  (Expr.methodCall
                                    (Expr.methodCall
                                      (Expr.path
                                        none
                                        (Path.mk false [(PathSegment.mk "ty" PathArguments.none)]))
                                      "layout"
                                      (some
                                        [
                                          (GenericArgument.type
                                            (Ty.path
                                              none
                                              (Path.mk
                                                false
                                                [(PathSegment.mk "T" PathArguments.none)])))])
                                      [])
                                    "is_sized"
                                    none
                                    []),
                                  (Expr.lit (Lit.str "Statement::Deinit: unsized place"))]))
                            true)]))),
                  (Arm.mk
                    []
                    (Pat.tupleStruct
                      none
                      (Path.mk false [(PathSegment.mk "StorageLive" PathArguments.none)])
                      [(Pat.ident false false "local" none)])
                    none
                    (Expr.block
                      none
                      (Block.mk
                        [
                          (Stmt.expr
                            (Expr.tryExpr
                              (Expr.call
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "ensure_wf" PathArguments.none)]))
                                [
                                  (Expr.methodCall
                                    (Expr.field
                                      (Expr.path
                                        none
                                        (Path.mk false [(PathSegment.mk "func" PathArguments.none)]))
                                      (Member.named "locals"))
                                    "contains_key"
                                    none
                                    [
                                      (Expr.path
                                        none
                                        (Path.mk
                                          false
                                          [(PathSegment.mk "local" PathArguments.none)]))]),
                                  (Expr.lit
                                    (Lit.str "Statement::StorageLive: invalid local variable"))]))
                            true)]))),
                  (Arm.mk
                    []
                    (Pat.tupleStruct
                      none
                      (Path.mk false [(PathSegment.mk "StorageDead" PathArguments.none)])
                      [(Pat.ident false false "local" none)])
                    none
                    (Expr.block
                      none
                      (Block.mk
                        [
                          (Stmt.expr
                            (Expr.tryExpr
                              (Expr.call
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "ensure_wf" PathArguments.none)]))
                                [
                                  (Expr.methodCall
                                    (Expr.field
                                      (Expr.path
                                        none
                                        (Path.mk false [(PathSegment.mk "func" PathArguments.none)]))
                                      (Member.named "locals"))
                                    "contains_key"
                                    none
                                    [
                                      (Expr.path
                                        none
                                        (Path.mk
                                          false
                                          [(PathSegment.mk "local" PathArguments.none)]))]),
                                  (Expr.lit
                                    (Lit.str "Statement::StorageDead: invalid local variable"))]))
                            true),
                          (Stmt.expr
                            (Expr.ite
                              (Expr.binary
                                (Expr.binary
                                  (Expr.path
                                    none
                                    (Path.mk false [(PathSegment.mk "local" PathArguments.none)]))
                                  BinOp.eq
                                  (Expr.field
                                    (Expr.path
                                      none
                                      (Path.mk false [(PathSegment.mk "func" PathArguments.none)]))
                                    (Member.named "ret")))
                                BinOp.or
                                (Expr.methodCall
                                  (Expr.field
                                    (Expr.path
                                      none
                                      (Path.mk false [(PathSegment.mk "func" PathArguments.none)]))
                                    (Member.named "args"))
                                  "any"
                                  none
                                  [
                                    (Expr.closure
                                      false
                                      [(Pat.ident false false "arg_name" none)]
                                      none
                                      (Expr.binary
                                        (Expr.path
                                          none
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "local" PathArguments.none)]))
                                        BinOp.eq
                                        (Expr.path
                                          none
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "arg_name" PathArguments.none)]))))]))
                              (Block.mk
                                [
                                  (Stmt.macro
                                    []
                                    (Macro.mk
                                      (Path.mk
                                        false
                                        [(PathSegment.mk "throw_ill_formed" PathArguments.none)])
                                      MacroDelimiter.paren
                                      (MacroBody.exprs
                                        [
                                          (Expr.lit
                                            (Lit.str
                                              "Statement::StorageDead: trying to mark argument or return local as dead"))]
                                        false))
                                    true)])
                              none)
                            false)])))])
              false),
            (Stmt.expr
              (Expr.call
                (Expr.path none (Path.mk false [(PathSegment.mk "ret" PathArguments.none)]))
                [(Expr.tuple [])])
              false)]))])

/-- `spec/lang/well-formed.md:695` -/
def fn_is_atomic_binop : Item :=
  (Item.fn
    [
      (Attr.mk
        true
        "doc"
        (AttrMeta.nameValue
          " Predicate to indicate if integer bin-op can be used for atomic fetch operations.")),
      (Attr.mk true "doc" (AttrMeta.nameValue " Needed for atomic fetch operations.")),
      (Attr.mk true "doc" (AttrMeta.nameValue "")),
      (Attr.mk
        true
        "doc"
        (AttrMeta.nameValue
          " We limit the binops that are allowed to be atomic based on current LLVM and Rust API exposures."))]
    Visibility.inherited
    (Signature.mk
      false
      false
      false
      none
      "is_atomic_binop"
      (Generics.mk [] [])
      [
        (FnArg.typed
          []
          (Pat.ident false false "op" none)
          (Ty.path none (Path.mk false [(PathSegment.mk "IntBinOp" PathArguments.none)])))]
      false
      (some (Ty.path none (Path.mk false [(PathSegment.mk "bool" PathArguments.none)]))))
    (Block.mk
      [
        (Stmt.item (Item.use [] Visibility.inherited false (UseTree.rename "IntBinOp" "B"))),
        (Stmt.expr
          (Expr.matchExpr
            (Expr.path none (Path.mk false [(PathSegment.mk "op" PathArguments.none)]))
            [
              (Arm.mk
                []
                (Pat.or
                  [
                    (Pat.path
                      none
                      (Path.mk
                        false
                        [
                          (PathSegment.mk "B" PathArguments.none),
                          (PathSegment.mk "Add" PathArguments.none)])),
                    (Pat.path
                      none
                      (Path.mk
                        false
                        [
                          (PathSegment.mk "B" PathArguments.none),
                          (PathSegment.mk "Sub" PathArguments.none)]))])
                none
                (Expr.lit (Lit.bool true))),
              (Arm.mk [] Pat.wild none (Expr.lit (Lit.bool false)))])
          false)]))

/-- `spec/lang/well-formed.md:707` -/
def impl_Terminator__check_wf : Item :=
  (Item.impl
    []
    false
    false
    (Generics.mk [] [])
    false
    none
    (Ty.path none (Path.mk false [(PathSegment.mk "Terminator" PathArguments.none)]))
    [
      (ImplItem.fn
        [
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue " Check the terminator and the block transitions.")),
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue
              " `block_kind` is the kind of the block in which the terminator is used."))]
        Visibility.inherited
        false
        (Signature.mk
          false
          false
          false
          none
          "check_wf"
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
              (Pat.ident false false "block_kind" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "BbKind" PathArguments.none)]))),
            (FnArg.typed
              []
              (Pat.ident false false "func" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "Function" PathArguments.none)]))),
            (FnArg.typed
              []
              (Pat.ident false false "prog" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "Program" PathArguments.none)])))]
          false
          (some
            (Ty.path
              none
              (Path.mk
                false
                [
                  (PathSegment.mk
                    "Result"
                    (PathArguments.angleBracketed false [(GenericArgument.type (Ty.tuple []))]))]))))
        (Block.mk
          [
            (Stmt.item
              (Item.use [] Visibility.inherited false (UseTree.path "Terminator" UseTree.glob))),
            (Stmt.expr
              (Expr.matchExpr
                (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                [
                  (Arm.mk
                    []
                    (Pat.tupleStruct
                      none
                      (Path.mk false [(PathSegment.mk "Goto" PathArguments.none)])
                      [(Pat.ident false false "block_name" none)])
                    none
                    (Expr.block
                      none
                      (Block.mk
                        [
                          (Stmt.expr
                            (Expr.tryExpr
                              (Expr.methodCall
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "func" PathArguments.none)]))
                                "check_next_block"
                                none
                                [
                                  (Expr.path
                                    none
                                    (Path.mk
                                      false
                                      [(PathSegment.mk "block_kind" PathArguments.none)])),
                                  (Expr.path
                                    none
                                    (Path.mk
                                      false
                                      [(PathSegment.mk "block_name" PathArguments.none)]))]))
                            true)]))),
                  (Arm.mk
                    []
                    (Pat.struct
                      none
                      (Path.mk false [(PathSegment.mk "Switch" PathArguments.none)])
                      [
                        (FieldPat.mk
                          []
                          (Member.named "value")
                          true
                          (Pat.ident false false "value" none)),
                        (FieldPat.mk
                          []
                          (Member.named "cases")
                          true
                          (Pat.ident false false "cases" none)),
                        (FieldPat.mk
                          []
                          (Member.named "fallback")
                          true
                          (Pat.ident false false "fallback" none))]
                      false)
                    none
                    (Expr.block
                      none
                      (Block.mk
                        [
                          (Stmt.letStmt
                            []
                            (Pat.ident false false "ty" none)
                            (some
                              (Expr.tryExpr
                                (Expr.methodCall
                                  (Expr.path
                                    none
                                    (Path.mk false [(PathSegment.mk "value" PathArguments.none)]))
                                  "check_wf"
                                  (some
                                    [
                                      (GenericArgument.type
                                        (Ty.path
                                          none
                                          (Path.mk false [(PathSegment.mk "T" PathArguments.none)])))])
                                  [
                                    (Expr.field
                                      (Expr.path
                                        none
                                        (Path.mk false [(PathSegment.mk "func" PathArguments.none)]))
                                      (Member.named "locals")),
                                    (Expr.path
                                      none
                                      (Path.mk false [(PathSegment.mk "prog" PathArguments.none)]))])))
                            none),
                          (Stmt.letStmt
                            []
                            (Pat.tupleStruct
                              none
                              (Path.mk
                                false
                                [
                                  (PathSegment.mk "Type" PathArguments.none),
                                  (PathSegment.mk "Int" PathArguments.none)])
                              [(Pat.ident false false "switch_ty" none)])
                            (some
                              (Expr.path
                                none
                                (Path.mk false [(PathSegment.mk "ty" PathArguments.none)])))
                            (some
                              (Expr.block
                                none
                                (Block.mk
                                  [
                                    (Stmt.expr
                                      (Expr.macro
                                        (Macro.mk
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "throw_ill_formed" PathArguments.none)])
                                          MacroDelimiter.paren
                                          (MacroBody.exprs
                                            [
                                              (Expr.lit
                                                (Lit.str "Terminator::Switch: switch is not Int"))]
                                            false)))
                                      false)])))),
                          (Stmt.expr
                            (Expr.forLoop
                              none
                              (Pat.tuple
                                [
                                  (Pat.ident false false "case" none),
                                  (Pat.ident false false "next_block" none)])
                              (Expr.methodCall
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "cases" PathArguments.none)]))
                                "iter"
                                none
                                [])
                              (Block.mk
                                [
                                  (Stmt.expr
                                    (Expr.tryExpr
                                      (Expr.call
                                        (Expr.path
                                          none
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "ensure_wf" PathArguments.none)]))
                                        [
                                          (Expr.methodCall
                                            (Expr.path
                                              none
                                              (Path.mk
                                                false
                                                [(PathSegment.mk "switch_ty" PathArguments.none)]))
                                            "can_represent"
                                            none
                                            [
                                              (Expr.path
                                                none
                                                (Path.mk
                                                  false
                                                  [(PathSegment.mk "case" PathArguments.none)]))]),
                                          (Expr.lit
                                            (Lit.str
                                              "Terminator::Switch: value does not fit in switch type"))]))
                                    true),
                                  (Stmt.expr
                                    (Expr.tryExpr
                                      (Expr.methodCall
                                        (Expr.path
                                          none
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "func" PathArguments.none)]))
                                        "check_next_block"
                                        none
                                        [
                                          (Expr.path
                                            none
                                            (Path.mk
                                              false
                                              [(PathSegment.mk "block_kind" PathArguments.none)])),
                                          (Expr.path
                                            none
                                            (Path.mk
                                              false
                                              [(PathSegment.mk "next_block" PathArguments.none)]))]))
                                    true)]))
                            false),
                          (Stmt.expr
                            (Expr.tryExpr
                              (Expr.methodCall
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "func" PathArguments.none)]))
                                "check_next_block"
                                none
                                [
                                  (Expr.path
                                    none
                                    (Path.mk
                                      false
                                      [(PathSegment.mk "block_kind" PathArguments.none)])),
                                  (Expr.path
                                    none
                                    (Path.mk false [(PathSegment.mk "fallback" PathArguments.none)]))]))
                            true)]))),
                  (Arm.mk
                    []
                    (Pat.ident false false "Unreachable" none)
                    none
                    (Expr.block none (Block.mk []))),
                  (Arm.mk
                    []
                    (Pat.struct
                      none
                      (Path.mk false [(PathSegment.mk "Intrinsic" PathArguments.none)])
                      [
                        (FieldPat.mk
                          []
                          (Member.named "intrinsic")
                          true
                          (Pat.ident false false "intrinsic" none)),
                        (FieldPat.mk
                          []
                          (Member.named "arguments")
                          true
                          (Pat.ident false false "arguments" none)),
                        (FieldPat.mk
                          []
                          (Member.named "ret")
                          true
                          (Pat.ident false false "ret" none)),
                        (FieldPat.mk
                          []
                          (Member.named "next_block")
                          true
                          (Pat.ident false false "next_block" none))]
                      false)
                    none
                    (Expr.block
                      none
                      (Block.mk
                        [
                          (Stmt.letStmt
                            []
                            (Pat.ident false false "ret_ty" none)
                            (some
                              (Expr.tryExpr
                                (Expr.methodCall
                                  (Expr.path
                                    none
                                    (Path.mk false [(PathSegment.mk "ret" PathArguments.none)]))
                                  "check_wf"
                                  (some
                                    [
                                      (GenericArgument.type
                                        (Ty.path
                                          none
                                          (Path.mk false [(PathSegment.mk "T" PathArguments.none)])))])
                                  [
                                    (Expr.field
                                      (Expr.path
                                        none
                                        (Path.mk false [(PathSegment.mk "func" PathArguments.none)]))
                                      (Member.named "locals")),
                                    (Expr.path
                                      none
                                      (Path.mk false [(PathSegment.mk "prog" PathArguments.none)]))])))
                            none),
                          (Stmt.expr
                            (Expr.tryExpr
                              (Expr.call
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "ensure_wf" PathArguments.none)]))
                                [
                                  (Expr.methodCall
                                    (Expr.methodCall
                                      (Expr.path
                                        none
                                        (Path.mk
                                          false
                                          [(PathSegment.mk "ret_ty" PathArguments.none)]))
                                      "layout"
                                      (some
                                        [
                                          (GenericArgument.type
                                            (Ty.path
                                              none
                                              (Path.mk
                                                false
                                                [(PathSegment.mk "T" PathArguments.none)])))])
                                      [])
                                    "is_sized"
                                    none
                                    []),
                                  (Expr.lit (Lit.str "Terminator::Intrinsic: unsized return type"))]))
                            true),
                          (Stmt.expr
                            (Expr.forLoop
                              none
                              (Pat.ident false false "arg" none)
                              (Expr.path
                                none
                                (Path.mk false [(PathSegment.mk "arguments" PathArguments.none)]))
                              (Block.mk
                                [
                                  (Stmt.letStmt
                                    []
                                    (Pat.ident false false "arg_ty" none)
                                    (some
                                      (Expr.tryExpr
                                        (Expr.methodCall
                                          (Expr.path
                                            none
                                            (Path.mk
                                              false
                                              [(PathSegment.mk "arg" PathArguments.none)]))
                                          "check_wf"
                                          (some
                                            [
                                              (GenericArgument.type
                                                (Ty.path
                                                  none
                                                  (Path.mk
                                                    false
                                                    [(PathSegment.mk "T" PathArguments.none)])))])
                                          [
                                            (Expr.field
                                              (Expr.path
                                                none
                                                (Path.mk
                                                  false
                                                  [(PathSegment.mk "func" PathArguments.none)]))
                                              (Member.named "locals")),
                                            (Expr.path
                                              none
                                              (Path.mk
                                                false
                                                [(PathSegment.mk "prog" PathArguments.none)]))])))
                                    none),
                                  (Stmt.expr
                                    (Expr.tryExpr
                                      (Expr.call
                                        (Expr.path
                                          none
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "ensure_wf" PathArguments.none)]))
                                        [
                                          (Expr.methodCall
                                            (Expr.methodCall
                                              (Expr.path
                                                none
                                                (Path.mk
                                                  false
                                                  [(PathSegment.mk "arg_ty" PathArguments.none)]))
                                              "layout"
                                              (some
                                                [
                                                  (GenericArgument.type
                                                    (Ty.path
                                                      none
                                                      (Path.mk
                                                        false
                                                        [(PathSegment.mk "T" PathArguments.none)])))])
                                              [])
                                            "is_sized"
                                            none
                                            []),
                                          (Expr.lit
                                            (Lit.str "Terminator::Intrinsic: unsized argument type"))]))
                                    true)]))
                            false),
                          (Stmt.expr
                            (Expr.matchExpr
                              (Expr.path
                                none
                                (Path.mk false [(PathSegment.mk "intrinsic" PathArguments.none)]))
                              [
                                (Arm.mk
                                  []
                                  (Pat.tupleStruct
                                    none
                                    (Path.mk
                                      false
                                      [
                                        (PathSegment.mk "IntrinsicOp" PathArguments.none),
                                        (PathSegment.mk "AtomicFetchAndOp" PathArguments.none)])
                                    [(Pat.ident false false "op" none)])
                                  none
                                  (Expr.block
                                    none
                                    (Block.mk
                                      [
                                        (Stmt.expr
                                          (Expr.ite
                                            (Expr.unary
                                              UnOp.not
                                              (Expr.call
                                                (Expr.path
                                                  none
                                                  (Path.mk
                                                    false
                                                    [
                                                      (PathSegment.mk
                                                        "is_atomic_binop"
                                                        PathArguments.none)]))
                                                [
                                                  (Expr.path
                                                    none
                                                    (Path.mk
                                                      false
                                                      [(PathSegment.mk "op" PathArguments.none)]))]))
                                            (Block.mk
                                              [
                                                (Stmt.macro
                                                  []
                                                  (Macro.mk
                                                    (Path.mk
                                                      false
                                                      [
                                                        (PathSegment.mk
                                                          "throw_ill_formed"
                                                          PathArguments.none)])
                                                    MacroDelimiter.paren
                                                    (MacroBody.exprs
                                                      [
                                                        (Expr.lit
                                                          (Lit.str
                                                            "IntrinsicOp::AtomicFetchAndOp: non atomic op"))]
                                                      false))
                                                  true)])
                                            none)
                                          false)]))),
                                (Arm.mk [] Pat.wild none (Expr.block none (Block.mk [])))])
                            false),
                          (Stmt.expr
                            (Expr.ite
                              (Expr.letCond
                                (Pat.tupleStruct
                                  none
                                  (Path.mk false [(PathSegment.mk "Some" PathArguments.none)])
                                  [(Pat.ident false false "next_block" none)])
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "next_block" PathArguments.none)])))
                              (Block.mk
                                [
                                  (Stmt.expr
                                    (Expr.tryExpr
                                      (Expr.methodCall
                                        (Expr.path
                                          none
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "func" PathArguments.none)]))
                                        "check_next_block"
                                        none
                                        [
                                          (Expr.path
                                            none
                                            (Path.mk
                                              false
                                              [(PathSegment.mk "block_kind" PathArguments.none)])),
                                          (Expr.path
                                            none
                                            (Path.mk
                                              false
                                              [(PathSegment.mk "next_block" PathArguments.none)]))]))
                                    true)])
                              none)
                            false)]))),
                  (Arm.mk
                    []
                    (Pat.struct
                      none
                      (Path.mk false [(PathSegment.mk "Call" PathArguments.none)])
                      [
                        (FieldPat.mk
                          []
                          (Member.named "callee")
                          true
                          (Pat.ident false false "callee" none)),
                        (FieldPat.mk [] (Member.named "calling_convention") false Pat.wild),
                        (FieldPat.mk
                          []
                          (Member.named "arguments")
                          true
                          (Pat.ident false false "arguments" none)),
                        (FieldPat.mk
                          []
                          (Member.named "ret")
                          true
                          (Pat.ident false false "ret" none)),
                        (FieldPat.mk
                          []
                          (Member.named "next_block")
                          true
                          (Pat.ident false false "next_block" none)),
                        (FieldPat.mk
                          []
                          (Member.named "unwind_block")
                          true
                          (Pat.ident false false "unwind_block" none))]
                      false)
                    none
                    (Expr.block
                      none
                      (Block.mk
                        [
                          (Stmt.letStmt
                            []
                            (Pat.ident false false "ty" none)
                            (some
                              (Expr.tryExpr
                                (Expr.methodCall
                                  (Expr.path
                                    none
                                    (Path.mk false [(PathSegment.mk "callee" PathArguments.none)]))
                                  "check_wf"
                                  (some
                                    [
                                      (GenericArgument.type
                                        (Ty.path
                                          none
                                          (Path.mk false [(PathSegment.mk "T" PathArguments.none)])))])
                                  [
                                    (Expr.field
                                      (Expr.path
                                        none
                                        (Path.mk false [(PathSegment.mk "func" PathArguments.none)]))
                                      (Member.named "locals")),
                                    (Expr.path
                                      none
                                      (Path.mk false [(PathSegment.mk "prog" PathArguments.none)]))])))
                            none),
                          (Stmt.expr
                            (Expr.tryExpr
                              (Expr.call
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "ensure_wf" PathArguments.none)]))
                                [
                                  (Expr.macro
                                    (Macro.mk
                                      (Path.mk
                                        false
                                        [(PathSegment.mk "matches" PathArguments.none)])
                                      MacroDelimiter.paren
                                      (MacroBody.exprAndPat
                                        (Expr.path
                                          none
                                          (Path.mk false [(PathSegment.mk "ty" PathArguments.none)]))
                                        (Pat.tupleStruct
                                          none
                                          (Path.mk
                                            false
                                            [
                                              (PathSegment.mk "Type" PathArguments.none),
                                              (PathSegment.mk "Ptr" PathArguments.none)])
                                          [
                                            (Pat.path
                                              none
                                              (Path.mk
                                                false
                                                [
                                                  (PathSegment.mk "PtrType" PathArguments.none),
                                                  (PathSegment.mk "FnPtr" PathArguments.none)]))])
                                        none))),
                                  (Expr.lit (Lit.str "Terminator::Call: invalid type"))]))
                            true),
                          (Stmt.letStmt
                            []
                            (Pat.ident false false "ret_ty" none)
                            (some
                              (Expr.tryExpr
                                (Expr.methodCall
                                  (Expr.path
                                    none
                                    (Path.mk false [(PathSegment.mk "ret" PathArguments.none)]))
                                  "check_wf"
                                  (some
                                    [
                                      (GenericArgument.type
                                        (Ty.path
                                          none
                                          (Path.mk false [(PathSegment.mk "T" PathArguments.none)])))])
                                  [
                                    (Expr.field
                                      (Expr.path
                                        none
                                        (Path.mk false [(PathSegment.mk "func" PathArguments.none)]))
                                      (Member.named "locals")),
                                    (Expr.path
                                      none
                                      (Path.mk false [(PathSegment.mk "prog" PathArguments.none)]))])))
                            none),
                          (Stmt.expr
                            (Expr.tryExpr
                              (Expr.call
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "ensure_wf" PathArguments.none)]))
                                [
                                  (Expr.methodCall
                                    (Expr.methodCall
                                      (Expr.path
                                        none
                                        (Path.mk
                                          false
                                          [(PathSegment.mk "ret_ty" PathArguments.none)]))
                                      "layout"
                                      (some
                                        [
                                          (GenericArgument.type
                                            (Ty.path
                                              none
                                              (Path.mk
                                                false
                                                [(PathSegment.mk "T" PathArguments.none)])))])
                                      [])
                                    "is_sized"
                                    none
                                    []),
                                  (Expr.lit (Lit.str "Terminator::Call: unsized return type"))]))
                            true),
                          (Stmt.expr
                            (Expr.forLoop
                              none
                              (Pat.ident false false "arg" none)
                              (Expr.path
                                none
                                (Path.mk false [(PathSegment.mk "arguments" PathArguments.none)]))
                              (Block.mk
                                [
                                  (Stmt.letStmt
                                    []
                                    (Pat.ident false false "arg_ty" none)
                                    (some
                                      (Expr.tryExpr
                                        (Expr.methodCall
                                          (Expr.path
                                            none
                                            (Path.mk
                                              false
                                              [(PathSegment.mk "arg" PathArguments.none)]))
                                          "check_wf"
                                          (some
                                            [
                                              (GenericArgument.type
                                                (Ty.path
                                                  none
                                                  (Path.mk
                                                    false
                                                    [(PathSegment.mk "T" PathArguments.none)])))])
                                          [
                                            (Expr.field
                                              (Expr.path
                                                none
                                                (Path.mk
                                                  false
                                                  [(PathSegment.mk "func" PathArguments.none)]))
                                              (Member.named "locals")),
                                            (Expr.path
                                              none
                                              (Path.mk
                                                false
                                                [(PathSegment.mk "prog" PathArguments.none)]))])))
                                    none),
                                  (Stmt.expr
                                    (Expr.tryExpr
                                      (Expr.call
                                        (Expr.path
                                          none
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "ensure_wf" PathArguments.none)]))
                                        [
                                          (Expr.methodCall
                                            (Expr.methodCall
                                              (Expr.path
                                                none
                                                (Path.mk
                                                  false
                                                  [(PathSegment.mk "arg_ty" PathArguments.none)]))
                                              "layout"
                                              (some
                                                [
                                                  (GenericArgument.type
                                                    (Ty.path
                                                      none
                                                      (Path.mk
                                                        false
                                                        [(PathSegment.mk "T" PathArguments.none)])))])
                                              [])
                                            "is_sized"
                                            none
                                            []),
                                          (Expr.lit
                                            (Lit.str "Terminator::Call: unsized argument type"))]))
                                    true)]))
                            false),
                          (Stmt.expr
                            (Expr.ite
                              (Expr.letCond
                                (Pat.tupleStruct
                                  none
                                  (Path.mk false [(PathSegment.mk "Some" PathArguments.none)])
                                  [(Pat.ident false false "next_block" none)])
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "next_block" PathArguments.none)])))
                              (Block.mk
                                [
                                  (Stmt.expr
                                    (Expr.tryExpr
                                      (Expr.methodCall
                                        (Expr.path
                                          none
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "func" PathArguments.none)]))
                                        "check_next_block"
                                        none
                                        [
                                          (Expr.path
                                            none
                                            (Path.mk
                                              false
                                              [(PathSegment.mk "block_kind" PathArguments.none)])),
                                          (Expr.path
                                            none
                                            (Path.mk
                                              false
                                              [(PathSegment.mk "next_block" PathArguments.none)]))]))
                                    true)])
                              none)
                            false),
                          (Stmt.expr
                            (Expr.ite
                              (Expr.letCond
                                (Pat.tupleStruct
                                  none
                                  (Path.mk false [(PathSegment.mk "Some" PathArguments.none)])
                                  [(Pat.ident false false "unwind_block" none)])
                                (Expr.path
                                  none
                                  (Path.mk
                                    false
                                    [(PathSegment.mk "unwind_block" PathArguments.none)])))
                              (Block.mk
                                [
                                  (Stmt.expr
                                    (Expr.tryExpr
                                      (Expr.methodCall
                                        (Expr.path
                                          none
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "func" PathArguments.none)]))
                                        "check_unwind_block"
                                        none
                                        [
                                          (Expr.path
                                            none
                                            (Path.mk
                                              false
                                              [(PathSegment.mk "block_kind" PathArguments.none)])),
                                          (Expr.path
                                            none
                                            (Path.mk
                                              false
                                              [(PathSegment.mk "unwind_block" PathArguments.none)]))]))
                                    true)])
                              none)
                            false)]))),
                  (Arm.mk
                    []
                    (Pat.ident false false "Return" none)
                    none
                    (Expr.block
                      none
                      (Block.mk
                        [
                          (Stmt.expr
                            (Expr.tryExpr
                              (Expr.call
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "ensure_wf" PathArguments.none)]))
                                [
                                  (Expr.binary
                                    (Expr.path
                                      none
                                      (Path.mk
                                        false
                                        [(PathSegment.mk "block_kind" PathArguments.none)]))
                                    BinOp.eq
                                    (Expr.path
                                      none
                                      (Path.mk
                                        false
                                        [
                                          (PathSegment.mk "BbKind" PathArguments.none),
                                          (PathSegment.mk "Regular" PathArguments.none)]))),
                                  (Expr.lit
                                    (Lit.str
                                      "Terminator::Return has to be called in a regular block"))]))
                            true)]))),
                  (Arm.mk
                    []
                    (Pat.struct
                      none
                      (Path.mk false [(PathSegment.mk "StartUnwind" PathArguments.none)])
                      [
                        (FieldPat.mk
                          []
                          (Member.named "unwind_payload")
                          true
                          (Pat.ident false false "unwind_payload" none)),
                        (FieldPat.mk
                          []
                          (Member.named "unwind_block")
                          true
                          (Pat.ident false false "unwind_block" none))]
                      false)
                    none
                    (Expr.block
                      none
                      (Block.mk
                        [
                          (Stmt.letStmt
                            []
                            (Pat.ident false false "payload_type" none)
                            (some
                              (Expr.tryExpr
                                (Expr.methodCall
                                  (Expr.path
                                    none
                                    (Path.mk
                                      false
                                      [(PathSegment.mk "unwind_payload" PathArguments.none)]))
                                  "check_wf"
                                  (some
                                    [
                                      (GenericArgument.type
                                        (Ty.path
                                          none
                                          (Path.mk false [(PathSegment.mk "T" PathArguments.none)])))])
                                  [
                                    (Expr.field
                                      (Expr.path
                                        none
                                        (Path.mk false [(PathSegment.mk "func" PathArguments.none)]))
                                      (Member.named "locals")),
                                    (Expr.path
                                      none
                                      (Path.mk false [(PathSegment.mk "prog" PathArguments.none)]))])))
                            none),
                          (Stmt.expr
                            (Expr.tryExpr
                              (Expr.call
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "ensure_wf" PathArguments.none)]))
                                [
                                  (Expr.binary
                                    (Expr.path
                                      none
                                      (Path.mk
                                        false
                                        [(PathSegment.mk "payload_type" PathArguments.none)]))
                                    BinOp.eq
                                    (Expr.call
                                      (Expr.path
                                        none
                                        (Path.mk
                                          false
                                          [
                                            (PathSegment.mk "Type" PathArguments.none),
                                            (PathSegment.mk "Ptr" PathArguments.none)]))
                                      [
                                        (Expr.struct
                                          none
                                          (Path.mk
                                            false
                                            [
                                              (PathSegment.mk "PtrType" PathArguments.none),
                                              (PathSegment.mk "Raw" PathArguments.none)])
                                          [
                                            (FieldValue.mk
                                              []
                                              (Member.named "meta_kind")
                                              false
                                              (Expr.path
                                                none
                                                (Path.mk
                                                  false
                                                  [
                                                    (PathSegment.mk
                                                      "PointerMetaKind"
                                                      PathArguments.none),
                                                    (PathSegment.mk "None" PathArguments.none)])))]
                                          false
                                          none)])),
                                  (Expr.lit
                                    (Lit.str
                                      "Terminator::StartUnwind: the unwind payload should be a raw pointer"))]))
                            true),
                          (Stmt.expr
                            (Expr.tryExpr
                              (Expr.call
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "ensure_wf" PathArguments.none)]))
                                [
                                  (Expr.binary
                                    (Expr.path
                                      none
                                      (Path.mk
                                        false
                                        [(PathSegment.mk "block_kind" PathArguments.none)]))
                                    BinOp.eq
                                    (Expr.path
                                      none
                                      (Path.mk
                                        false
                                        [
                                          (PathSegment.mk "BbKind" PathArguments.none),
                                          (PathSegment.mk "Regular" PathArguments.none)]))),
                                  (Expr.lit
                                    (Lit.str
                                      "Terminator::StartUnwind has to be called in a regular block"))]))
                            true),
                          (Stmt.expr
                            (Expr.tryExpr
                              (Expr.methodCall
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "func" PathArguments.none)]))
                                "check_unwind_block"
                                none
                                [
                                  (Expr.path
                                    none
                                    (Path.mk
                                      false
                                      [(PathSegment.mk "block_kind" PathArguments.none)])),
                                  (Expr.path
                                    none
                                    (Path.mk
                                      false
                                      [(PathSegment.mk "unwind_block" PathArguments.none)]))]))
                            true)]))),
                  (Arm.mk
                    []
                    (Pat.tupleStruct
                      none
                      (Path.mk false [(PathSegment.mk "StopUnwind" PathArguments.none)])
                      [(Pat.ident false false "next_block" none)])
                    none
                    (Expr.block
                      none
                      (Block.mk
                        [
                          (Stmt.expr
                            (Expr.tryExpr
                              (Expr.call
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "ensure_wf" PathArguments.none)]))
                                [
                                  (Expr.binary
                                    (Expr.path
                                      none
                                      (Path.mk
                                        false
                                        [(PathSegment.mk "block_kind" PathArguments.none)]))
                                    BinOp.eq
                                    (Expr.path
                                      none
                                      (Path.mk
                                        false
                                        [
                                          (PathSegment.mk "BbKind" PathArguments.none),
                                          (PathSegment.mk "Catch" PathArguments.none)]))),
                                  (Expr.lit
                                    (Lit.str
                                      "Terminator::StopUnwind has to be called in a catch block"))]))
                            true),
                          (Stmt.expr
                            (Expr.tryExpr
                              (Expr.methodCall
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "func" PathArguments.none)]))
                                "check_next_block"
                                none
                                [
                                  (Expr.path
                                    none
                                    (Path.mk
                                      false
                                      [
                                        (PathSegment.mk "BbKind" PathArguments.none),
                                        (PathSegment.mk "Regular" PathArguments.none)])),
                                  (Expr.path
                                    none
                                    (Path.mk
                                      false
                                      [(PathSegment.mk "next_block" PathArguments.none)]))]))
                            true)]))),
                  (Arm.mk
                    []
                    (Pat.ident false false "ResumeUnwind" none)
                    none
                    (Expr.block
                      none
                      (Block.mk
                        [
                          (Stmt.expr
                            (Expr.tryExpr
                              (Expr.call
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "ensure_wf" PathArguments.none)]))
                                [
                                  (Expr.binary
                                    (Expr.path
                                      none
                                      (Path.mk
                                        false
                                        [(PathSegment.mk "block_kind" PathArguments.none)]))
                                    BinOp.eq
                                    (Expr.path
                                      none
                                      (Path.mk
                                        false
                                        [
                                          (PathSegment.mk "BbKind" PathArguments.none),
                                          (PathSegment.mk "Cleanup" PathArguments.none)]))),
                                  (Expr.lit
                                    (Lit.str
                                      "Terminator::ResumeUnwind: has to be called in cleanup block"))]))
                            true)])))])
              false),
            (Stmt.expr
              (Expr.call
                (Expr.path none (Path.mk false [(PathSegment.mk "ret" PathArguments.none)]))
                [(Expr.tuple [])])
              false)]))])

/-- `spec/lang/well-formed.md:812` -/
def impl_Function__check_wf : Item :=
  (Item.impl
    []
    false
    false
    (Generics.mk [] [])
    false
    none
    (Ty.path none (Path.mk false [(PathSegment.mk "Function" PathArguments.none)]))
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
          "check_wf"
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
              (Pat.ident false false "prog" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "Program" PathArguments.none)])))]
          false
          (some
            (Ty.path
              none
              (Path.mk
                false
                [
                  (PathSegment.mk
                    "Result"
                    (PathArguments.angleBracketed false [(GenericArgument.type (Ty.tuple []))]))]))))
        (Block.mk
          [
            (Stmt.expr
              (Expr.forLoop
                none
                (Pat.ident false false "ty" none)
                (Expr.methodCall
                  (Expr.field
                    (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                    (Member.named "locals"))
                  "values"
                  none
                  [])
                (Block.mk
                  [
                    (Stmt.expr
                      (Expr.tryExpr
                        (Expr.call
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "ensure_wf" PathArguments.none)]))
                          [
                            (Expr.methodCall
                              (Expr.methodCall
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "ty" PathArguments.none)]))
                                "layout"
                                (some
                                  [
                                    (GenericArgument.type
                                      (Ty.path
                                        none
                                        (Path.mk false [(PathSegment.mk "T" PathArguments.none)])))])
                                [])
                              "is_sized"
                              none
                              []),
                            (Expr.lit (Lit.str "Function: unsized local variable"))]))
                      true),
                    (Stmt.expr
                      (Expr.tryExpr
                        (Expr.methodCall
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "ty" PathArguments.none)]))
                          "check_wf"
                          (some
                            [
                              (GenericArgument.type
                                (Ty.path
                                  none
                                  (Path.mk false [(PathSegment.mk "T" PathArguments.none)])))])
                          [
                            (Expr.path
                              none
                              (Path.mk false [(PathSegment.mk "prog" PathArguments.none)]))]))
                      true)]))
              false),
            (Stmt.letStmt
              []
              (Pat.typed
                (Pat.ident false true "start_live" none)
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
                                (Path.mk false [(PathSegment.mk "LocalName" PathArguments.none)])))]))])))
              (some
                (Expr.call
                  (Expr.path
                    none
                    (Path.mk
                      false
                      [
                        (PathSegment.mk "Set" PathArguments.none),
                        (PathSegment.mk "new" PathArguments.none)]))
                  []))
              none),
            (Stmt.expr
              (Expr.forLoop
                none
                (Pat.ident false false "arg" none)
                (Expr.field
                  (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                  (Member.named "args"))
                (Block.mk
                  [
                    (Stmt.expr
                      (Expr.tryExpr
                        (Expr.call
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "ensure_wf" PathArguments.none)]))
                          [
                            (Expr.methodCall
                              (Expr.field
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                                (Member.named "locals"))
                              "contains_key"
                              none
                              [
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "arg" PathArguments.none)]))]),
                            (Expr.lit (Lit.str "Function: argument local does not exist"))]))
                      true),
                    (Stmt.expr
                      (Expr.ite
                        (Expr.methodCall
                          (Expr.methodCall
                            (Expr.path
                              none
                              (Path.mk false [(PathSegment.mk "start_live" PathArguments.none)]))
                            "try_insert"
                            none
                            [
                              (Expr.path
                                none
                                (Path.mk false [(PathSegment.mk "arg" PathArguments.none)]))])
                          "is_err"
                          none
                          [])
                        (Block.mk
                          [
                            (Stmt.macro
                              []
                              (Macro.mk
                                (Path.mk
                                  false
                                  [(PathSegment.mk "throw_ill_formed" PathArguments.none)])
                                MacroDelimiter.paren
                                (MacroBody.exprs
                                  [
                                    (Expr.lit
                                      (Lit.str "Function: two arguments refer to the same local"))]
                                  false))
                              true)])
                        none)
                      true)]))
              false),
            (Stmt.expr
              (Expr.tryExpr
                (Expr.call
                  (Expr.path none (Path.mk false [(PathSegment.mk "ensure_wf" PathArguments.none)]))
                  [
                    (Expr.methodCall
                      (Expr.field
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                        (Member.named "locals"))
                      "contains_key"
                      none
                      [
                        (Expr.field
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                          (Member.named "ret"))]),
                    (Expr.lit (Lit.str "Function: return local does not exist"))]))
              true),
            (Stmt.expr
              (Expr.ite
                (Expr.methodCall
                  (Expr.methodCall
                    (Expr.path
                      none
                      (Path.mk false [(PathSegment.mk "start_live" PathArguments.none)]))
                    "try_insert"
                    none
                    [
                      (Expr.field
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                        (Member.named "ret"))])
                  "is_err"
                  none
                  [])
                (Block.mk
                  [
                    (Stmt.macro
                      []
                      (Macro.mk
                        (Path.mk false [(PathSegment.mk "throw_ill_formed" PathArguments.none)])
                        MacroDelimiter.paren
                        (MacroBody.exprs
                          [
                            (Expr.lit
                              (Lit.str "Function: return local is also used for an argument"))]
                          false))
                      true)])
                none)
              true),
            (Stmt.expr
              (Expr.forLoop
                none
                (Pat.ident false false "block" none)
                (Expr.methodCall
                  (Expr.field
                    (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                    (Member.named "blocks"))
                  "values"
                  none
                  [])
                (Block.mk
                  [
                    (Stmt.expr
                      (Expr.forLoop
                        none
                        (Pat.ident false false "statement" none)
                        (Expr.field
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "block" PathArguments.none)]))
                          (Member.named "statements"))
                        (Block.mk
                          [
                            (Stmt.expr
                              (Expr.tryExpr
                                (Expr.methodCall
                                  (Expr.path
                                    none
                                    (Path.mk
                                      false
                                      [(PathSegment.mk "statement" PathArguments.none)]))
                                  "check_wf"
                                  (some
                                    [
                                      (GenericArgument.type
                                        (Ty.path
                                          none
                                          (Path.mk false [(PathSegment.mk "T" PathArguments.none)])))])
                                  [
                                    (Expr.path
                                      none
                                      (Path.mk false [(PathSegment.mk "self" PathArguments.none)])),
                                    (Expr.path
                                      none
                                      (Path.mk false [(PathSegment.mk "prog" PathArguments.none)]))]))
                              true)]))
                      false),
                    (Stmt.expr
                      (Expr.tryExpr
                        (Expr.methodCall
                          (Expr.field
                            (Expr.path
                              none
                              (Path.mk false [(PathSegment.mk "block" PathArguments.none)]))
                            (Member.named "terminator"))
                          "check_wf"
                          (some
                            [
                              (GenericArgument.type
                                (Ty.path
                                  none
                                  (Path.mk false [(PathSegment.mk "T" PathArguments.none)])))])
                          [
                            (Expr.field
                              (Expr.path
                                none
                                (Path.mk false [(PathSegment.mk "block" PathArguments.none)]))
                              (Member.named "kind")),
                            (Expr.path
                              none
                              (Path.mk false [(PathSegment.mk "self" PathArguments.none)])),
                            (Expr.path
                              none
                              (Path.mk false [(PathSegment.mk "prog" PathArguments.none)]))]))
                      true)]))
              false),
            (Stmt.expr
              (Expr.call
                (Expr.path none (Path.mk false [(PathSegment.mk "ret" PathArguments.none)]))
                [(Expr.tuple [])])
              false)])),
      (ImplItem.fn
        [
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue
              " Checks whether the next block exists and has the correct block kind."))]
        Visibility.inherited
        false
        (Signature.mk
          false
          false
          false
          none
          "check_next_block"
          (Generics.mk [] [])
          [
            (FnArg.receiver [] false none false none),
            (FnArg.typed
              []
              (Pat.ident false false "expected_block_kind" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "BbKind" PathArguments.none)]))),
            (FnArg.typed
              []
              (Pat.ident false false "next_block_name" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "BbName" PathArguments.none)])))]
          false
          (some
            (Ty.path
              none
              (Path.mk
                false
                [
                  (PathSegment.mk
                    "Result"
                    (PathArguments.angleBracketed false [(GenericArgument.type (Ty.tuple []))]))]))))
        (Block.mk
          [
            (Stmt.letStmt
              []
              (Pat.tupleStruct
                none
                (Path.mk false [(PathSegment.mk "Some" PathArguments.none)])
                [(Pat.ident false false "next_block" none)])
              (some
                (Expr.methodCall
                  (Expr.field
                    (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                    (Member.named "blocks"))
                  "get"
                  none
                  [
                    (Expr.path
                      none
                      (Path.mk false [(PathSegment.mk "next_block_name" PathArguments.none)]))]))
              (some
                (Expr.block
                  none
                  (Block.mk
                    [
                      (Stmt.macro
                        []
                        (Macro.mk
                          (Path.mk false [(PathSegment.mk "throw_ill_formed" PathArguments.none)])
                          MacroDelimiter.paren
                          (MacroBody.exprs
                            [(Expr.lit (Lit.str "Terminator: next block does not exist"))]
                            false))
                        true)])))),
            (Stmt.expr
              (Expr.tryExpr
                (Expr.call
                  (Expr.path none (Path.mk false [(PathSegment.mk "ensure_wf" PathArguments.none)]))
                  [
                    (Expr.binary
                      (Expr.field
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "next_block" PathArguments.none)]))
                        (Member.named "kind"))
                      BinOp.eq
                      (Expr.path
                        none
                        (Path.mk false [(PathSegment.mk "expected_block_kind" PathArguments.none)]))),
                    (Expr.lit (Lit.str "Terminator: next block has the wrong block kind"))]))
              true),
            (Stmt.expr
              (Expr.call
                (Expr.path none (Path.mk false [(PathSegment.mk "ret" PathArguments.none)]))
                [(Expr.tuple [])])
              false)])),
      (ImplItem.fn
        [
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue
              " Checks whether the unwind block exists and has the correct block kind."))]
        Visibility.inherited
        false
        (Signature.mk
          false
          false
          false
          none
          "check_unwind_block"
          (Generics.mk [] [])
          [
            (FnArg.receiver [] false none false none),
            (FnArg.typed
              []
              (Pat.ident false false "current_block_kind" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "BbKind" PathArguments.none)]))),
            (FnArg.typed
              []
              (Pat.ident false false "unwind_block_name" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "BbName" PathArguments.none)])))]
          false
          (some
            (Ty.path
              none
              (Path.mk
                false
                [
                  (PathSegment.mk
                    "Result"
                    (PathArguments.angleBracketed false [(GenericArgument.type (Ty.tuple []))]))]))))
        (Block.mk
          [
            (Stmt.letStmt
              []
              (Pat.ident false false "expected_block_kinds" none)
              (some
                (Expr.matchExpr
                  (Expr.path
                    none
                    (Path.mk false [(PathSegment.mk "current_block_kind" PathArguments.none)]))
                  [
                    (Arm.mk
                      []
                      (Pat.path
                        none
                        (Path.mk
                          false
                          [
                            (PathSegment.mk "BbKind" PathArguments.none),
                            (PathSegment.mk "Regular" PathArguments.none)]))
                      none
                      (Expr.macro
                        (Macro.mk
                          (Path.mk false [(PathSegment.mk "list" PathArguments.none)])
                          MacroDelimiter.bracket
                          (MacroBody.exprs
                            [
                              (Expr.path
                                none
                                (Path.mk
                                  false
                                  [
                                    (PathSegment.mk "BbKind" PathArguments.none),
                                    (PathSegment.mk "Cleanup" PathArguments.none)])),
                              (Expr.path
                                none
                                (Path.mk
                                  false
                                  [
                                    (PathSegment.mk "BbKind" PathArguments.none),
                                    (PathSegment.mk "Catch" PathArguments.none)]))]
                            false)))),
                    (Arm.mk
                      []
                      (Pat.or
                        [
                          (Pat.path
                            none
                            (Path.mk
                              false
                              [
                                (PathSegment.mk "BbKind" PathArguments.none),
                                (PathSegment.mk "Cleanup" PathArguments.none)])),
                          (Pat.path
                            none
                            (Path.mk
                              false
                              [
                                (PathSegment.mk "BbKind" PathArguments.none),
                                (PathSegment.mk "Terminate" PathArguments.none)]))])
                      none
                      (Expr.macro
                        (Macro.mk
                          (Path.mk false [(PathSegment.mk "list" PathArguments.none)])
                          MacroDelimiter.bracket
                          (MacroBody.exprs
                            [
                              (Expr.path
                                none
                                (Path.mk
                                  false
                                  [
                                    (PathSegment.mk "BbKind" PathArguments.none),
                                    (PathSegment.mk "Terminate" PathArguments.none)]))]
                            false)))),
                    (Arm.mk
                      []
                      (Pat.path
                        none
                        (Path.mk
                          false
                          [
                            (PathSegment.mk "BbKind" PathArguments.none),
                            (PathSegment.mk "Catch" PathArguments.none)]))
                      none
                      (Expr.macro
                        (Macro.mk
                          (Path.mk false [(PathSegment.mk "throw_ill_formed" PathArguments.none)])
                          MacroDelimiter.paren
                          (MacroBody.exprs
                            [
                              (Expr.lit
                                (Lit.str "Terminator: unwinding is not allowed in a catch block"))]
                            false))))]))
              none),
            (Stmt.letStmt
              []
              (Pat.tupleStruct
                none
                (Path.mk false [(PathSegment.mk "Some" PathArguments.none)])
                [(Pat.ident false false "unwind_block" none)])
              (some
                (Expr.methodCall
                  (Expr.field
                    (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                    (Member.named "blocks"))
                  "get"
                  none
                  [
                    (Expr.path
                      none
                      (Path.mk false [(PathSegment.mk "unwind_block_name" PathArguments.none)]))]))
              (some
                (Expr.block
                  none
                  (Block.mk
                    [
                      (Stmt.macro
                        []
                        (Macro.mk
                          (Path.mk false [(PathSegment.mk "throw_ill_formed" PathArguments.none)])
                          MacroDelimiter.paren
                          (MacroBody.exprs
                            [(Expr.lit (Lit.str "Terminator: unwind block does not exist"))]
                            false))
                        true)])))),
            (Stmt.expr
              (Expr.tryExpr
                (Expr.call
                  (Expr.path none (Path.mk false [(PathSegment.mk "ensure_wf" PathArguments.none)]))
                  [
                    (Expr.methodCall
                      (Expr.path
                        none
                        (Path.mk false [(PathSegment.mk "expected_block_kinds" PathArguments.none)]))
                      "any"
                      none
                      [
                        (Expr.closure
                          false
                          [(Pat.ident false false "kind" none)]
                          none
                          (Expr.binary
                            (Expr.path
                              none
                              (Path.mk false [(PathSegment.mk "kind" PathArguments.none)]))
                            BinOp.eq
                            (Expr.field
                              (Expr.path
                                none
                                (Path.mk false [(PathSegment.mk "unwind_block" PathArguments.none)]))
                              (Member.named "kind"))))]),
                    (Expr.lit (Lit.str "Terminator: unwind block has the wrong block kind"))]))
              true),
            (Stmt.expr
              (Expr.call
                (Expr.path none (Path.mk false [(PathSegment.mk "ret" PathArguments.none)]))
                [(Expr.tuple [])])
              false)]))])

/-- `spec/lang/well-formed.md:875` -/
def impl_Relocation__check_wf : Item :=
  (Item.impl
    []
    false
    false
    (Generics.mk [] [])
    false
    none
    (Ty.path none (Path.mk false [(PathSegment.mk "Relocation" PathArguments.none)]))
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
          "check_wf"
          (Generics.mk [] [])
          [
            (FnArg.receiver [] false none false none),
            (FnArg.typed
              []
              (Pat.ident false false "globals" none)
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
                              (Path.mk false [(PathSegment.mk "Global" PathArguments.none)])))]))])))]
          false
          (some
            (Ty.path
              none
              (Path.mk
                false
                [
                  (PathSegment.mk
                    "Result"
                    (PathArguments.angleBracketed false [(GenericArgument.type (Ty.tuple []))]))]))))
        (Block.mk
          [
            (Stmt.letStmt
              []
              (Pat.tupleStruct
                none
                (Path.mk false [(PathSegment.mk "Some" PathArguments.none)])
                [(Pat.ident false false "global" none)])
              (some
                (Expr.methodCall
                  (Expr.path none (Path.mk false [(PathSegment.mk "globals" PathArguments.none)]))
                  "get"
                  none
                  [
                    (Expr.field
                      (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                      (Member.named "name"))]))
              (some
                (Expr.block
                  none
                  (Block.mk
                    [
                      (Stmt.macro
                        []
                        (Macro.mk
                          (Path.mk false [(PathSegment.mk "throw_ill_formed" PathArguments.none)])
                          MacroDelimiter.paren
                          (MacroBody.exprs
                            [(Expr.lit (Lit.str "Relocation: invalid global name"))]
                            false))
                        true)])))),
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
            (Stmt.expr
              (Expr.tryExpr
                (Expr.call
                  (Expr.path none (Path.mk false [(PathSegment.mk "ensure_wf" PathArguments.none)]))
                  [
                    (Expr.binary
                      (Expr.field
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                        (Member.named "offset"))
                      BinOp.le
                      (Expr.path none (Path.mk false [(PathSegment.mk "size" PathArguments.none)]))),
                    (Expr.lit (Lit.str "Relocation: offset out-of-bounds"))]))
              true),
            (Stmt.expr
              (Expr.call
                (Expr.path none (Path.mk false [(PathSegment.mk "ret" PathArguments.none)]))
                [(Expr.tuple [])])
              false)]))])

/-- `spec/lang/well-formed.md:891` -/
def impl_Program__check_wf : Item :=
  (Item.impl
    []
    false
    false
    (Generics.mk [] [])
    false
    none
    (Ty.path none (Path.mk false [(PathSegment.mk "Program" PathArguments.none)]))
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
          "check_wf"
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
            (Ty.path
              none
              (Path.mk
                false
                [
                  (PathSegment.mk
                    "Result"
                    (PathArguments.angleBracketed false [(GenericArgument.type (Ty.tuple []))]))]))))
        (Block.mk
          [
            (Stmt.expr
              (Expr.forLoop
                none
                (Pat.tuple
                  [(Pat.ident false false "_name" none), (Pat.ident false false "vtable" none)])
                (Expr.field
                  (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                  (Member.named "vtables"))
                (Block.mk
                  [
                    (Stmt.expr
                      (Expr.tryExpr
                        (Expr.call
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "ensure_wf" PathArguments.none)]))
                          [
                            (Expr.binary
                              (Expr.binary
                                (Expr.methodCall
                                  (Expr.field
                                    (Expr.path
                                      none
                                      (Path.mk false [(PathSegment.mk "vtable" PathArguments.none)]))
                                    (Member.named "size"))
                                  "bytes"
                                  none
                                  [])
                                BinOp.rem
                                (Expr.methodCall
                                  (Expr.field
                                    (Expr.path
                                      none
                                      (Path.mk false [(PathSegment.mk "vtable" PathArguments.none)]))
                                    (Member.named "align"))
                                  "bytes"
                                  none
                                  []))
                              BinOp.eq
                              (Expr.lit (Lit.int 0 ""))),
                            (Expr.lit
                              (Lit.str "Program: size stored in vtable not a multiple of alignment"))]))
                      true),
                    (Stmt.expr
                      (Expr.tryExpr
                        (Expr.call
                          (Expr.path
                            none
                            (Path.mk
                              false
                              [
                                (PathSegment.mk "UnsafeCellStrategy" PathArguments.none),
                                (PathSegment.mk "check_cells" PathArguments.none)]))
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
                              (Member.named "size"))]))
                      true),
                    (Stmt.letStmt
                      []
                      (Pat.tupleStruct
                        none
                        (Path.mk false [(PathSegment.mk "Some" PathArguments.none)])
                        [(Pat.ident false false "trait_methods" none)])
                      (some
                        (Expr.methodCall
                          (Expr.field
                            (Expr.path
                              none
                              (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                            (Member.named "traits"))
                          "get"
                          none
                          [
                            (Expr.field
                              (Expr.path
                                none
                                (Path.mk false [(PathSegment.mk "vtable" PathArguments.none)]))
                              (Member.named "trait_name"))]))
                      (some
                        (Expr.block
                          none
                          (Block.mk
                            [
                              (Stmt.macro
                                []
                                (Macro.mk
                                  (Path.mk
                                    false
                                    [(PathSegment.mk "throw_ill_formed" PathArguments.none)])
                                  MacroDelimiter.paren
                                  (MacroBody.exprs
                                    [(Expr.lit (Lit.str "Program: vtable for unknown trait"))]
                                    false))
                                true)])))),
                    (Stmt.letStmt
                      []
                      (Pat.ident false false "methods" none)
                      (some
                        (Expr.methodCall
                          (Expr.methodCall
                            (Expr.field
                              (Expr.path
                                none
                                (Path.mk false [(PathSegment.mk "vtable" PathArguments.none)]))
                              (Member.named "methods"))
                            "keys"
                            none
                            [])
                          "collect"
                          (some
                            [
                              (GenericArgument.type
                                (Ty.path
                                  none
                                  (Path.mk
                                    false
                                    [
                                      (PathSegment.mk
                                        "Set"
                                        (PathArguments.angleBracketed
                                          false
                                          [(GenericArgument.type Ty.infer)]))])))])
                          []))
                      none),
                    (Stmt.expr
                      (Expr.tryExpr
                        (Expr.call
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "ensure_wf" PathArguments.none)]))
                          [
                            (Expr.binary
                              (Expr.path
                                none
                                (Path.mk false [(PathSegment.mk "methods" PathArguments.none)]))
                              BinOp.eq
                              (Expr.path
                                none
                                (Path.mk
                                  false
                                  [(PathSegment.mk "trait_methods" PathArguments.none)]))),
                            (Expr.lit (Lit.str "Program: vtable has not the right set of methods"))]))
                      true)]))
              false),
            (Stmt.expr
              (Expr.forLoop
                none
                (Pat.ident false false "function" none)
                (Expr.methodCall
                  (Expr.field
                    (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                    (Member.named "functions"))
                  "values"
                  none
                  [])
                (Block.mk
                  [
                    (Stmt.expr
                      (Expr.tryExpr
                        (Expr.methodCall
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "function" PathArguments.none)]))
                          "check_wf"
                          (some
                            [
                              (GenericArgument.type
                                (Ty.path
                                  none
                                  (Path.mk false [(PathSegment.mk "T" PathArguments.none)])))])
                          [
                            (Expr.path
                              none
                              (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))]))
                      true)]))
              false),
            (Stmt.letStmt
              []
              (Pat.tupleStruct
                none
                (Path.mk false [(PathSegment.mk "Some" PathArguments.none)])
                [(Pat.ident false false "start" none)])
              (some
                (Expr.methodCall
                  (Expr.field
                    (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                    (Member.named "functions"))
                  "get"
                  none
                  [
                    (Expr.field
                      (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                      (Member.named "start"))]))
              (some
                (Expr.block
                  none
                  (Block.mk
                    [
                      (Stmt.macro
                        []
                        (Macro.mk
                          (Path.mk false [(PathSegment.mk "throw_ill_formed" PathArguments.none)])
                          MacroDelimiter.paren
                          (MacroBody.exprs
                            [(Expr.lit (Lit.str "Program: start function does not exist"))]
                            false))
                        true)])))),
            (Stmt.expr
              (Expr.tryExpr
                (Expr.call
                  (Expr.path none (Path.mk false [(PathSegment.mk "ensure_wf" PathArguments.none)]))
                  [
                    (Expr.binary
                      (Expr.field
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "start" PathArguments.none)]))
                        (Member.named "calling_convention"))
                      BinOp.eq
                      (Expr.path
                        none
                        (Path.mk
                          false
                          [
                            (PathSegment.mk "CallingConvention" PathArguments.none),
                            (PathSegment.mk "C" PathArguments.none)]))),
                    (Expr.lit (Lit.str "Program: start function has invalid calling convention"))]))
              true),
            (Stmt.letStmt
              []
              (Pat.ident false false "ret_layout" none)
              (some
                (Expr.methodCall
                  (Expr.index
                    (Expr.field
                      (Expr.path none (Path.mk false [(PathSegment.mk "start" PathArguments.none)]))
                      (Member.named "locals"))
                    (Expr.field
                      (Expr.path none (Path.mk false [(PathSegment.mk "start" PathArguments.none)]))
                      (Member.named "ret")))
                  "layout"
                  (some
                    [
                      (GenericArgument.type
                        (Ty.path none (Path.mk false [(PathSegment.mk "T" PathArguments.none)])))])
                  []))
              none),
            (Stmt.expr
              (Expr.tryExpr
                (Expr.call
                  (Expr.path none (Path.mk false [(PathSegment.mk "ensure_wf" PathArguments.none)]))
                  [
                    (Expr.binary
                      (Expr.path
                        none
                        (Path.mk false [(PathSegment.mk "ret_layout" PathArguments.none)]))
                      BinOp.eq
                      (Expr.call
                        (Expr.path
                          none
                          (Path.mk
                            false
                            [
                              (PathSegment.mk "LayoutStrategy" PathArguments.none),
                              (PathSegment.mk "Sized" PathArguments.none)]))
                        [
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
                                (PathSegment.mk "ONE" PathArguments.none)]))])),
                    (Expr.lit (Lit.str "Program: start function return local has invalid layout"))]))
              true),
            (Stmt.expr
              (Expr.tryExpr
                (Expr.call
                  (Expr.path none (Path.mk false [(PathSegment.mk "ensure_wf" PathArguments.none)]))
                  [
                    (Expr.methodCall
                      (Expr.field
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "start" PathArguments.none)]))
                        (Member.named "args"))
                      "is_empty"
                      none
                      []),
                    (Expr.lit (Lit.str "Program: start function has arguments"))]))
              true),
            (Stmt.expr
              (Expr.forLoop
                none
                (Pat.tuple
                  [(Pat.ident false false "_name" none), (Pat.ident false false "global" none)])
                (Expr.field
                  (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
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
                    (Stmt.expr
                      (Expr.forLoop
                        none
                        (Pat.tuple
                          [
                            (Pat.ident false false "offset" none),
                            (Pat.ident false false "relocation" none)])
                        (Expr.field
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "global" PathArguments.none)]))
                          (Member.named "relocations"))
                        (Block.mk
                          [
                            (Stmt.expr
                              (Expr.tryExpr
                                (Expr.call
                                  (Expr.path
                                    none
                                    (Path.mk
                                      false
                                      [(PathSegment.mk "ensure_wf" PathArguments.none)]))
                                  [
                                    (Expr.binary
                                      (Expr.binary
                                        (Expr.path
                                          none
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "offset" PathArguments.none)]))
                                        BinOp.add
                                        (Expr.path
                                          none
                                          (Path.mk
                                            false
                                            [
                                              (PathSegment.mk "T" PathArguments.none),
                                              (PathSegment.mk "PTR_SIZE" PathArguments.none)])))
                                      BinOp.le
                                      (Expr.path
                                        none
                                        (Path.mk false [(PathSegment.mk "size" PathArguments.none)]))),
                                    (Expr.lit (Lit.str "Program: invalid global pointer value"))]))
                              true),
                            (Stmt.expr
                              (Expr.tryExpr
                                (Expr.methodCall
                                  (Expr.path
                                    none
                                    (Path.mk
                                      false
                                      [(PathSegment.mk "relocation" PathArguments.none)]))
                                  "check_wf"
                                  none
                                  [
                                    (Expr.field
                                      (Expr.path
                                        none
                                        (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                                      (Member.named "globals"))]))
                              true)]))
                      false)]))
              false),
            (Stmt.expr
              (Expr.call
                (Expr.path none (Path.mk false [(PathSegment.mk "ret" PathArguments.none)]))
                [(Expr.tuple [])])
              false)]))])

/-- All items of `spec/lang/well-formed.md`, in source order, with provenance. -/
def items : List SourceItem :=
  [
    (SourceItem.mk
      "fn_ensure_wf"
      12
      "250d2d02732131912e6782e33a7ee9729ac42951c18279c4352a786c3c9ba54a"
      fn_ensure_wf),
    (SourceItem.mk
      "impl_IntType__check_wf"
      21
      "6deed21a9a2973643b84a1f861a58b13498e73ad9988251b2a2939fa810e15d0"
      impl_IntType__check_wf),
    (SourceItem.mk
      "impl_TupleHeadLayout__check_wf"
      28
      "40faf9ba2be1bd691b76784e538bcf4254a7a6c341b7745df5908c6ae17df8d0"
      impl_TupleHeadLayout__check_wf),
    (SourceItem.mk
      "impl_LayoutStrategy__check_wf"
      38
      "b045883dd8e7ad0baee6be988056124d38398a8badb8f5fe78aea9848c7ffade"
      impl_LayoutStrategy__check_wf),
    (SourceItem.mk
      "impl_UnsafeCellStrategy__check_cells"
      80
      "fd30015862c42ac1f6145f2f49fe76a79fd0a62f53f62fb1b321ea8d664d8242"
      impl_UnsafeCellStrategy__check_cells),
    (SourceItem.mk
      "impl_PointeeInfo__check_wf"
      112
      "5ae11aeabe39dd1a1621a1fa0f603276c520efd388bfebfcdc86fa600084384f"
      impl_PointeeInfo__check_wf),
    (SourceItem.mk
      "impl_PtrType__check_wf"
      122
      "5824a88638683af329b9b01d20ea576f51c68a457b817f9767c93a183eb84db9"
      impl_PtrType__check_wf),
    (SourceItem.mk
      "impl_Type__check_wf"
      138
      "01a43bea8eab88b200cbd90e8dbeb7cd51f8508f89d53220afa110ed2d3027aa"
      impl_Type__check_wf),
    (SourceItem.mk
      "impl_Discriminator__check_wf"
      262
      "5e159938b9a217c8d80cdc7e6baf577f5c65c33f0547dcf01ed7bceb40240567"
      impl_Discriminator__check_wf),
    (SourceItem.mk
      "impl_Constant__check_wf"
      292
      "32c6dd8f54dca50d612ed94237788d5bb80278c22f7a71590b540a2716b513f7"
      impl_Constant__check_wf),
    (SourceItem.mk
      "impl_ValueExpr__check_wf"
      329
      "c31930447bae68d09ef447e9526c6cb96b13b3a4b46f3eb1b7159e7cff2f4f5f"
      impl_ValueExpr__check_wf),
    (SourceItem.mk
      "impl_PlaceExpr__check_wf"
      556
      "9e8bfb24778377e38b03449dee5152262d932752af320a89ca0bc6bc47538e4c"
      impl_PlaceExpr__check_wf),
    (SourceItem.mk
      "impl_ArgumentExpr__check_wf"
      627
      "27d6fd2432a5aa0887c0a302fbf7725ddf61331f191ab8e55878a8891ff04e3e"
      impl_ArgumentExpr__check_wf),
    (SourceItem.mk
      "impl_Statement__check_wf"
      640
      "4e129ed98ac5a6af381423ac242c28f3f8836f640517550b3f5512028a583e1f"
      impl_Statement__check_wf),
    (SourceItem.mk
      "fn_is_atomic_binop"
      695
      "5f40867dda61c8f78f7cbf3b8cca54112b61b4c985dd1a9ce5d3c0dcc5eeff1e"
      fn_is_atomic_binop),
    (SourceItem.mk
      "impl_Terminator__check_wf"
      707
      "2c5e64153c008d37cb1506900f8240aa71ab87bb2a35df7d383e092ebbebea97"
      impl_Terminator__check_wf),
    (SourceItem.mk
      "impl_Function__check_wf"
      812
      "b4eca5c68214ccb5e540f76a832986ebc54da81b694da0eb1bfea6e1151a11a6"
      impl_Function__check_wf),
    (SourceItem.mk
      "impl_Relocation__check_wf"
      875
      "1ca50691153915eef143ddef4c69fc0a48d8a79cd810080ee3fe31082ca8f163"
      impl_Relocation__check_wf),
    (SourceItem.mk
      "impl_Program__check_wf"
      891
      "7b2bf9d3a22643416c78245992b7971cc1abb7fc86dc228b2f0cfc0f87a7f20f"
      impl_Program__check_wf)]

end MiniRustSpec.Gen.Items.Lang.WellFormed
