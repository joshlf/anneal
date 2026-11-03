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
`spec/lang/step/operators.md` (commit `d821c6e3`), one Lean definition per item, in source order.
-/

import MiniRustSpec.Meta.Syntax

set_option maxRecDepth 100000

namespace MiniRustSpec.Gen.Items.Lang.Step.Operators

open MiniRustSpec.Syntax

/-- Path of the upstream file these items were extracted from. -/
def sourceFile : String := "spec/lang/step/operators.md"

/-- SHA-256 of the upstream file. -/
def sourceSha256 : String := "075e1e7d0b9fee47ef4a0adea2e9fef9861fb6ccfe98af6d42a0123fce96400d"

/-- `spec/lang/step/operators.md:8` -/
def impl_Machine__eval_un_op_0 : Item :=
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
        [(Attr.mk true "specr::argmatch" (AttrMeta.list "operator"))]
        Visibility.inherited
        false
        (Signature.mk
          false
          false
          false
          none
          "eval_un_op"
          (Generics.mk [] [])
          [
            (FnArg.receiver [] true none false none),
            (FnArg.typed
              []
              (Pat.ident false false "operator" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "UnOp" PathArguments.none)]))),
            (FnArg.typed
              []
              (Pat.tuple
                [(Pat.ident false false "operand" none), (Pat.ident false false "op_ty" none)])
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
                                  (Path.mk false [(PathSegment.mk "M" PathArguments.none)])))]))])),
                  (Ty.path none (Path.mk false [(PathSegment.mk "Type" PathArguments.none)]))]))]
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
                                (Path.mk false [(PathSegment.mk "Type" PathArguments.none)]))]))]))]))))
        (Block.mk [(Stmt.expr (Expr.range none RangeLimits.halfOpen none) false)]))])

/-- `spec/lang/step/operators.md:17` -/
def impl_Machine__eval_int_un_op : Item :=
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
            (AttrMeta.nameValue " Perform the operation on the mathematical integer `operand`,")),
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue
              " but correcting for non-pure effects dependent of the `operand_ty`."))]
        Visibility.inherited
        false
        (Signature.mk
          false
          false
          false
          none
          "eval_int_un_op"
          (Generics.mk [] [])
          [
            (FnArg.typed
              []
              (Pat.ident false false "op" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "IntUnOp" PathArguments.none)]))),
            (FnArg.typed
              []
              (Pat.ident false false "operand" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "Int" PathArguments.none)]))),
            (FnArg.typed
              []
              (Pat.ident false false "operand_ty" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "IntType" PathArguments.none)])))]
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
                          (Ty.path none (Path.mk false [(PathSegment.mk "Int" PathArguments.none)])))]))]))))
        (Block.mk
          [
            (Stmt.item
              (Item.use [] Visibility.inherited false (UseTree.path "IntUnOp" UseTree.glob))),
            (Stmt.expr
              (Expr.call
                (Expr.path none (Path.mk false [(PathSegment.mk "ret" PathArguments.none)]))
                [
                  (Expr.matchExpr
                    (Expr.path none (Path.mk false [(PathSegment.mk "op" PathArguments.none)]))
                    [
                      (Arm.mk
                        []
                        (Pat.ident false false "Neg" none)
                        none
                        (Expr.methodCall
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "operand_ty" PathArguments.none)]))
                          "bring_in_bounds"
                          none
                          [
                            (Expr.unary
                              UnOp.neg
                              (Expr.path
                                none
                                (Path.mk false [(PathSegment.mk "operand" PathArguments.none)])))])),
                      (Arm.mk
                        []
                        (Pat.ident false false "BitNot" none)
                        none
                        (Expr.methodCall
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "operand_ty" PathArguments.none)]))
                          "bring_in_bounds"
                          none
                          [
                            (Expr.unary
                              UnOp.not
                              (Expr.path
                                none
                                (Path.mk false [(PathSegment.mk "operand" PathArguments.none)])))])),
                      (Arm.mk
                        []
                        (Pat.ident false false "CountOnes" none)
                        none
                        (Expr.call
                          (Expr.path
                            none
                            (Path.mk
                              false
                              [
                                (PathSegment.mk "Self" PathArguments.none),
                                (PathSegment.mk "eval_count_ones" PathArguments.none)]))
                          [
                            (Expr.path
                              none
                              (Path.mk false [(PathSegment.mk "operand" PathArguments.none)])),
                            (Expr.path
                              none
                              (Path.mk false [(PathSegment.mk "operand_ty" PathArguments.none)]))]))])])
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
          "eval_un_op"
          (Generics.mk [] [])
          [
            (FnArg.receiver [] true none false none),
            (FnArg.typed
              []
              (Pat.tupleStruct
                none
                (Path.mk
                  false
                  [
                    (PathSegment.mk "UnOp" PathArguments.none),
                    (PathSegment.mk "Int" PathArguments.none)])
                [(Pat.ident false false "op" none)])
              (Ty.path none (Path.mk false [(PathSegment.mk "UnOp" PathArguments.none)]))),
            (FnArg.typed
              []
              (Pat.tuple
                [(Pat.ident false false "operand" none), (Pat.ident false false "op_ty" none)])
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
                                  (Path.mk false [(PathSegment.mk "M" PathArguments.none)])))]))])),
                  (Ty.path none (Path.mk false [(PathSegment.mk "Type" PathArguments.none)]))]))]
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
                                (Path.mk false [(PathSegment.mk "Type" PathArguments.none)]))]))]))]))))
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
              (some (Expr.path none (Path.mk false [(PathSegment.mk "op_ty" PathArguments.none)])))
              (some
                (Expr.block
                  none
                  (Block.mk
                    [
                      (Stmt.expr
                        (Expr.macro
                          (Macro.mk
                            (Path.mk false [(PathSegment.mk "panic" PathArguments.none)])
                            MacroDelimiter.paren
                            (MacroBody.exprs
                              [(Expr.lit (Lit.str "non-integer input to integer operation"))]
                              false)))
                        false)])))),
            (Stmt.letStmt
              []
              (Pat.tupleStruct
                none
                (Path.mk
                  false
                  [
                    (PathSegment.mk "Value" PathArguments.none),
                    (PathSegment.mk "Int" PathArguments.none)])
                [(Pat.ident false false "operand" none)])
              (some
                (Expr.path none (Path.mk false [(PathSegment.mk "operand" PathArguments.none)])))
              (some
                (Expr.block
                  none
                  (Block.mk
                    [
                      (Stmt.expr
                        (Expr.macro
                          (Macro.mk
                            (Path.mk false [(PathSegment.mk "panic" PathArguments.none)])
                            MacroDelimiter.paren
                            (MacroBody.exprs
                              [(Expr.lit (Lit.str "non-integer input to integer operation"))]
                              false)))
                        false)])))),
            (Stmt.letStmt
              []
              (Pat.ident false false "ret_ty" none)
              (some
                (Expr.matchExpr
                  (Expr.path none (Path.mk false [(PathSegment.mk "op" PathArguments.none)]))
                  [
                    (Arm.mk
                      []
                      (Pat.path
                        none
                        (Path.mk
                          false
                          [
                            (PathSegment.mk "IntUnOp" PathArguments.none),
                            (PathSegment.mk "CountOnes" PathArguments.none)]))
                      none
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
                              (Path.mk false [(PathSegment.mk "Unsigned" PathArguments.none)]))),
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
                                      (PathSegment.mk "Size" PathArguments.none),
                                      (PathSegment.mk "from_bytes" PathArguments.none)]))
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
                        (Path.mk false [(PathSegment.mk "int_ty" PathArguments.none)])))]))
              none),
            (Stmt.letStmt
              []
              (Pat.ident false false "result" none)
              (some
                (Expr.call
                  (Expr.path
                    none
                    (Path.mk
                      false
                      [
                        (PathSegment.mk "Value" PathArguments.none),
                        (PathSegment.mk "Int" PathArguments.none)]))
                  [
                    (Expr.tryExpr
                      (Expr.call
                        (Expr.path
                          none
                          (Path.mk
                            false
                            [
                              (PathSegment.mk "Self" PathArguments.none),
                              (PathSegment.mk "eval_int_un_op" PathArguments.none)]))
                        [
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "op" PathArguments.none)])),
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "operand" PathArguments.none)])),
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "int_ty" PathArguments.none)]))]))]))
              none),
            (Stmt.expr
              (Expr.methodCall
                (Expr.methodCall
                  (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                  "check_value"
                  none
                  [
                    (Expr.path none (Path.mk false [(PathSegment.mk "result" PathArguments.none)])),
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
                          (Path.mk false [(PathSegment.mk "ret_ty" PathArguments.none)]))])])
                "expect"
                none
                [
                  (Expr.lit
                    (Lit.str "sanity check: result of UnOp::Int does not fit in the return type"))])
              true),
            (Stmt.expr
              (Expr.call
                (Expr.path none (Path.mk false [(PathSegment.mk "ret" PathArguments.none)]))
                [
                  (Expr.tuple
                    [
                      (Expr.path
                        none
                        (Path.mk false [(PathSegment.mk "result" PathArguments.none)])),
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
                            (Path.mk false [(PathSegment.mk "ret_ty" PathArguments.none)]))])])])
              false)]))])

/-- `spec/lang/step/operators.md:58` -/
def impl_Machine__eval_count_ones : Item :=
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
          "eval_count_ones"
          (Generics.mk [] [])
          [
            (FnArg.typed
              []
              (Pat.ident false false "operand" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "Int" PathArguments.none)]))),
            (FnArg.typed
              []
              (Pat.ident false false "int_ty" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "IntType" PathArguments.none)])))]
          false
          (some (Ty.path none (Path.mk false [(PathSegment.mk "Int" PathArguments.none)]))))
        (Block.mk
          [
            (Stmt.letStmt
              []
              (Pat.ident false true "ones" none)
              (some
                (Expr.path
                  none
                  (Path.mk
                    false
                    [
                      (PathSegment.mk "Int" PathArguments.none),
                      (PathSegment.mk "ZERO" PathArguments.none)])))
              none),
            (Stmt.letStmt
              []
              (Pat.ident false true "remaining_bits" none)
              (some
                (Expr.path none (Path.mk false [(PathSegment.mk "operand" PathArguments.none)])))
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
                    (Expr.methodCall
                      (Expr.field
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "int_ty" PathArguments.none)]))
                        (Member.named "size"))
                      "bits"
                      none
                      [])))
                (Block.mk
                  [
                    (Stmt.expr
                      (Expr.binary
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "ones" PathArguments.none)]))
                        BinOp.addAssign
                        (Expr.binary
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "remaining_bits" PathArguments.none)]))
                          BinOp.bitAnd
                          (Expr.path
                            none
                            (Path.mk
                              false
                              [
                                (PathSegment.mk "Int" PathArguments.none),
                                (PathSegment.mk "ONE" PathArguments.none)]))))
                      true),
                    (Stmt.expr
                      (Expr.binary
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "remaining_bits" PathArguments.none)]))
                        BinOp.shrAssign
                        (Expr.lit (Lit.int 1 "")))
                      true)]))
              false),
            (Stmt.expr
              (Expr.path none (Path.mk false [(PathSegment.mk "ones" PathArguments.none)]))
              false)]))])

/-- `spec/lang/step/operators.md:76` -/
def impl_Machine__eval_cast_op : Item :=
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
          "eval_cast_op"
          (Generics.mk [] [])
          [
            (FnArg.receiver [] true none false none),
            (FnArg.typed
              []
              (Pat.ident false false "cast_op" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "CastOp" PathArguments.none)]))),
            (FnArg.typed
              []
              (Pat.tuple
                [(Pat.ident false false "operand" none), (Pat.ident false false "old_ty" none)])
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
                                  (Path.mk false [(PathSegment.mk "M" PathArguments.none)])))]))])),
                  (Ty.path none (Path.mk false [(PathSegment.mk "Type" PathArguments.none)]))]))]
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
                                (Path.mk false [(PathSegment.mk "Type" PathArguments.none)]))]))]))]))))
        (Block.mk
          [
            (Stmt.item
              (Item.use [] Visibility.inherited false (UseTree.path "CastOp" UseTree.glob))),
            (Stmt.expr
              (Expr.matchExpr
                (Expr.path none (Path.mk false [(PathSegment.mk "cast_op" PathArguments.none)]))
                [
                  (Arm.mk
                    []
                    (Pat.tupleStruct
                      none
                      (Path.mk false [(PathSegment.mk "IntToInt" PathArguments.none)])
                      [(Pat.ident false false "int_ty" none)])
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
                                  (PathSegment.mk "Value" PathArguments.none),
                                  (PathSegment.mk "Int" PathArguments.none)])
                              [(Pat.ident false false "operand" none)])
                            (some
                              (Expr.path
                                none
                                (Path.mk false [(PathSegment.mk "operand" PathArguments.none)])))
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
                                            [(PathSegment.mk "panic" PathArguments.none)])
                                          MacroDelimiter.paren
                                          (MacroBody.exprs
                                            [
                                              (Expr.lit
                                                (Lit.str "non-integer input to int-to-int cast"))]
                                            false)))
                                      false)])))),
                          (Stmt.letStmt
                            []
                            (Pat.ident false false "result" none)
                            (some
                              (Expr.methodCall
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "int_ty" PathArguments.none)]))
                                "bring_in_bounds"
                                none
                                [
                                  (Expr.path
                                    none
                                    (Path.mk false [(PathSegment.mk "operand" PathArguments.none)]))]))
                            none),
                          (Stmt.expr
                            (Expr.call
                              (Expr.path
                                none
                                (Path.mk false [(PathSegment.mk "ret" PathArguments.none)]))
                              [
                                (Expr.tuple
                                  [
                                    (Expr.call
                                      (Expr.path
                                        none
                                        (Path.mk
                                          false
                                          [
                                            (PathSegment.mk "Value" PathArguments.none),
                                            (PathSegment.mk "Int" PathArguments.none)]))
                                      [
                                        (Expr.path
                                          none
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "result" PathArguments.none)]))]),
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
                                            [(PathSegment.mk "int_ty" PathArguments.none)]))])])])
                            false)]))),
                  (Arm.mk
                    []
                    (Pat.tupleStruct
                      none
                      (Path.mk false [(PathSegment.mk "Transmute" PathArguments.none)])
                      [(Pat.ident false false "new_ty" none)])
                    none
                    (Expr.block
                      none
                      (Block.mk
                        [
                          (Stmt.expr
                            (Expr.ite
                              (Expr.binary
                                (Expr.methodCall
                                  (Expr.methodCall
                                    (Expr.path
                                      none
                                      (Path.mk false [(PathSegment.mk "old_ty" PathArguments.none)]))
                                    "layout"
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
                                    [])
                                  "expect_size"
                                  none
                                  [(Expr.lit (Lit.str "WF ensures transmutes are sized"))])
                                BinOp.ne
                                (Expr.methodCall
                                  (Expr.methodCall
                                    (Expr.path
                                      none
                                      (Path.mk false [(PathSegment.mk "new_ty" PathArguments.none)]))
                                    "layout"
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
                                    [])
                                  "expect_size"
                                  none
                                  [(Expr.lit (Lit.str "WF ensures transmutes are sized"))]))
                              (Block.mk
                                [
                                  (Stmt.expr
                                    (Expr.macro
                                      (Macro.mk
                                        (Path.mk
                                          false
                                          [(PathSegment.mk "throw_ub" PathArguments.none)])
                                        MacroDelimiter.paren
                                        (MacroBody.exprs
                                          [
                                            (Expr.lit
                                              (Lit.str "transmute between types of different size"))]
                                          false)))
                                    false)])
                              none)
                            false),
                          (Stmt.letStmt
                            []
                            (Pat.ident false false "val" none)
                            (some
                              (Expr.tryExpr
                                (Expr.methodCall
                                  (Expr.path
                                    none
                                    (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                                  "transmute"
                                  none
                                  [
                                    (Expr.path
                                      none
                                      (Path.mk
                                        false
                                        [(PathSegment.mk "operand" PathArguments.none)])),
                                    (Expr.path
                                      none
                                      (Path.mk false [(PathSegment.mk "old_ty" PathArguments.none)])),
                                    (Expr.path
                                      none
                                      (Path.mk false [(PathSegment.mk "new_ty" PathArguments.none)]))])))
                            none),
                          (Stmt.expr
                            (Expr.call
                              (Expr.path
                                none
                                (Path.mk false [(PathSegment.mk "ret" PathArguments.none)]))
                              [
                                (Expr.tuple
                                  [
                                    (Expr.path
                                      none
                                      (Path.mk false [(PathSegment.mk "val" PathArguments.none)])),
                                    (Expr.path
                                      none
                                      (Path.mk false [(PathSegment.mk "new_ty" PathArguments.none)]))])])
                            false)])))])
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
          "eval_un_op"
          (Generics.mk [] [])
          [
            (FnArg.receiver [] true none false none),
            (FnArg.typed
              []
              (Pat.tupleStruct
                none
                (Path.mk
                  false
                  [
                    (PathSegment.mk "UnOp" PathArguments.none),
                    (PathSegment.mk "Cast" PathArguments.none)])
                [(Pat.ident false false "cast_op" none)])
              (Ty.path none (Path.mk false [(PathSegment.mk "UnOp" PathArguments.none)]))),
            (FnArg.typed
              []
              (Pat.tuple
                [(Pat.ident false false "operand" none), (Pat.ident false false "op_ty" none)])
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
                                  (Path.mk false [(PathSegment.mk "M" PathArguments.none)])))]))])),
                  (Ty.path none (Path.mk false [(PathSegment.mk "Type" PathArguments.none)]))]))]
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
                                (Path.mk false [(PathSegment.mk "Type" PathArguments.none)]))]))]))]))))
        (Block.mk
          [
            (Stmt.expr
              (Expr.call
                (Expr.path none (Path.mk false [(PathSegment.mk "ret" PathArguments.none)]))
                [
                  (Expr.tryExpr
                    (Expr.methodCall
                      (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                      "eval_cast_op"
                      none
                      [
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "cast_op" PathArguments.none)])),
                        (Expr.tuple
                          [
                            (Expr.path
                              none
                              (Path.mk false [(PathSegment.mk "operand" PathArguments.none)])),
                            (Expr.path
                              none
                              (Path.mk false [(PathSegment.mk "op_ty" PathArguments.none)]))])]))])
              false)]))])

/-- `spec/lang/step/operators.md:105` -/
def impl_Machine__eval_un_op_1 : Item :=
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
          "eval_un_op"
          (Generics.mk [] [])
          [
            (FnArg.receiver [] true none false none),
            (FnArg.typed
              []
              (Pat.path
                none
                (Path.mk
                  false
                  [
                    (PathSegment.mk "UnOp" PathArguments.none),
                    (PathSegment.mk "GetThinPointer" PathArguments.none)]))
              (Ty.path none (Path.mk false [(PathSegment.mk "UnOp" PathArguments.none)]))),
            (FnArg.typed
              []
              (Pat.tuple
                [(Pat.ident false false "operand" none), (Pat.ident false false "op_ty" none)])
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
                                  (Path.mk false [(PathSegment.mk "M" PathArguments.none)])))]))])),
                  (Ty.path none (Path.mk false [(PathSegment.mk "Type" PathArguments.none)]))]))]
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
                                (Path.mk false [(PathSegment.mk "Type" PathArguments.none)]))]))]))]))))
        (Block.mk
          [
            (Stmt.letStmt
              []
              (Pat.tupleStruct
                none
                (Path.mk
                  false
                  [
                    (PathSegment.mk "Value" PathArguments.none),
                    (PathSegment.mk "Ptr" PathArguments.none)])
                [(Pat.ident false false "ptr" none)])
              (some
                (Expr.path none (Path.mk false [(PathSegment.mk "operand" PathArguments.none)])))
              (some
                (Expr.block
                  none
                  (Block.mk
                    [
                      (Stmt.expr
                        (Expr.macro
                          (Macro.mk
                            (Path.mk false [(PathSegment.mk "panic" PathArguments.none)])
                            MacroDelimiter.paren
                            (MacroBody.exprs
                              [(Expr.lit (Lit.str "non-pointer GetThinPointer"))]
                              false)))
                        false)])))),
            (Stmt.letStmt
              []
              (Pat.ident false false "thin_ptr" none)
              (some
                (Expr.struct
                  none
                  (Path.mk false [(PathSegment.mk "Pointer" PathArguments.none)])
                  [
                    (FieldValue.mk
                      []
                      (Member.named "metadata")
                      false
                      (Expr.path none (Path.mk false [(PathSegment.mk "None" PathArguments.none)])))]
                  true
                  (some
                    (Expr.path none (Path.mk false [(PathSegment.mk "ptr" PathArguments.none)])))))
              none),
            (Stmt.letStmt
              []
              (Pat.ident false false "thin_ptr_ty" none)
              (some
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
                            (PathSegment.mk "PointerMetaKind" PathArguments.none),
                            (PathSegment.mk "None" PathArguments.none)])))]
                  false
                  none))
              none),
            (Stmt.expr
              (Expr.call
                (Expr.path none (Path.mk false [(PathSegment.mk "ret" PathArguments.none)]))
                [
                  (Expr.tuple
                    [
                      (Expr.call
                        (Expr.path
                          none
                          (Path.mk
                            false
                            [
                              (PathSegment.mk "Value" PathArguments.none),
                              (PathSegment.mk "Ptr" PathArguments.none)]))
                        [
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "thin_ptr" PathArguments.none)]))]),
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
                            (Path.mk false [(PathSegment.mk "thin_ptr_ty" PathArguments.none)]))])])])
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
          "eval_un_op"
          (Generics.mk [] [])
          [
            (FnArg.receiver [] true none false none),
            (FnArg.typed
              []
              (Pat.path
                none
                (Path.mk
                  false
                  [
                    (PathSegment.mk "UnOp" PathArguments.none),
                    (PathSegment.mk "GetMetadata" PathArguments.none)]))
              (Ty.path none (Path.mk false [(PathSegment.mk "UnOp" PathArguments.none)]))),
            (FnArg.typed
              []
              (Pat.tuple
                [(Pat.ident false false "operand" none), (Pat.ident false false "op_ty" none)])
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
                                  (Path.mk false [(PathSegment.mk "M" PathArguments.none)])))]))])),
                  (Ty.path none (Path.mk false [(PathSegment.mk "Type" PathArguments.none)]))]))]
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
                                (Path.mk false [(PathSegment.mk "Type" PathArguments.none)]))]))]))]))))
        (Block.mk
          [
            (Stmt.letStmt
              []
              (Pat.tupleStruct
                none
                (Path.mk
                  false
                  [
                    (PathSegment.mk "Value" PathArguments.none),
                    (PathSegment.mk "Ptr" PathArguments.none)])
                [(Pat.ident false false "ptr" none)])
              (some
                (Expr.path none (Path.mk false [(PathSegment.mk "operand" PathArguments.none)])))
              (some
                (Expr.block
                  none
                  (Block.mk
                    [
                      (Stmt.expr
                        (Expr.macro
                          (Macro.mk
                            (Path.mk false [(PathSegment.mk "panic" PathArguments.none)])
                            MacroDelimiter.paren
                            (MacroBody.exprs [(Expr.lit (Lit.str "non-pointer GetMetadata"))] false)))
                        false)])))),
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
              (some (Expr.path none (Path.mk false [(PathSegment.mk "op_ty" PathArguments.none)])))
              (some
                (Expr.block
                  none
                  (Block.mk
                    [
                      (Stmt.expr
                        (Expr.macro
                          (Macro.mk
                            (Path.mk false [(PathSegment.mk "panic" PathArguments.none)])
                            MacroDelimiter.paren
                            (MacroBody.exprs [(Expr.lit (Lit.str "non-pointer GetMetadata"))] false)))
                        false)])))),
            (Stmt.letStmt
              []
              (Pat.ident false false "meta_value" none)
              (some
                (Expr.methodCall
                  (Expr.methodCall
                    (Expr.path none (Path.mk false [(PathSegment.mk "ptr_ty" PathArguments.none)]))
                    "meta_kind"
                    none
                    [])
                  "encode_as_value"
                  (some
                    [
                      (GenericArgument.type
                        (Ty.path none (Path.mk false [(PathSegment.mk "M" PathArguments.none)])))])
                  [
                    (Expr.field
                      (Expr.path none (Path.mk false [(PathSegment.mk "ptr" PathArguments.none)]))
                      (Member.named "metadata"))]))
              none),
            (Stmt.letStmt
              []
              (Pat.ident false false "meta_ty" none)
              (some
                (Expr.methodCall
                  (Expr.methodCall
                    (Expr.path none (Path.mk false [(PathSegment.mk "ptr_ty" PathArguments.none)]))
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
                              (PathSegment.mk "M" PathArguments.none),
                              (PathSegment.mk "T" PathArguments.none)])))])
                  []))
              none),
            (Stmt.expr
              (Expr.methodCall
                (Expr.methodCall
                  (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                  "check_value"
                  none
                  [
                    (Expr.path
                      none
                      (Path.mk false [(PathSegment.mk "meta_value" PathArguments.none)])),
                    (Expr.path none (Path.mk false [(PathSegment.mk "meta_ty" PathArguments.none)]))])
                "expect"
                none
                [(Expr.lit (Lit.str "GetMetadata: sanity check, returned meta is well-formed"))])
              true),
            (Stmt.expr
              (Expr.call
                (Expr.path none (Path.mk false [(PathSegment.mk "ret" PathArguments.none)]))
                [
                  (Expr.tuple
                    [
                      (Expr.path
                        none
                        (Path.mk false [(PathSegment.mk "meta_value" PathArguments.none)])),
                      (Expr.path
                        none
                        (Path.mk false [(PathSegment.mk "meta_ty" PathArguments.none)]))])])
              false)]))])

/-- `spec/lang/step/operators.md:130` -/
def impl_Machine__eval_un_op_2 : Item :=
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
          "eval_un_op"
          (Generics.mk [] [])
          [
            (FnArg.receiver [] true none false none),
            (FnArg.typed
              []
              (Pat.tupleStruct
                none
                (Path.mk
                  false
                  [
                    (PathSegment.mk "UnOp" PathArguments.none),
                    (PathSegment.mk "ComputeSize" PathArguments.none)])
                [(Pat.ident false false "ty" none)])
              (Ty.path none (Path.mk false [(PathSegment.mk "UnOp" PathArguments.none)]))),
            (FnArg.typed
              []
              (Pat.tuple
                [(Pat.ident false false "operand" none), (Pat.ident false false "op_ty" none)])
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
                                  (Path.mk false [(PathSegment.mk "M" PathArguments.none)])))]))])),
                  (Ty.path none (Path.mk false [(PathSegment.mk "Type" PathArguments.none)]))]))]
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
                                (Path.mk false [(PathSegment.mk "Type" PathArguments.none)]))]))]))]))))
        (Block.mk
          [
            (Stmt.letStmt
              []
              (Pat.ident false false "meta" none)
              (some
                (Expr.methodCall
                  (Expr.methodCall
                    (Expr.path none (Path.mk false [(PathSegment.mk "ty" PathArguments.none)]))
                    "meta_kind"
                    none
                    [])
                  "decode_value"
                  (some
                    [
                      (GenericArgument.type
                        (Ty.path none (Path.mk false [(PathSegment.mk "M" PathArguments.none)])))])
                  [(Expr.path none (Path.mk false [(PathSegment.mk "operand" PathArguments.none)]))]))
              none),
            (Stmt.letStmt
              []
              (Pat.ident false false "size" none)
              (some
                (Expr.methodCall
                  (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                  "compute_size"
                  none
                  [
                    (Expr.methodCall
                      (Expr.path none (Path.mk false [(PathSegment.mk "ty" PathArguments.none)]))
                      "layout"
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
                      []),
                    (Expr.path none (Path.mk false [(PathSegment.mk "meta" PathArguments.none)]))]))
              none),
            (Stmt.expr
              (Expr.call
                (Expr.path none (Path.mk false [(PathSegment.mk "ret" PathArguments.none)]))
                [
                  (Expr.tuple
                    [
                      (Expr.call
                        (Expr.path
                          none
                          (Path.mk
                            false
                            [
                              (PathSegment.mk "Value" PathArguments.none),
                              (PathSegment.mk "Int" PathArguments.none)]))
                        [
                          (Expr.methodCall
                            (Expr.path
                              none
                              (Path.mk false [(PathSegment.mk "size" PathArguments.none)]))
                            "bytes"
                            none
                            [])]),
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
                                  (PathSegment.mk "IntType" PathArguments.none),
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
                                                (PathSegment.mk "M" PathArguments.none),
                                                (PathSegment.mk "T" PathArguments.none)])))]))]))
                            [])])])])
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
          "eval_un_op"
          (Generics.mk [] [])
          [
            (FnArg.receiver [] true none false none),
            (FnArg.typed
              []
              (Pat.tupleStruct
                none
                (Path.mk
                  false
                  [
                    (PathSegment.mk "UnOp" PathArguments.none),
                    (PathSegment.mk "ComputeAlign" PathArguments.none)])
                [(Pat.ident false false "ty" none)])
              (Ty.path none (Path.mk false [(PathSegment.mk "UnOp" PathArguments.none)]))),
            (FnArg.typed
              []
              (Pat.tuple
                [(Pat.ident false false "operand" none), (Pat.ident false false "op_ty" none)])
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
                                  (Path.mk false [(PathSegment.mk "M" PathArguments.none)])))]))])),
                  (Ty.path none (Path.mk false [(PathSegment.mk "Type" PathArguments.none)]))]))]
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
                                (Path.mk false [(PathSegment.mk "Type" PathArguments.none)]))]))]))]))))
        (Block.mk
          [
            (Stmt.letStmt
              []
              (Pat.ident false false "meta" none)
              (some
                (Expr.methodCall
                  (Expr.methodCall
                    (Expr.path none (Path.mk false [(PathSegment.mk "ty" PathArguments.none)]))
                    "meta_kind"
                    none
                    [])
                  "decode_value"
                  (some
                    [
                      (GenericArgument.type
                        (Ty.path none (Path.mk false [(PathSegment.mk "M" PathArguments.none)])))])
                  [(Expr.path none (Path.mk false [(PathSegment.mk "operand" PathArguments.none)]))]))
              none),
            (Stmt.letStmt
              []
              (Pat.ident false false "align" none)
              (some
                (Expr.methodCall
                  (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                  "compute_align"
                  none
                  [
                    (Expr.methodCall
                      (Expr.path none (Path.mk false [(PathSegment.mk "ty" PathArguments.none)]))
                      "layout"
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
                      []),
                    (Expr.path none (Path.mk false [(PathSegment.mk "meta" PathArguments.none)]))]))
              none),
            (Stmt.expr
              (Expr.call
                (Expr.path none (Path.mk false [(PathSegment.mk "ret" PathArguments.none)]))
                [
                  (Expr.tuple
                    [
                      (Expr.call
                        (Expr.path
                          none
                          (Path.mk
                            false
                            [
                              (PathSegment.mk "Value" PathArguments.none),
                              (PathSegment.mk "Int" PathArguments.none)]))
                        [
                          (Expr.methodCall
                            (Expr.path
                              none
                              (Path.mk false [(PathSegment.mk "align" PathArguments.none)]))
                            "bytes"
                            none
                            [])]),
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
                                  (PathSegment.mk "IntType" PathArguments.none),
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
                                                (PathSegment.mk "M" PathArguments.none),
                                                (PathSegment.mk "T" PathArguments.none)])))]))]))
                            [])])])])
              false)]))])

/-- `spec/lang/step/operators.md:152` -/
def impl_Machine__eval_un_op_3 : Item :=
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
          "eval_un_op"
          (Generics.mk [] [])
          [
            (FnArg.receiver [] true none false none),
            (FnArg.typed
              []
              (Pat.tupleStruct
                none
                (Path.mk
                  false
                  [
                    (PathSegment.mk "UnOp" PathArguments.none),
                    (PathSegment.mk "VTableMethodLookup" PathArguments.none)])
                [(Pat.ident false false "method" none)])
              (Ty.path none (Path.mk false [(PathSegment.mk "UnOp" PathArguments.none)]))),
            (FnArg.typed
              []
              (Pat.tuple
                [(Pat.ident false false "operand" none), (Pat.ident false false "op_ty" none)])
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
                                  (Path.mk false [(PathSegment.mk "M" PathArguments.none)])))]))])),
                  (Ty.path none (Path.mk false [(PathSegment.mk "Type" PathArguments.none)]))]))]
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
                                (Path.mk false [(PathSegment.mk "Type" PathArguments.none)]))]))]))]))))
        (Block.mk
          [
            (Stmt.letStmt
              []
              (Pat.tuple
                [
                  (Pat.tupleStruct
                    none
                    (Path.mk
                      false
                      [
                        (PathSegment.mk "Value" PathArguments.none),
                        (PathSegment.mk "Ptr" PathArguments.none)])
                    [(Pat.ident false false "ptr" none)]),
                  (Pat.tupleStruct
                    none
                    (Path.mk
                      false
                      [
                        (PathSegment.mk "Type" PathArguments.none),
                        (PathSegment.mk "Ptr" PathArguments.none)])
                    [(Pat.ident false false "_ptr_ty" none)])])
              (some
                (Expr.tuple
                  [
                    (Expr.path none (Path.mk false [(PathSegment.mk "operand" PathArguments.none)])),
                    (Expr.path none (Path.mk false [(PathSegment.mk "op_ty" PathArguments.none)]))]))
              (some
                (Expr.block
                  none
                  (Block.mk
                    [
                      (Stmt.macro
                        []
                        (Macro.mk
                          (Path.mk false [(PathSegment.mk "panic" PathArguments.none)])
                          MacroDelimiter.paren
                          (MacroBody.exprs
                            [(Expr.lit (Lit.str "vtable lookup on non-pointer"))]
                            false))
                        true)])))),
            (Stmt.letStmt
              []
              (Pat.ident false false "vtable" none)
              (some
                (Expr.call
                  (Expr.methodCall
                    (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                    "vtable_lookup"
                    none
                    [])
                  [
                    (Expr.field
                      (Expr.path none (Path.mk false [(PathSegment.mk "ptr" PathArguments.none)]))
                      (Member.named "thin_pointer"))]))
              none),
            (Stmt.letStmt
              []
              (Pat.ident false false "fn_name" none)
              (some
                (Expr.index
                  (Expr.field
                    (Expr.path none (Path.mk false [(PathSegment.mk "vtable" PathArguments.none)]))
                    (Member.named "methods"))
                  (Expr.path none (Path.mk false [(PathSegment.mk "method" PathArguments.none)]))))
              none),
            (Stmt.letStmt
              []
              (Pat.ident false false "fn_ptr" none)
              (some
                (Expr.call
                  (Expr.path
                    none
                    (Path.mk
                      false
                      [
                        (PathSegment.mk "Value" PathArguments.none),
                        (PathSegment.mk "Ptr" PathArguments.none)]))
                  [
                    (Expr.methodCall
                      (Expr.index
                        (Expr.field
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                          (Member.named "fn_ptrs"))
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "fn_name" PathArguments.none)])))
                      "widen"
                      none
                      [
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "None" PathArguments.none)]))])]))
              none),
            (Stmt.expr
              (Expr.call
                (Expr.path none (Path.mk false [(PathSegment.mk "ret" PathArguments.none)]))
                [
                  (Expr.tuple
                    [
                      (Expr.path
                        none
                        (Path.mk false [(PathSegment.mk "fn_ptr" PathArguments.none)])),
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
                                (PathSegment.mk "PtrType" PathArguments.none),
                                (PathSegment.mk "FnPtr" PathArguments.none)]))])])])
              false)]))])

/-- `spec/lang/step/operators.md:171` -/
def impl_Machine__eval_bin_op_0 : Item :=
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
        [(Attr.mk true "specr::argmatch" (AttrMeta.list "operator"))]
        Visibility.inherited
        false
        (Signature.mk
          false
          false
          false
          none
          "eval_bin_op"
          (Generics.mk [] [])
          [
            (FnArg.receiver [] true none false none),
            (FnArg.typed
              []
              (Pat.ident false false "operator" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "BinOp" PathArguments.none)]))),
            (FnArg.typed
              []
              (Pat.tuple [(Pat.ident false false "left" none), (Pat.ident false false "l_ty" none)])
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
                                  (Path.mk false [(PathSegment.mk "M" PathArguments.none)])))]))])),
                  (Ty.path none (Path.mk false [(PathSegment.mk "Type" PathArguments.none)]))])),
            (FnArg.typed
              []
              (Pat.tuple
                [(Pat.ident false false "right" none), (Pat.ident false false "_r_ty" none)])
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
                                  (Path.mk false [(PathSegment.mk "M" PathArguments.none)])))]))])),
                  (Ty.path none (Path.mk false [(PathSegment.mk "Type" PathArguments.none)]))]))]
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
                                (Path.mk false [(PathSegment.mk "Type" PathArguments.none)]))]))]))]))))
        (Block.mk [(Stmt.expr (Expr.range none RangeLimits.halfOpen none) false)]))])

/-- `spec/lang/step/operators.md:186` -/
def impl_Machine__eval_int_bin_op : Item :=
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
          "eval_int_bin_op"
          (Generics.mk [] [])
          [
            (FnArg.typed
              []
              (Pat.ident false false "op" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "IntBinOp" PathArguments.none)]))),
            (FnArg.typed
              []
              (Pat.ident false false "left" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "Int" PathArguments.none)]))),
            (FnArg.typed
              []
              (Pat.ident false false "right" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "Int" PathArguments.none)]))),
            (FnArg.typed
              []
              (Pat.ident false false "left_ty" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "IntType" PathArguments.none)])))]
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
                          (Ty.path none (Path.mk false [(PathSegment.mk "Int" PathArguments.none)])))]))]))))
        (Block.mk
          [
            (Stmt.item
              (Item.use [] Visibility.inherited false (UseTree.path "IntBinOp" UseTree.glob))),
            (Stmt.expr
              (Expr.call
                (Expr.path none (Path.mk false [(PathSegment.mk "ret" PathArguments.none)]))
                [
                  (Expr.matchExpr
                    (Expr.path none (Path.mk false [(PathSegment.mk "op" PathArguments.none)]))
                    [
                      (Arm.mk
                        []
                        (Pat.ident false false "Add" none)
                        none
                        (Expr.binary
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "left" PathArguments.none)]))
                          BinOp.add
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "right" PathArguments.none)])))),
                      (Arm.mk
                        []
                        (Pat.ident false false "AddUnchecked" none)
                        none
                        (Expr.block
                          none
                          (Block.mk
                            [
                              (Stmt.letStmt
                                []
                                (Pat.ident false false "result" none)
                                (some
                                  (Expr.binary
                                    (Expr.path
                                      none
                                      (Path.mk false [(PathSegment.mk "left" PathArguments.none)]))
                                    BinOp.add
                                    (Expr.path
                                      none
                                      (Path.mk false [(PathSegment.mk "right" PathArguments.none)]))))
                                none),
                              (Stmt.expr
                                (Expr.ite
                                  (Expr.unary
                                    UnOp.not
                                    (Expr.methodCall
                                      (Expr.path
                                        none
                                        (Path.mk
                                          false
                                          [(PathSegment.mk "left_ty" PathArguments.none)]))
                                      "can_represent"
                                      none
                                      [
                                        (Expr.path
                                          none
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "result" PathArguments.none)]))]))
                                  (Block.mk
                                    [
                                      (Stmt.macro
                                        []
                                        (Macro.mk
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "throw_ub" PathArguments.none)])
                                          MacroDelimiter.paren
                                          (MacroBody.exprs
                                            [(Expr.lit (Lit.str "overflow in unchecked add"))]
                                            false))
                                        true)])
                                  none)
                                false),
                              (Stmt.expr
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "result" PathArguments.none)]))
                                false)]))),
                      (Arm.mk
                        []
                        (Pat.ident false false "Sub" none)
                        none
                        (Expr.binary
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "left" PathArguments.none)]))
                          BinOp.sub
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "right" PathArguments.none)])))),
                      (Arm.mk
                        []
                        (Pat.ident false false "SubUnchecked" none)
                        none
                        (Expr.block
                          none
                          (Block.mk
                            [
                              (Stmt.letStmt
                                []
                                (Pat.ident false false "result" none)
                                (some
                                  (Expr.binary
                                    (Expr.path
                                      none
                                      (Path.mk false [(PathSegment.mk "left" PathArguments.none)]))
                                    BinOp.sub
                                    (Expr.path
                                      none
                                      (Path.mk false [(PathSegment.mk "right" PathArguments.none)]))))
                                none),
                              (Stmt.expr
                                (Expr.ite
                                  (Expr.unary
                                    UnOp.not
                                    (Expr.methodCall
                                      (Expr.path
                                        none
                                        (Path.mk
                                          false
                                          [(PathSegment.mk "left_ty" PathArguments.none)]))
                                      "can_represent"
                                      none
                                      [
                                        (Expr.path
                                          none
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "result" PathArguments.none)]))]))
                                  (Block.mk
                                    [
                                      (Stmt.macro
                                        []
                                        (Macro.mk
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "throw_ub" PathArguments.none)])
                                          MacroDelimiter.paren
                                          (MacroBody.exprs
                                            [(Expr.lit (Lit.str "overflow in unchecked sub"))]
                                            false))
                                        true)])
                                  none)
                                false),
                              (Stmt.expr
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "result" PathArguments.none)]))
                                false)]))),
                      (Arm.mk
                        []
                        (Pat.ident false false "Mul" none)
                        none
                        (Expr.binary
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "left" PathArguments.none)]))
                          BinOp.mul
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "right" PathArguments.none)])))),
                      (Arm.mk
                        []
                        (Pat.ident false false "MulUnchecked" none)
                        none
                        (Expr.block
                          none
                          (Block.mk
                            [
                              (Stmt.letStmt
                                []
                                (Pat.ident false false "result" none)
                                (some
                                  (Expr.binary
                                    (Expr.path
                                      none
                                      (Path.mk false [(PathSegment.mk "left" PathArguments.none)]))
                                    BinOp.mul
                                    (Expr.path
                                      none
                                      (Path.mk false [(PathSegment.mk "right" PathArguments.none)]))))
                                none),
                              (Stmt.expr
                                (Expr.ite
                                  (Expr.unary
                                    UnOp.not
                                    (Expr.methodCall
                                      (Expr.path
                                        none
                                        (Path.mk
                                          false
                                          [(PathSegment.mk "left_ty" PathArguments.none)]))
                                      "can_represent"
                                      none
                                      [
                                        (Expr.path
                                          none
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "result" PathArguments.none)]))]))
                                  (Block.mk
                                    [
                                      (Stmt.macro
                                        []
                                        (Macro.mk
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "throw_ub" PathArguments.none)])
                                          MacroDelimiter.paren
                                          (MacroBody.exprs
                                            [(Expr.lit (Lit.str "overflow in unchecked mul"))]
                                            false))
                                        true)])
                                  none)
                                false),
                              (Stmt.expr
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "result" PathArguments.none)]))
                                false)]))),
                      (Arm.mk
                        []
                        (Pat.ident false false "Div" none)
                        none
                        (Expr.block
                          none
                          (Block.mk
                            [
                              (Stmt.expr
                                (Expr.ite
                                  (Expr.binary
                                    (Expr.path
                                      none
                                      (Path.mk false [(PathSegment.mk "right" PathArguments.none)]))
                                    BinOp.eq
                                    (Expr.lit (Lit.int 0 "")))
                                  (Block.mk
                                    [
                                      (Stmt.macro
                                        []
                                        (Macro.mk
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "throw_ub" PathArguments.none)])
                                          MacroDelimiter.paren
                                          (MacroBody.exprs
                                            [(Expr.lit (Lit.str "division by zero"))]
                                            false))
                                        true)])
                                  none)
                                false),
                              (Stmt.letStmt
                                []
                                (Pat.ident false false "result" none)
                                (some
                                  (Expr.binary
                                    (Expr.path
                                      none
                                      (Path.mk false [(PathSegment.mk "left" PathArguments.none)]))
                                    BinOp.div
                                    (Expr.path
                                      none
                                      (Path.mk false [(PathSegment.mk "right" PathArguments.none)]))))
                                none),
                              (Stmt.expr
                                (Expr.ite
                                  (Expr.unary
                                    UnOp.not
                                    (Expr.methodCall
                                      (Expr.path
                                        none
                                        (Path.mk
                                          false
                                          [(PathSegment.mk "left_ty" PathArguments.none)]))
                                      "can_represent"
                                      none
                                      [
                                        (Expr.path
                                          none
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "result" PathArguments.none)]))]))
                                  (Block.mk
                                    [
                                      (Stmt.macro
                                        []
                                        (Macro.mk
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "throw_ub" PathArguments.none)])
                                          MacroDelimiter.paren
                                          (MacroBody.exprs
                                            [(Expr.lit (Lit.str "overflow in division"))]
                                            false))
                                        true)])
                                  none)
                                false),
                              (Stmt.expr
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "result" PathArguments.none)]))
                                false)]))),
                      (Arm.mk
                        []
                        (Pat.ident false false "DivExact" none)
                        none
                        (Expr.block
                          none
                          (Block.mk
                            [
                              (Stmt.expr
                                (Expr.ite
                                  (Expr.binary
                                    (Expr.path
                                      none
                                      (Path.mk false [(PathSegment.mk "right" PathArguments.none)]))
                                    BinOp.eq
                                    (Expr.lit (Lit.int 0 "")))
                                  (Block.mk
                                    [
                                      (Stmt.macro
                                        []
                                        (Macro.mk
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "throw_ub" PathArguments.none)])
                                          MacroDelimiter.paren
                                          (MacroBody.exprs
                                            [(Expr.lit (Lit.str "division by zero"))]
                                            false))
                                        true)])
                                  none)
                                false),
                              (Stmt.letStmt
                                []
                                (Pat.ident false false "result" none)
                                (some
                                  (Expr.binary
                                    (Expr.path
                                      none
                                      (Path.mk false [(PathSegment.mk "left" PathArguments.none)]))
                                    BinOp.div
                                    (Expr.path
                                      none
                                      (Path.mk false [(PathSegment.mk "right" PathArguments.none)]))))
                                none),
                              (Stmt.expr
                                (Expr.ite
                                  (Expr.unary
                                    UnOp.not
                                    (Expr.methodCall
                                      (Expr.path
                                        none
                                        (Path.mk
                                          false
                                          [(PathSegment.mk "left_ty" PathArguments.none)]))
                                      "can_represent"
                                      none
                                      [
                                        (Expr.path
                                          none
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "result" PathArguments.none)]))]))
                                  (Block.mk
                                    [
                                      (Stmt.macro
                                        []
                                        (Macro.mk
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "throw_ub" PathArguments.none)])
                                          MacroDelimiter.paren
                                          (MacroBody.exprs
                                            [(Expr.lit (Lit.str "overflow in division"))]
                                            false))
                                        true)])
                                  none)
                                false),
                              (Stmt.expr
                                (Expr.ite
                                  (Expr.binary
                                    (Expr.binary
                                      (Expr.path
                                        none
                                        (Path.mk false [(PathSegment.mk "left" PathArguments.none)]))
                                      BinOp.rem
                                      (Expr.path
                                        none
                                        (Path.mk
                                          false
                                          [(PathSegment.mk "right" PathArguments.none)])))
                                    BinOp.ne
                                    (Expr.lit (Lit.int 0 "")))
                                  (Block.mk
                                    [
                                      (Stmt.macro
                                        []
                                        (Macro.mk
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "throw_ub" PathArguments.none)])
                                          MacroDelimiter.paren
                                          (MacroBody.exprs
                                            [
                                              (Expr.lit
                                                (Lit.str "non-zero remainder in exact division"))]
                                            false))
                                        true)])
                                  none)
                                false),
                              (Stmt.expr
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "result" PathArguments.none)]))
                                false)]))),
                      (Arm.mk
                        []
                        (Pat.ident false false "Rem" none)
                        none
                        (Expr.block
                          none
                          (Block.mk
                            [
                              (Stmt.expr
                                (Expr.ite
                                  (Expr.binary
                                    (Expr.path
                                      none
                                      (Path.mk false [(PathSegment.mk "right" PathArguments.none)]))
                                    BinOp.eq
                                    (Expr.lit (Lit.int 0 "")))
                                  (Block.mk
                                    [
                                      (Stmt.macro
                                        []
                                        (Macro.mk
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "throw_ub" PathArguments.none)])
                                          MacroDelimiter.paren
                                          (MacroBody.exprs
                                            [(Expr.lit (Lit.str "modulus of remainder is zero"))]
                                            false))
                                        true)])
                                  none)
                                false),
                              (Stmt.expr
                                (Expr.ite
                                  (Expr.unary
                                    UnOp.not
                                    (Expr.methodCall
                                      (Expr.path
                                        none
                                        (Path.mk
                                          false
                                          [(PathSegment.mk "left_ty" PathArguments.none)]))
                                      "can_represent"
                                      none
                                      [
                                        (Expr.binary
                                          (Expr.path
                                            none
                                            (Path.mk
                                              false
                                              [(PathSegment.mk "left" PathArguments.none)]))
                                          BinOp.div
                                          (Expr.path
                                            none
                                            (Path.mk
                                              false
                                              [(PathSegment.mk "right" PathArguments.none)])))]))
                                  (Block.mk
                                    [
                                      (Stmt.macro
                                        []
                                        (Macro.mk
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "throw_ub" PathArguments.none)])
                                          MacroDelimiter.paren
                                          (MacroBody.exprs
                                            [(Expr.lit (Lit.str "overflow in remainder"))]
                                            false))
                                        true)])
                                  none)
                                false),
                              (Stmt.expr
                                (Expr.binary
                                  (Expr.path
                                    none
                                    (Path.mk false [(PathSegment.mk "left" PathArguments.none)]))
                                  BinOp.rem
                                  (Expr.path
                                    none
                                    (Path.mk false [(PathSegment.mk "right" PathArguments.none)])))
                                false)]))),
                      (Arm.mk
                        []
                        (Pat.or
                          [(Pat.ident false false "Shl" none), (Pat.ident false false "Shr" none)])
                        none
                        (Expr.block
                          none
                          (Block.mk
                            [
                              (Stmt.letStmt
                                []
                                (Pat.ident false false "bits" none)
                                (some
                                  (Expr.methodCall
                                    (Expr.field
                                      (Expr.path
                                        none
                                        (Path.mk
                                          false
                                          [(PathSegment.mk "left_ty" PathArguments.none)]))
                                      (Member.named "size"))
                                    "bits"
                                    none
                                    []))
                                none),
                              (Stmt.letStmt
                                []
                                (Pat.ident false false "offset" none)
                                (some
                                  (Expr.methodCall
                                    (Expr.path
                                      none
                                      (Path.mk false [(PathSegment.mk "right" PathArguments.none)]))
                                    "rem_euclid"
                                    none
                                    [
                                      (Expr.path
                                        none
                                        (Path.mk false [(PathSegment.mk "bits" PathArguments.none)]))]))
                                none),
                              (Stmt.expr
                                (Expr.matchExpr
                                  (Expr.path
                                    none
                                    (Path.mk false [(PathSegment.mk "op" PathArguments.none)]))
                                  [
                                    (Arm.mk
                                      []
                                      (Pat.ident false false "Shl" none)
                                      none
                                      (Expr.binary
                                        (Expr.path
                                          none
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "left" PathArguments.none)]))
                                        BinOp.shl
                                        (Expr.path
                                          none
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "offset" PathArguments.none)])))),
                                    (Arm.mk
                                      []
                                      (Pat.ident false false "Shr" none)
                                      none
                                      (Expr.binary
                                        (Expr.path
                                          none
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "left" PathArguments.none)]))
                                        BinOp.shr
                                        (Expr.path
                                          none
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "offset" PathArguments.none)])))),
                                    (Arm.mk
                                      []
                                      Pat.wild
                                      none
                                      (Expr.macro
                                        (Macro.mk
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "panic" PathArguments.none)])
                                          MacroDelimiter.paren
                                          (MacroBody.exprs [] false))))])
                                false)]))),
                      (Arm.mk
                        []
                        (Pat.or
                          [
                            (Pat.ident false false "ShlUnchecked" none),
                            (Pat.ident false false "ShrUnchecked" none)])
                        none
                        (Expr.block
                          none
                          (Block.mk
                            [
                              (Stmt.letStmt
                                []
                                (Pat.ident false false "bits" none)
                                (some
                                  (Expr.methodCall
                                    (Expr.field
                                      (Expr.path
                                        none
                                        (Path.mk
                                          false
                                          [(PathSegment.mk "left_ty" PathArguments.none)]))
                                      (Member.named "size"))
                                    "bits"
                                    none
                                    []))
                                none),
                              (Stmt.expr
                                (Expr.ite
                                  (Expr.binary
                                    (Expr.binary
                                      (Expr.path
                                        none
                                        (Path.mk
                                          false
                                          [(PathSegment.mk "right" PathArguments.none)]))
                                      BinOp.lt
                                      (Expr.lit (Lit.int 0 "")))
                                    BinOp.or
                                    (Expr.binary
                                      (Expr.path
                                        none
                                        (Path.mk
                                          false
                                          [(PathSegment.mk "right" PathArguments.none)]))
                                      BinOp.ge
                                      (Expr.path
                                        none
                                        (Path.mk false [(PathSegment.mk "bits" PathArguments.none)]))))
                                  (Block.mk
                                    [
                                      (Stmt.macro
                                        []
                                        (Macro.mk
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "throw_ub" PathArguments.none)])
                                          MacroDelimiter.paren
                                          (MacroBody.exprs
                                            [(Expr.lit (Lit.str "overflow in unchecked shift"))]
                                            false))
                                        true)])
                                  none)
                                false),
                              (Stmt.expr
                                (Expr.matchExpr
                                  (Expr.path
                                    none
                                    (Path.mk false [(PathSegment.mk "op" PathArguments.none)]))
                                  [
                                    (Arm.mk
                                      []
                                      (Pat.ident false false "ShlUnchecked" none)
                                      none
                                      (Expr.binary
                                        (Expr.path
                                          none
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "left" PathArguments.none)]))
                                        BinOp.shl
                                        (Expr.path
                                          none
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "right" PathArguments.none)])))),
                                    (Arm.mk
                                      []
                                      (Pat.ident false false "ShrUnchecked" none)
                                      none
                                      (Expr.binary
                                        (Expr.path
                                          none
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "left" PathArguments.none)]))
                                        BinOp.shr
                                        (Expr.path
                                          none
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "right" PathArguments.none)])))),
                                    (Arm.mk
                                      []
                                      Pat.wild
                                      none
                                      (Expr.macro
                                        (Macro.mk
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "panic" PathArguments.none)])
                                          MacroDelimiter.paren
                                          (MacroBody.exprs [] false))))])
                                false)]))),
                      (Arm.mk
                        []
                        (Pat.ident false false "BitAnd" none)
                        none
                        (Expr.binary
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "left" PathArguments.none)]))
                          BinOp.bitAnd
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "right" PathArguments.none)])))),
                      (Arm.mk
                        []
                        (Pat.ident false false "BitOr" none)
                        none
                        (Expr.binary
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "left" PathArguments.none)]))
                          BinOp.bitOr
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "right" PathArguments.none)])))),
                      (Arm.mk
                        []
                        (Pat.ident false false "BitXor" none)
                        none
                        (Expr.binary
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "left" PathArguments.none)]))
                          BinOp.bitXor
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "right" PathArguments.none)]))))])])
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
          "eval_bin_op"
          (Generics.mk [] [])
          [
            (FnArg.receiver [] true none false none),
            (FnArg.typed
              []
              (Pat.tupleStruct
                none
                (Path.mk
                  false
                  [
                    (PathSegment.mk "BinOp" PathArguments.none),
                    (PathSegment.mk "Int" PathArguments.none)])
                [(Pat.ident false false "op" none)])
              (Ty.path none (Path.mk false [(PathSegment.mk "BinOp" PathArguments.none)]))),
            (FnArg.typed
              []
              (Pat.tuple [(Pat.ident false false "left" none), (Pat.ident false false "l_ty" none)])
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
                                  (Path.mk false [(PathSegment.mk "M" PathArguments.none)])))]))])),
                  (Ty.path none (Path.mk false [(PathSegment.mk "Type" PathArguments.none)]))])),
            (FnArg.typed
              []
              (Pat.tuple
                [(Pat.ident false false "right" none), (Pat.ident false false "_r_ty" none)])
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
                                  (Path.mk false [(PathSegment.mk "M" PathArguments.none)])))]))])),
                  (Ty.path none (Path.mk false [(PathSegment.mk "Type" PathArguments.none)]))]))]
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
                                (Path.mk false [(PathSegment.mk "Type" PathArguments.none)]))]))]))]))))
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
              (some (Expr.path none (Path.mk false [(PathSegment.mk "l_ty" PathArguments.none)])))
              (some
                (Expr.block
                  none
                  (Block.mk
                    [
                      (Stmt.expr
                        (Expr.macro
                          (Macro.mk
                            (Path.mk false [(PathSegment.mk "panic" PathArguments.none)])
                            MacroDelimiter.paren
                            (MacroBody.exprs
                              [(Expr.lit (Lit.str "non-integer input to integer operation"))]
                              false)))
                        false)])))),
            (Stmt.letStmt
              []
              (Pat.tupleStruct
                none
                (Path.mk
                  false
                  [
                    (PathSegment.mk "Value" PathArguments.none),
                    (PathSegment.mk "Int" PathArguments.none)])
                [(Pat.ident false false "left" none)])
              (some (Expr.path none (Path.mk false [(PathSegment.mk "left" PathArguments.none)])))
              (some
                (Expr.block
                  none
                  (Block.mk
                    [
                      (Stmt.expr
                        (Expr.macro
                          (Macro.mk
                            (Path.mk false [(PathSegment.mk "panic" PathArguments.none)])
                            MacroDelimiter.paren
                            (MacroBody.exprs
                              [(Expr.lit (Lit.str "non-integer input to integer operation"))]
                              false)))
                        false)])))),
            (Stmt.letStmt
              []
              (Pat.tupleStruct
                none
                (Path.mk
                  false
                  [
                    (PathSegment.mk "Value" PathArguments.none),
                    (PathSegment.mk "Int" PathArguments.none)])
                [(Pat.ident false false "right" none)])
              (some (Expr.path none (Path.mk false [(PathSegment.mk "right" PathArguments.none)])))
              (some
                (Expr.block
                  none
                  (Block.mk
                    [
                      (Stmt.expr
                        (Expr.macro
                          (Macro.mk
                            (Path.mk false [(PathSegment.mk "panic" PathArguments.none)])
                            MacroDelimiter.paren
                            (MacroBody.exprs
                              [(Expr.lit (Lit.str "non-integer input to integer operation"))]
                              false)))
                        false)])))),
            (Stmt.letStmt
              []
              (Pat.ident false false "result" none)
              (some
                (Expr.tryExpr
                  (Expr.call
                    (Expr.path
                      none
                      (Path.mk
                        false
                        [
                          (PathSegment.mk "Self" PathArguments.none),
                          (PathSegment.mk "eval_int_bin_op" PathArguments.none)]))
                    [
                      (Expr.path none (Path.mk false [(PathSegment.mk "op" PathArguments.none)])),
                      (Expr.path none (Path.mk false [(PathSegment.mk "left" PathArguments.none)])),
                      (Expr.path none (Path.mk false [(PathSegment.mk "right" PathArguments.none)])),
                      (Expr.path
                        none
                        (Path.mk false [(PathSegment.mk "int_ty" PathArguments.none)]))])))
              none),
            (Stmt.letStmt
              []
              (Pat.ident false false "result" none)
              (some
                (Expr.methodCall
                  (Expr.path none (Path.mk false [(PathSegment.mk "int_ty" PathArguments.none)]))
                  "bring_in_bounds"
                  none
                  [(Expr.path none (Path.mk false [(PathSegment.mk "result" PathArguments.none)]))]))
              none),
            (Stmt.expr
              (Expr.call
                (Expr.path none (Path.mk false [(PathSegment.mk "ret" PathArguments.none)]))
                [
                  (Expr.tuple
                    [
                      (Expr.call
                        (Expr.path
                          none
                          (Path.mk
                            false
                            [
                              (PathSegment.mk "Value" PathArguments.none),
                              (PathSegment.mk "Int" PathArguments.none)]))
                        [
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "result" PathArguments.none)]))]),
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
                            (Path.mk false [(PathSegment.mk "int_ty" PathArguments.none)]))])])])
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
          "eval_bin_op"
          (Generics.mk [] [])
          [
            (FnArg.receiver [] true none false none),
            (FnArg.typed
              []
              (Pat.tupleStruct
                none
                (Path.mk
                  false
                  [
                    (PathSegment.mk "BinOp" PathArguments.none),
                    (PathSegment.mk "IntWithOverflow" PathArguments.none)])
                [(Pat.ident false false "op" none)])
              (Ty.path none (Path.mk false [(PathSegment.mk "BinOp" PathArguments.none)]))),
            (FnArg.typed
              []
              (Pat.tuple [(Pat.ident false false "left" none), (Pat.ident false false "l_ty" none)])
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
                                  (Path.mk false [(PathSegment.mk "M" PathArguments.none)])))]))])),
                  (Ty.path none (Path.mk false [(PathSegment.mk "Type" PathArguments.none)]))])),
            (FnArg.typed
              []
              (Pat.tuple
                [(Pat.ident false false "right" none), (Pat.ident false false "_r_ty" none)])
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
                                  (Path.mk false [(PathSegment.mk "M" PathArguments.none)])))]))])),
                  (Ty.path none (Path.mk false [(PathSegment.mk "Type" PathArguments.none)]))]))]
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
                                (Path.mk false [(PathSegment.mk "Type" PathArguments.none)]))]))]))]))))
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
              (some (Expr.path none (Path.mk false [(PathSegment.mk "l_ty" PathArguments.none)])))
              (some
                (Expr.block
                  none
                  (Block.mk
                    [
                      (Stmt.expr
                        (Expr.macro
                          (Macro.mk
                            (Path.mk false [(PathSegment.mk "panic" PathArguments.none)])
                            MacroDelimiter.paren
                            (MacroBody.exprs
                              [(Expr.lit (Lit.str "non-integer input to integer operation"))]
                              false)))
                        false)])))),
            (Stmt.letStmt
              []
              (Pat.tupleStruct
                none
                (Path.mk
                  false
                  [
                    (PathSegment.mk "Value" PathArguments.none),
                    (PathSegment.mk "Int" PathArguments.none)])
                [(Pat.ident false false "left" none)])
              (some (Expr.path none (Path.mk false [(PathSegment.mk "left" PathArguments.none)])))
              (some
                (Expr.block
                  none
                  (Block.mk
                    [
                      (Stmt.expr
                        (Expr.macro
                          (Macro.mk
                            (Path.mk false [(PathSegment.mk "panic" PathArguments.none)])
                            MacroDelimiter.paren
                            (MacroBody.exprs
                              [(Expr.lit (Lit.str "non-integer input to integer operation"))]
                              false)))
                        false)])))),
            (Stmt.letStmt
              []
              (Pat.tupleStruct
                none
                (Path.mk
                  false
                  [
                    (PathSegment.mk "Value" PathArguments.none),
                    (PathSegment.mk "Int" PathArguments.none)])
                [(Pat.ident false false "right" none)])
              (some (Expr.path none (Path.mk false [(PathSegment.mk "right" PathArguments.none)])))
              (some
                (Expr.block
                  none
                  (Block.mk
                    [
                      (Stmt.expr
                        (Expr.macro
                          (Macro.mk
                            (Path.mk false [(PathSegment.mk "panic" PathArguments.none)])
                            MacroDelimiter.paren
                            (MacroBody.exprs
                              [(Expr.lit (Lit.str "non-integer input to integer operation"))]
                              false)))
                        false)])))),
            (Stmt.letStmt
              []
              (Pat.ident false false "result" none)
              (some
                (Expr.matchExpr
                  (Expr.path none (Path.mk false [(PathSegment.mk "op" PathArguments.none)]))
                  [
                    (Arm.mk
                      []
                      (Pat.path
                        none
                        (Path.mk
                          false
                          [
                            (PathSegment.mk "IntBinOpWithOverflow" PathArguments.none),
                            (PathSegment.mk "Add" PathArguments.none)]))
                      none
                      (Expr.binary
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "left" PathArguments.none)]))
                        BinOp.add
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "right" PathArguments.none)])))),
                    (Arm.mk
                      []
                      (Pat.path
                        none
                        (Path.mk
                          false
                          [
                            (PathSegment.mk "IntBinOpWithOverflow" PathArguments.none),
                            (PathSegment.mk "Sub" PathArguments.none)]))
                      none
                      (Expr.binary
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "left" PathArguments.none)]))
                        BinOp.sub
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "right" PathArguments.none)])))),
                    (Arm.mk
                      []
                      (Pat.path
                        none
                        (Path.mk
                          false
                          [
                            (PathSegment.mk "IntBinOpWithOverflow" PathArguments.none),
                            (PathSegment.mk "Mul" PathArguments.none)]))
                      none
                      (Expr.binary
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "left" PathArguments.none)]))
                        BinOp.mul
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "right" PathArguments.none)]))))]))
              none),
            (Stmt.letStmt
              []
              (Pat.ident false false "overflow" none)
              (some
                (Expr.unary
                  UnOp.not
                  (Expr.methodCall
                    (Expr.path none (Path.mk false [(PathSegment.mk "int_ty" PathArguments.none)]))
                    "can_represent"
                    none
                    [
                      (Expr.path
                        none
                        (Path.mk false [(PathSegment.mk "result" PathArguments.none)]))])))
              none),
            (Stmt.letStmt
              []
              (Pat.ident false false "result" none)
              (some
                (Expr.methodCall
                  (Expr.path none (Path.mk false [(PathSegment.mk "int_ty" PathArguments.none)]))
                  "bring_in_bounds"
                  none
                  [(Expr.path none (Path.mk false [(PathSegment.mk "result" PathArguments.none)]))]))
              none),
            (Stmt.letStmt
              []
              (Pat.ident false false "value" none)
              (some
                (Expr.call
                  (Expr.path
                    none
                    (Path.mk
                      false
                      [
                        (PathSegment.mk "Value" PathArguments.none),
                        (PathSegment.mk "Tuple" PathArguments.none)]))
                  [
                    (Expr.macro
                      (Macro.mk
                        (Path.mk false [(PathSegment.mk "list" PathArguments.none)])
                        MacroDelimiter.bracket
                        (MacroBody.exprs
                          [
                            (Expr.call
                              (Expr.path
                                none
                                (Path.mk
                                  false
                                  [
                                    (PathSegment.mk "Value" PathArguments.none),
                                    (PathSegment.mk
                                      "Int"
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
                                  (Path.mk false [(PathSegment.mk "result" PathArguments.none)]))]),
                            (Expr.call
                              (Expr.path
                                none
                                (Path.mk
                                  false
                                  [
                                    (PathSegment.mk "Value" PathArguments.none),
                                    (PathSegment.mk
                                      "Bool"
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
                                  (Path.mk false [(PathSegment.mk "overflow" PathArguments.none)]))])]
                          false)))]))
              none),
            (Stmt.letStmt
              []
              (Pat.ident false false "ty" none)
              (some
                (Expr.methodCall
                  (Expr.path none (Path.mk false [(PathSegment.mk "int_ty" PathArguments.none)]))
                  "with_overflow"
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
              none),
            (Stmt.expr
              (Expr.call
                (Expr.path none (Path.mk false [(PathSegment.mk "ret" PathArguments.none)]))
                [
                  (Expr.tuple
                    [
                      (Expr.path none (Path.mk false [(PathSegment.mk "value" PathArguments.none)])),
                      (Expr.path none (Path.mk false [(PathSegment.mk "ty" PathArguments.none)]))])])
              false)]))])

/-- `spec/lang/step/operators.md:320` -/
def impl_Machine__eval_rel_op : Item :=
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
              " Turns the ordering from the comparasion result into a value, depending on the operation."))]
        Visibility.inherited
        false
        (Signature.mk
          false
          false
          false
          none
          "eval_rel_op"
          (Generics.mk [] [])
          [
            (FnArg.typed
              []
              (Pat.ident false false "rel" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "RelOp" PathArguments.none)]))),
            (FnArg.typed
              []
              (Pat.ident false false "ord" none)
              (Ty.path
                none
                (Path.mk
                  false
                  [
                    (PathSegment.mk "std" PathArguments.none),
                    (PathSegment.mk "cmp" PathArguments.none),
                    (PathSegment.mk "Ordering" PathArguments.none)])))]
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
                        "Value"
                        (PathArguments.angleBracketed
                          false
                          [
                            (GenericArgument.type
                              (Ty.path
                                none
                                (Path.mk false [(PathSegment.mk "M" PathArguments.none)])))]))])),
                (Ty.path none (Path.mk false [(PathSegment.mk "Type" PathArguments.none)]))])))
        (Block.mk
          [
            (Stmt.item (Item.use [] Visibility.inherited false (UseTree.path "RelOp" UseTree.glob))),
            (Stmt.expr
              (Expr.matchExpr
                (Expr.path none (Path.mk false [(PathSegment.mk "rel" PathArguments.none)]))
                [
                  (Arm.mk
                    []
                    (Pat.ident false false "Lt" none)
                    none
                    (Expr.tuple
                      [
                        (Expr.call
                          (Expr.path
                            none
                            (Path.mk
                              false
                              [
                                (PathSegment.mk "Value" PathArguments.none),
                                (PathSegment.mk "Bool" PathArguments.none)]))
                          [
                            (Expr.methodCall
                              (Expr.path
                                none
                                (Path.mk false [(PathSegment.mk "ord" PathArguments.none)]))
                              "is_lt"
                              none
                              [])]),
                        (Expr.path
                          none
                          (Path.mk
                            false
                            [
                              (PathSegment.mk "Type" PathArguments.none),
                              (PathSegment.mk "Bool" PathArguments.none)]))])),
                  (Arm.mk
                    []
                    (Pat.ident false false "Gt" none)
                    none
                    (Expr.tuple
                      [
                        (Expr.call
                          (Expr.path
                            none
                            (Path.mk
                              false
                              [
                                (PathSegment.mk "Value" PathArguments.none),
                                (PathSegment.mk "Bool" PathArguments.none)]))
                          [
                            (Expr.methodCall
                              (Expr.path
                                none
                                (Path.mk false [(PathSegment.mk "ord" PathArguments.none)]))
                              "is_gt"
                              none
                              [])]),
                        (Expr.path
                          none
                          (Path.mk
                            false
                            [
                              (PathSegment.mk "Type" PathArguments.none),
                              (PathSegment.mk "Bool" PathArguments.none)]))])),
                  (Arm.mk
                    []
                    (Pat.ident false false "Le" none)
                    none
                    (Expr.tuple
                      [
                        (Expr.call
                          (Expr.path
                            none
                            (Path.mk
                              false
                              [
                                (PathSegment.mk "Value" PathArguments.none),
                                (PathSegment.mk "Bool" PathArguments.none)]))
                          [
                            (Expr.methodCall
                              (Expr.path
                                none
                                (Path.mk false [(PathSegment.mk "ord" PathArguments.none)]))
                              "is_le"
                              none
                              [])]),
                        (Expr.path
                          none
                          (Path.mk
                            false
                            [
                              (PathSegment.mk "Type" PathArguments.none),
                              (PathSegment.mk "Bool" PathArguments.none)]))])),
                  (Arm.mk
                    []
                    (Pat.ident false false "Ge" none)
                    none
                    (Expr.tuple
                      [
                        (Expr.call
                          (Expr.path
                            none
                            (Path.mk
                              false
                              [
                                (PathSegment.mk "Value" PathArguments.none),
                                (PathSegment.mk "Bool" PathArguments.none)]))
                          [
                            (Expr.methodCall
                              (Expr.path
                                none
                                (Path.mk false [(PathSegment.mk "ord" PathArguments.none)]))
                              "is_ge"
                              none
                              [])]),
                        (Expr.path
                          none
                          (Path.mk
                            false
                            [
                              (PathSegment.mk "Type" PathArguments.none),
                              (PathSegment.mk "Bool" PathArguments.none)]))])),
                  (Arm.mk
                    []
                    (Pat.ident false false "Eq" none)
                    none
                    (Expr.tuple
                      [
                        (Expr.call
                          (Expr.path
                            none
                            (Path.mk
                              false
                              [
                                (PathSegment.mk "Value" PathArguments.none),
                                (PathSegment.mk "Bool" PathArguments.none)]))
                          [
                            (Expr.methodCall
                              (Expr.path
                                none
                                (Path.mk false [(PathSegment.mk "ord" PathArguments.none)]))
                              "is_eq"
                              none
                              [])]),
                        (Expr.path
                          none
                          (Path.mk
                            false
                            [
                              (PathSegment.mk "Type" PathArguments.none),
                              (PathSegment.mk "Bool" PathArguments.none)]))])),
                  (Arm.mk
                    []
                    (Pat.ident false false "Ne" none)
                    none
                    (Expr.tuple
                      [
                        (Expr.call
                          (Expr.path
                            none
                            (Path.mk
                              false
                              [
                                (PathSegment.mk "Value" PathArguments.none),
                                (PathSegment.mk "Bool" PathArguments.none)]))
                          [
                            (Expr.methodCall
                              (Expr.path
                                none
                                (Path.mk false [(PathSegment.mk "ord" PathArguments.none)]))
                              "is_ne"
                              none
                              [])]),
                        (Expr.path
                          none
                          (Path.mk
                            false
                            [
                              (PathSegment.mk "Type" PathArguments.none),
                              (PathSegment.mk "Bool" PathArguments.none)]))])),
                  (Arm.mk
                    []
                    (Pat.ident false false "Cmp" none)
                    none
                    (Expr.block
                      none
                      (Block.mk
                        [
                          (Stmt.letStmt
                            []
                            (Pat.ident false false "val" none)
                            (some
                              (Expr.matchExpr
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "ord" PathArguments.none)]))
                                [
                                  (Arm.mk
                                    []
                                    (Pat.path
                                      none
                                      (Path.mk
                                        false
                                        [
                                          (PathSegment.mk "std" PathArguments.none),
                                          (PathSegment.mk "cmp" PathArguments.none),
                                          (PathSegment.mk "Ordering" PathArguments.none),
                                          (PathSegment.mk "Less" PathArguments.none)]))
                                    none
                                    (Expr.unary UnOp.neg (Expr.lit (Lit.int 1 "")))),
                                  (Arm.mk
                                    []
                                    (Pat.path
                                      none
                                      (Path.mk
                                        false
                                        [
                                          (PathSegment.mk "std" PathArguments.none),
                                          (PathSegment.mk "cmp" PathArguments.none),
                                          (PathSegment.mk "Ordering" PathArguments.none),
                                          (PathSegment.mk "Equal" PathArguments.none)]))
                                    none
                                    (Expr.lit (Lit.int 0 ""))),
                                  (Arm.mk
                                    []
                                    (Pat.path
                                      none
                                      (Path.mk
                                        false
                                        [
                                          (PathSegment.mk "std" PathArguments.none),
                                          (PathSegment.mk "cmp" PathArguments.none),
                                          (PathSegment.mk "Ordering" PathArguments.none),
                                          (PathSegment.mk "Greater" PathArguments.none)]))
                                    none
                                    (Expr.lit (Lit.int 1 "")))]))
                            none),
                          (Stmt.expr
                            (Expr.tuple
                              [
                                (Expr.call
                                  (Expr.path
                                    none
                                    (Path.mk
                                      false
                                      [
                                        (PathSegment.mk "Value" PathArguments.none),
                                        (PathSegment.mk "Int" PathArguments.none)]))
                                  [
                                    (Expr.call
                                      (Expr.path
                                        none
                                        (Path.mk
                                          false
                                          [
                                            (PathSegment.mk "Int" PathArguments.none),
                                            (PathSegment.mk "from" PathArguments.none)]))
                                      [
                                        (Expr.path
                                          none
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "val" PathArguments.none)]))])]),
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
                                          (PathSegment.mk "IntType" PathArguments.none),
                                          (PathSegment.mk "I8" PathArguments.none)]))])])
                            false)])))])
              false)])),
      (ImplItem.fn
        [
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue
              " Compares two pointers including their metadata, but ignoring provenance."))]
        Visibility.inherited
        false
        (Signature.mk
          false
          false
          false
          none
          "compare_ptr"
          (Generics.mk [] [])
          [
            (FnArg.typed
              []
              (Pat.ident false false "left" none)
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
              (Pat.ident false false "right" none)
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
                                  (PathSegment.mk "Provenance" PathArguments.none)])))]))])))]
          false
          (some
            (Ty.path
              none
              (Path.mk
                false
                [
                  (PathSegment.mk "std" PathArguments.none),
                  (PathSegment.mk "cmp" PathArguments.none),
                  (PathSegment.mk "Ordering" PathArguments.none)]))))
        (Block.mk
          [
            (Stmt.letStmt
              []
              (Pat.ident false false "thin_cmp" none)
              (some
                (Expr.methodCall
                  (Expr.field
                    (Expr.field
                      (Expr.path none (Path.mk false [(PathSegment.mk "left" PathArguments.none)]))
                      (Member.named "thin_pointer"))
                    (Member.named "addr"))
                  "cmp"
                  none
                  [
                    (Expr.reference
                      false
                      (Expr.field
                        (Expr.field
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "right" PathArguments.none)]))
                          (Member.named "thin_pointer"))
                        (Member.named "addr")))]))
              none),
            (Stmt.letStmt
              []
              (Pat.ident false false "meta_cmp" none)
              (some
                (Expr.matchExpr
                  (Expr.tuple
                    [
                      (Expr.field
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "left" PathArguments.none)]))
                        (Member.named "metadata")),
                      (Expr.field
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "right" PathArguments.none)]))
                        (Member.named "metadata"))])
                  [
                    (Arm.mk
                      []
                      (Pat.tuple
                        [(Pat.ident false false "None" none), (Pat.ident false false "None" none)])
                      none
                      (Expr.path
                        none
                        (Path.mk
                          false
                          [
                            (PathSegment.mk "std" PathArguments.none),
                            (PathSegment.mk "cmp" PathArguments.none),
                            (PathSegment.mk "Ordering" PathArguments.none),
                            (PathSegment.mk "Equal" PathArguments.none)]))),
                    (Arm.mk
                      []
                      (Pat.tuple
                        [
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
                                [(Pat.ident false false "l" none)])]),
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
                                [(Pat.ident false false "r" none)])])])
                      none
                      (Expr.methodCall
                        (Expr.path none (Path.mk false [(PathSegment.mk "l" PathArguments.none)]))
                        "cmp"
                        none
                        [
                          (Expr.reference
                            false
                            (Expr.path
                              none
                              (Path.mk false [(PathSegment.mk "r" PathArguments.none)])))])),
                    (Arm.mk
                      []
                      (Pat.tuple
                        [
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
                                [(Pat.ident false false "l" none)])]),
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
                                [(Pat.ident false false "r" none)])])])
                      none
                      (Expr.methodCall
                        (Expr.field
                          (Expr.path none (Path.mk false [(PathSegment.mk "l" PathArguments.none)]))
                          (Member.named "addr"))
                        "cmp"
                        none
                        [
                          (Expr.reference
                            false
                            (Expr.field
                              (Expr.path
                                none
                                (Path.mk false [(PathSegment.mk "r" PathArguments.none)]))
                              (Member.named "addr")))])),
                    (Arm.mk
                      []
                      Pat.wild
                      none
                      (Expr.macro
                        (Macro.mk
                          (Path.mk false [(PathSegment.mk "panic" PathArguments.none)])
                          MacroDelimiter.paren
                          (MacroBody.exprs
                            [(Expr.lit (Lit.str "unmatching metadata in wide pointer comparasion"))]
                            false))))]))
              none),
            (Stmt.expr
              (Expr.methodCall
                (Expr.path none (Path.mk false [(PathSegment.mk "thin_cmp" PathArguments.none)]))
                "then"
                none
                [(Expr.path none (Path.mk false [(PathSegment.mk "meta_cmp" PathArguments.none)]))])
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
          "eval_bin_op"
          (Generics.mk [] [])
          [
            (FnArg.receiver [] true none false none),
            (FnArg.typed
              []
              (Pat.tupleStruct
                none
                (Path.mk
                  false
                  [
                    (PathSegment.mk "BinOp" PathArguments.none),
                    (PathSegment.mk "Rel" PathArguments.none)])
                [(Pat.ident false false "rel_op" none)])
              (Ty.path none (Path.mk false [(PathSegment.mk "BinOp" PathArguments.none)]))),
            (FnArg.typed
              []
              (Pat.tuple [(Pat.ident false false "left" none), (Pat.ident false false "l_ty" none)])
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
                                  (Path.mk false [(PathSegment.mk "M" PathArguments.none)])))]))])),
                  (Ty.path none (Path.mk false [(PathSegment.mk "Type" PathArguments.none)]))])),
            (FnArg.typed
              []
              (Pat.tuple
                [(Pat.ident false false "right" none), (Pat.ident false false "_r_ty" none)])
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
                                  (Path.mk false [(PathSegment.mk "M" PathArguments.none)])))]))])),
                  (Ty.path none (Path.mk false [(PathSegment.mk "Type" PathArguments.none)]))]))]
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
                                (Path.mk false [(PathSegment.mk "Type" PathArguments.none)]))]))]))]))))
        (Block.mk
          [
            (Stmt.letStmt
              []
              (Pat.ident false false "ord" none)
              (some
                (Expr.matchExpr
                  (Expr.tuple
                    [
                      (Expr.path none (Path.mk false [(PathSegment.mk "l_ty" PathArguments.none)])),
                      (Expr.path none (Path.mk false [(PathSegment.mk "left" PathArguments.none)])),
                      (Expr.path none (Path.mk false [(PathSegment.mk "right" PathArguments.none)]))])
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
                                (PathSegment.mk "Type" PathArguments.none),
                                (PathSegment.mk "Int" PathArguments.none)])
                            [Pat.wild]),
                          (Pat.tupleStruct
                            none
                            (Path.mk
                              false
                              [
                                (PathSegment.mk "Value" PathArguments.none),
                                (PathSegment.mk "Int" PathArguments.none)])
                            [(Pat.ident false false "left" none)]),
                          (Pat.tupleStruct
                            none
                            (Path.mk
                              false
                              [
                                (PathSegment.mk "Value" PathArguments.none),
                                (PathSegment.mk "Int" PathArguments.none)])
                            [(Pat.ident false false "right" none)])])
                      none
                      (Expr.block
                        none
                        (Block.mk
                          [
                            (Stmt.expr
                              (Expr.methodCall
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "left" PathArguments.none)]))
                                "cmp"
                                none
                                [
                                  (Expr.reference
                                    false
                                    (Expr.path
                                      none
                                      (Path.mk false [(PathSegment.mk "right" PathArguments.none)])))])
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
                                (PathSegment.mk "Type" PathArguments.none),
                                (PathSegment.mk "Bool" PathArguments.none)])),
                          (Pat.tupleStruct
                            none
                            (Path.mk
                              false
                              [
                                (PathSegment.mk "Value" PathArguments.none),
                                (PathSegment.mk "Bool" PathArguments.none)])
                            [(Pat.ident false false "left" none)]),
                          (Pat.tupleStruct
                            none
                            (Path.mk
                              false
                              [
                                (PathSegment.mk "Value" PathArguments.none),
                                (PathSegment.mk "Bool" PathArguments.none)])
                            [(Pat.ident false false "right" none)])])
                      none
                      (Expr.block
                        none
                        (Block.mk
                          [
                            (Stmt.expr
                              (Expr.methodCall
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "left" PathArguments.none)]))
                                "cmp"
                                none
                                [
                                  (Expr.reference
                                    false
                                    (Expr.path
                                      none
                                      (Path.mk false [(PathSegment.mk "right" PathArguments.none)])))])
                              false)]))),
                    (Arm.mk
                      []
                      (Pat.tuple
                        [
                          (Pat.tupleStruct
                            none
                            (Path.mk
                              false
                              [
                                (PathSegment.mk "Type" PathArguments.none),
                                (PathSegment.mk "Ptr" PathArguments.none)])
                            [Pat.wild]),
                          (Pat.tupleStruct
                            none
                            (Path.mk
                              false
                              [
                                (PathSegment.mk "Value" PathArguments.none),
                                (PathSegment.mk "Ptr" PathArguments.none)])
                            [(Pat.ident false false "left" none)]),
                          (Pat.tupleStruct
                            none
                            (Path.mk
                              false
                              [
                                (PathSegment.mk "Value" PathArguments.none),
                                (PathSegment.mk "Ptr" PathArguments.none)])
                            [(Pat.ident false false "right" none)])])
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
                                    [
                                      (PathSegment.mk "Self" PathArguments.none),
                                      (PathSegment.mk "compare_ptr" PathArguments.none)]))
                                [
                                  (Expr.path
                                    none
                                    (Path.mk false [(PathSegment.mk "left" PathArguments.none)])),
                                  (Expr.path
                                    none
                                    (Path.mk false [(PathSegment.mk "right" PathArguments.none)]))])
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
                                (Lit.str
                                  "relational operator on incomparable type or value-type mismatch"))]
                            false))))]))
              none),
            (Stmt.expr
              (Expr.call
                (Expr.path none (Path.mk false [(PathSegment.mk "ret" PathArguments.none)]))
                [
                  (Expr.call
                    (Expr.path
                      none
                      (Path.mk
                        false
                        [
                          (PathSegment.mk "Self" PathArguments.none),
                          (PathSegment.mk "eval_rel_op" PathArguments.none)]))
                    [
                      (Expr.path
                        none
                        (Path.mk false [(PathSegment.mk "rel_op" PathArguments.none)])),
                      (Expr.path none (Path.mk false [(PathSegment.mk "ord" PathArguments.none)]))])])
              false)]))])

/-- `spec/lang/step/operators.md:381` -/
def impl_Machine__ptr_offset_wrapping : Item :=
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
              " Perform a wrapping offset on the given pointer. (Can never fail.)"))]
        Visibility.inherited
        false
        (Signature.mk
          false
          false
          false
          none
          "ptr_offset_wrapping"
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
              (Pat.ident false false "offset" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "Int" PathArguments.none)])))]
          false
          (some
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
                                (PathSegment.mk "Provenance" PathArguments.none)])))]))]))))
        (Block.mk
          [
            (Stmt.expr
              (Expr.methodCall
                (Expr.path none (Path.mk false [(PathSegment.mk "ptr" PathArguments.none)]))
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
                [(Expr.path none (Path.mk false [(PathSegment.mk "offset" PathArguments.none)]))])
              false)])),
      (ImplItem.fn
        [
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue
              " Perform in-bounds arithmetic on the given pointer. This must not wrap,")),
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue " and the offset must stay in bounds of a single allocation."))]
        Visibility.inherited
        false
        (Signature.mk
          false
          false
          false
          none
          "ptr_offset_inbounds"
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
              (Pat.ident false false "offset" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "Int" PathArguments.none)])))]
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
              (Expr.tryExpr
                (Expr.methodCall
                  (Expr.field
                    (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                    (Member.named "mem"))
                  "signed_dereferenceable"
                  none
                  [
                    (Expr.path none (Path.mk false [(PathSegment.mk "ptr" PathArguments.none)])),
                    (Expr.path none (Path.mk false [(PathSegment.mk "offset" PathArguments.none)]))]))
              true),
            (Stmt.macro
              []
              (Macro.mk
                (Path.mk false [(PathSegment.mk "assert" PathArguments.none)])
                MacroDelimiter.paren
                (MacroBody.exprs
                  [
                    (Expr.methodCall
                      (Expr.path
                        none
                        (Path.mk false [(PathSegment.mk "offset" PathArguments.none)]))
                      "in_bounds"
                      none
                      [
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "Signed" PathArguments.none)])),
                        (Expr.path
                          none
                          (Path.mk
                            false
                            [
                              (PathSegment.mk "M" PathArguments.none),
                              (PathSegment.mk "T" PathArguments.none),
                              (PathSegment.mk "PTR_SIZE" PathArguments.none)]))])]
                  false))
              true),
            (Stmt.macro
              []
              (Macro.mk
                (Path.mk false [(PathSegment.mk "assert" PathArguments.none)])
                MacroDelimiter.paren
                (MacroBody.exprs
                  [
                    (Expr.methodCall
                      (Expr.paren
                        (Expr.binary
                          (Expr.field
                            (Expr.path
                              none
                              (Path.mk false [(PathSegment.mk "ptr" PathArguments.none)]))
                            (Member.named "addr"))
                          BinOp.add
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "offset" PathArguments.none)]))))
                      "in_bounds"
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
                              (PathSegment.mk "M" PathArguments.none),
                              (PathSegment.mk "T" PathArguments.none),
                              (PathSegment.mk "PTR_SIZE" PathArguments.none)]))])]
                  false))
              true),
            (Stmt.expr
              (Expr.call
                (Expr.path none (Path.mk false [(PathSegment.mk "ret" PathArguments.none)]))
                [
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
                              (Path.mk false [(PathSegment.mk "ptr" PathArguments.none)]))
                            (Member.named "addr"))
                          BinOp.add
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "offset" PathArguments.none)]))))]
                    true
                    (some
                      (Expr.path none (Path.mk false [(PathSegment.mk "ptr" PathArguments.none)]))))])
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
          "eval_bin_op"
          (Generics.mk [] [])
          [
            (FnArg.receiver [] true none false none),
            (FnArg.typed
              []
              (Pat.struct
                none
                (Path.mk
                  false
                  [
                    (PathSegment.mk "BinOp" PathArguments.none),
                    (PathSegment.mk "PtrOffset" PathArguments.none)])
                [
                  (FieldPat.mk
                    []
                    (Member.named "inbounds")
                    true
                    (Pat.ident false false "inbounds" none))]
                false)
              (Ty.path none (Path.mk false [(PathSegment.mk "BinOp" PathArguments.none)]))),
            (FnArg.typed
              []
              (Pat.tuple [(Pat.ident false false "left" none), (Pat.ident false false "l_ty" none)])
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
                                  (Path.mk false [(PathSegment.mk "M" PathArguments.none)])))]))])),
                  (Ty.path none (Path.mk false [(PathSegment.mk "Type" PathArguments.none)]))])),
            (FnArg.typed
              []
              (Pat.tuple
                [(Pat.ident false false "right" none), (Pat.ident false false "_r_ty" none)])
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
                                  (Path.mk false [(PathSegment.mk "M" PathArguments.none)])))]))])),
                  (Ty.path none (Path.mk false [(PathSegment.mk "Type" PathArguments.none)]))]))]
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
                                (Path.mk false [(PathSegment.mk "Type" PathArguments.none)]))]))]))]))))
        (Block.mk
          [
            (Stmt.letStmt
              []
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
                        (Pat.ident false false "left" none)),
                      (FieldPat.mk
                        []
                        (Member.named "metadata")
                        false
                        (Pat.ident false false "None" none))]
                    false)])
              (some (Expr.path none (Path.mk false [(PathSegment.mk "left" PathArguments.none)])))
              (some
                (Expr.block
                  none
                  (Block.mk
                    [
                      (Stmt.expr
                        (Expr.macro
                          (Macro.mk
                            (Path.mk false [(PathSegment.mk "panic" PathArguments.none)])
                            MacroDelimiter.paren
                            (MacroBody.exprs
                              [(Expr.lit (Lit.str "non-thin-pointer left input to `PtrOffset`"))]
                              false)))
                        false)])))),
            (Stmt.letStmt
              []
              (Pat.tupleStruct
                none
                (Path.mk
                  false
                  [
                    (PathSegment.mk "Value" PathArguments.none),
                    (PathSegment.mk "Int" PathArguments.none)])
                [(Pat.ident false false "right" none)])
              (some (Expr.path none (Path.mk false [(PathSegment.mk "right" PathArguments.none)])))
              (some
                (Expr.block
                  none
                  (Block.mk
                    [
                      (Stmt.expr
                        (Expr.macro
                          (Macro.mk
                            (Path.mk false [(PathSegment.mk "panic" PathArguments.none)])
                            MacroDelimiter.paren
                            (MacroBody.exprs
                              [(Expr.lit (Lit.str "non-integer right input to `PtrOffset`"))]
                              false)))
                        false)])))),
            (Stmt.letStmt
              []
              (Pat.ident false false "offset_ptr" none)
              (some
                (Expr.ite
                  (Expr.path none (Path.mk false [(PathSegment.mk "inbounds" PathArguments.none)]))
                  (Block.mk
                    [
                      (Stmt.expr
                        (Expr.tryExpr
                          (Expr.methodCall
                            (Expr.path
                              none
                              (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                            "ptr_offset_inbounds"
                            none
                            [
                              (Expr.path
                                none
                                (Path.mk false [(PathSegment.mk "left" PathArguments.none)])),
                              (Expr.path
                                none
                                (Path.mk false [(PathSegment.mk "right" PathArguments.none)]))]))
                        false)])
                  (some
                    (Expr.block
                      none
                      (Block.mk
                        [
                          (Stmt.expr
                            (Expr.methodCall
                              (Expr.path
                                none
                                (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                              "ptr_offset_wrapping"
                              none
                              [
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "left" PathArguments.none)])),
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "right" PathArguments.none)]))])
                            false)])))))
              none),
            (Stmt.expr
              (Expr.call
                (Expr.path none (Path.mk false [(PathSegment.mk "ret" PathArguments.none)]))
                [
                  (Expr.tuple
                    [
                      (Expr.call
                        (Expr.path
                          none
                          (Path.mk
                            false
                            [
                              (PathSegment.mk "Value" PathArguments.none),
                              (PathSegment.mk "Ptr" PathArguments.none)]))
                        [
                          (Expr.methodCall
                            (Expr.path
                              none
                              (Path.mk false [(PathSegment.mk "offset_ptr" PathArguments.none)]))
                            "widen"
                            none
                            [
                              (Expr.path
                                none
                                (Path.mk false [(PathSegment.mk "None" PathArguments.none)]))])]),
                      (Expr.path none (Path.mk false [(PathSegment.mk "l_ty" PathArguments.none)]))])])
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
          "eval_bin_op"
          (Generics.mk [] [])
          [
            (FnArg.receiver [] true none false none),
            (FnArg.typed
              []
              (Pat.struct
                none
                (Path.mk
                  false
                  [
                    (PathSegment.mk "BinOp" PathArguments.none),
                    (PathSegment.mk "PtrOffsetFrom" PathArguments.none)])
                [
                  (FieldPat.mk
                    []
                    (Member.named "inbounds")
                    true
                    (Pat.ident false false "inbounds" none)),
                  (FieldPat.mk
                    []
                    (Member.named "nonneg")
                    true
                    (Pat.ident false false "nonneg" none))]
                false)
              (Ty.path none (Path.mk false [(PathSegment.mk "BinOp" PathArguments.none)]))),
            (FnArg.typed
              []
              (Pat.tuple [(Pat.ident false false "left" none), (Pat.ident false false "l_ty" none)])
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
                                  (Path.mk false [(PathSegment.mk "M" PathArguments.none)])))]))])),
                  (Ty.path none (Path.mk false [(PathSegment.mk "Type" PathArguments.none)]))])),
            (FnArg.typed
              []
              (Pat.tuple
                [(Pat.ident false false "right" none), (Pat.ident false false "_r_ty" none)])
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
                                  (Path.mk false [(PathSegment.mk "M" PathArguments.none)])))]))])),
                  (Ty.path none (Path.mk false [(PathSegment.mk "Type" PathArguments.none)]))]))]
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
                                (Path.mk false [(PathSegment.mk "Type" PathArguments.none)]))]))]))]))))
        (Block.mk
          [
            (Stmt.letStmt
              []
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
                        (Pat.ident false false "left" none)),
                      (FieldPat.mk
                        []
                        (Member.named "metadata")
                        false
                        (Pat.ident false false "None" none))]
                    false)])
              (some (Expr.path none (Path.mk false [(PathSegment.mk "left" PathArguments.none)])))
              (some
                (Expr.block
                  none
                  (Block.mk
                    [
                      (Stmt.expr
                        (Expr.macro
                          (Macro.mk
                            (Path.mk false [(PathSegment.mk "panic" PathArguments.none)])
                            MacroDelimiter.paren
                            (MacroBody.exprs
                              [
                                (Expr.lit
                                  (Lit.str "non-thin-pointer left input to `PtrOffsetFrom`"))]
                              false)))
                        false)])))),
            (Stmt.letStmt
              []
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
                        (Pat.ident false false "right" none)),
                      (FieldPat.mk
                        []
                        (Member.named "metadata")
                        false
                        (Pat.ident false false "None" none))]
                    false)])
              (some (Expr.path none (Path.mk false [(PathSegment.mk "right" PathArguments.none)])))
              (some
                (Expr.block
                  none
                  (Block.mk
                    [
                      (Stmt.expr
                        (Expr.macro
                          (Macro.mk
                            (Path.mk false [(PathSegment.mk "panic" PathArguments.none)])
                            MacroDelimiter.paren
                            (MacroBody.exprs
                              [
                                (Expr.lit
                                  (Lit.str "non-thin-pointer right input to `PtrOffsetFrom`"))]
                              false)))
                        false)])))),
            (Stmt.letStmt
              []
              (Pat.ident false false "distance" none)
              (some
                (Expr.binary
                  (Expr.field
                    (Expr.path none (Path.mk false [(PathSegment.mk "left" PathArguments.none)]))
                    (Member.named "addr"))
                  BinOp.sub
                  (Expr.field
                    (Expr.path none (Path.mk false [(PathSegment.mk "right" PathArguments.none)]))
                    (Member.named "addr"))))
              none),
            (Stmt.letStmt
              []
              (Pat.ident false false "distance" none)
              (some
                (Expr.ite
                  (Expr.path none (Path.mk false [(PathSegment.mk "inbounds" PathArguments.none)]))
                  (Block.mk
                    [
                      (Stmt.expr
                        (Expr.tryExpr
                          (Expr.methodCall
                            (Expr.field
                              (Expr.path
                                none
                                (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                              (Member.named "mem"))
                            "signed_dereferenceable"
                            none
                            [
                              (Expr.path
                                none
                                (Path.mk false [(PathSegment.mk "left" PathArguments.none)])),
                              (Expr.unary
                                UnOp.neg
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "distance" PathArguments.none)])))]))
                        true),
                      (Stmt.expr
                        (Expr.tryExpr
                          (Expr.methodCall
                            (Expr.field
                              (Expr.path
                                none
                                (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                              (Member.named "mem"))
                            "signed_dereferenceable"
                            none
                            [
                              (Expr.path
                                none
                                (Path.mk false [(PathSegment.mk "right" PathArguments.none)])),
                              (Expr.path
                                none
                                (Path.mk false [(PathSegment.mk "distance" PathArguments.none)]))]))
                        true),
                      (Stmt.expr
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "distance" PathArguments.none)]))
                        false)])
                  (some
                    (Expr.block
                      none
                      (Block.mk
                        [
                          (Stmt.expr
                            (Expr.methodCall
                              (Expr.path
                                none
                                (Path.mk false [(PathSegment.mk "distance" PathArguments.none)]))
                              "bring_in_bounds"
                              none
                              [
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "Signed" PathArguments.none)])),
                                (Expr.path
                                  none
                                  (Path.mk
                                    false
                                    [
                                      (PathSegment.mk "M" PathArguments.none),
                                      (PathSegment.mk "T" PathArguments.none),
                                      (PathSegment.mk "PTR_SIZE" PathArguments.none)]))])
                            false)])))))
              none),
            (Stmt.expr
              (Expr.ite
                (Expr.binary
                  (Expr.path none (Path.mk false [(PathSegment.mk "nonneg" PathArguments.none)]))
                  BinOp.and
                  (Expr.binary
                    (Expr.path
                      none
                      (Path.mk false [(PathSegment.mk "distance" PathArguments.none)]))
                    BinOp.lt
                    (Expr.path
                      none
                      (Path.mk
                        false
                        [
                          (PathSegment.mk "Int" PathArguments.none),
                          (PathSegment.mk "ZERO" PathArguments.none)]))))
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
                              (Lit.str "PtrOffsetFrom: negative result with `nonneg` flag set"))]
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
                  (Path.mk false [(PathSegment.mk "IntType" PathArguments.none)])
                  [
                    (FieldValue.mk
                      []
                      (Member.named "signed")
                      false
                      (Expr.path
                        none
                        (Path.mk false [(PathSegment.mk "Signed" PathArguments.none)]))),
                    (FieldValue.mk
                      []
                      (Member.named "size")
                      false
                      (Expr.path
                        none
                        (Path.mk
                          false
                          [
                            (PathSegment.mk "M" PathArguments.none),
                            (PathSegment.mk "T" PathArguments.none),
                            (PathSegment.mk "PTR_SIZE" PathArguments.none)])))]
                  false
                  none))
              none),
            (Stmt.expr
              (Expr.call
                (Expr.path none (Path.mk false [(PathSegment.mk "ret" PathArguments.none)]))
                [
                  (Expr.tuple
                    [
                      (Expr.call
                        (Expr.path
                          none
                          (Path.mk
                            false
                            [
                              (PathSegment.mk "Value" PathArguments.none),
                              (PathSegment.mk "Int" PathArguments.none)]))
                        [
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "distance" PathArguments.none)]))]),
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
                            (Path.mk false [(PathSegment.mk "isize_int" PathArguments.none)]))])])])
              false)]))])

/-- `spec/lang/step/operators.md:458` -/
def impl_Machine__eval_bin_op_1 : Item :=
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
          "eval_bin_op"
          (Generics.mk [] [])
          [
            (FnArg.receiver [] true none false none),
            (FnArg.typed
              []
              (Pat.tupleStruct
                none
                (Path.mk
                  false
                  [
                    (PathSegment.mk "BinOp" PathArguments.none),
                    (PathSegment.mk "ConstructWidePointer" PathArguments.none)])
                [(Pat.ident false false "ptr_ty" none)])
              (Ty.path none (Path.mk false [(PathSegment.mk "BinOp" PathArguments.none)]))),
            (FnArg.typed
              []
              (Pat.tuple [(Pat.ident false false "left" none), (Pat.ident false false "l_ty" none)])
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
                                  (Path.mk false [(PathSegment.mk "M" PathArguments.none)])))]))])),
                  (Ty.path none (Path.mk false [(PathSegment.mk "Type" PathArguments.none)]))])),
            (FnArg.typed
              []
              (Pat.tuple
                [(Pat.ident false false "right" none), (Pat.ident false false "_r_ty" none)])
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
                                  (Path.mk false [(PathSegment.mk "M" PathArguments.none)])))]))])),
                  (Ty.path none (Path.mk false [(PathSegment.mk "Type" PathArguments.none)]))]))]
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
                                (Path.mk false [(PathSegment.mk "Type" PathArguments.none)]))]))]))]))))
        (Block.mk
          [
            (Stmt.letStmt
              []
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
                        true
                        (Pat.ident false false "thin_pointer" none)),
                      (FieldPat.mk
                        []
                        (Member.named "metadata")
                        false
                        (Pat.ident false false "None" none))]
                    false)])
              (some (Expr.path none (Path.mk false [(PathSegment.mk "left" PathArguments.none)])))
              (some
                (Expr.block
                  none
                  (Block.mk
                    [
                      (Stmt.expr
                        (Expr.macro
                          (Macro.mk
                            (Path.mk false [(PathSegment.mk "panic" PathArguments.none)])
                            MacroDelimiter.paren
                            (MacroBody.exprs
                              [
                                (Expr.lit
                                  (Lit.str "non-thin-pointer left input to `ConstructWidePointer`"))]
                              false)))
                        false)])))),
            (Stmt.letStmt
              []
              (Pat.ident false false "metadata" none)
              (some
                (Expr.methodCall
                  (Expr.methodCall
                    (Expr.path none (Path.mk false [(PathSegment.mk "ptr_ty" PathArguments.none)]))
                    "meta_kind"
                    none
                    [])
                  "decode_value"
                  (some
                    [
                      (GenericArgument.type
                        (Ty.path none (Path.mk false [(PathSegment.mk "M" PathArguments.none)])))])
                  [(Expr.path none (Path.mk false [(PathSegment.mk "right" PathArguments.none)]))]))
              none),
            (Stmt.letStmt
              []
              (Pat.ident false false "wide_ptr" none)
              (some
                (Expr.call
                  (Expr.path
                    none
                    (Path.mk
                      false
                      [
                        (PathSegment.mk "Value" PathArguments.none),
                        (PathSegment.mk "Ptr" PathArguments.none)]))
                  [
                    (Expr.struct
                      none
                      (Path.mk false [(PathSegment.mk "Pointer" PathArguments.none)])
                      [
                        (FieldValue.mk
                          []
                          (Member.named "thin_pointer")
                          true
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "thin_pointer" PathArguments.none)]))),
                        (FieldValue.mk
                          []
                          (Member.named "metadata")
                          true
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "metadata" PathArguments.none)])))]
                      false
                      none)]))
              none),
            (Stmt.expr
              (Expr.tryExpr
                (Expr.methodCall
                  (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                  "check_value"
                  none
                  [
                    (Expr.path
                      none
                      (Path.mk false [(PathSegment.mk "wide_ptr" PathArguments.none)])),
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
                          (Path.mk false [(PathSegment.mk "ptr_ty" PathArguments.none)]))])]))
              true),
            (Stmt.expr
              (Expr.call
                (Expr.path none (Path.mk false [(PathSegment.mk "ret" PathArguments.none)]))
                [
                  (Expr.tuple
                    [
                      (Expr.path
                        none
                        (Path.mk false [(PathSegment.mk "wide_ptr" PathArguments.none)])),
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
                            (Path.mk false [(PathSegment.mk "ptr_ty" PathArguments.none)]))])])])
              false)]))])

/-- All items of `spec/lang/step/operators.md`, in source order, with provenance. -/
def items : List SourceItem :=
  [
    (SourceItem.mk
      "impl_Machine__eval_un_op_0"
      8
      "bc75edbbf21e7bb11a120a95abc8a509426c9b7cb4c30a01bb944e71406609fe"
      impl_Machine__eval_un_op_0),
    (SourceItem.mk
      "impl_Machine__eval_int_un_op"
      17
      "d77850d14b0077d0b31ad48e5c3d50802b1d00c71cdc81df3cf0fdca386ab4bb"
      impl_Machine__eval_int_un_op),
    (SourceItem.mk
      "impl_Machine__eval_count_ones"
      58
      "c19ca4f371134183b42adeb305d0bb2e682898ca36ae70e8f31f3f1cbeb95244"
      impl_Machine__eval_count_ones),
    (SourceItem.mk
      "impl_Machine__eval_cast_op"
      76
      "acaf7b511f4694d2d02cd11ee8fe9dd965ef3171e58213e3abce23147f031deb"
      impl_Machine__eval_cast_op),
    (SourceItem.mk
      "impl_Machine__eval_un_op_1"
      105
      "4b04a40c487570eb8d2bf843a7d72369d19277fcf1f670de0b07c84a42557da0"
      impl_Machine__eval_un_op_1),
    (SourceItem.mk
      "impl_Machine__eval_un_op_2"
      130
      "2aaff5e02384e1fe1477d29115b70b5d83b0a62013dd8d4305753bf376065d5c"
      impl_Machine__eval_un_op_2),
    (SourceItem.mk
      "impl_Machine__eval_un_op_3"
      152
      "7a1dba14110e7f3a40edb1a4f6ba6a24668df96ce4223f8ce97ae7ac83e4176e"
      impl_Machine__eval_un_op_3),
    (SourceItem.mk
      "impl_Machine__eval_bin_op_0"
      171
      "babc56bb30b8c282e04b3b495b8edf1d8d812b4a8a35bd0d9c0cfc3e0c0c8f33"
      impl_Machine__eval_bin_op_0),
    (SourceItem.mk
      "impl_Machine__eval_int_bin_op"
      186
      "8ceef5b3ae1db7826d008630b6f69c068d3689399431e236d52334cc2515cbef"
      impl_Machine__eval_int_bin_op),
    (SourceItem.mk
      "impl_Machine__eval_rel_op"
      320
      "3cab9c6e85014ab92350e36f11c22d7e9c7a319170cf825acdf63ed51942da1e"
      impl_Machine__eval_rel_op),
    (SourceItem.mk
      "impl_Machine__ptr_offset_wrapping"
      381
      "e2b41199248cabea46f96dab16c19801c6bac607c726b7b3e57efc754de745d8"
      impl_Machine__ptr_offset_wrapping),
    (SourceItem.mk
      "impl_Machine__eval_bin_op_1"
      458
      "65690b62ca061793625fe0f0607e62e74ffff7052f586b72e485806673c06dbf"
      impl_Machine__eval_bin_op_1)]

end MiniRustSpec.Gen.Items.Lang.Step.Operators
