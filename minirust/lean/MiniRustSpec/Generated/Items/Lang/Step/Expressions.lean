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
`spec/lang/step/expressions.md` (commit `d821c6e3`), one Lean definition per item, in source order.
-/

import MiniRustSpec.Meta.Syntax

set_option maxRecDepth 100000

namespace MiniRustSpec.Gen.Items.Lang.Step.Expressions

open MiniRustSpec.Syntax

/-- Path of the upstream file these items were extracted from. -/
def sourceFile : String := "spec/lang/step/expressions.md"

/-- SHA-256 of the upstream file. -/
def sourceSha256 : String := "cfa01e5f8d30eae252e36dbd1ecca51365f5cc02e90fe73b1b706fc3747cb6cb"

/-- `spec/lang/step/expressions.md:17` -/
def impl_Machine__eval_value_0 : Item :=
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
            (AttrMeta.nameValue " Evaluate a well-formed value expression to a value.")),
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue " The result value will always be well-formed for the given type.")),
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue
              " Calling this with a non-well-formed expression or it returning a non-well-formed value is a spec bug.")),
          (Attr.mk true "specr::argmatch" (AttrMeta.list [(MetaItem.mk "val" AttrMeta.path)]))]
        Visibility.inherited
        false
        (Signature.mk
          false
          false
          false
          none
          "eval_value"
          (Generics.mk [] [])
          [
            (FnArg.receiver [] true none true none),
            (FnArg.typed
              []
              (Pat.ident false false "val" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "ValueExpr" PathArguments.none)])))]
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

/-- `spec/lang/step/expressions.md:32` -/
def impl_Machine__eval_constant : Item :=
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
            (AttrMeta.nameValue " converts `Constant` to their `Value` counterpart."))]
        Visibility.inherited
        false
        (Signature.mk
          false
          false
          false
          none
          "eval_constant"
          (Generics.mk [] [])
          [
            (FnArg.receiver [] true none true none),
            (FnArg.typed
              []
              (Pat.ident false false "constant" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "Constant" PathArguments.none)])))]
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
                                  "Value"
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
              (Expr.call
                (Expr.path none (Path.mk false [(PathSegment.mk "ret" PathArguments.none)]))
                [
                  (Expr.matchExpr
                    (Expr.path
                      none
                      (Path.mk false [(PathSegment.mk "constant" PathArguments.none)]))
                    [
                      (Arm.mk
                        []
                        (Pat.tupleStruct
                          none
                          (Path.mk
                            false
                            [
                              (PathSegment.mk "Constant" PathArguments.none),
                              (PathSegment.mk "Int" PathArguments.none)])
                          [(Pat.ident false false "i" none)])
                        none
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
                              (Path.mk false [(PathSegment.mk "i" PathArguments.none)]))])),
                      (Arm.mk
                        []
                        (Pat.tupleStruct
                          none
                          (Path.mk
                            false
                            [
                              (PathSegment.mk "Constant" PathArguments.none),
                              (PathSegment.mk "Bool" PathArguments.none)])
                          [(Pat.ident false false "b" none)])
                        none
                        (Expr.call
                          (Expr.path
                            none
                            (Path.mk
                              false
                              [
                                (PathSegment.mk "Value" PathArguments.none),
                                (PathSegment.mk "Bool" PathArguments.none)]))
                          [
                            (Expr.path
                              none
                              (Path.mk false [(PathSegment.mk "b" PathArguments.none)]))])),
                      (Arm.mk
                        []
                        (Pat.tupleStruct
                          none
                          (Path.mk
                            false
                            [
                              (PathSegment.mk "Constant" PathArguments.none),
                              (PathSegment.mk "GlobalPointer" PathArguments.none)])
                          [(Pat.ident false false "relocation" none)])
                        none
                        (Expr.block
                          none
                          (Block.mk
                            [
                              (Stmt.letStmt
                                []
                                (Pat.ident false false "ptr" none)
                                (some
                                  (Expr.methodCall
                                    (Expr.index
                                      (Expr.field
                                        (Expr.path
                                          none
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "self" PathArguments.none)]))
                                        (Member.named "global_ptrs"))
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
                              (Stmt.expr
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
                                        (Path.mk false [(PathSegment.mk "ptr" PathArguments.none)]))
                                      "widen"
                                      none
                                      [
                                        (Expr.path
                                          none
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "None" PathArguments.none)]))])])
                                false)]))),
                      (Arm.mk
                        []
                        (Pat.tupleStruct
                          none
                          (Path.mk
                            false
                            [
                              (PathSegment.mk "Constant" PathArguments.none),
                              (PathSegment.mk "FnPointer" PathArguments.none)])
                          [(Pat.ident false false "fn_name" none)])
                        none
                        (Expr.block
                          none
                          (Block.mk
                            [
                              (Stmt.letStmt
                                []
                                (Pat.ident false false "ptr" none)
                                (some
                                  (Expr.index
                                    (Expr.field
                                      (Expr.path
                                        none
                                        (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                                      (Member.named "fn_ptrs"))
                                    (Expr.path
                                      none
                                      (Path.mk
                                        false
                                        [(PathSegment.mk "fn_name" PathArguments.none)]))))
                                none),
                              (Stmt.expr
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
                                        (Path.mk false [(PathSegment.mk "ptr" PathArguments.none)]))
                                      "widen"
                                      none
                                      [
                                        (Expr.path
                                          none
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "None" PathArguments.none)]))])])
                                false)]))),
                      (Arm.mk
                        []
                        (Pat.tupleStruct
                          none
                          (Path.mk
                            false
                            [
                              (PathSegment.mk "Constant" PathArguments.none),
                              (PathSegment.mk "VTablePointer" PathArguments.none)])
                          [(Pat.ident false false "vtable_name" none)])
                        none
                        (Expr.block
                          none
                          (Block.mk
                            [
                              (Stmt.letStmt
                                []
                                (Pat.ident false false "ptr" none)
                                (some
                                  (Expr.index
                                    (Expr.field
                                      (Expr.path
                                        none
                                        (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                                      (Member.named "vtable_ptrs"))
                                    (Expr.path
                                      none
                                      (Path.mk
                                        false
                                        [(PathSegment.mk "vtable_name" PathArguments.none)]))))
                                none),
                              (Stmt.expr
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
                                        (Path.mk false [(PathSegment.mk "ptr" PathArguments.none)]))
                                      "widen"
                                      none
                                      [
                                        (Expr.path
                                          none
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "None" PathArguments.none)]))])])
                                false)]))),
                      (Arm.mk
                        []
                        (Pat.tupleStruct
                          none
                          (Path.mk
                            false
                            [
                              (PathSegment.mk "Constant" PathArguments.none),
                              (PathSegment.mk "PointerWithoutProvenance" PathArguments.none)])
                          [(Pat.ident false false "addr" none)])
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
                                        (PathSegment.mk "Value" PathArguments.none),
                                        (PathSegment.mk "Ptr" PathArguments.none)]))
                                  [
                                    (Expr.methodCall
                                      (Expr.struct
                                        none
                                        (Path.mk
                                          false
                                          [(PathSegment.mk "ThinPointer" PathArguments.none)])
                                        [
                                          (FieldValue.mk
                                            []
                                            (Member.named "addr")
                                            true
                                            (Expr.path
                                              none
                                              (Path.mk
                                                false
                                                [(PathSegment.mk "addr" PathArguments.none)]))),
                                          (FieldValue.mk
                                            []
                                            (Member.named "provenance")
                                            false
                                            (Expr.path
                                              none
                                              (Path.mk
                                                false
                                                [(PathSegment.mk "None" PathArguments.none)])))]
                                        false
                                        none)
                                      "widen"
                                      none
                                      [
                                        (Expr.path
                                          none
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "None" PathArguments.none)]))])])
                                false)])))])])
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
          "eval_value"
          (Generics.mk [] [])
          [
            (FnArg.receiver [] true none true none),
            (FnArg.typed
              []
              (Pat.tupleStruct
                none
                (Path.mk
                  false
                  [
                    (PathSegment.mk "ValueExpr" PathArguments.none),
                    (PathSegment.mk "Constant" PathArguments.none)])
                [(Pat.ident false false "constant" none), (Pat.ident false false "ty" none)])
              (Ty.path none (Path.mk false [(PathSegment.mk "ValueExpr" PathArguments.none)])))]
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
                  (Expr.tuple
                    [
                      (Expr.tryExpr
                        (Expr.methodCall
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                          "eval_constant"
                          none
                          [
                            (Expr.path
                              none
                              (Path.mk false [(PathSegment.mk "constant" PathArguments.none)]))])),
                      (Expr.path none (Path.mk false [(PathSegment.mk "ty" PathArguments.none)]))])])
              false)]))])

/-- `spec/lang/step/expressions.md:68` -/
def impl_Machine__eval_value_1 : Item :=
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
          "eval_value"
          (Generics.mk [] [])
          [
            (FnArg.receiver [] true none true none),
            (FnArg.typed
              []
              (Pat.tupleStruct
                none
                (Path.mk
                  false
                  [
                    (PathSegment.mk "ValueExpr" PathArguments.none),
                    (PathSegment.mk "Tuple" PathArguments.none)])
                [(Pat.ident false false "exprs" none), (Pat.ident false false "ty" none)])
              (Ty.path none (Path.mk false [(PathSegment.mk "ValueExpr" PathArguments.none)])))]
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
              (Pat.ident false false "vals" none)
              (some
                (Expr.methodCall
                  (Expr.tryExpr
                    (Expr.methodCall
                      (Expr.path none (Path.mk false [(PathSegment.mk "exprs" PathArguments.none)]))
                      "try_map"
                      none
                      [
                        (Expr.closure
                          false
                          [(Pat.ident false false "e" none)]
                          none
                          (Expr.methodCall
                            (Expr.path
                              none
                              (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                            "eval_value"
                            none
                            [
                              (Expr.path
                                none
                                (Path.mk false [(PathSegment.mk "e" PathArguments.none)]))]))]))
                  "map"
                  none
                  [
                    (Expr.closure
                      false
                      [(Pat.ident false false "e" none)]
                      none
                      (Expr.field
                        (Expr.path none (Path.mk false [(PathSegment.mk "e" PathArguments.none)]))
                        (Member.unnamed 0)))]))
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
                              (PathSegment.mk "Tuple" PathArguments.none)]))
                        [
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "vals" PathArguments.none)]))]),
                      (Expr.path none (Path.mk false [(PathSegment.mk "ty" PathArguments.none)]))])])
              false)]))])

/-- `spec/lang/step/expressions.md:79` -/
def impl_Machine__eval_value_2 : Item :=
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
          "eval_value"
          (Generics.mk [] [])
          [
            (FnArg.receiver [] true none true none),
            (FnArg.typed
              []
              (Pat.struct
                none
                (Path.mk
                  false
                  [
                    (PathSegment.mk "ValueExpr" PathArguments.none),
                    (PathSegment.mk "Union" PathArguments.none)])
                [
                  (FieldPat.mk [] (Member.named "field") true (Pat.ident false false "field" none)),
                  (FieldPat.mk [] (Member.named "expr") true (Pat.ident false false "expr" none)),
                  (FieldPat.mk
                    []
                    (Member.named "union_ty")
                    true
                    (Pat.ident false false "union_ty" none))]
                false)
              (Ty.path none (Path.mk false [(PathSegment.mk "ValueExpr" PathArguments.none)])))]
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
                    (Pat.ident false false "fields" none)),
                  (FieldPat.mk [] (Member.named "size") true (Pat.ident false false "size" none))]
                true)
              (some
                (Expr.path none (Path.mk false [(PathSegment.mk "union_ty" PathArguments.none)])))
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
                              [(Expr.lit (Lit.str "ValueExpr::Union requires union type"))]
                              false)))
                        false)])))),
            (Stmt.letStmt
              []
              (Pat.tuple
                [(Pat.ident false false "offset" none), (Pat.ident false false "expr_ty" none)])
              (some
                (Expr.index
                  (Expr.path none (Path.mk false [(PathSegment.mk "fields" PathArguments.none)]))
                  (Expr.path none (Path.mk false [(PathSegment.mk "field" PathArguments.none)]))))
              none),
            (Stmt.letStmt
              []
              (Pat.ident false true "data" none)
              (some
                (Expr.macro
                  (Macro.mk
                    (Path.mk false [(PathSegment.mk "list" PathArguments.none)])
                    MacroDelimiter.bracket
                    (MacroBody.repeatList
                      (Expr.path
                        none
                        (Path.mk
                          false
                          [
                            (PathSegment.mk "AbstractByte" PathArguments.none),
                            (PathSegment.mk "Uninit" PathArguments.none)]))
                      (Expr.methodCall
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "size" PathArguments.none)]))
                        "bytes"
                        none
                        [])))))
              none),
            (Stmt.letStmt
              []
              (Pat.tuple [(Pat.ident false false "val" none), Pat.wild])
              (some
                (Expr.tryExpr
                  (Expr.methodCall
                    (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                    "eval_value"
                    none
                    [(Expr.path none (Path.mk false [(PathSegment.mk "expr" PathArguments.none)]))])))
              none),
            (Stmt.expr
              (Expr.methodCall
                (Expr.path none (Path.mk false [(PathSegment.mk "data" PathArguments.none)]))
                "write_subslice_at_index"
                none
                [
                  (Expr.methodCall
                    (Expr.path none (Path.mk false [(PathSegment.mk "offset" PathArguments.none)]))
                    "bytes"
                    none
                    []),
                  (Expr.methodCall
                    (Expr.path none (Path.mk false [(PathSegment.mk "expr_ty" PathArguments.none)]))
                    "encode"
                    (some
                      [
                        (GenericArgument.type
                          (Ty.path none (Path.mk false [(PathSegment.mk "M" PathArguments.none)])))])
                    [(Expr.path none (Path.mk false [(PathSegment.mk "val" PathArguments.none)]))])])
              true),
            (Stmt.expr
              (Expr.call
                (Expr.path none (Path.mk false [(PathSegment.mk "ret" PathArguments.none)]))
                [
                  (Expr.tuple
                    [
                      (Expr.methodCall
                        (Expr.methodCall
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "union_ty" PathArguments.none)]))
                          "decode"
                          none
                          [
                            (Expr.path
                              none
                              (Path.mk false [(PathSegment.mk "data" PathArguments.none)]))])
                        "unwrap"
                        none
                        []),
                      (Expr.path
                        none
                        (Path.mk false [(PathSegment.mk "union_ty" PathArguments.none)]))])])
              false)]))])

/-- `spec/lang/step/expressions.md:94` -/
def impl_Machine__eval_value_3 : Item :=
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
          "eval_value"
          (Generics.mk [] [])
          [
            (FnArg.receiver [] true none true none),
            (FnArg.typed
              []
              (Pat.struct
                none
                (Path.mk
                  false
                  [
                    (PathSegment.mk "ValueExpr" PathArguments.none),
                    (PathSegment.mk "Variant" PathArguments.none)])
                [
                  (FieldPat.mk
                    []
                    (Member.named "enum_ty")
                    true
                    (Pat.ident false false "enum_ty" none)),
                  (FieldPat.mk
                    []
                    (Member.named "discriminant")
                    true
                    (Pat.ident false false "discriminant" none)),
                  (FieldPat.mk [] (Member.named "data") true (Pat.ident false false "data" none))]
                false)
              (Ty.path none (Path.mk false [(PathSegment.mk "ValueExpr" PathArguments.none)])))]
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
                  (Expr.tuple
                    [
                      (Expr.struct
                        none
                        (Path.mk
                          false
                          [
                            (PathSegment.mk "Value" PathArguments.none),
                            (PathSegment.mk "Variant" PathArguments.none)])
                        [
                          (FieldValue.mk
                            []
                            (Member.named "discriminant")
                            true
                            (Expr.path
                              none
                              (Path.mk false [(PathSegment.mk "discriminant" PathArguments.none)]))),
                          (FieldValue.mk
                            []
                            (Member.named "data")
                            false
                            (Expr.field
                              (Expr.tryExpr
                                (Expr.methodCall
                                  (Expr.path
                                    none
                                    (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                                  "eval_value"
                                  none
                                  [
                                    (Expr.path
                                      none
                                      (Path.mk false [(PathSegment.mk "data" PathArguments.none)]))]))
                              (Member.unnamed 0)))]
                        false
                        none),
                      (Expr.path
                        none
                        (Path.mk false [(PathSegment.mk "enum_ty" PathArguments.none)]))])])
              false)]))])

/-- `spec/lang/step/expressions.md:105` -/
def impl_Machine__eval_value_4 : Item :=
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
          "eval_value"
          (Generics.mk [] [])
          [
            (FnArg.receiver [] true none true none),
            (FnArg.typed
              []
              (Pat.struct
                none
                (Path.mk
                  false
                  [
                    (PathSegment.mk "ValueExpr" PathArguments.none),
                    (PathSegment.mk "GetDiscriminant" PathArguments.none)])
                [(FieldPat.mk [] (Member.named "place") true (Pat.ident false false "place" none))]
                false)
              (Ty.path none (Path.mk false [(PathSegment.mk "ValueExpr" PathArguments.none)])))]
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
              (Pat.tuple [(Pat.ident false false "place" none), (Pat.ident false false "ty" none)])
              (some
                (Expr.tryExpr
                  (Expr.methodCall
                    (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                    "eval_place"
                    none
                    [(Expr.path none (Path.mk false [(PathSegment.mk "place" PathArguments.none)]))])))
              none),
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
                    (Member.named "discriminator")
                    true
                    (Pat.ident false false "discriminator" none)),
                  (FieldPat.mk
                    []
                    (Member.named "discriminant_ty")
                    true
                    (Pat.ident false false "discriminant_ty" none))]
                true)
              (some (Expr.path none (Path.mk false [(PathSegment.mk "ty" PathArguments.none)])))
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
                            [(Expr.lit (Lit.str "ValueExpr::GetDiscriminant requires enum type"))]
                            false))
                        true)])))),
            (Stmt.expr
              (Expr.ite
                (Expr.unary
                  UnOp.not
                  (Expr.field
                    (Expr.path none (Path.mk false [(PathSegment.mk "place" PathArguments.none)]))
                    (Member.named "aligned")))
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
                                "Getting the discriminant of a place based on a misaligned pointer."))]
                          false))
                      true)])
                none)
              false),
            (Stmt.letStmt
              []
              (Pat.ident false false "accessor" none)
              (some
                (Expr.closure
                  false
                  [
                    (Pat.typed
                      (Pat.ident false false "idx" none)
                      (Ty.path none (Path.mk false [(PathSegment.mk "Offset" PathArguments.none)]))),
                    (Pat.typed
                      (Pat.ident false false "size" none)
                      (Ty.path none (Path.mk false [(PathSegment.mk "Size" PathArguments.none)])))]
                  none
                  (Expr.block
                    none
                    (Block.mk
                      [
                        (Stmt.letStmt
                          []
                          (Pat.ident false false "ptr" none)
                          (some
                            (Expr.tryExpr
                              (Expr.methodCall
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                                "ptr_offset_inbounds"
                                none
                                [
                                  (Expr.field
                                    (Expr.field
                                      (Expr.path
                                        none
                                        (Path.mk
                                          false
                                          [(PathSegment.mk "place" PathArguments.none)]))
                                      (Member.named "ptr"))
                                    (Member.named "thin_pointer")),
                                  (Expr.methodCall
                                    (Expr.path
                                      none
                                      (Path.mk false [(PathSegment.mk "idx" PathArguments.none)]))
                                    "bytes"
                                    none
                                    [])])))
                          none),
                        (Stmt.expr
                          (Expr.methodCall
                            (Expr.field
                              (Expr.path
                                none
                                (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                              (Member.named "mem"))
                            "load"
                            none
                            [
                              (Expr.path
                                none
                                (Path.mk false [(PathSegment.mk "ptr" PathArguments.none)])),
                              (Expr.path
                                none
                                (Path.mk false [(PathSegment.mk "size" PathArguments.none)])),
                              (Expr.path
                                none
                                (Path.mk
                                  false
                                  [
                                    (PathSegment.mk "Align" PathArguments.none),
                                    (PathSegment.mk "ONE" PathArguments.none)])),
                              (Expr.path
                                none
                                (Path.mk
                                  false
                                  [
                                    (PathSegment.mk "Atomicity" PathArguments.none),
                                    (PathSegment.mk "None" PathArguments.none)]))])
                          false)]))))
              none),
            (Stmt.letStmt
              []
              (Pat.tupleStruct
                none
                (Path.mk false [(PathSegment.mk "Some" PathArguments.none)])
                [(Pat.ident false false "discriminant" none)])
              (some
                (Expr.tryExpr
                  (Expr.call
                    (Expr.path
                      none
                      (Path.mk
                        false
                        [
                          (PathSegment.mk
                            "decode_discriminant"
                            (PathArguments.angleBracketed
                              true
                              [
                                (GenericArgument.type
                                  (Ty.path
                                    none
                                    (Path.mk false [(PathSegment.mk "M" PathArguments.none)])))]))]))
                    [
                      (Expr.path
                        none
                        (Path.mk false [(PathSegment.mk "accessor" PathArguments.none)])),
                      (Expr.path
                        none
                        (Path.mk false [(PathSegment.mk "discriminator" PathArguments.none)]))])))
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
                                  "ValueExpr::GetDiscriminant encountered invalid discriminant."))]
                            false))
                        true)])))),
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
                            (Path.mk false [(PathSegment.mk "discriminant" PathArguments.none)]))]),
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
                            (Path.mk false [(PathSegment.mk "discriminant_ty" PathArguments.none)]))])])])
              false)]))])

/-- `spec/lang/step/expressions.md:137` -/
def impl_Machine__place_load : Item :=
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
          "place_load"
          (Generics.mk [] [])
          [
            (FnArg.receiver [] true none true none),
            (FnArg.typed
              []
              (Pat.ident false false "place" none)
              (Ty.path
                none
                (Path.mk
                  false
                  [
                    (PathSegment.mk
                      "Place"
                      (PathArguments.angleBracketed
                        false
                        [
                          (GenericArgument.type
                            (Ty.path none (Path.mk false [(PathSegment.mk "M" PathArguments.none)])))]))]))),
            (FnArg.typed
              []
              (Pat.ident false false "ty" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "Type" PathArguments.none)])))]
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
                                  "Value"
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
              (Expr.ite
                (Expr.unary
                  UnOp.not
                  (Expr.field
                    (Expr.path none (Path.mk false [(PathSegment.mk "place" PathArguments.none)]))
                    (Member.named "aligned")))
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
                              (Lit.str "loading from a place based on a misaligned pointer"))]
                          false))
                      true)])
                none)
              false),
            (Stmt.expr
              (Expr.call
                (Expr.path none (Path.mk false [(PathSegment.mk "ret" PathArguments.none)]))
                [
                  (Expr.tryExpr
                    (Expr.methodCall
                      (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                      "typed_load"
                      none
                      [
                        (Expr.field
                          (Expr.field
                            (Expr.path
                              none
                              (Path.mk false [(PathSegment.mk "place" PathArguments.none)]))
                            (Member.named "ptr"))
                          (Member.named "thin_pointer")),
                        (Expr.path none (Path.mk false [(PathSegment.mk "ty" PathArguments.none)])),
                        (Expr.path
                          none
                          (Path.mk
                            false
                            [
                              (PathSegment.mk "Align" PathArguments.none),
                              (PathSegment.mk "ONE" PathArguments.none)])),
                        (Expr.path
                          none
                          (Path.mk
                            false
                            [
                              (PathSegment.mk "Atomicity" PathArguments.none),
                              (PathSegment.mk "None" PathArguments.none)]))]))])
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
          "eval_value"
          (Generics.mk [] [])
          [
            (FnArg.receiver [] true none true none),
            (FnArg.typed
              []
              (Pat.struct
                none
                (Path.mk
                  false
                  [
                    (PathSegment.mk "ValueExpr" PathArguments.none),
                    (PathSegment.mk "Load" PathArguments.none)])
                [
                  (FieldPat.mk
                    []
                    (Member.named "source")
                    true
                    (Pat.ident false false "source" none))]
                false)
              (Ty.path none (Path.mk false [(PathSegment.mk "ValueExpr" PathArguments.none)])))]
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
              (Pat.tuple [(Pat.ident false false "place" none), (Pat.ident false false "ty" none)])
              (some
                (Expr.tryExpr
                  (Expr.methodCall
                    (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                    "eval_place"
                    none
                    [
                      (Expr.path
                        none
                        (Path.mk false [(PathSegment.mk "source" PathArguments.none)]))])))
              none),
            (Stmt.letStmt
              []
              (Pat.ident false false "v" none)
              (some
                (Expr.tryExpr
                  (Expr.methodCall
                    (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                    "place_load"
                    none
                    [
                      (Expr.path none (Path.mk false [(PathSegment.mk "place" PathArguments.none)])),
                      (Expr.path none (Path.mk false [(PathSegment.mk "ty" PathArguments.none)]))])))
              none),
            (Stmt.expr
              (Expr.call
                (Expr.path none (Path.mk false [(PathSegment.mk "ret" PathArguments.none)]))
                [
                  (Expr.tuple
                    [
                      (Expr.path none (Path.mk false [(PathSegment.mk "v" PathArguments.none)])),
                      (Expr.path none (Path.mk false [(PathSegment.mk "ty" PathArguments.none)]))])])
              false)]))])

/-- `spec/lang/step/expressions.md:162` -/
def impl_Machine__eval_value_5 : Item :=
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
          "eval_value"
          (Generics.mk [] [])
          [
            (FnArg.receiver [] true none true none),
            (FnArg.typed
              []
              (Pat.struct
                none
                (Path.mk
                  false
                  [
                    (PathSegment.mk "ValueExpr" PathArguments.none),
                    (PathSegment.mk "AddrOf" PathArguments.none)])
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
              (Ty.path none (Path.mk false [(PathSegment.mk "ValueExpr" PathArguments.none)])))]
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
              (Pat.tuple [(Pat.ident false false "place" none), (Pat.ident false false "_ty" none)])
              (some
                (Expr.tryExpr
                  (Expr.methodCall
                    (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                    "eval_place"
                    none
                    [
                      (Expr.path
                        none
                        (Path.mk false [(PathSegment.mk "target" PathArguments.none)]))])))
              none),
            (Stmt.expr
              (Expr.tryExpr
                (Expr.methodCall
                  (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                  "check_value"
                  none
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
                        (Expr.field
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "place" PathArguments.none)]))
                          (Member.named "ptr"))]),
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
            (Stmt.letStmt
              []
              (Pat.ident false false "lookup" none)
              (some
                (Expr.methodCall
                  (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                  "vtable_lookup"
                  none
                  []))
              none),
            (Stmt.letStmt
              []
              (Pat.ident false false "ptr" none)
              (some
                (Expr.tryExpr
                  (Expr.methodCall
                    (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                    "mutate_cur_frame"
                    none
                    [
                      (Expr.closure
                        false
                        [(Pat.ident false false "frame" none), (Pat.ident false false "mem" none)]
                        none
                        (Expr.block
                          none
                          (Block.mk
                            [
                              (Stmt.expr
                                (Expr.methodCall
                                  (Expr.path
                                    none
                                    (Path.mk false [(PathSegment.mk "mem" PathArguments.none)]))
                                  "retag_ptr"
                                  none
                                  [
                                    (Expr.reference
                                      true
                                      (Expr.field
                                        (Expr.path
                                          none
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "frame" PathArguments.none)]))
                                        (Member.named "extra"))),
                                    (Expr.field
                                      (Expr.path
                                        none
                                        (Path.mk
                                          false
                                          [(PathSegment.mk "place" PathArguments.none)]))
                                      (Member.named "ptr")),
                                    (Expr.path
                                      none
                                      (Path.mk false [(PathSegment.mk "ptr_ty" PathArguments.none)])),
                                    (Expr.lit (Lit.bool false)),
                                    (Expr.lit (Lit.bool true)),
                                    (Expr.path
                                      none
                                      (Path.mk false [(PathSegment.mk "lookup" PathArguments.none)]))])
                                false)])))])))
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
                            (Path.mk false [(PathSegment.mk "ptr" PathArguments.none)]))]),
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

/-- `spec/lang/step/expressions.md:186` -/
def impl_Machine__eval_value_6 : Item :=
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
          "eval_value"
          (Generics.mk [] [])
          [
            (FnArg.receiver [] true none true none),
            (FnArg.typed
              []
              (Pat.struct
                none
                (Path.mk
                  false
                  [
                    (PathSegment.mk "ValueExpr" PathArguments.none),
                    (PathSegment.mk "UnOp" PathArguments.none)])
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
              (Ty.path none (Path.mk false [(PathSegment.mk "ValueExpr" PathArguments.none)])))]
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
                    (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                    "eval_value"
                    none
                    [
                      (Expr.path
                        none
                        (Path.mk false [(PathSegment.mk "operand" PathArguments.none)]))])))
              none),
            (Stmt.expr
              (Expr.call
                (Expr.path none (Path.mk false [(PathSegment.mk "ret" PathArguments.none)]))
                [
                  (Expr.tryExpr
                    (Expr.methodCall
                      (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                      "eval_un_op"
                      none
                      [
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "operator" PathArguments.none)])),
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "operand" PathArguments.none)]))]))])
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
          "eval_value"
          (Generics.mk [] [])
          [
            (FnArg.receiver [] true none true none),
            (FnArg.typed
              []
              (Pat.struct
                none
                (Path.mk
                  false
                  [
                    (PathSegment.mk "ValueExpr" PathArguments.none),
                    (PathSegment.mk "BinOp" PathArguments.none)])
                [
                  (FieldPat.mk
                    []
                    (Member.named "operator")
                    true
                    (Pat.ident false false "operator" none)),
                  (FieldPat.mk [] (Member.named "left") true (Pat.ident false false "left" none)),
                  (FieldPat.mk [] (Member.named "right") true (Pat.ident false false "right" none))]
                false)
              (Ty.path none (Path.mk false [(PathSegment.mk "ValueExpr" PathArguments.none)])))]
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
                    (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                    "eval_value"
                    none
                    [(Expr.path none (Path.mk false [(PathSegment.mk "left" PathArguments.none)]))])))
              none),
            (Stmt.letStmt
              []
              (Pat.ident false false "right" none)
              (some
                (Expr.tryExpr
                  (Expr.methodCall
                    (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                    "eval_value"
                    none
                    [(Expr.path none (Path.mk false [(PathSegment.mk "right" PathArguments.none)]))])))
              none),
            (Stmt.expr
              (Expr.call
                (Expr.path none (Path.mk false [(PathSegment.mk "ret" PathArguments.none)]))
                [
                  (Expr.tryExpr
                    (Expr.methodCall
                      (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                      "eval_bin_op"
                      none
                      [
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "operator" PathArguments.none)])),
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "left" PathArguments.none)])),
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "right" PathArguments.none)]))]))])
              false)]))])

/-- `spec/lang/step/expressions.md:211` -/
def impl_Machine__eval_place_0 : Item :=
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
          (Attr.mk true "doc" (AttrMeta.nameValue " Evaluate a place expression to a place.")),
          (Attr.mk true "doc" (AttrMeta.nameValue "")),
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue " Like a raw pointer, the result can be misaligned or null!")),
          (Attr.mk true "specr::argmatch" (AttrMeta.list [(MetaItem.mk "place" AttrMeta.path)]))]
        Visibility.inherited
        false
        (Signature.mk
          false
          false
          false
          none
          "eval_place"
          (Generics.mk [] [])
          [
            (FnArg.receiver [] true none true none),
            (FnArg.typed
              []
              (Pat.ident false false "place" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "PlaceExpr" PathArguments.none)])))]
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
                                      "Place"
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

/-- `spec/lang/step/expressions.md:227` -/
def impl_Machine__eval_place_1 : Item :=
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
          "eval_place"
          (Generics.mk [] [])
          [
            (FnArg.receiver [] true none true none),
            (FnArg.typed
              []
              (Pat.tupleStruct
                none
                (Path.mk
                  false
                  [
                    (PathSegment.mk "PlaceExpr" PathArguments.none),
                    (PathSegment.mk "Local" PathArguments.none)])
                [(Pat.ident false false "name" none)])
              (Ty.path none (Path.mk false [(PathSegment.mk "PlaceExpr" PathArguments.none)])))]
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
                                      "Place"
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
              (Pat.ident false false "ty" none)
              (some
                (Expr.index
                  (Expr.field
                    (Expr.field
                      (Expr.methodCall
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                        "cur_frame"
                        none
                        [])
                      (Member.named "func"))
                    (Member.named "locals"))
                  (Expr.path none (Path.mk false [(PathSegment.mk "name" PathArguments.none)]))))
              none),
            (Stmt.letStmt
              []
              (Pat.tupleStruct
                none
                (Path.mk false [(PathSegment.mk "Some" PathArguments.none)])
                [(Pat.ident false false "ptr" none)])
              (some
                (Expr.methodCall
                  (Expr.field
                    (Expr.methodCall
                      (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                      "cur_frame"
                      none
                      [])
                    (Member.named "locals"))
                  "get"
                  none
                  [(Expr.path none (Path.mk false [(PathSegment.mk "name" PathArguments.none)]))]))
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
                          (MacroBody.exprs [(Expr.lit (Lit.str "access to a dead local"))] false))
                        true)])))),
            (Stmt.expr
              (Expr.call
                (Expr.path none (Path.mk false [(PathSegment.mk "ret" PathArguments.none)]))
                [
                  (Expr.tuple
                    [
                      (Expr.struct
                        none
                        (Path.mk false [(PathSegment.mk "Place" PathArguments.none)])
                        [
                          (FieldValue.mk
                            []
                            (Member.named "ptr")
                            false
                            (Expr.methodCall
                              (Expr.path
                                none
                                (Path.mk false [(PathSegment.mk "ptr" PathArguments.none)]))
                              "widen"
                              none
                              [
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "None" PathArguments.none)]))])),
                          (FieldValue.mk
                            []
                            (Member.named "aligned")
                            false
                            (Expr.lit (Lit.bool true)))]
                        false
                        none),
                      (Expr.path none (Path.mk false [(PathSegment.mk "ty" PathArguments.none)]))])])
              false)]))])

/-- `spec/lang/step/expressions.md:245` -/
def impl_Machine__eval_place_2 : Item :=
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
          "eval_place"
          (Generics.mk [] [])
          [
            (FnArg.receiver [] true none true none),
            (FnArg.typed
              []
              (Pat.struct
                none
                (Path.mk
                  false
                  [
                    (PathSegment.mk "PlaceExpr" PathArguments.none),
                    (PathSegment.mk "Deref" PathArguments.none)])
                [
                  (FieldPat.mk
                    []
                    (Member.named "operand")
                    true
                    (Pat.ident false false "operand" none)),
                  (FieldPat.mk [] (Member.named "ty") true (Pat.ident false false "ty" none))]
                false)
              (Ty.path none (Path.mk false [(PathSegment.mk "PlaceExpr" PathArguments.none)])))]
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
                                      "Place"
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
                    [(Pat.ident false false "ptr_type" none)])])
              (some
                (Expr.tryExpr
                  (Expr.methodCall
                    (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                    "eval_value"
                    none
                    [
                      (Expr.path
                        none
                        (Path.mk false [(PathSegment.mk "operand" PathArguments.none)]))])))
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
                              [(Expr.lit (Lit.str "dereferencing a non-pointer"))]
                              false)))
                        false)])))),
            (Stmt.expr
              (Expr.ite
                (Expr.letCond
                  (Pat.tupleStruct
                    none
                    (Path.mk false [(PathSegment.mk "Some" PathArguments.none)])
                    [(Pat.ident false false "pointee" none)])
                  (Expr.methodCall
                    (Expr.path
                      none
                      (Path.mk false [(PathSegment.mk "ptr_type" PathArguments.none)]))
                    "safe_pointee"
                    none
                    []))
                (Block.mk
                  [
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
                                  (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                                "compute_align"
                                none
                                [
                                  (Expr.field
                                    (Expr.path
                                      none
                                      (Path.mk
                                        false
                                        [(PathSegment.mk "pointee" PathArguments.none)]))
                                    (Member.named "layout")),
                                  (Expr.field
                                    (Expr.path
                                      none
                                      (Path.mk false [(PathSegment.mk "ptr" PathArguments.none)]))
                                    (Member.named "metadata"))])
                              "is_aligned"
                              none
                              [
                                (Expr.field
                                  (Expr.field
                                    (Expr.path
                                      none
                                      (Path.mk false [(PathSegment.mk "ptr" PathArguments.none)]))
                                    (Member.named "thin_pointer"))
                                  (Member.named "addr"))])]
                          false))
                      true),
                    (Stmt.expr
                      (Expr.tryExpr
                        (Expr.methodCall
                          (Expr.field
                            (Expr.path
                              none
                              (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                            (Member.named "mem"))
                          "dereferenceable"
                          none
                          [
                            (Expr.field
                              (Expr.path
                                none
                                (Path.mk false [(PathSegment.mk "ptr" PathArguments.none)]))
                              (Member.named "thin_pointer")),
                            (Expr.methodCall
                              (Expr.path
                                none
                                (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                              "compute_size"
                              none
                              [
                                (Expr.field
                                  (Expr.path
                                    none
                                    (Path.mk false [(PathSegment.mk "pointee" PathArguments.none)]))
                                  (Member.named "layout")),
                                (Expr.field
                                  (Expr.path
                                    none
                                    (Path.mk false [(PathSegment.mk "ptr" PathArguments.none)]))
                                  (Member.named "metadata"))])]))
                      true)])
                none)
              false),
            (Stmt.letStmt
              []
              (Pat.ident false false "aligned" none)
              (some
                (Expr.methodCall
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
                      (Expr.field
                        (Expr.path none (Path.mk false [(PathSegment.mk "ptr" PathArguments.none)]))
                        (Member.named "metadata"))])
                  "is_aligned"
                  none
                  [
                    (Expr.field
                      (Expr.field
                        (Expr.path none (Path.mk false [(PathSegment.mk "ptr" PathArguments.none)]))
                        (Member.named "thin_pointer"))
                      (Member.named "addr"))]))
              none),
            (Stmt.expr
              (Expr.call
                (Expr.path none (Path.mk false [(PathSegment.mk "ret" PathArguments.none)]))
                [
                  (Expr.tuple
                    [
                      (Expr.struct
                        none
                        (Path.mk false [(PathSegment.mk "Place" PathArguments.none)])
                        [
                          (FieldValue.mk
                            []
                            (Member.named "ptr")
                            true
                            (Expr.path
                              none
                              (Path.mk false [(PathSegment.mk "ptr" PathArguments.none)]))),
                          (FieldValue.mk
                            []
                            (Member.named "aligned")
                            true
                            (Expr.path
                              none
                              (Path.mk false [(PathSegment.mk "aligned" PathArguments.none)])))]
                        false
                        none),
                      (Expr.path none (Path.mk false [(PathSegment.mk "ty" PathArguments.none)]))])])
              false)]))])

/-- `spec/lang/step/expressions.md:270` -/
def impl_Machine__eval_place_3 : Item :=
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
          "eval_place"
          (Generics.mk [] [])
          [
            (FnArg.receiver [] true none true none),
            (FnArg.typed
              []
              (Pat.struct
                none
                (Path.mk
                  false
                  [
                    (PathSegment.mk "PlaceExpr" PathArguments.none),
                    (PathSegment.mk "Field" PathArguments.none)])
                [
                  (FieldPat.mk [] (Member.named "root") true (Pat.ident false false "root" none)),
                  (FieldPat.mk [] (Member.named "field") true (Pat.ident false false "field" none))]
                false)
              (Ty.path none (Path.mk false [(PathSegment.mk "PlaceExpr" PathArguments.none)])))]
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
                                      "Place"
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
              (Pat.tuple [(Pat.ident false false "root" none), (Pat.ident false false "ty" none)])
              (some
                (Expr.tryExpr
                  (Expr.methodCall
                    (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                    "eval_place"
                    none
                    [(Expr.path none (Path.mk false [(PathSegment.mk "root" PathArguments.none)]))])))
              none),
            (Stmt.letStmt
              []
              (Pat.tuple
                [(Pat.ident false false "offset" none), (Pat.ident false false "field_ty" none)])
              (some
                (Expr.matchExpr
                  (Expr.path none (Path.mk false [(PathSegment.mk "ty" PathArguments.none)]))
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
                              (Expr.ite
                                (Expr.binary
                                  (Expr.binary
                                    (Expr.path
                                      none
                                      (Path.mk false [(PathSegment.mk "field" PathArguments.none)]))
                                    BinOp.ge
                                    (Expr.lit (Lit.int 0 "")))
                                  BinOp.and
                                  (Expr.binary
                                    (Expr.path
                                      none
                                      (Path.mk false [(PathSegment.mk "field" PathArguments.none)]))
                                    BinOp.lt
                                    (Expr.methodCall
                                      (Expr.path
                                        none
                                        (Path.mk
                                          false
                                          [(PathSegment.mk "sized_fields" PathArguments.none)]))
                                      "len"
                                      none
                                      [])))
                                (Block.mk
                                  [
                                    (Stmt.expr
                                      (Expr.index
                                        (Expr.path
                                          none
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "sized_fields" PathArguments.none)]))
                                        (Expr.path
                                          none
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "field" PathArguments.none)])))
                                      false)])
                                (some
                                  (Expr.ite
                                    (Expr.binary
                                      (Expr.path
                                        none
                                        (Path.mk
                                          false
                                          [(PathSegment.mk "field" PathArguments.none)]))
                                      BinOp.eq
                                      (Expr.methodCall
                                        (Expr.path
                                          none
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "sized_fields" PathArguments.none)]))
                                        "len"
                                        none
                                        []))
                                    (Block.mk
                                      [
                                        (Stmt.letStmt
                                          []
                                          (Pat.ident false false "tail_ty" none)
                                          (some
                                            (Expr.methodCall
                                              (Expr.path
                                                none
                                                (Path.mk
                                                  false
                                                  [
                                                    (PathSegment.mk
                                                      "unsized_field"
                                                      PathArguments.none)]))
                                              "expect"
                                              none
                                              [
                                                (Expr.lit
                                                  (Lit.str
                                                    "field projection to non-existing unsized tail"))]))
                                          none),
                                        (Stmt.letStmt
                                          []
                                          (Pat.ident false false "tail_align" none)
                                          (some
                                            (Expr.methodCall
                                              (Expr.path
                                                none
                                                (Path.mk
                                                  false
                                                  [(PathSegment.mk "self" PathArguments.none)]))
                                              "compute_align"
                                              none
                                              [
                                                (Expr.methodCall
                                                  (Expr.path
                                                    none
                                                    (Path.mk
                                                      false
                                                      [
                                                        (PathSegment.mk
                                                          "tail_ty"
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
                                                                "M"
                                                                PathArguments.none),
                                                              (PathSegment.mk
                                                                "T"
                                                                PathArguments.none)])))])
                                                  []),
                                                (Expr.field
                                                  (Expr.field
                                                    (Expr.path
                                                      none
                                                      (Path.mk
                                                        false
                                                        [(PathSegment.mk "root" PathArguments.none)]))
                                                    (Member.named "ptr"))
                                                  (Member.named "metadata"))]))
                                          none),
                                        (Stmt.letStmt
                                          []
                                          (Pat.ident false false "offset" none)
                                          (some
                                            (Expr.methodCall
                                              (Expr.path
                                                none
                                                (Path.mk
                                                  false
                                                  [
                                                    (PathSegment.mk
                                                      "sized_head_layout"
                                                      PathArguments.none)]))
                                              "tail_offset"
                                              none
                                              [
                                                (Expr.path
                                                  none
                                                  (Path.mk
                                                    false
                                                    [
                                                      (PathSegment.mk
                                                        "tail_align"
                                                        PathArguments.none)]))]))
                                          none),
                                        (Stmt.expr
                                          (Expr.tuple
                                            [
                                              (Expr.path
                                                none
                                                (Path.mk
                                                  false
                                                  [(PathSegment.mk "offset" PathArguments.none)])),
                                              (Expr.path
                                                none
                                                (Path.mk
                                                  false
                                                  [(PathSegment.mk "tail_ty" PathArguments.none)]))])
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
                                                  [(PathSegment.mk "panic" PathArguments.none)])
                                                MacroDelimiter.paren
                                                (MacroBody.exprs
                                                  [
                                                    (Expr.lit
                                                      (Lit.str "field projection to invalid field"))]
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
                      (Expr.index
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "fields" PathArguments.none)]))
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "field" PathArguments.none)])))),
                    (Arm.mk
                      []
                      Pat.wild
                      none
                      (Expr.macro
                        (Macro.mk
                          (Path.mk false [(PathSegment.mk "panic" PathArguments.none)])
                          MacroDelimiter.paren
                          (MacroBody.exprs
                            [(Expr.lit (Lit.str "field projection on non-projectable type"))]
                            false))))]))
              none),
            (Stmt.macro
              []
              (Macro.mk
                (Path.mk false [(PathSegment.mk "assert" PathArguments.none)])
                MacroDelimiter.paren
                (MacroBody.exprs
                  [
                    (Expr.binary
                      (Expr.path
                        none
                        (Path.mk false [(PathSegment.mk "offset" PathArguments.none)]))
                      BinOp.le
                      (Expr.methodCall
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                        "compute_size"
                        none
                        [
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
                                      [
                                        (PathSegment.mk "M" PathArguments.none),
                                        (PathSegment.mk "T" PathArguments.none)])))])
                            []),
                          (Expr.field
                            (Expr.field
                              (Expr.path
                                none
                                (Path.mk false [(PathSegment.mk "root" PathArguments.none)]))
                              (Member.named "ptr"))
                            (Member.named "metadata"))]))]
                  false))
              true),
            (Stmt.letStmt
              []
              (Pat.ident false false "ptr" none)
              (some
                (Expr.tryExpr
                  (Expr.methodCall
                    (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                    "ptr_offset_inbounds"
                    none
                    [
                      (Expr.field
                        (Expr.field
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "root" PathArguments.none)]))
                          (Member.named "ptr"))
                        (Member.named "thin_pointer")),
                      (Expr.methodCall
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "offset" PathArguments.none)]))
                        "bytes"
                        none
                        [])])))
              none),
            (Stmt.letStmt
              []
              (Pat.ident false false "ptr" none)
              (some
                (Expr.ite
                  (Expr.unary
                    UnOp.not
                    (Expr.methodCall
                      (Expr.methodCall
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "field_ty" PathArguments.none)]))
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
                      "is_sized"
                      none
                      []))
                  (Block.mk
                    [
                      (Stmt.expr
                        (Expr.methodCall
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "ptr" PathArguments.none)]))
                          "widen"
                          none
                          [
                            (Expr.field
                              (Expr.field
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "root" PathArguments.none)]))
                                (Member.named "ptr"))
                              (Member.named "metadata"))])
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
                                (Path.mk false [(PathSegment.mk "ptr" PathArguments.none)]))
                              "widen"
                              none
                              [
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "None" PathArguments.none)]))])
                            false)])))))
              none),
            (Stmt.expr
              (Expr.call
                (Expr.path none (Path.mk false [(PathSegment.mk "ret" PathArguments.none)]))
                [
                  (Expr.tuple
                    [
                      (Expr.struct
                        none
                        (Path.mk false [(PathSegment.mk "Place" PathArguments.none)])
                        [
                          (FieldValue.mk
                            []
                            (Member.named "ptr")
                            true
                            (Expr.path
                              none
                              (Path.mk false [(PathSegment.mk "ptr" PathArguments.none)])))]
                        true
                        (some
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "root" PathArguments.none)])))),
                      (Expr.path
                        none
                        (Path.mk false [(PathSegment.mk "field_ty" PathArguments.none)]))])])
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
          "eval_place"
          (Generics.mk [] [])
          [
            (FnArg.receiver [] true none true none),
            (FnArg.typed
              []
              (Pat.struct
                none
                (Path.mk
                  false
                  [
                    (PathSegment.mk "PlaceExpr" PathArguments.none),
                    (PathSegment.mk "Index" PathArguments.none)])
                [
                  (FieldPat.mk [] (Member.named "root") true (Pat.ident false false "root" none)),
                  (FieldPat.mk [] (Member.named "index") true (Pat.ident false false "index" none))]
                false)
              (Ty.path none (Path.mk false [(PathSegment.mk "PlaceExpr" PathArguments.none)])))]
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
                                      "Place"
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
              (Pat.tuple [(Pat.ident false false "root" none), (Pat.ident false false "ty" none)])
              (some
                (Expr.tryExpr
                  (Expr.methodCall
                    (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                    "eval_place"
                    none
                    [(Expr.path none (Path.mk false [(PathSegment.mk "root" PathArguments.none)]))])))
              none),
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
                        (PathSegment.mk "Int" PathArguments.none)])
                    [(Pat.ident false false "index" none)]),
                  Pat.wild])
              (some
                (Expr.tryExpr
                  (Expr.methodCall
                    (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                    "eval_value"
                    none
                    [(Expr.path none (Path.mk false [(PathSegment.mk "index" PathArguments.none)]))])))
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
                              [(Expr.lit (Lit.str "non-integer operand for array index"))]
                              false)))
                        false)])))),
            (Stmt.letStmt
              []
              (Pat.tuple
                [(Pat.ident false false "elem_ty" none), (Pat.ident false false "count" none)])
              (some
                (Expr.matchExpr
                  (Expr.path none (Path.mk false [(PathSegment.mk "ty" PathArguments.none)]))
                  [
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
                      (Expr.tuple
                        [
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "elem" PathArguments.none)])),
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "count" PathArguments.none)]))])),
                    (Arm.mk
                      []
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
                                (Path.mk false [(PathSegment.mk "Some" PathArguments.none)])
                                [
                                  (Pat.tupleStruct
                                    none
                                    (Path.mk
                                      false
                                      [
                                        (PathSegment.mk "PointerMeta" PathArguments.none),
                                        (PathSegment.mk "ElementCount" PathArguments.none)])
                                    [(Pat.ident false false "count" none)])])
                              (some
                                (Expr.field
                                  (Expr.field
                                    (Expr.path
                                      none
                                      (Path.mk false [(PathSegment.mk "root" PathArguments.none)]))
                                    (Member.named "ptr"))
                                  (Member.named "metadata")))
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
                                            [(PathSegment.mk "panic" PathArguments.none)])
                                          MacroDelimiter.paren
                                          (MacroBody.exprs
                                            [
                                              (Expr.lit
                                                (Lit.str
                                                  "eval_place should always return a ptr which matches meta for the LayoutStrategy of ty"))]
                                            false))
                                        true)])))),
                            (Stmt.expr
                              (Expr.tuple
                                [
                                  (Expr.path
                                    none
                                    (Path.mk false [(PathSegment.mk "elem" PathArguments.none)])),
                                  (Expr.path
                                    none
                                    (Path.mk false [(PathSegment.mk "count" PathArguments.none)]))])
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
                            [(Expr.lit (Lit.str "index projection on non-indexable type"))]
                            false))))]))
              none),
            (Stmt.expr
              (Expr.ite
                (Expr.binary
                  (Expr.binary
                    (Expr.path none (Path.mk false [(PathSegment.mk "index" PathArguments.none)]))
                    BinOp.lt
                    (Expr.lit (Lit.int 0 "")))
                  BinOp.or
                  (Expr.binary
                    (Expr.path none (Path.mk false [(PathSegment.mk "index" PathArguments.none)]))
                    BinOp.ge
                    (Expr.path none (Path.mk false [(PathSegment.mk "count" PathArguments.none)]))))
                (Block.mk
                  [
                    (Stmt.macro
                      []
                      (Macro.mk
                        (Path.mk false [(PathSegment.mk "throw_ub" PathArguments.none)])
                        MacroDelimiter.paren
                        (MacroBody.exprs
                          [(Expr.lit (Lit.str "access to out-of-bounds index"))]
                          false))
                      true)])
                none)
              false),
            (Stmt.letStmt
              []
              (Pat.ident false false "elem_size" none)
              (some
                (Expr.methodCall
                  (Expr.methodCall
                    (Expr.path none (Path.mk false [(PathSegment.mk "elem_ty" PathArguments.none)]))
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
                  [(Expr.lit (Lit.str "WF ensures array & slice elements are sized"))]))
              none),
            (Stmt.letStmt
              []
              (Pat.ident false false "offset" none)
              (some
                (Expr.binary
                  (Expr.path none (Path.mk false [(PathSegment.mk "index" PathArguments.none)]))
                  BinOp.mul
                  (Expr.path none (Path.mk false [(PathSegment.mk "elem_size" PathArguments.none)]))))
              none),
            (Stmt.macro
              []
              (Macro.mk
                (Path.mk false [(PathSegment.mk "assert" PathArguments.none)])
                MacroDelimiter.paren
                (MacroBody.exprs
                  [
                    (Expr.binary
                      (Expr.path
                        none
                        (Path.mk false [(PathSegment.mk "offset" PathArguments.none)]))
                      BinOp.le
                      (Expr.methodCall
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                        "compute_size"
                        none
                        [
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
                                      [
                                        (PathSegment.mk "M" PathArguments.none),
                                        (PathSegment.mk "T" PathArguments.none)])))])
                            []),
                          (Expr.field
                            (Expr.field
                              (Expr.path
                                none
                                (Path.mk false [(PathSegment.mk "root" PathArguments.none)]))
                              (Member.named "ptr"))
                            (Member.named "metadata"))])),
                    (Expr.lit
                      (Lit.str
                        "sanity check: the indexed offset should not be outside what the type allows."))]
                  false))
              true),
            (Stmt.letStmt
              []
              (Pat.ident false false "ptr" none)
              (some
                (Expr.tryExpr
                  (Expr.methodCall
                    (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                    "ptr_offset_inbounds"
                    none
                    [
                      (Expr.field
                        (Expr.field
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "root" PathArguments.none)]))
                          (Member.named "ptr"))
                        (Member.named "thin_pointer")),
                      (Expr.methodCall
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "offset" PathArguments.none)]))
                        "bytes"
                        none
                        [])])))
              none),
            (Stmt.expr
              (Expr.call
                (Expr.path none (Path.mk false [(PathSegment.mk "ret" PathArguments.none)]))
                [
                  (Expr.tuple
                    [
                      (Expr.struct
                        none
                        (Path.mk false [(PathSegment.mk "Place" PathArguments.none)])
                        [
                          (FieldValue.mk
                            []
                            (Member.named "ptr")
                            false
                            (Expr.methodCall
                              (Expr.path
                                none
                                (Path.mk false [(PathSegment.mk "ptr" PathArguments.none)]))
                              "widen"
                              none
                              [
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "None" PathArguments.none)]))]))]
                        true
                        (some
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "root" PathArguments.none)])))),
                      (Expr.path
                        none
                        (Path.mk false [(PathSegment.mk "elem_ty" PathArguments.none)]))])])
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
          "eval_place"
          (Generics.mk [] [])
          [
            (FnArg.receiver [] true none true none),
            (FnArg.typed
              []
              (Pat.struct
                none
                (Path.mk
                  false
                  [
                    (PathSegment.mk "PlaceExpr" PathArguments.none),
                    (PathSegment.mk "Downcast" PathArguments.none)])
                [
                  (FieldPat.mk [] (Member.named "root") true (Pat.ident false false "root" none)),
                  (FieldPat.mk
                    []
                    (Member.named "discriminant")
                    true
                    (Pat.ident false false "discriminant" none))]
                false)
              (Ty.path none (Path.mk false [(PathSegment.mk "PlaceExpr" PathArguments.none)])))]
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
                                      "Place"
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
              (Pat.tuple [(Pat.ident false false "root" none), (Pat.ident false false "ty" none)])
              (some
                (Expr.tryExpr
                  (Expr.methodCall
                    (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                    "eval_place"
                    none
                    [(Expr.path none (Path.mk false [(PathSegment.mk "root" PathArguments.none)]))])))
              none),
            (Stmt.letStmt
              []
              (Pat.ident false false "var_ty" none)
              (some
                (Expr.matchExpr
                  (Expr.path none (Path.mk false [(PathSegment.mk "ty" PathArguments.none)]))
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
                      (Expr.field
                        (Expr.index
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "variants" PathArguments.none)]))
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "discriminant" PathArguments.none)])))
                        (Member.named "ty"))),
                    (Arm.mk
                      []
                      Pat.wild
                      none
                      (Expr.macro
                        (Macro.mk
                          (Path.mk false [(PathSegment.mk "panic" PathArguments.none)])
                          MacroDelimiter.paren
                          (MacroBody.exprs [(Expr.lit (Lit.str "enum downcast on non-enum"))] false))))]))
              none),
            (Stmt.expr
              (Expr.call
                (Expr.path none (Path.mk false [(PathSegment.mk "ret" PathArguments.none)]))
                [
                  (Expr.tuple
                    [
                      (Expr.path none (Path.mk false [(PathSegment.mk "root" PathArguments.none)])),
                      (Expr.path
                        none
                        (Path.mk false [(PathSegment.mk "var_ty" PathArguments.none)]))])])
              false)]))])

/-- All items of `spec/lang/step/expressions.md`, in source order, with provenance. -/
def items : List SourceItem :=
  [
    (SourceItem.mk
      "impl_Machine__eval_value_0"
      17
      "94bba638fd72303c49a31a13e3eaca00c4a68be47015acf95161bae5a1fed1fb"
      impl_Machine__eval_value_0),
    (SourceItem.mk
      "impl_Machine__eval_constant"
      32
      "f83c7a5a7f61bfc3655b244d7ebd021aea5cc9c9601ddcadc5844225f451b948"
      impl_Machine__eval_constant),
    (SourceItem.mk
      "impl_Machine__eval_value_1"
      68
      "70ec0b5857334f8c47e283a18eff8842ae603b20ad739a41f9eaeec5aa622b76"
      impl_Machine__eval_value_1),
    (SourceItem.mk
      "impl_Machine__eval_value_2"
      79
      "98f306bcf4d0dcf60678154b73f28ff2f0e499666e312f94a6131ed80179a4c5"
      impl_Machine__eval_value_2),
    (SourceItem.mk
      "impl_Machine__eval_value_3"
      94
      "4789cec43a85dcac465f8716a3ea688cb0255fe2a90f415fa408269999e238af"
      impl_Machine__eval_value_3),
    (SourceItem.mk
      "impl_Machine__eval_value_4"
      105
      "761a67cd73c23887120ea739b88f8d478df5cbb5ef88400e4b5b09852402a202"
      impl_Machine__eval_value_4),
    (SourceItem.mk
      "impl_Machine__place_load"
      137
      "3330de96a32652660764c9241138d151b22712bafefb3dbb53f0950ab2a787a1"
      impl_Machine__place_load),
    (SourceItem.mk
      "impl_Machine__eval_value_5"
      162
      "f4f831c1ee4b26343c67e5808bb6e5eb8ca068b6eca6cc698901fafe85dea6ae"
      impl_Machine__eval_value_5),
    (SourceItem.mk
      "impl_Machine__eval_value_6"
      186
      "4793fa0f7bd635890ad9b7916a959cac72a0df67faf4b09f02e98608807b7a3a"
      impl_Machine__eval_value_6),
    (SourceItem.mk
      "impl_Machine__eval_place_0"
      211
      "7642a0b5418760da4b931b972824a3be02dcc10c08503ea3e6c0d2b1859fbec9"
      impl_Machine__eval_place_0),
    (SourceItem.mk
      "impl_Machine__eval_place_1"
      227
      "d27f2a90134d1584080d2ebb4017f10067ce4c01f56693a7194f2613921d1ac7"
      impl_Machine__eval_place_1),
    (SourceItem.mk
      "impl_Machine__eval_place_2"
      245
      "55e0ce7fce76c9e703b5bf095bfc4e2d7519ecb00852e704a5220cf89addc82c"
      impl_Machine__eval_place_2),
    (SourceItem.mk
      "impl_Machine__eval_place_3"
      270
      "4dae85886352b74ef9f5508c3f6849ec428bae017f38b8dc87e362f918eda0c9"
      impl_Machine__eval_place_3)]

end MiniRustSpec.Gen.Items.Lang.Step.Expressions
