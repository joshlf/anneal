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
`spec/lang/step/terminators.md` (commit `d821c6e3`), one Lean definition per item, in source order.
-/

import MiniRustSpec.Meta.Syntax

set_option maxRecDepth 100000

namespace MiniRustSpec.Gen.Items.Lang.Step.Terminators

open MiniRustSpec.Syntax

/-- Path of the upstream file these items were extracted from. -/
def sourceFile : String := "spec/lang/step/terminators.md"

/-- SHA-256 of the upstream file. -/
def sourceSha256 : String := "ae0c30634abe041ab520ee647c249489db5aa01e82ee0baa07b783e1d4086360"

/-- `spec/lang/step/terminators.md:8` -/
def impl_Machine__eval_terminator_0 : Item :=
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
        [(Attr.mk true "specr::argmatch" (AttrMeta.list "terminator"))]
        Visibility.inherited
        false
        (Signature.mk
          false
          false
          false
          none
          "eval_terminator"
          (Generics.mk [] [])
          [
            (FnArg.receiver [] true none true none),
            (FnArg.typed
              []
              (Pat.ident false false "terminator" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "Terminator" PathArguments.none)])))]
          false
          (some (Ty.path none (Path.mk false [(PathSegment.mk "NdResult" PathArguments.none)]))))
        (Block.mk [(Stmt.expr (Expr.range none RangeLimits.halfOpen none) false)]))])

/-- `spec/lang/step/terminators.md:19` -/
def impl_Machine__jump_to_block : Item :=
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
          "jump_to_block"
          (Generics.mk [] [])
          [
            (FnArg.receiver [] true none true none),
            (FnArg.typed
              []
              (Pat.ident false false "block" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "BbName" PathArguments.none)])))]
          false
          (some (Ty.path none (Path.mk false [(PathSegment.mk "NdResult" PathArguments.none)]))))
        (Block.mk
          [
            (Stmt.expr
              (Expr.methodCall
                (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                "try_mutate_cur_frame"
                none
                [
                  (Expr.closure
                    false
                    [(Pat.ident false false "frame" none), (Pat.ident false false "_mem" none)]
                    none
                    (Expr.block
                      none
                      (Block.mk
                        [
                          (Stmt.expr
                            (Expr.methodCall
                              (Expr.path
                                none
                                (Path.mk false [(PathSegment.mk "frame" PathArguments.none)]))
                              "jump_to_block"
                              none
                              [
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "block" PathArguments.none)]))])
                            true),
                          (Stmt.expr
                            (Expr.call
                              (Expr.path
                                none
                                (Path.mk false [(PathSegment.mk "ret" PathArguments.none)]))
                              [(Expr.tuple [])])
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
          "eval_terminator"
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
                    (PathSegment.mk "Terminator" PathArguments.none),
                    (PathSegment.mk "Goto" PathArguments.none)])
                [(Pat.ident false false "block_name" none)])
              (Ty.path none (Path.mk false [(PathSegment.mk "Terminator" PathArguments.none)])))]
          false
          (some (Ty.path none (Path.mk false [(PathSegment.mk "NdResult" PathArguments.none)]))))
        (Block.mk
          [
            (Stmt.expr
              (Expr.tryExpr
                (Expr.methodCall
                  (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                  "jump_to_block"
                  none
                  [
                    (Expr.path
                      none
                      (Path.mk false [(PathSegment.mk "block_name" PathArguments.none)]))]))
              true),
            (Stmt.expr
              (Expr.call
                (Expr.path none (Path.mk false [(PathSegment.mk "ret" PathArguments.none)]))
                [(Expr.tuple [])])
              false)]))])

/-- `spec/lang/step/terminators.md:37` -/
def impl_Machine__eval_terminator_1 : Item :=
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
          "eval_terminator"
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
                    (PathSegment.mk "Terminator" PathArguments.none),
                    (PathSegment.mk "Switch" PathArguments.none)])
                [
                  (FieldPat.mk [] (Member.named "value") true (Pat.ident false false "value" none)),
                  (FieldPat.mk [] (Member.named "cases") true (Pat.ident false false "cases" none)),
                  (FieldPat.mk
                    []
                    (Member.named "fallback")
                    true
                    (Pat.ident false false "fallback" none))]
                false)
              (Ty.path none (Path.mk false [(PathSegment.mk "Terminator" PathArguments.none)])))]
          false
          (some (Ty.path none (Path.mk false [(PathSegment.mk "NdResult" PathArguments.none)]))))
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
                [(Pat.ident false false "value" none)])
              (some
                (Expr.field
                  (Expr.tryExpr
                    (Expr.methodCall
                      (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                      "eval_value"
                      none
                      [
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "value" PathArguments.none)]))]))
                  (Member.unnamed 0)))
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
                          (MacroBody.exprs [(Expr.lit (Lit.str "switch on a non-integer"))] false))
                        true)])))),
            (Stmt.letStmt
              []
              (Pat.ident false false "next" none)
              (some
                (Expr.methodCall
                  (Expr.methodCall
                    (Expr.path none (Path.mk false [(PathSegment.mk "cases" PathArguments.none)]))
                    "get"
                    none
                    [(Expr.path none (Path.mk false [(PathSegment.mk "value" PathArguments.none)]))])
                  "unwrap_or"
                  none
                  [
                    (Expr.path
                      none
                      (Path.mk false [(PathSegment.mk "fallback" PathArguments.none)]))]))
              none),
            (Stmt.expr
              (Expr.tryExpr
                (Expr.methodCall
                  (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                  "jump_to_block"
                  none
                  [(Expr.path none (Path.mk false [(PathSegment.mk "next" PathArguments.none)]))]))
              true),
            (Stmt.expr
              (Expr.call
                (Expr.path none (Path.mk false [(PathSegment.mk "ret" PathArguments.none)]))
                [(Expr.tuple [])])
              false)]))])

/-- `spec/lang/step/terminators.md:53` -/
def impl_Machine__eval_terminator_2 : Item :=
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
          "eval_terminator"
          (Generics.mk [] [])
          [
            (FnArg.receiver [] true none true none),
            (FnArg.typed
              []
              (Pat.path
                none
                (Path.mk
                  false
                  [
                    (PathSegment.mk "Terminator" PathArguments.none),
                    (PathSegment.mk "Unreachable" PathArguments.none)]))
              (Ty.path none (Path.mk false [(PathSegment.mk "Terminator" PathArguments.none)])))]
          false
          (some (Ty.path none (Path.mk false [(PathSegment.mk "NdResult" PathArguments.none)]))))
        (Block.mk
          [
            (Stmt.macro
              []
              (Macro.mk
                (Path.mk false [(PathSegment.mk "throw_ub" PathArguments.none)])
                MacroDelimiter.paren
                (MacroBody.exprs [(Expr.lit (Lit.str "reached unreachable code"))] false))
              true)]))])

/-- `spec/lang/step/terminators.md:66` -/
def fn_check_abi_compatibility : Item :=
  (Item.fn
    [
      (Attr.mk
        true
        "doc"
        (AttrMeta.nameValue " Check whether the two types are compatible in function calls.")),
      (Attr.mk true "doc" (AttrMeta.nameValue "")),
      (Attr.mk
        true
        "doc"
        (AttrMeta.nameValue
          " This means *at least* they have the same size and alignment (for on-stack argument passing).")),
      (Attr.mk
        true
        "doc"
        (AttrMeta.nameValue
          " However, when arguments get passed in registers, more details become relevant, so we require")),
      (Attr.mk true "doc" (AttrMeta.nameValue " almost full structural equality."))]
    Visibility.inherited
    (Signature.mk
      false
      false
      false
      none
      "check_abi_compatibility"
      (Generics.mk [] [])
      [
        (FnArg.typed
          []
          (Pat.ident false false "caller_ty" none)
          (Ty.path none (Path.mk false [(PathSegment.mk "Type" PathArguments.none)]))),
        (FnArg.typed
          []
          (Pat.ident false false "callee_ty" none)
          (Ty.path none (Path.mk false [(PathSegment.mk "Type" PathArguments.none)])))]
      false
      (some (Ty.path none (Path.mk false [(PathSegment.mk "bool" PathArguments.none)]))))
    (Block.mk
      [
        (Stmt.expr
          (Expr.matchExpr
            (Expr.tuple
              [
                (Expr.path none (Path.mk false [(PathSegment.mk "caller_ty" PathArguments.none)])),
                (Expr.path none (Path.mk false [(PathSegment.mk "callee_ty" PathArguments.none)]))])
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
                      [(Pat.ident false false "caller_ty" none)]),
                    (Pat.tupleStruct
                      none
                      (Path.mk
                        false
                        [
                          (PathSegment.mk "Type" PathArguments.none),
                          (PathSegment.mk "Int" PathArguments.none)])
                      [(Pat.ident false false "callee_ty" none)])])
                none
                (Expr.binary
                  (Expr.path none (Path.mk false [(PathSegment.mk "caller_ty" PathArguments.none)]))
                  BinOp.eq
                  (Expr.path none (Path.mk false [(PathSegment.mk "callee_ty" PathArguments.none)])))),
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
                    (Pat.path
                      none
                      (Path.mk
                        false
                        [
                          (PathSegment.mk "Type" PathArguments.none),
                          (PathSegment.mk "Bool" PathArguments.none)]))])
                none
                (Expr.lit (Lit.bool true))),
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
                      [(Pat.ident false false "caller_ty" none)]),
                    (Pat.tupleStruct
                      none
                      (Path.mk
                        false
                        [
                          (PathSegment.mk "Type" PathArguments.none),
                          (PathSegment.mk "Ptr" PathArguments.none)])
                      [(Pat.ident false false "callee_ty" none)])])
                none
                (Expr.binary
                  (Expr.methodCall
                    (Expr.path
                      none
                      (Path.mk false [(PathSegment.mk "caller_ty" PathArguments.none)]))
                    "meta_kind"
                    none
                    [])
                  BinOp.eq
                  (Expr.methodCall
                    (Expr.path
                      none
                      (Path.mk false [(PathSegment.mk "callee_ty" PathArguments.none)]))
                    "meta_kind"
                    none
                    []))),
              (Arm.mk
                []
                (Pat.tuple
                  [
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
                          false
                          (Pat.ident false false "caller_fields" none)),
                        (FieldPat.mk
                          []
                          (Member.named "sized_head_layout")
                          false
                          (Pat.ident false false "caller_head_layout" none)),
                        (FieldPat.mk
                          []
                          (Member.named "unsized_field")
                          false
                          (Pat.ident false false "caller_unsized_field" none))]
                      false),
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
                          false
                          (Pat.ident false false "callee_fields" none)),
                        (FieldPat.mk
                          []
                          (Member.named "sized_head_layout")
                          false
                          (Pat.ident false false "callee_head_layout" none)),
                        (FieldPat.mk
                          []
                          (Member.named "unsized_field")
                          false
                          (Pat.ident false false "callee_unsized_field" none))]
                      false)])
                none
                (Expr.block
                  none
                  (Block.mk
                    [
                      (Stmt.letStmt
                        []
                        (Pat.tuple
                          [
                            (Pat.ident false false "caller_size" none),
                            (Pat.ident false false "caller_align" none)])
                        (some
                          (Expr.methodCall
                            (Expr.path
                              none
                              (Path.mk
                                false
                                [(PathSegment.mk "caller_head_layout" PathArguments.none)]))
                            "head_size_and_align"
                            none
                            []))
                        none),
                      (Stmt.letStmt
                        []
                        (Pat.tuple
                          [
                            (Pat.ident false false "callee_size" none),
                            (Pat.ident false false "callee_align" none)])
                        (some
                          (Expr.methodCall
                            (Expr.path
                              none
                              (Path.mk
                                false
                                [(PathSegment.mk "callee_head_layout" PathArguments.none)]))
                            "head_size_and_align"
                            none
                            []))
                        none),
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
                                  (Path.mk
                                    false
                                    [(PathSegment.mk "caller_unsized_field" PathArguments.none)]))
                                "is_none"
                                none
                                []),
                              (Expr.lit (Lit.str "wf ensures all arugments are sized"))]
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
                                (Expr.path
                                  none
                                  (Path.mk
                                    false
                                    [(PathSegment.mk "callee_unsized_field" PathArguments.none)]))
                                "is_none"
                                none
                                []),
                              (Expr.lit (Lit.str "wf ensures all arugments are sized"))]
                            false))
                        true),
                      (Stmt.expr
                        (Expr.binary
                          (Expr.binary
                            (Expr.binary
                              (Expr.binary
                                (Expr.methodCall
                                  (Expr.path
                                    none
                                    (Path.mk
                                      false
                                      [(PathSegment.mk "caller_fields" PathArguments.none)]))
                                  "len"
                                  none
                                  [])
                                BinOp.eq
                                (Expr.methodCall
                                  (Expr.path
                                    none
                                    (Path.mk
                                      false
                                      [(PathSegment.mk "callee_fields" PathArguments.none)]))
                                  "len"
                                  none
                                  []))
                              BinOp.and
                              (Expr.methodCall
                                (Expr.methodCall
                                  (Expr.path
                                    none
                                    (Path.mk
                                      false
                                      [(PathSegment.mk "caller_fields" PathArguments.none)]))
                                  "zip"
                                  none
                                  [
                                    (Expr.path
                                      none
                                      (Path.mk
                                        false
                                        [(PathSegment.mk "callee_fields" PathArguments.none)]))])
                                "all"
                                none
                                [
                                  (Expr.closure
                                    false
                                    [
                                      (Pat.tuple
                                        [
                                          (Pat.ident false false "caller_field" none),
                                          (Pat.ident false false "callee_field" none)])]
                                    none
                                    (Expr.binary
                                      (Expr.binary
                                        (Expr.field
                                          (Expr.path
                                            none
                                            (Path.mk
                                              false
                                              [(PathSegment.mk "caller_field" PathArguments.none)]))
                                          (Member.unnamed 0))
                                        BinOp.eq
                                        (Expr.field
                                          (Expr.path
                                            none
                                            (Path.mk
                                              false
                                              [(PathSegment.mk "callee_field" PathArguments.none)]))
                                          (Member.unnamed 0)))
                                      BinOp.and
                                      (Expr.call
                                        (Expr.path
                                          none
                                          (Path.mk
                                            false
                                            [
                                              (PathSegment.mk
                                                "check_abi_compatibility"
                                                PathArguments.none)]))
                                        [
                                          (Expr.field
                                            (Expr.path
                                              none
                                              (Path.mk
                                                false
                                                [(PathSegment.mk "caller_field" PathArguments.none)]))
                                            (Member.unnamed 1)),
                                          (Expr.field
                                            (Expr.path
                                              none
                                              (Path.mk
                                                false
                                                [(PathSegment.mk "callee_field" PathArguments.none)]))
                                            (Member.unnamed 1))])))]))
                            BinOp.and
                            (Expr.binary
                              (Expr.path
                                none
                                (Path.mk false [(PathSegment.mk "caller_size" PathArguments.none)]))
                              BinOp.eq
                              (Expr.path
                                none
                                (Path.mk false [(PathSegment.mk "callee_size" PathArguments.none)]))))
                          BinOp.and
                          (Expr.binary
                            (Expr.path
                              none
                              (Path.mk false [(PathSegment.mk "caller_align" PathArguments.none)]))
                            BinOp.eq
                            (Expr.path
                              none
                              (Path.mk false [(PathSegment.mk "callee_align" PathArguments.none)]))))
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
                          (PathSegment.mk "Type" PathArguments.none),
                          (PathSegment.mk "Array" PathArguments.none)])
                      [
                        (FieldPat.mk
                          []
                          (Member.named "elem")
                          false
                          (Pat.ident false false "caller_elem" none)),
                        (FieldPat.mk
                          []
                          (Member.named "count")
                          false
                          (Pat.ident false false "caller_count" none))]
                      false),
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
                          false
                          (Pat.ident false false "callee_elem" none)),
                        (FieldPat.mk
                          []
                          (Member.named "count")
                          false
                          (Pat.ident false false "callee_count" none))]
                      false)])
                none
                (Expr.binary
                  (Expr.call
                    (Expr.path
                      none
                      (Path.mk
                        false
                        [(PathSegment.mk "check_abi_compatibility" PathArguments.none)]))
                    [
                      (Expr.path
                        none
                        (Path.mk false [(PathSegment.mk "caller_elem" PathArguments.none)])),
                      (Expr.path
                        none
                        (Path.mk false [(PathSegment.mk "callee_elem" PathArguments.none)]))])
                  BinOp.and
                  (Expr.binary
                    (Expr.path
                      none
                      (Path.mk false [(PathSegment.mk "caller_count" PathArguments.none)]))
                    BinOp.eq
                    (Expr.path
                      none
                      (Path.mk false [(PathSegment.mk "callee_count" PathArguments.none)]))))),
              (Arm.mk
                []
                (Pat.tuple
                  [
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
                          false
                          (Pat.ident false false "caller_fields" none)),
                        (FieldPat.mk
                          []
                          (Member.named "chunks")
                          false
                          (Pat.ident false false "caller_chunks" none)),
                        (FieldPat.mk
                          []
                          (Member.named "size")
                          false
                          (Pat.ident false false "caller_size" none)),
                        (FieldPat.mk
                          []
                          (Member.named "align")
                          false
                          (Pat.ident false false "caller_align" none))]
                      false),
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
                          false
                          (Pat.ident false false "callee_fields" none)),
                        (FieldPat.mk
                          []
                          (Member.named "chunks")
                          false
                          (Pat.ident false false "callee_chunks" none)),
                        (FieldPat.mk
                          []
                          (Member.named "size")
                          false
                          (Pat.ident false false "callee_size" none)),
                        (FieldPat.mk
                          []
                          (Member.named "align")
                          false
                          (Pat.ident false false "callee_align" none))]
                      false)])
                none
                (Expr.binary
                  (Expr.binary
                    (Expr.binary
                      (Expr.binary
                        (Expr.binary
                          (Expr.methodCall
                            (Expr.path
                              none
                              (Path.mk false [(PathSegment.mk "caller_fields" PathArguments.none)]))
                            "len"
                            none
                            [])
                          BinOp.eq
                          (Expr.methodCall
                            (Expr.path
                              none
                              (Path.mk false [(PathSegment.mk "callee_fields" PathArguments.none)]))
                            "len"
                            none
                            []))
                        BinOp.and
                        (Expr.methodCall
                          (Expr.methodCall
                            (Expr.path
                              none
                              (Path.mk false [(PathSegment.mk "caller_fields" PathArguments.none)]))
                            "zip"
                            none
                            [
                              (Expr.path
                                none
                                (Path.mk
                                  false
                                  [(PathSegment.mk "callee_fields" PathArguments.none)]))])
                          "all"
                          none
                          [
                            (Expr.closure
                              false
                              [
                                (Pat.tuple
                                  [
                                    (Pat.ident false false "caller_field" none),
                                    (Pat.ident false false "callee_field" none)])]
                              none
                              (Expr.binary
                                (Expr.binary
                                  (Expr.field
                                    (Expr.path
                                      none
                                      (Path.mk
                                        false
                                        [(PathSegment.mk "caller_field" PathArguments.none)]))
                                    (Member.unnamed 0))
                                  BinOp.eq
                                  (Expr.field
                                    (Expr.path
                                      none
                                      (Path.mk
                                        false
                                        [(PathSegment.mk "callee_field" PathArguments.none)]))
                                    (Member.unnamed 0)))
                                BinOp.and
                                (Expr.call
                                  (Expr.path
                                    none
                                    (Path.mk
                                      false
                                      [
                                        (PathSegment.mk
                                          "check_abi_compatibility"
                                          PathArguments.none)]))
                                  [
                                    (Expr.field
                                      (Expr.path
                                        none
                                        (Path.mk
                                          false
                                          [(PathSegment.mk "caller_field" PathArguments.none)]))
                                      (Member.unnamed 1)),
                                    (Expr.field
                                      (Expr.path
                                        none
                                        (Path.mk
                                          false
                                          [(PathSegment.mk "callee_field" PathArguments.none)]))
                                      (Member.unnamed 1))])))]))
                      BinOp.and
                      (Expr.binary
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "caller_chunks" PathArguments.none)]))
                        BinOp.eq
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "callee_chunks" PathArguments.none)]))))
                    BinOp.and
                    (Expr.binary
                      (Expr.path
                        none
                        (Path.mk false [(PathSegment.mk "caller_size" PathArguments.none)]))
                      BinOp.eq
                      (Expr.path
                        none
                        (Path.mk false [(PathSegment.mk "callee_size" PathArguments.none)]))))
                  BinOp.and
                  (Expr.binary
                    (Expr.path
                      none
                      (Path.mk false [(PathSegment.mk "caller_align" PathArguments.none)]))
                    BinOp.eq
                    (Expr.path
                      none
                      (Path.mk false [(PathSegment.mk "callee_align" PathArguments.none)]))))),
              (Arm.mk
                []
                (Pat.tuple
                  [
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
                          false
                          (Pat.ident false false "caller_variants" none)),
                        (FieldPat.mk
                          []
                          (Member.named "discriminator")
                          false
                          (Pat.ident false false "caller_discriminator" none)),
                        (FieldPat.mk
                          []
                          (Member.named "discriminant_ty")
                          false
                          (Pat.ident false false "caller_discriminant_ty" none)),
                        (FieldPat.mk
                          []
                          (Member.named "size")
                          false
                          (Pat.ident false false "caller_size" none)),
                        (FieldPat.mk
                          []
                          (Member.named "align")
                          false
                          (Pat.ident false false "caller_align" none))]
                      false),
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
                          false
                          (Pat.ident false false "callee_variants" none)),
                        (FieldPat.mk
                          []
                          (Member.named "discriminator")
                          false
                          (Pat.ident false false "callee_discriminator" none)),
                        (FieldPat.mk
                          []
                          (Member.named "discriminant_ty")
                          false
                          (Pat.ident false false "callee_discriminant_ty" none)),
                        (FieldPat.mk
                          []
                          (Member.named "size")
                          false
                          (Pat.ident false false "callee_size" none)),
                        (FieldPat.mk
                          []
                          (Member.named "align")
                          false
                          (Pat.ident false false "callee_align" none))]
                      false)])
                none
                (Expr.binary
                  (Expr.binary
                    (Expr.binary
                      (Expr.binary
                        (Expr.binary
                          (Expr.binary
                            (Expr.methodCall
                              (Expr.path
                                none
                                (Path.mk
                                  false
                                  [(PathSegment.mk "caller_variants" PathArguments.none)]))
                              "len"
                              none
                              [])
                            BinOp.eq
                            (Expr.methodCall
                              (Expr.path
                                none
                                (Path.mk
                                  false
                                  [(PathSegment.mk "callee_variants" PathArguments.none)]))
                              "len"
                              none
                              []))
                          BinOp.and
                          (Expr.methodCall
                            (Expr.methodCall
                              (Expr.path
                                none
                                (Path.mk
                                  false
                                  [(PathSegment.mk "caller_variants" PathArguments.none)]))
                              "iter"
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
                                      (Pat.ident false false "caller_discriminant" none),
                                      (Pat.ident false false "caller_variant" none)])]
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
                                          [(Pat.ident false false "callee_variant" none)])
                                        (some
                                          (Expr.methodCall
                                            (Expr.path
                                              none
                                              (Path.mk
                                                false
                                                [
                                                  (PathSegment.mk
                                                    "callee_variants"
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
                                                      "caller_discriminant"
                                                      PathArguments.none)]))]))
                                        (some
                                          (Expr.block
                                            none
                                            (Block.mk
                                              [
                                                (Stmt.expr
                                                  (Expr.returnExpr
                                                    (some (Expr.lit (Lit.bool false))))
                                                  true)])))),
                                      (Stmt.expr
                                        (Expr.binary
                                          (Expr.call
                                            (Expr.path
                                              none
                                              (Path.mk
                                                false
                                                [
                                                  (PathSegment.mk
                                                    "check_abi_compatibility"
                                                    PathArguments.none)]))
                                            [
                                              (Expr.field
                                                (Expr.path
                                                  none
                                                  (Path.mk
                                                    false
                                                    [
                                                      (PathSegment.mk
                                                        "caller_variant"
                                                        PathArguments.none)]))
                                                (Member.named "ty")),
                                              (Expr.field
                                                (Expr.path
                                                  none
                                                  (Path.mk
                                                    false
                                                    [
                                                      (PathSegment.mk
                                                        "callee_variant"
                                                        PathArguments.none)]))
                                                (Member.named "ty"))])
                                          BinOp.and
                                          (Expr.binary
                                            (Expr.field
                                              (Expr.path
                                                none
                                                (Path.mk
                                                  false
                                                  [
                                                    (PathSegment.mk
                                                      "caller_variant"
                                                      PathArguments.none)]))
                                              (Member.named "tagger"))
                                            BinOp.eq
                                            (Expr.field
                                              (Expr.path
                                                none
                                                (Path.mk
                                                  false
                                                  [
                                                    (PathSegment.mk
                                                      "callee_variant"
                                                      PathArguments.none)]))
                                              (Member.named "tagger"))))
                                        false)])))]))
                        BinOp.and
                        (Expr.binary
                          (Expr.path
                            none
                            (Path.mk
                              false
                              [(PathSegment.mk "caller_discriminator" PathArguments.none)]))
                          BinOp.eq
                          (Expr.path
                            none
                            (Path.mk
                              false
                              [(PathSegment.mk "callee_discriminator" PathArguments.none)]))))
                      BinOp.and
                      (Expr.binary
                        (Expr.path
                          none
                          (Path.mk
                            false
                            [(PathSegment.mk "caller_discriminant_ty" PathArguments.none)]))
                        BinOp.eq
                        (Expr.path
                          none
                          (Path.mk
                            false
                            [(PathSegment.mk "callee_discriminant_ty" PathArguments.none)]))))
                    BinOp.and
                    (Expr.binary
                      (Expr.path
                        none
                        (Path.mk false [(PathSegment.mk "caller_size" PathArguments.none)]))
                      BinOp.eq
                      (Expr.path
                        none
                        (Path.mk false [(PathSegment.mk "callee_size" PathArguments.none)]))))
                  BinOp.and
                  (Expr.binary
                    (Expr.path
                      none
                      (Path.mk false [(PathSegment.mk "caller_align" PathArguments.none)]))
                    BinOp.eq
                    (Expr.path
                      none
                      (Path.mk false [(PathSegment.mk "callee_align" PathArguments.none)]))))),
              (Arm.mk [] Pat.wild none (Expr.lit (Lit.bool false)))])
          false)]))

/-- `spec/lang/step/terminators.md:136` -/
def impl_Machine__prepare_for_inplace_passing : Item :=
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
              " Prepare a place for being used in-place as a function argument or return value."))]
        Visibility.inherited
        false
        (Signature.mk
          false
          false
          false
          none
          "prepare_for_inplace_passing"
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
          (some (Ty.path none (Path.mk false [(PathSegment.mk "NdResult" PathArguments.none)]))))
        (Block.mk
          [
            (Stmt.expr
              (Expr.tryExpr
                (Expr.methodCall
                  (Expr.field
                    (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                    (Member.named "mem"))
                  "deinit"
                  none
                  [
                    (Expr.field
                      (Expr.field
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "place" PathArguments.none)]))
                        (Member.named "ptr"))
                      (Member.named "thin_pointer")),
                    (Expr.methodCall
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
                        [])
                      "expect_size"
                      none
                      [(Expr.lit (Lit.str "WF ensures arguments and return types are sized"))]),
                    (Expr.methodCall
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
                        [])
                      "expect_align"
                      none
                      [(Expr.lit (Lit.str "WF ensures arguments and return types are sized"))])]))
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
            (AttrMeta.nameValue " A helper function to deal with `ArgumentExpr`."))]
        Visibility.inherited
        false
        (Signature.mk
          false
          false
          false
          none
          "eval_argument"
          (Generics.mk [] [])
          [
            (FnArg.receiver [] true none true none),
            (FnArg.typed
              []
              (Pat.ident false false "val" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "ArgumentExpr" PathArguments.none)])))]
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
                  (Expr.matchExpr
                    (Expr.path none (Path.mk false [(PathSegment.mk "val" PathArguments.none)]))
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
                        (Expr.block
                          none
                          (Block.mk
                            [
                              (Stmt.expr
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
                                        (Path.mk
                                          false
                                          [(PathSegment.mk "value" PathArguments.none)]))]))
                                false)]))),
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
                        (Expr.block
                          none
                          (Block.mk
                            [
                              (Stmt.letStmt
                                []
                                (Pat.tuple
                                  [
                                    (Pat.ident false false "place" none),
                                    (Pat.ident false false "ty" none)])
                                (some
                                  (Expr.tryExpr
                                    (Expr.methodCall
                                      (Expr.path
                                        none
                                        (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                                      "eval_place"
                                      none
                                      [
                                        (Expr.path
                                          none
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "place" PathArguments.none)]))])))
                                none),
                              (Stmt.letStmt
                                []
                                (Pat.ident false false "value" none)
                                (some
                                  (Expr.tryExpr
                                    (Expr.methodCall
                                      (Expr.path
                                        none
                                        (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                                      "place_load"
                                      none
                                      [
                                        (Expr.path
                                          none
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "place" PathArguments.none)])),
                                        (Expr.path
                                          none
                                          (Path.mk false [(PathSegment.mk "ty" PathArguments.none)]))])))
                                none),
                              (Stmt.expr
                                (Expr.tryExpr
                                  (Expr.methodCall
                                    (Expr.path
                                      none
                                      (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                                    "prepare_for_inplace_passing"
                                    none
                                    [
                                      (Expr.path
                                        none
                                        (Path.mk
                                          false
                                          [(PathSegment.mk "place" PathArguments.none)])),
                                      (Expr.path
                                        none
                                        (Path.mk false [(PathSegment.mk "ty" PathArguments.none)]))]))
                                true),
                              (Stmt.expr
                                (Expr.tuple
                                  [
                                    (Expr.path
                                      none
                                      (Path.mk false [(PathSegment.mk "value" PathArguments.none)])),
                                    (Expr.path
                                      none
                                      (Path.mk false [(PathSegment.mk "ty" PathArguments.none)]))])
                                false)])))])])
              false)])),
      (ImplItem.fn
        [
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue
              " Creates a stack frame for the given function, initializes the arguments,")),
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue
              " and ensures that calling convention and argument/return value ABIs are all matching up."))]
        Visibility.inherited
        false
        (Signature.mk
          false
          false
          false
          none
          "create_frame"
          (Generics.mk [] [])
          [
            (FnArg.receiver [] true none true none),
            (FnArg.typed
              []
              (Pat.ident false false "func" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "Function" PathArguments.none)]))),
            (FnArg.typed
              []
              (Pat.ident false false "stack_pop_action" none)
              (Ty.path
                none
                (Path.mk
                  false
                  [
                    (PathSegment.mk
                      "StackPopAction"
                      (PathArguments.angleBracketed
                        false
                        [
                          (GenericArgument.type
                            (Ty.path none (Path.mk false [(PathSegment.mk "M" PathArguments.none)])))]))]))),
            (FnArg.typed
              []
              (Pat.ident false false "caller_conv" none)
              (Ty.path
                none
                (Path.mk false [(PathSegment.mk "CallingConvention" PathArguments.none)]))),
            (FnArg.typed
              []
              (Pat.ident false false "caller_ret_ty" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "Type" PathArguments.none)]))),
            (FnArg.typed
              []
              (Pat.ident false false "caller_args" none)
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
                                  (Path.mk false [(PathSegment.mk "Type" PathArguments.none)]))]))]))])))]
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
                                  "StackFrame"
                                  (PathArguments.angleBracketed
                                    false
                                    [
                                      (GenericArgument.type
                                        (Ty.path
                                          none
                                          (Path.mk false [(PathSegment.mk "M" PathArguments.none)])))]))])))]))]))))
        (Block.mk
          [
            (Stmt.letStmt
              []
              (Pat.ident false true "frame" none)
              (some
                (Expr.struct
                  none
                  (Path.mk false [(PathSegment.mk "StackFrame" PathArguments.none)])
                  [
                    (FieldValue.mk
                      []
                      (Member.named "func")
                      true
                      (Expr.path none (Path.mk false [(PathSegment.mk "func" PathArguments.none)]))),
                    (FieldValue.mk
                      []
                      (Member.named "locals")
                      false
                      (Expr.call
                        (Expr.path
                          none
                          (Path.mk
                            false
                            [
                              (PathSegment.mk "Map" PathArguments.none),
                              (PathSegment.mk "new" PathArguments.none)]))
                        [])),
                    (FieldValue.mk
                      []
                      (Member.named "stack_pop_action")
                      true
                      (Expr.path
                        none
                        (Path.mk false [(PathSegment.mk "stack_pop_action" PathArguments.none)]))),
                    (FieldValue.mk
                      []
                      (Member.named "next_block")
                      false
                      (Expr.field
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "func" PathArguments.none)]))
                        (Member.named "start"))),
                    (FieldValue.mk
                      []
                      (Member.named "next_stmt")
                      false
                      (Expr.path
                        none
                        (Path.mk
                          false
                          [
                            (PathSegment.mk "Int" PathArguments.none),
                            (PathSegment.mk "ZERO" PathArguments.none)]))),
                    (FieldValue.mk
                      []
                      (Member.named "extra")
                      false
                      (Expr.call
                        (Expr.path
                          none
                          (Path.mk
                            false
                            [
                              (PathSegment.mk "M" PathArguments.none),
                              (PathSegment.mk "new_call" PathArguments.none)]))
                        []))]
                  false
                  none))
              none),
            (Stmt.expr
              (Expr.tryExpr
                (Expr.methodCall
                  (Expr.path none (Path.mk false [(PathSegment.mk "frame" PathArguments.none)]))
                  "storage_live"
                  none
                  [
                    (Expr.reference
                      true
                      (Expr.field
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                        (Member.named "mem"))),
                    (Expr.field
                      (Expr.path none (Path.mk false [(PathSegment.mk "func" PathArguments.none)]))
                      (Member.named "ret"))]))
              true),
            (Stmt.expr
              (Expr.forLoop
                none
                (Pat.ident false false "arg_local" none)
                (Expr.field
                  (Expr.path none (Path.mk false [(PathSegment.mk "func" PathArguments.none)]))
                  (Member.named "args"))
                (Block.mk
                  [
                    (Stmt.expr
                      (Expr.tryExpr
                        (Expr.methodCall
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "frame" PathArguments.none)]))
                          "storage_live"
                          none
                          [
                            (Expr.reference
                              true
                              (Expr.field
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                                (Member.named "mem"))),
                            (Expr.path
                              none
                              (Path.mk false [(PathSegment.mk "arg_local" PathArguments.none)]))]))
                      true)]))
              false),
            (Stmt.expr
              (Expr.ite
                (Expr.binary
                  (Expr.path
                    none
                    (Path.mk false [(PathSegment.mk "caller_conv" PathArguments.none)]))
                  BinOp.ne
                  (Expr.field
                    (Expr.path none (Path.mk false [(PathSegment.mk "func" PathArguments.none)]))
                    (Member.named "calling_convention")))
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
                              (Lit.str "call ABI violation: calling conventions are not the same"))]
                          false))
                      true)])
                none)
              false),
            (Stmt.expr
              (Expr.ite
                (Expr.unary
                  UnOp.not
                  (Expr.call
                    (Expr.path
                      none
                      (Path.mk
                        false
                        [(PathSegment.mk "check_abi_compatibility" PathArguments.none)]))
                    [
                      (Expr.path
                        none
                        (Path.mk false [(PathSegment.mk "caller_ret_ty" PathArguments.none)])),
                      (Expr.index
                        (Expr.field
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "func" PathArguments.none)]))
                          (Member.named "locals"))
                        (Expr.field
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "func" PathArguments.none)]))
                          (Member.named "ret")))]))
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
                              (Lit.str "call ABI violation: return types are not compatible"))]
                          false))
                      true)])
                none)
              false),
            (Stmt.expr
              (Expr.ite
                (Expr.binary
                  (Expr.methodCall
                    (Expr.field
                      (Expr.path none (Path.mk false [(PathSegment.mk "func" PathArguments.none)]))
                      (Member.named "args"))
                    "len"
                    none
                    [])
                  BinOp.ne
                  (Expr.methodCall
                    (Expr.path
                      none
                      (Path.mk false [(PathSegment.mk "caller_args" PathArguments.none)]))
                    "len"
                    none
                    []))
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
                              (Lit.str "call ABI violation: number of arguments does not agree"))]
                          false))
                      true)])
                none)
              false),
            (Stmt.expr
              (Expr.forLoop
                none
                (Pat.tuple
                  [
                    (Pat.ident false false "callee_local" none),
                    (Pat.tuple
                      [
                        (Pat.ident false false "caller_val" none),
                        (Pat.ident false false "caller_ty" none)])])
                (Expr.methodCall
                  (Expr.field
                    (Expr.path none (Path.mk false [(PathSegment.mk "func" PathArguments.none)]))
                    (Member.named "args"))
                  "zip"
                  none
                  [
                    (Expr.path
                      none
                      (Path.mk false [(PathSegment.mk "caller_args" PathArguments.none)]))])
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
                                [(PathSegment.mk "check_abi_compatibility" PathArguments.none)]))
                            [
                              (Expr.path
                                none
                                (Path.mk false [(PathSegment.mk "caller_ty" PathArguments.none)])),
                              (Expr.index
                                (Expr.field
                                  (Expr.path
                                    none
                                    (Path.mk false [(PathSegment.mk "func" PathArguments.none)]))
                                  (Member.named "locals"))
                                (Expr.path
                                  none
                                  (Path.mk
                                    false
                                    [(PathSegment.mk "callee_local" PathArguments.none)])))]))
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
                                        "call ABI violation: argument types are not compatible"))]
                                  false))
                              true)])
                        none)
                      false),
                    (Stmt.letStmt
                      []
                      (Pat.ident false false "align" none)
                      (some
                        (Expr.methodCall
                          (Expr.methodCall
                            (Expr.path
                              none
                              (Path.mk false [(PathSegment.mk "caller_ty" PathArguments.none)]))
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
                          "expect_align"
                          none
                          [(Expr.lit (Lit.str "WF ensures function arguments are sized"))]))
                      none),
                    (Stmt.expr
                      (Expr.methodCall
                        (Expr.methodCall
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                          "typed_store"
                          none
                          [
                            (Expr.index
                              (Expr.field
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "frame" PathArguments.none)]))
                                (Member.named "locals"))
                              (Expr.path
                                none
                                (Path.mk false [(PathSegment.mk "callee_local" PathArguments.none)]))),
                            (Expr.path
                              none
                              (Path.mk false [(PathSegment.mk "caller_val" PathArguments.none)])),
                            (Expr.path
                              none
                              (Path.mk false [(PathSegment.mk "caller_ty" PathArguments.none)])),
                            (Expr.path
                              none
                              (Path.mk false [(PathSegment.mk "align" PathArguments.none)])),
                            (Expr.path
                              none
                              (Path.mk
                                false
                                [
                                  (PathSegment.mk "Atomicity" PathArguments.none),
                                  (PathSegment.mk "None" PathArguments.none)]))])
                        "unwrap"
                        none
                        [])
                      true)]))
              false),
            (Stmt.expr
              (Expr.call
                (Expr.path none (Path.mk false [(PathSegment.mk "ret" PathArguments.none)]))
                [(Expr.path none (Path.mk false [(PathSegment.mk "frame" PathArguments.none)]))])
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
          "eval_call"
          (Generics.mk [] [])
          [
            (FnArg.receiver [] true none true none),
            (FnArg.typed
              []
              (Pat.ident false false "callee" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "Function" PathArguments.none)]))),
            (FnArg.typed
              []
              (Pat.ident false false "caller_conv" none)
              (Ty.path
                none
                (Path.mk false [(PathSegment.mk "CallingConvention" PathArguments.none)]))),
            (FnArg.typed
              []
              (Pat.ident false false "arguments" none)
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
                                  (Path.mk false [(PathSegment.mk "Type" PathArguments.none)]))]))]))]))),
            (FnArg.typed
              []
              (Pat.ident false false "caller_ret" none)
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
                                  (Path.mk false [(PathSegment.mk "M" PathArguments.none)])))]))])),
                  (Ty.path none (Path.mk false [(PathSegment.mk "Type" PathArguments.none)]))])),
            (FnArg.typed
              []
              (Pat.ident false false "next_block" none)
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
                              (Path.mk false [(PathSegment.mk "BbName" PathArguments.none)])))]))]))),
            (FnArg.typed
              []
              (Pat.ident false false "unwind_block" none)
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
                              (Path.mk false [(PathSegment.mk "BbName" PathArguments.none)])))]))])))]
          false
          (some (Ty.path none (Path.mk false [(PathSegment.mk "NdResult" PathArguments.none)]))))
        (Block.mk
          [
            (Stmt.letStmt
              []
              (Pat.tuple
                [
                  (Pat.ident false false "caller_ret_place" none),
                  (Pat.ident false false "caller_ret_ty" none)])
              (some
                (Expr.path none (Path.mk false [(PathSegment.mk "caller_ret" PathArguments.none)])))
              none),
            (Stmt.letStmt
              []
              (Pat.ident false false "stack_pop_action" none)
              (some
                (Expr.struct
                  none
                  (Path.mk
                    false
                    [
                      (PathSegment.mk "StackPopAction" PathArguments.none),
                      (PathSegment.mk "BackToCaller" PathArguments.none)])
                  [
                    (FieldValue.mk
                      []
                      (Member.named "next_block")
                      true
                      (Expr.path
                        none
                        (Path.mk false [(PathSegment.mk "next_block" PathArguments.none)]))),
                    (FieldValue.mk
                      []
                      (Member.named "unwind_block")
                      true
                      (Expr.path
                        none
                        (Path.mk false [(PathSegment.mk "unwind_block" PathArguments.none)]))),
                    (FieldValue.mk
                      []
                      (Member.named "ret_val_ptr")
                      false
                      (Expr.field
                        (Expr.field
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "caller_ret_place" PathArguments.none)]))
                          (Member.named "ptr"))
                        (Member.named "thin_pointer")))]
                  false
                  none))
              none),
            (Stmt.letStmt
              []
              (Pat.ident false false "frame" none)
              (some
                (Expr.tryExpr
                  (Expr.methodCall
                    (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                    "create_frame"
                    none
                    [
                      (Expr.path
                        none
                        (Path.mk false [(PathSegment.mk "callee" PathArguments.none)])),
                      (Expr.path
                        none
                        (Path.mk false [(PathSegment.mk "stack_pop_action" PathArguments.none)])),
                      (Expr.path
                        none
                        (Path.mk false [(PathSegment.mk "caller_conv" PathArguments.none)])),
                      (Expr.path
                        none
                        (Path.mk false [(PathSegment.mk "caller_ret_ty" PathArguments.none)])),
                      (Expr.path
                        none
                        (Path.mk false [(PathSegment.mk "arguments" PathArguments.none)]))])))
              none),
            (Stmt.expr
              (Expr.methodCall
                (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                "mutate_cur_stack"
                none
                [
                  (Expr.closure
                    false
                    [(Pat.ident false false "stack" none)]
                    none
                    (Expr.methodCall
                      (Expr.path none (Path.mk false [(PathSegment.mk "stack" PathArguments.none)]))
                      "push"
                      none
                      [
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "frame" PathArguments.none)]))]))])
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
          "eval_terminator"
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
                    (PathSegment.mk "Terminator" PathArguments.none),
                    (PathSegment.mk "Call" PathArguments.none)])
                [
                  (FieldPat.mk
                    []
                    (Member.named "callee")
                    true
                    (Pat.ident false false "callee" none)),
                  (FieldPat.mk
                    []
                    (Member.named "calling_convention")
                    false
                    (Pat.ident false false "caller_conv" none)),
                  (FieldPat.mk
                    []
                    (Member.named "arguments")
                    true
                    (Pat.ident false false "arguments" none)),
                  (FieldPat.mk
                    []
                    (Member.named "ret")
                    false
                    (Pat.ident false false "ret_expr" none)),
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
              (Ty.path none (Path.mk false [(PathSegment.mk "Terminator" PathArguments.none)])))]
          false
          (some (Ty.path none (Path.mk false [(PathSegment.mk "NdResult" PathArguments.none)]))))
        (Block.mk
          [
            (Stmt.letStmt
              []
              (Pat.tuple
                [(Pat.ident false false "ret_place" none), (Pat.ident false false "ret_ty" none)])
              (some
                (Expr.tryExpr
                  (Expr.methodCall
                    (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                    "eval_place"
                    none
                    [
                      (Expr.path
                        none
                        (Path.mk false [(PathSegment.mk "ret_expr" PathArguments.none)]))])))
              none),
            (Stmt.expr
              (Expr.tryExpr
                (Expr.methodCall
                  (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                  "prepare_for_inplace_passing"
                  none
                  [
                    (Expr.path
                      none
                      (Path.mk false [(PathSegment.mk "ret_place" PathArguments.none)])),
                    (Expr.path none (Path.mk false [(PathSegment.mk "ret_ty" PathArguments.none)]))]))
              true),
            (Stmt.letStmt
              []
              (Pat.tuple [(Pat.ident false false "callee_val" none), Pat.wild])
              (some
                (Expr.tryExpr
                  (Expr.methodCall
                    (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                    "eval_value"
                    none
                    [
                      (Expr.path
                        none
                        (Path.mk false [(PathSegment.mk "callee" PathArguments.none)]))])))
              none),
            (Stmt.letStmt
              []
              (Pat.ident false false "callee" none)
              (some
                (Expr.tryExpr
                  (Expr.methodCall
                    (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                    "fn_from_ptr"
                    none
                    [
                      (Expr.path
                        none
                        (Path.mk false [(PathSegment.mk "callee_val" PathArguments.none)]))])))
              none),
            (Stmt.letStmt
              []
              (Pat.ident false false "arguments" none)
              (some
                (Expr.tryExpr
                  (Expr.methodCall
                    (Expr.path
                      none
                      (Path.mk false [(PathSegment.mk "arguments" PathArguments.none)]))
                    "try_map"
                    none
                    [
                      (Expr.closure
                        false
                        [(Pat.ident false false "arg" none)]
                        none
                        (Expr.methodCall
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                          "eval_argument"
                          none
                          [
                            (Expr.path
                              none
                              (Path.mk false [(PathSegment.mk "arg" PathArguments.none)]))]))])))
              none),
            (Stmt.expr
              (Expr.methodCall
                (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                "eval_call"
                none
                [
                  (Expr.path none (Path.mk false [(PathSegment.mk "callee" PathArguments.none)])),
                  (Expr.path
                    none
                    (Path.mk false [(PathSegment.mk "caller_conv" PathArguments.none)])),
                  (Expr.path none (Path.mk false [(PathSegment.mk "arguments" PathArguments.none)])),
                  (Expr.tuple
                    [
                      (Expr.path
                        none
                        (Path.mk false [(PathSegment.mk "ret_place" PathArguments.none)])),
                      (Expr.path
                        none
                        (Path.mk false [(PathSegment.mk "ret_ty" PathArguments.none)]))]),
                  (Expr.path
                    none
                    (Path.mk false [(PathSegment.mk "next_block" PathArguments.none)])),
                  (Expr.path
                    none
                    (Path.mk false [(PathSegment.mk "unwind_block" PathArguments.none)]))])
              false)]))])

/-- `spec/lang/step/terminators.md:298` -/
def impl_Machine__terminate_active_thread : Item :=
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
          "terminate_active_thread"
          (Generics.mk [] [])
          [(FnArg.receiver [] true none true none)]
          false
          (some (Ty.path none (Path.mk false [(PathSegment.mk "NdResult" PathArguments.none)]))))
        (Block.mk
          [
            (Stmt.letStmt
              []
              (Pat.ident false false "active" none)
              (some
                (Expr.field
                  (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                  (Member.named "active_thread")))
              none),
            (Stmt.expr
              (Expr.ite
                (Expr.binary
                  (Expr.path none (Path.mk false [(PathSegment.mk "active" PathArguments.none)]))
                  BinOp.eq
                  (Expr.lit (Lit.int 0 "")))
                (Block.mk
                  [
                    (Stmt.macro
                      []
                      (Macro.mk
                        (Path.mk false [(PathSegment.mk "throw_ub" PathArguments.none)])
                        MacroDelimiter.paren
                        (MacroBody.exprs
                          [(Expr.lit (Lit.str "the start function must not return"))]
                          false))
                      true)])
                none)
              false),
            (Stmt.expr
              (Expr.methodCall
                (Expr.field
                  (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                  (Member.named "threads"))
                "mutate_at"
                none
                [
                  (Expr.path none (Path.mk false [(PathSegment.mk "active" PathArguments.none)])),
                  (Expr.closure
                    false
                    [(Pat.ident false false "thread" none)]
                    none
                    (Expr.block
                      none
                      (Block.mk
                        [
                          (Stmt.macro
                            []
                            (Macro.mk
                              (Path.mk false [(PathSegment.mk "assert" PathArguments.none)])
                              MacroDelimiter.paren
                              (MacroBody.exprs
                                [
                                  (Expr.binary
                                    (Expr.methodCall
                                      (Expr.field
                                        (Expr.path
                                          none
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "thread" PathArguments.none)]))
                                        (Member.named "stack"))
                                      "len"
                                      none
                                      [])
                                    BinOp.eq
                                    (Expr.lit (Lit.int 0 "")))]
                                false))
                            true),
                          (Stmt.expr
                            (Expr.assign
                              (Expr.field
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "thread" PathArguments.none)]))
                                (Member.named "state"))
                              (Expr.path
                                none
                                (Path.mk
                                  false
                                  [
                                    (PathSegment.mk "ThreadState" PathArguments.none),
                                    (PathSegment.mk "Terminated" PathArguments.none)])))
                            true)])))])
              true),
            (Stmt.expr
              (Expr.forLoop
                none
                (Pat.ident false false "i" none)
                (Expr.range
                  (some
                    (Expr.path
                      none
                      (Path.mk
                        false
                        [
                          (PathSegment.mk "ThreadId" PathArguments.none),
                          (PathSegment.mk "ZERO" PathArguments.none)])))
                  RangeLimits.halfOpen
                  (some
                    (Expr.methodCall
                      (Expr.field
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                        (Member.named "threads"))
                      "len"
                      none
                      [])))
                (Block.mk
                  [
                    (Stmt.expr
                      (Expr.ite
                        (Expr.binary
                          (Expr.field
                            (Expr.index
                              (Expr.field
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                                (Member.named "threads"))
                              (Expr.path
                                none
                                (Path.mk false [(PathSegment.mk "i" PathArguments.none)])))
                            (Member.named "state"))
                          BinOp.eq
                          (Expr.call
                            (Expr.path
                              none
                              (Path.mk
                                false
                                [
                                  (PathSegment.mk "ThreadState" PathArguments.none),
                                  (PathSegment.mk "BlockedOnJoin" PathArguments.none)]))
                            [
                              (Expr.path
                                none
                                (Path.mk false [(PathSegment.mk "active" PathArguments.none)]))]))
                        (Block.mk
                          [
                            (Stmt.expr
                              (Expr.methodCall
                                (Expr.field
                                  (Expr.path
                                    none
                                    (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                                  (Member.named "synchronized_threads"))
                                "insert"
                                none
                                [
                                  (Expr.path
                                    none
                                    (Path.mk false [(PathSegment.mk "i" PathArguments.none)]))])
                              true),
                            (Stmt.expr
                              (Expr.methodCall
                                (Expr.field
                                  (Expr.path
                                    none
                                    (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                                  (Member.named "threads"))
                                "mutate_at"
                                none
                                [
                                  (Expr.path
                                    none
                                    (Path.mk false [(PathSegment.mk "i" PathArguments.none)])),
                                  (Expr.closure
                                    false
                                    [(Pat.ident false false "thread" none)]
                                    none
                                    (Expr.assign
                                      (Expr.field
                                        (Expr.path
                                          none
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "thread" PathArguments.none)]))
                                        (Member.named "state"))
                                      (Expr.path
                                        none
                                        (Path.mk
                                          false
                                          [
                                            (PathSegment.mk "ThreadState" PathArguments.none),
                                            (PathSegment.mk "Enabled" PathArguments.none)]))))])
                              false)])
                        none)
                      false)]))
              false),
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
          "eval_terminator"
          (Generics.mk [] [])
          [
            (FnArg.receiver [] true none true none),
            (FnArg.typed
              []
              (Pat.path
                none
                (Path.mk
                  false
                  [
                    (PathSegment.mk "Terminator" PathArguments.none),
                    (PathSegment.mk "Return" PathArguments.none)]))
              (Ty.path none (Path.mk false [(PathSegment.mk "Terminator" PathArguments.none)])))]
          false
          (some (Ty.path none (Path.mk false [(PathSegment.mk "NdResult" PathArguments.none)]))))
        (Block.mk
          [
            (Stmt.letStmt
              []
              (Pat.ident false true "frame" none)
              (some
                (Expr.methodCall
                  (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                  "mutate_cur_stack"
                  none
                  [
                    (Expr.closure
                      false
                      [(Pat.ident false false "stack" none)]
                      none
                      (Expr.methodCall
                        (Expr.methodCall
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "stack" PathArguments.none)]))
                          "pop"
                          none
                          [])
                        "unwrap"
                        none
                        []))]))
              none),
            (Stmt.letStmt
              []
              (Pat.ident false false "callee_ty" none)
              (some
                (Expr.index
                  (Expr.field
                    (Expr.field
                      (Expr.path none (Path.mk false [(PathSegment.mk "frame" PathArguments.none)]))
                      (Member.named "func"))
                    (Member.named "locals"))
                  (Expr.field
                    (Expr.field
                      (Expr.path none (Path.mk false [(PathSegment.mk "frame" PathArguments.none)]))
                      (Member.named "func"))
                    (Member.named "ret"))))
              none),
            (Stmt.letStmt
              []
              (Pat.ident false false "align" none)
              (some
                (Expr.methodCall
                  (Expr.methodCall
                    (Expr.path
                      none
                      (Path.mk false [(PathSegment.mk "callee_ty" PathArguments.none)]))
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
                  "expect_align"
                  none
                  [(Expr.lit (Lit.str "the return value is a local and thus sized"))]))
              none),
            (Stmt.letStmt
              []
              (Pat.ident false false "ret_val" none)
              (some
                (Expr.tryExpr
                  (Expr.methodCall
                    (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                    "typed_load"
                    none
                    [
                      (Expr.index
                        (Expr.field
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "frame" PathArguments.none)]))
                          (Member.named "locals"))
                        (Expr.field
                          (Expr.field
                            (Expr.path
                              none
                              (Path.mk false [(PathSegment.mk "frame" PathArguments.none)]))
                            (Member.named "func"))
                          (Member.named "ret"))),
                      (Expr.path
                        none
                        (Path.mk false [(PathSegment.mk "callee_ty" PathArguments.none)])),
                      (Expr.path none (Path.mk false [(PathSegment.mk "align" PathArguments.none)])),
                      (Expr.path
                        none
                        (Path.mk
                          false
                          [
                            (PathSegment.mk "Atomicity" PathArguments.none),
                            (PathSegment.mk "None" PathArguments.none)]))])))
              none),
            (Stmt.expr
              (Expr.whileLoop
                none
                (Expr.letCond
                  (Pat.tupleStruct
                    none
                    (Path.mk false [(PathSegment.mk "Some" PathArguments.none)])
                    [(Pat.ident false false "local" none)])
                  (Expr.methodCall
                    (Expr.methodCall
                      (Expr.field
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "frame" PathArguments.none)]))
                        (Member.named "locals"))
                      "keys"
                      none
                      [])
                    "next"
                    none
                    []))
                (Block.mk
                  [
                    (Stmt.expr
                      (Expr.tryExpr
                        (Expr.methodCall
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "frame" PathArguments.none)]))
                          "storage_dead"
                          none
                          [
                            (Expr.reference
                              true
                              (Expr.field
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                                (Member.named "mem"))),
                            (Expr.path
                              none
                              (Path.mk false [(PathSegment.mk "local" PathArguments.none)]))]))
                      true)]))
              false),
            (Stmt.expr
              (Expr.tryExpr
                (Expr.methodCall
                  (Expr.field
                    (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                    (Member.named "mem"))
                  "end_call"
                  none
                  [
                    (Expr.field
                      (Expr.path none (Path.mk false [(PathSegment.mk "frame" PathArguments.none)]))
                      (Member.named "extra"))]))
              true),
            (Stmt.expr
              (Expr.matchExpr
                (Expr.field
                  (Expr.path none (Path.mk false [(PathSegment.mk "frame" PathArguments.none)]))
                  (Member.named "stack_pop_action"))
                [
                  (Arm.mk
                    []
                    (Pat.path
                      none
                      (Path.mk
                        false
                        [
                          (PathSegment.mk "StackPopAction" PathArguments.none),
                          (PathSegment.mk "BottomOfStack" PathArguments.none)]))
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
                                  (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                                "terminate_active_thread"
                                none
                                []))
                            true)]))),
                  (Arm.mk
                    []
                    (Pat.struct
                      none
                      (Path.mk
                        false
                        [
                          (PathSegment.mk "StackPopAction" PathArguments.none),
                          (PathSegment.mk "BackToCaller" PathArguments.none)])
                      [
                        (FieldPat.mk
                          []
                          (Member.named "ret_val_ptr")
                          false
                          (Pat.ident false false "caller_ret_ptr" none)),
                        (FieldPat.mk
                          []
                          (Member.named "next_block")
                          true
                          (Pat.ident false false "next_block" none))]
                      true)
                    none
                    (Expr.block
                      none
                      (Block.mk
                        [
                          (Stmt.macro
                            []
                            (Macro.mk
                              (Path.mk false [(PathSegment.mk "assert" PathArguments.none)])
                              MacroDelimiter.paren
                              (MacroBody.exprs
                                [
                                  (Expr.binary
                                    (Expr.methodCall
                                      (Expr.field
                                        (Expr.methodCall
                                          (Expr.path
                                            none
                                            (Path.mk
                                              false
                                              [(PathSegment.mk "self" PathArguments.none)]))
                                          "active_thread"
                                          none
                                          [])
                                        (Member.named "stack"))
                                      "len"
                                      none
                                      [])
                                    BinOp.gt
                                    (Expr.lit (Lit.int 0 "")))]
                                false))
                            true),
                          (Stmt.expr
                            (Expr.tryExpr
                              (Expr.methodCall
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                                "typed_store"
                                none
                                [
                                  (Expr.path
                                    none
                                    (Path.mk
                                      false
                                      [(PathSegment.mk "caller_ret_ptr" PathArguments.none)])),
                                  (Expr.path
                                    none
                                    (Path.mk false [(PathSegment.mk "ret_val" PathArguments.none)])),
                                  (Expr.path
                                    none
                                    (Path.mk
                                      false
                                      [(PathSegment.mk "callee_ty" PathArguments.none)])),
                                  (Expr.path
                                    none
                                    (Path.mk false [(PathSegment.mk "align" PathArguments.none)])),
                                  (Expr.path
                                    none
                                    (Path.mk
                                      false
                                      [
                                        (PathSegment.mk "Atomicity" PathArguments.none),
                                        (PathSegment.mk "None" PathArguments.none)]))]))
                            true),
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
                                            [(PathSegment.mk "self" PathArguments.none)]))
                                        "jump_to_block"
                                        none
                                        [
                                          (Expr.path
                                            none
                                            (Path.mk
                                              false
                                              [(PathSegment.mk "next_block" PathArguments.none)]))]))
                                    true)])
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
                                            [(PathSegment.mk "throw_ub" PathArguments.none)])
                                          MacroDelimiter.paren
                                          (MacroBody.exprs
                                            [
                                              (Expr.lit
                                                (Lit.str
                                                  "return from a function where caller did not specify next block"))]
                                            false))
                                        true)]))))
                            false)])))])
              false),
            (Stmt.expr
              (Expr.call
                (Expr.path none (Path.mk false [(PathSegment.mk "ret" PathArguments.none)]))
                [(Expr.tuple [])])
              false)]))])

/-- `spec/lang/step/terminators.md:385` -/
def impl_Machine__eval_terminator_3 : Item :=
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
          "eval_terminator"
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
                    (PathSegment.mk "Terminator" PathArguments.none),
                    (PathSegment.mk "StartUnwind" PathArguments.none)])
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
              (Ty.path none (Path.mk false [(PathSegment.mk "Terminator" PathArguments.none)])))]
          false
          (some (Ty.path none (Path.mk false [(PathSegment.mk "NdResult" PathArguments.none)]))))
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
                    [(Pat.ident false false "unwind_payload" none)]),
                  (Pat.tupleStruct
                    none
                    (Path.mk
                      false
                      [
                        (PathSegment.mk "Type" PathArguments.none),
                        (PathSegment.mk "Ptr" PathArguments.none)])
                    [
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
                            false
                            (Pat.path
                              none
                              (Path.mk
                                false
                                [
                                  (PathSegment.mk "PointerMetaKind" PathArguments.none),
                                  (PathSegment.mk "None" PathArguments.none)])))]
                        false)])])
              (some
                (Expr.tryExpr
                  (Expr.methodCall
                    (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                    "eval_value"
                    none
                    [
                      (Expr.path
                        none
                        (Path.mk false [(PathSegment.mk "unwind_payload" PathArguments.none)]))])))
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
                            [
                              (Expr.lit
                                (Lit.str "StartUnwind: the unwind payload is not a raw pointer"))]
                            false))
                        true)])))),
            (Stmt.expr
              (Expr.methodCall
                (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                "mutate_active_thread"
                none
                [
                  (Expr.closure
                    false
                    [(Pat.ident false false "thread" none)]
                    none
                    (Expr.block
                      none
                      (Block.mk
                        [
                          (Stmt.expr
                            (Expr.methodCall
                              (Expr.field
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "thread" PathArguments.none)]))
                                (Member.named "unwind_payloads"))
                              "push"
                              none
                              [
                                (Expr.field
                                  (Expr.path
                                    none
                                    (Path.mk
                                      false
                                      [(PathSegment.mk "unwind_payload" PathArguments.none)]))
                                  (Member.named "thin_pointer"))])
                            false)])))])
              true),
            (Stmt.expr
              (Expr.tryExpr
                (Expr.methodCall
                  (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                  "jump_to_block"
                  none
                  [
                    (Expr.path
                      none
                      (Path.mk false [(PathSegment.mk "unwind_block" PathArguments.none)]))]))
              true),
            (Stmt.expr
              (Expr.call
                (Expr.path none (Path.mk false [(PathSegment.mk "ret" PathArguments.none)]))
                [(Expr.tuple [])])
              false)]))])

/-- `spec/lang/step/terminators.md:406` -/
def impl_Machine__eval_terminator_4 : Item :=
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
          "eval_terminator"
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
                    (PathSegment.mk "Terminator" PathArguments.none),
                    (PathSegment.mk "StopUnwind" PathArguments.none)])
                [(Pat.ident false false "block_name" none)])
              (Ty.path none (Path.mk false [(PathSegment.mk "Terminator" PathArguments.none)])))]
          false
          (some (Ty.path none (Path.mk false [(PathSegment.mk "NdResult" PathArguments.none)]))))
        (Block.mk
          [
            (Stmt.expr
              (Expr.tryExpr
                (Expr.methodCall
                  (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                  "mutate_active_thread"
                  none
                  [
                    (Expr.closure
                      false
                      [(Pat.ident false false "thread" none)]
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
                                  [(GenericArgument.type (Ty.tuple []))]))])))
                      (Expr.block
                        none
                        (Block.mk
                          [
                            (Stmt.letStmt
                              []
                              (Pat.tupleStruct
                                none
                                (Path.mk false [(PathSegment.mk "Some" PathArguments.none)])
                                [Pat.wild])
                              (some
                                (Expr.methodCall
                                  (Expr.field
                                    (Expr.path
                                      none
                                      (Path.mk false [(PathSegment.mk "thread" PathArguments.none)]))
                                    (Member.named "unwind_payloads"))
                                  "pop"
                                  none
                                  []))
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
                                            [(PathSegment.mk "throw_ub" PathArguments.none)])
                                          MacroDelimiter.paren
                                          (MacroBody.exprs
                                            [
                                              (Expr.lit
                                                (Lit.str "StopUnwind: the payload stack is empty"))]
                                            false))
                                        true)])))),
                            (Stmt.expr
                              (Expr.call
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "ret" PathArguments.none)]))
                                [(Expr.tuple [])])
                              false)])))]))
              true),
            (Stmt.expr
              (Expr.tryExpr
                (Expr.methodCall
                  (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                  "jump_to_block"
                  none
                  [
                    (Expr.path
                      none
                      (Path.mk false [(PathSegment.mk "block_name" PathArguments.none)]))]))
              true),
            (Stmt.expr
              (Expr.call
                (Expr.path none (Path.mk false [(PathSegment.mk "ret" PathArguments.none)]))
                [(Expr.tuple [])])
              false)]))])

/-- `spec/lang/step/terminators.md:423` -/
def impl_Machine__eval_terminator_5 : Item :=
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
          "eval_terminator"
          (Generics.mk [] [])
          [
            (FnArg.receiver [] true none true none),
            (FnArg.typed
              []
              (Pat.path
                none
                (Path.mk
                  false
                  [
                    (PathSegment.mk "Terminator" PathArguments.none),
                    (PathSegment.mk "ResumeUnwind" PathArguments.none)]))
              (Ty.path none (Path.mk false [(PathSegment.mk "Terminator" PathArguments.none)])))]
          false
          (some (Ty.path none (Path.mk false [(PathSegment.mk "NdResult" PathArguments.none)]))))
        (Block.mk
          [
            (Stmt.letStmt
              []
              (Pat.ident false true "frame" none)
              (some
                (Expr.methodCall
                  (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                  "mutate_cur_stack"
                  none
                  [
                    (Expr.closure
                      false
                      [(Pat.ident false false "stack" none)]
                      none
                      (Expr.methodCall
                        (Expr.methodCall
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "stack" PathArguments.none)]))
                          "pop"
                          none
                          [])
                        "unwrap"
                        none
                        []))]))
              none),
            (Stmt.expr
              (Expr.whileLoop
                none
                (Expr.letCond
                  (Pat.tupleStruct
                    none
                    (Path.mk false [(PathSegment.mk "Some" PathArguments.none)])
                    [(Pat.ident false false "local" none)])
                  (Expr.methodCall
                    (Expr.methodCall
                      (Expr.field
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "frame" PathArguments.none)]))
                        (Member.named "locals"))
                      "keys"
                      none
                      [])
                    "next"
                    none
                    []))
                (Block.mk
                  [
                    (Stmt.expr
                      (Expr.tryExpr
                        (Expr.methodCall
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "frame" PathArguments.none)]))
                          "storage_dead"
                          none
                          [
                            (Expr.reference
                              true
                              (Expr.field
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                                (Member.named "mem"))),
                            (Expr.path
                              none
                              (Path.mk false [(PathSegment.mk "local" PathArguments.none)]))]))
                      true)]))
              false),
            (Stmt.expr
              (Expr.tryExpr
                (Expr.methodCall
                  (Expr.field
                    (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                    (Member.named "mem"))
                  "end_call"
                  none
                  [
                    (Expr.field
                      (Expr.path none (Path.mk false [(PathSegment.mk "frame" PathArguments.none)]))
                      (Member.named "extra"))]))
              true),
            (Stmt.expr
              (Expr.matchExpr
                (Expr.field
                  (Expr.path none (Path.mk false [(PathSegment.mk "frame" PathArguments.none)]))
                  (Member.named "stack_pop_action"))
                [
                  (Arm.mk
                    []
                    (Pat.path
                      none
                      (Path.mk
                        false
                        [
                          (PathSegment.mk "StackPopAction" PathArguments.none),
                          (PathSegment.mk "BottomOfStack" PathArguments.none)]))
                    none
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
                                      "the function at the bottom of the stack must not unwind"))]
                                false))
                            true)]))),
                  (Arm.mk
                    []
                    (Pat.struct
                      none
                      (Path.mk
                        false
                        [
                          (PathSegment.mk "StackPopAction" PathArguments.none),
                          (PathSegment.mk "BackToCaller" PathArguments.none)])
                      [
                        (FieldPat.mk
                          []
                          (Member.named "unwind_block")
                          true
                          (Pat.ident false false "unwind_block" none))]
                      true)
                    none
                    (Expr.block
                      none
                      (Block.mk
                        [
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
                                            [(PathSegment.mk "self" PathArguments.none)]))
                                        "jump_to_block"
                                        none
                                        [
                                          (Expr.path
                                            none
                                            (Path.mk
                                              false
                                              [(PathSegment.mk "unwind_block" PathArguments.none)]))]))
                                    true)])
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
                                            [(PathSegment.mk "throw_ub" PathArguments.none)])
                                          MacroDelimiter.paren
                                          (MacroBody.exprs
                                            [
                                              (Expr.lit
                                                (Lit.str
                                                  "unwinding from a function where the caller did not specify an unwind_block"))]
                                            false))
                                        true)]))))
                            false)])))])
              false),
            (Stmt.expr
              (Expr.call
                (Expr.path none (Path.mk false [(PathSegment.mk "ret" PathArguments.none)]))
                [(Expr.tuple [])])
              false)]))])

/-- `spec/lang/step/terminators.md:461` -/
def impl_Machine__eval_terminator_6 : Item :=
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
          "eval_terminator"
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
                    (PathSegment.mk "Terminator" PathArguments.none),
                    (PathSegment.mk "Intrinsic" PathArguments.none)])
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
                    false
                    (Pat.ident false false "ret_expr" none)),
                  (FieldPat.mk
                    []
                    (Member.named "next_block")
                    true
                    (Pat.ident false false "next_block" none))]
                false)
              (Ty.path none (Path.mk false [(PathSegment.mk "Terminator" PathArguments.none)])))]
          false
          (some (Ty.path none (Path.mk false [(PathSegment.mk "NdResult" PathArguments.none)]))))
        (Block.mk
          [
            (Stmt.letStmt
              []
              (Pat.tuple
                [(Pat.ident false false "ret_place" none), (Pat.ident false false "ret_ty" none)])
              (some
                (Expr.tryExpr
                  (Expr.methodCall
                    (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                    "eval_place"
                    none
                    [
                      (Expr.path
                        none
                        (Path.mk false [(PathSegment.mk "ret_expr" PathArguments.none)]))])))
              none),
            (Stmt.letStmt
              []
              (Pat.ident false false "arguments" none)
              (some
                (Expr.tryExpr
                  (Expr.methodCall
                    (Expr.path
                      none
                      (Path.mk false [(PathSegment.mk "arguments" PathArguments.none)]))
                    "try_map"
                    none
                    [
                      (Expr.closure
                        false
                        [(Pat.ident false false "arg" none)]
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
                              (Path.mk false [(PathSegment.mk "arg" PathArguments.none)]))]))])))
              none),
            (Stmt.letStmt
              []
              (Pat.ident false false "value" none)
              (some
                (Expr.tryExpr
                  (Expr.methodCall
                    (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                    "eval_intrinsic"
                    none
                    [
                      (Expr.path
                        none
                        (Path.mk false [(PathSegment.mk "intrinsic" PathArguments.none)])),
                      (Expr.path
                        none
                        (Path.mk false [(PathSegment.mk "arguments" PathArguments.none)])),
                      (Expr.path
                        none
                        (Path.mk false [(PathSegment.mk "ret_ty" PathArguments.none)]))])))
              none),
            (Stmt.expr
              (Expr.tryExpr
                (Expr.methodCall
                  (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                  "place_store"
                  none
                  [
                    (Expr.path
                      none
                      (Path.mk false [(PathSegment.mk "ret_place" PathArguments.none)])),
                    (Expr.path none (Path.mk false [(PathSegment.mk "value" PathArguments.none)])),
                    (Expr.path none (Path.mk false [(PathSegment.mk "ret_ty" PathArguments.none)]))]))
              true),
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
                            (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                          "jump_to_block"
                          none
                          [
                            (Expr.path
                              none
                              (Path.mk false [(PathSegment.mk "next_block" PathArguments.none)]))]))
                      true)])
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
                                    "return from an intrinsic where caller did not specify next block"))]
                              false))
                          true)]))))
              false),
            (Stmt.expr
              (Expr.call
                (Expr.path none (Path.mk false [(PathSegment.mk "ret" PathArguments.none)]))
                [(Expr.tuple [])])
              false)]))])

/-- All items of `spec/lang/step/terminators.md`, in source order, with provenance. -/
def items : List SourceItem :=
  [
    (SourceItem.mk
      "impl_Machine__eval_terminator_0"
      8
      "c5025a5df453381047befaacd8e50b3180c3a2a81e7071ab91bd847e2a48bd71"
      impl_Machine__eval_terminator_0),
    (SourceItem.mk
      "impl_Machine__jump_to_block"
      19
      "25a223d317aa47ae05aadbc81218eed7a3b9fd8e9643dc30da924154f7486fe4"
      impl_Machine__jump_to_block),
    (SourceItem.mk
      "impl_Machine__eval_terminator_1"
      37
      "d22ab9f6e83a163d3523fe5cb76ae4e849ebbf52845aed2717731772734da769"
      impl_Machine__eval_terminator_1),
    (SourceItem.mk
      "impl_Machine__eval_terminator_2"
      53
      "7a0d575a3f8bed6666ad6523d1420f6a75e1582aef77ff706ada3ef84d132c57"
      impl_Machine__eval_terminator_2),
    (SourceItem.mk
      "fn_check_abi_compatibility"
      66
      "b75d61579e36409d02eab04ea3c87062bd9499d665682dae25760bd7b0a3e9f9"
      fn_check_abi_compatibility),
    (SourceItem.mk
      "impl_Machine__prepare_for_inplace_passing"
      136
      "2119652eac5e27137622703650381ed129d416e67a10fb59f2b8cce17a32874f"
      impl_Machine__prepare_for_inplace_passing),
    (SourceItem.mk
      "impl_Machine__terminate_active_thread"
      298
      "45319c0e710256385091ba8bcdf5b576c72c74bbb3dad46a6aae5a447c839a64"
      impl_Machine__terminate_active_thread),
    (SourceItem.mk
      "impl_Machine__eval_terminator_3"
      385
      "609aeedcde82c80223cf8ded9391509a81997ec41c5026740902d7d15ec8a33e"
      impl_Machine__eval_terminator_3),
    (SourceItem.mk
      "impl_Machine__eval_terminator_4"
      406
      "87fd55f2aff92d3130f7f969fd54e234a7a1020bf1565dd464822255f2f2ba13"
      impl_Machine__eval_terminator_4),
    (SourceItem.mk
      "impl_Machine__eval_terminator_5"
      423
      "d45794457f1e10718018445fb39088ed241b1087dc786374f0572332425cb758"
      impl_Machine__eval_terminator_5),
    (SourceItem.mk
      "impl_Machine__eval_terminator_6"
      461
      "6a4318d715d95e6573929ea1cd1058ea3f61e79854c6c1db56d9f68ace2b5bdf"
      impl_Machine__eval_terminator_6)]

end MiniRustSpec.Gen.Items.Lang.Step.Terminators
