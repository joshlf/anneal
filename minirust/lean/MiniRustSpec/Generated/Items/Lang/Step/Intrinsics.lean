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
`spec/lang/step/intrinsics.md` (commit `d821c6e3`), one Lean definition per item, in source order.
-/

import MiniRustSpec.Meta.Syntax

set_option maxRecDepth 100000

namespace MiniRustSpec.Gen.Items.Lang.Step.Intrinsics

open MiniRustSpec.Syntax

/-- Path of the upstream file these items were extracted from. -/
def sourceFile : String := "spec/lang/step/intrinsics.md"

/-- SHA-256 of the upstream file. -/
def sourceSha256 : String := "261fe197e65556bae74cf209c64c5913fdd713f3a57d2bf56f0b1fb0e3a34be8"

/-- `spec/lang/step/intrinsics.md:6` -/
def impl_Machine__eval_intrinsic_0 : Item :=
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
        [(Attr.mk true "specr::argmatch" (AttrMeta.list "intrinsic"))]
        Visibility.inherited
        false
        (Signature.mk
          false
          false
          false
          none
          "eval_intrinsic"
          (Generics.mk [] [])
          [
            (FnArg.receiver [] true none true none),
            (FnArg.typed
              []
              (Pat.ident false false "intrinsic" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "IntrinsicOp" PathArguments.none)]))),
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
              (Pat.ident false false "ret_ty" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "Type" PathArguments.none)])))]
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
                                  "Value"
                                  (PathArguments.angleBracketed
                                    false
                                    [
                                      (GenericArgument.type
                                        (Ty.path
                                          none
                                          (Path.mk false [(PathSegment.mk "M" PathArguments.none)])))]))])))]))]))))
        (Block.mk [(Stmt.expr (Expr.range none RangeLimits.halfOpen none) false)]))])

/-- `spec/lang/step/intrinsics.md:20` -/
def fn_unit_value : Item :=
  (Item.fn
    []
    Visibility.inherited
    (Signature.mk
      false
      false
      false
      none
      "unit_value"
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
      []
      false
      (some
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
                      (Ty.path none (Path.mk false [(PathSegment.mk "M" PathArguments.none)])))]))]))))
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
                  (PathSegment.mk "Tuple" PathArguments.none)]))
            [
              (Expr.macro
                (Macro.mk
                  (Path.mk false [(PathSegment.mk "list" PathArguments.none)])
                  MacroDelimiter.bracket
                  (MacroBody.exprs [] false)))])
          false)]))

/-- `spec/lang/step/intrinsics.md:24` -/
def fn_unit_type : Item :=
  (Item.fn
    []
    Visibility.inherited
    (Signature.mk
      false
      false
      false
      none
      "unit_type"
      (Generics.mk [] [])
      []
      false
      (some (Ty.path none (Path.mk false [(PathSegment.mk "Type" PathArguments.none)]))))
    (Block.mk
      [
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
                (Expr.macro
                  (Macro.mk
                    (Path.mk false [(PathSegment.mk "list" PathArguments.none)])
                    MacroDelimiter.bracket
                    (MacroBody.exprs [] false)))),
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
                        (Path.mk
                          false
                          [
                            (PathSegment.mk "Size" PathArguments.none),
                            (PathSegment.mk "ZERO" PathArguments.none)]))),
                    (FieldValue.mk
                      []
                      (Member.named "align")
                      false
                      (Expr.path
                        none
                        (Path.mk
                          false
                          [
                            (PathSegment.mk "Align" PathArguments.none),
                            (PathSegment.mk "ONE" PathArguments.none)]))),
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

/-- `spec/lang/step/intrinsics.md:36` -/
def impl_Machine__eval_intrinsic_1 : Item :=
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
          "eval_intrinsic"
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
                    (PathSegment.mk "IntrinsicOp" PathArguments.none),
                    (PathSegment.mk "PointerExposeProvenance" PathArguments.none)]))
              (Ty.path none (Path.mk false [(PathSegment.mk "IntrinsicOp" PathArguments.none)]))),
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
              (Pat.ident false false "ret_ty" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "Type" PathArguments.none)])))]
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
                (Expr.binary
                  (Expr.methodCall
                    (Expr.path
                      none
                      (Path.mk false [(PathSegment.mk "arguments" PathArguments.none)]))
                    "len"
                    none
                    [])
                  BinOp.ne
                  (Expr.lit (Lit.int 1 "")))
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
                                "invalid number of arguments for `PointerExposeProvenance` intrinsic"))]
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
                        (Pat.ident false false "ptr" none)),
                      (FieldPat.mk
                        []
                        (Member.named "metadata")
                        false
                        (Pat.ident false false "None" none))]
                    false)])
              (some
                (Expr.field
                  (Expr.index
                    (Expr.path
                      none
                      (Path.mk false [(PathSegment.mk "arguments" PathArguments.none)]))
                    (Expr.lit (Lit.int 0 "")))
                  (Member.unnamed 0)))
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
                                  "invalid argument for `PointerExposeProvenance` intrinsic: not a thin pointer"))]
                            false))
                        true)])))),
            (Stmt.expr
              (Expr.ite
                (Expr.binary
                  (Expr.path none (Path.mk false [(PathSegment.mk "ret_ty" PathArguments.none)]))
                  BinOp.ne
                  (Expr.call
                    (Expr.path
                      none
                      (Path.mk
                        false
                        [
                          (PathSegment.mk "Type" PathArguments.none),
                          (PathSegment.mk "Int" PathArguments.none)]))
                    [
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
                            (Expr.path
                              none
                              (Path.mk
                                false
                                [
                                  (PathSegment.mk "M" PathArguments.none),
                                  (PathSegment.mk "T" PathArguments.none),
                                  (PathSegment.mk "PTR_SIZE" PathArguments.none)])))]
                        false
                        none)]))
                (Block.mk
                  [
                    (Stmt.expr
                      (Expr.macro
                        (Macro.mk
                          (Path.mk false [(PathSegment.mk "throw_ub" PathArguments.none)])
                          MacroDelimiter.paren
                          (MacroBody.exprs
                            [
                              (Expr.lit
                                (Lit.str
                                  "invalid return type for `PointerExposeProvenance` intrinsic"))]
                            false)))
                      false)])
                none)
              false),
            (Stmt.expr
              (Expr.methodCall
                (Expr.field
                  (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                  (Member.named "intptrcast"))
                "expose"
                none
                [(Expr.path none (Path.mk false [(PathSegment.mk "ptr" PathArguments.none)]))])
              true),
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
                          (PathSegment.mk "Value" PathArguments.none),
                          (PathSegment.mk "Int" PathArguments.none)]))
                    [
                      (Expr.field
                        (Expr.path none (Path.mk false [(PathSegment.mk "ptr" PathArguments.none)]))
                        (Member.named "addr"))])])
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
          "eval_intrinsic"
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
                    (PathSegment.mk "IntrinsicOp" PathArguments.none),
                    (PathSegment.mk "PointerWithExposedProvenance" PathArguments.none)]))
              (Ty.path none (Path.mk false [(PathSegment.mk "IntrinsicOp" PathArguments.none)]))),
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
              (Pat.ident false false "ret_ty" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "Type" PathArguments.none)])))]
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
                (Expr.binary
                  (Expr.methodCall
                    (Expr.path
                      none
                      (Path.mk false [(PathSegment.mk "arguments" PathArguments.none)]))
                    "len"
                    none
                    [])
                  BinOp.ne
                  (Expr.lit (Lit.int 1 "")))
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
                                "invalid number of arguments for `PointerWithExposedProvenance` intrinsic"))]
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
                    (PathSegment.mk "Value" PathArguments.none),
                    (PathSegment.mk "Int" PathArguments.none)])
                [(Pat.ident false false "addr" none)])
              (some
                (Expr.field
                  (Expr.index
                    (Expr.path
                      none
                      (Path.mk false [(PathSegment.mk "arguments" PathArguments.none)]))
                    (Expr.lit (Lit.int 0 "")))
                  (Member.unnamed 0)))
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
                                  "invalid argument for `PointerWithExposedProvenance` intrinsic: not an integer"))]
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
                    (PathSegment.mk "Ptr" PathArguments.none)])
                [(Pat.ident false false "ret_ptr_ty" none)])
              (some (Expr.path none (Path.mk false [(PathSegment.mk "ret_ty" PathArguments.none)])))
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
                                  "invalid return type for `PointerWithExposedProvenance` intrinsic"))]
                            false))
                        true)])))),
            (Stmt.expr
              (Expr.ite
                (Expr.binary
                  (Expr.methodCall
                    (Expr.path
                      none
                      (Path.mk false [(PathSegment.mk "ret_ptr_ty" PathArguments.none)]))
                    "meta_kind"
                    none
                    [])
                  BinOp.ne
                  (Expr.path
                    none
                    (Path.mk
                      false
                      [
                        (PathSegment.mk "PointerMetaKind" PathArguments.none),
                        (PathSegment.mk "None" PathArguments.none)])))
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
                                "unsized pointee requested for `PointerWithExposedProvenance` intrinsic"))]
                          false))
                      true)])
                none)
              false),
            (Stmt.letStmt
              []
              (Pat.ident false false "ptr" none)
              (some
                (Expr.tryExpr
                  (Expr.methodCall
                    (Expr.field
                      (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                      (Member.named "intptrcast"))
                    "int2ptr"
                    none
                    [(Expr.path none (Path.mk false [(PathSegment.mk "addr" PathArguments.none)]))])))
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
                          (PathSegment.mk "Value" PathArguments.none),
                          (PathSegment.mk "Ptr" PathArguments.none)]))
                    [
                      (Expr.methodCall
                        (Expr.path none (Path.mk false [(PathSegment.mk "ptr" PathArguments.none)]))
                        "widen"
                        none
                        [
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "None" PathArguments.none)]))])])])
              false)]))])

/-- `spec/lang/step/intrinsics.md:85` -/
def impl_Machine__exit : Item :=
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
          "exit"
          (Generics.mk [] [])
          [(FnArg.receiver [] true none false none)]
          false
          (some
            (Ty.path
              none
              (Path.mk
                false
                [
                  (PathSegment.mk
                    "NdResult"
                    (PathArguments.angleBracketed false [(GenericArgument.type Ty.never)]))]))))
        (Block.mk
          [
            (Stmt.expr
              (Expr.tryExpr
                (Expr.methodCall
                  (Expr.field
                    (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                    (Member.named "mem"))
                  "leak_check"
                  none
                  []))
              true),
            (Stmt.macro
              []
              (Macro.mk
                (Path.mk false [(PathSegment.mk "throw_machine_stop" PathArguments.none)])
                MacroDelimiter.paren
                (MacroBody.exprs [] false))
              true)])),
      (ImplItem.fn
        []
        Visibility.inherited
        false
        (Signature.mk
          false
          false
          false
          none
          "eval_intrinsic"
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
                    (PathSegment.mk "IntrinsicOp" PathArguments.none),
                    (PathSegment.mk "Exit" PathArguments.none)]))
              (Ty.path none (Path.mk false [(PathSegment.mk "IntrinsicOp" PathArguments.none)]))),
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
              (Pat.ident false false "ret_ty" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "Type" PathArguments.none)])))]
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
              (Expr.tryExpr
                (Expr.methodCall
                  (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                  "exit"
                  none
                  []))
              false)]))])

/-- `spec/lang/step/intrinsics.md:107` -/
def impl_Machine__eval_intrinsic_2 : Item :=
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
          "eval_intrinsic"
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
                    (PathSegment.mk "IntrinsicOp" PathArguments.none),
                    (PathSegment.mk "Abort" PathArguments.none)]))
              (Ty.path none (Path.mk false [(PathSegment.mk "IntrinsicOp" PathArguments.none)]))),
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
              (Pat.ident false false "ret_ty" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "Type" PathArguments.none)])))]
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
            (Stmt.macro
              []
              (Macro.mk
                (Path.mk false [(PathSegment.mk "throw_abort" PathArguments.none)])
                MacroDelimiter.paren
                (MacroBody.exprs [] false))
              true)]))])

/-- `spec/lang/step/intrinsics.md:122` -/
def impl_Machine__eval_intrinsic_3 : Item :=
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
          "eval_intrinsic"
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
                    (PathSegment.mk "IntrinsicOp" PathArguments.none),
                    (PathSegment.mk "Assume" PathArguments.none)]))
              (Ty.path none (Path.mk false [(PathSegment.mk "IntrinsicOp" PathArguments.none)]))),
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
              (Pat.ident false false "ret_ty" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "Type" PathArguments.none)])))]
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
                (Expr.binary
                  (Expr.methodCall
                    (Expr.path
                      none
                      (Path.mk false [(PathSegment.mk "arguments" PathArguments.none)]))
                    "len"
                    none
                    [])
                  BinOp.ne
                  (Expr.lit (Lit.int 1 "")))
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
                              (Lit.str "invalid number of arguments for `Assume` intrinsic"))]
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
                    (PathSegment.mk "Value" PathArguments.none),
                    (PathSegment.mk "Bool" PathArguments.none)])
                [(Pat.ident false false "b" none)])
              (some
                (Expr.field
                  (Expr.index
                    (Expr.path
                      none
                      (Path.mk false [(PathSegment.mk "arguments" PathArguments.none)]))
                    (Expr.lit (Lit.int 0 "")))
                  (Member.unnamed 0)))
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
                                (Lit.str "invalid argument for `Assume` intrinsic: not a Boolean"))]
                            false))
                        true)])))),
            (Stmt.expr
              (Expr.ite
                (Expr.binary
                  (Expr.path none (Path.mk false [(PathSegment.mk "ret_ty" PathArguments.none)]))
                  BinOp.ne
                  (Expr.call
                    (Expr.path
                      none
                      (Path.mk false [(PathSegment.mk "unit_type" PathArguments.none)]))
                    []))
                (Block.mk
                  [
                    (Stmt.expr
                      (Expr.macro
                        (Macro.mk
                          (Path.mk false [(PathSegment.mk "throw_ub" PathArguments.none)])
                          MacroDelimiter.paren
                          (MacroBody.exprs
                            [(Expr.lit (Lit.str "invalid return type for `Assume` intrinsic"))]
                            false)))
                      false)])
                none)
              false),
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
                        (Path.mk false [(PathSegment.mk "throw_ub" PathArguments.none)])
                        MacroDelimiter.paren
                        (MacroBody.exprs
                          [
                            (Expr.lit
                              (Lit.str "`Assume` intrinsic called on condition that is violated"))]
                          false))
                      true)])
                none)
              false),
            (Stmt.expr
              (Expr.call
                (Expr.path none (Path.mk false [(PathSegment.mk "ret" PathArguments.none)]))
                [
                  (Expr.call
                    (Expr.path
                      none
                      (Path.mk false [(PathSegment.mk "unit_value" PathArguments.none)]))
                    [])])
              false)]))])

/-- `spec/lang/step/intrinsics.md:153` -/
def impl_Machine__eval_intrinsic_4 : Item :=
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
          "eval_intrinsic"
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
                    (PathSegment.mk "IntrinsicOp" PathArguments.none),
                    (PathSegment.mk "PrintStdout" PathArguments.none)]))
              (Ty.path none (Path.mk false [(PathSegment.mk "IntrinsicOp" PathArguments.none)]))),
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
              (Pat.ident false false "ret_ty" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "Type" PathArguments.none)])))]
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
                (Expr.binary
                  (Expr.path none (Path.mk false [(PathSegment.mk "ret_ty" PathArguments.none)]))
                  BinOp.ne
                  (Expr.call
                    (Expr.path
                      none
                      (Path.mk false [(PathSegment.mk "unit_type" PathArguments.none)]))
                    []))
                (Block.mk
                  [
                    (Stmt.expr
                      (Expr.macro
                        (Macro.mk
                          (Path.mk false [(PathSegment.mk "throw_ub" PathArguments.none)])
                          MacroDelimiter.paren
                          (MacroBody.exprs
                            [(Expr.lit (Lit.str "invalid return type for `PrintStdout` intrinsic"))]
                            false)))
                      false)])
                none)
              false),
            (Stmt.expr
              (Expr.tryExpr
                (Expr.methodCall
                  (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                  "eval_print"
                  none
                  [
                    (Expr.field
                      (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                      (Member.named "stdout")),
                    (Expr.path
                      none
                      (Path.mk false [(PathSegment.mk "arguments" PathArguments.none)]))]))
              true),
            (Stmt.expr
              (Expr.call
                (Expr.path none (Path.mk false [(PathSegment.mk "ret" PathArguments.none)]))
                [
                  (Expr.call
                    (Expr.path
                      none
                      (Path.mk false [(PathSegment.mk "unit_value" PathArguments.none)]))
                    [])])
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
          "eval_intrinsic"
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
                    (PathSegment.mk "IntrinsicOp" PathArguments.none),
                    (PathSegment.mk "PrintStderr" PathArguments.none)]))
              (Ty.path none (Path.mk false [(PathSegment.mk "IntrinsicOp" PathArguments.none)]))),
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
              (Pat.ident false false "ret_ty" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "Type" PathArguments.none)])))]
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
                (Expr.binary
                  (Expr.path none (Path.mk false [(PathSegment.mk "ret_ty" PathArguments.none)]))
                  BinOp.ne
                  (Expr.call
                    (Expr.path
                      none
                      (Path.mk false [(PathSegment.mk "unit_type" PathArguments.none)]))
                    []))
                (Block.mk
                  [
                    (Stmt.expr
                      (Expr.macro
                        (Macro.mk
                          (Path.mk false [(PathSegment.mk "throw_ub" PathArguments.none)])
                          MacroDelimiter.paren
                          (MacroBody.exprs
                            [(Expr.lit (Lit.str "invalid return type for `PrintStderr` intrinsic"))]
                            false)))
                      false)])
                none)
              false),
            (Stmt.expr
              (Expr.tryExpr
                (Expr.methodCall
                  (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                  "eval_print"
                  none
                  [
                    (Expr.field
                      (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                      (Member.named "stderr")),
                    (Expr.path
                      none
                      (Path.mk false [(PathSegment.mk "arguments" PathArguments.none)]))]))
              true),
            (Stmt.expr
              (Expr.call
                (Expr.path none (Path.mk false [(PathSegment.mk "ret" PathArguments.none)]))
                [
                  (Expr.call
                    (Expr.path
                      none
                      (Path.mk false [(PathSegment.mk "unit_value" PathArguments.none)]))
                    [])])
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
          "eval_print"
          (Generics.mk [] [])
          [
            (FnArg.receiver [] true none true none),
            (FnArg.typed
              []
              (Pat.ident false false "stream" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "DynWrite" PathArguments.none)]))),
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
                                  (Path.mk false [(PathSegment.mk "Type" PathArguments.none)]))]))]))])))]
          false
          (some (Ty.path none (Path.mk false [(PathSegment.mk "Result" PathArguments.none)]))))
        (Block.mk
          [
            (Stmt.expr
              (Expr.forLoop
                none
                (Pat.tuple [(Pat.ident false false "arg" none), Pat.wild])
                (Expr.path none (Path.mk false [(PathSegment.mk "arguments" PathArguments.none)]))
                (Block.mk
                  [
                    (Stmt.expr
                      (Expr.matchExpr
                        (Expr.path none (Path.mk false [(PathSegment.mk "arg" PathArguments.none)]))
                        [
                          (Arm.mk
                            []
                            (Pat.tupleStruct
                              none
                              (Path.mk
                                false
                                [
                                  (PathSegment.mk "Value" PathArguments.none),
                                  (PathSegment.mk "Int" PathArguments.none)])
                              [(Pat.ident false false "i" none)])
                            none
                            (Expr.methodCall
                              (Expr.macro
                                (Macro.mk
                                  (Path.mk false [(PathSegment.mk "write" PathArguments.none)])
                                  MacroDelimiter.paren
                                  (MacroBody.exprs
                                    [
                                      (Expr.path
                                        none
                                        (Path.mk
                                          false
                                          [(PathSegment.mk "stream" PathArguments.none)])),
                                      (Expr.lit (Lit.str "{}\n")),
                                      (Expr.path
                                        none
                                        (Path.mk false [(PathSegment.mk "i" PathArguments.none)]))]
                                    false)))
                              "unwrap"
                              none
                              [])),
                          (Arm.mk
                            []
                            (Pat.tupleStruct
                              none
                              (Path.mk
                                false
                                [
                                  (PathSegment.mk "Value" PathArguments.none),
                                  (PathSegment.mk "Bool" PathArguments.none)])
                              [(Pat.ident false false "b" none)])
                            none
                            (Expr.methodCall
                              (Expr.macro
                                (Macro.mk
                                  (Path.mk false [(PathSegment.mk "write" PathArguments.none)])
                                  MacroDelimiter.paren
                                  (MacroBody.exprs
                                    [
                                      (Expr.path
                                        none
                                        (Path.mk
                                          false
                                          [(PathSegment.mk "stream" PathArguments.none)])),
                                      (Expr.lit (Lit.str "{}\n")),
                                      (Expr.path
                                        none
                                        (Path.mk false [(PathSegment.mk "b" PathArguments.none)]))]
                                    false)))
                              "unwrap"
                              none
                              [])),
                          (Arm.mk
                            []
                            Pat.wild
                            none
                            (Expr.macro
                              (Macro.mk
                                (Path.mk false [(PathSegment.mk "throw_ub" PathArguments.none)])
                                MacroDelimiter.paren
                                (MacroBody.exprs
                                  [(Expr.lit (Lit.str "unsupported value for printing"))]
                                  false))))])
                      false)]))
              false),
            (Stmt.expr
              (Expr.call
                (Expr.path none (Path.mk false [(PathSegment.mk "ret" PathArguments.none)]))
                [(Expr.tuple [])])
              false)]))])

/-- `spec/lang/step/intrinsics.md:207` -/
def impl_Machine__eval_intrinsic_5 : Item :=
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
          "eval_intrinsic"
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
                    (PathSegment.mk "IntrinsicOp" PathArguments.none),
                    (PathSegment.mk "Allocate" PathArguments.none)]))
              (Ty.path none (Path.mk false [(PathSegment.mk "IntrinsicOp" PathArguments.none)]))),
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
              (Pat.ident false false "ret_ty" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "Type" PathArguments.none)])))]
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
                (Expr.binary
                  (Expr.methodCall
                    (Expr.path
                      none
                      (Path.mk false [(PathSegment.mk "arguments" PathArguments.none)]))
                    "len"
                    none
                    [])
                  BinOp.ne
                  (Expr.lit (Lit.int 2 "")))
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
                              (Lit.str "invalid number of arguments for `Allocate` intrinsic"))]
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
                    (PathSegment.mk "Value" PathArguments.none),
                    (PathSegment.mk "Int" PathArguments.none)])
                [(Pat.ident false false "size" none)])
              (some
                (Expr.field
                  (Expr.index
                    (Expr.path
                      none
                      (Path.mk false [(PathSegment.mk "arguments" PathArguments.none)]))
                    (Expr.lit (Lit.int 0 "")))
                  (Member.unnamed 0)))
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
                                  "invalid first argument to `Allocate` intrinsic: not an integer"))]
                            false))
                        true)])))),
            (Stmt.letStmt
              []
              (Pat.tupleStruct
                none
                (Path.mk false [(PathSegment.mk "Some" PathArguments.none)])
                [(Pat.ident false false "size" none)])
              (some
                (Expr.call
                  (Expr.path
                    none
                    (Path.mk
                      false
                      [
                        (PathSegment.mk "Size" PathArguments.none),
                        (PathSegment.mk "from_bytes" PathArguments.none)]))
                  [(Expr.path none (Path.mk false [(PathSegment.mk "size" PathArguments.none)]))]))
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
                                (Lit.str "invalid size for `Allocate` intrinsic: negative size"))]
                            false))
                        true)])))),
            (Stmt.letStmt
              []
              (Pat.tupleStruct
                none
                (Path.mk
                  false
                  [
                    (PathSegment.mk "Value" PathArguments.none),
                    (PathSegment.mk "Int" PathArguments.none)])
                [(Pat.ident false false "align" none)])
              (some
                (Expr.field
                  (Expr.index
                    (Expr.path
                      none
                      (Path.mk false [(PathSegment.mk "arguments" PathArguments.none)]))
                    (Expr.lit (Lit.int 1 "")))
                  (Member.unnamed 0)))
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
                                  "invalid second argument to `Allocate` intrinsic: not an integer"))]
                            false))
                        true)])))),
            (Stmt.letStmt
              []
              (Pat.tupleStruct
                none
                (Path.mk false [(PathSegment.mk "Some" PathArguments.none)])
                [(Pat.ident false false "align" none)])
              (some
                (Expr.call
                  (Expr.path
                    none
                    (Path.mk
                      false
                      [
                        (PathSegment.mk "Align" PathArguments.none),
                        (PathSegment.mk "from_bytes" PathArguments.none)]))
                  [(Expr.path none (Path.mk false [(PathSegment.mk "align" PathArguments.none)]))]))
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
                                  "invalid alignment for `Allocate` intrinsic: not a power of 2"))]
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
                    (PathSegment.mk "Ptr" PathArguments.none)])
                [(Pat.ident false false "ret_ptr_ty" none)])
              (some (Expr.path none (Path.mk false [(PathSegment.mk "ret_ty" PathArguments.none)])))
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
                            [(Expr.lit (Lit.str "invalid return type for `Allocate` intrinsic"))]
                            false))
                        true)])))),
            (Stmt.expr
              (Expr.ite
                (Expr.binary
                  (Expr.methodCall
                    (Expr.path
                      none
                      (Path.mk false [(PathSegment.mk "ret_ptr_ty" PathArguments.none)]))
                    "meta_kind"
                    none
                    [])
                  BinOp.ne
                  (Expr.path
                    none
                    (Path.mk
                      false
                      [
                        (PathSegment.mk "PointerMetaKind" PathArguments.none),
                        (PathSegment.mk "None" PathArguments.none)])))
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
                              (Lit.str "unsized pointee requested for `Allocate` intrinsic"))]
                          false))
                      true)])
                none)
              false),
            (Stmt.letStmt
              []
              (Pat.ident false false "alloc" none)
              (some
                (Expr.tryExpr
                  (Expr.methodCall
                    (Expr.field
                      (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                      (Member.named "mem"))
                    "allocate"
                    none
                    [
                      (Expr.path
                        none
                        (Path.mk
                          false
                          [
                            (PathSegment.mk "AllocationKind" PathArguments.none),
                            (PathSegment.mk "Heap" PathArguments.none)])),
                      (Expr.path none (Path.mk false [(PathSegment.mk "size" PathArguments.none)])),
                      (Expr.path none (Path.mk false [(PathSegment.mk "align" PathArguments.none)]))])))
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
                          (PathSegment.mk "Value" PathArguments.none),
                          (PathSegment.mk "Ptr" PathArguments.none)]))
                    [
                      (Expr.methodCall
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "alloc" PathArguments.none)]))
                        "widen"
                        none
                        [
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "None" PathArguments.none)]))])])])
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
          "eval_intrinsic"
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
                    (PathSegment.mk "IntrinsicOp" PathArguments.none),
                    (PathSegment.mk "Deallocate" PathArguments.none)]))
              (Ty.path none (Path.mk false [(PathSegment.mk "IntrinsicOp" PathArguments.none)]))),
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
              (Pat.ident false false "ret_ty" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "Type" PathArguments.none)])))]
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
                (Expr.binary
                  (Expr.methodCall
                    (Expr.path
                      none
                      (Path.mk false [(PathSegment.mk "arguments" PathArguments.none)]))
                    "len"
                    none
                    [])
                  BinOp.ne
                  (Expr.lit (Lit.int 3 "")))
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
                              (Lit.str "invalid number of arguments for `Deallocate` intrinsic"))]
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
                        (Pat.ident false false "ptr" none)),
                      (FieldPat.mk
                        []
                        (Member.named "metadata")
                        false
                        (Pat.ident false false "None" none))]
                    false)])
              (some
                (Expr.field
                  (Expr.index
                    (Expr.path
                      none
                      (Path.mk false [(PathSegment.mk "arguments" PathArguments.none)]))
                    (Expr.lit (Lit.int 0 "")))
                  (Member.unnamed 0)))
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
                                  "invalid first argument to `Deallocate` intrinsic: not a thin pointer"))]
                            false))
                        true)])))),
            (Stmt.letStmt
              []
              (Pat.tupleStruct
                none
                (Path.mk
                  false
                  [
                    (PathSegment.mk "Value" PathArguments.none),
                    (PathSegment.mk "Int" PathArguments.none)])
                [(Pat.ident false false "size" none)])
              (some
                (Expr.field
                  (Expr.index
                    (Expr.path
                      none
                      (Path.mk false [(PathSegment.mk "arguments" PathArguments.none)]))
                    (Expr.lit (Lit.int 1 "")))
                  (Member.unnamed 0)))
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
                                  "invalid second argument to `Deallocate` intrinsic: not an integer"))]
                            false))
                        true)])))),
            (Stmt.letStmt
              []
              (Pat.tupleStruct
                none
                (Path.mk false [(PathSegment.mk "Some" PathArguments.none)])
                [(Pat.ident false false "size" none)])
              (some
                (Expr.call
                  (Expr.path
                    none
                    (Path.mk
                      false
                      [
                        (PathSegment.mk "Size" PathArguments.none),
                        (PathSegment.mk "from_bytes" PathArguments.none)]))
                  [(Expr.path none (Path.mk false [(PathSegment.mk "size" PathArguments.none)]))]))
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
                                (Lit.str "invalid size for `Deallocate` intrinsic: negative size"))]
                            false))
                        true)])))),
            (Stmt.letStmt
              []
              (Pat.tupleStruct
                none
                (Path.mk
                  false
                  [
                    (PathSegment.mk "Value" PathArguments.none),
                    (PathSegment.mk "Int" PathArguments.none)])
                [(Pat.ident false false "align" none)])
              (some
                (Expr.field
                  (Expr.index
                    (Expr.path
                      none
                      (Path.mk false [(PathSegment.mk "arguments" PathArguments.none)]))
                    (Expr.lit (Lit.int 2 "")))
                  (Member.unnamed 0)))
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
                                  "invalid third argument to `Deallocate` intrinsic: not an integer"))]
                            false))
                        true)])))),
            (Stmt.letStmt
              []
              (Pat.tupleStruct
                none
                (Path.mk false [(PathSegment.mk "Some" PathArguments.none)])
                [(Pat.ident false false "align" none)])
              (some
                (Expr.call
                  (Expr.path
                    none
                    (Path.mk
                      false
                      [
                        (PathSegment.mk "Align" PathArguments.none),
                        (PathSegment.mk "from_bytes" PathArguments.none)]))
                  [(Expr.path none (Path.mk false [(PathSegment.mk "align" PathArguments.none)]))]))
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
                                  "invalid alignment for `Deallocate` intrinsic: not a power of 2"))]
                            false))
                        true)])))),
            (Stmt.expr
              (Expr.ite
                (Expr.binary
                  (Expr.path none (Path.mk false [(PathSegment.mk "ret_ty" PathArguments.none)]))
                  BinOp.ne
                  (Expr.call
                    (Expr.path
                      none
                      (Path.mk false [(PathSegment.mk "unit_type" PathArguments.none)]))
                    []))
                (Block.mk
                  [
                    (Stmt.expr
                      (Expr.macro
                        (Macro.mk
                          (Path.mk false [(PathSegment.mk "throw_ub" PathArguments.none)])
                          MacroDelimiter.paren
                          (MacroBody.exprs
                            [(Expr.lit (Lit.str "invalid return type for `Deallocate` intrinsic"))]
                            false)))
                      false)])
                none)
              false),
            (Stmt.expr
              (Expr.tryExpr
                (Expr.methodCall
                  (Expr.field
                    (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                    (Member.named "mem"))
                  "deallocate"
                  none
                  [
                    (Expr.path none (Path.mk false [(PathSegment.mk "ptr" PathArguments.none)])),
                    (Expr.path
                      none
                      (Path.mk
                        false
                        [
                          (PathSegment.mk "AllocationKind" PathArguments.none),
                          (PathSegment.mk "Heap" PathArguments.none)])),
                    (Expr.path none (Path.mk false [(PathSegment.mk "size" PathArguments.none)])),
                    (Expr.path none (Path.mk false [(PathSegment.mk "align" PathArguments.none)]))]))
              true),
            (Stmt.expr
              (Expr.call
                (Expr.path none (Path.mk false [(PathSegment.mk "ret" PathArguments.none)]))
                [
                  (Expr.call
                    (Expr.path
                      none
                      (Path.mk false [(PathSegment.mk "unit_value" PathArguments.none)]))
                    [])])
              false)]))])

/-- `spec/lang/step/intrinsics.md:288` -/
def impl_Machine__spawn : Item :=
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
          "spawn"
          (Generics.mk [] [])
          [
            (FnArg.receiver [] true none true none),
            (FnArg.typed
              []
              (Pat.ident false false "func" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "Function" PathArguments.none)]))),
            (FnArg.typed
              []
              (Pat.ident false false "data_pointer" none)
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
                            (Ty.path none (Path.mk false [(PathSegment.mk "M" PathArguments.none)])))]))]))),
            (FnArg.typed
              []
              (Pat.ident false false "data_ptr_ty" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "Type" PathArguments.none)])))]
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
                            (Path.mk false [(PathSegment.mk "ThreadId" PathArguments.none)])))]))]))))
        (Block.mk
          [
            (Stmt.letStmt
              []
              (Pat.ident false false "args" none)
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
                              (Path.mk false [(PathSegment.mk "data_pointer" PathArguments.none)])),
                            (Expr.path
                              none
                              (Path.mk false [(PathSegment.mk "data_ptr_ty" PathArguments.none)]))])]
                      false))))
              none),
            (Stmt.letStmt
              []
              (Pat.ident false false "thread_id" none)
              (some
                (Expr.tryExpr
                  (Expr.methodCall
                    (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                    "new_thread"
                    none
                    [
                      (Expr.path none (Path.mk false [(PathSegment.mk "func" PathArguments.none)])),
                      (Expr.path none (Path.mk false [(PathSegment.mk "args" PathArguments.none)]))])))
              none),
            (Stmt.expr
              (Expr.methodCall
                (Expr.field
                  (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                  (Member.named "synchronized_threads"))
                "insert"
                none
                [(Expr.path none (Path.mk false [(PathSegment.mk "thread_id" PathArguments.none)]))])
              true),
            (Stmt.expr
              (Expr.call
                (Expr.path none (Path.mk false [(PathSegment.mk "ret" PathArguments.none)]))
                [(Expr.path none (Path.mk false [(PathSegment.mk "thread_id" PathArguments.none)]))])
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
          "eval_intrinsic"
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
                    (PathSegment.mk "IntrinsicOp" PathArguments.none),
                    (PathSegment.mk "Spawn" PathArguments.none)]))
              (Ty.path none (Path.mk false [(PathSegment.mk "IntrinsicOp" PathArguments.none)]))),
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
              (Pat.ident false false "ret_ty" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "Type" PathArguments.none)])))]
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
                (Expr.binary
                  (Expr.methodCall
                    (Expr.path
                      none
                      (Path.mk false [(PathSegment.mk "arguments" PathArguments.none)]))
                    "len"
                    none
                    [])
                  BinOp.ne
                  (Expr.lit (Lit.int 2 "")))
                (Block.mk
                  [
                    (Stmt.macro
                      []
                      (Macro.mk
                        (Path.mk false [(PathSegment.mk "throw_ub" PathArguments.none)])
                        MacroDelimiter.paren
                        (MacroBody.exprs
                          [(Expr.lit (Lit.str "invalid number of arguments for `Spawn` intrinsic"))]
                          false))
                      true)])
                none)
              false),
            (Stmt.letStmt
              []
              (Pat.ident false false "fn_ptr" none)
              (some
                (Expr.field
                  (Expr.index
                    (Expr.path
                      none
                      (Path.mk false [(PathSegment.mk "arguments" PathArguments.none)]))
                    (Expr.lit (Lit.int 0 "")))
                  (Member.unnamed 0)))
              none),
            (Stmt.letStmt
              []
              (Pat.ident false false "func" none)
              (some
                (Expr.tryExpr
                  (Expr.methodCall
                    (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                    "fn_from_ptr"
                    none
                    [
                      (Expr.path
                        none
                        (Path.mk false [(PathSegment.mk "fn_ptr" PathArguments.none)]))])))
              none),
            (Stmt.letStmt
              []
              (Pat.tuple
                [
                  (Pat.ident false false "data_ptr" none),
                  (Pat.ident false false "data_ptr_ty" none)])
              (some
                (Expr.index
                  (Expr.path none (Path.mk false [(PathSegment.mk "arguments" PathArguments.none)]))
                  (Expr.lit (Lit.int 1 ""))))
              none),
            (Stmt.expr
              (Expr.ite
                (Expr.unary
                  UnOp.not
                  (Expr.macro
                    (Macro.mk
                      (Path.mk false [(PathSegment.mk "matches" PathArguments.none)])
                      MacroDelimiter.paren
                      (MacroBody.exprAndPat
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "data_ptr_ty" PathArguments.none)]))
                        (Pat.tupleStruct
                          none
                          (Path.mk
                            false
                            [
                              (PathSegment.mk "Type" PathArguments.none),
                              (PathSegment.mk "Ptr" PathArguments.none)])
                          [Pat.wild])
                        none))))
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
                                "invalid second argument to `Spawn` intrinsic: not a pointer"))]
                          false))
                      true)])
                none)
              false),
            (Stmt.expr
              (Expr.ite
                (Expr.unary
                  UnOp.not
                  (Expr.macro
                    (Macro.mk
                      (Path.mk false [(PathSegment.mk "matches" PathArguments.none)])
                      MacroDelimiter.paren
                      (MacroBody.exprAndPat
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "ret_ty" PathArguments.none)]))
                        (Pat.tupleStruct
                          none
                          (Path.mk
                            false
                            [
                              (PathSegment.mk "Type" PathArguments.none),
                              (PathSegment.mk "Int" PathArguments.none)])
                          [Pat.wild])
                        none))))
                (Block.mk
                  [
                    (Stmt.expr
                      (Expr.macro
                        (Macro.mk
                          (Path.mk false [(PathSegment.mk "throw_ub" PathArguments.none)])
                          MacroDelimiter.paren
                          (MacroBody.exprs
                            [(Expr.lit (Lit.str "invalid return type for `Spawn` intrinsic"))]
                            false)))
                      false)])
                none)
              false),
            (Stmt.letStmt
              []
              (Pat.ident false false "thread_id" none)
              (some
                (Expr.tryExpr
                  (Expr.methodCall
                    (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                    "spawn"
                    none
                    [
                      (Expr.path none (Path.mk false [(PathSegment.mk "func" PathArguments.none)])),
                      (Expr.path
                        none
                        (Path.mk false [(PathSegment.mk "data_ptr" PathArguments.none)])),
                      (Expr.path
                        none
                        (Path.mk false [(PathSegment.mk "data_ptr_ty" PathArguments.none)]))])))
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
                          (PathSegment.mk "Value" PathArguments.none),
                          (PathSegment.mk "Int" PathArguments.none)]))
                    [
                      (Expr.path
                        none
                        (Path.mk false [(PathSegment.mk "thread_id" PathArguments.none)]))])])
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
          "join"
          (Generics.mk [] [])
          [
            (FnArg.receiver [] true none true none),
            (FnArg.typed
              []
              (Pat.ident false false "thread_id" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "ThreadId" PathArguments.none)])))]
          false
          (some (Ty.path none (Path.mk false [(PathSegment.mk "NdResult" PathArguments.none)]))))
        (Block.mk
          [
            (Stmt.letStmt
              []
              (Pat.tupleStruct
                none
                (Path.mk false [(PathSegment.mk "Some" PathArguments.none)])
                [(Pat.ident false false "thread" none)])
              (some
                (Expr.methodCall
                  (Expr.field
                    (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                    (Member.named "threads"))
                  "get"
                  none
                  [
                    (Expr.path
                      none
                      (Path.mk false [(PathSegment.mk "thread_id" PathArguments.none)]))]))
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
                            [(Expr.lit (Lit.str "`Join` intrinsic: join non existing thread"))]
                            false))
                        true)])))),
            (Stmt.expr
              (Expr.matchExpr
                (Expr.field
                  (Expr.path none (Path.mk false [(PathSegment.mk "thread" PathArguments.none)]))
                  (Member.named "state"))
                [
                  (Arm.mk
                    []
                    (Pat.path
                      none
                      (Path.mk
                        false
                        [
                          (PathSegment.mk "ThreadState" PathArguments.none),
                          (PathSegment.mk "Terminated" PathArguments.none)]))
                    none
                    (Expr.block none (Block.mk []))),
                  (Arm.mk
                    []
                    Pat.wild
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
                                  (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                                (Member.named "threads"))
                              "mutate_at"
                              none
                              [
                                (Expr.field
                                  (Expr.path
                                    none
                                    (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                                  (Member.named "active_thread")),
                                (Expr.closure
                                  false
                                  [(Pat.ident false false "thread" none)]
                                  none
                                  (Expr.block
                                    none
                                    (Block.mk
                                      [
                                        (Stmt.expr
                                          (Expr.assign
                                            (Expr.field
                                              (Expr.path
                                                none
                                                (Path.mk
                                                  false
                                                  [(PathSegment.mk "thread" PathArguments.none)]))
                                              (Member.named "state"))
                                            (Expr.call
                                              (Expr.path
                                                none
                                                (Path.mk
                                                  false
                                                  [
                                                    (PathSegment.mk
                                                      "ThreadState"
                                                      PathArguments.none),
                                                    (PathSegment.mk
                                                      "BlockedOnJoin"
                                                      PathArguments.none)]))
                                              [
                                                (Expr.path
                                                  none
                                                  (Path.mk
                                                    false
                                                    [
                                                      (PathSegment.mk
                                                        "thread_id"
                                                        PathArguments.none)]))]))
                                          true)])))])
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
          "eval_intrinsic"
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
                    (PathSegment.mk "IntrinsicOp" PathArguments.none),
                    (PathSegment.mk "Join" PathArguments.none)]))
              (Ty.path none (Path.mk false [(PathSegment.mk "IntrinsicOp" PathArguments.none)]))),
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
              (Pat.ident false false "ret_ty" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "Type" PathArguments.none)])))]
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
                (Expr.binary
                  (Expr.methodCall
                    (Expr.path
                      none
                      (Path.mk false [(PathSegment.mk "arguments" PathArguments.none)]))
                    "len"
                    none
                    [])
                  BinOp.ne
                  (Expr.lit (Lit.int 1 "")))
                (Block.mk
                  [
                    (Stmt.macro
                      []
                      (Macro.mk
                        (Path.mk false [(PathSegment.mk "throw_ub" PathArguments.none)])
                        MacroDelimiter.paren
                        (MacroBody.exprs
                          [(Expr.lit (Lit.str "invalid number of arguments for `Join` intrinsic"))]
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
                    (PathSegment.mk "Value" PathArguments.none),
                    (PathSegment.mk "Int" PathArguments.none)])
                [(Pat.ident false false "thread_id" none)])
              (some
                (Expr.field
                  (Expr.index
                    (Expr.path
                      none
                      (Path.mk false [(PathSegment.mk "arguments" PathArguments.none)]))
                    (Expr.lit (Lit.int 0 "")))
                  (Member.unnamed 0)))
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
                                  "invalid first argument to `Join` intrinsic: not an integer"))]
                            false))
                        true)])))),
            (Stmt.expr
              (Expr.ite
                (Expr.binary
                  (Expr.path none (Path.mk false [(PathSegment.mk "ret_ty" PathArguments.none)]))
                  BinOp.ne
                  (Expr.call
                    (Expr.path
                      none
                      (Path.mk false [(PathSegment.mk "unit_type" PathArguments.none)]))
                    []))
                (Block.mk
                  [
                    (Stmt.expr
                      (Expr.macro
                        (Macro.mk
                          (Path.mk false [(PathSegment.mk "throw_ub" PathArguments.none)])
                          MacroDelimiter.paren
                          (MacroBody.exprs
                            [(Expr.lit (Lit.str "invalid return type for `Join` intrinsic"))]
                            false)))
                      false)])
                none)
              false),
            (Stmt.expr
              (Expr.tryExpr
                (Expr.methodCall
                  (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                  "join"
                  none
                  [
                    (Expr.path
                      none
                      (Path.mk false [(PathSegment.mk "thread_id" PathArguments.none)]))]))
              true),
            (Stmt.expr
              (Expr.call
                (Expr.path none (Path.mk false [(PathSegment.mk "ret" PathArguments.none)]))
                [
                  (Expr.call
                    (Expr.path
                      none
                      (Path.mk false [(PathSegment.mk "unit_value" PathArguments.none)]))
                    [])])
              false)]))])

/-- `spec/lang/step/intrinsics.md:368` -/
def impl_Machine__load_raw_data : Item :=
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
          "load_raw_data"
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
                      "Pointer"
                      (PathArguments.angleBracketed
                        false
                        [
                          (GenericArgument.type
                            (Ty.path
                              (some
                                (QSelf.mk
                                  (Ty.path
                                    none
                                    (Path.mk false [(PathSegment.mk "M" PathArguments.none)]))
                                  1
                                  true))
                              (Path.mk
                                false
                                [
                                  (PathSegment.mk "Memory" PathArguments.none),
                                  (PathSegment.mk "Provenance" PathArguments.none)])))]))]))),
            (FnArg.typed
              []
              (Pat.ident false false "ptr_ty" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "PtrType" PathArguments.none)])))]
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
                                          (Path.mk false [(PathSegment.mk "u8" PathArguments.none)])))]))])))]))]))))
        (Block.mk
          [
            (Stmt.letStmt
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
                    (Member.named "pointee")
                    true
                    (Pat.ident false false "pointee" none))]
                true)
              (some (Expr.path none (Path.mk false [(PathSegment.mk "ptr_ty" PathArguments.none)])))
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
                                (Lit.str "invalid argument to `RawEq` intrinsic: not a reference"))]
                            false))
                        true)])))),
            (Stmt.letStmt
              []
              (Pat.struct
                none
                (Path.mk false [(PathSegment.mk "PointeeInfo" PathArguments.none)])
                [
                  (FieldPat.mk
                    []
                    (Member.named "layout")
                    false
                    (Pat.tupleStruct
                      none
                      (Path.mk
                        false
                        [
                          (PathSegment.mk "LayoutStrategy" PathArguments.none),
                          (PathSegment.mk "Sized" PathArguments.none)])
                      [(Pat.ident false false "size" none), (Pat.ident false false "align" none)]))]
                true)
              (some
                (Expr.path none (Path.mk false [(PathSegment.mk "pointee" PathArguments.none)])))
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
                                (Lit.str "invalid argument to `RawEq` intrinsic: unsized pointee"))]
                            false))
                        true)])))),
            (Stmt.letStmt
              []
              (Pat.ident false false "bytes" none)
              (some
                (Expr.tryExpr
                  (Expr.methodCall
                    (Expr.field
                      (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                      (Member.named "mem"))
                    "load"
                    none
                    [
                      (Expr.field
                        (Expr.path none (Path.mk false [(PathSegment.mk "ptr" PathArguments.none)]))
                        (Member.named "thin_pointer")),
                      (Expr.path none (Path.mk false [(PathSegment.mk "size" PathArguments.none)])),
                      (Expr.path none (Path.mk false [(PathSegment.mk "align" PathArguments.none)])),
                      (Expr.path
                        none
                        (Path.mk
                          false
                          [
                            (PathSegment.mk "Atomicity" PathArguments.none),
                            (PathSegment.mk "None" PathArguments.none)]))])))
              none),
            (Stmt.letStmt
              []
              (Pat.tupleStruct
                none
                (Path.mk false [(PathSegment.mk "Some" PathArguments.none)])
                [(Pat.ident false false "data" none)])
              (some
                (Expr.methodCall
                  (Expr.path none (Path.mk false [(PathSegment.mk "bytes" PathArguments.none)]))
                  "try_map"
                  none
                  [
                    (Expr.closure
                      false
                      [(Pat.ident false false "byte" none)]
                      none
                      (Expr.methodCall
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "byte" PathArguments.none)]))
                        "data"
                        none
                        []))]))
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
                                  "invalid argument to `RawEq` intrinsic: byte is uninitialized"))]
                            false))
                        true)])))),
            (Stmt.expr
              (Expr.call
                (Expr.path none (Path.mk false [(PathSegment.mk "Ok" PathArguments.none)]))
                [(Expr.path none (Path.mk false [(PathSegment.mk "data" PathArguments.none)]))])
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
          "eval_intrinsic"
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
                    (PathSegment.mk "IntrinsicOp" PathArguments.none),
                    (PathSegment.mk "RawEq" PathArguments.none)]))
              (Ty.path none (Path.mk false [(PathSegment.mk "IntrinsicOp" PathArguments.none)]))),
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
              (Pat.ident false false "ret_ty" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "Type" PathArguments.none)])))]
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
                (Expr.binary
                  (Expr.methodCall
                    (Expr.path
                      none
                      (Path.mk false [(PathSegment.mk "arguments" PathArguments.none)]))
                    "len"
                    none
                    [])
                  BinOp.ne
                  (Expr.lit (Lit.int 2 "")))
                (Block.mk
                  [
                    (Stmt.macro
                      []
                      (Macro.mk
                        (Path.mk false [(PathSegment.mk "throw_ub" PathArguments.none)])
                        MacroDelimiter.paren
                        (MacroBody.exprs
                          [(Expr.lit (Lit.str "invalid number of arguments for `RawEq` intrinsic"))]
                          false))
                      true)])
                none)
              false),
            (Stmt.expr
              (Expr.ite
                (Expr.binary
                  (Expr.path none (Path.mk false [(PathSegment.mk "ret_ty" PathArguments.none)]))
                  BinOp.ne
                  (Expr.path
                    none
                    (Path.mk
                      false
                      [
                        (PathSegment.mk "Type" PathArguments.none),
                        (PathSegment.mk "Bool" PathArguments.none)])))
                (Block.mk
                  [
                    (Stmt.expr
                      (Expr.macro
                        (Macro.mk
                          (Path.mk false [(PathSegment.mk "throw_ub" PathArguments.none)])
                          MacroDelimiter.paren
                          (MacroBody.exprs
                            [(Expr.lit (Lit.str "invalid return type for `RawEq` intrinsic"))]
                            false)))
                      false)])
                none)
              false),
            (Stmt.letStmt
              []
              (Pat.tuple [(Pat.ident false false "left" none), (Pat.ident false false "l_ty" none)])
              (some
                (Expr.methodCall
                  (Expr.paren
                    (Expr.path
                      none
                      (Path.mk false [(PathSegment.mk "arguments" PathArguments.none)])))
                  "index_at"
                  none
                  [(Expr.lit (Lit.int 0 ""))]))
              none),
            (Stmt.letStmt
              []
              (Pat.tuple
                [(Pat.ident false false "right" none), (Pat.ident false false "r_ty" none)])
              (some
                (Expr.methodCall
                  (Expr.paren
                    (Expr.path
                      none
                      (Path.mk false [(PathSegment.mk "arguments" PathArguments.none)])))
                  "index_at"
                  none
                  [(Expr.lit (Lit.int 1 ""))]))
              none),
            (Stmt.expr
              (Expr.ite
                (Expr.binary
                  (Expr.path none (Path.mk false [(PathSegment.mk "l_ty" PathArguments.none)]))
                  BinOp.ne
                  (Expr.path none (Path.mk false [(PathSegment.mk "r_ty" PathArguments.none)])))
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
                                "invalid arguments to `RawEq` intrinsic: types of arguments are not identical"))]
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
                    (PathSegment.mk "Value" PathArguments.none),
                    (PathSegment.mk "Ptr" PathArguments.none)])
                [(Pat.ident false false "left" none)])
              (some (Expr.path none (Path.mk false [(PathSegment.mk "left" PathArguments.none)])))
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
                                  "invalid first argument to `RawEq` intrinsic: not a pointer"))]
                            false))
                        true)])))),
            (Stmt.letStmt
              []
              (Pat.tupleStruct
                none
                (Path.mk
                  false
                  [
                    (PathSegment.mk "Value" PathArguments.none),
                    (PathSegment.mk "Ptr" PathArguments.none)])
                [(Pat.ident false false "right" none)])
              (some (Expr.path none (Path.mk false [(PathSegment.mk "right" PathArguments.none)])))
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
                                  "invalid second argument to `RawEq` intrinsic: not a pointer"))]
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
                    (PathSegment.mk "Ptr" PathArguments.none)])
                [(Pat.ident false false "l_ty" none)])
              (some (Expr.path none (Path.mk false [(PathSegment.mk "l_ty" PathArguments.none)])))
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
                                  "invalid argument type to `RawEq` intrinsic: not a pointer"))]
                            false))
                        true)])))),
            (Stmt.letStmt
              []
              (Pat.ident false false "left_data" none)
              (some
                (Expr.tryExpr
                  (Expr.methodCall
                    (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                    "load_raw_data"
                    none
                    [
                      (Expr.path none (Path.mk false [(PathSegment.mk "left" PathArguments.none)])),
                      (Expr.path none (Path.mk false [(PathSegment.mk "l_ty" PathArguments.none)]))])))
              none),
            (Stmt.letStmt
              []
              (Pat.ident false false "right_data" none)
              (some
                (Expr.tryExpr
                  (Expr.methodCall
                    (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                    "load_raw_data"
                    none
                    [
                      (Expr.path none (Path.mk false [(PathSegment.mk "right" PathArguments.none)])),
                      (Expr.path none (Path.mk false [(PathSegment.mk "l_ty" PathArguments.none)]))])))
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
                          (PathSegment.mk "Value" PathArguments.none),
                          (PathSegment.mk "Bool" PathArguments.none)]))
                    [
                      (Expr.binary
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "left_data" PathArguments.none)]))
                        BinOp.eq
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "right_data" PathArguments.none)])))])])
              false)]))])

/-- `spec/lang/step/intrinsics.md:431` -/
def impl_Machine__eval_intrinsic_6 : Item :=
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
          "eval_intrinsic"
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
                    (PathSegment.mk "IntrinsicOp" PathArguments.none),
                    (PathSegment.mk "AtomicStore" PathArguments.none)]))
              (Ty.path none (Path.mk false [(PathSegment.mk "IntrinsicOp" PathArguments.none)]))),
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
              (Pat.ident false false "ret_ty" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "Type" PathArguments.none)])))]
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
                (Expr.binary
                  (Expr.methodCall
                    (Expr.path
                      none
                      (Path.mk false [(PathSegment.mk "arguments" PathArguments.none)]))
                    "len"
                    none
                    [])
                  BinOp.ne
                  (Expr.lit (Lit.int 2 "")))
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
                              (Lit.str "invalid number of arguments for `AtomicStore` intrinsic"))]
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
                        (Pat.ident false false "ptr" none)),
                      (FieldPat.mk
                        []
                        (Member.named "metadata")
                        false
                        (Pat.ident false false "None" none))]
                    false)])
              (some
                (Expr.field
                  (Expr.index
                    (Expr.path
                      none
                      (Path.mk false [(PathSegment.mk "arguments" PathArguments.none)]))
                    (Expr.lit (Lit.int 0 "")))
                  (Member.unnamed 0)))
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
                                  "invalid first argument to `AtomicStore` intrinsic: not a thin pointer"))]
                            false))
                        true)])))),
            (Stmt.letStmt
              []
              (Pat.tuple [(Pat.ident false false "val" none), (Pat.ident false false "ty" none)])
              (some
                (Expr.index
                  (Expr.path none (Path.mk false [(PathSegment.mk "arguments" PathArguments.none)]))
                  (Expr.lit (Lit.int 1 ""))))
              none),
            (Stmt.letStmt
              []
              (Pat.tupleStruct
                none
                (Path.mk
                  false
                  [
                    (PathSegment.mk "LayoutStrategy" PathArguments.none),
                    (PathSegment.mk "Sized" PathArguments.none)])
                [(Pat.ident false false "size" none), Pat.wild])
              (some
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
                  []))
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
                                  "invalid second argument to `AtomicStore` intrinsic: unsized type"))]
                            false))
                        true)])))),
            (Stmt.letStmt
              []
              (Pat.tupleStruct
                none
                (Path.mk false [(PathSegment.mk "Some" PathArguments.none)])
                [(Pat.ident false false "align" none)])
              (some
                (Expr.call
                  (Expr.path
                    none
                    (Path.mk
                      false
                      [
                        (PathSegment.mk "Align" PathArguments.none),
                        (PathSegment.mk "from_bytes" PathArguments.none)]))
                  [
                    (Expr.methodCall
                      (Expr.path none (Path.mk false [(PathSegment.mk "size" PathArguments.none)]))
                      "bytes"
                      none
                      [])]))
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
                                  "invalid second argument to `AtomicStore` intrinsic: size not power of two"))]
                            false))
                        true)])))),
            (Stmt.expr
              (Expr.ite
                (Expr.binary
                  (Expr.path none (Path.mk false [(PathSegment.mk "size" PathArguments.none)]))
                  BinOp.gt
                  (Expr.path
                    none
                    (Path.mk
                      false
                      [
                        (PathSegment.mk "M" PathArguments.none),
                        (PathSegment.mk "T" PathArguments.none),
                        (PathSegment.mk "MAX_ATOMIC_SIZE" PathArguments.none)])))
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
                                "invalid second argument to `AtomicStore` intrinsic: size too big"))]
                          false))
                      true)])
                none)
              false),
            (Stmt.expr
              (Expr.ite
                (Expr.binary
                  (Expr.path none (Path.mk false [(PathSegment.mk "ret_ty" PathArguments.none)]))
                  BinOp.ne
                  (Expr.call
                    (Expr.path
                      none
                      (Path.mk false [(PathSegment.mk "unit_type" PathArguments.none)]))
                    []))
                (Block.mk
                  [
                    (Stmt.expr
                      (Expr.macro
                        (Macro.mk
                          (Path.mk false [(PathSegment.mk "throw_ub" PathArguments.none)])
                          MacroDelimiter.paren
                          (MacroBody.exprs
                            [(Expr.lit (Lit.str "invalid return type for `AtomicStore` intrinsic"))]
                            false)))
                      false)])
                none)
              false),
            (Stmt.expr
              (Expr.tryExpr
                (Expr.methodCall
                  (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                  "typed_store"
                  none
                  [
                    (Expr.path none (Path.mk false [(PathSegment.mk "ptr" PathArguments.none)])),
                    (Expr.path none (Path.mk false [(PathSegment.mk "val" PathArguments.none)])),
                    (Expr.path none (Path.mk false [(PathSegment.mk "ty" PathArguments.none)])),
                    (Expr.path none (Path.mk false [(PathSegment.mk "align" PathArguments.none)])),
                    (Expr.path
                      none
                      (Path.mk
                        false
                        [
                          (PathSegment.mk "Atomicity" PathArguments.none),
                          (PathSegment.mk "Atomic" PathArguments.none)]))]))
              true),
            (Stmt.expr
              (Expr.call
                (Expr.path none (Path.mk false [(PathSegment.mk "ret" PathArguments.none)]))
                [
                  (Expr.call
                    (Expr.path
                      none
                      (Path.mk false [(PathSegment.mk "unit_value" PathArguments.none)]))
                    [])])
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
          "eval_intrinsic"
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
                    (PathSegment.mk "IntrinsicOp" PathArguments.none),
                    (PathSegment.mk "AtomicLoad" PathArguments.none)]))
              (Ty.path none (Path.mk false [(PathSegment.mk "IntrinsicOp" PathArguments.none)]))),
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
              (Pat.ident false false "ret_ty" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "Type" PathArguments.none)])))]
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
                (Expr.binary
                  (Expr.methodCall
                    (Expr.path
                      none
                      (Path.mk false [(PathSegment.mk "arguments" PathArguments.none)]))
                    "len"
                    none
                    [])
                  BinOp.ne
                  (Expr.lit (Lit.int 1 "")))
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
                              (Lit.str "invalid number of arguments for `AtomicLoad` intrinsic"))]
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
                        (Pat.ident false false "ptr" none)),
                      (FieldPat.mk
                        []
                        (Member.named "metadata")
                        false
                        (Pat.ident false false "None" none))]
                    false)])
              (some
                (Expr.field
                  (Expr.index
                    (Expr.path
                      none
                      (Path.mk false [(PathSegment.mk "arguments" PathArguments.none)]))
                    (Expr.lit (Lit.int 0 "")))
                  (Member.unnamed 0)))
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
                                  "invalid first argument to `AtomicLoad` intrinsic: not a thin pointer"))]
                            false))
                        true)])))),
            (Stmt.letStmt
              []
              (Pat.ident false false "size" none)
              (some
                (Expr.methodCall
                  (Expr.methodCall
                    (Expr.path none (Path.mk false [(PathSegment.mk "ret_ty" PathArguments.none)]))
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
                  [(Expr.lit (Lit.str "WF ensures intrinsic return types are sized"))]))
              none),
            (Stmt.letStmt
              []
              (Pat.tupleStruct
                none
                (Path.mk false [(PathSegment.mk "Some" PathArguments.none)])
                [(Pat.ident false false "align" none)])
              (some
                (Expr.call
                  (Expr.path
                    none
                    (Path.mk
                      false
                      [
                        (PathSegment.mk "Align" PathArguments.none),
                        (PathSegment.mk "from_bytes" PathArguments.none)]))
                  [
                    (Expr.methodCall
                      (Expr.path none (Path.mk false [(PathSegment.mk "size" PathArguments.none)]))
                      "bytes"
                      none
                      [])]))
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
                                  "invalid return type for `AtomicLoad` intrinsic: size not power of two"))]
                            false))
                        true)])))),
            (Stmt.expr
              (Expr.ite
                (Expr.binary
                  (Expr.path none (Path.mk false [(PathSegment.mk "size" PathArguments.none)]))
                  BinOp.gt
                  (Expr.path
                    none
                    (Path.mk
                      false
                      [
                        (PathSegment.mk "M" PathArguments.none),
                        (PathSegment.mk "T" PathArguments.none),
                        (PathSegment.mk "MAX_ATOMIC_SIZE" PathArguments.none)])))
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
                                "invalid return type for `AtomicLoad` intrinsic: size too big"))]
                          false))
                      true)])
                none)
              false),
            (Stmt.letStmt
              []
              (Pat.ident false false "val" none)
              (some
                (Expr.tryExpr
                  (Expr.methodCall
                    (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                    "typed_load"
                    none
                    [
                      (Expr.path none (Path.mk false [(PathSegment.mk "ptr" PathArguments.none)])),
                      (Expr.path
                        none
                        (Path.mk false [(PathSegment.mk "ret_ty" PathArguments.none)])),
                      (Expr.path none (Path.mk false [(PathSegment.mk "align" PathArguments.none)])),
                      (Expr.path
                        none
                        (Path.mk
                          false
                          [
                            (PathSegment.mk "Atomicity" PathArguments.none),
                            (PathSegment.mk "Atomic" PathArguments.none)]))])))
              none),
            (Stmt.expr
              (Expr.call
                (Expr.path none (Path.mk false [(PathSegment.mk "ret" PathArguments.none)]))
                [(Expr.path none (Path.mk false [(PathSegment.mk "val" PathArguments.none)]))])
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
          "eval_intrinsic"
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
                    (PathSegment.mk "IntrinsicOp" PathArguments.none),
                    (PathSegment.mk "AtomicCompareExchange" PathArguments.none)]))
              (Ty.path none (Path.mk false [(PathSegment.mk "IntrinsicOp" PathArguments.none)]))),
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
              (Pat.ident false false "ret_ty" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "Type" PathArguments.none)])))]
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
                (Expr.binary
                  (Expr.methodCall
                    (Expr.path
                      none
                      (Path.mk false [(PathSegment.mk "arguments" PathArguments.none)]))
                    "len"
                    none
                    [])
                  BinOp.ne
                  (Expr.lit (Lit.int 3 "")))
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
                                "invalid number of arguments for `AtomicCompareExchange` intrinsic"))]
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
                        (Pat.ident false false "ptr" none)),
                      (FieldPat.mk
                        []
                        (Member.named "metadata")
                        false
                        (Pat.ident false false "None" none))]
                    false)])
              (some
                (Expr.field
                  (Expr.index
                    (Expr.path
                      none
                      (Path.mk false [(PathSegment.mk "arguments" PathArguments.none)]))
                    (Expr.lit (Lit.int 0 "")))
                  (Member.unnamed 0)))
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
                                  "invalid first argument to `AtomicCompareExchange` intrinsic: not a thin pointer"))]
                            false))
                        true)])))),
            (Stmt.letStmt
              []
              (Pat.tuple
                [(Pat.ident false false "current" none), (Pat.ident false false "curr_ty" none)])
              (some
                (Expr.index
                  (Expr.path none (Path.mk false [(PathSegment.mk "arguments" PathArguments.none)]))
                  (Expr.lit (Lit.int 1 ""))))
              none),
            (Stmt.expr
              (Expr.ite
                (Expr.binary
                  (Expr.path none (Path.mk false [(PathSegment.mk "curr_ty" PathArguments.none)]))
                  BinOp.ne
                  (Expr.path none (Path.mk false [(PathSegment.mk "ret_ty" PathArguments.none)])))
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
                                "invalid second argument to `AtomicCompareExchange` intrinsic: not same type as return value"))]
                          false))
                      true)])
                none)
              false),
            (Stmt.letStmt
              []
              (Pat.tuple
                [(Pat.ident false false "next" none), (Pat.ident false false "next_ty" none)])
              (some
                (Expr.index
                  (Expr.path none (Path.mk false [(PathSegment.mk "arguments" PathArguments.none)]))
                  (Expr.lit (Lit.int 2 ""))))
              none),
            (Stmt.expr
              (Expr.ite
                (Expr.binary
                  (Expr.path none (Path.mk false [(PathSegment.mk "next_ty" PathArguments.none)]))
                  BinOp.ne
                  (Expr.path none (Path.mk false [(PathSegment.mk "ret_ty" PathArguments.none)])))
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
                                "invalid third argument to `AtomicCompareExchange` intrinsic: not same type as return value"))]
                          false))
                      true)])
                none)
              false),
            (Stmt.expr
              (Expr.ite
                (Expr.unary
                  UnOp.not
                  (Expr.macro
                    (Macro.mk
                      (Path.mk false [(PathSegment.mk "matches" PathArguments.none)])
                      MacroDelimiter.paren
                      (MacroBody.exprAndPat
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "ret_ty" PathArguments.none)]))
                        (Pat.tupleStruct
                          none
                          (Path.mk
                            false
                            [
                              (PathSegment.mk "Type" PathArguments.none),
                              (PathSegment.mk "Int" PathArguments.none)])
                          [Pat.wild])
                        none))))
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
                                "invalid return type for `Intrinis::AtomicCompareExchange`: only works with integers"))]
                          false))
                      true)])
                none)
              false),
            (Stmt.letStmt
              []
              (Pat.ident false false "size" none)
              (some
                (Expr.methodCall
                  (Expr.methodCall
                    (Expr.path none (Path.mk false [(PathSegment.mk "ret_ty" PathArguments.none)]))
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
                  [(Expr.lit (Lit.str "`ret_ty` is an integer"))]))
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
                      (Expr.methodCall
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "size" PathArguments.none)]))
                        "bytes"
                        none
                        [])])
                  "unwrap"
                  none
                  []))
              none),
            (Stmt.expr
              (Expr.ite
                (Expr.binary
                  (Expr.path none (Path.mk false [(PathSegment.mk "size" PathArguments.none)]))
                  BinOp.gt
                  (Expr.path
                    none
                    (Path.mk
                      false
                      [
                        (PathSegment.mk "M" PathArguments.none),
                        (PathSegment.mk "T" PathArguments.none),
                        (PathSegment.mk "MAX_ATOMIC_SIZE" PathArguments.none)])))
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
                                "invalid return type for `AtomicCompareExchange` intrinsic: size too big"))]
                          false))
                      true)])
                none)
              false),
            (Stmt.letStmt
              []
              (Pat.ident false false "before" none)
              (some
                (Expr.tryExpr
                  (Expr.methodCall
                    (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                    "typed_load"
                    none
                    [
                      (Expr.path none (Path.mk false [(PathSegment.mk "ptr" PathArguments.none)])),
                      (Expr.path
                        none
                        (Path.mk false [(PathSegment.mk "ret_ty" PathArguments.none)])),
                      (Expr.path none (Path.mk false [(PathSegment.mk "align" PathArguments.none)])),
                      (Expr.path
                        none
                        (Path.mk
                          false
                          [
                            (PathSegment.mk "Atomicity" PathArguments.none),
                            (PathSegment.mk "Atomic" PathArguments.none)]))])))
              none),
            (Stmt.expr
              (Expr.ite
                (Expr.binary
                  (Expr.path none (Path.mk false [(PathSegment.mk "current" PathArguments.none)]))
                  BinOp.eq
                  (Expr.path none (Path.mk false [(PathSegment.mk "before" PathArguments.none)])))
                (Block.mk
                  [
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
                              (Path.mk false [(PathSegment.mk "ptr" PathArguments.none)])),
                            (Expr.path
                              none
                              (Path.mk false [(PathSegment.mk "next" PathArguments.none)])),
                            (Expr.path
                              none
                              (Path.mk false [(PathSegment.mk "ret_ty" PathArguments.none)])),
                            (Expr.path
                              none
                              (Path.mk false [(PathSegment.mk "align" PathArguments.none)])),
                            (Expr.path
                              none
                              (Path.mk
                                false
                                [
                                  (PathSegment.mk "Atomicity" PathArguments.none),
                                  (PathSegment.mk "Atomic" PathArguments.none)]))]))
                      true)])
                (some (Expr.block none (Block.mk []))))
              false),
            (Stmt.expr
              (Expr.call
                (Expr.path none (Path.mk false [(PathSegment.mk "ret" PathArguments.none)]))
                [(Expr.path none (Path.mk false [(PathSegment.mk "before" PathArguments.none)]))])
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
          "eval_intrinsic"
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
                    (PathSegment.mk "IntrinsicOp" PathArguments.none),
                    (PathSegment.mk "AtomicFetchAndOp" PathArguments.none)])
                [(Pat.ident false false "op" none)])
              (Ty.path none (Path.mk false [(PathSegment.mk "IntrinsicOp" PathArguments.none)]))),
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
              (Pat.ident false false "ret_ty" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "Type" PathArguments.none)])))]
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
                (Expr.binary
                  (Expr.methodCall
                    (Expr.path
                      none
                      (Path.mk false [(PathSegment.mk "arguments" PathArguments.none)]))
                    "len"
                    none
                    [])
                  BinOp.ne
                  (Expr.lit (Lit.int 2 "")))
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
                                "invalid number of arguments for `AtomicFetchAndOp` intrinsic"))]
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
                        (Pat.ident false false "ptr" none)),
                      (FieldPat.mk
                        []
                        (Member.named "metadata")
                        false
                        (Pat.ident false false "None" none))]
                    false)])
              (some
                (Expr.field
                  (Expr.index
                    (Expr.path
                      none
                      (Path.mk false [(PathSegment.mk "arguments" PathArguments.none)]))
                    (Expr.lit (Lit.int 0 "")))
                  (Member.unnamed 0)))
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
                                  "invalid first argument to `AtomicFetchAndOp` intrinsic: not a thin pointer"))]
                            false))
                        true)])))),
            (Stmt.letStmt
              []
              (Pat.tuple
                [(Pat.ident false false "other" none), (Pat.ident false false "other_ty" none)])
              (some
                (Expr.index
                  (Expr.path none (Path.mk false [(PathSegment.mk "arguments" PathArguments.none)]))
                  (Expr.lit (Lit.int 1 ""))))
              none),
            (Stmt.expr
              (Expr.ite
                (Expr.binary
                  (Expr.path none (Path.mk false [(PathSegment.mk "other_ty" PathArguments.none)]))
                  BinOp.ne
                  (Expr.path none (Path.mk false [(PathSegment.mk "ret_ty" PathArguments.none)])))
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
                                "invalid second argument to `AtomicFetchAndOp` intrinsic: not same type as return value"))]
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
                    (PathSegment.mk "Int" PathArguments.none)])
                [(Pat.ident false false "int_ty" none)])
              (some (Expr.path none (Path.mk false [(PathSegment.mk "ret_ty" PathArguments.none)])))
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
                                  "invalid return type for `AtomicFetchAndOp` intrinsic: only works with integers"))]
                            false))
                        true)])))),
            (Stmt.letStmt
              []
              (Pat.ident false false "size" none)
              (some
                (Expr.methodCall
                  (Expr.methodCall
                    (Expr.path none (Path.mk false [(PathSegment.mk "ret_ty" PathArguments.none)]))
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
                  [(Expr.lit (Lit.str "`ret_ty` is an integer"))]))
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
                      (Expr.methodCall
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "size" PathArguments.none)]))
                        "bytes"
                        none
                        [])])
                  "unwrap"
                  none
                  []))
              none),
            (Stmt.expr
              (Expr.ite
                (Expr.binary
                  (Expr.path none (Path.mk false [(PathSegment.mk "size" PathArguments.none)]))
                  BinOp.gt
                  (Expr.path
                    none
                    (Path.mk
                      false
                      [
                        (PathSegment.mk "M" PathArguments.none),
                        (PathSegment.mk "T" PathArguments.none),
                        (PathSegment.mk "MAX_ATOMIC_SIZE" PathArguments.none)])))
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
                                "invalid return type for `AtomicFetchAndOp` intrinsic: size too big"))]
                          false))
                      true)])
                none)
              false),
            (Stmt.letStmt
              []
              (Pat.ident false false "previous" none)
              (some
                (Expr.tryExpr
                  (Expr.methodCall
                    (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                    "typed_load"
                    none
                    [
                      (Expr.path none (Path.mk false [(PathSegment.mk "ptr" PathArguments.none)])),
                      (Expr.path
                        none
                        (Path.mk false [(PathSegment.mk "ret_ty" PathArguments.none)])),
                      (Expr.path none (Path.mk false [(PathSegment.mk "align" PathArguments.none)])),
                      (Expr.path
                        none
                        (Path.mk
                          false
                          [
                            (PathSegment.mk "Atomicity" PathArguments.none),
                            (PathSegment.mk "Atomic" PathArguments.none)]))])))
              none),
            (Stmt.letStmt
              []
              (Pat.tupleStruct
                none
                (Path.mk
                  false
                  [
                    (PathSegment.mk "Value" PathArguments.none),
                    (PathSegment.mk "Int" PathArguments.none)])
                [(Pat.ident false false "other_int" none)])
              (some (Expr.path none (Path.mk false [(PathSegment.mk "other" PathArguments.none)])))
              (some
                (Expr.block
                  none
                  (Block.mk
                    [
                      (Stmt.expr
                        (Expr.macro
                          (Macro.mk
                            (Path.mk false [(PathSegment.mk "unreachable" PathArguments.none)])
                            MacroDelimiter.paren
                            (MacroBody.exprs [] false)))
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
                [(Pat.ident false false "previous_int" none)])
              (some
                (Expr.path none (Path.mk false [(PathSegment.mk "previous" PathArguments.none)])))
              (some
                (Expr.block
                  none
                  (Block.mk
                    [
                      (Stmt.expr
                        (Expr.macro
                          (Macro.mk
                            (Path.mk false [(PathSegment.mk "unreachable" PathArguments.none)])
                            MacroDelimiter.paren
                            (MacroBody.exprs [] false)))
                        false)])))),
            (Stmt.letStmt
              []
              (Pat.ident false false "next_int" none)
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
                      (Expr.path
                        none
                        (Path.mk false [(PathSegment.mk "previous_int" PathArguments.none)])),
                      (Expr.path
                        none
                        (Path.mk false [(PathSegment.mk "other_int" PathArguments.none)])),
                      (Expr.path
                        none
                        (Path.mk false [(PathSegment.mk "int_ty" PathArguments.none)]))])))
              none),
            (Stmt.letStmt
              []
              (Pat.ident false false "next" none)
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
                    (Expr.path
                      none
                      (Path.mk false [(PathSegment.mk "next_int" PathArguments.none)]))]))
              none),
            (Stmt.expr
              (Expr.tryExpr
                (Expr.methodCall
                  (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                  "typed_store"
                  none
                  [
                    (Expr.path none (Path.mk false [(PathSegment.mk "ptr" PathArguments.none)])),
                    (Expr.path none (Path.mk false [(PathSegment.mk "next" PathArguments.none)])),
                    (Expr.path none (Path.mk false [(PathSegment.mk "ret_ty" PathArguments.none)])),
                    (Expr.path none (Path.mk false [(PathSegment.mk "align" PathArguments.none)])),
                    (Expr.path
                      none
                      (Path.mk
                        false
                        [
                          (PathSegment.mk "Atomicity" PathArguments.none),
                          (PathSegment.mk "Atomic" PathArguments.none)]))]))
              true),
            (Stmt.expr
              (Expr.call
                (Expr.path none (Path.mk false [(PathSegment.mk "ret" PathArguments.none)]))
                [(Expr.path none (Path.mk false [(PathSegment.mk "previous" PathArguments.none)]))])
              false)]))])

/-- `spec/lang/step/intrinsics.md:594` -/
def impl_Machine__eval_intrinsic_7 : Item :=
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
          "eval_intrinsic"
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
                    (PathSegment.mk "IntrinsicOp" PathArguments.none),
                    (PathSegment.mk "GetUnwindPayload" PathArguments.none)]))
              (Ty.path none (Path.mk false [(PathSegment.mk "IntrinsicOp" PathArguments.none)]))),
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
              (Pat.ident false false "ret_ty" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "Type" PathArguments.none)])))]
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
                (Expr.binary
                  (Expr.methodCall
                    (Expr.path
                      none
                      (Path.mk false [(PathSegment.mk "arguments" PathArguments.none)]))
                    "len"
                    none
                    [])
                  BinOp.ne
                  (Expr.lit (Lit.int 0 "")))
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
                                "invalid number of arguments for `GetUnwindPayload` intrinsic"))]
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
                [(Pat.ident false false "ret_ptr_ty" none)])
              (some (Expr.path none (Path.mk false [(PathSegment.mk "ret_ty" PathArguments.none)])))
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
                                (Lit.str "invalid return type for `GetUnwindPayload` intrinsic"))]
                            false))
                        true)])))),
            (Stmt.expr
              (Expr.ite
                (Expr.binary
                  (Expr.methodCall
                    (Expr.path
                      none
                      (Path.mk false [(PathSegment.mk "ret_ptr_ty" PathArguments.none)]))
                    "meta_kind"
                    none
                    [])
                  BinOp.ne
                  (Expr.path
                    none
                    (Path.mk
                      false
                      [
                        (PathSegment.mk "PointerMetaKind" PathArguments.none),
                        (PathSegment.mk "None" PathArguments.none)])))
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
                              (Lit.str "invalid return type for `GetUnwindPayload` intrinsic"))]
                          false))
                      true)])
                none)
              false),
            (Stmt.letStmt
              []
              (Pat.tupleStruct
                none
                (Path.mk false [(PathSegment.mk "Some" PathArguments.none)])
                [(Pat.ident false false "thin_pointer" none)])
              (some
                (Expr.methodCall
                  (Expr.field
                    (Expr.methodCall
                      (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                      "active_thread"
                      none
                      [])
                    (Member.named "unwind_payloads"))
                  "last"
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
                          (Path.mk false [(PathSegment.mk "throw_ub" PathArguments.none)])
                          MacroDelimiter.paren
                          (MacroBody.exprs
                            [(Expr.lit (Lit.str "GetUnwindPayload: the payload stack is empty"))]
                            false))
                        true)])))),
            (Stmt.letStmt
              []
              (Pat.ident false false "payload_pointer" none)
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
                          false
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "None" PathArguments.none)])))]
                      false
                      none)]))
              none),
            (Stmt.expr
              (Expr.call
                (Expr.path none (Path.mk false [(PathSegment.mk "ret" PathArguments.none)]))
                [
                  (Expr.path
                    none
                    (Path.mk false [(PathSegment.mk "payload_pointer" PathArguments.none)]))])
              false)]))])

/-- All items of `spec/lang/step/intrinsics.md`, in source order, with provenance. -/
def items : List SourceItem :=
  [
    (SourceItem.mk
      "impl_Machine__eval_intrinsic_0"
      6
      "5d890920f8b53633c0b8b1c7841e3a62c51b30c2138d755c0307a2b3e11c8209"
      impl_Machine__eval_intrinsic_0),
    (SourceItem.mk
      "fn_unit_value"
      20
      "0a91e31f5547c1052a78a95ac96c40b343f3b2bc38189ab78dd1b94f274eab32"
      fn_unit_value),
    (SourceItem.mk
      "fn_unit_type"
      24
      "e5319d8972997e62ca7755a596174a443334b56a66611720461950c348bc061f"
      fn_unit_type),
    (SourceItem.mk
      "impl_Machine__eval_intrinsic_1"
      36
      "65afb7e1883ddac2d0464581d08ee55e454ef2754d586fbc8f6edefb41a67982"
      impl_Machine__eval_intrinsic_1),
    (SourceItem.mk
      "impl_Machine__exit"
      85
      "ca01d7ad39695ec2fa845d42693cf956027d48291eef752eff08c9e3ed0b6872"
      impl_Machine__exit),
    (SourceItem.mk
      "impl_Machine__eval_intrinsic_2"
      107
      "9f177f4d2c1bfd29bb057babc4bf0fae8b6240060676ae8ac380b2c35b3ea3c2"
      impl_Machine__eval_intrinsic_2),
    (SourceItem.mk
      "impl_Machine__eval_intrinsic_3"
      122
      "45105631d9a57e54b226e857926fb705b80e5d431705fc50da1d80a6d9e9e4e3"
      impl_Machine__eval_intrinsic_3),
    (SourceItem.mk
      "impl_Machine__eval_intrinsic_4"
      153
      "a07c9c8db564461a144f50d0340084e68252057e609bdc962320ae8e1f55a33f"
      impl_Machine__eval_intrinsic_4),
    (SourceItem.mk
      "impl_Machine__eval_intrinsic_5"
      207
      "cddbceda26c34acf70e1cf3f98e553e4e11a42414870ab5dcf44e00d5a8d988b"
      impl_Machine__eval_intrinsic_5),
    (SourceItem.mk
      "impl_Machine__spawn"
      288
      "d4217884dd92457374c4f7bd22863b599f6772224b8257f7c497aae4ea4a7594"
      impl_Machine__spawn),
    (SourceItem.mk
      "impl_Machine__load_raw_data"
      368
      "fc630c0965ce20d3c0c26cbb42be75e246933f34832a118fdbbff5da00ce2c4b"
      impl_Machine__load_raw_data),
    (SourceItem.mk
      "impl_Machine__eval_intrinsic_6"
      431
      "5b392e961064afd4216a41b98689e0d1b0bcd06ea8c1a33d9445b57dd212d39d"
      impl_Machine__eval_intrinsic_6),
    (SourceItem.mk
      "impl_Machine__eval_intrinsic_7"
      594
      "13a6b2700cbccbc74f9ccc011334dffb4d0d22ed6c9761a5607a71ad7dfe9b37"
      impl_Machine__eval_intrinsic_7)]

end MiniRustSpec.Gen.Items.Lang.Step.Intrinsics
