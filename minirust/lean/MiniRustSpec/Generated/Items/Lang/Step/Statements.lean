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
`spec/lang/step/statements.md` (commit `d821c6e3`), one Lean definition per item, in source order.
-/

import MiniRustSpec.Meta.Syntax

set_option maxRecDepth 100000

namespace MiniRustSpec.Gen.Items.Lang.Step.Statements

open MiniRustSpec.Syntax

/-- Path of the upstream file these items were extracted from. -/
def sourceFile : String := "spec/lang/step/statements.md"

/-- SHA-256 of the upstream file. -/
def sourceSha256 : String := "737151ae844720a47d4f224e50c28e8eb54a2dc80f0b450dd2b1f495570716a9"

/-- `spec/lang/step/statements.md:7` -/
def impl_Machine__eval_statement_0 : Item :=
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
        [(Attr.mk true "specr::argmatch" (AttrMeta.list "statement"))]
        Visibility.inherited
        false
        (Signature.mk
          false
          false
          false
          none
          "eval_statement"
          (Generics.mk [] [])
          [
            (FnArg.receiver [] true none true none),
            (FnArg.typed
              []
              (Pat.ident false false "statement" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "Statement" PathArguments.none)])))]
          false
          (some (Ty.path none (Path.mk false [(PathSegment.mk "NdResult" PathArguments.none)]))))
        (Block.mk [(Stmt.expr (Expr.range none RangeLimits.halfOpen none) false)]))])

/-- `spec/lang/step/statements.md:22` -/
def impl_Machine__place_store : Item :=
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
          "place_store"
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
              (Pat.ident false false "val" none)
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
              (Pat.ident false false "ty" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "Type" PathArguments.none)])))]
          false
          (some (Ty.path none (Path.mk false [(PathSegment.mk "Result" PathArguments.none)]))))
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
                          [(Expr.lit (Lit.str "storing to a place based on a misaligned pointer"))]
                          false))
                      true)])
                none)
              false),
            (Stmt.expr
              (Expr.tryExpr
                (Expr.methodCall
                  (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                  "typed_store"
                  none
                  [
                    (Expr.field
                      (Expr.field
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "place" PathArguments.none)]))
                        (Member.named "ptr"))
                      (Member.named "thin_pointer")),
                    (Expr.path none (Path.mk false [(PathSegment.mk "val" PathArguments.none)])),
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
                          (PathSegment.mk "None" PathArguments.none)]))]))
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
          "eval_statement"
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
                    (PathSegment.mk "Statement" PathArguments.none),
                    (PathSegment.mk "Assign" PathArguments.none)])
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
              (Ty.path none (Path.mk false [(PathSegment.mk "Statement" PathArguments.none)])))]
          false
          (some (Ty.path none (Path.mk false [(PathSegment.mk "NdResult" PathArguments.none)]))))
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
                        (Path.mk false [(PathSegment.mk "destination" PathArguments.none)]))])))
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
                    [
                      (Expr.path
                        none
                        (Path.mk false [(PathSegment.mk "source" PathArguments.none)]))])))
              none),
            (Stmt.expr
              (Expr.tryExpr
                (Expr.methodCall
                  (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                  "place_store"
                  none
                  [
                    (Expr.path none (Path.mk false [(PathSegment.mk "place" PathArguments.none)])),
                    (Expr.path none (Path.mk false [(PathSegment.mk "val" PathArguments.none)])),
                    (Expr.path none (Path.mk false [(PathSegment.mk "ty" PathArguments.none)]))]))
              true),
            (Stmt.expr
              (Expr.call
                (Expr.path none (Path.mk false [(PathSegment.mk "ret" PathArguments.none)]))
                [(Expr.tuple [])])
              false)]))])

/-- `spec/lang/step/statements.md:49` -/
def impl_Machine__eval_statement_1 : Item :=
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
          "eval_statement"
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
                    (PathSegment.mk "Statement" PathArguments.none),
                    (PathSegment.mk "PlaceMention" PathArguments.none)])
                [(Pat.ident false false "place" none)])
              (Ty.path none (Path.mk false [(PathSegment.mk "Statement" PathArguments.none)])))]
          false
          (some (Ty.path none (Path.mk false [(PathSegment.mk "NdResult" PathArguments.none)]))))
        (Block.mk
          [
            (Stmt.expr
              (Expr.tryExpr
                (Expr.methodCall
                  (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                  "eval_place"
                  none
                  [(Expr.path none (Path.mk false [(PathSegment.mk "place" PathArguments.none)]))]))
              true),
            (Stmt.expr
              (Expr.call
                (Expr.path none (Path.mk false [(PathSegment.mk "ret" PathArguments.none)]))
                [(Expr.tuple [])])
              false)]))])

/-- `spec/lang/step/statements.md:60` -/
def impl_Machine__eval_statement_2 : Item :=
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
          "eval_statement"
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
                    (PathSegment.mk "Statement" PathArguments.none),
                    (PathSegment.mk "SetDiscriminant" PathArguments.none)])
                [
                  (FieldPat.mk
                    []
                    (Member.named "destination")
                    true
                    (Pat.ident false false "destination" none)),
                  (FieldPat.mk [] (Member.named "value") true (Pat.ident false false "value" none))]
                false)
              (Ty.path none (Path.mk false [(PathSegment.mk "Statement" PathArguments.none)])))]
          false
          (some (Ty.path none (Path.mk false [(PathSegment.mk "NdResult" PathArguments.none)]))))
        (Block.mk
          [
            (Stmt.letStmt
              []
              (Pat.tuple
                [
                  (Pat.ident false false "place" none),
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
                    true)])
              (some
                (Expr.tryExpr
                  (Expr.methodCall
                    (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                    "eval_place"
                    none
                    [
                      (Expr.path
                        none
                        (Path.mk false [(PathSegment.mk "destination" PathArguments.none)]))])))
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
                                (Lit.str
                                  "setting the discriminant type of a non-enum contradicts well-formedness"))]
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
                                "setting the discriminant of a place based on a misaligned pointer"))]
                          false))
                      true)])
                none)
              false),
            (Stmt.letStmt
              []
              (Pat.ident false false "tagger" none)
              (some
                (Expr.matchExpr
                  (Expr.methodCall
                    (Expr.path
                      none
                      (Path.mk false [(PathSegment.mk "variants" PathArguments.none)]))
                    "get"
                    none
                    [(Expr.path none (Path.mk false [(PathSegment.mk "value" PathArguments.none)]))])
                  [
                    (Arm.mk
                      []
                      (Pat.tupleStruct
                        none
                        (Path.mk false [(PathSegment.mk "Some" PathArguments.none)])
                        [
                          (Pat.struct
                            none
                            (Path.mk false [(PathSegment.mk "Variant" PathArguments.none)])
                            [
                              (FieldPat.mk
                                []
                                (Member.named "tagger")
                                true
                                (Pat.ident false false "tagger" none))]
                            true)])
                      none
                      (Expr.path
                        none
                        (Path.mk false [(PathSegment.mk "tagger" PathArguments.none)]))),
                    (Arm.mk
                      []
                      (Pat.ident false false "None" none)
                      none
                      (Expr.macro
                        (Macro.mk
                          (Path.mk false [(PathSegment.mk "panic" PathArguments.none)])
                          MacroDelimiter.paren
                          (MacroBody.exprs
                            [(Expr.lit (Lit.str "setting an invalid discriminant ({value})"))]
                            false))))]))
              none),
            (Stmt.letStmt
              []
              (Pat.ident false false "accessor" none)
              (some
                (Expr.closure
                  false
                  [
                    (Pat.typed
                      (Pat.ident false false "offset" none)
                      (Ty.path none (Path.mk false [(PathSegment.mk "Offset" PathArguments.none)]))),
                    (Pat.ident false false "bytes" none)]
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
                                      (Path.mk false [(PathSegment.mk "offset" PathArguments.none)]))
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
                            "store"
                            none
                            [
                              (Expr.path
                                none
                                (Path.mk false [(PathSegment.mk "ptr" PathArguments.none)])),
                              (Expr.path
                                none
                                (Path.mk false [(PathSegment.mk "bytes" PathArguments.none)])),
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
            (Stmt.expr
              (Expr.tryExpr
                (Expr.call
                  (Expr.path
                    none
                    (Path.mk
                      false
                      [
                        (PathSegment.mk
                          "encode_discriminant"
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
                    (Expr.path none (Path.mk false [(PathSegment.mk "tagger" PathArguments.none)]))]))
              true),
            (Stmt.expr
              (Expr.call
                (Expr.path none (Path.mk false [(PathSegment.mk "ret" PathArguments.none)]))
                [(Expr.tuple [])])
              false)]))])

/-- `spec/lang/step/statements.md:95` -/
def impl_Machine__retag_val : Item :=
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
              " Find all pointers in this value, ensure they are valid, and retag them."))]
        Visibility.inherited
        false
        (Signature.mk
          false
          false
          false
          none
          "retag_val"
          (Generics.mk [] [])
          [
            (FnArg.receiver [] true none true none),
            (FnArg.typed
              []
              (Pat.ident false false "val" none)
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
              (Pat.ident false false "ty" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "Type" PathArguments.none)]))),
            (FnArg.typed
              []
              (Pat.ident false false "fn_entry" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "bool" PathArguments.none)])))]
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
                    (Expr.tuple
                      [
                        (Expr.path none (Path.mk false [(PathSegment.mk "val" PathArguments.none)])),
                        (Expr.path none (Path.mk false [(PathSegment.mk "ty" PathArguments.none)]))])
                    [
                      (Arm.mk
                        []
                        (Pat.tuple
                          [
                            (Pat.or
                              [
                                (Pat.tupleStruct
                                  none
                                  (Path.mk
                                    false
                                    [
                                      (PathSegment.mk "Value" PathArguments.none),
                                      (PathSegment.mk "Int" PathArguments.none)])
                                  [Pat.rest]),
                                (Pat.tupleStruct
                                  none
                                  (Path.mk
                                    false
                                    [
                                      (PathSegment.mk "Value" PathArguments.none),
                                      (PathSegment.mk "Bool" PathArguments.none)])
                                  [Pat.rest]),
                                (Pat.tupleStruct
                                  none
                                  (Path.mk
                                    false
                                    [
                                      (PathSegment.mk "Value" PathArguments.none),
                                      (PathSegment.mk "Union" PathArguments.none)])
                                  [Pat.rest])]),
                            Pat.wild])
                        none
                        (Expr.path none (Path.mk false [(PathSegment.mk "val" PathArguments.none)]))),
                      (Arm.mk
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
                        none
                        (Expr.block
                          none
                          (Block.mk
                            [
                              (Stmt.letStmt
                                []
                                (Pat.ident false false "lookup" none)
                                (some
                                  (Expr.methodCall
                                    (Expr.path
                                      none
                                      (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                                    "vtable_lookup"
                                    none
                                    []))
                                none),
                              (Stmt.letStmt
                                []
                                (Pat.ident false false "val" none)
                                (some
                                  (Expr.tryExpr
                                    (Expr.methodCall
                                      (Expr.path
                                        none
                                        (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                                      "mutate_cur_frame"
                                      none
                                      [
                                        (Expr.closure
                                          false
                                          [
                                            (Pat.ident false false "frame" none),
                                            (Pat.ident false false "mem" none)]
                                          none
                                          (Expr.block
                                            none
                                            (Block.mk
                                              [
                                                (Stmt.expr
                                                  (Expr.methodCall
                                                    (Expr.path
                                                      none
                                                      (Path.mk
                                                        false
                                                        [(PathSegment.mk "mem" PathArguments.none)]))
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
                                                              [
                                                                (PathSegment.mk
                                                                  "frame"
                                                                  PathArguments.none)]))
                                                          (Member.named "extra"))),
                                                      (Expr.path
                                                        none
                                                        (Path.mk
                                                          false
                                                          [
                                                            (PathSegment.mk
                                                              "ptr"
                                                              PathArguments.none)])),
                                                      (Expr.path
                                                        none
                                                        (Path.mk
                                                          false
                                                          [
                                                            (PathSegment.mk
                                                              "ptr_type"
                                                              PathArguments.none)])),
                                                      (Expr.path
                                                        none
                                                        (Path.mk
                                                          false
                                                          [
                                                            (PathSegment.mk
                                                              "fn_entry"
                                                              PathArguments.none)])),
                                                      (Expr.field
                                                        (Expr.field
                                                          (Expr.path
                                                            none
                                                            (Path.mk
                                                              false
                                                              [
                                                                (PathSegment.mk
                                                                  "frame"
                                                                  PathArguments.none)]))
                                                          (Member.named "func"))
                                                        (Member.named "implicit_writes")),
                                                      (Expr.path
                                                        none
                                                        (Path.mk
                                                          false
                                                          [
                                                            (PathSegment.mk
                                                              "lookup"
                                                              PathArguments.none)]))])
                                                  false)])))])))
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
                                    (Expr.path
                                      none
                                      (Path.mk false [(PathSegment.mk "val" PathArguments.none)]))])
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
                                  (PathSegment.mk "Value" PathArguments.none),
                                  (PathSegment.mk "Tuple" PathArguments.none)])
                              [(Pat.ident false false "vals" none)]),
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
                                  (Pat.ident false false "sized_fields" none))]
                              true)])
                        none
                        (Expr.call
                          (Expr.path
                            none
                            (Path.mk
                              false
                              [
                                (PathSegment.mk "Value" PathArguments.none),
                                (PathSegment.mk "Tuple" PathArguments.none)]))
                          [
                            (Expr.tryExpr
                              (Expr.methodCall
                                (Expr.methodCall
                                  (Expr.path
                                    none
                                    (Path.mk false [(PathSegment.mk "vals" PathArguments.none)]))
                                  "zip"
                                  none
                                  [
                                    (Expr.path
                                      none
                                      (Path.mk
                                        false
                                        [(PathSegment.mk "sized_fields" PathArguments.none)]))])
                                "try_map"
                                none
                                [
                                  (Expr.closure
                                    false
                                    [
                                      (Pat.tuple
                                        [
                                          (Pat.ident false false "val" none),
                                          (Pat.tuple
                                            [
                                              (Pat.ident false false "_offset" none),
                                              (Pat.ident false false "ty" none)])])]
                                    none
                                    (Expr.methodCall
                                      (Expr.path
                                        none
                                        (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                                      "retag_val"
                                      none
                                      [
                                        (Expr.path
                                          none
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "val" PathArguments.none)])),
                                        (Expr.path
                                          none
                                          (Path.mk false [(PathSegment.mk "ty" PathArguments.none)])),
                                        (Expr.path
                                          none
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "fn_entry" PathArguments.none)]))]))]))])),
                      (Arm.mk
                        []
                        (Pat.tuple
                          [
                            (Pat.tupleStruct
                              none
                              (Path.mk
                                false
                                [
                                  (PathSegment.mk "Value" PathArguments.none),
                                  (PathSegment.mk "Tuple" PathArguments.none)])
                              [(Pat.ident false false "vals" none)]),
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
                                  (Pat.ident false false "ty" none))]
                              true)])
                        none
                        (Expr.call
                          (Expr.path
                            none
                            (Path.mk
                              false
                              [
                                (PathSegment.mk "Value" PathArguments.none),
                                (PathSegment.mk "Tuple" PathArguments.none)]))
                          [
                            (Expr.tryExpr
                              (Expr.methodCall
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "vals" PathArguments.none)]))
                                "try_map"
                                none
                                [
                                  (Expr.closure
                                    false
                                    [(Pat.ident false false "val" none)]
                                    none
                                    (Expr.methodCall
                                      (Expr.path
                                        none
                                        (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                                      "retag_val"
                                      none
                                      [
                                        (Expr.path
                                          none
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "val" PathArguments.none)])),
                                        (Expr.path
                                          none
                                          (Path.mk false [(PathSegment.mk "ty" PathArguments.none)])),
                                        (Expr.path
                                          none
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "fn_entry" PathArguments.none)]))]))]))])),
                      (Arm.mk
                        []
                        (Pat.tuple
                          [
                            (Pat.struct
                              none
                              (Path.mk
                                false
                                [
                                  (PathSegment.mk "Value" PathArguments.none),
                                  (PathSegment.mk "Variant" PathArguments.none)])
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
                                  (Pat.ident false false "data" none))]
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
                                  true
                                  (Pat.ident false false "variants" none))]
                              true)])
                        none
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
                              (Expr.tryExpr
                                (Expr.methodCall
                                  (Expr.path
                                    none
                                    (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                                  "retag_val"
                                  none
                                  [
                                    (Expr.path
                                      none
                                      (Path.mk false [(PathSegment.mk "data" PathArguments.none)])),
                                    (Expr.field
                                      (Expr.index
                                        (Expr.path
                                          none
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "variants" PathArguments.none)]))
                                        (Expr.path
                                          none
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "discriminant" PathArguments.none)])))
                                      (Member.named "ty")),
                                    (Expr.path
                                      none
                                      (Path.mk
                                        false
                                        [(PathSegment.mk "fn_entry" PathArguments.none)]))])))]
                          false
                          none)),
                      (Arm.mk
                        []
                        Pat.wild
                        none
                        (Expr.macro
                          (Macro.mk
                            (Path.mk false [(PathSegment.mk "panic" PathArguments.none)])
                            MacroDelimiter.paren
                            (MacroBody.exprs
                              [(Expr.lit (Lit.str "this value does not have that type"))]
                              false))))])])
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
          "eval_statement"
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
                    (PathSegment.mk "Statement" PathArguments.none),
                    (PathSegment.mk "Validate" PathArguments.none)])
                [
                  (FieldPat.mk [] (Member.named "place") true (Pat.ident false false "place" none)),
                  (FieldPat.mk
                    []
                    (Member.named "fn_entry")
                    true
                    (Pat.ident false false "fn_entry" none))]
                false)
              (Ty.path none (Path.mk false [(PathSegment.mk "Statement" PathArguments.none)])))]
          false
          (some (Ty.path none (Path.mk false [(PathSegment.mk "NdResult" PathArguments.none)]))))
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
              (Pat.ident false false "val" none)
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
            (Stmt.letStmt
              []
              (Pat.ident false false "val" none)
              (some
                (Expr.tryExpr
                  (Expr.methodCall
                    (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                    "retag_val"
                    none
                    [
                      (Expr.path none (Path.mk false [(PathSegment.mk "val" PathArguments.none)])),
                      (Expr.path none (Path.mk false [(PathSegment.mk "ty" PathArguments.none)])),
                      (Expr.path
                        none
                        (Path.mk false [(PathSegment.mk "fn_entry" PathArguments.none)]))])))
              none),
            (Stmt.expr
              (Expr.tryExpr
                (Expr.methodCall
                  (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                  "place_store"
                  none
                  [
                    (Expr.path none (Path.mk false [(PathSegment.mk "place" PathArguments.none)])),
                    (Expr.path none (Path.mk false [(PathSegment.mk "val" PathArguments.none)])),
                    (Expr.path none (Path.mk false [(PathSegment.mk "ty" PathArguments.none)]))]))
              true),
            (Stmt.expr
              (Expr.call
                (Expr.path none (Path.mk false [(PathSegment.mk "ret" PathArguments.none)]))
                [(Expr.tuple [])])
              false)]))])

/-- `spec/lang/step/statements.md:139` -/
def impl_ConcurrentMemory__deinit : Item :=
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
            "ConcurrentMemory"
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
          "deinit"
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
              (Pat.ident false false "len" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "Size" PathArguments.none)]))),
            (FnArg.typed
              []
              (Pat.ident false false "align" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "Align" PathArguments.none)])))]
          false
          (some (Ty.path none (Path.mk false [(PathSegment.mk "Result" PathArguments.none)]))))
        (Block.mk
          [
            (Stmt.expr
              (Expr.tryExpr
                (Expr.methodCall
                  (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                  "store"
                  none
                  [
                    (Expr.path none (Path.mk false [(PathSegment.mk "ptr" PathArguments.none)])),
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
                              (Path.mk false [(PathSegment.mk "len" PathArguments.none)]))
                            "bytes"
                            none
                            [])))),
                    (Expr.path none (Path.mk false [(PathSegment.mk "align" PathArguments.none)])),
                    (Expr.path
                      none
                      (Path.mk
                        false
                        [
                          (PathSegment.mk "Atomicity" PathArguments.none),
                          (PathSegment.mk "None" PathArguments.none)]))]))
              true),
            (Stmt.expr
              (Expr.call
                (Expr.path none (Path.mk false [(PathSegment.mk "ret" PathArguments.none)]))
                [(Expr.tuple [])])
              false)]))])

/-- `spec/lang/step/statements.md:146` -/
def impl_Machine__eval_statement_3 : Item :=
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
          "eval_statement"
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
                    (PathSegment.mk "Statement" PathArguments.none),
                    (PathSegment.mk "Deinit" PathArguments.none)])
                [(FieldPat.mk [] (Member.named "place") true (Pat.ident false false "place" none))]
                false)
              (Ty.path none (Path.mk false [(PathSegment.mk "Statement" PathArguments.none)])))]
          false
          (some (Ty.path none (Path.mk false [(PathSegment.mk "NdResult" PathArguments.none)]))))
        (Block.mk
          [
            (Stmt.letStmt
              []
              (Pat.tuple [(Pat.ident false false "p" none), (Pat.ident false false "ty" none)])
              (some
                (Expr.tryExpr
                  (Expr.methodCall
                    (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                    "eval_place"
                    none
                    [(Expr.path none (Path.mk false [(PathSegment.mk "place" PathArguments.none)]))])))
              none),
            (Stmt.expr
              (Expr.ite
                (Expr.unary
                  UnOp.not
                  (Expr.field
                    (Expr.path none (Path.mk false [(PathSegment.mk "p" PathArguments.none)]))
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
                              (Lit.str "de-initializing a place based on a misaligned pointer"))]
                          false))
                      true)])
                none)
              false),
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
                        (Expr.path none (Path.mk false [(PathSegment.mk "p" PathArguments.none)]))
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
                      [(Expr.lit (Lit.str "WF ensures deinits are sized"))]),
                    (Expr.path
                      none
                      (Path.mk
                        false
                        [
                          (PathSegment.mk "Align" PathArguments.none),
                          (PathSegment.mk "ONE" PathArguments.none)]))]))
              true),
            (Stmt.expr
              (Expr.call
                (Expr.path none (Path.mk false [(PathSegment.mk "ret" PathArguments.none)]))
                [(Expr.tuple [])])
              false)]))])

/-- `spec/lang/step/statements.md:165` -/
def impl_StackFrame__storage_live : Item :=
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
            "StackFrame"
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
          "storage_live"
          (Generics.mk [] [])
          [
            (FnArg.receiver [] true none true none),
            (FnArg.typed
              []
              (Pat.ident false false "mem" none)
              (Ty.reference
                none
                true
                (Ty.path
                  none
                  (Path.mk
                    false
                    [
                      (PathSegment.mk
                        "ConcurrentMemory"
                        (PathArguments.angleBracketed
                          false
                          [
                            (GenericArgument.type
                              (Ty.path
                                none
                                (Path.mk false [(PathSegment.mk "M" PathArguments.none)])))]))])))),
            (FnArg.typed
              []
              (Pat.ident false false "local" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "LocalName" PathArguments.none)])))]
          false
          (some (Ty.path none (Path.mk false [(PathSegment.mk "NdResult" PathArguments.none)]))))
        (Block.mk
          [
            (Stmt.expr
              (Expr.tryExpr
                (Expr.methodCall
                  (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                  "storage_dead"
                  none
                  [
                    (Expr.path none (Path.mk false [(PathSegment.mk "mem" PathArguments.none)])),
                    (Expr.path none (Path.mk false [(PathSegment.mk "local" PathArguments.none)]))]))
              true),
            (Stmt.letStmt
              []
              (Pat.ident false false "pointee_size" none)
              (some
                (Expr.methodCall
                  (Expr.methodCall
                    (Expr.index
                      (Expr.field
                        (Expr.field
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                          (Member.named "func"))
                        (Member.named "locals"))
                      (Expr.path none (Path.mk false [(PathSegment.mk "local" PathArguments.none)])))
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
                  [(Expr.lit (Lit.str "WF ensures all locals are sized"))]))
              none),
            (Stmt.letStmt
              []
              (Pat.ident false false "pointee_align" none)
              (some
                (Expr.methodCall
                  (Expr.methodCall
                    (Expr.index
                      (Expr.field
                        (Expr.field
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                          (Member.named "func"))
                        (Member.named "locals"))
                      (Expr.path none (Path.mk false [(PathSegment.mk "local" PathArguments.none)])))
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
                  [(Expr.lit (Lit.str "WF ensures all locals are sized"))]))
              none),
            (Stmt.letStmt
              []
              (Pat.ident false false "ptr" none)
              (some
                (Expr.tryExpr
                  (Expr.methodCall
                    (Expr.path none (Path.mk false [(PathSegment.mk "mem" PathArguments.none)]))
                    "allocate"
                    none
                    [
                      (Expr.path
                        none
                        (Path.mk
                          false
                          [
                            (PathSegment.mk "AllocationKind" PathArguments.none),
                            (PathSegment.mk "Stack" PathArguments.none)])),
                      (Expr.path
                        none
                        (Path.mk false [(PathSegment.mk "pointee_size" PathArguments.none)])),
                      (Expr.path
                        none
                        (Path.mk false [(PathSegment.mk "pointee_align" PathArguments.none)]))])))
              none),
            (Stmt.expr
              (Expr.methodCall
                (Expr.field
                  (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                  (Member.named "locals"))
                "insert"
                none
                [
                  (Expr.path none (Path.mk false [(PathSegment.mk "local" PathArguments.none)])),
                  (Expr.path none (Path.mk false [(PathSegment.mk "ptr" PathArguments.none)]))])
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
          "storage_dead"
          (Generics.mk [] [])
          [
            (FnArg.receiver [] true none true none),
            (FnArg.typed
              []
              (Pat.ident false false "mem" none)
              (Ty.reference
                none
                true
                (Ty.path
                  none
                  (Path.mk
                    false
                    [
                      (PathSegment.mk
                        "ConcurrentMemory"
                        (PathArguments.angleBracketed
                          false
                          [
                            (GenericArgument.type
                              (Ty.path
                                none
                                (Path.mk false [(PathSegment.mk "M" PathArguments.none)])))]))])))),
            (FnArg.typed
              []
              (Pat.ident false false "local" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "LocalName" PathArguments.none)])))]
          false
          (some (Ty.path none (Path.mk false [(PathSegment.mk "NdResult" PathArguments.none)]))))
        (Block.mk
          [
            (Stmt.letStmt
              []
              (Pat.ident false false "pointee_size" none)
              (some
                (Expr.methodCall
                  (Expr.methodCall
                    (Expr.index
                      (Expr.field
                        (Expr.field
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                          (Member.named "func"))
                        (Member.named "locals"))
                      (Expr.path none (Path.mk false [(PathSegment.mk "local" PathArguments.none)])))
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
                  [(Expr.lit (Lit.str "WF ensures all locals are sized"))]))
              none),
            (Stmt.letStmt
              []
              (Pat.ident false false "pointee_align" none)
              (some
                (Expr.methodCall
                  (Expr.methodCall
                    (Expr.index
                      (Expr.field
                        (Expr.field
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                          (Member.named "func"))
                        (Member.named "locals"))
                      (Expr.path none (Path.mk false [(PathSegment.mk "local" PathArguments.none)])))
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
                  [(Expr.lit (Lit.str "WF ensures all locals are sized"))]))
              none),
            (Stmt.expr
              (Expr.ite
                (Expr.letCond
                  (Pat.tupleStruct
                    none
                    (Path.mk false [(PathSegment.mk "Some" PathArguments.none)])
                    [(Pat.ident false false "ptr" none)])
                  (Expr.methodCall
                    (Expr.field
                      (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                      (Member.named "locals"))
                    "remove"
                    none
                    [(Expr.path none (Path.mk false [(PathSegment.mk "local" PathArguments.none)]))]))
                (Block.mk
                  [
                    (Stmt.expr
                      (Expr.tryExpr
                        (Expr.methodCall
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "mem" PathArguments.none)]))
                          "deallocate"
                          none
                          [
                            (Expr.path
                              none
                              (Path.mk false [(PathSegment.mk "ptr" PathArguments.none)])),
                            (Expr.path
                              none
                              (Path.mk
                                false
                                [
                                  (PathSegment.mk "AllocationKind" PathArguments.none),
                                  (PathSegment.mk "Stack" PathArguments.none)])),
                            (Expr.path
                              none
                              (Path.mk false [(PathSegment.mk "pointee_size" PathArguments.none)])),
                            (Expr.path
                              none
                              (Path.mk false [(PathSegment.mk "pointee_align" PathArguments.none)]))]))
                      true)])
                none)
              false),
            (Stmt.expr
              (Expr.call
                (Expr.path none (Path.mk false [(PathSegment.mk "ret" PathArguments.none)]))
                [(Expr.tuple [])])
              false)]))])

/-- `spec/lang/step/statements.md:188` -/
def impl_Machine__eval_statement_4 : Item :=
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
          "eval_statement"
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
                    (PathSegment.mk "Statement" PathArguments.none),
                    (PathSegment.mk "StorageLive" PathArguments.none)])
                [(Pat.ident false false "local" none)])
              (Ty.path none (Path.mk false [(PathSegment.mk "Statement" PathArguments.none)])))]
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
                                (Path.mk false [(PathSegment.mk "frame" PathArguments.none)]))
                              "storage_live"
                              none
                              [
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "mem" PathArguments.none)])),
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "local" PathArguments.none)]))])
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
          "eval_statement"
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
                    (PathSegment.mk "Statement" PathArguments.none),
                    (PathSegment.mk "StorageDead" PathArguments.none)])
                [(Pat.ident false false "local" none)])
              (Ty.path none (Path.mk false [(PathSegment.mk "Statement" PathArguments.none)])))]
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
                                (Path.mk false [(PathSegment.mk "frame" PathArguments.none)]))
                              "storage_dead"
                              none
                              [
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "mem" PathArguments.none)])),
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "local" PathArguments.none)]))])
                            false)])))])
              false)]))])

/-- All items of `spec/lang/step/statements.md`, in source order, with provenance. -/
def items : List SourceItem :=
  [
    (SourceItem.mk
      "impl_Machine__eval_statement_0"
      7
      "07323383187cb1b9e58e12c540c8162f35ddc0af26f5a45dd7241f404bb75f70"
      impl_Machine__eval_statement_0),
    (SourceItem.mk
      "impl_Machine__place_store"
      22
      "fc21c13f72094299b758afae6a312a8afbcff911a24d381aea444d354ef8a818"
      impl_Machine__place_store),
    (SourceItem.mk
      "impl_Machine__eval_statement_1"
      49
      "d4af5d9efa3f6feadddfefdedbbd19ffbb205cc221fa91e3c981999ae1d15d55"
      impl_Machine__eval_statement_1),
    (SourceItem.mk
      "impl_Machine__eval_statement_2"
      60
      "22ed4040879e71b471840a53f785c62b77c7b5643031c5c3301200a50a9d0ee1"
      impl_Machine__eval_statement_2),
    (SourceItem.mk
      "impl_Machine__retag_val"
      95
      "841886d45dbee98af85c15f2f06ec12066fdb6cd33d4a2b0063db66b7d919098"
      impl_Machine__retag_val),
    (SourceItem.mk
      "impl_ConcurrentMemory__deinit"
      139
      "064fee7c7d7ae02e4f65184ee6696c49716ff2afc3317fde070884b4ba1b3d81"
      impl_ConcurrentMemory__deinit),
    (SourceItem.mk
      "impl_Machine__eval_statement_3"
      146
      "6270dfc020c8a0d9308f788c96c7c2c1d9d54d39bb170a916d48cf0e0f54ec25"
      impl_Machine__eval_statement_3),
    (SourceItem.mk
      "impl_StackFrame__storage_live"
      165
      "e59ebbc763b68d58a81bb41a1aa9cd5b2bbd56f38afc2839720791f51d233e08"
      impl_StackFrame__storage_live),
    (SourceItem.mk
      "impl_Machine__eval_statement_4"
      188
      "5a98dd09cb4219dd983b7ada0d233a5979f510b2b759d7357a045d02034c045f"
      impl_Machine__eval_statement_4)]

end MiniRustSpec.Gen.Items.Lang.Step.Statements
