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
`spec/lang/representation.md` (commit `d821c6e3`), one Lean definition per item, in source order.
-/

import MiniRustSpec.Meta.Syntax

set_option maxRecDepth 100000

namespace MiniRustSpec.Gen.Items.Lang.Representation

open MiniRustSpec.Syntax

/-- Path of the upstream file these items were extracted from. -/
def sourceFile : String := "spec/lang/representation.md"

/-- SHA-256 of the upstream file. -/
def sourceSha256 : String := "3b101b30e85a6aea580b5b06371116abaab97f87b622f62de7459e0363f37844"

/-- `spec/lang/representation.md:33` -/
def impl_Type__decode_0 : Item :=
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
        [
          (Attr.mk true "doc" (AttrMeta.nameValue " Decode a list of bytes into a value.")),
          (Attr.mk true "doc" (AttrMeta.nameValue " ")),
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue " This can fail if `bytes` is not a valid encoding for the type,")),
          (Attr.mk true "doc" (AttrMeta.nameValue " which typically means Undefined Behavior.")),
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue
              " Assumes `self` is well formed and `bytes.len()` matches the types size (violating this is a spec bug).")),
          (Attr.mk true "specr::argmatch" (AttrMeta.list [(MetaItem.mk "self" AttrMeta.path)]))]
        Visibility.inherited
        false
        (Signature.mk
          false
          false
          false
          none
          "decode"
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
            (FnArg.receiver [] false none false none),
            (FnArg.typed
              []
              (Pat.ident false false "bytes" none)
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
                                                (PathSegment.mk "M" PathArguments.none),
                                                (PathSegment.mk "Provenance" PathArguments.none)])))]))])))]))])))]
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
        (Block.mk [(Stmt.expr (Expr.range none RangeLimits.halfOpen none) false)])),
      (ImplItem.fn
        [
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue " Encode `v` into a list of bytes according to the type `self`.")),
          (Attr.mk true "doc" (AttrMeta.nameValue " ")),
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue
              " Assumes `self` is well formed and `val` is well-formed for this type (violating this is a spec bug)..")),
          (Attr.mk true "specr::argmatch" (AttrMeta.list [(MetaItem.mk "self" AttrMeta.path)]))]
        Visibility.inherited
        false
        (Signature.mk
          false
          false
          false
          none
          "encode"
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
            (FnArg.receiver [] false none false none),
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
                            (Ty.path none (Path.mk false [(PathSegment.mk "M" PathArguments.none)])))]))])))]
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
                                              (PathSegment.mk "M" PathArguments.none),
                                              (PathSegment.mk "Provenance" PathArguments.none)])))]))])))]))]))))
        (Block.mk [(Stmt.expr (Expr.range none RangeLimits.halfOpen none) false)]))])

/-- `spec/lang/representation.md:53` -/
def impl_Type__decode_1 : Item :=
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
          "decode"
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
            (FnArg.typed
              []
              (Pat.path
                none
                (Path.mk
                  false
                  [
                    (PathSegment.mk "Type" PathArguments.none),
                    (PathSegment.mk "Bool" PathArguments.none)]))
              (Ty.path none (Path.mk false [(PathSegment.mk "Self" PathArguments.none)]))),
            (FnArg.typed
              []
              (Pat.ident false false "bytes" none)
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
                                                (PathSegment.mk "M" PathArguments.none),
                                                (PathSegment.mk "Provenance" PathArguments.none)])))]))])))]))])))]
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
                    (Expr.path none (Path.mk false [(PathSegment.mk "bytes" PathArguments.none)]))
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
                        (Path.mk false [(PathSegment.mk "panic" PathArguments.none)])
                        MacroDelimiter.paren
                        (MacroBody.exprs
                          [(Expr.lit (Lit.str "decode of Type::Bool with invalid length"))]
                          false))
                      true)])
                none)
              false),
            (Stmt.expr
              (Expr.call
                (Expr.path none (Path.mk false [(PathSegment.mk "ret" PathArguments.none)]))
                [
                  (Expr.matchExpr
                    (Expr.index
                      (Expr.path none (Path.mk false [(PathSegment.mk "bytes" PathArguments.none)]))
                      (Expr.lit (Lit.int 0 "")))
                    [
                      (Arm.mk
                        []
                        (Pat.tupleStruct
                          none
                          (Path.mk
                            false
                            [
                              (PathSegment.mk "AbstractByte" PathArguments.none),
                              (PathSegment.mk "Init" PathArguments.none)])
                          [(Pat.lit (Expr.lit (Lit.int 0 ""))), Pat.wild])
                        none
                        (Expr.call
                          (Expr.path
                            none
                            (Path.mk
                              false
                              [
                                (PathSegment.mk "Value" PathArguments.none),
                                (PathSegment.mk "Bool" PathArguments.none)]))
                          [(Expr.lit (Lit.bool false))])),
                      (Arm.mk
                        []
                        (Pat.tupleStruct
                          none
                          (Path.mk
                            false
                            [
                              (PathSegment.mk "AbstractByte" PathArguments.none),
                              (PathSegment.mk "Init" PathArguments.none)])
                          [(Pat.lit (Expr.lit (Lit.int 1 ""))), Pat.wild])
                        none
                        (Expr.call
                          (Expr.path
                            none
                            (Path.mk
                              false
                              [
                                (PathSegment.mk "Value" PathArguments.none),
                                (PathSegment.mk "Bool" PathArguments.none)]))
                          [(Expr.lit (Lit.bool true))])),
                      (Arm.mk
                        []
                        Pat.wild
                        none
                        (Expr.macro
                          (Macro.mk
                            (Path.mk false [(PathSegment.mk "throw" PathArguments.none)])
                            MacroDelimiter.paren
                            (MacroBody.exprs [] false))))])])
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
          "encode"
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
            (FnArg.typed
              []
              (Pat.path
                none
                (Path.mk
                  false
                  [
                    (PathSegment.mk "Type" PathArguments.none),
                    (PathSegment.mk "Bool" PathArguments.none)]))
              (Ty.path none (Path.mk false [(PathSegment.mk "Self" PathArguments.none)]))),
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
                            (Ty.path none (Path.mk false [(PathSegment.mk "M" PathArguments.none)])))]))])))]
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
                                              (PathSegment.mk "M" PathArguments.none),
                                              (PathSegment.mk "Provenance" PathArguments.none)])))]))])))]))]))))
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
                    (PathSegment.mk "Bool" PathArguments.none)])
                [(Pat.ident false false "b" none)])
              (some (Expr.path none (Path.mk false [(PathSegment.mk "val" PathArguments.none)])))
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
                            (MacroBody.exprs [] false)))
                        false)])))),
            (Stmt.expr
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
                              (PathSegment.mk "AbstractByte" PathArguments.none),
                              (PathSegment.mk "Init" PathArguments.none)]))
                        [
                          (Expr.ite
                            (Expr.path
                              none
                              (Path.mk false [(PathSegment.mk "b" PathArguments.none)]))
                            (Block.mk [(Stmt.expr (Expr.lit (Lit.int 1 "")) false)])
                            (some
                              (Expr.block
                                none
                                (Block.mk [(Stmt.expr (Expr.lit (Lit.int 0 "")) false)])))),
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "None" PathArguments.none)]))])]
                    false)))
              false)]))])

/-- `spec/lang/representation.md:74` -/
def impl_Type__decode_2 : Item :=
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
          "decode"
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
            (FnArg.typed
              []
              (Pat.tupleStruct
                none
                (Path.mk
                  false
                  [
                    (PathSegment.mk "Type" PathArguments.none),
                    (PathSegment.mk "Int" PathArguments.none)])
                [
                  (Pat.struct
                    none
                    (Path.mk false [(PathSegment.mk "IntType" PathArguments.none)])
                    [
                      (FieldPat.mk
                        []
                        (Member.named "signed")
                        true
                        (Pat.ident false false "signed" none)),
                      (FieldPat.mk
                        []
                        (Member.named "size")
                        true
                        (Pat.ident false false "size" none))]
                    false)])
              (Ty.path none (Path.mk false [(PathSegment.mk "Self" PathArguments.none)]))),
            (FnArg.typed
              []
              (Pat.ident false false "bytes" none)
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
                                                (PathSegment.mk "M" PathArguments.none),
                                                (PathSegment.mk "Provenance" PathArguments.none)])))]))])))]))])))]
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
                    (Expr.path none (Path.mk false [(PathSegment.mk "bytes" PathArguments.none)]))
                    "len"
                    none
                    [])
                  BinOp.ne
                  (Expr.methodCall
                    (Expr.path none (Path.mk false [(PathSegment.mk "size" PathArguments.none)]))
                    "bytes"
                    none
                    []))
                (Block.mk
                  [
                    (Stmt.macro
                      []
                      (Macro.mk
                        (Path.mk false [(PathSegment.mk "panic" PathArguments.none)])
                        MacroDelimiter.paren
                        (MacroBody.exprs
                          [(Expr.lit (Lit.str "decode of Type::Int with invalid length"))]
                          false))
                      true)])
                none)
              false),
            (Stmt.letStmt
              []
              (Pat.typed
                (Pat.ident false false "bytes_data" none)
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
                                (Path.mk false [(PathSegment.mk "u8" PathArguments.none)])))]))])))
              (some
                (Expr.tryExpr
                  (Expr.methodCall
                    (Expr.path none (Path.mk false [(PathSegment.mk "bytes" PathArguments.none)]))
                    "try_map"
                    none
                    [
                      (Expr.closure
                        false
                        [(Pat.ident false false "b" none)]
                        none
                        (Expr.methodCall
                          (Expr.path none (Path.mk false [(PathSegment.mk "b" PathArguments.none)]))
                          "data"
                          none
                          []))])))
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
                      (Expr.methodCall
                        (Expr.path
                          none
                          (Path.mk
                            false
                            [
                              (PathSegment.mk "M" PathArguments.none),
                              (PathSegment.mk "T" PathArguments.none),
                              (PathSegment.mk "ENDIANNESS" PathArguments.none)]))
                        "decode"
                        none
                        [
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "signed" PathArguments.none)])),
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "bytes_data" PathArguments.none)]))])])])
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
          "encode"
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
            (FnArg.typed
              []
              (Pat.tupleStruct
                none
                (Path.mk
                  false
                  [
                    (PathSegment.mk "Type" PathArguments.none),
                    (PathSegment.mk "Int" PathArguments.none)])
                [
                  (Pat.struct
                    none
                    (Path.mk false [(PathSegment.mk "IntType" PathArguments.none)])
                    [
                      (FieldPat.mk
                        []
                        (Member.named "signed")
                        true
                        (Pat.ident false false "signed" none)),
                      (FieldPat.mk
                        []
                        (Member.named "size")
                        true
                        (Pat.ident false false "size" none))]
                    false)])
              (Ty.path none (Path.mk false [(PathSegment.mk "Self" PathArguments.none)]))),
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
                            (Ty.path none (Path.mk false [(PathSegment.mk "M" PathArguments.none)])))]))])))]
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
                                              (PathSegment.mk "M" PathArguments.none),
                                              (PathSegment.mk "Provenance" PathArguments.none)])))]))])))]))]))))
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
                [(Pat.ident false false "i" none)])
              (some (Expr.path none (Path.mk false [(PathSegment.mk "val" PathArguments.none)])))
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
                            (MacroBody.exprs [] false)))
                        false)])))),
            (Stmt.letStmt
              []
              (Pat.ident false false "bytes_data" none)
              (some
                (Expr.methodCall
                  (Expr.methodCall
                    (Expr.path
                      none
                      (Path.mk
                        false
                        [
                          (PathSegment.mk "M" PathArguments.none),
                          (PathSegment.mk "T" PathArguments.none),
                          (PathSegment.mk "ENDIANNESS" PathArguments.none)]))
                    "encode"
                    none
                    [
                      (Expr.path
                        none
                        (Path.mk false [(PathSegment.mk "signed" PathArguments.none)])),
                      (Expr.path none (Path.mk false [(PathSegment.mk "size" PathArguments.none)])),
                      (Expr.path none (Path.mk false [(PathSegment.mk "i" PathArguments.none)]))])
                  "unwrap"
                  none
                  []))
              none),
            (Stmt.expr
              (Expr.methodCall
                (Expr.path none (Path.mk false [(PathSegment.mk "bytes_data" PathArguments.none)]))
                "map"
                none
                [
                  (Expr.closure
                    false
                    [(Pat.ident false false "b" none)]
                    none
                    (Expr.call
                      (Expr.path
                        none
                        (Path.mk
                          false
                          [
                            (PathSegment.mk "AbstractByte" PathArguments.none),
                            (PathSegment.mk "Init" PathArguments.none)]))
                      [
                        (Expr.path none (Path.mk false [(PathSegment.mk "b" PathArguments.none)])),
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "None" PathArguments.none)]))]))])
              false)]))])

/-- `spec/lang/representation.md:112` -/
def fn_decode_ptr : Item :=
  (Item.fn
    []
    Visibility.inherited
    (Signature.mk
      false
      false
      false
      none
      "decode_ptr"
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
        (FnArg.typed
          []
          (Pat.ident false false "bytes" none)
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
                                            (PathSegment.mk "M" PathArguments.none),
                                            (PathSegment.mk "Provenance" PathArguments.none)])))]))])))]))])))]
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
          (Expr.ite
            (Expr.binary
              (Expr.methodCall
                (Expr.path none (Path.mk false [(PathSegment.mk "bytes" PathArguments.none)]))
                "len"
                none
                [])
              BinOp.ne
              (Expr.methodCall
                (Expr.path
                  none
                  (Path.mk
                    false
                    [
                      (PathSegment.mk "M" PathArguments.none),
                      (PathSegment.mk "T" PathArguments.none),
                      (PathSegment.mk "PTR_SIZE" PathArguments.none)]))
                "bytes"
                none
                []))
            (Block.mk
              [
                (Stmt.macro
                  []
                  (Macro.mk
                    (Path.mk false [(PathSegment.mk "panic" PathArguments.none)])
                    MacroDelimiter.paren
                    (MacroBody.exprs
                      [(Expr.lit (Lit.str "decode of thin pointer with invalid length"))]
                      false))
                  true)])
            none)
          false),
        (Stmt.letStmt
          []
          (Pat.ident false false "bytes_data" none)
          (some
            (Expr.tryExpr
              (Expr.methodCall
                (Expr.path none (Path.mk false [(PathSegment.mk "bytes" PathArguments.none)]))
                "try_map"
                none
                [
                  (Expr.closure
                    false
                    [(Pat.ident false false "b" none)]
                    none
                    (Expr.methodCall
                      (Expr.path none (Path.mk false [(PathSegment.mk "b" PathArguments.none)]))
                      "data"
                      none
                      []))])))
          none),
        (Stmt.letStmt
          []
          (Pat.ident false false "addr" none)
          (some
            (Expr.methodCall
              (Expr.path
                none
                (Path.mk
                  false
                  [
                    (PathSegment.mk "M" PathArguments.none),
                    (PathSegment.mk "T" PathArguments.none),
                    (PathSegment.mk "ENDIANNESS" PathArguments.none)]))
              "decode"
              none
              [
                (Expr.path none (Path.mk false [(PathSegment.mk "Unsigned" PathArguments.none)])),
                (Expr.path none (Path.mk false [(PathSegment.mk "bytes_data" PathArguments.none)]))]))
          none),
        (Stmt.letStmt
          []
          (Pat.ident false false "provenance" none)
          (some
            (Expr.methodCall
              (Expr.path none (Path.mk false [(PathSegment.mk "bytes" PathArguments.none)]))
              "fold_with_idx"
              none
              [
                (Expr.methodCall
                  (Expr.methodCall
                    (Expr.index
                      (Expr.path none (Path.mk false [(PathSegment.mk "bytes" PathArguments.none)]))
                      (Expr.lit (Lit.int 0 "")))
                    "provenance_frag"
                    none
                    [])
                  "map"
                  none
                  [
                    (Expr.closure
                      false
                      [(Pat.ident false false "frag" none)]
                      none
                      (Expr.field
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "frag" PathArguments.none)]))
                        (Member.named "provenance")))]),
                (Expr.closure
                  false
                  [
                    (Pat.ident false false "acc" none),
                    (Pat.ident false false "idx" none),
                    (Pat.ident false false "byte" none)]
                  none
                  (Expr.block
                    none
                    (Block.mk
                      [
                        (Stmt.expr
                          (Expr.ite
                            (Expr.binary
                              (Expr.binary
                                (Expr.letCond
                                  (Pat.tupleStruct
                                    none
                                    (Path.mk false [(PathSegment.mk "Some" PathArguments.none)])
                                    [(Pat.ident false false "frag" none)])
                                  (Expr.methodCall
                                    (Expr.path
                                      none
                                      (Path.mk false [(PathSegment.mk "byte" PathArguments.none)]))
                                    "provenance_frag"
                                    none
                                    []))
                                BinOp.and
                                (Expr.binary
                                  (Expr.field
                                    (Expr.path
                                      none
                                      (Path.mk false [(PathSegment.mk "frag" PathArguments.none)]))
                                    (Member.named "position"))
                                  BinOp.eq
                                  (Expr.path
                                    none
                                    (Path.mk false [(PathSegment.mk "idx" PathArguments.none)]))))
                              BinOp.and
                              (Expr.binary
                                (Expr.call
                                  (Expr.path
                                    none
                                    (Path.mk false [(PathSegment.mk "Some" PathArguments.none)]))
                                  [
                                    (Expr.field
                                      (Expr.path
                                        none
                                        (Path.mk false [(PathSegment.mk "frag" PathArguments.none)]))
                                      (Member.named "provenance"))])
                                BinOp.eq
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "acc" PathArguments.none)]))))
                            (Block.mk
                              [
                                (Stmt.expr
                                  (Expr.path
                                    none
                                    (Path.mk false [(PathSegment.mk "acc" PathArguments.none)]))
                                  false)])
                            (some
                              (Expr.block
                                none
                                (Block.mk
                                  [
                                    (Stmt.expr
                                      (Expr.path
                                        none
                                        (Path.mk false [(PathSegment.mk "None" PathArguments.none)]))
                                      false)]))))
                          false)])))]))
          none),
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
                    true
                    (Expr.path none (Path.mk false [(PathSegment.mk "addr" PathArguments.none)]))),
                  (FieldValue.mk
                    []
                    (Member.named "provenance")
                    true
                    (Expr.path
                      none
                      (Path.mk false [(PathSegment.mk "provenance" PathArguments.none)])))]
                false
                none)])
          false)]))

/-- `spec/lang/representation.md:135` -/
def fn_encode_ptr : Item :=
  (Item.fn
    []
    Visibility.inherited
    (Signature.mk
      false
      false
      false
      none
      "encode_ptr"
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
                              (PathSegment.mk "Provenance" PathArguments.none)])))]))])))]
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
                                          (PathSegment.mk "M" PathArguments.none),
                                          (PathSegment.mk "Provenance" PathArguments.none)])))]))])))]))]))))
    (Block.mk
      [
        (Stmt.letStmt
          []
          (Pat.ident false false "bytes_data" none)
          (some
            (Expr.methodCall
              (Expr.methodCall
                (Expr.path
                  none
                  (Path.mk
                    false
                    [
                      (PathSegment.mk "M" PathArguments.none),
                      (PathSegment.mk "T" PathArguments.none),
                      (PathSegment.mk "ENDIANNESS" PathArguments.none)]))
                "encode"
                none
                [
                  (Expr.path none (Path.mk false [(PathSegment.mk "Unsigned" PathArguments.none)])),
                  (Expr.path
                    none
                    (Path.mk
                      false
                      [
                        (PathSegment.mk "M" PathArguments.none),
                        (PathSegment.mk "T" PathArguments.none),
                        (PathSegment.mk "PTR_SIZE" PathArguments.none)])),
                  (Expr.field
                    (Expr.path none (Path.mk false [(PathSegment.mk "ptr" PathArguments.none)]))
                    (Member.named "addr"))])
              "unwrap"
              none
              []))
          none),
        (Stmt.expr
          (Expr.methodCall
            (Expr.path none (Path.mk false [(PathSegment.mk "bytes_data" PathArguments.none)]))
            "map_with_idx"
            none
            [
              (Expr.closure
                false
                [(Pat.ident false false "i" none), (Pat.ident false false "b" none)]
                none
                (Expr.call
                  (Expr.path
                    none
                    (Path.mk
                      false
                      [
                        (PathSegment.mk "AbstractByte" PathArguments.none),
                        (PathSegment.mk "Init" PathArguments.none)]))
                  [
                    (Expr.path none (Path.mk false [(PathSegment.mk "b" PathArguments.none)])),
                    (Expr.methodCall
                      (Expr.field
                        (Expr.path none (Path.mk false [(PathSegment.mk "ptr" PathArguments.none)]))
                        (Member.named "provenance"))
                      "map"
                      none
                      [
                        (Expr.closure
                          false
                          [(Pat.ident false false "provenance" none)]
                          none
                          (Expr.struct
                            none
                            (Path.mk false [(PathSegment.mk "ProvenanceFrag" PathArguments.none)])
                            [
                              (FieldValue.mk
                                []
                                (Member.named "provenance")
                                true
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "provenance" PathArguments.none)]))),
                              (FieldValue.mk
                                []
                                (Member.named "position")
                                false
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "i" PathArguments.none)])))]
                            false
                            none))])]))])
          false)]))

/-- `spec/lang/representation.md:144` -/
def impl_PointerMetaKind__ty : Item :=
  (Item.impl
    []
    false
    false
    (Generics.mk [] [])
    false
    none
    (Ty.path none (Path.mk false [(PathSegment.mk "PointerMetaKind" PathArguments.none)]))
    [
      (ImplItem.fn
        [
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue " Returns the type of the metadata when used as a value."))]
        Visibility.pub
        false
        (Signature.mk
          false
          false
          false
          none
          "ty"
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
          (some (Ty.path none (Path.mk false [(PathSegment.mk "Type" PathArguments.none)]))))
        (Block.mk
          [
            (Stmt.expr
              (Expr.matchExpr
                (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                [
                  (Arm.mk
                    []
                    (Pat.path
                      none
                      (Path.mk
                        false
                        [
                          (PathSegment.mk "PointerMetaKind" PathArguments.none),
                          (PathSegment.mk "None" PathArguments.none)]))
                    none
                    (Expr.call
                      (Expr.path
                        none
                        (Path.mk false [(PathSegment.mk "unit_type" PathArguments.none)]))
                      [])),
                  (Arm.mk
                    []
                    (Pat.path
                      none
                      (Path.mk
                        false
                        [
                          (PathSegment.mk "PointerMetaKind" PathArguments.none),
                          (PathSegment.mk "ElementCount" PathArguments.none)]))
                    none
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
                                          (Path.mk false [(PathSegment.mk "T" PathArguments.none)])))]))]))
                          [])])),
                  (Arm.mk
                    []
                    (Pat.tupleStruct
                      none
                      (Path.mk
                        false
                        [
                          (PathSegment.mk "PointerMetaKind" PathArguments.none),
                          (PathSegment.mk "VTablePointer" PathArguments.none)])
                      [(Pat.ident false false "trait_name" none)])
                    none
                    (Expr.call
                      (Expr.path
                        none
                        (Path.mk
                          false
                          [
                            (PathSegment.mk "Type" PathArguments.none),
                            (PathSegment.mk "Ptr" PathArguments.none)]))
                      [
                        (Expr.call
                          (Expr.path
                            none
                            (Path.mk
                              false
                              [
                                (PathSegment.mk "PtrType" PathArguments.none),
                                (PathSegment.mk "VTablePtr" PathArguments.none)]))
                          [
                            (Expr.path
                              none
                              (Path.mk false [(PathSegment.mk "trait_name" PathArguments.none)]))])]))])
              false)]))])

/-- `spec/lang/representation.md:155` -/
def impl_PtrType__as_wide_pair : Item :=
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
            (AttrMeta.nameValue
              " Returns a pair type representing this wide pointer or `None` if it is thin."))]
        Visibility.pub
        false
        (Signature.mk
          false
          false
          false
          none
          "as_wide_pair"
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
                    "Option"
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
              (Expr.ite
                (Expr.binary
                  (Expr.methodCall
                    (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                    "meta_kind"
                    none
                    [])
                  BinOp.eq
                  (Expr.path
                    none
                    (Path.mk
                      false
                      [
                        (PathSegment.mk "PointerMetaKind" PathArguments.none),
                        (PathSegment.mk "None" PathArguments.none)])))
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
              (Pat.ident false false "meta_ty" none)
              (some
                (Expr.methodCall
                  (Expr.methodCall
                    (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                    "meta_kind"
                    none
                    [])
                  "ty"
                  (some
                    [
                      (GenericArgument.type
                        (Ty.path none (Path.mk false [(PathSegment.mk "T" PathArguments.none)])))])
                  []))
              none),
            (Stmt.macro
              []
              (Macro.mk
                (Path.mk false [(PathSegment.mk "assert_eq" PathArguments.none)])
                MacroDelimiter.paren
                (MacroBody.exprs
                  [
                    (Expr.methodCall
                      (Expr.methodCall
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "meta_ty" PathArguments.none)]))
                        "layout"
                        (some
                          [
                            (GenericArgument.type
                              (Ty.path
                                none
                                (Path.mk false [(PathSegment.mk "T" PathArguments.none)])))])
                        [])
                      "expect_size"
                      none
                      [(Expr.lit (Lit.str "metadata is always sized"))]),
                    (Expr.path
                      none
                      (Path.mk
                        false
                        [
                          (PathSegment.mk "T" PathArguments.none),
                          (PathSegment.mk "PTR_SIZE" PathArguments.none)])),
                    (Expr.lit (Lit.str "metadata is assumed to be pointer-sized"))]
                  false))
              true),
            (Stmt.macro
              []
              (Macro.mk
                (Path.mk false [(PathSegment.mk "assert_eq" PathArguments.none)])
                MacroDelimiter.paren
                (MacroBody.exprs
                  [
                    (Expr.methodCall
                      (Expr.methodCall
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "meta_ty" PathArguments.none)]))
                        "layout"
                        (some
                          [
                            (GenericArgument.type
                              (Ty.path
                                none
                                (Path.mk false [(PathSegment.mk "T" PathArguments.none)])))])
                        [])
                      "expect_align"
                      none
                      [(Expr.lit (Lit.str "metadata is always sized"))]),
                    (Expr.path
                      none
                      (Path.mk
                        false
                        [
                          (PathSegment.mk "T" PathArguments.none),
                          (PathSegment.mk "PTR_ALIGN" PathArguments.none)])),
                    (Expr.lit (Lit.str "metadata is assumed to be pointer-aligned"))]
                  false))
              true),
            (Stmt.letStmt
              []
              (Pat.ident false false "thin_pointer_field" none)
              (some
                (Expr.tuple
                  [
                    (Expr.path
                      none
                      (Path.mk
                        false
                        [
                          (PathSegment.mk "Offset" PathArguments.none),
                          (PathSegment.mk "ZERO" PathArguments.none)])),
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
                                    (PathSegment.mk "PointerMetaKind" PathArguments.none),
                                    (PathSegment.mk "None" PathArguments.none)])))]
                          false
                          none)])]))
              none),
            (Stmt.letStmt
              []
              (Pat.ident false false "metadata_field" none)
              (some
                (Expr.tuple
                  [
                    (Expr.path
                      none
                      (Path.mk
                        false
                        [
                          (PathSegment.mk "T" PathArguments.none),
                          (PathSegment.mk "PTR_SIZE" PathArguments.none)])),
                    (Expr.path none (Path.mk false [(PathSegment.mk "meta_ty" PathArguments.none)]))]))
              none),
            (Stmt.expr
              (Expr.call
                (Expr.path none (Path.mk false [(PathSegment.mk "ret" PathArguments.none)]))
                [
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
                            (MacroBody.exprs
                              [
                                (Expr.path
                                  none
                                  (Path.mk
                                    false
                                    [(PathSegment.mk "thin_pointer_field" PathArguments.none)])),
                                (Expr.path
                                  none
                                  (Path.mk
                                    false
                                    [(PathSegment.mk "metadata_field" PathArguments.none)]))]
                              false)))),
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
                              (Expr.binary
                                (Expr.call
                                  (Expr.path
                                    none
                                    (Path.mk
                                      false
                                      [
                                        (PathSegment.mk "Int" PathArguments.none),
                                        (PathSegment.mk "from" PathArguments.none)]))
                                  [(Expr.lit (Lit.int 2 ""))])
                                BinOp.mul
                                (Expr.path
                                  none
                                  (Path.mk
                                    false
                                    [
                                      (PathSegment.mk "T" PathArguments.none),
                                      (PathSegment.mk "PTR_SIZE" PathArguments.none)])))),
                            (FieldValue.mk
                              []
                              (Member.named "align")
                              false
                              (Expr.path
                                none
                                (Path.mk
                                  false
                                  [
                                    (PathSegment.mk "T" PathArguments.none),
                                    (PathSegment.mk "PTR_ALIGN" PathArguments.none)]))),
                            (FieldValue.mk
                              []
                              (Member.named "packed_align")
                              false
                              (Expr.path
                                none
                                (Path.mk false [(PathSegment.mk "None" PathArguments.none)])))]
                          false
                          none)),
                      (FieldValue.mk
                        []
                        (Member.named "unsized_field")
                        false
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "None" PathArguments.none)])))]
                    false
                    none)])
              false)]))])

/-- `spec/lang/representation.md:178` -/
def impl_PointerMetaKind__decode_value : Item :=
  (Item.impl
    []
    false
    false
    (Generics.mk [] [])
    false
    none
    (Ty.path none (Path.mk false [(PathSegment.mk "PointerMetaKind" PathArguments.none)]))
    [
      (ImplItem.fn
        [
          (Attr.mk true "doc" (AttrMeta.nameValue " Decodes a value to metadata.")),
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue
              " The spec will only call this with values which are well formed for `self.ty()`,")),
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue
              " but this may return ill-formed metadata (as defined by `Machine::check_ptr_metadata`), thus needs to be checked."))]
        Visibility.inherited
        false
        (Signature.mk
          false
          false
          false
          none
          "decode_value"
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
            (FnArg.receiver [] false none false none),
            (FnArg.typed
              []
              (Pat.ident false false "value" none)
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
                            (Ty.path none (Path.mk false [(PathSegment.mk "M" PathArguments.none)])))]))])))]
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
                                              (PathSegment.mk "M" PathArguments.none),
                                              (PathSegment.mk "Provenance" PathArguments.none)])))]))])))]))]))))
        (Block.mk
          [
            (Stmt.expr
              (Expr.matchExpr
                (Expr.tuple
                  [
                    (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)])),
                    (Expr.path none (Path.mk false [(PathSegment.mk "value" PathArguments.none)]))])
                [
                  (Arm.mk
                    []
                    (Pat.tuple
                      [
                        (Pat.path
                          none
                          (Path.mk
                            false
                            [
                              (PathSegment.mk "PointerMetaKind" PathArguments.none),
                              (PathSegment.mk "None" PathArguments.none)])),
                        (Pat.tupleStruct
                          none
                          (Path.mk
                            false
                            [
                              (PathSegment.mk "Value" PathArguments.none),
                              (PathSegment.mk "Tuple" PathArguments.none)])
                          [(Pat.ident false false "fields" none)])])
                    (some
                      (Expr.methodCall
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "fields" PathArguments.none)]))
                        "is_empty"
                        none
                        []))
                    (Expr.path none (Path.mk false [(PathSegment.mk "None" PathArguments.none)]))),
                  (Arm.mk
                    []
                    (Pat.tuple
                      [
                        (Pat.path
                          none
                          (Path.mk
                            false
                            [
                              (PathSegment.mk "PointerMetaKind" PathArguments.none),
                              (PathSegment.mk "ElementCount" PathArguments.none)])),
                        (Pat.tupleStruct
                          none
                          (Path.mk
                            false
                            [
                              (PathSegment.mk "Value" PathArguments.none),
                              (PathSegment.mk "Int" PathArguments.none)])
                          [(Pat.ident false false "count" none)])])
                    none
                    (Expr.call
                      (Expr.path none (Path.mk false [(PathSegment.mk "Some" PathArguments.none)]))
                      [
                        (Expr.call
                          (Expr.path
                            none
                            (Path.mk
                              false
                              [
                                (PathSegment.mk "PointerMeta" PathArguments.none),
                                (PathSegment.mk "ElementCount" PathArguments.none)]))
                          [
                            (Expr.path
                              none
                              (Path.mk false [(PathSegment.mk "count" PathArguments.none)]))])])),
                  (Arm.mk
                    []
                    (Pat.tuple
                      [
                        (Pat.tupleStruct
                          none
                          (Path.mk
                            false
                            [
                              (PathSegment.mk "PointerMetaKind" PathArguments.none),
                              (PathSegment.mk "VTablePointer" PathArguments.none)])
                          [Pat.wild]),
                        (Pat.tupleStruct
                          none
                          (Path.mk
                            false
                            [
                              (PathSegment.mk "Value" PathArguments.none),
                              (PathSegment.mk "Ptr" PathArguments.none)])
                          [(Pat.ident false false "ptr" none)])])
                    (some
                      (Expr.methodCall
                        (Expr.field
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "ptr" PathArguments.none)]))
                          (Member.named "metadata"))
                        "is_none"
                        none
                        []))
                    (Expr.call
                      (Expr.path none (Path.mk false [(PathSegment.mk "Some" PathArguments.none)]))
                      [
                        (Expr.call
                          (Expr.path
                            none
                            (Path.mk
                              false
                              [
                                (PathSegment.mk "PointerMeta" PathArguments.none),
                                (PathSegment.mk "VTablePointer" PathArguments.none)]))
                          [
                            (Expr.field
                              (Expr.path
                                none
                                (Path.mk false [(PathSegment.mk "ptr" PathArguments.none)]))
                              (Member.named "thin_pointer"))])])),
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
                              (Lit.str "PointerMeta::decode_value called with invalid value"))]
                          false))))])
              false)])),
      (ImplItem.fn
        [
          (Attr.mk true "doc" (AttrMeta.nameValue " Encodes metadata as a value.")),
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue
              " The spec ensures this is only called with well-formed metadata (as defined by `Machine::check_ptr_metadata`)."))]
        Visibility.inherited
        false
        (Signature.mk
          false
          false
          false
          none
          "encode_as_value"
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
            (FnArg.receiver [] false none false none),
            (FnArg.typed
              []
              (Pat.ident false false "meta" none)
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
                                                (PathSegment.mk "M" PathArguments.none),
                                                (PathSegment.mk "Provenance" PathArguments.none)])))]))])))]))])))]
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
              (Expr.matchExpr
                (Expr.tuple
                  [
                    (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)])),
                    (Expr.path none (Path.mk false [(PathSegment.mk "meta" PathArguments.none)]))])
                [
                  (Arm.mk
                    []
                    (Pat.tuple
                      [
                        (Pat.path
                          none
                          (Path.mk
                            false
                            [
                              (PathSegment.mk "PointerMetaKind" PathArguments.none),
                              (PathSegment.mk "None" PathArguments.none)])),
                        (Pat.ident false false "None" none)])
                    none
                    (Expr.call
                      (Expr.path
                        none
                        (Path.mk false [(PathSegment.mk "unit_value" PathArguments.none)]))
                      [])),
                  (Arm.mk
                    []
                    (Pat.tuple
                      [
                        (Pat.path
                          none
                          (Path.mk
                            false
                            [
                              (PathSegment.mk "PointerMetaKind" PathArguments.none),
                              (PathSegment.mk "ElementCount" PathArguments.none)])),
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
                          (Path.mk false [(PathSegment.mk "count" PathArguments.none)]))])),
                  (Arm.mk
                    []
                    (Pat.tuple
                      [
                        (Pat.tupleStruct
                          none
                          (Path.mk
                            false
                            [
                              (PathSegment.mk "PointerMetaKind" PathArguments.none),
                              (PathSegment.mk "VTablePointer" PathArguments.none)])
                          [Pat.wild]),
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
                              (Path.mk false [(PathSegment.mk "None" PathArguments.none)]))])])),
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
                              (Lit.str "PointerMeta::encode_as_value called with invalid value"))]
                          false))))])
              false)]))])

/-- `spec/lang/representation.md:203` -/
def impl_Type__decode_3 : Item :=
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
          "decode"
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
            (FnArg.typed
              []
              (Pat.tupleStruct
                none
                (Path.mk
                  false
                  [
                    (PathSegment.mk "Type" PathArguments.none),
                    (PathSegment.mk "Ptr" PathArguments.none)])
                [(Pat.ident false false "ptr_type" none)])
              (Ty.path none (Path.mk false [(PathSegment.mk "Self" PathArguments.none)]))),
            (FnArg.typed
              []
              (Pat.ident false false "bytes" none)
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
                                                (PathSegment.mk "M" PathArguments.none),
                                                (PathSegment.mk "Provenance" PathArguments.none)])))]))])))]))])))]
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
                (Expr.letCond
                  (Pat.tupleStruct
                    none
                    (Path.mk false [(PathSegment.mk "Some" PathArguments.none)])
                    [(Pat.ident false false "pair_ty" none)])
                  (Expr.methodCall
                    (Expr.path
                      none
                      (Path.mk false [(PathSegment.mk "ptr_type" PathArguments.none)]))
                    "as_wide_pair"
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
                            (PathSegment.mk "Tuple" PathArguments.none)])
                        [(Pat.ident false false "parts" none)])
                      (some
                        (Expr.tryExpr
                          (Expr.methodCall
                            (Expr.path
                              none
                              (Path.mk false [(PathSegment.mk "pair_ty" PathArguments.none)]))
                            "decode"
                            (some
                              [
                                (GenericArgument.type
                                  (Ty.path
                                    none
                                    (Path.mk false [(PathSegment.mk "M" PathArguments.none)])))])
                            [
                              (Expr.path
                                none
                                (Path.mk false [(PathSegment.mk "bytes" PathArguments.none)]))])))
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
                                        (Lit.str "as_wide_pair always returns a tuple type"))]
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
                        [(Pat.ident false false "ptr" none)])
                      (some
                        (Expr.index
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "parts" PathArguments.none)]))
                          (Expr.lit (Lit.int 0 ""))))
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
                                          "as_wide_pair always returns tuple with the first field being a thin pointer"))]
                                    false))
                                true)])))),
                    (Stmt.letStmt
                      []
                      (Pat.ident false false "meta" none)
                      (some
                        (Expr.methodCall
                          (Expr.methodCall
                            (Expr.path
                              none
                              (Path.mk false [(PathSegment.mk "ptr_type" PathArguments.none)]))
                            "meta_kind"
                            none
                            [])
                          "decode_value"
                          none
                          [
                            (Expr.index
                              (Expr.path
                                none
                                (Path.mk false [(PathSegment.mk "parts" PathArguments.none)]))
                              (Expr.lit (Lit.int 1 "")))]))
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
                                (Path.mk false [(PathSegment.mk "meta" PathArguments.none)]))
                              "is_some"
                              none
                              []),
                            (Expr.lit
                              (Lit.str "as_wide_pair always returns a suitable metadata type"))]
                          false))
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
                                  (PathSegment.mk "Ptr" PathArguments.none)]))
                            [
                              (Expr.methodCall
                                (Expr.field
                                  (Expr.path
                                    none
                                    (Path.mk false [(PathSegment.mk "ptr" PathArguments.none)]))
                                  (Member.named "thin_pointer"))
                                "widen"
                                none
                                [
                                  (Expr.path
                                    none
                                    (Path.mk false [(PathSegment.mk "meta" PathArguments.none)]))])])])
                      false)])
                (some
                  (Expr.block
                    none
                    (Block.mk
                      [
                        (Stmt.letStmt
                          []
                          (Pat.ident false false "ptr" none)
                          (some
                            (Expr.tryExpr
                              (Expr.call
                                (Expr.path
                                  none
                                  (Path.mk
                                    false
                                    [
                                      (PathSegment.mk
                                        "decode_ptr"
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
                                    (Path.mk false [(PathSegment.mk "bytes" PathArguments.none)]))])))
                          none),
                        (Stmt.expr
                          (Expr.call
                            (Expr.path
                              none
                              (Path.mk false [(PathSegment.mk "ret" PathArguments.none)]))
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
                                      (Path.mk false [(PathSegment.mk "ptr" PathArguments.none)]))
                                    "widen"
                                    none
                                    [
                                      (Expr.path
                                        none
                                        (Path.mk false [(PathSegment.mk "None" PathArguments.none)]))])])])
                          false)]))))
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
          "encode"
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
            (FnArg.typed
              []
              (Pat.tupleStruct
                none
                (Path.mk
                  false
                  [
                    (PathSegment.mk "Type" PathArguments.none),
                    (PathSegment.mk "Ptr" PathArguments.none)])
                [(Pat.ident false false "ptr_type" none)])
              (Ty.path none (Path.mk false [(PathSegment.mk "Self" PathArguments.none)]))),
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
                            (Ty.path none (Path.mk false [(PathSegment.mk "M" PathArguments.none)])))]))])))]
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
                                              (PathSegment.mk "M" PathArguments.none),
                                              (PathSegment.mk "Provenance" PathArguments.none)])))]))])))]))]))))
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
              (some (Expr.path none (Path.mk false [(PathSegment.mk "val" PathArguments.none)])))
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
                            (MacroBody.exprs [(Expr.lit (Lit.str "val is WF for a pointer"))] false)))
                        false)])))),
            (Stmt.expr
              (Expr.ite
                (Expr.letCond
                  (Pat.tupleStruct
                    none
                    (Path.mk false [(PathSegment.mk "Some" PathArguments.none)])
                    [(Pat.ident false false "pair_ty" none)])
                  (Expr.methodCall
                    (Expr.path
                      none
                      (Path.mk false [(PathSegment.mk "ptr_type" PathArguments.none)]))
                    "as_wide_pair"
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
                (Block.mk
                  [
                    (Stmt.letStmt
                      []
                      (Pat.ident false false "thin_ptr_value" none)
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
                              (Expr.field
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "ptr" PathArguments.none)]))
                                (Member.named "thin_pointer"))
                              "widen"
                              none
                              [
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "None" PathArguments.none)]))])]))
                      none),
                    (Stmt.letStmt
                      []
                      (Pat.ident false false "meta_data_value" none)
                      (some
                        (Expr.methodCall
                          (Expr.methodCall
                            (Expr.path
                              none
                              (Path.mk false [(PathSegment.mk "ptr_type" PathArguments.none)]))
                            "meta_kind"
                            none
                            [])
                          "encode_as_value"
                          (some
                            [
                              (GenericArgument.type
                                (Ty.path
                                  none
                                  (Path.mk false [(PathSegment.mk "M" PathArguments.none)])))])
                          [
                            (Expr.field
                              (Expr.path
                                none
                                (Path.mk false [(PathSegment.mk "ptr" PathArguments.none)]))
                              (Member.named "metadata"))]))
                      none),
                    (Stmt.letStmt
                      []
                      (Pat.ident false false "tuple" none)
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
                                    (Expr.path
                                      none
                                      (Path.mk
                                        false
                                        [(PathSegment.mk "thin_ptr_value" PathArguments.none)])),
                                    (Expr.path
                                      none
                                      (Path.mk
                                        false
                                        [(PathSegment.mk "meta_data_value" PathArguments.none)]))]
                                  false)))]))
                      none),
                    (Stmt.expr
                      (Expr.methodCall
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "pair_ty" PathArguments.none)]))
                        "encode"
                        (some
                          [
                            (GenericArgument.type
                              (Ty.path
                                none
                                (Path.mk false [(PathSegment.mk "M" PathArguments.none)])))])
                        [
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "tuple" PathArguments.none)]))])
                      false)])
                (some
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
                                (Expr.methodCall
                                  (Expr.field
                                    (Expr.path
                                      none
                                      (Path.mk false [(PathSegment.mk "ptr" PathArguments.none)]))
                                    (Member.named "metadata"))
                                  "is_none"
                                  none
                                  []),
                                (Expr.lit (Lit.str "ptr_type and value have mismatching metadata"))]
                              false))
                          true),
                        (Stmt.expr
                          (Expr.call
                            (Expr.path
                              none
                              (Path.mk
                                false
                                [
                                  (PathSegment.mk
                                    "encode_ptr"
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
                              (Expr.field
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "ptr" PathArguments.none)]))
                                (Member.named "thin_pointer"))])
                          false)]))))
              false)]))])

/-- `spec/lang/representation.md:248` -/
def impl_Type__decode_4 : Item :=
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
          "decode"
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
            (FnArg.typed
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
                    (Member.named "sized_head_layout")
                    true
                    (Pat.ident false false "sized_head_layout" none)),
                  (FieldPat.mk
                    []
                    (Member.named "unsized_field")
                    true
                    (Pat.ident false false "unsized_field" none))]
                false)
              (Ty.path none (Path.mk false [(PathSegment.mk "Self" PathArguments.none)]))),
            (FnArg.typed
              []
              (Pat.ident false false "bytes" none)
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
                                                (PathSegment.mk "M" PathArguments.none),
                                                (PathSegment.mk "Provenance" PathArguments.none)])))]))])))]))])))]
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
                (Path.mk false [(PathSegment.mk "assert" PathArguments.none)])
                MacroDelimiter.paren
                (MacroBody.exprs
                  [
                    (Expr.methodCall
                      (Expr.path
                        none
                        (Path.mk false [(PathSegment.mk "unsized_field" PathArguments.none)]))
                      "is_none"
                      none
                      []),
                    (Expr.lit (Lit.str "decode of Type::Tuple with unsized field"))]
                  false))
              true),
            (Stmt.letStmt
              []
              (Pat.tuple [(Pat.ident false false "size" none), Pat.wild])
              (some
                (Expr.methodCall
                  (Expr.path
                    none
                    (Path.mk false [(PathSegment.mk "sized_head_layout" PathArguments.none)]))
                  "head_size_and_align"
                  none
                  []))
              none),
            (Stmt.expr
              (Expr.ite
                (Expr.binary
                  (Expr.methodCall
                    (Expr.path none (Path.mk false [(PathSegment.mk "bytes" PathArguments.none)]))
                    "len"
                    none
                    [])
                  BinOp.ne
                  (Expr.methodCall
                    (Expr.path none (Path.mk false [(PathSegment.mk "size" PathArguments.none)]))
                    "bytes"
                    none
                    []))
                (Block.mk
                  [
                    (Stmt.macro
                      []
                      (Macro.mk
                        (Path.mk false [(PathSegment.mk "panic" PathArguments.none)])
                        MacroDelimiter.paren
                        (MacroBody.exprs
                          [(Expr.lit (Lit.str "decode of Type::Tuple with invalid length"))]
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
                            (Path.mk false [(PathSegment.mk "sized_fields" PathArguments.none)]))
                          "try_map"
                          none
                          [
                            (Expr.closure
                              false
                              [
                                (Pat.tuple
                                  [
                                    (Pat.ident false false "offset" none),
                                    (Pat.ident false false "ty" none)])]
                              none
                              (Expr.block
                                none
                                (Block.mk
                                  [
                                    (Stmt.letStmt
                                      []
                                      (Pat.ident false false "subslice" none)
                                      (some
                                        (Expr.methodCall
                                          (Expr.path
                                            none
                                            (Path.mk
                                              false
                                              [(PathSegment.mk "bytes" PathArguments.none)]))
                                          "subslice_with_length"
                                          none
                                          [
                                            (Expr.methodCall
                                              (Expr.path
                                                none
                                                (Path.mk
                                                  false
                                                  [(PathSegment.mk "offset" PathArguments.none)]))
                                              "bytes"
                                              none
                                              []),
                                            (Expr.methodCall
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
                                                                "M"
                                                                PathArguments.none),
                                                              (PathSegment.mk
                                                                "T"
                                                                PathArguments.none)])))])
                                                  [])
                                                "expect_size"
                                                none
                                                [
                                                  (Expr.lit
                                                    (Lit.str
                                                      "WF ensures all sized tuple fields are sized"))])
                                              "bytes"
                                              none
                                              [])]))
                                      none),
                                    (Stmt.expr
                                      (Expr.methodCall
                                        (Expr.path
                                          none
                                          (Path.mk false [(PathSegment.mk "ty" PathArguments.none)]))
                                        "decode"
                                        (some
                                          [
                                            (GenericArgument.type
                                              (Ty.path
                                                none
                                                (Path.mk
                                                  false
                                                  [(PathSegment.mk "M" PathArguments.none)])))])
                                        [
                                          (Expr.path
                                            none
                                            (Path.mk
                                              false
                                              [(PathSegment.mk "subslice" PathArguments.none)]))])
                                      false)])))]))])])
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
          "encode"
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
            (FnArg.typed
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
                    (Member.named "sized_head_layout")
                    true
                    (Pat.ident false false "sized_head_layout" none)),
                  (FieldPat.mk
                    []
                    (Member.named "unsized_field")
                    true
                    (Pat.ident false false "unsized_field" none))]
                false)
              (Ty.path none (Path.mk false [(PathSegment.mk "Self" PathArguments.none)]))),
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
                            (Ty.path none (Path.mk false [(PathSegment.mk "M" PathArguments.none)])))]))])))]
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
                                              (PathSegment.mk "M" PathArguments.none),
                                              (PathSegment.mk "Provenance" PathArguments.none)])))]))])))]))]))))
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
                      (Expr.path
                        none
                        (Path.mk false [(PathSegment.mk "unsized_field" PathArguments.none)]))
                      "is_none"
                      none
                      []),
                    (Expr.lit (Lit.str "encode of Type::Tuple with unsized field"))]
                  false))
              true),
            (Stmt.letStmt
              []
              (Pat.tuple [(Pat.ident false false "size" none), Pat.wild])
              (some
                (Expr.methodCall
                  (Expr.path
                    none
                    (Path.mk false [(PathSegment.mk "sized_head_layout" PathArguments.none)]))
                  "head_size_and_align"
                  none
                  []))
              none),
            (Stmt.letStmt
              []
              (Pat.tupleStruct
                none
                (Path.mk
                  false
                  [
                    (PathSegment.mk "Value" PathArguments.none),
                    (PathSegment.mk "Tuple" PathArguments.none)])
                [(Pat.ident false false "values" none)])
              (some (Expr.path none (Path.mk false [(PathSegment.mk "val" PathArguments.none)])))
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
                            (MacroBody.exprs [] false)))
                        false)])))),
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
                        (Path.mk false [(PathSegment.mk "values" PathArguments.none)]))
                      "len"
                      none
                      []),
                    (Expr.methodCall
                      (Expr.path
                        none
                        (Path.mk false [(PathSegment.mk "sized_fields" PathArguments.none)]))
                      "len"
                      none
                      [])]
                  false))
              true),
            (Stmt.letStmt
              []
              (Pat.ident false true "bytes" none)
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
            (Stmt.expr
              (Expr.forLoop
                none
                (Pat.tuple
                  [
                    (Pat.tuple
                      [(Pat.ident false false "offset" none), (Pat.ident false false "ty" none)]),
                    (Pat.ident false false "value" none)])
                (Expr.methodCall
                  (Expr.path
                    none
                    (Path.mk false [(PathSegment.mk "sized_fields" PathArguments.none)]))
                  "zip"
                  none
                  [(Expr.path none (Path.mk false [(PathSegment.mk "values" PathArguments.none)]))])
                (Block.mk
                  [
                    (Stmt.expr
                      (Expr.methodCall
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "bytes" PathArguments.none)]))
                        "write_subslice_at_index"
                        none
                        [
                          (Expr.methodCall
                            (Expr.path
                              none
                              (Path.mk false [(PathSegment.mk "offset" PathArguments.none)]))
                            "bytes"
                            none
                            []),
                          (Expr.methodCall
                            (Expr.path
                              none
                              (Path.mk false [(PathSegment.mk "ty" PathArguments.none)]))
                            "encode"
                            (some
                              [
                                (GenericArgument.type
                                  (Ty.path
                                    none
                                    (Path.mk false [(PathSegment.mk "M" PathArguments.none)])))])
                            [
                              (Expr.path
                                none
                                (Path.mk false [(PathSegment.mk "value" PathArguments.none)]))])])
                      true)]))
              false),
            (Stmt.expr
              (Expr.path none (Path.mk false [(PathSegment.mk "bytes" PathArguments.none)]))
              false)]))])

/-- `spec/lang/representation.md:286` -/
def impl_Type__decode_5 : Item :=
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
          "decode"
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
            (FnArg.typed
              []
              (Pat.struct
                none
                (Path.mk
                  false
                  [
                    (PathSegment.mk "Type" PathArguments.none),
                    (PathSegment.mk "Array" PathArguments.none)])
                [
                  (FieldPat.mk [] (Member.named "elem") true (Pat.ident false false "elem" none)),
                  (FieldPat.mk [] (Member.named "count") true (Pat.ident false false "count" none))]
                false)
              (Ty.path none (Path.mk false [(PathSegment.mk "Self" PathArguments.none)]))),
            (FnArg.typed
              []
              (Pat.ident false false "bytes" none)
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
                                                (PathSegment.mk "M" PathArguments.none),
                                                (PathSegment.mk "Provenance" PathArguments.none)])))]))])))]))])))]
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
            (Stmt.letStmt
              []
              (Pat.ident false false "elem_size" none)
              (some
                (Expr.methodCall
                  (Expr.methodCall
                    (Expr.path none (Path.mk false [(PathSegment.mk "elem" PathArguments.none)]))
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
                  [(Expr.lit (Lit.str "WF ensures array element is sized"))]))
              none),
            (Stmt.letStmt
              []
              (Pat.ident false false "full_size" none)
              (some
                (Expr.binary
                  (Expr.path none (Path.mk false [(PathSegment.mk "elem_size" PathArguments.none)]))
                  BinOp.mul
                  (Expr.path none (Path.mk false [(PathSegment.mk "count" PathArguments.none)]))))
              none),
            (Stmt.expr
              (Expr.ite
                (Expr.binary
                  (Expr.methodCall
                    (Expr.path none (Path.mk false [(PathSegment.mk "bytes" PathArguments.none)]))
                    "len"
                    none
                    [])
                  BinOp.ne
                  (Expr.methodCall
                    (Expr.path
                      none
                      (Path.mk false [(PathSegment.mk "full_size" PathArguments.none)]))
                    "bytes"
                    none
                    []))
                (Block.mk
                  [
                    (Stmt.macro
                      []
                      (Macro.mk
                        (Path.mk false [(PathSegment.mk "panic" PathArguments.none)])
                        MacroDelimiter.paren
                        (MacroBody.exprs
                          [(Expr.lit (Lit.str "decode of Type::Array with invalid length"))]
                          false))
                      true)])
                none)
              false),
            (Stmt.letStmt
              []
              (Pat.typed
                (Pat.ident false false "chunks" none)
                (Ty.path
                  none
                  (Path.mk
                    false
                    [
                      (PathSegment.mk
                        "List"
                        (PathArguments.angleBracketed false [(GenericArgument.type Ty.infer)]))])))
              (some
                (Expr.methodCall
                  (Expr.methodCall
                    (Expr.paren
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
                            (Path.mk false [(PathSegment.mk "count" PathArguments.none)])))))
                    "map"
                    none
                    [
                      (Expr.closure
                        false
                        [(Pat.ident false false "i" none)]
                        none
                        (Expr.methodCall
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "bytes" PathArguments.none)]))
                          "subslice_with_length"
                          none
                          [
                            (Expr.binary
                              (Expr.path
                                none
                                (Path.mk false [(PathSegment.mk "i" PathArguments.none)]))
                              BinOp.mul
                              (Expr.methodCall
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "elem_size" PathArguments.none)]))
                                "bytes"
                                none
                                [])),
                            (Expr.methodCall
                              (Expr.path
                                none
                                (Path.mk false [(PathSegment.mk "elem_size" PathArguments.none)]))
                              "bytes"
                              none
                              [])]))])
                  "collect"
                  none
                  []))
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
                          (PathSegment.mk "Tuple" PathArguments.none)]))
                    [
                      (Expr.tryExpr
                        (Expr.methodCall
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "chunks" PathArguments.none)]))
                          "try_map"
                          none
                          [
                            (Expr.closure
                              false
                              [(Pat.ident false false "elem_bytes" none)]
                              none
                              (Expr.methodCall
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "elem" PathArguments.none)]))
                                "decode"
                                (some
                                  [
                                    (GenericArgument.type
                                      (Ty.path
                                        none
                                        (Path.mk false [(PathSegment.mk "M" PathArguments.none)])))])
                                [
                                  (Expr.path
                                    none
                                    (Path.mk
                                      false
                                      [(PathSegment.mk "elem_bytes" PathArguments.none)]))]))]))])])
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
          "encode"
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
            (FnArg.typed
              []
              (Pat.struct
                none
                (Path.mk
                  false
                  [
                    (PathSegment.mk "Type" PathArguments.none),
                    (PathSegment.mk "Array" PathArguments.none)])
                [
                  (FieldPat.mk [] (Member.named "elem") true (Pat.ident false false "elem" none)),
                  (FieldPat.mk [] (Member.named "count") true (Pat.ident false false "count" none))]
                false)
              (Ty.path none (Path.mk false [(PathSegment.mk "Self" PathArguments.none)]))),
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
                            (Ty.path none (Path.mk false [(PathSegment.mk "M" PathArguments.none)])))]))])))]
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
                                              (PathSegment.mk "M" PathArguments.none),
                                              (PathSegment.mk "Provenance" PathArguments.none)])))]))])))]))]))))
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
                    (PathSegment.mk "Tuple" PathArguments.none)])
                [(Pat.ident false false "values" none)])
              (some (Expr.path none (Path.mk false [(PathSegment.mk "val" PathArguments.none)])))
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
                            (MacroBody.exprs [] false)))
                        false)])))),
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
                        (Path.mk false [(PathSegment.mk "values" PathArguments.none)]))
                      "len"
                      none
                      []),
                    (Expr.path none (Path.mk false [(PathSegment.mk "count" PathArguments.none)]))]
                  false))
              true),
            (Stmt.expr
              (Expr.methodCall
                (Expr.path none (Path.mk false [(PathSegment.mk "values" PathArguments.none)]))
                "flat_map"
                none
                [
                  (Expr.closure
                    false
                    [(Pat.ident false false "value" none)]
                    none
                    (Expr.block
                      none
                      (Block.mk
                        [
                          (Stmt.letStmt
                            []
                            (Pat.ident false false "bytes" none)
                            (some
                              (Expr.methodCall
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "elem" PathArguments.none)]))
                                "encode"
                                (some
                                  [
                                    (GenericArgument.type
                                      (Ty.path
                                        none
                                        (Path.mk false [(PathSegment.mk "M" PathArguments.none)])))])
                                [
                                  (Expr.path
                                    none
                                    (Path.mk false [(PathSegment.mk "value" PathArguments.none)]))]))
                            none),
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
                                      (Path.mk false [(PathSegment.mk "bytes" PathArguments.none)]))
                                    "len"
                                    none
                                    []),
                                  (Expr.methodCall
                                    (Expr.methodCall
                                      (Expr.methodCall
                                        (Expr.path
                                          none
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "elem" PathArguments.none)]))
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
                                      [(Expr.lit (Lit.str "WF ensures array element is sized"))])
                                    "bytes"
                                    none
                                    [])]
                                false))
                            true),
                          (Stmt.expr
                            (Expr.path
                              none
                              (Path.mk false [(PathSegment.mk "bytes" PathArguments.none)]))
                            false)])))])
              false)]))])

/-- `spec/lang/representation.md:322` -/
def impl_Type__decode_6 : Item :=
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
          "decode"
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
            (FnArg.typed
              []
              (Pat.struct
                none
                (Path.mk
                  false
                  [
                    (PathSegment.mk "Type" PathArguments.none),
                    (PathSegment.mk "Union" PathArguments.none)])
                [
                  (FieldPat.mk [] (Member.named "size") true (Pat.ident false false "size" none)),
                  (FieldPat.mk
                    []
                    (Member.named "chunks")
                    true
                    (Pat.ident false false "chunks" none))]
                true)
              (Ty.path none (Path.mk false [(PathSegment.mk "Self" PathArguments.none)]))),
            (FnArg.typed
              []
              (Pat.ident false false "bytes" none)
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
                                                (PathSegment.mk "M" PathArguments.none),
                                                (PathSegment.mk "Provenance" PathArguments.none)])))]))])))]))])))]
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
                    (Expr.path none (Path.mk false [(PathSegment.mk "bytes" PathArguments.none)]))
                    "len"
                    none
                    [])
                  BinOp.ne
                  (Expr.methodCall
                    (Expr.path none (Path.mk false [(PathSegment.mk "size" PathArguments.none)]))
                    "bytes"
                    none
                    []))
                (Block.mk
                  [
                    (Stmt.macro
                      []
                      (Macro.mk
                        (Path.mk false [(PathSegment.mk "panic" PathArguments.none)])
                        MacroDelimiter.paren
                        (MacroBody.exprs
                          [(Expr.lit (Lit.str "decode of Type::Union with invalid length"))]
                          false))
                      true)])
                none)
              false),
            (Stmt.letStmt
              []
              (Pat.ident false true "chunk_data" none)
              (some
                (Expr.macro
                  (Macro.mk
                    (Path.mk false [(PathSegment.mk "list" PathArguments.none)])
                    MacroDelimiter.bracket
                    (MacroBody.exprs [] false))))
              none),
            (Stmt.expr
              (Expr.forLoop
                none
                (Pat.tuple
                  [(Pat.ident false false "offset" none), (Pat.ident false false "size" none)])
                (Expr.path none (Path.mk false [(PathSegment.mk "chunks" PathArguments.none)]))
                (Block.mk
                  [
                    (Stmt.expr
                      (Expr.methodCall
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "chunk_data" PathArguments.none)]))
                        "push"
                        none
                        [
                          (Expr.methodCall
                            (Expr.path
                              none
                              (Path.mk false [(PathSegment.mk "bytes" PathArguments.none)]))
                            "subslice_with_length"
                            none
                            [
                              (Expr.methodCall
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "offset" PathArguments.none)]))
                                "bytes"
                                none
                                []),
                              (Expr.methodCall
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "size" PathArguments.none)]))
                                "bytes"
                                none
                                [])])])
                      true)]))
              false),
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
                          (PathSegment.mk "Union" PathArguments.none)]))
                    [
                      (Expr.path
                        none
                        (Path.mk false [(PathSegment.mk "chunk_data" PathArguments.none)]))])])
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
          "encode"
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
            (FnArg.typed
              []
              (Pat.struct
                none
                (Path.mk
                  false
                  [
                    (PathSegment.mk "Type" PathArguments.none),
                    (PathSegment.mk "Union" PathArguments.none)])
                [
                  (FieldPat.mk [] (Member.named "size") true (Pat.ident false false "size" none)),
                  (FieldPat.mk
                    []
                    (Member.named "chunks")
                    true
                    (Pat.ident false false "chunks" none))]
                true)
              (Ty.path none (Path.mk false [(PathSegment.mk "Self" PathArguments.none)]))),
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
                            (Ty.path none (Path.mk false [(PathSegment.mk "M" PathArguments.none)])))]))])))]
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
                                              (PathSegment.mk "M" PathArguments.none),
                                              (PathSegment.mk "Provenance" PathArguments.none)])))]))])))]))]))))
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
                    (PathSegment.mk "Union" PathArguments.none)])
                [(Pat.ident false false "chunk_data" none)])
              (some (Expr.path none (Path.mk false [(PathSegment.mk "val" PathArguments.none)])))
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
                            (MacroBody.exprs [] false)))
                        false)])))),
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
                        (Path.mk false [(PathSegment.mk "chunk_data" PathArguments.none)]))
                      "len"
                      none
                      []),
                    (Expr.methodCall
                      (Expr.path
                        none
                        (Path.mk false [(PathSegment.mk "chunks" PathArguments.none)]))
                      "len"
                      none
                      [])]
                  false))
              true),
            (Stmt.letStmt
              []
              (Pat.ident false true "bytes" none)
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
            (Stmt.expr
              (Expr.forLoop
                none
                (Pat.tuple
                  [
                    (Pat.tuple
                      [(Pat.ident false false "offset" none), (Pat.ident false false "size" none)]),
                    (Pat.ident false false "data" none)])
                (Expr.methodCall
                  (Expr.path none (Path.mk false [(PathSegment.mk "chunks" PathArguments.none)]))
                  "zip"
                  none
                  [
                    (Expr.path
                      none
                      (Path.mk false [(PathSegment.mk "chunk_data" PathArguments.none)]))])
                (Block.mk
                  [
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
                                (Path.mk false [(PathSegment.mk "size" PathArguments.none)]))
                              "bytes"
                              none
                              []),
                            (Expr.methodCall
                              (Expr.path
                                none
                                (Path.mk false [(PathSegment.mk "data" PathArguments.none)]))
                              "len"
                              none
                              [])]
                          false))
                      true),
                    (Stmt.expr
                      (Expr.methodCall
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "bytes" PathArguments.none)]))
                        "write_subslice_at_index"
                        none
                        [
                          (Expr.methodCall
                            (Expr.path
                              none
                              (Path.mk false [(PathSegment.mk "offset" PathArguments.none)]))
                            "bytes"
                            none
                            []),
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "data" PathArguments.none)]))])
                      true)]))
              false),
            (Stmt.expr
              (Expr.path none (Path.mk false [(PathSegment.mk "bytes" PathArguments.none)]))
              false)]))])

/-- `spec/lang/representation.md:353` -/
def fn_decode_discriminant : Item :=
  (Item.fn
    [
      (Attr.mk
        true
        "doc"
        (AttrMeta.nameValue
          " Uses the `Discriminator` to decode the discriminant from the tag read out of the value's bytes using the accessor.")),
      (Attr.mk
        true
        "doc"
        (AttrMeta.nameValue
          " Returns `Ok(None)` when reaching `Discriminator::Invalid` and when any of the reads")),
      (Attr.mk
        true
        "doc"
        (AttrMeta.nameValue " for `Discriminator::Branch` encounters uninitialized memory.")),
      (Attr.mk true "doc" (AttrMeta.nameValue " Returns `Err` only if `accessor` returns `Err`.")),
      (Attr.mk true "doc" (AttrMeta.nameValue "")),
      (Attr.mk
        true
        "doc"
        (AttrMeta.nameValue
          " The accessor is given an offset relative to the beginning of the encoded enum value,")),
      (Attr.mk
        true
        "doc"
        (AttrMeta.nameValue " and it should return the abstract byte at that offset.")),
      (Attr.mk
        true
        "doc"
        (AttrMeta.nameValue
          " FIXME: we have multiple quite different fail sources, it would be nice to return more error information."))]
    Visibility.inherited
    (Signature.mk
      false
      false
      false
      none
      "decode_discriminant"
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
        (FnArg.typed
          []
          (Pat.ident false true "accessor" none)
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
                      "FnMut"
                      (PathArguments.parenthesized
                        [
                          (Ty.path
                            none
                            (Path.mk false [(PathSegment.mk "Offset" PathArguments.none)])),
                          (Ty.path
                            none
                            (Path.mk false [(PathSegment.mk "Size" PathArguments.none)]))]
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
                                                                            PathArguments.none)])))]))])))]))])))]))])))))]))])),
        (FnArg.typed
          []
          (Pat.ident false false "discriminator" none)
          (Ty.path none (Path.mk false [(PathSegment.mk "Discriminator" PathArguments.none)])))]
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
                              "Option"
                              (PathArguments.angleBracketed
                                false
                                [
                                  (GenericArgument.type
                                    (Ty.path
                                      none
                                      (Path.mk false [(PathSegment.mk "Int" PathArguments.none)])))]))])))]))]))))
    (Block.mk
      [
        (Stmt.expr
          (Expr.matchExpr
            (Expr.path none (Path.mk false [(PathSegment.mk "discriminator" PathArguments.none)]))
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
                  [(Pat.ident false false "val" none)])
                none
                (Expr.call
                  (Expr.path none (Path.mk false [(PathSegment.mk "ret" PathArguments.none)]))
                  [
                    (Expr.call
                      (Expr.path none (Path.mk false [(PathSegment.mk "Some" PathArguments.none)]))
                      [(Expr.path none (Path.mk false [(PathSegment.mk "val" PathArguments.none)]))])])),
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
                  [(Expr.path none (Path.mk false [(PathSegment.mk "None" PathArguments.none)]))])),
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
                      (Member.named "children")
                      true
                      (Pat.ident false false "children" none)),
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
                        (Pat.ident false false "bytes" none)
                        (some
                          (Expr.tryExpr
                            (Expr.call
                              (Expr.path
                                none
                                (Path.mk false [(PathSegment.mk "accessor" PathArguments.none)]))
                              [
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "offset" PathArguments.none)])),
                                (Expr.field
                                  (Expr.path
                                    none
                                    (Path.mk
                                      false
                                      [(PathSegment.mk "value_type" PathArguments.none)]))
                                  (Member.named "size"))])))
                        none),
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
                                  (PathSegment.mk "Value" PathArguments.none),
                                  (PathSegment.mk "Int" PathArguments.none)])
                              [(Pat.ident false false "val" none)])])
                        (some
                          (Expr.methodCall
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
                                  (Path.mk false [(PathSegment.mk "value_type" PathArguments.none)]))])
                            "decode"
                            (some
                              [
                                (GenericArgument.type
                                  (Ty.path
                                    none
                                    (Path.mk false [(PathSegment.mk "M" PathArguments.none)])))])
                            [
                              (Expr.path
                                none
                                (Path.mk false [(PathSegment.mk "bytes" PathArguments.none)]))]))
                        (some
                          (Expr.block
                            none
                            (Block.mk
                              [
                                (Stmt.expr
                                  (Expr.returnExpr
                                    (some
                                      (Expr.call
                                        (Expr.path
                                          none
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "ret" PathArguments.none)]))
                                        [
                                          (Expr.path
                                            none
                                            (Path.mk
                                              false
                                              [(PathSegment.mk "None" PathArguments.none)]))])))
                                  true)])))),
                      (Stmt.letStmt
                        []
                        (Pat.ident false false "next_discriminator" none)
                        (some
                          (Expr.methodCall
                            (Expr.methodCall
                              (Expr.methodCall
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "children" PathArguments.none)]))
                                "iter"
                                none
                                [])
                              "find_map"
                              none
                              [
                                (Expr.closure
                                  false
                                  [
                                    (Pat.tuple
                                      [
                                        (Pat.tuple
                                          [
                                            (Pat.ident false false "start" none),
                                            (Pat.ident false false "end" none)]),
                                        (Pat.ident false false "child" none)])]
                                  none
                                  (Expr.ite
                                    (Expr.binary
                                      (Expr.binary
                                        (Expr.path
                                          none
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "start" PathArguments.none)]))
                                        BinOp.le
                                        (Expr.path
                                          none
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "val" PathArguments.none)])))
                                      BinOp.and
                                      (Expr.binary
                                        (Expr.path
                                          none
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "val" PathArguments.none)]))
                                        BinOp.lt
                                        (Expr.path
                                          none
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "end" PathArguments.none)]))))
                                    (Block.mk
                                      [
                                        (Stmt.expr
                                          (Expr.call
                                            (Expr.path
                                              none
                                              (Path.mk
                                                false
                                                [(PathSegment.mk "Some" PathArguments.none)]))
                                            [
                                              (Expr.path
                                                none
                                                (Path.mk
                                                  false
                                                  [(PathSegment.mk "child" PathArguments.none)]))])
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
                                                  [(PathSegment.mk "None" PathArguments.none)]))
                                              false)])))))])
                            "unwrap_or"
                            none
                            [
                              (Expr.path
                                none
                                (Path.mk false [(PathSegment.mk "fallback" PathArguments.none)]))]))
                        none),
                      (Stmt.expr
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
                              (Path.mk
                                false
                                [(PathSegment.mk "next_discriminator" PathArguments.none)]))])
                        false)])))])
          false)]))

/-- `spec/lang/representation.md:377` -/
def fn_encode_discriminant : Item :=
  (Item.fn
    [
      (Attr.mk
        true
        "doc"
        (AttrMeta.nameValue
          " Writes the tag described by the tagger into the bytes accessed using the accessor.")),
      (Attr.mk true "doc" (AttrMeta.nameValue " Returns `Err` only if `accessor` returns `Err`.")),
      (Attr.mk true "doc" (AttrMeta.nameValue "")),
      (Attr.mk
        true
        "doc"
        (AttrMeta.nameValue
          " The accessor is given an offset relative to the beginning of the encoded enum value")),
      (Attr.mk
        true
        "doc"
        (AttrMeta.nameValue " and the integer value and type to store at that offset."))]
    Visibility.inherited
    (Signature.mk
      false
      false
      false
      none
      "encode_discriminant"
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
        (FnArg.typed
          []
          (Pat.ident false true "accessor" none)
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
                      "FnMut"
                      (PathArguments.parenthesized
                        [
                          (Ty.path
                            none
                            (Path.mk false [(PathSegment.mk "Offset" PathArguments.none)])),
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
                                                            (PathSegment.mk "M" PathArguments.none),
                                                            (PathSegment.mk
                                                              "Provenance"
                                                              PathArguments.none)])))]))])))]))]))]
                        (some
                          (Ty.path
                            none
                            (Path.mk false [(PathSegment.mk "Result" PathArguments.none)])))))]))])),
        (FnArg.typed
          []
          (Pat.ident false false "tagger" none)
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
                          (Path.mk false [(PathSegment.mk "Offset" PathArguments.none)]))),
                      (GenericArgument.type
                        (Ty.tuple
                          [
                            (Ty.path
                              none
                              (Path.mk false [(PathSegment.mk "IntType" PathArguments.none)])),
                            (Ty.path
                              none
                              (Path.mk false [(PathSegment.mk "Int" PathArguments.none)]))]))]))])))]
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
              [
                (Pat.ident false false "offset" none),
                (Pat.tuple
                  [(Pat.ident false false "value_type" none), (Pat.ident false false "value" none)])])
            (Expr.methodCall
              (Expr.path none (Path.mk false [(PathSegment.mk "tagger" PathArguments.none)]))
              "iter"
              none
              [])
            (Block.mk
              [
                (Stmt.letStmt
                  []
                  (Pat.ident false false "bytes" none)
                  (some
                    (Expr.methodCall
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
                            (Path.mk false [(PathSegment.mk "value_type" PathArguments.none)]))])
                      "encode"
                      (some
                        [
                          (GenericArgument.type
                            (Ty.path none (Path.mk false [(PathSegment.mk "M" PathArguments.none)])))])
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
                              (Path.mk false [(PathSegment.mk "value" PathArguments.none)]))])]))
                  none),
                (Stmt.expr
                  (Expr.tryExpr
                    (Expr.call
                      (Expr.path
                        none
                        (Path.mk false [(PathSegment.mk "accessor" PathArguments.none)]))
                      [
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "offset" PathArguments.none)])),
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "bytes" PathArguments.none)]))]))
                  true)]))
          false),
        (Stmt.expr
          (Expr.call
            (Expr.path none (Path.mk false [(PathSegment.mk "ret" PathArguments.none)]))
            [(Expr.tuple [])])
          false)]))

/-- `spec/lang/representation.md:393` -/
def impl_Type__decode_7 : Item :=
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
          "decode"
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
            (FnArg.typed
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
                    (Pat.ident false false "variants" none)),
                  (FieldPat.mk
                    []
                    (Member.named "discriminator")
                    true
                    (Pat.ident false false "discriminator" none)),
                  (FieldPat.mk [] (Member.named "size") true (Pat.ident false false "size" none))]
                true)
              (Ty.path none (Path.mk false [(PathSegment.mk "Self" PathArguments.none)]))),
            (FnArg.typed
              []
              (Pat.ident false false "bytes" none)
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
                                                (PathSegment.mk "M" PathArguments.none),
                                                (PathSegment.mk "Provenance" PathArguments.none)])))]))])))]))])))]
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
                    (Expr.path none (Path.mk false [(PathSegment.mk "bytes" PathArguments.none)]))
                    "len"
                    none
                    [])
                  BinOp.ne
                  (Expr.methodCall
                    (Expr.path none (Path.mk false [(PathSegment.mk "size" PathArguments.none)]))
                    "bytes"
                    none
                    []))
                (Block.mk
                  [
                    (Stmt.macro
                      []
                      (Macro.mk
                        (Path.mk false [(PathSegment.mk "panic" PathArguments.none)])
                        MacroDelimiter.paren
                        (MacroBody.exprs
                          [(Expr.lit (Lit.str "decode of Type::Enum with invalid length"))]
                          false))
                      true)])
                none)
              false),
            (Stmt.letStmt
              []
              (Pat.ident false false "discriminant" none)
              (some
                (Expr.tryExpr
                  (Expr.methodCall
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
                        (Expr.closure
                          false
                          [
                            (Pat.ident false false "offset" none),
                            (Pat.ident false false "size" none)]
                          none
                          (Expr.call
                            (Expr.path
                              none
                              (Path.mk false [(PathSegment.mk "ret" PathArguments.none)]))
                            [
                              (Expr.methodCall
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "bytes" PathArguments.none)]))
                                "subslice_with_length"
                                none
                                [
                                  (Expr.methodCall
                                    (Expr.path
                                      none
                                      (Path.mk false [(PathSegment.mk "offset" PathArguments.none)]))
                                    "bytes"
                                    none
                                    []),
                                  (Expr.methodCall
                                    (Expr.path
                                      none
                                      (Path.mk false [(PathSegment.mk "size" PathArguments.none)]))
                                    "bytes"
                                    none
                                    [])])])),
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "discriminator" PathArguments.none)]))])
                    "unwrap"
                    none
                    [])))
              none),
            (Stmt.letStmt
              []
              (Pat.tupleStruct
                none
                (Path.mk false [(PathSegment.mk "Some" PathArguments.none)])
                [(Pat.ident false false "value" none)])
              (some
                (Expr.methodCall
                  (Expr.field
                    (Expr.index
                      (Expr.path
                        none
                        (Path.mk false [(PathSegment.mk "variants" PathArguments.none)]))
                      (Expr.path
                        none
                        (Path.mk false [(PathSegment.mk "discriminant" PathArguments.none)])))
                    (Member.named "ty"))
                  "decode"
                  none
                  [(Expr.path none (Path.mk false [(PathSegment.mk "bytes" PathArguments.none)]))]))
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
                        false)])))),
            (Stmt.expr
              (Expr.call
                (Expr.path none (Path.mk false [(PathSegment.mk "Some" PathArguments.none)]))
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
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "value" PathArguments.none)])))]
                    false
                    none)])
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
          "encode"
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
            (FnArg.typed
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
              (Ty.path none (Path.mk false [(PathSegment.mk "Self" PathArguments.none)]))),
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
                            (Ty.path none (Path.mk false [(PathSegment.mk "M" PathArguments.none)])))]))])))]
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
                                              (PathSegment.mk "M" PathArguments.none),
                                              (PathSegment.mk "Provenance" PathArguments.none)])))]))])))]))]))))
        (Block.mk
          [
            (Stmt.letStmt
              []
              (Pat.tuple
                [(Pat.ident false false "discriminant" none), (Pat.ident false false "data" none)])
              (some
                (Expr.matchExpr
                  (Expr.path none (Path.mk false [(PathSegment.mk "val" PathArguments.none)]))
                  [
                    (Arm.mk
                      []
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
                        false)
                      none
                      (Expr.tuple
                        [
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "discriminant" PathArguments.none)])),
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "data" PathArguments.none)]))])),
                    (Arm.mk
                      []
                      Pat.wild
                      none
                      (Expr.macro
                        (Macro.mk
                          (Path.mk false [(PathSegment.mk "panic" PathArguments.none)])
                          MacroDelimiter.paren
                          (MacroBody.exprs [] false))))]))
              none),
            (Stmt.letStmt
              []
              (Pat.struct
                none
                (Path.mk false [(PathSegment.mk "Variant" PathArguments.none)])
                [
                  (FieldPat.mk [] (Member.named "ty") false (Pat.ident false false "variant" none)),
                  (FieldPat.mk
                    []
                    (Member.named "tagger")
                    true
                    (Pat.ident false false "tagger" none))]
                false)
              (some
                (Expr.index
                  (Expr.path none (Path.mk false [(PathSegment.mk "variants" PathArguments.none)]))
                  (Expr.path
                    none
                    (Path.mk false [(PathSegment.mk "discriminant" PathArguments.none)]))))
              none),
            (Stmt.letStmt
              []
              (Pat.ident false true "bytes" none)
              (some
                (Expr.methodCall
                  (Expr.path none (Path.mk false [(PathSegment.mk "variant" PathArguments.none)]))
                  "encode"
                  none
                  [(Expr.path none (Path.mk false [(PathSegment.mk "data" PathArguments.none)]))]))
              none),
            (Stmt.expr
              (Expr.methodCall
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
                    (Expr.closure
                      false
                      [
                        (Pat.ident false false "offset" none),
                        (Pat.ident false false "value_bytes" none)]
                      none
                      (Expr.block
                        none
                        (Block.mk
                          [
                            (Stmt.expr
                              (Expr.methodCall
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "bytes" PathArguments.none)]))
                                "write_subslice_at_index"
                                none
                                [
                                  (Expr.methodCall
                                    (Expr.path
                                      none
                                      (Path.mk false [(PathSegment.mk "offset" PathArguments.none)]))
                                    "bytes"
                                    none
                                    []),
                                  (Expr.path
                                    none
                                    (Path.mk
                                      false
                                      [(PathSegment.mk "value_bytes" PathArguments.none)]))])
                              true),
                            (Stmt.expr
                              (Expr.call
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "ret" PathArguments.none)]))
                                [(Expr.tuple [])])
                              false)]))),
                    (Expr.path none (Path.mk false [(PathSegment.mk "tagger" PathArguments.none)]))])
                "unwrap"
                none
                [])
              true),
            (Stmt.expr
              (Expr.path none (Path.mk false [(PathSegment.mk "bytes" PathArguments.none)]))
              false)]))])

/-- `spec/lang/representation.md:441` -/
def impl_Type__decode_8 : Item :=
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
          "decode"
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
            (FnArg.typed
              []
              (Pat.struct
                none
                (Path.mk
                  false
                  [
                    (PathSegment.mk "Type" PathArguments.none),
                    (PathSegment.mk "Slice" PathArguments.none)])
                []
                true)
              (Ty.path none (Path.mk false [(PathSegment.mk "Self" PathArguments.none)]))),
            (FnArg.typed
              []
              (Pat.ident false false "bytes" none)
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
                                                (PathSegment.mk "M" PathArguments.none),
                                                (PathSegment.mk "Provenance" PathArguments.none)])))]))])))]))])))]
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
              (Expr.macro
                (Macro.mk
                  (Path.mk false [(PathSegment.mk "panic" PathArguments.none)])
                  MacroDelimiter.paren
                  (MacroBody.exprs [(Expr.lit (Lit.str "decode of Type::Slice"))] false)))
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
          "encode"
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
            (FnArg.typed
              []
              (Pat.struct
                none
                (Path.mk
                  false
                  [
                    (PathSegment.mk "Type" PathArguments.none),
                    (PathSegment.mk "Slice" PathArguments.none)])
                []
                true)
              (Ty.path none (Path.mk false [(PathSegment.mk "Self" PathArguments.none)]))),
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
                            (Ty.path none (Path.mk false [(PathSegment.mk "M" PathArguments.none)])))]))])))]
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
                                              (PathSegment.mk "M" PathArguments.none),
                                              (PathSegment.mk "Provenance" PathArguments.none)])))]))])))]))]))))
        (Block.mk
          [
            (Stmt.expr
              (Expr.macro
                (Macro.mk
                  (Path.mk false [(PathSegment.mk "panic" PathArguments.none)])
                  MacroDelimiter.paren
                  (MacroBody.exprs [(Expr.lit (Lit.str "encode of Type::Slice"))] false)))
              false)]))])

/-- `spec/lang/representation.md:450` -/
def impl_Type__decode_9 : Item :=
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
          "decode"
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
            (FnArg.typed
              []
              (Pat.tupleStruct
                none
                (Path.mk
                  false
                  [
                    (PathSegment.mk "Type" PathArguments.none),
                    (PathSegment.mk "TraitObject" PathArguments.none)])
                [Pat.rest])
              (Ty.path none (Path.mk false [(PathSegment.mk "Self" PathArguments.none)]))),
            (FnArg.typed
              []
              (Pat.ident false false "bytes" none)
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
                                                (PathSegment.mk "M" PathArguments.none),
                                                (PathSegment.mk "Provenance" PathArguments.none)])))]))])))]))])))]
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
              (Expr.macro
                (Macro.mk
                  (Path.mk false [(PathSegment.mk "panic" PathArguments.none)])
                  MacroDelimiter.paren
                  (MacroBody.exprs [(Expr.lit (Lit.str "decode of Type::TraitObject"))] false)))
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
          "encode"
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
            (FnArg.typed
              []
              (Pat.tupleStruct
                none
                (Path.mk
                  false
                  [
                    (PathSegment.mk "Type" PathArguments.none),
                    (PathSegment.mk "TraitObject" PathArguments.none)])
                [Pat.rest])
              (Ty.path none (Path.mk false [(PathSegment.mk "Self" PathArguments.none)]))),
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
                            (Ty.path none (Path.mk false [(PathSegment.mk "M" PathArguments.none)])))]))])))]
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
                                              (PathSegment.mk "M" PathArguments.none),
                                              (PathSegment.mk "Provenance" PathArguments.none)])))]))])))]))]))))
        (Block.mk
          [
            (Stmt.expr
              (Expr.macro
                (Macro.mk
                  (Path.mk false [(PathSegment.mk "panic" PathArguments.none)])
                  MacroDelimiter.paren
                  (MacroBody.exprs [(Expr.lit (Lit.str "encode of Type::TraitObject"))] false)))
              false)]))])

/-- `spec/lang/representation.md:482` -/
def fn_ensure_else_ub : Item :=
  (Item.fn
    [
      (Attr.mk
        true
        "doc"
        (AttrMeta.nameValue " Ensures the given boolean is true or else raises UB."))]
    Visibility.inherited
    (Signature.mk
      false
      false
      false
      none
      "ensure_else_ub"
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
                    (Path.mk false [(PathSegment.mk "throw_ub" PathArguments.none)])
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

/-- `spec/lang/representation.md:488` -/
def impl_Machine__check_ptr_metadata : Item :=
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
            (AttrMeta.nameValue " Defines well-formedness for pointer metadata for a given kind."))]
        Visibility.inherited
        false
        (Signature.mk
          false
          false
          false
          none
          "check_ptr_metadata"
          (Generics.mk [] [])
          [
            (FnArg.receiver [] true none false none),
            (FnArg.typed
              []
              (Pat.ident false false "meta" none)
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
                                                (PathSegment.mk "M" PathArguments.none),
                                                (PathSegment.mk "Provenance" PathArguments.none)])))]))])))]))]))),
            (FnArg.typed
              []
              (Pat.ident false false "kind" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "PointerMetaKind" PathArguments.none)])))]
          false
          (some (Ty.path none (Path.mk false [(PathSegment.mk "Result" PathArguments.none)]))))
        (Block.mk
          [
            (Stmt.expr
              (Expr.matchExpr
                (Expr.tuple
                  [
                    (Expr.path none (Path.mk false [(PathSegment.mk "meta" PathArguments.none)])),
                    (Expr.path none (Path.mk false [(PathSegment.mk "kind" PathArguments.none)]))])
                [
                  (Arm.mk
                    []
                    (Pat.tuple
                      [
                        (Pat.ident false false "None" none),
                        (Pat.path
                          none
                          (Path.mk
                            false
                            [
                              (PathSegment.mk "PointerMetaKind" PathArguments.none),
                              (PathSegment.mk "None" PathArguments.none)]))])
                    none
                    (Expr.block none (Block.mk []))),
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
                              [(Pat.ident false false "num" none)])]),
                        (Pat.path
                          none
                          (Path.mk
                            false
                            [
                              (PathSegment.mk "PointerMetaKind" PathArguments.none),
                              (PathSegment.mk "ElementCount" PathArguments.none)]))])
                    none
                    (Expr.tryExpr
                      (Expr.methodCall
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
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
                                  (PathSegment.mk "Int" PathArguments.none)]))
                            [
                              (Expr.path
                                none
                                (Path.mk false [(PathSegment.mk "num" PathArguments.none)]))]),
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
                                [])])]))),
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
                              [(Pat.ident false false "ptr" none)])]),
                        (Pat.tupleStruct
                          none
                          (Path.mk
                            false
                            [
                              (PathSegment.mk "PointerMetaKind" PathArguments.none),
                              (PathSegment.mk "VTablePointer" PathArguments.none)])
                          [(Pat.ident false false "trait_name" none)])])
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
                                "check_ptr"
                                none
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
                                        (Path.mk false [(PathSegment.mk "None" PathArguments.none)]))]),
                                  (Expr.call
                                    (Expr.path
                                      none
                                      (Path.mk
                                        false
                                        [
                                          (PathSegment.mk "PtrType" PathArguments.none),
                                          (PathSegment.mk "VTablePtr" PathArguments.none)]))
                                    [
                                      (Expr.path
                                        none
                                        (Path.mk
                                          false
                                          [(PathSegment.mk "trait_name" PathArguments.none)]))])]))
                            true)]))),
                  (Arm.mk
                    []
                    Pat.wild
                    none
                    (Expr.macro
                      (Macro.mk
                        (Path.mk false [(PathSegment.mk "throw_ub" PathArguments.none)])
                        MacroDelimiter.paren
                        (MacroBody.exprs
                          [(Expr.lit (Lit.str "Value::Ptr: invalid metadata"))]
                          false))))])
              true),
            (Stmt.expr
              (Expr.call
                (Expr.path none (Path.mk false [(PathSegment.mk "Ok" PathArguments.none)]))
                [(Expr.tuple [])])
              false)])),
      (ImplItem.fn
        [(Attr.mk true "doc" (AttrMeta.nameValue " Checks that a pointer is well-formed."))]
        Visibility.inherited
        false
        (Signature.mk
          false
          false
          false
          none
          "check_ptr"
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
              (Pat.ident false false "ptr_ty" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "PtrType" PathArguments.none)])))]
          false
          (some (Ty.path none (Path.mk false [(PathSegment.mk "Result" PathArguments.none)]))))
        (Block.mk
          [
            (Stmt.expr
              (Expr.tryExpr
                (Expr.call
                  (Expr.path
                    none
                    (Path.mk false [(PathSegment.mk "ensure_else_ub" PathArguments.none)]))
                  [
                    (Expr.methodCall
                      (Expr.field
                        (Expr.field
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "ptr" PathArguments.none)]))
                          (Member.named "thin_pointer"))
                        (Member.named "addr"))
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
                              (PathSegment.mk "PTR_SIZE" PathArguments.none)]))]),
                    (Expr.lit (Lit.str "Value::Ptr: pointer out-of-bounds"))]))
              true),
            (Stmt.expr
              (Expr.tryExpr
                (Expr.methodCall
                  (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                  "check_ptr_metadata"
                  none
                  [
                    (Expr.field
                      (Expr.path none (Path.mk false [(PathSegment.mk "ptr" PathArguments.none)]))
                      (Member.named "metadata")),
                    (Expr.methodCall
                      (Expr.path
                        none
                        (Path.mk false [(PathSegment.mk "ptr_ty" PathArguments.none)]))
                      "meta_kind"
                      none
                      [])]))
              true),
            (Stmt.expr
              (Expr.ite
                (Expr.letCond
                  (Pat.tupleStruct
                    none
                    (Path.mk false [(PathSegment.mk "Some" PathArguments.none)])
                    [(Pat.ident false false "pointee" none)])
                  (Expr.methodCall
                    (Expr.path none (Path.mk false [(PathSegment.mk "ptr_ty" PathArguments.none)]))
                    "safe_pointee"
                    none
                    []))
                (Block.mk
                  [
                    (Stmt.letStmt
                      []
                      (Pat.ident false false "size" none)
                      (some
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
                              (Member.named "metadata"))]))
                      none),
                    (Stmt.letStmt
                      []
                      (Pat.ident false false "align" none)
                      (some
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
                                (Path.mk false [(PathSegment.mk "pointee" PathArguments.none)]))
                              (Member.named "layout")),
                            (Expr.field
                              (Expr.path
                                none
                                (Path.mk false [(PathSegment.mk "ptr" PathArguments.none)]))
                              (Member.named "metadata"))]))
                      none),
                    (Stmt.expr
                      (Expr.tryExpr
                        (Expr.call
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "ensure_else_ub" PathArguments.none)]))
                          [
                            (Expr.methodCall
                              (Expr.methodCall
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "size" PathArguments.none)]))
                                "bytes"
                                none
                                [])
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
                                      (PathSegment.mk "PTR_SIZE" PathArguments.none)]))]),
                            (Expr.lit (Lit.str "Value::Ptr: total size exeeds isize::MAX"))]))
                      true),
                    (Stmt.expr
                      (Expr.tryExpr
                        (Expr.call
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "ensure_else_ub" PathArguments.none)]))
                          [
                            (Expr.binary
                              (Expr.field
                                (Expr.field
                                  (Expr.path
                                    none
                                    (Path.mk false [(PathSegment.mk "ptr" PathArguments.none)]))
                                  (Member.named "thin_pointer"))
                                (Member.named "addr"))
                              BinOp.ne
                              (Expr.lit (Lit.int 0 ""))),
                            (Expr.lit (Lit.str "Value::Ptr: null safe pointer"))]))
                      true),
                    (Stmt.expr
                      (Expr.tryExpr
                        (Expr.call
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "ensure_else_ub" PathArguments.none)]))
                          [
                            (Expr.methodCall
                              (Expr.path
                                none
                                (Path.mk false [(PathSegment.mk "align" PathArguments.none)]))
                              "is_aligned"
                              none
                              [
                                (Expr.field
                                  (Expr.field
                                    (Expr.path
                                      none
                                      (Path.mk false [(PathSegment.mk "ptr" PathArguments.none)]))
                                    (Member.named "thin_pointer"))
                                  (Member.named "addr"))]),
                            (Expr.lit (Lit.str "Value::Ptr: unaligned safe pointer"))]))
                      true),
                    (Stmt.expr
                      (Expr.tryExpr
                        (Expr.call
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "ensure_else_ub" PathArguments.none)]))
                          [
                            (Expr.field
                              (Expr.path
                                none
                                (Path.mk false [(PathSegment.mk "pointee" PathArguments.none)]))
                              (Member.named "inhabited")),
                            (Expr.lit (Lit.str "Value::Ptr: safe pointer to uninhabited type"))]))
                      true),
                    (Stmt.expr
                      (Expr.tryExpr
                        (Expr.call
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "ensure_else_ub" PathArguments.none)]))
                          [
                            (Expr.methodCall
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
                                  (Expr.path
                                    none
                                    (Path.mk false [(PathSegment.mk "size" PathArguments.none)]))])
                              "is_ok"
                              none
                              []),
                            (Expr.lit (Lit.str "Value::Ptr: non-dereferenceable safe pointer"))]))
                      true)])
                (some
                  (Expr.ite
                    (Expr.letCond
                      (Pat.tupleStruct
                        none
                        (Path.mk
                          false
                          [
                            (PathSegment.mk "PtrType" PathArguments.none),
                            (PathSegment.mk "VTablePtr" PathArguments.none)])
                        [(Pat.ident false false "trait_name" none)])
                      (Expr.path
                        none
                        (Path.mk false [(PathSegment.mk "ptr_ty" PathArguments.none)])))
                    (Block.mk
                      [
                        (Stmt.letStmt
                          []
                          (Pat.ident false false "vtable" none)
                          (some
                            (Expr.tryExpr
                              (Expr.methodCall
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                                "vtable_from_ptr"
                                none
                                [
                                  (Expr.field
                                    (Expr.path
                                      none
                                      (Path.mk false [(PathSegment.mk "ptr" PathArguments.none)]))
                                    (Member.named "thin_pointer"))])))
                          none),
                        (Stmt.expr
                          (Expr.tryExpr
                            (Expr.call
                              (Expr.path
                                none
                                (Path.mk
                                  false
                                  [(PathSegment.mk "ensure_else_ub" PathArguments.none)]))
                              [
                                (Expr.binary
                                  (Expr.field
                                    (Expr.path
                                      none
                                      (Path.mk false [(PathSegment.mk "vtable" PathArguments.none)]))
                                    (Member.named "trait_name"))
                                  BinOp.eq
                                  (Expr.path
                                    none
                                    (Path.mk
                                      false
                                      [(PathSegment.mk "trait_name" PathArguments.none)]))),
                                (Expr.lit (Lit.str "Value::Ptr: invalid vtable in metadata"))]))
                          true)])
                    none)))
              false),
            (Stmt.expr
              (Expr.call
                (Expr.path none (Path.mk false [(PathSegment.mk "Ok" PathArguments.none)]))
                [(Expr.tuple [])])
              false)])),
      (ImplItem.fn
        [
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue
              " We assume `ty` is itself well-formed and sized and the variant of `value` matches the `ty` variant.")),
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue " The specification must not call this function otherwise."))]
        Visibility.inherited
        false
        (Signature.mk
          false
          false
          false
          none
          "check_value"
          (Generics.mk [] [])
          [
            (FnArg.receiver [] true none false none),
            (FnArg.typed
              []
              (Pat.ident false false "value" none)
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
              (Expr.matchExpr
                (Expr.tuple
                  [
                    (Expr.path none (Path.mk false [(PathSegment.mk "value" PathArguments.none)])),
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
                              (PathSegment.mk "Value" PathArguments.none),
                              (PathSegment.mk "Int" PathArguments.none)])
                          [(Pat.ident false false "i" none)]),
                        (Pat.tupleStruct
                          none
                          (Path.mk
                            false
                            [
                              (PathSegment.mk "Type" PathArguments.none),
                              (PathSegment.mk "Int" PathArguments.none)])
                          [(Pat.ident false false "int_ty" none)])])
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
                                    [(PathSegment.mk "ensure_else_ub" PathArguments.none)]))
                                [
                                  (Expr.methodCall
                                    (Expr.path
                                      none
                                      (Path.mk false [(PathSegment.mk "int_ty" PathArguments.none)]))
                                    "can_represent"
                                    none
                                    [
                                      (Expr.path
                                        none
                                        (Path.mk false [(PathSegment.mk "i" PathArguments.none)]))]),
                                  (Expr.lit (Lit.str "Value::Int: invalid integer value"))]))
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
                              (PathSegment.mk "Value" PathArguments.none),
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
                    (Expr.block none (Block.mk []))),
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
                          [(Pat.ident false false "ptr_ty" none)])])
                    none
                    (Expr.tryExpr
                      (Expr.methodCall
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                        "check_ptr"
                        none
                        [
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "ptr" PathArguments.none)])),
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "ptr_ty" PathArguments.none)]))]))),
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
                              (Pat.ident false false "sized_fields" none)),
                            (FieldPat.mk
                              []
                              (Member.named "unsized_field")
                              true
                              (Pat.ident false false "unsized_field" none))]
                          true)])
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
                                  (Expr.methodCall
                                    (Expr.path
                                      none
                                      (Path.mk
                                        false
                                        [(PathSegment.mk "unsized_field" PathArguments.none)]))
                                    "is_none"
                                    none
                                    []),
                                  (Expr.lit
                                    (Lit.str
                                      "Value: unsized structs cannot be represented as values"))]
                                false))
                            true),
                          (Stmt.expr
                            (Expr.tryExpr
                              (Expr.call
                                (Expr.path
                                  none
                                  (Path.mk
                                    false
                                    [(PathSegment.mk "ensure_else_ub" PathArguments.none)]))
                                [
                                  (Expr.binary
                                    (Expr.methodCall
                                      (Expr.path
                                        none
                                        (Path.mk false [(PathSegment.mk "vals" PathArguments.none)]))
                                      "len"
                                      none
                                      [])
                                    BinOp.eq
                                    (Expr.methodCall
                                      (Expr.path
                                        none
                                        (Path.mk
                                          false
                                          [(PathSegment.mk "sized_fields" PathArguments.none)]))
                                      "len"
                                      none
                                      [])),
                                  (Expr.lit (Lit.str "Value::Tuple: invalid number of fields"))]))
                            true),
                          (Stmt.expr
                            (Expr.forLoop
                              none
                              (Pat.tuple
                                [
                                  (Pat.ident false false "val" none),
                                  (Pat.tuple [Pat.wild, (Pat.ident false false "ty" none)])])
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
                                        "check_value"
                                        none
                                        [
                                          (Expr.path
                                            none
                                            (Path.mk
                                              false
                                              [(PathSegment.mk "val" PathArguments.none)])),
                                          (Expr.path
                                            none
                                            (Path.mk
                                              false
                                              [(PathSegment.mk "ty" PathArguments.none)]))]))
                                    true)]))
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
                                    [(PathSegment.mk "ensure_else_ub" PathArguments.none)]))
                                [
                                  (Expr.binary
                                    (Expr.methodCall
                                      (Expr.path
                                        none
                                        (Path.mk false [(PathSegment.mk "vals" PathArguments.none)]))
                                      "len"
                                      none
                                      [])
                                    BinOp.eq
                                    (Expr.path
                                      none
                                      (Path.mk false [(PathSegment.mk "count" PathArguments.none)]))),
                                  (Expr.lit (Lit.str "Value::Tuple: invalid number of elements"))]))
                            true),
                          (Stmt.expr
                            (Expr.forLoop
                              none
                              (Pat.ident false false "val" none)
                              (Expr.path
                                none
                                (Path.mk false [(PathSegment.mk "vals" PathArguments.none)]))
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
                                        "check_value"
                                        none
                                        [
                                          (Expr.path
                                            none
                                            (Path.mk
                                              false
                                              [(PathSegment.mk "val" PathArguments.none)])),
                                          (Expr.path
                                            none
                                            (Path.mk
                                              false
                                              [(PathSegment.mk "elem" PathArguments.none)]))]))
                                    true)]))
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
                              (PathSegment.mk "Union" PathArguments.none)])
                          [(Pat.ident false false "chunk_data" none)]),
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
                              (Member.named "chunks")
                              true
                              (Pat.ident false false "chunks" none))]
                          true)])
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
                                    [(PathSegment.mk "ensure_else_ub" PathArguments.none)]))
                                [
                                  (Expr.binary
                                    (Expr.methodCall
                                      (Expr.path
                                        none
                                        (Path.mk
                                          false
                                          [(PathSegment.mk "chunk_data" PathArguments.none)]))
                                      "len"
                                      none
                                      [])
                                    BinOp.eq
                                    (Expr.methodCall
                                      (Expr.path
                                        none
                                        (Path.mk
                                          false
                                          [(PathSegment.mk "chunks" PathArguments.none)]))
                                      "len"
                                      none
                                      [])),
                                  (Expr.lit (Lit.str "Value::Union: invalid chunk size"))]))
                            true),
                          (Stmt.expr
                            (Expr.forLoop
                              none
                              (Pat.tuple
                                [
                                  (Pat.ident false false "data" none),
                                  (Pat.tuple [Pat.wild, (Pat.ident false false "size" none)])])
                              (Expr.methodCall
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "chunk_data" PathArguments.none)]))
                                "zip"
                                none
                                [
                                  (Expr.path
                                    none
                                    (Path.mk false [(PathSegment.mk "chunks" PathArguments.none)]))])
                              (Block.mk
                                [
                                  (Stmt.expr
                                    (Expr.tryExpr
                                      (Expr.call
                                        (Expr.path
                                          none
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "ensure_else_ub" PathArguments.none)]))
                                        [
                                          (Expr.binary
                                            (Expr.methodCall
                                              (Expr.path
                                                none
                                                (Path.mk
                                                  false
                                                  [(PathSegment.mk "data" PathArguments.none)]))
                                              "len"
                                              none
                                              [])
                                            BinOp.eq
                                            (Expr.methodCall
                                              (Expr.path
                                                none
                                                (Path.mk
                                                  false
                                                  [(PathSegment.mk "size" PathArguments.none)]))
                                              "bytes"
                                              none
                                              [])),
                                          (Expr.lit (Lit.str "Value::Union: invalid chunk data"))]))
                                    true)]))
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
                    (Expr.block
                      none
                      (Block.mk
                        [
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
                                  (Path.mk false [(PathSegment.mk "variants" PathArguments.none)]))
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
                                          [(PathSegment.mk "throw_ub" PathArguments.none)])
                                        MacroDelimiter.paren
                                        (MacroBody.exprs
                                          [
                                            (Expr.lit
                                              (Lit.str "Value::Variant: invalid discrimant"))]
                                          false))
                                      true)])))),
                          (Stmt.expr
                            (Expr.tryExpr
                              (Expr.methodCall
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                                "check_value"
                                none
                                [
                                  (Expr.path
                                    none
                                    (Path.mk false [(PathSegment.mk "data" PathArguments.none)])),
                                  (Expr.field
                                    (Expr.path
                                      none
                                      (Path.mk
                                        false
                                        [(PathSegment.mk "variant" PathArguments.none)]))
                                    (Member.named "ty"))]))
                            true)]))),
                  (Arm.mk
                    []
                    (Pat.tuple
                      [
                        Pat.wild,
                        (Pat.struct
                          none
                          (Path.mk
                            false
                            [
                              (PathSegment.mk "Type" PathArguments.none),
                              (PathSegment.mk "Slice" PathArguments.none)])
                          []
                          true)])
                    none
                    (Expr.macro
                      (Macro.mk
                        (Path.mk false [(PathSegment.mk "panic" PathArguments.none)])
                        MacroDelimiter.paren
                        (MacroBody.exprs
                          [(Expr.lit (Lit.str "Value: slices cannot be represented as values"))]
                          false)))),
                  (Arm.mk
                    []
                    (Pat.tuple
                      [
                        Pat.wild,
                        (Pat.struct
                          none
                          (Path.mk
                            false
                            [
                              (PathSegment.mk "Type" PathArguments.none),
                              (PathSegment.mk "TraitObject" PathArguments.none)])
                          []
                          true)])
                    none
                    (Expr.macro
                      (Macro.mk
                        (Path.mk false [(PathSegment.mk "panic" PathArguments.none)])
                        MacroDelimiter.paren
                        (MacroBody.exprs
                          [
                            (Expr.lit
                              (Lit.str "Value: trait objects cannot be represented as values"))]
                          false)))),
                  (Arm.mk
                    []
                    Pat.wild
                    none
                    (Expr.macro
                      (Macro.mk
                        (Path.mk false [(PathSegment.mk "panic" PathArguments.none)])
                        MacroDelimiter.paren
                        (MacroBody.exprs
                          [(Expr.lit (Lit.str "Value: value does not match type"))]
                          false))))])
              false),
            (Stmt.expr
              (Expr.call
                (Expr.path none (Path.mk false [(PathSegment.mk "ret" PathArguments.none)]))
                [(Expr.tuple [])])
              false)]))])

/-- `spec/lang/representation.md:599` -/
def impl_Machine__typed_store : Item :=
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
          "typed_store"
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
              (Pat.ident false false "align" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "Align" PathArguments.none)]))),
            (FnArg.typed
              []
              (Pat.ident false false "atomicity" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "Atomicity" PathArguments.none)])))]
          false
          (some (Ty.path none (Path.mk false [(PathSegment.mk "Result" PathArguments.none)]))))
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
                        "check_value"
                        none
                        [
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "val" PathArguments.none)])),
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "ty" PathArguments.none)]))])
                      "is_ok"
                      none
                      []),
                    (Expr.lit (Lit.str "trying to store {val:?} which is ill-formed for {:#?}")),
                    (Expr.path none (Path.mk false [(PathSegment.mk "ty" PathArguments.none)]))]
                  false))
              true),
            (Stmt.letStmt
              []
              (Pat.ident false false "bytes" none)
              (some
                (Expr.methodCall
                  (Expr.path none (Path.mk false [(PathSegment.mk "ty" PathArguments.none)]))
                  "encode"
                  (some
                    [
                      (GenericArgument.type
                        (Ty.path none (Path.mk false [(PathSegment.mk "M" PathArguments.none)])))])
                  [(Expr.path none (Path.mk false [(PathSegment.mk "val" PathArguments.none)]))]))
              none),
            (Stmt.expr
              (Expr.tryExpr
                (Expr.methodCall
                  (Expr.field
                    (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                    (Member.named "mem"))
                  "store"
                  none
                  [
                    (Expr.path none (Path.mk false [(PathSegment.mk "ptr" PathArguments.none)])),
                    (Expr.path none (Path.mk false [(PathSegment.mk "bytes" PathArguments.none)])),
                    (Expr.path none (Path.mk false [(PathSegment.mk "align" PathArguments.none)])),
                    (Expr.path
                      none
                      (Path.mk false [(PathSegment.mk "atomicity" PathArguments.none)]))]))
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
          "typed_load"
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
              (Pat.ident false false "ty" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "Type" PathArguments.none)]))),
            (FnArg.typed
              []
              (Pat.ident false false "align" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "Align" PathArguments.none)]))),
            (FnArg.typed
              []
              (Pat.ident false false "atomicity" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "Atomicity" PathArguments.none)])))]
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
                      (Expr.path none (Path.mk false [(PathSegment.mk "ptr" PathArguments.none)])),
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
                                    [
                                      (PathSegment.mk "M" PathArguments.none),
                                      (PathSegment.mk "T" PathArguments.none)])))])
                          [])
                        "expect_size"
                        none
                        [(Expr.lit (Lit.str "the callers ensure `ty` is sized"))]),
                      (Expr.path none (Path.mk false [(PathSegment.mk "align" PathArguments.none)])),
                      (Expr.path
                        none
                        (Path.mk false [(PathSegment.mk "atomicity" PathArguments.none)]))])))
              none),
            (Stmt.expr
              (Expr.call
                (Expr.path none (Path.mk false [(PathSegment.mk "ret" PathArguments.none)]))
                [
                  (Expr.matchExpr
                    (Expr.methodCall
                      (Expr.path none (Path.mk false [(PathSegment.mk "ty" PathArguments.none)]))
                      "decode"
                      (some
                        [
                          (GenericArgument.type
                            (Ty.path none (Path.mk false [(PathSegment.mk "M" PathArguments.none)])))])
                      [
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "bytes" PathArguments.none)]))])
                    [
                      (Arm.mk
                        []
                        (Pat.tupleStruct
                          none
                          (Path.mk false [(PathSegment.mk "Some" PathArguments.none)])
                          [(Pat.ident false false "val" none)])
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
                                    "check_value"
                                    none
                                    [
                                      (Expr.path
                                        none
                                        (Path.mk false [(PathSegment.mk "val" PathArguments.none)])),
                                      (Expr.path
                                        none
                                        (Path.mk false [(PathSegment.mk "ty" PathArguments.none)]))]))
                                true),
                              (Stmt.expr
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "val" PathArguments.none)]))
                                false)]))),
                      (Arm.mk
                        []
                        (Pat.ident false false "None" none)
                        none
                        (Expr.macro
                          (Macro.mk
                            (Path.mk false [(PathSegment.mk "throw_ub" PathArguments.none)])
                            MacroDelimiter.paren
                            (MacroBody.exprs
                              [
                                (Expr.lit
                                  (Lit.str
                                    "load at type {ty:?} but the data in memory violates the language invariant"))]
                              false))))])])
              false)]))])

/-- `spec/lang/representation.md:642` -/
def trait_DefinedRelation : Item :=
  (Item.trait
    [(Attr.mk true "allow" (AttrMeta.list [(MetaItem.mk "unused" AttrMeta.path)]))]
    Visibility.inherited
    false
    false
    "DefinedRelation"
    (Generics.mk [] [])
    []
    [
      (TraitItem.fn
        [
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue " returns whether `self` is less or as defined as `other`"))]
        (Signature.mk
          false
          false
          false
          none
          "le_defined"
          (Generics.mk [] [])
          [
            (FnArg.receiver [] false none false none),
            (FnArg.typed
              []
              (Pat.ident false false "other" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "Self" PathArguments.none)])))]
          false
          (some (Ty.path none (Path.mk false [(PathSegment.mk "bool" PathArguments.none)]))))
        none)])

/-- `spec/lang/representation.md:652` -/
def impl_AbstractByte_for_DefinedRelation__le_defined : Item :=
  (Item.impl
    []
    false
    false
    (Generics.mk [(GenericParam.type [] "Provenance" [] none)] [])
    false
    (some (Path.mk false [(PathSegment.mk "DefinedRelation" PathArguments.none)]))
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
                  (Ty.path none (Path.mk false [(PathSegment.mk "Provenance" PathArguments.none)])))]))]))
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
          "le_defined"
          (Generics.mk [] [])
          [
            (FnArg.receiver [] false none false none),
            (FnArg.typed
              []
              (Pat.ident false false "other" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "Self" PathArguments.none)])))]
          false
          (some (Ty.path none (Path.mk false [(PathSegment.mk "bool" PathArguments.none)]))))
        (Block.mk
          [
            (Stmt.item
              (Item.use [] Visibility.inherited false (UseTree.path "AbstractByte" UseTree.glob))),
            (Stmt.expr
              (Expr.matchExpr
                (Expr.tuple
                  [
                    (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)])),
                    (Expr.path none (Path.mk false [(PathSegment.mk "other" PathArguments.none)]))])
                [
                  (Arm.mk
                    []
                    (Pat.tuple [(Pat.ident false false "Uninit" none), Pat.wild])
                    none
                    (Expr.lit (Lit.bool true))),
                  (Arm.mk
                    []
                    (Pat.tuple
                      [
                        (Pat.tupleStruct
                          none
                          (Path.mk false [(PathSegment.mk "Init" PathArguments.none)])
                          [
                            (Pat.ident false false "data1" none),
                            (Pat.ident false false "None" none)]),
                        (Pat.tupleStruct
                          none
                          (Path.mk false [(PathSegment.mk "Init" PathArguments.none)])
                          [(Pat.ident false false "data2" none), Pat.wild])])
                    none
                    (Expr.binary
                      (Expr.path none (Path.mk false [(PathSegment.mk "data1" PathArguments.none)]))
                      BinOp.eq
                      (Expr.path none (Path.mk false [(PathSegment.mk "data2" PathArguments.none)])))),
                  (Arm.mk
                    []
                    (Pat.tuple
                      [
                        (Pat.tupleStruct
                          none
                          (Path.mk false [(PathSegment.mk "Init" PathArguments.none)])
                          [
                            (Pat.ident false false "data1" none),
                            (Pat.tupleStruct
                              none
                              (Path.mk false [(PathSegment.mk "Some" PathArguments.none)])
                              [(Pat.ident false false "provenance1" none)])]),
                        (Pat.tupleStruct
                          none
                          (Path.mk false [(PathSegment.mk "Init" PathArguments.none)])
                          [
                            (Pat.ident false false "data2" none),
                            (Pat.tupleStruct
                              none
                              (Path.mk false [(PathSegment.mk "Some" PathArguments.none)])
                              [(Pat.ident false false "provenance2" none)])])])
                    none
                    (Expr.binary
                      (Expr.binary
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "data1" PathArguments.none)]))
                        BinOp.eq
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "data2" PathArguments.none)])))
                      BinOp.and
                      (Expr.binary
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "provenance1" PathArguments.none)]))
                        BinOp.eq
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "provenance2" PathArguments.none)]))))),
                  (Arm.mk [] Pat.wild none (Expr.lit (Lit.bool false)))])
              false)]))])

/-- `spec/lang/representation.md:674` -/
def impl_ThinPointer_for_DefinedRelation__le_defined : Item :=
  (Item.impl
    []
    false
    false
    (Generics.mk [(GenericParam.type [] "Provenance" [] none)] [])
    false
    (some (Path.mk false [(PathSegment.mk "DefinedRelation" PathArguments.none)]))
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
        []
        Visibility.inherited
        false
        (Signature.mk
          false
          false
          false
          none
          "le_defined"
          (Generics.mk [] [])
          [
            (FnArg.receiver [] false none false none),
            (FnArg.typed
              []
              (Pat.ident false false "other" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "Self" PathArguments.none)])))]
          false
          (some (Ty.path none (Path.mk false [(PathSegment.mk "bool" PathArguments.none)]))))
        (Block.mk
          [
            (Stmt.expr
              (Expr.binary
                (Expr.binary
                  (Expr.field
                    (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                    (Member.named "addr"))
                  BinOp.eq
                  (Expr.field
                    (Expr.path none (Path.mk false [(PathSegment.mk "other" PathArguments.none)]))
                    (Member.named "addr")))
                BinOp.and
                (Expr.matchExpr
                  (Expr.tuple
                    [
                      (Expr.field
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                        (Member.named "provenance")),
                      (Expr.field
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "other" PathArguments.none)]))
                        (Member.named "provenance"))])
                  [
                    (Arm.mk
                      []
                      (Pat.tuple [(Pat.ident false false "None" none), Pat.wild])
                      none
                      (Expr.lit (Lit.bool true))),
                    (Arm.mk
                      []
                      (Pat.tuple
                        [
                          (Pat.tupleStruct
                            none
                            (Path.mk false [(PathSegment.mk "Some" PathArguments.none)])
                            [(Pat.ident false false "prov1" none)]),
                          (Pat.tupleStruct
                            none
                            (Path.mk false [(PathSegment.mk "Some" PathArguments.none)])
                            [(Pat.ident false false "prov2" none)])])
                      none
                      (Expr.binary
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "prov1" PathArguments.none)]))
                        BinOp.eq
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "prov2" PathArguments.none)])))),
                    (Arm.mk [] Pat.wild none (Expr.lit (Lit.bool false)))]))
              false)]))])

/-- `spec/lang/representation.md:685` -/
def impl_PointerMeta_for_DefinedRelation__le_defined : Item :=
  (Item.impl
    []
    false
    false
    (Generics.mk [(GenericParam.type [] "Provenance" [] none)] [])
    false
    (some (Path.mk false [(PathSegment.mk "DefinedRelation" PathArguments.none)]))
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
                  (Ty.path none (Path.mk false [(PathSegment.mk "Provenance" PathArguments.none)])))]))]))
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
          "le_defined"
          (Generics.mk [] [])
          [
            (FnArg.receiver [] false none false none),
            (FnArg.typed
              []
              (Pat.ident false false "other" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "Self" PathArguments.none)])))]
          false
          (some (Ty.path none (Path.mk false [(PathSegment.mk "bool" PathArguments.none)]))))
        (Block.mk
          [
            (Stmt.expr
              (Expr.matchExpr
                (Expr.tuple
                  [
                    (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)])),
                    (Expr.path none (Path.mk false [(PathSegment.mk "other" PathArguments.none)]))])
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
                              (PathSegment.mk "PointerMeta" PathArguments.none),
                              (PathSegment.mk "VTablePointer" PathArguments.none)])
                          [(Pat.ident false false "ptr1" none)]),
                        (Pat.tupleStruct
                          none
                          (Path.mk
                            false
                            [
                              (PathSegment.mk "PointerMeta" PathArguments.none),
                              (PathSegment.mk "VTablePointer" PathArguments.none)])
                          [(Pat.ident false false "ptr2" none)])])
                    none
                    (Expr.methodCall
                      (Expr.path none (Path.mk false [(PathSegment.mk "ptr1" PathArguments.none)]))
                      "le_defined"
                      none
                      [
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "ptr2" PathArguments.none)]))])),
                  (Arm.mk
                    []
                    Pat.wild
                    none
                    (Expr.binary
                      (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                      BinOp.eq
                      (Expr.path none (Path.mk false [(PathSegment.mk "other" PathArguments.none)]))))])
              false)]))])

/-- `spec/lang/representation.md:694` -/
def impl_Pointer_for_DefinedRelation__le_defined : Item :=
  (Item.impl
    []
    false
    false
    (Generics.mk [(GenericParam.type [] "Provenance" [] none)] [])
    false
    (some (Path.mk false [(PathSegment.mk "DefinedRelation" PathArguments.none)]))
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
                  (Ty.path none (Path.mk false [(PathSegment.mk "Provenance" PathArguments.none)])))]))]))
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
          "le_defined"
          (Generics.mk [] [])
          [
            (FnArg.receiver [] false none false none),
            (FnArg.typed
              []
              (Pat.ident false false "other" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "Self" PathArguments.none)])))]
          false
          (some (Ty.path none (Path.mk false [(PathSegment.mk "bool" PathArguments.none)]))))
        (Block.mk
          [
            (Stmt.expr
              (Expr.binary
                (Expr.methodCall
                  (Expr.field
                    (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                    (Member.named "thin_pointer"))
                  "le_defined"
                  none
                  [
                    (Expr.field
                      (Expr.path none (Path.mk false [(PathSegment.mk "other" PathArguments.none)]))
                      (Member.named "thin_pointer"))])
                BinOp.and
                (Expr.methodCall
                  (Expr.field
                    (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                    (Member.named "metadata"))
                  "le_defined"
                  none
                  [
                    (Expr.field
                      (Expr.path none (Path.mk false [(PathSegment.mk "other" PathArguments.none)]))
                      (Member.named "metadata"))]))
              false)]))])

/-- `spec/lang/representation.md:705` -/
def impl_List_for_DefinedRelation__le_defined : Item :=
  (Item.impl
    []
    false
    false
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
              (Path.mk false [(PathSegment.mk "DefinedRelation" PathArguments.none)]))]
          none)]
      [])
    false
    (some (Path.mk false [(PathSegment.mk "DefinedRelation" PathArguments.none)]))
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
                  (Ty.path none (Path.mk false [(PathSegment.mk "T" PathArguments.none)])))]))]))
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
          "le_defined"
          (Generics.mk [] [])
          [
            (FnArg.receiver [] false none false none),
            (FnArg.typed
              []
              (Pat.ident false false "other" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "Self" PathArguments.none)])))]
          false
          (some (Ty.path none (Path.mk false [(PathSegment.mk "bool" PathArguments.none)]))))
        (Block.mk
          [
            (Stmt.expr
              (Expr.binary
                (Expr.binary
                  (Expr.methodCall
                    (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                    "len"
                    none
                    [])
                  BinOp.eq
                  (Expr.methodCall
                    (Expr.path none (Path.mk false [(PathSegment.mk "other" PathArguments.none)]))
                    "len"
                    none
                    []))
                BinOp.and
                (Expr.methodCall
                  (Expr.methodCall
                    (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                    "zip"
                    none
                    [(Expr.path none (Path.mk false [(PathSegment.mk "other" PathArguments.none)]))])
                  "all"
                  none
                  [
                    (Expr.closure
                      false
                      [
                        (Pat.tuple
                          [(Pat.ident false false "l" none), (Pat.ident false false "r" none)])]
                      none
                      (Expr.methodCall
                        (Expr.path none (Path.mk false [(PathSegment.mk "l" PathArguments.none)]))
                        "le_defined"
                        none
                        [(Expr.path none (Path.mk false [(PathSegment.mk "r" PathArguments.none)]))]))]))
              false)]))])

/-- `spec/lang/representation.md:715` -/
def impl_Value_for_DefinedRelation__le_defined : Item :=
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
    (some (Path.mk false [(PathSegment.mk "DefinedRelation" PathArguments.none)]))
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
          "le_defined"
          (Generics.mk [] [])
          [
            (FnArg.receiver [] false none false none),
            (FnArg.typed
              []
              (Pat.ident false false "other" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "Self" PathArguments.none)])))]
          false
          (some (Ty.path none (Path.mk false [(PathSegment.mk "bool" PathArguments.none)]))))
        (Block.mk
          [
            (Stmt.item (Item.use [] Visibility.inherited false (UseTree.path "Value" UseTree.glob))),
            (Stmt.expr
              (Expr.matchExpr
                (Expr.tuple
                  [
                    (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)])),
                    (Expr.path none (Path.mk false [(PathSegment.mk "other" PathArguments.none)]))])
                [
                  (Arm.mk
                    []
                    (Pat.tuple
                      [
                        (Pat.tupleStruct
                          none
                          (Path.mk false [(PathSegment.mk "Int" PathArguments.none)])
                          [(Pat.ident false false "i1" none)]),
                        (Pat.tupleStruct
                          none
                          (Path.mk false [(PathSegment.mk "Int" PathArguments.none)])
                          [(Pat.ident false false "i2" none)])])
                    none
                    (Expr.binary
                      (Expr.path none (Path.mk false [(PathSegment.mk "i1" PathArguments.none)]))
                      BinOp.eq
                      (Expr.path none (Path.mk false [(PathSegment.mk "i2" PathArguments.none)])))),
                  (Arm.mk
                    []
                    (Pat.tuple
                      [
                        (Pat.tupleStruct
                          none
                          (Path.mk false [(PathSegment.mk "Bool" PathArguments.none)])
                          [(Pat.ident false false "b1" none)]),
                        (Pat.tupleStruct
                          none
                          (Path.mk false [(PathSegment.mk "Bool" PathArguments.none)])
                          [(Pat.ident false false "b2" none)])])
                    none
                    (Expr.binary
                      (Expr.path none (Path.mk false [(PathSegment.mk "b1" PathArguments.none)]))
                      BinOp.eq
                      (Expr.path none (Path.mk false [(PathSegment.mk "b2" PathArguments.none)])))),
                  (Arm.mk
                    []
                    (Pat.tuple
                      [
                        (Pat.tupleStruct
                          none
                          (Path.mk false [(PathSegment.mk "Ptr" PathArguments.none)])
                          [(Pat.ident false false "p1" none)]),
                        (Pat.tupleStruct
                          none
                          (Path.mk false [(PathSegment.mk "Ptr" PathArguments.none)])
                          [(Pat.ident false false "p2" none)])])
                    none
                    (Expr.methodCall
                      (Expr.path none (Path.mk false [(PathSegment.mk "p1" PathArguments.none)]))
                      "le_defined"
                      none
                      [(Expr.path none (Path.mk false [(PathSegment.mk "p2" PathArguments.none)]))])),
                  (Arm.mk
                    []
                    (Pat.tuple
                      [
                        (Pat.tupleStruct
                          none
                          (Path.mk false [(PathSegment.mk "Tuple" PathArguments.none)])
                          [(Pat.ident false false "vals1" none)]),
                        (Pat.tupleStruct
                          none
                          (Path.mk false [(PathSegment.mk "Tuple" PathArguments.none)])
                          [(Pat.ident false false "vals2" none)])])
                    none
                    (Expr.methodCall
                      (Expr.path none (Path.mk false [(PathSegment.mk "vals1" PathArguments.none)]))
                      "le_defined"
                      none
                      [
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "vals2" PathArguments.none)]))])),
                  (Arm.mk
                    []
                    (Pat.tuple
                      [
                        (Pat.struct
                          none
                          (Path.mk false [(PathSegment.mk "Variant" PathArguments.none)])
                          [
                            (FieldPat.mk
                              []
                              (Member.named "discriminant")
                              false
                              (Pat.ident false false "discriminant1" none)),
                            (FieldPat.mk
                              []
                              (Member.named "data")
                              false
                              (Pat.ident false false "data1" none))]
                          false),
                        (Pat.struct
                          none
                          (Path.mk false [(PathSegment.mk "Variant" PathArguments.none)])
                          [
                            (FieldPat.mk
                              []
                              (Member.named "discriminant")
                              false
                              (Pat.ident false false "discriminant2" none)),
                            (FieldPat.mk
                              []
                              (Member.named "data")
                              false
                              (Pat.ident false false "data2" none))]
                          false)])
                    none
                    (Expr.binary
                      (Expr.binary
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "discriminant1" PathArguments.none)]))
                        BinOp.eq
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "discriminant2" PathArguments.none)])))
                      BinOp.and
                      (Expr.methodCall
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "data1" PathArguments.none)]))
                        "le_defined"
                        none
                        [
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "data2" PathArguments.none)]))]))),
                  (Arm.mk
                    []
                    (Pat.tuple
                      [
                        (Pat.tupleStruct
                          none
                          (Path.mk false [(PathSegment.mk "Union" PathArguments.none)])
                          [(Pat.ident false false "chunks1" none)]),
                        (Pat.tupleStruct
                          none
                          (Path.mk false [(PathSegment.mk "Union" PathArguments.none)])
                          [(Pat.ident false false "chunks2" none)])])
                    none
                    (Expr.methodCall
                      (Expr.path
                        none
                        (Path.mk false [(PathSegment.mk "chunks1" PathArguments.none)]))
                      "le_defined"
                      none
                      [
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "chunks2" PathArguments.none)]))])),
                  (Arm.mk [] Pat.wild none (Expr.lit (Lit.bool false)))])
              false)]))])

/-- `spec/lang/representation.md:738` -/
def impl_Option_for_DefinedRelation__le_defined : Item :=
  (Item.impl
    []
    false
    false
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
              (Path.mk false [(PathSegment.mk "DefinedRelation" PathArguments.none)]))]
          none)]
      [])
    false
    (some (Path.mk false [(PathSegment.mk "DefinedRelation" PathArguments.none)]))
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
                  (Ty.path none (Path.mk false [(PathSegment.mk "T" PathArguments.none)])))]))]))
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
          "le_defined"
          (Generics.mk [] [])
          [
            (FnArg.receiver [] false none false none),
            (FnArg.typed
              []
              (Pat.ident false false "other" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "Self" PathArguments.none)])))]
          false
          (some (Ty.path none (Path.mk false [(PathSegment.mk "bool" PathArguments.none)]))))
        (Block.mk
          [
            (Stmt.expr
              (Expr.matchExpr
                (Expr.tuple
                  [
                    (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)])),
                    (Expr.path none (Path.mk false [(PathSegment.mk "other" PathArguments.none)]))])
                [
                  (Arm.mk
                    []
                    (Pat.tuple [(Pat.ident false false "None" none), Pat.wild])
                    none
                    (Expr.lit (Lit.bool true))),
                  (Arm.mk
                    []
                    (Pat.tuple
                      [
                        (Pat.tupleStruct
                          none
                          (Path.mk false [(PathSegment.mk "Some" PathArguments.none)])
                          [(Pat.ident false false "l" none)]),
                        (Pat.tupleStruct
                          none
                          (Path.mk false [(PathSegment.mk "Some" PathArguments.none)])
                          [(Pat.ident false false "r" none)])])
                    none
                    (Expr.methodCall
                      (Expr.path none (Path.mk false [(PathSegment.mk "l" PathArguments.none)]))
                      "le_defined"
                      none
                      [(Expr.path none (Path.mk false [(PathSegment.mk "r" PathArguments.none)]))])),
                  (Arm.mk [] Pat.wild none (Expr.lit (Lit.bool false)))])
              false)]))])

/-- `spec/lang/representation.md:788` -/
def impl_Machine__transmute : Item :=
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
        [(Attr.mk true "doc" (AttrMeta.nameValue " Transmutes `val` from `type1` to `type2`."))]
        Visibility.inherited
        false
        (Signature.mk
          false
          false
          false
          none
          "transmute"
          (Generics.mk [] [])
          [
            (FnArg.receiver [] true none false none),
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
              (Pat.ident false false "type1" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "Type" PathArguments.none)]))),
            (FnArg.typed
              []
              (Pat.ident false false "type2" none)
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
            (Stmt.macro
              []
              (Macro.mk
                (Path.mk false [(PathSegment.mk "assert" PathArguments.none)])
                MacroDelimiter.paren
                (MacroBody.exprs
                  [
                    (Expr.binary
                      (Expr.methodCall
                        (Expr.methodCall
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "type1" PathArguments.none)]))
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
                        [(Expr.lit (Lit.str "WF ensures sized operands"))])
                      BinOp.eq
                      (Expr.methodCall
                        (Expr.methodCall
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "type2" PathArguments.none)]))
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
                        [(Expr.lit (Lit.str "WF ensures sized operands"))]))]
                  false))
              true),
            (Stmt.letStmt
              []
              (Pat.ident false false "bytes" none)
              (some
                (Expr.methodCall
                  (Expr.path none (Path.mk false [(PathSegment.mk "type1" PathArguments.none)]))
                  "encode"
                  (some
                    [
                      (GenericArgument.type
                        (Ty.path none (Path.mk false [(PathSegment.mk "M" PathArguments.none)])))])
                  [(Expr.path none (Path.mk false [(PathSegment.mk "val" PathArguments.none)]))]))
              none),
            (Stmt.expr
              (Expr.ite
                (Expr.letCond
                  (Pat.tupleStruct
                    none
                    (Path.mk false [(PathSegment.mk "Some" PathArguments.none)])
                    [(Pat.ident false false "raw_value" none)])
                  (Expr.methodCall
                    (Expr.path none (Path.mk false [(PathSegment.mk "type2" PathArguments.none)]))
                    "decode"
                    (some
                      [
                        (GenericArgument.type
                          (Ty.path none (Path.mk false [(PathSegment.mk "M" PathArguments.none)])))])
                    [(Expr.path none (Path.mk false [(PathSegment.mk "bytes" PathArguments.none)]))]))
                (Block.mk
                  [
                    (Stmt.expr
                      (Expr.tryExpr
                        (Expr.methodCall
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                          "check_value"
                          none
                          [
                            (Expr.path
                              none
                              (Path.mk false [(PathSegment.mk "raw_value" PathArguments.none)])),
                            (Expr.path
                              none
                              (Path.mk false [(PathSegment.mk "type2" PathArguments.none)]))]))
                      true),
                    (Stmt.expr
                      (Expr.call
                        (Expr.path none (Path.mk false [(PathSegment.mk "ret" PathArguments.none)]))
                        [
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "raw_value" PathArguments.none)]))])
                      false)])
                (some
                  (Expr.block
                    none
                    (Block.mk
                      [
                        (Stmt.expr
                          (Expr.macro
                            (Macro.mk
                              (Path.mk false [(PathSegment.mk "throw_ub" PathArguments.none)])
                              MacroDelimiter.paren
                              (MacroBody.exprs
                                [(Expr.lit (Lit.str "transmuted value is not valid at new type"))]
                                false)))
                          false)]))))
              false)]))])

/-- All items of `spec/lang/representation.md`, in source order, with provenance. -/
def items : List SourceItem :=
  [
    (SourceItem.mk
      "impl_Type__decode_0"
      33
      "3834924dca33e1a75f0c7bb3b7957025104817e26a1e927fb05860d06f0b1b3e"
      impl_Type__decode_0),
    (SourceItem.mk
      "impl_Type__decode_1"
      53
      "8b035d58220d31689dc801bfa0990355edcb221c72f0609d8747c0d855c8ab5c"
      impl_Type__decode_1),
    (SourceItem.mk
      "impl_Type__decode_2"
      74
      "fd8f4073f6460ce36c081b9f88e4fb5a759dadf0783dc3f6603023ae5c085fdf"
      impl_Type__decode_2),
    (SourceItem.mk
      "fn_decode_ptr"
      112
      "02d93380e1e6c419f667b40d8781af304b968cc63f06bf5c895999bf0fdca170"
      fn_decode_ptr),
    (SourceItem.mk
      "fn_encode_ptr"
      135
      "015846ad4f5b1cd9e67cc094b56a16452a139a43044dfeee1a081737130fab88"
      fn_encode_ptr),
    (SourceItem.mk
      "impl_PointerMetaKind__ty"
      144
      "0ab3da4c096cda23747507e6bbabb0ffc41b95878381acfbce4cbb5af3c3603f"
      impl_PointerMetaKind__ty),
    (SourceItem.mk
      "impl_PtrType__as_wide_pair"
      155
      "77a195f9e1cfb16bb9683248d3149303a84617b689ec8b286dcdfd8e1465ec3f"
      impl_PtrType__as_wide_pair),
    (SourceItem.mk
      "impl_PointerMetaKind__decode_value"
      178
      "d6425588b6cda92e5ddf03e3dca490aa03112397e5887b18b4ef96a5f57a091f"
      impl_PointerMetaKind__decode_value),
    (SourceItem.mk
      "impl_Type__decode_3"
      203
      "978d5e044d337916fc976f0ce6373904d967f704dc6c788069531db44fe51e5d"
      impl_Type__decode_3),
    (SourceItem.mk
      "impl_Type__decode_4"
      248
      "acb13b3c90aff1f53f590beab7f15600996d58482f87940eb81aa18a3b0535ad"
      impl_Type__decode_4),
    (SourceItem.mk
      "impl_Type__decode_5"
      286
      "4e306b30bc094bc37e7de484db82e9a660b4aac85132a473ad8ecd859c7c2f09"
      impl_Type__decode_5),
    (SourceItem.mk
      "impl_Type__decode_6"
      322
      "ffe2b0b36a9c007798cac71716a85d3d1eadae0afd24f8cab5b4c2931bb66911"
      impl_Type__decode_6),
    (SourceItem.mk
      "fn_decode_discriminant"
      353
      "5487eb6ae19c8c24537b029da2db0b1aa497326cbaa69fe2a197ebb6b07509ff"
      fn_decode_discriminant),
    (SourceItem.mk
      "fn_encode_discriminant"
      377
      "be434e2a3af0dcf0c006a01d6e376fa8b3451dcc3e496cbe3739e9af85c3cea9"
      fn_encode_discriminant),
    (SourceItem.mk
      "impl_Type__decode_7"
      393
      "c02900dc855aadab1e82cf3752a93ea12061fb42ca0878f9c9e96fe8b191b6fd"
      impl_Type__decode_7),
    (SourceItem.mk
      "impl_Type__decode_8"
      441
      "9fac7e2c667bef1c4998cc768fc1a949c45f6c456e37a174e5af92a83c8950b0"
      impl_Type__decode_8),
    (SourceItem.mk
      "impl_Type__decode_9"
      450
      "2fd60590d2d3862b33ed07a1759f3fe451dd790001b1e4280995a3c0ad13df13"
      impl_Type__decode_9),
    (SourceItem.mk
      "fn_ensure_else_ub"
      482
      "79713d3cd3ee2c8ca1740429a2ba850ee1efdbdfceb74d9c6f96bff5d0805793"
      fn_ensure_else_ub),
    (SourceItem.mk
      "impl_Machine__check_ptr_metadata"
      488
      "95e22453eb77af02c809ebd8bc9ee541641a186dff2e49494c720161013e4a4a"
      impl_Machine__check_ptr_metadata),
    (SourceItem.mk
      "impl_Machine__typed_store"
      599
      "1dcf6053cc92c46aaf645bf35f514bd6c20722d75a485b3defb8c4496449f21e"
      impl_Machine__typed_store),
    (SourceItem.mk
      "trait_DefinedRelation"
      642
      "7affca28e2a464f25678aaeb613c727b4521404d85510e6de2b0e2c4099465a4"
      trait_DefinedRelation),
    (SourceItem.mk
      "impl_AbstractByte_for_DefinedRelation__le_defined"
      652
      "e07a9d24bd5a6ce6f284d2dbac2622d89e2bcee5ad1d46951c11b398ddfbb7e2"
      impl_AbstractByte_for_DefinedRelation__le_defined),
    (SourceItem.mk
      "impl_ThinPointer_for_DefinedRelation__le_defined"
      674
      "7a69d1b49f5df40e5e8f2f573bcb9c2a926536bd4a44992d3fad1b6478c27af3"
      impl_ThinPointer_for_DefinedRelation__le_defined),
    (SourceItem.mk
      "impl_PointerMeta_for_DefinedRelation__le_defined"
      685
      "cb523df3b870fa0f6047905d2286e8e73e38f4fa056b12833f651c8bbab712ce"
      impl_PointerMeta_for_DefinedRelation__le_defined),
    (SourceItem.mk
      "impl_Pointer_for_DefinedRelation__le_defined"
      694
      "83d0e6b808488f571c3b4523ab2ba1cfbd58f33b41efeb7599a0b05684226bfe"
      impl_Pointer_for_DefinedRelation__le_defined),
    (SourceItem.mk
      "impl_List_for_DefinedRelation__le_defined"
      705
      "7b964231c147e0871731296ebfb2cadc62ac0961bad6ab1ce90a31369c0f49d5"
      impl_List_for_DefinedRelation__le_defined),
    (SourceItem.mk
      "impl_Value_for_DefinedRelation__le_defined"
      715
      "8e96d506a0cfc46d3d64facf4a049f161a6cf668954cc14156e73c8ce9b90d2a"
      impl_Value_for_DefinedRelation__le_defined),
    (SourceItem.mk
      "impl_Option_for_DefinedRelation__le_defined"
      738
      "cf2f2094ab5a0c4be2c12a76320bc979c11d0e84958fd109cbdc45f04445b217"
      impl_Option_for_DefinedRelation__le_defined),
    (SourceItem.mk
      "impl_Machine__transmute"
      788
      "c38b1df79341aa42f078869af8ee4b2e17946dd8fc82b2a17ef95bfdc7801306"
      impl_Machine__transmute)]

end MiniRustSpec.Gen.Items.Lang.Representation
