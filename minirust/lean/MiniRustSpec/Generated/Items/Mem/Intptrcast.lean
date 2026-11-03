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
`spec/mem/intptrcast.md` (commit `d821c6e3`), one Lean definition per item, in source order.
-/

import MiniRustSpec.Meta.Syntax

set_option maxRecDepth 100000

namespace MiniRustSpec.Gen.Items.Mem.Intptrcast

open MiniRustSpec.Syntax

/-- Path of the upstream file these items were extracted from. -/
def sourceFile : String := "spec/mem/intptrcast.md"

/-- SHA-256 of the upstream file. -/
def sourceSha256 : String := "ddb67b4ef74e05568fced9f1460730b595b4584d73d48c93fd326ff5dd7378b6"

/-- `spec/mem/intptrcast.md:13` -/
def struct_IntPtrCast : Item :=
  (Item.struct
    []
    Visibility.pub
    "IntPtrCast"
    (Generics.mk [(GenericParam.type [] "Provenance" [] none)] [])
    (Fields.named
      [
        (Field.mk
          [(Attr.mk true "doc" (AttrMeta.nameValue " The set of exposed provenance."))]
          Visibility.inherited
          (some "exposed")
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
                          (Path.mk false [(PathSegment.mk "Provenance" PathArguments.none)])))]))])))]))

/-- `spec/mem/intptrcast.md:18` -/
def impl_IntPtrCast__new : Item :=
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
            "IntPtrCast"
            (PathArguments.angleBracketed
              false
              [
                (GenericArgument.type
                  (Ty.path none (Path.mk false [(PathSegment.mk "Provenance" PathArguments.none)])))]))]))
    [
      (ImplItem.fn
        []
        Visibility.pub
        false
        (Signature.mk
          false
          false
          false
          none
          "new"
          (Generics.mk [] [])
          []
          false
          (some (Ty.path none (Path.mk false [(PathSegment.mk "Self" PathArguments.none)]))))
        (Block.mk
          [
            (Stmt.expr
              (Expr.struct
                none
                (Path.mk false [(PathSegment.mk "Self" PathArguments.none)])
                [
                  (FieldValue.mk
                    []
                    (Member.named "exposed")
                    false
                    (Expr.call
                      (Expr.path
                        none
                        (Path.mk
                          false
                          [
                            (PathSegment.mk "Set" PathArguments.none),
                            (PathSegment.mk "new" PathArguments.none)]))
                      []))]
                false
                none)
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
          "expose"
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
                              (Path.mk false [(PathSegment.mk "Provenance" PathArguments.none)])))]))])))]
          false
          none)
        (Block.mk
          [
            (Stmt.expr
              (Expr.ite
                (Expr.letCond
                  (Pat.tupleStruct
                    none
                    (Path.mk false [(PathSegment.mk "Some" PathArguments.none)])
                    [(Pat.ident false false "provenance" none)])
                  (Expr.field
                    (Expr.path none (Path.mk false [(PathSegment.mk "ptr" PathArguments.none)]))
                    (Member.named "provenance")))
                (Block.mk
                  [
                    (Stmt.expr
                      (Expr.methodCall
                        (Expr.field
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                          (Member.named "exposed"))
                        "insert"
                        none
                        [
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "provenance" PathArguments.none)]))])
                      true)])
                none)
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
          "int2ptr"
          (Generics.mk [] [])
          [
            (FnArg.receiver [] true none false none),
            (FnArg.typed
              []
              (Pat.ident false false "addr" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "Int" PathArguments.none)])))]
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
                                  "ThinPointer"
                                  (PathArguments.angleBracketed
                                    false
                                    [
                                      (GenericArgument.type
                                        (Ty.path
                                          none
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "Provenance" PathArguments.none)])))]))])))]))]))))
        (Block.mk
          [
            (Stmt.letStmt
              []
              (Pat.ident false false "provenance" none)
              (some
                (Expr.tryExpr
                  (Expr.call
                    (Expr.path none (Path.mk false [(PathSegment.mk "predict" PathArguments.none)]))
                    [
                      (Expr.closure
                        false
                        [
                          (Pat.typed
                            (Pat.ident false false "prov" none)
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
                                              [(PathSegment.mk "Provenance" PathArguments.none)])))]))])))]
                        none
                        (Expr.block
                          none
                          (Block.mk
                            [
                              (Stmt.expr
                                (Expr.methodCall
                                  (Expr.path
                                    none
                                    (Path.mk false [(PathSegment.mk "prov" PathArguments.none)]))
                                  "map_or"
                                  none
                                  [
                                    (Expr.lit (Lit.bool true)),
                                    (Expr.closure
                                      false
                                      [(Pat.ident false false "p" none)]
                                      none
                                      (Expr.methodCall
                                        (Expr.field
                                          (Expr.path
                                            none
                                            (Path.mk
                                              false
                                              [(PathSegment.mk "self" PathArguments.none)]))
                                          (Member.named "exposed"))
                                        "contains"
                                        none
                                        [
                                          (Expr.path
                                            none
                                            (Path.mk
                                              false
                                              [(PathSegment.mk "p" PathArguments.none)]))]))])
                                false)])))])))
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
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "addr" PathArguments.none)]))),
                      (FieldValue.mk
                        []
                        (Member.named "provenance")
                        true
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "provenance" PathArguments.none)])))]
                    false
                    none)])
              false)]))])

/-- All items of `spec/mem/intptrcast.md`, in source order, with provenance. -/
def items : List SourceItem :=
  [
    (SourceItem.mk
      "struct_IntPtrCast"
      13
      "0aebf46f9e85567fc161ca4ea2de732ba6510664de9a29647fd18950cf22b016"
      struct_IntPtrCast),
    (SourceItem.mk
      "impl_IntPtrCast__new"
      18
      "9dfa80c3e774f1c7646216844d11f9d846d069e35cde3eaf1b41e351fb166776"
      impl_IntPtrCast__new)]

end MiniRustSpec.Gen.Items.Mem.Intptrcast
