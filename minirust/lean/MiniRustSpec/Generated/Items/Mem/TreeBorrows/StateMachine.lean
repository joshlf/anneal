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
`spec/mem/tree_borrows/state_machine.md` (commit `d821c6e3`), one Lean definition per item, in source order.
-/

import MiniRustSpec.Meta.Syntax

set_option maxRecDepth 100000

namespace MiniRustSpec.Gen.Items.Mem.TreeBorrows.StateMachine

open MiniRustSpec.Syntax

/-- Path of the upstream file these items were extracted from. -/
def sourceFile : String := "spec/mem/tree_borrows/state_machine.md"

/-- SHA-256 of the upstream file. -/
def sourceSha256 : String := "548918ad62b98c862b8a5ab9b58483bf6fd865c03d133631273a0b82782e120b"

/-- `spec/mem/tree_borrows/state_machine.md:11` -/
def enum_Permission : Item :=
  (Item.enum
    []
    Visibility.inherited
    "Permission"
    (Generics.mk [] [])
    [
      (Variant.mk
        []
        "Unprot"
        (Fields.unnamed
          [
            (Field.mk
              []
              Visibility.inherited
              none
              (Ty.path
                none
                (Path.mk false [(PathSegment.mk "PermissionUnprot" PathArguments.none)])))])
        none),
      (Variant.mk
        []
        "Prot"
        (Fields.unnamed
          [
            (Field.mk
              []
              Visibility.inherited
              none
              (Ty.path none (Path.mk false [(PathSegment.mk "PermissionProt" PathArguments.none)])))])
        none)])

/-- `spec/mem/tree_borrows/state_machine.md:16` -/
def impl_Permission__transition : Item :=
  (Item.impl
    []
    false
    false
    (Generics.mk [] [])
    false
    none
    (Ty.path none (Path.mk false [(PathSegment.mk "Permission" PathArguments.none)]))
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
          "transition"
          (Generics.mk [] [])
          [
            (FnArg.receiver [] true none true none),
            (FnArg.typed
              []
              (Pat.ident false false "access_kind" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "AccessKind" PathArguments.none)]))),
            (FnArg.typed
              []
              (Pat.ident false false "node_relation" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "NodeRelation" PathArguments.none)])))]
          false
          (some (Ty.path none (Path.mk false [(PathSegment.mk "Result" PathArguments.none)]))))
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
                          (PathSegment.mk "Permission" PathArguments.none),
                          (PathSegment.mk "Unprot" PathArguments.none)])
                      [(Pat.ident false false "p" none)])
                    none
                    (Expr.block
                      none
                      (Block.mk
                        [
                          (Stmt.expr
                            (Expr.assign
                              (Expr.unary
                                UnOp.deref
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "p" PathArguments.none)])))
                              (Expr.tryExpr
                                (Expr.methodCall
                                  (Expr.path
                                    none
                                    (Path.mk false [(PathSegment.mk "p" PathArguments.none)]))
                                  "transition"
                                  none
                                  [
                                    (Expr.path
                                      none
                                      (Path.mk
                                        false
                                        [(PathSegment.mk "access_kind" PathArguments.none)])),
                                    (Expr.path
                                      none
                                      (Path.mk
                                        false
                                        [(PathSegment.mk "node_relation" PathArguments.none)]))])))
                            false)]))),
                  (Arm.mk
                    []
                    (Pat.tupleStruct
                      none
                      (Path.mk
                        false
                        [
                          (PathSegment.mk "Permission" PathArguments.none),
                          (PathSegment.mk "Prot" PathArguments.none)])
                      [(Pat.ident false false "p" none)])
                    none
                    (Expr.block
                      none
                      (Block.mk
                        [
                          (Stmt.expr
                            (Expr.assign
                              (Expr.unary
                                UnOp.deref
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "p" PathArguments.none)])))
                              (Expr.tryExpr
                                (Expr.methodCall
                                  (Expr.path
                                    none
                                    (Path.mk false [(PathSegment.mk "p" PathArguments.none)]))
                                  "transition"
                                  none
                                  [
                                    (Expr.path
                                      none
                                      (Path.mk
                                        false
                                        [(PathSegment.mk "access_kind" PathArguments.none)])),
                                    (Expr.path
                                      none
                                      (Path.mk
                                        false
                                        [(PathSegment.mk "node_relation" PathArguments.none)]))])))
                            false)])))])
              true),
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
              " When a protector is released, we transition to the unprotected state machine.")),
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue
              " Additionally, we might emit a _protector end access_, depending on our current state.")),
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue
              " The second state indicates that access, or is `None` when no access should happen.")),
          (Attr.mk true "doc" (AttrMeta.nameValue "")),
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue " This method may only be called when a protector is present."))]
        Visibility.inherited
        false
        (Signature.mk
          false
          false
          false
          none
          "unprotect"
          (Generics.mk [] [])
          [(FnArg.receiver [] false none false none)]
          false
          (some
            (Ty.tuple
              [
                (Ty.path none (Path.mk false [(PathSegment.mk "Permission" PathArguments.none)])),
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
                                (Path.mk false [(PathSegment.mk "AccessKind" PathArguments.none)])))]))]))])))
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
                          (PathSegment.mk "Permission" PathArguments.none),
                          (PathSegment.mk "Unprot" PathArguments.none)])
                      [Pat.wild])
                    none
                    (Expr.macro
                      (Macro.mk
                        (Path.mk false [(PathSegment.mk "unreachable" PathArguments.none)])
                        MacroDelimiter.paren
                        (MacroBody.exprs [] false)))),
                  (Arm.mk
                    []
                    (Pat.tupleStruct
                      none
                      (Path.mk
                        false
                        [
                          (PathSegment.mk "Permission" PathArguments.none),
                          (PathSegment.mk "Prot" PathArguments.none)])
                      [(Pat.ident false false "p" none)])
                    none
                    (Expr.block
                      none
                      (Block.mk
                        [
                          (Stmt.letStmt
                            []
                            (Pat.tuple
                              [
                                (Pat.ident false false "new_perm" none),
                                (Pat.ident false false "access" none)])
                            (some
                              (Expr.methodCall
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "p" PathArguments.none)]))
                                "unprotect"
                                none
                                []))
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
                                        (PathSegment.mk "Permission" PathArguments.none),
                                        (PathSegment.mk "Unprot" PathArguments.none)]))
                                  [
                                    (Expr.path
                                      none
                                      (Path.mk
                                        false
                                        [(PathSegment.mk "new_perm" PathArguments.none)]))]),
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "access" PathArguments.none)]))])
                            false)])))])
              false)])),
      (ImplItem.fn
        [
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue
              " Strongly protected nodes can block deallocation, based on their permission.")),
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue
              " Specifically, they block allocation iff they would cause UB on a foreign write,")),
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue
              " that is, if they have been locally accessed (\"used\"), with an exception for `Cell`.")),
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue
              " The check for whether the protector is actually strong happens elsewhere, before")),
          (Attr.mk true "doc" (AttrMeta.nameValue " this method is called."))]
        Visibility.inherited
        false
        (Signature.mk
          false
          false
          false
          none
          "prevents_deallocation"
          (Generics.mk [] [])
          [(FnArg.receiver [] true none false none)]
          false
          (some (Ty.path none (Path.mk false [(PathSegment.mk "bool" PathArguments.none)]))))
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
                          (PathSegment.mk "Permission" PathArguments.none),
                          (PathSegment.mk "Unprot" PathArguments.none)])
                      [(Pat.ident false false "p" none)])
                    none
                    (Expr.methodCall
                      (Expr.path none (Path.mk false [(PathSegment.mk "p" PathArguments.none)]))
                      "prevents_deallocation"
                      none
                      [])),
                  (Arm.mk
                    []
                    (Pat.tupleStruct
                      none
                      (Path.mk
                        false
                        [
                          (PathSegment.mk "Permission" PathArguments.none),
                          (PathSegment.mk "Prot" PathArguments.none)])
                      [(Pat.ident false false "p" none)])
                    none
                    (Expr.methodCall
                      (Expr.path none (Path.mk false [(PathSegment.mk "p" PathArguments.none)]))
                      "prevents_deallocation"
                      none
                      []))])
              false)])),
      (ImplItem.fn
        [
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue " This function checking this node's internal invariant.")),
          (Attr.mk true "doc" (AttrMeta.nameValue " It is only used in debug asserts."))]
        Visibility.inherited
        false
        (Signature.mk
          false
          false
          false
          none
          "matches_protector"
          (Generics.mk [] [])
          [
            (FnArg.receiver [] true none false none),
            (FnArg.typed
              []
              (Pat.ident false false "protected" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "Protected" PathArguments.none)])))]
          false
          (some (Ty.path none (Path.mk false [(PathSegment.mk "bool" PathArguments.none)]))))
        (Block.mk
          [
            (Stmt.expr
              (Expr.ite
                (Expr.methodCall
                  (Expr.path none (Path.mk false [(PathSegment.mk "protected" PathArguments.none)]))
                  "yes"
                  none
                  [])
                (Block.mk
                  [
                    (Stmt.expr
                      (Expr.macro
                        (Macro.mk
                          (Path.mk false [(PathSegment.mk "matches" PathArguments.none)])
                          MacroDelimiter.paren
                          (MacroBody.exprAndPat
                            (Expr.path
                              none
                              (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                            (Pat.tupleStruct
                              none
                              (Path.mk
                                false
                                [
                                  (PathSegment.mk "Permission" PathArguments.none),
                                  (PathSegment.mk "Prot" PathArguments.none)])
                              [Pat.wild])
                            none)))
                      false)])
                (some
                  (Expr.block
                    none
                    (Block.mk
                      [
                        (Stmt.expr
                          (Expr.macro
                            (Macro.mk
                              (Path.mk false [(PathSegment.mk "matches" PathArguments.none)])
                              MacroDelimiter.paren
                              (MacroBody.exprAndPat
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                                (Pat.tupleStruct
                                  none
                                  (Path.mk
                                    false
                                    [
                                      (PathSegment.mk "Permission" PathArguments.none),
                                      (PathSegment.mk "Unprot" PathArguments.none)])
                                  [Pat.wild])
                                none)))
                          false)]))))
              false)]))])

/-- `spec/mem/tree_borrows/state_machine.md:80` -/
def impl_Permission__init_access : Item :=
  (Item.impl
    []
    false
    false
    (Generics.mk [] [])
    false
    none
    (Ty.path none (Path.mk false [(PathSegment.mk "Permission" PathArguments.none)]))
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
          "init_access"
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
                            (Path.mk false [(PathSegment.mk "AccessKind" PathArguments.none)])))]))]))))
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
                          (PathSegment.mk "Permission" PathArguments.none),
                          (PathSegment.mk "Unprot" PathArguments.none)])
                      [(Pat.ident false false "p" none)])
                    none
                    (Expr.methodCall
                      (Expr.path none (Path.mk false [(PathSegment.mk "p" PathArguments.none)]))
                      "init_access"
                      none
                      [])),
                  (Arm.mk
                    []
                    (Pat.tupleStruct
                      none
                      (Path.mk
                        false
                        [
                          (PathSegment.mk "Permission" PathArguments.none),
                          (PathSegment.mk "Prot" PathArguments.none)])
                      [(Pat.ident false false "p" none)])
                    none
                    (Expr.methodCall
                      (Expr.path none (Path.mk false [(PathSegment.mk "p" PathArguments.none)]))
                      "init_access"
                      none
                      []))])
              false)]))])

/-- All items of `spec/mem/tree_borrows/state_machine.md`, in source order, with provenance. -/
def items : List SourceItem :=
  [
    (SourceItem.mk
      "enum_Permission"
      11
      "9e90bcf0357d3e6bb373889e100b853793859ff8575160b8837b1d0caf22466f"
      enum_Permission),
    (SourceItem.mk
      "impl_Permission__transition"
      16
      "e57cd27a95fbdb1b31434bd40a9bc1d804d242f94b5ffb2a1f51a15af8671c13"
      impl_Permission__transition),
    (SourceItem.mk
      "impl_Permission__init_access"
      80
      "316dccf7122ec7691d8979b244dcdea614d2ca8d301a81ca1174d58e636f442e"
      impl_Permission__init_access)]

end MiniRustSpec.Gen.Items.Mem.TreeBorrows.StateMachine
