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
`spec/mem/tree_borrows/state_machine_protected.md` (commit `d821c6e3`), one Lean definition per item, in source order.
-/

import MiniRustSpec.Meta.Syntax

set_option maxRecDepth 100000

namespace MiniRustSpec.Gen.Items.Mem.TreeBorrows.StateMachineProtected

open MiniRustSpec.Syntax

/-- Path of the upstream file these items were extracted from. -/
def sourceFile : String := "spec/mem/tree_borrows/state_machine_protected.md"

/-- SHA-256 of the upstream file. -/
def sourceSha256 : String := "968aa477b32c2e90aec47db517c24bed03a2e5292871b4121aab6a654deb7e51"

/-- `spec/mem/tree_borrows/state_machine_protected.md:7` -/
def enum_PermissionProt : Item :=
  (Item.enum
    []
    Visibility.inherited
    "PermissionProt"
    (Generics.mk [] [])
    [
      (Variant.mk
        [
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue " Represents a shared reference to interior mutable data."))]
        "Cell"
        Fields.unit
        none),
      (Variant.mk
        [
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue
              " The various flavours of `Reserved` correspond to a protected/noalias node where no writes happened yet."))]
        "Reserved"
        (Fields.named
          [
            (Field.mk
              []
              Visibility.inherited
              (some "had_local_read")
              (Ty.path none (Path.mk false [(PathSegment.mk "bool" PathArguments.none)]))),
            (Field.mk
              []
              Visibility.inherited
              (some "had_foreign_read")
              (Ty.path none (Path.mk false [(PathSegment.mk "bool" PathArguments.none)])))])
        none),
      (Variant.mk
        [
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue
              " Represents an activated (written to) mutable reference, i.e. it must actually be unique right now."))]
        "Unique"
        Fields.unit
        none),
      (Variant.mk
        [(Attr.mk true "doc" (AttrMeta.nameValue " Represents a shared (immutable) reference."))]
        "Frozen"
        (Fields.named
          [
            (Field.mk
              []
              Visibility.inherited
              (some "had_local_read")
              (Ty.path none (Path.mk false [(PathSegment.mk "bool" PathArguments.none)])))])
        none),
      (Variant.mk
        [
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue
              " Represents a reference that experienced a foreign write. It can not be used locally anymore."))]
        "Disabled"
        Fields.unit
        none)])

/-- `spec/mem/tree_borrows/state_machine_protected.md:28` -/
def impl_PermissionProt__local_read : Item :=
  (Item.impl
    []
    false
    false
    (Generics.mk [] [])
    false
    none
    (Ty.path none (Path.mk false [(PathSegment.mk "PermissionProt" PathArguments.none)]))
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
          "local_read"
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
                    (PathArguments.angleBracketed
                      false
                      [
                        (GenericArgument.type
                          (Ty.path
                            none
                            (Path.mk false [(PathSegment.mk "PermissionProt" PathArguments.none)])))]))]))))
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
                          (PathSegment.mk "PermissionProt" PathArguments.none),
                          (PathSegment.mk "Cell" PathArguments.none)]))
                    none
                    (Expr.call
                      (Expr.path none (Path.mk false [(PathSegment.mk "ret" PathArguments.none)]))
                      [
                        (Expr.path
                          none
                          (Path.mk
                            false
                            [
                              (PathSegment.mk "PermissionProt" PathArguments.none),
                              (PathSegment.mk "Cell" PathArguments.none)]))])),
                  (Arm.mk
                    []
                    (Pat.struct
                      none
                      (Path.mk
                        false
                        [
                          (PathSegment.mk "PermissionProt" PathArguments.none),
                          (PathSegment.mk "Reserved" PathArguments.none)])
                      [
                        (FieldPat.mk
                          []
                          (Member.named "had_foreign_read")
                          true
                          (Pat.ident false false "had_foreign_read" none))]
                      true)
                    none
                    (Expr.call
                      (Expr.path none (Path.mk false [(PathSegment.mk "ret" PathArguments.none)]))
                      [
                        (Expr.struct
                          none
                          (Path.mk
                            false
                            [
                              (PathSegment.mk "PermissionProt" PathArguments.none),
                              (PathSegment.mk "Reserved" PathArguments.none)])
                          [
                            (FieldValue.mk
                              []
                              (Member.named "had_local_read")
                              false
                              (Expr.lit (Lit.bool true))),
                            (FieldValue.mk
                              []
                              (Member.named "had_foreign_read")
                              true
                              (Expr.path
                                none
                                (Path.mk
                                  false
                                  [(PathSegment.mk "had_foreign_read" PathArguments.none)])))]
                          false
                          none)])),
                  (Arm.mk
                    []
                    (Pat.path
                      none
                      (Path.mk
                        false
                        [
                          (PathSegment.mk "PermissionProt" PathArguments.none),
                          (PathSegment.mk "Unique" PathArguments.none)]))
                    none
                    (Expr.call
                      (Expr.path none (Path.mk false [(PathSegment.mk "ret" PathArguments.none)]))
                      [
                        (Expr.path
                          none
                          (Path.mk
                            false
                            [
                              (PathSegment.mk "PermissionProt" PathArguments.none),
                              (PathSegment.mk "Unique" PathArguments.none)]))])),
                  (Arm.mk
                    []
                    (Pat.struct
                      none
                      (Path.mk
                        false
                        [
                          (PathSegment.mk "PermissionProt" PathArguments.none),
                          (PathSegment.mk "Frozen" PathArguments.none)])
                      []
                      true)
                    none
                    (Expr.call
                      (Expr.path none (Path.mk false [(PathSegment.mk "ret" PathArguments.none)]))
                      [
                        (Expr.struct
                          none
                          (Path.mk
                            false
                            [
                              (PathSegment.mk "PermissionProt" PathArguments.none),
                              (PathSegment.mk "Frozen" PathArguments.none)])
                          [
                            (FieldValue.mk
                              []
                              (Member.named "had_local_read")
                              false
                              (Expr.lit (Lit.bool true)))]
                          false
                          none)])),
                  (Arm.mk
                    []
                    (Pat.path
                      none
                      (Path.mk
                        false
                        [
                          (PathSegment.mk "PermissionProt" PathArguments.none),
                          (PathSegment.mk "Disabled" PathArguments.none)]))
                    none
                    (Expr.macro
                      (Macro.mk
                        (Path.mk false [(PathSegment.mk "throw_ub" PathArguments.none)])
                        MacroDelimiter.paren
                        (MacroBody.exprs
                          [
                            (Expr.lit
                              (Lit.str "Tree Borrows: local read of protected Disabled reference"))]
                          false))))])
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
          "local_write"
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
                    (PathArguments.angleBracketed
                      false
                      [
                        (GenericArgument.type
                          (Ty.path
                            none
                            (Path.mk false [(PathSegment.mk "PermissionProt" PathArguments.none)])))]))]))))
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
                          (PathSegment.mk "PermissionProt" PathArguments.none),
                          (PathSegment.mk "Cell" PathArguments.none)]))
                    none
                    (Expr.call
                      (Expr.path none (Path.mk false [(PathSegment.mk "ret" PathArguments.none)]))
                      [
                        (Expr.path
                          none
                          (Path.mk
                            false
                            [
                              (PathSegment.mk "PermissionProt" PathArguments.none),
                              (PathSegment.mk "Cell" PathArguments.none)]))])),
                  (Arm.mk
                    []
                    (Pat.path
                      none
                      (Path.mk
                        false
                        [
                          (PathSegment.mk "PermissionProt" PathArguments.none),
                          (PathSegment.mk "Unique" PathArguments.none)]))
                    none
                    (Expr.call
                      (Expr.path none (Path.mk false [(PathSegment.mk "ret" PathArguments.none)]))
                      [
                        (Expr.path
                          none
                          (Path.mk
                            false
                            [
                              (PathSegment.mk "PermissionProt" PathArguments.none),
                              (PathSegment.mk "Unique" PathArguments.none)]))])),
                  (Arm.mk
                    []
                    (Pat.struct
                      none
                      (Path.mk
                        false
                        [
                          (PathSegment.mk "PermissionProt" PathArguments.none),
                          (PathSegment.mk "Reserved" PathArguments.none)])
                      [
                        (FieldPat.mk
                          []
                          (Member.named "had_foreign_read")
                          false
                          (Pat.lit (Expr.lit (Lit.bool false))))]
                      true)
                    none
                    (Expr.call
                      (Expr.path none (Path.mk false [(PathSegment.mk "ret" PathArguments.none)]))
                      [
                        (Expr.path
                          none
                          (Path.mk
                            false
                            [
                              (PathSegment.mk "PermissionProt" PathArguments.none),
                              (PathSegment.mk "Unique" PathArguments.none)]))])),
                  (Arm.mk
                    []
                    (Pat.struct
                      none
                      (Path.mk
                        false
                        [
                          (PathSegment.mk "PermissionProt" PathArguments.none),
                          (PathSegment.mk "Reserved" PathArguments.none)])
                      [
                        (FieldPat.mk
                          []
                          (Member.named "had_foreign_read")
                          false
                          (Pat.lit (Expr.lit (Lit.bool true))))]
                      true)
                    none
                    (Expr.macro
                      (Macro.mk
                        (Path.mk false [(PathSegment.mk "throw_ub" PathArguments.none)])
                        MacroDelimiter.paren
                        (MacroBody.exprs
                          [
                            (Expr.lit
                              (Lit.str
                                "Tree Borrows: local write to protected Reserved reference that had a foreign read"))]
                          false)))),
                  (Arm.mk
                    []
                    (Pat.struct
                      none
                      (Path.mk
                        false
                        [
                          (PathSegment.mk "PermissionProt" PathArguments.none),
                          (PathSegment.mk "Frozen" PathArguments.none)])
                      []
                      true)
                    none
                    (Expr.macro
                      (Macro.mk
                        (Path.mk false [(PathSegment.mk "throw_ub" PathArguments.none)])
                        MacroDelimiter.paren
                        (MacroBody.exprs
                          [
                            (Expr.lit
                              (Lit.str "Tree Borrows: local write to protected Frozen reference"))]
                          false)))),
                  (Arm.mk
                    []
                    (Pat.path
                      none
                      (Path.mk
                        false
                        [
                          (PathSegment.mk "PermissionProt" PathArguments.none),
                          (PathSegment.mk "Disabled" PathArguments.none)]))
                    none
                    (Expr.macro
                      (Macro.mk
                        (Path.mk false [(PathSegment.mk "throw_ub" PathArguments.none)])
                        MacroDelimiter.paren
                        (MacroBody.exprs
                          [
                            (Expr.lit
                              (Lit.str "Tree Borrows: local write to protected Disabled reference"))]
                          false))))])
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
          "foreign_read"
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
                    (PathArguments.angleBracketed
                      false
                      [
                        (GenericArgument.type
                          (Ty.path
                            none
                            (Path.mk false [(PathSegment.mk "PermissionProt" PathArguments.none)])))]))]))))
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
                          (PathSegment.mk "PermissionProt" PathArguments.none),
                          (PathSegment.mk "Cell" PathArguments.none)]))
                    none
                    (Expr.call
                      (Expr.path none (Path.mk false [(PathSegment.mk "ret" PathArguments.none)]))
                      [
                        (Expr.path
                          none
                          (Path.mk
                            false
                            [
                              (PathSegment.mk "PermissionProt" PathArguments.none),
                              (PathSegment.mk "Cell" PathArguments.none)]))])),
                  (Arm.mk
                    []
                    (Pat.path
                      none
                      (Path.mk
                        false
                        [
                          (PathSegment.mk "PermissionProt" PathArguments.none),
                          (PathSegment.mk "Unique" PathArguments.none)]))
                    none
                    (Expr.macro
                      (Macro.mk
                        (Path.mk false [(PathSegment.mk "throw_ub" PathArguments.none)])
                        MacroDelimiter.paren
                        (MacroBody.exprs
                          [
                            (Expr.lit
                              (Lit.str "Tree Borrows: foreign read of protected Unique reference"))]
                          false)))),
                  (Arm.mk
                    []
                    (Pat.struct
                      none
                      (Path.mk
                        false
                        [
                          (PathSegment.mk "PermissionProt" PathArguments.none),
                          (PathSegment.mk "Reserved" PathArguments.none)])
                      [
                        (FieldPat.mk
                          []
                          (Member.named "had_local_read")
                          true
                          (Pat.ident false false "had_local_read" none))]
                      true)
                    none
                    (Expr.call
                      (Expr.path none (Path.mk false [(PathSegment.mk "ret" PathArguments.none)]))
                      [
                        (Expr.struct
                          none
                          (Path.mk
                            false
                            [
                              (PathSegment.mk "PermissionProt" PathArguments.none),
                              (PathSegment.mk "Reserved" PathArguments.none)])
                          [
                            (FieldValue.mk
                              []
                              (Member.named "had_local_read")
                              true
                              (Expr.path
                                none
                                (Path.mk
                                  false
                                  [(PathSegment.mk "had_local_read" PathArguments.none)]))),
                            (FieldValue.mk
                              []
                              (Member.named "had_foreign_read")
                              false
                              (Expr.lit (Lit.bool true)))]
                          false
                          none)])),
                  (Arm.mk
                    []
                    (Pat.struct
                      none
                      (Path.mk
                        false
                        [
                          (PathSegment.mk "PermissionProt" PathArguments.none),
                          (PathSegment.mk "Frozen" PathArguments.none)])
                      [
                        (FieldPat.mk
                          []
                          (Member.named "had_local_read")
                          true
                          (Pat.ident false false "had_local_read" none))]
                      false)
                    none
                    (Expr.call
                      (Expr.path none (Path.mk false [(PathSegment.mk "ret" PathArguments.none)]))
                      [
                        (Expr.struct
                          none
                          (Path.mk
                            false
                            [
                              (PathSegment.mk "PermissionProt" PathArguments.none),
                              (PathSegment.mk "Frozen" PathArguments.none)])
                          [
                            (FieldValue.mk
                              []
                              (Member.named "had_local_read")
                              true
                              (Expr.path
                                none
                                (Path.mk
                                  false
                                  [(PathSegment.mk "had_local_read" PathArguments.none)])))]
                          false
                          none)])),
                  (Arm.mk
                    []
                    (Pat.path
                      none
                      (Path.mk
                        false
                        [
                          (PathSegment.mk "PermissionProt" PathArguments.none),
                          (PathSegment.mk "Disabled" PathArguments.none)]))
                    none
                    (Expr.call
                      (Expr.path none (Path.mk false [(PathSegment.mk "ret" PathArguments.none)]))
                      [
                        (Expr.path
                          none
                          (Path.mk
                            false
                            [
                              (PathSegment.mk "PermissionProt" PathArguments.none),
                              (PathSegment.mk "Disabled" PathArguments.none)]))]))])
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
          "foreign_write"
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
                    (PathArguments.angleBracketed
                      false
                      [
                        (GenericArgument.type
                          (Ty.path
                            none
                            (Path.mk false [(PathSegment.mk "PermissionProt" PathArguments.none)])))]))]))))
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
                          (PathSegment.mk "PermissionProt" PathArguments.none),
                          (PathSegment.mk "Cell" PathArguments.none)]))
                    none
                    (Expr.call
                      (Expr.path none (Path.mk false [(PathSegment.mk "ret" PathArguments.none)]))
                      [
                        (Expr.path
                          none
                          (Path.mk
                            false
                            [
                              (PathSegment.mk "PermissionProt" PathArguments.none),
                              (PathSegment.mk "Cell" PathArguments.none)]))])),
                  (Arm.mk
                    []
                    (Pat.or
                      [
                        (Pat.struct
                          none
                          (Path.mk
                            false
                            [
                              (PathSegment.mk "PermissionProt" PathArguments.none),
                              (PathSegment.mk "Frozen" PathArguments.none)])
                          [
                            (FieldPat.mk
                              []
                              (Member.named "had_local_read")
                              false
                              (Pat.lit (Expr.lit (Lit.bool true))))]
                          false),
                        (Pat.struct
                          none
                          (Path.mk
                            false
                            [
                              (PathSegment.mk "PermissionProt" PathArguments.none),
                              (PathSegment.mk "Reserved" PathArguments.none)])
                          [
                            (FieldPat.mk
                              []
                              (Member.named "had_local_read")
                              false
                              (Pat.lit (Expr.lit (Lit.bool true))))]
                          true)])
                    none
                    (Expr.macro
                      (Macro.mk
                        (Path.mk false [(PathSegment.mk "throw_ub" PathArguments.none)])
                        MacroDelimiter.paren
                        (MacroBody.exprs
                          [
                            (Expr.lit
                              (Lit.str
                                "Tree Borrows: foreign write of protected {} reference which had a local read")),
                            (Expr.ite
                              (Expr.macro
                                (Macro.mk
                                  (Path.mk false [(PathSegment.mk "matches" PathArguments.none)])
                                  MacroDelimiter.paren
                                  (MacroBody.exprAndPat
                                    (Expr.path
                                      none
                                      (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                                    (Pat.struct
                                      none
                                      (Path.mk
                                        false
                                        [
                                          (PathSegment.mk "PermissionProt" PathArguments.none),
                                          (PathSegment.mk "Frozen" PathArguments.none)])
                                      []
                                      true)
                                    none)))
                              (Block.mk [(Stmt.expr (Expr.lit (Lit.str "Frozen")) false)])
                              (some
                                (Expr.block
                                  none
                                  (Block.mk [(Stmt.expr (Expr.lit (Lit.str "Reserved")) false)]))))]
                          false)))),
                  (Arm.mk
                    []
                    (Pat.path
                      none
                      (Path.mk
                        false
                        [
                          (PathSegment.mk "PermissionProt" PathArguments.none),
                          (PathSegment.mk "Unique" PathArguments.none)]))
                    none
                    (Expr.macro
                      (Macro.mk
                        (Path.mk false [(PathSegment.mk "throw_ub" PathArguments.none)])
                        MacroDelimiter.paren
                        (MacroBody.exprs
                          [
                            (Expr.lit
                              (Lit.str "Tree Borrows: foreign read of protected Unique reference"))]
                          false)))),
                  (Arm.mk
                    []
                    (Pat.or
                      [
                        (Pat.struct
                          none
                          (Path.mk
                            false
                            [
                              (PathSegment.mk "PermissionProt" PathArguments.none),
                              (PathSegment.mk "Frozen" PathArguments.none)])
                          [
                            (FieldPat.mk
                              []
                              (Member.named "had_local_read")
                              false
                              (Pat.lit (Expr.lit (Lit.bool false))))]
                          false),
                        (Pat.struct
                          none
                          (Path.mk
                            false
                            [
                              (PathSegment.mk "PermissionProt" PathArguments.none),
                              (PathSegment.mk "Reserved" PathArguments.none)])
                          [
                            (FieldPat.mk
                              []
                              (Member.named "had_local_read")
                              false
                              (Pat.lit (Expr.lit (Lit.bool false))))]
                          true)])
                    none
                    (Expr.call
                      (Expr.path none (Path.mk false [(PathSegment.mk "ret" PathArguments.none)]))
                      [
                        (Expr.path
                          none
                          (Path.mk
                            false
                            [
                              (PathSegment.mk "PermissionProt" PathArguments.none),
                              (PathSegment.mk "Disabled" PathArguments.none)]))])),
                  (Arm.mk
                    []
                    (Pat.path
                      none
                      (Path.mk
                        false
                        [
                          (PathSegment.mk "PermissionProt" PathArguments.none),
                          (PathSegment.mk "Disabled" PathArguments.none)]))
                    none
                    (Expr.call
                      (Expr.path none (Path.mk false [(PathSegment.mk "ret" PathArguments.none)]))
                      [
                        (Expr.path
                          none
                          (Path.mk
                            false
                            [
                              (PathSegment.mk "PermissionProt" PathArguments.none),
                              (PathSegment.mk "Disabled" PathArguments.none)]))]))])
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
          "transition"
          (Generics.mk [] [])
          [
            (FnArg.receiver [] false none false none),
            (FnArg.typed
              []
              (Pat.ident false false "access_kind" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "AccessKind" PathArguments.none)]))),
            (FnArg.typed
              []
              (Pat.ident false false "node_relation" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "NodeRelation" PathArguments.none)])))]
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
                            (Path.mk false [(PathSegment.mk "PermissionProt" PathArguments.none)])))]))]))))
        (Block.mk
          [
            (Stmt.expr
              (Expr.matchExpr
                (Expr.tuple
                  [
                    (Expr.path
                      none
                      (Path.mk false [(PathSegment.mk "node_relation" PathArguments.none)])),
                    (Expr.path
                      none
                      (Path.mk false [(PathSegment.mk "access_kind" PathArguments.none)]))])
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
                              (PathSegment.mk "NodeRelation" PathArguments.none),
                              (PathSegment.mk "Local" PathArguments.none)])),
                        (Pat.path
                          none
                          (Path.mk
                            false
                            [
                              (PathSegment.mk "AccessKind" PathArguments.none),
                              (PathSegment.mk "Read" PathArguments.none)]))])
                    none
                    (Expr.methodCall
                      (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                      "local_read"
                      none
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
                              (PathSegment.mk "NodeRelation" PathArguments.none),
                              (PathSegment.mk "Local" PathArguments.none)])),
                        (Pat.path
                          none
                          (Path.mk
                            false
                            [
                              (PathSegment.mk "AccessKind" PathArguments.none),
                              (PathSegment.mk "Write" PathArguments.none)]))])
                    none
                    (Expr.methodCall
                      (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                      "local_write"
                      none
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
                              (PathSegment.mk "NodeRelation" PathArguments.none),
                              (PathSegment.mk "Foreign" PathArguments.none)])),
                        (Pat.path
                          none
                          (Path.mk
                            false
                            [
                              (PathSegment.mk "AccessKind" PathArguments.none),
                              (PathSegment.mk "Read" PathArguments.none)]))])
                    none
                    (Expr.methodCall
                      (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                      "foreign_read"
                      none
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
                              (PathSegment.mk "NodeRelation" PathArguments.none),
                              (PathSegment.mk "Foreign" PathArguments.none)])),
                        (Pat.path
                          none
                          (Path.mk
                            false
                            [
                              (PathSegment.mk "AccessKind" PathArguments.none),
                              (PathSegment.mk "Write" PathArguments.none)]))])
                    none
                    (Expr.methodCall
                      (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                      "foreign_write"
                      none
                      []))])
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
                    (Pat.path
                      none
                      (Path.mk
                        false
                        [
                          (PathSegment.mk "PermissionProt" PathArguments.none),
                          (PathSegment.mk "Cell" PathArguments.none)]))
                    none
                    (Expr.path none (Path.mk false [(PathSegment.mk "None" PathArguments.none)]))),
                  (Arm.mk
                    []
                    (Pat.path
                      none
                      (Path.mk
                        false
                        [
                          (PathSegment.mk "PermissionProt" PathArguments.none),
                          (PathSegment.mk "Unique" PathArguments.none)]))
                    none
                    (Expr.call
                      (Expr.path none (Path.mk false [(PathSegment.mk "Some" PathArguments.none)]))
                      [
                        (Expr.path
                          none
                          (Path.mk
                            false
                            [
                              (PathSegment.mk "AccessKind" PathArguments.none),
                              (PathSegment.mk "Write" PathArguments.none)]))])),
                  (Arm.mk
                    []
                    Pat.wild
                    none
                    (Expr.call
                      (Expr.path none (Path.mk false [(PathSegment.mk "Some" PathArguments.none)]))
                      [
                        (Expr.path
                          none
                          (Path.mk
                            false
                            [
                              (PathSegment.mk "AccessKind" PathArguments.none),
                              (PathSegment.mk "Read" PathArguments.none)]))]))])
              false)]))])

/-- `spec/mem/tree_borrows/state_machine_protected.md:111` -/
def impl_PermissionProt__unprotect : Item :=
  (Item.impl
    []
    false
    false
    (Generics.mk [] [])
    false
    none
    (Ty.path none (Path.mk false [(PathSegment.mk "PermissionProt" PathArguments.none)]))
    [
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
              " The second state indicates that access, or is `None` when no access should happen."))]
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
                (Ty.path
                  none
                  (Path.mk false [(PathSegment.mk "PermissionUnprot" PathArguments.none)])),
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
                    (Pat.path
                      none
                      (Path.mk
                        false
                        [
                          (PathSegment.mk "PermissionProt" PathArguments.none),
                          (PathSegment.mk "Unique" PathArguments.none)]))
                    none
                    (Expr.tuple
                      [
                        (Expr.path
                          none
                          (Path.mk
                            false
                            [
                              (PathSegment.mk "PermissionUnprot" PathArguments.none),
                              (PathSegment.mk "Unique" PathArguments.none)])),
                        (Expr.call
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "Some" PathArguments.none)]))
                          [
                            (Expr.path
                              none
                              (Path.mk
                                false
                                [
                                  (PathSegment.mk "AccessKind" PathArguments.none),
                                  (PathSegment.mk "Write" PathArguments.none)]))])])),
                  (Arm.mk
                    []
                    (Pat.struct
                      none
                      (Path.mk
                        false
                        [
                          (PathSegment.mk "PermissionProt" PathArguments.none),
                          (PathSegment.mk "Reserved" PathArguments.none)])
                      [
                        (FieldPat.mk
                          []
                          (Member.named "had_local_read")
                          false
                          (Pat.lit (Expr.lit (Lit.bool true))))]
                      true)
                    none
                    (Expr.tuple
                      [
                        (Expr.path
                          none
                          (Path.mk
                            false
                            [
                              (PathSegment.mk "PermissionUnprot" PathArguments.none),
                              (PathSegment.mk "Reserved" PathArguments.none)])),
                        (Expr.call
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "Some" PathArguments.none)]))
                          [
                            (Expr.path
                              none
                              (Path.mk
                                false
                                [
                                  (PathSegment.mk "AccessKind" PathArguments.none),
                                  (PathSegment.mk "Read" PathArguments.none)]))])])),
                  (Arm.mk
                    []
                    (Pat.struct
                      none
                      (Path.mk
                        false
                        [
                          (PathSegment.mk "PermissionProt" PathArguments.none),
                          (PathSegment.mk "Reserved" PathArguments.none)])
                      [
                        (FieldPat.mk
                          []
                          (Member.named "had_local_read")
                          false
                          (Pat.lit (Expr.lit (Lit.bool false))))]
                      true)
                    none
                    (Expr.tuple
                      [
                        (Expr.path
                          none
                          (Path.mk
                            false
                            [
                              (PathSegment.mk "PermissionUnprot" PathArguments.none),
                              (PathSegment.mk "Reserved" PathArguments.none)])),
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "None" PathArguments.none)]))])),
                  (Arm.mk
                    []
                    (Pat.struct
                      none
                      (Path.mk
                        false
                        [
                          (PathSegment.mk "PermissionProt" PathArguments.none),
                          (PathSegment.mk "Frozen" PathArguments.none)])
                      [
                        (FieldPat.mk
                          []
                          (Member.named "had_local_read")
                          false
                          (Pat.lit (Expr.lit (Lit.bool true))))]
                      false)
                    none
                    (Expr.tuple
                      [
                        (Expr.path
                          none
                          (Path.mk
                            false
                            [
                              (PathSegment.mk "PermissionUnprot" PathArguments.none),
                              (PathSegment.mk "Frozen" PathArguments.none)])),
                        (Expr.call
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "Some" PathArguments.none)]))
                          [
                            (Expr.path
                              none
                              (Path.mk
                                false
                                [
                                  (PathSegment.mk "AccessKind" PathArguments.none),
                                  (PathSegment.mk "Read" PathArguments.none)]))])])),
                  (Arm.mk
                    []
                    (Pat.struct
                      none
                      (Path.mk
                        false
                        [
                          (PathSegment.mk "PermissionProt" PathArguments.none),
                          (PathSegment.mk "Frozen" PathArguments.none)])
                      [
                        (FieldPat.mk
                          []
                          (Member.named "had_local_read")
                          false
                          (Pat.lit (Expr.lit (Lit.bool false))))]
                      false)
                    none
                    (Expr.tuple
                      [
                        (Expr.path
                          none
                          (Path.mk
                            false
                            [
                              (PathSegment.mk "PermissionUnprot" PathArguments.none),
                              (PathSegment.mk "Frozen" PathArguments.none)])),
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "None" PathArguments.none)]))])),
                  (Arm.mk
                    []
                    (Pat.path
                      none
                      (Path.mk
                        false
                        [
                          (PathSegment.mk "PermissionProt" PathArguments.none),
                          (PathSegment.mk "Disabled" PathArguments.none)]))
                    none
                    (Expr.tuple
                      [
                        (Expr.path
                          none
                          (Path.mk
                            false
                            [
                              (PathSegment.mk "PermissionUnprot" PathArguments.none),
                              (PathSegment.mk "Disabled" PathArguments.none)])),
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "None" PathArguments.none)]))])),
                  (Arm.mk
                    []
                    (Pat.path
                      none
                      (Path.mk
                        false
                        [
                          (PathSegment.mk "PermissionProt" PathArguments.none),
                          (PathSegment.mk "Cell" PathArguments.none)]))
                    none
                    (Expr.tuple
                      [
                        (Expr.path
                          none
                          (Path.mk
                            false
                            [
                              (PathSegment.mk "PermissionUnprot" PathArguments.none),
                              (PathSegment.mk "Cell" PathArguments.none)])),
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "None" PathArguments.none)]))]))])
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
              " The check for whether the protector is actually strong happens elsewhere."))]
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
                    (Pat.path
                      none
                      (Path.mk
                        false
                        [
                          (PathSegment.mk "PermissionProt" PathArguments.none),
                          (PathSegment.mk "Unique" PathArguments.none)]))
                    none
                    (Expr.lit (Lit.bool true))),
                  (Arm.mk
                    []
                    (Pat.or
                      [
                        (Pat.struct
                          none
                          (Path.mk
                            false
                            [
                              (PathSegment.mk "PermissionProt" PathArguments.none),
                              (PathSegment.mk "Reserved" PathArguments.none)])
                          [
                            (FieldPat.mk
                              []
                              (Member.named "had_local_read")
                              true
                              (Pat.ident false false "had_local_read" none))]
                          true),
                        (Pat.struct
                          none
                          (Path.mk
                            false
                            [
                              (PathSegment.mk "PermissionProt" PathArguments.none),
                              (PathSegment.mk "Frozen" PathArguments.none)])
                          [
                            (FieldPat.mk
                              []
                              (Member.named "had_local_read")
                              true
                              (Pat.ident false false "had_local_read" none))]
                          false)])
                    none
                    (Expr.unary
                      UnOp.deref
                      (Expr.path
                        none
                        (Path.mk false [(PathSegment.mk "had_local_read" PathArguments.none)])))),
                  (Arm.mk
                    []
                    (Pat.path
                      none
                      (Path.mk
                        false
                        [
                          (PathSegment.mk "PermissionProt" PathArguments.none),
                          (PathSegment.mk "Disabled" PathArguments.none)]))
                    none
                    (Expr.lit (Lit.bool false))),
                  (Arm.mk
                    []
                    (Pat.path
                      none
                      (Path.mk
                        false
                        [
                          (PathSegment.mk "PermissionProt" PathArguments.none),
                          (PathSegment.mk "Cell" PathArguments.none)]))
                    none
                    (Expr.lit (Lit.bool false)))])
              false)]))])

/-- All items of `spec/mem/tree_borrows/state_machine_protected.md`, in source order, with provenance. -/
def items : List SourceItem :=
  [
    (SourceItem.mk
      "enum_PermissionProt"
      7
      "fce176a7474e0c4501c5ac6b2e3707d1f8e576943ff051db1363f91e0acfb6a2"
      enum_PermissionProt),
    (SourceItem.mk
      "impl_PermissionProt__local_read"
      28
      "00df1cac64016be816a53402b6057198e3aea356ee11ec877886bcfe1aff0de2"
      impl_PermissionProt__local_read),
    (SourceItem.mk
      "impl_PermissionProt__unprotect"
      111
      "7901f60b3f29330b8f3b150919b1715884635474b501c2719b978f4b43b10cba"
      impl_PermissionProt__unprotect)]

end MiniRustSpec.Gen.Items.Mem.TreeBorrows.StateMachineProtected
