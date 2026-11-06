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
`spec/mem/tree_borrows/state_machine_unprotected.md` (commit `d821c6e3`), one Lean definition per item, in source order.
-/

import MiniRustSpec.Meta.Syntax

set_option maxRecDepth 100000

namespace MiniRustSpec.Gen.Items.Mem.TreeBorrows.StateMachineUnprotected

open MiniRustSpec.Syntax

/-- Path of the upstream file these items were extracted from. -/
def sourceFile : String := "spec/mem/tree_borrows/state_machine_unprotected.md"

/-- SHA-256 of the upstream file. -/
def sourceSha256 : String := "956688821b81db8912a5847730bd9f3aa439e79f727b29dc95e58f8e1b1e9335"

/-- `spec/mem/tree_borrows/state_machine_unprotected.md:6` -/
def enum_PermissionUnprot : Item :=
  (Item.enum
    []
    Visibility.inherited
    "PermissionUnprot"
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
            (AttrMeta.nameValue " Represents a two-phase borrow during its reservation phase"))]
        "Reserved"
        Fields.unit
        none),
      (Variant.mk
        [
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue
              " Represents a interior mutable two-phase borrow during its reservation phase"))]
        "ReservedIm"
        Fields.unit
        none),
      (Variant.mk
        [
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue
              " Represents an activated (written to) mutable reference, i.e. it must actually be unique right now"))]
        "Unique"
        Fields.unit
        none),
      (Variant.mk
        [(Attr.mk true "doc" (AttrMeta.nameValue " Represents a shared (immutable) reference"))]
        "Frozen"
        Fields.unit
        none),
      (Variant.mk
        [(Attr.mk true "doc" (AttrMeta.nameValue " Represents a dead reference"))]
        "Disabled"
        Fields.unit
        none)])

/-- `spec/mem/tree_borrows/state_machine_unprotected.md:26` -/
def impl_PermissionUnprot__local_read : Item :=
  (Item.impl
    []
    false
    false
    (Generics.mk [] [])
    false
    none
    (Ty.path none (Path.mk false [(PathSegment.mk "PermissionUnprot" PathArguments.none)]))
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
                            (Path.mk false [(PathSegment.mk "PermissionUnprot" PathArguments.none)])))]))]))))
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
                        (Pat.path
                          none
                          (Path.mk
                            false
                            [
                              (PathSegment.mk "PermissionUnprot" PathArguments.none),
                              (PathSegment.mk "Disabled" PathArguments.none)]))
                        none
                        (Expr.macro
                          (Macro.mk
                            (Path.mk false [(PathSegment.mk "throw_ub" PathArguments.none)])
                            MacroDelimiter.paren
                            (MacroBody.exprs
                              [
                                (Expr.lit
                                  (Lit.str "Tree Borrows: local read of Disabled reference"))]
                              false)))),
                      (Arm.mk
                        []
                        (Pat.ident false false "perm" none)
                        none
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "perm" PathArguments.none)])))])])
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
                            (Path.mk false [(PathSegment.mk "PermissionUnprot" PathArguments.none)])))]))]))))
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
                          (PathSegment.mk "PermissionUnprot" PathArguments.none),
                          (PathSegment.mk "Frozen" PathArguments.none)]))
                    none
                    (Expr.macro
                      (Macro.mk
                        (Path.mk false [(PathSegment.mk "throw_ub" PathArguments.none)])
                        MacroDelimiter.paren
                        (MacroBody.exprs
                          [(Expr.lit (Lit.str "Tree Borrows: local write of Frozen reference"))]
                          false)))),
                  (Arm.mk
                    []
                    (Pat.path
                      none
                      (Path.mk
                        false
                        [
                          (PathSegment.mk "PermissionUnprot" PathArguments.none),
                          (PathSegment.mk "Disabled" PathArguments.none)]))
                    none
                    (Expr.macro
                      (Macro.mk
                        (Path.mk false [(PathSegment.mk "throw_ub" PathArguments.none)])
                        MacroDelimiter.paren
                        (MacroBody.exprs
                          [(Expr.lit (Lit.str "Tree Borrows: local write of Disabled reference"))]
                          false)))),
                  (Arm.mk
                    []
                    (Pat.path
                      none
                      (Path.mk
                        false
                        [
                          (PathSegment.mk "PermissionUnprot" PathArguments.none),
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
                              (PathSegment.mk "PermissionUnprot" PathArguments.none),
                              (PathSegment.mk "Cell" PathArguments.none)]))])),
                  (Arm.mk
                    []
                    Pat.wild
                    none
                    (Expr.call
                      (Expr.path none (Path.mk false [(PathSegment.mk "ret" PathArguments.none)]))
                      [
                        (Expr.path
                          none
                          (Path.mk
                            false
                            [
                              (PathSegment.mk "PermissionUnprot" PathArguments.none),
                              (PathSegment.mk "Unique" PathArguments.none)]))]))])
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
                            (Path.mk false [(PathSegment.mk "PermissionUnprot" PathArguments.none)])))]))]))))
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
                          (PathSegment.mk "PermissionUnprot" PathArguments.none),
                          (PathSegment.mk "Reserved" PathArguments.none)]))
                    none
                    (Expr.call
                      (Expr.path none (Path.mk false [(PathSegment.mk "ret" PathArguments.none)]))
                      [
                        (Expr.path
                          none
                          (Path.mk
                            false
                            [
                              (PathSegment.mk "PermissionUnprot" PathArguments.none),
                              (PathSegment.mk "Reserved" PathArguments.none)]))])),
                  (Arm.mk
                    []
                    (Pat.path
                      none
                      (Path.mk
                        false
                        [
                          (PathSegment.mk "PermissionUnprot" PathArguments.none),
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
                              (PathSegment.mk "PermissionUnprot" PathArguments.none),
                              (PathSegment.mk "Frozen" PathArguments.none)]))])),
                  (Arm.mk
                    []
                    (Pat.ident false false "perm" none)
                    none
                    (Expr.call
                      (Expr.path none (Path.mk false [(PathSegment.mk "ret" PathArguments.none)]))
                      [
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "perm" PathArguments.none)]))]))])
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
                            (Path.mk false [(PathSegment.mk "PermissionUnprot" PathArguments.none)])))]))]))))
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
                          (PathSegment.mk "PermissionUnprot" PathArguments.none),
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
                              (PathSegment.mk "PermissionUnprot" PathArguments.none),
                              (PathSegment.mk "Cell" PathArguments.none)]))])),
                  (Arm.mk
                    []
                    (Pat.path
                      none
                      (Path.mk
                        false
                        [
                          (PathSegment.mk "PermissionUnprot" PathArguments.none),
                          (PathSegment.mk "ReservedIm" PathArguments.none)]))
                    none
                    (Expr.call
                      (Expr.path none (Path.mk false [(PathSegment.mk "ret" PathArguments.none)]))
                      [
                        (Expr.path
                          none
                          (Path.mk
                            false
                            [
                              (PathSegment.mk "PermissionUnprot" PathArguments.none),
                              (PathSegment.mk "ReservedIm" PathArguments.none)]))])),
                  (Arm.mk
                    []
                    Pat.wild
                    none
                    (Expr.call
                      (Expr.path none (Path.mk false [(PathSegment.mk "ret" PathArguments.none)]))
                      [
                        (Expr.path
                          none
                          (Path.mk
                            false
                            [
                              (PathSegment.mk "PermissionUnprot" PathArguments.none),
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
                            (Path.mk false [(PathSegment.mk "PermissionUnprot" PathArguments.none)])))]))]))))
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
              " This method is never called because we first check whether there is a strong protector,")),
          (Attr.mk true "doc" (AttrMeta.nameValue " but it is here anyways for consistency."))]
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
        (Block.mk [(Stmt.expr (Expr.lit (Lit.bool false)) false)])),
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
                          (PathSegment.mk "PermissionUnprot" PathArguments.none),
                          (PathSegment.mk "Cell" PathArguments.none)]))
                    none
                    (Expr.path none (Path.mk false [(PathSegment.mk "None" PathArguments.none)]))),
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

/-- All items of `spec/mem/tree_borrows/state_machine_unprotected.md`, in source order, with provenance. -/
def items : List SourceItem :=
  [
    (SourceItem.mk
      "enum_PermissionUnprot"
      6
      "3a1b8c5eb184b8445cebd41dc44c6ef7a6b686bb9a70290bb7d391042f67f27f"
      enum_PermissionUnprot),
    (SourceItem.mk
      "impl_PermissionUnprot__local_read"
      26
      "96ce5390412389689598d601e8d621a28fea56ec8f8f5ec1e7c2169cf1253dab"
      impl_PermissionUnprot__local_read)]

end MiniRustSpec.Gen.Items.Mem.TreeBorrows.StateMachineUnprotected
