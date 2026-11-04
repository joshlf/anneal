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
`spec/mem/tree_borrows/tree.md` (commit `d821c6e3`), one Lean definition per item, in source order.
-/

import MiniRustSpec.Meta.Syntax

set_option maxRecDepth 100000

namespace MiniRustSpec.Gen.Items.Mem.TreeBorrows.Tree

open MiniRustSpec.Syntax

/-- Path of the upstream file these items were extracted from. -/
def sourceFile : String := "spec/mem/tree_borrows/tree.md"

/-- SHA-256 of the upstream file. -/
def sourceSha256 : String := "67e3d2e245ffc752ee2ec4f82bdf928a23c6345926436b22a041546aa32ff988"

/-- `spec/mem/tree_borrows/tree.md:14` -/
def enum_Protected : Item :=
  (Item.enum
    []
    Visibility.inherited
    "Protected"
    (Generics.mk [] [])
    [
      (Variant.mk [] "Strong" Fields.unit none),
      (Variant.mk [] "Weak" Fields.unit none),
      (Variant.mk [] "No" Fields.unit none)])

/-- `spec/mem/tree_borrows/tree.md:20` -/
def impl_Protected__yes : Item :=
  (Item.impl
    []
    false
    false
    (Generics.mk [] [])
    false
    none
    (Ty.path none (Path.mk false [(PathSegment.mk "Protected" PathArguments.none)]))
    [
      (ImplItem.fn
        [
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue " Check whether the node is either strongly or weakly protected."))]
        Visibility.inherited
        false
        (Signature.mk
          false
          false
          false
          none
          "yes"
          (Generics.mk [] [])
          [(FnArg.receiver [] false none false none)]
          false
          (some (Ty.path none (Path.mk false [(PathSegment.mk "bool" PathArguments.none)]))))
        (Block.mk
          [
            (Stmt.expr
              (Expr.binary
                (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                BinOp.ne
                (Expr.path
                  none
                  (Path.mk
                    false
                    [
                      (PathSegment.mk "Protected" PathArguments.none),
                      (PathSegment.mk "No" PathArguments.none)])))
              false)]))])

/-- `spec/mem/tree_borrows/tree.md:31` -/
def struct_Node : Item :=
  (Item.struct
    []
    Visibility.inherited
    "Node"
    (Generics.mk [] [])
    (Fields.named
      [
        (Field.mk
          []
          Visibility.inherited
          (some "children")
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
                        (Ty.path none (Path.mk false [(PathSegment.mk "Node" PathArguments.none)])))]))]))),
        (Field.mk
          [(Attr.mk true "doc" (AttrMeta.nameValue " State for each location."))]
          Visibility.inherited
          (some "permissions")
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
                          (Path.mk false [(PathSegment.mk "Permission" PathArguments.none)])))]))]))),
        (Field.mk
          [
            (Attr.mk
              true
              "doc"
              (AttrMeta.nameValue " Indicates whether the node is protected by a function call,")),
            (Attr.mk
              true
              "doc"
              (AttrMeta.nameValue
                " i.e., whether the original reference passed as an argument of a function call.")),
            (Attr.mk
              true
              "doc"
              (AttrMeta.nameValue
                " This will be some kind of protection (weak or strong) if and only if this node is in")),
            (Attr.mk true "doc" (AttrMeta.nameValue " some frame's `extra.protectors` list.")),
            (Attr.mk
              true
              "doc"
              (AttrMeta.nameValue
                " There is an invariant between this field and the `permissions`:")),
            (Attr.mk
              true
              "doc"
              (AttrMeta.nameValue
                " If `protected.yes()`, then all states in `permissions` must be `Permission::Prot()`.")),
            (Attr.mk
              true
              "doc"
              (AttrMeta.nameValue
                " If `!protected.yes()`, they must all be `Permission::Unprot()`."))]
          Visibility.inherited
          (some "protected")
          (Ty.path none (Path.mk false [(PathSegment.mk "Protected" PathArguments.none)])))]))

/-- `spec/mem/tree_borrows/tree.md:51` -/
def enum_NodeRelation : Item :=
  (Item.enum
    []
    Visibility.inherited
    "NodeRelation"
    (Generics.mk [] [])
    [(Variant.mk [] "Local" Fields.unit none), (Variant.mk [] "Foreign" Fields.unit none)])

/-- `spec/mem/tree_borrows/tree.md:60` -/
def enum_AccessKind : Item :=
  (Item.enum
    []
    Visibility.inherited
    "AccessKind"
    (Generics.mk [] [])
    [(Variant.mk [] "Read" Fields.unit none), (Variant.mk [] "Write" Fields.unit none)])

/-- `spec/mem/tree_borrows/tree.md:69` -/
def impl_Node__transition : Item :=
  (Item.impl
    []
    false
    false
    (Generics.mk [] [])
    false
    none
    (Ty.path none (Path.mk false [(PathSegment.mk "Node" PathArguments.none)]))
    [
      (ImplItem.fn
        [
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue " Perform state transition on all locations of `self`.")),
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue
              " The `node_relation` indicates whether the accessed node is a local or foreign")),
          (Attr.mk true "doc" (AttrMeta.nameValue " *from the perspective of `self`*."))]
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
              (Pat.ident false false "node_relation" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "NodeRelation" PathArguments.none)]))),
            (FnArg.typed
              []
              (Pat.ident false false "access_kind" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "AccessKind" PathArguments.none)]))),
            (FnArg.typed
              []
              (Pat.ident false false "offset_in_alloc" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "Offset" PathArguments.none)]))),
            (FnArg.typed
              []
              (Pat.ident false false "size" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "Size" PathArguments.none)])))]
          false
          (some (Ty.path none (Path.mk false [(PathSegment.mk "Result" PathArguments.none)]))))
        (Block.mk
          [
            (Stmt.letStmt
              []
              (Pat.ident false false "offset_start" none)
              (some
                (Expr.methodCall
                  (Expr.path
                    none
                    (Path.mk false [(PathSegment.mk "offset_in_alloc" PathArguments.none)]))
                  "bytes"
                  none
                  []))
              none),
            (Stmt.expr
              (Expr.forLoop
                none
                (Pat.ident false false "offset" none)
                (Expr.range
                  (some
                    (Expr.path
                      none
                      (Path.mk false [(PathSegment.mk "offset_start" PathArguments.none)])))
                  RangeLimits.halfOpen
                  (some
                    (Expr.binary
                      (Expr.path
                        none
                        (Path.mk false [(PathSegment.mk "offset_start" PathArguments.none)]))
                      BinOp.add
                      (Expr.methodCall
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "size" PathArguments.none)]))
                        "bytes"
                        none
                        []))))
                (Block.mk
                  [
                    (Stmt.expr
                      (Expr.tryExpr
                        (Expr.methodCall
                          (Expr.field
                            (Expr.path
                              none
                              (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                            (Member.named "permissions"))
                          "mutate_at"
                          none
                          [
                            (Expr.path
                              none
                              (Path.mk false [(PathSegment.mk "offset" PathArguments.none)])),
                            (Expr.closure
                              false
                              [(Pat.ident false false "permission" none)]
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
                                            [(PathSegment.mk "permission" PathArguments.none)]))
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
                                              [(PathSegment.mk "node_relation" PathArguments.none)]))])
                                      false)])))]))
                      true)]))
              false),
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
            (AttrMeta.nameValue
              " Recusively do state transition on `self` node and all its descendants.")),
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue " `path` is the path from `self` to the accessed node.")),
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue
              " `path` is None when the accessed node is not a descendant of `self`.")),
          (Attr.mk true "doc" (AttrMeta.nameValue "")),
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue
              " This method will throw UBs, representing the undefined behavior captured by Tree Borrows."))]
        Visibility.inherited
        false
        (Signature.mk
          false
          false
          false
          none
          "access"
          (Generics.mk [] [])
          [
            (FnArg.receiver [] true none true none),
            (FnArg.typed
              []
              (Pat.ident false false "path" none)
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
                              (Path.mk false [(PathSegment.mk "Path" PathArguments.none)])))]))]))),
            (FnArg.typed
              []
              (Pat.ident false false "access_kind" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "AccessKind" PathArguments.none)]))),
            (FnArg.typed
              []
              (Pat.ident false false "offset_in_alloc" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "Offset" PathArguments.none)]))),
            (FnArg.typed
              []
              (Pat.ident false false "size" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "Size" PathArguments.none)])))]
          false
          (some (Ty.path none (Path.mk false [(PathSegment.mk "Result" PathArguments.none)]))))
        (Block.mk
          [
            (Stmt.letStmt
              []
              (Pat.ident false false "node_relation" none)
              (some
                (Expr.ite
                  (Expr.methodCall
                    (Expr.path none (Path.mk false [(PathSegment.mk "path" PathArguments.none)]))
                    "is_some"
                    none
                    [])
                  (Block.mk
                    [
                      (Stmt.expr
                        (Expr.path
                          none
                          (Path.mk
                            false
                            [
                              (PathSegment.mk "NodeRelation" PathArguments.none),
                              (PathSegment.mk "Local" PathArguments.none)]))
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
                                [
                                  (PathSegment.mk "NodeRelation" PathArguments.none),
                                  (PathSegment.mk "Foreign" PathArguments.none)]))
                            false)])))))
              none),
            (Stmt.expr
              (Expr.tryExpr
                (Expr.methodCall
                  (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                  "transition"
                  none
                  [
                    (Expr.path
                      none
                      (Path.mk false [(PathSegment.mk "node_relation" PathArguments.none)])),
                    (Expr.path
                      none
                      (Path.mk false [(PathSegment.mk "access_kind" PathArguments.none)])),
                    (Expr.path
                      none
                      (Path.mk false [(PathSegment.mk "offset_in_alloc" PathArguments.none)])),
                    (Expr.path none (Path.mk false [(PathSegment.mk "size" PathArguments.none)]))]))
              true),
            (Stmt.expr
              (Expr.forLoop
                none
                (Pat.ident false false "child_id" none)
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
                          (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                        (Member.named "children"))
                      "len"
                      none
                      [])))
                (Block.mk
                  [
                    (Stmt.letStmt
                      []
                      (Pat.ident false false "sub_path" none)
                      (some
                        (Expr.matchExpr
                          (Expr.methodCall
                            (Expr.path
                              none
                              (Path.mk false [(PathSegment.mk "path" PathArguments.none)]))
                            "and_then"
                            none
                            [
                              (Expr.closure
                                false
                                [(Pat.ident false false "p" none)]
                                none
                                (Expr.methodCall
                                  (Expr.path
                                    none
                                    (Path.mk false [(PathSegment.mk "p" PathArguments.none)]))
                                  "split_first"
                                  none
                                  []))])
                          [
                            (Arm.mk
                              []
                              (Pat.tupleStruct
                                none
                                (Path.mk false [(PathSegment.mk "Some" PathArguments.none)])
                                [
                                  (Pat.tuple
                                    [
                                      (Pat.ident false false "head" none),
                                      (Pat.ident false false "tail" none)])])
                              (some
                                (Expr.binary
                                  (Expr.path
                                    none
                                    (Path.mk false [(PathSegment.mk "head" PathArguments.none)]))
                                  BinOp.eq
                                  (Expr.path
                                    none
                                    (Path.mk false [(PathSegment.mk "child_id" PathArguments.none)]))))
                              (Expr.call
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "Some" PathArguments.none)]))
                                [
                                  (Expr.path
                                    none
                                    (Path.mk false [(PathSegment.mk "tail" PathArguments.none)]))])),
                            (Arm.mk
                              []
                              Pat.wild
                              none
                              (Expr.path
                                none
                                (Path.mk false [(PathSegment.mk "None" PathArguments.none)])))]))
                      none),
                    (Stmt.expr
                      (Expr.tryExpr
                        (Expr.methodCall
                          (Expr.field
                            (Expr.path
                              none
                              (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                            (Member.named "children"))
                          "mutate_at"
                          none
                          [
                            (Expr.path
                              none
                              (Path.mk false [(PathSegment.mk "child_id" PathArguments.none)])),
                            (Expr.closure
                              false
                              [(Pat.ident false false "child" none)]
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
                                            [(PathSegment.mk "child" PathArguments.none)]))
                                        "access"
                                        none
                                        [
                                          (Expr.path
                                            none
                                            (Path.mk
                                              false
                                              [(PathSegment.mk "sub_path" PathArguments.none)])),
                                          (Expr.path
                                            none
                                            (Path.mk
                                              false
                                              [(PathSegment.mk "access_kind" PathArguments.none)])),
                                          (Expr.path
                                            none
                                            (Path.mk
                                              false
                                              [
                                                (PathSegment.mk
                                                  "offset_in_alloc"
                                                  PathArguments.none)])),
                                          (Expr.path
                                            none
                                            (Path.mk
                                              false
                                              [(PathSegment.mk "size" PathArguments.none)]))])
                                      false)])))]))
                      true)]))
              false),
            (Stmt.expr
              (Expr.call
                (Expr.path none (Path.mk false [(PathSegment.mk "ret" PathArguments.none)]))
                [(Expr.tuple [])])
              false)]))])

/-- `spec/mem/tree_borrows/tree.md:132` -/
def impl_Node__access_node : Item :=
  (Item.impl
    []
    false
    false
    (Generics.mk [] [])
    false
    none
    (Ty.path none (Path.mk false [(PathSegment.mk "Node" PathArguments.none)]))
    [
      (ImplItem.fn
        [
          (Attr.mk true "doc" (AttrMeta.nameValue " Apply `f` to a child node of `self`")),
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue " `path` is the path from `self` to the target child node."))]
        Visibility.inherited
        false
        (Signature.mk
          false
          false
          false
          none
          "access_node"
          (Generics.mk [(GenericParam.type [] "O" [] none)] [])
          [
            (FnArg.receiver [] true none true none),
            (FnArg.typed
              []
              (Pat.ident false false "path" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "Path" PathArguments.none)]))),
            (FnArg.typed
              []
              (Pat.ident false false "f" none)
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
                          "FnOnce"
                          (PathArguments.parenthesized
                            [
                              (Ty.reference
                                none
                                true
                                (Ty.path
                                  none
                                  (Path.mk false [(PathSegment.mk "Self" PathArguments.none)])))]
                            (some
                              (Ty.path
                                none
                                (Path.mk false [(PathSegment.mk "O" PathArguments.none)])))))]))]))]
          false
          (some (Ty.path none (Path.mk false [(PathSegment.mk "O" PathArguments.none)]))))
        (Block.mk
          [
            (Stmt.letStmt
              []
              (Pat.tupleStruct
                none
                (Path.mk false [(PathSegment.mk "Some" PathArguments.none)])
                [
                  (Pat.tuple
                    [
                      (Pat.ident false false "sub_root_id" none),
                      (Pat.ident false false "sub_path" none)])])
              (some
                (Expr.methodCall
                  (Expr.path none (Path.mk false [(PathSegment.mk "path" PathArguments.none)]))
                  "split_first"
                  none
                  []))
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
                                (Path.mk false [(PathSegment.mk "f" PathArguments.none)]))
                              [
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))])))
                        true)])))),
            (Stmt.expr
              (Expr.ite
                (Expr.methodCall
                  (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                  "is_leaf"
                  none
                  [])
                (Block.mk
                  [
                    (Stmt.macro
                      []
                      (Macro.mk
                        (Path.mk false [(PathSegment.mk "panic" PathArguments.none)])
                        MacroDelimiter.paren
                        (MacroBody.exprs
                          [(Expr.lit (Lit.str "Node::access_node: invalid node path"))]
                          false))
                      true)])
                none)
              false),
            (Stmt.expr
              (Expr.methodCall
                (Expr.field
                  (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                  (Member.named "children"))
                "mutate_at"
                none
                [
                  (Expr.path
                    none
                    (Path.mk false [(PathSegment.mk "sub_root_id" PathArguments.none)])),
                  (Expr.closure
                    false
                    [(Pat.ident false false "child" none)]
                    none
                    (Expr.methodCall
                      (Expr.path none (Path.mk false [(PathSegment.mk "child" PathArguments.none)]))
                      "access_node"
                      none
                      [
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "sub_path" PathArguments.none)])),
                        (Expr.path none (Path.mk false [(PathSegment.mk "f" PathArguments.none)]))]))])
              false)])),
      (ImplItem.fn
        [
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue " Add a new child node to the tree whose root is self")),
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue " `path` is the path from `self` to the parent of the `node`.")),
          (Attr.mk true "doc" (AttrMeta.nameValue "")),
          (Attr.mk true "doc" (AttrMeta.nameValue " Return the path from `self` to the `node`"))]
        Visibility.inherited
        false
        (Signature.mk
          false
          false
          false
          none
          "add_node"
          (Generics.mk [] [])
          [
            (FnArg.receiver [] true none true none),
            (FnArg.typed
              []
              (Pat.ident false false "parent_path" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "Path" PathArguments.none)]))),
            (FnArg.typed
              []
              (Pat.ident false false "child" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "Node" PathArguments.none)])))]
          false
          (some (Ty.path none (Path.mk false [(PathSegment.mk "Path" PathArguments.none)]))))
        (Block.mk
          [
            (Stmt.letStmt
              []
              (Pat.ident false false "child_idx" none)
              (some
                (Expr.methodCall
                  (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                  "access_node"
                  none
                  [
                    (Expr.path
                      none
                      (Path.mk false [(PathSegment.mk "parent_path" PathArguments.none)])),
                    (Expr.closure
                      false
                      [(Pat.ident false false "node" none)]
                      none
                      (Expr.block
                        none
                        (Block.mk
                          [
                            (Stmt.letStmt
                              []
                              (Pat.ident false false "child_idx" none)
                              (some
                                (Expr.methodCall
                                  (Expr.field
                                    (Expr.path
                                      none
                                      (Path.mk false [(PathSegment.mk "node" PathArguments.none)]))
                                    (Member.named "children"))
                                  "len"
                                  none
                                  []))
                              none),
                            (Stmt.expr
                              (Expr.methodCall
                                (Expr.field
                                  (Expr.path
                                    none
                                    (Path.mk false [(PathSegment.mk "node" PathArguments.none)]))
                                  (Member.named "children"))
                                "push"
                                none
                                [
                                  (Expr.path
                                    none
                                    (Path.mk false [(PathSegment.mk "child" PathArguments.none)]))])
                              true),
                            (Stmt.expr
                              (Expr.path
                                none
                                (Path.mk false [(PathSegment.mk "child_idx" PathArguments.none)]))
                              false)])))]))
              none),
            (Stmt.letStmt
              []
              (Pat.ident false true "child_path" none)
              (some
                (Expr.path none (Path.mk false [(PathSegment.mk "parent_path" PathArguments.none)])))
              none),
            (Stmt.expr
              (Expr.methodCall
                (Expr.path none (Path.mk false [(PathSegment.mk "child_path" PathArguments.none)]))
                "push"
                none
                [(Expr.path none (Path.mk false [(PathSegment.mk "child_idx" PathArguments.none)]))])
              true),
            (Stmt.expr
              (Expr.path none (Path.mk false [(PathSegment.mk "child_path" PathArguments.none)]))
              false)])),
      (ImplItem.fn
        [(Attr.mk true "doc" (AttrMeta.nameValue " Check whether `self` is a leaf."))]
        Visibility.inherited
        false
        (Signature.mk
          false
          false
          false
          none
          "is_leaf"
          (Generics.mk [] [])
          [(FnArg.receiver [] true none false none)]
          false
          (some (Ty.path none (Path.mk false [(PathSegment.mk "bool" PathArguments.none)]))))
        (Block.mk
          [
            (Stmt.expr
              (Expr.binary
                (Expr.methodCall
                  (Expr.field
                    (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                    (Member.named "children"))
                  "len"
                  none
                  [])
                BinOp.eq
                (Expr.path
                  none
                  (Path.mk
                    false
                    [
                      (PathSegment.mk "Int" PathArguments.none),
                      (PathSegment.mk "ZERO" PathArguments.none)])))
              false)]))])

/-- `spec/mem/tree_borrows/tree.md:175` -/
def impl_Node__release_protector : Item :=
  (Item.impl
    []
    false
    false
    (Generics.mk [] [])
    false
    none
    (Ty.path none (Path.mk false [(PathSegment.mk "Node" PathArguments.none)]))
    [
      (ImplItem.fn
        [
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue
              " Release the protector, and perform a special access for the protector end semantics.")),
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue
              " Recusively do state transition on all foreigns of the protected node.")),
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue " `path` is the path from `self` to the proctected node.")),
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue
              " `path` is None when the protected node is not a descendant of `self`.")),
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue " `accesses` describes which access happens at which offset."))]
        Visibility.inherited
        false
        (Signature.mk
          false
          false
          false
          none
          "release_protector"
          (Generics.mk [] [])
          [
            (FnArg.receiver [] true none true none),
            (FnArg.typed
              []
              (Pat.ident false false "path" none)
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
                              (Path.mk false [(PathSegment.mk "Path" PathArguments.none)])))]))]))),
            (FnArg.typed
              []
              (Pat.ident false false "accesses" none)
              (Ty.reference
                none
                false
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
                                      "Option"
                                      (PathArguments.angleBracketed
                                        false
                                        [
                                          (GenericArgument.type
                                            (Ty.path
                                              none
                                              (Path.mk
                                                false
                                                [(PathSegment.mk "AccessKind" PathArguments.none)])))]))])))]))]))))]
          false
          (some (Ty.path none (Path.mk false [(PathSegment.mk "Result" PathArguments.none)]))))
        (Block.mk
          [
            (Stmt.letStmt
              []
              (Pat.ident false false "node_relation" none)
              (some
                (Expr.ite
                  (Expr.methodCall
                    (Expr.path none (Path.mk false [(PathSegment.mk "path" PathArguments.none)]))
                    "is_some"
                    none
                    [])
                  (Block.mk
                    [
                      (Stmt.expr
                        (Expr.path
                          none
                          (Path.mk
                            false
                            [
                              (PathSegment.mk "NodeRelation" PathArguments.none),
                              (PathSegment.mk "Local" PathArguments.none)]))
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
                                [
                                  (PathSegment.mk "NodeRelation" PathArguments.none),
                                  (PathSegment.mk "Foreign" PathArguments.none)]))
                            false)])))))
              none),
            (Stmt.expr
              (Expr.ite
                (Expr.methodCall
                  (Expr.path none (Path.mk false [(PathSegment.mk "path" PathArguments.none)]))
                  "is_some_and"
                  none
                  [
                    (Expr.closure
                      false
                      [(Pat.ident false false "p" none)]
                      none
                      (Expr.methodCall
                        (Expr.path none (Path.mk false [(PathSegment.mk "p" PathArguments.none)]))
                        "is_empty"
                        none
                        []))])
                (Block.mk
                  [
                    (Stmt.expr
                      (Expr.assign
                        (Expr.field
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                          (Member.named "protected"))
                        (Expr.path
                          none
                          (Path.mk
                            false
                            [
                              (PathSegment.mk "Protected" PathArguments.none),
                              (PathSegment.mk "No" PathArguments.none)])))
                      true),
                    (Stmt.expr
                      (Expr.returnExpr
                        (some
                          (Expr.call
                            (Expr.path
                              none
                              (Path.mk false [(PathSegment.mk "ret" PathArguments.none)]))
                            [(Expr.tuple [])])))
                      true)])
                none)
              false),
            (Stmt.expr
              (Expr.forLoop
                none
                (Pat.tuple
                  [(Pat.ident false false "offset" none), (Pat.ident false false "access" none)])
                (Expr.methodCall
                  (Expr.methodCall
                    (Expr.path
                      none
                      (Path.mk false [(PathSegment.mk "accesses" PathArguments.none)]))
                    "iter"
                    none
                    [])
                  "enumerate"
                  none
                  [])
                (Block.mk
                  [
                    (Stmt.letStmt
                      []
                      (Pat.tupleStruct
                        none
                        (Path.mk false [(PathSegment.mk "Some" PathArguments.none)])
                        [(Pat.ident false false "access" none)])
                      (some
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "access" PathArguments.none)])))
                      (some (Expr.block none (Block.mk [(Stmt.expr (Expr.continue none) false)])))),
                    (Stmt.expr
                      (Expr.tryExpr
                        (Expr.methodCall
                          (Expr.field
                            (Expr.path
                              none
                              (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                            (Member.named "permissions"))
                          "mutate_at"
                          none
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
                                  (Path.mk false [(PathSegment.mk "offset" PathArguments.none)]))]),
                            (Expr.closure
                              false
                              [(Pat.ident false false "permission" none)]
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
                                            [(PathSegment.mk "permission" PathArguments.none)]))
                                        "transition"
                                        none
                                        [
                                          (Expr.path
                                            none
                                            (Path.mk
                                              false
                                              [(PathSegment.mk "access" PathArguments.none)])),
                                          (Expr.path
                                            none
                                            (Path.mk
                                              false
                                              [(PathSegment.mk "node_relation" PathArguments.none)]))])
                                      false)])))]))
                      true)]))
              false),
            (Stmt.expr
              (Expr.forLoop
                none
                (Pat.ident false false "child_id" none)
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
                          (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                        (Member.named "children"))
                      "len"
                      none
                      [])))
                (Block.mk
                  [
                    (Stmt.letStmt
                      []
                      (Pat.ident false false "sub_path" none)
                      (some
                        (Expr.matchExpr
                          (Expr.methodCall
                            (Expr.path
                              none
                              (Path.mk false [(PathSegment.mk "path" PathArguments.none)]))
                            "and_then"
                            none
                            [
                              (Expr.closure
                                false
                                [(Pat.ident false false "p" none)]
                                none
                                (Expr.methodCall
                                  (Expr.path
                                    none
                                    (Path.mk false [(PathSegment.mk "p" PathArguments.none)]))
                                  "split_first"
                                  none
                                  []))])
                          [
                            (Arm.mk
                              []
                              (Pat.tupleStruct
                                none
                                (Path.mk false [(PathSegment.mk "Some" PathArguments.none)])
                                [
                                  (Pat.tuple
                                    [
                                      (Pat.ident false false "head" none),
                                      (Pat.ident false false "tail" none)])])
                              (some
                                (Expr.binary
                                  (Expr.path
                                    none
                                    (Path.mk false [(PathSegment.mk "head" PathArguments.none)]))
                                  BinOp.eq
                                  (Expr.path
                                    none
                                    (Path.mk false [(PathSegment.mk "child_id" PathArguments.none)]))))
                              (Expr.call
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "Some" PathArguments.none)]))
                                [
                                  (Expr.path
                                    none
                                    (Path.mk false [(PathSegment.mk "tail" PathArguments.none)]))])),
                            (Arm.mk
                              []
                              Pat.wild
                              none
                              (Expr.path
                                none
                                (Path.mk false [(PathSegment.mk "None" PathArguments.none)])))]))
                      none),
                    (Stmt.expr
                      (Expr.tryExpr
                        (Expr.methodCall
                          (Expr.field
                            (Expr.path
                              none
                              (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                            (Member.named "children"))
                          "mutate_at"
                          none
                          [
                            (Expr.path
                              none
                              (Path.mk false [(PathSegment.mk "child_id" PathArguments.none)])),
                            (Expr.closure
                              false
                              [(Pat.ident false false "child" none)]
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
                                            [(PathSegment.mk "child" PathArguments.none)]))
                                        "release_protector"
                                        none
                                        [
                                          (Expr.path
                                            none
                                            (Path.mk
                                              false
                                              [(PathSegment.mk "sub_path" PathArguments.none)])),
                                          (Expr.path
                                            none
                                            (Path.mk
                                              false
                                              [(PathSegment.mk "accesses" PathArguments.none)]))])
                                      false)])))]))
                      true)]))
              false),
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
            (AttrMeta.nameValue
              " Recusively check whether there is a strongly protected node in `self` and all its descendants.")),
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue
              " This is used to reject deallocation as long as there's a strong protector anywhere.")),
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue
              " Note that not all strongly protected nodes prevent deallocation. Specifically, if all offsets in")),
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue
              " the allocation fulfill the following property, the strong protector is not considered:")),
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue " * the offset has `Cell` permission, i.e. is interior mutable, or")),
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue
              " * the offset was not accessed yet, i.e. the protector is not active at this offset.")),
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue
              " See `prevents_deallocation` which implements by actually looking at the permission.")),
          (Attr.mk true "doc" (AttrMeta.nameValue "")),
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue
              " Return true if there is a strongly protected node preventing deallocation."))]
        Visibility.inherited
        false
        (Signature.mk
          false
          false
          false
          none
          "contains_strong_protector_preventing_deallocation"
          (Generics.mk [] [])
          [(FnArg.receiver [] true none false none)]
          false
          (some (Ty.path none (Path.mk false [(PathSegment.mk "bool" PathArguments.none)]))))
        (Block.mk
          [
            (Stmt.expr
              (Expr.binary
                (Expr.paren
                  (Expr.binary
                    (Expr.binary
                      (Expr.field
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                        (Member.named "protected"))
                      BinOp.eq
                      (Expr.path
                        none
                        (Path.mk
                          false
                          [
                            (PathSegment.mk "Protected" PathArguments.none),
                            (PathSegment.mk "Strong" PathArguments.none)])))
                    BinOp.and
                    (Expr.methodCall
                      (Expr.field
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                        (Member.named "permissions"))
                      "any"
                      none
                      [
                        (Expr.closure
                          false
                          [(Pat.ident false false "st" none)]
                          none
                          (Expr.methodCall
                            (Expr.path
                              none
                              (Path.mk false [(PathSegment.mk "st" PathArguments.none)]))
                            "prevents_deallocation"
                            none
                            []))])))
                BinOp.or
                (Expr.methodCall
                  (Expr.field
                    (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                    (Member.named "children"))
                  "any"
                  none
                  [
                    (Expr.closure
                      false
                      [(Pat.ident false false "child" none)]
                      none
                      (Expr.methodCall
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "child" PathArguments.none)]))
                        "contains_strong_protector_preventing_deallocation"
                        none
                        []))]))
              false)]))])

/-- All items of `spec/mem/tree_borrows/tree.md`, in source order, with provenance. -/
def items : List SourceItem :=
  [
    (SourceItem.mk
      "enum_Protected"
      14
      "2f85372d0f3cf32081358f9ec0d11cf57f0c819e1cdce8afd2a5ba5dd30eb99a"
      enum_Protected),
    (SourceItem.mk
      "impl_Protected__yes"
      20
      "8556c0e7d6e8d487f8b4f872bf67b2987350aab02ff178d0a59215f5789abc3b"
      impl_Protected__yes),
    (SourceItem.mk
      "struct_Node"
      31
      "a95ddddbc9ce9acef4ef64d6e89e3fe91c0f903aa38cbcd0a6c958777779b882"
      struct_Node),
    (SourceItem.mk
      "enum_NodeRelation"
      51
      "72c90d314b7091cea65201c1373debfd4e7b0070239127510f981c96ff092e88"
      enum_NodeRelation),
    (SourceItem.mk
      "enum_AccessKind"
      60
      "4dfd5ccef87a385e8e66005cd2951a53c1562220e01ec56547faec4800726233"
      enum_AccessKind),
    (SourceItem.mk
      "impl_Node__transition"
      69
      "e3e906529131371a05bf158af0e0b72421c27cdb3020e3aea63700d0fcb6e60d"
      impl_Node__transition),
    (SourceItem.mk
      "impl_Node__access_node"
      132
      "b903724d699f1b5a6d7fd261178cbdc620a2598628b672f6862e0335037aa16c"
      impl_Node__access_node),
    (SourceItem.mk
      "impl_Node__release_protector"
      175
      "2a8655943462032d33a0b20ea3acb827370deb839f9ada1855e2305e90b655ec"
      impl_Node__release_protector)]

end MiniRustSpec.Gen.Items.Mem.TreeBorrows.Tree
