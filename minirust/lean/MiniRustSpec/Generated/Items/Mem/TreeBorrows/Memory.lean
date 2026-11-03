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
`spec/mem/tree_borrows/memory.md` (commit `d821c6e3`), one Lean definition per item, in source order.
-/

import MiniRustSpec.Meta.Syntax

set_option maxRecDepth 100000

namespace MiniRustSpec.Gen.Items.Mem.TreeBorrows.Memory

open MiniRustSpec.Syntax

/-- Path of the upstream file these items were extracted from. -/
def sourceFile : String := "spec/mem/tree_borrows/memory.md"

/-- SHA-256 of the upstream file. -/
def sourceSha256 : String := "a61ffb69e23c0b0076c09e63ae9d1fa4843d0d5b2258b10c9c8d67bbc652fc2f"

/-- `spec/mem/tree_borrows/memory.md:14` -/
def struct_TreeBorrowsAllocationExtra : Item :=
  (Item.struct
    []
    Visibility.inherited
    "TreeBorrowsAllocationExtra"
    (Generics.mk [] [])
    (Fields.named
      [
        (Field.mk
          []
          Visibility.inherited
          (some "root")
          (Ty.path none (Path.mk false [(PathSegment.mk "Node" PathArguments.none)])))]))

/-- `spec/mem/tree_borrows/memory.md:38` -/
def type_ChildId : Item :=
  (Item.type
    [(Attr.mk true "doc" (AttrMeta.nameValue " The index of a child in the list of child nodes."))]
    Visibility.inherited
    "ChildId"
    (Generics.mk [] [])
    (Ty.path none (Path.mk false [(PathSegment.mk "Int" PathArguments.none)])))

/-- `spec/mem/tree_borrows/memory.md:40` -/
def type_Path : Item :=
  (Item.type
    [
      (Attr.mk
        true
        "doc"
        (AttrMeta.nameValue " A path from the root of a tree to some node inside the tree."))]
    Visibility.inherited
    "Path"
    (Generics.mk [] [])
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
                  (Ty.path none (Path.mk false [(PathSegment.mk "ChildId" PathArguments.none)])))]))])))

/-- `spec/mem/tree_borrows/memory.md:47` -/
def type_TreeBorrowsProvenance : Item :=
  (Item.type
    []
    Visibility.inherited
    "TreeBorrowsProvenance"
    (Generics.mk [] [])
    (Ty.tuple
      [
        (Ty.path none (Path.mk false [(PathSegment.mk "AllocId" PathArguments.none)])),
        (Ty.path none (Path.mk false [(PathSegment.mk "Path" PathArguments.none)]))]))

/-- `spec/mem/tree_borrows/memory.md:53` -/
def struct_TreeBorrowsParams : Item :=
  (Item.struct
    [
      (Attr.mk
        true
        "doc"
        (AttrMeta.nameValue " Global parameters controlling Tree Borrows behavior.")),
      (Attr.mk true "derive" (AttrMeta.list "Default"))]
    Visibility.pub
    "TreeBorrowsParams"
    (Generics.mk [] [])
    (Fields.named
      [
        (Field.mk
          [(Attr.mk true "doc" (AttrMeta.nameValue " Whether implicit writes are enabled or not."))]
          Visibility.pub
          (some "implicit_writes")
          (Ty.path none (Path.mk false [(PathSegment.mk "bool" PathArguments.none)])))]))

/-- `spec/mem/tree_borrows/memory.md:62` -/
def struct_TreeBorrowsMemory : Item :=
  (Item.struct
    []
    Visibility.pub
    "TreeBorrowsMemory"
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
    (Fields.named
      [
        (Field.mk
          []
          Visibility.inherited
          (some "params")
          (Ty.path none (Path.mk false [(PathSegment.mk "TreeBorrowsParams" PathArguments.none)]))),
        (Field.mk
          []
          Visibility.inherited
          (some "mem")
          (Ty.path
            none
            (Path.mk
              false
              [
                (PathSegment.mk
                  "BasicMemory"
                  (PathArguments.angleBracketed
                    false
                    [
                      (GenericArgument.type
                        (Ty.path none (Path.mk false [(PathSegment.mk "T" PathArguments.none)]))),
                      (GenericArgument.type
                        (Ty.path none (Path.mk false [(PathSegment.mk "Path" PathArguments.none)]))),
                      (GenericArgument.type
                        (Ty.path
                          none
                          (Path.mk
                            false
                            [(PathSegment.mk "TreeBorrowsAllocationExtra" PathArguments.none)])))]))])))]))

/-- `spec/mem/tree_borrows/memory.md:67` -/
def struct_TreeBorrowsFrameExtra : Item :=
  (Item.struct
    []
    Visibility.pub
    "TreeBorrowsFrameExtra"
    (Generics.mk [] [])
    (Fields.named
      [
        (Field.mk
          [
            (Attr.mk
              true
              "doc"
              (AttrMeta.nameValue
                " Our per-frame state is the list of nodes that are protected by this call."))]
          Visibility.inherited
          (some "protectors")
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
                            [(PathSegment.mk "TreeBorrowsProvenance" PathArguments.none)])))]))])))]))

/-- `spec/mem/tree_borrows/memory.md:72` -/
def impl_TreeBorrowsFrameExtra__new : Item :=
  (Item.impl
    []
    false
    false
    (Generics.mk [] [])
    false
    none
    (Ty.path none (Path.mk false [(PathSegment.mk "TreeBorrowsFrameExtra" PathArguments.none)]))
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
                    (Member.named "protectors")
                    false
                    (Expr.call
                      (Expr.path
                        none
                        (Path.mk
                          false
                          [
                            (PathSegment.mk "List" PathArguments.none),
                            (PathSegment.mk "new" PathArguments.none)]))
                      []))]
                false
                none)
              false)]))])

/-- `spec/mem/tree_borrows/memory.md:80` -/
def impl_TreeBorrowsMemory__reborrow : Item :=
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
              (Path.mk false [(PathSegment.mk "Target" PathArguments.none)]))]
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
            "TreeBorrowsMemory"
            (PathArguments.angleBracketed
              false
              [
                (GenericArgument.type
                  (Ty.path none (Path.mk false [(PathSegment.mk "T" PathArguments.none)])))]))]))
    [
      (ImplItem.fn
        [(Attr.mk true "doc" (AttrMeta.nameValue " Create a new node for a pointer (reborrow)"))]
        Visibility.inherited
        false
        (Signature.mk
          false
          false
          false
          none
          "reborrow"
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
                                [(PathSegment.mk "TreeBorrowsProvenance" PathArguments.none)])))]))]))),
            (FnArg.typed
              []
              (Pat.ident false false "settings" none)
              (Ty.path
                none
                (Path.mk false [(PathSegment.mk "ReborrowSettings" PathArguments.none)]))),
            (FnArg.typed
              []
              (Pat.ident false false "frame_extra" none)
              (Ty.reference
                none
                true
                (Ty.path
                  none
                  (Path.mk false [(PathSegment.mk "TreeBorrowsFrameExtra" PathArguments.none)]))))]
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
                                              (PathSegment.mk
                                                "TreeBorrowsProvenance"
                                                PathArguments.none)])))]))])))]))]))))
        (Block.mk
          [
            (Stmt.letStmt
              []
              (Pat.ident false false "pointee_size" none)
              (some
                (Expr.methodCall
                  (Expr.call
                    (Expr.path
                      none
                      (Path.mk
                        false
                        [
                          (PathSegment.mk "Size" PathArguments.none),
                          (PathSegment.mk "from_bytes" PathArguments.none)]))
                    [
                      (Expr.methodCall
                        (Expr.field
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "settings" PathArguments.none)]))
                          (Member.named "inside"))
                        "len"
                        none
                        [])])
                  "unwrap"
                  none
                  []))
              none),
            (Stmt.expr
              (Expr.tryExpr
                (Expr.methodCall
                  (Expr.field
                    (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                    (Member.named "mem"))
                  "check_ptr"
                  none
                  [
                    (Expr.path none (Path.mk false [(PathSegment.mk "ptr" PathArguments.none)])),
                    (Expr.path
                      none
                      (Path.mk false [(PathSegment.mk "pointee_size" PathArguments.none)]))]))
              true),
            (Stmt.letStmt
              []
              (Pat.tupleStruct
                none
                (Path.mk false [(PathSegment.mk "Some" PathArguments.none)])
                [
                  (Pat.tuple
                    [
                      (Pat.ident false false "alloc_id" none),
                      (Pat.ident false false "parent_path" none)])])
              (some
                (Expr.field
                  (Expr.path none (Path.mk false [(PathSegment.mk "ptr" PathArguments.none)]))
                  (Member.named "provenance")))
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
                                (Expr.path
                                  none
                                  (Path.mk
                                    false
                                    [(PathSegment.mk "pointee_size" PathArguments.none)]))
                                "is_zero"
                                none
                                [])]
                            false))
                        true),
                      (Stmt.expr
                        (Expr.returnExpr
                          (some
                            (Expr.call
                              (Expr.path
                                none
                                (Path.mk false [(PathSegment.mk "ret" PathArguments.none)]))
                              [
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "ptr" PathArguments.none)]))])))
                        true)])))),
            (Stmt.letStmt
              []
              (Pat.ident false false "child_path" none)
              (some
                (Expr.tryExpr
                  (Expr.methodCall
                    (Expr.field
                      (Expr.field
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                        (Member.named "mem"))
                      (Member.named "allocations"))
                    "mutate_at"
                    none
                    [
                      (Expr.field
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "alloc_id" PathArguments.none)]))
                        (Member.unnamed 0)),
                      (Expr.closure
                        false
                        [(Pat.ident false false "allocation" none)]
                        none
                        (Expr.block
                          none
                          (Block.mk
                            [
                              (Stmt.letStmt
                                []
                                (Pat.ident false false "alloc_size" none)
                                (some
                                  (Expr.methodCall
                                    (Expr.path
                                      none
                                      (Path.mk
                                        false
                                        [(PathSegment.mk "allocation" PathArguments.none)]))
                                    "size"
                                    none
                                    []))
                                none),
                              (Stmt.letStmt
                                []
                                (Pat.ident false false "offset" none)
                                (some
                                  (Expr.methodCall
                                    (Expr.call
                                      (Expr.path
                                        none
                                        (Path.mk
                                          false
                                          [
                                            (PathSegment.mk "Offset" PathArguments.none),
                                            (PathSegment.mk "from_bytes" PathArguments.none)]))
                                      [
                                        (Expr.binary
                                          (Expr.field
                                            (Expr.path
                                              none
                                              (Path.mk
                                                false
                                                [(PathSegment.mk "ptr" PathArguments.none)]))
                                            (Member.named "addr"))
                                          BinOp.sub
                                          (Expr.field
                                            (Expr.path
                                              none
                                              (Path.mk
                                                false
                                                [(PathSegment.mk "allocation" PathArguments.none)]))
                                            (Member.named "addr")))])
                                    "unwrap"
                                    none
                                    []))
                                none),
                              (Stmt.letStmt
                                []
                                (Pat.ident false true "permissions" none)
                                (some
                                  (Expr.macro
                                    (Macro.mk
                                      (Path.mk false [(PathSegment.mk "list" PathArguments.none)])
                                      MacroDelimiter.bracket
                                      (MacroBody.repeatList
                                        (Expr.field
                                          (Expr.path
                                            none
                                            (Path.mk
                                              false
                                              [(PathSegment.mk "settings" PathArguments.none)]))
                                          (Member.named "outside"))
                                        (Expr.methodCall
                                          (Expr.path
                                            none
                                            (Path.mk
                                              false
                                              [(PathSegment.mk "alloc_size" PathArguments.none)]))
                                          "bytes"
                                          none
                                          [])))))
                                none),
                              (Stmt.expr
                                (Expr.ite
                                  (Expr.binary
                                    (Expr.methodCall
                                      (Expr.field
                                        (Expr.path
                                          none
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "settings" PathArguments.none)]))
                                        (Member.named "inside"))
                                      "len"
                                      none
                                      [])
                                    BinOp.gt
                                    (Expr.lit (Lit.int 0 "")))
                                  (Block.mk
                                    [
                                      (Stmt.expr
                                        (Expr.methodCall
                                          (Expr.path
                                            none
                                            (Path.mk
                                              false
                                              [(PathSegment.mk "permissions" PathArguments.none)]))
                                          "write_subslice_at_index"
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
                                            (Expr.field
                                              (Expr.path
                                                none
                                                (Path.mk
                                                  false
                                                  [(PathSegment.mk "settings" PathArguments.none)]))
                                              (Member.named "inside"))])
                                        true)])
                                  none)
                                false),
                              (Stmt.letStmt
                                []
                                (Pat.ident false false "child_node" none)
                                (some
                                  (Expr.struct
                                    none
                                    (Path.mk false [(PathSegment.mk "Node" PathArguments.none)])
                                    [
                                      (FieldValue.mk
                                        []
                                        (Member.named "children")
                                        false
                                        (Expr.call
                                          (Expr.path
                                            none
                                            (Path.mk
                                              false
                                              [
                                                (PathSegment.mk "List" PathArguments.none),
                                                (PathSegment.mk "new" PathArguments.none)]))
                                          [])),
                                      (FieldValue.mk
                                        []
                                        (Member.named "permissions")
                                        true
                                        (Expr.path
                                          none
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "permissions" PathArguments.none)]))),
                                      (FieldValue.mk
                                        []
                                        (Member.named "protected")
                                        false
                                        (Expr.field
                                          (Expr.path
                                            none
                                            (Path.mk
                                              false
                                              [(PathSegment.mk "settings" PathArguments.none)]))
                                          (Member.named "protected")))]
                                    false
                                    none))
                                none),
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
                                            (Path.mk
                                              false
                                              [(PathSegment.mk "child_node" PathArguments.none)]))
                                          (Member.named "permissions"))
                                        "all"
                                        none
                                        [
                                          (Expr.closure
                                            false
                                            [(Pat.ident false false "x" none)]
                                            none
                                            (Expr.methodCall
                                              (Expr.path
                                                none
                                                (Path.mk
                                                  false
                                                  [(PathSegment.mk "x" PathArguments.none)]))
                                              "matches_protector"
                                              none
                                              [
                                                (Expr.field
                                                  (Expr.path
                                                    none
                                                    (Path.mk
                                                      false
                                                      [
                                                        (PathSegment.mk
                                                          "child_node"
                                                          PathArguments.none)]))
                                                  (Member.named "protected"))]))])]
                                    false))
                                true),
                              (Stmt.letStmt
                                []
                                (Pat.ident false false "child_path" none)
                                (some
                                  (Expr.methodCall
                                    (Expr.field
                                      (Expr.field
                                        (Expr.path
                                          none
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "allocation" PathArguments.none)]))
                                        (Member.named "extra"))
                                      (Member.named "root"))
                                    "add_node"
                                    none
                                    [
                                      (Expr.path
                                        none
                                        (Path.mk
                                          false
                                          [(PathSegment.mk "parent_path" PathArguments.none)])),
                                      (Expr.path
                                        none
                                        (Path.mk
                                          false
                                          [(PathSegment.mk "child_node" PathArguments.none)]))]))
                                none),
                              (Stmt.expr
                                (Expr.forLoop
                                  none
                                  (Pat.tuple
                                    [
                                      (Pat.ident false false "idx" none),
                                      (Pat.ident false false "perm" none)])
                                  (Expr.methodCall
                                    (Expr.methodCall
                                      (Expr.field
                                        (Expr.path
                                          none
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "settings" PathArguments.none)]))
                                        (Member.named "inside"))
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
                                        (Pat.ident false false "idx" none)
                                        (some
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
                                                (Path.mk
                                                  false
                                                  [(PathSegment.mk "idx" PathArguments.none)]))]))
                                        none),
                                      (Stmt.letStmt
                                        []
                                        (Pat.ident false false "idx" none)
                                        (some
                                          (Expr.methodCall
                                            (Expr.call
                                              (Expr.path
                                                none
                                                (Path.mk
                                                  false
                                                  [
                                                    (PathSegment.mk "Size" PathArguments.none),
                                                    (PathSegment.mk "from_bytes" PathArguments.none)]))
                                              [
                                                (Expr.path
                                                  none
                                                  (Path.mk
                                                    false
                                                    [(PathSegment.mk "idx" PathArguments.none)]))])
                                            "unwrap"
                                            none
                                            []))
                                        none),
                                      (Stmt.expr
                                        (Expr.ite
                                          (Expr.letCond
                                            (Pat.tupleStruct
                                              none
                                              (Path.mk
                                                false
                                                [(PathSegment.mk "Some" PathArguments.none)])
                                              [(Pat.ident false false "access" none)])
                                            (Expr.methodCall
                                              (Expr.path
                                                none
                                                (Path.mk
                                                  false
                                                  [(PathSegment.mk "perm" PathArguments.none)]))
                                              "init_access"
                                              none
                                              []))
                                          (Block.mk
                                            [
                                              (Stmt.expr
                                                (Expr.tryExpr
                                                  (Expr.methodCall
                                                    (Expr.field
                                                      (Expr.field
                                                        (Expr.path
                                                          none
                                                          (Path.mk
                                                            false
                                                            [
                                                              (PathSegment.mk
                                                                "allocation"
                                                                PathArguments.none)]))
                                                        (Member.named "extra"))
                                                      (Member.named "root"))
                                                    "access"
                                                    none
                                                    [
                                                      (Expr.call
                                                        (Expr.path
                                                          none
                                                          (Path.mk
                                                            false
                                                            [
                                                              (PathSegment.mk
                                                                "Some"
                                                                PathArguments.none)]))
                                                        [
                                                          (Expr.path
                                                            none
                                                            (Path.mk
                                                              false
                                                              [
                                                                (PathSegment.mk
                                                                  "child_path"
                                                                  PathArguments.none)]))]),
                                                      (Expr.path
                                                        none
                                                        (Path.mk
                                                          false
                                                          [
                                                            (PathSegment.mk
                                                              "access"
                                                              PathArguments.none)])),
                                                      (Expr.binary
                                                        (Expr.path
                                                          none
                                                          (Path.mk
                                                            false
                                                            [
                                                              (PathSegment.mk
                                                                "offset"
                                                                PathArguments.none)]))
                                                        BinOp.add
                                                        (Expr.path
                                                          none
                                                          (Path.mk
                                                            false
                                                            [
                                                              (PathSegment.mk
                                                                "idx"
                                                                PathArguments.none)]))),
                                                      (Expr.call
                                                        (Expr.path
                                                          none
                                                          (Path.mk
                                                            false
                                                            [
                                                              (PathSegment.mk
                                                                "Offset"
                                                                PathArguments.none),
                                                              (PathSegment.mk
                                                                "from_bytes_const"
                                                                PathArguments.none)]))
                                                        [(Expr.lit (Lit.int 1 ""))])]))
                                                false)])
                                          none)
                                        false)]))
                                false),
                              (Stmt.expr
                                (Expr.call
                                  (Expr.path
                                    none
                                    (Path.mk
                                      false
                                      [
                                        (PathSegment.mk
                                          "ret"
                                          (PathArguments.angleBracketed
                                            true
                                            [
                                              (GenericArgument.type
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
                                                                      "Path"
                                                                      PathArguments.none)])))]))])))]))]))
                                  [
                                    (Expr.path
                                      none
                                      (Path.mk
                                        false
                                        [(PathSegment.mk "child_path" PathArguments.none)]))])
                                false)])))])))
              none),
            (Stmt.expr
              (Expr.ite
                (Expr.methodCall
                  (Expr.field
                    (Expr.path
                      none
                      (Path.mk false [(PathSegment.mk "settings" PathArguments.none)]))
                    (Member.named "protected"))
                  "yes"
                  none
                  [])
                (Block.mk
                  [
                    (Stmt.expr
                      (Expr.methodCall
                        (Expr.field
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "frame_extra" PathArguments.none)]))
                          (Member.named "protectors"))
                        "push"
                        none
                        [
                          (Expr.tuple
                            [
                              (Expr.path
                                none
                                (Path.mk false [(PathSegment.mk "alloc_id" PathArguments.none)])),
                              (Expr.path
                                none
                                (Path.mk false [(PathSegment.mk "child_path" PathArguments.none)]))])])
                      true)])
                none)
              false),
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
                        (Member.named "provenance")
                        false
                        (Expr.call
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "Some" PathArguments.none)]))
                          [
                            (Expr.tuple
                              [
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "alloc_id" PathArguments.none)])),
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "child_path" PathArguments.none)]))])]))]
                    true
                    (some
                      (Expr.path none (Path.mk false [(PathSegment.mk "ptr" PathArguments.none)]))))])
              false)])),
      (ImplItem.fn
        [
          (Attr.mk true "doc" (AttrMeta.nameValue " Remove the protector.")),
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue " `provenance` is the provenance of the protector.")),
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue
              " Perform a special implicit access on all locations that have been accessed."))]
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
              (Pat.ident false false "provenance" none)
              (Ty.path
                none
                (Path.mk false [(PathSegment.mk "TreeBorrowsProvenance" PathArguments.none)])))]
          false
          (some (Ty.path none (Path.mk false [(PathSegment.mk "Result" PathArguments.none)]))))
        (Block.mk
          [
            (Stmt.letStmt
              []
              (Pat.tuple
                [(Pat.ident false false "alloc_id" none), (Pat.ident false false "path" none)])
              (some
                (Expr.path none (Path.mk false [(PathSegment.mk "provenance" PathArguments.none)])))
              none),
            (Stmt.expr
              (Expr.methodCall
                (Expr.field
                  (Expr.field
                    (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                    (Member.named "mem"))
                  (Member.named "allocations"))
                "mutate_at"
                none
                [
                  (Expr.field
                    (Expr.path
                      none
                      (Path.mk false [(PathSegment.mk "alloc_id" PathArguments.none)]))
                    (Member.unnamed 0)),
                  (Expr.closure
                    false
                    [(Pat.ident false false "allocation" none)]
                    none
                    (Expr.block
                      none
                      (Block.mk
                        [
                          (Stmt.letStmt
                            []
                            (Pat.typed
                              (Pat.ident false false "protector_accesses" none)
                              (Ty.path
                                none
                                (Path.mk
                                  false
                                  [
                                    (PathSegment.mk
                                      "List"
                                      (PathArguments.angleBracketed
                                        false
                                        [(GenericArgument.type Ty.infer)]))])))
                            (some
                              (Expr.methodCall
                                (Expr.field
                                  (Expr.field
                                    (Expr.path
                                      none
                                      (Path.mk
                                        false
                                        [(PathSegment.mk "allocation" PathArguments.none)]))
                                    (Member.named "extra"))
                                  (Member.named "root"))
                                "access_node"
                                none
                                [
                                  (Expr.path
                                    none
                                    (Path.mk false [(PathSegment.mk "path" PathArguments.none)])),
                                  (Expr.closure
                                    false
                                    [(Pat.ident false false "node" none)]
                                    none
                                    (Expr.block
                                      none
                                      (Block.mk
                                        [
                                          (Stmt.macro
                                            []
                                            (Macro.mk
                                              (Path.mk
                                                false
                                                [(PathSegment.mk "assert" PathArguments.none)])
                                              MacroDelimiter.paren
                                              (MacroBody.exprs
                                                [
                                                  (Expr.methodCall
                                                    (Expr.field
                                                      (Expr.path
                                                        none
                                                        (Path.mk
                                                          false
                                                          [
                                                            (PathSegment.mk
                                                              "node"
                                                              PathArguments.none)]))
                                                      (Member.named "protected"))
                                                    "yes"
                                                    none
                                                    [])]
                                                false))
                                            true),
                                          (Stmt.letStmt
                                            []
                                            (Pat.ident
                                              false
                                              false
                                              "list_of_perms_and_accesses"
                                              none)
                                            (some
                                              (Expr.methodCall
                                                (Expr.field
                                                  (Expr.path
                                                    none
                                                    (Path.mk
                                                      false
                                                      [(PathSegment.mk "node" PathArguments.none)]))
                                                  (Member.named "permissions"))
                                                "map"
                                                none
                                                [
                                                  (Expr.closure
                                                    false
                                                    [(Pat.ident false false "x" none)]
                                                    none
                                                    (Expr.methodCall
                                                      (Expr.path
                                                        none
                                                        (Path.mk
                                                          false
                                                          [(PathSegment.mk "x" PathArguments.none)]))
                                                      "unprotect"
                                                      none
                                                      []))]))
                                            none),
                                          (Stmt.expr
                                            (Expr.assign
                                              (Expr.field
                                                (Expr.path
                                                  none
                                                  (Path.mk
                                                    false
                                                    [(PathSegment.mk "node" PathArguments.none)]))
                                                (Member.named "permissions"))
                                              (Expr.methodCall
                                                (Expr.path
                                                  none
                                                  (Path.mk
                                                    false
                                                    [
                                                      (PathSegment.mk
                                                        "list_of_perms_and_accesses"
                                                        PathArguments.none)]))
                                                "map"
                                                none
                                                [
                                                  (Expr.closure
                                                    false
                                                    [
                                                      (Pat.tuple
                                                        [
                                                          (Pat.ident false false "perm" none),
                                                          (Pat.ident false false "_acc" none)])]
                                                    none
                                                    (Expr.path
                                                      none
                                                      (Path.mk
                                                        false
                                                        [(PathSegment.mk "perm" PathArguments.none)])))]))
                                            true),
                                          (Stmt.expr
                                            (Expr.methodCall
                                              (Expr.path
                                                none
                                                (Path.mk
                                                  false
                                                  [
                                                    (PathSegment.mk
                                                      "list_of_perms_and_accesses"
                                                      PathArguments.none)]))
                                              "map"
                                              none
                                              [
                                                (Expr.closure
                                                  false
                                                  [
                                                    (Pat.tuple
                                                      [
                                                        (Pat.ident false false "_perm" none),
                                                        (Pat.ident false false "acc" none)])]
                                                  none
                                                  (Expr.path
                                                    none
                                                    (Path.mk
                                                      false
                                                      [(PathSegment.mk "acc" PathArguments.none)])))])
                                            false)])))]))
                            none),
                          (Stmt.expr
                            (Expr.ite
                              (Expr.unary
                                UnOp.not
                                (Expr.field
                                  (Expr.path
                                    none
                                    (Path.mk
                                      false
                                      [(PathSegment.mk "allocation" PathArguments.none)]))
                                  (Member.named "live")))
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
                                          [(Expr.tuple [])])))
                                    true)])
                              none)
                            false),
                          (Stmt.expr
                            (Expr.methodCall
                              (Expr.field
                                (Expr.field
                                  (Expr.path
                                    none
                                    (Path.mk
                                      false
                                      [(PathSegment.mk "allocation" PathArguments.none)]))
                                  (Member.named "extra"))
                                (Member.named "root"))
                              "release_protector"
                              none
                              [
                                (Expr.call
                                  (Expr.path
                                    none
                                    (Path.mk false [(PathSegment.mk "Some" PathArguments.none)]))
                                  [
                                    (Expr.path
                                      none
                                      (Path.mk false [(PathSegment.mk "path" PathArguments.none)]))]),
                                (Expr.reference
                                  false
                                  (Expr.path
                                    none
                                    (Path.mk
                                      false
                                      [(PathSegment.mk "protector_accesses" PathArguments.none)])))])
                            false)])))])
              false)]))])

/-- `spec/mem/tree_borrows/memory.md:184` -/
def impl_TreeBorrowsMemory_for_Memory__Provenance : Item :=
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
              (Path.mk false [(PathSegment.mk "Target" PathArguments.none)]))]
          none)]
      [])
    false
    (some (Path.mk false [(PathSegment.mk "Memory" PathArguments.none)]))
    (Ty.path
      none
      (Path.mk
        false
        [
          (PathSegment.mk
            "TreeBorrowsMemory"
            (PathArguments.angleBracketed
              false
              [
                (GenericArgument.type
                  (Ty.path none (Path.mk false [(PathSegment.mk "T" PathArguments.none)])))]))]))
    [
      (ImplItem.type
        []
        Visibility.inherited
        false
        "Provenance"
        (Generics.mk [] [])
        (Ty.path none (Path.mk false [(PathSegment.mk "TreeBorrowsProvenance" PathArguments.none)]))),
      (ImplItem.type
        []
        Visibility.inherited
        false
        "FrameExtra"
        (Generics.mk [] [])
        (Ty.path none (Path.mk false [(PathSegment.mk "TreeBorrowsFrameExtra" PathArguments.none)]))),
      (ImplItem.type
        []
        Visibility.inherited
        false
        "T"
        (Generics.mk [] [])
        (Ty.path none (Path.mk false [(PathSegment.mk "T" PathArguments.none)]))),
      (ImplItem.type
        []
        Visibility.inherited
        false
        "Params"
        (Generics.mk [] [])
        (Ty.path none (Path.mk false [(PathSegment.mk "TreeBorrowsParams" PathArguments.none)]))),
      (ImplItem.fn
        []
        Visibility.inherited
        false
        (Signature.mk
          false
          false
          false
          none
          "new"
          (Generics.mk [] [])
          [
            (FnArg.typed
              []
              (Pat.ident false false "params" none)
              (Ty.path
                none
                (Path.mk false [(PathSegment.mk "TreeBorrowsParams" PathArguments.none)])))]
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
                    (Member.named "mem")
                    false
                    (Expr.call
                      (Expr.path
                        none
                        (Path.mk
                          false
                          [
                            (PathSegment.mk "BasicMemory" PathArguments.none),
                            (PathSegment.mk "new" PathArguments.none)]))
                      [])),
                  (FieldValue.mk
                    []
                    (Member.named "params")
                    true
                    (Expr.path none (Path.mk false [(PathSegment.mk "params" PathArguments.none)])))]
                false
                none)
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
          "allocate"
          (Generics.mk [] [])
          [
            (FnArg.receiver [] true none true none),
            (FnArg.typed
              []
              (Pat.ident false false "kind" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "AllocationKind" PathArguments.none)]))),
            (FnArg.typed
              []
              (Pat.ident false false "size" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "Size" PathArguments.none)]))),
            (FnArg.typed
              []
              (Pat.ident false false "align" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "Align" PathArguments.none)])))]
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
                                            [
                                              (PathSegment.mk "Self" PathArguments.none),
                                              (PathSegment.mk "Provenance" PathArguments.none)])))]))])))]))]))))
        (Block.mk
          [
            (Stmt.letStmt
              []
              (Pat.ident false false "root" none)
              (some
                (Expr.struct
                  none
                  (Path.mk false [(PathSegment.mk "Node" PathArguments.none)])
                  [
                    (FieldValue.mk
                      []
                      (Member.named "children")
                      false
                      (Expr.call
                        (Expr.path
                          none
                          (Path.mk
                            false
                            [
                              (PathSegment.mk "List" PathArguments.none),
                              (PathSegment.mk "new" PathArguments.none)]))
                        [])),
                    (FieldValue.mk
                      []
                      (Member.named "permissions")
                      false
                      (Expr.macro
                        (Macro.mk
                          (Path.mk false [(PathSegment.mk "list" PathArguments.none)])
                          MacroDelimiter.bracket
                          (MacroBody.repeatList
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
                                    [
                                      (PathSegment.mk "PermissionUnprot" PathArguments.none),
                                      (PathSegment.mk "Unique" PathArguments.none)]))])
                            (Expr.methodCall
                              (Expr.path
                                none
                                (Path.mk false [(PathSegment.mk "size" PathArguments.none)]))
                              "bytes"
                              none
                              []))))),
                    (FieldValue.mk
                      []
                      (Member.named "protected")
                      false
                      (Expr.path
                        none
                        (Path.mk
                          false
                          [
                            (PathSegment.mk "Protected" PathArguments.none),
                            (PathSegment.mk "No" PathArguments.none)])))]
                  false
                  none))
              none),
            (Stmt.letStmt
              []
              (Pat.ident false false "path" none)
              (some
                (Expr.call
                  (Expr.path
                    none
                    (Path.mk
                      false
                      [
                        (PathSegment.mk "Path" PathArguments.none),
                        (PathSegment.mk "new" PathArguments.none)]))
                  []))
              none),
            (Stmt.letStmt
              []
              (Pat.ident false false "extra" none)
              (some
                (Expr.struct
                  none
                  (Path.mk false [(PathSegment.mk "TreeBorrowsAllocationExtra" PathArguments.none)])
                  [
                    (FieldValue.mk
                      []
                      (Member.named "root")
                      true
                      (Expr.path none (Path.mk false [(PathSegment.mk "root" PathArguments.none)])))]
                  false
                  none))
              none),
            (Stmt.expr
              (Expr.methodCall
                (Expr.field
                  (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                  (Member.named "mem"))
                "allocate"
                none
                [
                  (Expr.path none (Path.mk false [(PathSegment.mk "kind" PathArguments.none)])),
                  (Expr.path none (Path.mk false [(PathSegment.mk "size" PathArguments.none)])),
                  (Expr.path none (Path.mk false [(PathSegment.mk "align" PathArguments.none)])),
                  (Expr.path none (Path.mk false [(PathSegment.mk "path" PathArguments.none)])),
                  (Expr.path none (Path.mk false [(PathSegment.mk "extra" PathArguments.none)]))])
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
          "deallocate"
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
                                  (PathSegment.mk "Self" PathArguments.none),
                                  (PathSegment.mk "Provenance" PathArguments.none)])))]))]))),
            (FnArg.typed
              []
              (Pat.ident false false "kind" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "AllocationKind" PathArguments.none)]))),
            (FnArg.typed
              []
              (Pat.ident false false "size" none)
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
              (Expr.methodCall
                (Expr.field
                  (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                  (Member.named "mem"))
                "deallocate"
                none
                [
                  (Expr.path none (Path.mk false [(PathSegment.mk "ptr" PathArguments.none)])),
                  (Expr.path none (Path.mk false [(PathSegment.mk "kind" PathArguments.none)])),
                  (Expr.path none (Path.mk false [(PathSegment.mk "size" PathArguments.none)])),
                  (Expr.path none (Path.mk false [(PathSegment.mk "align" PathArguments.none)])),
                  (Expr.closure
                    false
                    [(Pat.ident false false "extra" none), (Pat.ident false false "path" none)]
                    none
                    (Expr.block
                      none
                      (Block.mk
                        [
                          (Stmt.expr
                            (Expr.tryExpr
                              (Expr.methodCall
                                (Expr.field
                                  (Expr.path
                                    none
                                    (Path.mk false [(PathSegment.mk "extra" PathArguments.none)]))
                                  (Member.named "root"))
                                "access"
                                none
                                [
                                  (Expr.call
                                    (Expr.path
                                      none
                                      (Path.mk false [(PathSegment.mk "Some" PathArguments.none)]))
                                    [
                                      (Expr.path
                                        none
                                        (Path.mk false [(PathSegment.mk "path" PathArguments.none)]))]),
                                  (Expr.path
                                    none
                                    (Path.mk
                                      false
                                      [
                                        (PathSegment.mk "AccessKind" PathArguments.none),
                                        (PathSegment.mk "Write" PathArguments.none)])),
                                  (Expr.path
                                    none
                                    (Path.mk
                                      false
                                      [
                                        (PathSegment.mk "Offset" PathArguments.none),
                                        (PathSegment.mk "ZERO" PathArguments.none)])),
                                  (Expr.path
                                    none
                                    (Path.mk false [(PathSegment.mk "size" PathArguments.none)]))]))
                            true),
                          (Stmt.expr
                            (Expr.ite
                              (Expr.methodCall
                                (Expr.field
                                  (Expr.path
                                    none
                                    (Path.mk false [(PathSegment.mk "extra" PathArguments.none)]))
                                  (Member.named "root"))
                                "contains_strong_protector_preventing_deallocation"
                                none
                                [])
                              (Block.mk
                                [
                                  (Stmt.expr
                                    (Expr.macro
                                      (Macro.mk
                                        (Path.mk
                                          false
                                          [(PathSegment.mk "throw_ub" PathArguments.none)])
                                        MacroDelimiter.paren
                                        (MacroBody.exprs
                                          [
                                            (Expr.lit
                                              (Lit.str
                                                "Tree Borrows: deallocating strongly protected allocation"))]
                                          false)))
                                    false)])
                              none)
                            false),
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
          "load"
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
                                  (PathSegment.mk "Self" PathArguments.none),
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
                                                              "Self"
                                                              PathArguments.none),
                                                            (PathSegment.mk
                                                              "Provenance"
                                                              PathArguments.none)])))]))])))]))])))]))]))))
        (Block.mk
          [
            (Stmt.expr
              (Expr.methodCall
                (Expr.field
                  (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                  (Member.named "mem"))
                "load"
                none
                [
                  (Expr.path none (Path.mk false [(PathSegment.mk "ptr" PathArguments.none)])),
                  (Expr.path none (Path.mk false [(PathSegment.mk "len" PathArguments.none)])),
                  (Expr.path none (Path.mk false [(PathSegment.mk "align" PathArguments.none)])),
                  (Expr.closure
                    false
                    [
                      (Pat.ident false false "extra" none),
                      (Pat.ident false false "path" none),
                      (Pat.ident false false "offset" none)]
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
                                  (Path.mk false [(PathSegment.mk "extra" PathArguments.none)]))
                                (Member.named "root"))
                              "access"
                              none
                              [
                                (Expr.call
                                  (Expr.path
                                    none
                                    (Path.mk false [(PathSegment.mk "Some" PathArguments.none)]))
                                  [
                                    (Expr.path
                                      none
                                      (Path.mk false [(PathSegment.mk "path" PathArguments.none)]))]),
                                (Expr.path
                                  none
                                  (Path.mk
                                    false
                                    [
                                      (PathSegment.mk "AccessKind" PathArguments.none),
                                      (PathSegment.mk "Read" PathArguments.none)])),
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "offset" PathArguments.none)])),
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "len" PathArguments.none)]))])
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
          "store"
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
                                  (PathSegment.mk "Self" PathArguments.none),
                                  (PathSegment.mk "Provenance" PathArguments.none)])))]))]))),
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
                                                (PathSegment.mk "Self" PathArguments.none),
                                                (PathSegment.mk "Provenance" PathArguments.none)])))]))])))]))]))),
            (FnArg.typed
              []
              (Pat.ident false false "align" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "Align" PathArguments.none)])))]
          false
          (some (Ty.path none (Path.mk false [(PathSegment.mk "Result" PathArguments.none)]))))
        (Block.mk
          [
            (Stmt.letStmt
              []
              (Pat.ident false false "size" none)
              (some
                (Expr.methodCall
                  (Expr.call
                    (Expr.path
                      none
                      (Path.mk
                        false
                        [
                          (PathSegment.mk "Size" PathArguments.none),
                          (PathSegment.mk "from_bytes" PathArguments.none)]))
                    [
                      (Expr.methodCall
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "bytes" PathArguments.none)]))
                        "len"
                        none
                        [])])
                  "unwrap"
                  none
                  []))
              none),
            (Stmt.expr
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
                  (Expr.closure
                    false
                    [
                      (Pat.ident false false "extra" none),
                      (Pat.ident false false "path" none),
                      (Pat.ident false false "offset" none)]
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
                                  (Path.mk false [(PathSegment.mk "extra" PathArguments.none)]))
                                (Member.named "root"))
                              "access"
                              none
                              [
                                (Expr.call
                                  (Expr.path
                                    none
                                    (Path.mk false [(PathSegment.mk "Some" PathArguments.none)]))
                                  [
                                    (Expr.path
                                      none
                                      (Path.mk false [(PathSegment.mk "path" PathArguments.none)]))]),
                                (Expr.path
                                  none
                                  (Path.mk
                                    false
                                    [
                                      (PathSegment.mk "AccessKind" PathArguments.none),
                                      (PathSegment.mk "Write" PathArguments.none)])),
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "offset" PathArguments.none)])),
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "size" PathArguments.none)]))])
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
          "dereferenceable"
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
                                  (PathSegment.mk "Self" PathArguments.none),
                                  (PathSegment.mk "Provenance" PathArguments.none)])))]))]))),
            (FnArg.typed
              []
              (Pat.ident false false "len" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "Size" PathArguments.none)])))]
          false
          (some (Ty.path none (Path.mk false [(PathSegment.mk "Result" PathArguments.none)]))))
        (Block.mk
          [
            (Stmt.expr
              (Expr.tryExpr
                (Expr.methodCall
                  (Expr.field
                    (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                    (Member.named "mem"))
                  "check_ptr"
                  none
                  [
                    (Expr.path none (Path.mk false [(PathSegment.mk "ptr" PathArguments.none)])),
                    (Expr.path none (Path.mk false [(PathSegment.mk "len" PathArguments.none)]))]))
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
          "retag_ptr"
          (Generics.mk [] [])
          [
            (FnArg.receiver [] true none true none),
            (FnArg.typed
              []
              (Pat.ident false false "frame_extra" none)
              (Ty.reference
                none
                true
                (Ty.path
                  none
                  (Path.mk
                    false
                    [
                      (PathSegment.mk "Self" PathArguments.none),
                      (PathSegment.mk "FrameExtra" PathArguments.none)])))),
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
                                  (PathSegment.mk "Self" PathArguments.none),
                                  (PathSegment.mk "Provenance" PathArguments.none)])))]))]))),
            (FnArg.typed
              []
              (Pat.ident false false "ptr_type" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "PtrType" PathArguments.none)]))),
            (FnArg.typed
              []
              (Pat.ident false false "fn_entry" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "bool" PathArguments.none)]))),
            (FnArg.typed
              []
              (Pat.ident false false "fn_implicit_writes" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "bool" PathArguments.none)]))),
            (FnArg.typed
              []
              (Pat.ident false false "vtable_lookup" none)
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
                          "Fn"
                          (PathArguments.parenthesized
                            [
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
                                                  (PathSegment.mk "Self" PathArguments.none),
                                                  (PathSegment.mk "Provenance" PathArguments.none)])))]))]))]
                            (some
                              (Ty.path
                                none
                                (Path.mk
                                  false
                                  [
                                    (PathSegment.mk "crate" PathArguments.none),
                                    (PathSegment.mk "lang" PathArguments.none),
                                    (PathSegment.mk "VTable" PathArguments.none)])))))])),
                  (TypeParamBound.lifetime "static")]))]
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
                                              (PathSegment.mk "Self" PathArguments.none),
                                              (PathSegment.mk "Provenance" PathArguments.none)])))]))])))]))]))))
        (Block.mk
          [
            (Stmt.expr
              (Expr.call
                (Expr.path none (Path.mk false [(PathSegment.mk "ret" PathArguments.none)]))
                [
                  (Expr.ite
                    (Expr.letCond
                      (Pat.tupleStruct
                        none
                        (Path.mk false [(PathSegment.mk "Some" PathArguments.none)])
                        [(Pat.ident false false "perms" none)])
                      (Expr.call
                        (Expr.path
                          none
                          (Path.mk
                            false
                            [
                              (PathSegment.mk "ReborrowSettings" PathArguments.none),
                              (PathSegment.mk "new" PathArguments.none)]))
                        [
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "ptr" PathArguments.none)])),
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "ptr_type" PathArguments.none)])),
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "fn_entry" PathArguments.none)])),
                          (Expr.field
                            (Expr.path
                              none
                              (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                            (Member.named "params")),
                          (Expr.path
                            none
                            (Path.mk
                              false
                              [(PathSegment.mk "fn_implicit_writes" PathArguments.none)])),
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "vtable_lookup" PathArguments.none)]))]))
                    (Block.mk
                      [
                        (Stmt.expr
                          (Expr.methodCall
                            (Expr.tryExpr
                              (Expr.methodCall
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                                "reborrow"
                                none
                                [
                                  (Expr.field
                                    (Expr.path
                                      none
                                      (Path.mk false [(PathSegment.mk "ptr" PathArguments.none)]))
                                    (Member.named "thin_pointer")),
                                  (Expr.path
                                    none
                                    (Path.mk false [(PathSegment.mk "perms" PathArguments.none)])),
                                  (Expr.path
                                    none
                                    (Path.mk
                                      false
                                      [(PathSegment.mk "frame_extra" PathArguments.none)]))]))
                            "widen"
                            none
                            [
                              (Expr.field
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "ptr" PathArguments.none)]))
                                (Member.named "metadata"))])
                          false)])
                    (some
                      (Expr.block
                        none
                        (Block.mk
                          [
                            (Stmt.expr
                              (Expr.path
                                none
                                (Path.mk false [(PathSegment.mk "ptr" PathArguments.none)]))
                              false)]))))])
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
          "new_call"
          (Generics.mk [] [])
          []
          false
          (some
            (Ty.path
              none
              (Path.mk
                false
                [
                  (PathSegment.mk "Self" PathArguments.none),
                  (PathSegment.mk "FrameExtra" PathArguments.none)]))))
        (Block.mk
          [
            (Stmt.expr
              (Expr.call
                (Expr.path
                  none
                  (Path.mk
                    false
                    [
                      (PathSegment.mk "Self" PathArguments.none),
                      (PathSegment.mk "FrameExtra" PathArguments.none),
                      (PathSegment.mk "new" PathArguments.none)]))
                [])
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
          "end_call"
          (Generics.mk [] [])
          [
            (FnArg.receiver [] true none true none),
            (FnArg.typed
              []
              (Pat.ident false false "extra" none)
              (Ty.path
                none
                (Path.mk
                  false
                  [
                    (PathSegment.mk "Self" PathArguments.none),
                    (PathSegment.mk "FrameExtra" PathArguments.none)])))]
          false
          (some (Ty.path none (Path.mk false [(PathSegment.mk "Result" PathArguments.none)]))))
        (Block.mk
          [
            (Stmt.expr
              (Expr.tryExpr
                (Expr.methodCall
                  (Expr.field
                    (Expr.path none (Path.mk false [(PathSegment.mk "extra" PathArguments.none)]))
                    (Member.named "protectors"))
                  "try_map"
                  none
                  [
                    (Expr.closure
                      false
                      [(Pat.ident false false "provenance" none)]
                      none
                      (Expr.methodCall
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                        "release_protector"
                        none
                        [
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "provenance" PathArguments.none)]))]))]))
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
          "leak_check"
          (Generics.mk [] [])
          [(FnArg.receiver [] true none false none)]
          false
          (some (Ty.path none (Path.mk false [(PathSegment.mk "Result" PathArguments.none)]))))
        (Block.mk
          [
            (Stmt.expr
              (Expr.methodCall
                (Expr.field
                  (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                  (Member.named "mem"))
                "leak_check"
                none
                [])
              false)]))])

/-- All items of `spec/mem/tree_borrows/memory.md`, in source order, with provenance. -/
def items : List SourceItem :=
  [
    (SourceItem.mk
      "struct_TreeBorrowsAllocationExtra"
      14
      "a85ed7fcdb184c536b1a1edeb2ca71be1c9a30883b536e4de2b26d63a20d4f9d"
      struct_TreeBorrowsAllocationExtra),
    (SourceItem.mk
      "type_ChildId"
      38
      "e64c44de9793730094b8e96287817c87194d01ed21184dff1931cebac631b567"
      type_ChildId),
    (SourceItem.mk
      "type_Path"
      40
      "e14bc41f2be1b8b87d27de1a875ce26343732567e8416b07fdf3922d19491ec5"
      type_Path),
    (SourceItem.mk
      "type_TreeBorrowsProvenance"
      47
      "85b4f7a33bc2a6c342c018613308c7df228cb03bf45c8dc552d840afc54feb40"
      type_TreeBorrowsProvenance),
    (SourceItem.mk
      "struct_TreeBorrowsParams"
      53
      "ea4e7c12fa4c21720a59b348a781f98ee6c484512c094d06a8d43f48d68fb79d"
      struct_TreeBorrowsParams),
    (SourceItem.mk
      "struct_TreeBorrowsMemory"
      62
      "5107353ba745ee83f5b28ae73c057a0d2482d74cd5bcbbcbfaf70d0cfebb35ec"
      struct_TreeBorrowsMemory),
    (SourceItem.mk
      "struct_TreeBorrowsFrameExtra"
      67
      "bf73c1e89611e20e44e9a7606999cc47e4225ca5861b8f2cf9e79a76c7ea8f3c"
      struct_TreeBorrowsFrameExtra),
    (SourceItem.mk
      "impl_TreeBorrowsFrameExtra__new"
      72
      "b7ade75c85850816b8595acc01fe412cada6028cef8a8a6f5798dc18d500f595"
      impl_TreeBorrowsFrameExtra__new),
    (SourceItem.mk
      "impl_TreeBorrowsMemory__reborrow"
      80
      "a0945cee3aac61f2bfc956c3f55391396c5f0a709eae345aca6a6713ec65f327"
      impl_TreeBorrowsMemory__reborrow),
    (SourceItem.mk
      "impl_TreeBorrowsMemory_for_Memory__Provenance"
      184
      "7a65908ec120bb0a970c3c28da5928335a78671e2551f474d3a5b3495fa0cb03"
      impl_TreeBorrowsMemory_for_Memory__Provenance)]

end MiniRustSpec.Gen.Items.Mem.TreeBorrows.Memory
