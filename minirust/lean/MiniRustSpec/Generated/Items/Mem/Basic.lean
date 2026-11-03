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
`spec/mem/basic.md` (commit `d821c6e3`), one Lean definition per item, in source order.
-/

import MiniRustSpec.Meta.Syntax

set_option maxRecDepth 100000

namespace MiniRustSpec.Gen.Items.Mem.Basic

open MiniRustSpec.Syntax

/-- Path of the upstream file these items were extracted from. -/
def sourceFile : String := "spec/mem/basic.md"

/-- SHA-256 of the upstream file. -/
def sourceSha256 : String := "99b80806ce4a14fd1787d9b20d6931bb4756155b9fd74b380508d8c7cf87c072"

/-- `spec/mem/basic.md:18` -/
def struct_AllocId : Item :=
  (Item.struct
    []
    Visibility.pub
    "AllocId"
    (Generics.mk [] [])
    (Fields.unnamed
      [
        (Field.mk
          []
          Visibility.inherited
          none
          (Ty.path none (Path.mk false [(PathSegment.mk "Int" PathArguments.none)])))]))

/-- `spec/mem/basic.md:20` -/
def type_Provenance : Item :=
  (Item.type
    []
    Visibility.inherited
    "Provenance"
    (Generics.mk [(GenericParam.type [] "Extra" [] none)] [])
    (Ty.tuple
      [
        (Ty.path none (Path.mk false [(PathSegment.mk "AllocId" PathArguments.none)])),
        (Ty.path none (Path.mk false [(PathSegment.mk "Extra" PathArguments.none)]))]))

/-- `spec/mem/basic.md:26` -/
def struct_Allocation : Item :=
  (Item.struct
    []
    Visibility.inherited
    "Allocation"
    (Generics.mk
      [
        (GenericParam.type [] "ProvExtra" [] (some (Ty.tuple []))),
        (GenericParam.type [] "AllocExtra" [] (some (Ty.tuple [])))]
      [])
    (Fields.named
      [
        (Field.mk
          [(Attr.mk true "doc" (AttrMeta.nameValue " The data stored in this allocation."))]
          Visibility.inherited
          (some "data")
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
                                              "Provenance"
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
                                                            "ProvExtra"
                                                            PathArguments.none)])))]))])))]))])))]))]))),
        (Field.mk
          [
            (Attr.mk true "doc" (AttrMeta.nameValue " The address where this allocation starts.")),
            (Attr.mk
              true
              "doc"
              (AttrMeta.nameValue " This is never 0, and `addr + data.len()` fits into a `usize`."))]
          Visibility.inherited
          (some "addr")
          (Ty.path none (Path.mk false [(PathSegment.mk "Address" PathArguments.none)]))),
        (Field.mk
          [
            (Attr.mk
              true
              "doc"
              (AttrMeta.nameValue " The alignment that was requested for this allocation.")),
            (Attr.mk true "doc" (AttrMeta.nameValue " `addr` will be a multiple of this."))]
          Visibility.inherited
          (some "align")
          (Ty.path none (Path.mk false [(PathSegment.mk "Align" PathArguments.none)]))),
        (Field.mk
          [(Attr.mk true "doc" (AttrMeta.nameValue " The kind of this allocation."))]
          Visibility.inherited
          (some "kind")
          (Ty.path none (Path.mk false [(PathSegment.mk "AllocationKind" PathArguments.none)]))),
        (Field.mk
          [(Attr.mk true "doc" (AttrMeta.nameValue " Whether this allocation is still live."))]
          Visibility.inherited
          (some "live")
          (Ty.path none (Path.mk false [(PathSegment.mk "bool" PathArguments.none)]))),
        (Field.mk
          [
            (Attr.mk
              true
              "doc"
              (AttrMeta.nameValue " Additional information needed for the memory model"))]
          Visibility.inherited
          (some "extra")
          (Ty.path none (Path.mk false [(PathSegment.mk "AllocExtra" PathArguments.none)])))]))

/-- `spec/mem/basic.md:47` -/
def struct_BasicMemory : Item :=
  (Item.struct
    []
    Visibility.pub
    "BasicMemory"
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
          none),
        (GenericParam.type [] "ProvExtra" [] (some (Ty.tuple []))),
        (GenericParam.type [] "AllocExtra" [] (some (Ty.tuple [])))]
      [])
    (Fields.named
      [
        (Field.mk
          []
          Visibility.inherited
          (some "allocations")
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
                                "Allocation"
                                (PathArguments.angleBracketed
                                  false
                                  [
                                    (GenericArgument.type
                                      (Ty.path
                                        none
                                        (Path.mk
                                          false
                                          [(PathSegment.mk "ProvExtra" PathArguments.none)]))),
                                    (GenericArgument.type
                                      (Ty.path
                                        none
                                        (Path.mk
                                          false
                                          [(PathSegment.mk "AllocExtra" PathArguments.none)])))]))])))]))]))),
        (Field.mk
          []
          Visibility.inherited
          (some "_phantom")
          (Ty.path
            none
            (Path.mk
              false
              [
                (PathSegment.mk "std" PathArguments.none),
                (PathSegment.mk "marker" PathArguments.none),
                (PathSegment.mk
                  "PhantomData"
                  (PathArguments.angleBracketed
                    false
                    [
                      (GenericArgument.type
                        (Ty.path none (Path.mk false [(PathSegment.mk "T" PathArguments.none)])))]))])))]))

/-- `spec/mem/basic.md:54` -/
def impl_BasicMemory__new : Item :=
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
          none),
        (GenericParam.type [] "ProvExtra" [] none),
        (GenericParam.type [] "AllocExtra" [] none)]
      [])
    false
    none
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
                  (Ty.path none (Path.mk false [(PathSegment.mk "ProvExtra" PathArguments.none)]))),
                (GenericArgument.type
                  (Ty.path none (Path.mk false [(PathSegment.mk "AllocExtra" PathArguments.none)])))]))]))
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
                    (Member.named "allocations")
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
                    (Member.named "_phantom")
                    false
                    (Expr.path
                      none
                      (Path.mk
                        false
                        [
                          (PathSegment.mk "std" PathArguments.none),
                          (PathSegment.mk "marker" PathArguments.none),
                          (PathSegment.mk "PhantomData" PathArguments.none)])))]
                false
                none)
              false)]))])

/-- `spec/mem/basic.md:66` -/
def impl_Allocation__size : Item :=
  (Item.impl
    []
    false
    false
    (Generics.mk
      [(GenericParam.type [] "ProvExtra" [] none), (GenericParam.type [] "AllocExtra" [] none)]
      [])
    false
    none
    (Ty.path
      none
      (Path.mk
        false
        [
          (PathSegment.mk
            "Allocation"
            (PathArguments.angleBracketed
              false
              [
                (GenericArgument.type
                  (Ty.path none (Path.mk false [(PathSegment.mk "ProvExtra" PathArguments.none)]))),
                (GenericArgument.type
                  (Ty.path none (Path.mk false [(PathSegment.mk "AllocExtra" PathArguments.none)])))]))]))
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
          "size"
          (Generics.mk [] [])
          [(FnArg.receiver [] false none false none)]
          false
          (some (Ty.path none (Path.mk false [(PathSegment.mk "Size" PathArguments.none)]))))
        (Block.mk
          [
            (Stmt.expr
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
                          (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                        (Member.named "data"))
                      "len"
                      none
                      [])])
                "unwrap"
                none
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
          "overlaps"
          (Generics.mk [] [])
          [
            (FnArg.receiver [] false none false none),
            (FnArg.typed
              []
              (Pat.ident false false "other_addr" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "Address" PathArguments.none)]))),
            (FnArg.typed
              []
              (Pat.ident false false "other_size" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "Size" PathArguments.none)])))]
          false
          (some (Ty.path none (Path.mk false [(PathSegment.mk "bool" PathArguments.none)]))))
        (Block.mk
          [
            (Stmt.letStmt
              []
              (Pat.ident false false "end_addr" none)
              (some
                (Expr.binary
                  (Expr.field
                    (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                    (Member.named "addr"))
                  BinOp.add
                  (Expr.methodCall
                    (Expr.methodCall
                      (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                      "size"
                      none
                      [])
                    "bytes"
                    none
                    [])))
              none),
            (Stmt.letStmt
              []
              (Pat.ident false false "other_end_addr" none)
              (some
                (Expr.binary
                  (Expr.path
                    none
                    (Path.mk false [(PathSegment.mk "other_addr" PathArguments.none)]))
                  BinOp.add
                  (Expr.methodCall
                    (Expr.path
                      none
                      (Path.mk false [(PathSegment.mk "other_size" PathArguments.none)]))
                    "bytes"
                    none
                    [])))
              none),
            (Stmt.expr
              (Expr.ite
                (Expr.binary
                  (Expr.binary
                    (Expr.path
                      none
                      (Path.mk false [(PathSegment.mk "end_addr" PathArguments.none)]))
                    BinOp.le
                    (Expr.path
                      none
                      (Path.mk false [(PathSegment.mk "other_addr" PathArguments.none)])))
                  BinOp.or
                  (Expr.binary
                    (Expr.path
                      none
                      (Path.mk false [(PathSegment.mk "other_end_addr" PathArguments.none)]))
                    BinOp.le
                    (Expr.field
                      (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                      (Member.named "addr"))))
                (Block.mk
                  [
                    (Stmt.expr
                      (Expr.binary
                        (Expr.field
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                          (Member.named "addr"))
                        BinOp.eq
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "other_addr" PathArguments.none)])))
                      false)])
                (some (Expr.block none (Block.mk [(Stmt.expr (Expr.lit (Lit.bool true)) false)]))))
              false)]))])

/-- `spec/mem/basic.md:91` -/
def impl_BasicMemory__allocate : Item :=
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
          none),
        (GenericParam.type [] "ProvExtra" [] none),
        (GenericParam.type [] "AllocExtra" [] none)]
      [])
    false
    none
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
                  (Ty.path none (Path.mk false [(PathSegment.mk "ProvExtra" PathArguments.none)]))),
                (GenericArgument.type
                  (Ty.path none (Path.mk false [(PathSegment.mk "AllocExtra" PathArguments.none)])))]))]))
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
              (Ty.path none (Path.mk false [(PathSegment.mk "Align" PathArguments.none)]))),
            (FnArg.typed
              []
              (Pat.ident false false "prov_extra" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "ProvExtra" PathArguments.none)]))),
            (FnArg.typed
              []
              (Pat.ident false false "alloc_extra" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "AllocExtra" PathArguments.none)])))]
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
                                              (PathSegment.mk
                                                "Provenance"
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
                                                              "ProvExtra"
                                                              PathArguments.none)])))]))])))]))])))]))]))))
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
                        [
                          (PathSegment.mk "T" PathArguments.none),
                          (PathSegment.mk "valid_size" PathArguments.none)]))
                    [(Expr.path none (Path.mk false [(PathSegment.mk "size" PathArguments.none)]))]))
                (Block.mk
                  [
                    (Stmt.macro
                      []
                      (Macro.mk
                        (Path.mk false [(PathSegment.mk "throw_ub" PathArguments.none)])
                        MacroDelimiter.paren
                        (MacroBody.exprs
                          [(Expr.lit (Lit.str "asking for a too large allocation"))]
                          false))
                      true)])
                none)
              false),
            (Stmt.letStmt
              []
              (Pat.ident false false "distr" none)
              (some
                (Expr.struct
                  none
                  (Path.mk
                    false
                    [
                      (PathSegment.mk "libspecr" PathArguments.none),
                      (PathSegment.mk "IntDistribution" PathArguments.none)])
                  [
                    (FieldValue.mk
                      []
                      (Member.named "start")
                      false
                      (Expr.path
                        none
                        (Path.mk
                          false
                          [
                            (PathSegment.mk "Int" PathArguments.none),
                            (PathSegment.mk "ONE" PathArguments.none)]))),
                    (FieldValue.mk
                      []
                      (Member.named "end")
                      false
                      (Expr.methodCall
                        (Expr.call
                          (Expr.path
                            none
                            (Path.mk
                              false
                              [
                                (PathSegment.mk "Int" PathArguments.none),
                                (PathSegment.mk "from" PathArguments.none)]))
                          [(Expr.lit (Lit.int 2 ""))])
                        "pow"
                        none
                        [
                          (Expr.methodCall
                            (Expr.path
                              none
                              (Path.mk
                                false
                                [
                                  (PathSegment.mk "T" PathArguments.none),
                                  (PathSegment.mk "PTR_SIZE" PathArguments.none)]))
                            "bits"
                            none
                            [])])),
                    (FieldValue.mk
                      []
                      (Member.named "divisor")
                      false
                      (Expr.methodCall
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "align" PathArguments.none)]))
                        "bytes"
                        none
                        []))]
                  false
                  none))
              none),
            (Stmt.letStmt
              []
              (Pat.ident false false "addr" none)
              (some
                (Expr.tryExpr
                  (Expr.call
                    (Expr.path none (Path.mk false [(PathSegment.mk "pick" PathArguments.none)]))
                    [
                      (Expr.path none (Path.mk false [(PathSegment.mk "distr" PathArguments.none)])),
                      (Expr.closure
                        false
                        [
                          (Pat.typed
                            (Pat.ident false false "addr" none)
                            (Ty.path
                              none
                              (Path.mk false [(PathSegment.mk "Address" PathArguments.none)])))]
                        none
                        (Expr.block
                          none
                          (Block.mk
                            [
                              (Stmt.expr
                                (Expr.ite
                                  (Expr.binary
                                    (Expr.path
                                      none
                                      (Path.mk false [(PathSegment.mk "addr" PathArguments.none)]))
                                    BinOp.le
                                    (Expr.lit (Lit.int 0 "")))
                                  (Block.mk
                                    [
                                      (Stmt.expr
                                        (Expr.returnExpr (some (Expr.lit (Lit.bool false))))
                                        true)])
                                  none)
                                false),
                              (Stmt.expr
                                (Expr.ite
                                  (Expr.unary
                                    UnOp.not
                                    (Expr.methodCall
                                      (Expr.path
                                        none
                                        (Path.mk
                                          false
                                          [(PathSegment.mk "align" PathArguments.none)]))
                                      "is_aligned"
                                      none
                                      [
                                        (Expr.path
                                          none
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "addr" PathArguments.none)]))]))
                                  (Block.mk
                                    [
                                      (Stmt.expr
                                        (Expr.returnExpr (some (Expr.lit (Lit.bool false))))
                                        true)])
                                  none)
                                false),
                              (Stmt.expr
                                (Expr.ite
                                  (Expr.unary
                                    UnOp.not
                                    (Expr.methodCall
                                      (Expr.paren
                                        (Expr.binary
                                          (Expr.path
                                            none
                                            (Path.mk
                                              false
                                              [(PathSegment.mk "addr" PathArguments.none)]))
                                          BinOp.add
                                          (Expr.methodCall
                                            (Expr.path
                                              none
                                              (Path.mk
                                                false
                                                [(PathSegment.mk "size" PathArguments.none)]))
                                            "bytes"
                                            none
                                            [])))
                                      "in_bounds"
                                      none
                                      [
                                        (Expr.path
                                          none
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "Unsigned" PathArguments.none)])),
                                        (Expr.path
                                          none
                                          (Path.mk
                                            false
                                            [
                                              (PathSegment.mk "T" PathArguments.none),
                                              (PathSegment.mk "PTR_SIZE" PathArguments.none)]))]))
                                  (Block.mk
                                    [
                                      (Stmt.expr
                                        (Expr.returnExpr (some (Expr.lit (Lit.bool false))))
                                        true)])
                                  none)
                                false),
                              (Stmt.expr
                                (Expr.ite
                                  (Expr.methodCall
                                    (Expr.field
                                      (Expr.path
                                        none
                                        (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                                      (Member.named "allocations"))
                                    "any"
                                    none
                                    [
                                      (Expr.closure
                                        false
                                        [(Pat.ident false false "a" none)]
                                        none
                                        (Expr.binary
                                          (Expr.field
                                            (Expr.path
                                              none
                                              (Path.mk
                                                false
                                                [(PathSegment.mk "a" PathArguments.none)]))
                                            (Member.named "live"))
                                          BinOp.and
                                          (Expr.methodCall
                                            (Expr.path
                                              none
                                              (Path.mk
                                                false
                                                [(PathSegment.mk "a" PathArguments.none)]))
                                            "overlaps"
                                            none
                                            [
                                              (Expr.path
                                                none
                                                (Path.mk
                                                  false
                                                  [(PathSegment.mk "addr" PathArguments.none)])),
                                              (Expr.path
                                                none
                                                (Path.mk
                                                  false
                                                  [(PathSegment.mk "size" PathArguments.none)]))])))])
                                  (Block.mk
                                    [
                                      (Stmt.expr
                                        (Expr.returnExpr (some (Expr.lit (Lit.bool false))))
                                        true)])
                                  none)
                                false),
                              (Stmt.expr (Expr.lit (Lit.bool true)) false)])))])))
              none),
            (Stmt.letStmt
              []
              (Pat.ident false false "allocation" none)
              (some
                (Expr.struct
                  none
                  (Path.mk false [(PathSegment.mk "Allocation" PathArguments.none)])
                  [
                    (FieldValue.mk
                      []
                      (Member.named "addr")
                      true
                      (Expr.path none (Path.mk false [(PathSegment.mk "addr" PathArguments.none)]))),
                    (FieldValue.mk
                      []
                      (Member.named "align")
                      true
                      (Expr.path none (Path.mk false [(PathSegment.mk "align" PathArguments.none)]))),
                    (FieldValue.mk
                      []
                      (Member.named "kind")
                      true
                      (Expr.path none (Path.mk false [(PathSegment.mk "kind" PathArguments.none)]))),
                    (FieldValue.mk [] (Member.named "live") false (Expr.lit (Lit.bool true))),
                    (FieldValue.mk
                      []
                      (Member.named "data")
                      false
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
                              []))))),
                    (FieldValue.mk
                      []
                      (Member.named "extra")
                      false
                      (Expr.path
                        none
                        (Path.mk false [(PathSegment.mk "alloc_extra" PathArguments.none)])))]
                  false
                  none))
              none),
            (Stmt.letStmt
              []
              (Pat.ident false false "id" none)
              (some
                (Expr.call
                  (Expr.path none (Path.mk false [(PathSegment.mk "AllocId" PathArguments.none)]))
                  [
                    (Expr.methodCall
                      (Expr.field
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                        (Member.named "allocations"))
                      "len"
                      none
                      [])]))
              none),
            (Stmt.expr
              (Expr.methodCall
                (Expr.field
                  (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                  (Member.named "allocations"))
                "push"
                none
                [
                  (Expr.path
                    none
                    (Path.mk false [(PathSegment.mk "allocation" PathArguments.none)]))])
              true),
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
                                  (Path.mk false [(PathSegment.mk "id" PathArguments.none)])),
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "prov_extra" PathArguments.none)]))])]))]
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
                                  (PathSegment.mk
                                    "Provenance"
                                    (PathArguments.angleBracketed
                                      false
                                      [
                                        (GenericArgument.type
                                          (Ty.path
                                            none
                                            (Path.mk
                                              false
                                              [(PathSegment.mk "ProvExtra" PathArguments.none)])))]))])))]))]))),
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
              (Ty.path none (Path.mk false [(PathSegment.mk "Align" PathArguments.none)]))),
            (FnArg.typed
              []
              (Pat.ident false false "handle_extra" none)
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
                                  (Path.mk false [(PathSegment.mk "AllocExtra" PathArguments.none)]))),
                              (Ty.path
                                none
                                (Path.mk false [(PathSegment.mk "ProvExtra" PathArguments.none)]))]
                            (some
                              (Ty.path
                                none
                                (Path.mk false [(PathSegment.mk "Result" PathArguments.none)])))))]))]))]
          false
          (some (Ty.path none (Path.mk false [(PathSegment.mk "Result" PathArguments.none)]))))
        (Block.mk
          [
            (Stmt.letStmt
              []
              (Pat.tupleStruct
                none
                (Path.mk false [(PathSegment.mk "Some" PathArguments.none)])
                [
                  (Pat.tuple
                    [(Pat.ident false false "id" none), (Pat.ident false false "prov_extra" none)])])
              (some
                (Expr.field
                  (Expr.path none (Path.mk false [(PathSegment.mk "ptr" PathArguments.none)]))
                  (Member.named "provenance")))
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
                              [(Expr.lit (Lit.str "deallocating invalid pointer"))]
                              false)))
                        false)])))),
            (Stmt.letStmt
              []
              (Pat.ident false true "allocation" none)
              (some
                (Expr.index
                  (Expr.field
                    (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                    (Member.named "allocations"))
                  (Expr.field
                    (Expr.path none (Path.mk false [(PathSegment.mk "id" PathArguments.none)]))
                    (Member.unnamed 0))))
              none),
            (Stmt.expr
              (Expr.ite
                (Expr.unary
                  UnOp.not
                  (Expr.field
                    (Expr.path
                      none
                      (Path.mk false [(PathSegment.mk "allocation" PathArguments.none)]))
                    (Member.named "live")))
                (Block.mk
                  [
                    (Stmt.macro
                      []
                      (Macro.mk
                        (Path.mk false [(PathSegment.mk "throw_ub" PathArguments.none)])
                        MacroDelimiter.paren
                        (MacroBody.exprs [(Expr.lit (Lit.str "double-free"))] false))
                      true)])
                none)
              false),
            (Stmt.expr
              (Expr.ite
                (Expr.binary
                  (Expr.field
                    (Expr.path none (Path.mk false [(PathSegment.mk "ptr" PathArguments.none)]))
                    (Member.named "addr"))
                  BinOp.ne
                  (Expr.field
                    (Expr.path
                      none
                      (Path.mk false [(PathSegment.mk "allocation" PathArguments.none)]))
                    (Member.named "addr")))
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
                                "deallocating with pointer not to the beginning of its allocation"))]
                          false))
                      true)])
                none)
              false),
            (Stmt.expr
              (Expr.ite
                (Expr.binary
                  (Expr.path none (Path.mk false [(PathSegment.mk "kind" PathArguments.none)]))
                  BinOp.ne
                  (Expr.field
                    (Expr.path
                      none
                      (Path.mk false [(PathSegment.mk "allocation" PathArguments.none)]))
                    (Member.named "kind")))
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
                              (Lit.str "deallocating {:?} memory with {:?} deallocation operation")),
                            (Expr.field
                              (Expr.path
                                none
                                (Path.mk false [(PathSegment.mk "allocation" PathArguments.none)]))
                              (Member.named "kind")),
                            (Expr.path
                              none
                              (Path.mk false [(PathSegment.mk "kind" PathArguments.none)]))]
                          false))
                      true)])
                none)
              false),
            (Stmt.expr
              (Expr.ite
                (Expr.binary
                  (Expr.path none (Path.mk false [(PathSegment.mk "size" PathArguments.none)]))
                  BinOp.ne
                  (Expr.methodCall
                    (Expr.path
                      none
                      (Path.mk false [(PathSegment.mk "allocation" PathArguments.none)]))
                    "size"
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
                          [(Expr.lit (Lit.str "deallocating with incorrect size information"))]
                          false))
                      true)])
                none)
              false),
            (Stmt.expr
              (Expr.ite
                (Expr.binary
                  (Expr.path none (Path.mk false [(PathSegment.mk "align" PathArguments.none)]))
                  BinOp.ne
                  (Expr.field
                    (Expr.path
                      none
                      (Path.mk false [(PathSegment.mk "allocation" PathArguments.none)]))
                    (Member.named "align")))
                (Block.mk
                  [
                    (Stmt.macro
                      []
                      (Macro.mk
                        (Path.mk false [(PathSegment.mk "throw_ub" PathArguments.none)])
                        MacroDelimiter.paren
                        (MacroBody.exprs
                          [(Expr.lit (Lit.str "deallocating with incorrect alignment information"))]
                          false))
                      true)])
                none)
              false),
            (Stmt.expr
              (Expr.tryExpr
                (Expr.call
                  (Expr.path
                    none
                    (Path.mk false [(PathSegment.mk "handle_extra" PathArguments.none)]))
                  [
                    (Expr.reference
                      true
                      (Expr.field
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "allocation" PathArguments.none)]))
                        (Member.named "extra"))),
                    (Expr.path
                      none
                      (Path.mk false [(PathSegment.mk "prov_extra" PathArguments.none)]))]))
              true),
            (Stmt.expr
              (Expr.assign
                (Expr.field
                  (Expr.path
                    none
                    (Path.mk false [(PathSegment.mk "allocation" PathArguments.none)]))
                  (Member.named "live"))
                (Expr.lit (Lit.bool false)))
              true),
            (Stmt.expr
              (Expr.methodCall
                (Expr.field
                  (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                  (Member.named "allocations"))
                "set"
                none
                [
                  (Expr.field
                    (Expr.path none (Path.mk false [(PathSegment.mk "id" PathArguments.none)]))
                    (Member.unnamed 0)),
                  (Expr.path
                    none
                    (Path.mk false [(PathSegment.mk "allocation" PathArguments.none)]))])
              true),
            (Stmt.expr
              (Expr.call
                (Expr.path none (Path.mk false [(PathSegment.mk "ret" PathArguments.none)]))
                [(Expr.tuple [])])
              false)]))])

/-- `spec/mem/basic.md:193` -/
def impl_BasicMemory__check_ptr : Item :=
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
          none),
        (GenericParam.type [] "ProvExtra" [] none),
        (GenericParam.type [] "AllocExtra" [] none)]
      [])
    false
    none
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
                  (Ty.path none (Path.mk false [(PathSegment.mk "ProvExtra" PathArguments.none)]))),
                (GenericArgument.type
                  (Ty.path none (Path.mk false [(PathSegment.mk "AllocExtra" PathArguments.none)])))]))]))
    [
      (ImplItem.fn
        [
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue
              " Check if the given pointer is dereferenceable for an access of the given")),
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue " length. For dereferenceable, return the allocation ID and")),
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue
              " offset; this can be missing for invalid pointers and accesses of size 0."))]
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
                                    "Provenance"
                                    (PathArguments.angleBracketed
                                      false
                                      [
                                        (GenericArgument.type
                                          (Ty.path
                                            none
                                            (Path.mk
                                              false
                                              [(PathSegment.mk "ProvExtra" PathArguments.none)])))]))])))]))]))),
            (FnArg.typed
              []
              (Pat.ident false false "len" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "Size" PathArguments.none)])))]
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
                                        (Ty.tuple
                                          [
                                            (Ty.path
                                              none
                                              (Path.mk
                                                false
                                                [(PathSegment.mk "AllocId" PathArguments.none)])),
                                            (Ty.path
                                              none
                                              (Path.mk
                                                false
                                                [(PathSegment.mk "ProvExtra" PathArguments.none)])),
                                            (Ty.path
                                              none
                                              (Path.mk
                                                false
                                                [(PathSegment.mk "Size" PathArguments.none)]))]))]))])))]))]))))
        (Block.mk
          [
            (Stmt.expr
              (Expr.ite
                (Expr.methodCall
                  (Expr.path none (Path.mk false [(PathSegment.mk "len" PathArguments.none)]))
                  "is_zero"
                  none
                  [])
                (Block.mk
                  [
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
                                (Path.mk false [(PathSegment.mk "None" PathArguments.none)]))])))
                      true)])
                none)
              false),
            (Stmt.letStmt
              []
              (Pat.tupleStruct
                none
                (Path.mk false [(PathSegment.mk "Some" PathArguments.none)])
                [
                  (Pat.tuple
                    [(Pat.ident false false "id" none), (Pat.ident false false "prov_extra" none)])])
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
                          (Path.mk false [(PathSegment.mk "throw_ub" PathArguments.none)])
                          MacroDelimiter.paren
                          (MacroBody.exprs
                            [(Expr.lit (Lit.str "dereferencing pointer without provenance"))]
                            false))
                        true)])))),
            (Stmt.letStmt
              []
              (Pat.ident false false "allocation" none)
              (some
                (Expr.index
                  (Expr.field
                    (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                    (Member.named "allocations"))
                  (Expr.field
                    (Expr.path none (Path.mk false [(PathSegment.mk "id" PathArguments.none)]))
                    (Member.unnamed 0))))
              none),
            (Stmt.expr
              (Expr.ite
                (Expr.unary
                  UnOp.not
                  (Expr.field
                    (Expr.path
                      none
                      (Path.mk false [(PathSegment.mk "allocation" PathArguments.none)]))
                    (Member.named "live")))
                (Block.mk
                  [
                    (Stmt.macro
                      []
                      (Macro.mk
                        (Path.mk false [(PathSegment.mk "throw_ub" PathArguments.none)])
                        MacroDelimiter.paren
                        (MacroBody.exprs
                          [(Expr.lit (Lit.str "dereferencing pointer to dead allocation"))]
                          false))
                      true)])
                none)
              false),
            (Stmt.letStmt
              []
              (Pat.ident false false "offset_in_alloc" none)
              (some
                (Expr.binary
                  (Expr.field
                    (Expr.path none (Path.mk false [(PathSegment.mk "ptr" PathArguments.none)]))
                    (Member.named "addr"))
                  BinOp.sub
                  (Expr.field
                    (Expr.path
                      none
                      (Path.mk false [(PathSegment.mk "allocation" PathArguments.none)]))
                    (Member.named "addr"))))
              none),
            (Stmt.expr
              (Expr.ite
                (Expr.binary
                  (Expr.binary
                    (Expr.path
                      none
                      (Path.mk false [(PathSegment.mk "offset_in_alloc" PathArguments.none)]))
                    BinOp.lt
                    (Expr.lit (Lit.int 0 "")))
                  BinOp.or
                  (Expr.binary
                    (Expr.binary
                      (Expr.path
                        none
                        (Path.mk false [(PathSegment.mk "offset_in_alloc" PathArguments.none)]))
                      BinOp.add
                      (Expr.methodCall
                        (Expr.path none (Path.mk false [(PathSegment.mk "len" PathArguments.none)]))
                        "bytes"
                        none
                        []))
                    BinOp.gt
                    (Expr.methodCall
                      (Expr.methodCall
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "allocation" PathArguments.none)]))
                        "size"
                        none
                        [])
                      "bytes"
                      none
                      [])))
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
                              (Lit.str "dereferencing pointer outside the bounds of its allocation"))]
                          false))
                      true)])
                none)
              false),
            (Stmt.expr
              (Expr.call
                (Expr.path none (Path.mk false [(PathSegment.mk "ret" PathArguments.none)]))
                [
                  (Expr.call
                    (Expr.path none (Path.mk false [(PathSegment.mk "Some" PathArguments.none)]))
                    [
                      (Expr.tuple
                        [
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "id" PathArguments.none)])),
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "prov_extra" PathArguments.none)])),
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
                                (Expr.path
                                  none
                                  (Path.mk
                                    false
                                    [(PathSegment.mk "offset_in_alloc" PathArguments.none)]))])
                            "unwrap"
                            none
                            [])])])])
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
                                  (PathSegment.mk
                                    "Provenance"
                                    (PathArguments.angleBracketed
                                      false
                                      [
                                        (GenericArgument.type
                                          (Ty.path
                                            none
                                            (Path.mk
                                              false
                                              [(PathSegment.mk "ProvExtra" PathArguments.none)])))]))])))]))]))),
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
                                                (PathSegment.mk
                                                  "Provenance"
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
                                                                "ProvExtra"
                                                                PathArguments.none)])))]))])))]))])))]))]))),
            (FnArg.typed
              []
              (Pat.ident false false "align" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "Align" PathArguments.none)]))),
            (FnArg.typed
              []
              (Pat.ident false false "handle_extra" none)
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
                                  (Path.mk false [(PathSegment.mk "AllocExtra" PathArguments.none)]))),
                              (Ty.path
                                none
                                (Path.mk false [(PathSegment.mk "ProvExtra" PathArguments.none)])),
                              (Ty.path
                                none
                                (Path.mk false [(PathSegment.mk "Offset" PathArguments.none)]))]
                            (some
                              (Ty.path
                                none
                                (Path.mk false [(PathSegment.mk "Result" PathArguments.none)])))))]))]))]
          false
          (some (Ty.path none (Path.mk false [(PathSegment.mk "Result" PathArguments.none)]))))
        (Block.mk
          [
            (Stmt.expr
              (Expr.ite
                (Expr.unary
                  UnOp.not
                  (Expr.methodCall
                    (Expr.path none (Path.mk false [(PathSegment.mk "align" PathArguments.none)]))
                    "is_aligned"
                    none
                    [
                      (Expr.field
                        (Expr.path none (Path.mk false [(PathSegment.mk "ptr" PathArguments.none)]))
                        (Member.named "addr"))]))
                (Block.mk
                  [
                    (Stmt.macro
                      []
                      (Macro.mk
                        (Path.mk false [(PathSegment.mk "throw_ub" PathArguments.none)])
                        MacroDelimiter.paren
                        (MacroBody.exprs
                          [(Expr.lit (Lit.str "store to a misaligned pointer"))]
                          false))
                      true)])
                none)
              false),
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
            (Stmt.letStmt
              []
              (Pat.tupleStruct
                none
                (Path.mk false [(PathSegment.mk "Some" PathArguments.none)])
                [
                  (Pat.tuple
                    [
                      (Pat.ident false false "id" none),
                      (Pat.ident false false "prov_extra" none),
                      (Pat.ident false false "offset" none)])])
              (some
                (Expr.tryExpr
                  (Expr.methodCall
                    (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                    "check_ptr"
                    none
                    [
                      (Expr.path none (Path.mk false [(PathSegment.mk "ptr" PathArguments.none)])),
                      (Expr.path none (Path.mk false [(PathSegment.mk "size" PathArguments.none)]))])))
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
                                (Path.mk false [(PathSegment.mk "ret" PathArguments.none)]))
                              [(Expr.tuple [])])))
                        true)])))),
            (Stmt.letStmt
              []
              (Pat.ident false true "allocation" none)
              (some
                (Expr.index
                  (Expr.field
                    (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                    (Member.named "allocations"))
                  (Expr.field
                    (Expr.path none (Path.mk false [(PathSegment.mk "id" PathArguments.none)]))
                    (Member.unnamed 0))))
              none),
            (Stmt.expr
              (Expr.tryExpr
                (Expr.call
                  (Expr.path
                    none
                    (Path.mk false [(PathSegment.mk "handle_extra" PathArguments.none)]))
                  [
                    (Expr.reference
                      true
                      (Expr.field
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "allocation" PathArguments.none)]))
                        (Member.named "extra"))),
                    (Expr.path
                      none
                      (Path.mk false [(PathSegment.mk "prov_extra" PathArguments.none)])),
                    (Expr.path none (Path.mk false [(PathSegment.mk "offset" PathArguments.none)]))]))
              true),
            (Stmt.expr
              (Expr.methodCall
                (Expr.field
                  (Expr.path
                    none
                    (Path.mk false [(PathSegment.mk "allocation" PathArguments.none)]))
                  (Member.named "data"))
                "write_subslice_at_index"
                none
                [
                  (Expr.methodCall
                    (Expr.path none (Path.mk false [(PathSegment.mk "offset" PathArguments.none)]))
                    "bytes"
                    none
                    []),
                  (Expr.path none (Path.mk false [(PathSegment.mk "bytes" PathArguments.none)]))])
              true),
            (Stmt.expr
              (Expr.methodCall
                (Expr.field
                  (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                  (Member.named "allocations"))
                "set"
                none
                [
                  (Expr.field
                    (Expr.path none (Path.mk false [(PathSegment.mk "id" PathArguments.none)]))
                    (Member.unnamed 0)),
                  (Expr.path
                    none
                    (Path.mk false [(PathSegment.mk "allocation" PathArguments.none)]))])
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
                                  (PathSegment.mk
                                    "Provenance"
                                    (PathArguments.angleBracketed
                                      false
                                      [
                                        (GenericArgument.type
                                          (Ty.path
                                            none
                                            (Path.mk
                                              false
                                              [(PathSegment.mk "ProvExtra" PathArguments.none)])))]))])))]))]))),
            (FnArg.typed
              []
              (Pat.ident false false "len" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "Size" PathArguments.none)]))),
            (FnArg.typed
              []
              (Pat.ident false false "align" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "Align" PathArguments.none)]))),
            (FnArg.typed
              []
              (Pat.ident false false "handle_extra" none)
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
                                  (Path.mk false [(PathSegment.mk "AllocExtra" PathArguments.none)]))),
                              (Ty.path
                                none
                                (Path.mk false [(PathSegment.mk "ProvExtra" PathArguments.none)])),
                              (Ty.path
                                none
                                (Path.mk false [(PathSegment.mk "Offset" PathArguments.none)]))]
                            (some
                              (Ty.path
                                none
                                (Path.mk false [(PathSegment.mk "Result" PathArguments.none)])))))]))]))]
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
                                                              "Provenance"
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
                                                                            "ProvExtra"
                                                                            PathArguments.none)])))]))])))]))])))]))])))]))]))))
        (Block.mk
          [
            (Stmt.expr
              (Expr.ite
                (Expr.unary
                  UnOp.not
                  (Expr.methodCall
                    (Expr.path none (Path.mk false [(PathSegment.mk "align" PathArguments.none)]))
                    "is_aligned"
                    none
                    [
                      (Expr.field
                        (Expr.path none (Path.mk false [(PathSegment.mk "ptr" PathArguments.none)]))
                        (Member.named "addr"))]))
                (Block.mk
                  [
                    (Stmt.macro
                      []
                      (Macro.mk
                        (Path.mk false [(PathSegment.mk "throw_ub" PathArguments.none)])
                        MacroDelimiter.paren
                        (MacroBody.exprs
                          [(Expr.lit (Lit.str "load from a misaligned pointer"))]
                          false))
                      true)])
                none)
              false),
            (Stmt.letStmt
              []
              (Pat.tupleStruct
                none
                (Path.mk false [(PathSegment.mk "Some" PathArguments.none)])
                [
                  (Pat.tuple
                    [
                      (Pat.ident false false "id" none),
                      (Pat.ident false false "prov_extra" none),
                      (Pat.ident false false "offset" none)])])
              (some
                (Expr.tryExpr
                  (Expr.methodCall
                    (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                    "check_ptr"
                    none
                    [
                      (Expr.path none (Path.mk false [(PathSegment.mk "ptr" PathArguments.none)])),
                      (Expr.path none (Path.mk false [(PathSegment.mk "len" PathArguments.none)]))])))
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
                                (Path.mk false [(PathSegment.mk "ret" PathArguments.none)]))
                              [
                                (Expr.macro
                                  (Macro.mk
                                    (Path.mk false [(PathSegment.mk "list" PathArguments.none)])
                                    MacroDelimiter.bracket
                                    (MacroBody.exprs [] false)))])))
                        true)])))),
            (Stmt.letStmt
              []
              (Pat.ident false true "allocation" none)
              (some
                (Expr.index
                  (Expr.field
                    (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                    (Member.named "allocations"))
                  (Expr.field
                    (Expr.path none (Path.mk false [(PathSegment.mk "id" PathArguments.none)]))
                    (Member.unnamed 0))))
              none),
            (Stmt.expr
              (Expr.tryExpr
                (Expr.call
                  (Expr.path
                    none
                    (Path.mk false [(PathSegment.mk "handle_extra" PathArguments.none)]))
                  [
                    (Expr.reference
                      true
                      (Expr.field
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "allocation" PathArguments.none)]))
                        (Member.named "extra"))),
                    (Expr.path
                      none
                      (Path.mk false [(PathSegment.mk "prov_extra" PathArguments.none)])),
                    (Expr.path none (Path.mk false [(PathSegment.mk "offset" PathArguments.none)]))]))
              true),
            (Stmt.expr
              (Expr.methodCall
                (Expr.field
                  (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                  (Member.named "allocations"))
                "set"
                none
                [
                  (Expr.field
                    (Expr.path none (Path.mk false [(PathSegment.mk "id" PathArguments.none)]))
                    (Member.unnamed 0)),
                  (Expr.path
                    none
                    (Path.mk false [(PathSegment.mk "allocation" PathArguments.none)]))])
              true),
            (Stmt.expr
              (Expr.call
                (Expr.path none (Path.mk false [(PathSegment.mk "ret" PathArguments.none)]))
                [
                  (Expr.methodCall
                    (Expr.field
                      (Expr.path
                        none
                        (Path.mk false [(PathSegment.mk "allocation" PathArguments.none)]))
                      (Member.named "data"))
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
                        (Expr.path none (Path.mk false [(PathSegment.mk "len" PathArguments.none)]))
                        "bytes"
                        none
                        [])])])
              false)]))])

/-- `spec/mem/basic.md:282` -/
def impl_BasicMemory__leak_check : Item :=
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
          none),
        (GenericParam.type [] "ProvExtra" [] none),
        (GenericParam.type [] "AllocExtra" [] none)]
      [])
    false
    none
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
                  (Ty.path none (Path.mk false [(PathSegment.mk "ProvExtra" PathArguments.none)]))),
                (GenericArgument.type
                  (Ty.path none (Path.mk false [(PathSegment.mk "AllocExtra" PathArguments.none)])))]))]))
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
          "leak_check"
          (Generics.mk [] [])
          [(FnArg.receiver [] true none false none)]
          false
          (some (Ty.path none (Path.mk false [(PathSegment.mk "Result" PathArguments.none)]))))
        (Block.mk
          [
            (Stmt.item
              (Item.use [] Visibility.inherited false (UseTree.path "AllocationKind" UseTree.glob))),
            (Stmt.expr
              (Expr.forLoop
                none
                (Pat.ident false false "allocation" none)
                (Expr.field
                  (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                  (Member.named "allocations"))
                (Block.mk
                  [
                    (Stmt.expr
                      (Expr.ite
                        (Expr.field
                          (Expr.path
                            none
                            (Path.mk false [(PathSegment.mk "allocation" PathArguments.none)]))
                          (Member.named "live"))
                        (Block.mk
                          [
                            (Stmt.expr
                              (Expr.matchExpr
                                (Expr.field
                                  (Expr.path
                                    none
                                    (Path.mk
                                      false
                                      [(PathSegment.mk "allocation" PathArguments.none)]))
                                  (Member.named "kind"))
                                [
                                  (Arm.mk
                                    []
                                    (Pat.ident false false "Heap" none)
                                    none
                                    (Expr.macro
                                      (Macro.mk
                                        (Path.mk
                                          false
                                          [(PathSegment.mk "throw_memory_leak" PathArguments.none)])
                                        MacroDelimiter.paren
                                        (MacroBody.exprs [] false)))),
                                  (Arm.mk
                                    []
                                    (Pat.or
                                      [
                                        (Pat.ident false false "Global" none),
                                        (Pat.ident false false "Function" none),
                                        (Pat.ident false false "Stack" none),
                                        (Pat.ident false false "VTable" none)])
                                    none
                                    (Expr.block none (Block.mk [])))])
                              false)])
                        none)
                      false)]))
              false),
            (Stmt.expr
              (Expr.call
                (Expr.path none (Path.mk false [(PathSegment.mk "ret" PathArguments.none)]))
                [(Expr.tuple [])])
              false)]))])

/-- `spec/mem/basic.md:305` -/
def impl_BasicMemory_for_Memory__Provenance : Item :=
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
            "BasicMemory"
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
        (Ty.path
          none
          (Path.mk
            false
            [
              (PathSegment.mk
                "Provenance"
                (PathArguments.angleBracketed false [(GenericArgument.type (Ty.tuple []))]))]))),
      (ImplItem.type
        [(Attr.mk true "doc" (AttrMeta.nameValue " The target is given by the generic parameter."))]
        Visibility.inherited
        false
        "T"
        (Generics.mk [] [])
        (Ty.path none (Path.mk false [(PathSegment.mk "T" PathArguments.none)]))),
      (ImplItem.type
        [
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue " The basic memory model does not need any per-frame data,")),
          (Attr.mk true "doc" (AttrMeta.nameValue " so we set `FrameExtra` to the unit type."))]
        Visibility.inherited
        false
        "FrameExtra"
        (Generics.mk [] [])
        (Ty.tuple [])),
      (ImplItem.type
        [
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue
              " The basic memory model does not have any configuration parameters."))]
        Visibility.inherited
        false
        "Params"
        (Generics.mk [] [])
        (Ty.tuple [])),
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
          [(FnArg.typed [] (Pat.ident false false "_params" none) (Ty.tuple []))]
          false
          (some (Ty.path none (Path.mk false [(PathSegment.mk "Self" PathArguments.none)]))))
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
            (Stmt.expr
              (Expr.methodCall
                (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                "allocate"
                none
                [
                  (Expr.path none (Path.mk false [(PathSegment.mk "kind" PathArguments.none)])),
                  (Expr.path none (Path.mk false [(PathSegment.mk "size" PathArguments.none)])),
                  (Expr.path none (Path.mk false [(PathSegment.mk "align" PathArguments.none)])),
                  (Expr.tuple []),
                  (Expr.tuple [])])
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
                (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                "deallocate"
                none
                [
                  (Expr.path none (Path.mk false [(PathSegment.mk "ptr" PathArguments.none)])),
                  (Expr.path none (Path.mk false [(PathSegment.mk "kind" PathArguments.none)])),
                  (Expr.path none (Path.mk false [(PathSegment.mk "size" PathArguments.none)])),
                  (Expr.path none (Path.mk false [(PathSegment.mk "align" PathArguments.none)])),
                  (Expr.closure
                    false
                    [(Pat.tuple []), (Pat.tuple [])]
                    none
                    (Expr.call
                      (Expr.path none (Path.mk false [(PathSegment.mk "ret" PathArguments.none)]))
                      [(Expr.tuple [])]))])
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
            (Stmt.expr
              (Expr.methodCall
                (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                "store"
                none
                [
                  (Expr.path none (Path.mk false [(PathSegment.mk "ptr" PathArguments.none)])),
                  (Expr.path none (Path.mk false [(PathSegment.mk "bytes" PathArguments.none)])),
                  (Expr.path none (Path.mk false [(PathSegment.mk "align" PathArguments.none)])),
                  (Expr.closure
                    false
                    [(Pat.tuple []), (Pat.tuple []), (Pat.ident false false "_offset" none)]
                    none
                    (Expr.call
                      (Expr.path none (Path.mk false [(PathSegment.mk "ret" PathArguments.none)]))
                      [(Expr.tuple [])]))])
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
                (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                "load"
                none
                [
                  (Expr.path none (Path.mk false [(PathSegment.mk "ptr" PathArguments.none)])),
                  (Expr.path none (Path.mk false [(PathSegment.mk "len" PathArguments.none)])),
                  (Expr.path none (Path.mk false [(PathSegment.mk "align" PathArguments.none)])),
                  (Expr.closure
                    false
                    [(Pat.tuple []), (Pat.tuple []), (Pat.ident false false "_offset" none)]
                    none
                    (Expr.call
                      (Expr.path none (Path.mk false [(PathSegment.mk "ret" PathArguments.none)]))
                      [(Expr.tuple [])]))])
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
                  (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
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
        (Block.mk [(Stmt.expr (Expr.tuple []) false)])),
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
                (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                "leak_check"
                none
                [])
              false)]))])

/-- All items of `spec/mem/basic.md`, in source order, with provenance. -/
def items : List SourceItem :=
  [
    (SourceItem.mk
      "struct_AllocId"
      18
      "8d6b5cdd7c0720f368aa792e4f20c2f4526cc7f355e0be574c2921a269be24d7"
      struct_AllocId),
    (SourceItem.mk
      "type_Provenance"
      20
      "ea58ef323b06398ce80b59bb3a1d0ecc890680af6bf33c122e4fe5acbf46dfe2"
      type_Provenance),
    (SourceItem.mk
      "struct_Allocation"
      26
      "598a66ac40812bf2f59ef2429e143834673fa949308e72eabb8618d3ef8d9ba7"
      struct_Allocation),
    (SourceItem.mk
      "struct_BasicMemory"
      47
      "9181a13db6fa1c5fbc87fa11895878f1fe0f7bb2ab20cb6b1aa6219243b73a32"
      struct_BasicMemory),
    (SourceItem.mk
      "impl_BasicMemory__new"
      54
      "0c860e6c746fd988eca5c7cc964903d318890599f35319b0a37f406ba69473a1"
      impl_BasicMemory__new),
    (SourceItem.mk
      "impl_Allocation__size"
      66
      "fe931d69e3e3f52a21a11a90aeec596314d94d5fddc0fdd775b8f000375b74d8"
      impl_Allocation__size),
    (SourceItem.mk
      "impl_BasicMemory__allocate"
      91
      "7032eb855841319cd9c9d20afb80bdea2eebd06403d9762ec845116cfc138bf3"
      impl_BasicMemory__allocate),
    (SourceItem.mk
      "impl_BasicMemory__check_ptr"
      193
      "548843ba7ad0dd6a5ad1c78d66290bc78b80f59ed466ec7c000691e5cac53684"
      impl_BasicMemory__check_ptr),
    (SourceItem.mk
      "impl_BasicMemory__leak_check"
      282
      "d014f502cbeec3f75833ad95eec35240fc231c114ccecb1dfeb3cdd4f38e5e91"
      impl_BasicMemory__leak_check),
    (SourceItem.mk
      "impl_BasicMemory_for_Memory__Provenance"
      305
      "66210899d6f2cb4c3a8f649993b1e5bf4b8e983ffc6b6a5ce37fbd3305eb596a"
      impl_BasicMemory_for_Memory__Provenance)]

end MiniRustSpec.Gen.Items.Mem.Basic
