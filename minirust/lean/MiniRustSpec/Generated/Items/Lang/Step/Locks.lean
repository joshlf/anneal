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
`spec/lang/step/locks.md` (commit `d821c6e3`), one Lean definition per item, in source order.
-/

import MiniRustSpec.Meta.Syntax

set_option maxRecDepth 100000

namespace MiniRustSpec.Gen.Items.Lang.Step.Locks

open MiniRustSpec.Syntax

/-- Path of the upstream file these items were extracted from. -/
def sourceFile : String := "spec/lang/step/locks.md"

/-- SHA-256 of the upstream file. -/
def sourceSha256 : String := "385edb3568484f685f7c6ec9511f0d4f269e27a10d54eef253f2c82865ee73a6"

/-- `spec/lang/step/locks.md:9` -/
def enum_LockState : Item :=
  (Item.enum
    []
    Visibility.pub
    "LockState"
    (Generics.mk [] [])
    [
      (Variant.mk [] "Unlocked" Fields.unit none),
      (Variant.mk
        []
        "LockedBy"
        (Fields.unnamed
          [
            (Field.mk
              []
              Visibility.inherited
              none
              (Ty.path none (Path.mk false [(PathSegment.mk "ThreadId" PathArguments.none)])))])
        none)])

/-- `spec/lang/step/locks.md:14` -/
def type_LockId : Item :=
  (Item.type
    []
    Visibility.pub
    "LockId"
    (Generics.mk [] [])
    (Ty.path none (Path.mk false [(PathSegment.mk "Int" PathArguments.none)])))

/-- `spec/lang/step/locks.md:22` -/
def impl_Machine__lock_create : Item :=
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
        Visibility.pub
        false
        (Signature.mk
          false
          false
          false
          none
          "lock_create"
          (Generics.mk [] [])
          [(FnArg.receiver [] true none true none)]
          false
          (some (Ty.path none (Path.mk false [(PathSegment.mk "LockId" PathArguments.none)]))))
        (Block.mk
          [
            (Stmt.letStmt
              []
              (Pat.ident false false "id" none)
              (some
                (Expr.methodCall
                  (Expr.field
                    (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                    (Member.named "locks"))
                  "len"
                  none
                  []))
              none),
            (Stmt.expr
              (Expr.methodCall
                (Expr.field
                  (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                  (Member.named "locks"))
                "push"
                none
                [
                  (Expr.path
                    none
                    (Path.mk
                      false
                      [
                        (PathSegment.mk "LockState" PathArguments.none),
                        (PathSegment.mk "Unlocked" PathArguments.none)]))])
              true),
            (Stmt.expr
              (Expr.path none (Path.mk false [(PathSegment.mk "id" PathArguments.none)]))
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
          "lock_acquire"
          (Generics.mk [] [])
          [
            (FnArg.receiver [] true none true none),
            (FnArg.typed
              []
              (Pat.ident false false "lock_id" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "LockId" PathArguments.none)])))]
          false
          (some (Ty.path none (Path.mk false [(PathSegment.mk "Result" PathArguments.none)]))))
        (Block.mk
          [
            (Stmt.letStmt
              []
              (Pat.ident false false "active" none)
              (some
                (Expr.field
                  (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                  (Member.named "active_thread")))
              none),
            (Stmt.letStmt
              []
              (Pat.tupleStruct
                none
                (Path.mk false [(PathSegment.mk "Some" PathArguments.none)])
                [(Pat.ident false false "lock" none)])
              (some
                (Expr.methodCall
                  (Expr.field
                    (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                    (Member.named "locks"))
                  "get"
                  none
                  [(Expr.path none (Path.mk false [(PathSegment.mk "lock_id" PathArguments.none)]))]))
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
                            [(Expr.lit (Lit.str "acquiring non-existing lock"))]
                            false))
                        true)])))),
            (Stmt.expr
              (Expr.matchExpr
                (Expr.path none (Path.mk false [(PathSegment.mk "lock" PathArguments.none)]))
                [
                  (Arm.mk
                    []
                    (Pat.path
                      none
                      (Path.mk
                        false
                        [
                          (PathSegment.mk "LockState" PathArguments.none),
                          (PathSegment.mk "Unlocked" PathArguments.none)]))
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
                                (Member.named "locks"))
                              "mutate_at"
                              none
                              [
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "lock_id" PathArguments.none)])),
                                (Expr.closure
                                  false
                                  [(Pat.ident false false "lock_state" none)]
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
                                                (Path.mk
                                                  false
                                                  [(PathSegment.mk "lock_state" PathArguments.none)])))
                                            (Expr.call
                                              (Expr.path
                                                none
                                                (Path.mk
                                                  false
                                                  [
                                                    (PathSegment.mk "LockState" PathArguments.none),
                                                    (PathSegment.mk "LockedBy" PathArguments.none)]))
                                              [
                                                (Expr.path
                                                  none
                                                  (Path.mk
                                                    false
                                                    [(PathSegment.mk "active" PathArguments.none)]))]))
                                          true)])))])
                            true)]))),
                  (Arm.mk
                    []
                    (Pat.tupleStruct
                      none
                      (Path.mk
                        false
                        [
                          (PathSegment.mk "LockState" PathArguments.none),
                          (PathSegment.mk "LockedBy" PathArguments.none)])
                      [Pat.wild])
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
                                (Expr.path
                                  none
                                  (Path.mk false [(PathSegment.mk "active" PathArguments.none)])),
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
                                                      "BlockedOnLock"
                                                      PathArguments.none)]))
                                              [
                                                (Expr.path
                                                  none
                                                  (Path.mk
                                                    false
                                                    [(PathSegment.mk "lock_id" PathArguments.none)]))]))
                                          true)])))])
                            true)])))])
              false),
            (Stmt.expr
              (Expr.call
                (Expr.path none (Path.mk false [(PathSegment.mk "ret" PathArguments.none)]))
                [(Expr.tuple [])])
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
          "lock_release"
          (Generics.mk [] [])
          [
            (FnArg.receiver [] true none true none),
            (FnArg.typed
              []
              (Pat.ident false false "lock_id" none)
              (Ty.path none (Path.mk false [(PathSegment.mk "LockId" PathArguments.none)])))]
          false
          (some (Ty.path none (Path.mk false [(PathSegment.mk "NdResult" PathArguments.none)]))))
        (Block.mk
          [
            (Stmt.letStmt
              []
              (Pat.ident false false "active" none)
              (some
                (Expr.field
                  (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                  (Member.named "active_thread")))
              none),
            (Stmt.letStmt
              []
              (Pat.tupleStruct
                none
                (Path.mk false [(PathSegment.mk "Some" PathArguments.none)])
                [(Pat.ident false false "lock" none)])
              (some
                (Expr.methodCall
                  (Expr.field
                    (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                    (Member.named "locks"))
                  "get"
                  none
                  [(Expr.path none (Path.mk false [(PathSegment.mk "lock_id" PathArguments.none)]))]))
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
                            [(Expr.lit (Lit.str "releasing non-existing lock"))]
                            false))
                        true)])))),
            (Stmt.expr
              (Expr.matchExpr
                (Expr.path none (Path.mk false [(PathSegment.mk "lock" PathArguments.none)]))
                [
                  (Arm.mk
                    []
                    (Pat.tupleStruct
                      none
                      (Path.mk
                        false
                        [
                          (PathSegment.mk "LockState" PathArguments.none),
                          (PathSegment.mk "LockedBy" PathArguments.none)])
                      [(Pat.ident false false "thread_id" none)])
                    (some
                      (Expr.binary
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "thread_id" PathArguments.none)]))
                        BinOp.eq
                        (Expr.path
                          none
                          (Path.mk false [(PathSegment.mk "active" PathArguments.none)]))))
                    (Expr.block
                      none
                      (Block.mk
                        [
                          (Stmt.expr
                            (Expr.ite
                              (Expr.methodCall
                                (Expr.field
                                  (Expr.path
                                    none
                                    (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                                  (Member.named "threads"))
                                "any"
                                none
                                [
                                  (Expr.closure
                                    false
                                    [(Pat.ident false false "thread" none)]
                                    none
                                    (Expr.binary
                                      (Expr.field
                                        (Expr.path
                                          none
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "thread" PathArguments.none)]))
                                        (Member.named "state"))
                                      BinOp.eq
                                      (Expr.call
                                        (Expr.path
                                          none
                                          (Path.mk
                                            false
                                            [
                                              (PathSegment.mk "ThreadState" PathArguments.none),
                                              (PathSegment.mk "BlockedOnLock" PathArguments.none)]))
                                        [
                                          (Expr.path
                                            none
                                            (Path.mk
                                              false
                                              [(PathSegment.mk "lock_id" PathArguments.none)]))])))])
                              (Block.mk
                                [
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
                                                  (PathSegment.mk "ZERO" PathArguments.none)]))),
                                          (FieldValue.mk
                                            []
                                            (Member.named "end")
                                            false
                                            (Expr.call
                                              (Expr.path
                                                none
                                                (Path.mk
                                                  false
                                                  [
                                                    (PathSegment.mk "Int" PathArguments.none),
                                                    (PathSegment.mk "from" PathArguments.none)]))
                                              [
                                                (Expr.methodCall
                                                  (Expr.field
                                                    (Expr.path
                                                      none
                                                      (Path.mk
                                                        false
                                                        [(PathSegment.mk "self" PathArguments.none)]))
                                                    (Member.named "threads"))
                                                  "len"
                                                  none
                                                  [])])),
                                          (FieldValue.mk
                                            []
                                            (Member.named "divisor")
                                            false
                                            (Expr.path
                                              none
                                              (Path.mk
                                                false
                                                [
                                                  (PathSegment.mk "Int" PathArguments.none),
                                                  (PathSegment.mk "ONE" PathArguments.none)])))]
                                        false
                                        none))
                                    none),
                                  (Stmt.letStmt
                                    []
                                    (Pat.typed
                                      (Pat.ident false false "acquirer_id" none)
                                      (Ty.path
                                        none
                                        (Path.mk
                                          false
                                          [(PathSegment.mk "ThreadId" PathArguments.none)])))
                                    (some
                                      (Expr.tryExpr
                                        (Expr.call
                                          (Expr.path
                                            none
                                            (Path.mk
                                              false
                                              [(PathSegment.mk "pick" PathArguments.none)]))
                                          [
                                            (Expr.path
                                              none
                                              (Path.mk
                                                false
                                                [(PathSegment.mk "distr" PathArguments.none)])),
                                            (Expr.closure
                                              false
                                              [
                                                (Pat.typed
                                                  (Pat.ident false false "id" none)
                                                  (Ty.path
                                                    none
                                                    (Path.mk
                                                      false
                                                      [
                                                        (PathSegment.mk
                                                          "ThreadId"
                                                          PathArguments.none)])))]
                                              none
                                              (Expr.block
                                                none
                                                (Block.mk
                                                  [
                                                    (Stmt.letStmt
                                                      []
                                                      (Pat.tupleStruct
                                                        none
                                                        (Path.mk
                                                          false
                                                          [
                                                            (PathSegment.mk
                                                              "Some"
                                                              PathArguments.none)])
                                                        [(Pat.ident false false "thread" none)])
                                                      (some
                                                        (Expr.methodCall
                                                          (Expr.field
                                                            (Expr.path
                                                              none
                                                              (Path.mk
                                                                false
                                                                [
                                                                  (PathSegment.mk
                                                                    "self"
                                                                    PathArguments.none)]))
                                                            (Member.named "threads"))
                                                          "get"
                                                          none
                                                          [
                                                            (Expr.path
                                                              none
                                                              (Path.mk
                                                                false
                                                                [
                                                                  (PathSegment.mk
                                                                    "id"
                                                                    PathArguments.none)]))]))
                                                      (some
                                                        (Expr.block
                                                          none
                                                          (Block.mk
                                                            [
                                                              (Stmt.expr
                                                                (Expr.returnExpr
                                                                  (some (Expr.lit (Lit.bool false))))
                                                                true)])))),
                                                    (Stmt.expr
                                                      (Expr.binary
                                                        (Expr.field
                                                          (Expr.path
                                                            none
                                                            (Path.mk
                                                              false
                                                              [
                                                                (PathSegment.mk
                                                                  "thread"
                                                                  PathArguments.none)]))
                                                          (Member.named "state"))
                                                        BinOp.eq
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
                                                                  "BlockedOnLock"
                                                                  PathArguments.none)]))
                                                          [
                                                            (Expr.path
                                                              none
                                                              (Path.mk
                                                                false
                                                                [
                                                                  (PathSegment.mk
                                                                    "lock_id"
                                                                    PathArguments.none)]))]))
                                                      false)])))])))
                                    none),
                                  (Stmt.expr
                                    (Expr.methodCall
                                      (Expr.field
                                        (Expr.path
                                          none
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "self" PathArguments.none)]))
                                        (Member.named "threads"))
                                      "mutate_at"
                                      none
                                      [
                                        (Expr.path
                                          none
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "acquirer_id" PathArguments.none)])),
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
                                                          [
                                                            (PathSegment.mk
                                                              "thread"
                                                              PathArguments.none)]))
                                                      (Member.named "state"))
                                                    (Expr.path
                                                      none
                                                      (Path.mk
                                                        false
                                                        [
                                                          (PathSegment.mk
                                                            "ThreadState"
                                                            PathArguments.none),
                                                          (PathSegment.mk
                                                            "Enabled"
                                                            PathArguments.none)])))
                                                  true)])))])
                                    true),
                                  (Stmt.expr
                                    (Expr.methodCall
                                      (Expr.field
                                        (Expr.path
                                          none
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "self" PathArguments.none)]))
                                        (Member.named "synchronized_threads"))
                                      "insert"
                                      none
                                      [
                                        (Expr.path
                                          none
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "acquirer_id" PathArguments.none)]))])
                                    true),
                                  (Stmt.expr
                                    (Expr.methodCall
                                      (Expr.field
                                        (Expr.path
                                          none
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "self" PathArguments.none)]))
                                        (Member.named "locks"))
                                      "mutate_at"
                                      none
                                      [
                                        (Expr.path
                                          none
                                          (Path.mk
                                            false
                                            [(PathSegment.mk "lock_id" PathArguments.none)])),
                                        (Expr.closure
                                          false
                                          [(Pat.ident false false "lock" none)]
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
                                                        (Path.mk
                                                          false
                                                          [
                                                            (PathSegment.mk
                                                              "lock"
                                                              PathArguments.none)])))
                                                    (Expr.call
                                                      (Expr.path
                                                        none
                                                        (Path.mk
                                                          false
                                                          [
                                                            (PathSegment.mk
                                                              "LockState"
                                                              PathArguments.none),
                                                            (PathSegment.mk
                                                              "LockedBy"
                                                              PathArguments.none)]))
                                                      [
                                                        (Expr.path
                                                          none
                                                          (Path.mk
                                                            false
                                                            [
                                                              (PathSegment.mk
                                                                "acquirer_id"
                                                                PathArguments.none)]))]))
                                                  true)])))])
                                    true)])
                              (some
                                (Expr.block
                                  none
                                  (Block.mk
                                    [
                                      (Stmt.expr
                                        (Expr.methodCall
                                          (Expr.field
                                            (Expr.path
                                              none
                                              (Path.mk
                                                false
                                                [(PathSegment.mk "self" PathArguments.none)]))
                                            (Member.named "locks"))
                                          "mutate_at"
                                          none
                                          [
                                            (Expr.path
                                              none
                                              (Path.mk
                                                false
                                                [(PathSegment.mk "lock_id" PathArguments.none)])),
                                            (Expr.closure
                                              false
                                              [(Pat.ident false false "lock" none)]
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
                                                            (Path.mk
                                                              false
                                                              [
                                                                (PathSegment.mk
                                                                  "lock"
                                                                  PathArguments.none)])))
                                                        (Expr.path
                                                          none
                                                          (Path.mk
                                                            false
                                                            [
                                                              (PathSegment.mk
                                                                "LockState"
                                                                PathArguments.none),
                                                              (PathSegment.mk
                                                                "Unlocked"
                                                                PathArguments.none)])))
                                                      true)])))])
                                        true)]))))
                            false),
                          (Stmt.expr
                            (Expr.call
                              (Expr.path
                                none
                                (Path.mk false [(PathSegment.mk "ret" PathArguments.none)]))
                              [(Expr.tuple [])])
                            false)]))),
                  (Arm.mk
                    []
                    Pat.wild
                    none
                    (Expr.macro
                      (Macro.mk
                        (Path.mk false [(PathSegment.mk "throw_ub" PathArguments.none)])
                        MacroDelimiter.paren
                        (MacroBody.exprs [(Expr.lit (Lit.str "releasing non-acquired lock"))] false))))])
              false)]))])

/-- `spec/lang/step/locks.md:116` -/
def impl_Machine__eval_intrinsic : Item :=
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
              (Pat.tupleStruct
                none
                (Path.mk
                  false
                  [
                    (PathSegment.mk "IntrinsicOp" PathArguments.none),
                    (PathSegment.mk "Lock" PathArguments.none)])
                [
                  (Pat.path
                    none
                    (Path.mk
                      false
                      [
                        (PathSegment.mk "IntrinsicLockOp" PathArguments.none),
                        (PathSegment.mk "Create" PathArguments.none)]))])
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
                  BinOp.gt
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
                              (Lit.str "invalid number of arguments for `Create` lock intrinsic"))]
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
                            [(Expr.lit (Lit.str "invalid return type for `Create` lock intrinsic"))]
                            false)))
                      false)])
                none)
              false),
            (Stmt.letStmt
              []
              (Pat.ident false false "lock_id" none)
              (some
                (Expr.methodCall
                  (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                  "lock_create"
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
                          (PathSegment.mk "Int" PathArguments.none)]))
                    [
                      (Expr.path
                        none
                        (Path.mk false [(PathSegment.mk "lock_id" PathArguments.none)]))])])
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
                    (PathSegment.mk "Lock" PathArguments.none)])
                [
                  (Pat.path
                    none
                    (Path.mk
                      false
                      [
                        (PathSegment.mk "IntrinsicLockOp" PathArguments.none),
                        (PathSegment.mk "Acquire" PathArguments.none)]))])
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
                              (Lit.str "invalid number of arguments for `Acquire` lock intrinsic"))]
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
                [(Pat.ident false false "lock_id" none)])
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
                                (Lit.str "invalid first argument to `Acquire` lock intrinsic"))]
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
                            [
                              (Expr.lit
                                (Lit.str "invalid return type for `Acquire` lock intrinsic"))]
                            false)))
                      false)])
                none)
              false),
            (Stmt.expr
              (Expr.tryExpr
                (Expr.methodCall
                  (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                  "lock_acquire"
                  none
                  [(Expr.path none (Path.mk false [(PathSegment.mk "lock_id" PathArguments.none)]))]))
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
              (Pat.tupleStruct
                none
                (Path.mk
                  false
                  [
                    (PathSegment.mk "IntrinsicOp" PathArguments.none),
                    (PathSegment.mk "Lock" PathArguments.none)])
                [
                  (Pat.path
                    none
                    (Path.mk
                      false
                      [
                        (PathSegment.mk "IntrinsicLockOp" PathArguments.none),
                        (PathSegment.mk "Release" PathArguments.none)]))])
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
                              (Lit.str "invalid number of arguments for `Release` lock intrinsic"))]
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
                [(Pat.ident false false "lock_id" none)])
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
                                (Lit.str "invalid first argument to `Release` lock intrinsic"))]
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
                            [
                              (Expr.lit
                                (Lit.str "invalid return type for `Release` lock intrinsic"))]
                            false)))
                      false)])
                none)
              false),
            (Stmt.expr
              (Expr.tryExpr
                (Expr.methodCall
                  (Expr.path none (Path.mk false [(PathSegment.mk "self" PathArguments.none)]))
                  "lock_release"
                  none
                  [(Expr.path none (Path.mk false [(PathSegment.mk "lock_id" PathArguments.none)]))]))
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

/-- All items of `spec/lang/step/locks.md`, in source order, with provenance. -/
def items : List SourceItem :=
  [
    (SourceItem.mk
      "enum_LockState"
      9
      "57986baec2252ae5f6c55e9b787a6cd32f6a4d52db2feecf75c9fa136bdbdd35"
      enum_LockState),
    (SourceItem.mk
      "type_LockId"
      14
      "0aca9d2ef8ae12e8ca070ebfaa81fb6c9bd091551656e69240024bfff208d766"
      type_LockId),
    (SourceItem.mk
      "impl_Machine__lock_create"
      22
      "068de914231705e4c9485d60752eaace87db0923427da46e1b737a8b1807cd00"
      impl_Machine__lock_create),
    (SourceItem.mk
      "impl_Machine__eval_intrinsic"
      116
      "a93074bff0985ca49311e2ff338e294ab4e330e928870237eabe572dd9453e4e"
      impl_Machine__eval_intrinsic)]

end MiniRustSpec.Gen.Items.Lang.Step.Locks
