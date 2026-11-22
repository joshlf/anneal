-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import Lean

/-!
# `Lean.Expr` DAG Sharing & Marginal Kernel Replay Profiler (`Workbench.Lab.KernelBench`)

Exploration-only (`lab_meta`) profiling helpers for diagnosing `.olean` size
explosions, loss of `Expr` subterm sharing, and slow kernel typechecking:

1. **`measureExpr` (`ExprStats`):** Computes unique DAG nodes, unfolded tree
   nodes (capped to prevent overflow), and maximum AST depth of any `Lean.Expr`.
   When `treeNodes >> dagNodes`, tactics like `rw` or `simp` that traverse tree
   paths without DAG memoization will stall even when `.olean` size looks small;
   conversely, large `dagNodes` pinpoints `.olean` serialization bloat.
2. **`profileDecl` (`DeclProfile`):** Summarizes type + value `ExprStats` and
   direct constant references of any declaration in the current environment.
-/

namespace Workbench.Lab.KernelBench

open Lean

structure ExprStats where
  dagNodes  : Nat
  treeNodes : Nat
  maxDepth  : Nat
  deriving Repr, Inhabited

private def treeNodeCap : Nat := 10000000

/-- Computes DAG node count (by `Expr` hash/equality memoization), capped
unfolded tree node count, and AST depth. -/
partial def measureExpr (root : Expr) : ExprStats :=
  let rec go (e : Expr) : StateM (Std.HashMap Expr (Nat × Nat)) (Nat × Nat) := do
    if let some cached := (← get).get? e then
      return cached
    let res ← match e with
      | .bvar _ | .fvar _ | .mvar _ | .sort _ | .const _ _ | .lit _ =>
        pure (1, 1)
      | .mdata _ b | .proj _ _ b => do
        let (t, d) ← go b
        pure (Nat.min treeNodeCap (1 + t), 1 + d)
      | .app f a => do
        let (tf, df) ← go f
        let (ta, da) ← go a
        pure (Nat.min treeNodeCap (1 + tf + ta), 1 + Nat.max df da)
      | .lam _ ty body _ | .forallE _ ty body _ => do
        let (tt, dt) ← go ty
        let (tb, db) ← go body
        pure (Nat.min treeNodeCap (1 + tt + tb), 1 + Nat.max dt db)
      | .letE _ ty val body _ => do
        let (tt, dt) ← go ty
        let (tv, dv) ← go val
        let (tb, db) ← go body
        pure (Nat.min treeNodeCap (1 + tt + tv + tb),
              1 + Nat.max dt (Nat.max dv db))
    modify (·.insert e res)
    return res
  let ((treeN, depth), visited) := (go root).run {}
  { dagNodes := visited.size, treeNodes := treeN, maxDepth := depth }

structure DeclProfile where
  name          : Name
  kind          : String
  typeStats     : ExprStats
  valueStats    : Option ExprStats
  directConsts  : Nat
  isUnsafe      : Bool
  isPartial     : Bool
  deriving Repr

def classifyConstantKind : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _  => "def"
  | .thmInfo _   => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _  => "quot"
  | .inductInfo _ => "inductive"
  | .ctorInfo _  => "ctor"
  | .recInfo _   => "recursor"

def profileConstantInfo (ci : ConstantInfo) : DeclProfile :=
  let tyStats := measureExpr ci.type
  let valStats := ci.value?.map measureExpr
  let consts := ci.getUsedConstantsAsSet.size
  let isPartial := match ci with
    | .defnInfo v => v.safety == .partial
    | _ => false
  { name := ci.name
  , kind := classifyConstantKind ci
  , typeStats := tyStats
  , valueStats := valStats
  , directConsts := consts
  , isUnsafe := ci.isUnsafe
  , isPartial := isPartial
  }

def profileDecl (declName : Name) : CoreM DeclProfile := do
  let ci ← getConstInfo declName
  return profileConstantInfo ci

end Workbench.Lab.KernelBench
