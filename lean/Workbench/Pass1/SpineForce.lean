-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.Core
import Init.Data.Nat.Basic
import Init.Data.List.Basic

/-!
# CPS Spine-Forcing and `@Nat.rec` Recursion Combinators (`Workbench.Pass1.SpineForce`)

Pass-1-portable (`prelude` + locked `Init.*` only, zero `._unsafe_rec`, allowed
theory tactics only) combinators solving three recurring Lean 4.34.1 kernel
scaling and TCB-admission bottlenecks:

1. **`withStrictNat` (`@Nat.casesOn` Numeral History Stripper):**
   Repeated `Nat.land` / `Nat.lor` / `Nat.shiftRight` inside recursive checkers
   can retain deep unreduced `Expr` history unless forced in `whnf`. Pattern
   matching via `@Nat.casesOn` forces `n` to a kernel numeral (`0` or
   `Nat.succ (Lit (n - 1))`) in $O(1)$, discarding the intermediate `Expr` tree.

2. **CPS Spine-Forcing (`forceNat`, `forceList`, `forceOption`):**
   When a symbolic MIR state contains free variables (`hasFVar == true`),
   `Lean.Meta.WHNF` disables its WHNF cache, turning chained `List.set` updates
   into $O(2^k)$ re-evaluations. Forcing the `List` cons-spine in CPS before
   passing it to the next continuation materializes concrete `a :: b :: ...`
   spines and eliminates exponential blowup.

3. **Zero-`._unsafe_rec` Bounded Iteration & Quantifiers (`natFold`,
   `runChunksPow2`, `checkRange`):**
   Equation-compiler recursion over fuel or indices can emit `._unsafe_rec`
   auxiliaries rejected by `TrustedBoundary`. Defining combinators directly via
   `@Nat.rec` guarantees `0` `._unsafe_rec` and `0` `noncomputable` markers,
   while `checkRange_sound` discharges bounded `∀ i < n, P i` goals by `rfl` or
   `decide`.
-/

namespace Workbench.Pass1.SpineForce

/-! ## 1. `O(1)` Kernel Numeral Forcing (`withStrictNat`) -/

def withStrictNat {α : Type u} (n : Nat) (k : Nat → α) : α :=
  @Nat.casesOn (fun _ => α) n (k 0) (fun p => k (Nat.succ p))

theorem withStrictNat_eq {α : Type u} (n : Nat) (k : Nat → α) :
    withStrictNat n k = k n := by
  cases n <;> rfl

/-! ## 2. CPS Spine-Forcing (`forceNat`, `forceOption`, `forceList`) -/

def forceNat {α : Type u} (n : Nat) (cont : Nat → α) : α :=
  @Nat.rec (fun _ => (Nat → α) → α)
    (fun k => k 0)
    (fun _ ih k => ih (fun m' => k (m' + 1)))
    n cont

theorem forceNat_eq {α : Type u} :
    ∀ (n : Nat) (cont : Nat → α), forceNat n cont = cont n
  | 0, _ => rfl
  | m + 1, cont => by
    dsimp only [forceNat]
    exact forceNat_eq m (fun m' => cont (m' + 1))

def forceOption {α : Type u} {β : Type v} (opt : Option α)
    (cont : Option α → β) : β :=
  match opt with
  | none => cont none
  | some x => cont (some x)

theorem forceOption_eq {α : Type u} {β : Type v} (opt : Option α)
    (cont : Option α → β) : forceOption opt cont = cont opt := by
  cases opt <;> rfl

def forceList {α : Type u} {β : Type v} (xs : List α)
    (cont : List α → β) : β :=
  List.foldr
    (fun (x : α) (ih : (List α → β) → β) (k : List α → β) =>
      ih (fun xs' => k (x :: xs')))
    (fun k => k [])
    xs cont

theorem forceList_eq {α : Type u} {β : Type v} :
    ∀ (xs : List α) (cont : List α → β), forceList xs cont = cont xs
  | [], _ => rfl
  | x :: xs, cont => by
    dsimp only [forceList, List.foldr]
    exact forceList_eq xs (fun xs' => cont (x :: xs'))

/-! ## 3. Zero-`._unsafe_rec` Iteration & Shallow `$2^d$` Stepper -/

def natFold {α : Type u} (steps : Nat) (stepFn : Nat → α → α) (init : α) : α :=
  @Nat.rec (fun _ => α → α)
    (fun acc => acc)
    (fun k ih acc => ih (stepFn k acc))
    steps init

theorem natFold_zero {α : Type u} (stepFn : Nat → α → α) (init : α) :
    natFold 0 stepFn init = init := rfl

theorem natFold_succ {α : Type u} (n : Nat) (stepFn : Nat → α → α) (init : α) :
    natFold (n + 1) stepFn init = natFold n stepFn (stepFn n init) := rfl

/-- Runs `stepChunk` `2 ^ pow2Depth` times with $O(\text{pow2Depth})$ kernel
call-stack depth so multi-thousand-step concrete executions never trip Lean's
`defaultMaxRecDepth = 512`. -/
def runPow2 {α : Type u} (pow2Depth : Nat) (stepChunk : α → α) (st : α) : α :=
  @Nat.rec (fun _ => α → α)
    stepChunk
    (fun _ ih cur => ih (ih cur))
    pow2Depth st

theorem runPow2_zero {α : Type u} (stepChunk : α → α) (st : α) :
    runPow2 0 stepChunk st = stepChunk st := rfl

theorem runPow2_succ {α : Type u} (d : Nat) (stepChunk : α → α) (st : α) :
    runPow2 (d + 1) stepChunk st =
      runPow2 d stepChunk (runPow2 d stepChunk st) := rfl

theorem runPow2_preserves {α : Type u} (inv : α → Prop) (stepChunk : α → α)
    (hStep : ∀ s : α, inv s → inv (stepChunk s)) :
    ∀ (d : Nat) (st : α), inv st → inv (runPow2 d stepChunk st)
  | 0, st, hInv => hStep st hInv
  | d + 1, st, hInv =>
    runPow2_preserves inv stepChunk hStep d (runPow2 d stepChunk st)
      (runPow2_preserves inv stepChunk hStep d st hInv)

/-! ## 4. Bounded Quantifier Reflection (`checkRange` / `checkRange_sound`) -/

def checkRange (predB : Nat → Bool) (bound : Nat) : Bool :=
  @Nat.rec (fun _ => Bool)
    true
    (fun k acc => predB k && acc)
    bound

theorem checkRange_zero (predB : Nat → Bool) :
    checkRange predB 0 = true := rfl

theorem checkRange_succ (predB : Nat → Bool) (n : Nat) :
    checkRange predB (n + 1) = (predB n && checkRange predB n) := rfl

theorem checkRange_true_imp (predB : Nat → Bool) :
    ∀ (bound i : Nat), checkRange predB bound = true → i < bound → predB i = true
  | 0, _, _, hLt => by nomatch hLt
  | n + 1, i, hChk, hLt => by
    rw [checkRange_succ] at hChk
    have hHead : predB n = true := by
      cases hb : predB n with
      | false => rw [hb] at hChk; nomatch hChk
      | true => rfl
    have hTail : checkRange predB n = true := by
      rw [hHead] at hChk
      exact hChk
    cases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hLt) with
    | inl hEq =>
      rw [hEq]
      exact hHead
    | inr hSubLt =>
      exact checkRange_true_imp predB n i hTail hSubLt

/-- Discharges `∀ i, i < bound → P i` via `rfl` or `decide` whenever `predB`
reflects `P`. -/
theorem checkRange_sound {P : Nat → Prop} (predB : Nat → Bool)
    (hReflect : ∀ i : Nat, predB i = true → P i)
    (bound : Nat) (hOk : checkRange predB bound = true) :
    ∀ i : Nat, i < bound → P i :=
  fun i hLt => hReflect i (checkRange_true_imp predB bound i hOk hLt)

end Workbench.Pass1.SpineForce
