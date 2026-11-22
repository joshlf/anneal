-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

/-!
# Rapid Counterexample Search & Spec-Vacuity Probes (`Workbench.Lab.Counterexample`)

Exploration-only (`lab_meta`) utilities for falsifying candidate lemmas and
auditing proposed specifications *before* investing proof effort:

1. **Deterministic SplitMix64 + Boundary Input Search (`findCounterexample*`):**
   Tests boundary values (`0, 1, 2, 3, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128,
   255, 256, 2^32 - 1, 2^64 - 1`) followed by SplitMix64 pseudo-random samples
   so off-by-one, shift-width, and wrap-around bugs surface in `<5ms` under
   `#eval`.
2. **3-Axis Specification Sanity Probe (`probeSpecHealth`):**
   Checks boolean-decidable approximations of `(requires, ensures)` for:
   - **Precondition vacuity:** zero sampled inputs satisfy `requires`.
   - **Postcondition tautology:** every `(input, output)` pair satisfies
     `ensures`.
   - **Output insensitivity:** mutating the return value never changes
     `ensures` on any valid input (catching specs that forgot to constrain
     `ret`).
-/

namespace Workbench.Lab.Counterexample

/-! ## 1. SplitMix64 Generator & Boundary Seeds -/

def mask64 : Nat := (1 <<< 64) - 1

def splitMix64Next (state : Nat) : Nat × Nat :=
  let s' := (state + 0x9e3779b97f4a7c15) &&& mask64
  let z1 := ((s' ^^^ (s' >>> 30)) * 0xbf58476d1ce4e5b9) &&& mask64
  let z2 := ((z1 ^^^ (z1 >>> 27)) * 0x94d049bb133111eb) &&& mask64
  let out := (z2 ^^^ (z2 >>> 31)) &&& mask64
  (out, s')

def boundaryNats : List Nat :=
  [ 0, 1, 2, 3, 4, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256
  , 65535, 65536, (1 <<< 31) - 1, 1 <<< 31, (1 <<< 32) - 1, 1 <<< 32
  , (1 <<< 63) - 1, 1 <<< 63, (1 <<< 64) - 1 ]

def sampleNats (count : Nat) (maxVal : Nat := 1024) (seed : Nat := 0x5eed1234) :
    List Nat :=
  let cap := if maxVal == 0 then 1 else maxVal + 1
  let rec go : Nat → Nat → List Nat → List Nat
    | 0, _, acc => acc.reverse
    | n + 1, st, acc =>
      let (r, st') := splitMix64Next st
      go n st' ((r % cap) :: acc)
  boundaryNats.filter (· ≤ maxVal) ++ go count seed []

/-! ## 2. 1-Arity, 2-Arity, and 3-Arity Counterexample Finders -/

def findCounterexample1 (pred : Nat → Bool) (trials : Nat := 256)
    (maxVal : Nat := 1024) : Option Nat :=
  (sampleNats trials maxVal).find? (fun x => !pred x)

def findCounterexample2 (pred : Nat → Nat → Bool) (trials : Nat := 64)
    (maxVal : Nat := 1024) : Option (Nat × Nat) :=
  let xs := sampleNats trials maxVal
  let ys := sampleNats trials maxVal 0x99887766
  let rec searchOuter : List Nat → Option (Nat × Nat)
    | [] => none
    | x :: rest =>
      match ys.find? (fun y => !pred x y) with
      | some y => some (x, y)
      | none => searchOuter rest
  searchOuter xs

def findCounterexample3 (pred : Nat → Nat → Nat → Bool) (trials : Nat := 24)
    (maxVal : Nat := 1024) : Option (Nat × Nat × Nat) :=
  let xs := sampleNats trials maxVal
  let ys := sampleNats trials maxVal 0x13579bdf
  let zs := sampleNats trials maxVal 0x2468ace0
  let rec searchX : List Nat → Option (Nat × Nat × Nat)
    | [] => none
    | x :: rx =>
      let rec searchY : List Nat → Option (Nat × Nat × Nat)
        | [] => searchX rx
        | y :: ry =>
          match zs.find? (fun z => !pred x y z) with
          | some z => some (x, y, z)
          | none => searchY ry
      searchY ys
  searchX xs

/-! ## 3. 3-Axis Specification Vacuity & Sensitivity Probe -/

structure SpecHealthReport where
  sampledInputs       : Nat
  validInputs         : Nat
  refutablePairs      : Nat
  outputSensitiveHits : Nat
  deriving Repr, DecidableEq

def SpecHealthReport.isHealthy (r : SpecHealthReport) : Bool :=
  decide (0 < r.validInputs) &&
  decide (0 < r.refutablePairs) &&
  decide (0 < r.outputSensitiveHits)

def SpecHealthReport.warnings (r : SpecHealthReport) : List String :=
  (if r.validInputs == 0 then
    ["VACUOUS_REQUIRES: 0 sampled inputs satisfied `requires`"]
   else []) ++
  (if r.validInputs > 0 && r.refutablePairs == 0 then
    ["TAUTOLOGICAL_ENSURES: `ensures` held for every tested output"]
   else []) ++
  (if r.validInputs > 0 && r.outputSensitiveHits == 0 then
    ["OUTPUT_INSENSITIVE: mutating return value never changed `ensures`"]
   else [])

/-- Evaluates `(reqB, ensB)` across `inputs × outputs` to catch vacuous
preconditions, tautological postconditions, and output-ignoring specs. -/
def probeSpecHealth {α β : Type} (reqB : α → Bool) (ensB : α → β → Bool)
    (inputs : List α) (candidateOutputs : List β) : SpecHealthReport :=
  let valid := inputs.filter reqB
  let refutable :=
    valid.foldl (fun acc x =>
      acc + (candidateOutputs.filter (fun y => !ensB x y)).length) 0
  let sensitive :=
    valid.filter (fun x =>
      let hasTrue := candidateOutputs.any (fun y => ensB x y)
      let hasFalse := candidateOutputs.any (fun y => !ensB x y)
      hasTrue && hasFalse)
  { sampledInputs := inputs.length
  , validInputs := valid.length
  , refutablePairs := refutable
  , outputSensitiveHits := sensitive.length
  }

end Workbench.Lab.Counterexample
