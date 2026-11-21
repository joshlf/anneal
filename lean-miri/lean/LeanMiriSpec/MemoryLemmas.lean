/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import Lean
import Miri.Memory.InitMask
import Miri.Memory.ProvenanceMap
import Miri.Memory.Allocation

/-!
# Zero-patch memory specification lemmas (`LeanMiriSpec.MemoryLemmas`)

`google/zerocopy#4022` appended 50 public specification theorems about
`Miri.Memory.{InitMask, ProvenanceMap, Allocation}` directly to the vendored
`lean-miri/vendor/Miri/Memory/{InitMask,ProvenanceMap,Allocation}.lean`. This module proves the
same 50 theorems, with the same names, namespaces, hypotheses and conclusions, as a companion
module that leaves `lean-miri/vendor/**` and `lean-miri/UPSTREAM_PIN.json` byte-for-byte
unmodified.

## Working outside the vendored modules

The `#4022` proofs refer to declarations that `lean-miri` marks `private` (`checkedSlice`,
`setInitialization`, `overwriteRawBytes`, `prepareForOverwrite`, `setRangeInbounds`, `findBit`,
`materialize`, `targetUIntBytes`, `readTargetUInt`, the `Allocation.mk` constructor and its
`rawBytes`/`size`/`provenance`/`initMask` fields, ...), which an importing module cannot name.
This module never names them. Instead:

* every private helper the proofs need is mirrored verbatim by a `private` definition of the
  same name in this module (`Allocation.mk` by `mkAlloc`, built with the `constructor` tactic;
  the `rawBytes` field by `Allocation.raw`, read through the public `casesOn` eliminator);
* every public `lean-miri` operation whose body calls such a helper gets a mirror (`…R`) and a
  bridge `@op = @opR := rfl`, so the kernel itself checks that each mirror is definitionally
  the vendored code; proofs rewrite with the bridge and then unfold the mirror;
* `InitMask.collectChunks` (whose private worker is a well-founded recursion) is unfolded
  through the public `WellFounded.Nat.fix_eq`.

No `sorry`, `native_decide`, `unsafe`, `implemented_by`, custom axioms, or name-resolution
metaprogramming are used; Part 5 instantiates all 50 theorems in closed/existential `private`
non-vacuity witnesses on concrete states, and Part 6 checks with `#assert_standard_axioms` and
`#assert_module_standard_axioms` that the module exposes those exact 50 public theorems (zero
private-helper type leakage, matching `LeanMiriSpec.MemoryLemmas` re-exports, 50/50 non-vacuity
witness coverage) and that every declaration in this module depends only on `propext`,
`Classical.choice`, and `Quot.sound`.

## The 50 theorems

* `Miri.Memory.InitMask.WriteProof` (7): `get_ok_of_wellFormed`, `set_range_get`,
  `isRangeInitialized_nonempty_iff`, `isRangeInitialized_after_setRange_true`,
  `isRangeInitialized_frame`, `prepareCopy_of_uniform`, `applyCopy_singleton`.
* `Miri.Memory.ProvenanceMap` (4): `rangeEmpty_new`, `readPtr_new`, `prepareCopy_new`,
  `applyCopy_empty`.
* `Miri.Memory.Allocation` (39): the `withExtra`/`mapExtra` projections and commutations
  (`byteSize_withExtra` … `clearProvenance_mapExtra`), constructors and slices (`fromBytes_spec`,
  `fromBytes_exists`, `tryNew_spec`, `tryNew_exists`, `getBytesUnchecked_size`,
  `getBytesUnchecked_subrange`, `getBytesUnchecked_split`, `getBytesStripProvenance_uninit_err`,
  `getBytesStripProvenance_ok`), endian-aware scalar reads (`readScalar_uninit_err`,
  `readScalar_int_of_bytes`, `readScalar_int_roundtrip`, `readScalar_ptr_roundtrip`,
  `readScalar_ptr_none_roundtrip`), and framed writes and copies (`writeScalar_spec`,
  `writeBytes_zero_spec`, `writeBytes_spec`, `writeUninit_zero_spec`, `writeUninit_spec`,
  `copyRepeatedly_initialized_spec`, `copy_initialized_spec`).
-/

set_option autoImplicit false

/-- Fail unless:
1. every listed declaration depends only on Lean's standard axioms (`propext`, `Quot.sound`,
   `Classical.choice`) — in particular zero `sorryAx` and zero `Lean.ofReduceBool`;
2. every listed declaration's kernel type references zero `private` helper declarations;
3. every listed declaration is re-exported under `LeanMiriSpec.MemoryLemmas.<shortName>` pointing
   to the exact same declaration;
4. every listed declaration appears in the kernel proof/type terms of the `private theorem`
   non-vacuity witnesses in `LeanMiriSpec.MemoryLemmas.NonVacuity`; and
5. no extra user-authored public declaration exists in `env.constants.map₂` outside the listed 50.
File-local analogue of `LeanMiriSpec.Audit`'s command (that module imports all of `LeanMiriSpec`). -/
local elab "#assert_standard_axioms " ids:ident* : command => do
  let env ← Lean.getEnv
  let mut witnessUsed : Lean.NameSet := {}
  for (c, ci) in env.constants.map₂.toList do
    if (c.toString.splitOn "LeanMiriSpec.MemoryLemmas.NonVacuity.").length > 1 then
      if let some v := ci.value? (allowOpaque := true) then
        for u in v.getUsedConstants do
          witnessUsed := witnessUsed.insert u
      for u in ci.type.getUsedConstants do
        witnessUsed := witnessUsed.insert u
  let mut listed : Lean.NameSet := {}
  for id in ids do
    let n ← Lean.Elab.Command.liftCoreM <| Lean.Elab.realizeGlobalConstNoOverloadWithInfo id
    if listed.contains n then
      throwError "duplicate entry {n} in #assert_standard_axioms"
    listed := listed.insert n
    let axs ← Lean.Elab.Command.liftCoreM <| Lean.collectAxioms n
    for a in axs do
      unless a == ``propext || a == ``Quot.sound || a == ``Classical.choice do
        throwError "{n} depends on the non-standard axiom {a}"
    if let some ci := env.find? n then
      for u in ci.type.getUsedConstants do
        if Lean.isPrivateName u then
          throwError "{n}'s public type leaks private constant {u}"
    if let .str _ shortName := n then
      let aliasId := Lean.mkIdent (`LeanMiriSpec.MemoryLemmas ++ Lean.Name.mkSimple shortName)
      let aliasTarget ← Lean.Elab.Command.liftCoreM <| Lean.realizeGlobalConstNoOverload aliasId
      unless aliasTarget == n do
        throwError "re-export LeanMiriSpec.MemoryLemmas.{shortName} resolves to {aliasTarget}, expected {n}"
    unless witnessUsed.contains n do
      throwError "{n} is not exercised by any Part 5 NonVacuity witness"
    Lean.logInfo m!"{n} depends on axioms: {axs.toList}"
  unless listed.size == 50 do
    throwError "expected exactly 50 audited public theorems, got {listed.size}"
  for (c, _) in env.constants.map₂.toList do
    if !Lean.isPrivateName c then
      let s := c.toString
      let isAux :=
        (s.splitOn "._proof_").length > 1 ||
        (s.splitOn "._simp_").length > 1 ||
        (s.splitOn ".match_").length > 1 ||
        (s.splitOn "_aux_").length > 1 ||
        s.endsWith ".eq_1"
      if !isAux && !listed.contains c then
        throwError "unexpected extra public declaration {c} in LeanMiriSpec.MemoryLemmas"

/-- Sweep every declaration elaborated in this module (`env.constants.map₂`, both public and
private) and fail if any depends on a non-standard axiom. -/
local elab "#assert_module_standard_axioms" : command => do
  let env ← Lean.getEnv
  let mut checked : Nat := 0
  let mut seen : Array Lean.Name := #[]
  for (c, _) in env.constants.map₂.toList do
    let axs ← Lean.Elab.Command.liftCoreM <| Lean.collectAxioms c
    for a in axs do
      unless a == ``propext || a == ``Quot.sound || a == ``Classical.choice do
        throwError "{c} (in LeanMiriSpec.MemoryLemmas) depends on the non-standard axiom {a}"
      unless seen.contains a do
        seen := seen.push a
    checked := checked + 1
  if checked == 0 then
    throwError "module-wide axiom audit checked 0 declarations"
  Lean.logInfo m!"LeanMiriSpec.MemoryLemmas module-wide audit: {checked} declarations depend only on {seen.toList}"

/-! ## Part 1. `InitMask` -/

/-! ### 1a. Private mirrors of private `Miri.Memory` `InitMask` helpers -/

namespace Miri.Memory
open Miri.ABI

private def maxSizeBytes : Nat := 18446744073709551615
private def wordMask : Nat := 18446744073709551615
private def blockSize : Nat := 64
private def sizeBytes (size : Size) : Nat := size.bytes.toNat

private def sizeFromNat (n : Nat) : Except InitMaskError Size :=
  if n ≤ maxSizeBytes then .ok (Size.ofBytes (UInt64.ofNat n))
  else .error (.sizeFromNatOverflow n)

private def bitAt (word bit : Nat) : Bool := Nat.testBit word bit

private def setWordRange (word lo hi : Nat) (state : Bool) : UInt64 :=
  let mask := (2 ^ hi - 1) - (2 ^ lo - 1)
  UInt64.ofNat (if state then Nat.lor word mask else Nat.land word (wordMask - mask))

namespace InitMaskMaterialized

private def bitIndexR (offset : Size) : Nat × Nat :=
  let bytes := sizeBytes offset
  (bytes / blockSize, bytes % blockSize)

private def sizeFromBitIndex (block bit : Nat) : Except InitMaskError Size :=
  sizeFromNat (block * blockSize + bit)

private def getBlock (self : InitMaskMaterialized) (block : Nat) :
    Except InitMaskError UInt64 :=
  match self.blocks[block]? with
  | some word => .ok word
  | none => .error (.blockIndexOutOfBounds block self.blocks.size)

private def setBlock (blocks : Array UInt64) (index : Nat) (word : UInt64) :
    Except InitMaskError (Array UInt64) :=
  if h : index < blocks.size then
    .ok (blocks.set index word h)
  else
    .error (.blockIndexOutOfBounds index blocks.size)

private def get (self : InitMaskMaterialized) (offset : Size) :
    Except InitMaskError Bool := do
  let (block, bit) := bitIndexR offset
  let word ← getBlock self block
  return bitAt word.toNat bit

private def setRangeInbounds (self : InitMaskMaterialized) (start finish : Size)
    (newState : Bool) : Except InitMaskError InitMaskMaterialized := do
  let (blockA, bitA) := bitIndexR start
  let (blockB, bitB) := bitIndexR finish
  let mut words := self.blocks
  if blockA == blockB then
    let endBit := if bitB == 0 then 64 else bitB
    let word ← getBlock ⟨words⟩ blockA
    words ← setBlock words blockA (setWordRange word.toNat bitA endBit newState)
  else if newState then
    let wordA ← getBlock ⟨words⟩ blockA
    words ← setBlock words blockA (setWordRange wordA.toNat bitA 64 true)
    if bitB != 0 then
      let wordB ← getBlock ⟨words⟩ blockB
      words ← setBlock words blockB (setWordRange wordB.toNat 0 bitB true)
    for block in [blockA + 1:blockB] do
      words ← setBlock words block (UInt64.ofNat wordMask)
  else
    let wordA ← getBlock ⟨words⟩ blockA
    words ← setBlock words blockA (setWordRange wordA.toNat bitA 64 false)
    if bitB != 0 then
      let wordB ← getBlock ⟨words⟩ blockB
      words ← setBlock words blockB (setWordRange wordB.toNat 0 bitB false)
    for block in [blockA + 1:blockB] do
      words ← setBlock words block 0
  return ⟨words⟩

private def grow (self : InitMaskMaterialized) (len amount : Size)
    (newState : Bool) : Except InitMaskError InitMaskMaterialized := do
  let amountBytes := sizeBytes amount
  if amountBytes == 0 then return self
  let lenBytes := sizeBytes len
  let capacity := self.blocks.size * blockSize
  if capacity < lenBytes then
    throw (.blockCapacityTooSmall lenBytes capacity)
  let unusedTrailingBits := capacity - lenBytes
  let mut words := self.blocks
  if amountBytes > unusedTrailingBits then
    let additionalBlocks := amountBytes / blockSize + 1
    let word := if newState then UInt64.ofNat wordMask else 0
    words := words ++ Array.replicate additionalBlocks word
  if unusedTrailingBits > 0 then
    let tailEnd ← sizeFromNat (lenBytes + unusedTrailingBits)
    let grown ← setRangeInbounds ⟨words⟩ len tailEnd newState
    words := grown.blocks
  return ⟨words⟩

private def firstSetBit (word startBit : Nat) : Option Nat :=
  ((List.range (64 - startBit)).find? fun offset =>
    bitAt word (startBit + offset)).map (· + startBit)

private def searchBlock (word : UInt64) (block startBit : Nat)
    (isInit : Bool) : Except InitMaskError (Option Size) := do
  let bits := if isInit then word.toNat else wordMask - word.toNat
  match firstSetBit bits startBit with
  | none => return none
  | some bit => return some (← sizeFromBitIndex block bit)

private def findBitFast (self : InitMaskMaterialized) (start finish : Size)
    (isInit : Bool) : Except InitMaskError (Option Size) := do
  let startBytes := sizeBytes start
  let finishBytes := sizeBytes finish
  if startBytes >= finishBytes then return none
  let (startBlock, startBit) := bitIndexR start
  let endInclusive ← sizeFromNat (finishBytes - 1)
  let (endBlockInclusive, _) := bitIndexR endInclusive
  let first ← searchBlock (← getBlock self startBlock) startBlock startBit isInit
  match first with
  | some index =>
    if sizeBytes index < finishBytes then return some index else return none
  | none =>
    if startBlock < endBlockInclusive then
      for block in [startBlock + 1:endBlockInclusive + 1] do
        match ← searchBlock (← getBlock self block) block 0 isInit with
        | some index =>
          if sizeBytes index < finishBytes then return some index else return none
        | none => pure ()
    return none

private def findBit (self : InitMaskMaterialized) (start finish : Size)
    (isInit : Bool) : Except InitMaskError (Option Size) :=
  findBitFast self start finish isInit

end InitMaskMaterialized

namespace InitMask

private def materialize (self : InitMask) :
    Except InitMaskError InitMaskMaterialized := do
  match self.blocks with
  | .Lazy state => InitMaskMaterialized.grow ⟨#[]⟩ (Size.ofBytes 0) self.len state
  | .Materialized blocks => return blocks

/-! ### 1b. Mirrors of public `InitMask` operations and `rfl` bridges -/

private def getR (self : InitMask) (index : Size) : Except InitMaskError Bool := do
  match self.blocks with
  | .Lazy state => return state
  | .Materialized blocks => blocks.get index

private def isRangeInitializedR (self : InitMask) (range : AllocRange) :
    Except InitMaskError (Except AllocRange Unit) := do
  let finish ← range.endExclusive
  if finish.bytes > self.len.bytes then
    return .error (← AllocRange.fromEndpoints self.len finish)
  match self.blocks with
  | .Lazy state =>
    if state then return .ok () else return .error range
  | .Materialized blocks =>
    match ← blocks.findBit range.start finish false with
    | none => return .ok ()
    | some uninitStart =>
      let uninitEnd := (← blocks.findBit uninitStart finish true).getD finish
      return .error (← AllocRange.fromEndpoints uninitStart uninitEnd)

private def setRangeR (self : InitMask) (range : AllocRange)
    (newState : Bool) : Except InitMaskError InitMask := do
  let start := range.start
  let finish ← range.endExclusive
  let fullOverwrite := start.bytes = 0 ∧ self.len.bytes ≤ finish.bytes
  match self.blocks with
  | .Lazy state =>
    if fullOverwrite then return ⟨.Lazy newState, finish⟩
    else if state == newState then
      if finish.bytes > self.len.bytes then return ⟨.Lazy state, finish⟩
      else return self
    else
      let blocks ← materialize self
      if finish.bytes ≤ self.len.bytes then
        return ⟨.Materialized (← blocks.setRangeInbounds start finish newState), self.len⟩
      else
        let firstPart ← if start.bytes < self.len.bytes then
          blocks.setRangeInbounds start self.len newState else pure blocks
        let amount ← (Size.sub finish self.len).mapError MemoryError.sizeError
        return ⟨.Materialized (← firstPart.grow self.len amount newState), finish⟩
  | .Materialized oldBlocks =>
    if fullOverwrite then return ⟨.Lazy newState, finish⟩
    else if finish.bytes ≤ self.len.bytes then
      return ⟨.Materialized (← oldBlocks.setRangeInbounds start finish newState), self.len⟩
    else
      let firstPart ← if start.bytes < self.len.bytes then
        oldBlocks.setRangeInbounds start self.len newState else pure oldBlocks
      let amount ← (Size.sub finish self.len).mapError MemoryError.sizeError
      return ⟨.Materialized (← firstPart.grow self.len amount newState), finish⟩

private theorem get_eq_getR : @InitMask.get = @getR := rfl
private theorem isRangeInitialized_eq_R : @InitMask.isRangeInitialized = @isRangeInitializedR := rfl
private theorem setRange_eq_R : @InitMask.setRange = @setRangeR := rfl

end InitMask

namespace InitChunkIter

private def nextR (iter : InitChunkIter) :
    Except InitMaskError (Option (InitChunk × InitChunkIter)) := do
  if iter.start.bytes > iter.finish.bytes ||
      iter.finish.bytes > iter.initMask.len.bytes then
    throw (.invalidChunkIterator iter.start iter.finish)
  if sizeBytes iter.start >= sizeBytes iter.finish then return none
  match iter.initMask.blocks with
  | .Lazy state =>
    if state != iter.isInit then
      throw (.invalidChunkIterator iter.start iter.finish)
  | .Materialized _ => pure ()
  let chunkEnd ← do
    match iter.initMask.blocks with
    | .Lazy _ => pure iter.finish
    | .Materialized blocks => do
      let found ← blocks.findBit iter.start iter.finish (!iter.isInit)
      pure (found.getD iter.finish)
  if chunkEnd.bytes ≤ iter.start.bytes then
    throw (.invalidChunkIterator iter.start iter.finish)
  let chunk := if iter.isInit then InitChunk.Init iter.start chunkEnd
    else InitChunk.Uninit iter.start chunkEnd
  return some (chunk, { iter with isInit := !iter.isInit, start := chunkEnd })

private theorem next?_eq_R : @InitChunkIter.next? = @nextR := rfl

end InitChunkIter

end Miri.Memory

/-! ### 1c. `WriteProof` helpers over the mirrors -/

namespace Miri.Memory.InitMask.WriteProof
open Miri.ABI Miri.Memory
variable {ε α β : Type}

private abbrev getBlock := @Miri.Memory.InitMaskMaterialized.getBlock
private abbrev setBlock := @Miri.Memory.InitMaskMaterialized.setBlock
private abbrev setRangeInbounds := @Miri.Memory.InitMaskMaterialized.setRangeInbounds
private abbrev materialize := @Miri.Memory.InitMask.materialize
private abbrev setWordRange := @Miri.Memory.setWordRange
private abbrev wordMask := @Miri.Memory.wordMask

private theorem get_block_ok (words : Array UInt64) (index : Nat) (inBounds : index < words.size) :
    getBlock ⟨words⟩ index = .ok words[index] := by
  unfold getBlock
  unfold Miri.Memory.InitMaskMaterialized.getBlock
  simp [Array.getElem?_eq_getElem inBounds]

private def write_step (word : UInt64) (index : Nat) (words : Array UInt64) :
    Except InitMaskError (ForInStep (Array UInt64)) := do
  let updated ← setBlock words index word
  pure (.yield updated)

private def update_word (words : Array UInt64) (index : Nat) (transform : UInt64 → UInt64) :
    Except InitMaskError (Array UInt64) := do
  let word ← getBlock ⟨words⟩ index
  setBlock words index (transform word)

private def set_range_words (words : Array UInt64) (blockA bitA blockB bitB : Nat) (state : Bool) :
    Except InitMaskError (Array UInt64) := do
  if blockA == blockB then
    update_word words blockA (fun word => setWordRange word.toNat bitA (if bitB == 0 then 64 else bitB) state)
  else
    let initial ← update_word words blockA (fun word => setWordRange word.toNat bitA 64 state)
    let middle ← if bitB != 0 then update_word initial blockB (fun word => setWordRange word.toNat 0 bitB state) else pure initial
    forIn (Std.Legacy.Range.mk (blockA + 1) blockB 1 (by decide)) middle
      (write_step (if state then UInt64.ofNat wordMask else 0))

private theorem bind_if (p : Prop) [Decidable p] (yes no : Except ε α) (next : α → Except ε β) :
    ((if p then yes else no) >>= next) = (if p then yes >>= next else no >>= next) := by
  split <;> rfl

private theorem set_range_inbounds_reduces (self : InitMaskMaterialized) (start finish : Size) (state : Bool) :
    setRangeInbounds self start finish state = do
      let words ← set_range_words self.blocks (start.bytes.toNat / 64) (start.bytes.toNat % 64)
        (finish.bytes.toNat / 64) (finish.bytes.toNat % 64) state
      return ⟨words⟩ := by
  unfold setRangeInbounds
  unfold Miri.Memory.InitMaskMaterialized.setRangeInbounds
  unfold set_range_words update_word write_step getBlock setBlock setWordRange wordMask
  unfold InitMaskMaterialized.bitIndexR
  unfold Miri.Memory.sizeBytes
  unfold Miri.Memory.blockSize
  cases state <;> simp only [Bool.false_eq_true, ↓reduceIte, bind_if, bind_assoc, pure_bind]

private theorem materialize_lazy_nonzero (len : Size) (state : Bool) (nonzero : len.bytes.toNat ≠ 0) :
    materialize (InitMask.new len state) = .ok ⟨Array.replicate (len.bytes.toNat / 64 + 1) (if state then UInt64.ofNat 18446744073709551615 else 0)⟩ := by
  unfold materialize
  unfold Miri.Memory.InitMask.materialize
  unfold InitMask.new
  dsimp only
  unfold Miri.Memory.InitMaskMaterialized.grow
  unfold Miri.Memory.sizeBytes
  unfold Miri.Memory.blockSize
  unfold Miri.Memory.wordMask
  simp [nonzero, Size.ofBytes, Array.empty_append, Pure.pure, Except.pure]

/-- `collectChunks` (a well-founded private recursion in `lean-miri`) on an iterator that
yields exactly one chunk. Unfolded through the public `WellFounded.Nat.fix_eq`. -/
private theorem collectChunks_single (iter next : InitChunkIter) (chunk : InitChunk)
    (nonempty : iter.start.bytes.toNat < iter.finish.bytes.toNat)
    (h0 : iter.next? = .ok (some (chunk, next))) (h1 : next.next? = .ok none) :
    InitMask.collectChunks iter = .ok #[chunk] := by
  unfold InitMask.collectChunks
  have hfuel : iter.finish.bytes.toNat - iter.start.bytes.toNat + 1 =
      (iter.finish.bytes.toNat - iter.start.bytes.toNat - 1) + 1 + 1 := by omega
  with_unfolding_all erw [hfuel]
  with_unfolding_all refine (WellFounded.Nat.fix_eq (α := (_ : InitChunkIter) ×' Nat)
    (motive := fun _ => Except InitMaskError (Array InitChunk)) _ _ ⟨iter, _⟩).trans ?_
  dsimp only
  rw [h0]
  dsimp only [bind, Except.bind]
  rw [WellFounded.Nat.fix_eq]
  dsimp only
  rw [h1]
  rfl

/-! ### 1d. The seven `InitMask.WriteProof` specification theorems -/

private theorem if_pos_eq {α : Type} {c : Prop} [Decidable c] {t e : α} (h : c) :
    (if c then t else e) = t := by
  split
  · rfl
  · next hn => exact absurd h hn

private theorem if_neg_eq {α : Type} {c : Prop} [Decidable c] {t e : α} (h : ¬c) :
    (if c then t else e) = e := by
  split
  · next hp => exact absurd hp h
  · rfl

private theorem testBit_wordMask (bit : Nat) (h : bit < 64) :
    Nat.testBit wordMask bit = true := by
  have hm : wordMask = 2 ^ 64 - 1 := by decide
  rw [hm, Nat.testBit_two_pow_sub_one]
  exact decide_eq_true h

private theorem setWordRange_testBit (word lo hi bit : Nat) (state : Bool)
    (h_lo_hi : lo ≤ hi) (h_hi : hi ≤ 64) (h_bit : bit < 64) :
    Nat.testBit (setWordRange word lo hi state).toNat bit =
      if lo ≤ bit ∧ bit < hi then state else Nat.testBit word bit := by
  let mask := (2 ^ hi - 1) - (2 ^ lo - 1)
  have h_pow_lo : 1 ≤ 2 ^ lo := Nat.one_le_two_pow
  have h_pow_diff : 1 ≤ 2 ^ (hi - lo) := Nat.one_le_two_pow
  have h_sum : mask = (2 ^ (hi - lo) - 1) <<< lo := by
    have h_eq : hi = lo + (hi - lo) := by omega
    have h_pow : 2 ^ hi = 2 ^ lo * 2 ^ (hi - lo) := by
      conv => lhs; rw [h_eq]
      exact Nat.pow_add 2 lo (hi - lo)
    have h_mul : 2 ^ lo * (2 ^ (hi - lo) - 1) = 2 ^ lo * 2 ^ (hi - lo) - 2 ^ lo := by
      rw [Nat.mul_sub_left_distrib, Nat.mul_one]
    rw [Nat.shiftLeft_eq, Nat.mul_comm]
    dsimp only [mask]
    omega
  have h_mask_lt : mask < 2 ^ 64 := by
    have : 2 ^ hi ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) h_hi
    dsimp only [mask]
    omega
  have h_mask_bit : Nat.testBit mask bit = decide (lo ≤ bit ∧ bit < hi) := by
    rw [h_sum, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one]
    by_cases h_ge : lo ≤ bit
    · by_cases h_lt : bit < hi
      · have : bit - lo < hi - lo := by omega
        simp [h_ge, h_lt, this]
      · have : ¬(bit - lo < hi - lo) := by omega
        simp [h_ge, h_lt, this]
    · simp [h_ge]
  have h_inv : Nat.testBit (Miri.Memory.wordMask - mask) bit = !Nat.testBit mask bit := by
    have h_wm : Miri.Memory.wordMask = 2 ^ 64 - 1 := rfl
    rw [h_wm]
    have h_bv : BitVec.ofNat 64 (2 ^ 64 - 1 - mask) = ~~~(BitVec.ofNat 64 mask) := by
      apply BitVec.eq_of_toNat_eq
      simp [BitVec.toNat_not]
      omega
    have h1 := congrArg (fun b : BitVec 64 => b.getLsbD bit) h_bv
    simp only [BitVec.getLsbD_ofNat, BitVec.getLsbD_not, h_bit, decide_true, Bool.true_and] at h1
    exact h1
  unfold setWordRange Miri.Memory.setWordRange
  dsimp only
  cases state
  · simp only [Bool.false_eq_true, ↓reduceIte, UInt64.toNat_ofNat', Nat.testBit_mod_two_pow,
      h_bit, decide_true, Bool.true_and]
    change (word &&& (Miri.Memory.wordMask - mask)).testBit bit = _
    rw [Nat.testBit_and, h_inv, h_mask_bit]
    by_cases h_in : lo ≤ bit ∧ bit < hi <;> simp [h_in]
  · simp only [↓reduceIte, UInt64.toNat_ofNat', Nat.testBit_mod_two_pow,
      h_bit, decide_true, Bool.true_and]
    change (word ||| mask).testBit bit = _
    rw [Nat.testBit_or, h_mask_bit]
    by_cases h_in : lo ≤ bit ∧ bit < hi <;> simp [h_in]

private theorem write_list_getElem? (indices : List Nat) (words : Array UInt64) (word : UInt64)
    (updated : Array UInt64)
    (h_ok : forIn indices words (write_step word) = .ok updated) :
    updated.size = words.size ∧
      ∀ k, updated[k]? = if k ∈ indices then some word else words[k]? := by
  induction indices generalizing words with
  | nil =>
    simp only [List.forIn_nil, Pure.pure, Except.pure, Except.ok.injEq] at h_ok
    subst h_ok
    exact ⟨rfl, fun _ => by simp⟩
  | cons first rest ih =>
    simp only [List.forIn_cons, write_step, Miri.Memory.InitMaskMaterialized.setBlock,
      setBlock, Bind.bind, Except.bind, Pure.pure, Except.pure] at h_ok
    by_cases h_first : first < words.size
    · simp only [h_first, ↓reduceDIte] at h_ok
      obtain ⟨h_sz, h_elem⟩ := ih (words.set first word h_first) h_ok
      have h_wsz : (words.set first word h_first).size = words.size := Array.size_set ..
      refine ⟨h_sz.trans h_wsz, fun k => ?_⟩
      rw [h_elem k]
      by_cases h_rest : k ∈ rest
      · simp [h_rest]
      · simp only [h_rest, ↓reduceIte, List.mem_cons, or_false]
        by_cases h_eq : k = first
        · subst h_eq; simp [h_first]
        · simp [Ne.symm h_eq, h_eq]
    · simp [h_first] at h_ok

private theorem write_range_getElem? (lower upper : Nat) (words : Array UInt64) (word : UInt64)
    (updated : Array UInt64)
    (h_ok : forIn (Std.Legacy.Range.mk lower upper 1 (by decide)) words (write_step word) = .ok updated) :
    updated.size = words.size ∧
      ∀ k, updated[k]? = if lower ≤ k ∧ k < upper then some word else words[k]? := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range'] at h_ok
  obtain ⟨h_sz, h_elem⟩ := write_list_getElem? _ words word updated h_ok
  refine ⟨h_sz, fun k => ?_⟩
  rw [h_elem k]
  have h_mem : (k ∈ List.range' [lower:upper].start [lower:upper].size [lower:upper].step) ↔
      (lower ≤ k ∧ k < upper) := by
    simp only [List.mem_range', Std.Legacy.Range.size, Nat.div_one, Nat.one_mul]
    constructor
    · rintro ⟨i, hi, rfl⟩; omega
    · intro ⟨h1, h2⟩; exact ⟨k - lower, by omega, by omega⟩
  by_cases h_in : lower ≤ k ∧ k < upper
  · have hm : k ∈ List.range' [lower:upper].start [lower:upper].size [lower:upper].step := h_mem.mpr h_in
    rw [if_pos_eq (hm), if_pos_eq (h_in)]
  · have hm : k ∉ List.range' [lower:upper].start [lower:upper].size [lower:upper].step := fun h => h_in (h_mem.mp h)
    rw [if_neg_eq (hm), if_neg_eq (h_in)]

private theorem update_word_getElem? (words : Array UInt64) (index : Nat)
    (transform : UInt64 → UInt64) (updated : Array UInt64)
    (h_ok : update_word words index transform = .ok updated) :
    index < words.size ∧ updated.size = words.size ∧
      ∀ k, updated[k]? = if k = index then words[index]?.map transform else words[k]? := by
  unfold update_word getBlock Miri.Memory.InitMaskMaterialized.getBlock
    setBlock Miri.Memory.InitMaskMaterialized.setBlock at h_ok
  dsimp only at h_ok
  by_cases h_idx : index < words.size
  · have h_get : words[index]? = some words[index] := Array.getElem?_eq_getElem h_idx
    simp only [h_get, Bind.bind, Except.bind, h_idx, ↓reduceDIte, Except.ok.injEq] at h_ok
    subst h_ok
    refine ⟨h_idx, Array.size_set .., fun k => ?_⟩
    by_cases h_eq : k = index
    · subst h_eq; simp [h_idx]
    · simp [Ne.symm h_eq, h_eq]
  · have h_get : words[index]? = none := Array.getElem?_eq_none (Nat.le_of_not_lt h_idx)
    simp [h_get, Bind.bind, Except.bind] at h_ok

private theorem set_range_words_bit_gen (words : Array UInt64) (bA rA bB rB : Nat) (state : Bool)
    (updated : Array UInt64)
    (h_rA : rA < 64) (h_rB : rB < 64)
    (h_nonempty : bA * 64 + rA < bB * 64 + rB)
    (h_ok : set_range_words words bA rA bB rB state = .ok updated) :
    updated.size = words.size ∧
      ∀ (k bit : Nat), k < words.size → bit < 64 →
        ∃ w oldW,
          updated[k]? = some w ∧
          words[k]? = some oldW ∧
          Nat.testBit w.toNat bit =
            if bA * 64 + rA ≤ k * 64 + bit ∧ k * 64 + bit < bB * 64 + rB then
              state
            else
              Nat.testBit oldW.toNat bit := by
  unfold set_range_words at h_ok
  by_cases h_same : bA == bB
  · simp only [h_same, ↓reduceIte] at h_ok
    have h_bA_eq : bA = bB := eq_of_beq h_same
    have h_rB_nz : rB ≠ 0 := by omega
    obtain ⟨_, h_sz, h_elem⟩ := update_word_getElem? words bA _ updated h_ok
    refine ⟨h_sz, fun k bit h_ib h_bit => ?_⟩
    have h_old : words[k]? = some (words[k]'h_ib) := Array.getElem?_eq_getElem h_ib
    by_cases h_k : k = bA
    · subst h_k
      refine ⟨setWordRange (words[k]'h_ib).toNat rA (if rB == 0 then 64 else rB) state,
        words[k]'h_ib, ?_, h_old, ?_⟩
      · have he := h_elem k
        rw [if_pos_eq rfl, h_old] at he
        exact he
      · have h_rB_beq : (rB == 0) = false := beq_false_of_ne h_rB_nz
        simp only [h_rB_beq, Bool.false_eq_true, ↓reduceIte]
        have h_lo_hi : rA ≤ rB := by omega
        have h_hi : rB ≤ 64 := by omega
        rw [setWordRange_testBit _ rA rB bit state h_lo_hi h_hi h_bit]
        have h_iff : (rA ≤ bit ∧ bit < rB) ↔ (k * 64 + rA ≤ k * 64 + bit ∧ k * 64 + bit < bB * 64 + rB) := by omega
        by_cases h1 : rA ≤ bit ∧ bit < rB
        · rw [if_pos_eq h1, if_pos_eq (h_iff.mp h1)]
        · rw [if_neg_eq h1, if_neg_eq (fun h2 => h1 (h_iff.mpr h2))]
    · refine ⟨words[k]'h_ib, words[k]'h_ib, ?_, h_old, ?_⟩
      · have he := h_elem k
        rw [if_neg_eq h_k] at he
        exact he.trans h_old
      · have h_out : ¬(bA * 64 + rA ≤ k * 64 + bit ∧ k * 64 + bit < bB * 64 + rB) := by omega
        rw [if_neg_eq h_out]
  · simp only [h_same, Bool.false_eq_true, ↓reduceIte] at h_ok
    have h_lt_div : bA < bB := by
      have h_ne : bA ≠ bB := fun h => h_same (beq_iff_eq.mpr h)
      omega
    cases h_init : update_word words bA (fun word => setWordRange word.toNat rA 64 state) with
    | error e => simp [h_init, Bind.bind, Except.bind] at h_ok
    | ok initial =>
      obtain ⟨_, h_init_sz, h_init_elem⟩ := update_word_getElem? words bA _ initial h_init
      have h_mid_step : ∃ middle,
          forIn (Std.Legacy.Range.mk (bA + 1) bB 1 (by decide)) middle
            (write_step (if state then UInt64.ofNat wordMask else 0)) = .ok updated ∧
          middle.size = words.size ∧
          ∀ k, middle[k]? =
            if rB ≠ 0 ∧ k = bB then initial[bB]?.map (fun word => setWordRange word.toNat 0 rB state)
            else initial[k]? := by
        by_cases h_rB_zero : rB = 0
        · subst h_rB_zero
          simp only [h_init, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, Bind.bind, Except.bind, Pure.pure, Except.pure] at h_ok
          exact ⟨initial, h_ok, h_init_sz, fun k => by simp⟩
        · have h_bne : (rB != 0) = true := bne_iff_ne.mpr h_rB_zero
          simp only [h_init, h_bne, ↓reduceIte, Bind.bind, Except.bind] at h_ok
          cases h_m : update_word initial bB (fun word => setWordRange word.toNat 0 rB state) with
          | error e => simp [h_m] at h_ok
          | ok mid =>
            simp only [h_m] at h_ok
            obtain ⟨_, h_mid_sz, h_mid_elem⟩ := update_word_getElem? initial bB _ mid h_m
            refine ⟨mid, h_ok, h_mid_sz.trans h_init_sz, fun k => ?_⟩
            rw [h_mid_elem k]
            by_cases hk : k = bB
            · rw [if_pos_eq hk, if_pos_eq ⟨h_rB_zero, hk⟩]
            · rw [if_neg_eq hk, if_neg_eq (fun h => hk h.2)]
      obtain ⟨middle, h_loop, h_mid_sz, h_mid_elem⟩ := h_mid_step
      let fillWord : UInt64 := if state then UInt64.ofNat wordMask else 0
      obtain ⟨h_upd_sz, h_upd_elem⟩ := write_range_getElem? (bA + 1) bB middle fillWord updated h_loop
      refine ⟨h_upd_sz.trans h_mid_sz, fun k bit h_ib h_bit => ?_⟩
      have h_old : words[k]? = some (words[k]'h_ib) := Array.getElem?_eq_getElem h_ib
      have h_fill_bit : Nat.testBit fillWord.toNat bit = state := by
        dsimp only [fillWord]
        cases state
        · simp
        · simp only [↓reduceIte]
          have h_wm : (UInt64.ofNat wordMask).toNat = wordMask := by decide
          rw [h_wm, testBit_wordMask bit h_bit]
      by_cases h_in_mid : bA + 1 ≤ k ∧ k < bB
      · refine ⟨fillWord, words[k]'h_ib, ?_, h_old, ?_⟩
        · have he := h_upd_elem k
          rw [if_pos_eq h_in_mid] at he
          exact he
        · have h_in_idx : bA * 64 + rA ≤ k * 64 + bit ∧ k * 64 + bit < bB * 64 + rB := by omega
          rw [if_pos_eq h_in_idx, h_fill_bit]
      · have he_upd := h_upd_elem k
        rw [if_neg_eq h_in_mid, h_mid_elem k] at he_upd
        by_cases h_k_bB : rB ≠ 0 ∧ k = bB
        · obtain ⟨h_rB_nz, h_eq_bB⟩ := h_k_bB
          subst h_eq_bB
          have h_init_bB : initial[k]? = words[k]? := by
            have hi := h_init_elem k
            have hne : k ≠ bA := by omega
            rw [if_neg_eq hne] at hi
            exact hi
          rw [if_pos_eq ⟨h_rB_nz, rfl⟩, h_init_bB, h_old] at he_upd
          refine ⟨setWordRange (words[k]'h_ib).toNat 0 rB state, words[k]'h_ib, he_upd, h_old, ?_⟩
          have h_hi : rB ≤ 64 := by omega
          rw [setWordRange_testBit _ 0 rB bit state (Nat.zero_le _) h_hi h_bit]
          have h_iff : (0 ≤ bit ∧ bit < rB) ↔ (bA * 64 + rA ≤ k * 64 + bit ∧ k * 64 + bit < k * 64 + rB) := by omega
          by_cases h1 : 0 ≤ bit ∧ bit < rB
          · rw [if_pos_eq h1, if_pos_eq (h_iff.mp h1)]
          · rw [if_neg_eq h1, if_neg_eq (fun h2 => h1 (h_iff.mpr h2))]
        · rw [if_neg_eq h_k_bB, h_init_elem k] at he_upd
          by_cases h_k_bA : k = bA
          · subst h_k_bA
            rw [if_pos_eq rfl, h_old] at he_upd
            refine ⟨setWordRange (words[k]'h_ib).toNat rA 64 state, words[k]'h_ib, he_upd, h_old, ?_⟩
            have h_lo_hi : rA ≤ 64 := by omega
            rw [setWordRange_testBit _ rA 64 bit state h_lo_hi (Nat.le_refl 64) h_bit]
            have h_iff : (rA ≤ bit ∧ bit < 64) ↔ (k * 64 + rA ≤ k * 64 + bit ∧ k * 64 + bit < bB * 64 + rB) := by omega
            by_cases h1 : rA ≤ bit ∧ bit < 64
            · rw [if_pos_eq h1, if_pos_eq (h_iff.mp h1)]
            · rw [if_neg_eq h1, if_neg_eq (fun h2 => h1 (h_iff.mpr h2))]
          · rw [if_neg_eq h_k_bA] at he_upd
            refine ⟨words[k]'h_ib, words[k]'h_ib, he_upd.trans h_old, h_old, ?_⟩
            have h_out : ¬(bA * 64 + rA ≤ k * 64 + bit ∧ k * 64 + bit < bB * 64 + rB) := by omega
            rw [if_neg_eq h_out]

theorem get_ok_of_wellFormed (mask : InitMask) (idx : Size)
    (valid : WellFormed mask) (inBounds : idx.bytes.toNat < mask.len.bytes.toNat) :
    ∃ b, mask.get idx = .ok b := by
  cases mask with
  | mk blocks len =>
    cases blocks with
    | Lazy state => exact ⟨state, rfl⟩
    | Materialized blocks =>
      dsimp only [WellFormed] at valid
      dsimp only at inBounds
      have h_ib : idx.bytes.toNat / 64 < blocks.blocks.size := by omega
      refine ⟨Nat.testBit (blocks.blocks[idx.bytes.toNat / 64]'h_ib).toNat (idx.bytes.toNat % 64), ?_⟩
      rw [InitMask.get_eq_getR]
      unfold InitMask.getR Miri.Memory.InitMaskMaterialized.get
        Miri.Memory.InitMaskMaterialized.getBlock
        InitMaskMaterialized.bitIndexR Miri.Memory.sizeBytes Miri.Memory.blockSize
        Miri.Memory.bitAt
      dsimp only
      rw [Array.getElem?_eq_getElem h_ib]
      rfl

theorem set_range_get (mask updated : InitMask) (range : AllocRange) (finish idx : Size)
    (state : Bool)
    (valid : WellFormed mask) (endpoint : range.endExclusive = .ok finish)
    (nonempty : range.start.bytes.toNat < finish.bytes.toNat)
    (inBounds : finish.bytes.toNat ≤ mask.len.bytes.toNat)
    (idxInBounds : idx.bytes.toNat < mask.len.bytes.toNat)
    (h_set : mask.setRange range state = .ok updated) :
    updated.get idx =
      if range.start.bytes.toNat ≤ idx.bytes.toNat ∧ idx.bytes.toNat < finish.bytes.toNat then
        .ok state
      else
        mask.get idx := by
  cases mask with
  | mk blocks len =>
    dsimp only at inBounds idxInBounds
    cases blocks with
    | Materialized oldBlocks =>
      dsimp only [WellFormed] at valid
      rw [InitMask.setRange_eq_R] at h_set
      unfold InitMask.setRangeR at h_set
      simp only [endpoint, Bind.bind, Except.bind] at h_set
      by_cases full : range.start.bytes = 0 ∧ len.bytes ≤ finish.bytes
      · rw [if_pos_eq full] at h_set
        injection h_set with h_upd
        subst h_upd
        have h_in : range.start.bytes.toNat ≤ idx.bytes.toNat ∧ idx.bytes.toNat < finish.bytes.toNat := by
          have := UInt64.le_iff_toNat_le.mp full.2
          have h0 : range.start.bytes.toNat = 0 := by simp [full.1]
          omega
        rw [if_pos_eq h_in]
        rfl
      · rw [if_neg_eq full] at h_set
        have h_fin_le : finish.bytes ≤ len.bytes := UInt64.le_iff_toNat_le.mpr inBounds
        rw [if_pos_eq h_fin_le] at h_set
        have h_red := set_range_inbounds_reduces oldBlocks range.start finish state
        unfold setRangeInbounds at h_red
        rw [h_red] at h_set
        cases h_words : set_range_words oldBlocks.blocks
            (range.start.bytes.toNat / 64) (range.start.bytes.toNat % 64)
            (finish.bytes.toNat / 64) (finish.bytes.toNat % 64) state with
        | error e => simp [h_words, Bind.bind, Except.bind] at h_set
        | ok newWords =>
          simp only [h_words, Bind.bind, Except.bind, Pure.pure, Except.pure, Except.ok.injEq] at h_set
          subst h_set
          have h_rA : range.start.bytes.toNat % 64 < 64 := Nat.mod_lt _ (by decide)
          have h_rB : finish.bytes.toNat % 64 < 64 := Nat.mod_lt _ (by decide)
          have h_ne_mul : (range.start.bytes.toNat / 64) * 64 + range.start.bytes.toNat % 64 <
              (finish.bytes.toNat / 64) * 64 + finish.bytes.toNat % 64 := by omega
          obtain ⟨_, h_bit⟩ := set_range_words_bit_gen oldBlocks.blocks _ _ _ _ state newWords
            h_rA h_rB h_ne_mul h_words
          have h_ib : idx.bytes.toNat / 64 < oldBlocks.blocks.size := by omega
          obtain ⟨w, oldW, hw, holdW, h_tb⟩ := h_bit (idx.bytes.toNat / 64) (idx.bytes.toNat % 64)
            h_ib (Nat.mod_lt _ (by decide))
          have h_iff : ((range.start.bytes.toNat / 64) * 64 + range.start.bytes.toNat % 64 ≤
                (idx.bytes.toNat / 64) * 64 + idx.bytes.toNat % 64 ∧
              (idx.bytes.toNat / 64) * 64 + idx.bytes.toNat % 64 <
                (finish.bytes.toNat / 64) * 64 + finish.bytes.toNat % 64) ↔
              (range.start.bytes.toNat ≤ idx.bytes.toNat ∧ idx.bytes.toNat < finish.bytes.toNat) := by omega
          rw [InitMask.get_eq_getR]
          unfold InitMask.getR Miri.Memory.InitMaskMaterialized.get
            Miri.Memory.InitMaskMaterialized.getBlock
            InitMaskMaterialized.bitIndexR Miri.Memory.sizeBytes Miri.Memory.blockSize
            Miri.Memory.bitAt
          dsimp only
          rw [hw, holdW]
          simp only [Bind.bind, Except.bind, Pure.pure, Except.pure]
          rw [h_tb]
          by_cases h_in : range.start.bytes.toNat ≤ idx.bytes.toNat ∧ idx.bytes.toNat < finish.bytes.toNat
          · rw [if_pos_eq (h_iff.mpr h_in), if_pos_eq h_in]
          · rw [if_neg_eq (fun h => h_in (h_iff.mp h)), if_neg_eq h_in]
    | Lazy initial =>
      rw [InitMask.setRange_eq_R] at h_set
      unfold InitMask.setRangeR at h_set
      simp only [endpoint, Bind.bind, Except.bind] at h_set
      by_cases full : range.start.bytes = 0 ∧ len.bytes ≤ finish.bytes
      · rw [if_pos_eq full] at h_set
        injection h_set with h_upd
        subst h_upd
        have h_in : range.start.bytes.toNat ≤ idx.bytes.toNat ∧ idx.bytes.toNat < finish.bytes.toNat := by
          have := UInt64.le_iff_toNat_le.mp full.2
          have h0 : range.start.bytes.toNat = 0 := by simp [full.1]
          omega
        rw [if_pos_eq h_in]
        rfl
      · rw [if_neg_eq full] at h_set
        by_cases same : initial == state
        · have h_eq_st : initial = state := eq_of_beq same
          subst h_eq_st
          rw [if_pos_eq (beq_self_eq_true initial)] at h_set
          have notGrow : ¬finish.bytes > len.bytes := by
            simpa [UInt64.lt_iff_toNat_lt] using Nat.not_lt.mpr inBounds
          rw [if_neg_eq notGrow] at h_set
          injection h_set with h_upd
          subst h_upd
          by_cases h_in : range.start.bytes.toNat ≤ idx.bytes.toNat ∧ idx.bytes.toNat < finish.bytes.toNat
          · rw [if_pos_eq h_in]; rfl
          · rw [if_neg_eq h_in]
        · rw [if_neg_eq same] at h_set
          have lenNonzero : len.bytes.toNat ≠ 0 := by omega
          have matEq := materialize_lazy_nonzero len initial lenNonzero
          unfold materialize InitMask.new at matEq
          rw [matEq] at h_set
          have h_fin_le : finish.bytes ≤ len.bytes := UInt64.le_iff_toNat_le.mpr inBounds
          dsimp only at h_set
          rw [if_pos_eq h_fin_le] at h_set
          let initWords := Array.replicate (len.bytes.toNat / 64 + 1)
            (if initial then UInt64.ofNat 18446744073709551615 else 0)
          have h_red := set_range_inbounds_reduces ⟨initWords⟩ range.start finish state
          unfold setRangeInbounds at h_red
          dsimp only [initWords] at h_red
          rw [h_red] at h_set
          cases h_words : set_range_words initWords
              (range.start.bytes.toNat / 64) (range.start.bytes.toNat % 64)
              (finish.bytes.toNat / 64) (finish.bytes.toNat % 64) state with
          | error e =>
            dsimp only [initWords] at h_words
            rw [h_words] at h_set
            cases h_set
          | ok newWords =>
            have h_words_unf := h_words
            dsimp only [initWords] at h_words_unf
            rw [h_words_unf] at h_set
            simp only [Bind.bind, Except.bind, Pure.pure, Except.pure, Except.ok.injEq] at h_set
            subst h_set
            have h_rA : range.start.bytes.toNat % 64 < 64 := Nat.mod_lt _ (by decide)
            have h_rB : finish.bytes.toNat % 64 < 64 := Nat.mod_lt _ (by decide)
            have h_ne_mul : (range.start.bytes.toNat / 64) * 64 + range.start.bytes.toNat % 64 <
                (finish.bytes.toNat / 64) * 64 + finish.bytes.toNat % 64 := by omega
            obtain ⟨_, h_bit⟩ := set_range_words_bit_gen initWords _ _ _ _ state newWords
              h_rA h_rB h_ne_mul h_words
            have h_ib : idx.bytes.toNat / 64 < initWords.size := by
              simp only [initWords, Array.size_replicate]; omega
            obtain ⟨w, oldW, hw, holdW, h_tb⟩ := h_bit (idx.bytes.toNat / 64) (idx.bytes.toNat % 64)
              h_ib (Nat.mod_lt _ (by decide))
            have h_oldW_eq : oldW = (if initial then UInt64.ofNat 18446744073709551615 else 0) := by
              have h_ib_len : idx.bytes.toNat / 64 < len.bytes.toNat / 64 + 1 := by omega
              have h_rep : initWords[idx.bytes.toNat / 64]? =
                  some (if initial then UInt64.ofNat 18446744073709551615 else 0) := by
                simp [initWords, h_ib_len]
              exact Option.some.inj (holdW.symm.trans h_rep)
            have h_old_bit : Nat.testBit oldW.toNat (idx.bytes.toNat % 64) = initial := by
              rw [h_oldW_eq]
              cases initial
              · simp
              · simp only [↓reduceIte]
                have h_wm : (UInt64.ofNat 18446744073709551615).toNat = wordMask := by decide
                rw [h_wm, testBit_wordMask _ (Nat.mod_lt _ (by decide))]
            have h_iff : ((range.start.bytes.toNat / 64) * 64 + range.start.bytes.toNat % 64 ≤
                  (idx.bytes.toNat / 64) * 64 + idx.bytes.toNat % 64 ∧
                (idx.bytes.toNat / 64) * 64 + idx.bytes.toNat % 64 <
                  (finish.bytes.toNat / 64) * 64 + finish.bytes.toNat % 64) ↔
                (range.start.bytes.toNat ≤ idx.bytes.toNat ∧ idx.bytes.toNat < finish.bytes.toNat) := by omega
            rw [InitMask.get_eq_getR]
            unfold InitMask.getR Miri.Memory.InitMaskMaterialized.get
              Miri.Memory.InitMaskMaterialized.getBlock
              InitMaskMaterialized.bitIndexR Miri.Memory.sizeBytes Miri.Memory.blockSize
              Miri.Memory.bitAt
            dsimp only
            rw [hw]
            simp only [Bind.bind, Except.bind, Pure.pure, Except.pure]
            rw [h_tb, h_old_bit]
            by_cases h_in : range.start.bytes.toNat ≤ idx.bytes.toNat ∧ idx.bytes.toNat < finish.bytes.toNat
            · rw [if_pos_eq (h_iff.mpr h_in), if_pos_eq h_in]
            · rw [if_neg_eq (fun h => h_in (h_iff.mp h)), if_neg_eq h_in]

private theorem firstSetBit_spec_none (bits startBit : Nat) :
    Miri.Memory.InitMaskMaterialized.firstSetBit bits startBit = none ↔
      ∀ b, startBit ≤ b → b < 64 → Nat.testBit bits b = false := by
  unfold Miri.Memory.InitMaskMaterialized.firstSetBit Miri.Memory.bitAt
  simp only [Option.map_eq_none_iff, List.find?_eq_none, List.mem_range, Bool.not_eq_true]
  constructor
  · intro h b h_lo h_hi
    have h_off : b - startBit < 64 - startBit := by omega
    have h_eq : startBit + (b - startBit) = b := by omega
    simpa [h_eq] using h (b - startBit) h_off
  · intro h off h_off
    exact h (startBit + off) (by omega) (by omega)

private theorem firstSetBit_spec_some (bits startBit res : Nat)
    (h_some : Miri.Memory.InitMaskMaterialized.firstSetBit bits startBit = some res) :
    startBit ≤ res ∧ res < 64 ∧ Nat.testBit bits res = true ∧
      ∀ b, startBit ≤ b → b < res → Nat.testBit bits b = false := by
  unfold Miri.Memory.InitMaskMaterialized.firstSetBit Miri.Memory.bitAt at h_some
  rw [Option.map_eq_some_iff] at h_some
  obtain ⟨off, h_find, rfl⟩ := h_some
  have h_mem : off ∈ List.range (64 - startBit) := List.mem_of_find?_eq_some h_find
  rw [List.mem_range] at h_mem
  obtain ⟨h_true, xs, ys, h_eq_list, h_all_false⟩ := List.find?_eq_some_iff_append.mp h_find
  refine ⟨by omega, by omega, by simpa [Nat.add_comm] using h_true, fun b h_lo h_lt => ?_⟩
  have h_pw : List.Pairwise (· < ·) (List.range (64 - startBit)) := List.pairwise_lt_range
  rw [h_eq_list, List.pairwise_append, List.pairwise_cons] at h_pw
  obtain ⟨_, ⟨h_lt_ys, _⟩, _⟩ := h_pw
  have h_b_mem : b - startBit ∈ List.range (64 - startBit) := by
    rw [List.mem_range]; omega
  rw [h_eq_list, List.mem_append, List.mem_cons] at h_b_mem
  rcases h_b_mem with h_in_xs | h_eq_off | h_in_ys
  · have hf := h_all_false (b - startBit) h_in_xs
    have h_sum : startBit + (b - startBit) = b := by omega
    simpa [Bool.not_eq_true, h_sum] using hf
  · omega
  · have := h_lt_ys (b - startBit) h_in_ys
    omega

private theorem testBit_wordMask_sub (w : UInt64) (bit : Nat) (h_bit : bit < 64) :
    Nat.testBit (wordMask - w.toNat) bit = !Nat.testBit w.toNat bit := by
  have h_wm : wordMask = 2 ^ 64 - 1 := by decide
  rw [h_wm]
  have h_lt := w.toNat_lt
  have h_bv : BitVec.ofNat 64 (2 ^ 64 - 1 - w.toNat) = ~~~(BitVec.ofNat 64 w.toNat) := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_not]
    omega
  have h1 := congrArg (fun b : BitVec 64 => b.getLsbD bit) h_bv
  simp only [BitVec.getLsbD_ofNat, BitVec.getLsbD_not, h_bit, decide_true, Bool.true_and] at h1
  exact h1

private theorem searchBlock_spec (word : UInt64) (block startBit : Nat) (isInit : Bool)
    (h_block_fits : block * 64 + 63 ≤ 18446744073709551615) :
    ∃ res?, Miri.Memory.InitMaskMaterialized.searchBlock word block startBit isInit = .ok res? ∧
      match res? with
      | none => ∀ b, startBit ≤ b → b < 64 → Nat.testBit word.toNat b = !isInit
      | some idx =>
        ∃ bit, startBit ≤ bit ∧ bit < 64 ∧ idx.bytes.toNat = block * 64 + bit ∧
          Nat.testBit word.toNat bit = isInit ∧
          ∀ b, startBit ≤ b → b < bit → Nat.testBit word.toNat b = !isInit := by
  let bits := if isInit then word.toNat else wordMask - word.toNat
  have h_bits_tb : ∀ b, b < 64 → (Nat.testBit bits b = true ↔ Nat.testBit word.toNat b = isInit) := by
    intro b hb
    dsimp only [bits]
    cases isInit
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [testBit_wordMask_sub word b hb]
      cases word.toNat.testBit b <;> simp
    · simp
  have h_bits_false : ∀ b, b < 64 → (Nat.testBit bits b = false ↔ Nat.testBit word.toNat b = !isInit) := by
    intro b hb
    dsimp only [bits]
    cases isInit
    · simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_false]
      rw [testBit_wordMask_sub word b hb]
      cases word.toNat.testBit b <;> simp
    · simp
  cases h_fsb : Miri.Memory.InitMaskMaterialized.firstSetBit bits startBit with
  | none =>
    refine ⟨none, ?_, ?_⟩
    · unfold Miri.Memory.InitMaskMaterialized.searchBlock
      dsimp only [bits] at h_fsb
      unfold wordMask at h_fsb
      simp [h_fsb, Pure.pure, Except.pure]
    · intro b h_lo h_hi
      have hf := (firstSetBit_spec_none bits startBit).mp h_fsb b h_lo h_hi
      exact (h_bits_false b h_hi).mp hf
  | some bit =>
    obtain ⟨h_lo, h_hi, h_tb, h_prev⟩ := firstSetBit_spec_some bits startBit bit h_fsb
    have h_fits : block * 64 + bit ≤ Miri.Memory.maxSizeBytes := by
      unfold Miri.Memory.maxSizeBytes; omega
    have h_lt264 : block * 64 + bit < 2 ^ 64 := by omega
    let idx := Size.ofBytes (UInt64.ofNat (block * 64 + bit))
    have h_sfi : Miri.Memory.InitMaskMaterialized.sizeFromBitIndex block bit = .ok idx := by
      unfold Miri.Memory.InitMaskMaterialized.sizeFromBitIndex Miri.Memory.sizeFromNat Miri.Memory.blockSize
      rw [if_pos_eq h_fits]
    refine ⟨some idx, ?_, bit, h_lo, h_hi, ?_, (h_bits_tb bit h_hi).mp h_tb, ?_⟩
    · unfold Miri.Memory.InitMaskMaterialized.searchBlock
      dsimp only [bits] at h_fsb
      unfold wordMask at h_fsb
      simp [h_fsb, h_sfi, Bind.bind, Except.bind, Pure.pure, Except.pure]
    · simp [idx, Size.ofBytes, UInt64.toNat_ofNat', Nat.mod_eq_of_lt h_lt264]
    · intro b hb_lo hb_lt
      exact (h_bits_false b (by omega)).mp (h_prev b hb_lo hb_lt)

private theorem search_blocks_list_spec (self : InitMaskMaterialized) (finish : Size) (isInit : Bool)
    (blocksList : List Nat)
    (h_sorted : List.Pairwise (· < ·) blocksList)
    (h_blocks_in : ∀ blk ∈ blocksList, blk < self.blocks.size)
    (h_blocks_fits : ∀ blk ∈ blocksList, blk * 64 + 63 ≤ 18446744073709551615) :
    ∃ out,
      forIn blocksList (none, ⟨⟩) (fun (block : Nat) (_ : Option (Option Size) × PUnit) =>
        (do
          match ← Miri.Memory.InitMaskMaterialized.searchBlock (← getBlock self block) block 0 isInit with
          | some index =>
            if Miri.Memory.sizeBytes index < Miri.Memory.sizeBytes finish then
              pure (ForInStep.done (some (some index), ⟨⟩))
            else
              pure (ForInStep.done (some none, ⟨⟩))
          | none => pure (ForInStep.yield (none, ⟨⟩)) :
          Except InitMaskError (ForInStep (Option (Option Size) × PUnit)))) = .ok (out, ⟨⟩) ∧
      match out with
      | none | some none =>
        ∀ blk (h_mem : blk ∈ blocksList) (b : Nat), b < 64 → blk * 64 + b < finish.bytes.toNat →
          Nat.testBit (self.blocks[blk]'(h_blocks_in blk h_mem)).toNat b = !isInit
      | some (some idx) =>
        ∃ blk, ∃ (h_mem : blk ∈ blocksList), ∃ bit, bit < 64 ∧
          idx.bytes.toNat = blk * 64 + bit ∧
          idx.bytes.toNat < finish.bytes.toNat ∧
          Nat.testBit (self.blocks[blk]'(h_blocks_in blk h_mem)).toNat bit = isInit ∧
          ∀ blk' (h_mem' : blk' ∈ blocksList) (b : Nat), b < 64 →
            blk' * 64 + b < idx.bytes.toNat →
            Nat.testBit (self.blocks[blk']'(h_blocks_in blk' h_mem')).toNat b = !isInit := by
  induction blocksList with
  | nil =>
    refine ⟨none, rfl, fun _ h => False.elim (List.not_mem_nil h)⟩
  | cons blk rest ih =>
    rw [List.pairwise_cons] at h_sorted
    obtain ⟨h_lt_rest, h_pw_rest⟩ := h_sorted
    have h_ib : blk < self.blocks.size := h_blocks_in blk (List.mem_cons_self ..)
    have h_fits : blk * 64 + 63 ≤ 18446744073709551615 := h_blocks_fits blk (List.mem_cons_self ..)
    have h_gb : getBlock self blk = .ok (self.blocks[blk]'h_ib) := get_block_ok self.blocks blk h_ib
    obtain ⟨res?, h_sb, h_sb_prop⟩ := searchBlock_spec (self.blocks[blk]'h_ib) blk 0 isInit h_fits
    cases res? with
    | none =>
      obtain ⟨tailOut, h_tail, h_tail_prop⟩ := ih h_pw_rest
        (fun x hx => h_blocks_in x (List.mem_cons_of_mem _ hx))
        (fun x hx => h_blocks_fits x (List.mem_cons_of_mem _ hx))
      refine ⟨tailOut, ?_, ?_⟩
      · simp only [List.forIn_cons, h_gb, h_sb, Bind.bind, Except.bind, Pure.pure, Except.pure]
        exact h_tail
      · cases tailOut with
        | none =>
          intro x hx b hb h_lt_fin
          rcases List.mem_cons.mp hx with rfl | hx_rest
          · exact h_sb_prop b (Nat.zero_le _) hb
          · exact h_tail_prop x hx_rest b hb h_lt_fin
        | some inner =>
          cases inner with
          | none =>
            intro x hx b hb h_lt_fin
            rcases List.mem_cons.mp hx with rfl | hx_rest
            · exact h_sb_prop b (Nat.zero_le _) hb
            · exact h_tail_prop x hx_rest b hb h_lt_fin
          | some idx =>
            obtain ⟨x, hx_rest, bit, hbit, h_idx_eq, h_lt_fin, h_tb, h_prev_rest⟩ := h_tail_prop
            refine ⟨x, List.mem_cons_of_mem _ hx_rest, bit, hbit, h_idx_eq, h_lt_fin, h_tb, ?_⟩
            intro x' hx' b hb h_lt_idx
            rcases List.mem_cons.mp hx' with rfl | hx'_rest
            · exact h_sb_prop b (Nat.zero_le _) hb
            · exact h_prev_rest x' hx'_rest b hb h_lt_idx
    | some idx =>
      obtain ⟨bit, _, hbit, h_idx_eq, h_tb, h_prev⟩ := h_sb_prop
      by_cases h_lt_fin : Miri.Memory.sizeBytes idx < Miri.Memory.sizeBytes finish
      · refine ⟨some (some idx), ?_, blk, List.mem_cons_self .., bit, hbit, h_idx_eq, ?_, h_tb, ?_⟩
        · simp [List.forIn_cons, h_gb, h_sb, h_lt_fin, Bind.bind, Except.bind, Pure.pure, Except.pure]
        · simpa [Miri.Memory.sizeBytes] using h_lt_fin
        · intro x' hx' b hb h_lt_idx
          rcases List.mem_cons.mp hx' with rfl | hx'_rest
          · exact h_prev b (Nat.zero_le _) (by omega)
          · have := h_lt_rest x' hx'_rest
            omega
      · refine ⟨some none, ?_, ?_⟩
        · simp [List.forIn_cons, h_gb, h_sb, h_lt_fin, Bind.bind, Except.bind, Pure.pure, Except.pure]
        · have h_ge_fin : finish.bytes.toNat ≤ blk * 64 + bit := by
            simp only [Miri.Memory.sizeBytes] at h_lt_fin
            omega
          intro x hx b hb h_lt
          rcases List.mem_cons.mp hx with rfl | hx_rest
          · exact h_prev b (Nat.zero_le _) (by omega)
          · have := h_lt_rest x hx_rest
            omega

private theorem findBit_spec (self : InitMaskMaterialized) (start finish : Size) (isInit : Bool)
    (h_cap : finish.bytes.toNat ≤ self.blocks.size * 64) :
    ∃ res?, Miri.Memory.InitMaskMaterialized.findBit self start finish isInit = .ok res? ∧
      match res? with
      | none =>
        ∀ (idx : Size), start.bytes.toNat ≤ idx.bytes.toNat → idx.bytes.toNat < finish.bytes.toNat →
          Miri.Memory.InitMaskMaterialized.get self idx = .ok (!isInit)
      | some found =>
        start.bytes.toNat ≤ found.bytes.toNat ∧ found.bytes.toNat < finish.bytes.toNat ∧
          Miri.Memory.InitMaskMaterialized.get self found = .ok isInit ∧
          ∀ (idx : Size), start.bytes.toNat ≤ idx.bytes.toNat → idx.bytes.toNat < found.bytes.toNat →
            Miri.Memory.InitMaskMaterialized.get self idx = .ok (!isInit) := by
  unfold Miri.Memory.InitMaskMaterialized.findBit
    Miri.Memory.InitMaskMaterialized.findBitFast
  have h_fin_u64 := finish.bytes.toNat_lt
  by_cases h_empty : Miri.Memory.sizeBytes start ≥ Miri.Memory.sizeBytes finish
  · refine ⟨none, ?_, ?_⟩
    · simp [h_empty, Pure.pure, Except.pure]
    · intro idx h1 h2
      simp only [Miri.Memory.sizeBytes] at h_empty
      omega
  · rw [if_neg_eq h_empty]
    have h_lt_sf : start.bytes.toNat < finish.bytes.toNat := by
      simp only [Miri.Memory.sizeBytes] at h_empty; omega
    let startBlock := start.bytes.toNat / 64
    let startBit := start.bytes.toNat % 64
    let endIncNat := finish.bytes.toNat - 1
    have h_end_fits : endIncNat ≤ Miri.Memory.maxSizeBytes := by
      unfold Miri.Memory.maxSizeBytes; omega
    have h_sfn : Miri.Memory.sizeFromNat (finish.bytes.toNat - 1) =
        .ok (Size.ofBytes (UInt64.ofNat endIncNat)) := by
      unfold Miri.Memory.sizeFromNat
      dsimp only [endIncNat] at h_end_fits ⊢
      rw [if_pos_eq h_end_fits]
    have h_endInc_bytes : (Size.ofBytes (UInt64.ofNat endIncNat)).bytes.toNat = endIncNat := by
      simp [Size.ofBytes, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega : endIncNat < 2 ^ 64)]
    let endBlock := endIncNat / 64
    have h_sb_ib : startBlock < self.blocks.size := by dsimp only [startBlock]; omega
    have h_eb_ib : endBlock < self.blocks.size := by dsimp only [endBlock, endIncNat]; omega
    have h_sb_fits : startBlock * 64 + 63 ≤ 18446744073709551615 := by
      dsimp only [startBlock]; omega
    have h_gb0 : Miri.Memory.InitMaskMaterialized.getBlock self startBlock = .ok (self.blocks[startBlock]'h_sb_ib) :=
      get_block_ok self.blocks startBlock h_sb_ib
    obtain ⟨first?, h_sb0, h_sb0_prop⟩ := searchBlock_spec (self.blocks[startBlock]'h_sb_ib) startBlock startBit isInit h_sb_fits
    have h_get_eq : ∀ (idx : Size) (h_ib : idx.bytes.toNat / 64 < self.blocks.size),
        Miri.Memory.InitMaskMaterialized.get self idx =
          .ok (Nat.testBit (self.blocks[idx.bytes.toNat / 64]'h_ib).toNat (idx.bytes.toNat % 64)) := by
      intro idx h_ib
      unfold Miri.Memory.InitMaskMaterialized.get Miri.Memory.InitMaskMaterialized.getBlock
        InitMaskMaterialized.bitIndexR Miri.Memory.sizeBytes Miri.Memory.blockSize Miri.Memory.bitAt
      dsimp only
      rw [Array.getElem?_eq_getElem h_ib]
      rfl
    simp only [InitMaskMaterialized.bitIndexR, Miri.Memory.sizeBytes, Miri.Memory.blockSize]
    rw [h_sfn]
    simp only [Bind.bind, Except.bind, h_endInc_bytes]
    dsimp only [startBlock, startBit, endBlock] at h_gb0 h_sb0 ⊢
    rw [h_gb0]
    simp only
    rw [h_sb0]
    simp only
    cases first? with
    | some firstIdx =>
      obtain ⟨bit, h_lo, h_hi, h_f_eq, h_tb, h_prev⟩ := h_sb0_prop
      by_cases h_lt_f : firstIdx.bytes.toNat < finish.bytes.toNat
      · refine ⟨some firstIdx, ?_, ?_⟩
        · simp [h_lt_f, Pure.pure, Except.pure]
        · have h_div : firstIdx.bytes.toNat / 64 = startBlock := by omega
          have h_mod : firstIdx.bytes.toNat % 64 = bit := by omega
          refine ⟨by dsimp only [startBlock, startBit] at h_lo h_f_eq; omega, h_lt_f, ?_, ?_⟩
          · rw [h_get_eq firstIdx (by omega)]
            simpa [h_div, h_mod] using h_tb
          · intro idx h_idx_lo h_idx_lt
            have h_idx_div : idx.bytes.toNat / 64 = startBlock := by
              dsimp only [startBlock, startBit] at h_lo h_f_eq; omega
            rw [h_get_eq idx (by omega)]
            have h_p := h_prev (idx.bytes.toNat % 64)
              (by dsimp only [startBlock, startBit] at h_idx_div ⊢; omega)
              (by dsimp only [startBlock] at h_idx_div h_f_eq; omega)
            simpa [h_idx_div] using h_p
      · refine ⟨none, ?_, ?_⟩
        · simp [h_lt_f, Pure.pure, Except.pure]
        · intro idx h_idx_lo h_idx_lt
          have h_idx_div : idx.bytes.toNat / 64 = startBlock := by
            dsimp only [startBlock, startBit] at h_f_eq h_lt_f; omega
          rw [h_get_eq idx (by omega)]
          have h_p := h_prev (idx.bytes.toNat % 64)
            (by dsimp only [startBlock, startBit] at h_idx_div ⊢; omega)
            (by dsimp only [startBlock] at h_idx_div h_f_eq h_lt_f; omega)
          simpa [h_idx_div] using h_p
    | none =>
      by_cases h_more : startBlock < endBlock
      · dsimp only [startBlock, endBlock, endIncNat] at h_more
        rw [if_pos_eq h_more]
        rw [Std.Legacy.Range.forIn_eq_forIn_range']
        let rngList := List.range' [startBlock + 1:endBlock + 1].start
          [startBlock + 1:endBlock + 1].size [startBlock + 1:endBlock + 1].step
        have h_mem_rng : ∀ x, x ∈ rngList ↔ (startBlock + 1 ≤ x ∧ x ≤ endBlock) := by
          intro x
          simp only [rngList, List.mem_range', Std.Legacy.Range.size, Nat.div_one, Nat.one_mul]
          constructor
          · rintro ⟨i, hi, rfl⟩; omega
          · intro ⟨h1, h2⟩; exact ⟨x - (startBlock + 1), by omega, by omega⟩
        have h_pw_rng : List.Pairwise (· < ·) rngList := List.pairwise_lt_range'
        have h_in_rng : ∀ x ∈ rngList, x < self.blocks.size := by
          intro x hx; have := (h_mem_rng x).mp hx; omega
        have h_fits_rng : ∀ x ∈ rngList, x * 64 + 63 ≤ 18446744073709551615 := by
          intro x hx; have := (h_mem_rng x).mp hx
          dsimp only [endBlock, endIncNat] at this; omega
        obtain ⟨loopOut, h_loop, h_loop_prop⟩ := search_blocks_list_spec self finish isInit
          rngList h_pw_rng h_in_rng h_fits_rng
        unfold Miri.Memory.sizeBytes getBlock at h_loop
        dsimp only [rngList, startBlock, endBlock, endIncNat] at h_loop
        simp only [Bind.bind, Except.bind] at h_loop ⊢
        erw [h_loop]
        simp only [Pure.pure, Except.pure]
        cases loopOut with
        | none =>
          refine ⟨none, rfl, ?_⟩
          intro idx h_idx_lo h_idx_lt
          by_cases hk : idx.bytes.toNat / 64 = startBlock
          · rw [h_get_eq idx (by omega)]
            have h_p := h_sb0_prop (idx.bytes.toNat % 64)
              (by dsimp only [startBlock, startBit] at hk ⊢; omega)
              (Nat.mod_lt _ (by decide))
            simpa [hk] using h_p
          · have h_in_l : idx.bytes.toNat / 64 ∈ rngList :=
              (h_mem_rng _).mpr (by dsimp only [startBlock, endBlock, endIncNat] at hk ⊢; omega)
            rw [h_get_eq idx (h_in_rng _ h_in_l)]
            exact congrArg Except.ok
              (h_loop_prop (idx.bytes.toNat / 64) h_in_l (idx.bytes.toNat % 64)
                (Nat.mod_lt _ (by decide)) (by omega))
        | some inner =>
          cases inner with
          | none =>
            refine ⟨none, rfl, ?_⟩
            intro idx h_idx_lo h_idx_lt
            by_cases hk : idx.bytes.toNat / 64 = startBlock
            · rw [h_get_eq idx (by omega)]
              have h_p := h_sb0_prop (idx.bytes.toNat % 64)
                (by dsimp only [startBlock, startBit] at hk ⊢; omega)
                (Nat.mod_lt _ (by decide))
              simpa [hk] using h_p
            · have h_in_l : idx.bytes.toNat / 64 ∈ rngList :=
                (h_mem_rng _).mpr (by dsimp only [startBlock, endBlock, endIncNat] at hk ⊢; omega)
              rw [h_get_eq idx (h_in_rng _ h_in_l)]
              exact congrArg Except.ok
                (h_loop_prop (idx.bytes.toNat / 64) h_in_l (idx.bytes.toNat % 64)
                  (Nat.mod_lt _ (by decide)) (by omega))
          | some found =>
            obtain ⟨blk, h_blk_mem, bit, hbit, h_f_eq, h_f_lt, h_f_tb, h_f_prev⟩ := h_loop_prop
            have h_blk_bounds := (h_mem_rng blk).mp h_blk_mem
            have h_f_div : found.bytes.toNat / 64 = blk := by omega
            have h_f_mod : found.bytes.toNat % 64 = bit := by omega
            refine ⟨some found, rfl, ?_, h_f_lt, ?_, ?_⟩
            · dsimp only [startBlock] at h_blk_bounds; omega
            · rw [h_get_eq found (by omega)]
              simpa [h_f_div, h_f_mod] using h_f_tb
            · intro idx h_idx_lo h_idx_lt
              by_cases hk : idx.bytes.toNat / 64 = startBlock
              · rw [h_get_eq idx (by omega)]
                have h_p := h_sb0_prop (idx.bytes.toNat % 64)
                  (by dsimp only [startBlock, startBit] at hk ⊢; omega)
                  (Nat.mod_lt _ (by decide))
                simpa [hk] using h_p
              · have h_in_l : idx.bytes.toNat / 64 ∈ rngList := (h_mem_rng _).mpr (by
                  dsimp only [startBlock, endBlock, endIncNat] at hk h_blk_bounds ⊢; omega)
                rw [h_get_eq idx (h_in_rng _ h_in_l)]
                exact congrArg Except.ok
                  (h_f_prev (idx.bytes.toNat / 64) h_in_l (idx.bytes.toNat % 64)
                    (Nat.mod_lt _ (by decide)) (by omega))
      · dsimp only [startBlock, endBlock, endIncNat] at h_more
        rw [if_neg_eq h_more]
        refine ⟨none, rfl, ?_⟩
        intro idx h_idx_lo h_idx_lt
        have h_idx_div : idx.bytes.toNat / 64 = startBlock := by
          dsimp only [startBlock] at h_more ⊢; omega
        rw [h_get_eq idx (by omega)]
        have h_p := h_sb0_prop (idx.bytes.toNat % 64)
          (by dsimp only [startBlock, startBit] at h_idx_div ⊢; omega)
          (Nat.mod_lt _ (by decide))
        simpa [h_idx_div] using h_p

private theorem fromEndpoints_ok_of_le (a b : Size) (h : a.bytes.toNat ≤ b.bytes.toNat) :
    ∃ r, AllocRange.fromEndpoints a b = .ok r ∧ r.start = a ∧
      r.size.bytes.toNat = b.bytes.toNat - a.bytes.toNat := by
  have h_le : a.bytes ≤ b.bytes := UInt64.le_iff_toNat_le.mpr h
  have h_not_lt : ¬(b.bytes < a.bytes) := UInt64.not_lt.mpr h_le
  refine ⟨⟨a, Size.ofBytes (b.bytes - a.bytes)⟩, ?_, rfl, ?_⟩
  · unfold AllocRange.fromEndpoints Size.sub
    simp [h_not_lt, Bind.bind, Except.bind, Except.mapError, Pure.pure, Except.pure]
  · simp [Size.ofBytes, UInt64.toNat_sub_of_le _ _ h_le]

theorem isRangeInitialized_nonempty_iff (mask : InitMask) (range : AllocRange) (finish : Size)
    (valid : WellFormed mask) (endpoint : range.endExclusive = .ok finish)
    (nonempty : range.start.bytes.toNat < finish.bytes.toNat)
    (inBounds : finish.bytes.toNat ≤ mask.len.bytes.toNat) :
    (mask.isRangeInitialized range = .ok (.ok ()) ↔
      ∀ (idx : Size), range.start.bytes.toNat ≤ idx.bytes.toNat → idx.bytes.toNat < finish.bytes.toNat →
        mask.get idx = .ok true) ∧
    ((∃ idx : Size, range.start.bytes.toNat ≤ idx.bytes.toNat ∧ idx.bytes.toNat < finish.bytes.toNat ∧
        mask.get idx = .ok false) →
      ∃ bad : AllocRange, mask.isRangeInitialized range = .ok (.error bad)) := by
  have h_not_oob : ¬(finish.bytes > mask.len.bytes) := by
    simpa [UInt64.lt_iff_toNat_lt] using Nat.not_lt.mpr inBounds
  cases mask with
  | mk blocks len =>
    dsimp only at inBounds h_not_oob
    cases blocks with
    | Lazy state =>
      rw [InitMask.isRangeInitialized_eq_R, InitMask.get_eq_getR]
      unfold InitMask.isRangeInitializedR InitMask.getR
      simp only [endpoint, Bind.bind, Except.bind, h_not_oob, ↓reduceIte, Pure.pure, Except.pure]
      cases state
      · simp only [Bool.false_eq_true, ↓reduceIte]
        constructor
        · constructor
          · intro h; cases h
          · intro h_all
            have h_start := h_all range.start (Nat.le_refl _) nonempty
            cases h_start
        · intro _
          exact ⟨range, rfl⟩
      · simp only [↓reduceIte]
        constructor
        · constructor
          · intro _ _ _ _; trivial
          · intro _; trivial
        · rintro ⟨_, _, _, hf⟩
          cases hf
    | Materialized mat =>
      dsimp only [WellFormed] at valid
      have h_cap : finish.bytes.toNat ≤ mat.blocks.size * 64 := by omega
      obtain ⟨uninit?, h_fb0, h_fb0_prop⟩ := findBit_spec mat range.start finish false h_cap
      rw [InitMask.isRangeInitialized_eq_R, InitMask.get_eq_getR]
      unfold InitMask.isRangeInitializedR InitMask.getR
      simp only [endpoint, Bind.bind, Except.bind, h_not_oob, ↓reduceIte, h_fb0]
      cases uninit? with
      | none =>
        dsimp only at h_fb0_prop ⊢
        simp only [Pure.pure, Except.pure, Bool.not_false] at h_fb0_prop ⊢
        constructor
        · constructor
          · intro _ idx h1 h2; exact h_fb0_prop idx h1 h2
          · intro _; trivial
        · rintro ⟨idx, h1, h2, hf⟩
          have ht : Miri.Memory.InitMaskMaterialized.get mat idx = .ok true := h_fb0_prop idx h1 h2
          rw [ht] at hf
          cases hf
      | some uninitStart =>
        dsimp only at h_fb0_prop ⊢
        obtain ⟨h_us_lo, h_us_lt, h_us_get, _⟩ := h_fb0_prop
        obtain ⟨end?, h_fb1, h_fb1_prop⟩ := findBit_spec mat uninitStart finish true h_cap
        rw [h_fb1]
        simp only [Pure.pure, Except.pure]
        have h_end_ge : uninitStart.bytes.toNat ≤ (end?.getD finish).bytes.toNat := by
          cases end? with
          | none => exact Nat.le_of_lt h_us_lt
          | some e => exact h_fb1_prop.1
        obtain ⟨bad, h_bad, _, _⟩ := fromEndpoints_ok_of_le uninitStart (end?.getD finish) h_end_ge
        rw [h_bad]
        dsimp only
        constructor
        · constructor
          · intro h; cases h
          · intro h_all
            have ht := h_all uninitStart h_us_lo h_us_lt
            rw [h_us_get] at ht
            cases ht
        · intro _
          exact ⟨bad, rfl⟩

theorem isRangeInitialized_after_setRange_true (mask updated : InitMask)
    (range : AllocRange) (finish : Size)
    (valid : WellFormed mask) (endpoint : range.endExclusive = .ok finish)
    (nonempty : range.start.bytes.toNat < finish.bytes.toNat)
    (inBounds : finish.bytes.toNat ≤ mask.len.bytes.toNat)
    (h_set : mask.setRange range true = .ok updated) :
    updated.isRangeInitialized range = .ok (.ok ()) := by
  obtain ⟨u, h_u, h_len, h_wf⟩ := set_range_exists mask range finish true valid endpoint nonempty inBounds
  have h_eq : u = updated := Except.ok.inj (h_u.symm.trans h_set)
  subst h_eq
  rw [(isRangeInitialized_nonempty_iff u range finish h_wf endpoint nonempty (by rw [h_len]; exact inBounds)).1]
  intro idx h_lo h_hi
  have h_idx_ib : idx.bytes.toNat < mask.len.bytes.toNat := by omega
  rw [set_range_get mask u range finish idx true valid endpoint nonempty inBounds h_idx_ib h_u]
  rw [if_pos_eq ⟨h_lo, h_hi⟩]

theorem isRangeInitialized_frame (mask updated : InitMask)
    (writeRange queryRange : AllocRange) (writeFinish queryFinish : Size) (state : Bool)
    (valid : WellFormed mask)
    (wEnd : writeRange.endExclusive = .ok writeFinish)
    (qEnd : queryRange.endExclusive = .ok queryFinish)
    (wNonempty : writeRange.start.bytes.toNat < writeFinish.bytes.toNat)
    (qNonempty : queryRange.start.bytes.toNat < queryFinish.bytes.toNat)
    (wInBounds : writeFinish.bytes.toNat ≤ mask.len.bytes.toNat)
    (qInBounds : queryFinish.bytes.toNat ≤ mask.len.bytes.toNat)
    (disjoint : writeFinish.bytes.toNat ≤ queryRange.start.bytes.toNat ∨
      queryFinish.bytes.toNat ≤ writeRange.start.bytes.toNat)
    (h_set : mask.setRange writeRange state = .ok updated) :
    (updated.isRangeInitialized queryRange = .ok (.ok ()) ↔
      mask.isRangeInitialized queryRange = .ok (.ok ())) := by
  obtain ⟨u, h_u, h_len, h_wf⟩ := set_range_exists mask writeRange writeFinish state valid wEnd wNonempty wInBounds
  have h_eq : u = updated := Except.ok.inj (h_u.symm.trans h_set)
  subst h_eq
  rw [(isRangeInitialized_nonempty_iff u queryRange queryFinish h_wf qEnd qNonempty (by rw [h_len]; exact qInBounds)).1]
  rw [(isRangeInitialized_nonempty_iff mask queryRange queryFinish valid qEnd qNonempty qInBounds).1]
  constructor
  · intro h idx h_lo h_hi
    have h_out : ¬(writeRange.start.bytes.toNat ≤ idx.bytes.toNat ∧ idx.bytes.toNat < writeFinish.bytes.toNat) := by
      omega
    have h_get := set_range_get mask u writeRange writeFinish idx state valid wEnd wNonempty wInBounds (by omega) h_u
    rw [if_neg_eq h_out] at h_get
    exact h_get.symm.trans (h idx h_lo h_hi)
  · intro h idx h_lo h_hi
    have h_out : ¬(writeRange.start.bytes.toNat ≤ idx.bytes.toNat ∧ idx.bytes.toNat < writeFinish.bytes.toNat) := by
      omega
    have h_get := set_range_get mask u writeRange writeFinish idx state valid wEnd wNonempty wInBounds (by omega) h_u
    rw [if_neg_eq h_out] at h_get
    exact h_get.trans (h idx h_lo h_hi)

private theorem endExclusive_size_eq (range : AllocRange) (finish : Size)
    (endpoint : range.endExclusive = .ok finish) :
    finish.bytes.toNat = range.start.bytes.toNat + range.size.bytes.toNat ∧
      finish.bytes - range.start.bytes = range.size.bytes := by
  unfold AllocRange.endExclusive AllocRange.end Size.add at endpoint
  by_cases h_wrap : range.start.bytes + range.size.bytes < range.start.bytes
  · simp [h_wrap, Except.mapError] at endpoint
  · simp only [h_wrap, ↓reduceIte, Except.mapError, Except.ok.injEq] at endpoint
    subst endpoint
    have h_nw : ¬((range.start.bytes + range.size.bytes).toNat < range.start.bytes.toNat) := by
      simpa [UInt64.lt_iff_toNat_lt] using h_wrap
    have h1 := range.start.bytes.toNat_lt
    have h2 := range.size.bytes.toNat_lt
    have h_fits : range.start.bytes.toNat + range.size.bytes.toNat < 2 ^ 64 := by
      by_cases h_lt : range.start.bytes.toNat + range.size.bytes.toNat < 2 ^ 64
      · exact h_lt
      · have h_mod : (range.start.bytes + range.size.bytes).toNat =
            range.start.bytes.toNat + range.size.bytes.toNat - 2 ^ 64 := by
          rw [UInt64.toNat_add]; omega
        omega
    constructor
    · simp [Size.ofBytes, UInt64.toNat_add, Nat.mod_eq_of_lt h_fits]
    · apply UInt64.toNat_inj.mp
      have h_le : range.start.bytes ≤ (Size.ofBytes (range.start.bytes + range.size.bytes)).bytes := by
        simp [Size.ofBytes, UInt64.le_iff_toNat_le, UInt64.toNat_add, Nat.mod_eq_of_lt h_fits]
      rw [UInt64.toNat_sub_of_le _ _ h_le]
      simp [Size.ofBytes, UInt64.toNat_add, Nat.mod_eq_of_lt h_fits]

theorem prepareCopy_of_uniform (mask : InitMask) (range : AllocRange) (finish : Size) (state : Bool)
    (valid : WellFormed mask)
    (endpoint : range.endExclusive = .ok finish)
    (nonempty : range.start.bytes.toNat < finish.bytes.toNat)
    (inBounds : finish.bytes.toNat ≤ mask.len.bytes.toNat)
    (uniform : ∀ (idx : Size), range.start.bytes.toNat ≤ idx.bytes.toNat →
      idx.bytes.toNat < finish.bytes.toNat → mask.get idx = .ok state) :
    mask.prepareCopy range = .ok ⟨state, #[range.size.bytes]⟩ := by
  obtain ⟨h_fin_eq, h_sub_eq⟩ := endExclusive_size_eq range finish endpoint
  have h_sz_pos : 0 < range.size.bytes.toNat := by omega
  have h_sz_nz : range.size.bytes ≠ 0 := fun h0 => by
    have : range.size.bytes.toNat = 0 := by simp [h0]
    omega
  have h_sz_beq : (range.size.bytes == 0) = false := beq_false_of_ne h_sz_nz
  have h_not_oob : ¬(finish.bytes > mask.len.bytes) := by
    simpa [UInt64.lt_iff_toNat_lt] using Nat.not_lt.mpr inBounds
  have h_lt_u64 : range.start.bytes < finish.bytes := UInt64.lt_iff_toNat_lt.mpr nonempty
  have h_not_gt_sf : ¬(range.start.bytes > finish.bytes) :=
    UInt64.not_lt.mpr (UInt64.le_iff_toNat_le.mpr (Nat.le_of_lt nonempty))
  have h_not_le_fs : ¬(finish.bytes ≤ range.start.bytes) :=
    UInt64.not_le.mpr h_lt_u64
  have h_get_start : mask.get range.start = .ok state := uniform range.start (Nat.le_refl _) nonempty
  have h_raic : mask.rangeAsInitChunks range = .ok ⟨mask, state, range.start, finish⟩ := by
    unfold InitMask.rangeAsInitChunks
    simp [endpoint, h_not_oob, h_lt_u64, h_get_start, Bind.bind, Except.bind, Pure.pure, Except.pure]
  let chunk0 : InitChunk := if state then .Init range.start finish else .Uninit range.start finish
  have h_next0 : (⟨mask, state, range.start, finish⟩ : InitChunkIter).next? =
      .ok (some (chunk0, ⟨mask, !state, finish, finish⟩)) := by
    rw [InitChunkIter.next?_eq_R]
    unfold InitChunkIter.nextR Miri.Memory.sizeBytes
    have h_not_ge : ¬(range.start.bytes.toNat ≥ finish.bytes.toNat) := by omega
    cases mask with
    | mk blocks len =>
      dsimp only at inBounds h_not_oob h_get_start ⊢
      cases blocks with
      | Lazy s =>
        have h_s_eq : s = state := Except.ok.inj h_get_start
        subst h_s_eq
        simp [h_not_gt_sf, h_not_oob, h_not_ge, h_not_le_fs, chunk0,
          Bind.bind, Except.bind, Pure.pure, Except.pure]
      | Materialized mat =>
        dsimp only [WellFormed] at valid
        obtain ⟨found?, h_fb, h_fb_prop⟩ := findBit_spec mat range.start finish (!state) (by omega)
        have h_found_none : found? = none := by
          cases found? with
          | none => rfl
          | some f =>
            obtain ⟨h_lo, h_hi, h_f_get, _⟩ := h_fb_prop
            have h_u := uniform f h_lo h_hi
            rw [InitMask.get_eq_getR] at h_u
            unfold InitMask.getR at h_u
            dsimp only at h_u
            rw [h_f_get] at h_u
            cases state <;> cases h_u
        subst h_found_none
        simp [h_not_gt_sf, h_not_oob, h_not_ge, h_fb, h_not_le_fs, chunk0,
          Bind.bind, Except.bind, Pure.pure, Except.pure]
  have h_next1 : (⟨mask, !state, finish, finish⟩ : InitChunkIter).next? = .ok none := by
    rw [InitChunkIter.next?_eq_R]
    unfold InitChunkIter.nextR Miri.Memory.sizeBytes
    have h_not_ff : ¬(finish.bytes > finish.bytes) := UInt64.lt_irrefl _
    simp [h_not_ff, h_not_oob, Pure.pure, Except.pure]
  have h_collect : InitMask.collectChunks ⟨mask, state, range.start, finish⟩ = .ok #[chunk0] :=
    collectChunks_single _ _ _ nonempty h_next0 h_next1
  have h_chunk_isInit : chunk0.isInit = state := by
    dsimp only [chunk0]; cases state <;> rfl
  have h_chunk_range : chunk0.range = .ok ⟨range.start, range.size⟩ := by
    dsimp only [chunk0]
    have h_le : range.start.bytes ≤ finish.bytes := UInt64.le_of_lt h_lt_u64
    have h_not_lt : ¬(finish.bytes < range.start.bytes) := UInt64.not_lt.mpr h_le
    cases state <;> {
      unfold InitChunk.range AllocRange.fromEndpoints Size.sub
      simp [h_not_lt, h_sub_eq, Size.ofBytes, Bind.bind, Except.bind, Except.mapError, Pure.pure, Except.pure]
    }
  unfold InitMask.prepareCopy
  simp only [h_sz_beq, Bool.false_eq_true, ↓reduceIte, h_raic, Bind.bind, Except.bind, h_collect]
  rw [← Array.forIn_toList]
  simp [List.forIn_cons, List.forIn_nil, h_chunk_range, h_chunk_isInit,
    Bind.bind, Except.bind, Pure.pure, Except.pure]

theorem applyCopy_singleton (destMask : InitMask) (destStart srcSize total : Size)
    (repeatCount : UInt64) (state : Bool)
    (nonzero : srcSize.bytes ≠ 0)
    (h_mul : Size.mul srcSize repeatCount = .ok total) :
    destMask.applyCopy ⟨state, #[srcSize.bytes]⟩ (allocRange destStart srcSize) repeatCount =
      destMask.setRange (allocRange destStart total) state := by
  unfold InitMask.applyCopy
  simp [nonzero, allocRange, h_mul, Except.mapError, Bind.bind, Except.bind]

end Miri.Memory.InitMask.WriteProof

/-! ## Part 2. `ProvenanceMap` -/

/-! ### 2a. Private mirrors of private `ProvenanceMap` helpers and `rfl` bridges -/

namespace Miri.Memory.ProvenanceMap
open Miri.ABI

private def rangeEntries {α : Type} (values : Array (Size × α)) (start finish : Size) :
    Array (Size × α) :=
  values.filter fun entry => start.bytes ≤ entry.1.bytes && entry.1.bytes < finish.bytes

private def adjustedStart (range : AllocRange) (pointerSize : Size) : Except ProvenanceMapError Size :=
  if pointerSize.bytes == 0 then .error .pointerSizeZero
  else .ok (Size.ofBytes (UInt64.ofNat (range.start.bytes.toNat - (pointerSize.bytes.toNat - 1))))

private def rangeEnd (range : AllocRange) : Except ProvenanceMapError Size :=
  range.endExclusive.mapError .memory

private def subtractSize (left right : Size) : Except ProvenanceMapError Size :=
  (Size.sub left right).mapError (ProvenanceMapError.memory ∘ MemoryError.sizeError)

private def ptrFragments {Prov : Type} (inRange : Size → Bool) (position : Size) (prov : Prov)
    (data : Array UInt8) (pointerSize : Size) :
    Except ProvenanceMapError (Array (Size × PointerFrag Prov)) := do
  if pointerSize.bytes > 8 then throw (.pointerSizeExceedsFragmentStorage pointerSize.bytes)
  let finish ← (Size.add position pointerSize).mapError (ProvenanceMapError.memory ∘ MemoryError.sizeError)
  if h : position.bytes.toNat + pointerSize.bytes.toNat ≤ data.size then
    let bytes : Vector UInt8 8 := Vector.ofFn fun index =>
      if hi : index.val < pointerSize.bytes.toNat then
        data[position.bytes.toNat + index.val]'(by omega)
      else 0
    let mut fragments := #[]
    for index in [:pointerSize.bytes.toNat] do
      let pos := Size.ofBytes (position.bytes + UInt64.ofNat index)
      if inRange pos then
        fragments := fragments.push (pos, ⟨UInt8.ofNat index, prov, bytes⟩)
    return fragments
  else throw (.fragmentSliceOutOfBounds position pointerSize data.size)

private def rangePtrsR {Prov : Type} (self : ProvenanceMap Prov) (range : AllocRange)
    (pointerSize : Size) : Except ProvenanceMapError (Array (Size × Prov)) := do
  let start ← adjustedStart range pointerSize
  let finish ← rangeEnd range
  return rangeEntries self.ptrs start finish

private def rangeBytesR {Prov : Type} (self : ProvenanceMap Prov) (range : AllocRange) :
    Except ProvenanceMapError (Array (Size × PointerFrag Prov)) := do
  let finish ← rangeEnd range
  return rangeEntries (self.byteFragments.getD #[]) range.start finish

private def prepareCopyR {Prov : Type} (self : ProvenanceMap Prov) (range : AllocRange)
    (data : Array UInt8) (pointerSize : Size) : Except ProvenanceMapError (ProvenanceCopy Prov) := do
  if pointerSize.bytes == 0 then throw .pointerSizeZero
  let finish ← rangeEnd range
  let mut ptrs := #[]
  if range.size.bytes ≥ pointerSize.bytes then
    let adjustedEnd ← subtractSize finish (Size.ofBytes (pointerSize.bytes - 1))
    for (offset, prov) in rangeEntries self.ptrs range.start adjustedEnd do
      ptrs := ptrs.push (← subtractSize offset range.start, prov)
  let beginOverlap := (← self.rangePtrs (allocRange range.start Size.ZERO) pointerSize)[0]?
  let endOverlap := (← self.rangePtrs (allocRange finish Size.ZERO) pointerSize)[0]?
  let mut bytes := #[]
  if beginOverlap.isSome || endOverlap.isSome || self.byteFragments.isSome then
    if let some (position, prov) := beginOverlap then
      let ptrEnd ← (Size.add position pointerSize).mapError (ProvenanceMapError.memory ∘ MemoryError.sizeError)
      let fragmentEnd := if ptrEnd.bytes < finish.bytes then ptrEnd else finish
      if range.start.bytes < fragmentEnd.bytes then
        let fragments ← ptrFragments (fun pos => range.start.bytes ≤ pos.bytes && pos.bytes < fragmentEnd.bytes) position prov data pointerSize
        for (pos, frag) in fragments do
          bytes := bytes.push (← subtractSize pos range.start, frag)
    for (offset, frag) in (← self.rangeBytes range) do
      bytes := bytes.push (← subtractSize offset range.start, frag)
    if let some (position, prov) := endOverlap then
      if (beginOverlap.map fun (begin, _) => begin.bytes != position.bytes).getD true then
        if position.bytes < range.start.bytes then throw .unsortedOrDuplicateKeys
        if position.bytes < finish.bytes then
          let fragments ← ptrFragments (fun pos => position.bytes ≤ pos.bytes && pos.bytes < finish.bytes) position prov data pointerSize
          for (pos, frag) in fragments do
            let shifted ← subtractSize pos range.start
            if !((bytes.back?.map fun last => decide (last.1.bytes < shifted.bytes)).getD true) then
              throw .unsortedOrDuplicateKeys
            bytes := bytes.push (shifted, frag)
  return ⟨ptrs, bytes⟩

private theorem rangePtrs_eq_R {Prov : Type} : @rangePtrs Prov = @rangePtrsR Prov := rfl
private theorem rangeBytes_eq_R {Prov : Type} : @rangeBytes Prov = @rangeBytesR Prov := rfl
private theorem prepareCopy_eq_R {Prov : Type} : @prepareCopy Prov = @prepareCopyR Prov := rfl

end Miri.Memory.ProvenanceMap

/-! ### 2b. The four `ProvenanceMap` specification theorems -/

namespace Miri.Memory.ProvenanceMap
open Miri.ABI
variable {P : Type}

private theorem empty_range (range : AllocRange) (pointerSize finish : Size)
    (positive : pointerSize.bytes ≠ 0) (endEq : range.endExclusive = .ok finish) :
    (new (Prov := P)).rangeEmpty range pointerSize = .ok true := by
  unfold rangeEmpty
  rw [rangePtrs_eq_R, rangeBytes_eq_R]
  unfold rangePtrsR rangeBytesR adjustedStart rangeEnd rangeEntries
  simp [new, positive, endEq, bind, Bind.bind, Except.bind, pure, Pure.pure, Except.pure, Except.mapError]

theorem rangeEmpty_new (range : AllocRange) (pointerSize finish : Size)
    (positive : pointerSize.bytes ≠ 0) (endEq : range.endExclusive = .ok finish) :
    (new (Prov := P)).rangeEmpty range pointerSize = .ok true :=
  empty_range range pointerSize finish positive endEq

theorem readPtr_new [DecidableEq P] [PointerProvenance P]
    (offset pointerSize finish : Size)
    (positive : pointerSize.bytes ≠ 0)
    (endEq : (allocRange offset pointerSize).endExclusive = .ok finish) :
    (new (Prov := P)).readPtr offset pointerSize = .ok none := by
  unfold readPtr getPtr
  rw [rangePtrs_eq_R, rangeBytes_eq_R]
  unfold rangePtrsR rangeBytesR adjustedStart rangeEnd rangeEntries new
  simp [positive, endEq, bind, Bind.bind, Except.bind, pure, Pure.pure, Except.pure, Except.mapError]

theorem prepareCopy_new (range : AllocRange) (data : Array UInt8) (pointerSize finish : Size)
    (positive : pointerSize.bytes ≠ 0)
    (endEq : range.endExclusive = .ok finish) :
    (new (Prov := P)).prepareCopy range data pointerSize = .ok ⟨#[], #[]⟩ := by
  have h_start0 : (allocRange range.start Size.ZERO).endExclusive = .ok range.start := by
    cases range.start
    simp [allocRange, AllocRange.endExclusive, AllocRange.end, Size.ZERO, Size.ofBytes, Size.add, Except.mapError]
  have h_fin0 : (allocRange finish Size.ZERO).endExclusive = .ok finish := by
    cases finish
    simp [allocRange, AllocRange.endExclusive, AllocRange.end, Size.ZERO, Size.ofBytes, Size.add, Except.mapError]
  have h_rp_start : (new (Prov := P)).rangePtrs (allocRange range.start Size.ZERO) pointerSize = .ok #[] := by
    rw [rangePtrs_eq_R]
    unfold rangePtrsR adjustedStart rangeEnd rangeEntries new
    simp [positive, h_start0, bind, Bind.bind, Except.bind, pure, Pure.pure, Except.pure, Except.mapError]
  have h_rp_fin : (new (Prov := P)).rangePtrs (allocRange finish Size.ZERO) pointerSize = .ok #[] := by
    rw [rangePtrs_eq_R]
    unfold rangePtrsR adjustedStart rangeEnd rangeEntries new
    simp [positive, h_fin0, bind, Bind.bind, Except.bind, pure, Pure.pure, Except.pure, Except.mapError]
  rw [prepareCopy_eq_R]
  unfold prepareCopyR
  simp only [positive, beq_iff_eq, ↓reduceIte, rangeEnd, endEq, Except.mapError,
    h_rp_start, h_rp_fin, Bind.bind, Except.bind, Pure.pure, Except.pure]
  by_cases h_ge : pointerSize.bytes ≤ range.size.bytes
  · have h_le_fin : pointerSize.bytes - 1 ≤ finish.bytes := by
      have h_end_def : Size.add range.start range.size = .ok finish := by
        unfold AllocRange.endExclusive AllocRange.end at endEq
        cases h_add : Size.add range.start range.size with
        | error e => simp [h_add, Except.mapError] at endEq
        | ok f => simpa [h_add, Except.mapError] using endEq
      unfold Size.add at h_end_def
      by_cases h_wrap : range.start.bytes + range.size.bytes < range.start.bytes
      · simp [h_wrap] at h_end_def
      · simp only [h_wrap, ↓reduceIte, Except.ok.injEq] at h_end_def
        subst h_end_def
        have h_ge_nat : pointerSize.bytes.toNat ≤ range.size.bytes.toNat := UInt64.le_iff_toNat_le.mp h_ge
        have h_nw : ¬((range.start.bytes + range.size.bytes).toNat < range.start.bytes.toNat) := by
          simpa [UInt64.lt_iff_toNat_lt] using h_wrap
        have h1 := range.start.bytes.toNat_lt
        have h2 := range.size.bytes.toNat_lt
        have h_fits : range.start.bytes.toNat + range.size.bytes.toNat < 2 ^ 64 := by
          by_cases h_lt : range.start.bytes.toNat + range.size.bytes.toNat < 2 ^ 64
          · exact h_lt
          · have h_mod : (range.start.bytes + range.size.bytes).toNat =
                range.start.bytes.toNat + range.size.bytes.toNat - 2 ^ 64 := by
              rw [UInt64.toNat_add]
              omega
            omega
        have h_p1 : pointerSize.bytes.toNat ≠ 0 := fun h0 => positive (UInt64.toNat_inj.mp h0)
        have h_sub : (pointerSize.bytes - 1).toNat = pointerSize.bytes.toNat - 1 := by
          have h_u1 : (1 : UInt64).toNat = 1 := rfl
          rw [UInt64.toNat_sub_of_le]
          · exact congrArg (pointerSize.bytes.toNat - ·) h_u1
          · exact UInt64.le_iff_toNat_le.mpr (by rw [h_u1]; omega)
        simp only [Size.ofBytes, UInt64.le_iff_toNat_le, UInt64.toNat_add, Nat.mod_eq_of_lt h_fits]
        omega
    have h_not_lt : ¬(finish.bytes < pointerSize.bytes - 1) := UInt64.not_lt.mpr h_le_fin
    have h_sub_ok : subtractSize finish (Size.ofBytes (pointerSize.bytes - 1)) =
        .ok (Size.ofBytes (finish.bytes - (pointerSize.bytes - 1))) := by
      unfold subtractSize Size.sub Size.ofBytes
      simp [h_not_lt, Except.mapError]
    simp only [ge_iff_le, h_ge, ↓reduceIte, h_sub_ok]
    have h_re : rangeEntries (new (Prov := P)).ptrs range.start
        (Size.ofBytes (finish.bytes - (pointerSize.bytes - 1))) = #[] := rfl
    rw [h_re]
    rfl
  · simp only [ge_iff_le, h_ge, ↓reduceIte]
    rfl

theorem applyCopy_empty (range : AllocRange) (repeatCount : UInt64) (pm : ProvenanceMap P) :
    applyCopy ⟨#[], #[]⟩ range repeatCount pm = .ok () pm := by
  unfold applyCopy
  simp [pure, Pure.pure, EStateM.pure]

end Miri.Memory.ProvenanceMap

/-! ## Part 3. `Allocation` -/

/-! ### 3a. Private mirrors of private `Allocation` helpers

`Allocation.mk` and the `rawBytes`/`size`/`provenance`/`initMask` fields are `private` in
`lean-miri`. `mkAlloc` builds the private constructor with the standard `constructor`
tactic, and `Allocation.raw` reads the byte storage through the public `casesOn`
eliminator; neither introduces axioms, and every mirror below is checked to be
definitionally equal to the corresponding `lean-miri` operation by `rfl`. -/

namespace Miri.Memory
open Miri.ABI

private def maxU64Nat : Nat := 18446744073709551615

private def checkedAlign (align : Align) : Except AllocError Align := do
  let bytes ← (Align.bytes align).mapError AllocError.alignment
  let normalized ← (Align.fromBytes bytes).mapError AllocError.alignment
  if normalized == align then return align
  throw (.alignment (.tooLarge bytes))

private def sizeForArray (length : Nat) : Except AllocError Size := do
  if length > maxU64Nat then throw (.storageLengthOverflow length)
  let size := Size.ofBytes (UInt64.ofNat length)
  if size.bytes.toNat == length then return size
  throw (.storageLengthOverflow length)

private def pointerSize (layout : TargetDataLayout) : Size :=
  Size.fromBits layout.pointerWidth.bits

private def targetUIntBytes (layout : TargetDataLayout) (size : Size) (bits : U128) :
    Except AllocError (Array UInt8) := do
  if size.bytes > 16 then throw (.scalarBytesTooWide size)
  let count := size.bytes.toNat
  let mut result := #[]
  for index in [:count] do
    let valueIndex := if layout.endian == .little then index else count - index - 1
    let byte := (bits.toNat / 2 ^ (8 * valueIndex)) % 256
    result := result.push (UInt8.ofNat byte)
  return result

private def readTargetUInt (layout : TargetDataLayout) (bytes : Array UInt8) :
    Except AllocError U128 := do
  if bytes.size > 16 then throw (.scalarBytesTooWide (Size.ofBytes (UInt64.ofNat bytes.size)))
  let mut value := 0
  for index in [:bytes.size] do
    let some byte := bytes[index]? | throw (.invalidSliceEndpoints index (index + 1) bytes.size)
    let valueIndex := if layout.endian == .little then index else bytes.size - index - 1
    value := value + byte.toNat * 2 ^ (8 * valueIndex)
  return BitVec.ofNat 128 value

private def firstNonZero (bytes : Array UInt8) : Option (Nat × UInt8) := Id.run do
  for index in [:bytes.size] do
    match bytes[index]? with
    | some byte => if byte != 0 then return some (index, byte)
    | none => return some (index, 0)
  return none

namespace Allocation

variable {Prov Extra : Type}

/-- The private `Allocation.mk`, built with the standard `constructor` tactic. -/
private def mkAlloc (rawBytes : Array UInt8) (size : Size) (provenance : ProvenanceMap Prov)
    (initMask : InitMask) (align : Align) (mutability : Mutability) (extra : Extra)
    (nativeBuffer : Option NativeBufferOwnership) : Allocation Prov Extra := by
  constructor
  · exact rawBytes
  · exact size
  · exact provenance
  · exact initMask
  · exact align
  · exact mutability
  · exact extra
  · exact nativeBuffer

/-- The private `rawBytes` field, read through the public `casesOn` eliminator. -/
private def raw (allocation : Allocation Prov Extra) : Array UInt8 :=
  Allocation.casesOn (motive := fun _ => Array UInt8) allocation
    (fun rawBytes _ _ _ _ _ _ _ => rawBytes)

private def checkedSlice (allocation : Allocation Prov Extra) (range : AllocRange) :
    Except AllocError (Array UInt8) := do
  if (raw allocation).size != allocation.byteSize.bytes.toNat then
    throw (.storageLengthMismatch allocation.byteSize (raw allocation).size)
  let finish ← range.endExclusive |>.mapError AllocError.memory
  if range.start.bytes > finish.bytes || finish.bytes > allocation.byteSize.bytes then
    throw (.outOfBounds range allocation.byteSize)
  return (raw allocation).extract range.start.bytes.toNat finish.bytes.toNat

/-- `{ state with provenance }`. -/
private def withProvenance (state : Allocation Prov Extra) (provenance : ProvenanceMap Prov) :
    Allocation Prov Extra :=
  mkAlloc (raw state) state.byteSize provenance state.initializationMask state.align
    state.mutability state.extra state.nativeBuffer

/-- `{ state with initMask }`. -/
private def withInitMask (state : Allocation Prov Extra) (initMask : InitMask) :
    Allocation Prov Extra :=
  mkAlloc (raw state) state.byteSize state.provenanceMap initMask state.align
    state.mutability state.extra state.nativeBuffer

/-- `{ state with rawBytes }`. -/
private def withRawBytes (state : Allocation Prov Extra) (rawBytes : Array UInt8) :
    Allocation Prov Extra :=
  mkAlloc rawBytes state.byteSize state.provenanceMap state.initializationMask state.align
    state.mutability state.extra state.nativeBuffer

private def runProvenanceMutation {α : Type}
    (mutation : EStateM.Result ProvenanceMapError (ProvenanceMap Prov) α)
    (state : Allocation Prov Extra) :
    EStateM.Result AllocError (Allocation Prov Extra) α :=
  match mutation with
  | .ok value provenance => .ok value (withProvenance state provenance)
  | .error reason provenance => .error (.provenance reason) (withProvenance state provenance)

private def setInitialization (state : Allocation Prov Extra) (range : AllocRange)
    (initialized : Bool) : Except AllocError (Allocation Prov Extra) := do
  let initMask ← state.initializationMask.setRange range initialized |>.mapError AllocError.memory
  return withInitMask state initMask

private def overwriteRawBytes (state : Allocation Prov Extra) (range : AllocRange)
    (bytes : Array UInt8) : Except AllocError (Allocation Prov Extra) := do
  let finish ← range.endExclusive |>.mapError AllocError.memory
  let start := range.start.bytes.toNat
  let endIndex := finish.bytes.toNat
  let updated := (raw state).extract 0 start ++ bytes ++
    (raw state).extract endIndex (raw state).size
  if updated.size != state.byteSize.bytes.toNat then
    throw (.storageLengthMismatch state.byteSize updated.size)
  return withRawBytes state updated

private def prepareForOverwrite (range : AllocRange) (pointerSize : Size)
    (state : Allocation Prov Extra) :
    EStateM.Result AllocError (Allocation Prov Extra) Unit := Id.run do
  match checkedSlice state range with
  | .error reason => return .error reason state
  | .ok _ => pure ()
  if range.size.bytes == 0 then return .ok () state
  if state.mutability != .Mut then return .error .readOnlyAllocation state
  let initialized ← if range.size.bytes == 0 then pure state else
    match setInitialization state range true with
    | .ok initialized => pure initialized
    | .error reason => return .error reason state
  return runProvenanceMutation
    (initialized.provenanceMap.clear range (raw initialized) pointerSize) initialized

/-! ### 3b. Mirrors of public `Allocation` operations and `rfl` bridges -/

private def fromBytesR (bytes : Array UInt8) (align : Align) (mutability : Mutability) :
    Except AllocError (Allocation Prov Unit) := do
  let align ← checkedAlign align
  let size ← sizeForArray bytes.size
  if _h : bytes.size = size.bytes.toNat then
    return mkAlloc bytes size ProvenanceMap.new (InitMask.new size true) align mutability () none
  else
    throw (.storageLengthOverflow bytes.size)

private def tryNewR (size : Size) (align : Align) (init : AllocInit)
    (zeroedStorage : Size → Align → Option (Array UInt8)) :
    Except AllocError (Allocation Prov Unit) := do
  let align ← checkedAlign align
  let bytes ← match zeroedStorage size align with
    | some bytes => pure bytes
    | none => throw .hostMemoryExhausted
  if bytes.size != size.bytes.toNat then
    throw (.storageLengthMismatch size bytes.size)
  if let some (index, value) := firstNonZero bytes then
    throw (.storageBackendNotZeroed index value)
  let initialized := match init with
    | .Uninit => false
    | .Zero => true
  if _h : bytes.size = size.bytes.toNat then
    return mkAlloc bytes size ProvenanceMap.new (InitMask.new size initialized) align .Mut () none
  else
    throw (.storageLengthMismatch size bytes.size)

private def getBytesStripProvenanceR [PointerProvenance Prov]
    (allocation : Allocation Prov Extra) (layout : TargetDataLayout)
    (range : AllocRange) : Except AllocError (Array UInt8) := do
  match ← (allocation.initializationMask.isRangeInitialized range).mapError AllocError.memory with
  | .error bad => throw (.invalidUninitBytes (some ⟨range, bad⟩))
  | .ok () => pure ()
  if !PointerProvenance.offsetIsAddr (Prov := Prov) then
    let ptrBytes := pointerSize layout
    let isEmpty ← (allocation.provenanceMap.rangeEmpty range ptrBytes).mapError AllocError.provenance
    if !isEmpty then
      let entries ← (allocation.provenanceMap.getRange range ptrBytes).mapError AllocError.provenance
      let some (provRange, _) := entries[0]?
        | throw .nonEmptyProvenanceWithoutEntry
      let provFinish ← provRange.endExclusive |>.mapError AllocError.memory
      let rangeFinish ← range.endExclusive |>.mapError AllocError.memory
      let badStart := if provRange.start.bytes > range.start.bytes
        then provRange.start else range.start
      let badFinish := if provFinish.bytes < rangeFinish.bytes
        then provFinish else rangeFinish
      let bad ← (AllocRange.fromEndpoints badStart badFinish).mapError AllocError.memory
      throw (.readPointerAsInt (some ⟨range, bad⟩))
  checkedSlice allocation range

private def readScalarR [DecidableEq Prov] [PointerProvenance Prov]
    (allocation : Allocation Prov Extra) (layout : TargetDataLayout)
    (range : AllocRange) (readProvenance : Bool) :
    Except AllocError (Scalar Prov) := do
  match ← (allocation.initializationMask.isRangeInitialized range).mapError AllocError.memory with
  | .error bad => throw (.invalidUninitBytes (some ⟨range, bad⟩))
  | .ok () => pure ()
  let bytes ← checkedSlice allocation range
  let bits ← readTargetUInt layout bytes
  if readProvenance then
    let targetSize := pointerSize layout
    if range.size != targetSize then
      throw (.scalarPointerNotTargetSized range.size targetSize)
    let provenance ← match allocation.provenanceMap.readPtr range.start targetSize with
      | .ok provenance => pure provenance
      | .error (.readPartialPointer offset) => throw (.readPartialPointer offset)
      | .error reason => throw (.provenance reason)
    match provenance with
    | some provenance =>
      if bits.toNat > 18446744073709551615 then
        throw (.pointerBitsDoNotFitOffset bits)
      return Scalar.fromPointer layout
        (Pointer.new provenance (Size.ofBytes (UInt64.ofNat bits.toNat)))
    | none =>
      let scalar ← (Scalar.fromUInt bits range.size).mapError AllocError.scalar
      return scalar
  else
    if PointerProvenance.offsetIsAddr (Prov := Prov) then
      let scalar ← (Scalar.fromUInt bits range.size).mapError AllocError.scalar
      return scalar
    let isEmpty ← (allocation.provenanceMap.rangeEmpty range (pointerSize layout)).mapError AllocError.provenance
    if isEmpty then
      let scalar ← (Scalar.fromUInt bits range.size).mapError AllocError.scalar
      return scalar
    throw (.readPointerAsInt none)

private def writeScalarR (layout : TargetDataLayout) (range : AllocRange)
    (value : Scalar Prov) : EStateM AllocError (Allocation Prov Extra) Unit := fun state => Id.run do
  if state.mutability != .Mut then return .error .readOnlyAllocation state
  let bitsAndPointer ← match value.toBitsOrPtrInternal range.size with
    | .ok converted => pure converted
    | .error reason => return .error (.scalar reason) state
  match checkedSlice state range with
  | .error error => return .error error state
  | .ok _ => pure ()
  let nextMask ← match state.initializationMask.setRange range true with
    | .ok mask => pure mask
    | .error error => return .error (.memory error) state
  let beforeClear := withInitMask state nextMask
  match state.provenanceMap.clear range (raw state) (pointerSize layout) with
  | .error reason mapAfter =>
    return .error (.provenance reason) (withProvenance beforeClear mapAfter)
  | .ok () clearedMap =>
    let finish := range.start.bytes.toNat + range.size.bytes.toNat
    let start := range.start.bytes.toNat
    let (bits, provenance) := match bitsAndPointer with
      | .bits bits => (bits, none)
      | .pointer pointer => (BitVec.ofNat 128 pointer.offset.bytes.toNat, some pointer.provenance)
    let data ← match targetUIntBytes layout range.size bits with
      | .ok data => pure data
      | .error error => return .error error (withProvenance beforeClear clearedMap)
    let bytes := (raw state).extract 0 start ++ data ++
      (raw state).extract finish (raw state).size
    if bytes.size != state.byteSize.bytes.toNat then
      return .error (.storageLengthMismatch state.byteSize bytes.size)
        (withProvenance beforeClear clearedMap)
    let afterWrite := withProvenance (withRawBytes beforeClear bytes) clearedMap
    match provenance with
    | none => return .ok () afterWrite
    | some provenance =>
      if range.size != pointerSize layout then
        return .error (.scalarPointerNotTargetSized range.size (pointerSize layout)) afterWrite
      match clearedMap.insertPtr range.start provenance (pointerSize layout) with
      | .error reason mapAfter =>
        return .error (.provenance reason) (withProvenance afterWrite mapAfter)
      | .ok () insertedMap =>
        return .ok () (withProvenance afterWrite insertedMap)

private def writeBytesR (start : Size) (bytes : Array UInt8) (pointerSize : Size) :
    EStateM AllocError (Allocation Prov Extra) Unit := fun state => Id.run do
  let writeSize ← match sizeForArray bytes.size with
    | .ok size => pure size
    | .error reason => return .error reason state
  let range := allocRange start writeSize
  match checkedSlice state range with
  | .error reason => return .error reason state
  | .ok _ => pure ()
  if writeSize.bytes == 0 then return .ok () state
  if state.mutability != .Mut then return .error .readOnlyAllocation state
  let initialized ← match setInitialization state range true with
    | .ok initialized => pure initialized
    | .error reason => return .error reason state
  let clearedResult := initialized.provenanceMap.clear range (raw initialized) pointerSize
  let cleared ← match clearedResult with
    | .ok () provenance => pure (withProvenance initialized provenance)
    | .error reason provenance =>
        return .error (.provenance reason) (withProvenance initialized provenance)
  match overwriteRawBytes cleared range bytes with
  | .ok updated => return .ok () updated
  | .error reason => return .error reason cleared

private def writeUninitR (range : AllocRange) (pointerSize : Size) :
    EStateM AllocError (Allocation Prov Extra) Unit := fun state => Id.run do
  match checkedSlice state range with
  | .error reason => return .error reason state
  | .ok _ => pure ()
  if range.size.bytes == 0 then return .ok () state
  if state.mutability != .Mut then return .error .readOnlyAllocation state
  let uninitialized ← match setInitialization state range false with
    | .ok uninitialized => pure uninitialized
    | .error reason => return .error reason state
  let cleared := uninitialized.provenanceMap.clear range (raw uninitialized) pointerSize
  match cleared with
  | .ok () provenance => return .ok () (withProvenance uninitialized provenance)
  | .error reason provenance =>
      return .error (.provenance reason) (withProvenance uninitialized provenance)

private def clearProvenanceR (range : AllocRange) (pointerSize : Size) :
    EStateM AllocError (Allocation Prov Extra) Unit := fun state => Id.run do
  match checkedSlice state range with
  | .error reason => return .error reason state
  | .ok _ => pure ()
  let cleared := state.provenanceMap.clear range (raw state) pointerSize
  match cleared with
  | .ok () provenance => return .ok () (withProvenance state provenance)
  | .error reason provenance => return .error (.provenance reason) (withProvenance state provenance)

private def copyRepeatedlyR
    (source : Allocation Prov Extra) (sourceRange : AllocRange) (destStart : Size)
    (repeatCount : UInt64) (pointerSize : Size) (sameAllocation nonoverlapping : Bool) :
    EStateM AllocError (Allocation Prov Extra) Unit := fun state => Id.run do
  let sourceBytes ← match checkedSlice source sourceRange with
    | .error reason => return .error reason state
    | .ok sourceBytes => pure sourceBytes
  let totalSize ← match Size.mul sourceRange.size repeatCount with
    | .ok size => pure size
    | .error reason => return .error (.memory (.sizeError reason)) state
  let destRange := allocRange destStart totalSize
  match checkedSlice state destRange with
  | .error reason => return .error reason state
  | .ok _ => pure ()
  let provenance ← match source.provenanceMap.prepareCopy sourceRange (raw source) pointerSize with
    | .ok copy => pure copy
    | .error reason => return .error (.provenance reason) state
  let initialized ← match source.initializationMask.prepareCopy sourceRange with
    | .ok copy => pure copy
    | .error reason => return .error (.memory reason) state
  let prepared := prepareForOverwrite destRange pointerSize state
  let afterClear ← match prepared with
    | .ok () updated => pure updated
    | .error reason updated => return .error reason updated
  if initialized.noBytesInit then
    let uninitResult := Allocation.writeUninit destRange pointerSize afterClear
    match uninitResult with
    | .error reason updated => return .error reason updated
    | .ok () updated => return .ok () updated
  if sameAllocation && nonoverlapping then
    let sourceFinish ← match sourceRange.endExclusive with
      | .ok finish => pure finish
      | .error reason => return .error (.memory reason) afterClear
    let firstDestFinish ← match (allocRange destStart sourceRange.size).endExclusive with
      | .ok finish => pure finish
      | .error reason => return .error (.memory reason) afterClear
    if sourceRange.start.bytes < firstDestFinish.bytes && destStart.bytes < sourceFinish.bytes then
      return .error .copyRangesOverlap afterClear
  if repeatCount > 1 && !nonoverlapping then
    return .error .repeatedCopyRequiresNonoverlapping afterClear
  if sourceRange.size.bytes == 1 && repeatCount == 0 && !initialized.noBytesInit then
    return .error .singleByteZeroCountCopy afterClear
  let mut copiedBytes := #[]
  for _ in [:repeatCount.toNat] do
    copiedBytes := copiedBytes ++ sourceBytes
  let afterBytes ← match overwriteRawBytes afterClear destRange copiedBytes with
    | .ok updated => pure updated
    | .error reason => return .error reason afterClear
  let afterInit ← match afterBytes.initializationMask.applyCopy initialized
      (allocRange destStart sourceRange.size) repeatCount with
    | .ok initMask => pure (withInitMask afterBytes initMask)
    | .error reason => return .error (.memory reason) afterBytes
  match afterInit.provenanceMap.applyCopy provenance
      (allocRange destStart sourceRange.size) repeatCount with
  | .ok () provenance => return .ok () (withProvenance afterInit provenance)
  | .error reason provenance =>
      return .error (.provenance reason) (withProvenance afterInit provenance)

private theorem getBytesUnchecked_eq :
    @Allocation.getBytesUnchecked Prov Extra = @checkedSlice Prov Extra := rfl
private theorem fromBytes_eq_R : @Allocation.fromBytes Prov = @fromBytesR Prov := rfl
private theorem tryNew_eq_R : @Allocation.tryNew Prov = @tryNewR Prov := rfl
private theorem getBytesStripProvenance_eq_R :
    @Allocation.getBytesStripProvenance Prov Extra = @getBytesStripProvenanceR Prov Extra := rfl
private theorem readScalar_eq_R : @Allocation.readScalar Prov Extra = @readScalarR Prov Extra := rfl
private theorem writeScalar_eq_R : @Allocation.writeScalar Prov Extra = @writeScalarR Prov Extra := rfl
private theorem writeBytes_eq_R : @Allocation.writeBytes Prov Extra = @writeBytesR Prov Extra := rfl
private theorem writeUninit_eq_R : @Allocation.writeUninit Prov Extra = @writeUninitR Prov Extra := rfl
private theorem clearProvenance_eq_R :
    @Allocation.clearProvenance Prov Extra = @clearProvenanceR Prov Extra := rfl
private theorem copyRepeatedly_eq_R :
    @Allocation.copyRepeatedly Prov Extra = @copyRepeatedlyR Prov Extra := rfl

end Allocation

end Miri.Memory

namespace Miri.Memory.Allocation
open Miri.ABI
variable {P E E' : Type}

/-! ### 3c. Accessor lemmas for the mirrors and ported private `lean-miri` lemmas -/

private theorem raw_withInitMask (a : Allocation P E) (m : InitMask) : raw (withInitMask a m) = raw a := rfl
private theorem byteSize_withInitMask (a : Allocation P E) (m : InitMask) : (withInitMask a m).byteSize = a.byteSize := rfl
private theorem provenanceMap_withInitMask (a : Allocation P E) (m : InitMask) : (withInitMask a m).provenanceMap = a.provenanceMap := rfl
private theorem initializationMask_withInitMask (a : Allocation P E) (m : InitMask) : (withInitMask a m).initializationMask = m := rfl
private theorem raw_withProvenance (a : Allocation P E) (p : ProvenanceMap P) : raw (withProvenance a p) = raw a := rfl
private theorem byteSize_withProvenance (a : Allocation P E) (p : ProvenanceMap P) : (withProvenance a p).byteSize = a.byteSize := rfl
private theorem provenanceMap_withProvenance (a : Allocation P E) (p : ProvenanceMap P) : (withProvenance a p).provenanceMap = p := rfl
private theorem initializationMask_withProvenance (a : Allocation P E) (p : ProvenanceMap P) : (withProvenance a p).initializationMask = a.initializationMask := rfl
private theorem provenanceMap_withRawBytes (a : Allocation P E) (r : Array UInt8) : (withRawBytes a r).provenanceMap = a.provenanceMap := rfl
private theorem initializationMask_withRawBytes (a : Allocation P E) (r : Array UInt8) : (withRawBytes a r).initializationMask = a.initializationMask := rfl
private theorem raw_mapExtra (a : Allocation P E) (f : E → E') : raw (a.mapExtra f) = raw a := rfl

private theorem write_add_size (left right : Size)
    (fits : left.bytes.toNat + right.bytes.toNat < 2 ^ 64) :
    Size.add left right = .ok (Size.ofBytes (left.bytes + right.bytes)) := by
  have noWrap : ¬left.bytes + right.bytes < left.bytes := by
    simp only [UInt64.lt_iff_toNat_lt, UInt64.toNat_add, Nat.mod_eq_of_lt fits]
    omega
  simp [Size.add, noWrap]

private theorem firstNonZero_replicate (n : Nat) : firstNonZero (Array.replicate n 0) = none := by
  let step : Nat → Option (Option (Nat × UInt8)) × Unit → Id (ForInStep (Option (Option (Nat × UInt8)) × Unit)) :=
    fun index _ => match (Array.replicate n 0)[index]? with
      | some byte => if byte != 0 then pure (.done (some (some (index, byte)), ())) else pure (.yield (none, ()))
      | none => pure (.done (some (some (index, 0)), ()))
  have scan : ∀ indices : List Nat, (∀ index ∈ indices, index < n) →
      forIn indices (none, ()) step = (none, ()) := by
    intro indices
    induction indices with
    | nil => intro good; rfl
    | cons head tail ih =>
      intro good
      have bound := good head (by simp)
      have atHead : (Array.replicate n (0 : UInt8))[head]? = some 0 := by simp [bound]
      rw [List.forIn_cons]
      simp only [step, atHead, pure, Pure.pure, bind, Bind.bind]
      exact ih (by intro index member; exact good index (by simp [member]))
  simp only [firstNonZero]
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Array.size_replicate, Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  simp only [Id.run, bind, Bind.bind, pure, Pure.pure]
  dsimp only [step, Id.run, pure, Pure.pure] at scan
  rw [scan (List.range' 0 n) (by intro index member; have := List.mem_range'.mp member; omega)]

/-! ### 3d. The 39 `Allocation` specification theorems (and their private helpers) -/

private theorem if_pos_eq {α : Type} {c : Prop} [Decidable c] {t e : α} (h : c) :
    (if c then t else e) = t := by
  split
  · rfl
  · next hn => exact absurd h hn

private theorem if_neg_eq {α : Type} {c : Prop} [Decidable c] {t e : α} (h : ¬c) :
    (if c then t else e) = e := by
  split
  · next hp => exact absurd hp h
  · rfl

private theorem checkedSlice_ok (allocation : Allocation P E) (range : AllocRange) (finish : Size)
    (storage : allocation.len = allocation.byteSize.bytes.toNat)
    (endEq : range.endExclusive = .ok finish)
    (startLe : range.start.bytes.toNat ≤ finish.bytes.toNat)
    (inBounds : finish.bytes.toNat ≤ allocation.byteSize.bytes.toNat) :
    checkedSlice allocation range =
      .ok ((raw allocation).extract range.start.bytes.toNat finish.bytes.toNat) := by
  unfold checkedSlice
  change (raw allocation).size = allocation.byteSize.bytes.toNat at storage
  have h_not_s : ¬(finish.bytes < range.start.bytes) :=
    UInt64.not_lt.mpr (UInt64.le_iff_toNat_le.mpr startLe)
  have h_not_f : ¬(allocation.byteSize.bytes < finish.bytes) :=
    UInt64.not_lt.mpr (UInt64.le_iff_toNat_le.mpr inBounds)
  simp [storage, endEq, h_not_s, h_not_f, bind, Bind.bind, Except.bind, Except.mapError, pure, Pure.pure, Except.pure]

private theorem full_range_endExclusive (sz : Size) :
    (allocRange Size.ZERO sz).endExclusive = .ok sz := by
  cases sz
  simp [allocRange, AllocRange.endExclusive, AllocRange.end, Size.ZERO, Size.ofBytes, Size.add, Except.mapError]

private theorem eq_of_not_bne {α : Type} [BEq α] [LawfulBEq α] {a b : α}
    (h : ¬((a != b) = true)) : a = b := by
  simp [bne] at h
  exact h

private theorem getBytesUnchecked_full_rawBytes (allocation : Allocation P E)
    (storage : allocation.len = allocation.byteSize.bytes.toNat) :
    allocation.getBytesUnchecked (allocRange Size.ZERO allocation.byteSize) = .ok (raw allocation) := by
  rw [getBytesUnchecked_eq]
  rw [checkedSlice_ok allocation (allocRange Size.ZERO allocation.byteSize) allocation.byteSize
    storage (full_range_endExclusive allocation.byteSize) (Nat.zero_le _) (Nat.le_refl _)]
  dsimp only [allocRange]
  have h_zero : Size.ZERO.bytes.toNat = 0 := rfl
  rw [h_zero, ← storage]
  exact congrArg Except.ok (Array.extract_size (xs := (raw allocation)))

private theorem extract_ByteAt (arr : Array UInt8) (start finish idx : Nat)
    (h_fin : finish ≤ arr.size) (h_lo : start ≤ idx) (h_hi : idx < finish) :
    (arr.extract start finish)[idx - start]? = arr[idx]? := by
  have h_idx_lt : idx < arr.size := by omega
  have h_ext_sz : (arr.extract start finish).size = finish - start := by
    simp [Array.size_extract, Nat.min_eq_left h_fin]
  have h_sub_lt : idx - start < (arr.extract start finish).size := by omega
  rw [Array.getElem?_eq_getElem h_sub_lt, Array.getElem?_eq_getElem h_idx_lt, Array.getElem_extract]
  have h_add_sub : start + (idx - start) = idx := by omega
  simp [h_add_sub]

private theorem splice_getElem? (raw data : Array UInt8) (start finish k : Nat)
    (h_lo : start ≤ finish) (h_fin : finish ≤ raw.size)
    (h_data_sz : data.size = finish - start) :
    (raw.extract 0 start ++ data ++ raw.extract finish raw.size)[k]? =
      if start ≤ k ∧ k < finish then data[k - start]? else raw[k]? := by
  let pfx := raw.extract 0 start
  let sfx := raw.extract finish raw.size
  have h_pfx_sz : pfx.size = start := by
    simp [pfx, Array.size_extract, Nat.min_eq_left (by omega : start ≤ raw.size)]
  have h_sfx_sz : sfx.size = raw.size - finish := by
    simp [sfx, Array.size_extract]
  by_cases h_lt_start : k < start
  · have h_not_in : ¬(start ≤ k ∧ k < finish) := by omega
    rw [if_neg_eq h_not_in]
    have h1 : (pfx ++ data ++ sfx)[k]? = (pfx ++ data)[k]? :=
      Array.getElem?_append_left (by simp [Array.size_append, h_pfx_sz]; omega)
    have h2 : (pfx ++ data)[k]? = pfx[k]? :=
      Array.getElem?_append_left (by simp [h_pfx_sz, h_lt_start])
    rw [h1, h2]
    have he := extract_ByteAt raw 0 start k (by omega) (Nat.zero_le _) h_lt_start
    simpa [pfx] using he
  · by_cases h_lt_fin : k < finish
    · have h_in : start ≤ k ∧ k < finish := ⟨by omega, h_lt_fin⟩
      rw [if_pos_eq h_in]
      have h1 : (pfx ++ data ++ sfx)[k]? = (pfx ++ data)[k]? :=
        Array.getElem?_append_left (by simp [Array.size_append, h_pfx_sz, h_data_sz]; omega)
      have h2 : (pfx ++ data)[k]? = data[k - pfx.size]? :=
        Array.getElem?_append_right (by simp [h_pfx_sz]; omega)
      simpa [h_pfx_sz] using h1.trans h2
    · have h_not_in : ¬(start ≤ k ∧ k < finish) := by omega
      rw [if_neg_eq h_not_in]
      have h1 : (pfx ++ data ++ sfx)[k]? = sfx[k - (pfx ++ data).size]? :=
        Array.getElem?_append_right (by simp [Array.size_append, h_pfx_sz, h_data_sz]; omega)
      have h_pd_sz : (pfx ++ data).size = finish := by
        simp [Array.size_append, h_pfx_sz, h_data_sz]; omega
      rw [h1, h_pd_sz]
      by_cases h_lt_raw : k < raw.size
      · have he := extract_ByteAt raw finish raw.size k (Nat.le_refl _) (by omega) h_lt_raw
        simpa [sfx] using he
      · have h_none1 : sfx[k - finish]? = none :=
          Array.getElem?_eq_none (by rw [h_sfx_sz]; omega)
        have h_none2 : raw[k]? = none :=
          Array.getElem?_eq_none (by omega)
        exact h_none1.trans h_none2.symm

private theorem splice_extract_exact (raw data : Array UInt8) (start finish : Nat)
    (h_lo : start ≤ finish) (h_fin : finish ≤ raw.size)
    (h_data_sz : data.size = finish - start) :
    (raw.extract 0 start ++ data ++ raw.extract finish raw.size).extract start finish = data := by
  let spliced := raw.extract 0 start ++ data ++ raw.extract finish raw.size
  have h_sp_sz : spliced.size = raw.size := by
    simp [spliced, Array.size_append, Array.size_extract,
      Nat.min_eq_left (by omega : start ≤ raw.size), h_data_sz]
    omega
  apply Array.ext
  · rw [Array.size_extract, h_sp_sz, Nat.min_eq_left h_fin, h_data_sz]
  · intro i hi1 hi2
    have hi_lt : i < finish - start := by simpa [h_data_sz] using hi2
    have h_eq? := extract_ByteAt spliced start finish (start + i) (by rw [h_sp_sz]; exact h_fin)
      (by omega) (by omega)
    have h_sub : start + i - start = i := by omega
    rw [h_sub] at h_eq?
    have h_sp_i := splice_getElem? raw data start finish (start + i) h_lo h_fin h_data_sz
    rw [if_pos_eq ⟨by omega, by omega⟩, h_sub] at h_sp_i
    have h_lhs : (spliced.extract start finish)[i]? = some ((spliced.extract start finish)[i]'hi1) :=
      Array.getElem?_eq_getElem hi1
    have h_rhs : data[i]? = some (data[i]'hi2) := Array.getElem?_eq_getElem hi2
    have h_comb : (spliced.extract start finish)[i]? = data[i]? := h_eq?.trans h_sp_i
    exact Option.some.inj (h_lhs.symm.trans (h_comb.trans h_rhs))

private theorem splice_extract_disjoint (raw data : Array UInt8) (wStart wFin qStart qFin : Nat)
    (h_w_lo : wStart ≤ wFin) (h_w_fin : wFin ≤ raw.size)
    (h_q_lo : qStart ≤ qFin) (h_q_fin : qFin ≤ raw.size)
    (h_data_sz : data.size = wFin - wStart)
    (h_disj : wFin ≤ qStart ∨ qFin ≤ wStart) :
    (raw.extract 0 wStart ++ data ++ raw.extract wFin raw.size).extract qStart qFin =
      raw.extract qStart qFin := by
  let spliced := raw.extract 0 wStart ++ data ++ raw.extract wFin raw.size
  have h_sp_sz : spliced.size = raw.size := by
    simp [spliced, Array.size_append, Array.size_extract,
      Nat.min_eq_left (by omega : wStart ≤ raw.size), h_data_sz]
    omega
  apply Array.ext
  · rw [Array.size_extract, h_sp_sz, Array.size_extract]
  · intro i hi1 hi2
    have hi_lt : i < qFin - qStart := by
      rw [Array.size_extract, Nat.min_eq_left h_q_fin] at hi2
      exact hi2
    have h_sub : qStart + i - qStart = i := by omega
    have h_eq1 := extract_ByteAt spliced qStart qFin (qStart + i) (by rw [h_sp_sz]; exact h_q_fin)
      (by omega) (by omega)
    have h_eq2 := extract_ByteAt raw qStart qFin (qStart + i) h_q_fin (by omega) (by omega)
    have h_sp_i := splice_getElem? raw data wStart wFin (qStart + i) h_w_lo h_w_fin h_data_sz
    have h_out : ¬(wStart ≤ qStart + i ∧ qStart + i < wFin) := by omega
    rw [if_neg_eq h_out] at h_sp_i
    have h_comb : (spliced.extract qStart qFin)[i]? = (raw.extract qStart qFin)[i]? := by
      simpa [h_sub] using (h_eq1.trans h_sp_i).trans h_eq2.symm
    have h_lhs := Array.getElem?_eq_getElem hi1
    have h_rhs := Array.getElem?_eq_getElem hi2
    exact Option.some.inj (h_lhs.symm.trans (h_comb.trans h_rhs))

theorem byteSize_withExtra (allocation : Allocation P Unit) (extra : E) :
    (allocation.withExtra extra).byteSize = allocation.byteSize := rfl

theorem len_withExtra (allocation : Allocation P Unit) (extra : E) :
    (allocation.withExtra extra).len = allocation.len := rfl

theorem align_withExtra (allocation : Allocation P Unit) (extra : E) :
    (allocation.withExtra extra).align = allocation.align := rfl

theorem mutability_withExtra (allocation : Allocation P Unit) (extra : E) :
    (allocation.withExtra extra).mutability = allocation.mutability := rfl

theorem provenanceMap_withExtra (allocation : Allocation P Unit) (extra : E) :
    (allocation.withExtra extra).provenanceMap = allocation.provenanceMap := rfl

theorem initializationMask_withExtra (allocation : Allocation P Unit) (extra : E) :
    (allocation.withExtra extra).initializationMask = allocation.initializationMask := rfl

theorem getBytesUnchecked_withExtra (allocation : Allocation P Unit) (extra : E) (range : AllocRange) :
    (allocation.withExtra extra).getBytesUnchecked range = allocation.getBytesUnchecked range := rfl

theorem byteSize_mapExtra (allocation : Allocation P E) (f : E → E') :
    (allocation.mapExtra f).byteSize = allocation.byteSize := rfl

theorem len_mapExtra (allocation : Allocation P E) (f : E → E') :
    (allocation.mapExtra f).len = allocation.len := rfl

theorem align_mapExtra (allocation : Allocation P E) (f : E → E') :
    (allocation.mapExtra f).align = allocation.align := rfl

theorem mutability_mapExtra (allocation : Allocation P E) (f : E → E') :
    (allocation.mapExtra f).mutability = allocation.mutability := rfl

theorem provenanceMap_mapExtra (allocation : Allocation P E) (f : E → E') :
    (allocation.mapExtra f).provenanceMap = allocation.provenanceMap := rfl

theorem initializationMask_mapExtra (allocation : Allocation P E) (f : E → E') :
    (allocation.mapExtra f).initializationMask = allocation.initializationMask := rfl

theorem getBytesUnchecked_mapExtra (allocation : Allocation P E) (f : E → E') (range : AllocRange) :
    (allocation.mapExtra f).getBytesUnchecked range = allocation.getBytesUnchecked range := rfl

theorem getBytesStripProvenance_mapExtra [PointerProvenance P]
    (allocation : Allocation P E) (f : E → E') (layout : TargetDataLayout) (range : AllocRange) :
    (allocation.mapExtra f).getBytesStripProvenance layout range =
      allocation.getBytesStripProvenance layout range := rfl

theorem readScalar_mapExtra [DecidableEq P] [PointerProvenance P]
    (allocation : Allocation P E) (f : E → E') (layout : TargetDataLayout)
    (range : AllocRange) (readProvenance : Bool) :
    (allocation.mapExtra f).readScalar layout range readProvenance =
      allocation.readScalar layout range readProvenance := rfl

theorem writeBytes_mapExtra (start : Size) (bytes : Array UInt8) (ptrSize : Size)
    (allocation : Allocation P E) (f : E → E') :
    Allocation.writeBytes start bytes ptrSize (allocation.mapExtra f) =
      (match Allocation.writeBytes start bytes ptrSize allocation with
       | .ok value state => .ok value (state.mapExtra f)
       | .error error state => .error error (state.mapExtra f)) := by
  have slices : ∀ r, checkedSlice (allocation.mapExtra f) r = checkedSlice allocation r := fun _ => rfl
  rw [writeBytes_eq_R, writeBytes_eq_R]
  unfold writeBytesR setInitialization overwriteRawBytes
  simp only [Id.run, bind, Bind.bind, pure, Pure.pure, Except.bind, Except.mapError, Except.pure, slices,
    mutability_mapExtra, initializationMask_mapExtra, raw_withProvenance, byteSize_withProvenance]
  cases sizeForArray bytes.size with
  | error e => rfl
  | ok writeSize =>
    dsimp only
    cases checkedSlice allocation (allocRange start writeSize) with
    | error e => rfl
    | ok _ =>
      dsimp only
      by_cases h0 : writeSize.bytes == 0
      · simp only [h0, ↓reduceIte]
      · simp only [h0, Bool.false_eq_true, ↓reduceIte]
        by_cases hm : allocation.mutability != .Mut
        · simp only [hm, ↓reduceIte]
        · simp only [hm, Bool.false_eq_true, ↓reduceIte]
          cases allocation.initializationMask.setRange (allocRange start writeSize) true with
          | error e => rfl
          | ok mask =>
            dsimp only
            simp only [raw_mapExtra, provenanceMap_mapExtra, byteSize_mapExtra,
              raw_withInitMask, byteSize_withInitMask, provenanceMap_withInitMask]
            cases allocation.provenanceMap.clear (allocRange start writeSize) (raw allocation) ptrSize with
            | error e pm => rfl
            | ok _ pm =>
              dsimp only
              cases (allocRange start writeSize).endExclusive with
              | error e => rfl
              | ok fin =>
                dsimp only
                by_cases h_len :
                    (((raw allocation).extract 0 (allocRange start writeSize).start.bytes.toNat ++
                      bytes ++ (raw allocation).extract fin.bytes.toNat).size !=
                      allocation.byteSize.bytes.toNat) = true <;>
                  simp only [h_len, Bool.false_eq_true, ↓reduceIte, throw, MonadExceptOf.throw,
                    throwThe] <;>
                  rfl

theorem clearProvenance_mapExtra (range : AllocRange) (ptrSize : Size)
    (allocation : Allocation P E) (f : E → E') :
    Allocation.clearProvenance range ptrSize (allocation.mapExtra f) =
      (match Allocation.clearProvenance range ptrSize allocation with
       | .ok value state => .ok value (state.mapExtra f)
       | .error error state => .error error (state.mapExtra f)) := by
  have slices : checkedSlice (allocation.mapExtra f) range = checkedSlice allocation range := rfl
  rw [clearProvenance_eq_R, clearProvenance_eq_R]
  unfold clearProvenanceR
  rw [slices]
  simp only [Id.run, pure, Pure.pure, raw_mapExtra, provenanceMap_mapExtra]
  cases checkedSlice allocation range with
  | error _ => rfl
  | ok _ =>
    dsimp only
    cases allocation.provenanceMap.clear range (raw allocation) ptrSize <;> rfl

private theorem replicate_extract_zero (n start finish : Nat)
    (_h_lo : start ≤ finish) (h_fin : finish ≤ n) :
    (Array.replicate n (0 : UInt8)).extract start finish = Array.replicate (finish - start) 0 := by
  apply Array.ext
  · simp [Array.size_replicate, Nat.min_eq_left h_fin]
  · intro i hi1 hi2
    rw [Array.getElem_extract, Array.getElem_replicate, Array.getElem_replicate]

theorem fromBytes_spec (bytes : Array UInt8) (align : Align) (mutability : Mutability)
    (alloc : Allocation P Unit)
    (created : Allocation.fromBytes bytes align mutability = .ok alloc) :
    alloc.byteSize.bytes.toNat = bytes.size ∧
      alloc.len = bytes.size ∧
      alloc.mutability = mutability ∧
      alloc.extra = () ∧
      alloc.nativeBuffer = none ∧
      alloc.provenanceMap = ProvenanceMap.new ∧
      alloc.initializationMask = InitMask.new alloc.byteSize true ∧
      InitMask.WriteProof.WellFormed alloc.initializationMask ∧
      ∀ (range : AllocRange) (finish : Size),
        range.endExclusive = .ok finish →
        range.start.bytes.toNat ≤ finish.bytes.toNat →
        finish.bytes.toNat ≤ bytes.size →
        alloc.getBytesUnchecked range =
          .ok (bytes.extract range.start.bytes.toNat finish.bytes.toNat) := by
  rw [fromBytes_eq_R] at created
  unfold fromBytesR at created
  cases h_al : checkedAlign align with
  | error e => simp [h_al, bind, Bind.bind, Except.bind] at created
  | ok normAlign =>
    simp only [h_al, bind, Bind.bind, Except.bind] at created
    cases h_sz : sizeForArray bytes.size with
    | error e => simp [h_sz] at created
    | ok sz =>
      simp only [h_sz] at created
      by_cases h_eq : bytes.size = sz.bytes.toNat
      · simp only [h_eq, ↓reduceDIte, pure, Pure.pure, Except.pure, Except.ok.injEq] at created
        subst created
        refine ⟨h_eq.symm, rfl, rfl, rfl, rfl, rfl, rfl, trivial, ?_⟩
        intro range finish h_end h_lo h_fin
        exact checkedSlice_ok _ range finish h_eq h_end h_lo
          (by change _ ≤ sz.bytes.toNat; omega)
      · simp [h_eq] at created

theorem fromBytes_exists (bytes : Array UInt8) (align : Align) (alignmentBytes : UInt64)
    (mutability : Mutability)
    (h_bytes : Align.bytes align = .ok alignmentBytes)
    (h_norm : Align.fromBytes alignmentBytes = .ok align)
    (h_fits : bytes.size < 2 ^ 64) :
    ∃ alloc : Allocation P Unit,
      Allocation.fromBytes bytes align mutability = .ok alloc ∧
      alloc.byteSize = Size.ofBytes (UInt64.ofNat bytes.size) ∧
      alloc.align = align := by
  have h_ca : checkedAlign align = .ok align := by
    unfold checkedAlign
    simp [h_bytes, h_norm, bind, Bind.bind, Except.bind, Except.mapError, pure, Pure.pure, Except.pure]
  have h_not_gt : ¬(bytes.size > maxU64Nat) := by
    unfold maxU64Nat; omega
  have h_tonat : (Size.ofBytes (UInt64.ofNat bytes.size)).bytes.toNat = bytes.size := by
    simp [Size.ofBytes, UInt64.toNat_ofNat', Nat.mod_eq_of_lt h_fits]
  have h_sfa : sizeForArray bytes.size = .ok (Size.ofBytes (UInt64.ofNat bytes.size)) := by
    unfold sizeForArray
    simp [h_not_gt, h_tonat, pure, Pure.pure, Except.pure]
  refine ⟨mkAlloc bytes (Size.ofBytes (UInt64.ofNat bytes.size)) ProvenanceMap.new
    (InitMask.new (Size.ofBytes (UInt64.ofNat bytes.size)) true) align mutability () none,
    ?_, rfl, rfl⟩
  rw [fromBytes_eq_R]
  unfold fromBytesR
  simp [h_ca, h_sfa, h_tonat, bind, Bind.bind, Except.bind, pure, Pure.pure, Except.pure]

theorem tryNew_spec (size : Size) (align : Align) (init : AllocInit)
    (alloc : Allocation P Unit)
    (created : Allocation.tryNew size align init
      (fun n _ => some (Array.replicate n.bytes.toNat 0)) = .ok alloc) :
    alloc.byteSize = size ∧
      alloc.len = size.bytes.toNat ∧
      alloc.mutability = .Mut ∧
      alloc.extra = () ∧
      alloc.nativeBuffer = none ∧
      alloc.provenanceMap = ProvenanceMap.new ∧
      (init = .Uninit → alloc.initializationMask = InitMask.new size false) ∧
      (init = .Zero → alloc.initializationMask = InitMask.new size true) ∧
      InitMask.WriteProof.WellFormed alloc.initializationMask ∧
      ∀ (range : AllocRange) (finish : Size),
        range.endExclusive = .ok finish →
        range.start.bytes.toNat ≤ finish.bytes.toNat →
        finish.bytes.toNat ≤ size.bytes.toNat →
        alloc.getBytesUnchecked range =
          .ok (Array.replicate (finish.bytes.toNat - range.start.bytes.toNat) 0) := by
  rw [tryNew_eq_R] at created
  unfold tryNewR at created
  cases h_al : checkedAlign align with
  | error e => simp [h_al, bind, Bind.bind, Except.bind] at created
  | ok normAlign =>
    let bInit := match init with | .Uninit => false | .Zero => true
    simp [h_al, firstNonZero_replicate,
      bind, Bind.bind, Except.bind, pure, Pure.pure, Except.pure] at created
    subst created
    refine ⟨rfl, Array.size_replicate, rfl, rfl, rfl, rfl,
      fun h => by subst h; rfl, fun h => by subst h; rfl, trivial, ?_⟩
    intro range finish h_end h_lo h_fin
    let a0 : Allocation P Unit :=
      mkAlloc (Array.replicate size.bytes.toNat 0) size ProvenanceMap.new
        (InitMask.new size bInit) normAlign .Mut () none
    rw [getBytesUnchecked_eq]
    rw [checkedSlice_ok a0 range finish Array.size_replicate h_end h_lo h_fin]
    exact congrArg Except.ok (replicate_extract_zero size.bytes.toNat _ _ h_lo h_fin)

theorem tryNew_exists (size : Size) (align : Align) (alignmentBytes : UInt64) (init : AllocInit)
    (h_bytes : Align.bytes align = .ok alignmentBytes)
    (h_norm : Align.fromBytes alignmentBytes = .ok align) :
    ∃ alloc : Allocation P Unit,
      Allocation.tryNew size align init
        (fun n _ => some (Array.replicate n.bytes.toNat 0)) = .ok alloc ∧
      alloc.align = align := by
  refine ⟨mkAlloc (Array.replicate size.bytes.toNat 0) size ProvenanceMap.new
    (InitMask.new size (match init with | .Uninit => false | .Zero => true)) align .Mut () none,
    ?_, rfl⟩
  rw [tryNew_eq_R]
  simp [tryNewR, checkedAlign, h_bytes, h_norm, firstNonZero_replicate,
    bind, Bind.bind, Except.bind, pure, Pure.pure, Except.pure, Except.mapError]

theorem getBytesUnchecked_size (allocation : Allocation P E) (range : AllocRange) (finish : Size)
    (storage : allocation.len = allocation.byteSize.bytes.toNat)
    (endEq : range.endExclusive = .ok finish)
    (startLe : range.start.bytes.toNat ≤ finish.bytes.toNat)
    (inBounds : finish.bytes.toNat ≤ allocation.byteSize.bytes.toNat) :
    ∃ slice, allocation.getBytesUnchecked range = .ok slice ∧
      slice.size = finish.bytes.toNat - range.start.bytes.toNat := by
  refine ⟨(raw allocation).extract range.start.bytes.toNat finish.bytes.toNat,
    checkedSlice_ok allocation range finish storage endEq startLe inBounds, ?_⟩
  change _ = _
  have h_fin_raw : finish.bytes.toNat ≤ (raw allocation).size := by
    change finish.bytes.toNat ≤ allocation.len; omega
  simp [Array.size_extract, Nat.min_eq_left h_fin_raw]

theorem getBytesUnchecked_subrange (allocation : Allocation P E)
    (rOuter rInner : AllocRange) (fOuter fInner : Size) (outerBytes : Array UInt8)
    (h_outer_end : rOuter.endExclusive = .ok fOuter)
    (h_inner_end : rInner.endExclusive = .ok fInner)
    (h_lo : rOuter.start.bytes.toNat ≤ rInner.start.bytes.toNat)
    (h_mid : rInner.start.bytes.toNat ≤ fInner.bytes.toNat)
    (h_hi : fInner.bytes.toNat ≤ fOuter.bytes.toNat)
    (h_outer : allocation.getBytesUnchecked rOuter = .ok outerBytes) :
    allocation.getBytesUnchecked rInner =
      .ok (outerBytes.extract
        (rInner.start.bytes.toNat - rOuter.start.bytes.toNat)
        (fInner.bytes.toNat - rOuter.start.bytes.toNat)) := by
  rw [getBytesUnchecked_eq] at h_outer
  unfold checkedSlice at h_outer
  by_cases h_mis : (raw allocation).size != allocation.byteSize.bytes.toNat
  · simp [h_mis, bind, Bind.bind, Except.bind] at h_outer
  · have h_raw_sz : (raw allocation).size = allocation.byteSize.bytes.toNat := eq_of_not_bne h_mis
    have storage : allocation.len = allocation.byteSize.bytes.toNat := h_raw_sz
    simp only [h_mis, Bool.false_eq_true, ↓reduceIte, h_outer_end, Except.mapError,
      bind, Bind.bind, Except.bind] at h_outer
    by_cases h_oob : rOuter.start.bytes > fOuter.bytes || fOuter.bytes > allocation.byteSize.bytes
    · simp [h_oob] at h_outer
    · simp only [h_oob, Bool.false_eq_true, ↓reduceIte, pure, Pure.pure, Except.pure,
        Except.ok.injEq] at h_outer
      simp only [Bool.or_eq_true, not_or, decide_eq_true_eq, gt_iff_lt, UInt64.lt_iff_toNat_lt] at h_oob
      have h_fOuter_le : fOuter.bytes.toNat ≤ allocation.byteSize.bytes.toNat := by omega
      have h_fOuter_raw : fOuter.bytes.toNat ≤ (raw allocation).size := by omega
      have h_fInner_raw : fInner.bytes.toNat ≤ (raw allocation).size := by omega
      rw [getBytesUnchecked_eq]
      rw [checkedSlice_ok allocation rInner fInner storage h_inner_end h_mid (by omega)]
      subst h_outer
      apply congrArg Except.ok
      apply Array.ext
      · simp [Array.size_extract, Nat.min_eq_left h_fOuter_raw, Nat.min_eq_left h_fInner_raw]
        omega
      · intro i hi1 hi2
        rw [Array.getElem_extract, Array.getElem_extract, Array.getElem_extract]
        have h_idx_eq : rOuter.start.bytes.toNat + ((rInner.start.bytes.toNat - rOuter.start.bytes.toNat) + i) =
            rInner.start.bytes.toNat + i := by omega
        simp only [h_idx_eq]

theorem getBytesUnchecked_split (allocation : Allocation P E)
    (r1 r2 r12 : AllocRange) (mid fin : Size) (b1 b2 : Array UInt8)
    (h_end1 : r1.endExclusive = .ok mid)
    (h_start2 : r2.start = mid)
    (h_end2 : r2.endExclusive = .ok fin)
    (h_start12 : r12.start = r1.start)
    (h_end12 : r12.endExclusive = .ok fin)
    (h_lo1 : r1.start.bytes.toNat ≤ mid.bytes.toNat)
    (h_lo2 : mid.bytes.toNat ≤ fin.bytes.toNat)
    (h_get1 : allocation.getBytesUnchecked r1 = .ok b1)
    (h_get2 : allocation.getBytesUnchecked r2 = .ok b2) :
    allocation.getBytesUnchecked r12 = .ok (b1 ++ b2) := by
  have h_chk2 := h_get2
  rw [getBytesUnchecked_eq] at h_chk2
  unfold checkedSlice at h_chk2
  by_cases h_mis : (raw allocation).size != allocation.byteSize.bytes.toNat
  · simp [h_mis, bind, Bind.bind, Except.bind] at h_chk2
  · have h_raw_sz : (raw allocation).size = allocation.byteSize.bytes.toNat := eq_of_not_bne h_mis
    have storage : allocation.len = allocation.byteSize.bytes.toNat := h_raw_sz
    simp only [h_mis, Bool.false_eq_true, ↓reduceIte, h_end2, Except.mapError,
      bind, Bind.bind, Except.bind] at h_chk2
    by_cases h_oob : r2.start.bytes > fin.bytes || fin.bytes > allocation.byteSize.bytes
    · simp [h_oob] at h_chk2
    · simp only [Bool.or_eq_true, not_or, decide_eq_true_eq, gt_iff_lt, UInt64.lt_iff_toNat_lt] at h_oob
      have h_fin_ib : fin.bytes.toNat ≤ allocation.byteSize.bytes.toNat := by omega
      have h_fin_raw : fin.bytes.toNat ≤ (raw allocation).size := by omega
      have h_mid_raw : mid.bytes.toNat ≤ (raw allocation).size := by omega
      have hs1 := checkedSlice_ok allocation r1 mid storage h_end1 h_lo1 (by omega)
      have hs2 := checkedSlice_ok allocation r2 fin storage h_end2 (by rw [h_start2]; exact h_lo2) h_fin_ib
      have hs12 := checkedSlice_ok allocation r12 fin storage h_end12 (by rw [h_start12]; omega) h_fin_ib
      rw [getBytesUnchecked_eq] at h_get1 h_get2 ⊢
      rw [hs1] at h_get1
      rw [hs2] at h_get2
      injection h_get1 with hb1
      injection h_get2 with hb2
      subst hb1; subst hb2
      rw [hs12, h_start12, h_start2]
      apply congrArg Except.ok
      apply Array.ext
      · simp [Array.size_extract, Nat.min_eq_left h_fin_raw]
        omega
      · intro i hi1 hi2
        have hi_lt : i < fin.bytes.toNat - r1.start.bytes.toNat := by
          rw [Array.size_extract, Nat.min_eq_left h_fin_raw] at hi1; exact hi1
        by_cases h_left : i < mid.bytes.toNat - r1.start.bytes.toNat
        · have h_sz1 : ((raw allocation).extract r1.start.bytes.toNat mid.bytes.toNat).size =
              mid.bytes.toNat - r1.start.bytes.toNat := by
            simp [Array.size_extract, Nat.min_eq_left h_mid_raw]
          rw [Array.getElem_append_left (by rw [h_sz1]; exact h_left),
            Array.getElem_extract, Array.getElem_extract]
        · have h_sz1 : ((raw allocation).extract r1.start.bytes.toNat mid.bytes.toNat).size =
              mid.bytes.toNat - r1.start.bytes.toNat := by
            simp [Array.size_extract, Nat.min_eq_left h_mid_raw]
          rw [Array.getElem_append_right (by rw [h_sz1]; omega),
            Array.getElem_extract, Array.getElem_extract]
          have h_idx_eq : mid.bytes.toNat +
              (i - ((raw allocation).extract r1.start.bytes.toNat mid.bytes.toNat).size) =
              r1.start.bytes.toNat + i := by omega
          simp only [h_idx_eq]

private theorem targetUIntBytes_eq_ofFn (layout : TargetDataLayout) (size : Size) (bits : U128)
    (limit : size.bytes.toNat ≤ 16) :
    targetUIntBytes layout size bits =
      .ok (Array.ofFn (fun i : Fin size.bytes.toNat =>
        UInt8.ofNat ((bits.toNat / 2 ^ (8 *
          (if layout.endian == .little then i.1 else size.bytes.toNat - i.1 - 1))) % 256))) := by
  let byteFn : Nat → UInt8 := fun index =>
    UInt8.ofNat ((bits.toNat / 2 ^ (8 *
      (if layout.endian == .little then index else size.bytes.toNat - index - 1))) % 256)
  have h_loop : ∀ (indices : List Nat) (acc : Array UInt8),
      (forIn indices acc (fun index cur =>
        (Except.ok (ForInStep.yield (cur.push (byteFn index))) :
          Except AllocError (ForInStep (Array UInt8))))) =
      .ok (acc ++ (indices.map byteFn).toArray) := by
    intro indices
    induction indices with
    | nil =>
      intro acc
      simp [List.forIn_nil, Pure.pure, Except.pure]
    | cons idx rest ih =>
      intro acc
      rw [List.forIn_cons]
      dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure]
      rw [ih (acc.push (byteFn idx))]
      apply congrArg Except.ok
      apply Array.ext
      · simp [Array.size_append]
      · intro k hk1 hk2
        by_cases hk : k < acc.size
        · rw [Array.getElem_append_left (by simp [Array.size_push]; omega),
            Array.getElem_push_lt hk, Array.getElem_append_left hk]
        · by_cases hk_eq : k = acc.size
          · subst hk_eq
            rw [Array.getElem_append_left (by simp [Array.size_push]),
              Array.getElem_push_eq, Array.getElem_append_right (Nat.le_refl _)]
            simp
          · rw [Array.getElem_append_right (by simp [Array.size_push]; omega),
              Array.getElem_append_right (by omega)]
            simp only [Array.size_push, List.map_cons, List.getElem_toArray, List.getElem_cons]
            have h_pos : k - acc.size = (k - (acc.size + 1)) + 1 := by omega
            simp [h_pos]
  have small : ¬size.bytes > 16 := by
    simp only [UInt64.lt_iff_toNat_lt]
    exact Nat.not_lt.mpr limit
  unfold targetUIntBytes
  simp only [small, ↓reduceIte, Std.Legacy.Range.forIn_eq_forIn_range']
  have h_inst := h_loop (List.range' 0 [:size.bytes.toNat].size) #[]
  dsimp only [byteFn] at h_inst
  change (forIn (List.range' 0 [:size.bytes.toNat].size) #[] (fun index cur =>
    Except.ok (ForInStep.yield (cur.push (UInt8.ofNat ((bits.toNat / 2 ^ (8 *
      (if layout.endian == .little then index else size.bytes.toNat - index - 1))) % 256))))) >>=
    Except.ok) = _
  rw [h_inst]
  simp only [Bind.bind, Except.bind, Array.empty_append]
  apply congrArg Except.ok
  apply Array.ext
  · simp [Std.Legacy.Range.size]
  · intro i hi1 hi2
    simp [List.getElem_range']

private theorem readTargetUInt_eq_foldl (layout : TargetDataLayout) (bytes : Array UInt8)
    (limit : bytes.size ≤ 16) :
    readTargetUInt layout bytes =
      .ok (BitVec.ofNat 128 ((List.range bytes.size).foldl (fun acc index =>
        acc + (bytes[index]?.getD 0).toNat * 2 ^ (8 *
          (if layout.endian == .little then index else bytes.size - index - 1))) 0)) := by
  have h_loop : ∀ (indices : List Nat) (acc : Nat),
      (∀ idx ∈ indices, idx < bytes.size) →
      (forIn indices acc (fun index value =>
        (match bytes[index]? with
          | some byte =>
            pure (ForInStep.yield (value + byte.toNat * 2 ^ (8 *
              (if layout.endian == .little then index else bytes.size - index - 1))))
          | _ => do
            throw (.invalidSliceEndpoints index (index + 1) bytes.size)
            pure (ForInStep.yield value) :
          Except AllocError (ForInStep Nat)))) =
      .ok (indices.foldl (fun v index =>
        v + (bytes[index]?.getD 0).toNat * 2 ^ (8 *
          (if layout.endian == .little then index else bytes.size - index - 1))) acc) := by
    intro indices
    induction indices with
    | nil =>
      intro acc _
      rfl
    | cons idx rest ih =>
      intro acc h_in
      have h_ib : idx < bytes.size := h_in idx (List.mem_cons_self ..)
      have h_get : bytes[idx]? = some (bytes[idx]'h_ib) := Array.getElem?_eq_getElem h_ib
      rw [List.forIn_cons, List.foldl_cons]
      simp only [h_get, Option.getD_some, Bind.bind, Except.bind, Pure.pure, Except.pure]
      exact ih _ (fun x hx => h_in x (List.mem_cons_of_mem _ hx))
  have small : ¬bytes.size > 16 := Nat.not_lt.mpr limit
  unfold readTargetUInt
  simp only [small, ↓reduceIte, Std.Legacy.Range.forIn_eq_forIn_range']
  have h_rng_eq : List.range' [0:bytes.size].start [0:bytes.size].size [0:bytes.size].step =
      List.range bytes.size := by
    simp [Std.Legacy.Range.size, List.range_eq_range']
  rw [h_rng_eq]
  rw [h_loop (List.range bytes.size) 0 (fun idx h => List.mem_range.mp h)]
  rfl

private theorem digit_step_mod (val m : Nat) :
    val % 2 ^ (8 * m) + ((val / 2 ^ (8 * m)) % 256) * 2 ^ (8 * m) =
      val % 2 ^ (8 * (m + 1)) := by
  let P := 2 ^ (8 * m)
  have hP_pos : 0 < P := Nat.two_pow_pos (8 * m)
  let r := val % P
  let d := (val / P) % 256
  let q := (val / P) / 256
  have hr : r < P := Nat.mod_lt val hP_pos
  have hd : d < 256 := Nat.mod_lt _ (by decide)
  have hd_le : d ≤ 255 := by omega
  have h_dp : d * P ≤ 255 * P := Nat.mul_le_mul_right P hd_le
  have h_sum_lt : r + d * P < P * 256 := by omega
  have h_div1 : P * (val / P) + r = val := Nat.div_add_mod val P
  have h_div2 : 256 * q + d = val / P := Nat.div_add_mod (val / P) 256
  have h_pow_succ : 2 ^ (8 * (m + 1)) = P * 256 := by
    have he : 8 * (m + 1) = 8 * m + 8 := by omega
    rw [he, Nat.pow_add]
  have h_val_decomp : val = (r + d * P) + (P * 256) * q := by
    calc
      val = P * (val / P) + r := h_div1.symm
      _ = P * (256 * q + d) + r := by rw [← h_div2]
      _ = (r + d * P) + (P * 256) * q := by
        simp [Nat.left_distrib, Nat.mul_comm, Nat.mul_left_comm,
          Nat.add_assoc, Nat.add_comm]
  have h_rhs : val % 2 ^ (8 * (m + 1)) = ((r + d * P) + (P * 256) * q) % (P * 256) := by
    rw [h_pow_succ]
    exact congrArg (· % (P * 256)) h_val_decomp
  rw [h_rhs, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h_sum_lt]

private theorem foldl_add_init (xs : List Nat) (g : Nat → Nat) (init : Nat) :
    xs.foldl (fun acc x => acc + g x) init =
      init + xs.foldl (fun acc x => acc + g x) 0 := by
  induction xs generalizing init with
  | nil => simp
  | cons x rest ih =>
    simp only [List.foldl_cons, Nat.zero_add]
    rw [ih (init + g x), ih (g x), Nat.add_assoc]

private theorem endian_digits_fold_mod (endian : Endian) (val n : Nat) :
    (List.range n).foldl (fun acc idx =>
      acc + ((val / 2 ^ (8 * (if endian == .little then idx else n - idx - 1))) % 256) *
        2 ^ (8 * (if endian == .little then idx else n - idx - 1))) 0 =
      val % 2 ^ (8 * n) := by
  cases endian with
  | little =>
    simp only [beq_self_eq_true, ↓reduceIte]
    induction n with
    | zero => simp [Nat.mod_one]
    | succ m ih =>
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ih]
      exact digit_step_mod val m
  | big =>
    have h_be : (Endian.big == Endian.little) = false := rfl
    simp only [h_be, Bool.false_eq_true, ↓reduceIte]
    induction n with
    | zero => simp [Nat.mod_one]
    | succ m ih =>
      rw [List.range_succ_eq_map, List.foldl_cons, List.foldl_map]
      have hm0 : m + 1 - 0 - 1 = m := by omega
      simp only [Nat.zero_add, hm0]
      have h_fn_eq : (fun acc (x : Nat) =>
          acc + ((val / 2 ^ (8 * (m + 1 - x.succ - 1))) % 256) *
            2 ^ (8 * (m + 1 - x.succ - 1))) =
        (fun acc (x : Nat) =>
          acc + ((val / 2 ^ (8 * (m - x - 1))) % 256) * 2 ^ (8 * (m - x - 1))) := by
        funext acc x
        have hx : m + 1 - x.succ - 1 = m - x - 1 := by omega
        rw [hx]
      rw [h_fn_eq, foldl_add_init, ih, Nat.add_comm]
      exact digit_step_mod val m

private theorem readTargetUInt_ofFn_mod (layout : TargetDataLayout) (n val : Nat)
    (limit : n ≤ 16) :
    readTargetUInt layout (Array.ofFn (fun i : Fin n =>
      UInt8.ofNat ((val / 2 ^ (8 *
        (if layout.endian == .little then i.1 else n - i.1 - 1))) % 256))) =
      .ok (BitVec.ofNat 128 (val % 2 ^ (8 * n))) := by
  let arr := Array.ofFn (fun i : Fin n =>
    UInt8.ofNat ((val / 2 ^ (8 *
      (if layout.endian == .little then i.1 else n - i.1 - 1))) % 256))
  have h_sz : arr.size = n := Array.size_ofFn ..
  rw [readTargetUInt_eq_foldl layout arr (by rw [h_sz]; exact limit)]
  rw [h_sz]
  apply congrArg Except.ok
  apply congrArg (BitVec.ofNat 128)
  have h_congr : ∀ (xs : List Nat) (acc : Nat),
      (∀ idx ∈ xs, idx < n) →
      xs.foldl (fun a idx =>
        a + (arr[idx]?.getD 0).toNat * 2 ^ (8 *
          (if layout.endian == .little then idx else n - idx - 1))) acc =
      xs.foldl (fun a idx =>
        a + ((val / 2 ^ (8 * (if layout.endian == .little then idx else n - idx - 1))) % 256) *
          2 ^ (8 * (if layout.endian == .little then idx else n - idx - 1))) acc := by
    intro xs
    induction xs with
    | nil => intro acc _; rfl
    | cons idx rest ih =>
      intro acc h_in
      have h_ib : idx < n := h_in idx (List.mem_cons_self ..)
      have h_ib_arr : idx < arr.size := by rw [h_sz]; exact h_ib
      have h_elem : (arr[idx]?.getD 0).toNat =
          (val / 2 ^ (8 * (if layout.endian == .little then idx else n - idx - 1))) % 256 := by
        rw [Array.getElem?_eq_getElem h_ib_arr, Option.getD_some]
        dsimp only [arr]
        rw [Array.getElem_ofFn]
        have h_lt256 : (val / 2 ^ (8 * (if layout.endian == .little then idx else n - idx - 1))) % 256 < 256 :=
          Nat.mod_lt _ (by decide)
        simp [UInt8.toNat_ofNat']
      simp only [List.foldl_cons, h_elem]
      exact ih _ (fun x hx => h_in x (List.mem_cons_of_mem _ hx))
  rw [h_congr (List.range n) 0 (fun idx h => List.mem_range.mp h)]
  exact endian_digits_fold_mod layout.endian val n

theorem getBytesStripProvenance_uninit_err [PointerProvenance P]
    (allocation : Allocation P E) (layout : TargetDataLayout)
    (range bad : AllocRange)
    (h_uninit : allocation.initializationMask.isRangeInitialized range = .ok (.error bad)) :
    allocation.getBytesStripProvenance layout range =
      .error (.invalidUninitBytes (some ⟨range, bad⟩)) := by
  rw [getBytesStripProvenance_eq_R]
  unfold getBytesStripProvenanceR
  simp [h_uninit, bind, Bind.bind, Except.bind, Except.mapError, throw, MonadExceptOf.throw, throwThe]

theorem getBytesStripProvenance_ok [PointerProvenance P]
    (allocation : Allocation P E) (layout : TargetDataLayout) (range : AllocRange)
    (h_init : allocation.initializationMask.isRangeInitialized range = .ok (.ok ()))
    (h_prov : PointerProvenance.offsetIsAddr (Prov := P) = true ∨
      allocation.provenanceMap.rangeEmpty range (Size.fromBits layout.pointerWidth.bits) = .ok true) :
    allocation.getBytesStripProvenance layout range = allocation.getBytesUnchecked range := by
  rw [getBytesStripProvenance_eq_R, getBytesUnchecked_eq]
  unfold getBytesStripProvenanceR pointerSize
  rcases h_prov with h_addr | h_empty
  · simp [h_init, h_addr, bind, Bind.bind, Except.bind, Except.mapError]
  · by_cases h_addr : PointerProvenance.offsetIsAddr (Prov := P) = true
    · simp [h_init, h_addr, bind, Bind.bind, Except.bind, Except.mapError]
    · have h_addr_f : PointerProvenance.offsetIsAddr (Prov := P) = false :=
        Bool.eq_false_iff.mpr h_addr
      simp [h_init, h_addr_f, h_empty, bind, Bind.bind, Except.bind, Except.mapError]

theorem readScalar_uninit_err [DecidableEq P] [PointerProvenance P]
    (allocation : Allocation P E) (layout : TargetDataLayout)
    (range bad : AllocRange) (readProvenance : Bool)
    (h_uninit : allocation.initializationMask.isRangeInitialized range = .ok (.error bad)) :
    allocation.readScalar layout range readProvenance =
      .error (.invalidUninitBytes (some ⟨range, bad⟩)) := by
  rw [readScalar_eq_R]
  unfold readScalarR
  simp [h_uninit, bind, Bind.bind, Except.bind, Except.mapError, throw, MonadExceptOf.throw, throwThe]

theorem readScalar_int_of_bytes [DecidableEq P] [PointerProvenance P]
    (allocation : Allocation P E) (layout : TargetDataLayout)
    (range : AllocRange) (bytes : Array UInt8)
    (h_init : allocation.initializationMask.isRangeInitialized range = .ok (.ok ()))
    (h_slice : allocation.getBytesUnchecked range = .ok bytes)
    (h_limit : bytes.size ≤ 16)
    (h_prov : PointerProvenance.offsetIsAddr (Prov := P) = true ∨
      allocation.provenanceMap.rangeEmpty range (Size.fromBits layout.pointerWidth.bits) = .ok true) :
    allocation.readScalar layout range false =
      (Scalar.fromUInt (BitVec.ofNat 128 ((List.range bytes.size).foldl (fun acc idx =>
        acc + (bytes[idx]?.getD 0).toNat * 2 ^ (8 *
          (if layout.endian == .little then idx else bytes.size - idx - 1))) 0))
        range.size).mapError AllocError.scalar := by
  rw [readScalar_eq_R]
  unfold readScalarR pointerSize
  rw [getBytesUnchecked_eq] at h_slice
  have h_read := readTargetUInt_eq_foldl layout bytes h_limit
  simp only [h_init, h_slice, Except.mapError, bind, Bind.bind, Except.bind, pure, Pure.pure, Except.pure]
  rw [h_read]
  rcases h_prov with h_addr | h_empty
  · simp [h_addr]
  · by_cases h_addr : PointerProvenance.offsetIsAddr (Prov := P) = true
    · simp [h_addr]
    · have h_addr_f : PointerProvenance.offsetIsAddr (Prov := P) = false :=
        Bool.eq_false_iff.mpr h_addr
      simp [h_addr_f, h_empty]

theorem readScalar_int_roundtrip [DecidableEq P] [PointerProvenance P]
    (allocation : Allocation P E) (layout : TargetDataLayout)
    (range : AllocRange) (bits : U128)
    (h_init : allocation.initializationMask.isRangeInitialized range = .ok (.ok ()))
    (h_limit : range.size.bytes.toNat ≤ 16)
    (h_bits_bound : bits.toNat < 2 ^ (8 * range.size.bytes.toNat))
    (h_prov : PointerProvenance.offsetIsAddr (Prov := P) = true ∨
      allocation.provenanceMap.rangeEmpty range (Size.fromBits layout.pointerWidth.bits) = .ok true)
    (h_slice : allocation.getBytesUnchecked range =
      .ok (Array.ofFn (fun i : Fin range.size.bytes.toNat =>
        UInt8.ofNat ((bits.toNat / 2 ^ (8 *
          (if layout.endian == .little then i.1 else range.size.bytes.toNat - i.1 - 1))) % 256)))) :
    allocation.readScalar layout range false =
      (Scalar.fromUInt bits range.size).mapError AllocError.scalar := by
  rw [readScalar_eq_R]
  unfold readScalarR pointerSize
  rw [getBytesUnchecked_eq] at h_slice
  have h_read := readTargetUInt_ofFn_mod layout range.size.bytes.toNat bits.toNat h_limit
  rw [Nat.mod_eq_of_lt h_bits_bound, BitVec.ofNat_toNat, BitVec.setWidth_eq] at h_read
  simp only [h_init, h_slice, Except.mapError, bind, Bind.bind, Except.bind, pure, Pure.pure, Except.pure]
  rw [h_read]
  rcases h_prov with h_addr | h_empty
  · simp [h_addr]
  · by_cases h_addr : PointerProvenance.offsetIsAddr (Prov := P) = true
    · simp [h_addr]
    · have h_addr_f : PointerProvenance.offsetIsAddr (Prov := P) = false :=
        Bool.eq_false_iff.mpr h_addr
      simp [h_addr_f, h_empty]

theorem readScalar_ptr_roundtrip [DecidableEq P] [PointerProvenance P]
    (allocation : Allocation P E) (layout : TargetDataLayout)
    (range : AllocRange) (ptr : Pointer P)
    (h_init : allocation.initializationMask.isRangeInitialized range = .ok (.ok ()))
    (h_ptr_sz : range.size = Size.fromBits layout.pointerWidth.bits)
    (h_limit : range.size.bytes.toNat ≤ 16)
    (h_off_bound : ptr.offset.bytes.toNat < 2 ^ (8 * range.size.bytes.toNat))
    (h_prov : allocation.provenanceMap.readPtr range.start
      (Size.fromBits layout.pointerWidth.bits) = .ok (some ptr.provenance))
    (h_slice : allocation.getBytesUnchecked range =
      .ok (Array.ofFn (fun i : Fin range.size.bytes.toNat =>
        UInt8.ofNat ((ptr.offset.bytes.toNat / 2 ^ (8 *
          (if layout.endian == .little then i.1 else range.size.bytes.toNat - i.1 - 1))) % 256)))) :
    allocation.readScalar layout range true = .ok (Scalar.fromPointer layout ptr) := by
  rw [readScalar_eq_R]
  unfold readScalarR pointerSize
  rw [getBytesUnchecked_eq] at h_slice
  have h_read := readTargetUInt_ofFn_mod layout range.size.bytes.toNat ptr.offset.bytes.toNat h_limit
  rw [Nat.mod_eq_of_lt h_off_bound] at h_read
  have h_u64_lt := ptr.offset.bytes.toNat_lt
  have h_lt128 : ptr.offset.bytes.toNat < 2 ^ 128 := by omega
  have h_bv_nat : (BitVec.ofNat 128 ptr.offset.bytes.toNat).toNat = ptr.offset.bytes.toNat := by
    simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h_lt128]
  have h_not_gt : ¬(18446744073709551615 < ptr.offset.bytes.toNat) := by omega
  have h_ptr_eta : Pointer.new ptr.provenance (Size.ofBytes ptr.offset.bytes) = ptr := by
    cases ptr with
    | mk off prov =>
      cases off with
      | mk b =>
        rfl
  simp only [h_init, h_slice, Except.mapError, bind, Bind.bind, Except.bind, pure, Pure.pure, Except.pure]
  rw [h_read]
  simp [h_ptr_sz, h_prov, h_bv_nat, h_not_gt, h_ptr_eta]

theorem readScalar_ptr_none_roundtrip [DecidableEq P] [PointerProvenance P]
    (allocation : Allocation P E) (layout : TargetDataLayout)
    (range : AllocRange) (bits : U128)
    (h_init : allocation.initializationMask.isRangeInitialized range = .ok (.ok ()))
    (h_ptr_sz : range.size = Size.fromBits layout.pointerWidth.bits)
    (h_limit : range.size.bytes.toNat ≤ 16)
    (h_bits_bound : bits.toNat < 2 ^ (8 * range.size.bytes.toNat))
    (h_prov : allocation.provenanceMap.readPtr range.start
      (Size.fromBits layout.pointerWidth.bits) = .ok none)
    (h_slice : allocation.getBytesUnchecked range =
      .ok (Array.ofFn (fun i : Fin range.size.bytes.toNat =>
        UInt8.ofNat ((bits.toNat / 2 ^ (8 *
          (if layout.endian == .little then i.1 else range.size.bytes.toNat - i.1 - 1))) % 256)))) :
    allocation.readScalar layout range true =
      (Scalar.fromUInt bits range.size).mapError AllocError.scalar := by
  rw [readScalar_eq_R]
  unfold readScalarR pointerSize
  rw [getBytesUnchecked_eq] at h_slice
  have h_read := readTargetUInt_ofFn_mod layout range.size.bytes.toNat bits.toNat h_limit
  rw [Nat.mod_eq_of_lt h_bits_bound, BitVec.ofNat_toNat, BitVec.setWidth_eq] at h_read
  simp only [h_init, h_slice, Except.mapError, bind, Bind.bind, Except.bind, pure, Pure.pure, Except.pure]
  rw [h_read]
  simp [h_ptr_sz, h_prov]

theorem writeScalar_spec (layout : TargetDataLayout)
    (allocation : Allocation P E) (range : AllocRange) (value : Scalar P)
    (converted : ScalarBitsOrPointer P) (cleared nextProvenance : ProvenanceMap P)
    (storage : allocation.len = allocation.byteSize.bytes.toNat)
    (mutable : allocation.mutability = .Mut)
    (maskLength : allocation.initializationMask.len = allocation.byteSize)
    (maskValid : InitMask.WriteProof.WellFormed allocation.initializationMask)
    (nonzero : range.size.bytes ≠ 0)
    (width : range.size.bytes.toNat ≤ 16)
    (bound : range.start.bytes.toNat + range.size.bytes.toNat ≤ allocation.byteSize.bytes.toNat)
    (conversion : value.toBitsOrPtrInternal range.size = .ok converted)
    (clear : ∀ fullBytes : Array UInt8,
      allocation.getBytesUnchecked (allocRange Size.ZERO allocation.byteSize) = .ok fullBytes →
      allocation.provenanceMap.clear range fullBytes
        (Size.fromBits layout.pointerWidth.bits) = .ok () cleared)
    (insert : match converted with
      | .bits _ => nextProvenance = cleared
      | .pointer pointer => range.size = Size.fromBits layout.pointerWidth.bits ∧
          cleared.insertPtr range.start pointer.provenance
            (Size.fromBits layout.pointerWidth.bits) = .ok () nextProvenance) :
    ∃ updated,
      Allocation.writeScalar layout range value allocation = .ok () updated ∧
      updated.byteSize = allocation.byteSize ∧
      updated.len = allocation.len ∧
      updated.mutability = allocation.mutability ∧
      updated.align = allocation.align ∧
      updated.extra = allocation.extra ∧
      updated.nativeBuffer = allocation.nativeBuffer ∧
      updated.initializationMask.len = allocation.initializationMask.len ∧
      InitMask.WriteProof.WellFormed updated.initializationMask ∧
      allocation.initializationMask.setRange range true = .ok updated.initializationMask ∧
      updated.initializationMask.isRangeInitialized range = .ok (.ok ()) ∧
      updated.provenanceMap = nextProvenance ∧
      (∀ b, converted = .bits b →
        updated.getBytesUnchecked range =
          .ok (Array.ofFn (fun i : Fin range.size.bytes.toNat =>
            UInt8.ofNat ((b.toNat /
              2 ^ (8 * (if layout.endian == .little then i.1 else range.size.bytes.toNat - i.1 - 1))) % 256)))) ∧
      (∀ p, converted = .pointer p →
        updated.getBytesUnchecked range =
          .ok (Array.ofFn (fun i : Fin range.size.bytes.toNat =>
            UInt8.ofNat (((BitVec.ofNat 128 p.offset.bytes.toNat).toNat /
              2 ^ (8 * (if layout.endian == .little then i.1 else range.size.bytes.toNat - i.1 - 1))) % 256)))) ∧
      ∀ (qRange : AllocRange) (qFin : Size),
        qRange.endExclusive = .ok qFin →
        qRange.start.bytes.toNat ≤ qFin.bytes.toNat →
        qFin.bytes.toNat ≤ allocation.byteSize.bytes.toNat →
        (range.start.bytes.toNat + range.size.bytes.toNat ≤ qRange.start.bytes.toNat ∨
          qFin.bytes.toNat ≤ range.start.bytes.toNat) →
        updated.getBytesUnchecked qRange = allocation.getBytesUnchecked qRange := by
  have fits : range.start.bytes.toNat + range.size.bytes.toNat < 2 ^ 64 := by
    have := allocation.byteSize.bytes.toNat_lt; omega
  let finish := Size.ofBytes (range.start.bytes + range.size.bytes)
  have endpoint : range.endExclusive = .ok finish := by
    unfold AllocRange.endExclusive AllocRange.end
    exact congrArg (Except.mapError MemoryError.sizeError) (write_add_size range.start range.size fits)
  have finishNat : finish.bytes.toNat = range.start.bytes.toNat + range.size.bytes.toNat := by
    simp only [finish, Size.ofBytes, UInt64.toNat_add, Nat.mod_eq_of_lt fits]
  have positive : 0 < range.size.bytes.toNat := Nat.pos_of_ne_zero (by
    intro zero; exact nonzero (UInt64.toNat_inj.mp zero))
  obtain ⟨mask, maskOk, maskSize, maskWF⟩ :=
    InitMask.WriteProof.set_range_exists allocation.initializationMask range finish true
      maskValid endpoint (by omega) (by rw [maskLength]; simpa only [finishNat] using bound)
  have h_is_init : mask.isRangeInitialized range = .ok (.ok ()) :=
    InitMask.WriteProof.isRangeInitialized_after_setRange_true
      allocation.initializationMask mask range finish maskValid endpoint
      (by omega) (by rw [maskLength]; simpa only [finishNat] using bound) maskOk
  let bits : U128 := match converted with
    | .bits b => b
    | .pointer p => BitVec.ofNat 128 p.offset.bytes.toNat
  let data := Array.ofFn (fun i : Fin range.size.bytes.toNat =>
    UInt8.ofNat ((bits.toNat / 2 ^ (8 *
      (if layout.endian == .little then i.1 else range.size.bytes.toNat - i.1 - 1))) % 256))
  have dataOk : targetUIntBytes layout range.size bits = .ok data :=
    targetUIntBytes_eq_ofFn layout range.size bits width
  have dataSize : data.size = range.size.bytes.toNat := Array.size_ofFn ..
  let wStart := range.start.bytes.toNat
  let wFin := range.start.bytes.toNat + range.size.bytes.toNat
  let spliced := (raw allocation).extract 0 wStart ++ data ++
    (raw allocation).extract wFin (raw allocation).size
  have h_wFin_raw : wFin ≤ (raw allocation).size := by
    change wFin ≤ allocation.len; omega
  have bytesLength : spliced.size = allocation.byteSize.bytes.toNat := by
    simp only [spliced, Array.size_append, Array.size_extract,
      Nat.min_eq_left (by omega : wStart ≤ (raw allocation).size),
      Nat.min_self, Nat.sub_zero, dataSize]
    change _ = allocation.byteSize.bytes.toNat
    change (raw allocation).size = allocation.byteSize.bytes.toNat at storage
    omega
  have h_clear_raw : allocation.provenanceMap.clear range (raw allocation) (pointerSize layout) =
      .ok () cleared :=
    clear (raw allocation) (getBytesUnchecked_full_rawBytes allocation storage)
  let updated : Allocation P E :=
    mkAlloc spliced allocation.byteSize nextProvenance mask allocation.align
      allocation.mutability allocation.extra allocation.nativeBuffer
  have h_upd_storage : updated.len = updated.byteSize.bytes.toNat := bytesLength
  have h_get_data : updated.getBytesUnchecked range = .ok data := by
    rw [getBytesUnchecked_eq]
    have h_fin_ib : finish.bytes.toNat ≤ updated.byteSize.bytes.toNat := by
      change finish.bytes.toNat ≤ allocation.byteSize.bytes.toNat
      simpa only [finishNat] using bound
    rw [checkedSlice_ok updated range finish h_upd_storage endpoint (by omega) h_fin_ib]
    rw [finishNat]
    exact congrArg Except.ok
      (splice_extract_exact (raw allocation) data wStart wFin
        (by dsimp only [wStart, wFin]; omega) h_wFin_raw
        (by rw [dataSize]; dsimp only [wStart, wFin]; omega))
  refine ⟨updated, ?_, rfl, bytesLength.trans storage.symm, rfl, rfl, rfl, rfl,
    maskSize, maskWF, maskOk, h_is_init, rfl,
    fun b hb => by subst hb; exact h_get_data,
    fun p hp => by subst hp; exact h_get_data,
    ?_⟩
  · have slice := checkedSlice_ok allocation range finish storage endpoint (by omega)
      (by simpa only [finishNat] using bound)
    rw [writeScalar_eq_R]
    unfold writeScalarR
    simp only [mutable, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, conversion,
      Id.run, bind, Bind.bind, pure, Pure.pure]
    rw [slice, maskOk]
    rw [h_clear_raw]
    dsimp only [spliced, wStart, wFin] at bytesLength
    cases converted with
    | bits payload =>
      dsimp only [bits] at dataOk
      rw [dataOk]
      simp only [bytesLength, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
      subst insert
      rfl
    | pointer pointer =>
      dsimp only [bits] at dataOk
      rw [dataOk]
      simp only [bytesLength, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
      rcases insert with ⟨sizeEq, inserted⟩
      have sizeEq' : range.size = pointerSize layout := sizeEq
      have inserted' : cleared.insertPtr range.start pointer.provenance (pointerSize layout) =
          .ok () nextProvenance := inserted
      have h_sz_bne : (range.size != pointerSize layout) = false := by
        rw [sizeEq']
        exact bne_self_eq_false (pointerSize layout)
      simp only [h_sz_bne, Bool.false_eq_true, ↓reduceIte]
      rw [inserted']
      rfl
  · intro qRange qFin h_qend h_qlo h_qib h_disj
    rw [getBytesUnchecked_eq]
    have h_qib_upd : qFin.bytes.toNat ≤ updated.byteSize.bytes.toNat := h_qib
    rw [checkedSlice_ok updated qRange qFin h_upd_storage h_qend h_qlo h_qib_upd,
      checkedSlice_ok allocation qRange qFin storage h_qend h_qlo h_qib]
    have h_qfin_raw : qFin.bytes.toNat ≤ (raw allocation).size := by
      change qFin.bytes.toNat ≤ allocation.len; omega
    exact congrArg Except.ok
      (splice_extract_disjoint (raw allocation) data wStart wFin
        qRange.start.bytes.toNat qFin.bytes.toNat
        (by omega) h_wFin_raw h_qlo h_qfin_raw (by rw [dataSize]; omega) h_disj)

theorem writeBytes_zero_spec (start ptrSize : Size) (bytes : Array UInt8)
    (allocation : Allocation P E)
    (h_empty : bytes.size = 0)
    (storage : allocation.len = allocation.byteSize.bytes.toNat)
    (inBounds : start.bytes.toNat ≤ allocation.byteSize.bytes.toNat) :
    Allocation.writeBytes start bytes ptrSize allocation = .ok () allocation := by
  have h_sfa : sizeForArray 0 = .ok Size.ZERO := rfl
  have h_end : (allocRange start Size.ZERO).endExclusive = .ok start := by
    cases start
    simp [allocRange, AllocRange.endExclusive, AllocRange.end, Size.ZERO, Size.ofBytes, Size.add, Except.mapError]
  have h_slice := checkedSlice_ok allocation (allocRange start Size.ZERO) start storage h_end
    (Nat.le_refl _) inBounds
  rw [writeBytes_eq_R]
  unfold writeBytesR
  rw [h_empty, h_sfa]
  simp only [Id.run, bind, Bind.bind, pure, Pure.pure, h_slice]
  rfl

theorem writeBytes_spec (start ptrSize : Size) (bytes : Array UInt8)
    (allocation : Allocation P E) (nextProvenance : ProvenanceMap P)
    (h_nonempty : 0 < bytes.size)
    (storage : allocation.len = allocation.byteSize.bytes.toNat)
    (mutable : allocation.mutability = .Mut)
    (maskLength : allocation.initializationMask.len = allocation.byteSize)
    (maskValid : InitMask.WriteProof.WellFormed allocation.initializationMask)
    (inBounds : start.bytes.toNat + bytes.size ≤ allocation.byteSize.bytes.toNat)
    (clear : ∀ fullBytes : Array UInt8,
      allocation.getBytesUnchecked (allocRange Size.ZERO allocation.byteSize) = .ok fullBytes →
      allocation.provenanceMap.clear
        (allocRange start (Size.ofBytes (UInt64.ofNat bytes.size))) fullBytes ptrSize =
        .ok () nextProvenance) :
    ∃ updated,
      Allocation.writeBytes start bytes ptrSize allocation = .ok () updated ∧
      updated.byteSize = allocation.byteSize ∧
      updated.len = allocation.len ∧
      updated.mutability = allocation.mutability ∧
      updated.align = allocation.align ∧
      updated.extra = allocation.extra ∧
      updated.nativeBuffer = allocation.nativeBuffer ∧
      updated.initializationMask.len = allocation.initializationMask.len ∧
      InitMask.WriteProof.WellFormed updated.initializationMask ∧
      allocation.initializationMask.setRange
        (allocRange start (Size.ofBytes (UInt64.ofNat bytes.size))) true =
        .ok updated.initializationMask ∧
      updated.initializationMask.isRangeInitialized
        (allocRange start (Size.ofBytes (UInt64.ofNat bytes.size))) = .ok (.ok ()) ∧
      updated.provenanceMap = nextProvenance ∧
      updated.getBytesUnchecked (allocRange start (Size.ofBytes (UInt64.ofNat bytes.size))) =
        .ok bytes ∧
      ∀ (qRange : AllocRange) (qFin : Size),
        qRange.endExclusive = .ok qFin →
        qRange.start.bytes.toNat ≤ qFin.bytes.toNat →
        qFin.bytes.toNat ≤ allocation.byteSize.bytes.toNat →
        (start.bytes.toNat + bytes.size ≤ qRange.start.bytes.toNat ∨
          qFin.bytes.toNat ≤ start.bytes.toNat) →
        updated.getBytesUnchecked qRange = allocation.getBytesUnchecked qRange := by
  have h_u64_alloc := allocation.byteSize.bytes.toNat_lt
  have h_bsz_lt : bytes.size < 2 ^ 64 := by omega
  have h_not_gt_max : ¬(bytes.size > maxU64Nat) := by unfold maxU64Nat; omega
  let writeSize := Size.ofBytes (UInt64.ofNat bytes.size)
  have h_wsz_nat : writeSize.bytes.toNat = bytes.size := by
    simp [writeSize, Size.ofBytes, UInt64.toNat_ofNat', Nat.mod_eq_of_lt h_bsz_lt]
  have h_sfa : sizeForArray bytes.size = .ok writeSize := by
    unfold sizeForArray
    simp [h_not_gt_max, h_wsz_nat, writeSize, pure, Pure.pure, Except.pure]
  have h_wsz_nz : (writeSize.bytes == 0) = false := by
    apply beq_false_of_ne
    intro h0
    have : writeSize.bytes.toNat = 0 := by simp [h0]
    omega
  let range := allocRange start writeSize
  have fits : start.bytes.toNat + writeSize.bytes.toNat < 2 ^ 64 := by omega
  let finish := Size.ofBytes (start.bytes + writeSize.bytes)
  have endpoint : range.endExclusive = .ok finish := by
    unfold AllocRange.endExclusive AllocRange.end range allocRange
    exact congrArg (Except.mapError MemoryError.sizeError) (write_add_size start writeSize fits)
  have finishNat : finish.bytes.toNat = start.bytes.toNat + bytes.size := by
    have h_def : finish.bytes.toNat = (start.bytes + writeSize.bytes).toNat := rfl
    rw [h_def, UInt64.toNat_add, Nat.mod_eq_of_lt fits, h_wsz_nat]
  obtain ⟨mask, maskOk, maskSize, maskWF⟩ :=
    InitMask.WriteProof.set_range_exists allocation.initializationMask range finish true
      maskValid endpoint (by dsimp only [range, allocRange]; omega)
      (by rw [maskLength]; omega)
  have h_is_init : mask.isRangeInitialized range = .ok (.ok ()) :=
    InitMask.WriteProof.isRangeInitialized_after_setRange_true
      allocation.initializationMask mask range finish maskValid endpoint
      (by dsimp only [range, allocRange]; omega) (by rw [maskLength]; omega) maskOk
  have h_slice := checkedSlice_ok allocation range finish storage endpoint
    (by dsimp only [range, allocRange]; omega) (by omega)
  have h_clear_raw : allocation.provenanceMap.clear range (raw allocation) ptrSize =
      .ok () nextProvenance :=
    clear (raw allocation) (getBytesUnchecked_full_rawBytes allocation storage)
  let wStart := start.bytes.toNat
  let wFin := finish.bytes.toNat
  let spliced := (raw allocation).extract 0 wStart ++ bytes ++
    (raw allocation).extract wFin (raw allocation).size
  have h_wFin_raw : wFin ≤ (raw allocation).size := by
    change wFin ≤ allocation.len; omega
  have bytesLength : spliced.size = allocation.byteSize.bytes.toNat := by
    simp only [spliced, Array.size_append, Array.size_extract,
      Nat.min_eq_left (by omega : wStart ≤ (raw allocation).size),
      Nat.min_self, Nat.sub_zero]
    change _ = allocation.byteSize.bytes.toNat
    change (raw allocation).size = allocation.byteSize.bytes.toNat at storage
    omega
  let updated : Allocation P E :=
    mkAlloc spliced allocation.byteSize nextProvenance mask allocation.align
      allocation.mutability allocation.extra allocation.nativeBuffer
  have h_upd_storage : updated.len = updated.byteSize.bytes.toNat := bytesLength
  refine ⟨updated, ?_, rfl, bytesLength.trans storage.symm, rfl, rfl, rfl, rfl,
    maskSize, maskWF, maskOk, h_is_init, rfl, ?_, ?_⟩
  · dsimp only [range] at maskOk h_clear_raw endpoint h_slice
    rw [writeBytes_eq_R]
    unfold writeBytesR setInitialization overwriteRawBytes
    rw [h_sfa]
    dsimp only [Id.run, bind, Bind.bind, pure, Pure.pure]
    change (match checkedSlice allocation (allocRange start writeSize) with
      | .error reason => EStateM.Result.error reason allocation
      | .ok _ => _) = _
    rw [h_slice]
    simp only [h_wsz_nz, Bool.false_eq_true, ↓reduceIte, mutable, bne_self_eq_false,
      maskOk, Except.mapError, Except.bind, Except.pure, raw_withInitMask, provenanceMap_withInitMask]
    rw [h_clear_raw]
    dsimp only
    rw [endpoint]
    dsimp only [Except.mapError, Except.bind, allocRange]
    have h_len_chk : (spliced.size != allocation.byteSize.bytes.toNat) = false := by
      change (spliced.size != allocation.byteSize.bytes.toNat) = false
      rw [bytesLength]
      exact bne_self_eq_false _
    dsimp only [spliced, wStart, wFin, allocRange] at h_len_chk
    simp only [raw_withProvenance, raw_withInitMask, byteSize_withProvenance, byteSize_withInitMask]
    simp only [h_len_chk, Bool.false_eq_true, ↓reduceIte]
    rfl
  · rw [getBytesUnchecked_eq]
    have h_fin_ib : finish.bytes.toNat ≤ updated.byteSize.bytes.toNat := by
      change finish.bytes.toNat ≤ allocation.byteSize.bytes.toNat; omega
    rw [checkedSlice_ok updated range finish h_upd_storage endpoint
      (by dsimp only [range, allocRange]; omega) h_fin_ib]
    exact congrArg Except.ok
      (splice_extract_exact (raw allocation) bytes wStart wFin
        (by omega) h_wFin_raw (by omega))
  · intro qRange qFin h_qend h_qlo h_qib h_disj
    rw [getBytesUnchecked_eq]
    have h_qib_upd : qFin.bytes.toNat ≤ updated.byteSize.bytes.toNat := h_qib
    rw [checkedSlice_ok updated qRange qFin h_upd_storage h_qend h_qlo h_qib_upd,
      checkedSlice_ok allocation qRange qFin storage h_qend h_qlo h_qib]
    have h_qfin_raw : qFin.bytes.toNat ≤ (raw allocation).size := by
      change qFin.bytes.toNat ≤ allocation.len; omega
    exact congrArg Except.ok
      (splice_extract_disjoint (raw allocation) bytes wStart wFin
        qRange.start.bytes.toNat qFin.bytes.toNat
        (by omega) h_wFin_raw h_qlo h_qfin_raw (by omega)
        (by dsimp only [wStart, wFin]; omega))

theorem writeUninit_zero_spec (range : AllocRange) (finish ptrSize : Size)
    (allocation : Allocation P E)
    (h_zero : range.size.bytes = 0)
    (storage : allocation.len = allocation.byteSize.bytes.toNat)
    (endEq : range.endExclusive = .ok finish)
    (startLe : range.start.bytes.toNat ≤ finish.bytes.toNat)
    (inBounds : finish.bytes.toNat ≤ allocation.byteSize.bytes.toNat) :
    Allocation.writeUninit range ptrSize allocation = .ok () allocation := by
  have h_slice := checkedSlice_ok allocation range finish storage endEq startLe inBounds
  rw [writeUninit_eq_R]
  unfold writeUninitR
  simp [h_slice, h_zero, Id.run, pure, Pure.pure]

theorem writeUninit_spec (range : AllocRange) (ptrSize : Size)
    (allocation : Allocation P E) (nextProvenance : ProvenanceMap P)
    (nonzero : range.size.bytes ≠ 0)
    (storage : allocation.len = allocation.byteSize.bytes.toNat)
    (mutable : allocation.mutability = .Mut)
    (maskLength : allocation.initializationMask.len = allocation.byteSize)
    (maskValid : InitMask.WriteProof.WellFormed allocation.initializationMask)
    (inBounds : range.start.bytes.toNat + range.size.bytes.toNat ≤ allocation.byteSize.bytes.toNat)
    (clear : ∀ fullBytes : Array UInt8,
      allocation.getBytesUnchecked (allocRange Size.ZERO allocation.byteSize) = .ok fullBytes →
      allocation.provenanceMap.clear range fullBytes ptrSize = .ok () nextProvenance) :
    ∃ updated,
      Allocation.writeUninit range ptrSize allocation = .ok () updated ∧
      updated.byteSize = allocation.byteSize ∧
      updated.len = allocation.len ∧
      updated.mutability = allocation.mutability ∧
      updated.align = allocation.align ∧
      updated.extra = allocation.extra ∧
      updated.nativeBuffer = allocation.nativeBuffer ∧
      updated.initializationMask.len = allocation.initializationMask.len ∧
      InitMask.WriteProof.WellFormed updated.initializationMask ∧
      allocation.initializationMask.setRange range false = .ok updated.initializationMask ∧
      updated.provenanceMap = nextProvenance ∧
      ∀ (anyRange : AllocRange),
        updated.getBytesUnchecked anyRange = allocation.getBytesUnchecked anyRange := by
  have fits : range.start.bytes.toNat + range.size.bytes.toNat < 2 ^ 64 := by
    have := allocation.byteSize.bytes.toNat_lt; omega
  let finish := Size.ofBytes (range.start.bytes + range.size.bytes)
  have endpoint : range.endExclusive = .ok finish := by
    unfold AllocRange.endExclusive AllocRange.end
    exact congrArg (Except.mapError MemoryError.sizeError) (write_add_size range.start range.size fits)
  have finishNat : finish.bytes.toNat = range.start.bytes.toNat + range.size.bytes.toNat := by
    simp only [finish, Size.ofBytes, UInt64.toNat_add, Nat.mod_eq_of_lt fits]
  have positive : 0 < range.size.bytes.toNat := Nat.pos_of_ne_zero (by
    intro zero; exact nonzero (UInt64.toNat_inj.mp zero))
  obtain ⟨mask, maskOk, maskSize, maskWF⟩ :=
    InitMask.WriteProof.set_range_exists allocation.initializationMask range finish false
      maskValid endpoint (by omega) (by rw [maskLength]; simpa only [finishNat] using inBounds)
  have h_slice := checkedSlice_ok allocation range finish storage endpoint (by omega)
    (by simpa only [finishNat] using inBounds)
  have h_clear_raw : allocation.provenanceMap.clear range (raw allocation) ptrSize =
      .ok () nextProvenance :=
    clear (raw allocation) (getBytesUnchecked_full_rawBytes allocation storage)
  let updated : Allocation P E :=
    mkAlloc (raw allocation) allocation.byteSize nextProvenance mask allocation.align
      allocation.mutability allocation.extra allocation.nativeBuffer
  refine ⟨updated, ?_, rfl, rfl, rfl, rfl, rfl, rfl, maskSize, maskWF, maskOk, rfl, fun _ => rfl⟩
  have h_nz_beq : (range.size.bytes == 0) = false := beq_false_of_ne nonzero
  rw [writeUninit_eq_R]
  unfold writeUninitR setInitialization
  simp only [Id.run, bind, Bind.bind, pure, Pure.pure, h_slice, h_nz_beq,
    Bool.false_eq_true, ↓reduceIte, mutable, bne_self_eq_false,
    maskOk, Except.mapError, Except.bind, Except.pure, raw_withInitMask, provenanceMap_withInitMask]
  rw [h_clear_raw]
  rfl

theorem copyRepeatedly_initialized_spec
    (source state : Allocation P E)
    (sourceRange : AllocRange) (srcFinish destStart totalSize ptrSize : Size)
    (repeatCount : UInt64) (sameAllocation nonoverlapping : Bool)
    (srcBytes : Array UInt8) (provCopy : ProvenanceCopy P)
    (clearedProv finalProv : ProvenanceMap P)
    (srcStorage : source.len = source.byteSize.bytes.toNat)
    (srcEnd : sourceRange.endExclusive = .ok srcFinish)
    (srcNonzero : sourceRange.size.bytes ≠ 0)
    (srcMaskLen : source.initializationMask.len = source.byteSize)
    (srcMaskWF : InitMask.WriteProof.WellFormed source.initializationMask)
    (srcInit : source.initializationMask.isRangeInitialized sourceRange = .ok (.ok ()))
    (srcSlice : source.getBytesUnchecked sourceRange = .ok srcBytes)
    (srcInBounds : srcFinish.bytes.toNat ≤ source.byteSize.bytes.toNat)
    (h_prepProv : ∀ srcFull : Array UInt8,
      source.getBytesUnchecked (allocRange Size.ZERO source.byteSize) = .ok srcFull →
      source.provenanceMap.prepareCopy sourceRange srcFull ptrSize = .ok provCopy)
    (h_repPos : 0 < repeatCount.toNat)
    (h_mul : Size.mul sourceRange.size repeatCount = .ok totalSize)
    (h_repMode : repeatCount > 1 → nonoverlapping = true)
    (h_disjSame : sameAllocation = true → nonoverlapping = true →
      srcFinish.bytes.toNat ≤ destStart.bytes.toNat ∨
        destStart.bytes.toNat + sourceRange.size.bytes.toNat ≤ sourceRange.start.bytes.toNat)
    (destStorage : state.len = state.byteSize.bytes.toNat)
    (destMut : state.mutability = .Mut)
    (destMaskLen : state.initializationMask.len = state.byteSize)
    (destMaskWF : InitMask.WriteProof.WellFormed state.initializationMask)
    (destInBounds : destStart.bytes.toNat + totalSize.bytes.toNat ≤ state.byteSize.bytes.toNat)
    (h_clearProv : ∀ stFull : Array UInt8,
      state.getBytesUnchecked (allocRange Size.ZERO state.byteSize) = .ok stFull →
      state.provenanceMap.clear (allocRange destStart totalSize) stFull ptrSize =
        .ok () clearedProv)
    (h_applyProv : clearedProv.applyCopy provCopy
      (allocRange destStart sourceRange.size) repeatCount = .ok () finalProv) :
    ∃ updated,
      Allocation.copyRepeatedly source sourceRange destStart repeatCount
        ptrSize sameAllocation nonoverlapping state = .ok () updated ∧
      updated.byteSize = state.byteSize ∧
      updated.len = state.len ∧
      updated.mutability = state.mutability ∧
      updated.align = state.align ∧
      updated.extra = state.extra ∧
      updated.nativeBuffer = state.nativeBuffer ∧
      updated.initializationMask.len = state.initializationMask.len ∧
      InitMask.WriteProof.WellFormed updated.initializationMask ∧
      updated.initializationMask.isRangeInitialized (allocRange destStart totalSize) = .ok (.ok ()) ∧
      (∀ (idx : Size), idx.bytes.toNat < state.byteSize.bytes.toNat →
        updated.initializationMask.get idx =
          if destStart.bytes.toNat ≤ idx.bytes.toNat ∧
              idx.bytes.toNat < destStart.bytes.toNat + totalSize.bytes.toNat then
            .ok true
          else
            state.initializationMask.get idx) ∧
      (∀ (qRange : AllocRange) (qFin : Size),
        qRange.endExclusive = .ok qFin →
        qRange.start.bytes.toNat < qFin.bytes.toNat →
        qFin.bytes.toNat ≤ state.byteSize.bytes.toNat →
        (destStart.bytes.toNat + totalSize.bytes.toNat ≤ qRange.start.bytes.toNat ∨
          qFin.bytes.toNat ≤ destStart.bytes.toNat) →
        (updated.initializationMask.isRangeInitialized qRange = .ok (.ok ()) ↔
          state.initializationMask.isRangeInitialized qRange = .ok (.ok ()))) ∧
      updated.provenanceMap = finalProv ∧
      updated.getBytesUnchecked (allocRange destStart totalSize) =
        .ok ((List.replicate repeatCount.toNat srcBytes.toList).flatten.toArray) ∧
      ∀ (qRange : AllocRange) (qFin : Size),
        qRange.endExclusive = .ok qFin →
        qRange.start.bytes.toNat ≤ qFin.bytes.toNat →
        qFin.bytes.toNat ≤ state.byteSize.bytes.toNat →
        (destStart.bytes.toNat + totalSize.bytes.toNat ≤ qRange.start.bytes.toNat ∨
          qFin.bytes.toNat ≤ destStart.bytes.toNat) →
        updated.getBytesUnchecked qRange = state.getBytesUnchecked qRange := by
  have h_src_pos : 0 < sourceRange.size.bytes.toNat := Nat.pos_of_ne_zero (by
    intro h0; exact srcNonzero (UInt64.toNat_inj.mp h0))
  have h_src_fits : sourceRange.start.bytes.toNat + sourceRange.size.bytes.toNat < 2 ^ 64 := by
    unfold AllocRange.endExclusive AllocRange.end Size.add at srcEnd
    by_cases hw : sourceRange.start.bytes + sourceRange.size.bytes < sourceRange.start.bytes
    · simp [hw, Except.mapError] at srcEnd
    · have hnw : ¬((sourceRange.start.bytes + sourceRange.size.bytes).toNat <
          sourceRange.start.bytes.toNat) := by simpa [UInt64.lt_iff_toNat_lt] using hw
      have := sourceRange.start.bytes.toNat_lt
      have := sourceRange.size.bytes.toNat_lt
      by_cases hlt : sourceRange.start.bytes.toNat + sourceRange.size.bytes.toNat < 2 ^ 64
      · exact hlt
      · rw [UInt64.toNat_add] at hnw; omega
  have h_srcFin_nat : srcFinish.bytes.toNat =
      sourceRange.start.bytes.toNat + sourceRange.size.bytes.toNat := by
    unfold AllocRange.endExclusive AllocRange.end Size.add at srcEnd
    by_cases hw : sourceRange.start.bytes + sourceRange.size.bytes < sourceRange.start.bytes
    · simp [hw, Except.mapError] at srcEnd
    · simp only [hw, ↓reduceIte, Except.mapError, Except.ok.injEq] at srcEnd
      subst srcEnd
      simp only [Size.ofBytes, UInt64.toNat_add, Nat.mod_eq_of_lt h_src_fits]
  have h_srcBytes_sz : srcBytes.size = sourceRange.size.bytes.toNat := by
    have hs := checkedSlice_ok source sourceRange srcFinish srcStorage srcEnd (by omega) srcInBounds
    rw [getBytesUnchecked_eq] at srcSlice
    rw [hs] at srcSlice
    injection srcSlice with h_eq
    subst h_eq
    have h_f_raw : srcFinish.bytes.toNat ≤ (raw source).size := by
      change srcFinish.bytes.toNat ≤ source.len; omega
    rw [Array.size_extract, Nat.min_eq_left h_f_raw, h_srcFin_nat]
    omega
  have h_mul_nat : totalSize.bytes.toNat =
      sourceRange.size.bytes.toNat * repeatCount.toNat := by
    unfold Size.mul at h_mul
    have h_rc_nz : (repeatCount != 0) = true := by
      apply bne_iff_ne.mpr
      intro h0; simp [h0] at h_repPos
    by_cases h_ovf : (sourceRange.size.bytes * repeatCount) / repeatCount != sourceRange.size.bytes
    · simp [h_rc_nz, h_ovf] at h_mul
    · simp only [h_rc_nz, Bool.true_and, h_ovf, Bool.false_eq_true, ↓reduceIte, Except.ok.injEq] at h_mul
      subst h_mul
      have h_div_eq : (sourceRange.size.bytes * repeatCount) / repeatCount = sourceRange.size.bytes :=
        eq_of_not_bne h_ovf
      have h_prod_lt : sourceRange.size.bytes.toNat * repeatCount.toNat < 2 ^ 64 := by
        have h_le_u64 := (sourceRange.size.bytes * repeatCount).toNat_lt
        have h_div_nat : ((sourceRange.size.bytes * repeatCount) / repeatCount).toNat =
            (sourceRange.size.bytes * repeatCount).toNat / repeatCount.toNat := UInt64.toNat_div ..
        rw [h_div_eq] at h_div_nat
        have := Nat.mul_le_of_le_div repeatCount.toNat _ _ (Nat.le_of_eq h_div_nat)
        have h_rem := Nat.div_add_mod (sourceRange.size.bytes * repeatCount).toNat repeatCount.toNat
        omega
      simp only [Size.ofBytes, UInt64.toNat_mul, Nat.mod_eq_of_lt h_prod_lt]
  have h_tot_pos : 0 < totalSize.bytes.toNat := by
    rw [h_mul_nat]; exact Nat.mul_pos h_src_pos h_repPos
  have h_tot_nz : (totalSize.bytes == 0) = false := by
    apply beq_false_of_ne
    intro h0; have : totalSize.bytes.toNat = 0 := by simp [h0]
    omega
  let destRange := allocRange destStart totalSize
  have h_dest_fits : destStart.bytes.toNat + totalSize.bytes.toNat < 2 ^ 64 := by
    have := state.byteSize.bytes.toNat_lt; omega
  let destFinish := Size.ofBytes (destStart.bytes + totalSize.bytes)
  have destEnd : destRange.endExclusive = .ok destFinish := by
    unfold AllocRange.endExclusive AllocRange.end destRange allocRange
    exact congrArg (Except.mapError MemoryError.sizeError) (write_add_size destStart totalSize h_dest_fits)
  have h_destFin_nat : destFinish.bytes.toNat = destStart.bytes.toNat + totalSize.bytes.toNat := by
    simp only [destFinish, Size.ofBytes, UInt64.toNat_add, Nat.mod_eq_of_lt h_dest_fits]
  have h_src_unif : ∀ idx : Size, sourceRange.start.bytes.toNat ≤ idx.bytes.toNat →
      idx.bytes.toNat < srcFinish.bytes.toNat → source.initializationMask.get idx = .ok true :=
    (InitMask.WriteProof.isRangeInitialized_nonempty_iff source.initializationMask
      sourceRange srcFinish srcMaskWF srcEnd (by omega)
      (by rw [srcMaskLen]; exact srcInBounds)).1.mp srcInit
  have h_prep_init : source.initializationMask.prepareCopy sourceRange =
      .ok ⟨true, #[sourceRange.size.bytes]⟩ :=
    InitMask.WriteProof.prepareCopy_of_uniform source.initializationMask
      sourceRange srcFinish true srcMaskWF srcEnd (by omega)
      (by rw [srcMaskLen]; exact srcInBounds) h_src_unif
  have h_prep_prov : source.provenanceMap.prepareCopy sourceRange (raw source) ptrSize = .ok provCopy :=
    h_prepProv (raw source) (getBytesUnchecked_full_rawBytes source srcStorage)
  obtain ⟨mask1, mask1Ok, mask1Len, mask1WF⟩ :=
    InitMask.WriteProof.set_range_exists state.initializationMask destRange destFinish true
      destMaskWF destEnd (by dsimp only [destRange, allocRange]; omega)
      (by rw [destMaskLen]; omega)
  obtain ⟨mask2, mask2Ok, mask2Len, mask2WF⟩ :=
    InitMask.WriteProof.set_range_exists mask1 destRange destFinish true
      mask1WF destEnd (by dsimp only [destRange, allocRange]; omega)
      (by rw [mask1Len, destMaskLen]; omega)
  have h_apply_init : mask1.applyCopy ⟨true, #[sourceRange.size.bytes]⟩
      (allocRange destStart sourceRange.size) repeatCount = .ok mask2 := by
    rw [InitMask.WriteProof.applyCopy_singleton mask1 destStart sourceRange.size totalSize
      repeatCount true srcNonzero h_mul]
    exact mask2Ok
  have h_mask2_isInit : mask2.isRangeInitialized destRange = .ok (.ok ()) :=
    InitMask.WriteProof.isRangeInitialized_after_setRange_true mask1 mask2 destRange destFinish
      mask1WF destEnd (by dsimp only [destRange, allocRange]; omega)
      (by rw [mask1Len, destMaskLen]; omega) mask2Ok
  have h_clear_raw : state.provenanceMap.clear destRange (raw state) ptrSize = .ok () clearedProv :=
    h_clearProv (raw state) (getBytesUnchecked_full_rawBytes state destStorage)
  have h_srcSlice_chk : checkedSlice source sourceRange = .ok srcBytes := srcSlice
  have h_destSlice_chk := checkedSlice_ok state destRange destFinish destStorage destEnd
    (by dsimp only [destRange, allocRange]; omega) (by omega)
  let copiedBytes := (List.replicate repeatCount.toNat srcBytes.toList).flatten.toArray
  have h_rep_loop : ∀ (k s : Nat) (acc : Array UInt8),
      forIn (m := Id) (List.range' s k) acc (fun _ cur =>
        pure (ForInStep.yield (cur ++ srcBytes))) =
      acc ++ (List.replicate k srcBytes.toList).flatten.toArray := by
    intro k
    induction k with
    | zero =>
      intro s acc
      simp [List.range', List.forIn_nil, pure, Pure.pure]
    | succ m ih =>
      intro s acc
      rw [List.range'_succ, List.forIn_cons]
      change forIn (m := Id) (List.range' (s + 1) m) (acc ++ srcBytes)
        (fun _ cur => pure (ForInStep.yield (cur ++ srcBytes))) = _
      rw [ih (s + 1) (acc ++ srcBytes)]
      apply Array.ext
      · simp [Array.size_append, List.replicate_succ]
      · intro i hi1 hi2
        have h_toList : (acc ++ srcBytes ++ (List.replicate m srcBytes.toList).flatten.toArray).toList =
            (acc ++ (List.replicate (m + 1) srcBytes.toList).flatten.toArray).toList := by
          simp [Array.toList_append, List.replicate_succ]
        exact List.getElem_of_eq h_toList _
  have h_copied_sz : copiedBytes.size = totalSize.bytes.toNat := by
    have h_len : (List.replicate repeatCount.toNat srcBytes.toList).flatten.length =
        repeatCount.toNat * srcBytes.size := by
      induction repeatCount.toNat with
      | zero => simp
      | succ m ih => simp [List.replicate_succ, ih, Nat.succ_mul, Nat.add_comm]
    simp [copiedBytes, h_len, h_srcBytes_sz, h_mul_nat, Nat.mul_comm]
  let wStart := destStart.bytes.toNat
  let wFin := destFinish.bytes.toNat
  let spliced := (raw state).extract 0 wStart ++ copiedBytes ++
    (raw state).extract wFin (raw state).size
  have h_wFin_raw : wFin ≤ (raw state).size := by
    change wFin ≤ state.len; omega
  have bytesLength : spliced.size = state.byteSize.bytes.toNat := by
    simp only [spliced, Array.size_append, Array.size_extract,
      Nat.min_eq_left (by omega : wStart ≤ (raw state).size),
      Nat.min_self, Nat.sub_zero, h_copied_sz]
    change _ = state.byteSize.bytes.toNat
    change (raw state).size = state.byteSize.bytes.toNat at destStorage
    omega
  let updated : Allocation P E :=
    mkAlloc spliced state.byteSize finalProv mask2 state.align
      state.mutability state.extra state.nativeBuffer
  have h_upd_storage : updated.len = updated.byteSize.bytes.toNat := bytesLength
  have h_mask_get_frame : ∀ (idx : Size), idx.bytes.toNat < state.byteSize.bytes.toNat →
      mask2.get idx =
        if destStart.bytes.toNat ≤ idx.bytes.toNat ∧
            idx.bytes.toNat < destStart.bytes.toNat + totalSize.bytes.toNat then
          .ok true
        else
          state.initializationMask.get idx := by
    intro idx h_idx_lt
    have h_g2 := InitMask.WriteProof.set_range_get mask1 mask2 destRange destFinish idx true
      mask1WF destEnd (by dsimp only [destRange, allocRange]; omega)
      (by rw [mask1Len, destMaskLen]; omega)
      (by rw [mask1Len, destMaskLen]; exact h_idx_lt) mask2Ok
    have h_g1 := InitMask.WriteProof.set_range_get state.initializationMask mask1
      destRange destFinish idx true destMaskWF destEnd
      (by dsimp only [destRange, allocRange]; omega)
      (by rw [destMaskLen]; omega)
      (by rw [destMaskLen]; exact h_idx_lt) mask1Ok
    have h_dr_start : destRange.start = destStart := rfl
    rw [h_dr_start, h_destFin_nat] at h_g2 h_g1
    by_cases h_in : destStart.bytes.toNat ≤ idx.bytes.toNat ∧
        idx.bytes.toNat < destStart.bytes.toNat + totalSize.bytes.toNat
    · rw [if_pos_eq h_in] at h_g2 ⊢; exact h_g2
    · rw [if_neg_eq h_in] at h_g2 h_g1 ⊢; exact h_g2.trans h_g1
  have h_mask_range_frame : ∀ (qRange : AllocRange) (qFin : Size),
      qRange.endExclusive = .ok qFin →
      qRange.start.bytes.toNat < qFin.bytes.toNat →
      qFin.bytes.toNat ≤ state.byteSize.bytes.toNat →
      (destStart.bytes.toNat + totalSize.bytes.toNat ≤ qRange.start.bytes.toNat ∨
        qFin.bytes.toNat ≤ destStart.bytes.toNat) →
      (mask2.isRangeInitialized qRange = .ok (.ok ()) ↔
        state.initializationMask.isRangeInitialized qRange = .ok (.ok ())) := by
    intro qRange qFin h_qend h_qne h_qib h_disj
    have h_disj' : destFinish.bytes.toNat ≤ qRange.start.bytes.toNat ∨
        qFin.bytes.toNat ≤ destRange.start.bytes.toNat := by
      dsimp only [destRange, allocRange]; omega
    exact (InitMask.WriteProof.isRangeInitialized_frame mask1 mask2 destRange qRange
      destFinish qFin true mask1WF destEnd h_qend
      (by dsimp only [destRange, allocRange]; omega) h_qne
      (by rw [mask1Len, destMaskLen]; omega)
      (by rw [mask1Len, destMaskLen]; exact h_qib) h_disj' mask2Ok).trans
      (InitMask.WriteProof.isRangeInitialized_frame state.initializationMask mask1 destRange qRange
        destFinish qFin true destMaskWF destEnd h_qend
        (by dsimp only [destRange, allocRange]; omega) h_qne
        (by rw [destMaskLen]; omega)
        (by rw [destMaskLen]; exact h_qib) h_disj' mask1Ok)
  refine ⟨updated, ?_, rfl, bytesLength.trans destStorage.symm, rfl, rfl, rfl, rfl,
    mask2Len.trans mask1Len, mask2WF, h_mask2_isInit, h_mask_get_frame, h_mask_range_frame,
    rfl, ?_, ?_⟩
  · rw [copyRepeatedly_eq_R]
    unfold copyRepeatedlyR prepareForOverwrite setInitialization
      runProvenanceMutation overwriteRawBytes
    simp only [Id.run, bind, Bind.bind, pure, Pure.pure,
      h_srcSlice_chk, h_mul, h_prep_prov, h_prep_init]
    dsimp only [destRange, allocRange] at h_destSlice_chk mask1Ok h_clear_raw destEnd ⊢
    simp only [h_destSlice_chk, h_tot_nz, Bool.false_eq_true, ↓reduceIte,
      destMut, bne_self_eq_false, mask1Ok, Except.mapError, Except.bind, Except.pure,
      h_clear_raw, InitCopy.noBytesInit, Bool.not_true, Bool.false_and,
      raw_withInitMask, raw_withProvenance, byteSize_withInitMask, byteSize_withProvenance,
      provenanceMap_withInitMask]
    have h_first_fits : destStart.bytes.toNat + sourceRange.size.bytes.toNat < 2 ^ 64 := by
      have : sourceRange.size.bytes.toNat * 1 ≤ sourceRange.size.bytes.toNat * repeatCount.toNat :=
        Nat.mul_le_mul_left _ h_repPos
      omega
    let firstFin := Size.ofBytes (destStart.bytes + sourceRange.size.bytes)
    have h_first_end : (allocRange destStart sourceRange.size).endExclusive = .ok firstFin := by
      unfold AllocRange.endExclusive AllocRange.end allocRange
      exact congrArg (Except.mapError MemoryError.sizeError)
        (write_add_size destStart sourceRange.size h_first_fits)
    have h_first_nat : firstFin.bytes.toNat = destStart.bytes.toNat + sourceRange.size.bytes.toNat := by
      simp only [firstFin, Size.ofBytes, UInt64.toNat_add, Nat.mod_eq_of_lt h_first_fits]
    have h_rep_chk : (repeatCount > 1 && !nonoverlapping) = false := by
      by_cases h_gt1 : repeatCount > 1
      · simp [h_gt1, h_repMode h_gt1]
      · simp [h_gt1]
    have h_rc_nz_beq : (repeatCount == 0) = false := by
      apply beq_false_of_ne; intro h0; simp [h0] at h_repPos
    have h_len_ne : (spliced.size != state.byteSize.bytes.toNat) = false := by
      change (spliced.size != state.byteSize.bytes.toNat) = false
      rw [bytesLength]; exact bne_self_eq_false _
    dsimp only [spliced, wStart, wFin, copiedBytes] at h_len_ne
    dsimp only [allocRange] at h_first_end h_apply_init h_applyProv
    by_cases h_sn : (sameAllocation && nonoverlapping) = true
    · simp only [Bool.and_eq_true] at h_sn
      have h_d := h_disjSame h_sn.1 h_sn.2
      have h_no_ovl : ¬(sourceRange.start.bytes < firstFin.bytes ∧ destStart.bytes < srcFinish.bytes) := by
        simp only [UInt64.lt_iff_toNat_lt]; omega
      simp only [h_sn, Bool.and_self, ↓reduceIte, srcEnd, h_first_end, h_no_ovl,
        decide_eq_true_eq, Bool.and_eq_true, Bool.false_eq_true,
        h_rc_nz_beq, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false,
        Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
        Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
      have h_loop_inst := h_rep_loop repeatCount.toNat 0 #[]
      dsimp only [pure, Pure.pure] at h_loop_inst
      rw [h_loop_inst]
      simp only [Array.empty_append, destEnd]
      simp only [h_len_ne, Bool.false_eq_true, ↓reduceIte, h_apply_init, h_applyProv,
        provenanceMap_withProvenance, provenanceMap_withRawBytes,
        initializationMask_withInitMask, initializationMask_withProvenance,
        initializationMask_withRawBytes]
      rfl
    · simp only [h_sn, Bool.false_eq_true, ↓reduceIte, h_rep_chk,
        h_rc_nz_beq, Bool.not_false, Bool.false_and, Bool.and_false,
        Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
        Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
      have h_loop_inst := h_rep_loop repeatCount.toNat 0 #[]
      dsimp only [pure, Pure.pure] at h_loop_inst
      rw [h_loop_inst]
      simp only [Array.empty_append, destEnd]
      simp only [h_len_ne, Bool.false_eq_true, ↓reduceIte, h_apply_init, h_applyProv,
        provenanceMap_withProvenance, provenanceMap_withRawBytes,
        initializationMask_withInitMask, initializationMask_withProvenance,
        initializationMask_withRawBytes]
      rfl
  · rw [getBytesUnchecked_eq]
    have h_destFin_ib : destFinish.bytes.toNat ≤ updated.byteSize.bytes.toNat := by
      change destFinish.bytes.toNat ≤ state.byteSize.bytes.toNat; omega
    rw [checkedSlice_ok updated destRange destFinish h_upd_storage destEnd
      (by dsimp only [destRange, allocRange]; omega) h_destFin_ib]
    exact congrArg Except.ok
      (splice_extract_exact (raw state) copiedBytes wStart wFin
        (by omega) h_wFin_raw (by omega))
  · intro qRange qFin h_qend h_qlo h_qib h_disj
    rw [getBytesUnchecked_eq]
    have h_qib_upd : qFin.bytes.toNat ≤ updated.byteSize.bytes.toNat := h_qib
    rw [checkedSlice_ok updated qRange qFin h_upd_storage h_qend h_qlo h_qib_upd,
      checkedSlice_ok state qRange qFin destStorage h_qend h_qlo h_qib]
    have h_qfin_raw : qFin.bytes.toNat ≤ (raw state).size := by
      change qFin.bytes.toNat ≤ state.len; omega
    exact congrArg Except.ok
      (splice_extract_disjoint (raw state) copiedBytes wStart wFin
        qRange.start.bytes.toNat qFin.bytes.toNat
        (by omega) h_wFin_raw h_qlo h_qfin_raw (by omega)
        (by dsimp only [wStart, wFin]; omega))

theorem copy_initialized_spec
    (source state : Allocation P E)
    (sourceRange : AllocRange) (srcFinish destStart ptrSize : Size)
    (sameAllocation nonoverlapping : Bool)
    (srcBytes : Array UInt8) (provCopy : ProvenanceCopy P)
    (clearedProv finalProv : ProvenanceMap P)
    (srcStorage : source.len = source.byteSize.bytes.toNat)
    (srcEnd : sourceRange.endExclusive = .ok srcFinish)
    (srcNonzero : sourceRange.size.bytes ≠ 0)
    (srcMaskLen : source.initializationMask.len = source.byteSize)
    (srcMaskWF : InitMask.WriteProof.WellFormed source.initializationMask)
    (srcInit : source.initializationMask.isRangeInitialized sourceRange = .ok (.ok ()))
    (srcSlice : source.getBytesUnchecked sourceRange = .ok srcBytes)
    (srcInBounds : srcFinish.bytes.toNat ≤ source.byteSize.bytes.toNat)
    (h_prepProv : ∀ srcFull : Array UInt8,
      source.getBytesUnchecked (allocRange Size.ZERO source.byteSize) = .ok srcFull →
      source.provenanceMap.prepareCopy sourceRange srcFull ptrSize = .ok provCopy)
    (h_disjSame : sameAllocation = true → nonoverlapping = true →
      srcFinish.bytes.toNat ≤ destStart.bytes.toNat ∨
        destStart.bytes.toNat + sourceRange.size.bytes.toNat ≤ sourceRange.start.bytes.toNat)
    (destStorage : state.len = state.byteSize.bytes.toNat)
    (destMut : state.mutability = .Mut)
    (destMaskLen : state.initializationMask.len = state.byteSize)
    (destMaskWF : InitMask.WriteProof.WellFormed state.initializationMask)
    (destInBounds : destStart.bytes.toNat + sourceRange.size.bytes.toNat ≤ state.byteSize.bytes.toNat)
    (h_clearProv : ∀ stFull : Array UInt8,
      state.getBytesUnchecked (allocRange Size.ZERO state.byteSize) = .ok stFull →
      state.provenanceMap.clear (allocRange destStart sourceRange.size) stFull ptrSize =
        .ok () clearedProv)
    (h_applyProv : clearedProv.applyCopy provCopy
      (allocRange destStart sourceRange.size) 1 = .ok () finalProv) :
    ∃ updated,
      Allocation.copy source sourceRange destStart ptrSize
        sameAllocation nonoverlapping state = .ok () updated ∧
      updated.byteSize = state.byteSize ∧
      updated.len = state.len ∧
      updated.mutability = state.mutability ∧
      updated.align = state.align ∧
      updated.extra = state.extra ∧
      updated.nativeBuffer = state.nativeBuffer ∧
      updated.initializationMask.len = state.initializationMask.len ∧
      InitMask.WriteProof.WellFormed updated.initializationMask ∧
      updated.initializationMask.isRangeInitialized (allocRange destStart sourceRange.size) = .ok (.ok ()) ∧
      (∀ (idx : Size), idx.bytes.toNat < state.byteSize.bytes.toNat →
        updated.initializationMask.get idx =
          if destStart.bytes.toNat ≤ idx.bytes.toNat ∧
              idx.bytes.toNat < destStart.bytes.toNat + sourceRange.size.bytes.toNat then
            .ok true
          else
            state.initializationMask.get idx) ∧
      (∀ (qRange : AllocRange) (qFin : Size),
        qRange.endExclusive = .ok qFin →
        qRange.start.bytes.toNat < qFin.bytes.toNat →
        qFin.bytes.toNat ≤ state.byteSize.bytes.toNat →
        (destStart.bytes.toNat + sourceRange.size.bytes.toNat ≤ qRange.start.bytes.toNat ∨
          qFin.bytes.toNat ≤ destStart.bytes.toNat) →
        (updated.initializationMask.isRangeInitialized qRange = .ok (.ok ()) ↔
          state.initializationMask.isRangeInitialized qRange = .ok (.ok ()))) ∧
      updated.provenanceMap = finalProv ∧
      updated.getBytesUnchecked (allocRange destStart sourceRange.size) = .ok srcBytes ∧
      ∀ (qRange : AllocRange) (qFin : Size),
        qRange.endExclusive = .ok qFin →
        qRange.start.bytes.toNat ≤ qFin.bytes.toNat →
        qFin.bytes.toNat ≤ state.byteSize.bytes.toNat →
        (destStart.bytes.toNat + sourceRange.size.bytes.toNat ≤ qRange.start.bytes.toNat ∨
          qFin.bytes.toNat ≤ destStart.bytes.toNat) →
        updated.getBytesUnchecked qRange = state.getBytesUnchecked qRange := by
  have h_mul1 : Size.mul sourceRange.size 1 = .ok sourceRange.size := by
    cases sourceRange.size
    unfold Size.mul
    simp [UInt64.mul_one, UInt64.div_one, Size.ofBytes]
  obtain ⟨updated, h_ok, h_bs, h_len, h_mut, h_al, h_ex, h_nb, h_ml, h_mwf,
      h_isInit, h_mget, h_mframe, h_prov, h_bytes, h_frame⟩ :=
    copyRepeatedly_initialized_spec source state sourceRange srcFinish destStart sourceRange.size ptrSize
      1 sameAllocation nonoverlapping srcBytes provCopy clearedProv finalProv
      srcStorage srcEnd srcNonzero srcMaskLen srcMaskWF srcInit srcSlice srcInBounds h_prepProv
      (by decide) h_mul1 (fun h => absurd h (by decide)) h_disjSame
      destStorage destMut destMaskLen destMaskWF destInBounds h_clearProv h_applyProv
  have h_flat1 : (List.replicate (1 : UInt64).toNat srcBytes.toList).flatten.toArray = srcBytes := by
    have h1 : (1 : UInt64).toNat = 1 := rfl
    simp [h1]
  rw [h_flat1] at h_bytes
  exact ⟨updated, h_ok, h_bs, h_len, h_mut, h_al, h_ex, h_nb, h_ml, h_mwf,
    h_isInit, h_mget, h_mframe, h_prov, h_bytes, h_frame⟩

end Miri.Memory.Allocation

/-! ## Part 4. `LeanMiriSpec.MemoryLemmas` re-exports

All 50 theorems live in the `lean-miri` namespaces used by `google/zerocopy#4022`
(`Miri.Memory.InitMask.WriteProof`, `Miri.Memory.ProvenanceMap`, `Miri.Memory.Allocation`), so
dot notation and `open Miri.Memory` work unchanged. The `export` aliases below additionally
expose every one of the 50 theorems after `open LeanMiriSpec.MemoryLemmas`. -/

namespace LeanMiriSpec.MemoryLemmas

export Miri.Memory.InitMask.WriteProof (get_ok_of_wellFormed set_range_get
  isRangeInitialized_nonempty_iff isRangeInitialized_after_setRange_true isRangeInitialized_frame
  prepareCopy_of_uniform applyCopy_singleton)

export Miri.Memory.ProvenanceMap (rangeEmpty_new readPtr_new prepareCopy_new applyCopy_empty)

export Miri.Memory.Allocation (byteSize_withExtra len_withExtra align_withExtra
  mutability_withExtra provenanceMap_withExtra initializationMask_withExtra
  getBytesUnchecked_withExtra byteSize_mapExtra len_mapExtra align_mapExtra mutability_mapExtra
  provenanceMap_mapExtra initializationMask_mapExtra getBytesUnchecked_mapExtra
  getBytesStripProvenance_mapExtra readScalar_mapExtra writeBytes_mapExtra clearProvenance_mapExtra
  fromBytes_spec fromBytes_exists tryNew_spec tryNew_exists getBytesUnchecked_size
  getBytesUnchecked_subrange getBytesUnchecked_split getBytesStripProvenance_uninit_err
  getBytesStripProvenance_ok readScalar_uninit_err readScalar_int_of_bytes readScalar_int_roundtrip
  readScalar_ptr_roundtrip readScalar_ptr_none_roundtrip writeScalar_spec writeBytes_zero_spec
  writeBytes_spec writeUninit_zero_spec writeUninit_spec copyRepeatedly_initialized_spec
  copy_initialized_spec)

end LeanMiriSpec.MemoryLemmas

/-! ## Part 5. Non-vacuity witnesses (50 / 50 theorem coverage)

Compile-time checks that the hypotheses of all 50 specification theorems are jointly satisfiable
on concrete states, by instantiating every theorem in closed or existentially-constructed
`private theorem`s (unlike `example`, `private theorem` declarations remain in `env.constants.map₂`
so `#assert_module_standard_axioms` audits their axiom footprint while adding zero public API).
They cover multi-block `.Lazy` → `.Materialized` `InitMask` transitions (`64` and `128` byte
boundaries), `ProvenanceMap` operations, `fromBytes` / `tryNew` (`.Uninit` and `.Zero`), framed
`writeBytes`, `writeUninit`, zero-length writes, `getBytesUnchecked` size/subrange/split,
`getBytesStripProvenance`, little- and big-endian integer and pointer `writeScalar` / `readScalar`
roundtrips, `withExtra` / `mapExtra` commutations, and cross-allocation plus same-allocation
`copy` and `copyRepeatedly`. -/

namespace LeanMiriSpec.MemoryLemmas.NonVacuity
open Miri.ABI Miri.Memory

/-- 1. All 7 `InitMask.WriteProof` theorems across two 64-bit word boundaries (`64` and `128`),
starting from a `.Lazy false` mask. -/
private theorem wit_initMask_full_chain :
    ∃ (u uCopy : InitMask) (b0 : Bool) (bad : AllocRange),
      (InitMask.new (Size.ofBytes 200) false).get Size.ZERO = .ok b0 ∧
      (InitMask.new (Size.ofBytes 200) false).setRange
        (allocRange (Size.ofBytes 60) (Size.ofBytes 80)) true = .ok u ∧
      u.get (Size.ofBytes 59) = .ok false ∧ u.get (Size.ofBytes 60) = .ok true ∧
      u.get (Size.ofBytes 63) = .ok true ∧ u.get (Size.ofBytes 64) = .ok true ∧
      u.get (Size.ofBytes 127) = .ok true ∧ u.get (Size.ofBytes 128) = .ok true ∧
      u.get (Size.ofBytes 139) = .ok true ∧ u.get (Size.ofBytes 140) = .ok false ∧
      u.isRangeInitialized (allocRange (Size.ofBytes 60) (Size.ofBytes 80)) = .ok (.ok ()) ∧
      (u.isRangeInitialized (allocRange Size.ZERO (Size.ofBytes 60)) = .ok (.ok ()) ↔
        (InitMask.new (Size.ofBytes 200) false).isRangeInitialized
          (allocRange Size.ZERO (Size.ofBytes 60)) = .ok (.ok ())) ∧
      u.isRangeInitialized (allocRange Size.ZERO (Size.ofBytes 60)) = .ok (.error bad) ∧
      u.prepareCopy (allocRange (Size.ofBytes 60) (Size.ofBytes 80)) = .ok ⟨true, #[80]⟩ ∧
      u.applyCopy ⟨true, #[80]⟩ (allocRange Size.ZERO (Size.ofBytes 80)) 2 = .ok uCopy := by
  let m0 := InitMask.new (Size.ofBytes 200) false
  have hwf0 : InitMask.WriteProof.WellFormed m0 := trivial
  obtain ⟨b0, hb0⟩ := InitMask.WriteProof.get_ok_of_wellFormed m0 Size.ZERO hwf0 (by decide)
  have hend : (allocRange (Size.ofBytes 60) (Size.ofBytes 80)).endExclusive =
      .ok (Size.ofBytes 140) := by decide
  obtain ⟨u, hu, hlen, hwfu⟩ := InitMask.WriteProof.set_range_exists m0
    (allocRange (Size.ofBytes 60) (Size.ofBytes 80)) (Size.ofBytes 140) true hwf0 hend
    (by decide) (by decide)
  have hget : ∀ idx : Size, idx.bytes.toNat < 200 → u.get idx =
      if 60 ≤ idx.bytes.toNat ∧ idx.bytes.toNat < 140 then .ok true else .ok false :=
    fun idx hidx => InitMask.WriteProof.set_range_get m0 u
      (allocRange (Size.ofBytes 60) (Size.ofBytes 80)) (Size.ofBytes 140) idx true hwf0 hend
      (by decide) (by decide) hidx hu
  have his := InitMask.WriteProof.isRangeInitialized_after_setRange_true m0 u
    (allocRange (Size.ofBytes 60) (Size.ofBytes 80)) (Size.ofBytes 140) hwf0 hend
    (by decide) (by decide) hu
  have hfr := InitMask.WriteProof.isRangeInitialized_frame m0 u
    (allocRange (Size.ofBytes 60) (Size.ofBytes 80)) (allocRange Size.ZERO (Size.ofBytes 60))
    (Size.ofBytes 140) (Size.ofBytes 60) true hwf0 hend (by decide)
    (by decide) (by decide) (by decide) (by decide) (Or.inr (by decide)) hu
  have hiff_true := (InitMask.WriteProof.isRangeInitialized_nonempty_iff u
    (allocRange (Size.ofBytes 60) (Size.ofBytes 80)) (Size.ofBytes 140) hwfu hend
    (by decide) (by rw [hlen]; decide)).1.mp his
  have h59 : u.get (Size.ofBytes 59) = .ok false := by rw [hget _ (by decide)]; decide
  obtain ⟨bad, hbad⟩ := (InitMask.WriteProof.isRangeInitialized_nonempty_iff u
    (allocRange Size.ZERO (Size.ofBytes 60)) (Size.ofBytes 60) hwfu (by decide)
    (by decide) (by rw [hlen]; decide)).2 ⟨Size.ofBytes 59, by decide, by decide, h59⟩
  have hpc := InitMask.WriteProof.prepareCopy_of_uniform u
    (allocRange (Size.ofBytes 60) (Size.ofBytes 80)) (Size.ofBytes 140) true hwfu hend
    (by decide) (by rw [hlen]; decide) hiff_true
  have hap := InitMask.WriteProof.applyCopy_singleton u Size.ZERO (Size.ofBytes 80)
    (Size.ofBytes 160) 2 true (by decide) (by decide)
  obtain ⟨uCopy, huCopy, -, -⟩ := InitMask.WriteProof.set_range_exists u
    (allocRange Size.ZERO (Size.ofBytes 160)) (Size.ofBytes 160) true hwfu (by decide)
    (by decide) (by rw [hlen]; decide)
  refine ⟨u, uCopy, b0, bad, hb0, hu, h59, ?_, ?_, ?_, ?_, ?_, ?_, ?_, his, hfr, hbad, hpc,
    hap.trans huCopy⟩ <;> rw [hget _ (by decide)] <;> decide

/-- 2. `fromBytes_exists` / `fromBytes_spec`, `writeBytes_spec`, `writeBytes_zero_spec`,
`getBytesUnchecked_{size,subrange,split}`, and all 18 `withExtra`/`mapExtra` lemmas. -/
private theorem wit_fromBytes_writeBytes_slices_and_mapExtra :
    ∃ (alloc updated : Allocation CtfeProvenance Unit) (slice26 : Array UInt8),
      Allocation.fromBytes (Array.replicate 8 (0 : UInt8)) Align.ONE .Mut = .ok alloc ∧
      Allocation.writeBytes (Size.ofBytes 8) #[] (Size.ofBytes 8) alloc = .ok () alloc ∧
      Allocation.writeBytes (Size.ofBytes 2) #[7, 9] (Size.ofBytes 8) alloc = .ok () updated ∧
      updated.getBytesUnchecked (allocRange (Size.ofBytes 2) (Size.ofBytes 2)) = .ok #[7, 9] ∧
      updated.initializationMask.isRangeInitialized
        (allocRange (Size.ofBytes 2) (Size.ofBytes 2)) = .ok (.ok ()) ∧
      updated.getBytesUnchecked (allocRange (Size.ofBytes 4) (Size.ofBytes 4)) = .ok #[0, 0, 0, 0] ∧
      updated.getBytesUnchecked (allocRange (Size.ofBytes 2) (Size.ofBytes 4)) = .ok slice26 ∧
      slice26.size = 4 ∧
      updated.getBytesUnchecked (allocRange (Size.ofBytes 3) (Size.ofBytes 2)) =
        .ok (slice26.extract 1 3) ∧
      updated.getBytesUnchecked (allocRange (Size.ofBytes 2) (Size.ofBytes 6)) =
        .ok (#[7, 9] ++ #[0, 0, 0, 0]) ∧
      ((updated.withExtra (42 : Nat)).mapExtra (· + 1)).byteSize = updated.byteSize ∧
      ((updated.withExtra (42 : Nat)).mapExtra (· + 1)).len = updated.len ∧
      ((updated.withExtra (42 : Nat)).mapExtra (· + 1)).align = updated.align ∧
      ((updated.withExtra (42 : Nat)).mapExtra (· + 1)).mutability = updated.mutability ∧
      ((updated.withExtra (42 : Nat)).mapExtra (· + 1)).provenanceMap = updated.provenanceMap ∧
      ((updated.withExtra (42 : Nat)).mapExtra (· + 1)).initializationMask =
        updated.initializationMask ∧
      ((updated.withExtra (42 : Nat)).mapExtra (· + 1)).getBytesUnchecked
        (allocRange (Size.ofBytes 2) (Size.ofBytes 2)) =
        updated.getBytesUnchecked (allocRange (Size.ofBytes 2) (Size.ofBytes 2)) ∧
      (updated.mapExtra id).getBytesStripProvenance ⟨.little, .w64⟩
        (allocRange (Size.ofBytes 2) (Size.ofBytes 2)) =
        updated.getBytesStripProvenance ⟨.little, .w64⟩
          (allocRange (Size.ofBytes 2) (Size.ofBytes 2)) ∧
      (updated.mapExtra id).readScalar ⟨.little, .w64⟩
        (allocRange (Size.ofBytes 2) (Size.ofBytes 2)) false =
        updated.readScalar ⟨.little, .w64⟩
          (allocRange (Size.ofBytes 2) (Size.ofBytes 2)) false ∧
      Allocation.writeBytes (Size.ofBytes 2) #[7, 9] (Size.ofBytes 8) (alloc.mapExtra id) =
        .ok () (updated.mapExtra id) ∧
      Allocation.clearProvenance (allocRange Size.ZERO (Size.ofBytes 2)) (Size.ofBytes 8)
        (updated.mapExtra id) =
        (match Allocation.clearProvenance (allocRange Size.ZERO (Size.ofBytes 2))
            (Size.ofBytes 8) updated with
         | .ok v s => .ok v (s.mapExtra id)
         | .error e s => .error e (s.mapExtra id)) := by
  obtain ⟨alloc, hcreated, -, -⟩ := Allocation.fromBytes_exists (P := CtfeProvenance)
    (Array.replicate 8 0) Align.ONE 1 .Mut rfl rfl (by decide)
  obtain ⟨hbs, hlen, hmut, -, -, hprov, hmask, hwf, hslice⟩ :=
    Allocation.fromBytes_spec _ _ _ alloc hcreated
  have hzero := Allocation.writeBytes_zero_spec (Size.ofBytes 8) (Size.ofBytes 8) #[] alloc
    rfl (hlen.trans hbs.symm) (by rw [hbs]; decide)
  obtain ⟨updated, hw, hbsU, hlenU, -, -, -, -, -, -, -, hinit, -, hget22, hframe⟩ :=
    Allocation.writeBytes_spec (Size.ofBytes 2) (Size.ofBytes 8) #[7, 9] alloc ProvenanceMap.new
      (by decide) (hlen.trans hbs.symm) hmut (by rw [hmask]; rfl) hwf (by rw [hbs]; decide)
      (fun _ _ => by
        rw [hprov]
        exact ProvenanceMap.clear_new _ _ _ (Size.ofBytes 4) (by decide) (by decide))
  have hget44 : updated.getBytesUnchecked (allocRange (Size.ofBytes 4) (Size.ofBytes 4)) =
      .ok #[0, 0, 0, 0] := by
    rw [hframe _ (Size.ofBytes 8) (by decide) (by decide) (by rw [hbs]; decide) (by decide),
      hslice _ (Size.ofBytes 8) (by decide) (by decide) (by decide)]
    decide
  have hstorU : updated.len = updated.byteSize.bytes.toNat :=
    hlenU.trans (hlen.trans (hbs.symm.trans (congrArg (·.bytes.toNat) hbsU.symm)))
  obtain ⟨slice26, hget24, hsz24⟩ := Allocation.getBytesUnchecked_size updated
    (allocRange (Size.ofBytes 2) (Size.ofBytes 4)) (Size.ofBytes 6) hstorU
    (by decide) (by decide) (by rw [hbsU, hbs]; decide)
  have hsub := Allocation.getBytesUnchecked_subrange updated
    (allocRange (Size.ofBytes 2) (Size.ofBytes 4)) (allocRange (Size.ofBytes 3) (Size.ofBytes 2))
    (Size.ofBytes 6) (Size.ofBytes 5) slice26 (by decide) (by decide)
    (by decide) (by decide) (by decide) hget24
  have hsplit := Allocation.getBytesUnchecked_split updated
    (allocRange (Size.ofBytes 2) (Size.ofBytes 2)) (allocRange (Size.ofBytes 4) (Size.ofBytes 4))
    (allocRange (Size.ofBytes 2) (Size.ofBytes 6)) (Size.ofBytes 4) (Size.ofBytes 8)
    #[7, 9] #[0, 0, 0, 0] (by decide) rfl (by decide) rfl (by decide)
    (by decide) (by decide) hget22 hget44
  have hw_map := Allocation.writeBytes_mapExtra (Size.ofBytes 2) #[7, 9] (Size.ofBytes 8) alloc id
  rw [hw] at hw_map
  refine ⟨alloc, updated, slice26, hcreated, hzero, hw, hget22, hinit, hget44, hget24,
    hsz24, hsub, hsplit,
    (Allocation.byteSize_mapExtra _ _).trans (Allocation.byteSize_withExtra _ _),
    (Allocation.len_mapExtra _ _).trans (Allocation.len_withExtra _ _),
    (Allocation.align_mapExtra _ _).trans (Allocation.align_withExtra _ _),
    (Allocation.mutability_mapExtra _ _).trans (Allocation.mutability_withExtra _ _),
    (Allocation.provenanceMap_mapExtra _ _).trans (Allocation.provenanceMap_withExtra _ _),
    (Allocation.initializationMask_mapExtra _ _).trans (Allocation.initializationMask_withExtra _ _),
    (Allocation.getBytesUnchecked_mapExtra _ _ _).trans
      (Allocation.getBytesUnchecked_withExtra _ _ _),
    Allocation.getBytesStripProvenance_mapExtra _ _ _ _,
    Allocation.readScalar_mapExtra _ _ _ _ _,
    hw_map, ?_⟩
  rw [Allocation.clearProvenance_mapExtra]
  cases Allocation.clearProvenance (allocRange Size.ZERO (Size.ofBytes 2))
    (Size.ofBytes 8) updated <;> rfl

/-- 3. `tryNew_exists` / `tryNew_spec` (both `.Uninit` and `.Zero`),
`getBytesStripProvenance_{uninit_err,ok}`, `readScalar_uninit_err`, and
`writeUninit_{zero_,}spec`. -/
private theorem wit_tryNew_strip_and_writeUninit :
    ∃ (aUninit aZero aDeinit : Allocation CtfeProvenance Unit) (bad : AllocRange),
      Allocation.tryNew (Size.ofBytes 8) Align.EIGHT .Uninit
        (fun n _ => some (Array.replicate n.bytes.toNat 0)) = .ok aUninit ∧
      aUninit.getBytesStripProvenance ⟨.little, .w64⟩ (allocRange Size.ZERO (Size.ofBytes 4)) =
        .error (.invalidUninitBytes (some ⟨allocRange Size.ZERO (Size.ofBytes 4), bad⟩)) ∧
      aUninit.readScalar ⟨.little, .w64⟩ (allocRange Size.ZERO (Size.ofBytes 4)) false =
        .error (.invalidUninitBytes (some ⟨allocRange Size.ZERO (Size.ofBytes 4), bad⟩)) ∧
      Allocation.tryNew (Size.ofBytes 8) Align.EIGHT .Zero
        (fun n _ => some (Array.replicate n.bytes.toNat 0)) = .ok aZero ∧
      aZero.getBytesStripProvenance ⟨.little, .w64⟩ (allocRange Size.ZERO (Size.ofBytes 4)) =
        .ok #[0, 0, 0, 0] ∧
      Allocation.writeUninit (allocRange (Size.ofBytes 8) Size.ZERO) (Size.ofBytes 8) aZero =
        .ok () aZero ∧
      Allocation.writeUninit (allocRange Size.ZERO (Size.ofBytes 2)) (Size.ofBytes 8) aZero =
        .ok () aDeinit ∧
      aDeinit.initializationMask.get Size.ZERO = .ok false ∧
      aDeinit.initializationMask.get (Size.ofBytes 2) = .ok true ∧
      aDeinit.getBytesUnchecked (allocRange Size.ZERO (Size.ofBytes 4)) = .ok #[0, 0, 0, 0] := by
  obtain ⟨aUninit, huNew, _⟩ := Allocation.tryNew_exists (P := CtfeProvenance)
    (Size.ofBytes 8) Align.EIGHT 8 .Uninit (by decide) (by decide)
  obtain ⟨hbsU, _, _, _, _, _, hmaskU, _, hwfU, _⟩ :=
    Allocation.tryNew_spec (Size.ofBytes 8) Align.EIGHT .Uninit aUninit huNew
  have hmU := hmaskU rfl
  have hget0_false : aUninit.initializationMask.get Size.ZERO = .ok false := by rw [hmU]; rfl
  obtain ⟨bad, hbad⟩ := (InitMask.WriteProof.isRangeInitialized_nonempty_iff
    aUninit.initializationMask (allocRange Size.ZERO (Size.ofBytes 4)) (Size.ofBytes 4)
    hwfU (by decide) (by decide) (by rw [hmU]; decide)).2
    ⟨Size.ZERO, by decide, by decide, hget0_false⟩
  have hstripErr := Allocation.getBytesStripProvenance_uninit_err aUninit ⟨.little, .w64⟩ _ bad hbad
  have hreadErr := Allocation.readScalar_uninit_err aUninit ⟨.little, .w64⟩ _ bad false hbad
  obtain ⟨aZero, hzNew, _⟩ := Allocation.tryNew_exists (P := CtfeProvenance)
    (Size.ofBytes 8) Align.EIGHT 8 .Zero (by decide) (by decide)
  obtain ⟨hbsZ, hlenZ, hmutZ, _, _, hprovZ, _, hmaskZ, hwfZ, hsliceZ⟩ :=
    Allocation.tryNew_spec (Size.ofBytes 8) Align.EIGHT .Zero aZero hzNew
  have hmZ := hmaskZ rfl
  have hend4 : (allocRange Size.ZERO (Size.ofBytes 4)).endExclusive = .ok (Size.ofBytes 4) := by
    decide
  have hps : (Size.fromBits PointerWidth.w64.bits).bytes ≠ 0 := by decide
  have hinitZ : aZero.initializationMask.isRangeInitialized
      (allocRange Size.ZERO (Size.ofBytes 4)) = .ok (.ok ()) := by
    rw [hmZ]
    exact InitMask.lazy_initialized_query _ _ _ hend4 (by decide)
  have hstripOk : aZero.getBytesStripProvenance ⟨.little, .w64⟩
      (allocRange Size.ZERO (Size.ofBytes 4)) = .ok #[0, 0, 0, 0] := by
    rw [Allocation.getBytesStripProvenance_ok aZero _ _ hinitZ
      (Or.inr (by rw [hprovZ]; exact ProvenanceMap.rangeEmpty_new _ _ _ hps hend4))]
    exact hsliceZ _ _ hend4 (by decide) (by decide)
  have hstorZ : aZero.len = aZero.byteSize.bytes.toNat := by rw [hlenZ, hbsZ]
  have hwuZero := Allocation.writeUninit_zero_spec (allocRange (Size.ofBytes 8) Size.ZERO)
    (Size.ofBytes 8) (Size.ofBytes 8) aZero rfl hstorZ (by decide) (by decide)
    (by rw [hbsZ]; decide)
  obtain ⟨aDeinit, hwu, _, _, _, _, _, _, _, _, hsetF, _, hbytesEq⟩ :=
    Allocation.writeUninit_spec (allocRange Size.ZERO (Size.ofBytes 2)) (Size.ofBytes 8)
      aZero ProvenanceMap.new (by decide) hstorZ hmutZ (by rw [hmZ, hbsZ]; rfl) hwfZ
      (by rw [hbsZ]; decide)
      (fun _ _ => by
        rw [hprovZ]
        exact ProvenanceMap.clear_new _ _ _ (Size.ofBytes 2) (by decide) (by decide))
  have hg0 := InitMask.WriteProof.set_range_get aZero.initializationMask
    aDeinit.initializationMask (allocRange Size.ZERO (Size.ofBytes 2)) (Size.ofBytes 2)
    Size.ZERO false hwfZ (by decide) (by decide) (by rw [hmZ]; decide) (by rw [hmZ]; decide) hsetF
  have hg2 := InitMask.WriteProof.set_range_get aZero.initializationMask
    aDeinit.initializationMask (allocRange Size.ZERO (Size.ofBytes 2)) (Size.ofBytes 2)
    (Size.ofBytes 2) false hwfZ (by decide) (by decide) (by rw [hmZ]; decide)
    (by rw [hmZ]; decide) hsetF
  have hmZ0 : aZero.initializationMask.get Size.ZERO = .ok true := by rw [hmZ]; rfl
  have hmZ2 : aZero.initializationMask.get (Size.ofBytes 2) = .ok true := by rw [hmZ]; rfl
  refine ⟨aUninit, aZero, aDeinit, bad, huNew, hstripErr, hreadErr, hzNew, hstripOk, hwuZero,
    hwu, ?_, ?_, (hbytesEq _).trans (hsliceZ _ _ hend4 (by decide) (by decide))⟩
  · rw [hg0, hmZ0]; decide
  · rw [hg2, hmZ2]; decide

/-- 4. `readScalar_int_of_bytes` decodes `#[1, 2]` as `0x0201` on little-endian targets and
`0x0102` on big-endian targets. -/
private theorem wit_readScalar_int_of_bytes (endian : Endian) :
    ∃ alloc : Allocation CtfeProvenance Unit,
      Allocation.fromBytes #[1, 2] Align.ONE .Not = .ok alloc ∧
      alloc.readScalar ⟨endian, .w64⟩ (allocRange Size.ZERO (Size.ofBytes 2)) false =
        (Scalar.fromUInt (BitVec.ofNat 128 (if endian == .little then 0x0201 else 0x0102))
          (Size.ofBytes 2)).mapError AllocError.scalar := by
  obtain ⟨alloc, hcreated, -, -⟩ := Allocation.fromBytes_exists (P := CtfeProvenance)
    #[1, 2] Align.ONE 1 .Not rfl rfl (by decide)
  obtain ⟨hbs, -, -, -, -, hprov, hmask, -, hslice⟩ :=
    Allocation.fromBytes_spec _ _ _ alloc hcreated
  have hend : (allocRange Size.ZERO (Size.ofBytes 2)).endExclusive = .ok (Size.ofBytes 2) := by
    decide
  have hps : (Size.fromBits PointerWidth.w64.bits).bytes ≠ 0 := by decide
  refine ⟨alloc, hcreated, ?_⟩
  rw [Allocation.readScalar_int_of_bytes alloc _ _ #[1, 2]
    (by
      rw [hmask]
      exact InitMask.lazy_initialized_query _ _ _ hend
        (UInt64.le_iff_toNat_le.mpr (by rw [hbs]; decide)))
    (hslice _ _ hend (by decide) (by decide)) (by decide)
    (Or.inr (by rw [hprov]; exact ProvenanceMap.rangeEmpty_new _ _ _ hps hend))]
  cases endian <;> rfl

/-- 5. `writeScalar_spec` (both `.bits` and `.pointer` branches) chained into
`readScalar_int_roundtrip`, `readScalar_ptr_none_roundtrip`, and `readScalar_ptr_roundtrip`
across both little- and big-endian target layouts. -/
private theorem wit_writeScalar_and_readScalar_roundtrips (endian : Endian) :
    ∃ (a0 aBits : Allocation CtfeProvenance Unit) (p0 pPtr : Allocation Provenance Unit),
      let layout : TargetDataLayout := ⟨endian, .w64⟩
      let intVal : Scalar CtfeProvenance := Scalar.fromScalarInt (ScalarInt.ofUInt64 0x0102030405060708)
      let ptr : Pointer Provenance := ⟨Size.ofBytes 0x1020, .wildcard⟩
      let ptrVal : Scalar Provenance := Scalar.fromPointer layout ptr
      Allocation.tryNew (Size.ofBytes 8) Align.EIGHT .Uninit
        (fun n _ => some (Array.replicate n.bytes.toNat 0)) = .ok a0 ∧
      Allocation.writeScalar layout (allocRange Size.ZERO (Size.ofBytes 8)) intVal a0 =
        .ok () aBits ∧
      aBits.readScalar layout (allocRange Size.ZERO (Size.ofBytes 8)) false = .ok intVal ∧
      aBits.readScalar layout (allocRange Size.ZERO (Size.ofBytes 8)) true = .ok intVal ∧
      Allocation.tryNew (Size.ofBytes 16) Align.EIGHT .Uninit
        (fun n _ => some (Array.replicate n.bytes.toNat 0)) = .ok p0 ∧
      Allocation.writeScalar layout (allocRange Size.ZERO (Size.ofBytes 8)) ptrVal p0 =
        .ok () pPtr ∧
      pPtr.readScalar layout (allocRange Size.ZERO (Size.ofBytes 8)) true = .ok ptrVal ∧
      pPtr.getBytesUnchecked (allocRange (Size.ofBytes 8) (Size.ofBytes 8)) =
        .ok (Array.replicate 8 0) := by
  let layout : TargetDataLayout := ⟨endian, .w64⟩
  let bits : U128 := BitVec.ofNat 128 (0x0102030405060708 : UInt64).toNat
  let intVal : Scalar CtfeProvenance := Scalar.fromScalarInt (ScalarInt.ofUInt64 0x0102030405060708)
  let r08 := allocRange Size.ZERO (Size.ofBytes 8)
  have hend08 : r08.endExclusive = .ok (Size.ofBytes 8) := by decide
  have hps_eq : Size.fromBits layout.pointerWidth.bits = Size.ofBytes 8 := by
    dsimp only [layout]; decide
  have hps_nz : (Size.fromBits layout.pointerWidth.bits).bytes ≠ 0 := by
    dsimp only [layout]; decide
  obtain ⟨a0, ha0, _⟩ := Allocation.tryNew_exists (P := CtfeProvenance)
    (Size.ofBytes 8) Align.EIGHT 8 .Uninit (by decide) (by decide)
  obtain ⟨hbs0, hlen0, hmut0, _, _, hprov0, hmask0, _, hwf0, _⟩ :=
    Allocation.tryNew_spec (Size.ofBytes 8) Align.EIGHT .Uninit a0 ha0
  obtain ⟨aBits, hwBits, _, _, _, _, _, _, _, _, _, hisBits, hprovBits, hbytesBits, _, _⟩ :=
    Allocation.writeScalar_spec layout a0 r08 intVal (.bits bits) ProvenanceMap.new ProvenanceMap.new
      (by rw [hlen0, hbs0]) hmut0 (by rw [hmask0 rfl, hbs0]; rfl) hwf0
      (by decide) (by decide) (by rw [hbs0]; decide) (by decide)
      (fun _ _ => by
        rw [hprov0, hps_eq]
        exact ProvenanceMap.clear_new _ _ _ (Size.ofBytes 8) (by decide) hend08)
      rfl
  have hfromUInt : (Scalar.fromUInt (Prov := CtfeProvenance) bits r08.size).mapError
      AllocError.scalar = .ok intVal := by decide
  have hreadInt := Allocation.readScalar_int_roundtrip aBits layout r08 bits
    hisBits (by decide) (by decide)
    (Or.inr (by rw [hprovBits]; exact ProvenanceMap.rangeEmpty_new _ _ _ hps_nz hend08))
    (hbytesBits bits rfl)
  have hreadPtrNone := Allocation.readScalar_ptr_none_roundtrip aBits layout r08 bits
    hisBits hps_eq.symm (by decide) (by decide)
    (by rw [hprovBits, hps_eq]; exact ProvenanceMap.readPtr_new _ _ _ (by decide) hend08)
    (hbytesBits bits rfl)
  let ptr : Pointer Provenance := ⟨Size.ofBytes 0x1020, .wildcard⟩
  let ptrVal : Scalar Provenance := Scalar.fromPointer layout ptr
  obtain ⟨pm1, hpm1_ins, hpm1_ptrs⟩ :
      ∃ pm1 : ProvenanceMap Provenance,
        ProvenanceMap.insertPtr Size.ZERO Provenance.wildcard (Size.ofBytes 8) ProvenanceMap.new =
          .ok () pm1 ∧
        pm1.ptrs = #[(Size.ZERO, Provenance.wildcard)] :=
    ⟨_, ProvenanceMap.insertPtr_new Size.ZERO (Size.ofBytes 8) (Size.ofBytes 8)
      Provenance.wildcard (by decide) hend08, rfl⟩
  have hconvPtr : ptrVal.toBitsOrPtrInternal r08.size = .ok (.pointer ptr) := by
    cases endian <;> decide
  obtain ⟨p0, hp0, _⟩ := Allocation.tryNew_exists (P := Provenance)
    (Size.ofBytes 16) Align.EIGHT 8 .Uninit (by decide) (by decide)
  obtain ⟨hbsP, hlenP, hmutP, _, _, hprovP, hmaskP, _, hwfP, hsliceP⟩ :=
    Allocation.tryNew_spec (Size.ofBytes 16) Align.EIGHT .Uninit p0 hp0
  obtain ⟨pPtr, hwPtr, _, _, _, _, _, _, _, _, _, hisPtr, hprovPtr, _, hbytesPtr, hframePtr⟩ :=
    Allocation.writeScalar_spec layout p0 r08 ptrVal (.pointer ptr) ProvenanceMap.new pm1
      (by rw [hlenP, hbsP]) hmutP (by rw [hmaskP rfl, hbsP]; rfl) hwfP
      (by decide) (by decide) (by rw [hbsP]; decide) hconvPtr
      (fun _ _ => by
        rw [hprovP, hps_eq]
        exact ProvenanceMap.clear_new _ _ _ (Size.ofBytes 8) (by decide) hend08)
      ⟨hps_eq.symm, by rw [hps_eq]; exact hpm1_ins⟩
  have hpSlice : pPtr.getBytesUnchecked r08 =
      .ok (Array.ofFn (fun i : Fin r08.size.bytes.toNat =>
        UInt8.ofNat ((ptr.offset.bytes.toNat / 2 ^ (8 *
          (if layout.endian == .little then i.1 else r08.size.bytes.toNat - i.1 - 1))) % 256))) := by
    have hbv : (BitVec.ofNat 128 ptr.offset.bytes.toNat).toNat = ptr.offset.bytes.toNat := by decide
    simpa [hbv] using hbytesPtr ptr rfl
  have hgetPtr : pm1.getPtr r08.start = some ptr.provenance := by
    unfold ProvenanceMap.getPtr
    rw [hpm1_ptrs]
    decide
  have hreadPtr := Allocation.readScalar_ptr_roundtrip pPtr layout r08 ptr
    hisPtr hps_eq.symm (by decide) (by decide)
    (by rw [hprovPtr, hps_eq]; exact ProvenanceMap.read_exact_pointer pm1 _ _ _ hgetPtr) hpSlice
  have hfr8 := hframePtr (allocRange (Size.ofBytes 8) (Size.ofBytes 8)) (Size.ofBytes 16)
    (by decide) (by decide) (by rw [hbsP]; decide) (Or.inl (by decide))
  have hp8 := hsliceP (allocRange (Size.ofBytes 8) (Size.ofBytes 8)) (Size.ofBytes 16)
    (by decide) (by decide) (by decide)
  exact ⟨a0, aBits, p0, pPtr, ha0, hwBits, hreadInt.trans hfromUInt,
    hreadPtrNone.trans hfromUInt, hp0, hwPtr, hreadPtr, hfr8.trans hp8⟩

/-- 6. `copy_initialized_spec` (cross-allocation and non-overlapping same-allocation) and
`copyRepeatedly_initialized_spec` (`repeatCount = 3`), together with `prepareCopy_new` and
`applyCopy_empty`, verifying byte + mask `get` + `isRangeInitialized` framing. -/
private theorem wit_copy_and_copyRepeatedly :
    ∃ (src d0 d1 d2 d3 : Allocation CtfeProvenance Unit),
      Allocation.fromBytes #[5, 6] Align.ONE .Not = .ok src ∧
      Allocation.tryNew (Size.ofBytes 12) Align.ONE .Uninit
        (fun n _ => some (Array.replicate n.bytes.toNat 0)) = .ok d0 ∧
      Allocation.copy src (allocRange Size.ZERO (Size.ofBytes 2)) Size.ZERO
        (Size.ofBytes 8) false true d0 = .ok () d1 ∧
      Allocation.copy d1 (allocRange Size.ZERO (Size.ofBytes 2)) (Size.ofBytes 2)
        (Size.ofBytes 8) true true d1 = .ok () d2 ∧
      d2.getBytesUnchecked (allocRange (Size.ofBytes 2) (Size.ofBytes 2)) = .ok #[5, 6] ∧
      d2.getBytesUnchecked (allocRange Size.ZERO (Size.ofBytes 2)) = .ok #[5, 6] ∧
      d2.initializationMask.get (Size.ofBytes 10) = .ok false ∧
      Allocation.copyRepeatedly d2 (allocRange Size.ZERO (Size.ofBytes 2)) (Size.ofBytes 4)
        3 (Size.ofBytes 8) true true d2 = .ok () d3 ∧
      d3.getBytesUnchecked (allocRange (Size.ofBytes 4) (Size.ofBytes 6)) =
        .ok #[5, 6, 5, 6, 5, 6] ∧
      d3.getBytesUnchecked (allocRange Size.ZERO (Size.ofBytes 4)) = .ok #[5, 6, 5, 6] ∧
      d3.initializationMask.isRangeInitialized (allocRange (Size.ofBytes 4) (Size.ofBytes 6)) =
        .ok (.ok ()) ∧
      d3.initializationMask.isRangeInitialized (allocRange Size.ZERO (Size.ofBytes 2)) =
        .ok (.ok ()) ∧
      d3.initializationMask.get (Size.ofBytes 10) = .ok false := by
  obtain ⟨src, hsrc, _, _⟩ := Allocation.fromBytes_exists (P := CtfeProvenance)
    #[5, 6] Align.ONE 1 .Not rfl rfl (by decide)
  obtain ⟨hbsS, hlenS, _, _, _, hprovS, hmaskS, hwfS, hsliceS⟩ :=
    Allocation.fromBytes_spec _ _ _ src hsrc
  have hend02 : (allocRange Size.ZERO (Size.ofBytes 2)).endExclusive = .ok (Size.ofBytes 2) := by
    decide
  have hinitS : src.initializationMask.isRangeInitialized
      (allocRange Size.ZERO (Size.ofBytes 2)) = .ok (.ok ()) := by
    rw [hmaskS]
    exact InitMask.lazy_initialized_query _ _ _ hend02
      (UInt64.le_iff_toNat_le.mpr (by rw [hbsS]; decide))
  obtain ⟨d0, hd0, _⟩ := Allocation.tryNew_exists (P := CtfeProvenance)
    (Size.ofBytes 12) Align.ONE 1 .Uninit (by decide) (by decide)
  obtain ⟨hbs0, hlen0, hmut0, _, _, hprov0, hmask0, _, hwf0, _⟩ :=
    Allocation.tryNew_spec (Size.ofBytes 12) Align.ONE .Uninit d0 hd0
  have hm0 := hmask0 rfl
  obtain ⟨d1, hc1, hbs1, hlen1, hmut1, _, _, _, hml1, hwf1, his1_02, hmget1, _, hprov1, hb1_02, _⟩ :=
    Allocation.copy_initialized_spec src d0 (allocRange Size.ZERO (Size.ofBytes 2))
      (Size.ofBytes 2) Size.ZERO (Size.ofBytes 8) false true #[5, 6]
      ⟨#[], #[]⟩ ProvenanceMap.new ProvenanceMap.new
      (hlenS.trans hbsS.symm) hend02 (by decide) (by rw [hmaskS]; rfl) hwfS hinitS
      (hsliceS _ _ hend02 (by decide) (by decide)) (by rw [hbsS]; decide)
      (fun _ _ => by rw [hprovS]; exact ProvenanceMap.prepareCopy_new _ _ _ _ (by decide) hend02)
      (fun h => by cases h)
      (by rw [hlen0, hbs0]) hmut0 (by rw [hm0, hbs0]; rfl) hwf0 (by rw [hbs0]; decide)
      (fun _ _ => by rw [hprov0]; exact ProvenanceMap.clear_new _ _ _ _ (by decide) hend02)
      (ProvenanceMap.applyCopy_empty _ 1 ProvenanceMap.new)
  have hd1_stor : d1.len = d1.byteSize.bytes.toNat := by rw [hlen1, hbs1, hlen0, hbs0]
  have hd1_ml : d1.initializationMask.len = d1.byteSize := by rw [hml1, hbs1, hm0, hbs0]; rfl
  obtain ⟨d2, hc2, hbs2, hlen2, hmut2, _, _, _, hml2, hwf2, _, hmget2, hmfr2, hprov2, hb2_22, hbfr2⟩ :=
    Allocation.copy_initialized_spec d1 d1 (allocRange Size.ZERO (Size.ofBytes 2))
      (Size.ofBytes 2) (Size.ofBytes 2) (Size.ofBytes 8) true true #[5, 6]
      ⟨#[], #[]⟩ ProvenanceMap.new ProvenanceMap.new
      hd1_stor hend02 (by decide) hd1_ml hwf1 his1_02 hb1_02 (by rw [hbs1, hbs0]; decide)
      (fun _ _ => by rw [hprov1]; exact ProvenanceMap.prepareCopy_new _ _ _ _ (by decide) hend02)
      (fun _ _ => Or.inl (by decide))
      hd1_stor (hmut1.trans hmut0) hd1_ml hwf1 (by rw [hbs1, hbs0]; decide)
      (fun _ _ => by rw [hprov1]; exact ProvenanceMap.clear_new _ _ _ (Size.ofBytes 4) (by decide) (by decide))
      (ProvenanceMap.applyCopy_empty _ 1 ProvenanceMap.new)
  have hb2_02 : d2.getBytesUnchecked (allocRange Size.ZERO (Size.ofBytes 2)) = .ok #[5, 6] :=
    (hbfr2 _ (Size.ofBytes 2) hend02 (by decide) (by rw [hbs1, hbs0]; decide)
      (Or.inr (by decide))).trans hb1_02
  have his2_02 : d2.initializationMask.isRangeInitialized
      (allocRange Size.ZERO (Size.ofBytes 2)) = .ok (.ok ()) :=
    (hmfr2 _ (Size.ofBytes 2) hend02 (by decide) (by rw [hbs1, hbs0]; decide)
      (Or.inr (by decide))).mpr his1_02
  have hd2_10 : d2.initializationMask.get (Size.ofBytes 10) = .ok false := by
    have h2 := hmget2 (Size.ofBytes 10) (by rw [hbs1, hbs0]; decide)
    have h1 := hmget1 (Size.ofBytes 10) (by rw [hbs0]; decide)
    have hm0_10 : d0.initializationMask.get (Size.ofBytes 10) = .ok false := by rw [hm0]; rfl
    rw [h2, h1, hm0_10]
    decide
  have hd2_stor : d2.len = d2.byteSize.bytes.toNat := by rw [hlen2, hbs2]; exact hd1_stor
  have hd2_ml : d2.initializationMask.len = d2.byteSize := by rw [hml2, hbs2]; exact hd1_ml
  obtain ⟨d3, hc3, _, _, _, _, _, _, _, _, his3_46, hmget3, hmfr3, _, hb3_46, hbfr3⟩ :=
    Allocation.copyRepeatedly_initialized_spec d2 d2 (allocRange Size.ZERO (Size.ofBytes 2))
      (Size.ofBytes 2) (Size.ofBytes 4) (Size.ofBytes 6) (Size.ofBytes 8) 3 true true #[5, 6]
      ⟨#[], #[]⟩ ProvenanceMap.new ProvenanceMap.new
      hd2_stor hend02 (by decide) hd2_ml hwf2 his2_02 hb2_02 (by rw [hbs2, hbs1, hbs0]; decide)
      (fun _ _ => by rw [hprov2]; exact ProvenanceMap.prepareCopy_new _ _ _ _ (by decide) hend02)
      (by decide) (by decide) (fun _ => rfl) (fun _ _ => Or.inl (by decide))
      hd2_stor (hmut2.trans (hmut1.trans hmut0)) hd2_ml hwf2 (by rw [hbs2, hbs1, hbs0]; decide)
      (fun _ _ => by rw [hprov2]; exact ProvenanceMap.clear_new _ _ _ (Size.ofBytes 10) (by decide) (by decide))
      (ProvenanceMap.applyCopy_empty _ 3 ProvenanceMap.new)
  have hb2_04 : d2.getBytesUnchecked (allocRange Size.ZERO (Size.ofBytes 4)) = .ok #[5, 6, 5, 6] :=
    Allocation.getBytesUnchecked_split d2 (allocRange Size.ZERO (Size.ofBytes 2))
      (allocRange (Size.ofBytes 2) (Size.ofBytes 2)) (allocRange Size.ZERO (Size.ofBytes 4))
      (Size.ofBytes 2) (Size.ofBytes 4) #[5, 6] #[5, 6] hend02 rfl (by decide) rfl (by decide)
      (by decide) (by decide) hb2_02 hb2_22
  have hb3_04 : d3.getBytesUnchecked (allocRange Size.ZERO (Size.ofBytes 4)) = .ok #[5, 6, 5, 6] :=
    (hbfr3 _ (Size.ofBytes 4) (by decide) (by decide) (by rw [hbs2, hbs1, hbs0]; decide)
      (Or.inr (by decide))).trans hb2_04
  have his3_02 : d3.initializationMask.isRangeInitialized
      (allocRange Size.ZERO (Size.ofBytes 2)) = .ok (.ok ()) :=
    (hmfr3 _ (Size.ofBytes 2) hend02 (by decide) (by rw [hbs2, hbs1, hbs0]; decide)
      (Or.inr (by decide))).mpr his2_02
  have hd3_10 : d3.initializationMask.get (Size.ofBytes 10) = .ok false := by
    have h3 := hmget3 (Size.ofBytes 10) (by rw [hbs2, hbs1, hbs0]; decide)
    rw [h3, hd2_10]
    decide
  exact ⟨src, d0, d1, d2, d3, hsrc, hd0, hc1, hc2, hb2_22, hb2_02, hd2_10,
    hc3, by simpa using hb3_46, hb3_04, his3_46, his3_02, hd3_10⟩

end LeanMiriSpec.MemoryLemmas.NonVacuity

/-! ## Part 6. Axiom audit of all 50 theorems -/

#assert_standard_axioms
  Miri.Memory.InitMask.WriteProof.get_ok_of_wellFormed
  Miri.Memory.InitMask.WriteProof.set_range_get
  Miri.Memory.InitMask.WriteProof.isRangeInitialized_nonempty_iff
  Miri.Memory.InitMask.WriteProof.isRangeInitialized_after_setRange_true
  Miri.Memory.InitMask.WriteProof.isRangeInitialized_frame
  Miri.Memory.InitMask.WriteProof.prepareCopy_of_uniform
  Miri.Memory.InitMask.WriteProof.applyCopy_singleton
  Miri.Memory.ProvenanceMap.rangeEmpty_new
  Miri.Memory.ProvenanceMap.readPtr_new
  Miri.Memory.ProvenanceMap.prepareCopy_new
  Miri.Memory.ProvenanceMap.applyCopy_empty
  Miri.Memory.Allocation.byteSize_withExtra
  Miri.Memory.Allocation.len_withExtra
  Miri.Memory.Allocation.align_withExtra
  Miri.Memory.Allocation.mutability_withExtra
  Miri.Memory.Allocation.provenanceMap_withExtra
  Miri.Memory.Allocation.initializationMask_withExtra
  Miri.Memory.Allocation.getBytesUnchecked_withExtra
  Miri.Memory.Allocation.byteSize_mapExtra
  Miri.Memory.Allocation.len_mapExtra
  Miri.Memory.Allocation.align_mapExtra
  Miri.Memory.Allocation.mutability_mapExtra
  Miri.Memory.Allocation.provenanceMap_mapExtra
  Miri.Memory.Allocation.initializationMask_mapExtra
  Miri.Memory.Allocation.getBytesUnchecked_mapExtra
  Miri.Memory.Allocation.getBytesStripProvenance_mapExtra
  Miri.Memory.Allocation.readScalar_mapExtra
  Miri.Memory.Allocation.writeBytes_mapExtra
  Miri.Memory.Allocation.clearProvenance_mapExtra
  Miri.Memory.Allocation.fromBytes_spec
  Miri.Memory.Allocation.fromBytes_exists
  Miri.Memory.Allocation.tryNew_spec
  Miri.Memory.Allocation.tryNew_exists
  Miri.Memory.Allocation.getBytesUnchecked_size
  Miri.Memory.Allocation.getBytesUnchecked_subrange
  Miri.Memory.Allocation.getBytesUnchecked_split
  Miri.Memory.Allocation.getBytesStripProvenance_uninit_err
  Miri.Memory.Allocation.getBytesStripProvenance_ok
  Miri.Memory.Allocation.readScalar_uninit_err
  Miri.Memory.Allocation.readScalar_int_of_bytes
  Miri.Memory.Allocation.readScalar_int_roundtrip
  Miri.Memory.Allocation.readScalar_ptr_roundtrip
  Miri.Memory.Allocation.readScalar_ptr_none_roundtrip
  Miri.Memory.Allocation.writeScalar_spec
  Miri.Memory.Allocation.writeBytes_zero_spec
  Miri.Memory.Allocation.writeBytes_spec
  Miri.Memory.Allocation.writeUninit_zero_spec
  Miri.Memory.Allocation.writeUninit_spec
  Miri.Memory.Allocation.copyRepeatedly_initialized_spec
  Miri.Memory.Allocation.copy_initialized_spec

#assert_module_standard_axioms
