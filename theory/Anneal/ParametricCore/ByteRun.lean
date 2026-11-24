-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.Core
import Init.NotationExtra
import Init.Data.Nat.Basic
import Init.Data.Nat.Div.Basic
import Init.Data.List.Basic
import Init.Data.Option.Basic
import Init.Data.BitVec.BasicAux
import Init.Data.UInt.BasicAux
import Anneal.Firewall
import Anneal.ParametricCore.LoopInv
import Anneal.ParametricCore.StageCut
import Anneal.ParametricCore.ByteSubLens

universe u v w x y z a b

namespace Anneal.ParametricCore

/-!
# Mixed-`InitMask` Byte-Run Copy Algebra & `[T; N]` Repeat Fusion
(`Anneal.ParametricCore.ByteRun`)

Zero-TCB, MIR-parametric, fully LCNF-computable (`0`
`._unsafe_rec`) run-decomposed byte-copy algebra over
`Anneal.ParametricCore.ByteSubLens` (`ByteStoreOps` / `LawfulByteStoreOps`),
`Anneal.ParametricCore.StageCut`, and `Anneal.Firewall.IndexedCut`:

1. **Run-Decomposed Byte Algebra (`ByteRunAtom`, `ByteRunCodec`, `ByteRun`):**
   Models mixed `.initPlain` scalar bytes, `.initProv` pointer-provenance bytes,
   and `.uninitPad` padding runs with lawful round-trip encoding/decoding
   (`ByteRunCodec.id`, `ByteRunCodec.optionUInt8`, `ByteRunCodec.optionProv`,
   `PlainByteRunCodec.uint8`), exact length/append/split/stride theorems, and
   `ByteCodec` interoperability.
2. **Untyped Range Copy & `[T; N]` Repeat Fusion (`copyRangeComp`,
   `copyRepeatedlyComp`, `writeRepeatRunsComp`):** Overlap-tolerant
   read-then-write copy preserving `.uninitPad` and `.initProv` verbatim,
   failing closed on zero-length, mismatched-length, out-of-bounds, or
   unwritable slices, plus exact fusion of `n` sequential element copies into a
   single `repeatByteRuns n runs` bulk write over any `LawfulByteStoreOps`.
3. **Zero-`Prop`-Argument `@[irreducible] ByteRunCopyCut`:** Stage-cut barrier
   pairing `StepStageCut` with `execByteRunCopyOps`, with `seal`, `unseal`,
   `compose`, disjoint-lens `frame`, `MutSummaryCut` bridge, and
   `Anneal.Firewall.IndexedCut` interoperability.
4. **Canaries:** Kernel-checked positive, overlap, repeat-fusion, stale-padding,
   stage-cut, and fail-closed negative tests over `SliceStore`.
-/

/-! ## Part I: Constructive Helpers (`repeatSlice` and Contiguous Splice Fusion) -/

section Helpers

variable {α : Type u}

/-- Repeats a list `n` times via `@Nat.rec` (computable, `0`
`._unsafe_rec`). -/
def repeatSlice (n : Nat) (elem : List α) : List α :=
  @Nat.rec (fun _ => List α) [] (fun _ acc => acc ++ elem) n

/-- Base equation `repeatSlice 0 elem = []`. -/
theorem repeatSlice_zero (elem : List α) : repeatSlice 0 elem = [] :=
  rfl

/-- Step equation `repeatSlice (n + 1) elem = repeatSlice n elem ++ elem`. -/
theorem repeatSlice_succ (n : Nat) (elem : List α) :
    repeatSlice (n + 1) elem = repeatSlice n elem ++ elem :=
  rfl

/-- Length of `repeatSlice n elem` is `n * elem.length`. -/
theorem repeatSlice_length (n : Nat) (elem : List α) :
    (repeatSlice n elem).length = n * elem.length := by
  induction n with
  | zero =>
    rw [repeatSlice_zero, Nat.zero_mul]
    rfl
  | succ k ih =>
    rw [repeatSlice_succ, List.length_append, ih, Nat.succ_mul]

/-- Prepending `elem` onto `repeatSlice n elem` equals appending `elem`. -/
theorem repeatSlice_cons_head (n : Nat) (elem : List α) :
    elem ++ repeatSlice n elem = repeatSlice n elem ++ elem := by
  induction n with
  | zero => exact List.append_nil elem
  | succ k ih =>
    rw [repeatSlice_succ, ← List.append_assoc elem (repeatSlice k elem) elem, ih]

/-- Stride projection: slicing `repeatSlice n elem` at `(i * elem.length,
elem.length)` for `i < n` recovers `elem`. -/
theorem repeatSlice_project_elem (n i : Nat) (elem : List α) (hLt : i < n) :
    ((repeatSlice n elem).drop (i * elem.length)).take elem.length = elem := by
  induction n generalizing i with
  | zero => exact False.elim (Nat.not_lt_zero i hLt)
  | succ k ih =>
    rw [repeatSlice_succ, ← repeatSlice_cons_head k elem]
    cases i with
    | zero =>
      rw [Nat.zero_mul]
      exact listTake_append_exact elem (repeatSlice k elem)
    | succ i' =>
      have hLt' : i' < k := Nat.lt_of_succ_lt_succ hLt
      rw [Nat.succ_mul, Nat.add_comm (i' * elem.length) elem.length,
        listDrop_add elem.length (i' * elem.length) (elem ++ repeatSlice k elem),
        listDrop_append_exact elem (repeatSlice k elem)]
      exact ih i' hLt'

/-- Contiguous splice fusion: splicing `mid₁` at `off` and then `mid₂`
immediately adjacent at `off + mid₁.length` equals a single splice of
`mid₁ ++ mid₂` at `off`. -/
theorem listSplice_contiguous_fuse (xs : List α) (off : Nat)
    (mid₁ mid₂ : List α) (h₁ : off + mid₁.length ≤ xs.length) :
    listSplice (listSplice xs off mid₁) (off + mid₁.length) mid₂ =
      listSplice xs off (mid₁ ++ mid₂) := by
  have hOff : off ≤ xs.length := Nat.le_trans (Nat.le_add_right off mid₁.length) h₁
  have hPreLen : (xs.take off ++ mid₁).length = off + mid₁.length := by
    rw [List.length_append, listTake_length_of_le off xs hOff]
  have hTake :
      (listSplice xs off mid₁).take (off + mid₁.length) = xs.take off ++ mid₁ :=
    listTake_append_of_len (off + mid₁.length) (xs.take off ++ mid₁)
      (xs.drop (off + mid₁.length)) hPreLen
  have hDrop :
      (listSplice xs off mid₁).drop (off + mid₁.length + mid₂.length) =
        xs.drop (off + (mid₁ ++ mid₂).length) := by
    rw [listDrop_add (off + mid₁.length) mid₂.length (listSplice xs off mid₁),
      listSplice_drop_suffix xs off mid₁ h₁,
      ← listDrop_add (off + mid₁.length) mid₂.length xs,
      Nat.add_assoc off mid₁.length mid₂.length, List.length_append]
  unfold listSplice
  change (listSplice xs off mid₁).take (off + mid₁.length) ++ mid₂ ++
      (listSplice xs off mid₁).drop (off + mid₁.length + mid₂.length) =
    xs.take off ++ (mid₁ ++ mid₂) ++ xs.drop (off + (mid₁ ++ mid₂).length)
  rw [hTake, hDrop, List.append_assoc (xs.take off) mid₁ mid₂]

/-- Splicing the empty list at offset `0` is the identity. -/
theorem listSplice_zero_nil (xs : List α) : listSplice xs 0 [] = xs :=
  rfl

/-- Splicing a full-length replacement at offset `0` replaces the whole list. -/
theorem listSplice_zero_full (xs ys : List α) (hLen : ys.length = xs.length) :
    listSplice xs 0 ys = ys := by
  unfold listSplice
  rw [Nat.zero_add, hLen]
  have hDropNil : xs.drop xs.length = [] := by
    have hLenZero : (xs.drop xs.length).length = 0 := by
      rw [listDrop_length, Nat.sub_self]
    cases hd : xs.drop xs.length with
    | nil => rfl
    | cons _ _ =>
      rw [hd] at hLenZero
      cases hLenZero
  rw [hDropNil]
  exact List.append_nil ys

/-- Replicates `x` exactly `n` times via `@Nat.rec` (`0` `._unsafe_rec`). -/
def replicateComp (n : Nat) (x : α) : List α :=
  @Nat.rec (fun _ => List α) [] (fun _ acc => x :: acc) n

/-- Length of `replicateComp n x` is `n`. -/
theorem replicateComp_length (n : Nat) (x : α) :
    (replicateComp n x).length = n := by
  induction n with
  | zero => rfl
  | succ _ ih => exact congrArg Nat.succ ih

/-- Mapping `f` over `replicateComp n x` equals `replicateComp n (f x)`. -/
theorem map_replicateComp {β : Type v} (f : α → β) (n : Nat) (x : α) :
    (replicateComp n x).foldr (fun y acc => f y :: acc) [] =
      replicateComp n (f x) := by
  induction n with
  | zero => rfl
  | succ _ ih => exact congrArg (List.cons (f x)) ih

/-- `foldr`-based list map (`0` `._unsafe_rec`). -/
def listMapComp {β : Type v} (f : α → β) (xs : List α) : List β :=
  xs.foldr (fun x acc => f x :: acc) []

/-- `listMapComp` preserves length. -/
theorem listMapComp_length {β : Type v} (f : α → β) :
    ∀ (xs : List α), (listMapComp f xs).length = xs.length
  | [] => rfl
  | _ :: tl => congrArg Nat.succ (listMapComp_length f tl)

/-- `listMapComp` distributes over `++`. -/
theorem listMapComp_append {β : Type v} (f : α → β) (xs ys : List α) :
    listMapComp f (xs ++ ys) = listMapComp f xs ++ listMapComp f ys := by
  induction xs with
  | nil => rfl
  | cons hd _ ih => exact congrArg (List.cons (f hd)) ih

/-- `listMapComp` on `replicateComp`. -/
theorem listMapComp_replicateComp {β : Type v} (f : α → β) (n : Nat) (x : α) :
    listMapComp f (replicateComp n x) = replicateComp n (f x) :=
  map_replicateComp f n x

end Helpers

/-! ## Part II: Mixed-`InitMask` Byte-Run Algebra (`ByteRunAtom`, `ByteRunCodec`, `ByteRun`) -/

/-- Atomic abstract byte carrying initialization mask and optional pointer
provenance `Prov`:
- `.uninitPad`: uninitialized padding byte,
- `.initPlain b`: initialized scalar byte without pointer provenance,
- `.initProv b prov`: initialized byte carrying pointer provenance `prov`. -/
inductive ByteRunAtom (Prov : Type u) : Type u where
  | uninitPad : ByteRunAtom Prov
  | initPlain (b : UInt8) : ByteRunAtom Prov
  | initProv (b : UInt8) (prov : Prov) : ByteRunAtom Prov

/-- Lawful injection/projection carrier embedding `ByteRunAtom Prov` into a
byte-store slot type `Byte` with exact round-trip preservation of `.uninitPad`,
`.initPlain`, and `.initProv`. -/
structure ByteRunCodec (Prov : Type u) (Byte : Type v) where
  /-- Embeds an abstract byte atom into a store slot. -/
  encodeAtom : ByteRunAtom Prov → Byte
  /-- Projects a store slot back to its abstract byte atom when well-formed. -/
  decodeAtom? : Byte → Option (ByteRunAtom Prov)
  /-- Round-trip law: decoding an encoded atom recovers it verbatim. -/
  decode_encode : ∀ a : ByteRunAtom Prov, decodeAtom? (encodeAtom a) = some a

namespace ByteRunCodec

/-- Canonical identity codec on `ByteRunAtom Prov`. -/
def id (Prov : Type u) : ByteRunCodec Prov (ByteRunAtom Prov) where
  encodeAtom a := a
  decodeAtom? a := some a
  decode_encode _ := rfl

/-- Canonical `Option UInt8` codec for provenance-free byte stores (such as
uninitialized/initialized `Option UInt8` buffers where `Prov = PEmpty`). -/
def optionUInt8 : ByteRunCodec PEmpty.{1} (Option UInt8) where
  encodeAtom
    | .uninitPad => none
    | .initPlain b => some b
    | .initProv _ p => p.elim
  decodeAtom?
    | none => some .uninitPad
    | some b => some (.initPlain b)
  decode_encode a := by
    cases a with
    | uninitPad => rfl
    | initPlain _ => rfl
    | initProv _ p => exact p.elim

/-- Canonical `Option (UInt8 × Option Prov)` codec modeling `AbstractByte`
stores with full uninitialized padding and optional pointer provenance. -/
def optionProv (Prov : Type u) :
    ByteRunCodec Prov (Option (UInt8 × Option Prov)) where
  encodeAtom
    | .uninitPad => none
    | .initPlain b => some (b, none)
    | .initProv b p => some (b, some p)
  decodeAtom?
    | none => some .uninitPad
    | some (b, none) => some (.initPlain b)
    | some (b, some p) => some (.initProv b p)
  decode_encode a := by
    cases a with
    | uninitPad => rfl
    | initPlain _ => rfl
    | initProv _ _ => rfl

/-- Lifts any `ByteCodec Byte` (such as `ByteCodec.uint8`) into a
provenance-free `ByteRunCodec PEmpty (Option Byte)` where `none` represents
`.uninitPad`. -/
def ofByteCodec {Byte : Type v} (c : ByteCodec Byte) :
    ByteRunCodec PEmpty.{1} (Option Byte) where
  encodeAtom
    | .uninitPad => none
    | .initPlain b => some (c.enc b.toBitVec)
    | .initProv _ p => p.elim
  decodeAtom?
    | none => some .uninitPad
    | some slot =>
      match c.dec slot with
      | none => none
      | some bv => some (.initPlain (UInt8.ofBitVec bv))
  decode_encode a := by
    cases a with
    | uninitPad => rfl
    | initPlain b =>
      dsimp only
      rw [c.dec_enc b.toBitVec]
    | initProv _ p => exact p.elim

/-- Strict scalar `ByteCodec` derived from a `ByteRunCodec`: decodes only
`.initPlain` scalar bytes, failing closed (`none`) on `.uninitPad` and
`.initProv`. -/
def toByteCodec {Prov : Type u} {Byte : Type v}
    (c : ByteRunCodec Prov Byte) : ByteCodec Byte where
  enc bv := c.encodeAtom (.initPlain (UInt8.ofBitVec bv))
  dec slot :=
    match c.decodeAtom? slot with
    | some (.initPlain b) => some b.toBitVec
    | _ => none
  dec_enc bv := by
    change (match c.decodeAtom? (c.encodeAtom (.initPlain (UInt8.ofBitVec bv))) with
      | some (.initPlain b) => some b.toBitVec
      | _ => none) = some bv
    rw [c.decode_encode (.initPlain (UInt8.ofBitVec bv))]

/-- Initialized-byte `ByteCodec` derived from a `ByteRunCodec`: decodes both
`.initPlain` and `.initProv` bytes to their `BitVec 8` value, failing closed
(`none`) on `.uninitPad`. -/
def toInitByteCodec {Prov : Type u} {Byte : Type v}
    (c : ByteRunCodec Prov Byte) : ByteCodec Byte where
  enc bv := c.encodeAtom (.initPlain (UInt8.ofBitVec bv))
  dec slot :=
    match c.decodeAtom? slot with
    | some (.initPlain b) => some b.toBitVec
    | some (.initProv b _) => some b.toBitVec
    | _ => none
  dec_enc bv := by
    change (match c.decodeAtom? (c.encodeAtom (.initPlain (UInt8.ofBitVec bv))) with
      | some (.initPlain b) => some b.toBitVec
      | some (.initProv b _) => some b.toBitVec
      | _ => none) = some bv
    rw [c.decode_encode (.initPlain (UInt8.ofBitVec bv))]

/-- `.uninitPad` encoded via `c` fails closed to `none` under `c.toByteCodec`. -/
theorem toByteCodec_uninit_none {Prov : Type u} {Byte : Type v}
    (c : ByteRunCodec Prov Byte) :
    c.toByteCodec.dec (c.encodeAtom .uninitPad) = none := by
  unfold toByteCodec
  dsimp only
  rw [c.decode_encode .uninitPad]

/-- `.uninitPad` encoded via `c` fails closed to `none` under
`c.toInitByteCodec`. -/
theorem toInitByteCodec_uninit_none {Prov : Type u} {Byte : Type v}
    (c : ByteRunCodec Prov Byte) :
    c.toInitByteCodec.dec (c.encodeAtom .uninitPad) = none := by
  unfold toInitByteCodec
  dsimp only
  rw [c.decode_encode .uninitPad]

/-- `.initProv` encoded via `c` fails closed to `none` under strict scalar
`c.toByteCodec` (preventing provenance erasure in scalar-only loads). -/
theorem toByteCodec_prov_none {Prov : Type u} {Byte : Type v}
    (c : ByteRunCodec Prov Byte) (b : UInt8) (p : Prov) :
    c.toByteCodec.dec (c.encodeAtom (.initProv b p)) = none := by
  unfold toByteCodec
  dsimp only
  rw [c.decode_encode (.initProv b p)]

/-- `encodeAtom` is injective on `ByteRunAtom Prov`. -/
theorem encodeAtom_injective {Prov : Type u} {Byte : Type v}
    (c : ByteRunCodec Prov Byte) {a₁ a₂ : ByteRunAtom Prov}
    (h : c.encodeAtom a₁ = c.encodeAtom a₂) : a₁ = a₂ := by
  have hDec : c.decodeAtom? (c.encodeAtom a₁) = c.decodeAtom? (c.encodeAtom a₂) :=
    congrArg c.decodeAtom? h
  rw [c.decode_encode a₁, c.decode_encode a₂] at hDec
  exact Option.some.inj hDec

/-- Encoding `.uninitPad` never collides with encoding `.initPlain b`. -/
theorem encodeAtom_uninit_ne_plain {Prov : Type u} {Byte : Type v}
    (c : ByteRunCodec Prov Byte) (b : UInt8) :
    c.encodeAtom .uninitPad ≠ c.encodeAtom (.initPlain b) := by
  intro hEq
  have hA := c.encodeAtom_injective hEq
  cases hA

/-- Encoding `.initProv b p` never collides with encoding `.initPlain b'`. -/
theorem encodeAtom_prov_ne_plain {Prov : Type u} {Byte : Type v}
    (c : ByteRunCodec Prov Byte) (b b' : UInt8) (p : Prov) :
    c.encodeAtom (.initProv b p) ≠ c.encodeAtom (.initPlain b') := by
  intro hEq
  have hA := c.encodeAtom_injective hEq
  cases hA

end ByteRunCodec

/-- Plain initialized-only byte codec for raw `UInt8` stores (which have 256
states and therefore cannot losslessly represent a 257th `.uninitPad` state).
Round-trips every `UInt8` scalar byte cleanly. -/
structure PlainByteRunCodec (Byte : Type v) where
  encodePlain : UInt8 → Byte
  decodePlain? : Byte → Option UInt8
  decode_encode : ∀ b : UInt8, decodePlain? (encodePlain b) = some b

namespace PlainByteRunCodec

/-- Canonical identity plain-byte codec on raw `UInt8`. -/
def uint8 : PlainByteRunCodec UInt8 where
  encodePlain b := b
  decodePlain? b := some b
  decode_encode _ := rfl

/-- Canonical plain-byte codec on `Option UInt8`. -/
def optionUInt8 : PlainByteRunCodec (Option UInt8) where
  encodePlain b := some b
  decodePlain? slot := slot
  decode_encode _ := rfl

/-- Any full `ByteRunCodec Prov Byte` restricts to a `PlainByteRunCodec Byte`.
-/
def ofByteRunCodec {Prov : Type u} {Byte : Type v}
    (c : ByteRunCodec Prov Byte) : PlainByteRunCodec Byte where
  encodePlain b := c.encodeAtom (.initPlain b)
  decodePlain? slot :=
    match c.decodeAtom? slot with
    | some (.initPlain b) => some b
    | _ => none
  decode_encode b := by
    change (match c.decodeAtom? (c.encodeAtom (.initPlain b)) with
      | some (.initPlain x) => some x
      | _ => none) = some b
    rw [c.decode_encode (.initPlain b)]

end PlainByteRunCodec

/-- Contiguous mixed-`InitMask` / provenance byte run:
- `.initPlain bytes`: initialized scalar bytes without provenance,
- `.initProv bytes prov`: initialized bytes carrying pointer provenance `prov`,
- `.uninitPad len`: `len` contiguous uninitialized padding bytes. -/
inductive ByteRun (Prov : Type u) : Type u where
  | initPlain (bytes : List UInt8) : ByteRun Prov
  | initProv (bytes : List UInt8) (prov : Prov) : ByteRun Prov
  | uninitPad (len : Nat) : ByteRun Prov

namespace ByteRun

/-- Byte length of a single `ByteRun`. -/
def byteLen {Prov : Type u} (r : ByteRun Prov) : Nat :=
  match r with
  | .initPlain bs => bs.length
  | .initProv bs _ => bs.length
  | .uninitPad len => len

/-- Expands a single `ByteRun` into abstract `ByteRunAtom`s. -/
def toAtoms {Prov : Type u} (r : ByteRun Prov) : List (ByteRunAtom Prov) :=
  match r with
  | .initPlain bs => listMapComp ByteRunAtom.initPlain bs
  | .initProv bs p => listMapComp (fun b => ByteRunAtom.initProv b p) bs
  | .uninitPad len => replicateComp len .uninitPad

/-- Encodes a single `ByteRun` into store bytes using `codec`. -/
def toBytes {Prov : Type u} {Byte : Type v}
    (codec : ByteRunCodec Prov Byte) (r : ByteRun Prov) : List Byte :=
  listMapComp codec.encodeAtom r.toAtoms

/-- Length of `r.toAtoms` equals `r.byteLen`. -/
theorem toAtoms_length {Prov : Type u} (r : ByteRun Prov) :
    r.toAtoms.length = r.byteLen := by
  cases r with
  | initPlain bs => exact listMapComp_length ByteRunAtom.initPlain bs
  | initProv bs p => exact listMapComp_length (fun b => ByteRunAtom.initProv b p) bs
  | uninitPad len => exact replicateComp_length len (ByteRunAtom.uninitPad : ByteRunAtom Prov)

/-- Length of `r.toBytes codec` equals `r.byteLen`. -/
theorem toBytes_length {Prov : Type u} {Byte : Type v}
    (codec : ByteRunCodec Prov Byte) (r : ByteRun Prov) :
    (r.toBytes codec).length = r.byteLen :=
  (listMapComp_length codec.encodeAtom r.toAtoms).trans r.toAtoms_length

end ByteRun

/-- Total byte length of a list of `ByteRun`s (`List.foldr`, `0`
`._unsafe_rec`). -/
def runsByteLen {Prov : Type u} (runs : List (ByteRun Prov)) : Nat :=
  runs.foldr (fun r acc => r.byteLen + acc) 0

/-- Flattens a list of `ByteRun`s into `List (ByteRunAtom Prov)`. -/
def flattenByteRunAtoms {Prov : Type u} (runs : List (ByteRun Prov)) :
    List (ByteRunAtom Prov) :=
  runs.foldr (fun r acc => r.toAtoms ++ acc) []

/-- Flattens a list of `ByteRun`s into encoded store bytes `List Byte` via
`codec`. -/
def flattenByteRuns {Prov : Type u} {Byte : Type v}
    (codec : ByteRunCodec Prov Byte) (runs : List (ByteRun Prov)) : List Byte :=
  runs.foldr (fun r acc => r.toBytes codec ++ acc) []

/-- Decodes a list of store bytes into `List (ByteRunAtom Prov)`, failing
closed (`none`) if any byte fails `codec.decodeAtom?`. -/
def decodeAtoms? {Prov : Type u} {Byte : Type v}
    (codec : ByteRunCodec Prov Byte) (bs : List Byte) :
    Option (List (ByteRunAtom Prov)) :=
  bs.foldr
    (fun b acc =>
      match codec.decodeAtom? b with
      | none => none
      | some a =>
        match acc with
        | none => none
        | some rest => some (a :: rest))
    (some [])

/-- Repeats a run layout `n` times (`[T; n]`). -/
def repeatByteRuns {Prov : Type u} (n : Nat) (runs : List (ByteRun Prov)) :
    List (ByteRun Prov) :=
  repeatSlice n runs

/-- Length of `runsByteLen` distributes over `++`. -/
theorem runsByteLen_append {Prov : Type u} (r₁ r₂ : List (ByteRun Prov)) :
    runsByteLen (r₁ ++ r₂) = runsByteLen r₁ + runsByteLen r₂ := by
  induction r₁ with
  | nil => exact (Nat.zero_add (runsByteLen r₂)).symm
  | cons hd tl ih =>
    change hd.byteLen + runsByteLen (tl ++ r₂) =
      (hd.byteLen + runsByteLen tl) + runsByteLen r₂
    rw [ih, Nat.add_assoc]

/-- Length of `repeatByteRuns n runs` is `n * runsByteLen runs`. -/
theorem runsByteLen_repeat {Prov : Type u} (n : Nat)
    (runs : List (ByteRun Prov)) :
    runsByteLen (repeatByteRuns n runs) = n * runsByteLen runs := by
  induction n with
  | zero =>
    rw [Nat.zero_mul]
    rfl
  | succ k ih =>
    change runsByteLen (repeatByteRuns k runs ++ runs) = (k + 1) * runsByteLen runs
    rw [runsByteLen_append, ih, Nat.succ_mul]

/-- Exact length of `flattenByteRunAtoms`. -/
theorem flattenByteRunAtoms_length {Prov : Type u}
    (runs : List (ByteRun Prov)) :
    (flattenByteRunAtoms runs).length = runsByteLen runs := by
  induction runs with
  | nil => rfl
  | cons hd tl ih =>
    change (hd.toAtoms ++ flattenByteRunAtoms tl).length =
      hd.byteLen + runsByteLen tl
    rw [List.length_append, hd.toAtoms_length, ih]

/-- Exact length of `flattenByteRuns`. -/
theorem flattenByteRuns_length {Prov : Type u} {Byte : Type v}
    (codec : ByteRunCodec Prov Byte) (runs : List (ByteRun Prov)) :
    (flattenByteRuns codec runs).length = runsByteLen runs := by
  induction runs with
  | nil => rfl
  | cons hd tl ih =>
    change (hd.toBytes codec ++ flattenByteRuns codec tl).length =
      hd.byteLen + runsByteLen tl
    rw [List.length_append, hd.toBytes_length codec, ih]

/-- `flattenByteRuns` equals mapping `codec.encodeAtom` over
`flattenByteRunAtoms`. -/
theorem flattenByteRuns_eq_map_atoms {Prov : Type u} {Byte : Type v}
    (codec : ByteRunCodec Prov Byte) (runs : List (ByteRun Prov)) :
    flattenByteRuns codec runs =
      listMapComp codec.encodeAtom (flattenByteRunAtoms runs) := by
  induction runs with
  | nil => rfl
  | cons hd tl ih =>
    change hd.toBytes codec ++ flattenByteRuns codec tl =
      listMapComp codec.encodeAtom (hd.toAtoms ++ flattenByteRunAtoms tl)
    rw [listMapComp_append, ih]
    rfl

/-- Homomorphism of `flattenByteRuns` over `++`. -/
theorem flattenByteRuns_append {Prov : Type u} {Byte : Type v}
    (codec : ByteRunCodec Prov Byte) (r₁ r₂ : List (ByteRun Prov)) :
    flattenByteRuns codec (r₁ ++ r₂) =
      flattenByteRuns codec r₁ ++ flattenByteRuns codec r₂ := by
  induction r₁ with
  | nil => rfl
  | cons hd tl ih =>
    change hd.toBytes codec ++ flattenByteRuns codec (tl ++ r₂) =
      (hd.toBytes codec ++ flattenByteRuns codec tl) ++ flattenByteRuns codec r₂
    rw [ih, List.append_assoc]

/-- Commutation of `flattenByteRuns` with `repeatByteRuns`. -/
theorem flattenByteRuns_repeat {Prov : Type u} {Byte : Type v}
    (codec : ByteRunCodec Prov Byte) (n : Nat) (runs : List (ByteRun Prov)) :
    flattenByteRuns codec (repeatByteRuns n runs) =
      repeatSlice n (flattenByteRuns codec runs) := by
  induction n with
  | zero => rfl
  | succ k ih =>
    change flattenByteRuns codec (repeatSlice k runs ++ runs) =
      repeatSlice k (flattenByteRuns codec runs) ++ flattenByteRuns codec runs
    rw [flattenByteRuns_append, ← ih]
    rfl

/-- Exact length of `flattenByteRuns codec (repeatByteRuns n runs)`. -/
theorem flattenByteRuns_repeat_length {Prov : Type u} {Byte : Type v}
    (codec : ByteRunCodec Prov Byte) (n : Nat) (runs : List (ByteRun Prov)) :
    (flattenByteRuns codec (repeatByteRuns n runs)).length =
      n * runsByteLen runs := by
  rw [flattenByteRuns_repeat, repeatSlice_length, flattenByteRuns_length]

/-- Round-trip decoding of encoded atoms recovers the atom list verbatim. -/
theorem decodeAtoms?_listMapComp {Prov : Type u} {Byte : Type v}
    (codec : ByteRunCodec Prov Byte) (atoms : List (ByteRunAtom Prov)) :
    decodeAtoms? codec (listMapComp codec.encodeAtom atoms) = some atoms := by
  induction atoms with
  | nil => rfl
  | cons a tl ih =>
    change (match codec.decodeAtom? (codec.encodeAtom a) with
      | none => none
      | some x =>
        match decodeAtoms? codec (listMapComp codec.encodeAtom tl) with
        | none => none
        | some rest => some (x :: rest)) = some (a :: tl)
    rw [codec.decode_encode a, ih]

/-- Round-trip decoding of `flattenByteRuns codec runs` recovers
`flattenByteRunAtoms runs` (preserving all `.uninitPad` and `.initProv` atoms
verbatim). -/
theorem decodeAtoms?_flattenByteRuns {Prov : Type u} {Byte : Type v}
    (codec : ByteRunCodec Prov Byte) (runs : List (ByteRun Prov)) :
    decodeAtoms? codec (flattenByteRuns codec runs) =
      some (flattenByteRunAtoms runs) := by
  rw [flattenByteRuns_eq_map_atoms]
  exact decodeAtoms?_listMapComp codec (flattenByteRunAtoms runs)

/-- Exact sub-slice projection of `focus` inside `pre ++ (focus :: post)`. -/
theorem projectRunAtSplit {Prov : Type u} {Byte : Type v}
    (codec : ByteRunCodec Prov Byte) (pre : List (ByteRun Prov))
    (focus : ByteRun Prov) (post : List (ByteRun Prov)) :
    ((flattenByteRuns codec (pre ++ (focus :: post))).drop (runsByteLen pre)).take
        focus.byteLen = focus.toBytes codec := by
  rw [flattenByteRuns_append, ← flattenByteRuns_length codec pre]
  change ((flattenByteRuns codec pre ++
      (focus.toBytes codec ++ flattenByteRuns codec post)).drop
    (flattenByteRuns codec pre).length).take focus.byteLen = focus.toBytes codec
  rw [listDrop_append_exact (flattenByteRuns codec pre),
    ← focus.toBytes_length codec,
    listTake_append_exact (focus.toBytes codec) (flattenByteRuns codec post)]

/-- Element-stride projection: for `i < n`, slicing
`flattenByteRuns codec (repeatByteRuns n runs)` at `(i * runsByteLen runs,
runsByteLen runs)` equals `flattenByteRuns codec runs`. -/
theorem flattenByteRuns_repeat_project_elem {Prov : Type u} {Byte : Type v}
    (codec : ByteRunCodec Prov Byte) (n i : Nat) (runs : List (ByteRun Prov))
    (hLt : i < n) :
    ((flattenByteRuns codec (repeatByteRuns n runs)).drop
        (i * runsByteLen runs)).take (runsByteLen runs) =
      flattenByteRuns codec runs := by
  rw [flattenByteRuns_repeat, ← flattenByteRuns_length codec runs]
  exact repeatSlice_project_elem n i (flattenByteRuns codec runs) hLt

/-! ## Part III: Overlap-Tolerant Range Copy & `[T; N]` Repeat Fusion -/

section CopyAlgebra

variable {Mem : Type u} {Addr : Type v} {Byte : Type w}
  [ops : ByteStoreOps Mem Addr Byte]

/-- Overlap-tolerant untyped byte-range copy (`src.get m` then `dst.set m`),
failing closed (`none`) when `src.len = 0`, `dst.len = 0`, `src.len ≠ dst.len`,
out-of-bounds, or unwritable. Preserves `.uninitPad` and `.initProv` verbatim
and supports arbitrary overlap (including `src = dst`). -/
def copyRangeComp (src dst : ByteSubLens Addr) (m : Mem) : Option Mem :=
  match Nat.beq src.len 0 || Nat.beq dst.len 0 || !(Nat.beq src.len dst.len) with
  | true => none
  | false =>
    match src.get m with
    | none => none
    | some bs => dst.set m bs

/-- Sequential `n`-element repeat copy into `{ addr := dstAddr, offset :=
dstOff + i * src.len, len := src.len }` for `0 ≤ i < n` via `@Nat.rec` (`0`
`._unsafe_rec`), failing closed (`none`) when `n = 0` or `src.len = 0`. -/
def copyRepeatedlyComp (src : ByteSubLens Addr) (dstAddr : Addr)
    (dstOff n : Nat) (m : Mem) : Option Mem :=
  match Nat.beq n 0 || Nat.beq src.len 0 with
  | true => none
  | false =>
    @Nat.rec (fun _ => Option Mem) (some m)
      (fun i acc =>
        match acc with
        | none => none
        | some mCur =>
          copyRangeComp src
            { addr := dstAddr, offset := dstOff + i * src.len, len := src.len }
            mCur)
      n

/-- Fused single-write `[T; n]` repeat store of `repeatByteRuns n runs` into
`[dstOff, dstOff + n * runsByteLen runs)`. -/
def writeRepeatRunsComp {Prov : Type x} (codec : ByteRunCodec Prov Byte)
    (dstAddr : Addr) (dstOff n : Nat) (runs : List (ByteRun Prov)) (m : Mem) :
    Option Mem :=
  ({ addr := dstAddr, offset := dstOff, len := n * runsByteLen runs } :
      ByteSubLens Addr).set m (flattenByteRuns codec (repeatByteRuns n runs))

/-- Fail-closed: `copyRangeComp` rejects `src.len = 0`. -/
theorem copyRangeComp_none_of_src_zero {src dst : ByteSubLens Addr} (m : Mem)
    (hZero : src.len = 0) : copyRangeComp src dst m = none := by
  unfold copyRangeComp
  rw [hZero]
  rfl

/-- Fail-closed: `copyRangeComp` rejects `dst.len = 0`. -/
theorem copyRangeComp_none_of_dst_zero {src dst : ByteSubLens Addr} (m : Mem)
    (hZero : dst.len = 0) : copyRangeComp src dst m = none := by
  unfold copyRangeComp
  rw [hZero]
  cases Nat.beq src.len 0 <;> rfl

/-- Fail-closed: `copyRangeComp` rejects `src.len ≠ dst.len`. -/
theorem copyRangeComp_none_of_len_ne {src dst : ByteSubLens Addr} (m : Mem)
    (hNe : src.len ≠ dst.len) : copyRangeComp src dst m = none := by
  unfold copyRangeComp
  rw [natBeq_false_of_not_eq hNe]
  cases Nat.beq src.len 0 <;> cases Nat.beq dst.len 0 <;> rfl

/-- Fail-closed: `copyRangeComp` returns `none` when `src.get m = none`. -/
theorem copyRangeComp_none_of_src_none {src dst : ByteSubLens Addr} {m : Mem}
    (hNone : src.get m = none) : copyRangeComp src dst m = none := by
  unfold copyRangeComp
  cases (Nat.beq src.len 0 || Nat.beq dst.len 0 || !(Nat.beq src.len dst.len)) with
  | true => rfl
  | false => rw [hNone]

/-- Fail-closed: `copyRepeatedlyComp` rejects `n = 0`. -/
theorem copyRepeatedlyComp_none_of_n_zero (src : ByteSubLens Addr)
    (dstAddr : Addr) (dstOff : Nat) (m : Mem) :
    copyRepeatedlyComp src dstAddr dstOff 0 m = none :=
  rfl

/-- Fail-closed: `copyRepeatedlyComp` rejects `src.len = 0`. -/
theorem copyRepeatedlyComp_none_of_src_zero {src : ByteSubLens Addr}
    (dstAddr : Addr) (dstOff n : Nat) (m : Mem) (hZero : src.len = 0) :
    copyRepeatedlyComp src dstAddr dstOff n m = none := by
  unfold copyRepeatedlyComp
  rw [hZero]
  cases Nat.beq n 0 <;> rfl

/-- Inversion of a successful `copyRangeComp`. -/
theorem copyRangeComp_inv {src dst : ByteSubLens Addr} {m m' : Mem}
    (h : copyRangeComp src dst m = some m') :
    0 < src.len ∧ src.len = dst.len ∧
      ∃ bs : List Byte, src.get m = some bs ∧ dst.set m bs = some m' := by
  unfold copyRangeComp at h
  cases hSrcZ : Nat.beq src.len 0 with
  | true =>
    rw [hSrcZ] at h
    cases h
  | false =>
    cases hDstZ : Nat.beq dst.len 0 with
    | true =>
      rw [hSrcZ, hDstZ] at h
      cases h
    | false =>
      cases hEqLen : Nat.beq src.len dst.len with
      | false =>
        rw [hSrcZ, hDstZ, hEqLen] at h
        cases h
      | true =>
        rw [hSrcZ, hDstZ, hEqLen] at h
        have hPos : 0 < src.len := by
          cases hs : src.len with
          | zero => rw [hs] at hSrcZ; cases hSrcZ
          | succ _ => exact Nat.zero_lt_succ _
        have hLenEq : src.len = dst.len := Nat.eq_of_beq_eq_true hEqLen
        cases hGet : src.get m with
        | none =>
          rw [hGet] at h
          cases h
        | some bs =>
          rw [hGet] at h
          exact ⟨hPos, hLenEq, bs, rfl, h⟩

/-- Reduction of `copyRangeComp` when `0 < src.len`, `src.len = dst.len`, and
`src.get m = some bs`. -/
theorem copyRangeComp_of_get {src dst : ByteSubLens Addr} {m : Mem}
    {bs : List Byte} (hPos : 0 < src.len) (hLenEq : src.len = dst.len)
    (hGet : src.get m = some bs) :
    copyRangeComp src dst m = dst.set m bs := by
  have hSrcZ : Nat.beq src.len 0 = false :=
    natBeq_false_of_not_eq (fun hZ => Nat.not_lt_zero 0 (hZ ▸ hPos))
  have hDstZ : Nat.beq dst.len 0 = false :=
    natBeq_false_of_not_eq (fun hZ => Nat.not_lt_zero 0 ((hLenEq.trans hZ) ▸ hPos))
  have hEqB : Nat.beq src.len dst.len = true := by
    rw [hLenEq]
    exact Nat.beq_refl dst.len
  unfold copyRangeComp
  rw [hSrcZ, hDstZ, hEqB]
  change (match src.get m with | none => none | some bs => dst.set m bs) = _
  rw [hGet]

/-- Auxiliary metadata preservation for `copyRangeComp`. -/
theorem copyRangeComp_preserves {V : Sort y} {proj : Mem → V}
    (hPres : ops.WritePreserves proj) {src dst : ByteSubLens Addr}
    {m m' : Mem} (h : copyRangeComp src dst m = some m') :
    proj m' = proj m := by
  let ⟨_, _, _, _, hSet⟩ := copyRangeComp_inv h
  exact ByteSubLens.set_preserves hPres hSet

/-- Auxiliary metadata preservation for `copyRepeatedlyComp`. -/
theorem copyRepeatedlyComp_preserves {V : Sort y} {proj : Mem → V}
    (hPres : ops.WritePreserves proj) {src : ByteSubLens Addr}
    {dstAddr : Addr} {dstOff n : Nat} {m m' : Mem}
    (hRep : copyRepeatedlyComp src dstAddr dstOff n m = some m') :
    proj m' = proj m := by
  unfold copyRepeatedlyComp at hRep
  cases hGuard : (Nat.beq n 0 || Nat.beq src.len 0) with
  | true => rw [hGuard] at hRep; cases hRep
  | false =>
    rw [hGuard] at hRep
    have hAux :
        ∀ (j : Nat) mOut,
          @Nat.rec (fun _ => Option Mem) (some m)
            (fun i acc =>
              match acc with
              | none => none
              | some mCur =>
                copyRangeComp src
                  { addr := dstAddr, offset := dstOff + i * src.len,
                    len := src.len } mCur) j = some mOut →
          proj mOut = proj m := by
      intro j
      induction j with
      | zero =>
        intro mOut hEq
        have hM : m = mOut := Option.some.inj hEq
        rw [← hM]
      | succ k ih =>
        intro mOut hStep
        change (match @Nat.rec (fun _ => Option Mem) (some m)
            (fun i acc =>
              match acc with
              | none => none
              | some mCur =>
                copyRangeComp src
                  { addr := dstAddr, offset := dstOff + i * src.len,
                    len := src.len } mCur) k with
          | none => none
          | some mCur =>
            copyRangeComp src
              { addr := dstAddr, offset := dstOff + k * src.len,
                len := src.len } mCur) = some mOut at hStep
        cases hPrev : @Nat.rec (fun _ => Option Mem) (some m)
            (fun i acc =>
              match acc with
              | none => none
              | some mCur =>
                copyRangeComp src
                  { addr := dstAddr, offset := dstOff + i * src.len,
                    len := src.len } mCur) k with
        | none => rw [hPrev] at hStep; cases hStep
        | some mK =>
          rw [hPrev] at hStep
          dsimp only at hStep
          exact (copyRangeComp_preserves hPres hStep).trans (ih mK hPrev)
    exact hAux n m' hRep

variable [LawfulByteStoreOps Mem Addr Byte]

/-- Existence of `copyRangeComp` whenever `src` and `dst` have equal length and
are both readable in `m` (independent of whether `src` and `dst` overlap!). -/
theorem copyRangeComp_isSome_of_get {src dst : ByteSubLens Addr} {m : Mem}
    {bs oldDst : List Byte} (hLenEq : src.len = dst.len)
    (hSrc : src.get m = some bs) (hDst : dst.get m = some oldDst) :
    ∃ m', copyRangeComp src dst m = some m' := by
  have hPos : 0 < src.len := (ByteSubLens.get_inv hSrc).1
  have hBsLen : bs.length = dst.len := (ByteSubLens.get_len hSrc).trans hLenEq
  rw [copyRangeComp_of_get hPos hLenEq hSrc]
  exact ByteSubLens.set_isSome_of_get bs hDst hBsLen

/-- Self-copy idempotence (`src = dst`): copying a readable slice onto itself
succeeds and leaves memory identical. -/
theorem copyRangeComp_self {L : ByteSubLens Addr} {m : Mem} {bs : List Byte}
    (hGet : L.get m = some bs) : copyRangeComp L L m = some m := by
  have hPos : 0 < L.len := (ByteSubLens.get_inv hGet).1
  rw [copyRangeComp_of_get hPos rfl hGet]
  exact ByteSubLens.set_get hGet

/-- Overlap-tolerant untyped `copyRangeComp` soundness (no disjointness
requirement between `src` and `dst`):
1. `dst.set m bs = some m'` and `dst.get m' = some bs` (verbatim preservation of
   all `.uninitPad` and `.initProv` atoms);
2. For `bs = flattenByteRuns codec runs`, `decodeAtoms? codec` recovers
   `flattenByteRunAtoms runs`, and every positive-length run split
   `runs = pre ++ (focus :: post)` reads back at `dst.zoom (runsByteLen pre)
   focus.byteLen`;
3. Every lens disjoint from `dst` is framed unchanged (`other.get m' =
   other.get m`). -/
theorem copyRangeComp_sound {Prov : Type x} (codec : ByteRunCodec Prov Byte)
    {src dst : ByteSubLens Addr} {m m' : Mem} (runs : List (ByteRun Prov))
    (hSrc : src.get m = some (flattenByteRuns codec runs))
    (hCopy : copyRangeComp src dst m = some m') :
    dst.set m (flattenByteRuns codec runs) = some m' ∧
    dst.get m' = some (flattenByteRuns codec runs) ∧
    decodeAtoms? codec (flattenByteRuns codec runs) =
      some (flattenByteRunAtoms runs) ∧
    (∀ (pre post : List (ByteRun Prov)) (focus : ByteRun Prov),
      runs = pre ++ (focus :: post) →
      0 < focus.byteLen →
      (dst.zoom (runsByteLen pre) focus.byteLen).get m' =
        some (focus.toBytes codec)) ∧
    (∀ (other : ByteSubLens Addr),
      ByteSubLens.Disjoint Mem other dst →
      other.get m' = other.get m) := by
  let ⟨_, hLenEq, bs, hGetBs, hSet⟩ := copyRangeComp_inv hCopy
  have hBsEq : bs = flattenByteRuns codec runs :=
    Option.some.inj (hGetBs.symm.trans hSrc)
  rw [hBsEq] at hSet
  have hDstGet : dst.get m' = some (flattenByteRuns codec runs) :=
    ByteSubLens.get_set hSet
  have hDstLen : dst.len = runsByteLen runs := by
    have h1 := ByteSubLens.get_len hDstGet
    rw [flattenByteRuns_length] at h1
    exact h1.symm
  refine ⟨hSet, hDstGet, decodeAtoms?_flattenByteRuns codec runs, ?_, ?_⟩
  · intro pre post focus hSplit hFocusPos
    have hSub : runsByteLen pre + focus.byteLen ≤ dst.len := by
      rw [hDstLen, hSplit, runsByteLen_append]
      change runsByteLen pre + focus.byteLen ≤
        runsByteLen pre + (focus.byteLen + runsByteLen post)
      rw [← Nat.add_assoc]
      exact Nat.le_add_right _ _
    rw [ByteSubLens.zoom_get hDstGet hFocusPos hSub, hSplit,
      projectRunAtSplit codec pre focus post]
  · intro other hDisj
    exact ByteSubLens.get_set_disjoint hDisj.symm hSet

/-- Raw byte-slice form of `copyRangeComp_sound` (works without specifying a
`ByteRun` decomposition, including self/overlapping copies). -/
theorem copyRangeComp_sound_raw {src dst : ByteSubLens Addr} {m m' : Mem}
    {bs : List Byte} (hSrc : src.get m = some bs)
    (hCopy : copyRangeComp src dst m = some m') :
    dst.set m bs = some m' ∧
    dst.get m' = some bs ∧
    (∀ other : ByteSubLens Addr,
      ByteSubLens.Disjoint Mem other dst → other.get m' = other.get m) := by
  let ⟨_, _, bs', hGetBs, hSet⟩ := copyRangeComp_inv hCopy
  have hEq : bs' = bs := Option.some.inj (hGetBs.symm.trans hSrc)
  rw [hEq] at hSet
  exact ⟨hSet, ByteSubLens.get_set hSet,
    fun other hDisj => ByteSubLens.get_set_disjoint hDisj.symm hSet⟩

private theorem copyRepeatedly_fold_fused
    (src : ByteSubLens Addr) (dstAddr : Addr) (dstOff n : Nat)
    (m : Mem) (elemBs oldWin : List Byte)
    (hElemPos : 0 < elemBs.length)
    (hSrcLen : src.len = elemBs.length)
    (hSrcGet : src.get m = some elemBs)
    (hWinGet : ({ addr := dstAddr, offset := dstOff,
                  len := n * elemBs.length } : ByteSubLens Addr).get m =
      some oldWin)
    (hDisj : ByteSubLens.Disjoint Mem
      ({ addr := dstAddr, offset := dstOff,
         len := n * elemBs.length } : ByteSubLens Addr) src) :
    ∀ (j : Nat), j ≤ n →
      @Nat.rec (fun _ => Option Mem) (some m)
        (fun i acc =>
          match acc with
          | none => none
          | some mCur =>
            copyRangeComp src
              { addr := dstAddr, offset := dstOff + i * src.len, len := src.len }
              mCur)
        j =
      ({ addr := dstAddr, offset := dstOff,
         len := n * elemBs.length } : ByteSubLens Addr).set m
        (listSplice oldWin 0 (repeatSlice j elemBs)) := by
  let dstWin : ByteSubLens Addr :=
    { addr := dstAddr, offset := dstOff, len := n * elemBs.length }
  have hOldLen : oldWin.length = n * elemBs.length := ByteSubLens.get_len hWinGet
  intro j
  induction j with
  | zero =>
    intro _
    change some m = dstWin.set m (listSplice oldWin 0 [])
    rw [listSplice_zero_nil]
    exact (ByteSubLens.set_get hWinGet).symm
  | succ k ih =>
    intro hK1Le
    have hKLe : k ≤ n := Nat.le_trans (Nat.le_succ k) hK1Le
    have hPrev := ih hKLe
    have hRepKLen : (repeatSlice k elemBs).length = k * elemBs.length :=
      repeatSlice_length k elemBs
    have hKBound : 0 + (repeatSlice k elemBs).length ≤ oldWin.length := by
      rw [Nat.zero_add, hRepKLen, hOldLen]
      exact Nat.mul_le_mul_right elemBs.length hKLe
    have hSpliceKLen :
        (listSplice oldWin 0 (repeatSlice k elemBs)).length = dstWin.len :=
      (listSplice_length oldWin 0 (repeatSlice k elemBs) hKBound).trans hOldLen
    let ⟨mK, hSetK⟩ :=
      ByteSubLens.set_isSome_of_get
        (listSplice oldWin 0 (repeatSlice k elemBs)) hWinGet hSpliceKLen
    have hRecEq :
        @Nat.rec (fun _ => Option Mem) (some m)
          (fun i acc =>
            match acc with
            | none => none
            | some mCur =>
              copyRangeComp src
                { addr := dstAddr, offset := dstOff + i * src.len,
                  len := src.len } mCur)
          k = some mK := hPrev.trans hSetK
    change (match @Nat.rec (fun _ => Option Mem) (some m)
        (fun i acc =>
          match acc with
          | none => none
          | some mCur =>
            copyRangeComp src
              { addr := dstAddr, offset := dstOff + i * src.len,
                len := src.len } mCur) k with
      | none => none
      | some mCur =>
        copyRangeComp src
          { addr := dstAddr, offset := dstOff + k * src.len,
            len := src.len } mCur) =
      dstWin.set m (listSplice oldWin 0 (repeatSlice (k + 1) elemBs))
    rw [hRecEq]
    dsimp only
    have hSrcK : src.get mK = some elemBs :=
      (ByteSubLens.get_set_disjoint hDisj hSetK).trans hSrcGet
    have hSrcPos : 0 < src.len := by rw [hSrcLen]; exact hElemPos
    let elemLens : ByteSubLens Addr :=
      { addr := dstAddr, offset := dstOff + k * src.len, len := src.len }
    have hCopyK : copyRangeComp src elemLens mK = elemLens.set mK elemBs :=
      copyRangeComp_of_get hSrcPos rfl hSrcK
    rw [hCopyK]
    have hElemLensEq : elemLens = dstWin.zoom (k * elemBs.length) elemBs.length := by
      dsimp only [elemLens, dstWin, ByteSubLens.zoom]
      rw [hSrcLen]
    rw [hElemLensEq]
    have hWinK : dstWin.get mK = some (listSplice oldWin 0 (repeatSlice k elemBs)) :=
      ByteSubLens.get_set hSetK
    have hSubIn : k * elemBs.length + elemBs.length ≤ dstWin.len := by
      change k * elemBs.length + elemBs.length ≤ n * elemBs.length
      rw [← Nat.succ_mul]
      exact Nat.mul_le_mul_right elemBs.length hK1Le
    rw [ByteSubLens.zoom_set_eq_splice hWinK hElemPos hSubIn rfl]
    have hFuse :=
      listSplice_contiguous_fuse oldWin 0 (repeatSlice k elemBs) elemBs hKBound
    rw [Nat.zero_add, hRepKLen] at hFuse
    rw [hFuse, ← repeatSlice_succ k elemBs]
    exact ByteSubLens.set_set
      (listSplice oldWin 0 (repeatSlice (k + 1) elemBs)) hSetK

/-- **Repeat Fusion Theorem (`Option Mem` equality):** when `0 < n`,
`0 < runsByteLen runs`, `src` holds `flattenByteRuns codec runs`, the target
`[dstOff, dstOff + n * runsByteLen runs)` window is readable, and `src` is
disjoint from that target window, `n` sequential element copies via
`copyRepeatedlyComp` produce the EXACT same `Option Mem` result as the single
fused bulk write `writeRepeatRunsComp`. -/
theorem copyRepeatedlyComp_eq_writeRepeatRunsComp {Prov : Type x}
    (codec : ByteRunCodec Prov Byte)
    {src : ByteSubLens Addr} {dstAddr : Addr} {dstOff n : Nat}
    {m : Mem} {oldWin : List Byte} (runs : List (ByteRun Prov))
    (hNPos : 0 < n) (hElemPos : 0 < runsByteLen runs)
    (hSrcGet : src.get m = some (flattenByteRuns codec runs))
    (hWinGet :
      ({ addr := dstAddr, offset := dstOff,
         len := n * runsByteLen runs } : ByteSubLens Addr).get m = some oldWin)
    (hDisj : ByteSubLens.Disjoint Mem
      ({ addr := dstAddr, offset := dstOff,
         len := n * runsByteLen runs } : ByteSubLens Addr) src) :
    copyRepeatedlyComp src dstAddr dstOff n m =
      writeRepeatRunsComp codec dstAddr dstOff n runs m := by
  let elemBs := flattenByteRuns codec runs
  have hElemLen : elemBs.length = runsByteLen runs :=
    flattenByteRuns_length codec runs
  have hSrcLen : src.len = elemBs.length :=
    (ByteSubLens.get_len hSrcGet).symm
  have hNZero : Nat.beq n 0 = false :=
    natBeq_false_of_not_eq (fun hZ => Nat.not_lt_zero 0 (hZ ▸ hNPos))
  have hSrcPos : 0 < src.len := by
    rw [hSrcLen, hElemLen]; exact hElemPos
  have hSrcZero : Nat.beq src.len 0 = false :=
    natBeq_false_of_not_eq (fun hZ => Nat.not_lt_zero 0 (hZ ▸ hSrcPos))
  unfold copyRepeatedlyComp
  rw [hNZero, hSrcZero]
  have hElemBsPos : 0 < elemBs.length := by
    rw [hElemLen]; exact hElemPos
  have hWinGet' :
      ({ addr := dstAddr, offset := dstOff,
         len := n * elemBs.length } : ByteSubLens Addr).get m = some oldWin := by
    rw [hElemLen]; exact hWinGet
  have hDisj' :
      ByteSubLens.Disjoint Mem
        ({ addr := dstAddr, offset := dstOff,
           len := n * elemBs.length } : ByteSubLens Addr) src := by
    rw [hElemLen]; exact hDisj
  have hFused :=
    copyRepeatedly_fold_fused src dstAddr dstOff n m elemBs oldWin
      hElemBsPos hSrcLen hSrcGet hWinGet' hDisj' n (Nat.le_refl n)
  rw [hFused]
  have hRepLen : (repeatSlice n elemBs).length = oldWin.length := by
    rw [repeatSlice_length, hElemLen, ByteSubLens.get_len hWinGet]
  rw [listSplice_zero_full oldWin (repeatSlice n elemBs) hRepLen]
  unfold writeRepeatRunsComp
  rw [flattenByteRuns_repeat codec n runs, hElemLen]
  rfl

/-- Full `[T; N]` repeat-fusion soundness theorem: produces the post-state
`mFinal` witnessing exact agreement between `copyRepeatedlyComp` and
`writeRepeatRunsComp`, full-window readback, every element `i < n` stride
readback, per-element run-split projection, disjoint-lens framing, and
auxiliary metadata preservation. -/
theorem copyRepeatedlyComp_sound {Prov : Type x}
    (codec : ByteRunCodec Prov Byte)
    {src : ByteSubLens Addr} {dstAddr : Addr} {dstOff n : Nat}
    {m : Mem} {oldWin : List Byte} (runs : List (ByteRun Prov))
    (hNPos : 0 < n) (hElemPos : 0 < runsByteLen runs)
    (hSrcGet : src.get m = some (flattenByteRuns codec runs))
    (hWinGet :
      ({ addr := dstAddr, offset := dstOff,
         len := n * runsByteLen runs } : ByteSubLens Addr).get m = some oldWin)
    (hDisj : ByteSubLens.Disjoint Mem
      ({ addr := dstAddr, offset := dstOff,
         len := n * runsByteLen runs } : ByteSubLens Addr) src) :
    let dstWin : ByteSubLens Addr :=
      { addr := dstAddr, offset := dstOff, len := n * runsByteLen runs }
    ∃ mFinal : Mem,
      copyRepeatedlyComp src dstAddr dstOff n m = some mFinal ∧
      writeRepeatRunsComp codec dstAddr dstOff n runs m = some mFinal ∧
      dstWin.get mFinal = some (flattenByteRuns codec (repeatByteRuns n runs)) ∧
      (∀ i : Nat, i < n →
        (dstWin.zoom (i * runsByteLen runs) (runsByteLen runs)).get mFinal =
          some (flattenByteRuns codec runs)) ∧
      (∀ (i : Nat) (pre post : List (ByteRun Prov)) (focus : ByteRun Prov),
        i < n →
        runs = pre ++ (focus :: post) →
        0 < focus.byteLen →
        (dstWin.zoom (i * runsByteLen runs + runsByteLen pre) focus.byteLen).get
            mFinal = some (focus.toBytes codec)) ∧
      (∀ other : ByteSubLens Addr,
        ByteSubLens.Disjoint Mem dstWin other →
        other.get mFinal = other.get m) := by
  let dstWin : ByteSubLens Addr :=
    { addr := dstAddr, offset := dstOff, len := n * runsByteLen runs }
  let payload := flattenByteRuns codec (repeatByteRuns n runs)
  have hPayLen : payload.length = dstWin.len :=
    flattenByteRuns_repeat_length codec n runs
  let ⟨mFinal, hWrite⟩ := ByteSubLens.set_isSome_of_get payload hWinGet hPayLen
  have hFused :
      copyRepeatedlyComp src dstAddr dstOff n m =
        writeRepeatRunsComp codec dstAddr dstOff n runs m :=
    copyRepeatedlyComp_eq_writeRepeatRunsComp codec runs hNPos hElemPos
      hSrcGet hWinGet hDisj
  have hCopyEq : copyRepeatedlyComp src dstAddr dstOff n m = some mFinal :=
    hFused.trans hWrite
  have hGetFinal : dstWin.get mFinal = some payload :=
    ByteSubLens.get_set hWrite
  refine ⟨mFinal, hCopyEq, hWrite, hGetFinal, ?_, ?_, ?_⟩
  · intro i hLt
    have hSub : i * runsByteLen runs + runsByteLen runs ≤ dstWin.len := by
      change i * runsByteLen runs + runsByteLen runs ≤ n * runsByteLen runs
      rw [← Nat.succ_mul]
      exact Nat.mul_le_mul_right (runsByteLen runs) hLt
    rw [ByteSubLens.zoom_get hGetFinal hElemPos hSub]
    exact congrArg some (flattenByteRuns_repeat_project_elem codec n i runs hLt)
  · intro i pre post focus hLt hSplit hFocusPos
    have hSubElem : i * runsByteLen runs + runsByteLen runs ≤ dstWin.len := by
      change i * runsByteLen runs + runsByteLen runs ≤ n * runsByteLen runs
      rw [← Nat.succ_mul]
      exact Nat.mul_le_mul_right (runsByteLen runs) hLt
    have hElemGet :
        (dstWin.zoom (i * runsByteLen runs) (runsByteLen runs)).get mFinal =
          some (flattenByteRuns codec runs) := by
      rw [ByteSubLens.zoom_get hGetFinal hElemPos hSubElem]
      exact congrArg some (flattenByteRuns_repeat_project_elem codec n i runs hLt)
    have hSubRun : runsByteLen pre + focus.byteLen ≤ runsByteLen runs := by
      rw [hSplit, runsByteLen_append]
      change runsByteLen pre + focus.byteLen ≤
        runsByteLen pre + (focus.byteLen + runsByteLen post)
      rw [← Nat.add_assoc]
      exact Nat.le_add_right _ _
    have hZoomEq :=
      ByteSubLens.zoom_zoom dstWin (i * runsByteLen runs) (runsByteLen runs)
        (runsByteLen pre) focus.byteLen
    rw [← hZoomEq, ByteSubLens.zoom_get hElemGet hFocusPos hSubRun, hSplit,
      projectRunAtSplit codec pre focus post]
  · intro other hDisjOther
    exact ByteSubLens.get_set_disjoint hDisjOther hWrite

/-- Disjoint-lens framing for `copyRepeatedlyComp` directly (even without
specifying a `ByteRun` layout or source disjointness). -/
theorem copyRepeatedlyComp_frame_disjoint {src : ByteSubLens Addr}
    {dstAddr : Addr} {dstOff n : Nat} {m m' : Mem} {other : ByteSubLens Addr}
    (hDisj : ByteSubLens.Disjoint Mem
      ({ addr := dstAddr, offset := dstOff, len := n * src.len } :
        ByteSubLens Addr) other)
    (hRep : copyRepeatedlyComp src dstAddr dstOff n m = some m') :
    other.get m' = other.get m := by
  unfold copyRepeatedlyComp at hRep
  cases hGuard : (Nat.beq n 0 || Nat.beq src.len 0) with
  | true =>
    rw [hGuard] at hRep
    cases hRep
  | false =>
    rw [hGuard] at hRep
    have hAux :
        ∀ (j : Nat), j ≤ n → ∀ mOut,
          @Nat.rec (fun _ => Option Mem) (some m)
            (fun i acc =>
              match acc with
              | none => none
              | some mCur =>
                copyRangeComp src
                  { addr := dstAddr, offset := dstOff + i * src.len,
                    len := src.len } mCur) j = some mOut →
          other.get mOut = other.get m := by
      intro j
      induction j with
      | zero =>
        intro _ mOut hEq
        have hM : m = mOut := Option.some.inj hEq
        rw [← hM]
      | succ k ih =>
        intro hK1Le mOut hStep
        change (match @Nat.rec (fun _ => Option Mem) (some m)
            (fun i acc =>
              match acc with
              | none => none
              | some mCur =>
                copyRangeComp src
                  { addr := dstAddr, offset := dstOff + i * src.len,
                    len := src.len } mCur) k with
          | none => none
          | some mCur =>
            copyRangeComp src
              { addr := dstAddr, offset := dstOff + k * src.len,
                len := src.len } mCur) = some mOut at hStep
        cases hPrev : @Nat.rec (fun _ => Option Mem) (some m)
            (fun i acc =>
              match acc with
              | none => none
              | some mCur =>
                copyRangeComp src
                  { addr := dstAddr, offset := dstOff + i * src.len,
                    len := src.len } mCur) k with
        | none =>
          rw [hPrev] at hStep
          cases hStep
        | some mK =>
          rw [hPrev] at hStep
          dsimp only at hStep
          have hSubContained :
              ({ addr := dstAddr, offset := dstOff + k * src.len,
                 len := src.len } : ByteSubLens Addr).ContainedIn
                { addr := dstAddr, offset := dstOff, len := n * src.len } := by
            refine ⟨rfl, Nat.le_add_right dstOff (k * src.len), ?_⟩
            change dstOff + k * src.len + src.len ≤ dstOff + n * src.len
            rw [Nat.add_assoc]
            refine Nat.add_le_add_left ?_ dstOff
            rw [← Nat.succ_mul]
            exact Nat.mul_le_mul_right src.len hK1Le
          have hDisjK :
              ByteSubLens.Disjoint Mem
                { addr := dstAddr, offset := dstOff + k * src.len,
                  len := src.len } other :=
            ByteSubLens.disjoint_of_contained_disjoint hSubContained
              (ByteSubLens.containedIn_refl other) hDisj
          let ⟨_, _, _, _, hSetK⟩ := copyRangeComp_inv hStep
          have hEqK : other.get mOut = other.get mK :=
            ByteSubLens.get_set_disjoint hDisjK hSetK
          exact hEqK.trans (ih (Nat.le_trans (Nat.le_succ k) hK1Le) mK hPrev)
    exact hAux n (Nat.le_refl n) m' hRep

end CopyAlgebra

/-! ## Part IV: Zero-`Prop`-Argument `@[irreducible] ByteRunCopyCut` -/

/-- Pure-data descriptor of an untyped byte-run copy operation (`0` `Prop`
fields). -/
inductive ByteRunCopyOp (Addr : Type v) : Type v where
  | copyRange (src dst : ByteSubLens Addr) : ByteRunCopyOp Addr
  | copyRepeat (src : ByteSubLens Addr) (dstAddr : Addr) (dstOff n : Nat) :
      ByteRunCopyOp Addr

namespace ByteRunCopyOp

/-- Target destination byte window mutated by `op`. -/
def dstLens {Addr : Type v} (op : ByteRunCopyOp Addr) : ByteSubLens Addr :=
  match op with
  | .copyRange _ dst => dst
  | .copyRepeat src dstAddr dstOff n =>
    { addr := dstAddr, offset := dstOff, len := n * src.len }

/-- Executes a single `ByteRunCopyOp` on memory `m`. -/
def exec {Mem : Type u} {Addr : Type v} {Byte : Type w}
    [ops : ByteStoreOps Mem Addr Byte]
    (op : ByteRunCopyOp Addr) (m : Mem) : Option Mem :=
  match op with
  | .copyRange src dst => copyRangeComp src dst m
  | .copyRepeat src dstAddr dstOff n => copyRepeatedlyComp src dstAddr dstOff n m

/-- Frame law for a single `ByteRunCopyOp`. -/
theorem exec_frame_disjoint {Mem : Type u} {Addr : Type v} {Byte : Type w}
    [ops : ByteStoreOps Mem Addr Byte] [LawfulByteStoreOps Mem Addr Byte]
    {op : ByteRunCopyOp Addr} {m m' : Mem} {other : ByteSubLens Addr}
    (hDisj : ByteSubLens.Disjoint Mem op.dstLens other)
    (hExec : op.exec m = some m') :
    other.get m' = other.get m := by
  cases op with
  | copyRange src dst =>
    let ⟨_, _, _, _, hSet⟩ := copyRangeComp_inv hExec
    exact ByteSubLens.get_set_disjoint hDisj hSet
  | copyRepeat src dstAddr dstOff n =>
    exact copyRepeatedlyComp_frame_disjoint hDisj hExec

/-- Auxiliary metadata preservation for a single `ByteRunCopyOp`. -/
theorem exec_preserves {Mem : Type u} {Addr : Type v} {Byte : Type w}
    [ops : ByteStoreOps Mem Addr Byte]
    {V : Sort y} {proj : Mem → V}
    (hPres : ops.WritePreserves proj)
    {op : ByteRunCopyOp Addr} {m m' : Mem}
    (hExec : op.exec m = some m') :
    proj m' = proj m := by
  cases op with
  | copyRange _ _ => exact copyRangeComp_preserves hPres hExec
  | copyRepeat _ _ _ _ => exact copyRepeatedlyComp_preserves hPres hExec

end ByteRunCopyOp

/-- Sequentially executes a list of `ByteRunCopyOp`s (`List.foldl`, `0`
`._unsafe_rec`). -/
def execByteRunCopyOps {Mem : Type u} {Addr : Type v} {Byte : Type w}
    [ops : ByteStoreOps Mem Addr Byte]
    (copyOps : List (ByteRunCopyOp Addr)) (m : Mem) : Option Mem :=
  copyOps.foldl
    (fun (acc : Option Mem) (op : ByteRunCopyOp Addr) =>
      match acc with
      | none => none
      | some mCur => op.exec mCur)
    (some m)

private theorem execByteRunCopyOps_foldl_none {Mem : Type u} {Addr : Type v}
    {Byte : Type w} [ops : ByteStoreOps Mem Addr Byte]
    (copyOps : List (ByteRunCopyOp Addr)) :
    copyOps.foldl
      (fun (acc : Option Mem) (op : ByteRunCopyOp Addr) =>
        match acc with
        | none => none
        | some mCur => op.exec mCur)
      (none : Option Mem) = none := by
  induction copyOps with
  | nil => rfl
  | cons _ tl ih => exact ih

/-- Empty operation list leaves memory unchanged. -/
theorem execByteRunCopyOps_nil {Mem : Type u} {Addr : Type v} {Byte : Type w}
    [ops : ByteStoreOps Mem Addr Byte] (m : Mem) :
    execByteRunCopyOps ([] : List (ByteRunCopyOp Addr)) m = some m :=
  rfl

/-- Cons unfolding of `execByteRunCopyOps`. -/
theorem execByteRunCopyOps_cons {Mem : Type u} {Addr : Type v} {Byte : Type w}
    [ops : ByteStoreOps Mem Addr Byte]
    (op : ByteRunCopyOp Addr) (rest : List (ByteRunCopyOp Addr)) (m : Mem) :
    execByteRunCopyOps (op :: rest) m =
      match op.exec m with
      | none => none
      | some m₁ => execByteRunCopyOps rest m₁ := by
  unfold execByteRunCopyOps
  change rest.foldl
      (fun (acc : Option Mem) (o : ByteRunCopyOp Addr) =>
        match acc with | none => none | some mCur => o.exec mCur)
      (op.exec m) = _
  cases op.exec m with
  | none => exact execByteRunCopyOps_foldl_none rest
  | some _ => rfl

/-- Composition of `execByteRunCopyOps` across `++`. -/
theorem execByteRunCopyOps_append {Mem : Type u} {Addr : Type v}
    {Byte : Type w} [ops : ByteStoreOps Mem Addr Byte]
    (ops₁ ops₂ : List (ByteRunCopyOp Addr)) (m : Mem) :
    execByteRunCopyOps (ops₁ ++ ops₂) m =
      match execByteRunCopyOps ops₁ m with
      | none => none
      | some m₁ => execByteRunCopyOps ops₂ m₁ := by
  induction ops₁ generalizing m with
  | nil => rfl
  | cons op rest ih =>
    change execByteRunCopyOps (op :: (rest ++ ops₂)) m = _
    rw [execByteRunCopyOps_cons, execByteRunCopyOps_cons]
    cases op.exec m with
    | none => rfl
    | some m₁ => exact ih m₁

/-- Pairwise disjointness of `other` from every destination window in `copyOps`.
-/
def AllCopyOpsDisjoint (Mem : Type u) {Addr : Type v} {Byte : Type w}
    [ops : ByteStoreOps Mem Addr Byte] (other : ByteSubLens Addr)
    (copyOps : List (ByteRunCopyOp Addr)) : Prop :=
  copyOps.foldr
    (fun op acc => ByteSubLens.Disjoint Mem op.dstLens other ∧ acc)
    True

/-- `AllCopyOpsDisjoint` over `++`. -/
theorem allCopyOpsDisjoint_append {Mem : Type u} {Addr : Type v}
    {Byte : Type w} [ops : ByteStoreOps Mem Addr Byte]
    {other : ByteSubLens Addr} {ops₁ ops₂ : List (ByteRunCopyOp Addr)}
    (h₁ : AllCopyOpsDisjoint Mem other ops₁)
    (h₂ : AllCopyOpsDisjoint Mem other ops₂) :
    AllCopyOpsDisjoint Mem other (ops₁ ++ ops₂) := by
  induction ops₁ with
  | nil => exact h₂
  | cons _ _ ih => exact ⟨h₁.1, ih h₁.2⟩

/-- Frame law for `execByteRunCopyOps`. -/
theorem execByteRunCopyOps_frame_disjoint {Mem : Type u} {Addr : Type v}
    {Byte : Type w} [ops : ByteStoreOps Mem Addr Byte]
    [LawfulByteStoreOps Mem Addr Byte]
    (copyOps : List (ByteRunCopyOp Addr)) {other : ByteSubLens Addr}
    {m m' : Mem} (hDisj : AllCopyOpsDisjoint Mem other copyOps)
    (hExec : execByteRunCopyOps copyOps m = some m') :
    other.get m' = other.get m := by
  induction copyOps generalizing m with
  | nil =>
    have hM : m = m' := Option.some.inj hExec
    rw [← hM]
  | cons op rest ih =>
    rw [execByteRunCopyOps_cons] at hExec
    cases hOp : op.exec m with
    | none => rw [hOp] at hExec; cases hExec
    | some m₁ =>
      rw [hOp] at hExec
      exact (ih hDisj.2 hExec).trans
        (ByteRunCopyOp.exec_frame_disjoint hDisj.1 hOp)

/-- Auxiliary metadata preservation for `execByteRunCopyOps`. -/
theorem execByteRunCopyOps_preserves {Mem : Type u} {Addr : Type v}
    {Byte : Type w} [ops : ByteStoreOps Mem Addr Byte] {V : Sort y}
    {proj : Mem → V} (hPres : ops.WritePreserves proj)
    (copyOps : List (ByteRunCopyOp Addr)) {m m' : Mem}
    (hExec : execByteRunCopyOps copyOps m = some m') :
    proj m' = proj m := by
  induction copyOps generalizing m with
  | nil =>
    have hM : m = m' := Option.some.inj hExec
    rw [← hM]
  | cons op rest ih =>
    rw [execByteRunCopyOps_cons] at hExec
    cases hOp : op.exec m with
    | none => rw [hOp] at hExec; cases hExec
    | some m₁ =>
      rw [hOp] at hExec
      exact (ih hExec).trans (ByteRunCopyOp.exec_preserves hPres hOp)

section CopyCut

variable {S : Type x} {Out : Type y} {Fault : Type z}
  {Mem : Type u} {Addr : Type v} {Byte : Type w}
  [ops : ByteStoreOps Mem Addr Byte]

/-- Unsealed denotation of `ByteRunCopyCut`: `s₀` reaches `s₁` within `fuel`
steps of `step` (`StepStageCut`) and the memory transition from `memOf s₀` to
`memOf s₁` equals executing `copyOps`. -/
def denoteByteRunCopyCut (step : S → StepOutcome S Out Fault)
    (memOf : S → Mem) (copyOps : List (ByteRunCopyOp Addr))
    (fuel : Nat) (s₀ s₁ : S) : Prop :=
  StepStageCut step fuel s₀ s₁ ∧
  execByteRunCopyOps copyOps (memOf s₀) = some (memOf s₁)

/-- Zero-`Prop`-argument stage-cut barrier for byte-run copy pipelines
(carrying only computational functions and data, sealed `@[irreducible]` below
after its seal/unseal/compose/frame/interop laws). -/
def ByteRunCopyCut (step : S → StepOutcome S Out Fault) (memOf : S → Mem)
    (copyOps : List (ByteRunCopyOp Addr)) (fuel : Nat) (s₀ s₁ : S) : Prop :=
  denoteByteRunCopyCut step memOf copyOps fuel s₀ s₁

/-- Seals a `denoteByteRunCopyCut` proof behind `ByteRunCopyCut`. -/
theorem seal_byteRunCopyCut {step : S → StepOutcome S Out Fault}
    {memOf : S → Mem} {copyOps : List (ByteRunCopyOp Addr)}
    {fuel : Nat} {s₀ s₁ : S}
    (h : denoteByteRunCopyCut step memOf copyOps fuel s₀ s₁) :
    ByteRunCopyCut step memOf copyOps fuel s₀ s₁ :=
  h

/-- Unseals `ByteRunCopyCut` into `denoteByteRunCopyCut`. -/
theorem open_byteRunCopyCut {step : S → StepOutcome S Out Fault}
    {memOf : S → Mem} {copyOps : List (ByteRunCopyOp Addr)}
    {fuel : Nat} {s₀ s₁ : S}
    (h : ByteRunCopyCut step memOf copyOps fuel s₀ s₁) :
    denoteByteRunCopyCut step memOf copyOps fuel s₀ s₁ :=
  h

/-- Reflexive empty-pipeline `ByteRunCopyCut`. -/
theorem ByteRunCopyCut.refl (step : S → StepOutcome S Out Fault)
    (memOf : S → Mem) (fuel : Nat) (s : S) :
    ByteRunCopyCut step memOf ([] : List (ByteRunCopyOp Addr)) fuel s s :=
  ⟨StepStageCut.refl step fuel s, rfl⟩

/-- Seals a single `copyRangeComp` transition into `ByteRunCopyCut`. -/
theorem ByteRunCopyCut.singleRange {step : S → StepOutcome S Out Fault}
    {memOf : S → Mem} {src dst : ByteSubLens Addr} {fuel : Nat} {s₀ s₁ : S}
    (hStage : StepStageCut step fuel s₀ s₁)
    (hCopy : copyRangeComp src dst (memOf s₀) = some (memOf s₁)) :
    ByteRunCopyCut step memOf [.copyRange src dst] fuel s₀ s₁ := by
  refine ⟨hStage, ?_⟩
  rw [execByteRunCopyOps_cons]
  change (match copyRangeComp src dst (memOf s₀) with
    | none => none
    | some m₁ => some m₁) = some (memOf s₁)
  rw [hCopy]

/-- Seals a single `copyRepeatedlyComp` transition into `ByteRunCopyCut`. -/
theorem ByteRunCopyCut.singleRepeat {step : S → StepOutcome S Out Fault}
    {memOf : S → Mem} {src : ByteSubLens Addr} {dstAddr : Addr}
    {dstOff n fuel : Nat} {s₀ s₁ : S}
    (hStage : StepStageCut step fuel s₀ s₁)
    (hRep : copyRepeatedlyComp src dstAddr dstOff n (memOf s₀) =
      some (memOf s₁)) :
    ByteRunCopyCut step memOf [.copyRepeat src dstAddr dstOff n] fuel s₀ s₁ := by
  refine ⟨hStage, ?_⟩
  rw [execByteRunCopyOps_cons]
  change (match copyRepeatedlyComp src dstAddr dstOff n (memOf s₀) with
    | none => none
    | some m₁ => some m₁) = some (memOf s₁)
  rw [hRep]

/-- Sequential composition of `ByteRunCopyCut` pipelines (`ops₁ ++ ops₂`,
`f₁ + f₂` fuel). -/
theorem ByteRunCopyCut.compose {step : S → StepOutcome S Out Fault}
    {memOf : S → Mem} {ops₁ ops₂ : List (ByteRunCopyOp Addr)}
    {f₁ f₂ : Nat} {s₀ s₁ s₂ : S}
    (h₁ : ByteRunCopyCut step memOf ops₁ f₁ s₀ s₁)
    (h₂ : ByteRunCopyCut step memOf ops₂ f₂ s₁ s₂) :
    ByteRunCopyCut step memOf (ops₁ ++ ops₂) (f₁ + f₂) s₀ s₂ := by
  refine ⟨StepStageCut.trans h₁.1 h₂.1, ?_⟩
  rw [execByteRunCopyOps_append, h₁.2]
  exact h₂.2

/-- Fuel weakening for `ByteRunCopyCut`. -/
theorem ByteRunCopyCut.fuel_mono {step : S → StepOutcome S Out Fault}
    {memOf : S → Mem} {copyOps : List (ByteRunCopyOp Addr)}
    {f₁ f₂ : Nat} {s₀ s₁ : S} (hLe : f₁ ≤ f₂)
    (h : ByteRunCopyCut step memOf copyOps f₁ s₀ s₁) :
    ByteRunCopyCut step memOf copyOps f₂ s₀ s₁ :=
  ⟨StepStageCut.fuel_mono hLe h.1, h.2⟩

/-- Projects the underlying `StepStageCut`. -/
theorem ByteRunCopyCut.to_stepStageCut {step : S → StepOutcome S Out Fault}
    {memOf : S → Mem} {copyOps : List (ByteRunCopyOp Addr)}
    {fuel : Nat} {s₀ s₁ : S}
    (h : ByteRunCopyCut step memOf copyOps fuel s₀ s₁) :
    StepStageCut step fuel s₀ s₁ :=
  h.1

/-- Projects a fuel-free `DetStageCut`. -/
theorem ByteRunCopyCut.to_detStageCut {step : S → StepOutcome S Out Fault}
    {memOf : S → Mem} {copyOps : List (ByteRunCopyOp Addr)}
    {fuel : Nat} {s₀ s₁ : S}
    (h : ByteRunCopyCut step memOf copyOps fuel s₀ s₁) :
    DetStageCut step s₀ s₁ :=
  DetStageCut.of_stepStageCut h.1

/-- Lifts a `ByteRunCopyCut` into a `ParametricCore.StageCut`. -/
theorem ByteRunCopyCut.to_stageCut {step : S → StepOutcome S Out Fault}
    {tag : S → Option Nat} {memOf : S → Mem}
    {copyOps : List (ByteRunCopyOp Addr)} {fuel : Nat} {s₀ s₁ : S}
    {onDone : Out → Prop} {onFault : Fault → Prop}
    (h : ByteRunCopyCut step memOf copyOps fuel s₀ s₁) :
    StageCut (ops := MirWpOps.ofDetStep step tag)
      (fun s => s = s₀) (fun s => s = s₁) onDone onFault :=
  StageCut.of_stepStageCut h.1

/-- Prepends a `ByteRunCopyCut` onto a fuel-free `wpUntil` proof. -/
theorem ByteRunCopyCut.to_wpUntil {step : S → StepOutcome S Out Fault}
    {tag : S → Option Nat} {memOf : S → Mem}
    {copyOps : List (ByteRunCopyOp Addr)} {fuel : Nat} {s₀ s₁ : S}
    {stop : S → Prop} {onDone : Out → Prop} {onFault : Fault → Prop}
    (h : ByteRunCopyCut step memOf copyOps fuel s₀ s₁)
    (hRest : wpUntil (ops := MirWpOps.ofDetStep step tag) stop onDone onFault
      s₁) :
    wpUntil (ops := MirWpOps.ofDetStep step tag) stop onDone onFault s₀ :=
  StepStageCut.to_wpUntil h.1 hRest

/-- Prepends a `ByteRunCopyCut` onto a fuel-free `wpOutcome` proof. -/
theorem ByteRunCopyCut.to_wpOutcome {step : S → StepOutcome S Out Fault}
    {tag : S → Option Nat} {memOf : S → Mem}
    {copyOps : List (ByteRunCopyOp Addr)} {fuel : Nat} {s₀ s₁ : S}
    {onDone : Out → Prop} {onFault : Fault → Prop}
    (h : ByteRunCopyCut step memOf copyOps fuel s₀ s₁)
    (hRest : wpOutcome (ops := MirWpOps.ofDetStep step tag) onDone onFault s₁) :
    wpOutcome (ops := MirWpOps.ofDetStep step tag) onDone onFault s₀ :=
  StepStageCut.to_wpOutcome h.1 hRest

/-- Disjoint-lens frame theorem for `ByteRunCopyCut`. -/
theorem ByteRunCopyCut.frame_disjoint [LawfulByteStoreOps Mem Addr Byte]
    {step : S → StepOutcome S Out Fault} {memOf : S → Mem}
    {copyOps : List (ByteRunCopyOp Addr)} {fuel : Nat} {s₀ s₁ : S}
    {other : ByteSubLens Addr}
    (hDisj : AllCopyOpsDisjoint Mem other copyOps)
    (h : ByteRunCopyCut step memOf copyOps fuel s₀ s₁) :
    other.get (memOf s₁) = other.get (memOf s₀) :=
  execByteRunCopyOps_frame_disjoint copyOps hDisj h.2

/-- Auxiliary metadata preservation for `ByteRunCopyCut`. -/
theorem ByteRunCopyCut.preserves_proj {V : Sort a} {proj : Mem → V}
    (hPres : ops.WritePreserves proj)
    {step : S → StepOutcome S Out Fault} {memOf : S → Mem}
    {copyOps : List (ByteRunCopyOp Addr)} {fuel : Nat} {s₀ s₁ : S}
    (h : ByteRunCopyCut step memOf copyOps fuel s₀ s₁) :
    proj (memOf s₁) = proj (memOf s₀) :=
  execByteRunCopyOps_preserves hPres copyOps h.2

end CopyCut

attribute [irreducible] ByteRunCopyCut

/-! ### Interop with `MutSummary` / `MutSummaryCut` and `Anneal.Firewall.IndexedCut` -/

/-- `MutSummary` that overwrites a slice of length `runsByteLen runs` with
`flattenByteRuns codec runs` (preserving `.uninitPad` and `.initProv`). -/
def byteRunWriteSummary {Prov : Type u} {Byte : Type v}
    (codec : ByteRunCodec Prov Byte) (runs : List (ByteRun Prov)) :
    MutSummary Byte Unit Unit where
  len := runsByteLen runs
  summaryFn _ _ := some (flattenByteRuns codec runs, ())

/-- `MutSummary` that overwrites a slice of length `n * runsByteLen runs` with
`flattenByteRuns codec (repeatByteRuns n runs)`. -/
def byteRunRepeatSummary {Prov : Type u} {Byte : Type v}
    (codec : ByteRunCodec Prov Byte) (n : Nat) (runs : List (ByteRun Prov)) :
    MutSummary Byte Unit Unit where
  len := n * runsByteLen runs
  summaryFn _ _ := some (flattenByteRuns codec (repeatByteRuns n runs), ())

/-- Executing `byteRunWriteSummary` agrees with `dst.set` whenever `dst` is
readable and has length `runsByteLen runs`. -/
theorem execMutSummary_byteRunWriteSummary {Mem : Type u} {Addr : Type v}
    {Byte : Type w} {Prov : Type x} [ops : ByteStoreOps Mem Addr Byte]
    [LawfulByteStoreOps Mem Addr Byte]
    (codec : ByteRunCodec Prov Byte) (runs : List (ByteRun Prov))
    {dst : ByteSubLens Addr} {m m' : Mem} {old : List Byte}
    (hLen : dst.len = runsByteLen runs) (hGet : dst.get m = some old)
    (hSet : dst.set m (flattenByteRuns codec runs) = some m') :
    execMutSummary (byteRunWriteSummary codec runs) dst m () = some (m', ()) :=
  execMutSummary_of (sum := byteRunWriteSummary codec runs) hLen hGet rfl hSet

/-- Executing `byteRunRepeatSummary` agrees with `writeRepeatRunsComp` whenever
the target window is readable. -/
theorem execMutSummary_byteRunRepeatSummary {Mem : Type u} {Addr : Type v}
    {Byte : Type w} {Prov : Type x} [ops : ByteStoreOps Mem Addr Byte]
    [LawfulByteStoreOps Mem Addr Byte]
    (codec : ByteRunCodec Prov Byte) (n : Nat) (runs : List (ByteRun Prov))
    {dstAddr : Addr} {dstOff : Nat} {m m' : Mem} {old : List Byte}
    (hGet :
      ({ addr := dstAddr, offset := dstOff,
         len := n * runsByteLen runs } : ByteSubLens Addr).get m = some old)
    (hWrite : writeRepeatRunsComp codec dstAddr dstOff n runs m = some m') :
    execMutSummary (byteRunRepeatSummary codec n runs)
      { addr := dstAddr, offset := dstOff, len := n * runsByteLen runs } m () =
      some (m', ()) :=
  execMutSummary_of (sum := byteRunRepeatSummary codec n runs) rfl hGet rfl hWrite

/-- Bridge from a sealed `MutSummaryCut` realizing `byteRunWriteSummary` on a
deterministic step machine into a sealed `ByteRunCopyCut` (obtaining exact
fuel and `copyRangeComp` agreement). -/
theorem byteRunCopyCut_of_mutSummaryCut {S : Type x} {Out : Type y}
    {Fault : Type z} {Mem : Type u} {Addr : Type v} {Byte : Type w}
    {Prov : Type a} [ops : ByteStoreOps Mem Addr Byte]
    [LawfulByteStoreOps Mem Addr Byte]
    {step : S → StepOutcome S Out Fault} {tag : S → Option Nat}
    {memOf : S → Mem} {atEntry : ByteSubLens Addr → Unit → S → Prop}
    {atExit : Unit → S → S → Prop}
    (codec : ByteRunCodec Prov Byte) (runs : List (ByteRun Prov))
    (hCut : MutSummaryCut (wops := MirWpOps.ofDetStep step tag)
      memOf atEntry atExit (byteRunWriteSummary codec runs))
    {src dst : ByteSubLens Addr} {s₀ : S} {oldDst : List Byte}
    (hEntry : atEntry dst () s₀)
    (hSrcGet : src.get (memOf s₀) = some (flattenByteRuns codec runs))
    (hDstGet : dst.get (memOf s₀) = some oldDst)
    (hDstLen : dst.len = runsByteLen runs) :
    ∃ (fuel : Nat) (s₁ : S),
      ByteRunCopyCut step memOf [.copyRange src dst] fuel s₀ s₁ ∧
      atExit () s₀ s₁ := by
  have hPayLen : (flattenByteRuns codec runs).length = dst.len :=
    (flattenByteRuns_length codec runs).trans hDstLen.symm
  let ⟨m₁, hSet⟩ :=
    ByteSubLens.set_isSome_of_get (flattenByteRuns codec runs) hDstGet hPayLen
  have hExec :=
    execMutSummary_byteRunWriteSummary codec runs hDstLen hDstGet hSet
  have hApply :=
    apply_mutSummaryCut_sound (wops := MirWpOps.ofDetStep step tag)
      hCut hEntry hExec
  let ⟨s₁, hDet, hPost⟩ :=
    (wpReach_det_iff_exists_detStageCut (step := step) (tag := tag)).mp hApply.1
  let ⟨fuel, hStepCut⟩ := DetStageCut.exists_fuel hDet
  have hSrcPos : 0 < src.len := (ByteSubLens.get_inv hSrcGet).1
  have hSrcLenEq : src.len = dst.len := by
    rw [← ByteSubLens.get_len hSrcGet, flattenByteRuns_length, hDstLen]
  have hCopy : copyRangeComp src dst (memOf s₀) = some (memOf s₁) := by
    rw [copyRangeComp_of_get hSrcPos hSrcLenEq hSrcGet, hPost.1]
    exact hSet
  exact ⟨fuel, s₁, ByteRunCopyCut.singleRange hStepCut hCopy, hPost.2⟩

/-- Indexed stage-cut family for `Anneal.Firewall.IndexedCut`: stage `k` holds
the sealed `ByteRunCopyCut` transition from `st` to `target` using `opsAt k`
and budget `fuelAt k`. -/
def byteRunIndexedCutFamily {S : Type x} {Out : Type y} {Fault : Type z}
    {Mem : Type u} {Addr : Type v} {Byte : Type w}
    [ops : ByteStoreOps Mem Addr Byte]
    (step : S → StepOutcome S Out Fault) (memOf : S → Mem)
    (opsAt : Nat → List (ByteRunCopyOp Addr)) (fuelAt : Nat → Nat)
    (target : S) (stage : Nat) (st : S) : Prop :=
  ByteRunCopyCut step memOf (opsAt stage) (fuelAt stage) st target

/-- Seals a `ByteRunCopyCut` into an `Anneal.Firewall.IndexedCut`. -/
theorem ByteRunCopyCut.to_indexedCut {S : Type x} {Out : Type y}
    {Fault : Type z} {Mem : Type u} {Addr : Type v} {Byte : Type w}
    [ops : ByteStoreOps Mem Addr Byte]
    {step : S → StepOutcome S Out Fault} {memOf : S → Mem}
    {opsAt : Nat → List (ByteRunCopyOp Addr)} {fuelAt : Nat → Nat}
    {target st : S} {stage : Nat}
    (h : ByteRunCopyCut step memOf (opsAt stage) (fuelAt stage) st target) :
    Anneal.Firewall.IndexedCut
      (byteRunIndexedCutFamily step memOf opsAt fuelAt target) stage st :=
  Anneal.Firewall.seal_cut h

/-- Prepends a `ByteRunCopyCut` step onto an `Anneal.Firewall.IndexedCut`
via `Anneal.Firewall.step_cut`. -/
theorem byteRunIndexedCut_step {S : Type x} {Out : Type y} {Fault : Type z}
    {Mem : Type u} {Addr : Type v} {Byte : Type w}
    [ops : ByteStoreOps Mem Addr Byte]
    {step : S → StepOutcome S Out Fault} {memOf : S → Mem}
    {opsAt : Nat → List (ByteRunCopyOp Addr)} {fuelAt : Nat → Nat}
    {target s₀ s₁ : S} {stage₁ stage₂ : Nat}
    {stepOps : List (ByteRunCopyOp Addr)} {stepFuel : Nat}
    (hOpsEq : opsAt stage₁ = stepOps ++ opsAt stage₂)
    (hFuelEq : fuelAt stage₁ = stepFuel + fuelAt stage₂)
    (hStep : ByteRunCopyCut step memOf stepOps stepFuel s₀ s₁)
    (hNext : Anneal.Firewall.IndexedCut
      (byteRunIndexedCutFamily step memOf opsAt fuelAt target) stage₂ s₁) :
    Anneal.Firewall.IndexedCut
      (byteRunIndexedCutFamily step memOf opsAt fuelAt target) stage₁ s₀ :=
  Anneal.Firewall.step_cut
    (fun hTail => by
      unfold byteRunIndexedCutFamily
      rw [hOpsEq, hFuelEq]
      exact ByteRunCopyCut.compose hStep hTail)
    hNext

/-- Discharges a final goal from a sealed `ByteRunCopyCut` `IndexedCut` via
`Anneal.Firewall.finish_cut`. -/
theorem byteRunIndexedCut_finish {S : Type x} {Out : Type y} {Fault : Type z}
    {Mem : Type u} {Addr : Type v} {Byte : Type w}
    [ops : ByteStoreOps Mem Addr Byte]
    {step : S → StepOutcome S Out Fault} {memOf : S → Mem}
    {opsAt : Nat → List (ByteRunCopyOp Addr)} {fuelAt : Nat → Nat}
    {target st : S} {stage : Nat} {post : Prop}
    (hDone : ByteRunCopyCut step memOf (opsAt stage) (fuelAt stage) st target →
      post)
    (hCut : Anneal.Firewall.IndexedCut
      (byteRunIndexedCutFamily step memOf opsAt fuelAt target) stage st) :
    post :=
  Anneal.Firewall.finish_cut hDone hCut

/-! ## Part V: Self-Contained Positive & Fail-Closed Negative Canaries -/

/-- Canonical 12-byte padded provenance-mixed aggregate
`(u8, [u8; 3] uninit pad, ptrBytes@prov, u8, [u8; 3] uninit pad)`. -/
def canaryPaddedProvMix12 (a : UInt8) (prov : Nat)
    (p0 p1 p2 p3 : UInt8) (c : UInt8) : List (ByteRun Nat) :=
  [.initPlain [a], .uninitPad 3, .initProv [p0, p1, p2, p3] prov,
   .initPlain [c], .uninitPad 3]

/-- Canonical 12-byte plain padded aggregate
`(u8, [u8; 3] uninit pad, u32, u8, [u8; 3] uninit pad)`. -/
def canaryPaddedPlain12 (a b0 b1 b2 b3 c : UInt8) : List (ByteRun PEmpty.{1}) :=
  [.initPlain [a], .uninitPad 3, .initPlain [b0, b1, b2, b3],
   .initPlain [c], .uninitPad 3]

/-- Sample `SliceStore (ByteRunAtom Nat)` with `canaryPaddedProvMix12` at
`[0..12)`, destination `[12..24)`, and guard tail `[24..32)`. -/
def canaryProvMixStore0 : SliceStore (ByteRunAtom Nat) :=
  let c := ByteRunCodec.id Nat
  let src := flattenByteRuns c (canaryPaddedProvMix12 0x11 7 0xA0 0xA1 0xA2 0xA3 0x66)
  let dst := replicateComp 12 (ByteRunAtom.initPlain 0xEE)
  let tail := replicateComp 8 (ByteRunAtom.initProv 0x77 88)
  { allocs := [{ allocId := 1, bytes := src ++ dst ++ tail, writable := true },
               { allocId := 2, bytes := replicateComp 4 .uninitPad, writable := false }] }

/-- Positive canary: mixed-mask 12-byte padded struct copy preserving
`.initPlain`, `.uninitPad`, and `.initProv` verbatim, plus disjoint guard-tail
framing, self-copy idempotence, and partial overlapping copy safety. -/
theorem canary_byterun_padded_and_overlap :
    let c := ByteRunCodec.id Nat
    let runs := canaryPaddedProvMix12 0x11 7 0xA0 0xA1 0xA2 0xA3 0x66
    let src : ByteSubLens Nat := { addr := 1, offset := 0, len := 12 }
    let dst : ByteSubLens Nat := { addr := 1, offset := 12, len := 12 }
    let tail : ByteSubLens Nat := { addr := 1, offset := 24, len := 8 }
    let overlapDst : ByteSubLens Nat := { addr := 1, offset := 4, len := 12 }
    (∃ m1 : SliceStore (ByteRunAtom Nat),
      copyRangeComp src dst canaryProvMixStore0 = some m1 ∧
      dst.get m1 = some (flattenByteRuns c runs) ∧
      (dst.zoom 1 3).get m1 = some (replicateComp 3 .uninitPad) ∧
      (dst.zoom 4 4).get m1 =
        some [.initProv 0xA0 7, .initProv 0xA1 7, .initProv 0xA2 7, .initProv 0xA3 7] ∧
      tail.get m1 = some (replicateComp 8 (.initProv 0x77 88))) ∧
    copyRangeComp src src canaryProvMixStore0 = some canaryProvMixStore0 ∧
    (∃ mOv : SliceStore (ByteRunAtom Nat),
      copyRangeComp src overlapDst canaryProvMixStore0 = some mOv ∧
      overlapDst.get mOv = some (flattenByteRuns c runs)) := by
  refine ⟨⟨_, rfl, rfl, rfl, rfl, rfl⟩, rfl, ⟨_, rfl, rfl⟩⟩

/-- Sample `SliceStore (ByteRunAtom Nat)` for 3-element `[PaddedProvMix12; 3]`
repeat fusion (`[0..12)` source, `[12..48)` destination, `[48..52)` guard). -/
def canaryRepeatStore0 : SliceStore (ByteRunAtom Nat) :=
  let c := ByteRunCodec.id Nat
  let src := flattenByteRuns c (canaryPaddedProvMix12 0x3A 42 0xB0 0xB1 0xB2 0xB3 0x7F)
  let dst := replicateComp 36 (ByteRunAtom.initPlain 0xCC)
  let guard := replicateComp 4 (ByteRunAtom.initProv 0x99 55)
  { allocs := [{ allocId := 1, bytes := src ++ dst ++ guard, writable := true }] }

/-- Positive `[T; 3]` repeat-fusion canary: verifies exact agreement between
3-step `copyRepeatedlyComp` and fused `writeRepeatRunsComp`, per-element
stride readback, provenance & padding preservation, and guard-tail framing. -/
theorem canary_byterun_repeat_fusion :
    let c := ByteRunCodec.id Nat
    let runs := canaryPaddedProvMix12 0x3A 42 0xB0 0xB1 0xB2 0xB3 0x7F
    let src : ByteSubLens Nat := { addr := 1, offset := 0, len := 12 }
    let dstWin : ByteSubLens Nat := { addr := 1, offset := 12, len := 36 }
    let guard : ByteSubLens Nat := { addr := 1, offset := 48, len := 4 }
    ∃ mRep : SliceStore (ByteRunAtom Nat),
      copyRepeatedlyComp src 1 12 3 canaryRepeatStore0 = some mRep ∧
      writeRepeatRunsComp c 1 12 3 runs canaryRepeatStore0 = some mRep ∧
      dstWin.get mRep = some (flattenByteRuns c (repeatByteRuns 3 runs)) ∧
      (dstWin.zoom 0 12).get mRep = some (flattenByteRuns c runs) ∧
      (dstWin.zoom 12 12).get mRep = some (flattenByteRuns c runs) ∧
      (dstWin.zoom 24 12).get mRep = some (flattenByteRuns c runs) ∧
      (dstWin.zoom 28 4).get mRep =
        some [.initProv 0xB0 42, .initProv 0xB1 42, .initProv 0xB2 42, .initProv 0xB3 42] ∧
      (dstWin.zoom 25 3).get mRep = some (replicateComp 3 .uninitPad) ∧
      guard.get mRep = some (replicateComp 4 (.initProv 0x99 55)) :=
  ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `Option UInt8` (`ByteRunCodec.optionUInt8`) and stale-padding distinction
canary: untyped `copyRangeComp` preserves `.uninitPad` (`none`) distinct from
stale initialized padding (`some 0x99`), while `toByteCodec` reads initialized
fields identically and rejects copied `.uninitPad` bytes. -/
theorem canary_byterun_optionUInt8_and_stale_padding :
    let c := ByteRunCodec.optionUInt8
    let runsUninit := canaryPaddedPlain12 0x11 0x22 0x33 0x44 0x55 0x66
    let runsStale : List (ByteRun PEmpty.{1}) :=
      [.initPlain [0x11, 0x99, 0x99, 0x99, 0x22, 0x33, 0x44, 0x55, 0x66, 0xAA, 0xAA, 0xAA]]
    let mUninit : SliceStore (Option UInt8) :=
      { allocs := [{ allocId := 1,
                     bytes := flattenByteRuns c runsUninit ++ replicateComp 12 (some 0xFF),
                     writable := true }] }
    let mStale : SliceStore (Option UInt8) :=
      { allocs := [{ allocId := 1,
                     bytes := flattenByteRuns c runsStale ++ replicateComp 12 (some 0xFF),
                     writable := true }] }
    let src : ByteSubLens Nat := { addr := 1, offset := 0, len := 12 }
    let dst : ByteSubLens Nat := { addr := 1, offset := 12, len := 12 }
    ∃ m1 m2 : SliceStore (Option UInt8),
      copyRangeComp src dst mUninit = some m1 ∧
      copyRangeComp src dst mStale = some m2 ∧
      dst.get m1 ≠ dst.get m2 ∧
      (dst.zoom 4 4).getU32 c.toByteCodec m1 = some (BitVec.ofNat 32 0x55443322) ∧
      (dst.zoom 4 4).getU32 c.toByteCodec m2 = some (BitVec.ofNat 32 0x55443322) ∧
      (dst.zoom 1 1).getLe c.toByteCodec 1 m1 = none ∧
      (dst.zoom 1 1).getLe c.toByteCodec 1 m2 = some (BitVec.ofNat 8 0x99) := by
  refine ⟨_, _, rfl, rfl, ?_, rfl, rfl, rfl, rfl⟩
  intro hEq
  have hL :
      flattenByteRuns ByteRunCodec.optionUInt8
        (canaryPaddedPlain12 0x11 0x22 0x33 0x44 0x55 0x66) =
      flattenByteRuns ByteRunCodec.optionUInt8
        [.initPlain [0x11, 0x99, 0x99, 0x99, 0x22, 0x33, 0x44, 0x55, 0x66, 0xAA, 0xAA, 0xAA]] :=
    Option.some.inj hEq
  have hTail := (List.cons.inj hL).2
  have hHd := (List.cons.inj hTail).1
  cases hHd

/-- Raw `UInt8` (`PlainByteRunCodec.uint8`) canary verifying `copyRangeComp`
and `PlainByteRunCodec.uint8.decode_encode` over `SliceStore UInt8`. -/
theorem canary_byterun_raw_uint8 :
    let m0 : SliceStore UInt8 :=
      { allocs := [{ allocId := 1, bytes := [0x10, 0x20, 0x30, 0x40, 0x00, 0x00, 0x00, 0x00],
                     writable := true }] }
    let src : ByteSubLens Nat := { addr := 1, offset := 0, len := 4 }
    let dst : ByteSubLens Nat := { addr := 1, offset := 4, len := 4 }
    ∃ m1 : SliceStore UInt8,
      copyRangeComp src dst m0 = some m1 ∧
      dst.get m1 = some [0x10, 0x20, 0x30, 0x40] ∧
      PlainByteRunCodec.uint8.decodePlain? (PlainByteRunCodec.uint8.encodePlain 0x20) =
        some 0x20 :=
  ⟨_, rfl, rfl, rfl⟩

/-- Toy 2-stage copy machine exercising `@[irreducible] ByteRunCopyCut`
composition, disjoint framing, and `Anneal.Firewall.IndexedCut`. -/
private structure CopyToyState where
  pc : Nat
  mem : SliceStore (ByteRunAtom Nat)

private def copyToyStep (s : CopyToyState) :
    StepOutcome CopyToyState (SliceStore (ByteRunAtom Nat)) Unit :=
  match s.pc with
  | 0 =>
    match copyRangeComp { addr := 1, offset := 0, len := 12 }
        { addr := 1, offset := 12, len := 12 } s.mem with
    | some m1 => .step { pc := 1, mem := m1 }
    | none => .fault ()
  | 1 =>
    match copyRangeComp { addr := 1, offset := 12, len := 12 }
        { addr := 1, offset := 12, len := 12 } s.mem with
    | some m2 => .step { pc := 2, mem := m2 }
    | none => .fault ()
  | _ => .done s.mem

/-- End-to-end `ByteRunCopyCut` + `Anneal.Firewall.IndexedCut` composition and
disjoint-lens framing canary. -/
theorem canary_byterun_copy_cut_and_indexed_cut :
    let s0 : CopyToyState := { pc := 0, mem := canaryProvMixStore0 }
    let tail : ByteSubLens Nat := { addr := 1, offset := 24, len := 8 }
    ∃ s2 : CopyToyState,
      StepStageCut copyToyStep 2 s0 s2 ∧
      tail.get s2.mem = tail.get canaryProvMixStore0 := by
  let op1 : ByteRunCopyOp Nat :=
    .copyRange { addr := 1, offset := 0, len := 12 }
      { addr := 1, offset := 12, len := 12 }
  let op2 : ByteRunCopyOp Nat :=
    .copyRange { addr := 1, offset := 12, len := 12 }
      { addr := 1, offset := 12, len := 12 }
  let m1 : SliceStore (ByteRunAtom Nat) :=
    match copyRangeComp { addr := 1, offset := 0, len := 12 }
        { addr := 1, offset := 12, len := 12 } canaryProvMixStore0 with
    | some m => m
    | none => canaryProvMixStore0
  let s0 : CopyToyState := { pc := 0, mem := canaryProvMixStore0 }
  let s1 : CopyToyState := { pc := 1, mem := m1 }
  let s2 : CopyToyState := { pc := 2, mem := m1 }
  have hCut1 : ByteRunCopyCut copyToyStep CopyToyState.mem [op1] 1 s0 s1 :=
    ByteRunCopyCut.singleRange (StepStageCut.single rfl) rfl
  have hCut2 : ByteRunCopyCut copyToyStep CopyToyState.mem [op2] 1 s1 s2 :=
    ByteRunCopyCut.singleRange (StepStageCut.single rfl) rfl
  let opsAt : Nat → List (ByteRunCopyOp Nat)
    | 0 => [op1, op2]
    | _ => [op2]
  let fuelAt : Nat → Nat
    | 0 => 2
    | _ => 1
  have hIdx1 :
      Anneal.Firewall.IndexedCut
        (byteRunIndexedCutFamily copyToyStep CopyToyState.mem opsAt fuelAt s2)
        1 s1 :=
    ByteRunCopyCut.to_indexedCut hCut2
  have hIdx0 :
      Anneal.Firewall.IndexedCut
        (byteRunIndexedCutFamily copyToyStep CopyToyState.mem opsAt fuelAt s2)
        0 s0 :=
    byteRunIndexedCut_step (stage₁ := 0) (stage₂ := 1) rfl rfl hCut1 hIdx1
  refine ⟨s2, ?_, ?_⟩
  · exact byteRunIndexedCut_finish ByteRunCopyCut.to_stepStageCut hIdx0
  · have hCut02 :
        ByteRunCopyCut copyToyStep CopyToyState.mem [op1, op2] 2 s0 s2 :=
      Anneal.Firewall.open_cut hIdx0
    have hDisj :
        AllCopyOpsDisjoint (SliceStore (ByteRunAtom Nat))
          { addr := 1, offset := 24, len := 8 } [op1, op2] :=
      ⟨ByteSubLens.disjoint_of_separated
          (ByteSubLens.separated_of_natLensSeparatedBool rfl),
       ByteSubLens.disjoint_of_separated
          (ByteSubLens.separated_of_natLensSeparatedBool rfl),
       True.intro⟩
    exact ByteRunCopyCut.frame_disjoint hDisj hCut02

/-- Fail-closed negative regression suite: zero `src.len`, zero `dst.len`,
mismatched lengths, zero repeat count `n = 0`, zero repeat `elemLen`,
out-of-bounds target, unwritable allocation `2`, and missing allocation `99`. -/
theorem canary_byterun_negative_fail_closed :
    copyRangeComp { addr := 1, offset := 0, len := 0 }
      { addr := 1, offset := 12, len := 0 } canaryProvMixStore0 = none ∧
    copyRangeComp { addr := 1, offset := 0, len := 12 }
      { addr := 1, offset := 12, len := 0 } canaryProvMixStore0 = none ∧
    copyRangeComp { addr := 1, offset := 0, len := 12 }
      { addr := 1, offset := 12, len := 8 } canaryProvMixStore0 = none ∧
    copyRepeatedlyComp { addr := 1, offset := 0, len := 12 }
      1 12 0 canaryRepeatStore0 = none ∧
    copyRepeatedlyComp { addr := 1, offset := 0, len := 0 }
      1 12 3 canaryRepeatStore0 = none ∧
    copyRangeComp { addr := 1, offset := 0, len := 12 }
      { addr := 1, offset := 28, len := 12 } canaryProvMixStore0 = none ∧
    copyRangeComp { addr := 1, offset := 0, len := 4 }
      { addr := 2, offset := 0, len := 4 } canaryProvMixStore0 = none ∧
    copyRangeComp { addr := 99, offset := 0, len := 4 }
      { addr := 1, offset := 12, len := 4 } canaryProvMixStore0 = none :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end Anneal.ParametricCore
