-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import Anneal.ByteCodec
import Anneal.PureLift.V2026_06_01Bridge

/-!
# `Anneal.ByteCodec.FixedByteCodec` ↔ `PureLift.SpatialCodec` Bridge (`FixedByteCodecBridge`)

Standalone bridge module lifting any provenance-free `Anneal.ByteCodec.FixedByteCodec α n`
to `Anneal.SepLogicLenses.ByteLensCodec α n` and `Anneal.PureLift.SpatialCodec Val`
(and `SpatialCodec StdVal`), while connecting `FixedByteCodec.IsInitCodec` and
`FixedByteCodec.IsSurjectiveInitDecoder` to `hasUninitCell` and `SpatialCodec`
reabsorption.
-/

namespace Anneal.PureLift.FixedByteCodecBridge

open Anneal.ByteCodec
open Anneal.PureLift
open Anneal.PureLift.MirLiftCoreInterop
open Anneal.PureLift.V2026_06_01Bridge
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics

/-- Convert any `Anneal.ByteCodec.FixedByteCodec α n` to an
`Anneal.SepLogicLenses.ByteLensCodec α n`. -/
def byteLensCodecOfFixedByteCodec {α : Type} {n : Nat}
    (c : FixedByteCodec α n) : Anneal.SepLogicLenses.ByteLensCodec α n where
  encode := c.encode
  decode := c.decode
  encode_len := c.encode_length
  decode_encode := c.decode_encode

/-- Lift any provenance-free `Anneal.ByteCodec.FixedByteCodec α n` to a
`PureLift.SpatialCodec Val` via `spatialCodecOfByteLensCodec`. -/
def spatialCodecOfFixedByteCodec {Val α : Type} {n : Nat}
    (cid : Nat) (c : FixedByteCodec α n)
    (hProv : ∀ a : α, provenanceFree (c.encode a) = true)
    (toVal : α → Val) (ofVal? : Val → Option α)
    (toVal_ofVal? : ∀ (v : Val) (a : α), ofVal? v = some a → toVal a = v) :
    SpatialCodec Val :=
  spatialCodecOfByteLensCodec cid (byteLensCodecOfFixedByteCodec c) hProv
    toVal ofVal? toVal_ofVal?

/-- Every `FixedByteCodec` lifted via `spatialCodecOfFixedByteCodec` satisfies
`LawfulCodec`. -/
theorem spatialCodecOfFixedByteCodec_lawful {Val α : Type} {n : Nat}
    (cid : Nat) (c : FixedByteCodec α n)
    (hProv : ∀ a : α, provenanceFree (c.encode a) = true)
    (toVal : α → Val) (ofVal? : Val → Option α)
    (toVal_ofVal? : ∀ (v : Val) (a : α), ofVal? v = some a → toVal a = v) :
    LawfulCodec
      (spatialCodecOfFixedByteCodec cid c hProv toVal ofVal? toVal_ofVal?) :=
  (spatialCodecOfFixedByteCodec cid c hProv toVal ofVal? toVal_ofVal?).decode_encode

/-- If `c` is an `IsInitCodec` (`IntoBytes` side-condition), freezing any value
in `α`'s image produces an `.uninit`-free cell window (`hasUninitCell = false`). -/
theorem spatialCodecOfFixedByteCodec_hasUninitCell_false {Val α : Type} {n : Nat}
    (cid : Nat) (c : FixedByteCodec α n)
    (hProv : ∀ a : α, provenanceFree (c.encode a) = true)
    (hInit : c.IsInitCodec)
    (toVal : α → Val) (ofVal? : Val → Option α)
    (toVal_ofVal? : ∀ (v : Val) (a : α), ofVal? v = some a → toVal a = v)
    (v : Val) (a : α) (hv : ofVal? v = some a) :
    hasUninitCell
      ((spatialCodecOfFixedByteCodec cid c hProv toVal ofVal?
          toVal_ofVal?).encode v) = false :=
  spatialCodecOfByteLensCodec_hasUninitCell_false cid
    (byteLensCodecOfFixedByteCodec c) hProv toVal ofVal? toVal_ofVal?
    v a hv (hInit a)

/-- Non-vacuous `SpatialCodec StdVal` lifted directly from
`FixedByteCodec.boolByte` (`0x00 ↦ false`, `0x01 ↦ true`, `0x02 ↦ none`). -/
def fixedBoolSpatialCodec : SpatialCodec StdVal :=
  spatialCodecOfFixedByteCodec 101 FixedByteCodec.boolByte
    (fun b => by cases b <;> rfl) boolEmbed stdAsBool boolEmbed_embed?

theorem fixedBoolSpatialCodec_canary :
    fixedBoolSpatialCodec.encode (.bool true) = [.rawByte 1] ∧
    fixedBoolSpatialCodec.decode [.rawByte 0] = some (.bool false) ∧
    fixedBoolSpatialCodec.decode [.rawByte 2] = none ∧
    fixedBoolSpatialCodec.decode [.uninit] = none :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ## `MirValueCodec` → `MirTypedByteCodec`: live-MIR window bridges for `FixedByteCodec` -/

/-- Every `ByteCodec.MirValueCodec` with provenance-free encodings is a
`V2026_06_01Bridge.MirTypedByteCodec`, so its `FixedByteCodec` inherits every
live-MIR window bridge: freezing writes the trusted operational byte window
(`spatialCodec_freeze_eq_placeByteWindow`), unpinning succeeds iff the trusted
decoder does (`spatialCodec_unpin_iff_mir_decode`), the state-level pin
lifecycle bridges (`freeze_spatialPinnedBlockHolds`,
`unpin_eq_live_mir_decode`), and the `BitValidity` marker-trait bridges. -/
def mirTypedByteCodecOfMirValueCodec {layouts : LayoutTable} {ty : Ty} {α : Type} {sz : Nat}
    (m : MirValueCodec layouts ty α sz)
    (hProv : ∀ x : α, provenanceFree (m.codec.encode x) = true) :
    MirTypedByteCodec layouts ty α sz where
  codec := byteLensCodecOfFixedByteCodec m.codec
  toValue := m.toValue
  ofValue := m.ofValue
  ofValue_toValue := m.ofValue_toValue
  tySize_eq := m.tySize_eq
  encode_toValue := m.encode_toValue
  decode_eq_map := m.decode_eq_map
  encode_provenanceFree := hProv

/-- `ByteCodec.MirValueCodec.bool` (`FixedByteCodec.boolByte`) as a
`MirTypedByteCodec`. -/
def fixedBoolMirCodec (layouts : LayoutTable) : MirTypedByteCodec layouts boolTy Bool 1 :=
  mirTypedByteCodecOfMirValueCodec (MirValueCodec.bool layouts 0) (fun b => by cases b <;> rfl)

/-- `ByteCodec.MirValueCodec.uint .u32` (`FixedByteCodec.uintBitsLE 4`) as a
`MirTypedByteCodec`. -/
def fixedU32MirCodec (layouts : LayoutTable) :
    MirTypedByteCodec layouts u32Ty { bits : Nat // bits < 2 ^ (8 * 4) } 4 :=
  mirTypedByteCodecOfMirValueCodec (MirValueCodec.uint layouts .u32 0)
    (fun x => provenanceFree_encodeLittleEndianBytes 4 x.val)

/-- `zerocopy` marker traits through the `FixedByteCodec` path: `bool` is
`TryFromBytes` but not `FromBytes` (`0x02` is initialized yet rejected by
`FixedByteCodec.boolByte`). -/
theorem fixedBool_bitValidity (layouts : LayoutTable) :
    Anneal.BitValidity.IsTryFromBytes layouts boolTy
      (fun v => Exists fun b => (fixedBoolMirCodec layouts).toValue b = v ∧
        (fixedBoolMirCodec layouts).ofValue v = some b) ∧
    ¬ Anneal.BitValidity.IsFromBytes layouts boolTy :=
  ⟨(fixedBoolMirCodec layouts).isTryFromBytes,
   (fixedBoolMirCodec layouts).not_isFromBytes [.init (UInt8.ofNat 2) none] rfl rfl rfl⟩

/-- Embedding of `FixedByteCodec.uintBitsLE 4` values into `StdVal` naturals. -/
def fixedU32Embed (x : { bits : Nat // bits < 2 ^ (8 * 4) }) : StdVal := .nat x.val

/-- Partial inverse of `fixedU32Embed`. -/
def fixedU32Embed? (v : StdVal) : Option { bits : Nat // bits < 2 ^ (8 * 4) } :=
  match stdNatVal? v with
  | some k => if h : k < 2 ^ (8 * 4) then some ⟨k, h⟩ else none
  | none => none

theorem fixedU32Embed_embed? (v : StdVal) (x : { bits : Nat // bits < 2 ^ (8 * 4) })
    (h : fixedU32Embed? v = some x) : fixedU32Embed x = v := by
  cases v with
  | mk fuel tree =>
    cases tree with
    | nat k =>
      unfold fixedU32Embed? at h
      change (if h : k < 2 ^ (8 * 4) then some ⟨k, h⟩ else none) = some x at h
      by_cases hk : k < 2 ^ (8 * 4)
      · rw [dite_eq_left hk] at h
        injection h with h
        subst h
        rfl
      · rw [dite_eq_right hk] at h
        exact nomatch h
    | _ => exact nomatch h

/-- **`FixedByteCodec` freeze = live MIR window**: freezing `5 : u32` with the
spatial codec induced by `ByteCodec.MirValueCodec.uint .u32` writes exactly the
trusted byte window of a live MIR local holding `5`, `TypedAt` under the lifted
`FixedByteCodec`, and unpinning a rewritten window decodes it exactly as the
trusted `u32` decoder does. -/
theorem fixedU32_live_window_canary (layouts : LayoutTable) :
    let m := fixedU32MirCodec layouts
    let sc := m.spatialCodec 132 fixedU32Embed fixedU32Embed? fixedU32Embed_embed?
    let ms : MachineState :=
      { frame := { blockIdx := 0, stmtIdx := 0, locals := [.init (.scalar ⟨5, 4⟩)] },
        memory := emptyMemory }
    (placeByteWindow? layouts u32Ty ms 0 [] = some (m.codec.encode ⟨5, by decide⟩) ∧
      abstractBytesOfCells (sc.encode (.nat 5)) = some (m.codec.encode ⟨5, by decide⟩) ∧
      Anneal.SepLogicLenses.TypedAt m.codec 0 ⟨5, by decide⟩ (m.codec.encode ⟨5, by decide⟩)) ∧
    sc.decode [.rawByte 6, .rawByte 0, .rawByte 0, .rawByte 0] = some (.nat 6) ∧
    sc.decode [.uninit, .rawByte 0, .rawByte 0, .rawByte 0] = none := by
  intro m sc ms
  exact ⟨spatialCodec_freeze_eq_placeByteWindow m 132 fixedU32Embed fixedU32Embed?
      fixedU32Embed_embed? ms 0 [] (.nat 5) ⟨5, by decide⟩ rfl rfl,
    (m.spatialCodec_unpin_iff_mir_decode 132 fixedU32Embed fixedU32Embed?
      fixedU32Embed_embed? [.rawByte 6, .rawByte 0, .rawByte 0, .rawByte 0]
      [.init 6 none, .init 0 none, .init 0 none, .init 0 none] rfl rfl).2 ⟨6, by decide⟩ rfl,
    rfl⟩

/-! ## `FixedByteCodec.scalarValidRange` (`NonZeroU32`) → `SpatialCodec StdVal` -/

/-- `NonZeroU32` wrapping range `1..=u32::MAX`. -/
def nonZeroU32Range : WrappingRange :=
  { start := 1, end_ := 2 ^ (8 * 4) - 1 }

/-- `FixedByteCodec` for `NonZeroU32` (`scalarValidRange 4 _ nonZeroU32Range`). -/
def fixedNonZeroU32Codec :
    FixedByteCodec
      { bits : Nat // bits < 2 ^ (8 * 4) ∧ wrappingRangeContains nonZeroU32Range bits = true }
      4 :=
  FixedByteCodec.scalarValidRange 4 (by decide) nonZeroU32Range

def fixedNonZeroU32Embed
    (x : { bits : Nat // bits < 2 ^ (8 * 4) ∧ wrappingRangeContains nonZeroU32Range bits = true }) :
    StdVal :=
  .nat x.val

def fixedNonZeroU32Embed? (v : StdVal) :
    Option
      { bits : Nat // bits < 2 ^ (8 * 4) ∧ wrappingRangeContains nonZeroU32Range bits = true } :=
  match stdNatVal? v with
  | some k =>
    if hk : k < 2 ^ (8 * 4) ∧ wrappingRangeContains nonZeroU32Range k = true then
      some ⟨k, hk⟩
    else none
  | none => none

theorem fixedNonZeroU32Embed_embed? (v : StdVal)
    (x : { bits : Nat // bits < 2 ^ (8 * 4) ∧ wrappingRangeContains nonZeroU32Range bits = true })
    (h : fixedNonZeroU32Embed? v = some x) : fixedNonZeroU32Embed x = v := by
  cases v with
  | mk fuel tree =>
    cases tree with
    | nat k =>
      unfold fixedNonZeroU32Embed? at h
      dsimp only [stdNatVal?] at h
      by_cases hk : k < 2 ^ (8 * 4) ∧ wrappingRangeContains nonZeroU32Range k = true
      · rw [dite_eq_left hk] at h
        injection h with h
        subst h
        rfl
      · rw [dite_eq_right hk] at h
        exact nomatch h
    | _ => exact nomatch h

/-- `NonZeroU32` `SpatialCodec StdVal` lifted from `FixedByteCodec.scalarValidRange`. -/
def fixedNonZeroU32SpatialCodec : SpatialCodec StdVal :=
  spatialCodecOfFixedByteCodec 133 fixedNonZeroU32Codec
    (fun x => provenanceFree_encodeLittleEndianBytes 4 x.val)
    fixedNonZeroU32Embed fixedNonZeroU32Embed? fixedNonZeroU32Embed_embed?

theorem fixedNonZeroU32_canary :
    fixedNonZeroU32SpatialCodec.encode (.nat 7) =
      [.rawByte 7, .rawByte 0, .rawByte 0, .rawByte 0] ∧
    fixedNonZeroU32SpatialCodec.decode
      [.rawByte 7, .rawByte 0, .rawByte 0, .rawByte 0] = some (.nat 7) ∧
    fixedNonZeroU32SpatialCodec.decode
      [.rawByte 0, .rawByte 0, .rawByte 0, .rawByte 0] = none ∧
    fixedNonZeroU32SpatialCodec.decode
      [.uninit, .rawByte 0, .rawByte 0, .rawByte 0] = none :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ## `NonZeroU32` against the trusted niche decoder (`MirValueCodec.scalarNicheNewtype`) -/

/-- `rustc` layout of `core::num::NonZeroU32`: a 4-byte scalar newtype whose
valid range `1..=u32::MAX` makes `0` a niche. -/
def nonZeroU32Layout : TypeLayout :=
  { size := { bytes := 4 }, align := { bytes := 4 },
    backendRepr := .scalar (.initialized (.int 32 false) nonZeroU32Range),
    fields := .arbitrary [{ bytes := 0 }] [0],
    variants := .single 0,
    isUninhabited := false }

/-- Layout table holding `nonZeroU32Layout` at index `0`. -/
def nonZeroU32Layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := [nonZeroU32Layout] }

/-- MIR type `core::num::NonZeroU32` at layout index `0`. -/
def nonZeroU32Ty : Ty := { kind := .adt "core::num::NonZeroU32" [], layoutIdx := 0 }

/-- `ByteCodec.MirValueCodec.scalarNicheNewtype` for `NonZeroU32`, lifted to a
`MirTypedByteCodec`: its `FixedByteCodec.scalarValidRange` agrees pointwise
with the trusted niche-checking decoder. -/
def fixedNonZeroU32MirCodec :
    MirTypedByteCodec nonZeroU32Layouts nonZeroU32Ty
      { bits : Nat // bits < 2 ^ (8 * 4) ∧ wrappingRangeContains nonZeroU32Range bits = true }
      4 :=
  mirTypedByteCodecOfMirValueCodec
    (MirValueCodec.scalarNicheNewtype nonZeroU32Layouts "core::num::NonZeroU32" 0
      nonZeroU32Layout 4 32 false 0 [0] nonZeroU32Range (by decide) rfl rfl rfl rfl rfl rfl
      rfl rfl)
    (fun x => provenanceFree_encodeLittleEndianBytes 4 x.val)

/-- **`0` for `NonZeroU32` fails exactly as in the trusted semantics**: a live
`NonZeroU32` local holding `7` freezes to its trusted byte window, the trusted
decoder rejects the all-zero window, so unpinning `[0, 0, 0, 0]` fails while
`[42, 0, 0, 0]` unpins to `42`, and `NonZeroU32` is not `zerocopy::FromBytes`. -/
theorem fixedNonZeroU32_live_niche_canary :
    let m := fixedNonZeroU32MirCodec
    let sc := m.spatialCodec 134 fixedNonZeroU32Embed fixedNonZeroU32Embed?
      fixedNonZeroU32Embed_embed?
    let ms : MachineState :=
      { frame :=
          { blockIdx := 0, stmtIdx := 0,
            locals := [.init (.aggregate 0 [.scalar ⟨7, 4⟩])] },
        memory := emptyMemory }
    placeByteWindow? nonZeroU32Layouts nonZeroU32Ty ms 0 [] =
      some [.init 7 none, .init 0 none, .init 0 none, .init 0 none] ∧
    decodeValueFromBytes defaultCodecFuel nonZeroU32Layouts nonZeroU32Ty
      [.init 0 none, .init 0 none, .init 0 none, .init 0 none] = none ∧
    sc.decode [.rawByte 0, .rawByte 0, .rawByte 0, .rawByte 0] = none ∧
    sc.decode [.rawByte 42, .rawByte 0, .rawByte 0, .rawByte 0] = some (.nat 42) ∧
    ¬ Anneal.BitValidity.IsFromBytes nonZeroU32Layouts nonZeroU32Ty := by
  intro m sc ms
  exact ⟨rfl, rfl, rfl, rfl,
    m.not_isFromBytes [.init 0 none, .init 0 none, .init 0 none, .init 0 none] rfl rfl rfl⟩

end Anneal.PureLift.FixedByteCodecBridge
