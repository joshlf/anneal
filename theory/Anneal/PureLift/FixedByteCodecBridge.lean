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

end Anneal.PureLift.FixedByteCodecBridge
