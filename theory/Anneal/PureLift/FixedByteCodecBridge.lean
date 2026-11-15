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

end Anneal.PureLift.FixedByteCodecBridge
