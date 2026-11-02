-- @anneal-allow-replace-rust-spec
import Trusted
import Mir.FuchsiaUsercopy.fidl_chunk_padding_len
import Obligations.FuchsiaUsercopy.fidl_chunk_padding_len

namespace Specs.FuchsiaUsercopy.fidl_chunk_padding_len

open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult

/-- Precondition over representative FIDL wire element sizes `es ∈ {1, 4, 8}`
    (`u8`, `u32`, `u64`/`Chunk`, all satisfying `align_of::<T>() <= CHUNK_SIZE = 8`)
    and slice lengths `len ∈ {0, 1, 3, 8}` covering empty, unaligned, and
    chunk-aligned FIDL slices in `DecoderExt::take_slice_slot`
    (`src/lib/fidl/rust_next/fidl_next_codec/src/decoder.rs:150-179`). -/
def pre (args : List Value) : Prop :=
  ∃ (es len : Nat),
    (es = 1 ∨ es = 4 ∨ es = 8) ∧
    (len = 0 ∨ len = 1 ∨ len = 3 ∨ len = 8) ∧
    args =
      [ .scalar { bits := es, sizeBytes := 8 }
      , .scalar { bits := len, sizeBytes := 8 } ]

/-- Exact postcondition: returns `(slice_byte_length, padding_length)` where
    `padding_length = ((es * len + 7) / 8) * 8 - es * len < 8` and
    `(es * len) + padding_length == ((es * len + 7) / 8) * 8`. -/
def post (args : List Value) (ret : Value) : Prop :=
  ∀ (es len : Nat),
    args =
      [ .scalar { bits := es, sizeBytes := 8 }
      , .scalar { bits := len, sizeBytes := 8 } ] →
    let bl := es * len
    let pad := ((bl + 7) / 8) * 8 - bl
    ret = .aggregate 0
      [ .scalar { bits := bl, sizeBytes := 8 }
      , .scalar { bits := pad, sizeBytes := 8 } ] ∧
    pad < 8 ∧
    bl + pad = ((bl + 7) / 8) * 8

instance : ItemSpec "fuchsia_usercopy::fidl_chunk_padding_len" where
  pre := pre
  post := post

instance : StatefulItemSpec "fuchsia_usercopy::fidl_chunk_padding_len" where
  pre := fun args mem => pre args ∧ mem = emptyMemory
  post := fun args _ ret _ => post args ret

end Specs.FuchsiaUsercopy.fidl_chunk_padding_len
