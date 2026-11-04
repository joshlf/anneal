/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import MiniRustSpec.Generated
import MiniRustSpec.Interp

/-!
# Anchors: what `MiniRustSpec.Interp` transcribes

`MiniRustSpec.Interp` is a hand-written, executable transcription of a small
part of the vendored MiniRust specification; every definition quotes the
spec text it transcribes. This module pins each transcribed upstream item, by
name, source line, and SHA-256 of its token stream, to the *generated* model
(`MiniRustSpec.Generated`, produced mechanically from the vendored sources).

`anchors_ok` is checked by the kernel. If the vendored specification changes
(for example after re-pinning MiniRust and regenerating), any changed item
breaks the build here, which forces a re-review of the corresponding
transcriptions (listed in `interp`) instead of letting them drift silently.
The double-backtick names make the build fail as well if a listed
transcription is renamed or removed.

`libspecr` operations (`Int::in_bounds`, `Map`, `List`, ...) live in the
`libspecr` crate, not in the vendored spec, and have no anchor; they are
transcribed from `libspecr` 0.1.41 (see `MiniRustSpec.Interp`).
-/

namespace MiniRustSpec.Anchors

open MiniRustSpec.Syntax (SourceItem)

/-- One transcribed upstream item. -/
structure Anchor : Type where
  /-- The definitions in `MiniRustSpec.Interp` that transcribe (part of) the item. -/
  interp : List Lean.Name
  /-- The vendored spec file containing the item. -/
  file : String
  /-- The generated item list of that file. -/
  items : List SourceItem
  /-- The generated item name. -/
  name : String
  /-- The line of the item in the vendored file. -/
  line : Nat
  /-- The SHA-256 of the item's token stream, as recorded by the generator. -/
  tokenSha256 : String

/-- The generated model contains the pinned item unchanged, the anchor cites a
known vendored file, and links at least one `MiniRustSpec.Interp` definition. -/
def Anchor.ok (a : Anchor) : Bool :=
  !a.interp.isEmpty &&
  MiniRustSpec.Generated.Manifest.vendoredFiles.any (fun (f, _) => f == a.file) &&
  a.items.any (fun i => i.name == a.name && i.line == a.line && i.tokenSha256 == a.tokenSha256)

/-- Every upstream item transcribed by `MiniRustSpec.Interp`. -/
def anchors : List Anchor := [
  { interp := [``MiniRustSpec.Interp.step, ``MiniRustSpec.Interp.steps, ``MiniRustSpec.Interp.pickActiveThread],
    file := "spec/lang/machine.md", items := MiniRustSpec.Gen.Items.Lang.Machine.items,
    name := "impl_Machine__new", line := 128,
    tokenSha256 := "45ee0382262183b14b28c5fad1005abbbcbb8bcf0f0cc536fb55ad12605190cf" },
  { interp := [``MiniRustSpec.Interp.activeThread, ``MiniRustSpec.Interp.curFrame, ``MiniRustSpec.Interp.mutateCurFrame],
    file := "spec/lang/machine.md", items := MiniRustSpec.Gen.Items.Lang.Machine.items,
    name := "impl_Machine__active_thread", line := 246,
    tokenSha256 := "e1ba15aad87afbb3de6c4aeae1f4639ae48acfdce0be83da8db00a1bbeeb5582" },
  { interp := [``MiniRustSpec.Interp.curFrame, ``MiniRustSpec.Interp.mutateCurFrame],
    file := "spec/lang/machine.md", items := MiniRustSpec.Gen.Items.Lang.Machine.items,
    name := "impl_Thread__cur_frame", line := 272,
    tokenSha256 := "9c7c08af8ad7f1407c6daa053b0c84ad9e5a3139be3167f7ed9d1e359825337e" },
  { interp := [``MiniRustSpec.Interp.jumpToBlock],
    file := "spec/lang/machine.md", items := MiniRustSpec.Gen.Items.Lang.Machine.items,
    name := "impl_StackFrame__jump_to_block", line := 296,
    tokenSha256 := "f8853893d8d78e8ee1e51a8c74d59bb1b4d7db3781f20e96b02ec7b86655ae22" },
  { interp := [``MiniRustSpec.Interp.resetDataRaceTracking],
    file := "spec/lang/machine.md", items := MiniRustSpec.Gen.Items.Lang.Machine.items,
    name := "impl_Machine__new_thread", line := 308,
    tokenSha256 := "cb6de376722065548f7d8e61627a4e969d70c5fe7f347b09a55f2512cdbbe185" },
  { interp := [``MiniRustSpec.Interp.Type.decode, ``MiniRustSpec.Interp.Type.encode],
    file := "spec/lang/representation.md", items := MiniRustSpec.Gen.Items.Lang.Representation.items,
    name := "impl_Type__decode_1", line := 53,
    tokenSha256 := "8b035d58220d31689dc801bfa0990355edcb221c72f0609d8747c0d855c8ab5c" },
  { interp := [``MiniRustSpec.Interp.Type.decodeInt, ``MiniRustSpec.Interp.Type.encodeInt],
    file := "spec/lang/representation.md", items := MiniRustSpec.Gen.Items.Lang.Representation.items,
    name := "impl_Type__decode_2", line := 74,
    tokenSha256 := "fd8f4073f6460ce36c081b9f88e4fb5a759dadf0783dc3f6603023ae5c085fdf" },
  { interp := [``MiniRustSpec.Interp.Type.decode, ``MiniRustSpec.Interp.Type.encode,
      ``MiniRustSpec.Interp.Type.decodeFields, ``MiniRustSpec.Interp.Type.encodeFields],
    file := "spec/lang/representation.md", items := MiniRustSpec.Gen.Items.Lang.Representation.items,
    name := "impl_Type__decode_4", line := 248,
    tokenSha256 := "acb13b3c90aff1f53f590beab7f15600996d58482f87940eb81aa18a3b0535ad" },
  { interp := [``MiniRustSpec.Interp.decodeDiscriminant,
      ``MiniRustSpec.Interp.decodeDiscriminantChildren],
    file := "spec/lang/representation.md", items := MiniRustSpec.Gen.Items.Lang.Representation.items,
    name := "fn_decode_discriminant", line := 353,
    tokenSha256 := "5487eb6ae19c8c24537b029da2db0b1aa497326cbaa69fe2a197ebb6b07509ff" },
  { interp := [``MiniRustSpec.Interp.encodeDiscriminant],
    file := "spec/lang/representation.md", items := MiniRustSpec.Gen.Items.Lang.Representation.items,
    name := "fn_encode_discriminant", line := 377,
    tokenSha256 := "be434e2a3af0dcf0c006a01d6e376fa8b3451dcc3e496cbe3739e9af85c3cea9" },
  { interp := [``MiniRustSpec.Interp.Type.decode, ``MiniRustSpec.Interp.Type.encode,
      ``MiniRustSpec.Interp.Type.decodeVariant, ``MiniRustSpec.Interp.Type.encodeVariant],
    file := "spec/lang/representation.md", items := MiniRustSpec.Gen.Items.Lang.Representation.items,
    name := "impl_Type__decode_7", line := 393,
    tokenSha256 := "c02900dc855aadab1e82cf3752a93ea12061fb42ca0878f9c9e96fe8b191b6fd" },
  { interp := [``MiniRustSpec.Interp.Type.decode, ``MiniRustSpec.Interp.Type.encode],
    file := "spec/lang/representation.md", items := MiniRustSpec.Gen.Items.Lang.Representation.items,
    name := "impl_Type__decode_8", line := 441,
    tokenSha256 := "9fac7e2c667bef1c4998cc768fc1a949c45f6c456e37a174e5af92a83c8950b0" },
  { interp := [``MiniRustSpec.Interp.Type.decode, ``MiniRustSpec.Interp.Type.encode],
    file := "spec/lang/representation.md", items := MiniRustSpec.Gen.Items.Lang.Representation.items,
    name := "impl_Type__decode_9", line := 450,
    tokenSha256 := "2fd60590d2d3862b33ed07a1759f3fe451dd790001b1e4280995a3c0ad13df13" },
  { interp := [``MiniRustSpec.Interp.checkValue, ``MiniRustSpec.Interp.checkFields,
      ``MiniRustSpec.Interp.checkVariant],
    file := "spec/lang/representation.md", items := MiniRustSpec.Gen.Items.Lang.Representation.items,
    name := "impl_Machine__check_ptr_metadata", line := 488,
    tokenSha256 := "95e22453eb77af02c809ebd8bc9ee541641a186dff2e49494c720161013e4a4a" },
  { interp := [``MiniRustSpec.Interp.typedLoad, ``MiniRustSpec.Interp.typedStore],
    file := "spec/lang/representation.md", items := MiniRustSpec.Gen.Items.Lang.Representation.items,
    name := "impl_Machine__typed_store", line := 599,
    tokenSha256 := "1dcf6053cc92c46aaf645bf35f514bd6c20722d75a485b3defb8c4496449f21e" },
  { interp := [``MiniRustSpec.Interp.transmute, ``MiniRustSpec.Interp.evalCastOp],
    file := "spec/lang/representation.md", items := MiniRustSpec.Gen.Items.Lang.Representation.items,
    name := "impl_Machine__transmute", line := 788,
    tokenSha256 := "c38b1df79341aa42f078869af8ee4b2e17946dd8fc82b2a17ef95bfdc7801306" },
  { interp := [``MiniRustSpec.Interp.evalConstant, ``MiniRustSpec.Interp.evalValue],
    file := "spec/lang/step/expressions.md", items := MiniRustSpec.Gen.Items.Lang.Step.Expressions.items,
    name := "impl_Machine__eval_constant", line := 32,
    tokenSha256 := "f83c7a5a7f61bfc3655b244d7ebd021aea5cc9c9601ddcadc5844225f451b948" },
  { interp := [``MiniRustSpec.Interp.placeLoad, ``MiniRustSpec.Interp.evalValue],
    file := "spec/lang/step/expressions.md", items := MiniRustSpec.Gen.Items.Lang.Step.Expressions.items,
    name := "impl_Machine__place_load", line := 137,
    tokenSha256 := "3330de96a32652660764c9241138d151b22712bafefb3dbb53f0950ab2a787a1" },
  { interp := [``MiniRustSpec.Interp.evalValue],
    file := "spec/lang/step/expressions.md", items := MiniRustSpec.Gen.Items.Lang.Step.Expressions.items,
    name := "impl_Machine__eval_value_6", line := 186,
    tokenSha256 := "4793fa0f7bd635890ad9b7916a959cac72a0df67faf4b09f02e98608807b7a3a" },
  { interp := [``MiniRustSpec.Interp.evalPlace],
    file := "spec/lang/step/expressions.md", items := MiniRustSpec.Gen.Items.Lang.Step.Expressions.items,
    name := "impl_Machine__eval_place_1", line := 227,
    tokenSha256 := "d27f2a90134d1584080d2ebb4017f10067ce4c01f56693a7194f2613921d1ac7" },
  { interp := [``MiniRustSpec.Interp.evalUnOp],
    file := "spec/lang/step/operators.md", items := MiniRustSpec.Gen.Items.Lang.Step.Operators.items,
    name := "impl_Machine__eval_un_op_0", line := 8,
    tokenSha256 := "bc75edbbf21e7bb11a120a95abc8a509426c9b7cb4c30a01bb944e71406609fe" },
  { interp := [``MiniRustSpec.Interp.evalIntUnOp, ``MiniRustSpec.Interp.evalUnOp],
    file := "spec/lang/step/operators.md", items := MiniRustSpec.Gen.Items.Lang.Step.Operators.items,
    name := "impl_Machine__eval_int_un_op", line := 17,
    tokenSha256 := "d77850d14b0077d0b31ad48e5c3d50802b1d00c71cdc81df3cf0fdca386ab4bb" },
  { interp := [``MiniRustSpec.Interp.evalCountOnes, ``MiniRustSpec.Interp.countOnesLoop],
    file := "spec/lang/step/operators.md", items := MiniRustSpec.Gen.Items.Lang.Step.Operators.items,
    name := "impl_Machine__eval_count_ones", line := 58,
    tokenSha256 := "c19ca4f371134183b42adeb305d0bb2e682898ca36ae70e8f31f3f1cbeb95244" },
  { interp := [``MiniRustSpec.Interp.evalCastOp, ``MiniRustSpec.Interp.evalUnOp],
    file := "spec/lang/step/operators.md", items := MiniRustSpec.Gen.Items.Lang.Step.Operators.items,
    name := "impl_Machine__eval_cast_op", line := 76,
    tokenSha256 := "acaf7b511f4694d2d02cd11ee8fe9dd965ef3171e58213e3abce23147f031deb" },
  { interp := [``MiniRustSpec.Interp.evalBinOp],
    file := "spec/lang/step/operators.md", items := MiniRustSpec.Gen.Items.Lang.Step.Operators.items,
    name := "impl_Machine__eval_bin_op_0", line := 171,
    tokenSha256 := "babc56bb30b8c282e04b3b495b8edf1d8d812b4a8a35bd0d9c0cfc3e0c0c8f33" },
  { interp := [``MiniRustSpec.Interp.evalIntBinOp, ``MiniRustSpec.Interp.evalBinOp],
    file := "spec/lang/step/operators.md", items := MiniRustSpec.Gen.Items.Lang.Step.Operators.items,
    name := "impl_Machine__eval_int_bin_op", line := 186,
    tokenSha256 := "8ceef5b3ae1db7826d008630b6f69c068d3689399431e236d52334cc2515cbef" },
  { interp := [``MiniRustSpec.Interp.evalRelOp, ``MiniRustSpec.Interp.evalBinOp,
      ``MiniRustSpec.Interp.intCmp, ``MiniRustSpec.Interp.boolCmp],
    file := "spec/lang/step/operators.md", items := MiniRustSpec.Gen.Items.Lang.Step.Operators.items,
    name := "impl_Machine__eval_rel_op", line := 320,
    tokenSha256 := "3cab9c6e85014ab92350e36f11c22d7e9c7a319170cf825acdf63ed51942da1e" },
  { interp := [``MiniRustSpec.Interp.placeStore, ``MiniRustSpec.Interp.evalStatement],
    file := "spec/lang/step/statements.md", items := MiniRustSpec.Gen.Items.Lang.Step.Statements.items,
    name := "impl_Machine__place_store", line := 22,
    tokenSha256 := "fc21c13f72094299b758afae6a312a8afbcff911a24d381aea444d354ef8a818" },
  { interp := [``MiniRustSpec.Interp.evalStatement],
    file := "spec/lang/step/statements.md", items := MiniRustSpec.Gen.Items.Lang.Step.Statements.items,
    name := "impl_Machine__eval_statement_1", line := 49,
    tokenSha256 := "d4af5d9efa3f6feadddfefdedbbd19ffbb205cc221fa91e3c981999ae1d15d55" },
  { interp := [``MiniRustSpec.Interp.storageDead],
    file := "spec/lang/step/statements.md", items := MiniRustSpec.Gen.Items.Lang.Step.Statements.items,
    name := "impl_StackFrame__storage_live", line := 165,
    tokenSha256 := "e59ebbc763b68d58a81bb41a1aa9cd5b2bbd56f38afc2839720791f51d233e08" },
  { interp := [``MiniRustSpec.Interp.evalTerminator, ``MiniRustSpec.Interp.jumpToBlock],
    file := "spec/lang/step/terminators.md", items := MiniRustSpec.Gen.Items.Lang.Step.Terminators.items,
    name := "impl_Machine__jump_to_block", line := 19,
    tokenSha256 := "25a223d317aa47ae05aadbc81218eed7a3b9fd8e9643dc30da924154f7486fe4" },
  { interp := [``MiniRustSpec.Interp.evalTerminator],
    file := "spec/lang/step/terminators.md", items := MiniRustSpec.Gen.Items.Lang.Step.Terminators.items,
    name := "impl_Machine__eval_terminator_1", line := 37,
    tokenSha256 := "d22ab9f6e83a163d3523fe5cb76ae4e849ebbf52845aed2717731772734da769" },
  { interp := [``MiniRustSpec.Interp.evalTerminator],
    file := "spec/lang/step/terminators.md", items := MiniRustSpec.Gen.Items.Lang.Step.Terminators.items,
    name := "impl_Machine__eval_terminator_2", line := 53,
    tokenSha256 := "7a0d575a3f8bed6666ad6523d1420f6a75e1582aef77ff706ada3ef84d132c57" },
  { interp := [``MiniRustSpec.Interp.evalReturn, ``MiniRustSpec.Interp.terminateActiveThread, ``MiniRustSpec.Interp.deallocAll],
    file := "spec/lang/step/terminators.md", items := MiniRustSpec.Gen.Items.Lang.Step.Terminators.items,
    name := "impl_Machine__terminate_active_thread", line := 298,
    tokenSha256 := "45319c0e710256385091ba8bcdf5b576c72c74bbb3dad46a6aae5a447c839a64" },
  { interp := [``MiniRustSpec.Interp.IntType.align],
    file := "spec/lang/types.md", items := MiniRustSpec.Gen.Items.Lang.Types.items,
    name := "impl_IntType__align", line := 138,
    tokenSha256 := "7fe63ee221d67adfee70c4048a1ec290c95d557d77cc0c8bbec2df68ce95041a" },
  { interp := [``MiniRustSpec.Interp.Type.layout],
    file := "spec/lang/types.md", items := MiniRustSpec.Gen.Items.Lang.Types.items,
    name := "impl_Type__layout", line := 148,
    tokenSha256 := "682e0cbfbea24b480557a76f0b8f41b2d286f604a8f6d0b26df81a02fa15cfcd" },
  { interp := [``MiniRustSpec.Interp.TupleHeadLayout.head_size_and_align],
    file := "spec/lang/types.md", items := MiniRustSpec.Gen.Items.Lang.Types.items,
    name := "impl_TupleHeadLayout__capped_tail_align", line := 200,
    tokenSha256 := "b4ae4d20f48c251605379a6d0cb0900922148640cc382899ca7c07957ae94c93" },
  { interp := [``MiniRustSpec.Interp.LayoutStrategy.expect_size, ``MiniRustSpec.Interp.LayoutStrategy.expect_align],
    file := "spec/lang/types.md", items := MiniRustSpec.Gen.Items.Lang.Types.items,
    name := "impl_LayoutStrategy__is_sized", line := 234,
    tokenSha256 := "e52080897bef565d064ef299545ac4985b3364e30fb6076be23e24827dbd9bd5" },
  { interp := [``MiniRustSpec.Interp.IntType.can_represent, ``MiniRustSpec.Interp.IntType.bring_in_bounds,
      ``MiniRustSpec.Interp.IntType.I8],
    file := "spec/lang/types.md", items := MiniRustSpec.Gen.Items.Lang.Types.items,
    name := "impl_IntType__I8", line := 295,
    tokenSha256 := "b0754c0840f7498f21559e09fe5421930c3eaccebff1f87a53ca8e6fc457db66" },
  { interp := [``MiniRustSpec.Interp.Allocation.size],
    file := "spec/mem/basic.md", items := MiniRustSpec.Gen.Items.Mem.Basic.items,
    name := "impl_Allocation__size", line := 66,
    tokenSha256 := "fe931d69e3e3f52a21a11a90aeec596314d94d5fddc0fdd775b8f000375b74d8" },
  { interp := [``MiniRustSpec.Interp.BM.deallocate],
    file := "spec/mem/basic.md", items := MiniRustSpec.Gen.Items.Mem.Basic.items,
    name := "impl_BasicMemory__allocate", line := 91,
    tokenSha256 := "7032eb855841319cd9c9d20afb80bdea2eebd06403d9762ec845116cfc138bf3" },
  { interp := [``MiniRustSpec.Interp.BM.check_ptr, ``MiniRustSpec.Interp.BM.store, ``MiniRustSpec.Interp.BM.load],
    file := "spec/mem/basic.md", items := MiniRustSpec.Gen.Items.Mem.Basic.items,
    name := "impl_BasicMemory__check_ptr", line := 193,
    tokenSha256 := "548843ba7ad0dd6a5ad1c78d66290bc78b80f59ed466ec7c000691e5cac53684" },
  { interp := [``MiniRustSpec.Interp.BM.store, ``MiniRustSpec.Interp.BM.load, ``MiniRustSpec.Interp.BM.deallocate],
    file := "spec/mem/basic.md", items := MiniRustSpec.Gen.Items.Mem.Basic.items,
    name := "impl_BasicMemory_for_Memory__Provenance", line := 305,
    tokenSha256 := "66210899d6f2cb4c3a8f649993b1e5bf4b8e983ffc6b6a5ce37fbd3305eb596a" },
  { interp := [``MiniRustSpec.Interp.CM.store, ``MiniRustSpec.Interp.CM.load, ``MiniRustSpec.Interp.CM.deallocate],
    file := "spec/mem/concurrent.md", items := MiniRustSpec.Gen.Items.Mem.Concurrent.items,
    name := "impl_ConcurrentMemory__new", line := 44,
    tokenSha256 := "3115f9afaf9bca67448e9dbcccda3080a4da794597864e8140dfeb68c26932c2" },
  { interp := [``MiniRustSpec.Interp.CM.check_data_races, ``MiniRustSpec.Interp.resetDataRaceTracking],
    file := "spec/mem/concurrent.md", items := MiniRustSpec.Gen.Items.Mem.Concurrent.items,
    name := "impl_ConcurrentMemory__check_data_races", line := 134,
    tokenSha256 := "4fd9af133b55d648e6cf0a1e4b226025c24815243741399853395c4d25b63937" },
  { interp := [``MiniRustSpec.Interp.Access.races],
    file := "spec/mem/concurrent.md", items := MiniRustSpec.Gen.Items.Mem.Concurrent.items,
    name := "impl_Access__races", line := 161,
    tokenSha256 := "e2a7dd884410223c7cc1841d4ebdd44571280d49e5e09c43d5437dae4ca1e644" },
  { interp := [``MiniRustSpec.Interp.AbstractByte.data],
    file := "spec/mem/interface.md", items := MiniRustSpec.Gen.Items.Mem.Interface.items,
    name := "impl_AbstractByte__data", line := 35,
    tokenSha256 := "d66c13f7b6681f5079ba957ec27f0e9319ec234f0791723026e2858a606376bb" },
  { interp := [``MiniRustSpec.Interp.x86_64.PTR_SIZE, ``MiniRustSpec.Interp.x86_64.INT_MAX_ALIGN, ``MiniRustSpec.Interp.x86_64.ENDIANNESS],
    file := "spec/prelude/target.md", items := MiniRustSpec.Gen.Items.Prelude.Target.items,
    name := "impl_x86_64_for_Target__PTR_SIZE", line := 35,
    tokenSha256 := "af4c702eb751ff89569e4676de009743cced5aaf60295c0964b8bf2567e7ef3d" }
]

theorem anchors_ok : anchors.all Anchor.ok = true := by decide

theorem anchors_nodup :
    decide ((anchors.map (fun a => (a.file, a.name, a.line))).Nodup) = true := by decide

end MiniRustSpec.Anchors
