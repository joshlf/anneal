/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.

GENERATED FILE -- DO NOT EDIT. Regenerate with
`cargo run -p anneal-minirust-gen -- generate`.

Deep (syntax) embedding of every top-level item of upstream MiniRust
`spec/prelude/main.md` (commit `d821c6e3`), one Lean definition per item, in source order.
-/

import MiniRustSpec.Meta.Syntax

set_option maxRecDepth 100000

namespace MiniRustSpec.Gen.Items.Prelude.Main

open MiniRustSpec.Syntax

/-- Path of the upstream file these items were extracted from. -/
def sourceFile : String := "spec/prelude/main.md"

/-- SHA-256 of the upstream file. -/
def sourceSha256 : String := "b031f4b168ca826e0713b840415cb69d076299b01d4588fc92cfe89452d18262"

/-- `spec/prelude/main.md:6` -/
def use_0 : Item :=
  (Item.use
    [
      (Attr.mk
        true
        "doc"
        (AttrMeta.nameValue
          " Documentation for libspecr can be found here: https://docs.rs/libspecr"))]
    Visibility.pub
    false
    (UseTree.path "libspecr" (UseTree.path "prelude" UseTree.glob)))

/-- `spec/prelude/main.md:9` -/
def use_1 : Item :=
  (Item.use
    [(Attr.mk true "doc" (AttrMeta.nameValue " Make the two main modules available."))]
    Visibility.pub
    false
    (UseTree.path "crate" (UseTree.group [(UseTree.name "lang"), (UseTree.name "mem")])))

/-- `spec/prelude/main.md:12` -/
def type_Offset : Item :=
  (Item.type
    [
      (Attr.mk
        true
        "doc"
        (AttrMeta.nameValue
          " When a non-negative integer is used as an offset into an allocation or type")),
      (Attr.mk
        true
        "doc"
        (AttrMeta.nameValue
          " rather than to describe the size of an object or type, use this type instead")),
      (Attr.mk true "doc" (AttrMeta.nameValue " of `Size` for extra clarity."))]
    Visibility.pub
    "Offset"
    (Generics.mk [] [])
    (Ty.path none (Path.mk false [(PathSegment.mk "Size" PathArguments.none)])))

/-- `spec/prelude/main.md:17` -/
def type_Result : Item :=
  (Item.type
    [
      (Attr.mk
        true
        "doc"
        (AttrMeta.nameValue
          " All operations are fallible, so they return `Result`.  If they fail, that")),
      (Attr.mk
        true
        "doc"
        (AttrMeta.nameValue " means the program caused UB or put the machine to a halt."))]
    Visibility.pub
    "Result"
    (Generics.mk [(GenericParam.type [] "T" [] (some (Ty.tuple [])))] [])
    (Ty.path
      none
      (Path.mk
        false
        [
          (PathSegment.mk "std" PathArguments.none),
          (PathSegment.mk "result" PathArguments.none),
          (PathSegment.mk
            "Result"
            (PathArguments.angleBracketed
              false
              [
                (GenericArgument.type
                  (Ty.path none (Path.mk false [(PathSegment.mk "T" PathArguments.none)]))),
                (GenericArgument.type
                  (Ty.path
                    none
                    (Path.mk false [(PathSegment.mk "TerminationInfo" PathArguments.none)])))]))])))

/-- `spec/prelude/main.md:21` -/
def enum_TerminationInfo : Item :=
  (Item.enum
    []
    Visibility.pub
    "TerminationInfo"
    (Generics.mk [] [])
    [
      (Variant.mk
        [
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue " The execution encountered undefined behaviour."))]
        "Ub"
        (Fields.unnamed
          [
            (Field.mk
              []
              Visibility.inherited
              none
              (Ty.path none (Path.mk false [(PathSegment.mk "String" PathArguments.none)])))])
        none),
      (Variant.mk
        [
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue " The program was executed and the machine stopped without error."))]
        "MachineStop"
        Fields.unit
        none),
      (Variant.mk
        [(Attr.mk true "doc" (AttrMeta.nameValue " The program terminated with a panic"))]
        "Abort"
        Fields.unit
        none),
      (Variant.mk
        [(Attr.mk true "doc" (AttrMeta.nameValue " The program was ill-formed."))]
        "IllFormed"
        (Fields.unnamed
          [
            (Field.mk
              []
              Visibility.inherited
              none
              (Ty.path none (Path.mk false [(PathSegment.mk "String" PathArguments.none)])))])
        none),
      (Variant.mk
        [
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue " The program did not terminate but no thread can make progress."))]
        "Deadlock"
        Fields.unit
        none),
      (Variant.mk
        [
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue " The program terminated successfully but memory was leaked."))]
        "MemoryLeak"
        Fields.unit
        none)])

/-- `spec/prelude/main.md:36` -/
def macro_rules_throw : Item :=
  (Item.macro
    [
      (Attr.mk
        true
        "doc"
        (AttrMeta.nameValue " Some macros for convenient yeeting, i.e., return an error from a")),
      (Attr.mk true "doc" (AttrMeta.nameValue " `Option`/`Result`-returning function."))]
    (some "throw")
    (Macro.mk
      (Path.mk false [(PathSegment.mk "macro_rules" PathArguments.none)])
      MacroDelimiter.brace
      (MacroBody.tokens "($ ($ tt : tt) *) => { do yeet () } ;")))

/-- `spec/prelude/main.md:43` -/
def macro_rules_throw_ub : Item :=
  (Item.macro
    []
    (some "throw_ub")
    (Macro.mk
      (Path.mk false [(PathSegment.mk "macro_rules" PathArguments.none)])
      MacroDelimiter.brace
      (MacroBody.tokens
        "($ ($ tt : tt) *) => { do yeet TerminationInfo :: Ub (format ! ($ ($ tt) *)) } ;")))

/-- `spec/prelude/main.md:48` -/
def macro_rules_throw_abort : Item :=
  (Item.macro
    []
    (some "throw_abort")
    (Macro.mk
      (Path.mk false [(PathSegment.mk "macro_rules" PathArguments.none)])
      MacroDelimiter.brace
      (MacroBody.tokens "() => { do yeet TerminationInfo :: Abort }")))

/-- `spec/prelude/main.md:53` -/
def macro_rules_throw_machine_stop : Item :=
  (Item.macro
    []
    (some "throw_machine_stop")
    (Macro.mk
      (Path.mk false [(PathSegment.mk "macro_rules" PathArguments.none)])
      MacroDelimiter.brace
      (MacroBody.tokens "() => { do yeet TerminationInfo :: MachineStop } ;")))

/-- `spec/prelude/main.md:58` -/
def macro_rules_throw_memory_leak : Item :=
  (Item.macro
    []
    (some "throw_memory_leak")
    (Macro.mk
      (Path.mk false [(PathSegment.mk "macro_rules" PathArguments.none)])
      MacroDelimiter.brace
      (MacroBody.tokens "() => { do yeet TerminationInfo :: MemoryLeak } ;")))

/-- `spec/prelude/main.md:64` -/
def macro_rules_throw_ill_formed : Item :=
  (Item.macro
    []
    (some "throw_ill_formed")
    (Macro.mk
      (Path.mk false [(PathSegment.mk "macro_rules" PathArguments.none)])
      MacroDelimiter.brace
      (MacroBody.tokens
        "($ ($ tt : tt) *) => { do yeet TerminationInfo :: IllFormed (format ! ($ ($ tt) *)) } ;")))

/-- `spec/prelude/main.md:70` -/
def macro_rules_throw_deadlock : Item :=
  (Item.macro
    []
    (some "throw_deadlock")
    (Macro.mk
      (Path.mk false [(PathSegment.mk "macro_rules" PathArguments.none)])
      MacroDelimiter.brace
      (MacroBody.tokens "() => { do yeet TerminationInfo :: Deadlock } ;")))

/-- `spec/prelude/main.md:76` -/
def use_2 : Item :=
  (Item.use
    [
      (Attr.mk
        true
        "doc"
        (AttrMeta.nameValue " We leave the encoding of the non-determinism monad opaque."))]
    Visibility.pub
    false
    (UseTree.path "libspecr" (UseTree.name "Nondet")))

/-- `spec/prelude/main.md:78` -/
def type_NdResult : Item :=
  (Item.type
    []
    Visibility.pub
    "NdResult"
    (Generics.mk [(GenericParam.type [] "T" [] (some (Ty.tuple [])))] [])
    (Ty.path
      none
      (Path.mk
        false
        [
          (PathSegment.mk "libspecr" PathArguments.none),
          (PathSegment.mk
            "NdResult"
            (PathArguments.angleBracketed
              false
              [
                (GenericArgument.type
                  (Ty.path none (Path.mk false [(PathSegment.mk "T" PathArguments.none)]))),
                (GenericArgument.type
                  (Ty.path
                    none
                    (Path.mk false [(PathSegment.mk "TerminationInfo" PathArguments.none)])))]))])))

/-- All items of `spec/prelude/main.md`, in source order, with provenance. -/
def items : List SourceItem :=
  [
    (SourceItem.mk
      "use_0"
      6
      "397e2a505f6566de6d84c431acbf6559e927b241ea97e710b0eb17bb8704ab92"
      use_0),
    (SourceItem.mk
      "use_1"
      9
      "3d991770b55fcbafb1684c61494a313c0d2d233cb4fc2695fbb21af473360099"
      use_1),
    (SourceItem.mk
      "type_Offset"
      12
      "8be63a0847ed8cd5d21b1024df07a6178a91e6965ae3d04d43b53b2c7a63f9aa"
      type_Offset),
    (SourceItem.mk
      "type_Result"
      17
      "a812d2bc18acc499acde8229a591f0c7a20f41239ac9cc84747b42e33cb52494"
      type_Result),
    (SourceItem.mk
      "enum_TerminationInfo"
      21
      "a2c74b4a6bb420ebf5ac21643b8f7ee0785a5a0d067df99e95752857839bf095"
      enum_TerminationInfo),
    (SourceItem.mk
      "macro_rules_throw"
      36
      "5af8bb909ad2532705e33f45caf6301fdfe365b76abc9483839e32c1cea6c04a"
      macro_rules_throw),
    (SourceItem.mk
      "macro_rules_throw_ub"
      43
      "fffb378afdf92b57ca3f573de292e5dee09eb985863c612ca3b9b9d37c3556fa"
      macro_rules_throw_ub),
    (SourceItem.mk
      "macro_rules_throw_abort"
      48
      "f3d25c4e0151410cffd06fc81e3f23a083cd1f581249a6bc436e53052a132ec6"
      macro_rules_throw_abort),
    (SourceItem.mk
      "macro_rules_throw_machine_stop"
      53
      "bdfb632763b258001f907c917efd8a75aec84ba4b360d24bde816d33e9728c59"
      macro_rules_throw_machine_stop),
    (SourceItem.mk
      "macro_rules_throw_memory_leak"
      58
      "e17e3fd080999bbde34565984f414643765dc083c196f391d85b9a563c2aef51"
      macro_rules_throw_memory_leak),
    (SourceItem.mk
      "macro_rules_throw_ill_formed"
      64
      "0c0c45018186f1b243a80f34340ec6fd6b016564d0862d2203022029bc6d7d91"
      macro_rules_throw_ill_formed),
    (SourceItem.mk
      "macro_rules_throw_deadlock"
      70
      "a6c7c7934e24b73d6449518d0249495520d0ecd4bfd57950f17aaa9e80b0cd1f"
      macro_rules_throw_deadlock),
    (SourceItem.mk
      "use_2"
      76
      "45f21d778ffac5a0da685afc75706e92e1a6f6c2a37e2ceb6195bf528f4076a7"
      use_2),
    (SourceItem.mk
      "type_NdResult"
      78
      "d444e44209df7d638b899b368872ac9da4398a52b6eb82e362580a28f9171a77"
      type_NdResult)]

end MiniRustSpec.Gen.Items.Prelude.Main
