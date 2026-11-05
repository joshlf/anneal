import MiniRustSpec.Correspondence.Witness

open MiniRustSpec Gen LibSpecr

def optionU8Ty : Gen.Type :=
  .Enum
    ⟨[(0, { ty := .Tuple [] { «end» := ⟨0⟩, align := ⟨1⟩, packed_align := none } none,
            tagger := ⟨[(⟨0⟩, (u8, 0))]⟩ }),
      (1, { ty := .Tuple [(⟨1⟩, .Int u8)] { «end» := ⟨2⟩, align := ⟨1⟩, packed_align := none } none,
            tagger := ⟨[(⟨0⟩, (u8, 1))]⟩ })]⟩
    u8
    (.Branch ⟨0⟩ u8 .Invalid ⟨[((0, 0), .Known 0), ((1, 1), .Known 1)]⟩)
    ⟨2⟩
    ⟨1⟩

theorem option_u8_encode_decode :
    Type.layout optionU8Ty = .ok (.Sized ⟨2⟩ ⟨1⟩) ∧
    Type.encode optionU8Ty (.Variant 0 (.Tuple [])) = .ok [.Init 0 none, .Uninit] ∧
    Type.encode optionU8Ty (.Variant 1 (.Tuple [(⟨1⟩, .Int 42)])) = .ok [.Init 1 none, .Init 42 none] ∧
    Type.decode optionU8Ty [.Init 0 none, .Init 99 none] = .ok (some (.Variant 0 (.Tuple []))) ∧
    Type.decode optionU8Ty [.Init 1 none, .Init 42 none] = .ok (some (.Variant 1 (.Tuple [(⟨1⟩, .Int 42)]))) ∧
    checkValue (.Variant 1 (.Tuple [(⟨1⟩, .Int 42)])) optionU8Ty = .ok () ∧
    Interp.evalPlace nestedTupleOkMInit (.Downcast (.Local (localName 2)) 1) =
      .error (.specPanic "downcast on non-projectable type") :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
