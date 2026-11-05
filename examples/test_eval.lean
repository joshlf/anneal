import MiniRustSpec.Interp

open MiniRustSpec

def u8 : Gen.IntType := ⟨false, 1⟩

def optionU8Ty : Gen.Type :=
  .Enum
    ⟨[(0, { ty := .Tuple [] { «end» := ⟨2⟩, align := ⟨1⟩, packed_align := none } none,
            tagger := ⟨[(⟨0⟩, (u8, 0))]⟩ }),
      (1, { ty := .Tuple [(⟨1⟩, .Int u8)] { «end» := ⟨2⟩, align := ⟨1⟩, packed_align := none } none,
            tagger := ⟨[(⟨0⟩, (u8, 1))]⟩ })]⟩
    u8
    (.Branch ⟨0⟩ u8 .Invalid ⟨[((0, 0), .Known 0), ((1, 1), .Known 1)]⟩)
    ⟨2⟩
    ⟨1⟩

def res := Type.decode optionU8Ty [.Init 1 none, .Init 42 none]
#eval match res with | .ok v => "OK" | .error _ => "ERR"
