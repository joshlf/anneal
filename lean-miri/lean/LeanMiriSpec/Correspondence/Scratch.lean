import LeanMiriSpec.Correspondence.SimLM3_2
import Lean

open Miri.Memory
open Lean Elab Tactic Meta

elab "unfold_private_collect" : tactic => do
  let env ← getEnv
  let some name1 := env.constants.map₁.toList.map (·.1)
    |>.find? (fun n => (toString n).drop ((toString n).length - 16) == "collectChunksAux")
    | throwError "Not found 1"
  let some name2 := env.constants.map₁.toList.map (·.1)
    |>.find? (fun n => (toString n).drop ((toString n).length - 23) == "collectChunksAux._unary")
    | throwError "Not found 2"
  evalTactic (← `(tactic| delta $(mkIdent name1)))
  evalTactic (← `(tactic| delta $(mkIdent name2)))

theorem test_unroll (off n : Nat) (hnot_oob : ¬ (UInt64.ofNat (off + 1) > (Miri.ABI.Size.ofBytes 1000).bytes))
  (hnot_gt : ¬ (UInt64.ofNat off > UInt64.ofNat (off + 1))) :
    InitMask.collectChunks {
      initMask := InitMask.new (Miri.ABI.Size.ofBytes 1000) false,
      isInit := false,
      start := ⟨UInt64.ofNat off⟩,
      finish := ⟨UInt64.ofNat (off + 1)⟩
    } = .ok #[InitChunk.Uninit ⟨UInt64.ofNat off⟩ ⟨UInt64.ofNat (off + 1)⟩] := by
  unfold InitMask.collectChunks
  have hfuel : (UInt64.ofNat (off + 1)).toNat - (UInt64.ofNat off).toNat + 1 = 2 := sorry
  erw [hfuel]
  unfold_private_collect
  rw [WellFounded.Nat.fix_eq]
  dsimp only [bind, Except.bind, pure, Except.pure]
  have hiter0 : (Miri.Memory.InitChunkIter.mk
      (Miri.Memory.InitMask.new (Miri.ABI.Size.ofBytes 1000) false) false
      ⟨UInt64.ofNat off⟩ ⟨UInt64.ofNat (off + 1)⟩).next? = .ok (some (.Uninit ⟨UInt64.ofNat off⟩ ⟨UInt64.ofNat (off + 1)⟩, ⟨Miri.Memory.InitMask.new (Miri.ABI.Size.ofBytes 1000) false, true, ⟨UInt64.ofNat (off + 1)⟩, ⟨UInt64.ofNat (off + 1)⟩⟩)) := sorry
  erw [hiter0]
  dsimp only [bind, Except.bind, pure, Except.pure]
  rw [WellFounded.Nat.fix_eq]
  dsimp only [bind, Except.bind, pure, Except.pure]
  have hiter1 : (Miri.Memory.InitChunkIter.mk
      (Miri.Memory.InitMask.new (Miri.ABI.Size.ofBytes 1000) false) true
      ⟨UInt64.ofNat (off + 1)⟩ ⟨UInt64.ofNat (off + 1)⟩).next? = .ok none := sorry
  erw [hiter1]
  dsimp only [bind, Except.bind, pure, Except.pure, Array.append]
  rfl
