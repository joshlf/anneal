import LeanMiriSpec.Correspondence.Translate
import LeanMiriSpec.Correspondence.Relation

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open LeanMiriSpec.Correspondence

def isSigned (kind : RigidTy) : Bool :=
  match kind with
  | .int _ => true
  | _ => false

theorem evalBinOp_rel_simulation
    (op : MirAst.BinOp) (hop : op = .eq ∨ op = .ne ∨ op = .lt ∨ op = .le ∨ op = .gt ∨ op = .ge)
    {sc₁ sc₂ : MirAst.ScalarInt} {msc₁ msc₂ : Miri.Memory.ScalarInt}
    (hrel₁ : ScalarRel sc₁ msc₁) (hrel₂ : ScalarRel sc₂ msc₂)
    (locals : List LocalSlot) (mem : Memory)
    (ty : Ty) (hty : ty.kind = .bool ∨ (∃ k, ty.kind = .int k) ∨ (∃ k, ty.kind = .uint k))
    (hsz : sc₁.sizeBytes = sc₂.sizeBytes)
    (hsz_ty : sc₁.sizeBytes = match ty.kind with | .bool => 1 | _ => sc₁.sizeBytes)
    (hbits₁ : ty.kind = .bool → sc₁.bits = 0 ∨ sc₁.bits = 1)
    (hbits₂ : ty.kind = .bool → sc₂.bits = 0 ∨ sc₂.bits = 1)
    (mop : Miri.MIR.BinOp) (hmop : translateBinOp op = some mop) :
    ∃ b : Bool,
      evalScalarBinOp op sc₁ sc₂ locals mem (isSigned ty.kind) =
        .ok (.scalar (boolToScalar b)) locals mem ∧
      Miri.Interpreter.ScalarOps.binary (annealScalarOpsHooks []) () mop
        ⟨.scalar (.fromScalarInt msc₁), translateTy ty emptyLayoutTable⟩
        ⟨.scalar (.fromScalarInt msc₂), translateTy ty emptyLayoutTable⟩ =
        .ok ⟨.scalar (.fromScalarInt (Miri.Memory.ScalarInt.ofBool b)), translateTy { kind := .bool, layoutIdx := 0 } emptyLayoutTable⟩ := by
  have hbeq0 : sc₁.sizeBytes.beq 0 = false := by
    rcases hrel₁.validBytes with h|h|h|h|h <;> { rw [h]; rfl }
  have hbeq_eq : sc₁.sizeBytes.beq sc₂.sizeBytes = true := by
    rw [hsz, Nat.beq_refl]
  
  rcases ty with ⟨kind, idx⟩
  rcases hty with hbool | ⟨k, hint⟩ | ⟨k, huint⟩
  · subst hbool
    have hb1 := hbits₁ rfl; have hb2 := hbits₂ rfl
    have hmsz1 : msc₁.size = translateSizeBytes 1 := by rw [hrel₁.size_eq, hsz_ty]; rfl
    have hmsz2 : msc₂.size = translateSizeBytes 1 := by rw [hrel₂.size_eq, ← hsz, hsz_ty]; rfl
    have hmsc1 : ∃ b1 : Bool, msc₁ = Miri.Memory.ScalarInt.ofBool b1 ∧ sc₁ = boolToScalar b1 := by
      rcases hb1 with hb|hb
      · refine ⟨false, ?_, ?_⟩
        · cases msc₁; have hd := hrel₁.data_eq; dsimp at hd; rw [hb] at hd; dsimp at hmsz1; subst hd hmsz1; rfl
        · cases sc₁; dsimp at hsz_ty; subst hb hsz_ty; rfl
      · refine ⟨true, ?_, ?_⟩
        · cases msc₁; have hd := hrel₁.data_eq; dsimp at hd; rw [hb] at hd; dsimp at hmsz1; subst hd hmsz1; rfl
        · cases sc₁; dsimp at hsz_ty; subst hb hsz_ty; rfl
    have hmsc2 : ∃ b2 : Bool, msc₂ = Miri.Memory.ScalarInt.ofBool b2 ∧ sc₂ = boolToScalar b2 := by
      rcases hb2 with hb|hb
      · refine ⟨false, ?_, ?_⟩
        · cases msc₂; have hd := hrel₂.data_eq; dsimp at hd; rw [hb] at hd; dsimp at hmsz2; subst hd hmsz2; rfl
        · cases sc₂; have hsz2 : sc₂.sizeBytes = 1 := by rw [← hsz, hsz_ty]; subst hb hsz2; rfl
      · refine ⟨true, ?_, ?_⟩
        · cases msc₂; have hd := hrel₂.data_eq; dsimp at hd; rw [hb] at hd; dsimp at hmsz2; subst hd hmsz2; rfl
        · cases sc₂; have hsz2 : sc₂.sizeBytes = 1 := by rw [← hsz, hsz_ty]; subst hb hsz2; rfl
    
    rcases hmsc1 with ⟨b1, rfl, rfl⟩
    rcases hmsc2 with ⟨b2, rfl, rfl⟩
    rcases hop with rfl|rfl|rfl|rfl|rfl|rfl <;> (
      dsimp [evalScalarBinOp, translateBinOp, isSigned] at hmop ⊢
      injection hmop with hmop; subst hmop
      cases b1 <;> cases b2 <;> exact ⟨_, rfl⟩
    )
  · sorry
  · sorry
