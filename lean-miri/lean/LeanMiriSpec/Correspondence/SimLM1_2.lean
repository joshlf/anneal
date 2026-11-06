
import LeanMiriSpec.Correspondence.Translate
import LeanMiriSpec.Correspondence.Relation
import LeanMiriSpec.Correspondence.Simulation

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics

namespace LeanMiriSpec.Correspondence

theorem evalUnOp_bool_not_simulation
    {sc : MirAst.ScalarInt} {msc : Miri.Memory.ScalarInt}
    (hrel : ScalarRel sc msc) (locals : List LocalSlot) (mem : Memory)
    (ty : Ty) (hty : ty.kind = .bool) (hsz : sc.sizeBytes = 1)
    (hbits : sc.bits = 0 ∨ sc.bits = 1) :
    ∃ sc' msc',
      evalUnaryNot sc (some ty) locals mem = .ok (.scalar sc') locals mem ∧
      Miri.Interpreter.ScalarOps.unary (annealScalarOpsHooks []) () .Not
        ⟨.scalar (.fromScalarInt msc), translateTy ty emptyLayoutTable⟩ =
        .ok ⟨.scalar (.fromScalarInt msc'), translateTy ty emptyLayoutTable⟩ ∧
      ScalarRel sc' msc' := by
  have hb : ∃ b : Bool, sc = boolToScalar b ∧ msc = Miri.Memory.ScalarInt.ofBool b := by
    rcases sc with ⟨sc_bits, sc_size⟩
    rcases msc with ⟨msc_data, msc_size⟩
    have hsize := hrel.size_eq; have hdata := hrel.data_eq
    dsimp at hsz hsize hdata
    rcases hbits with h0 | h1
    · dsimp at h0; subst h0 hsz; dsimp [translateSizeBytes] at hsize
      subst hsize hdata; exact ⟨false, rfl, rfl⟩
    · dsimp at h1; subst h1 hsz; dsimp [translateSizeBytes] at hsize
      subst hsize hdata; exact ⟨true, rfl, rfl⟩
  rcases hb with ⟨b, rfl, rfl⟩
  refine ⟨boolToScalar (!b), Miri.Memory.ScalarInt.ofBool (!b), ?_⟩
  refine ⟨?_, ?_, ScalarRel.of_boolToScalar (!b)⟩
  · simp [evalUnaryNot, hty, boolToScalar]
    cases b <;> rfl
  · have he : encodeTyId ty = 1 := by
      rcases ty with ⟨kind, idx⟩
      cases kind <;> try contradiction
      rfl
    unfold Miri.Interpreter.ScalarOps.unary
    simp only [he, hty, annealScalarOpsHooks, classifyEncodedTyId, translateTy]
    cases b <;> rfl

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
    (hsz_ty : sc₁.sizeBytes = match ty.kind with | .bool => 1 | .int k => k.byteWidth 64 | .uint k => k.byteWidth 64 | _ => sc₁.sizeBytes)
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
  have hety : translateTy { kind := .bool, layoutIdx := 0 } emptyLayoutTable = { ty := 1, layout := scalarLayoutData 1 false 0 1 } := rfl
  rcases ty with ⟨kind, layoutIdx⟩
  rcases hty with rfl | ⟨k, rfl⟩ | ⟨k, rfl⟩
  · -- .bool case
    dsimp at hsz_ty
    have h1 := hbits₁ rfl
    have h2 := hbits₂ rfl
    have he : encodeTyId { kind := .bool, layoutIdx := layoutIdx } = 1 := rfl
    rcases sc₁ with ⟨b1, sz1⟩
    rcases sc₂ with ⟨b2, sz2⟩
    rcases msc₁ with ⟨d1, ms1⟩
    rcases msc₂ with ⟨d2, ms2⟩
    have hd1 := hrel₁.data_eq
    have hd2 := hrel₂.data_eq
    dsimp at hd1 hd2 hsz hsz_ty h1 h2
    subst hsz_ty
    subst hsz
    have hms1 := hrel₁.size_eq
    have hms2 := hrel₂.size_eq
    dsimp [translateSizeBytes] at hms1 hms2
    subst hms1 hms2
    rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl <;> (
      dsimp at hd1 hd2; subst hd1 hd2
      rcases hop with rfl | rfl | rfl | rfl | rfl | rfl <;> (
        injection hmop with hmop; subst hmop
        exact ⟨_, rfl, by
          funext m₂
          rw [scalarOps_binary_def]
          simp only [he, annealScalarOpsHooks, classifyEncodedTyId, translateTy, isSigned]
          rfl
        ⟩
      )
    )
  · -- .int case
    have hlhs : IsIntegralTy { kind := .int k, layoutIdx := layoutIdx } (translateIntTy k) := .int k rfl
    have hrhs : IsIntegralTy { kind := .int k, layoutIdx := layoutIdx } (translateIntTy k) := .int k rfl
    have hsz₁ : (translateTy { kind := .int k, layoutIdx := layoutIdx } emptyLayoutTable).layout.size = translateSizeBytes sc₁.sizeBytes := by
      rw [hsz_ty]; cases k <;> rfl
    have hsz₂ : (translateTy { kind := .int k, layoutIdx := layoutIdx } emptyLayoutTable).layout.size = translateSizeBytes sc₂.sizeBytes := by
      rw [←hsz, hsz_ty]; cases k <;> rfl
    rcases hop with h|h|h|h|h|h <;> (
      subst h; injection hmop with hmop; subst hmop
      have hbeq0 : sc₁.sizeBytes.beq 0 = false := hrel₁.beq_sizeBytes_zero
      have hbeq_eq : sc₁.sizeBytes.beq sc₂.sizeBytes = true := by rw [hsz, Nat.beq_refl]
      have hx_bits : sc₁.bits < 2 ^ (8 * sc₁.sizeBytes) := by
        have h := hrel₁.canonical; rw [scalarModulus_eq_two_pow] at h; exact h
      have hy_bits : sc₂.bits < 2 ^ (8 * sc₁.sizeBytes) := by
        have h := hrel₂.canonical; rw [scalarModulus_eq_two_pow, ←hsz] at h; exact h
      have hxMod : wrapScalarBits sc₁.bits (scalarModulus sc₁.sizeBytes) = sc₁.bits := hrel₁.wrapScalarBits_self
      have hyMod : wrapScalarBits sc₂.bits (scalarModulus sc₁.sizeBytes) = sc₂.bits := by rw [hsz]; exact hrel₂.wrapScalarBits_self
      simp only [evalScalarBinOp, hbeq0, hbeq_eq, isSigned, hxMod, hyMod]
    )
    · have hx := integerOps_binary_sameType_eq hrel₁ hrel₂ hsz (translateIntTy k) .Eq rfl
      have heq_b : (decodeBitsInt true sc₁.sizeBytes sc₁.bits == decodeBitsInt true sc₁.sizeBytes sc₂.bits) = Nat.beq sc₁.bits sc₂.bits := by
        rw [nat_beq_eq_decide]; apply Bool.eq_iff_iff.mpr; simp only [beq_iff_eq, decide_eq_true_eq]; exact decodeBitsInt_inj hrel₁.validBytes hx_bits hy_bits
      exact ⟨_, rfl, by funext m₂; have hm := scalarOps_binary_integer_step [] hlhs hrhs hrel₁ hrel₂ hsz₁ hsz₂ (Or.inr rfl) m₂; rw [hm]; dsimp [scalarOpsFinish, liftScalarResult, Except.mapError]; rw [hx]; dsimp; rw [heq_b]; rfl⟩
    · have hx := integerOps_binary_sameType_eq hrel₁ hrel₂ hsz (translateIntTy k) .Ne rfl
      have hne_b : (decodeBitsInt true sc₁.sizeBytes sc₁.bits != decodeBitsInt true sc₁.sizeBytes sc₂.bits) = !Nat.beq sc₁.bits sc₂.bits := by
        rw [nat_beq_eq_decide]; apply Bool.eq_iff_iff.mpr; simp only [bne_iff_ne, Ne, Bool.not_eq_true', decide_eq_false_iff_not]; exact not_congr (decodeBitsInt_inj hrel₁.validBytes hx_bits hy_bits)
      exact ⟨_, rfl, by funext m₂; have hm := scalarOps_binary_integer_step [] hlhs hrhs hrel₁ hrel₂ hsz₁ hsz₂ (Or.inr rfl) m₂; rw [hm]; dsimp [scalarOpsFinish, liftScalarResult, Except.mapError]; rw [hx]; dsimp; rw [hne_b]; rfl⟩
    · have hx := integerOps_binary_sameType_eq hrel₁ hrel₂ hsz (translateIntTy k) .Lt rfl
      have hlt_b : (decodeBitsInt true sc₁.sizeBytes sc₁.bits < decodeBitsInt true sc₁.sizeBytes sc₂.bits) = signedLt sc₁.bits sc₂.bits sc₁.sizeBytes := by rw [nat_blt_eq_decide]; sorry
      exact ⟨_, rfl, by funext m₂; have hm := scalarOps_binary_integer_step [] hlhs hrhs hrel₁ hrel₂ hsz₁ hsz₂ (Or.inr rfl) m₂; rw [hm]; dsimp [scalarOpsFinish, liftScalarResult, Except.mapError]; rw [hx]; dsimp; sorry⟩
    · sorry
    · sorry
    · sorry
  · -- .uint case
    sorry
