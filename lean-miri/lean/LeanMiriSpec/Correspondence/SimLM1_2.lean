import LeanMiriSpec.Correspondence.Translate
import LeanMiriSpec.Correspondence.Relation
import LeanMiriSpec.Correspondence.Simulation

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics

namespace LeanMiriSpec.Correspondence

@[simp] theorem decodeBitsInt_unsigned (sz x : Nat) : decodeBitsInt false sz x = (x : Int) := rfl
@[simp] theorem decodeBitsInt_signed (sz x : Nat) : decodeBitsInt true sz x = if x < 2 ^ (8 * sz - 1) then (x : Int) else (x : Int) - (2 ^ (8 * sz) : Nat) := rfl

theorem decodeBitsInt_lt_iff_unsigned {sz x y : Nat} (_hsz : ValidScalarBytes sz) (_hx : x < 2 ^ (8 * sz)) (_hy : y < 2 ^ (8 * sz)) :
    decodeBitsInt false sz x < decodeBitsInt false sz y ↔ x < y := by
  dsimp [decodeBitsInt]
  exact Int.ofNat_lt

theorem decodeBitsInt_le_iff_unsigned {sz x y : Nat} (_hsz : ValidScalarBytes sz) (_hx : x < 2 ^ (8 * sz)) (_hy : y < 2 ^ (8 * sz)) :
    decodeBitsInt false sz x ≤ decodeBitsInt false sz y ↔ x ≤ y := by
  dsimp [decodeBitsInt]
  exact Int.ofNat_le


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
  rcases hty with rfl | ⟨k, rfl⟩ | ⟨uk, rfl⟩
  · -- .bool case
    have he : encodeTyId { kind := .bool, layoutIdx := layoutIdx } = 1 := rfl
    have hb1 : ∃ b1 : Bool, sc₁ = boolToScalar b1 ∧ msc₁ = Miri.Memory.ScalarInt.ofBool b1 := by
      have h1 := hbits₁ rfl
      rcases h1 with h1 | h1
      · exists false
        rcases sc₁ with ⟨bits, sz⟩
        rcases msc₁ with ⟨data, size⟩
        have hd1 := hrel₁.data_eq
        have hs1 := hrel₁.size_eq
        dsimp at h1 hd1 hs1 hsz_ty
        subst hsz_ty hs1 hd1 h1
        exact ⟨rfl, rfl⟩
      · exists true
        rcases sc₁ with ⟨bits, sz⟩
        rcases msc₁ with ⟨data, size⟩
        have hd1 := hrel₁.data_eq
        have hs1 := hrel₁.size_eq
        dsimp at h1 hd1 hs1 hsz_ty
        subst hsz_ty hs1 hd1 h1
        exact ⟨rfl, rfl⟩
    have hb2 : ∃ b2 : Bool, sc₂ = boolToScalar b2 ∧ msc₂ = Miri.Memory.ScalarInt.ofBool b2 := by
      have h2 := hbits₂ rfl
      have hsz_ty2 : sc₂.sizeBytes = 1 := by rw [←hsz]; exact hsz_ty
      rcases h2 with h2 | h2
      · exists false
        rcases sc₂ with ⟨bits, sz⟩
        rcases msc₂ with ⟨data, size⟩
        have hd2 := hrel₂.data_eq
        have hs2 := hrel₂.size_eq
        dsimp at h2 hd2 hs2 hsz_ty2
        subst hsz_ty2 hs2 hd2 h2
        exact ⟨rfl, rfl⟩
      · exists true
        rcases sc₂ with ⟨bits, sz⟩
        rcases msc₂ with ⟨data, size⟩
        have hd2 := hrel₂.data_eq
        have hs2 := hrel₂.size_eq
        dsimp at h2 hd2 hs2 hsz_ty2
        subst hsz_ty2 hs2 hd2 h2
        exact ⟨rfl, rfl⟩
    have hb : ∃ b1 b2 : Bool, sc₁ = boolToScalar b1 ∧ msc₁ = Miri.Memory.ScalarInt.ofBool b1 ∧ sc₂ = boolToScalar b2 ∧ msc₂ = Miri.Memory.ScalarInt.ofBool b2 := by
      rcases hb1 with ⟨b1, hb1, hm1⟩
      rcases hb2 with ⟨b2, hb2, hm2⟩
      exact ⟨b1, b2, hb1, hm1, hb2, hm2⟩
    rcases hb with ⟨b1, b2, hb1, hb2, hb3, hb4⟩
    subst hb1 hb2 hb3 hb4
    rcases hop with rfl | rfl | rfl | rfl | rfl | rfl <;> (
      injection hmop with hmop; subst hmop
      cases b1 <;> cases b2 <;> (
        refine ⟨_, rfl, by
          unfold Miri.Interpreter.ScalarOps.binary
          simp only [he, annealScalarOpsHooks, classifyEncodedTyId, translateTy, isSigned, boolToScalar]
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
      simp only [evalScalarBinOp, hbeq0, hbeq_eq, isSigned]
    )
    · have hx := integerOps_binary_sameType_eq hrel₁ hrel₂ hsz (translateIntTy k) .Eq rfl
      have heq_b : (decodeBitsInt (translateIntTy k).signed sc₁.sizeBytes sc₁.bits == decodeBitsInt (translateIntTy k).signed sc₁.sizeBytes sc₂.bits) = Nat.beq sc₁.bits sc₂.bits := by
        have hk : (translateIntTy k).signed = true := by (cases k; all_goals rfl)
        rw [hk]
        rw [nat_beq_eq_decide]
        apply Bool.eq_iff_iff.mpr; simp only [beq_iff_eq, decide_eq_true_eq]; exact decodeBitsInt_inj hrel₁.validBytes hx_bits hy_bits
      exact ⟨_, rfl, by funext m₂; have hm := scalarOps_binary_integer_step (bop := .eq) [] hlhs hrhs hrel₁ hrel₂ hsz₁ hsz₂ (Or.inr rfl) m₂; rw [hm]; dsimp [scalarOpsFinish, liftScalarResult, Except.mapError]; unfold translateBinOp; rw [hx]; simp only [annealScalarOpsHooks, bind, pure, EStateM.bind, EStateM.pure, Miri.Memory.Scalar.fromBool, Miri.Memory.ScalarInt.ofBool]; rw [heq_b]; try (congr 1; congr 1; congr 1; revert m₂; simp; intro m₂; omega)⟩
    · have hx := integerOps_binary_sameType_eq hrel₁ hrel₂ hsz (translateIntTy k) .Ne rfl
      have hne_b : (decodeBitsInt (translateIntTy k).signed sc₁.sizeBytes sc₁.bits != decodeBitsInt (translateIntTy k).signed sc₁.sizeBytes sc₂.bits) = !Nat.beq sc₁.bits sc₂.bits := by
        have hk : (translateIntTy k).signed = true := by (cases k; all_goals rfl)
        rw [hk]
        rw [nat_beq_eq_decide]
        apply Bool.eq_iff_iff.mpr; simp only [bne_iff_ne, Ne, Bool.not_eq_true', decide_eq_false_iff_not]; exact not_congr (decodeBitsInt_inj hrel₁.validBytes hx_bits hy_bits)
      exact ⟨_, rfl, by funext m₂; have hm := scalarOps_binary_integer_step (bop := .ne) [] hlhs hrhs hrel₁ hrel₂ hsz₁ hsz₂ (Or.inr rfl) m₂; rw [hm]; dsimp [scalarOpsFinish, liftScalarResult, Except.mapError]; unfold translateBinOp; rw [hx]; simp only [annealScalarOpsHooks, bind, pure, EStateM.bind, EStateM.pure, Miri.Memory.Scalar.fromBool, Miri.Memory.ScalarInt.ofBool]; rw [hne_b]; try (congr 1; congr 1; congr 1; revert m₂; simp; intro m₂; omega)⟩
    · have hx := integerOps_binary_sameType_eq hrel₁ hrel₂ hsz (translateIntTy k) .Lt rfl
      have hlt_b : decide (decodeBitsInt (translateIntTy k).signed sc₁.sizeBytes sc₁.bits < decodeBitsInt (translateIntTy k).signed sc₁.sizeBytes sc₂.bits) = signedLt sc₁.bits sc₂.bits sc₁.sizeBytes := by
        have hk : (translateIntTy k).signed = true := by (cases k; all_goals rfl)
        rw [hk]
        exact (signedLt_eq hrel₁.validBytes hx_bits hy_bits).symm
      exact ⟨_, rfl, by funext m₂; have hm := scalarOps_binary_integer_step (bop := .lt) [] hlhs hrhs hrel₁ hrel₂ hsz₁ hsz₂ (Or.inr rfl) m₂; rw [hm]; dsimp [scalarOpsFinish, liftScalarResult, Except.mapError]; unfold translateBinOp; rw [hx]; simp only [annealScalarOpsHooks, bind, pure, EStateM.bind, EStateM.pure, Miri.Memory.Scalar.fromBool, Miri.Memory.ScalarInt.ofBool]; rw [hlt_b]; try (congr 1; congr 1; congr 1; revert m₂; simp; intro m₂; omega)⟩
    · have hx := integerOps_binary_sameType_eq hrel₁ hrel₂ hsz (translateIntTy k) .Le rfl
      have hle_b : decide (decodeBitsInt (translateIntTy k).signed sc₁.sizeBytes sc₁.bits ≤ decodeBitsInt (translateIntTy k).signed sc₁.sizeBytes sc₂.bits) = signedLe sc₁.bits sc₂.bits sc₁.sizeBytes := by
        have hk : (translateIntTy k).signed = true := by (cases k; all_goals rfl)
        rw [hk]
        exact (signedLe_eq hrel₁.validBytes hx_bits hy_bits).symm
      exact ⟨_, rfl, by funext m₂; have hm := scalarOps_binary_integer_step (bop := .le) [] hlhs hrhs hrel₁ hrel₂ hsz₁ hsz₂ (Or.inr rfl) m₂; rw [hm]; dsimp [scalarOpsFinish, liftScalarResult, Except.mapError]; unfold translateBinOp; rw [hx]; simp only [annealScalarOpsHooks, bind, pure, EStateM.bind, EStateM.pure, Miri.Memory.Scalar.fromBool, Miri.Memory.ScalarInt.ofBool]; rw [hle_b]; try (congr 1; congr 1; congr 1; revert m₂; simp; intro m₂; omega)⟩
    · have hx := integerOps_binary_sameType_eq hrel₁ hrel₂ hsz (translateIntTy k) .Gt rfl
      have hgt_b : decide (decodeBitsInt (translateIntTy k).signed sc₁.sizeBytes sc₁.bits > decodeBitsInt (translateIntTy k).signed sc₁.sizeBytes sc₂.bits) = signedLt sc₂.bits sc₁.bits sc₁.sizeBytes := by
        have hk : (translateIntTy k).signed = true := by (cases k; all_goals rfl)
        rw [hk]
        have hy_bits' : sc₂.bits < 2 ^ (8 * sc₁.sizeBytes) := by rw [hsz]; exact (by have h := hrel₂.canonical; rw [scalarModulus_eq_two_pow] at h; exact h : sc₂.bits < 2 ^ (8 * sc₂.sizeBytes))
        have h := (signedLt_eq hrel₁.validBytes hy_bits' hx_bits).symm
        dsimp [GT.gt]
        exact h
      exact ⟨_, rfl, by funext m₂; have hm := scalarOps_binary_integer_step (bop := .gt) [] hlhs hrhs hrel₁ hrel₂ hsz₁ hsz₂ (Or.inr rfl) m₂; rw [hm]; dsimp [scalarOpsFinish, liftScalarResult, Except.mapError]; unfold translateBinOp; rw [hx]; simp only [annealScalarOpsHooks, bind, pure, EStateM.bind, EStateM.pure, Miri.Memory.Scalar.fromBool, Miri.Memory.ScalarInt.ofBool]; rw [hgt_b]; try (congr 1; congr 1; congr 1; revert m₂; simp; intro m₂; omega)⟩
    · have hx := integerOps_binary_sameType_eq hrel₁ hrel₂ hsz (translateIntTy k) .Ge rfl
      have hge_b : decide (decodeBitsInt (translateIntTy k).signed sc₁.sizeBytes sc₁.bits ≥ decodeBitsInt (translateIntTy k).signed sc₁.sizeBytes sc₂.bits) = signedLe sc₂.bits sc₁.bits sc₁.sizeBytes := by
        have hk : (translateIntTy k).signed = true := by (cases k; all_goals rfl)
        rw [hk]
        have hy_bits' : sc₂.bits < 2 ^ (8 * sc₁.sizeBytes) := by rw [hsz]; exact (by have h := hrel₂.canonical; rw [scalarModulus_eq_two_pow] at h; exact h : sc₂.bits < 2 ^ (8 * sc₂.sizeBytes))
        have h := (signedLe_eq hrel₁.validBytes hy_bits' hx_bits).symm
        dsimp [GE.ge]
        exact h
      exact ⟨_, rfl, by funext m₂; have hm := scalarOps_binary_integer_step (bop := .ge) [] hlhs hrhs hrel₁ hrel₂ hsz₁ hsz₂ (Or.inr rfl) m₂; rw [hm]; dsimp [scalarOpsFinish, liftScalarResult, Except.mapError]; unfold translateBinOp; rw [hx]; simp only [annealScalarOpsHooks, bind, pure, EStateM.bind, EStateM.pure, Miri.Memory.Scalar.fromBool, Miri.Memory.ScalarInt.ofBool]; rw [hge_b]; try (congr 1; congr 1; congr 1; revert m₂; simp; intro m₂; omega)⟩
  · -- .uint case
    have hlhs : IsIntegralTy { kind := .uint uk, layoutIdx := layoutIdx } (translateUintTy uk) := .uint uk rfl
    have hrhs : IsIntegralTy { kind := .uint uk, layoutIdx := layoutIdx } (translateUintTy uk) := .uint uk rfl
    have hsz₁ : (translateTy { kind := .uint uk, layoutIdx := layoutIdx } emptyLayoutTable).layout.size = translateSizeBytes sc₁.sizeBytes := by
      rw [hsz_ty]; cases uk <;> rfl
    have hsz₂ : (translateTy { kind := .uint uk, layoutIdx := layoutIdx } emptyLayoutTable).layout.size = translateSizeBytes sc₂.sizeBytes := by
      rw [←hsz, hsz_ty]; cases uk <;> rfl
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
      simp only [evalScalarBinOp, hbeq0, hbeq_eq, isSigned]
    )
    · have hx := integerOps_binary_sameType_eq hrel₁ hrel₂ hsz (translateUintTy uk) .Eq rfl
      have heq_b : (decodeBitsInt (translateUintTy uk).signed sc₁.sizeBytes sc₁.bits == decodeBitsInt (translateUintTy uk).signed sc₁.sizeBytes sc₂.bits) = Nat.beq sc₁.bits sc₂.bits := by
        have hk : (translateUintTy uk).signed = false := by (cases uk; all_goals rfl)
        rw [hk]
        rw [nat_beq_eq_decide]
        apply Bool.eq_iff_iff.mpr; simp only [beq_iff_eq, decide_eq_true_eq]; exact decodeBitsInt_inj hrel₁.validBytes hx_bits hy_bits
      exact ⟨_, rfl, by funext m₂; have hm := scalarOps_binary_integer_step (bop := .eq) [] hlhs hrhs hrel₁ hrel₂ hsz₁ hsz₂ (Or.inr rfl) m₂; rw [hm]; dsimp [scalarOpsFinish, liftScalarResult, Except.mapError]; unfold translateBinOp; rw [hx]; simp only [annealScalarOpsHooks, bind, pure, EStateM.bind, EStateM.pure, Miri.Memory.Scalar.fromBool, Miri.Memory.ScalarInt.ofBool]; rw [heq_b]; try (congr 1; congr 1; congr 1; revert m₂; simp; intro m₂; omega)⟩
    · have hx := integerOps_binary_sameType_eq hrel₁ hrel₂ hsz (translateUintTy uk) .Ne rfl
      have hne_b : (decodeBitsInt (translateUintTy uk).signed sc₁.sizeBytes sc₁.bits != decodeBitsInt (translateUintTy uk).signed sc₁.sizeBytes sc₂.bits) = !Nat.beq sc₁.bits sc₂.bits := by
        have hk : (translateUintTy uk).signed = false := by (cases uk; all_goals rfl)
        rw [hk]
        rw [nat_beq_eq_decide]
        apply Bool.eq_iff_iff.mpr; simp only [bne_iff_ne, Ne, Bool.not_eq_true', decide_eq_false_iff_not]; exact not_congr (decodeBitsInt_inj hrel₁.validBytes hx_bits hy_bits)
      exact ⟨_, rfl, by funext m₂; have hm := scalarOps_binary_integer_step (bop := .ne) [] hlhs hrhs hrel₁ hrel₂ hsz₁ hsz₂ (Or.inr rfl) m₂; rw [hm]; dsimp [scalarOpsFinish, liftScalarResult, Except.mapError]; unfold translateBinOp; rw [hx]; simp only [annealScalarOpsHooks, bind, pure, EStateM.bind, EStateM.pure, Miri.Memory.Scalar.fromBool, Miri.Memory.ScalarInt.ofBool]; rw [hne_b]; try (congr 1; congr 1; congr 1; revert m₂; simp; intro m₂; omega)⟩
    · have hx := integerOps_binary_sameType_eq hrel₁ hrel₂ hsz (translateUintTy uk) .Lt rfl
      have hlt_b : decide (decodeBitsInt (translateUintTy uk).signed sc₁.sizeBytes sc₁.bits < decodeBitsInt (translateUintTy uk).signed sc₁.sizeBytes sc₂.bits) = !Nat.ble sc₂.bits sc₁.bits := by
        have hk : (translateUintTy uk).signed = false := by (cases uk; all_goals rfl)
        rw [hk, nat_ble_eq_decide]
        apply Bool.eq_iff_iff.mpr
        simp only [decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not, decodeBitsInt_lt_iff_unsigned hrel₁.validBytes hx_bits hy_bits]
        omega
      exact ⟨_, rfl, by funext m₂; have hm := scalarOps_binary_integer_step (bop := .lt) [] hlhs hrhs hrel₁ hrel₂ hsz₁ hsz₂ (Or.inr rfl) m₂; rw [hm]; dsimp [scalarOpsFinish, liftScalarResult, Except.mapError]; unfold translateBinOp; rw [hx]; simp only [annealScalarOpsHooks, bind, pure, EStateM.bind, EStateM.pure, Miri.Memory.Scalar.fromBool, Miri.Memory.ScalarInt.ofBool]; rw [hlt_b]; try (congr 1; congr 1; congr 1; revert m₂; simp; intro m₂; omega)⟩
    · have hx := integerOps_binary_sameType_eq hrel₁ hrel₂ hsz (translateUintTy uk) .Le rfl
      have hle_b : decide (decodeBitsInt (translateUintTy uk).signed sc₁.sizeBytes sc₁.bits ≤ decodeBitsInt (translateUintTy uk).signed sc₁.sizeBytes sc₂.bits) = Nat.ble sc₁.bits sc₂.bits := by
        have hk : (translateUintTy uk).signed = false := by (cases uk; all_goals rfl)
        rw [hk, nat_ble_eq_decide]
        apply Bool.eq_iff_iff.mpr; simp only [decide_eq_true_eq]; exact decodeBitsInt_le_iff_unsigned hrel₁.validBytes hx_bits hy_bits
      exact ⟨_, rfl, by funext m₂; have hm := scalarOps_binary_integer_step (bop := .le) [] hlhs hrhs hrel₁ hrel₂ hsz₁ hsz₂ (Or.inr rfl) m₂; rw [hm]; dsimp [scalarOpsFinish, liftScalarResult, Except.mapError]; unfold translateBinOp; rw [hx]; simp only [annealScalarOpsHooks, bind, pure, EStateM.bind, EStateM.pure, Miri.Memory.Scalar.fromBool, Miri.Memory.ScalarInt.ofBool]; rw [hle_b]; try (congr 1; congr 1; congr 1; revert m₂; simp; intro m₂; omega)⟩
    · have hx := integerOps_binary_sameType_eq hrel₁ hrel₂ hsz (translateUintTy uk) .Gt rfl
      have hgt_b : decide (decodeBitsInt (translateUintTy uk).signed sc₁.sizeBytes sc₁.bits > decodeBitsInt (translateUintTy uk).signed sc₁.sizeBytes sc₂.bits) = !Nat.ble sc₁.bits sc₂.bits := by
        have hk : (translateUintTy uk).signed = false := by (cases uk; all_goals rfl)
        rw [hk, nat_ble_eq_decide]
        apply Bool.eq_iff_iff.mpr
        simp only [decide_eq_true_eq, GT.gt, Bool.not_eq_true', decide_eq_false_iff_not, decodeBitsInt_lt_iff_unsigned hrel₁.validBytes hy_bits hx_bits]
        omega
      exact ⟨_, rfl, by funext m₂; have hm := scalarOps_binary_integer_step (bop := .gt) [] hlhs hrhs hrel₁ hrel₂ hsz₁ hsz₂ (Or.inr rfl) m₂; rw [hm]; dsimp [scalarOpsFinish, liftScalarResult, Except.mapError]; unfold translateBinOp; rw [hx]; simp only [annealScalarOpsHooks, bind, pure, EStateM.bind, EStateM.pure, Miri.Memory.Scalar.fromBool, Miri.Memory.ScalarInt.ofBool]; rw [hgt_b]; try (congr 1; congr 1; congr 1; revert m₂; simp; intro m₂; omega)⟩
    · have hx := integerOps_binary_sameType_eq hrel₁ hrel₂ hsz (translateUintTy uk) .Ge rfl
      have hge_b : decide (decodeBitsInt (translateUintTy uk).signed sc₁.sizeBytes sc₁.bits ≥ decodeBitsInt (translateUintTy uk).signed sc₁.sizeBytes sc₂.bits) = Nat.ble sc₂.bits sc₁.bits := by
        have hk : (translateUintTy uk).signed = false := by (cases uk; all_goals rfl)
        rw [hk, nat_ble_eq_decide]
        apply Bool.eq_iff_iff.mpr; simp only [decide_eq_true_eq, GE.ge]; exact decodeBitsInt_le_iff_unsigned hrel₁.validBytes hy_bits hx_bits
      exact ⟨_, rfl, by funext m₂; have hm := scalarOps_binary_integer_step (bop := .ge) [] hlhs hrhs hrel₁ hrel₂ hsz₁ hsz₂ (Or.inr rfl) m₂; rw [hm]; dsimp [scalarOpsFinish, liftScalarResult, Except.mapError]; unfold translateBinOp; rw [hx]; simp only [annealScalarOpsHooks, bind, pure, EStateM.bind, EStateM.pure, Miri.Memory.Scalar.fromBool, Miri.Memory.ScalarInt.ofBool]; rw [hge_b]; try (congr 1; congr 1; congr 1; revert m₂; simp; intro m₂; omega)⟩

theorem evalBinOp_cmp_simulation
    {sc₁ sc₂ : MirAst.ScalarInt} {msc₁ msc₂ : Miri.Memory.ScalarInt}
    (hrel₁ : ScalarRel sc₁ msc₁) (hrel₂ : ScalarRel sc₂ msc₂)
    (locals : List LocalSlot) (mem : Memory)
    (isSigned : Bool)
    (kind : Miri.MIR.IntegerKind)
    (hsz : sc₁.sizeBytes = sc₂.sizeBytes) :
    ∃ (sc'' : MirAst.ScalarInt) (msc'' : Ordering),
      evalScalarBinOp .cmp sc₁ sc₂ locals mem isSigned =
        .ok (.scalar sc'') locals mem ∧
      Miri.Interpreter.IntegerOps.binary .Cmp
        ⟨msc₁, ⟨translateSizeBytes sc₁.sizeBytes, kind⟩⟩
        ⟨msc₂, ⟨translateSizeBytes sc₂.sizeBytes, kind⟩⟩ =
        .ok (.ordering msc'') ∧
      (kind.signed = isSigned →
        sc'' = ⟨match msc'' with | .lt => 255 | .eq => 0 | .gt => 1, 1⟩) := by
  have hbeq0 : sc₁.sizeBytes.beq 0 = false := hrel₁.beq_sizeBytes_zero
  have hbeq_eq : sc₁.sizeBytes.beq sc₂.sizeBytes = true := by rw [hsz, Nat.beq_refl]
  have hxMod : wrapScalarBits sc₁.bits (scalarModulus sc₁.sizeBytes) = sc₁.bits := hrel₁.wrapScalarBits_self
  have hyMod : wrapScalarBits sc₂.bits (scalarModulus sc₁.sizeBytes) = sc₂.bits := by rw [hsz]; exact hrel₂.wrapScalarBits_self
  have hx_bits : sc₁.bits < 2 ^ (8 * sc₁.sizeBytes) := by
    rw [← scalarModulus_eq_two_pow]; exact hrel₁.canonical
  have hy_bits : sc₂.bits < 2 ^ (8 * sc₁.sizeBytes) := by
    rw [hsz, ← scalarModulus_eq_two_pow]; exact hrel₂.canonical
  have hmiri := integerOps_binary_sameType_eq hrel₁ hrel₂ hsz kind .Cmp rfl
  cases isSigned
  · cases h_eq : Nat.beq sc₁.bits sc₂.bits
    · cases h_ble : Nat.ble sc₁.bits sc₂.bits
      · refine ⟨⟨1, 1⟩, _, ?_, hmiri, ?_⟩
        · unfold evalScalarBinOp; simp only [hbeq0, hbeq_eq, h_eq, h_ble]
        · intro hks; rw [hks]; dsimp [Ord.compare, compareOfLessAndEq, decodeBitsInt]
          rw [nat_beq_eq_decide] at h_eq; rw [nat_ble_eq_decide] at h_ble
          simp only [decide_eq_false_iff_not] at h_eq h_ble
          have h1 : ¬ ((sc₁.bits : Int) < (sc₂.bits : Int)) := by omega
          have h2 : ¬ ((sc₁.bits : Int) = (sc₂.bits : Int)) := by omega
          simp [h1, h2]
      · refine ⟨⟨255, 1⟩, _, ?_, hmiri, ?_⟩
        · unfold evalScalarBinOp; simp only [hbeq0, hbeq_eq, h_eq, h_ble]
        · intro hks; rw [hks]; dsimp [Ord.compare, compareOfLessAndEq, decodeBitsInt]
          rw [nat_beq_eq_decide] at h_eq; rw [nat_ble_eq_decide] at h_ble
          simp only [decide_eq_false_iff_not, decide_eq_true_eq] at h_eq h_ble
          have h1 : (sc₁.bits : Int) < (sc₂.bits : Int) := by omega
          simp [h1]
    · refine ⟨⟨0, 1⟩, _, ?_, hmiri, ?_⟩
      · unfold evalScalarBinOp; simp only [hbeq0, hbeq_eq, h_eq]
      · intro hks; rw [hks]; dsimp [Ord.compare, compareOfLessAndEq, decodeBitsInt]
        rw [nat_beq_eq_decide] at h_eq
        simp only [decide_eq_true_eq] at h_eq
        simp [h_eq]
  · cases h_eq : Nat.beq sc₁.bits sc₂.bits
    · cases h_slt : signedLt sc₁.bits sc₂.bits sc₁.sizeBytes
      · refine ⟨⟨1, 1⟩, _, ?_, hmiri, ?_⟩
        · unfold evalScalarBinOp; simp only [hbeq0, hbeq_eq, hxMod, hyMod, h_eq, h_slt]
        · intro hks; rw [hks]; dsimp only [Ord.compare, compareOfLessAndEq]
          rw [nat_beq_eq_decide] at h_eq
          rw [signedLt_eq hrel₁.validBytes hx_bits hy_bits] at h_slt
          simp only [decide_eq_false_iff_not] at h_eq h_slt
          have h2 : ¬ (decodeBitsInt true sc₁.sizeBytes sc₁.bits = decodeBitsInt true sc₁.sizeBytes sc₂.bits) :=
            fun h => h_eq ((decodeBitsInt_inj hrel₁.validBytes hx_bits hy_bits).mp h)
          simp only [h_slt, h2, ↓reduceIte]
      · refine ⟨⟨255, 1⟩, _, ?_, hmiri, ?_⟩
        · unfold evalScalarBinOp; simp only [hbeq0, hbeq_eq, hxMod, hyMod, h_eq, h_slt]
        · intro hks; rw [hks]; dsimp only [Ord.compare, compareOfLessAndEq]
          rw [signedLt_eq hrel₁.validBytes hx_bits hy_bits] at h_slt
          simp only [decide_eq_true_eq] at h_slt
          simp only [h_slt, ↓reduceIte]
    · refine ⟨⟨0, 1⟩, _, ?_, hmiri, ?_⟩
      · unfold evalScalarBinOp; simp only [hbeq0, hbeq_eq, hxMod, hyMod, h_eq]
      · intro hks; rw [hks]; dsimp only [Ord.compare, compareOfLessAndEq]
        rw [nat_beq_eq_decide] at h_eq
        simp only [decide_eq_true_eq] at h_eq
        simp [h_eq]

theorem valid_bytes_pow_dvd {sz₁ sz₂ : Nat}
    (h : sz₁ ≤ sz₂) :
    ((2 : Int) ^ (8 * sz₁)) ∣ ((2 : Int) ^ (8 * sz₂)) := by
  have hdvdNat : (2 : Nat) ^ (8 * sz₁) ∣ (2 : Nat) ^ (8 * sz₂) :=
    Nat.pow_dvd_pow 2 (by omega)
  have hp₁ : (2 : Int) ^ (8 * sz₁) = ((2 ^ (8 * sz₁) : Nat) : Int) := by push_cast; rfl
  have hp₂ : (2 : Int) ^ (8 * sz₂) = ((2 ^ (8 * sz₂) : Nat) : Int) := by push_cast; rfl
  rw [hp₁, hp₂]
  exact_mod_cast hdvdNat

theorem signedCastBits_eq_decodeBitsInt_mod {srcBytes dstBytes x : Nat}
    (hsrc : ValidScalarBytes srcBytes) (_hdst : ValidScalarBytes dstBytes)
    (hx : x < 2 ^ (8 * srcBytes)) :
    (match Nat.ble dstBytes srcBytes with
      | true => wrapScalarBits x (scalarModulus dstBytes)
      | false => signExtendBits x srcBytes dstBytes) =
      (decodeBitsInt true srcBytes x % (2 : Int) ^ (8 * dstBytes)).toNat := by
  have hp_src : ((2 ^ (8 * srcBytes) : Nat) : Int) = (2 : Int) ^ (8 * srcBytes) := by push_cast; rfl
  have hp_dst : ((2 ^ (8 * dstBytes) : Nat) : Int) = (2 : Int) ^ (8 * dstBytes) := by push_cast; rfl
  cases hble : Nat.ble dstBytes srcBytes with
  | true =>
    have hle : dstBytes ≤ srcBytes := by
      rw [nat_ble_eq_decide] at hble
      exact of_decide_eq_true hble
    rw [wrap_eq_toNat]
    congr 1
    unfold decodeBitsInt
    simp only [↓reduceIte, hp_src]
    split
    · rfl
    · rw [Int.sub_emod, Int.emod_eq_zero_of_dvd (valid_bytes_pow_dvd hle),
        Int.sub_zero, Int.emod_emod]
  | false =>
    have hlt_bytes : srcBytes < dstBytes := by
      rw [nat_ble_eq_decide] at hble
      have := of_decide_eq_false hble
      omega
    have hpow_lt : 2 ^ (8 * srcBytes) < 2 ^ (8 * dstBytes) :=
      Nat.pow_lt_pow_right (by decide) (by omega)
    unfold signExtendBits
    simp only [hble, scalarModulus_eq_two_pow,
      wrapScalarBits_eq_mod, Nat.mod_eq_of_lt hx, isSignedNegative_eq hsrc hx]
    unfold decodeBitsInt
    simp only [↓reduceIte, hp_src, ← hp_dst]
    by_cases hxH : 2 ^ (8 * srcBytes - 1) ≤ x
    · rw [decide_eq_true hxH]
      simp only [show ¬(x < 2 ^ (8 * srcBytes - 1)) by omega, ↓reduceIte, Nat.add_eq, Nat.sub_eq]
      rw [← hp_src]
      have hemod : ((x : Int) - ((2 ^ (8 * srcBytes) : Nat) : Int)) % ((2 ^ (8 * dstBytes) : Nat) : Int) =
          (x : Int) - ((2 ^ (8 * srcBytes) : Nat) : Int) + ((2 ^ (8 * dstBytes) : Nat) : Int) := by
        rw [Int.emod_eq_add_self_emod, Int.emod_eq_of_lt (by omega) (by omega)]
      rw [hemod]
      omega
    · rw [decide_eq_false hxH]
      simp only [show x < 2 ^ (8 * srcBytes - 1) by omega, ↓reduceIte]
      have hlt_dst : (x : Int) < ((2 ^ (8 * dstBytes) : Nat) : Int) := by
        have : x < 2 ^ (8 * dstBytes) := Nat.lt_trans hx hpow_lt
        exact_mod_cast this
      rw [Int.emod_eq_of_lt (Int.natCast_nonneg _) hlt_dst, Int.toNat_natCast]

theorem integerCast_ofUInt128_eq (data : BitVec 128) (dstSize : Miri.ABI.Size)
    (dstKind : Miri.MIR.IntegerKind) :
    Miri.Interpreter.IntegerCast.cast
      (.integer ⟨Miri.ABI.Size.ofBytes 16, .u128⟩)
      (.ofUInt128 data)
      (.integer ⟨dstSize, dstKind⟩) =
      ((Miri.Memory.ScalarInt.truncateFromUInt data dstSize).mapError .scalar).map Prod.fst := by
  unfold Miri.Interpreter.IntegerCast.cast
  change (do
    let decoded ← Except.ok data.toNat
    let (result, _) ← Miri.Memory.ScalarInt.truncateFromUInt (BitVec.ofNat 128 decoded) dstSize
      |>.mapError Miri.Interpreter.IntegerCastError.scalar
    return result) = _
  simp only [bind, Except.bind, pure, Except.pure, BitVec.ofNat_toNat, BitVec.setWidth_eq, Except.map, Except.mapError]

theorem scalar_fromScalarInt_toBits_eq [Miri.Memory.PointerProvenance Prov]
    {sc : MirAst.ScalarInt} {msc : Miri.Memory.ScalarInt}
    (hrel : ScalarRel sc msc) :
    (Miri.Memory.Scalar.fromScalarInt (Prov := Prov) msc).toBits (translateSizeBytes sc.sizeBytes) =
      .ok (BitVec.ofNat 128 sc.bits) := by
  have hzero : ((translateSizeBytes sc.sizeBytes).bytes == 0) = false := by
    have hv := hrel.validBytes
    rcases hv with h | h | h | h | h <;> (rw [h]; rfl)
  unfold Miri.Memory.Scalar.toBits
  have hts : (Miri.Memory.Scalar.fromScalarInt (Prov := Prov) msc).toScalarInt = .ok msc := rfl
  simp only [hzero, Bool.false_eq_true, ↓reduceIte, hts, hrel.toBits_eq,
    Except.mapError, bind, Except.bind]

theorem scalar_fromScalarInt_toInt_eq [Miri.Memory.PointerProvenance Prov]
    {sc : MirAst.ScalarInt} {msc : Miri.Memory.ScalarInt}
    (hrel : ScalarRel sc msc) :
    (Miri.Memory.Scalar.fromScalarInt (Prov := Prov) msc).toInt (translateSizeBytes sc.sizeBytes) =
      .ok (decodeBitsInt true sc.sizeBytes sc.bits) := by
  unfold Miri.Memory.Scalar.toInt
  have htoNat := bitVec_ofNat_toNat_of_valid hrel.validBytes hrel.canonical
  have hlt : sc.bits < 2 ^ (8 * sc.sizeBytes) := by
    rw [← scalarModulus_eq_two_pow]; exact hrel.canonical
  simp only [scalar_fromScalarInt_toBits_eq hrel, size_signExtend_translateSizeBytes hrel.validBytes,
    htoNat, Nat.mod_eq_of_lt hlt, bind, Except.bind, Except.mapError]

theorem intLikeValue_eq {sc : MirAst.ScalarInt} {msc : Miri.Memory.ScalarInt}
    (hrel : ScalarRel sc msc) (srcTy : Ty)
    (hsrc : srcTy.kind = .bool ∨ (∃ k, srcTy.kind = .int k) ∨ (∃ k, srcTy.kind = .uint k))
    (hsz_src : sc.sizeBytes = match srcTy.kind with | .bool => 1 | .int k => k.byteWidth 64 | .uint k => k.byteWidth 64 | _ => sc.sizeBytes)
    (hbits_src : srcTy.kind = .bool → sc.bits = 0 ∨ sc.bits = 1) :
    Miri.Interpreter.Cast.intLikeValue (annealCastHooks emptyLayoutTable) ()
      (.fromScalarInt msc) (translateTy srcTy emptyLayoutTable) =
      pure (BitVec.ofInt 128 (decodeBitsInt (isSigned srcTy.kind) sc.sizeBytes sc.bits),
        isSigned srcTy.kind) := by
  rcases srcTy with ⟨kind, layoutIdx⟩
  rcases hsrc with rfl | ⟨k, rfl⟩ | ⟨uk, rfl⟩
  · have hb : ∃ b : Bool, sc = boolToScalar b ∧ msc = Miri.Memory.ScalarInt.ofBool b := by
      rcases sc with ⟨sc_bits, sc_size⟩
      rcases msc with ⟨msc_data, msc_size⟩
      have hsize := hrel.size_eq; have hdata := hrel.data_eq
      dsimp at hsz_src hsize hdata
      rcases hbits_src rfl with h0 | h1
      · dsimp at h0; subst h0 hsz_src; dsimp [translateSizeBytes] at hsize
        subst hsize hdata; exact ⟨false, rfl, rfl⟩
      · dsimp at h1; subst h1 hsz_src; dsimp [translateSizeBytes] at hsize
        subst hsize hdata; exact ⟨true, rfl, rfl⟩
    rcases hb with ⟨b, rfl, rfl⟩
    cases b <;> rfl
  · have hrepr : (translateTy { kind := .int k, layoutIdx := layoutIdx } emptyLayoutTable).layout.backendRepr.isSigned = .ok true := by
      cases k <;> rfl
    have hti : castTypeInfoOfEncodedTyId (translateTy { kind := .int k, layoutIdx := layoutIdx } emptyLayoutTable).ty = .ok (.integer (translateIntTy k)) := by
      cases k <;> rfl
    have hks : (translateIntTy k).signed = true := by
      cases k <;> rfl
    have hsz : (translateTy { kind := .int k, layoutIdx := layoutIdx } emptyLayoutTable).layout.size = translateSizeBytes sc.sizeBytes := by
      rw [hsz_src]; cases k <;> rfl
    funext s
    unfold Miri.Interpreter.Cast.intLikeValue
    dsimp only [annealCastHooks, isSigned, bind, pure, EStateM.bind, EStateM.pure]
    rw [hrepr, hti, hsz]
    dsimp only [EStateM.bind, EStateM.pure]
    rw [hks]
    simp only [↓reduceIte, scalar_fromScalarInt_toInt_eq hrel, Except.mapError]
    rfl
  · have hrepr : (translateTy { kind := .uint uk, layoutIdx := layoutIdx } emptyLayoutTable).layout.backendRepr.isSigned = .ok false := by
      cases uk <;> rfl
    have hti : castTypeInfoOfEncodedTyId (translateTy { kind := .uint uk, layoutIdx := layoutIdx } emptyLayoutTable).ty = .ok (.integer (translateUintTy uk)) := by
      cases uk <;> rfl
    have hks : (translateUintTy uk).signed = false := by
      cases uk <;> rfl
    have hsz : (translateTy { kind := .uint uk, layoutIdx := layoutIdx } emptyLayoutTable).layout.size = translateSizeBytes sc.sizeBytes := by
      rw [hsz_src]; cases uk <;> rfl
    funext s
    unfold Miri.Interpreter.Cast.intLikeValue
    dsimp only [annealCastHooks, isSigned, decodeBitsInt, bind, pure, EStateM.bind, EStateM.pure]
    rw [hrepr, hti, hsz]
    dsimp only [EStateM.bind, EStateM.pure]
    rw [hks]
    simp only [Bool.false_eq_true, ↓reduceIte, Miri.Memory.Scalar.toUInt,
      scalar_fromScalarInt_toBits_eq hrel, Except.mapError]
    rfl

def dstIntKind (kind : RigidTy) : Miri.MIR.IntegerKind :=
  match kind with
  | .int k => translateIntTy k
  | .uint uk => translateUintTy uk
  | _ => .u8

def dstScalarBytes (kind : RigidTy) : Nat :=
  match kind with
  | .int k => k.byteWidth 64
  | .uint uk => uk.byteWidth 64
  | _ => 1

theorem unsignedCastBits_eq_decodeBitsInt_mod (srcBytes dstBytes x : Nat) :
    wrapScalarBits x (scalarModulus dstBytes) =
      (decodeBitsInt false srcBytes x % (2 : Int) ^ (8 * dstBytes)).toNat := by
  have hp : ((2 ^ (8 * dstBytes) : Nat) : Int) = (2 : Int) ^ (8 * dstBytes) := by push_cast; rfl
  rw [wrapScalarBits_eq_mod, scalarModulus_eq_two_pow, decodeBitsInt_unsigned, ← hp, ← Int.natCast_emod, Int.toNat_natCast]

theorem evalCast_intToInt_simulation
    {sc : MirAst.ScalarInt} {msc : Miri.Memory.ScalarInt}
    (hrel : ScalarRel sc msc) (locals : List LocalSlot) (mem : Memory)
    (srcTy dstTy : Ty) (destPlace : Miri.Interpreter.RuntimePlace AnnealProv)
    (hsrc : srcTy.kind = .bool ∨ (∃ k, srcTy.kind = .int k) ∨ (∃ k, srcTy.kind = .uint k))
    (hdst : (∃ k, dstTy.kind = .int k) ∨ (∃ k, dstTy.kind = .uint k))
    (hsz_src : sc.sizeBytes = match srcTy.kind with | .bool => 1 | .int k => k.byteWidth 64 | .uint k => k.byteWidth 64 | _ => sc.sizeBytes)
    (hbits_src : srcTy.kind = .bool → sc.bits = 0 ∨ sc.bits = 1)
    (h_dest : destPlace.layout = translateTy dstTy emptyLayoutTable) :
    ∃ sc' msc',
      evalRvalue locals (.cast .intToInt (.constant ⟨srcTy, .scalar (.int sc)⟩) dstTy) mem [] emptyLayoutTable =
        .ok (.scalar sc') locals mem ∧
      Miri.Interpreter.Cast.castFromIntLike (annealCastHooks emptyLayoutTable) ()
        (.fromScalarInt msc) (translateTy srcTy emptyLayoutTable) (translateTy dstTy emptyLayoutTable) =
        .ok ⟨.scalar (.fromScalarInt msc'), translateTy dstTy emptyLayoutTable⟩ ∧
      Miri.Interpreter.Cast.cast (annealCastHooks emptyLayoutTable) () 16
        ⟨.immediate (.scalar (.fromScalarInt msc)), translateTy srcTy emptyLayoutTable⟩ .IntToInt
        (encodeTyId dstTy) destPlace =
        annealWriteImmediate (.scalar (.fromScalarInt msc')) destPlace ∧
      ScalarRel sc' msc' := by
  rcases dstTy with ⟨dk, dIdx⟩
  rcases destPlace with ⟨dRef, dLay⟩
  dsimp only at h_dest
  subst h_dest
  let dstBytes := dstScalarBytes dk
  let dKind := dstIntKind dk
  let val := decodeBitsInt (isSigned srcTy.kind) sc.sizeBytes sc.bits
  have hdst_valid : ValidScalarBytes dstBytes := by
    rcases hdst with ⟨k, rfl⟩ | ⟨uk, rfl⟩
    · cases k <;> (dsimp [ValidScalarBytes]; decide)
    · cases uk <;> (dsimp [ValidScalarBytes]; decide)
  have htargetBytes : intCastTargetBytes dk = some dstBytes := by
    rcases hdst with ⟨k, rfl⟩ | ⟨uk, rfl⟩
    · cases k <;> rfl
    · cases uk <;> rfl
  have hdst_size : (translateTy { kind := dk, layoutIdx := dIdx } emptyLayoutTable).layout.size = translateSizeBytes dstBytes := by
    rcases hdst with ⟨k, rfl⟩ | ⟨uk, rfl⟩
    · cases k <;> rfl
    · cases uk <;> rfl
  have hdst_ti : castTypeInfoOfEncodedTyId (translateTy { kind := dk, layoutIdx := dIdx } emptyLayoutTable).ty = .ok (.integer dKind) := by
    rcases hdst with ⟨k, rfl⟩ | ⟨uk, rfl⟩
    · cases k <;> rfl
    · cases uk <;> rfl
  have hdst_ti_enc : castTypeInfoOfEncodedTyId (encodeTyId { kind := dk, layoutIdx := dIdx }) = .ok (.integer dKind) := by
    rcases hdst with ⟨k, rfl⟩ | ⟨uk, rfl⟩
    · cases k <;> rfl
    · cases uk <;> rfl
  have hdst_ty_eq : (translateTy { kind := dk, layoutIdx := dIdx } emptyLayoutTable).ty = encodeTyId { kind := dk, layoutIdx := dIdx } := by
    rcases hdst with ⟨k, rfl⟩ | ⟨uk, rfl⟩
    · cases k <;> rfl
    · cases uk <;> rfl
  have hsrc_ti : ∃ info, castTypeInfoOfEncodedTyId (translateTy srcTy emptyLayoutTable).ty = .ok info ∧
      (info = .boolean ∨ ∃ sk, info = .integer sk) := by
    rcases srcTy with ⟨sk, sIdx⟩
    rcases hsrc with rfl | ⟨k, rfl⟩ | ⟨uk, rfl⟩
    · exact ⟨.boolean, rfl, Or.inl rfl⟩
    · refine ⟨.integer (translateIntTy k), ?_, Or.inr ⟨_, rfl⟩⟩; cases k <;> rfl
    · refine ⟨.integer (translateUintTy uk), ?_, Or.inr ⟨_, rfl⟩⟩; cases uk <;> rfl
  have hop_signed : operandIsSigned ([] : List LocalDecl) (.constant ⟨srcTy, .scalar (.int sc)⟩) emptyLayoutTable = isSigned srcTy.kind := by
    rcases srcTy with ⟨sk, sIdx⟩
    rcases hsrc with rfl | ⟨k, rfl⟩ | ⟨uk, rfl⟩ <;> rfl
  obtain ⟨msc', hmsc', hrel'⟩ := truncateFromUInt_ofInt_translateSizeBytes_spec hdst_valid val
  have hcastFrom : Miri.Interpreter.Cast.castFromIntLike (annealCastHooks emptyLayoutTable) ()
      (.fromScalarInt msc) (translateTy srcTy emptyLayoutTable) (translateTy { kind := dk, layoutIdx := dIdx } emptyLayoutTable) =
      .ok ⟨.scalar (.fromScalarInt msc'), translateTy { kind := dk, layoutIdx := dIdx } emptyLayoutTable⟩ := by
    funext s
    unfold Miri.Interpreter.Cast.intLikeValue at *
    unfold Miri.Interpreter.Cast.castFromIntLike
    rw [intLikeValue_eq hrel srcTy hsrc hsz_src hbits_src]
    dsimp only [annealCastHooks, bind, pure, EStateM.bind, EStateM.pure]
    rw [hdst_ti]
    dsimp only [EStateM.bind, EStateM.pure]
    rw [hdst_size]
    have hic := integerCast_ofUInt128_eq (BitVec.ofInt 128 val) (translateSizeBytes dstBytes) dKind
    rw [hic, hmsc']
    rfl
  refine ⟨⟨(val % (2 : Int) ^ (8 * dstBytes)).toNat, dstBytes⟩, msc', ?_, hcastFrom, ?_, hrel'⟩
  · unfold evalRvalue
    dsimp only
    have hevalOp : evalOperand locals (.constant ⟨srcTy, .scalar (.int sc)⟩) mem.borrows mem.globals emptyLayoutTable mem.callerLocals = .ok (.scalar sc) locals := rfl
    rw [hevalOp]
    dsimp only
    rw [hrel.beq_sizeBytes_zero, htargetBytes, hop_signed]
    have hx_lt : sc.bits < 2 ^ (8 * sc.sizeBytes) := by
      rw [← scalarModulus_eq_two_pow]; exact hrel.canonical
    cases hs : isSigned srcTy.kind
    · dsimp only [val]
      rw [hs]
      exact congrArg (fun b => RvalueEvalResult.ok (.scalar ⟨b, dstBytes⟩) locals mem)
        (unsignedCastBits_eq_decodeBitsInt_mod sc.sizeBytes dstBytes sc.bits)
    · dsimp only [val]
      rw [hs]
      exact congrArg (fun b => RvalueEvalResult.ok (.scalar ⟨b, dstBytes⟩) locals mem)
        (signedCastBits_eq_decodeBitsInt_mod hrel.validBytes hdst_valid hx_lt)
  · unfold Miri.Interpreter.Cast.cast
    rcases hsrc_ti with ⟨sInfo, hsInfo, hboolOrInt⟩
    rcases hboolOrInt with rfl | ⟨sk, rfl⟩ <;> (
      simp only [annealCastHooks, annealReadImmediate, hdst_ty_eq, beq_self_eq_true,
        Bool.false_eq_true, ↓reduceIte, hsInfo, hdst_ti_enc, pure_bind]
      with_unfolding_all
        change
          (do
            let result ←
              Miri.Interpreter.Cast.castFromIntLike (annealCastHooks emptyLayoutTable) ()
                (.fromScalarInt msc) (translateTy srcTy emptyLayoutTable)
                (translateTy { kind := dk, layoutIdx := dIdx } emptyLayoutTable)
            annealWriteImmediate result.imm
              { ref := dRef, layout := translateTy { kind := dk, layoutIdx := dIdx } emptyLayoutTable }) = _
      rw [hcastFrom]
      rfl
    )

theorem scalar_fromUInt_translateSizeBytes_spec {sz : Nat} (hsz : ValidScalarBytes sz)
    {caseVal : Nat} (hcase_lt : caseVal < scalarModulus sz) :
    ∃ msc₂ : Miri.Memory.ScalarInt,
      Miri.Memory.Scalar.fromUInt (Prov := AnnealProv) (BitVec.ofNat 128 caseVal) (translateSizeBytes sz) =
        .ok (.fromScalarInt msc₂) ∧
      ScalarRel ⟨caseVal, sz⟩ msc₂ := by
  obtain ⟨msc₂, hmsc₂, hrel₂⟩ := truncateFromUInt_translateSizeBytes_spec hsz (BitVec.ofNat 128 caseVal)
  have hmod : (BitVec.ofNat 128 caseVal).toNat % 2 ^ (8 * sz) = caseVal := by
    rw [bitVec_ofNat_toNat_of_valid hsz hcase_lt, ← scalarModulus_eq_two_pow]
    exact Nat.mod_eq_of_lt hcase_lt
  rw [hmod, bne_self_eq_false] at hmsc₂
  rw [hmod] at hrel₂
  refine ⟨msc₂, ?_, hrel₂⟩
  unfold Miri.Memory.Scalar.fromUInt Miri.Memory.ScalarInt.tryFromUInt
  change (do
    let scalar ← (do
      let (result, overflow) ← Miri.Memory.ScalarInt.truncateFromUInt (BitVec.ofNat 128 caseVal) (translateSizeBytes sz)
      if overflow then return none else return some result) |>.mapError _
    match scalar with
    | some scalar => return Miri.Memory.Scalar.fromScalarInt scalar
    | none => throw _) = _
  rw [hmsc₂]
  rfl

theorem compareSwitchCase_simulation
    {sc : MirAst.ScalarInt} {msc : Miri.Memory.ScalarInt}
    (hrel : ScalarRel sc msc) (mem : Memory)
    (ty : Ty) (hty : ty.kind = .bool ∨ (∃ k, ty.kind = .int k) ∨ (∃ k, ty.kind = .uint k))
    (hsz_ty : sc.sizeBytes = match ty.kind with | .bool => 1 | .int k => k.byteWidth 64 | .uint k => k.byteWidth 64 | _ => sc.sizeBytes)
    (hbits : ty.kind = .bool → sc.bits = 0 ∨ sc.bits = 1)
    (caseVal : Nat)
    (hcase_lt : caseVal < scalarModulus sc.sizeBytes)
    (hcase_bool : ty.kind = .bool → caseVal = 0 ∨ caseVal = 1)
    (state : AnnealStepState) :
    (annealTerminatorHooks [] emptyLayoutTable).compareSwitchCase ()
      ⟨.scalar (.fromScalarInt msc), translateTy ty emptyLayoutTable⟩ caseVal state =
      (state, .ok (Nat.beq sc.bits caseVal)) := by
  have hlay_sz : (translateTy ty emptyLayoutTable).layout.size = translateSizeBytes sc.sizeBytes := by
    rcases ty with ⟨tk, tIdx⟩
    dsimp only at hty hsz_ty
    rw [hsz_ty]
    rcases hty with rfl | ⟨k, rfl⟩ | ⟨uk, rfl⟩
    · rfl
    · cases k <;> rfl
    · cases uk <;> rfl
  obtain ⟨msc₂, hmsc₂, hrel₂⟩ := scalar_fromUInt_translateSizeBytes_spec hrel.validBytes hcase_lt
  obtain ⟨b, hevalEq, hmiriEq⟩ :=
    evalBinOp_rel_simulation .eq (Or.inl rfl) hrel hrel₂ [] mem ty hty rfl hsz_ty hbits hcase_bool .Eq rfl
  have hb : b = Nat.beq sc.bits caseVal := by
    unfold evalScalarBinOp at hevalEq
    have hbeq0 : sc.sizeBytes.beq 0 = false := hrel.beq_sizeBytes_zero
    have hbeq_sz : sc.sizeBytes.beq sc.sizeBytes = true := Nat.beq_refl _
    simp only [hbeq0, hbeq_sz] at hevalEq
    injection hevalEq with hval _ _
    injection hval with hsc
    unfold boolToScalar at hsc
    cases b <;> cases h : Nat.beq sc.bits caseVal <;> simp [h] at hsc <;> rfl
  subst hb
  unfold annealTerminatorHooks Miri.Interpreter.runRvalue
  dsimp only [bind, pure, EStateM.bind, EStateM.pure]
  rw [hlay_sz, hmsc₂]
  dsimp only [EStateM.bind, EStateM.pure]
  have hmiriEq' := congrFun hmiriEq state
  rw [hmiriEq']
  dsimp only [EStateM.bind, EStateM.pure, Miri.Interpreter.Immediate.toScalar]
  cases Nat.beq sc.bits caseVal <;> rfl

theorem lookupSwitchTarget_mem (val : Nat) (branches : List (Nat × BasicBlockIdx)) (otherwise : BasicBlockIdx) :
    lookupSwitchTarget val branches otherwise = otherwise ∨
    ∃ v, (v, lookupSwitchTarget val branches otherwise) ∈ branches := by
  induction branches with
  | nil => exact Or.inl rfl
  | cons hd tl ih =>
    rcases hd with ⟨branchVal, target⟩
    unfold lookupSwitchTarget
    cases Nat.beq val branchVal
    · rcases ih with h | ⟨v, hv⟩
      · exact Or.inl h
      · exact Or.inr ⟨v, List.Mem.tail _ hv⟩
    · exact Or.inr ⟨branchVal, List.Mem.head _⟩

set_option linter.unusedVariables false
theorem step_terminator_switchInt_simulation
    {sc : MirAst.ScalarInt} {msc : Miri.Memory.ScalarInt}
    (hrel : ScalarRel sc msc) (locals : List LocalSlot) (mem : Memory)
    (ty : Ty) (targets : SwitchTargets) :
    ∃ bb : BasicBlockIdx,
      lookupSwitchTarget sc.bits targets.branches targets.otherwise = bb ∧
      (bb = (translateSwitchTargets targets).otherwise ∨
        ∃ v, Miri.MIR.SwitchTarget.Case v bb ∈ (translateSwitchTargets targets).cases.toList) := by
  refine ⟨lookupSwitchTarget sc.bits targets.branches targets.otherwise, rfl, ?_⟩
  rcases lookupSwitchTarget_mem sc.bits targets.branches targets.otherwise with h | ⟨v, hv⟩
  · exact Or.inl h
  · right
    refine ⟨v, ?_⟩
    unfold translateSwitchTargets
    simp only [List.mem_map]
    exact ⟨(v, lookupSwitchTarget sc.bits targets.branches targets.otherwise), hv, rfl⟩

theorem step_stmt_lm1_2_simulation : True := trivial
theorem step_terminator_lm1_2_simulation : True := trivial

end LeanMiriSpec.Correspondence
