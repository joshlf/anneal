import LeanMiriSpec.Correspondence.SimLM1_3

namespace LeanMiriSpec.Correspondence

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics

namespace Witness

def mkStmt3 (k : StatementKind) : MirAst.Statement := { kind := k, span := "lm-1.3-witness" }
def mkTerm3 (k : TerminatorKind) : MirAst.Terminator := { kind := k, span := "lm-1.3-witness" }
def local_3 (i : Nat) : Place := { local_ := i, projection := [] }

/-! ## Checked `(u16, bool)` `AddWithOverflow` witness (ABI-aligned scalar pair) -/

def u16Ty : Ty := { kind := .uint .u16, layoutIdx := 0 }
def u16BoolTupleTy : Ty := { kind := .tuple [u16Ty.kind, .bool], layoutIdx := 0 }
def u16Decl : LocalDecl := { mutability := .mut, ty := u16Ty, debugName := none }
def u16BoolDecl : LocalDecl := { mutability := .mut, ty := u16BoolTupleTy, debugName := none }
def constU16 (n : Nat) : ConstOperand := { ty := u16Ty, val := .scalar (.int ⟨n, 2⟩) }

def u16BoolPairLayout : TypeLayout :=
  { size := { bytes := 4 }
    align := { bytes := 2 }
    backendRepr :=
      .scalarPair
        (.initialized (.int 16 false) { start := 0, end_ := 65535 })
        (.initialized (.int 8 false) { start := 0, end_ := 1 })
    fields := .arbitrary [{ bytes := 0 }, { bytes := 2 }] [0, 1]
    variants := .single 0
    isUninhabited := false }

def u16BoolLayoutTable : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := [u16BoolPairLayout] }

def fnAbiU16Bool : FnAbi :=
  { args := []
    ret := { layout := u16BoolPairLayout, mode := .direct }
    conv := .rust
    canUnwind := false }

/-- `Runtime(PostCleanup)` MIR body computing `AddWithOverflow(65500_u16, rhs_u16)`
into a `(u16, bool)` return local `_0` whose ABI size is `4` (aligned from `3` up
to alignment `2`):
```text
bb0: StorageLive(_1); _1 = const 65500_u16;
     _0 = AddWithOverflow(copy _1, const rhs_u16);
     StorageDead(_1); return
``` -/
def addWithOverflowBody (rhs : Nat) : CapturedMir where
  defPath := "lm_1_1_witness::add_with_overflow"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [u16BoolDecl, u16Decl]
  basicBlocks := [
    { statements := [
        mkStmt3 (.storageLive 1),
        mkStmt3 (.assign (local_3 1) (.use (.constant (constU16 65500)))),
        mkStmt3 (.assign (local_3 0)
          (.binaryOp .addWithOverflow (.copy (local_3 1)) (.constant (constU16 rhs)))),
        mkStmt3 (.storageDead 1)],
      terminator := mkTerm3 .return_, isCleanup := false }]
  fnAbi := fnAbiU16Bool
  layouts := u16BoolLayoutTable
  allocations := []

def annealAddOvfInit (rhs : Nat) : MachineState :=
  initMachineState (addWithOverflowBody rhs) []

def miriAddOvfFrame (rhs : Nat) :
    Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit :=
  { body := translateBody (addWithOverflowBody rhs)
    bodyIdentity := .ofCanonicalIndex 0
    functionInstance := { kind := .Item 0, args := #[] }
    extra := ()
    returnContinuation := .stop false
    returnPlace :=
      .frameLocal 0 0 none (translateTy u16BoolTupleTy u16BoolLayoutTable) (.ofAllocationToken 0)
    localsIdentity := .ofAllocationToken 0
    locals := #[{ value := .live (.immediate .uninit), layout := none },
      { value := .dead, layout := none }]
    vaList := #[]
    trackCallerArg := none
    location := .mir ⟨0, 0⟩ }

def miriAddOvfInit (rhs : Nat) : AnnealStepState :=
  { stack := ⟨#[miriAddOvfFrame rhs]⟩, machine := AnnealMachine.empty }

theorem stateRel_addWithOverflow (rhs : Nat) :
    StateRel (addWithOverflowBody rhs) (annealAddOvfInit rhs) (miriAddOvfInit rhs) := by
  refine StateRel.mk (miriAddOvfFrame rhs) rfl rfl
    ⟨translateTy u16BoolTupleTy u16BoolLayoutTable, rfl⟩ ?_ rfl rfl rfl rfl rfl (by
      intro i j mplace_i mplace_j lay_i lay_j hneq hi hj
      revert hi
      match i with
      | 0 => rintro ⟨⟩
      | 1 => rintro ⟨⟩
      | 2 => rintro ⟨⟩
      | _ + 3 => rintro ⟨⟩)
  refine
    { body_eq := rfl
      location_eq := rfl
      af_locals_len := rfl
      mf_locals_size := rfl
      locals_rel := ?_ }
  intro i decl slot mls hdecl hslot hmls
  match i with
  | 0 =>
    have hd : decl = u16BoolDecl := by simpa [addWithOverflowBody, get?] using hdecl.symm
    have hs : slot = .uninit := by
      simpa [annealAddOvfInit, initMachineState, addWithOverflowBody, initLocalsAux, get?]
        using hslot.symm
    have hm : mls = { value := .live (.immediate .uninit), layout := none } := by
      simpa [miriAddOvfFrame] using hmls.symm
    subst hd hs hm
    exact .immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩)
  | 1 =>
    have hd : decl = u16Decl := by simpa [addWithOverflowBody, get?] using hdecl.symm
    have hs : slot = .dead := by
      simpa [annealAddOvfInit, initMachineState, addWithOverflowBody, initLocalsAux, get?]
        using hslot.symm
    have hm : mls = { value := .dead, layout := none } := by
      simpa [miriAddOvfFrame] using hmls.symm
    subst hd hs hm
    exact .dead none (fun _ h => nomatch h)
  | n + 2 =>
    simp [addWithOverflowBody, get?] at hdecl

theorem wellTyped_addWithOverflow (rhs : Nat) (hrhs : rhs < 65536) :
    WellTypedBody (addWithOverflowBody rhs) := by
  have hu16 : IsPrimScalarTy u16Ty := Or.inr (Or.inr (Or.inr ⟨.u16, rfl⟩))
  have hbits : ∀ n, n < 65536 → n < scalarModulus 2 := fun n h => by
    rw [scalarModulus_eq_two_pow]; simpa using h
  have hconst : ∀ n, n < 65536 →
      WellTypedScalarOperandSyn (addWithOverflowBody rhs) (fun _ => True)
        (.constant (constU16 n)) u16Ty :=
    fun n hn => .constScalar (constU16 n) ⟨n, 2⟩ rfl hu16 (Or.inr (Or.inl rfl))
      (hbits n hn) rfl (fun h => nomatch h) (fun h => nomatch h)
  have hu16int : IsIntegralTy u16Ty (translateUintTy .u16) := .uint .u16 rfl
  refine ⟨(fun p h => by simp [addWithOverflowBody] at h), ?_⟩
  intro bb hbb
  simp only [addWithOverflowBody, List.mem_singleton] at hbb
  subst hbb
  have hsz0 : (translateTy u16BoolDecl.ty u16BoolLayoutTable).layout.size ≠ Miri.ABI.Size.ZERO := by
    decide
  refine ⟨rfl, ?_, Or.inr (Or.inl ⟨rfl, trivial, u16BoolDecl, rfl, hsz0⟩)⟩
  intro stmt hstmt
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hstmt
  rcases hstmt with rfl | rfl | rfl | rfl
  · exact .storageLive _ 1 u16Decl rfl rfl trivial
  · exact .assign _ 1 u16Decl _ rfl rfl trivial (.use _ _ (hconst 65500 (by decide)))
  · exact .assign _ 0 u16BoolDecl _ rfl rfl trivial
      (.binaryOp .addWithOverflow _ _ u16Ty u16Ty u16BoolTupleTy
        (.copyLocal 1 u16Decl rfl (IsPrimScalarTy.size_ne_zero hu16) trivial)
        (hconst rhs hrhs)
        (.intWithOverflow .addWithOverflow u16Ty u16Ty u16BoolTupleTy _
          (Or.inl rfl) hu16int hu16int (Or.inl ⟨[u16Ty.kind, .bool], rfl⟩) rfl))
  · exact .storageDead _ 1 u16Decl rfl rfl (by decide) trivial

theorem run_bisim_addWithOverflow (fuel : Nat) (rhs : Nat) (hrhs : rhs < 65536) :
    ((∃ s', runAnnealBounded (addWithOverflowBody rhs) fuel (annealAddOvfInit rhs) =
        .running s') ↔
      (∃ m', runMiriBounded (addWithOverflowBody rhs) fuel (miriAddOvfInit rhs) =
        .running m')) ∧
    (∀ s' m',
      runAnnealBounded (addWithOverflowBody rhs) fuel (annealAddOvfInit rhs) = .running s' →
      runMiriBounded (addWithOverflowBody rhs) fuel (miriAddOvfInit rhs) = .running m' →
      StateRel (addWithOverflowBody rhs) s' m') ∧
    ((∃ retVal mem',
        runAnnealBounded (addWithOverflowBody rhs) fuel (annealAddOvfInit rhs) =
          .returned retVal mem') ↔
      (∃ m' retImm,
        runMiriBounded (addWithOverflowBody rhs) fuel (miriAddOvfInit rhs) =
          .returned m' (.ok (.immediate retImm)))) ∧
    (∀ retVal mem' m' retImm,
      runAnnealBounded (addWithOverflowBody rhs) fuel (annealAddOvfInit rhs) =
        .returned retVal mem' →
      runMiriBounded (addWithOverflowBody rhs) fuel (miriAddOvfInit rhs) =
        .returned m' (.ok (.immediate retImm)) →
      ∃ decl0, get? (addWithOverflowBody rhs).localDecls 0 = some decl0 ∧
        ImmediateRel decl0.ty (addWithOverflowBody rhs).layouts retVal retImm) ∧
    (runAnnealBounded (addWithOverflowBody rhs) fuel (annealAddOvfInit rhs) = .faulted .ub ↔
      ∃ m' msg,
        runMiriBounded (addWithOverflowBody rhs) fuel (miriAddOvfInit rhs) =
          .error m' (.undefinedBehavior msg)) ∧
    ((∃ s', runAnnealBounded (addWithOverflowBody rhs) fuel (annealAddOvfInit rhs) =
        .running s') ∨
      (∃ retVal mem',
        runAnnealBounded (addWithOverflowBody rhs) fuel (annealAddOvfInit rhs) =
          .returned retVal mem') ∨
      runAnnealBounded (addWithOverflowBody rhs) fuel (annealAddOvfInit rhs) = .faulted .ub) :=
  run_wellTypedBody_bisim fuel (wellTyped_addWithOverflow rhs hrhs)
    (stateRel_addWithOverflow rhs)
    ⟨_, rfl, Nat.zero_le _⟩
    (NonAddrTakenImmediate.of_live_nil _ (stateRel_addWithOverflow rhs) rfl)

def annealOutcomeU16Bool : AnnealRunOutcome → Option (Nat × Bool)
  | .returned (.aggregate 0 [.scalar ⟨bits, 2⟩, .scalar ⟨b, 1⟩]) _ =>
      if b == 0 then some (bits, false)
      else if b == 1 then some (bits, true)
      else none
  | _ => none

def miriOutcomeU16Bool : MiriRunOutcome → Option (Nat × Bool)
  | .returned m' (.ok (.immediate (.scalarPair s₁ s₂))) =>
      if m'.stack.frames.isEmpty then
        match s₁.toScalarInt, s₂.toScalarInt with
        | .ok sc₁, .ok sc₂ =>
            if sc₁.size == Miri.ABI.Size.ofBytes 2 && sc₂.size == Miri.ABI.Size.ofBytes 1 then
              if sc₂.data.toNat == 0 then some (sc₁.data.toNat, false)
              else if sc₂.data.toNat == 1 then some (sc₁.data.toNat, true)
              else none
            else none
        | _, _ => none
      else none
  | _ => none

/-- Checked `65500_u16 + 100_u16`: both machines wrap to `64` and set `overflow = true`. -/
theorem addWithOverflow_overflows_agrees :
    annealOutcomeU16Bool
        (runAnnealBounded (addWithOverflowBody 100) 5 (annealAddOvfInit 100)) =
      some (64, true) ∧
    miriOutcomeU16Bool
        (runMiriBounded (addWithOverflowBody 100) 5 (miriAddOvfInit 100)) =
      some (64, true) := by
  decide

/-- Checked `65500_u16 + 10_u16`: both machines return `(65510, false)`. -/
theorem addWithOverflow_noOverflow_agrees :
    annealOutcomeU16Bool
        (runAnnealBounded (addWithOverflowBody 10) 5 (annealAddOvfInit 10)) =
      some (65510, false) ∧
    miriOutcomeU16Bool
        (runMiriBounded (addWithOverflowBody 10) 5 (miriAddOvfInit 10)) =
      some (65510, false) := by
  decide

end Witness
end LeanMiriSpec.Correspondence
