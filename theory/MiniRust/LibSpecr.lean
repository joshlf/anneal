import Trusted.Refinement

/-!
# `MiniRust.LibSpecr` — Mechanized Foundation for `specr lang` Primitives

Provides the mathematical foundation for upstream MiniRust (`minirust/minirust`)
specifications translated into Lean 4:

1. Exact mathematical integers (`SpecrInt`), power-of-two byte alignment (`Align`),
   byte/bit sizes (`Size`), signed byte offsets (`Offset`), and endianness (`Endianness`).
2. Transparent value-semantic copy-on-write wrapper erasure (`GcCow α := α`).
3. Canonical persistent map and set containers (`SpecrMap`, `SpecrSet`).
4. Explicit machine termination outcomes (`TerminationInfo`: `ub`, `illFormed`,
   `machineStop`, `deadlock`, `memoryLeak`) and the dual-mode finitary
   nondeterministic computation tree (`NdComp α`).
5. Direct bridge into Layer 1A's Smyth refinement order (`Trusted.Refinement.Partial`
   and `Trusted.Refinement.BehaviorSet`), proving soundness of the deterministic
   seeded evaluator (`evalDet_sound_of_defined`) and top-refinement preservation
   for conservative UB and unmodeled features (`top_refines_unsupported`,
   `top_refines_false_positive_ub`).
-/

namespace MiniRust.LibSpecr

open Trusted.Refinement

/-! ## 1. Exact Mathematical Integers (`libspecr::Int`) -/

/-- Mathematical arbitrary-precision integer matching `libspecr::Int`. -/
abbrev SpecrInt : Type := Int

namespace SpecrInt

/-- Unsigned bit-width modulus $2^{\text{bits}}$. -/
@[reducible]
def unsignedModulus (bits : Nat) : Nat :=
  2 ^ bits

/-- Wrap an arbitrary integer modulo $2^{\text{bits}}$ into $[0, 2^{\text{bits}})$. -/
@[reducible]
def wrapUnsigned (x : SpecrInt) (bits : Nat) : Nat :=
  Int.toNat (x % (Int.ofNat (2 ^ bits)))

/-- Check whether `x` lies within unsigned range $[0, 2^{\text{bits}})$. -/
@[reducible]
def inUnsignedRange (x : SpecrInt) (bits : Nat) : Bool :=
  decide (0 ≤ x ∧ x < Int.ofNat (2 ^ bits))

/-- Check whether `x` lies within two's-complement signed range $[-2^{\text{bits}-1}, 2^{\text{bits}-1})$. -/
@[reducible]
def inSignedRange (x : SpecrInt) (bits : Nat) : Bool :=
  match bits with
  | 0 => decide (x = 0)
  | k + 1 =>
    let half : Int := Int.ofNat (2 ^ k)
    decide (-half ≤ x ∧ x < half)

/-- Decode a canonical unsigned bit pattern in $[0, 2^{\text{bits}})$ as two's-complement signed `Int`. -/
@[reducible]
def toSigned (unsignedBits : Nat) (bitWidth : Nat) : SpecrInt :=
  match bitWidth with
  | 0 => 0
  | k + 1 =>
    let half := 2 ^ k
    let full := 2 ^ (k + 1)
    if unsignedBits < half then
      Int.ofNat unsignedBits
    else
      Int.ofNat unsignedBits - Int.ofNat full

/-- Encode a signed integer `x` into its canonical unsigned bit pattern modulo $2^{\text{bits}}$. -/
@[reducible]
def ofSigned (x : SpecrInt) (bitWidth : Nat) : Nat :=
  (x % Int.ofNat (2 ^ bitWidth)).toNat

theorem unsignedModulus_pos (bits : Nat) : 0 < unsignedModulus bits := by
  exact Nat.two_pow_pos bits

theorem toSigned_nonneg_of_lt_half (u k : Nat) (h : u < 2 ^ k) :
    0 ≤ toSigned u (k + 1) := by
  simp [toSigned, h]

theorem toSigned_zero (bitWidth : Nat) :
    toSigned 0 bitWidth = 0 := by
  cases bitWidth with
  | zero => rfl
  | succ k =>
    have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
    simp [toSigned, hpos]

end SpecrInt

/-! ## 2. Power-of-Two Byte Alignment (`libspecr::Align`) -/

/-- Power-of-two byte alignment $2^{\text{exp}}$ matching `libspecr::Align`. -/
structure Align : Type where
  /-- Base-2 exponent of the alignment in bytes (`bytes = 2 ^ exp`). -/
  exp : Nat
  deriving DecidableEq, Repr

namespace Align

/-- 1-byte alignment ($2^0 = 1$). -/
@[reducible] def one : Align := ⟨0⟩
/-- 2-byte alignment ($2^1 = 2$). -/
@[reducible] def two : Align := ⟨1⟩
/-- 4-byte alignment ($2^2 = 4$). -/
@[reducible] def four : Align := ⟨2⟩
/-- 8-byte alignment ($2^3 = 8$). -/
@[reducible] def eight : Align := ⟨3⟩
/-- 16-byte alignment ($2^4 = 16$). -/
@[reducible] def sixteen : Align := ⟨4⟩

/-- Concrete alignment in bytes ($2^{\text{exp}} > 0$). -/
@[reducible]
def bytes (a : Align) : Nat :=
  2 ^ a.exp

/-- Concrete alignment in bits ($8 \cdot 2^{\text{exp}}$). -/
@[reducible]
def bits (a : Align) : Nat :=
  8 * a.bytes

/-- Test whether byte address `addr` is aligned to `a`. -/
@[reducible]
def isAligned (addr : Nat) (a : Align) : Bool :=
  addr % a.bytes == 0

/-- Maximum of two alignments (`max a₁ a₂`). -/
@[reducible]
def maxAlign (a₁ a₂ : Align) : Align :=
  ⟨Nat.max a₁.exp a₂.exp⟩

theorem bytes_pos (a : Align) : 0 < a.bytes := by
  exact Nat.two_pow_pos a.exp

theorem isAligned_iff_mod_eq_zero (addr : Nat) (a : Align) :
    isAligned addr a = true ↔ addr % a.bytes = 0 := by
  simp [isAligned]

theorem isAligned_zero (a : Align) : isAligned 0 a = true := by
  simp [isAligned, Align.bytes]

theorem isAligned_mul_self (k : Nat) (a : Align) :
    isAligned (k * a.bytes) a = true := by
  simp [isAligned, Nat.mul_mod_left]

theorem isAligned_one (addr : Nat) : isAligned addr Align.one = true := by
  rw [isAligned_iff_mod_eq_zero]
  exact Nat.mod_one addr

theorem isAligned_add (x y : Nat) (a : Align)
    (hx : isAligned x a = true) (hy : isAligned y a = true) :
    isAligned (x + y) a = true := by
  rw [isAligned_iff_mod_eq_zero] at hx hy ⊢
  rw [Nat.add_mod, hx, hy]
  simp

end Align

/-! ## 3. Non-Negative Byte/Bit Sizes (`libspecr::Size`) & Offsets (`libspecr::Offset`) -/

/-- Non-negative size in bytes matching `libspecr::Size`. -/
structure Size : Type where
  /-- Number of bytes. -/
  bytes : Nat
  deriving DecidableEq, Repr

namespace Size

@[reducible] def zero : Size := ⟨0⟩

@[reducible] def fromBytes (n : Nat) : Size := ⟨n⟩

@[reducible] def bits (s : Size) : Nat := s.bytes * 8

@[reducible] def fromBitsExact (b : Nat) : Option Size :=
  if b % 8 == 0 then some ⟨b / 8⟩ else none

@[reducible] def add (s₁ s₂ : Size) : Size := ⟨s₁.bytes + s₂.bytes⟩

/-- Round `s.bytes` up to the next multiple of `a.bytes`. -/
@[reducible]
def alignTo (s : Size) (a : Align) : Size :=
  let rem := s.bytes % a.bytes
  if rem == 0 then s else ⟨s.bytes + (a.bytes - rem)⟩

theorem bits_eq_mul_eight (s : Size) : s.bits = s.bytes * 8 := rfl

theorem fromBitsExact_bits (s : Size) :
    fromBitsExact s.bits = some s := by
  cases s with | mk n =>
  have hdiv : (n * 8) / 8 = n := by omega
  simp [fromBitsExact, bits, hdiv]

theorem add_bytes (s₁ s₂ : Size) : (add s₁ s₂).bytes = s₁.bytes + s₂.bytes := rfl

theorem add_bits_distrib (s₁ s₂ : Size) :
    (add s₁ s₂).bits = s₁.bits + s₂.bits := by
  simp [bits, Nat.add_mul]

end Size

/-- Signed byte offset matching `libspecr::Offset`. -/
structure Offset : Type where
  /-- Signed offset in bytes. -/
  bytes : SpecrInt
  deriving DecidableEq, Repr

/-- Target byte ordering matching `libspecr::Endianness`. -/
inductive Endianness : Type where
  | little
  | big
  deriving DecidableEq, Repr

/-! ## 4. Transparent Value-Semantic Wrapper Erasure (`GcCow α := α`) -/

/--
In upstream `specr lang`, `GcCow<T>` wraps recursive types so Rust accepts them as
`Copy` persistent values. In Lean 4, inductive types are natively persistent and
value-semantic, so `GcCow` erases transparently to the identity type constructor.
-/
abbrev GcCow (α : Type u) : Type u := α

namespace GcCow

@[reducible] def new {α : Type u} (x : α) : GcCow α := x
@[reducible] def extract {α : Type u} (x : GcCow α) : α := x

theorem extract_new {α : Type u} (x : α) : extract (new x) = x := rfl
theorem new_extract {α : Type u} (x : GcCow α) : new (extract x) = x := rfl

end GcCow

/-! ## 5. Persistent Specr Collections (`SpecrList`, `SpecrMap`, `SpecrSet`) -/

/-- Value-semantic list matching `libspecr::List<T>`. -/
abbrev SpecrList (α : Type u) : Type u := List α

/-- Computable finite map matching `libspecr::Map<K, V>`. -/
structure SpecrMap (κ : Type) (ν : Type) : Type where
  entries : List (κ × ν)
  deriving DecidableEq, Repr

namespace SpecrMap

@[reducible]
def empty {κ ν : Type} : SpecrMap κ ν := ⟨[]⟩

@[reducible]
def get {κ ν : Type} [DecidableEq κ] (m : SpecrMap κ ν) (k : κ) : Option ν :=
  match m.entries.find? (fun p => decide (p.1 = k)) with
  | some (_, v) => some v
  | none => none

@[reducible]
def insert {κ ν : Type} (m : SpecrMap κ ν) (k : κ) (v : ν) : SpecrMap κ ν :=
  ⟨(k, v) :: m.entries⟩

@[simp]
theorem get_insert_self {κ ν : Type} [DecidableEq κ]
    (m : SpecrMap κ ν) (k : κ) (v : ν) :
    (m.insert k v).get k = some v := by
  simp [get]

@[simp]
theorem get_insert_ne {κ ν : Type} [DecidableEq κ]
    (m : SpecrMap κ ν) {k₁ k₂ : κ} (v : ν) (hne : k₁ ≠ k₂) :
    (m.insert k₁ v).get k₂ = m.get k₂ := by
  simp [get, hne]

end SpecrMap

/-- Computable finite set matching `libspecr::Set<T>`. -/
structure SpecrSet (α : Type) : Type where
  elems : List α
  deriving DecidableEq, Repr

namespace SpecrSet

@[reducible]
def empty {α : Type} : SpecrSet α := ⟨[]⟩

@[reducible]
def contains {α : Type} [DecidableEq α] (s : SpecrSet α) (x : α) : Bool :=
  s.elems.contains x

@[reducible]
def insert {α : Type} (s : SpecrSet α) (x : α) : SpecrSet α :=
  ⟨x :: s.elems⟩

@[reducible]
def union {α : Type} (s₁ s₂ : SpecrSet α) : SpecrSet α :=
  ⟨s₁.elems ++ s₂.elems⟩

@[simp]
theorem contains_insert_self {α : Type} [DecidableEq α]
    (s : SpecrSet α) (x : α) :
    (s.insert x).contains x = true := by
  simp [contains]

end SpecrSet

/-! ## 6. Machine Termination Outcomes & Dual-Mode Nondeterministic Monad (`NdComp`) -/

/--
Machine termination outcomes matching MiniRust's `TerminationInfo` enum.
-/
inductive TerminationInfo : Type where
  /-- Undefined behavior triggered with diagnostic message `msg`. -/
  | ub (msg : String)
  /-- Statically ill-formed MiniRust program (`Wf` check failed). -/
  | illFormed (msg : String)
  /-- Clean machine halt (e.g., normal termination or unwinding stop). -/
  | machineStop
  /-- Thread synchronization deadlock. -/
  | deadlock
  /-- Unfreed allocation detected under leak checking. -/
  | memoryLeak
  deriving DecidableEq, Repr

namespace TerminationInfo

/-- Predicate testing whether termination represents undefined behavior (`ub _`). -/
@[reducible]
def isUb : TerminationInfo → Bool
  | .ub _ => true
  | _ => false

end TerminationInfo

/-- Fallible single-path result alias matching MiniRust's `type Result<T> = std::result::Result<T, TerminationInfo>`. -/
abbrev SpecrResult (α : Type) : Type := Except TerminationInfo α

/--
Inspectable finitary computation tree capturing MiniRust's `NdResult<T>` monad
(`Nondet<Result<T, TerminationInfo>>`) with zero opacity.

Supports both:
1. Relational whole-tree behavior extraction (`NdComp.toPartialBehavior`) into
   `Trusted.Refinement.Partial (Trusted.Refinement.BehaviorSet α)`; and
2. Deterministic seeded execution (`NdComp.evalDet`) for fast `#eval` and kernel
   `by decide` proofs.
-/
inductive NdComp (α : Type) : Type where
  /-- Terminal leaf returning either a value `.ok v` or `.error info`. -/
  | ret (val : Except TerminationInfo α)
  /-- Finitary nondeterministic choice over candidate natural numbers in `domain`. -/
  | pick (domain : List Nat) (k : Nat → NdComp α)

/-- Alias matching upstream `specr lang`'s `NdResult<T>` type constructor name. -/
abbrev NdResult (α : Type) : Type := NdComp α

namespace NdComp

/-- Embed a pure value `a` as `.ret (.ok a)`. -/
@[reducible]
protected def pure {α : Type} (a : α) : NdComp α :=
  .ret (.ok a)

/-- Raise immediate undefined behavior with diagnostic message `msg`. -/
@[reducible]
def throwUb {α : Type} (msg : String) : NdComp α :=
  .ret (.error (.ub msg))

/-- Halt execution cleanly with `.machineStop`. -/
@[reducible]
def throwMachineStop {α : Type} : NdComp α :=
  .ret (.error .machineStop)

/-- Lift an `Except TerminationInfo α` (`Result<T>`) into `NdComp α`. -/
@[reducible]
def liftResult {α : Type} (r : Except TerminationInfo α) : NdComp α :=
  .ret r

/-- Functorial map over the normal return leaves of an `NdComp` tree. -/
def map {α β : Type} (f : α → β) : NdComp α → NdComp β
  | .ret (.ok a) => .ret (.ok (f a))
  | .ret (.error e) => .ret (.error e)
  | .pick domain k => .pick domain (fun n => map f (k n))

/-- Monadic sequential composition (`>>=`) threading errors and nondeterministic choices. -/
def bind {α β : Type} (c : NdComp α) (f : α → NdComp β) : NdComp β :=
  match c with
  | .ret (.ok a) => f a
  | .ret (.error e) => .ret (.error e)
  | .pick domain k => .pick domain (fun n => bind (k n) f)

instance instMonadNdComp : Monad NdComp where
  pure := NdComp.pure
  bind := NdComp.bind
  map := NdComp.map

@[simp]
theorem pure_bind {α β : Type} (a : α) (f : α → NdComp β) :
    NdComp.bind (NdComp.pure a) f = f a := rfl

@[simp]
theorem error_bind {α β : Type} (e : TerminationInfo) (f : α → NdComp β) :
    NdComp.bind (.ret (.error e)) f = .ret (.error e) := rfl

theorem bind_pure {α : Type} (c : NdComp α) :
    NdComp.bind c NdComp.pure = c := by
  induction c with
  | ret r =>
    cases r <;> rfl
  | pick domain k ih =>
    simp only [NdComp.bind]
    congr
    funext n
    exact ih n

theorem bind_assoc {α β γ : Type}
    (c : NdComp α) (f : α → NdComp β) (g : β → NdComp γ) :
    NdComp.bind (NdComp.bind c f) g = NdComp.bind c (fun a => NdComp.bind (f a) g) := by
  induction c with
  | ret r =>
    cases r <;> rfl
  | pick domain k ih =>
    simp only [NdComp.bind]
    congr
    funext n
    exact ih n

theorem map_eq_bind_pure_comp {α β : Type} (f : α → β) (c : NdComp α) :
    NdComp.map f c = NdComp.bind c (fun a => NdComp.pure (f a)) := by
  induction c with
  | ret r =>
    cases r <;> rfl
  | pick domain k ih =>
    simp only [NdComp.map, NdComp.bind]
    congr
    funext n
    exact ih n

/-! ## 7. Relational Path Semantics & Deterministic Seeded Evaluator (`evalDet`) -/

/--
Inductive path reachability relation `ReachesOutcome c out` witnessing that some
valid resolution of nondeterministic choices in `c` terminates at leaf `out`.
-/
inductive ReachesOutcome {α : Type} : NdComp α → Except TerminationInfo α → Prop where
  /-- Direct termination at leaf `.ret out`. -/
  | ret (out : Except TerminationInfo α) :
      ReachesOutcome (.ret out) out
  /-- Nondeterministic choice selecting an element `n ∈ domain`. -/
  | pickMem {domain : List Nat} {k : Nat → NdComp α} {n : Nat}
      {out : Except TerminationInfo α}
      (h_mem : n ∈ domain)
      (h_next : ReachesOutcome (k n) out) :
      ReachesOutcome (.pick domain k) out
  /-- Fallback branch `0` when `domain` is empty (`[]`). -/
  | pickEmpty {k : Nat → NdComp α} {out : Except TerminationInfo α}
      (h_next : ReachesOutcome (k 0) out) :
      ReachesOutcome (.pick [] k) out

/--
Deterministic seeded interpreter traversing one valid nondeterministic path of
`c : NdComp α` selected by `seed : Nat`.
-/
def evalDet {α : Type} (seed : Nat) : NdComp α → Except TerminationInfo α
  | .ret out => out
  | .pick [] k => evalDet (seed / 2 + 1) (k 0)
  | .pick (d :: ds) k =>
    let len := (d :: ds).length
    let idx : Fin len := ⟨seed % len, Nat.mod_lt seed (Nat.zero_lt_succ ds.length)⟩
    let choice := (d :: ds).get idx
    evalDet (seed / len) (k choice)

/--
Every outcome produced by `evalDet seed c` is a valid reachable outcome of the
nondeterministic computation tree `c`.
-/
theorem evalDet_reachesOutcome {α : Type} (seed : Nat) (c : NdComp α) :
    ReachesOutcome c (evalDet seed c) := by
  induction c generalizing seed with
  | ret out =>
    exact ReachesOutcome.ret out
  | pick domain k ih =>
    cases domain with
    | nil =>
      simp only [evalDet]
      exact ReachesOutcome.pickEmpty (ih 0 (seed / 2 + 1))
    | cons d ds =>
      simp only [evalDet]
      have h_mem : (d :: ds).get ⟨seed % (d :: ds).length, Nat.mod_lt seed (Nat.zero_lt_succ ds.length)⟩ ∈ (d :: ds) :=
        List.get_mem (d :: ds) ⟨seed % (d :: ds).length, Nat.mod_lt seed (Nat.zero_lt_succ ds.length)⟩
      exact ReachesOutcome.pickMem h_mem (ih _ (seed / (d :: ds).length))

/-! ## 8. Fundamental Smyth Refinement Bridge into `Trusted.Refinement.Partial` -/

/--
Project a MiniRust `NdComp α` computation tree into Layer 1A's canonical
Smyth-ordered partial behavior domain `Partial (BehaviorSet α)`:

- `defined` holds iff **no** reachable execution path triggers undefined behavior
  (`.error (.ub msg)`). Non-UB stops (`.machineStop`, `.deadlock`, `.memoryLeak`)
  do **not** falsify `defined`.
- When `defined` holds, `val _ v` holds iff `.ok v` is reachable along some valid
  nondeterministic execution path (`ReachesOutcome c (.ok v)`).
-/
def toPartialBehavior {α : Type} (c : NdComp α) :
    Partial (BehaviorSet α) where
  defined := ∀ msg : String, ¬ ReachesOutcome c (.error (.ub msg))
  val _ v := ReachesOutcome c (.ok v)

/--
Exact logical characterization of Smyth refinement (`≤`) between two projected
MiniRust computations in `Trusted.Refinement.Partial (BehaviorSet α)`.
-/
theorem ndComp_refines_iff {α : Type} (c₁ c₂ : NdComp α) :
    toPartialBehavior c₁ ≤ toPartialBehavior c₂ ↔
      ((∀ msg, ¬ ReachesOutcome c₂ (.error (.ub msg))) →
        (∀ msg, ¬ ReachesOutcome c₁ (.error (.ub msg))) ∧
        (∀ v, ReachesOutcome c₁ (.ok v) → ReachesOutcome c₂ (.ok v))) := by
  constructor
  · intro h_le h_def₂
    obtain ⟨h_def₁, h_sub⟩ := h_le h_def₂
    exact ⟨h_def₁, fun v hv => h_sub v hv⟩
  · intro h_imp h_def₂
    obtain ⟨h_def₁, h_sub⟩ := h_imp h_def₂
    exact ⟨h_def₁, fun v hv => h_sub v hv⟩

/--
**Soundness of Deterministic Evaluation (`evalDet_sound_of_defined`)**:
Whenever `(toPartialBehavior c).defined` holds (i.e., `c` is UB-free across all
nondeterministic choices), then for EVERY deterministic seed `s : Nat`:
1. `evalDet s c` never produces `.error (.ub msg)`; and
2. Whenever `evalDet s c = .ok v`, `v` is an admitted behavior in
   `(toPartialBehavior c).val h_def v`.
-/
theorem evalDet_sound_of_defined {α : Type} (c : NdComp α)
    (h_def : (toPartialBehavior c).defined) (s : Nat) :
    (∀ msg : String, evalDet s c ≠ .error (.ub msg)) ∧
    (∀ v : α, evalDet s c = .ok v → (toPartialBehavior c).val h_def v) := by
  have h_reach : ReachesOutcome c (evalDet s c) := evalDet_reachesOutcome s c
  constructor
  · intro msg h_eq
    rw [h_eq] at h_reach
    exact h_def msg h_reach
  · intro v h_eq
    rw [h_eq] at h_reach
    exact h_reach

/--
**Forward Soundness of Unmodeled Features (`top_refines_unsupported`)**:
Any state where Anneal emits `.fail .unsupported` maps to `Partial.ub` (`⊤`) in
`Trusted.Refinement`'s Smyth order `instLEPartial`, which is refined by EVERY
MiniRust computation `toPartialBehavior c`.
-/
theorem top_refines_unsupported {α : Type} (c : NdComp α) :
    toPartialBehavior c ≤ (Partial.ub : Partial (BehaviorSet α)) := by
  intro h_top_def
  exact False.elim h_top_def

/--
**Forward Soundness of Conservative UB (`top_refines_false_positive_ub`)**:
Any state where Anneal conservatively emits `.fail .ub` maps to `Partial.ub` (`⊤`)
in `Trusted.Refinement`'s Smyth order `instLEPartial`, preserving forward
soundness (`toPartialBehavior c ≤ Partial.ub`) for every MiniRust computation `c`.
-/
theorem top_refines_false_positive_ub {α : Type} (c : NdComp α) :
    toPartialBehavior c ≤ (Partial.ub : Partial (BehaviorSet α)) := by
  intro h_top_def
  exact False.elim h_top_def

end NdComp

end MiniRust.LibSpecr
