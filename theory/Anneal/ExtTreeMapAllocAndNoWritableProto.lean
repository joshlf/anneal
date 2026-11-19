import Trusted
import Anneal.Memory
import Anneal.BitValidity
import Std.Data.TreeMap.Raw

/-!
# Prototype: Keyed `UInt64` Extensional Tree-Map Allocation State, `#[rustc_no_writable]` & Static-Temporary Tree Borrows Retags, and Array `Sized` / Auto-Trait VTable / Null-VTable Validity (`ws-proto-ext-treemap-alloc-and-no-writable-retag`)

Track P isolated prototype (`PROTOTYPE_NO_MERGE`) evaluating three upstream operational-semantics
and MIR-extraction mechanisms for Anneal (`leanprover/lean4:v4.34.1`):
1. **Part 1 (`proofs-rs/lean-miri#73`)**: Full-width `UInt64` `MiriAllocId` (`NonZeroU64`) and a
   `Classical.choice`-free quotient-extensional balanced AA-tree map (`ExtTreeMap0`) replacing
   linear-scan `filter`-plus-append tables (`live`, `dead`, `globals`, `issuedIds`, and per-alloc
   `race` clocks), with bidirectional refinement (`AllocWorldRel`), propositional extensionality
   (`KeyedAllocWorld.ext`), and exact Miri deallocation failure ordering (`MemoryState.lean` +
   `AllocationMachine.lean`).
   *Note on `Std.ExtTreeMap` in Lean `v4.34.1`*: `Std.ExtTreeMap.empty`, `Std.ExtTreeMap.insert`,
   and `Std.TreeMap.Raw.WF` pull `Classical.choice` into the kernel axiom closure via
   `Std.DTreeMap.Internal.WF`. `ExtTreeMap0` provides the identical `[TransCmp cmp] [LawfulEqCmp cmp]`
   interface and `ext_getElem?` law using exclusively `{propext, Quot.sound}`.
2. **Part 2 (`AeneasVerif/charon#1619/#1620` + `minirust#295`)**:
   - **2A**: Per-parameter `FnEntryRetagPolicy` (`writableChildWrite` vs. `rustcNoWritable`),
     bridging `Miri.TreeBorrows.RetagPolicy`, `Anneal.Memory.ByteRangePerm`, and
     `Trusted.Rustc.V2026_06_01.MirSemantics.evalStmt` (including `ReservedFrz { conflicted }`
     foreign-read latch behavior, ZST `len = 0` no-op write semantics, and `!Unpin` guard).
   - **2B**: Static-access temporary retag preservation before `&raw const STATIC` with byte-range
     `FreezeVisitor` sensitivity across pure `Freeze`, pure `UnsafeCell` (`AtomicI32`), and mixed
     `(Freeze, UnsafeCell)` composite statics (including inter-field/trailing padding flushing).
3. **Part 3 (`proofs-rs/lean-miri#75/#79/#82`)**:
   - **3A**: Syntactic `[T; N]` `Sized` fast-path in raw-pointer validity before `computeTyLayout`,
     avoiding spurious overflow errors on `*const [u8; usize::MAX]` while preserving safe-reference
     layout checks and slice DST metadata requirements.
   - **3B**: Principal-less auto-trait existential vtables (`dyn Send`, `dyn Send + Sync`) with
     canonicalized `AutoTraitSet` keys, `ExtTreeMap0`-backed `VTableRegistry`, non-collision with
     principal-bearing vtables, and auto-trait upcast soundness.
   - **3C**: Wide `dyn` pointer validation enforcing null/invalid-vtable UB precedence before
     null/dangling/unaligned data-pointer UB, even on `(data = null, vtable = null)`.
-/

set_option autoImplicit false

namespace Anneal.ExtTreeMapAllocAndNoWritableProto

open Std
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Anneal.Memory
open Anneal.BitValidity

instance instDecidableEqMutabilityProto : DecidableEq Mutability
  | .not, .not => isTrue rfl
  | .mut, .mut => isTrue rfl
  | .not, .mut => isFalse (fun h => nomatch h)
  | .mut, .not => isFalse (fun h => nomatch h)

instance instReprMutabilityProto : Repr Mutability where
  reprPrec m _ := match m with | .not => ".not" | .mut => ".mut"

instance instDecidableEqAbstractByteProto : DecidableEq AbstractByte
  | .uninit, .uninit => isTrue rfl
  | .init b₁ p₁, .init b₂ p₂ =>
    if h : b₁ = b₂ ∧ p₁ = p₂ then
      isTrue (by rw [h.1, h.2])
    else
      isFalse (fun heq => by injection heq with hb hp; exact h ⟨hb, hp⟩)
  | .uninit, .init _ _ => isFalse (fun h => nomatch h)
  | .init _ _, .uninit => isFalse (fun h => nomatch h)

instance instReprAbstractByteProto : Repr AbstractByte where
  reprPrec b _ :=
    match b with
    | .uninit => ".uninit"
    | .init v p => s!".init {repr v} {repr p}"

instance instDecidableEqTreeBorrowPermProto : DecidableEq TreeBorrowPerm
  | .cell, .cell => isTrue rfl
  | .reservedFrz c₁, .reservedFrz c₂ =>
    if h : c₁ = c₂ then isTrue (by rw [h])
    else isFalse (fun heq => by injection heq with hc; exact h hc)
  | .reservedIM, .reservedIM => isTrue rfl
  | .unique, .unique => isTrue rfl
  | .frozen, .frozen => isTrue rfl
  | .disabled, .disabled => isTrue rfl
  | .cell, .reservedFrz _ | .cell, .reservedIM | .cell, .unique | .cell, .frozen | .cell, .disabled
  | .reservedFrz _, .cell | .reservedFrz _, .reservedIM | .reservedFrz _, .unique | .reservedFrz _, .frozen | .reservedFrz _, .disabled
  | .reservedIM, .cell | .reservedIM, .reservedFrz _ | .reservedIM, .unique | .reservedIM, .frozen | .reservedIM, .disabled
  | .unique, .cell | .unique, .reservedFrz _ | .unique, .reservedIM | .unique, .frozen | .unique, .disabled
  | .frozen, .cell | .frozen, .reservedFrz _ | .frozen, .reservedIM | .frozen, .unique | .frozen, .disabled
  | .disabled, .cell | .disabled, .reservedFrz _ | .disabled, .reservedIM | .disabled, .unique | .disabled, .frozen =>
    isFalse (fun h => nomatch h)

instance instReprTreeBorrowPermProto : Repr TreeBorrowPerm where
  reprPrec p _ :=
    match p with
    | .cell => ".cell"
    | .reservedFrz c => s!".reservedFrz {repr c}"
    | .reservedIM => ".reservedIM"
    | .unique => ".unique"
    | .frozen => ".frozen"
    | .disabled => ".disabled"

instance instDecidableEqExceptProto {ε α : Type} [DecidableEq ε] [DecidableEq α] :
    DecidableEq (Except ε α)
  | .error e₁, .error e₂ =>
    if h : e₁ = e₂ then isTrue (by rw [h])
    else isFalse (fun heq => by injection heq with he; exact h he)
  | .ok a₁, .ok a₂ =>
    if h : a₁ = a₂ then isTrue (by rw [h])
    else isFalse (fun heq => by injection heq with ha; exact h ha)
  | .error _, .ok _ => isFalse (fun h => nomatch h)
  | .ok _, .error _ => isFalse (fun h => nomatch h)

instance instBEqExceptProto {ε α : Type} [DecidableEq ε] [DecidableEq α] :
    BEq (Except ε α) where
  beq x y := decide (x = y)

/-! ### Constructive `0`-Axiom `TransCmp` & `LawfulEqCmp` for `Nat` and `UInt64`
*(Note: Lean `v4.34.1`'s default `Nat.instTransOrd` / `UInt64.instTransOrd` transitively invoke
`Classical.not_not` via `Init.Data.Ord.Basic`; these high-priority constructive instances eliminate
`Classical.choice` across all `Nat`-, `UInt64`-, `MiriAllocId`-, `AutoTrait`-, and `VTableKey`-keyed
maps.)* -/

private theorem nat_compare_eq_swap (a b : Nat) :
    compare a b = (compare b a).swap := by
  change compareOfLessAndEq a b = (compareOfLessAndEq b a).swap
  unfold compareOfLessAndEq
  split
  · split
    · omega
    · split
      · omega
      · rfl
  · split
    · subst_vars; simp [Ordering.swap]
    · split
      · rfl
      · omega

private theorem nat_compare_isLE_trans {a b c : Nat}
    (h₁ : (compare a b).isLE) (h₂ : (compare b c).isLE) : (compare a c).isLE := by
  have hab : a ≤ b := by
    change (compareOfLessAndEq a b).isLE = true at h₁
    unfold compareOfLessAndEq at h₁
    split at h₁
    · omega
    · split at h₁
      · omega
      · nomatch h₁
  have hbc : b ≤ c := by
    change (compareOfLessAndEq b c).isLE = true at h₂
    unfold compareOfLessAndEq at h₂
    split at h₂
    · omega
    · split at h₂
      · omega
      · nomatch h₂
  change (compareOfLessAndEq a c).isLE = true
  unfold compareOfLessAndEq
  split
  · rfl
  · split
    · rfl
    · omega

private theorem nat_compare_eq_of_compare {a b : Nat} (h : compare a b = .eq) : a = b := by
  change compareOfLessAndEq a b = .eq at h
  unfold compareOfLessAndEq at h
  split at h
  · nomatch h
  · split at h
    · assumption
    · nomatch h

private theorem nat_compare_self (a : Nat) : compare a a = .eq := by
  change compareOfLessAndEq a a = .eq
  unfold compareOfLessAndEq
  split
  · omega
  · simp

instance (priority := 2000) instTransCmpNatConstructive :
    TransCmp (compare : Nat → Nat → Ordering) where
  eq_swap {a b} := nat_compare_eq_swap a b
  isLE_trans := nat_compare_isLE_trans

instance (priority := 2000) instLawfulEqCmpNatConstructive :
    LawfulEqCmp (compare : Nat → Nat → Ordering) where
  eq_of_compare := nat_compare_eq_of_compare
  compare_self {a} := nat_compare_self a

/-! ## Section 1: Full-Width `UInt64` `MiriAllocId` & `0 Classical.choice` `ExtTreeMap0` -/

/-- Full-width nonzero 64-bit allocation identifier (`NonZeroU64`), mirroring
`Miri.Memory.AllocId` (`lean-miri/vendor/Miri/Memory/Identity.lean`). -/
structure MiriAllocId where
  value : UInt64
  nonzero : value ≠ 0
  deriving Repr

namespace MiriAllocId

theorem ext {a b : MiriAllocId} (h : a.value = b.value) : a = b := by
  cases a
  cases b
  subst h
  rfl

instance : DecidableEq MiriAllocId := fun a b =>
  if h : a.value = b.value then
    isTrue (ext h)
  else
    isFalse (fun heq => h (congrArg MiriAllocId.value heq))

instance : BEq MiriAllocId where
  beq a b := Nat.beq a.value.toNat b.value.toNat

instance : LawfulBEq MiriAllocId where
  eq_of_beq h := ext (UInt64.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq (Nat.eq_of_beq_eq_true h)))
  rfl {a} := Nat.beq_refl a.value.toNat

/-- Construct `MiriAllocId` from a raw `UInt64`, rejecting the reserved `0` sentinel. -/
def ofUInt64 (raw : UInt64) : Option MiriAllocId :=
  if h : raw = 0 then none else some ⟨raw, h⟩

@[simp]
theorem ofUInt64_zero : ofUInt64 0 = none := rfl

theorem ofUInt64_eq_some_iff {raw : UInt64} {id : MiriAllocId} :
    ofUInt64 raw = some id ↔ ∃ h : raw ≠ 0, id = ⟨raw, h⟩ := by
  unfold ofUInt64
  split
  · rename_i hzero
    constructor
    · intro h; nomatch h
    · rintro ⟨hne, _⟩; exact absurd hzero hne
  · rename_i hne
    constructor
    · intro h
      injection h with hid
      exact ⟨hne, hid.symm⟩
    · rintro ⟨_, rfl⟩
      rfl

/-- Injective, nonzero bridge to `Trusted.MirAst.AllocId` (`Nat`). -/
def toTrustedAllocId (id : MiriAllocId) : Trusted.Rustc.V2026_06_01.MirAst.AllocId :=
  id.value.toNat

theorem toTrustedAllocId_pos (id : MiriAllocId) : 0 < id.toTrustedAllocId := by
  unfold toTrustedAllocId
  apply Nat.pos_of_ne_zero
  intro hz
  apply id.nonzero
  exact UInt64.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq hz)

theorem toTrustedAllocId_injective {a b : MiriAllocId}
    (h : a.toTrustedAllocId = b.toTrustedAllocId) : a = b :=
  ext (UInt64.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq h))

instance : LT MiriAllocId where
  lt a b := a.value < b.value

instance (a b : MiriAllocId) : Decidable (a < b) :=
  inferInstanceAs (Decidable (a.value < b.value))

instance : Ord MiriAllocId where
  compare a b := compare a.value.toNat b.value.toNat

instance : TransCmp (compare : MiriAllocId → MiriAllocId → Ordering) where
  eq_swap {a b} := nat_compare_eq_swap a.value.toNat b.value.toNat
  isLE_trans := nat_compare_isLE_trans

instance : LawfulEqCmp (compare : MiriAllocId → MiriAllocId → Ordering) where
  eq_of_compare h := toTrustedAllocId_injective (nat_compare_eq_of_compare h)
  compare_self {a} := nat_compare_self a.value.toNat

def one : MiriAllocId := ⟨1, by decide⟩

instance : Inhabited MiriAllocId := ⟨one⟩

end MiriAllocId

/-! ### Constructive Balanced AA-Tree & Quotient-Extensional `ExtTreeMap0` -/

/-- Underlying balanced Arne Andersson (AA) search tree (`O(log n)` height, zero axioms). -/
inductive RawAATree (α : Type) (β : Type) where
  | leaf
  | node (lvl : Nat) (left : RawAATree α β) (key : α) (val : β) (right : RawAATree α β)
  deriving DecidableEq, Repr

namespace RawAATree

def level {α β : Type} : RawAATree α β → Nat
  | .leaf => 0
  | .node lvl _ _ _ _ => lvl

def setLevel {α β : Type} (lvl : Nat) : RawAATree α β → RawAATree α β
  | .leaf => .leaf
  | .node _ l k v r => .node lvl l k v r

/-- In-order key-value sequence of `RawAATree`. -/
def toList {α β : Type} : RawAATree α β → List (α × β)
  | .leaf => []
  | .node _ l k v r => toList l ++ (k, v) :: toList r

@[simp]
theorem toList_leaf {α β : Type} : (leaf : RawAATree α β).toList = [] := rfl

@[simp]
theorem toList_node {α β : Type} (lvl : Nat) (l : RawAATree α β) (k : α) (v : β)
    (r : RawAATree α β) :
    (node lvl l k v r).toList = l.toList ++ (k, v) :: r.toList := rfl

/-- AA right-rotation eliminating a horizontal left link (`llvl == lvl`). -/
def skew {α β : Type} : RawAATree α β → RawAATree α β
  | .node lvl (.node llvl a kx vx b) ky vy c =>
    if Nat.beq llvl lvl then .node lvl a kx vx (.node lvl b ky vy c)
    else .node lvl (.node llvl a kx vx b) ky vy c
  | t => t

/-- AA left-rotation eliminating consecutive horizontal right links (`lvl == rrlvl`). -/
def split {α β : Type} : RawAATree α β → RawAATree α β
  | .node lvl a kx vx (.node rlvl b ky vy (.node rrlvl c kz vz d)) =>
    if Nat.beq lvl rrlvl then .node (lvl + 1) (.node lvl a kx vx b) ky vy (.node rrlvl c kz vz d)
    else .node lvl a kx vx (.node rlvl b ky vy (.node rrlvl c kz vz d))
  | t => t

def decreaseLevel {α β : Type} : RawAATree α β → RawAATree α β
  | .leaf => .leaf
  | .node lvl l k v r =>
    let shouldBe := Nat.min (level l) (level r) + 1
    if shouldBe < lvl then
      let r' := if shouldBe < level r then setLevel shouldBe r else r
      .node shouldBe l k v r'
    else .node lvl l k v r

def skewRight {α β : Type} : RawAATree α β → RawAATree α β
  | .leaf => .leaf
  | .node lvl l k v r => .node lvl l k v (skew r)

def skewRightRight {α β : Type} : RawAATree α β → RawAATree α β
  | .node lvl l k v (.node rlvl rl rk rv rr) =>
    .node lvl l k v (.node rlvl rl rk rv (skew rr))
  | t => t

def splitRight {α β : Type} : RawAATree α β → RawAATree α β
  | .leaf => .leaf
  | .node lvl l k v r => .node lvl l k v (split r)

def rebalanceAfterErase {α β : Type} (t : RawAATree α β) : RawAATree α β :=
  splitRight (split (skewRightRight (skewRight (skew (decreaseLevel t)))))

@[simp]
theorem toList_setLevel {α β : Type} (m : Nat) (t : RawAATree α β) :
    toList (setLevel m t) = toList t := by
  cases t <;> rfl

@[simp]
theorem toList_skew {α β : Type} (t : RawAATree α β) :
    toList (skew t) = toList t := by
  unfold skew
  split
  · split
    · simp [List.append_assoc]
    · rfl
  · rfl

@[simp]
theorem toList_split {α β : Type} (t : RawAATree α β) :
    toList (split t) = toList t := by
  unfold split
  split
  · split
    · simp [List.append_assoc]
    · rfl
  · rfl

@[simp]
theorem toList_decreaseLevel {α β : Type} (t : RawAATree α β) :
    toList (decreaseLevel t) = toList t := by
  cases t with
  | leaf => rfl
  | node lvl l k v r =>
    unfold decreaseLevel
    dsimp only
    split
    · split <;> simp
    · rfl

@[simp]
theorem toList_skewRight {α β : Type} (t : RawAATree α β) :
    toList (skewRight t) = toList t := by
  cases t <;> simp [skewRight]

@[simp]
theorem toList_skewRightRight {α β : Type} (t : RawAATree α β) :
    toList (skewRightRight t) = toList t := by
  unfold skewRightRight
  split <;> simp

@[simp]
theorem toList_splitRight {α β : Type} (t : RawAATree α β) :
    toList (splitRight t) = toList t := by
  cases t <;> simp [splitRight]

@[simp]
theorem toList_rebalanceAfterErase {α β : Type} (t : RawAATree α β) :
    toList (rebalanceAfterErase t) = toList t := by
  simp [rebalanceAfterErase]

/-- Logarithmic binary-search lookup on `RawAATree`. -/
def get? {α β : Type} (cmp : α → α → Ordering) : RawAATree α β → α → Option β
  | .leaf, _ => none
  | .node _ l kx vx r, k =>
    match cmp k kx with
    | .lt => get? cmp l k
    | .eq => some vx
    | .gt => get? cmp r k

/-- Balanced AA-tree insertion replacing any existing entry with `cmp k kx = .eq`. -/
def insert {α β : Type} (cmp : α → α → Ordering) : RawAATree α β → α → β → RawAATree α β
  | .leaf, k, v => .node 1 .leaf k v .leaf
  | .node lvl l kx vx r, k, v =>
    match cmp k kx with
    | .lt => split (skew (.node lvl (insert cmp l k v) kx vx r))
    | .eq => .node lvl l k v r
    | .gt => split (skew (.node lvl l kx vx (insert cmp r k v)))

/-- Extract the minimum `(key, val)` and rebalanced remainder from a non-empty subtree. -/
def popMin {α β : Type} : RawAATree α β → Option (α × β × RawAATree α β)
  | .leaf => none
  | .node _ .leaf k v r => some (k, v, r)
  | .node lvl (.node llvl ll lk lv lr) k v r =>
    match popMin (.node llvl ll lk lv lr) with
    | none => none
    | some (mk, mv, l') => some (mk, mv, rebalanceAfterErase (.node lvl l' k v r))

theorem popMin_node_isSome {α β : Type} (lvl : Nat) (l : RawAATree α β) (k : α) (v : β)
    (r : RawAATree α β) :
    ∃ mk mv t', popMin (.node lvl l k v r) = some (mk, mv, t') ∧
      toList (.node lvl l k v r) = (mk, mv) :: toList t' := by
  induction l generalizing lvl k v r with
  | leaf =>
    exact ⟨k, v, r, by rw [popMin], rfl⟩
  | node llvl ll lk lv lr ih =>
    obtain ⟨mk, mv, l', hpop, hlist⟩ := ih llvl lk lv lr
    refine ⟨mk, mv, rebalanceAfterErase (.node lvl l' k v r), ?_, ?_⟩
    · rw [popMin, hpop]
    · rw [toList_node, hlist, toList_rebalanceAfterErase, toList_node]
      rfl

/-- Balanced AA-tree key deletion. -/
def erase {α β : Type} (cmp : α → α → Ordering) : RawAATree α β → α → RawAATree α β
  | .leaf, _ => .leaf
  | .node lvl l kx vx r, k =>
    match cmp k kx with
    | .lt => rebalanceAfterErase (.node lvl (erase cmp l k) kx vx r)
    | .gt => rebalanceAfterErase (.node lvl l kx vx (erase cmp r k))
    | .eq =>
      match popMin r with
      | none => l
      | some (mk, mv, r') => rebalanceAfterErase (.node lvl l mk mv r')

def size {α β : Type} : RawAATree α β → Nat
  | .leaf => 0
  | .node _ l _ _ r => size l + 1 + size r

theorem size_eq_length_toList {α β : Type} (t : RawAATree α β) :
    t.size = t.toList.length := by
  induction t with
  | leaf => rfl
  | node lvl l k v r ihl ihr =>
    simp [size, ihl, ihr]
    omega

/-- Sorted-list reference specification for `get?`, `insert`, and `erase`. -/
def lookupSorted {α β : Type} (cmp : α → α → Ordering) : List (α × β) → α → Option β
  | [], _ => none
  | (kx, vx) :: rest, k =>
    match cmp k kx with
    | .lt => none
    | .eq => some vx
    | .gt => lookupSorted cmp rest k

def insertSorted {α β : Type} (cmp : α → α → Ordering) : List (α × β) → α → β → List (α × β)
  | [], k, v => [(k, v)]
  | (kx, vx) :: rest, k, v =>
    match cmp k kx with
    | .lt => (k, v) :: (kx, vx) :: rest
    | .eq => (k, v) :: rest
    | .gt => (kx, vx) :: insertSorted cmp rest k v

def eraseSorted {α β : Type} (cmp : α → α → Ordering) : List (α × β) → α → List (α × β)
  | [], _ => []
  | (kx, vx) :: rest, k =>
    match cmp k kx with
    | .lt => (kx, vx) :: rest
    | .eq => rest
    | .gt => (kx, vx) :: eraseSorted cmp rest k

/-- Constructive strict key-ordering invariant (`List.Pairwise` over `cmp p.1 q.1 = .lt`). -/
def StrictlySorted {α β : Type} (cmp : α → α → Ordering) (xs : List (α × β)) : Prop :=
  List.Pairwise (fun p q => cmp p.1 q.1 = .lt) xs

/-- A `RawAATree` is a valid binary search tree iff its in-order list is strictly `cmp`-sorted. -/
def BST {α β : Type} (cmp : α → α → Ordering) (t : RawAATree α β) : Prop :=
  StrictlySorted cmp t.toList

private theorem bst_node_iff {α β : Type} {cmp : α → α → Ordering} [TransCmp cmp]
    {lvl : Nat} {l : RawAATree α β} {k : α} {v : β} {r : RawAATree α β} :
    BST cmp (.node lvl l k v r) ↔
      BST cmp l ∧ BST cmp r ∧
      (∀ p ∈ l.toList, cmp p.1 k = .lt) ∧
      (∀ q ∈ r.toList, cmp k q.1 = .lt) := by
  unfold BST StrictlySorted
  rw [toList_node, List.pairwise_append, List.pairwise_cons]
  constructor
  · rintro ⟨hl, ⟨hkr, hr⟩, hcross⟩
    refine ⟨hl, hr, ?_, hkr⟩
    intro p hp
    exact hcross p hp (k, v) (List.mem_cons_self ..)
  · rintro ⟨hl, hr, hlk, hkr⟩
    refine ⟨hl, ⟨hkr, hr⟩, ?_⟩
    intro p hp q hq
    rcases List.mem_cons.mp hq with rfl | hqr
    · exact hlk p hp
    · exact TransCmp.lt_trans (hlk p hp) (hkr q hqr)

private theorem lookupSorted_none_of_all_gt {α β : Type} {cmp : α → α → Ordering}
    {xs : List (α × β)} {k : α} (h : ∀ q ∈ xs, cmp k q.1 = .lt) :
    lookupSorted cmp xs k = none := by
  cases xs with
  | nil => rfl
  | cons q rest =>
    have hlt : cmp k q.1 = .lt := h q (List.mem_cons_self ..)
    simp [lookupSorted, hlt]

private theorem lookupSorted_append_of_split {α β : Type} {cmp : α → α → Ordering} [TransCmp cmp]
    {ls rs : List (α × β)} {kx : α} {vx : β}
    (hl : ∀ p ∈ ls, cmp p.1 kx = .lt)
    (k : α) :
    lookupSorted cmp (ls ++ (kx, vx) :: rs) k =
      match cmp k kx with
      | .lt => lookupSorted cmp ls k
      | .eq => some vx
      | .gt => lookupSorted cmp rs k := by
  induction ls with
  | nil =>
    cases hck : cmp k kx <;> simp [lookupSorted, hck]
  | cons p rest ih =>
    have hp_lt_kx : cmp p.1 kx = .lt := hl p (List.mem_cons_self ..)
    have hl_rest : ∀ p' ∈ rest, cmp p'.1 kx = .lt :=
      fun p' hp' => hl p' (List.mem_cons_of_mem _ hp')
    cases hck : cmp k kx with
    | lt =>
      simp only [List.cons_append, lookupSorted]
      cases cmp k p.1 with
      | lt => rfl
      | eq => rfl
      | gt =>
        rw [ih hl_rest]
        simp [hck]
    | eq =>
      have hgt : cmp k p.1 = .gt := by
        rw [OrientedCmp.gt_iff_lt]
        exact TransCmp.lt_of_lt_of_eq hp_lt_kx (OrientedCmp.eq_symm hck)
      simp only [List.cons_append, lookupSorted, hgt]
      rw [ih hl_rest]
      simp [hck]
    | gt =>
      have hgt : cmp k p.1 = .gt := by
        rw [OrientedCmp.gt_iff_lt]
        exact TransCmp.lt_trans hp_lt_kx (OrientedCmp.lt_of_gt hck)
      simp only [List.cons_append, lookupSorted, hgt]
      rw [ih hl_rest]
      simp [hck]

theorem get?_eq_lookupSorted {α β : Type} {cmp : α → α → Ordering} [TransCmp cmp]
    (t : RawAATree α β) (hbst : BST cmp t) (k : α) :
    t.get? cmp k = lookupSorted cmp t.toList k := by
  induction t with
  | leaf => rfl
  | node lvl l kx vx r ihl ihr =>
    obtain ⟨hl, hr, hlk, _⟩ := bst_node_iff.mp hbst
    rw [toList_node, lookupSorted_append_of_split hlk k]
    unfold get?
    cases cmp k kx with
    | lt => exact ihl hl
    | eq => rfl
    | gt => exact ihr hr

private theorem insertSorted_append_split {α β : Type} {cmp : α → α → Ordering} [TransCmp cmp]
    {ls rs : List (α × β)} {kx : α} {vx : β}
    (hl : ∀ p ∈ ls, cmp p.1 kx = .lt)
    (k : α) (v : β) :
    insertSorted cmp (ls ++ (kx, vx) :: rs) k v =
      match cmp k kx with
      | .lt => insertSorted cmp ls k v ++ (kx, vx) :: rs
      | .eq => ls ++ (k, v) :: rs
      | .gt => ls ++ (kx, vx) :: insertSorted cmp rs k v := by
  induction ls with
  | nil =>
    cases hck : cmp k kx <;> simp [insertSorted, hck]
  | cons p rest ih =>
    have hp_lt_kx : cmp p.1 kx = .lt := hl p (List.mem_cons_self ..)
    have hl_rest : ∀ p' ∈ rest, cmp p'.1 kx = .lt :=
      fun p' hp' => hl p' (List.mem_cons_of_mem _ hp')
    cases hck : cmp k kx with
    | lt =>
      simp only [List.cons_append, insertSorted]
      cases cmp k p.1 with
      | lt => rfl
      | eq => rfl
      | gt =>
        simp only [List.cons_append]
        congr 1
        rw [ih hl_rest]
        simp [hck]
    | eq =>
      have hgt : cmp k p.1 = .gt := by
        rw [OrientedCmp.gt_iff_lt]
        exact TransCmp.lt_of_lt_of_eq hp_lt_kx (OrientedCmp.eq_symm hck)
      simp only [List.cons_append, insertSorted, hgt]
      congr 1
      rw [ih hl_rest]
      simp [hck]
    | gt =>
      have hgt : cmp k p.1 = .gt := by
        rw [OrientedCmp.gt_iff_lt]
        exact TransCmp.lt_trans hp_lt_kx (OrientedCmp.lt_of_gt hck)
      simp only [List.cons_append, insertSorted, hgt]
      congr 1
      rw [ih hl_rest]
      simp [hck]

private theorem mem_insertSorted {α β : Type} {cmp : α → α → Ordering}
    {xs : List (α × β)} {k : α} {v : β} {p : α × β}
    (hm : p ∈ insertSorted cmp xs k v) :
    p = (k, v) ∨ p ∈ xs := by
  induction xs with
  | nil =>
    simp [insertSorted] at hm
    exact .inl hm
  | cons q rest ih =>
    unfold insertSorted at hm
    split at hm
    · rcases List.mem_cons.mp hm with rfl | hrest
      · exact .inl rfl
      · exact .inr hrest
    · rcases List.mem_cons.mp hm with rfl | hrest
      · exact .inl rfl
      · exact .inr (List.mem_cons_of_mem _ hrest)
    · rcases List.mem_cons.mp hm with rfl | hrest
      · exact .inr (List.mem_cons_self ..)
      · rcases ih hrest with rfl | hmem
        · exact .inl rfl
        · exact .inr (List.mem_cons_of_mem _ hmem)

private theorem strictlySorted_insertSorted {α β : Type} {cmp : α → α → Ordering} [TransCmp cmp]
    {xs : List (α × β)} (hxs : StrictlySorted cmp xs) (k : α) (v : β) :
    StrictlySorted cmp (insertSorted cmp xs k v) := by
  induction xs with
  | nil =>
    simp [insertSorted, StrictlySorted]
  | cons q rest ih =>
    obtain ⟨hq_rest, hrest⟩ := List.pairwise_cons.mp hxs
    unfold insertSorted
    cases hcq : cmp k q.1 with
    | lt =>
      rw [StrictlySorted, List.pairwise_cons]
      refine ⟨?_, hxs⟩
      intro p hp
      rcases List.mem_cons.mp hp with rfl | hp_rest
      · exact hcq
      · exact TransCmp.lt_trans hcq (hq_rest p hp_rest)
    | eq =>
      rw [StrictlySorted, List.pairwise_cons]
      refine ⟨?_, hrest⟩
      intro p hp
      exact TransCmp.lt_of_eq_of_lt hcq (hq_rest p hp)
    | gt =>
      rw [StrictlySorted, List.pairwise_cons]
      refine ⟨?_, ih hrest⟩
      intro p hp
      rcases mem_insertSorted hp with rfl | hp_rest
      · exact OrientedCmp.lt_of_gt hcq
      · exact hq_rest p hp_rest

theorem toList_insert {α β : Type} {cmp : α → α → Ordering} [TransCmp cmp]
    (t : RawAATree α β) (hbst : BST cmp t) (k : α) (v : β) :
    (t.insert cmp k v).toList = insertSorted cmp t.toList k v := by
  induction t with
  | leaf => rfl
  | node lvl l kx vx r ihl ihr =>
    obtain ⟨hl, hr, hlk, _⟩ := bst_node_iff.mp hbst
    rw [toList_node, insertSorted_append_split hlk k v]
    unfold insert
    cases cmp k kx with
    | lt => simp [ihl hl]
    | eq => simp
    | gt => simp [ihr hr]

theorem bst_insert {α β : Type} {cmp : α → α → Ordering} [TransCmp cmp]
    (t : RawAATree α β) (hbst : BST cmp t) (k : α) (v : β) :
    BST cmp (t.insert cmp k v) := by
  unfold BST
  rw [toList_insert t hbst k v]
  exact strictlySorted_insertSorted hbst k v

private theorem eraseSorted_append_split {α β : Type} {cmp : α → α → Ordering} [TransCmp cmp]
    {ls rs : List (α × β)} {kx : α} {vx : β}
    (hl : ∀ p ∈ ls, cmp p.1 kx = .lt)
    (k : α) :
    eraseSorted cmp (ls ++ (kx, vx) :: rs) k =
      match cmp k kx with
      | .lt => eraseSorted cmp ls k ++ (kx, vx) :: rs
      | .eq => ls ++ rs
      | .gt => ls ++ (kx, vx) :: eraseSorted cmp rs k := by
  induction ls with
  | nil =>
    cases hck : cmp k kx <;> simp [eraseSorted, hck]
  | cons p rest ih =>
    have hp_lt_kx : cmp p.1 kx = .lt := hl p (List.mem_cons_self ..)
    have hl_rest : ∀ p' ∈ rest, cmp p'.1 kx = .lt :=
      fun p' hp' => hl p' (List.mem_cons_of_mem _ hp')
    cases hck : cmp k kx with
    | lt =>
      simp only [List.cons_append, eraseSorted]
      cases cmp k p.1 with
      | lt => rfl
      | eq => rfl
      | gt =>
        simp only [List.cons_append]
        congr 1
        rw [ih hl_rest]
        simp [hck]
    | eq =>
      have hgt : cmp k p.1 = .gt := by
        rw [OrientedCmp.gt_iff_lt]
        exact TransCmp.lt_of_lt_of_eq hp_lt_kx (OrientedCmp.eq_symm hck)
      simp only [List.cons_append, eraseSorted, hgt]
      congr 1
      rw [ih hl_rest]
      simp [hck]
    | gt =>
      have hgt : cmp k p.1 = .gt := by
        rw [OrientedCmp.gt_iff_lt]
        exact TransCmp.lt_trans hp_lt_kx (OrientedCmp.lt_of_gt hck)
      simp only [List.cons_append, eraseSorted, hgt]
      congr 1
      rw [ih hl_rest]
      simp [hck]

private theorem mem_eraseSorted_subset {α β : Type} {cmp : α → α → Ordering}
    {xs : List (α × β)} {k : α} {p : α × β}
    (hm : p ∈ eraseSorted cmp xs k) : p ∈ xs := by
  induction xs with
  | nil => nomatch hm
  | cons q rest ih =>
    unfold eraseSorted at hm
    split at hm
    · exact hm
    · exact List.mem_cons_of_mem _ hm
    · rcases List.mem_cons.mp hm with rfl | hrest
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (ih hrest)

private theorem strictlySorted_eraseSorted {α β : Type} {cmp : α → α → Ordering}
    {xs : List (α × β)} (hxs : StrictlySorted cmp xs) (k : α) :
    StrictlySorted cmp (eraseSorted cmp xs k) := by
  induction xs with
  | nil => exact hxs
  | cons q rest ih =>
    obtain ⟨hq_rest, hrest⟩ := List.pairwise_cons.mp hxs
    unfold eraseSorted
    split
    · exact hxs
    · exact hrest
    · rw [StrictlySorted, List.pairwise_cons]
      refine ⟨?_, ih hrest⟩
      intro p hp
      exact hq_rest p (mem_eraseSorted_subset hp)

theorem toList_erase {α β : Type} {cmp : α → α → Ordering} [TransCmp cmp]
    (t : RawAATree α β) (hbst : BST cmp t) (k : α) :
    (t.erase cmp k).toList = eraseSorted cmp t.toList k := by
  induction t with
  | leaf => rfl
  | node lvl l kx vx r ihl ihr =>
    obtain ⟨hl, hr, hlk, _⟩ := bst_node_iff.mp hbst
    rw [toList_node, eraseSorted_append_split hlk k]
    unfold erase
    cases cmp k kx with
    | lt => simp [ihl hl]
    | gt => simp [ihr hr]
    | eq =>
      cases r with
      | leaf =>
        simp [popMin]
      | node rlvl rl rk rv rr =>
        obtain ⟨mk, mv, r', hpop, hrlist⟩ := popMin_node_isSome rlvl rl rk rv rr
        rw [hpop, toList_rebalanceAfterErase, toList_node, hrlist]

theorem bst_erase {α β : Type} {cmp : α → α → Ordering} [TransCmp cmp]
    (t : RawAATree α β) (hbst : BST cmp t) (k : α) :
    BST cmp (t.erase cmp k) := by
  unfold BST
  rw [toList_erase t hbst k]
  exact strictlySorted_eraseSorted hbst k

theorem lookupSorted_insertSorted {α β : Type} {cmp : α → α → Ordering} [TransCmp cmp]
    {xs : List (α × β)} (hxs : StrictlySorted cmp xs) (k : α) (v : β) (a : α) :
    lookupSorted cmp (insertSorted cmp xs k v) a =
      if cmp k a = .eq then some v else lookupSorted cmp xs a := by
  induction xs with
  | nil =>
    simp only [insertSorted, lookupSorted]
    cases hca : cmp a k with
    | lt =>
      have hka : cmp k a = .gt := OrientedCmp.gt_of_lt hca
      simp [hka]
    | eq =>
      have hka : cmp k a = .eq := OrientedCmp.eq_symm hca
      simp [hka]
    | gt =>
      have hka : cmp k a = .lt := OrientedCmp.lt_of_gt hca
      simp [hka]
  | cons q rest ih =>
    obtain ⟨hq_rest, hrest⟩ := List.pairwise_cons.mp hxs
    unfold insertSorted
    cases hkq : cmp k q.1 with
    | lt =>
      simp only [lookupSorted]
      cases hak : cmp a k with
      | lt =>
        have haq : cmp a q.1 = .lt := TransCmp.lt_trans hak hkq
        have hka : cmp k a = .gt := OrientedCmp.gt_of_lt hak
        simp [haq, hka]
      | eq =>
        have hka : cmp k a = .eq := OrientedCmp.eq_symm hak
        simp [hka]
      | gt =>
        have hka : cmp k a = .lt := OrientedCmp.lt_of_gt hak
        simp [hka]
    | eq =>
      simp only [lookupSorted]
      have hcongr : cmp a k = cmp a q.1 := TransCmp.congr_right hkq
      rw [hcongr]
      cases haq : cmp a q.1 with
      | lt =>
        have hka : cmp k a = .gt := by
          rw [← hcongr] at haq
          exact OrientedCmp.gt_of_lt haq
        simp [hka]
      | eq =>
        have hka : cmp k a = .eq := by
          rw [← hcongr] at haq
          exact OrientedCmp.eq_symm haq
        simp [hka]
      | gt =>
        have hka : cmp k a = .lt := by
          rw [← hcongr] at haq
          exact OrientedCmp.lt_of_gt haq
        simp [hka]
    | gt =>
      simp only [lookupSorted]
      cases haq : cmp a q.1 with
      | lt =>
        have hka : cmp k a = .gt :=
          OrientedCmp.gt_of_lt (TransCmp.lt_trans haq (OrientedCmp.lt_of_gt hkq))
        simp [hka]
      | eq =>
        have hka : cmp k a = .gt := by
          have hqk : cmp q.1 k = .lt := OrientedCmp.lt_of_gt hkq
          exact OrientedCmp.gt_of_lt (TransCmp.lt_of_eq_of_lt haq hqk)
        simp [hka]
      | gt =>
        exact ih hrest

theorem lookupSorted_eraseSorted {α β : Type} {cmp : α → α → Ordering} [TransCmp cmp]
    {xs : List (α × β)} (hxs : StrictlySorted cmp xs) (k a : α) :
    lookupSorted cmp (eraseSorted cmp xs k) a =
      if cmp k a = .eq then none else lookupSorted cmp xs a := by
  induction xs with
  | nil =>
    simp [eraseSorted, lookupSorted]
  | cons q rest ih =>
    obtain ⟨hq_rest, hrest⟩ := List.pairwise_cons.mp hxs
    unfold eraseSorted
    cases hkq : cmp k q.1 with
    | lt =>
      simp only [lookupSorted]
      cases haq : cmp a q.1 with
      | lt =>
        cases cmp k a <;> simp
      | eq =>
        have hka : cmp k a = .lt := TransCmp.lt_of_lt_of_eq hkq (OrientedCmp.eq_symm haq)
        simp [hka]
      | gt =>
        have hka : cmp k a = .lt := TransCmp.lt_trans hkq (OrientedCmp.lt_of_gt haq)
        simp [hka]
    | eq =>
      have hcongr : cmp a k = cmp a q.1 := TransCmp.congr_right hkq
      cases haq : cmp a q.1 with
      | lt =>
        have hka : cmp k a = .gt := by
          rw [← hcongr] at haq
          exact OrientedCmp.gt_of_lt haq
        have hnone : lookupSorted cmp rest a = none :=
          lookupSorted_none_of_all_gt (fun p hp => TransCmp.lt_trans haq (hq_rest p hp))
        simp [lookupSorted, haq, hka, hnone]
      | eq =>
        have hka : cmp k a = .eq := by
          rw [← hcongr] at haq
          exact OrientedCmp.eq_symm haq
        have hnone : lookupSorted cmp rest a = none :=
          lookupSorted_none_of_all_gt (fun p hp => TransCmp.lt_of_eq_of_lt haq (hq_rest p hp))
        simp [hka, hnone]
      | gt =>
        have hka : cmp k a = .lt := by
          rw [← hcongr] at haq
          exact OrientedCmp.lt_of_gt haq
        simp [lookupSorted, haq, hka]
    | gt =>
      simp only [lookupSorted]
      cases haq : cmp a q.1 with
      | lt =>
        have hka : cmp k a = .gt :=
          OrientedCmp.gt_of_lt (TransCmp.lt_trans haq (OrientedCmp.lt_of_gt hkq))
        simp [hka]
      | eq =>
        have hka : cmp k a = .gt :=
          OrientedCmp.gt_of_lt (TransCmp.lt_of_eq_of_lt haq (OrientedCmp.lt_of_gt hkq))
        simp [hka]
      | gt =>
        exact ih hrest

theorem strictlySorted_eq_of_lookupSorted_eq {α β : Type}
    {cmp : α → α → Ordering} [TransCmp cmp] [LawfulEqCmp cmp]
    {xs ys : List (α × β)} (hxs : StrictlySorted cmp xs) (hys : StrictlySorted cmp ys)
    (hlookup : ∀ k : α, lookupSorted cmp xs k = lookupSorted cmp ys k) :
    xs = ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons q rest =>
      have hq := hlookup q.1
      simp [lookupSorted, ReflCmp.compare_self] at hq
  | cons p xrest ih =>
    obtain ⟨hp_xrest, hxrest⟩ := List.pairwise_cons.mp hxs
    cases ys with
    | nil =>
      have hp := hlookup p.1
      simp [lookupSorted, ReflCmp.compare_self] at hp
    | cons q yrest =>
      obtain ⟨hq_yrest, hyrest⟩ := List.pairwise_cons.mp hys
      cases hpq : cmp p.1 q.1 with
      | lt =>
        have hp := hlookup p.1
        simp [lookupSorted, ReflCmp.compare_self, hpq] at hp
      | gt =>
        have hqp : cmp q.1 p.1 = .lt := OrientedCmp.lt_of_gt hpq
        have hq := hlookup q.1
        simp [lookupSorted, ReflCmp.compare_self, hqp] at hq
      | eq =>
        have hk_eq : p.1 = q.1 := LawfulEqCmp.eq_of_compare hpq
        have hp := hlookup p.1
        cases p with
        | mk pk pv =>
          cases q with
          | mk qk qv =>
            dsimp only at hk_eq
            subst hk_eq
            simp [lookupSorted, ReflCmp.compare_self] at hp
            subst hp
            congr 1
            apply ih hxrest hyrest
            intro k
            cases hkp : cmp k pk with
            | lt =>
              rw [lookupSorted_none_of_all_gt (fun r hr => TransCmp.lt_trans hkp (hp_xrest r hr)),
                lookupSorted_none_of_all_gt (fun r hr => TransCmp.lt_trans hkp (hq_yrest r hr))]
            | eq =>
              rw [lookupSorted_none_of_all_gt (fun r hr => TransCmp.lt_of_eq_of_lt hkp (hp_xrest r hr)),
                lookupSorted_none_of_all_gt (fun r hr => TransCmp.lt_of_eq_of_lt hkp (hq_yrest r hr))]
            | gt =>
              have hk := hlookup k
              simpa [lookupSorted, hkp] using hk

end RawAATree

/-- Well-formed balanced AA-tree bundled with its constructive `BST` proof. -/
abbrev WFAATree (α β : Type) (cmp : α → α → Ordering) :=
  { t : RawAATree α β // RawAATree.BST cmp t }

def wfAATreeSetoid (α β : Type) (cmp : α → α → Ordering) : Setoid (WFAATree α β cmp) where
  r a b := a.val.toList = b.val.toList
  iseqv := ⟨fun _ => rfl, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩

/-- `0 Classical.choice` quotient-extensional ordered tree map (`{propext, Quot.sound}` only),
providing the exact `Std.ExtTreeMap` signature and `ext_get?` / `ext_getElem?` extensionality law. -/
structure ExtTreeMap0 (α : Type) (β : Type) (cmp : α → α → Ordering := by exact compare) where
  inner : Quotient (wfAATreeSetoid α β cmp)

namespace ExtTreeMap0

def empty {α β : Type} {cmp : α → α → Ordering} : ExtTreeMap0 α β cmp :=
  ⟨Quotient.mk (wfAATreeSetoid α β cmp) ⟨.leaf, List.Pairwise.nil⟩⟩

instance {α β : Type} {cmp : α → α → Ordering} : EmptyCollection (ExtTreeMap0 α β cmp) where
  emptyCollection := empty

instance {α β : Type} {cmp : α → α → Ordering} : Inhabited (ExtTreeMap0 α β cmp) := ⟨∅⟩

@[simp]
theorem empty_eq_emptyc {α β : Type} {cmp : α → α → Ordering} :
    (empty : ExtTreeMap0 α β cmp) = ∅ := rfl

def toList {α β : Type} {cmp : α → α → Ordering} (m : ExtTreeMap0 α β cmp) : List (α × β) :=
  Quotient.liftOn m.inner (fun t => t.val.toList) (fun _ _ h => h)

def size {α β : Type} {cmp : α → α → Ordering} (m : ExtTreeMap0 α β cmp) : Nat :=
  Quotient.liftOn m.inner (fun t => t.val.size) (fun a b h => by
    rw [RawAATree.size_eq_length_toList, RawAATree.size_eq_length_toList, h])

def isEmpty {α β : Type} {cmp : α → α → Ordering} (m : ExtTreeMap0 α β cmp) : Bool :=
  Nat.beq m.size 0

def get? {α β : Type} {cmp : α → α → Ordering} [TransCmp cmp]
    (m : ExtTreeMap0 α β cmp) (k : α) : Option β :=
  Quotient.liftOn m.inner (fun t => t.val.get? cmp k) (fun a b h => by
    rw [RawAATree.get?_eq_lookupSorted a.val a.property k,
      RawAATree.get?_eq_lookupSorted b.val b.property k, h])

def contains {α β : Type} {cmp : α → α → Ordering} [TransCmp cmp]
    (m : ExtTreeMap0 α β cmp) (k : α) : Bool :=
  (m.get? k).isSome

instance {α β : Type} {cmp : α → α → Ordering} [TransCmp cmp] :
    Membership α (ExtTreeMap0 α β cmp) where
  mem m k := m.contains k = true

instance {α β : Type} {cmp : α → α → Ordering} [TransCmp cmp]
    {m : ExtTreeMap0 α β cmp} {k : α} : Decidable (k ∈ m) :=
  inferInstanceAs (Decidable (m.contains k = true))

instance {α β : Type} {cmp : α → α → Ordering} [TransCmp cmp] :
    GetElem? (ExtTreeMap0 α β cmp) α β (fun m k => k ∈ m) where
  getElem m k h := (m.get? k).get h
  getElem? m k := m.get? k
  getElem! m k := (m.get? k).get!

def insert {α β : Type} {cmp : α → α → Ordering} [TransCmp cmp]
    (m : ExtTreeMap0 α β cmp) (k : α) (v : β) : ExtTreeMap0 α β cmp :=
  ⟨Quotient.liftOn m.inner
    (fun t => Quotient.mk (wfAATreeSetoid α β cmp)
      ⟨t.val.insert cmp k v, RawAATree.bst_insert t.val t.property k v⟩)
    (fun a b h => Quotient.sound (by
      show (a.val.insert cmp k v).toList = (b.val.insert cmp k v).toList
      rw [RawAATree.toList_insert a.val a.property k v,
        RawAATree.toList_insert b.val b.property k v, h]))⟩

def erase {α β : Type} {cmp : α → α → Ordering} [TransCmp cmp]
    (m : ExtTreeMap0 α β cmp) (k : α) : ExtTreeMap0 α β cmp :=
  ⟨Quotient.liftOn m.inner
    (fun t => Quotient.mk (wfAATreeSetoid α β cmp)
      ⟨t.val.erase cmp k, RawAATree.bst_erase t.val t.property k⟩)
    (fun a b h => Quotient.sound (by
      show (a.val.erase cmp k).toList = (b.val.erase cmp k).toList
      rw [RawAATree.toList_erase a.val a.property k,
        RawAATree.toList_erase b.val b.property k, h]))⟩

@[simp]
theorem getElem?_eq_get? {α β : Type} {cmp : α → α → Ordering} [TransCmp cmp]
    (m : ExtTreeMap0 α β cmp) (k : α) : m[k]? = m.get? k := rfl

@[simp]
theorem get?_empty {α β : Type} {cmp : α → α → Ordering} [TransCmp cmp] (k : α) :
    (∅ : ExtTreeMap0 α β cmp).get? k = none := rfl

@[simp]
theorem size_empty {α β : Type} {cmp : α → α → Ordering} :
    (∅ : ExtTreeMap0 α β cmp).size = 0 := rfl

theorem size_eq_length_toList {α β : Type} {cmp : α → α → Ordering}
    (m : ExtTreeMap0 α β cmp) : m.size = m.toList.length := by
  rcases m with ⟨q⟩
  refine Quotient.inductionOn q (fun t => ?_)
  exact RawAATree.size_eq_length_toList t.val

theorem get?_insert {α β : Type} {cmp : α → α → Ordering} [TransCmp cmp]
    (m : ExtTreeMap0 α β cmp) (k : α) (v : β) (a : α) :
    (m.insert k v).get? a = if cmp k a = .eq then some v else m.get? a := by
  rcases m with ⟨q⟩
  refine Quotient.inductionOn q (fun t => ?_)
  change (t.val.insert cmp k v).get? cmp a = if cmp k a = .eq then some v else t.val.get? cmp a
  rw [RawAATree.get?_eq_lookupSorted _ (RawAATree.bst_insert t.val t.property k v) a,
    RawAATree.toList_insert t.val t.property k v,
    RawAATree.lookupSorted_insertSorted t.property k v a,
    RawAATree.get?_eq_lookupSorted t.val t.property a]

@[simp]
theorem get?_insert_self {α β : Type} {cmp : α → α → Ordering} [TransCmp cmp]
    (m : ExtTreeMap0 α β cmp) (k : α) (v : β) :
    (m.insert k v).get? k = some v := by
  rw [get?_insert]
  simp [ReflCmp.compare_self]

theorem get?_insert_ne {α β : Type} {cmp : α → α → Ordering} [TransCmp cmp] [LawfulEqCmp cmp]
    (m : ExtTreeMap0 α β cmp) {k a : α} (hne : k ≠ a) (v : β) :
    (m.insert k v).get? a = m.get? a := by
  rw [get?_insert]
  have hcmp : cmp k a ≠ .eq := fun hc => hne (LawfulEqCmp.eq_of_compare hc)
  simp [hcmp]

theorem get?_erase {α β : Type} {cmp : α → α → Ordering} [TransCmp cmp]
    (m : ExtTreeMap0 α β cmp) (k a : α) :
    (m.erase k).get? a = if cmp k a = .eq then none else m.get? a := by
  rcases m with ⟨q⟩
  refine Quotient.inductionOn q (fun t => ?_)
  change (t.val.erase cmp k).get? cmp a = if cmp k a = .eq then none else t.val.get? cmp a
  rw [RawAATree.get?_eq_lookupSorted _ (RawAATree.bst_erase t.val t.property k) a,
    RawAATree.toList_erase t.val t.property k,
    RawAATree.lookupSorted_eraseSorted t.property k a,
    RawAATree.get?_eq_lookupSorted t.val t.property a]

@[simp]
theorem get?_erase_self {α β : Type} {cmp : α → α → Ordering} [TransCmp cmp]
    (m : ExtTreeMap0 α β cmp) (k : α) :
    (m.erase k).get? k = none := by
  rw [get?_erase]
  simp [ReflCmp.compare_self]

theorem get?_erase_ne {α β : Type} {cmp : α → α → Ordering} [TransCmp cmp] [LawfulEqCmp cmp]
    (m : ExtTreeMap0 α β cmp) {k a : α} (hne : k ≠ a) :
    (m.erase k).get? a = m.get? a := by
  rw [get?_erase]
  have hcmp : cmp k a ≠ .eq := fun hc => hne (LawfulEqCmp.eq_of_compare hc)
  simp [hcmp]

theorem contains_eq_isSome_get? {α β : Type} {cmp : α → α → Ordering} [TransCmp cmp]
    (m : ExtTreeMap0 α β cmp) (k : α) :
    m.contains k = (m.get? k).isSome := rfl

theorem toList_inj {α β : Type} {cmp : α → α → Ordering}
    {m₁ m₂ : ExtTreeMap0 α β cmp} :
    m₁.toList = m₂.toList ↔ m₁ = m₂ := by
  rcases m₁ with ⟨q₁⟩
  rcases m₂ with ⟨q₂⟩
  refine Quotient.inductionOn₂ q₁ q₂ (fun t₁ t₂ => ?_)
  constructor
  · intro h
    exact congrArg ExtTreeMap0.mk (Quotient.sound h)
  · intro h
    injection h with hq
    exact Quotient.exact hq

/-- **Propositional Map Extensionality (`ExtTreeMap0.ext_get?`)**: two `ExtTreeMap0` maps with
identical pointwise lookups are propositionally equal (`m₁ = m₂`), eliminating order-dependent
list/array permutation invariants without `Classical.choice`. -/
theorem ext_get? {α β : Type} {cmp : α → α → Ordering} [TransCmp cmp] [LawfulEqCmp cmp]
    {m₁ m₂ : ExtTreeMap0 α β cmp} (h : ∀ k : α, m₁.get? k = m₂.get? k) : m₁ = m₂ := by
  rcases m₁ with ⟨q₁⟩
  rcases m₂ with ⟨q₂⟩
  revert h
  refine Quotient.inductionOn₂ q₁ q₂ (fun t₁ t₂ h => ?_)
  apply congrArg ExtTreeMap0.mk
  apply Quotient.sound
  apply RawAATree.strictlySorted_eq_of_lookupSorted_eq t₁.property t₂.property
  intro k
  rw [← RawAATree.get?_eq_lookupSorted t₁.val t₁.property k,
    ← RawAATree.get?_eq_lookupSorted t₂.val t₂.property k]
  exact h k

theorem ext_getElem? {α β : Type} {cmp : α → α → Ordering} [TransCmp cmp] [LawfulEqCmp cmp]
    {m₁ m₂ : ExtTreeMap0 α β cmp} (h : ∀ k : α, m₁[k]? = m₂[k]?) : m₁ = m₂ :=
  ext_get? h

theorem insert_insert_same {α β : Type} {cmp : α → α → Ordering} [TransCmp cmp] [LawfulEqCmp cmp]
    (m : ExtTreeMap0 α β cmp) (k : α) (v₁ v₂ : β) :
    (m.insert k v₁).insert k v₂ = m.insert k v₂ := by
  apply ext_get?
  intro a
  rw [get?_insert, get?_insert, get?_insert]
  split <;> rfl

theorem erase_insert_self_of_none {α β : Type} {cmp : α → α → Ordering}
    [TransCmp cmp] [LawfulEqCmp cmp]
    (m : ExtTreeMap0 α β cmp) (k : α) (v : β) (hnone : m.get? k = none) :
    (m.insert k v).erase k = m := by
  apply ext_get?
  intro a
  rw [get?_erase, get?_insert]
  split
  · rename_i heq
    have hka : k = a := LawfulEqCmp.eq_of_compare heq
    subst hka
    exact hnone.symm
  · rfl

/-- Constructive agreement relation between `ExtTreeMap0` and `Std.TreeMap.Raw` (`0` axioms). -/
def AgreesWithStdRaw {α β : Type} {cmp : α → α → Ordering} [TransCmp cmp]
    (m : ExtTreeMap0 α β cmp) (raw : Std.TreeMap.Raw α β cmp) : Prop :=
  ∀ k : α, m.get? k = raw.get? k

theorem agreesWithStdRaw_empty {α β : Type} {cmp : α → α → Ordering} [TransCmp cmp] :
    AgreesWithStdRaw (∅ : ExtTreeMap0 α β cmp) (Std.TreeMap.Raw.empty : Std.TreeMap.Raw α β cmp) :=
  fun _ => rfl

/-- Multi-step map mutation trace (`[adv A1]`), allowing concrete multi-operation `insert` /
overwrite / `erase` / `get?` trace agreement against `Std.TreeMap.Raw` (`0` axioms) without
importing `Std.TreeMap.Raw.WF` (which pulls `Classical.choice` in `v4.34.1`). -/
inductive MapTraceOp (α β : Type) where
  | insert (k : α) (v : β)
  | erase (k : α)
  deriving DecidableEq, Repr

def execMapTraceExt0 {α β : Type} {cmp : α → α → Ordering} [TransCmp cmp]
    (ops : List (MapTraceOp α β)) : ExtTreeMap0 α β cmp :=
  ops.foldl (fun m op => match op with | .insert k v => m.insert k v | .erase k => m.erase k) ∅

def execMapTraceStdRaw {α β : Type} {cmp : α → α → Ordering} [TransCmp cmp]
    (ops : List (MapTraceOp α β)) : Std.TreeMap.Raw α β cmp :=
  ops.foldl (fun m op => match op with | .insert k v => m.insert k v | .erase k => m.erase k)
    Std.TreeMap.Raw.empty

theorem execMapTraceExt0_snoc_insert {α β : Type} {cmp : α → α → Ordering} [TransCmp cmp]
    [LawfulEqCmp cmp] (ops : List (MapTraceOp α β)) (k a : α) (v : β) :
    (execMapTraceExt0 (cmp := cmp) (ops ++ [.insert k v])).get? a =
      if cmp k a == Ordering.eq then some v else (execMapTraceExt0 (cmp := cmp) ops).get? a := by
  simp only [execMapTraceExt0, List.foldl_append, List.foldl]
  rw [get?_insert]
  cases cmp k a <;> rfl

end ExtTreeMap0

/-! ## Section 2: Part 1 — Keyed `UInt64` Allocation World vs. Linear-Scan World (`lean-miri#73`) -/

/-- Allocation memory-kind tag (`Miri.Memory.MemoryKind`). -/
inductive AllocMemoryKind where
  | stack
  | callerLocation
  | heap
  | globalCache
  deriving DecidableEq, Repr, Inhabited

/-- Compiler global-allocation kind (`Miri.Memory.GlobalAllocationKind`). -/
inductive GlobalAllocKind where
  | function
  | vtable
  | typeId
  | static
  | memory
  deriving DecidableEq, Repr, Inhabited

/-- Live local allocation payload (`Miri.Memory.LocalAllocation`), carrying real `Trusted`
`Mutability` and `AbstractByte` storage. -/
structure LocalAllocEntry where
  kind : AllocMemoryKind
  sizeBytes : UInt64
  alignBytes : UInt64
  mutability : Mutability
  bytes : List AbstractByte := []
  deriving DecidableEq, Repr

/-- Dead-allocation tombstones (`Miri.Memory.DeadAllocation`). -/
structure DeadAllocEntry where
  allocId : MiriAllocId
  sizeBytes : UInt64
  alignBytes : UInt64
  deriving DecidableEq, Repr

/-- Global allocation metadata (`Miri.Memory.GlobalAllocation`). -/
structure GlobalAllocEntry where
  allocId : MiriAllocId
  kind : GlobalAllocKind
  sizeBytes : UInt64
  alignBytes : UInt64
  mutability : Mutability := .not
  deriving DecidableEq, Repr

/-- Per-allocation vector-clock metadata (`Miri.Concurrency.VClockAlloc` in `raceAllocations`).
- `[adv A1]`: `lastReaderThread` tracks the thread of a concurrent read since the last write so
  `raceDeallocVerdict` detects read-vs-deallocate data races even when `actor.thread == writerThread`.
- `[adv A2]`: `extraReaders` tracks additional concurrent reader `(thread, timestamp)` slots from
  `VClockAlloc.read` (`DataRace.lean:254–275`), eliminating single-reader conflation when multiple
  foreign threads read between writes. -/
structure RaceClockEntry where
  writerThread : UInt32
  writeTimestamp : UInt64
  readTimestamp : UInt64
  deallocObserved : Bool := false
  lastReaderThread : Option UInt32 := none
  extraReaders : List (UInt32 × UInt64) := []
  deriving DecidableEq, Repr

/-- Classification returned by `getAllocInfo` (`Miri.Memory.AllocationKind`). -/
inductive AllocInfoKind where
  | liveData
  | function
  | vtable
  | typeId
  | dead
  deriving DecidableEq, Repr

/-- Resolved allocation metadata (`Miri.Memory.AllocationInfo`). -/
structure AllocInfo where
  sizeBytes : UInt64
  alignBytes : UInt64
  kind : AllocInfoKind
  mutability : Mutability
  deriving DecidableEq, Repr

inductive AllocIdErr where
  | exhausted
  | alreadyIssued (allocId : MiriAllocId)
  deriving DecidableEq, Repr

inductive AllocLookupErr where
  | unavailable (allocId : MiriAllocId)
  deriving DecidableEq, Repr

inductive LiveAllocInfoErr where
  | lookup (err : AllocLookupErr)
  | useAfterFree (allocId : MiriAllocId)
  deriving DecidableEq, Repr

/-- Pointer resolved at the deallocation boundary (`Miri.Memory.Pointer (Option Provenance)`). -/
inductive ResolvedDeallocPtr where
  | danglingAddress (addr : UInt64)
  | provenanced (allocId : MiriAllocId) (offsetBytes : UInt64)
  deriving DecidableEq, Repr

/-- Machine `beforeDeallocation` hook outcome (`MemoryState.lean` + `AllocationMachine.lean`):
checks data-race clocks and Tree Borrows protectors *after* `removeLive` has already detached the
allocation from `live`. -/
inductive DeallocHookSpec where
  | ok
  | raceDataRaceFault (writerThread : UInt32) (timestamp : UInt64)
  | protectedBorrowFault (tag : Nat)
  /-- `[adv B2]`: `memoryRaceAccess` found no `raceAllocations` entry although the detector is
  configured — upstream `.invalidProgram "allocation missing vector-clock extra"`. -/
  | missingRaceClock
  deriving DecidableEq, Repr

/-- Deallocating thread's vector-clock view (`[adv B1]`, generalized to per-thread clock components
in `[adv A2]`): `perThreadView` maps foreign thread IDs to the timestamp observed by `actor` in that
thread's vector-clock slot (`thread.clock[tid]`), falling back to `observedTimestamp` when absent. -/
structure DeallocActor where
  thread : UInt32
  observedTimestamp : UInt64
  perThreadView : List (UInt32 × UInt64) := []
  deriving DecidableEq, Repr

/-- Component of `actor`'s vector clock for `targetThread` (`[adv A2]`). -/
def DeallocActor.viewFor (actor : DeallocActor) (targetThread : UInt32) : UInt64 :=
  match actor.perThreadView.find? (fun p => p.1 == targetThread) with
  | some (_, ts) => ts
  | none => actor.observedTimestamp

/-- Data-race detector configuration consulted by `MachineHooks.memoryRaceAccess`
(`MachineHooks.lean:231–237`, `[adv B2]`): `unconfigured` ≙ `machine.dataRace = none`
(`-Zmiri-disable-data-race-detector`: no check at all, no clocks required); `configured detecting`
≙ `machine.dataRace = some global` with `global.raceDetecting = detecting` (false while the program
is single-threaded). Miri's default is `configured`. -/
inductive RaceDetectorMode where
  | unconfigured
  | configured (raceDetecting : Bool)
  deriving DecidableEq, Repr

/-- Scan `extraReaders` for any foreign reader `(rThread, rTs)` not yet observed by `actor`
(`actor.viewFor rThread < rTs`, mirroring `cell.read.le thread.clock` across multi-reader slots in
`DataRace.nonAtomicWriteDetect`, `[adv A2]`). -/
def findExtraReaderRace (actor : DeallocActor) : List (UInt32 × UInt64) → Option (UInt32 × UInt64)
  | [] => none
  | (rThread, rTs) :: rest =>
    if rThread != actor.thread && decide (actor.viewFor rThread < rTs) then
      some (rThread, rTs)
    else
      findExtraReaderRace actor rest

/-- Vector-clock projection of `MachineHooks.memoryRaceAccess … (some .Deallocate)` in
`AllocationMachine.before` (`[adv B1]`, fixed in `[adv A1]`, generalized to per-thread views and
multi-reader `extraReaders` in `[adv A2]`):
`Miri.Concurrency.DataRace.nonAtomicWriteDetect` checks `cell.writeWasBefore thread.clock &&
cell.read.le thread.clock` (`DataRace.lean:439`), comparing each writer/reader thread's timestamp
against `actor`'s component `actor.viewFor tid` for **that specific thread** rather than a single
scalar timestamp shared across all threads. -/
def raceDeallocVerdict (actor : DeallocActor) (clk : RaceClockEntry) : DeallocHookSpec :=
  let writeRaces :=
    clk.writerThread != actor.thread && decide (actor.viewFor clk.writerThread < clk.writeTimestamp)
  let readerThread := clk.lastReaderThread.getD clk.writerThread
  let readRaces :=
    readerThread != actor.thread && decide (actor.viewFor readerThread < clk.readTimestamp)
  if writeRaces then
    .raceDataRaceFault clk.writerThread clk.writeTimestamp
  else if readRaces then
    .raceDataRaceFault readerThread clk.readTimestamp
  else
    match findExtraReaderRace actor clk.extraReaders with
    | some (rThread, rTs) => .raceDataRaceFault rThread rTs
    | none => .ok

/-- Machine deallocation hook in exact `AllocationMachine.before` / `MachineHooks.memoryRaceAccess`
order (`[adv B1]`, ZST-fixed in `[adv A1]`, detector-mode-fixed in `[adv B2]`):
1. `unconfigured` detector (`machine.dataRace = none`): no race check at all → `tb`.
2. Configured detector: the per-allocation entry is looked up *first*; a missing entry is
   `.missingRaceClock` (upstream `invalidProgram "allocation missing vector-clock extra"`) — even for
   a zero-sized allocation. `[adv B2]`: B1/A1 treated a missing entry as race-free (`tb`),
   conflating "detector disabled" with "clock lost".
3. `raceDetecting = false` (single-threaded) → `tb` without consulting clocks.
4. Otherwise the scalar happens-before verdict runs on the *still-present* entry (before
   `raceAllocations` cleanup), except that a zero-sized allocation (`sizeBytes == 0`) checks `0`
   bytes (`DataRace.runRangeLoop`), and only a race-free deallocation proceeds to the Tree Borrows
   protector verdict `tb`. -/
def machineDeallocHook (allocSizeBytes : Option UInt64) (raceEntry : Option RaceClockEntry)
    (actor : DeallocActor) (tb : DeallocHookSpec)
    (mode : RaceDetectorMode := .configured true) : DeallocHookSpec :=
  match mode with
  | .unconfigured => tb
  | .configured detecting =>
    match raceEntry with
    | none => .missingRaceClock
    | some clk =>
      if !detecting || allocSizeBytes == some 0 then
        tb
      else
        match raceDeallocVerdict actor clk with
        | .ok => tb
        | fault => fault

/-- Lifecycle errors for allocation and deallocation (`Miri.Memory.MemoryLifecycleError`). -/
inductive AllocLifecycleErr where
  | allocationIdError (err : AllocIdErr)
  | allocationTooLarge (sizeBytes maxBytes : UInt64)
  | dynamicallyAllocatingGlobal
  | danglingPointer (addr : UInt64)
  | nonzeroAllocationOffset (allocId : MiriAllocId) (offsetBytes : UInt64)
  | globalAllocationDeallocation (allocId : MiriAllocId) (kind : GlobalAllocKind)
  /-- Upstream `MemoryLifecycleError.useAfterFree` (`[adv B1]`, renamed from A0's invented
  `alreadyDeallocated`): reported whenever `id` is absent from both `live` and the global table.
  `deallocatePtrWith` never consults `dead` on this path, so a tombstoned double free, a never-issued
  id, and a GC-pruned tombstone (`pruneDead`) are indistinguishable. -/
  | useAfterFree (allocId : MiriAllocId)
  | immutableAllocation (allocId : MiriAllocId)
  | memoryKindMismatch (allocId : MiriAllocId)
  | layoutMismatch (allocId : MiriAllocId) (actualSize reqSize actualAlign reqAlign : UInt64)
  | hookFailure (reason : String)
  | duplicateDeadAllocation (allocId : MiriAllocId)
  deriving DecidableEq, Repr

/-! ### Linear-Scan List/Filter+Append Allocation World (Pre-`lean-miri#73`) -/

def linearFind? {K V : Type} [BEq K] (rows : List (K × V)) (k : K) : Option V :=
  (rows.find? (fun entry => entry.1 == k)).map Prod.snd

def linearContains {K V : Type} [BEq K] (rows : List (K × V)) (k : K) : Bool :=
  rows.any (fun entry => entry.1 == k)

def linearUpsert {K V : Type} [BEq K] (rows : List (K × V)) (k : K) (v : V) : List (K × V) :=
  (rows.filter (fun old => old.1 != k)) ++ [(k, v)]

def linearErase {K V : Type} [BEq K] (rows : List (K × V)) (k : K) : List (K × V) :=
  rows.filter (fun old => old.1 != k)

/-- Linear-scan allocation world using `filter (· != id)` + append (`push`) across `issuedIds`,
`live`, `dead`, `globals`, and `race` (`lean-miri` prior to PR #73). -/
structure LinearAllocWorld where
  nextAllocId : UInt64 := 1
  idSupplyExhausted : Bool := false
  issuedIds : List (MiriAllocId × Unit) := []
  live : List (MiriAllocId × LocalAllocEntry) := []
  dead : List (MiriAllocId × DeadAllocEntry) := []
  globals : List (MiriAllocId × GlobalAllocEntry) := []
  race : List (MiriAllocId × RaceClockEntry) := []
  deriving DecidableEq, Repr

/-- Keyed `ExtTreeMap0`-backed allocation world (`lean-miri` PR #73, `0 Classical.choice`). -/
structure KeyedAllocWorld where
  nextAllocId : UInt64 := 1
  idSupplyExhausted : Bool := false
  issuedIds : ExtTreeMap0 MiriAllocId Unit := ∅
  live : ExtTreeMap0 MiriAllocId LocalAllocEntry := ∅
  dead : ExtTreeMap0 MiriAllocId DeadAllocEntry := ∅
  globals : ExtTreeMap0 MiriAllocId GlobalAllocEntry := ∅
  race : ExtTreeMap0 MiriAllocId RaceClockEntry := ∅

/-- **Propositional Extensionality of `KeyedAllocWorld` (`KeyedAllocWorld.ext`)**: any two keyed
worlds agreeing on scalar supply counters and pointwise table lookups are propositionally equal
(`w₁ = w₂`), eliminating array/list permutation obligations. -/
theorem KeyedAllocWorld.ext {w₁ w₂ : KeyedAllocWorld}
    (hnext : w₁.nextAllocId = w₂.nextAllocId)
    (hexh : w₁.idSupplyExhausted = w₂.idSupplyExhausted)
    (hiss : ∀ id : MiriAllocId, w₁.issuedIds.get? id = w₂.issuedIds.get? id)
    (hlive : ∀ id : MiriAllocId, w₁.live.get? id = w₂.live.get? id)
    (hdead : ∀ id : MiriAllocId, w₁.dead.get? id = w₂.dead.get? id)
    (hglob : ∀ id : MiriAllocId, w₁.globals.get? id = w₂.globals.get? id)
    (hrace : ∀ id : MiriAllocId, w₁.race.get? id = w₂.race.get? id) :
    w₁ = w₂ := by
  cases w₁
  cases w₂
  dsimp only at *
  subst hnext hexh
  rw [ExtTreeMap0.ext_get? hiss,
    ExtTreeMap0.ext_get? hlive,
    ExtTreeMap0.ext_get? hdead,
    ExtTreeMap0.ext_get? hglob,
    ExtTreeMap0.ext_get? hrace]

/-! ### Linear Helper Lemmas -/

private theorem linearFind?_filter_not_beq {K V : Type} [BEq K] [LawfulBEq K] [DecidableEq K]
    (rows : List (K × V)) (k a : K) :
    linearFind? (rows.filter (fun old => old.1 != k)) a =
      if k = a then none else linearFind? rows a := by
  induction rows with
  | nil =>
    split <;> rfl
  | cons hd tl ih =>
    unfold linearFind? at ih ⊢
    by_cases hka : k = a
    · subst hka
      simp only [↓reduceIte] at ih ⊢
      cases hhk : hd.1 != k with
      | false =>
        rw [List.filter, hhk]
        exact ih
      | true =>
        have hne : hd.1 ≠ k := bne_iff_ne.mp hhk
        have hbeq : (hd.1 == k) = false := beq_false_of_ne hne
        rw [List.filter, hhk, List.find?, hbeq]
        exact ih
    · simp only [hka, ↓reduceIte] at ih ⊢
      cases hhk : hd.1 != k with
      | false =>
        have hbeq_hk : (hd.1 == k) = true := by
          cases h : hd.1 == k with
          | true => rfl
          | false => simp [bne, h] at hhk
        have heq : hd.1 = k := eq_of_beq hbeq_hk
        have hbeq_ha : (hd.1 == a) = false := beq_false_of_ne (fun h => hka (heq.symm.trans h))
        rw [List.filter, hhk, List.find?, hbeq_ha]
        exact ih
      | true =>
        rw [List.filter, hhk]
        dsimp only [↓reduceIte, List.find?]
        cases hd.1 == a with
        | false => exact ih
        | true => rfl

private theorem linearFind?_append_singleton_of_none {K V : Type} [BEq K] [LawfulBEq K] [DecidableEq K]
    (rows : List (K × V)) (k : K) (v : V) (a : K)
    (hnone : k = a → linearFind? rows a = none) :
    linearFind? (rows ++ [(k, v)]) a =
      if k = a then some v else linearFind? rows a := by
  induction rows with
  | nil =>
    unfold linearFind?
    by_cases hka : k = a
    · subst hka; simp
    · have hbeq : (k == a) = false := beq_false_of_ne hka
      simp [hka, hbeq]
  | cons hd tl ih =>
    unfold linearFind? at hnone ih ⊢
    simp only [List.cons_append, List.find?]
    cases hha : hd.1 == a with
    | true =>
      have hne_ka : k ≠ a := by
        intro heq
        have hn := hnone heq
        simp [List.find?, hha] at hn
      simp [hne_ka]
    | false =>
      apply ih
      intro heq
      have hn := hnone heq
      simpa [List.find?, hha] using hn

theorem linearFind?_upsert {K V : Type} [BEq K] [LawfulBEq K] [DecidableEq K]
    (rows : List (K × V)) (k : K) (v : V) (a : K) :
    linearFind? (linearUpsert rows k v) a =
      if k = a then some v else linearFind? rows a := by
  unfold linearUpsert
  rw [linearFind?_append_singleton_of_none]
  · split
    · rfl
    · rename_i hne
      rw [linearFind?_filter_not_beq]
      simp [hne]
  · intro hka
    rw [linearFind?_filter_not_beq]
    simp [hka]

theorem linearFind?_linearErase {K V : Type} [BEq K] [LawfulBEq K] [DecidableEq K]
    (rows : List (K × V)) (k a : K) :
    linearFind? (linearErase rows k) a =
      if k = a then none else linearFind? rows a :=
  linearFind?_filter_not_beq rows k a

theorem linearContains_eq_isSome_linearFind? {K V : Type} [BEq K]
    (rows : List (K × V)) (k : K) :
    linearContains rows k = (linearFind? rows k).isSome := by
  induction rows with
  | nil => rfl
  | cons hd tl ih =>
    unfold linearContains linearFind? at ih ⊢
    simp only [List.any_cons, List.find?]
    cases hd.1 == k <;> simp [ih]

/-! ### Operations on `LinearAllocWorld` and `KeyedAllocWorld` -/

namespace LinearAllocWorld

def empty : LinearAllocWorld := {}

def findLive? (w : LinearAllocWorld) (id : MiriAllocId) : Option LocalAllocEntry :=
  linearFind? w.live id

def findDead? (w : LinearAllocWorld) (id : MiriAllocId) : Option DeadAllocEntry :=
  linearFind? w.dead id

def findGlobal? (w : LinearAllocWorld) (id : MiriAllocId) : Option GlobalAllocEntry :=
  linearFind? w.globals id

def findRace? (w : LinearAllocWorld) (id : MiriAllocId) : Option RaceClockEntry :=
  linearFind? w.race id

def hasIssuedId (w : LinearAllocWorld) (id : MiriAllocId) : Bool :=
  linearContains w.issuedIds id

def containsId (w : LinearAllocWorld) (id : MiriAllocId) : Bool :=
  linearContains w.issuedIds id || linearContains w.live id ||
    linearContains w.dead id || linearContains w.globals id

def isAllocLive (w : LinearAllocWorld) (id : MiriAllocId) : Bool :=
  linearContains w.live id || linearContains w.globals id

def getAllocInfo (w : LinearAllocWorld) (id : MiriAllocId) : Except AllocLookupErr AllocInfo :=
  match w.findLive? id with
  | some loc => .ok ⟨loc.sizeBytes, loc.alignBytes, .liveData, loc.mutability⟩
  | none =>
    match w.findGlobal? id with
    | some glob =>
      match glob.kind with
      | .function => .ok ⟨0, 1, .function, .not⟩
      | .vtable => .ok ⟨0, glob.alignBytes, .vtable, .not⟩
      | .typeId => .ok ⟨0, 1, .typeId, .not⟩
      | .static | .memory => .ok ⟨glob.sizeBytes, glob.alignBytes, .liveData, glob.mutability⟩
    | none =>
      match w.findDead? id with
      | some dead => .ok ⟨dead.sizeBytes, dead.alignBytes, .dead, .not⟩
      | none => .error (.unavailable id)

def getLiveAllocSizeAndAlign (w : LinearAllocWorld) (id : MiriAllocId) :
    Except LiveAllocInfoErr (UInt64 × UInt64) :=
  match w.getAllocInfo id with
  | .error e => .error (.lookup e)
  | .ok info =>
    if info.kind == .dead then .error (.useAfterFree id)
    else .ok (info.sizeBytes, info.alignBytes)

def reserveAllocId (w : LinearAllocWorld) :
    LinearAllocWorld × Except AllocIdErr MiriAllocId :=
  if w.idSupplyExhausted then
    (w, .error .exhausted)
  else
    let advanced := { w with nextAllocId := w.nextAllocId + 1 }
    match MiriAllocId.ofUInt64 w.nextAllocId with
    | none => ({ advanced with idSupplyExhausted := true }, .error .exhausted)
    | some id =>
      if w.containsId id then
        (advanced, .error (.alreadyIssued id))
      else
        ({ advanced with issuedIds := linearUpsert w.issuedIds id () }, .ok id)

def insertLive (w : LinearAllocWorld) (id : MiriAllocId) (entry : LocalAllocEntry) :
    LinearAllocWorld :=
  { w with live := linearUpsert w.live id entry }

def removeLive (w : LinearAllocWorld) (id : MiriAllocId) :
    LinearAllocWorld × Option LocalAllocEntry :=
  ({ w with live := linearErase w.live id }, w.findLive? id)

def insertDead (w : LinearAllocWorld) (entry : DeadAllocEntry) : LinearAllocWorld :=
  { w with dead := linearUpsert w.dead entry.allocId entry }

def setRace (w : LinearAllocWorld) (id : MiriAllocId) (entry : RaceClockEntry) : LinearAllocWorld :=
  { w with race := linearUpsert w.race id entry }

def removeRace (w : LinearAllocWorld) (id : MiriAllocId) : LinearAllocWorld :=
  { w with race := linearErase w.race id }

def registerGlobal (w : LinearAllocWorld) (entry : GlobalAllocEntry) : LinearAllocWorld :=
  { w with
    issuedIds := linearUpsert w.issuedIds entry.allocId ()
    globals := linearUpsert w.globals entry.allocId entry }

def updateLiveBytes (w : LinearAllocWorld) (id : MiriAllocId) (bytes : List AbstractByte) :
    Except AllocLookupErr LinearAllocWorld :=
  match w.findLive? id with
  | none => .error (.unavailable id)
  | some entry => .ok (w.insertLive id { entry with bytes := bytes })

def allocate (w : LinearAllocWorld) (entry : LocalAllocEntry) (maxObjectSize : UInt64)
    (initClock : Option RaceClockEntry) :
    LinearAllocWorld × Except AllocLifecycleErr MiriAllocId :=
  if entry.sizeBytes > maxObjectSize then
    (w, .error (.allocationTooLarge entry.sizeBytes maxObjectSize))
  else
    let (wRes, res) := w.reserveAllocId
    match res with
    | .error e => (wRes, .error (.allocationIdError e))
    | .ok id =>
      if entry.kind == .globalCache then
        (wRes, .error .dynamicallyAllocatingGlobal)
      else
        let wLive := wRes.insertLive id entry
        let wFinal := match initClock with
          | none => wLive
          | some clk => wLive.setRace id clk
        (wFinal, .ok id)

def deallocate (w : LinearAllocWorld) (ptr : ResolvedDeallocPtr)
    (reqLayout : Option (UInt64 × UInt64)) (reqKind : AllocMemoryKind)
    (hook : DeallocHookSpec) :
    LinearAllocWorld × Option (MiriAllocId × LocalAllocEntry) × Except AllocLifecycleErr Unit :=
  match ptr with
  | .danglingAddress addr =>
    (w, none, .error (.danglingPointer addr))
  | .provenanced id offsetBytes =>
    if offsetBytes != 0 then
      (w, none, .error (.nonzeroAllocationOffset id offsetBytes))
    else
      let (afterRemove, entry?) := w.removeLive id
      match entry? with
      | none =>
        match w.findGlobal? id with
        | some glob => (w, none, .error (.globalAllocationDeallocation id glob.kind))
        | none => (w, none, .error (.useAfterFree id))
      | some entry =>
        let detached := some (id, entry)
        let afterFailCleanup := afterRemove.removeRace id
        if entry.mutability == .not then
          (afterFailCleanup, detached, .error (.immutableAllocation id))
        else if entry.kind != reqKind then
          (afterFailCleanup, detached, .error (.memoryKindMismatch id))
        else
          let layoutBad := match reqLayout with
            | none => false
            | some (reqSz, reqAl) => reqSz != entry.sizeBytes || reqAl != entry.alignBytes
          if layoutBad then
            match reqLayout with
            | some (reqSz, reqAl) =>
              (afterFailCleanup, detached,
                .error (.layoutMismatch id entry.sizeBytes reqSz entry.alignBytes reqAl))
            | none => (afterFailCleanup, detached, .ok ())
          else
            match hook with
            | .raceDataRaceFault _ _ =>
              (afterFailCleanup, detached, .error (.hookFailure "DataRace"))
            | .protectedBorrowFault _ =>
              (afterFailCleanup, detached, .error (.hookFailure "TreeBorrowsProtectedDealloc"))
            | .missingRaceClock =>
              (afterFailCleanup, detached, .error (.hookFailure "MissingVectorClockExtra"))
            | .ok =>
              let alreadyDead := (afterRemove.findDead? id).isSome
              let deadEntry : DeadAllocEntry := ⟨id, entry.sizeBytes, entry.alignBytes⟩
              let afterDead := (afterRemove.insertDead deadEntry).removeRace id
              if alreadyDead then
                (afterDead, detached, .error (.duplicateDeadAllocation id))
              else
                (afterDead, detached, .ok ())

end LinearAllocWorld

namespace KeyedAllocWorld

def empty : KeyedAllocWorld := {}

def findLive? (w : KeyedAllocWorld) (id : MiriAllocId) : Option LocalAllocEntry :=
  w.live.get? id

def findDead? (w : KeyedAllocWorld) (id : MiriAllocId) : Option DeadAllocEntry :=
  w.dead.get? id

def findGlobal? (w : KeyedAllocWorld) (id : MiriAllocId) : Option GlobalAllocEntry :=
  w.globals.get? id

def findRace? (w : KeyedAllocWorld) (id : MiriAllocId) : Option RaceClockEntry :=
  w.race.get? id

def hasIssuedId (w : KeyedAllocWorld) (id : MiriAllocId) : Bool :=
  w.issuedIds.contains id

def containsId (w : KeyedAllocWorld) (id : MiriAllocId) : Bool :=
  w.issuedIds.contains id || w.live.contains id ||
    w.dead.contains id || w.globals.contains id

def isAllocLive (w : KeyedAllocWorld) (id : MiriAllocId) : Bool :=
  w.live.contains id || w.globals.contains id

def getAllocInfo (w : KeyedAllocWorld) (id : MiriAllocId) : Except AllocLookupErr AllocInfo :=
  match w.findLive? id with
  | some loc => .ok ⟨loc.sizeBytes, loc.alignBytes, .liveData, loc.mutability⟩
  | none =>
    match w.findGlobal? id with
    | some glob =>
      match glob.kind with
      | .function => .ok ⟨0, 1, .function, .not⟩
      | .vtable => .ok ⟨0, glob.alignBytes, .vtable, .not⟩
      | .typeId => .ok ⟨0, 1, .typeId, .not⟩
      | .static | .memory => .ok ⟨glob.sizeBytes, glob.alignBytes, .liveData, glob.mutability⟩
    | none =>
      match w.findDead? id with
      | some dead => .ok ⟨dead.sizeBytes, dead.alignBytes, .dead, .not⟩
      | none => .error (.unavailable id)

def getLiveAllocSizeAndAlign (w : KeyedAllocWorld) (id : MiriAllocId) :
    Except LiveAllocInfoErr (UInt64 × UInt64) :=
  match w.getAllocInfo id with
  | .error e => .error (.lookup e)
  | .ok info =>
    if info.kind == .dead then .error (.useAfterFree id)
    else .ok (info.sizeBytes, info.alignBytes)

def reserveAllocId (w : KeyedAllocWorld) :
    KeyedAllocWorld × Except AllocIdErr MiriAllocId :=
  if w.idSupplyExhausted then
    (w, .error .exhausted)
  else
    let advanced := { w with nextAllocId := w.nextAllocId + 1 }
    match MiriAllocId.ofUInt64 w.nextAllocId with
    | none => ({ advanced with idSupplyExhausted := true }, .error .exhausted)
    | some id =>
      if w.containsId id then
        (advanced, .error (.alreadyIssued id))
      else
        ({ advanced with issuedIds := w.issuedIds.insert id () }, .ok id)

def insertLive (w : KeyedAllocWorld) (id : MiriAllocId) (entry : LocalAllocEntry) :
    KeyedAllocWorld :=
  { w with live := w.live.insert id entry }

def removeLive (w : KeyedAllocWorld) (id : MiriAllocId) :
    KeyedAllocWorld × Option LocalAllocEntry :=
  ({ w with live := w.live.erase id }, w.findLive? id)

def insertDead (w : KeyedAllocWorld) (entry : DeadAllocEntry) : KeyedAllocWorld :=
  { w with dead := w.dead.insert entry.allocId entry }

def setRace (w : KeyedAllocWorld) (id : MiriAllocId) (entry : RaceClockEntry) : KeyedAllocWorld :=
  { w with race := w.race.insert id entry }

def removeRace (w : KeyedAllocWorld) (id : MiriAllocId) : KeyedAllocWorld :=
  { w with race := w.race.erase id }

def registerGlobal (w : KeyedAllocWorld) (entry : GlobalAllocEntry) : KeyedAllocWorld :=
  { w with
    issuedIds := w.issuedIds.insert entry.allocId ()
    globals := w.globals.insert entry.allocId entry }

def updateLiveBytes (w : KeyedAllocWorld) (id : MiriAllocId) (bytes : List AbstractByte) :
    Except AllocLookupErr KeyedAllocWorld :=
  match w.findLive? id with
  | none => .error (.unavailable id)
  | some entry => .ok (w.insertLive id { entry with bytes := bytes })

def allocate (w : KeyedAllocWorld) (entry : LocalAllocEntry) (maxObjectSize : UInt64)
    (initClock : Option RaceClockEntry) :
    KeyedAllocWorld × Except AllocLifecycleErr MiriAllocId :=
  if entry.sizeBytes > maxObjectSize then
    (w, .error (.allocationTooLarge entry.sizeBytes maxObjectSize))
  else
    let (wRes, res) := w.reserveAllocId
    match res with
    | .error e => (wRes, .error (.allocationIdError e))
    | .ok id =>
      if entry.kind == .globalCache then
        (wRes, .error .dynamicallyAllocatingGlobal)
      else
        let wLive := wRes.insertLive id entry
        let wFinal := match initClock with
          | none => wLive
          | some clk => wLive.setRace id clk
        (wFinal, .ok id)

def deallocate (w : KeyedAllocWorld) (ptr : ResolvedDeallocPtr)
    (reqLayout : Option (UInt64 × UInt64)) (reqKind : AllocMemoryKind)
    (hook : DeallocHookSpec) :
    KeyedAllocWorld × Option (MiriAllocId × LocalAllocEntry) × Except AllocLifecycleErr Unit :=
  match ptr with
  | .danglingAddress addr =>
    (w, none, .error (.danglingPointer addr))
  | .provenanced id offsetBytes =>
    if offsetBytes != 0 then
      (w, none, .error (.nonzeroAllocationOffset id offsetBytes))
    else
      let (afterRemove, entry?) := w.removeLive id
      match entry? with
      | none =>
        match w.findGlobal? id with
        | some glob => (w, none, .error (.globalAllocationDeallocation id glob.kind))
        | none => (w, none, .error (.useAfterFree id))
      | some entry =>
        let detached := some (id, entry)
        let afterFailCleanup := afterRemove.removeRace id
        if entry.mutability == .not then
          (afterFailCleanup, detached, .error (.immutableAllocation id))
        else if entry.kind != reqKind then
          (afterFailCleanup, detached, .error (.memoryKindMismatch id))
        else
          let layoutBad := match reqLayout with
            | none => false
            | some (reqSz, reqAl) => reqSz != entry.sizeBytes || reqAl != entry.alignBytes
          if layoutBad then
            match reqLayout with
            | some (reqSz, reqAl) =>
              (afterFailCleanup, detached,
                .error (.layoutMismatch id entry.sizeBytes reqSz entry.alignBytes reqAl))
            | none => (afterFailCleanup, detached, .ok ())
          else
            match hook with
            | .raceDataRaceFault _ _ =>
              (afterFailCleanup, detached, .error (.hookFailure "DataRace"))
            | .protectedBorrowFault _ =>
              (afterFailCleanup, detached, .error (.hookFailure "TreeBorrowsProtectedDealloc"))
            | .missingRaceClock =>
              (afterFailCleanup, detached, .error (.hookFailure "MissingVectorClockExtra"))
            | .ok =>
              let alreadyDead := (afterRemove.findDead? id).isSome
              let deadEntry : DeadAllocEntry := ⟨id, entry.sizeBytes, entry.alignBytes⟩
              let afterDead := (afterRemove.insertDead deadEntry).removeRace id
              if alreadyDead then
                (afterDead, detached, .error (.duplicateDeadAllocation id))
              else
                (afterDead, detached, .ok ())

end KeyedAllocWorld

/-- Mode-aware machine allocation (`AllocationMachine.allocate` + `MachineHooks.memoryRaceAlloc`,
`[adv A2]`): seeds an initial `RaceClockEntry` iff `mode` is `.configured _`, pairing symmetrically
with `deallocateMachine` so configured allocations carry their vector-clock extra while
`unconfigured` allocations omit it. -/
def LinearAllocWorld.allocateMachine (w : LinearAllocWorld) (entry : LocalAllocEntry)
    (maxObjectSize : UInt64) (creatorThread : UInt32) (timestamp : UInt64)
    (mode : RaceDetectorMode := .configured true) :
    LinearAllocWorld × Except AllocLifecycleErr MiriAllocId :=
  let initClk : Option RaceClockEntry :=
    match mode with
    | .unconfigured => none
    | .configured _ =>
      some { writerThread := creatorThread, writeTimestamp := timestamp, readTimestamp := 0 }
  w.allocate entry maxObjectSize initClk

/-- Keyed counterpart of `LinearAllocWorld.allocateMachine` (`[adv A2]`). -/
def KeyedAllocWorld.allocateMachine (w : KeyedAllocWorld) (entry : LocalAllocEntry)
    (maxObjectSize : UInt64) (creatorThread : UInt32) (timestamp : UInt64)
    (mode : RaceDetectorMode := .configured true) :
    KeyedAllocWorld × Except AllocLifecycleErr MiriAllocId :=
  let initClk : Option RaceClockEntry :=
    match mode with
    | .unconfigured => none
    | .configured _ =>
      some { writerThread := creatorThread, writeTimestamp := timestamp, readTimestamp := 0 }
  w.allocate entry maxObjectSize initClk

/-- Machine-level deallocation (`AllocationMachine.deallocate`, `[adv B1]`, ZST-fixed `[adv A1]`):
the hook verdict is *computed* from the world's own live size and per-allocation race entry, read
before any race cleanup, instead of being supplied as an unconstrained parameter. -/
def LinearAllocWorld.deallocateMachine (w : LinearAllocWorld) (ptr : ResolvedDeallocPtr)
    (reqLayout : Option (UInt64 × UInt64)) (reqKind : AllocMemoryKind)
    (actor : DeallocActor) (tb : DeallocHookSpec) (mode : RaceDetectorMode := .configured true) :
    LinearAllocWorld × Option (MiriAllocId × LocalAllocEntry) × Except AllocLifecycleErr Unit :=
  let (szOpt, raceEntry) := match ptr with
    | .provenanced id _ => ((w.findLive? id).map (·.sizeBytes), w.findRace? id)
    | .danglingAddress _ => (none, none)
  w.deallocate ptr reqLayout reqKind (machineDeallocHook szOpt raceEntry actor tb mode)

/-- Keyed counterpart of `LinearAllocWorld.deallocateMachine` (`[adv B1]`, ZST-fixed `[adv A1]`,
detector-mode `[adv B2]`). -/
def KeyedAllocWorld.deallocateMachine (w : KeyedAllocWorld) (ptr : ResolvedDeallocPtr)
    (reqLayout : Option (UInt64 × UInt64)) (reqKind : AllocMemoryKind)
    (actor : DeallocActor) (tb : DeallocHookSpec) (mode : RaceDetectorMode := .configured true) :
    KeyedAllocWorld × Option (MiriAllocId × LocalAllocEntry) × Except AllocLifecycleErr Unit :=
  let (szOpt, raceEntry) := match ptr with
    | .provenanced id _ => ((w.findLive? id).map (·.sizeBytes), w.findRace? id)
    | .danglingAddress _ => (none, none)
  w.deallocate ptr reqLayout reqKind (machineDeallocHook szOpt raceEntry actor tb mode)

/-- Keyed projection of one linear table (`[adv B1]`): `foldr` inserts rows right-to-left, so the
*first* row for each key (the one `linearFind?` returns) is inserted last and wins — reproducing
first-match lookup even on linear tables that carry shadowed duplicate keys. -/
def ofLinearRows {V : Type} (rows : List (MiriAllocId × V)) : ExtTreeMap0 MiriAllocId V :=
  rows.foldr (fun row m => m.insert row.1 row.2) ∅

theorem get?_ofLinearRows {V : Type} (rows : List (MiriAllocId × V)) (a : MiriAllocId) :
    (ofLinearRows rows).get? a = linearFind? rows a := by
  induction rows with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨k, v⟩
    show ((ofLinearRows tl).insert k v).get? a = linearFind? ((k, v) :: tl) a
    rw [ExtTreeMap0.get?_insert, ih]
    by_cases hka : k = a
    · subst hka
      simp [linearFind?, ReflCmp.compare_self]
    · have hcmp : compare k a ≠ .eq := fun h => hka (LawfulEqCmp.eq_of_compare h)
      have hbeq : (k == a) = false := beq_false_of_ne hka
      simp [linearFind?, hcmp, hbeq, List.find?]

private theorem linearFind?_none_of_all_gt {V : Type} {rows : List (MiriAllocId × V)}
    {a : MiriAllocId} (h : ∀ q ∈ rows, compare a q.1 = .lt) : linearFind? rows a = none := by
  induction rows with
  | nil => rfl
  | cons q rest ih =>
    have hq : compare a q.1 = .lt := h q (List.mem_cons_self ..)
    have hne : q.1 ≠ a := by
      intro hqa
      rw [hqa, ReflCmp.compare_self (cmp := compare)] at hq
      nomatch hq
    have hbeq : (q.1 == a) = false := beq_false_of_ne hne
    have ih' := ih (fun q' hq' => h q' (List.mem_cons_of_mem _ hq'))
    unfold linearFind? at ih' ⊢
    simp [List.find?, hbeq, ih']

private theorem lookupSorted_eq_linearFind? {V : Type} :
    ∀ {rows : List (MiriAllocId × V)}, RawAATree.StrictlySorted compare rows →
      ∀ a : MiriAllocId, RawAATree.lookupSorted compare rows a = linearFind? rows a
  | [], _, _ => rfl
  | (kx, vx) :: rest, hs, a => by
    obtain ⟨hhead, hrest⟩ := List.pairwise_cons.mp hs
    unfold RawAATree.lookupSorted
    cases hc : compare a kx with
    | lt =>
      have hall : ∀ q ∈ (kx, vx) :: rest, compare a q.1 = .lt := by
        intro q hq
        rcases List.mem_cons.mp hq with rfl | hq'
        · exact hc
        · exact TransCmp.lt_trans hc (hhead q hq')
      exact (linearFind?_none_of_all_gt hall).symm
    | eq =>
      have hak : a = kx := LawfulEqCmp.eq_of_compare hc
      subst hak
      simp [linearFind?, List.find?]
    | gt =>
      have hne : kx ≠ a := by
        intro hka
        subst hka
        rw [ReflCmp.compare_self (cmp := compare)] at hc
        nomatch hc
      have hbeq : (kx == a) = false := beq_false_of_ne hne
      rw [lookupSorted_eq_linearFind? hrest a]
      simp [linearFind?, List.find?, hbeq]

/-- The canonical sorted `toList` of a keyed table answers `linearFind?` exactly like `get?`
(`[adv B1]`). -/
theorem ExtTreeMap0.linearFind?_toList {V : Type} (m : ExtTreeMap0 MiriAllocId V)
    (a : MiriAllocId) : linearFind? m.toList a = m.get? a := by
  rcases m with ⟨q⟩
  refine Quotient.inductionOn q (fun t => ?_)
  change linearFind? t.val.toList a = t.val.get? compare a
  rw [RawAATree.get?_eq_lookupSorted t.val t.property a]
  exact (lookupSorted_eq_linearFind? (rows := t.val.toList) t.property a).symm

/-- Keyed projection of an arbitrary (possibly duplicate-carrying) linear world (`[adv B1]`). -/
def KeyedAllocWorld.ofLinear (lw : LinearAllocWorld) : KeyedAllocWorld where
  nextAllocId := lw.nextAllocId
  idSupplyExhausted := lw.idSupplyExhausted
  issuedIds := ofLinearRows lw.issuedIds
  live := ofLinearRows lw.live
  dead := ofLinearRows lw.dead
  globals := ofLinearRows lw.globals
  race := ofLinearRows lw.race

/-- Linear (sorted, duplicate-free) image of a keyed world (`[adv B1]`). -/
def LinearAllocWorld.ofKeyed (kw : KeyedAllocWorld) : LinearAllocWorld where
  nextAllocId := kw.nextAllocId
  idSupplyExhausted := kw.idSupplyExhausted
  issuedIds := kw.issuedIds.toList
  live := kw.live.toList
  dead := kw.dead.toList
  globals := kw.globals.toList
  race := kw.race.toList

/-! ### Bidirectional Refinement Relation `AllocWorldRel` & Equivalence Theorems -/

/-- Bidirectional refinement/equivalence relation between `LinearAllocWorld` and
`KeyedAllocWorld`: exact agreement on allocator cursor, exhaustion latch, and pointwise lookups
across `issuedIds`, `live`, `dead`, `globals`, and per-allocation `race` clocks. -/
structure AllocWorldRel (lw : LinearAllocWorld) (kw : KeyedAllocWorld) : Prop where
  nextAllocId_eq : lw.nextAllocId = kw.nextAllocId
  exhausted_eq : lw.idSupplyExhausted = kw.idSupplyExhausted
  issued_eq : ∀ id : MiriAllocId, linearFind? lw.issuedIds id = kw.issuedIds.get? id
  live_eq : ∀ id : MiriAllocId, lw.findLive? id = kw.findLive? id
  dead_eq : ∀ id : MiriAllocId, lw.findDead? id = kw.findDead? id
  globals_eq : ∀ id : MiriAllocId, lw.findGlobal? id = kw.findGlobal? id
  race_eq : ∀ id : MiriAllocId, lw.findRace? id = kw.findRace? id

theorem allocWorldRel_empty : AllocWorldRel LinearAllocWorld.empty KeyedAllocWorld.empty where
  nextAllocId_eq := rfl
  exhausted_eq := rfl
  issued_eq _ := rfl
  live_eq _ := rfl
  dead_eq _ := rfl
  globals_eq _ := rfl
  race_eq _ := rfl

/-- Uniqueness of the `KeyedAllocWorld` refinement partner: any two `KeyedAllocWorld`s related to
the same `LinearAllocWorld` are propositionally equal (`kw₁ = kw₂`). -/
theorem allocWorldRel_keyed_unique {lw : LinearAllocWorld} {kw₁ kw₂ : KeyedAllocWorld}
    (h₁ : AllocWorldRel lw kw₁) (h₂ : AllocWorldRel lw kw₂) : kw₁ = kw₂ :=
  KeyedAllocWorld.ext
    (h₁.nextAllocId_eq.symm.trans h₂.nextAllocId_eq)
    (h₁.exhausted_eq.symm.trans h₂.exhausted_eq)
    (fun id => (h₁.issued_eq id).symm.trans (h₂.issued_eq id))
    (fun id => (h₁.live_eq id).symm.trans (h₂.live_eq id))
    (fun id => (h₁.dead_eq id).symm.trans (h₂.dead_eq id))
    (fun id => (h₁.globals_eq id).symm.trans (h₂.globals_eq id))
    (fun id => (h₁.race_eq id).symm.trans (h₂.race_eq id))

/-- **Totality, Linear → Keyed (`allocWorldRel_ofLinear`, `[adv B1]`)**: *every* linear world —
including ones carrying shadowed duplicate keys that no `filter`+`push` history produces — has a
keyed refinement partner, namely its first-match projection `KeyedAllocWorld.ofLinear`. -/
theorem allocWorldRel_ofLinear (lw : LinearAllocWorld) :
    AllocWorldRel lw (KeyedAllocWorld.ofLinear lw) where
  nextAllocId_eq := rfl
  exhausted_eq := rfl
  issued_eq a := (get?_ofLinearRows lw.issuedIds a).symm
  live_eq a := (get?_ofLinearRows lw.live a).symm
  dead_eq a := (get?_ofLinearRows lw.dead a).symm
  globals_eq a := (get?_ofLinearRows lw.globals a).symm
  race_eq a := (get?_ofLinearRows lw.race a).symm

/-- **Totality, Keyed → Linear (`allocWorldRel_ofKeyed`, `[adv B1]`)**: every keyed world is the
refinement of its sorted duplicate-free linear image, so `AllocWorldRel` is total in both directions
(A0 proved only partner uniqueness and step preservation). -/
theorem allocWorldRel_ofKeyed (kw : KeyedAllocWorld) :
    AllocWorldRel (LinearAllocWorld.ofKeyed kw) kw where
  nextAllocId_eq := rfl
  exhausted_eq := rfl
  issued_eq a := ExtTreeMap0.linearFind?_toList kw.issuedIds a
  live_eq a := ExtTreeMap0.linearFind?_toList kw.live a
  dead_eq a := ExtTreeMap0.linearFind?_toList kw.dead a
  globals_eq a := ExtTreeMap0.linearFind?_toList kw.globals a
  race_eq a := ExtTreeMap0.linearFind?_toList kw.race a

/-- **`AllocWorldRel` Is Exactly the Graph of `ofLinear` (`allocWorldRel_iff_eq_ofLinear`,
`[adv B1]`)**: the refinement relation is a total function from linear to keyed worlds. -/
theorem allocWorldRel_iff_eq_ofLinear (lw : LinearAllocWorld) (kw : KeyedAllocWorld) :
    AllocWorldRel lw kw ↔ kw = KeyedAllocWorld.ofLinear lw := by
  constructor
  · intro h
    exact allocWorldRel_keyed_unique h (allocWorldRel_ofLinear lw)
  · intro h
    subst h
    exact allocWorldRel_ofLinear lw

theorem allocWorldRel_containsId_eq {lw : LinearAllocWorld} {kw : KeyedAllocWorld}
    (hrel : AllocWorldRel lw kw) (id : MiriAllocId) :
    lw.containsId id = kw.containsId id := by
  unfold LinearAllocWorld.containsId KeyedAllocWorld.containsId
  rw [linearContains_eq_isSome_linearFind?, linearContains_eq_isSome_linearFind?,
    linearContains_eq_isSome_linearFind?, linearContains_eq_isSome_linearFind?,
    ExtTreeMap0.contains_eq_isSome_get?, ExtTreeMap0.contains_eq_isSome_get?,
    ExtTreeMap0.contains_eq_isSome_get?, ExtTreeMap0.contains_eq_isSome_get?,
    hrel.issued_eq id]
  have hl := hrel.live_eq id
  have hd := hrel.dead_eq id
  have hg := hrel.globals_eq id
  unfold LinearAllocWorld.findLive? KeyedAllocWorld.findLive? at hl
  unfold LinearAllocWorld.findDead? KeyedAllocWorld.findDead? at hd
  unfold LinearAllocWorld.findGlobal? KeyedAllocWorld.findGlobal? at hg
  rw [hl, hd, hg]

theorem allocWorldRel_isAllocLive_eq {lw : LinearAllocWorld} {kw : KeyedAllocWorld}
    (hrel : AllocWorldRel lw kw) (id : MiriAllocId) :
    lw.isAllocLive id = kw.isAllocLive id := by
  unfold LinearAllocWorld.isAllocLive KeyedAllocWorld.isAllocLive
  rw [linearContains_eq_isSome_linearFind?, linearContains_eq_isSome_linearFind?,
    ExtTreeMap0.contains_eq_isSome_get?, ExtTreeMap0.contains_eq_isSome_get?]
  have hl := hrel.live_eq id
  have hg := hrel.globals_eq id
  unfold LinearAllocWorld.findLive? KeyedAllocWorld.findLive? at hl
  unfold LinearAllocWorld.findGlobal? KeyedAllocWorld.findGlobal? at hg
  rw [hl, hg]

theorem allocWorldRel_getAllocInfo_eq {lw : LinearAllocWorld} {kw : KeyedAllocWorld}
    (hrel : AllocWorldRel lw kw) (id : MiriAllocId) :
    lw.getAllocInfo id = kw.getAllocInfo id := by
  unfold LinearAllocWorld.getAllocInfo KeyedAllocWorld.getAllocInfo
  rw [hrel.live_eq id, hrel.globals_eq id, hrel.dead_eq id]

theorem allocWorldRel_getLiveAllocSizeAndAlign_eq {lw : LinearAllocWorld} {kw : KeyedAllocWorld}
    (hrel : AllocWorldRel lw kw) (id : MiriAllocId) :
    lw.getLiveAllocSizeAndAlign id = kw.getLiveAllocSizeAndAlign id := by
  unfold LinearAllocWorld.getLiveAllocSizeAndAlign KeyedAllocWorld.getLiveAllocSizeAndAlign
  rw [allocWorldRel_getAllocInfo_eq hrel id]

private theorem cmp_eq_iff_eq_id (a b : MiriAllocId) :
    (compare a b = .eq) ↔ (a = b) :=
  LawfulEqCmp.compare_eq_iff_eq (cmp := compare)

theorem allocWorldRel_insertLive {lw : LinearAllocWorld} {kw : KeyedAllocWorld}
    (hrel : AllocWorldRel lw kw) (id : MiriAllocId) (entry : LocalAllocEntry) :
    AllocWorldRel (lw.insertLive id entry) (kw.insertLive id entry) where
  nextAllocId_eq := hrel.nextAllocId_eq
  exhausted_eq := hrel.exhausted_eq
  issued_eq := hrel.issued_eq
  live_eq a := by
    unfold LinearAllocWorld.insertLive KeyedAllocWorld.insertLive
    unfold LinearAllocWorld.findLive? KeyedAllocWorld.findLive?
    dsimp only
    rw [linearFind?_upsert, ExtTreeMap0.get?_insert]
    simp only [cmp_eq_iff_eq_id]
    split
    · rfl
    · exact hrel.live_eq a
  dead_eq := hrel.dead_eq
  globals_eq := hrel.globals_eq
  race_eq := hrel.race_eq

theorem allocWorldRel_removeLive {lw : LinearAllocWorld} {kw : KeyedAllocWorld}
    (hrel : AllocWorldRel lw kw) (id : MiriAllocId) :
    (lw.removeLive id).2 = (kw.removeLive id).2 ∧
    AllocWorldRel (lw.removeLive id).1 (kw.removeLive id).1 := by
  refine ⟨hrel.live_eq id, ?_⟩
  refine {
    nextAllocId_eq := hrel.nextAllocId_eq
    exhausted_eq := hrel.exhausted_eq
    issued_eq := hrel.issued_eq
    live_eq := fun a => ?_
    dead_eq := hrel.dead_eq
    globals_eq := hrel.globals_eq
    race_eq := hrel.race_eq
  }
  unfold LinearAllocWorld.removeLive KeyedAllocWorld.removeLive
  unfold LinearAllocWorld.findLive? KeyedAllocWorld.findLive?
  dsimp only
  rw [linearFind?_linearErase, ExtTreeMap0.get?_erase]
  simp only [cmp_eq_iff_eq_id]
  split
  · rfl
  · exact hrel.live_eq a

theorem allocWorldRel_insertDead {lw : LinearAllocWorld} {kw : KeyedAllocWorld}
    (hrel : AllocWorldRel lw kw) (entry : DeadAllocEntry) :
    AllocWorldRel (lw.insertDead entry) (kw.insertDead entry) where
  nextAllocId_eq := hrel.nextAllocId_eq
  exhausted_eq := hrel.exhausted_eq
  issued_eq := hrel.issued_eq
  live_eq := hrel.live_eq
  dead_eq a := by
    unfold LinearAllocWorld.insertDead KeyedAllocWorld.insertDead
    unfold LinearAllocWorld.findDead? KeyedAllocWorld.findDead?
    dsimp only
    rw [linearFind?_upsert, ExtTreeMap0.get?_insert]
    simp only [cmp_eq_iff_eq_id]
    split
    · rfl
    · exact hrel.dead_eq a
  globals_eq := hrel.globals_eq
  race_eq := hrel.race_eq

theorem allocWorldRel_setRace {lw : LinearAllocWorld} {kw : KeyedAllocWorld}
    (hrel : AllocWorldRel lw kw) (id : MiriAllocId) (entry : RaceClockEntry) :
    AllocWorldRel (lw.setRace id entry) (kw.setRace id entry) where
  nextAllocId_eq := hrel.nextAllocId_eq
  exhausted_eq := hrel.exhausted_eq
  issued_eq := hrel.issued_eq
  live_eq := hrel.live_eq
  dead_eq := hrel.dead_eq
  globals_eq := hrel.globals_eq
  race_eq a := by
    unfold LinearAllocWorld.setRace KeyedAllocWorld.setRace
    unfold LinearAllocWorld.findRace? KeyedAllocWorld.findRace?
    dsimp only
    rw [linearFind?_upsert, ExtTreeMap0.get?_insert]
    simp only [cmp_eq_iff_eq_id]
    split
    · rfl
    · exact hrel.race_eq a

theorem allocWorldRel_removeRace {lw : LinearAllocWorld} {kw : KeyedAllocWorld}
    (hrel : AllocWorldRel lw kw) (id : MiriAllocId) :
    AllocWorldRel (lw.removeRace id) (kw.removeRace id) where
  nextAllocId_eq := hrel.nextAllocId_eq
  exhausted_eq := hrel.exhausted_eq
  issued_eq := hrel.issued_eq
  live_eq := hrel.live_eq
  dead_eq := hrel.dead_eq
  globals_eq := hrel.globals_eq
  race_eq a := by
    unfold LinearAllocWorld.removeRace KeyedAllocWorld.removeRace
    unfold LinearAllocWorld.findRace? KeyedAllocWorld.findRace?
    dsimp only
    rw [linearFind?_linearErase, ExtTreeMap0.get?_erase]
    simp only [cmp_eq_iff_eq_id]
    split
    · rfl
    · exact hrel.race_eq a

theorem allocWorldRel_registerGlobal {lw : LinearAllocWorld} {kw : KeyedAllocWorld}
    (hrel : AllocWorldRel lw kw) (entry : GlobalAllocEntry) :
    AllocWorldRel (lw.registerGlobal entry) (kw.registerGlobal entry) where
  nextAllocId_eq := hrel.nextAllocId_eq
  exhausted_eq := hrel.exhausted_eq
  issued_eq a := by
    unfold LinearAllocWorld.registerGlobal KeyedAllocWorld.registerGlobal
    dsimp only
    rw [linearFind?_upsert, ExtTreeMap0.get?_insert]
    simp only [cmp_eq_iff_eq_id]
    split
    · rfl
    · exact hrel.issued_eq a
  live_eq := hrel.live_eq
  dead_eq := hrel.dead_eq
  globals_eq a := by
    unfold LinearAllocWorld.registerGlobal KeyedAllocWorld.registerGlobal
    unfold LinearAllocWorld.findGlobal? KeyedAllocWorld.findGlobal?
    dsimp only
    rw [linearFind?_upsert, ExtTreeMap0.get?_insert]
    simp only [cmp_eq_iff_eq_id]
    split
    · rfl
    · exact hrel.globals_eq a
  race_eq := hrel.race_eq

theorem allocWorldRel_updateLiveBytes {lw : LinearAllocWorld} {kw : KeyedAllocWorld}
    (hrel : AllocWorldRel lw kw) (id : MiriAllocId) (bytes : List AbstractByte) :
    match lw.updateLiveBytes id bytes, kw.updateLiveBytes id bytes with
    | .error e₁, .error e₂ => e₁ = e₂
    | .ok lw', .ok kw' => AllocWorldRel lw' kw'
    | _, _ => False := by
  unfold LinearAllocWorld.updateLiveBytes KeyedAllocWorld.updateLiveBytes
  rw [hrel.live_eq id]
  cases kw.findLive? id with
  | none => rfl
  | some entry => exact allocWorldRel_insertLive hrel id { entry with bytes := bytes }

private theorem bool_if_true {α : Sort _} {b : Bool} (hb : b = true) (t e : α) :
    (if b = true then t else e) = t := by
  subst hb
  rfl

private theorem bool_if_false {α : Sort _} {b : Bool} (hb : b = false) (t e : α) :
    (if b = true then t else e) = e := by
  subst hb
  rfl

theorem allocWorldRel_reserveAllocId {lw : LinearAllocWorld} {kw : KeyedAllocWorld}
    (hrel : AllocWorldRel lw kw) :
    (lw.reserveAllocId).2 = (kw.reserveAllocId).2 ∧
    AllocWorldRel (lw.reserveAllocId).1 (kw.reserveAllocId).1 := by
  unfold LinearAllocWorld.reserveAllocId KeyedAllocWorld.reserveAllocId
  rw [hrel.exhausted_eq, hrel.nextAllocId_eq]
  by_cases hex : kw.idSupplyExhausted = true
  · repeat rw [bool_if_true hex]
    exact ⟨rfl, hrel⟩
  · have hexf : kw.idSupplyExhausted = false := Bool.eq_false_iff.mpr hex
    repeat rw [bool_if_false hexf]
    cases MiriAllocId.ofUInt64 kw.nextAllocId with
    | none =>
      exact ⟨rfl, {
        nextAllocId_eq := rfl
        exhausted_eq := rfl
        issued_eq := hrel.issued_eq
        live_eq := hrel.live_eq
        dead_eq := hrel.dead_eq
        globals_eq := hrel.globals_eq
        race_eq := hrel.race_eq
      }⟩
    | some id =>
      dsimp only
      rw [allocWorldRel_containsId_eq hrel id]
      by_cases hc : kw.containsId id = true
      · repeat rw [bool_if_true hc]
        exact ⟨rfl, {
          nextAllocId_eq := rfl
          exhausted_eq := rfl
          issued_eq := hrel.issued_eq
          live_eq := hrel.live_eq
          dead_eq := hrel.dead_eq
          globals_eq := hrel.globals_eq
          race_eq := hrel.race_eq
        }⟩
      · have hcf : kw.containsId id = false := Bool.eq_false_iff.mpr hc
        repeat rw [bool_if_false hcf]
        refine ⟨rfl, {
          nextAllocId_eq := rfl
          exhausted_eq := rfl
          issued_eq := fun a => ?_
          live_eq := hrel.live_eq
          dead_eq := hrel.dead_eq
          globals_eq := hrel.globals_eq
          race_eq := hrel.race_eq
        }⟩
        dsimp only
        rw [linearFind?_upsert, ExtTreeMap0.get?_insert]
        simp only [cmp_eq_iff_eq_id]
        split
        · rfl
        · exact hrel.issued_eq a

/-- Wrap-around exhaustion guarantee (`Miri.Memory.MemoryState.reserveAllocId`): when
`idSupplyExhausted = false` and `nextAllocId` wraps around to the reserved `0` sentinel,
`reserveAllocId` latches `idSupplyExhausted = true`, returns `.error .exhausted`, and all
subsequent `reserveAllocId` calls remain `.error .exhausted`. -/
theorem keyedReserveAllocId_wrapAround_latches_exhausted (w : KeyedAllocWorld)
    (havail : w.idSupplyExhausted = false)
    (hzero : w.nextAllocId = 0) :
    let (w', out) := w.reserveAllocId
    out = .error .exhausted ∧
    w'.idSupplyExhausted = true ∧
    w'.reserveAllocId = (w', .error .exhausted) := by
  simp [KeyedAllocWorld.reserveAllocId, havail, hzero]

/-- Monotonic high-water supply guarantee (`Miri.Memory.MemoryState.reserve_of_highWater`): when
`idSupplyExhausted = false`, `nextAllocId ≠ 0`, and all issued/live/dead/global IDs lie strictly
below `nextAllocId`, `KeyedAllocWorld.reserveAllocId` succeeds and advances `nextAllocId`. -/
theorem keyedReserveAllocId_of_highWater (w : KeyedAllocWorld)
    (havail : w.idSupplyExhausted = false)
    (hnz : w.nextAllocId ≠ 0)
    (hiss : ∀ id : MiriAllocId, (w.issuedIds.get? id).isSome = true → id.value < w.nextAllocId)
    (hlive : ∀ id : MiriAllocId, (w.live.get? id).isSome = true → id.value < w.nextAllocId)
    (hdead : ∀ id : MiriAllocId, (w.dead.get? id).isSome = true → id.value < w.nextAllocId)
    (hglob : ∀ id : MiriAllocId, (w.globals.get? id).isSome = true → id.value < w.nextAllocId) :
    let fresh : MiriAllocId := ⟨w.nextAllocId, hnz⟩
    w.reserveAllocId =
      ({ w with nextAllocId := w.nextAllocId + 1, issuedIds := w.issuedIds.insert fresh () },
        .ok fresh) := by
  intro fresh
  have hnot_iss : w.issuedIds.contains fresh = false := by
    rw [ExtTreeMap0.contains_eq_isSome_get?]
    cases hs : (w.issuedIds.get? fresh).isSome with
    | false => rfl
    | true => exact False.elim (UInt64.lt_irrefl w.nextAllocId (hiss fresh hs))
  have hnot_live : w.live.contains fresh = false := by
    rw [ExtTreeMap0.contains_eq_isSome_get?]
    cases hs : (w.live.get? fresh).isSome with
    | false => rfl
    | true => exact False.elim (UInt64.lt_irrefl w.nextAllocId (hlive fresh hs))
  have hnot_dead : w.dead.contains fresh = false := by
    rw [ExtTreeMap0.contains_eq_isSome_get?]
    cases hs : (w.dead.get? fresh).isSome with
    | false => rfl
    | true => exact False.elim (UInt64.lt_irrefl w.nextAllocId (hdead fresh hs))
  have hnot_glob : w.globals.contains fresh = false := by
    rw [ExtTreeMap0.contains_eq_isSome_get?]
    cases hs : (w.globals.get? fresh).isSome with
    | false => rfl
    | true => exact False.elim (UInt64.lt_irrefl w.nextAllocId (hglob fresh hs))
  have hnot_contains : w.containsId fresh = false := by
    simp [KeyedAllocWorld.containsId, hnot_iss, hnot_live, hnot_dead, hnot_glob]
  unfold KeyedAllocWorld.reserveAllocId MiriAllocId.ofUInt64
  simp [havail, hnz, fresh, hnot_contains]

theorem allocWorldRel_allocate {lw : LinearAllocWorld} {kw : KeyedAllocWorld}
    (hrel : AllocWorldRel lw kw) (entry : LocalAllocEntry) (maxObjectSize : UInt64)
    (initClock : Option RaceClockEntry) :
    (lw.allocate entry maxObjectSize initClock).2 =
      (kw.allocate entry maxObjectSize initClock).2 ∧
    AllocWorldRel
      (lw.allocate entry maxObjectSize initClock).1
      (kw.allocate entry maxObjectSize initClock).1 := by
  unfold LinearAllocWorld.allocate KeyedAllocWorld.allocate
  split
  · exact ⟨rfl, hrel⟩
  · obtain ⟨hres_out, hres_rel⟩ := allocWorldRel_reserveAllocId hrel
    cases hl : lw.reserveAllocId with
    | mk lwRes lOut =>
      cases hk : kw.reserveAllocId with
      | mk kwRes kOut =>
        rw [hl, hk] at hres_out hres_rel
        dsimp only at hres_out hres_rel ⊢
        subst hres_out
        cases lOut with
        | error e => exact ⟨rfl, hres_rel⟩
        | ok id =>
          dsimp only
          by_cases hg : (entry.kind == .globalCache) = true
          · repeat rw [bool_if_true hg]
            exact ⟨rfl, hres_rel⟩
          · have hgf : (entry.kind == .globalCache) = false := Bool.eq_false_iff.mpr hg
            repeat rw [bool_if_false hgf]
            have hlive_rel := allocWorldRel_insertLive hres_rel id entry
            cases initClock with
            | none => exact ⟨rfl, hlive_rel⟩
            | some clk => exact ⟨rfl, allocWorldRel_setRace hlive_rel id clk⟩

/-- **Exact Deallocation Refinement (`allocWorldRel_deallocate`)**: across all pointer states,
requested layouts, memory kinds, and machine deallocation hooks, `LinearAllocWorld.deallocate` and
`KeyedAllocWorld.deallocate` produce identical `detached` owners, identical `Except` outcomes, and
`AllocWorldRel`-equivalent successor states (including on every failure path). -/
theorem allocWorldRel_deallocate {lw : LinearAllocWorld} {kw : KeyedAllocWorld}
    (hrel : AllocWorldRel lw kw) (ptr : ResolvedDeallocPtr)
    (reqLayout : Option (UInt64 × UInt64)) (reqKind : AllocMemoryKind)
    (hook : DeallocHookSpec) :
    let (lw', detL, outL) := lw.deallocate ptr reqLayout reqKind hook
    let (kw', detK, outK) := kw.deallocate ptr reqLayout reqKind hook
    detL = detK ∧ outL = outK ∧ AllocWorldRel lw' kw' := by
  dsimp only
  unfold LinearAllocWorld.deallocate KeyedAllocWorld.deallocate
  cases ptr with
  | danglingAddress addr =>
    exact ⟨rfl, rfl, hrel⟩
  | provenanced id offsetBytes =>
    dsimp only
    by_cases hoff : (offsetBytes != 0) = true
    · repeat rw [bool_if_true hoff]
      exact ⟨rfl, rfl, hrel⟩
    · have hoff_f : (offsetBytes != 0) = false := Bool.eq_false_iff.mpr hoff
      repeat rw [bool_if_false hoff_f]
      obtain ⟨hrem_out, hrem_rel⟩ := allocWorldRel_removeLive hrel id
      cases hlrem : lw.removeLive id with
      | mk lwRem lEntry? =>
        cases hkrem : kw.removeLive id with
        | mk kwRem kEntry? =>
          rw [hlrem, hkrem] at hrem_out hrem_rel
          dsimp only at hrem_out hrem_rel ⊢
          subst hrem_out
          cases lEntry? with
          | none =>
            rw [hrel.globals_eq id]
            cases kw.findGlobal? id <;> exact ⟨rfl, rfl, hrel⟩
          | some entry =>
            dsimp only
            have hfail_rel := allocWorldRel_removeRace hrem_rel id
            by_cases hmut : (entry.mutability == .not) = true
            · repeat rw [bool_if_true hmut]
              exact ⟨rfl, rfl, hfail_rel⟩
            · have hmut_f : (entry.mutability == .not) = false := Bool.eq_false_iff.mpr hmut
              repeat rw [bool_if_false hmut_f]
              by_cases hkind : (entry.kind != reqKind) = true
              · repeat rw [bool_if_true hkind]
                exact ⟨rfl, rfl, hfail_rel⟩
              · have hkind_f : (entry.kind != reqKind) = false := Bool.eq_false_iff.mpr hkind
                repeat rw [bool_if_false hkind_f]
                cases reqLayout with
                | none =>
                  dsimp only [Bool.false_eq_true, ↓reduceIte]
                  cases hook with
                  | raceDataRaceFault _ _ => exact ⟨rfl, rfl, hfail_rel⟩
                  | protectedBorrowFault _ => exact ⟨rfl, rfl, hfail_rel⟩
                  | missingRaceClock => exact ⟨rfl, rfl, hfail_rel⟩
                  | ok =>
                    dsimp only
                    rw [hrem_rel.dead_eq id]
                    have hdead_rel :=
                      allocWorldRel_removeRace
                        (allocWorldRel_insertDead hrem_rel
                          ⟨id, entry.sizeBytes, entry.alignBytes⟩)
                        id
                    by_cases his : (kwRem.findDead? id).isSome = true
                    · repeat rw [bool_if_true his]
                      exact ⟨rfl, rfl, hdead_rel⟩
                    · have his_f : (kwRem.findDead? id).isSome = false := Bool.eq_false_iff.mpr his
                      repeat rw [bool_if_false his_f]
                      exact ⟨rfl, rfl, hdead_rel⟩
                | some reqPair =>
                  rcases reqPair with ⟨reqSz, reqAl⟩
                  dsimp only
                  by_cases hlay : (reqSz != entry.sizeBytes || reqAl != entry.alignBytes) = true
                  · repeat rw [bool_if_true hlay]
                    exact ⟨rfl, rfl, hfail_rel⟩
                  · have hlay_f : (reqSz != entry.sizeBytes || reqAl != entry.alignBytes) = false :=
                      Bool.eq_false_iff.mpr hlay
                    repeat rw [bool_if_false hlay_f]
                    cases hook with
                    | raceDataRaceFault _ _ => exact ⟨rfl, rfl, hfail_rel⟩
                    | protectedBorrowFault _ => exact ⟨rfl, rfl, hfail_rel⟩
                    | missingRaceClock => exact ⟨rfl, rfl, hfail_rel⟩
                    | ok =>
                      dsimp only
                      rw [hrem_rel.dead_eq id]
                      have hdead_rel :=
                        allocWorldRel_removeRace
                          (allocWorldRel_insertDead hrem_rel
                            ⟨id, entry.sizeBytes, entry.alignBytes⟩)
                          id
                      by_cases his : (kwRem.findDead? id).isSome = true
                      · repeat rw [bool_if_true his]
                        exact ⟨rfl, rfl, hdead_rel⟩
                      · have his_f : (kwRem.findDead? id).isSome = false := Bool.eq_false_iff.mpr his
                        repeat rw [bool_if_false his_f]
                        exact ⟨rfl, rfl, hdead_rel⟩

/-! ### Exact Failure-Ordering & State-Retention Theorems on `KeyedAllocWorld` -/

/-- **Failure Ordering 1**: Nonzero offset fails *before* `removeLive`, so a live allocation at
`id` remains live (`findLive? id = some entry`, `detached = none`). -/
theorem keyedDeallocate_nonzeroOffset_preserves_live (w : KeyedAllocWorld) (id : MiriAllocId)
    (offsetBytes : UInt64) (hoff : offsetBytes ≠ 0)
    (reqLayout : Option (UInt64 × UInt64)) (reqKind : AllocMemoryKind) (hook : DeallocHookSpec) :
    w.deallocate (.provenanced id offsetBytes) reqLayout reqKind hook =
      (w, none, .error (.nonzeroAllocationOffset id offsetBytes)) := by
  have hne : (offsetBytes != 0) = true := bne_iff_ne.mpr hoff
  simp [KeyedAllocWorld.deallocate, hne]

/-- **Failure Ordering 2**: Double-free (`id` absent from `live`, present in `dead`) reports
`useAfterFree id` *before* checking `reqKind`, `reqLayout`, or `hook` (even when `reqLayout`
mismatches the tombstoned layout), and keeps the tombstone. *Honest scope (`[adv B1]`)*: the
`hdead` premise is used only for the tombstone-retention conjunct — `deallocate` never consults
`dead` here; see `keyedDeallocate_absent_reports_useAfterFree`. -/
theorem keyedDeallocate_doubleFree_precedes_layout_and_kind (w : KeyedAllocWorld) (id : MiriAllocId)
    (deadEntry : DeadAllocEntry)
    (hnotLive : w.findLive? id = none)
    (hnotGlobal : w.findGlobal? id = none)
    (hdead : w.findDead? id = some deadEntry)
    (reqLayout : Option (UInt64 × UInt64)) (reqKind : AllocMemoryKind) (hook : DeallocHookSpec) :
    let (w', det, out) := w.deallocate (.provenanced id 0) reqLayout reqKind hook
    w' = w ∧ det = none ∧ out = .error (.useAfterFree id) ∧ w'.findDead? id = some deadEntry := by
  simp [KeyedAllocWorld.deallocate, KeyedAllocWorld.removeLive, hnotLive, hnotGlobal, hdead]

/-- **Use-After-Free Never Consults `dead` (`keyedDeallocate_absent_reports_useAfterFree`,
`[adv B1]`)**: whenever `id` is absent from both `live` and the global table, deallocation reports
`.useAfterFree id` and leaves the world untouched *whatever* the `dead` table contains — a tombstoned
double free, a never-issued id, and a GC-pruned tombstone coincide, exactly as in upstream
`deallocatePtrWith` (whose `removeLive` miss falls through to `findGlobal?` and then `useAfterFree`). -/
theorem keyedDeallocate_absent_reports_useAfterFree (w : KeyedAllocWorld) (id : MiriAllocId)
    (hnotLive : w.findLive? id = none) (hnotGlobal : w.findGlobal? id = none)
    (reqLayout : Option (UInt64 × UInt64)) (reqKind : AllocMemoryKind) (hook : DeallocHookSpec)
    (dead' : ExtTreeMap0 MiriAllocId DeadAllocEntry) :
    w.deallocate (.provenanced id 0) reqLayout reqKind hook = (w, none, .error (.useAfterFree id)) ∧
    ({ w with dead := dead' } : KeyedAllocWorld).deallocate (.provenanced id 0) reqLayout reqKind hook =
      ({ w with dead := dead' }, none, .error (.useAfterFree id)) := by
  have hl' : ({ w with dead := dead' } : KeyedAllocWorld).findLive? id = none := hnotLive
  have hg' : ({ w with dead := dead' } : KeyedAllocWorld).findGlobal? id = none := hnotGlobal
  constructor
  · simp [KeyedAllocWorld.deallocate, KeyedAllocWorld.removeLive, hnotLive, hnotGlobal]
  · simp only [KeyedAllocWorld.deallocate, KeyedAllocWorld.removeLive, hl', hg',
      bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]

/-- **Failure Ordering 3**: Attempting to deallocate a compiler global (`function`, `vtable`,
`static`, etc.) reports `globalAllocationDeallocation id glob.kind` without mutating `w`. -/
theorem keyedDeallocate_global_reports_globalErr (w : KeyedAllocWorld) (id : MiriAllocId)
    (glob : GlobalAllocEntry) (hnotLive : w.findLive? id = none)
    (hglob : w.findGlobal? id = some glob)
    (reqLayout : Option (UInt64 × UInt64)) (reqKind : AllocMemoryKind) (hook : DeallocHookSpec) :
    w.deallocate (.provenanced id 0) reqLayout reqKind hook =
      (w, none, .error (.globalAllocationDeallocation id glob.kind)) := by
  simp [KeyedAllocWorld.deallocate, KeyedAllocWorld.removeLive, hnotLive, hglob]

/-- **Failure Ordering 4 (`live` Removal Retained Across Post-Removal Errors)**: when `id` is live
with `entry`, any failure in mutability (`.not`), kind (`entry.kind ≠ reqKind`), layout mismatch,
or `beforeDeallocation` hook (`raceDataRaceFault` / `protectedBorrowFault`) retains the detached
owner `some (id, entry)`, leaves `id` **removed** from `live` (`w'.findLive? id = none`) and
`race` (`w'.findRace? id = none`), and does **not** insert `id` into `dead`
(`w'.findDead? id = w.findDead? id`). -/
theorem keyedDeallocate_postRemovalFailure_retains_detached_state
    (w : KeyedAllocWorld) (id : MiriAllocId) (entry : LocalAllocEntry)
    (hlive : w.findLive? id = some entry)
    (reqLayout : Option (UInt64 × UInt64)) (reqKind : AllocMemoryKind) (hook : DeallocHookSpec)
    (hfail : entry.mutability = .not ∨ entry.kind ≠ reqKind ∨
      (∃ sz al, reqLayout = some (sz, al) ∧ (sz ≠ entry.sizeBytes ∨ al ≠ entry.alignBytes)) ∨
      hook ≠ .ok) :
    let (w', det, out) := w.deallocate (.provenanced id 0) reqLayout reqKind hook
    det = some (id, entry) ∧
    out.isOk = false ∧
    w'.findLive? id = none ∧
    w'.findRace? id = none ∧
    w'.findDead? id = w.findDead? id := by
  dsimp only
  unfold KeyedAllocWorld.deallocate KeyedAllocWorld.removeLive
  simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, hlive]
  by_cases hmut_t : (entry.mutability == .not) = true
  · repeat rw [bool_if_true hmut_t]
    simp [KeyedAllocWorld.removeRace, KeyedAllocWorld.findLive?,
      KeyedAllocWorld.findRace?, KeyedAllocWorld.findDead?, Except.isOk, Except.toBool]
  · have hmut : (entry.mutability == .not) = false := Bool.eq_false_iff.mpr hmut_t
    repeat rw [bool_if_false hmut]
    by_cases hkind_t : (entry.kind != reqKind) = true
    · repeat rw [bool_if_true hkind_t]
      simp [KeyedAllocWorld.removeRace, KeyedAllocWorld.findLive?,
        KeyedAllocWorld.findRace?, KeyedAllocWorld.findDead?, Except.isOk, Except.toBool]
    · have hkind : (entry.kind != reqKind) = false := Bool.eq_false_iff.mpr hkind_t
      repeat rw [bool_if_false hkind]
      have hmut_mut : entry.mutability ≠ .not := fun hm => by
        rw [hm] at hmut; nomatch hmut
      have hkind_eq : entry.kind = reqKind :=
        Decidable.of_not_not (by simpa [bne] using hkind)
      cases reqLayout with
      | none =>
        dsimp only [Bool.false_eq_true, ↓reduceIte]
        have hhook_ne : hook ≠ .ok := by
          rcases hfail with hm | hk | ⟨_, _, hsome, _⟩ | hh
          · exact absurd hm hmut_mut
          · exact absurd hkind_eq hk
          · nomatch hsome
          · exact hh
        cases hook with
        | ok => exact absurd rfl hhook_ne
        | raceDataRaceFault _ _ =>
          simp [KeyedAllocWorld.removeRace, KeyedAllocWorld.findLive?,
            KeyedAllocWorld.findRace?, KeyedAllocWorld.findDead?, Except.isOk, Except.toBool]
        | protectedBorrowFault _ =>
          simp [KeyedAllocWorld.removeRace, KeyedAllocWorld.findLive?,
            KeyedAllocWorld.findRace?, KeyedAllocWorld.findDead?, Except.isOk, Except.toBool]
        | missingRaceClock =>
          simp [KeyedAllocWorld.removeRace, KeyedAllocWorld.findLive?,
            KeyedAllocWorld.findRace?, KeyedAllocWorld.findDead?, Except.isOk, Except.toBool]
      | some reqPair =>
        rcases reqPair with ⟨reqSz, reqAl⟩
        dsimp only
        by_cases hlay_t : (reqSz != entry.sizeBytes || reqAl != entry.alignBytes) = true
        · repeat rw [bool_if_true hlay_t]
          simp [KeyedAllocWorld.removeRace, KeyedAllocWorld.findLive?,
            KeyedAllocWorld.findRace?, KeyedAllocWorld.findDead?, Except.isOk, Except.toBool]
        · have hlay : (reqSz != entry.sizeBytes || reqAl != entry.alignBytes) = false :=
            Bool.eq_false_iff.mpr hlay_t
          repeat rw [bool_if_false hlay]
          have hlay_eq : reqSz = entry.sizeBytes ∧ reqAl = entry.alignBytes := by
            have hboth := Bool.or_eq_false_iff.mp hlay
            exact ⟨Decidable.of_not_not (by simpa [bne] using hboth.1),
              Decidable.of_not_not (by simpa [bne] using hboth.2)⟩
          have hhook_ne : hook ≠ .ok := by
            rcases hfail with hm | hk | ⟨sz, al, hsome, hneq⟩ | hh
            · exact absurd hm hmut_mut
            · exact absurd hkind_eq hk
            · injection hsome with hpair
              injection hpair with hsz hal
              subst hsz hal
              rcases hneq with hsz_ne | hal_ne
              · exact absurd hlay_eq.1 hsz_ne
              · exact absurd hlay_eq.2 hal_ne
            · exact hh
          cases hook with
          | ok => exact absurd rfl hhook_ne
          | raceDataRaceFault _ _ =>
            simp [KeyedAllocWorld.removeRace, KeyedAllocWorld.findLive?,
              KeyedAllocWorld.findRace?, KeyedAllocWorld.findDead?, Except.isOk, Except.toBool]
          | protectedBorrowFault _ =>
            simp [KeyedAllocWorld.removeRace, KeyedAllocWorld.findLive?,
              KeyedAllocWorld.findRace?, KeyedAllocWorld.findDead?, Except.isOk, Except.toBool]
          | missingRaceClock =>
            simp [KeyedAllocWorld.removeRace, KeyedAllocWorld.findLive?,
              KeyedAllocWorld.findRace?, KeyedAllocWorld.findDead?, Except.isOk, Except.toBool]

/-- **Failure Ordering 5 (Duplicate-`dead` Replacement Before Error)**: when `id` is live with
valid layout/kind/hook `.ok` AND already has a stale `oldDead` entry in `dead`, deallocation
removes `id` from `live` and `race`, **replaces** `w'.findDead? id` with the fresh layout
`⟨id, entry.sizeBytes, entry.alignBytes⟩` (without duplicate keys), and then returns
`.error (.duplicateDeadAllocation id)`. -/
theorem keyedDeallocate_duplicateDead_replaces_before_error
    (w : KeyedAllocWorld) (id : MiriAllocId) (entry : LocalAllocEntry)
    (oldDead : DeadAllocEntry)
    (hlive : w.findLive? id = some entry)
    (hmut : entry.mutability = .mut)
    (hdead : w.findDead? id = some oldDead) :
    let (w', det, out) := w.deallocate (.provenanced id 0)
      (some (entry.sizeBytes, entry.alignBytes)) entry.kind .ok
    det = some (id, entry) ∧
    out = .error (.duplicateDeadAllocation id) ∧
    w'.findLive? id = none ∧
    w'.findRace? id = none ∧
    w'.findDead? id = some ⟨id, entry.sizeBytes, entry.alignBytes⟩ := by
  unfold KeyedAllocWorld.deallocate KeyedAllocWorld.removeLive
  have hmut_false : (entry.mutability == .not) = false := by rw [hmut]; rfl
  simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, hlive, hmut_false, Bool.or_self]
  have hdead_rem : ({ w with live := w.live.erase id } : KeyedAllocWorld).findDead? id = some oldDead := hdead
  rw [hdead_rem]
  simp [KeyedAllocWorld.insertDead, KeyedAllocWorld.removeRace,
    KeyedAllocWorld.findLive?, KeyedAllocWorld.findRace?, KeyedAllocWorld.findDead?]

/-- **Machine Deallocation Refinement (`allocWorldRel_deallocateMachine`, `[adv B1]`, all detector
modes `[adv B2]`)**: with the hook verdict computed from each world's own race table, linear and
keyed machine deallocation agree on detached owner, outcome, and successor `AllocWorldRel` for
every `RaceDetectorMode`. -/
theorem allocWorldRel_deallocateMachine {lw : LinearAllocWorld} {kw : KeyedAllocWorld}
    (hrel : AllocWorldRel lw kw) (ptr : ResolvedDeallocPtr)
    (reqLayout : Option (UInt64 × UInt64)) (reqKind : AllocMemoryKind)
    (actor : DeallocActor) (tb : DeallocHookSpec) (mode : RaceDetectorMode) :
    let (lw', detL, outL) := lw.deallocateMachine ptr reqLayout reqKind actor tb mode
    let (kw', detK, outK) := kw.deallocateMachine ptr reqLayout reqKind actor tb mode
    detL = detK ∧ outL = outK ∧ AllocWorldRel lw' kw' := by
  unfold LinearAllocWorld.deallocateMachine KeyedAllocWorld.deallocateMachine
  cases ptr with
  | danglingAddress addr =>
    exact allocWorldRel_deallocate hrel (.danglingAddress addr) reqLayout reqKind
      (machineDeallocHook none none actor tb mode)
  | provenanced id off =>
    dsimp only
    have hlive : lw.findLive? id = kw.findLive? id := hrel.live_eq id
    have hrace : lw.findRace? id = kw.findRace? id := hrel.race_eq id
    rw [hlive, hrace]
    exact allocWorldRel_deallocate hrel (.provenanced id off) reqLayout reqKind
      (machineDeallocHook ((kw.findLive? id).map (·.sizeBytes)) (kw.findRace? id) actor tb mode)

/-- **Race Check Precedes Race Cleanup (`keyedDeallocateMachine_race_checked_before_cleanup`,
`[adv B1]`, ZST-refined `[adv A1]`, detector-mode `[adv B2]`)**: under the (default) configured,
detecting race detector, when `id` is live (`sizeBytes ≠ 0`), passes the mutability/kind/layout
checks, has no tombstone, and its *still-present* race clock `clk` races with `actor`, machine
deallocation reports `.hookFailure "DataRace"`, retains the detached owner, drops `id` from `live`
and only *then* from `race`, and does not tombstone it. The order is observable: on
`w.removeRace id` (cleanup-first) the lost clock is reported as an invalid program
(`MissingVectorClockExtra`, upstream `memoryRaceAccess`) instead of the race. -/
theorem keyedDeallocateMachine_race_checked_before_cleanup
    (w : KeyedAllocWorld) (id : MiriAllocId) (entry : LocalAllocEntry) (clk : RaceClockEntry)
    (actor : DeallocActor) (tb : DeallocHookSpec)
    (hlive : w.findLive? id = some entry)
    (hsz : entry.sizeBytes ≠ 0)
    (hmut : entry.mutability = .mut)
    (hnodead : w.findDead? id = none)
    (hrace : w.findRace? id = some clk)
    (hracy : raceDeallocVerdict actor clk ≠ .ok) :
    let r := w.deallocateMachine (.provenanced id 0)
      (some (entry.sizeBytes, entry.alignBytes)) entry.kind actor tb
    r.2.1 = some (id, entry) ∧
    r.2.2 = .error (.hookFailure "DataRace") ∧
    r.1.findLive? id = none ∧
    r.1.findRace? id = none ∧
    r.1.findDead? id = none ∧
    ((w.removeRace id).deallocateMachine (.provenanced id 0)
      (some (entry.sizeBytes, entry.alignBytes)) entry.kind actor .ok).2.2 =
      .error (.hookFailure "MissingVectorClockExtra") := by
  have hfault : ∃ th ts, raceDeallocVerdict actor clk = .raceDataRaceFault th ts := by
    unfold raceDeallocVerdict at hracy ⊢
    dsimp only at hracy ⊢
    split
    · exact ⟨_, _, rfl⟩
    · rename_i hw
      simp only [hw] at hracy
      split
      · exact ⟨_, _, rfl⟩
      · rename_i hr
        simp only [hr] at hracy
        cases hf : findExtraReaderRace actor clk.extraReaders with
        | some p => exact ⟨p.1, p.2, rfl⟩
        | none => rw [hf] at hracy; exact False.elim (hracy rfl)
  rcases hfault with ⟨th, ts, hfaultEq⟩
  have hsz_false : (some entry.sizeBytes == some (0 : UInt64)) = false := by
    cases h : (some entry.sizeBytes == some (0 : UInt64)) with
    | false => rfl
    | true =>
      have heq : some entry.sizeBytes = some 0 := eq_of_beq h
      injection heq with h0
      exact False.elim (hsz h0)
  have hmut_false : (entry.mutability == .not) = false := by rw [hmut]; rfl
  have hlive' : w.live.get? id = some entry := hlive
  have hrace' : w.race.get? id = some clk := hrace
  have hdead' : w.dead.get? id = none := hnodead
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [KeyedAllocWorld.deallocateMachine, KeyedAllocWorld.deallocate,
      KeyedAllocWorld.removeLive, KeyedAllocWorld.removeRace,
      KeyedAllocWorld.findLive?, KeyedAllocWorld.findRace?, KeyedAllocWorld.findDead?,
      machineDeallocHook, hsz_false, hfaultEq, hlive', hrace', hdead', hmut_false]

/-- **Same-Writer Foreign-Reader Deallocation Race (`keyedDeallocateMachine_sameWriter_foreignRead_races`,
`[adv A1]`)**: even when the deallocating thread *is* the recorded writer (`actor.thread =
clk.writerThread`), an unsynchronized concurrent read by another thread (`clk.lastReaderThread =
some reader`, `reader ≠ actor.thread`, `actor.observedTimestamp < clk.readTimestamp`) faults with
`.hookFailure "DataRace"`, matching `DataRace.nonAtomicWriteDetect` (`cell.read.le thread.clock`). -/
theorem keyedDeallocateMachine_sameWriter_foreignRead_races
    (w : KeyedAllocWorld) (id : MiriAllocId) (entry : LocalAllocEntry) (clk : RaceClockEntry)
    (actor : DeallocActor) (reader : UInt32) (tb : DeallocHookSpec)
    (hlive : w.findLive? id = some entry)
    (hsz : entry.sizeBytes ≠ 0)
    (hmut : entry.mutability = .mut)
    (hnodead : w.findDead? id = none)
    (hrace : w.findRace? id = some clk)
    (hsameWriter : clk.writerThread = actor.thread)
    (hreader : clk.lastReaderThread = some reader)
    (hneReader : reader ≠ actor.thread)
    (hunobserved : actor.viewFor reader < clk.readTimestamp) :
    (w.deallocateMachine (.provenanced id 0)
      (some (entry.sizeBytes, entry.alignBytes)) entry.kind actor tb).2.2 =
      .error (.hookFailure "DataRace") := by
  have hracy : raceDeallocVerdict actor clk ≠ .ok := by
    have hneB : (reader != actor.thread) = true := bne_iff_ne.mpr hneReader
    have hltD : decide (actor.viewFor reader < clk.readTimestamp) = true :=
      decide_eq_true hunobserved
    unfold raceDeallocVerdict
    simp [hsameWriter, hreader, hneB, hltD]
  exact (keyedDeallocateMachine_race_checked_before_cleanup w id entry clk actor tb
    hlive hsz hmut hnodead hrace hracy).2.1

/-- **Zero-Sized Deallocation Skips Race Detector (`keyedDeallocateMachine_zst_skips_race_check`,
`[adv A1]`, clock premise added `[adv B2]`)**: when `entry.sizeBytes = 0` and the allocation still
carries its race clock (any clock, even one that would race), `deallocateMachine` checks `0` bytes
(matching `DataRace.runRangeLoop` `remaining = 0`) and succeeds with `.ok ()` while still removing
`id` from `live` and `race` and recording the zero-sized tombstone. Without the clock premise the
configured detector reports `MissingVectorClockExtra` (`keyedDeallocateMachine_missingClock_invalid`). -/
theorem keyedDeallocateMachine_zst_skips_race_check
    (w : KeyedAllocWorld) (id : MiriAllocId) (entry : LocalAllocEntry) (clk : RaceClockEntry)
    (actor : DeallocActor)
    (hlive : w.findLive? id = some entry)
    (hsz0 : entry.sizeBytes = 0)
    (hmut : entry.mutability = .mut)
    (hnodead : w.findDead? id = none)
    (hrace : w.findRace? id = some clk) :
    let r := w.deallocateMachine (.provenanced id 0)
      (some (entry.sizeBytes, entry.alignBytes)) entry.kind actor .ok
    r.2.2 = .ok () ∧ r.1.findLive? id = none ∧ r.1.findRace? id = none := by
  have hsz_true : (some entry.sizeBytes == some (0 : UInt64)) = true := by rw [hsz0]; rfl
  have hmut_false : (entry.mutability == .not) = false := by rw [hmut]; rfl
  have hlive' : w.live.get? id = some entry := hlive
  have hdead' : w.dead.get? id = none := hnodead
  have hrace' : w.race.get? id = some clk := hrace
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [KeyedAllocWorld.deallocateMachine, KeyedAllocWorld.deallocate,
      KeyedAllocWorld.removeLive, KeyedAllocWorld.removeRace, KeyedAllocWorld.insertDead,
      KeyedAllocWorld.findLive?, KeyedAllocWorld.findRace?, KeyedAllocWorld.findDead?,
      machineDeallocHook, hsz_true, hlive', hdead', hrace', hmut_false]

/-- **Lost Race Clock Is an Invalid Program, Even for ZSTs
(`keyedDeallocateMachine_missingClock_invalid`, `[adv B2]`)**: with a configured detector
(detecting or not), a live allocation that passes the mutability/kind/layout checks but has no
`raceAllocations` entry fails with `.hookFailure "MissingVectorClockExtra"` — upstream
`memoryRaceAccess` looks the entry up *before* the `raceDetecting` and byte-range checks
(`MachineHooks.lean:234–237`). B1/A1 silently treated a missing entry as race-free. The detached
owner is still returned and `id` stays removed from `live`. -/
theorem keyedDeallocateMachine_missingClock_invalid
    (w : KeyedAllocWorld) (id : MiriAllocId) (entry : LocalAllocEntry)
    (actor : DeallocActor) (tb : DeallocHookSpec) (detecting : Bool)
    (hlive : w.findLive? id = some entry)
    (hmut : entry.mutability = .mut)
    (hnorace : w.findRace? id = none) :
    let r := w.deallocateMachine (.provenanced id 0)
      (some (entry.sizeBytes, entry.alignBytes)) entry.kind actor tb (.configured detecting)
    r.2.1 = some (id, entry) ∧
    r.2.2 = .error (.hookFailure "MissingVectorClockExtra") ∧
    r.1.findLive? id = none := by
  have hmut_false : (entry.mutability == .not) = false := by rw [hmut]; rfl
  have hlive' : w.live.get? id = some entry := hlive
  have hrace' : w.race.get? id = none := hnorace
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [KeyedAllocWorld.deallocateMachine, KeyedAllocWorld.deallocate,
      KeyedAllocWorld.removeLive, KeyedAllocWorld.removeRace,
      KeyedAllocWorld.findLive?, KeyedAllocWorld.findRace?,
      machineDeallocHook, hlive', hrace', hmut_false]

/-- **No Detector, No Race Check (`keyedDeallocateMachine_unconfigured_eq_deallocate`, `[adv B2]`)**:
with `machine.dataRace = none` the race table is never consulted: machine deallocation is plain
`deallocate` with the Tree Borrows verdict, for every pointer. -/
theorem keyedDeallocateMachine_unconfigured_eq_deallocate
    (w : KeyedAllocWorld) (ptr : ResolvedDeallocPtr)
    (reqLayout : Option (UInt64 × UInt64)) (reqKind : AllocMemoryKind)
    (actor : DeallocActor) (tb : DeallocHookSpec) :
    w.deallocateMachine ptr reqLayout reqKind actor tb .unconfigured =
      w.deallocate ptr reqLayout reqKind tb := by
  cases ptr <;> rfl

/-- **Single-Threaded Phase Skips the Verdict (`keyedDeallocateMachine_notDetecting_eq_deallocate`,
`[adv B2]`)**: with a configured detector that is not `raceDetecting` (single-threaded program), a
present clock is not inspected — even a clock that would race — and machine deallocation is plain
`deallocate` with the Tree Borrows verdict. -/
theorem keyedDeallocateMachine_notDetecting_eq_deallocate
    (w : KeyedAllocWorld) (id : MiriAllocId) (off : UInt64) (clk : RaceClockEntry)
    (reqLayout : Option (UInt64 × UInt64)) (reqKind : AllocMemoryKind)
    (actor : DeallocActor) (tb : DeallocHookSpec)
    (hrace : w.findRace? id = some clk) :
    w.deallocateMachine (.provenanced id off) reqLayout reqKind actor tb (.configured false) =
      w.deallocate (.provenanced id off) reqLayout reqKind tb := by
  unfold KeyedAllocWorld.deallocateMachine machineDeallocHook
  simp [hrace]

/-- **Machine Allocation Refinement (`allocWorldRel_allocateMachine`, `[adv A2]`)**: mode-aware
machine allocation preserves `AllocWorldRel` and returns identical outcomes across all
`RaceDetectorMode` settings. -/
theorem allocWorldRel_allocateMachine {lw : LinearAllocWorld} {kw : KeyedAllocWorld}
    (hrel : AllocWorldRel lw kw) (entry : LocalAllocEntry) (maxObjectSize : UInt64)
    (creatorThread : UInt32) (timestamp : UInt64) (mode : RaceDetectorMode) :
    (lw.allocateMachine entry maxObjectSize creatorThread timestamp mode).2 =
      (kw.allocateMachine entry maxObjectSize creatorThread timestamp mode).2 ∧
    AllocWorldRel
      (lw.allocateMachine entry maxObjectSize creatorThread timestamp mode).1
      (kw.allocateMachine entry maxObjectSize creatorThread timestamp mode).1 :=
  allocWorldRel_allocate hrel entry maxObjectSize _

/-- **End-to-End Machine Allocate → Same-Thread Deallocate Lifecycle Soundness
(`keyedAllocateMachine_deallocateMachine_sameThread_ok`, `[adv A2]`)**: for *every*
`RaceDetectorMode` (`unconfigured`, `configured false`, and `configured true`), allocating a mutable
local object via `allocateMachine` and freeing it on the creating thread via `deallocateMachine`
with matching `mode` succeeds with `.ok ()` (no `MissingVectorClockExtra` and no `DataRace`),
detaches `some (id, entry)`, clears `live` and `race`, and records the tombstone in `dead`. -/
theorem keyedAllocateMachine_deallocateMachine_sameThread_ok
    (w w₁ : KeyedAllocWorld) (entry : LocalAllocEntry) (maxObjectSize : UInt64)
    (creatorThread : UInt32) (timestamp : UInt64) (actor : DeallocActor)
    (mode : RaceDetectorMode) (id : MiriAllocId)
    (halloc : w.allocateMachine entry maxObjectSize creatorThread timestamp mode = (w₁, .ok id))
    (hmut : entry.mutability = .mut)
    (hnodead : w.findDead? id = none)
    (hsameThread : actor.thread = creatorThread) :
    let r := w₁.deallocateMachine (.provenanced id 0)
      (some (entry.sizeBytes, entry.alignBytes)) entry.kind actor .ok mode
    r.2.1 = some (id, entry) ∧
    r.2.2 = .ok () ∧
    r.1.findLive? id = none ∧
    r.1.findDead? id = some ⟨id, entry.sizeBytes, entry.alignBytes⟩ := by
  unfold KeyedAllocWorld.allocateMachine KeyedAllocWorld.allocate at halloc
  dsimp only at halloc
  if hgt : entry.sizeBytes > maxObjectSize then
    simp [hgt] at halloc
  else
    simp only [hgt, ↓reduceIte] at halloc
    cases hres : w.reserveAllocId with
    | mk wRes resOut =>
      rw [hres] at halloc
      cases resOut with
      | error _ => nomatch halloc
      | ok id' =>
        dsimp only at halloc
        cases hg : (entry.kind == .globalCache) with
        | true => rw [hg] at halloc; nomatch halloc
        | false =>
          rw [hg] at halloc
          simp only [Bool.false_eq_true, ↓reduceIte] at halloc
          injection halloc with hw₁ hidEq
          injection hidEq with hid'
          subst id'
          have hresDead : wRes.dead = w.dead := by
            unfold KeyedAllocWorld.reserveAllocId at hres
            split at hres
            · nomatch hres
            · cases hof : MiriAllocId.ofUInt64 w.nextAllocId with
              | none => simp [hof] at hres
              | some cand =>
                rw [hof] at hres
                dsimp only at hres
                cases hc : w.containsId cand with
                | true => simp [hc] at hres
                | false =>
                  simp only [hc, Bool.false_eq_true, ↓reduceIte, Prod.mk.injEq] at hres
                  rcases hres with ⟨hwR, _⟩
                  subst hwR; rfl
          have hdead₁ : wRes.dead.get? id = none := by
            rw [hresDead]; exact hnodead
          have hmut_false : (entry.mutability == .not) = false := by rw [hmut]; rfl
          subst hw₁
          cases mode with
          | unconfigured =>
            dsimp only
            refine ⟨?_, ?_, ?_, ?_⟩ <;>
              simp [KeyedAllocWorld.deallocateMachine, KeyedAllocWorld.deallocate,
                KeyedAllocWorld.insertLive, KeyedAllocWorld.removeLive,
                KeyedAllocWorld.insertDead, KeyedAllocWorld.removeRace,
                KeyedAllocWorld.findLive?, KeyedAllocWorld.findDead?,
                machineDeallocHook, hdead₁, hmut_false]
          | configured detecting =>
            dsimp only
            have hverdOk :
                raceDeallocVerdict actor
                  { writerThread := creatorThread, writeTimestamp := timestamp, readTimestamp := 0 } = .ok := by
              unfold raceDeallocVerdict findExtraReaderRace
              simp [hsameThread]
            have hhookOk :
                machineDeallocHook (some entry.sizeBytes)
                  (some { writerThread := creatorThread, writeTimestamp := timestamp, readTimestamp := 0 })
                  actor .ok (.configured detecting) = .ok := by
              unfold machineDeallocHook
              split
              · rfl
              · simp [hverdOk]
            refine ⟨?_, ?_, ?_, ?_⟩ <;>
              simp [KeyedAllocWorld.deallocateMachine, KeyedAllocWorld.deallocate,
                KeyedAllocWorld.insertLive, KeyedAllocWorld.setRace,
                KeyedAllocWorld.removeLive, KeyedAllocWorld.insertDead, KeyedAllocWorld.removeRace,
                KeyedAllocWorld.findLive?, KeyedAllocWorld.findRace?, KeyedAllocWorld.findDead?,
                hhookOk, hdead₁, hmut_false]

private theorem findExtraReaderRace_isSome_of_mem (actor : DeallocActor) :
    ∀ (extra : List (UInt32 × UInt64)),
      (∃ p ∈ extra, p.1 ≠ actor.thread ∧ actor.viewFor p.1 < p.2) →
      ∃ th ts, findExtraReaderRace actor extra = some (th, ts)
  | [], ⟨_, hmem, _⟩ => nomatch hmem
  | (rt, rts) :: rest, ⟨p, hmem, hne, hlt⟩ => by
    unfold findExtraReaderRace
    cases hcond : (rt != actor.thread && decide (actor.viewFor rt < rts)) with
    | true =>
      simp only [↓reduceIte]
      exact ⟨rt, rts, rfl⟩
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      rcases List.mem_cons.mp hmem with rfl | hmemRest
      · have hneB : (rt != actor.thread) = true := bne_iff_ne.mpr hne
        have hltD : decide (actor.viewFor rt < rts) = true := decide_eq_true hlt
        rw [hneB, hltD] at hcond
        nomatch hcond
      · exact findExtraReaderRace_isSome_of_mem actor rest ⟨p, hmemRest, hne, hlt⟩

/-- **Multi-Reader & Per-Thread Vector-Clock Race Detection
(`keyedDeallocateMachine_perThreadClock_catches_unsynced_reader`, `[adv A2]`)**: even when `actor`
has synchronized with `clk.writerThread` (`actor.viewFor clk.writerThread ≥ clk.writeTimestamp`,
e.g. a large scalar `observedTimestamp`) AND with `clk.lastReaderThread`, an unsynchronized
concurrent read `(rThread, rTs) ∈ clk.extraReaders` (`rThread ≠ actor.thread`,
`actor.viewFor rThread < rTs`) deterministically faults with `.error (.hookFailure "DataRace")`,
closing B2's single-reader and single-scalar-view gap against `Miri.Concurrency.VClockAlloc`. -/
theorem keyedDeallocateMachine_perThreadClock_catches_unsynced_reader
    (w : KeyedAllocWorld) (id : MiriAllocId) (entry : LocalAllocEntry) (clk : RaceClockEntry)
    (actor : DeallocActor) (rThread : UInt32) (rTs : UInt64) (tb : DeallocHookSpec)
    (hlive : w.findLive? id = some entry)
    (hsz : entry.sizeBytes ≠ 0)
    (hmut : entry.mutability = .mut)
    (hnodead : w.findDead? id = none)
    (hrace : w.findRace? id = some clk)
    (hmem : (rThread, rTs) ∈ clk.extraReaders)
    (hne : rThread ≠ actor.thread)
    (hunobs : actor.viewFor rThread < rTs) :
    (w.deallocateMachine (.provenanced id 0)
      (some (entry.sizeBytes, entry.alignBytes)) entry.kind actor tb).2.2 =
      .error (.hookFailure "DataRace") := by
  obtain ⟨th, ts, hextra⟩ := findExtraReaderRace_isSome_of_mem actor clk.extraReaders
    ⟨(rThread, rTs), hmem, hne, hunobs⟩
  have hracy : raceDeallocVerdict actor clk ≠ .ok := by
    unfold raceDeallocVerdict
    dsimp only
    split
    · intro h; nomatch h
    · split
      · intro h; nomatch h
      · rw [hextra]
        intro h; nomatch h
  exact (keyedDeallocateMachine_race_checked_before_cleanup w id entry clk actor tb
    hlive hsz hmut hnodead hrace hracy).2.1

/-! ## Section 3: Part 2 — `#[rustc_no_writable]` (`charon#1619` + `minirust#295`) & Static-Access Temporary Retags (`charon#1620`) -/

/-! ### Part 2A: Per-Parameter `FnEntryRetagPolicy` (`writableChildWrite` vs. `rustcNoWritable`) -/

/-- Per-parameter function-entry retag policy (`charon#1619` + `minirust#295`):
- `.writableChildWrite`: ordinary `&mut T` parameter without `#[rustc_no_writable]`; when
  `implicitWrites = true`, `Unpin`, and `len > 0`, `FnEntry` retag performs an implicit child write.
- `.rustcNoWritable`: parameter bearing `#[rustc_no_writable]` (such as `core::mem::forget` and
  `<[T]>::get_mut`); suppresses the `FnEntry` implicit child write while still minting the
  protected `.reservedFrz false` child tag in the borrow tree. -/
inductive FnEntryRetagPolicy where
  | writableChildWrite
  | rustcNoWritable
  deriving DecidableEq, Repr, Inhabited

/-- Compiler type predicates supplied to `Miri.TreeBorrows.RetagPolicy.create`. -/
structure RetagTypeFacts where
  isFreeze : Bool
  isUnpin : Bool
  isUnsafeUnpin : Bool
  deriving DecidableEq, Repr, Inhabited

def RetagTypeFacts.tyIsUnpin (facts : RetagTypeFacts) : Bool :=
  facts.isUnpin && facts.isUnsafeUnpin

inductive RetagRefKind where
  | shared
  | mutable
  | box
  deriving DecidableEq, Repr, Inhabited

inductive ProtectorStrength where
  | strong
  | weak
  deriving DecidableEq, Repr

/-- Selected permissions for `RetagMode.FnEntry` (`Miri.TreeBorrows.RetagPolicy.NewPermission`),
expressed in `Anneal.Memory.AbstractPerm`. -/
structure SelectedFnEntryPerm where
  freezePerm : AbstractPerm
  nonfreezePerm : AbstractPerm
  outsidePerm : AbstractPerm
  protector : ProtectorStrength
  performsImplicitWrite : Bool
  deriving DecidableEq, Repr

/-- Exact `Miri.TreeBorrows.RetagPolicy.create` policy selection at `RetagMode.FnEntry`. -/
def selectFnEntryPolicy (facts : RetagTypeFacts) (kind : RetagRefKind)
    (implicitWrites : Bool) (paramPolicy : FnEntryRetagPolicy) : Option SelectedFnEntryPerm :=
  if (kind == .mutable || kind == .box) && !facts.tyIsUnpin then
    none
  else
    let doImplicitWrite :=
      (kind == .mutable || kind == .box) && implicitWrites &&
        paramPolicy == .writableChildWrite
    match kind with
    | .shared =>
      some {
        freezePerm := .frozen
        nonfreezePerm := .cell
        outsidePerm := if facts.isFreeze then .frozen else .cell
        protector := .strong
        performsImplicitWrite := false
      }
    | .mutable =>
      some {
        freezePerm := if doImplicitWrite then .active else .reservedFrz false
        nonfreezePerm := if doImplicitWrite then .active else .reservedFrz false
        outsidePerm := .reservedFrz false
        protector := .strong
        performsImplicitWrite := doImplicitWrite
      }
    | .box =>
      some {
        freezePerm := if doImplicitWrite then .active else .reservedFrz false
        nonfreezePerm := if doImplicitWrite then .active else .reservedFrz false
        outsidePerm := .reservedFrz false
        protector := .weak
        performsImplicitWrite := doImplicitWrite
      }

/-- `!Unpin` mutable references and `Box` skip `FnEntry` retagging (`Miri.TreeBorrows.RetagPolicy`). -/
theorem pinned_mutable_or_box_fnEntry_skips_retag (facts : RetagTypeFacts)
    (kind : RetagRefKind) (implicitWrites : Bool) (paramPolicy : FnEntryRetagPolicy)
    (hkind : kind = .mutable ∨ kind = .box)
    (hpinned : facts.tyIsUnpin = false) :
    selectFnEntryPolicy facts kind implicitWrites paramPolicy = none := by
  rcases hkind with rfl | rfl <;> simp [selectFnEntryPolicy, hpinned]

/-- Under `rustcNoWritable`, an `Unpin` `&mut T` mints a strong-protected `.reservedFrz false`
policy with `performsImplicitWrite = false`, regardless of `implicitWrites` or `isFreeze`. -/
theorem selectFnEntryPolicy_rustcNoWritable_mut (facts : RetagTypeFacts)
    (implicitWrites : Bool) (hunpin : facts.tyIsUnpin = true) :
    selectFnEntryPolicy facts .mutable implicitWrites .rustcNoWritable =
      some {
        freezePerm := .reservedFrz false
        nonfreezePerm := .reservedFrz false
        outsidePerm := .reservedFrz false
        protector := .strong
        performsImplicitWrite := false
      } := by
  simp [selectFnEntryPolicy, hunpin]

/-! ### `[adv B1]` Verbatim Mirror of Pinned `Miri.TreeBorrows.RetagPolicy.create`

`lean-miri/vendor/Miri` is not a Lake library of this workspace, so the pinned upstream policy
(`lean-miri/vendor/Miri/TreeBorrows/RetagPolicy.lean`, which *already* carries
`PolicyConfig.rustcNoWritable`) is transcribed verbatim below and `selectFnEntryPolicy` is proved
equal to it on every input at `RetagMode.FnEntry`. -/

namespace MiriRetagPolicyMirror

/-- `Miri.TreeBorrows.Permission` (pinned `Permissions.lean`). -/
inductive Permission where
  | Cell
  | ReservedIM
  | ReservedFrz (conflicted : Bool)
  | Unique
  | Frozen
  | Disabled
  deriving DecidableEq, Repr

inductive AccessKind where
  | Read
  | Write
  deriving DecidableEq, Repr

/-- `Permission.associatedAccess`: the parent access a reborrow performs for a byte carrying this
initial permission (`RetagPipeline.accessTreeForReborrow`). -/
def Permission.associatedAccess : Permission → Option AccessKind
  | .Cell => none
  | .Unique => some .Write
  | _ => some .Read

def Permission.toAbstractPerm : Permission → AbstractPerm
  | .Cell => .cell
  | .ReservedIM => .reservedIM
  | .ReservedFrz c => .reservedFrz c
  | .Unique => .active
  | .Frozen => .frozen
  | .Disabled => .disabled

inductive RetagMode where
  | None
  | Default
  | TwoPhase
  | FnEntry
  | Raw
  deriving DecidableEq, Repr

inductive ReferenceKind where
  | Shared
  | Mutable
  | Box
  deriving DecidableEq, Repr

structure TypeFacts where
  isUnpin : Bool
  isUnsafeUnpin : Bool
  isFreeze : Bool
  deriving DecidableEq, Repr

structure PolicyConfig where
  implicitWrites : Bool
  rustcNoWritable : Bool
  deriving DecidableEq, Repr

inductive ProtectorKind where
  | WeakProtector
  | StrongProtector
  deriving DecidableEq, Repr

def ProtectorKind.toStrength : ProtectorKind → ProtectorStrength
  | .WeakProtector => .weak
  | .StrongProtector => .strong

structure NewPermission where
  freezePermission : Permission
  nonfreezePermission : Permission
  outsidePermission : Permission
  protector : Option ProtectorKind
  deriving DecidableEq, Repr

inductive Part where
  | InsideFrozen
  | InsideUnsafeCell
  | Outside
  deriving DecidableEq, Repr

def selectedPermission (kind : ReferenceKind) (part : Part)
    (frozen isProtected implicitWrites : Bool) : Permission :=
  match kind with
  | .Shared => if frozen then .Frozen else .Cell
  | .Mutable | .Box =>
      if implicitWrites && part != .Outside then .Unique
      else if isProtected || frozen then .ReservedFrz false
      else .ReservedIM

def create (facts : TypeFacts) (kind : ReferenceKind) (mode : RetagMode)
    (config : PolicyConfig) : Option NewPermission := Id.run do
  if mode == .None then return none
  let tyIsUnpin := facts.isUnpin && facts.isUnsafeUnpin
  let isProtected := mode == .FnEntry
  let implicitWritesEnabled := isProtected && config.implicitWrites &&
    !config.rustcNoWritable
  if (kind == .Mutable || kind == .Box) && !tyIsUnpin then
    return none
  let choose (part : Part) :=
    let frozen := match part with
      | .InsideFrozen => true
      | .InsideUnsafeCell => false
      | .Outside => facts.isFreeze
    selectedPermission kind part frozen isProtected implicitWritesEnabled
  let protector :=
    if isProtected then
      some (if kind == .Box then .WeakProtector else .StrongProtector)
    else none
  return some {
    freezePermission := choose .InsideFrozen
    nonfreezePermission := choose .InsideUnsafeCell
    outsidePermission := choose .Outside
    protector
  }

end MiriRetagPolicyMirror

def RetagRefKind.toMirror : RetagRefKind → MiriRetagPolicyMirror.ReferenceKind
  | .shared => .Shared
  | .mutable => .Mutable
  | .box => .Box

/-- **`selectFnEntryPolicy` = Upstream `RetagPolicy.create` at `FnEntry`
(`selectFnEntryPolicy_eq_upstream_create`, `[adv B1]`)**: for *every* type-fact triple, reference
kind, `implicitWrites` flag, and `#[rustc_no_writable]` bit, the prototype policy agrees with the
verbatim transcription of pinned `RetagPolicy.create … .FnEntry ⟨implicitWrites, rustcNoWritable⟩`
on all three permissions and the protector (including the `!Unpin` `none` early return), and its
`performsImplicitWrite` flag is exactly "upstream's inside-frozen permission performs a `.Write`
parent access" (`associatedAccess .Unique = some .Write`), i.e. the A0 flag is not an invented knob. -/
theorem selectFnEntryPolicy_eq_upstream_create (facts : RetagTypeFacts) (kind : RetagRefKind)
    (implicitWrites rustcNoWritable : Bool) :
    (selectFnEntryPolicy facts kind implicitWrites
        (if rustcNoWritable then .rustcNoWritable else .writableChildWrite)).map
      (fun s => (s.freezePerm, s.nonfreezePerm, s.outsidePerm, some s.protector,
        s.performsImplicitWrite)) =
    (MiriRetagPolicyMirror.create ⟨facts.isUnpin, facts.isUnsafeUnpin, facts.isFreeze⟩
        kind.toMirror .FnEntry ⟨implicitWrites, rustcNoWritable⟩).map
      (fun n => (n.freezePermission.toAbstractPerm, n.nonfreezePermission.toAbstractPerm,
        n.outsidePermission.toAbstractPerm, n.protector.map MiriRetagPolicyMirror.ProtectorKind.toStrength,
        n.freezePermission.associatedAccess == some .Write)) := by
  rcases facts with ⟨isFreeze, isUnpin, isUnsafeUnpin⟩
  cases kind <;> cases implicitWrites <;> cases rustcNoWritable <;> cases isFreeze <;>
    cases isUnpin <;> cases isUnsafeUnpin <;> decide

/-- Per-parameter `#[rustc_no_writable]` attribute map keyed by MIR parameter `LocalIdx` (`Nat`)
using `ExtTreeMap0`, defaulting to `.writableChildWrite` when absent (`charon#1619`). -/
structure FnParamRetagMap where
  byLocal : ExtTreeMap0 Nat FnEntryRetagPolicy := ∅

def FnParamRetagMap.set (m : FnParamRetagMap) (paramLocal : LocalIdx)
    (policy : FnEntryRetagPolicy) : FnParamRetagMap :=
  ⟨m.byLocal.insert paramLocal policy⟩

def FnParamRetagMap.policyFor (m : FnParamRetagMap) (paramLocal : LocalIdx) : FnEntryRetagPolicy :=
  (m.byLocal.get? paramLocal).getD .writableChildWrite

theorem FnParamRetagMap.policyFor_set (m : FnParamRetagMap) (p q : LocalIdx)
    (pol : FnEntryRetagPolicy) :
    (m.set p pol).policyFor q = if p = q then pol else m.policyFor q := by
  unfold FnParamRetagMap.set FnParamRetagMap.policyFor
  rw [ExtTreeMap0.get?_insert]
  simp only [LawfulEqCmp.compare_eq_iff_eq (cmp := (compare : Nat → Nat → Ordering))]
  split <;> rfl

/-- Byte-level Tree Borrows node in an allocation's borrow tree, carrying real `Trusted`
`TreeBorrowPerm` (including the `ReservedFrz { conflicted }` latch!), byte range, parent link, and
optional protector token, bridged directly to `Anneal.Memory.ByteRangePerm`. -/
structure TreeTagNode where
  tag : Nat
  allocId : Nat
  offset : Nat
  len : Nat
  perm : TreeBorrowPerm
  protector : Option Nat := none
  parentTag : Option Nat := none
  deriving DecidableEq, Repr

def TreeTagNode.toByteRangePerm (node : TreeTagNode) : ByteRangePerm where
  tag := node.tag
  allocId := node.allocId
  offset := node.offset
  len := node.len
  perm := TreeBorrowPerm.toAbstractPerm node.perm
  protector := node.protector

def TreeTagNode.isProtected (node : TreeTagNode) (ps : ProtectorSet) : Bool :=
  match node.protector with
  | some lft => ps.contains lft
  | none => false

@[simp]
theorem TreeTagNode.isProtected_eq_toByteRangePerm (node : TreeTagNode) (ps : ProtectorSet) :
    node.isProtected ps = node.toByteRangePerm.isProtected ps := rfl

/-- Allocation byte + borrow-tree world for `FnEntry` retagging and subsequent reads/writes. -/
structure FnEntryBorrowWorld where
  allocId : Nat
  bytes : List AbstractByte
  nodes : List TreeTagNode
  activeProtectors : ProtectorSet := ProtectorSet.empty
  nextTag : Nat := 1
  nextProtector : Nat := 1
  deriving DecidableEq, Repr

inductive RetagStepErr where
  | parentTagMissing
  | parentDisabled
  | ancestorWriteForbidden
  | protectedForeignConflict
  | uninitializedPointeeWrite
  | conflictedProtectedChildWrite
  | outOfBounds
  deriving DecidableEq, Repr

def findTagNode? (nodes : List TreeTagNode) (tag : Nat) : Option TreeTagNode :=
  nodes.find? (fun n => Nat.beq n.tag tag)

def isDescendantOrSelfAux : Nat → List TreeTagNode → Nat → Nat → Bool
  | 0, _, _, _ => false
  | fuel + 1, nodes, childTag, ancTag =>
    if Nat.beq childTag ancTag then true
    else
      match findTagNode? nodes childTag with
      | none => false
      | some node =>
        match node.parentTag with
        | none => false
        | some pTag => isDescendantOrSelfAux fuel nodes pTag ancTag

def isDescendantOrSelf (nodes : List TreeTagNode) (childTag ancTag : Nat) : Bool :=
  isDescendantOrSelfAux (nodes.length + 1) nodes childTag ancTag

def stepNodeOnRangeRead (allNodes : List TreeTagNode) (ps : ProtectorSet)
    (readAlloc off len readerTag : Nat) (node : TreeTagNode) : Except RetagStepErr TreeTagNode :=
  if Nat.beq len 0 then
    .ok node
  else if isDescendantOrSelf allNodes readerTag node.tag then
    if !(Nat.beq node.allocId readAlloc) then .ok node
    else
      match node.perm with
      | .disabled => .error .parentDisabled
      | _ => .ok node
  else if byteRangeOverlapsWrite node.toByteRangePerm readAlloc off len then
    let prot := node.isProtected ps
    match node.perm with
    | .cell | .frozen | .disabled => .ok node
    | .reservedIM => .ok node
    | .reservedFrz conflicted =>
      .ok { node with perm := .reservedFrz (if prot then true else conflicted) }
    | .unique =>
      if prot then .error .protectedForeignConflict
      else .ok { node with perm := .frozen }
  else
    .ok node

def stepNodeOnRangeWrite (allNodes : List TreeTagNode) (ps : ProtectorSet)
    (writeAlloc off len writerTag : Nat) (node : TreeTagNode) : Except RetagStepErr TreeTagNode :=
  if Nat.beq len 0 then
    .ok node
  else if isDescendantOrSelf allNodes writerTag node.tag then
    if !(Nat.beq node.allocId writeAlloc) then .ok node
    else
      let prot := node.isProtected ps
      match node.perm with
      | .cell => .ok node
      | .frozen | .disabled => .error .ancestorWriteForbidden
      | .reservedFrz true =>
        if prot then .error .conflictedProtectedChildWrite
        else .ok { node with perm := .unique }
      | .reservedFrz false | .reservedIM | .unique =>
        .ok { node with perm := .unique }
  else if byteRangeOverlapsWrite node.toByteRangePerm writeAlloc off len then
    if node.isProtected ps then
      match node.perm with
      | .disabled | .cell => .ok node
      | _ => .error .protectedForeignConflict
    else
      let nextPerm : TreeBorrowPerm :=
        match node.perm with
        | .cell => .cell
        | .reservedIM => .reservedIM
        | _ => .disabled
      .ok { node with perm := nextPerm }
  else
    .ok node

def mapNodesM {ε : Type} (f : TreeTagNode → Except ε TreeTagNode) :
    List TreeTagNode → Except ε (List TreeTagNode)
  | [] => .ok []
  | n :: ns => do
    let n' ← f n
    let ns' ← mapNodesM f ns
    return n' :: ns'

/-- Execute a `RetagMode.FnEntry` reborrow of `&mut T` (`parentTag`, `[off, off + len)`) under
`facts`, `implicitWrites`, `paramPolicy`, and `requireInitOnImplicitWrite`. -/
def execFnEntryMutRetag (w : FnEntryBorrowWorld) (parentTag off len : Nat)
    (facts : RetagTypeFacts) (implicitWrites : Bool) (paramPolicy : FnEntryRetagPolicy)
    (requireInitOnImplicitWrite : Bool := false) :
    Except RetagStepErr (FnEntryBorrowWorld × Option Nat) := do
  match selectFnEntryPolicy facts .mutable implicitWrites paramPolicy with
  | none =>
    return (w, none)
  | some selected =>
    let some parentNode := findTagNode? w.nodes parentTag
      | throw RetagStepErr.parentTagMissing
    if parentNode.perm == .disabled then
      throw RetagStepErr.parentDisabled
    if off + len > w.bytes.length then
      throw RetagStepErr.outOfBounds
    let childTag := w.nextTag
    let protId := w.nextProtector
    let ps' := w.activeProtectors.insert protId
    let nodesAfterRead ←
      if Nat.beq len 0 then .ok w.nodes
      else mapNodesM (stepNodeOnRangeRead w.nodes w.activeProtectors w.allocId off len parentTag) w.nodes
    let childNode : TreeTagNode := {
      tag := childTag
      allocId := w.allocId
      offset := off
      len := len
      perm := .reservedFrz false
      protector := some protId
      parentTag := some parentTag
    }
    let withChild := childNode :: nodesAfterRead
    if selected.performsImplicitWrite && !(Nat.beq len 0) then
      let slice := (w.bytes.drop off).take len
      if requireInitOnImplicitWrite && !(allBytesInitialized slice) then
        throw RetagStepErr.uninitializedPointeeWrite
      let nodesAfterWrite ←
        mapNodesM (stepNodeOnRangeWrite withChild ps' w.allocId off len childTag) withChild
      return ({
        w with
        nodes := nodesAfterWrite
        activeProtectors := ps'
        nextTag := childTag + 1
        nextProtector := protId + 1
      }, some childTag)
    else
      return ({
        w with
        nodes := withChild
        activeProtectors := ps'
        nextTag := childTag + 1
        nextProtector := protId + 1
      }, some childTag)

/-- Perform a subsequent read of `[off, off + len)` through `readerTag` on `FnEntryBorrowWorld`. -/
def execBorrowRead (w : FnEntryBorrowWorld) (readerTag off len : Nat) :
    Except RetagStepErr FnEntryBorrowWorld := do
  if off + len > w.bytes.length then throw RetagStepErr.outOfBounds
  let nodes' ← mapNodesM (stepNodeOnRangeRead w.nodes w.activeProtectors w.allocId off len readerTag) w.nodes
  return { w with nodes := nodes' }

/-- Perform an explicit write of `newBytes` at `[off, off + newBytes.length)` through `writerTag`. -/
def execBorrowWrite (w : FnEntryBorrowWorld) (writerTag off : Nat) (newBytes : List AbstractByte) :
    Except RetagStepErr FnEntryBorrowWorld := do
  let len := newBytes.length
  if off + len > w.bytes.length then throw RetagStepErr.outOfBounds
  let nodes' ← mapNodesM (stepNodeOnRangeWrite w.nodes w.activeProtectors w.allocId off len writerTag) w.nodes
  let some bytes' := writeAbstractBytesAt w.bytes off newBytes
    | throw RetagStepErr.outOfBounds
  return { w with nodes := nodes', bytes := bytes' }

/-- **ZST No-Write Theorem (`fnEntryMutRetag_zst_no_write`)**: when `len = 0` (`&mut ()`),
`execFnEntryMutRetag` produces the **exact same** world and `.reservedFrz false` child under both
`.writableChildWrite` and `.rustcNoWritable`, performing zero byte-range write invalidations. -/
theorem fnEntryMutRetag_zst_no_write (w : FnEntryBorrowWorld) (parentTag off : Nat)
    (facts : RetagTypeFacts) (implicitWrites requireInit : Bool) :
    execFnEntryMutRetag w parentTag off 0 facts implicitWrites .writableChildWrite requireInit =
      execFnEntryMutRetag w parentTag off 0 facts implicitWrites .rustcNoWritable requireInit := by
  unfold execFnEntryMutRetag selectFnEntryPolicy
  cases facts.tyIsUnpin <;> simp [Bind.bind, Except.bind]

/-- **Foreign-Write Protector Bridge (`stepNodeOnRangeWrite_foreign_protected_conflict`)**: any
overlapping foreign write (`isDescendantOrSelf = false`) to a protected live non-`.cell`
`TreeTagNode` fails with `.error .protectedForeignConflict`, agreeing with
`Anneal.Memory.protector_forbids_conflicting_foreign_write`. -/
theorem stepNodeOnRangeWrite_foreign_protected_conflict
    (allNodes : List TreeTagNode) (ps : ProtectorSet)
    (writeAlloc off len writerTag : Nat) (node : TreeTagNode)
    (hlen : Nat.beq len 0 = false)
    (hforeign : isDescendantOrSelf allNodes writerTag node.tag = false)
    (hoverlap : byteRangeOverlapsWrite node.toByteRangePerm writeAlloc off len = true)
    (hprot : node.isProtected ps = true)
    (hlive : node.perm ≠ .disabled)
    (hnotCell : node.perm ≠ .cell) :
    stepNodeOnRangeWrite allNodes ps writeAlloc off len writerTag node =
      .error .protectedForeignConflict ∧
    stepForeignWriteByteRange ps node.toByteRangePerm writeAlloc off len = none := by
  refine ⟨?_, ?_⟩
  · unfold stepNodeOnRangeWrite
    rw [hlen, hforeign, hoverlap, hprot]
    cases hp : node.perm <;> simp_all
  · apply protector_forbids_conflicting_foreign_write ps node.toByteRangePerm writeAlloc off len
      hoverlap hprot
    · intro hd
      apply hlive
      unfold TreeTagNode.toByteRangePerm at hd
      cases hp : node.perm <;> simp_all [TreeBorrowPerm.toAbstractPerm]
    · intro hc
      apply hnotCell
      unfold TreeTagNode.toByteRangePerm at hc
      cases hp : node.perm <;> simp_all [TreeBorrowPerm.toAbstractPerm]

/-- Canonical two-branch borrow tree (`root` `tag = 1` in `.unique` + unprotected sibling `tag = 2`
in `.frozen` over `[0, len)`) used to state general `FnEntry` policy separation theorems. -/
def mkTwoBranchBorrowWorld (allocId len : Nat) (bytes : List AbstractByte) : FnEntryBorrowWorld where
  allocId := allocId
  bytes := bytes
  nodes := [
    ⟨2, allocId, 0, len, .frozen, none, some 1⟩,
    ⟨1, allocId, 0, len, .unique, none, none⟩
  ]
  activeProtectors := ProtectorSet.empty
  nextTag := 3
  nextProtector := 1

/-- **General `#[rustc_no_writable]` Separation Theorem (`rustcNoWritable_preserves_uninit_and_frozen_sibling`)**:
for any `allocId`, `0 < len ≤ bytes.length`, and `Unpin` `facts`:
1. Under `.rustcNoWritable`, `execFnEntryMutRetag` with `implicitWrites = true` and
   `requireInitOnImplicitWrite = true` **succeeds** even when `bytes` is uninitialized, minting
   protected child `tag = 3` in `.reservedFrz false` while preserving sibling `tag = 2` at `.frozen`!
2. Under `.writableChildWrite` with `requireInitOnImplicitWrite = true` on uninitialized bytes,
   `execFnEntryMutRetag` **faults** with `.error .uninitializedPointeeWrite`!
3. Under `.writableChildWrite` with `requireInitOnImplicitWrite = false`, `execFnEntryMutRetag`
   activates child `tag = 3` to `.unique` and **disables** sibling `tag = 2` (`.disabled`)! -/
theorem rustcNoWritable_preserves_uninit_and_frozen_sibling
    (allocId len : Nat) (bytes : List AbstractByte) (facts : RetagTypeFacts)
    (hlen : 0 < len) (hbound : len ≤ bytes.length) (hunpin : facts.tyIsUnpin = true) :
    let w := mkTwoBranchBorrowWorld allocId len bytes
    execFnEntryMutRetag w 1 0 len facts true .rustcNoWritable true =
      .ok ({
        w with
        nodes := [
          ⟨3, allocId, 0, len, .reservedFrz false, some 1, some 1⟩,
          ⟨2, allocId, 0, len, .frozen, none, some 1⟩,
          ⟨1, allocId, 0, len, .unique, none, none⟩
        ]
        activeProtectors := ProtectorSet.empty.insert 1
        nextTag := 4
        nextProtector := 2
      }, some 3) ∧
    (allBytesInitialized ((bytes.drop 0).take len) = false →
      execFnEntryMutRetag w 1 0 len facts true .writableChildWrite true =
        .error .uninitializedPointeeWrite) ∧
    execFnEntryMutRetag w 1 0 len facts true .writableChildWrite false =
      .ok ({
        w with
        nodes := [
          ⟨3, allocId, 0, len, .unique, some 1, some 1⟩,
          ⟨2, allocId, 0, len, .disabled, none, some 1⟩,
          ⟨1, allocId, 0, len, .unique, none, none⟩
        ]
        activeProtectors := ProtectorSet.empty.insert 1
        nextTag := 4
        nextProtector := 2
      }, some 3) := by
  have hlen0 : Nat.beq len 0 = false := by
    cases len with
    | zero => omega
    | succ _ => rfl
  have hov : ∀ (tg : Nat) (p : AbstractPerm) (pr : Option Nat),
      byteRangeOverlapsWrite ⟨tg, allocId, 0, len, p, pr⟩ allocId 0 len = true := by
    intro tg p pr
    unfold byteRangeOverlapsWrite
    simp only [Nat.beq_refl, Bool.true_and]
    unfold byteRangesOverlapBool
    cases len with
    | zero => omega
    | succ _ => rfl
  refine ⟨?_, ?_, ?_⟩
  · unfold mkTwoBranchBorrowWorld execFnEntryMutRetag selectFnEntryPolicy
    simp [hunpin, findTagNode?, hbound, hlen0, mapNodesM, stepNodeOnRangeRead,
      isDescendantOrSelf, isDescendantOrSelfAux, TreeTagNode.toByteRangePerm,
      TreeBorrowPerm.toAbstractPerm, hov, Bind.bind, Except.bind, Pure.pure, Except.pure]
  · intro huninit
    have huninit' : allBytesInitialized (bytes.take len) = false := by simpa using huninit
    unfold mkTwoBranchBorrowWorld execFnEntryMutRetag selectFnEntryPolicy
    simp [hunpin, findTagNode?, hbound, hlen0, huninit', mapNodesM, stepNodeOnRangeRead,
      isDescendantOrSelf, isDescendantOrSelfAux, TreeTagNode.toByteRangePerm,
      TreeBorrowPerm.toAbstractPerm, hov, Bind.bind, Except.bind, Pure.pure, Except.pure,
      throw, throwThe, MonadExceptOf.throw]
  · unfold mkTwoBranchBorrowWorld execFnEntryMutRetag selectFnEntryPolicy
    simp [hunpin, findTagNode?, hbound, hlen0, mapNodesM, stepNodeOnRangeRead,
      stepNodeOnRangeWrite, isDescendantOrSelf, isDescendantOrSelfAux,
      TreeTagNode.toByteRangePerm, TreeBorrowPerm.toAbstractPerm, TreeTagNode.isProtected, hov,
      Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- **General `ReservedFrz { conflicted }` Latch & Child-Write Activation Theorem
(`rustcNoWritable_foreignRead_latches_conflicted`)**: after `rustcNoWritable` `FnEntry` retag on
`mkTwoBranchBorrowWorld`:
1. A foreign read through sibling `tag = 2` succeeds and latches child `tag = 3` from
   `.reservedFrz false` to `.reservedFrz true` (`wLatched`), while a subsequent explicit write
   through child `tag = 3` while still protected faults with `.error .conflictedProtectedChildWrite`!
2. Conversely, without an intervening foreign read, an explicit write of `newBytes` through child
   `tag = 3` (`newBytes.length = len`) activates child `tag = 3` to `.unique` and disables foreign
   `.frozen` sibling `tag = 2` (`.disabled`)! -/
theorem rustcNoWritable_foreignRead_latches_conflicted
    (allocId : Nat) (bytes newBytes bytesAfter : List AbstractByte)
    (hlen : 0 < newBytes.length)
    (hbound : newBytes.length ≤ bytes.length)
    (hwrite : writeAbstractBytesAt bytes 0 newBytes = some bytesAfter) :
    let len := newBytes.length
    let ps := ProtectorSet.empty.insert 1
    let wAfter : FnEntryBorrowWorld := {
      allocId := allocId
      bytes := bytes
      nodes := [
        ⟨3, allocId, 0, len, .reservedFrz false, some 1, some 1⟩,
        ⟨2, allocId, 0, len, .frozen, none, some 1⟩,
        ⟨1, allocId, 0, len, .unique, none, none⟩
      ]
      activeProtectors := ps
      nextTag := 4
      nextProtector := 2
    }
    let wLatched : FnEntryBorrowWorld := {
      wAfter with
      nodes := [
        ⟨3, allocId, 0, len, .reservedFrz true, some 1, some 1⟩,
        ⟨2, allocId, 0, len, .frozen, none, some 1⟩,
        ⟨1, allocId, 0, len, .unique, none, none⟩
      ]
    }
    execBorrowRead wAfter 2 0 len = .ok wLatched ∧
    execBorrowWrite wLatched 3 0 newBytes = .error .conflictedProtectedChildWrite ∧
    execBorrowWrite wAfter 3 0 newBytes =
      .ok {
        wAfter with
        nodes := [
          ⟨3, allocId, 0, len, .unique, some 1, some 1⟩,
          ⟨2, allocId, 0, len, .disabled, none, some 1⟩,
          ⟨1, allocId, 0, len, .unique, none, none⟩
        ]
        bytes := bytesAfter
      } := by
  have hlen0 : Nat.beq newBytes.length 0 = false := by
    cases h : newBytes.length with
    | zero => omega
    | succ _ => rfl
  have hov : ∀ (tg : Nat) (p : AbstractPerm) (pr : Option Nat),
      byteRangeOverlapsWrite ⟨tg, allocId, 0, newBytes.length, p, pr⟩ allocId 0 newBytes.length = true := by
    intro tg p pr
    unfold byteRangeOverlapsWrite
    simp only [Nat.beq_refl, Bool.true_and]
    unfold byteRangesOverlapBool
    cases h : newBytes.length with
    | zero => omega
    | succ _ => rfl
  refine ⟨?_, ?_, ?_⟩
  · dsimp only
    unfold execBorrowRead
    simp [hbound, hlen0, mapNodesM, stepNodeOnRangeRead, findTagNode?,
      isDescendantOrSelf, isDescendantOrSelfAux, TreeTagNode.toByteRangePerm,
      TreeBorrowPerm.toAbstractPerm, TreeTagNode.isProtected, hov,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
  · dsimp only
    unfold execBorrowWrite
    simp [hbound, hlen0, mapNodesM, stepNodeOnRangeWrite,
      isDescendantOrSelf, isDescendantOrSelfAux, TreeTagNode.isProtected,
      Bind.bind, Except.bind, throw, throwThe, MonadExceptOf.throw]
  · dsimp only
    unfold execBorrowWrite
    simp [hbound, hlen0, hwrite, mapNodesM, stepNodeOnRangeWrite, findTagNode?,
      isDescendantOrSelf, isDescendantOrSelfAux, TreeTagNode.toByteRangePerm,
      TreeBorrowPerm.toAbstractPerm, TreeTagNode.isProtected, hov,
      Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- **World-Level Protector Conflict (`rustcNoWritable_parentWrite_faults_on_protected_child`,
`[adv B1]`)**: after a `.rustcNoWritable` `FnEntry` retag on `mkTwoBranchBorrowWorld`, an explicit
write through the *parent* tag `1` into the protected range faults with
`.protectedForeignConflict` at the `execBorrowWrite` level — the brief's "foreign writes to the
protected range still fault" (A0 proved only the node-level `stepNodeOnRangeWrite` instance). -/
theorem rustcNoWritable_parentWrite_faults_on_protected_child
    (allocId : Nat) (bytes newBytes : List AbstractByte)
    (hlen : 0 < newBytes.length) (hbound : newBytes.length ≤ bytes.length) :
    let len := newBytes.length
    let wAfter : FnEntryBorrowWorld := {
      allocId := allocId
      bytes := bytes
      nodes := [
        ⟨3, allocId, 0, len, .reservedFrz false, some 1, some 1⟩,
        ⟨2, allocId, 0, len, .frozen, none, some 1⟩,
        ⟨1, allocId, 0, len, .unique, none, none⟩
      ]
      activeProtectors := ProtectorSet.empty.insert 1
      nextTag := 4
      nextProtector := 2
    }
    execBorrowWrite wAfter 1 0 newBytes = .error .protectedForeignConflict := by
  have hlen0 : Nat.beq newBytes.length 0 = false := by
    cases h : newBytes.length with
    | zero => omega
    | succ _ => rfl
  have hov : ∀ (tg : Nat) (p : AbstractPerm) (pr : Option Nat),
      byteRangeOverlapsWrite ⟨tg, allocId, 0, newBytes.length, p, pr⟩ allocId 0
        newBytes.length = true := by
    intro tg p pr
    unfold byteRangeOverlapsWrite
    simp only [Nat.beq_refl, Bool.true_and]
    unfold byteRangesOverlapBool
    cases h : newBytes.length with
    | zero => omega
    | succ _ => rfl
  dsimp only
  unfold execBorrowWrite
  simp [hbound, hlen0, mapNodesM, stepNodeOnRangeWrite, findTagNode?,
    isDescendantOrSelf, isDescendantOrSelfAux, TreeTagNode.toByteRangePerm,
    TreeBorrowPerm.toAbstractPerm, TreeTagNode.isProtected, hov,
    Bind.bind, Except.bind, throw, throwThe, MonadExceptOf.throw]

/-- Upstream `RetagPipeline.accessTreeForReborrow` single-parent-access execution (`[adv A1]`):
instead of performing a parent `.Read`, inserting `.reservedFrz false`, and performing a child
`.Write`, upstream performs **one** parent access determined by `selected.performsImplicitWrite`
(`stepNodeOnRangeWrite` on `parentTag` when `performsImplicitWrite && len > 0`, else
`stepNodeOnRangeRead` on `parentTag` when `len > 0`) and inserts `childTag` directly in its
initial permission (`.unique` when `performsImplicitWrite && len > 0`, else `.reservedFrz false`). -/
def execFnEntryMutRetagUpstream (w : FnEntryBorrowWorld) (parentTag off len : Nat)
    (facts : RetagTypeFacts) (implicitWrites : Bool) (paramPolicy : FnEntryRetagPolicy) :
    Except RetagStepErr (FnEntryBorrowWorld × Option Nat) := do
  match selectFnEntryPolicy facts .mutable implicitWrites paramPolicy with
  | none =>
    return (w, none)
  | some selected =>
    let some parentNode := findTagNode? w.nodes parentTag
      | throw RetagStepErr.parentTagMissing
    if parentNode.perm == .disabled then
      throw RetagStepErr.parentDisabled
    if off + len > w.bytes.length then
      throw RetagStepErr.outOfBounds
    let childTag := w.nextTag
    let protId := w.nextProtector
    let ps' := w.activeProtectors.insert protId
    let doWrite := selected.performsImplicitWrite && !(Nat.beq len 0)
    let nodesAfterParent ←
      if Nat.beq len 0 then
        .ok w.nodes
      else if doWrite then
        mapNodesM (stepNodeOnRangeWrite w.nodes w.activeProtectors w.allocId off len parentTag) w.nodes
      else
        mapNodesM (stepNodeOnRangeRead w.nodes w.activeProtectors w.allocId off len parentTag) w.nodes
    let childNode : TreeTagNode := {
      tag := childTag
      allocId := w.allocId
      offset := off
      len := len
      perm := if doWrite then .unique else .reservedFrz false
      protector := some protId
      parentTag := some parentTag
    }
    return ({
      w with
      nodes := childNode :: nodesAfterParent
      activeProtectors := ps'
      nextTag := childTag + 1
      nextProtector := protId + 1
    }, some childTag)

/-- **Node-Level Read-Then-Child-Write = Single Parent-Write (`stepNode_read_then_childWrite_eq_parentWrite`,
`[adv A1]`)**: for **every** foreign node (across all 6 permissions and both protected/unprotected
states) and **every** non-`.disabled` ancestor node, composing `stepNodeOnRangeRead` for `parentTag`
with `stepNodeOnRangeWrite` for fresh `childTag` produces the **exact same** node state and error
diagnostic as a single `stepNodeOnRangeWrite` for `parentTag`! -/
theorem stepNode_read_then_childWrite_eq_parentWrite
    (allNodes withChild : List TreeTagNode) (ps ps' : ProtectorSet)
    (allocId off len parentTag childTag : Nat) (node : TreeTagNode)
    (hdesc : isDescendantOrSelf withChild childTag node.tag =
      isDescendantOrSelf allNodes parentTag node.tag)
    (hprot : node.isProtected ps' = node.isProtected ps)
    (hnoDisabledAnc :
      isDescendantOrSelf allNodes parentTag node.tag = true →
      Nat.beq node.allocId allocId = true →
      node.perm ≠ .disabled) :
    (stepNodeOnRangeRead allNodes ps allocId off len parentTag node >>=
      stepNodeOnRangeWrite withChild ps' allocId off len childTag) =
    stepNodeOnRangeWrite allNodes ps allocId off len parentTag node := by
  rcases node with ⟨tg, nAlloc, nOff, nLen, perm, prot, pTag⟩
  dsimp only [TreeTagNode.isProtected] at hdesc hprot hnoDisabledAnc
  change Except.bind (stepNodeOnRangeRead allNodes ps allocId off len parentTag
      ⟨tg, nAlloc, nOff, nLen, perm, prot, pTag⟩)
      (stepNodeOnRangeWrite withChild ps' allocId off len childTag) =
    stepNodeOnRangeWrite allNodes ps allocId off len parentTag
      ⟨tg, nAlloc, nOff, nLen, perm, prot, pTag⟩
  unfold stepNodeOnRangeRead stepNodeOnRangeWrite byteRangeOverlapsWrite
    TreeTagNode.toByteRangePerm TreeTagNode.isProtected
  cases hlen : Nat.beq len 0
  · cases hanc : isDescendantOrSelf allNodes parentTag tg
    · cases hov : (Nat.beq nAlloc allocId && byteRangesOverlapBool nOff nLen off len)
      · simp only [Bool.false_eq_true, ↓reduceIte, Except.bind, hdesc, hanc, hov]
      · cases perm
        case reservedFrz conf =>
          cases conf <;>
            cases hpr : (match prot with | some lft => ps.contains lft | none => false) <;>
            simp only [Bool.false_eq_true, ↓reduceIte, Except.bind, hdesc, hanc, hov, hprot, hpr]
        case unique =>
          cases hpr : (match prot with | some lft => ps.contains lft | none => false)
          · simp only [Bool.false_eq_true, ↓reduceIte, Except.bind, hdesc, hanc, hov, hprot, hpr]
          · rfl
        all_goals
          simp only [Bool.false_eq_true, ↓reduceIte, Except.bind, hdesc, hanc, hov, hprot]
    · cases halloc : Nat.beq nAlloc allocId
      · simp only [Bool.false_eq_true, Bool.not_false, ↓reduceIte, Except.bind, hdesc, hanc, halloc]
      · have hnd := hnoDisabledAnc hanc halloc
        cases perm
        case disabled => exact False.elim (hnd rfl)
        case reservedFrz conf =>
          cases conf <;>
            simp only [Bool.false_eq_true, Bool.not_true, ↓reduceIte, Except.bind, hdesc, hanc, halloc, hprot]
        all_goals
          simp only [Bool.false_eq_true, Bool.not_true, ↓reduceIte, Except.bind, hdesc, hanc, halloc]
  · rfl

/-- **Unconditional Upstream Agreement When Implicit Writes Do Not Fire
(`execFnEntryMutRetag_eq_upstream_when_no_implicitWrite`, `[adv A1]`)**: whenever
`paramPolicy = .rustcNoWritable`, `implicitWrites = false`, or `len = 0`, two-pass
`execFnEntryMutRetag` (`requireInit = false`) is **unconditionally equal** to upstream
single-access `execFnEntryMutRetagUpstream` on *every* `FnEntryBorrowWorld`! -/
theorem execFnEntryMutRetag_eq_upstream_when_no_implicitWrite
    (w : FnEntryBorrowWorld) (parentTag off len : Nat) (facts : RetagTypeFacts)
    (implicitWrites : Bool) (paramPolicy : FnEntryRetagPolicy)
    (hnoWrite : paramPolicy = .rustcNoWritable ∨ implicitWrites = false ∨ len = 0) :
    execFnEntryMutRetag w parentTag off len facts implicitWrites paramPolicy false =
      execFnEntryMutRetagUpstream w parentTag off len facts implicitWrites paramPolicy := by
  unfold execFnEntryMutRetag execFnEntryMutRetagUpstream selectFnEntryPolicy
  cases hunpin : facts.tyIsUnpin
  · simp
  · rcases hnoWrite with rfl | rfl | rfl
    · simp [Bind.bind]
    · simp [Bind.bind]
    · simp [Bind.bind]

/-- **Two-Branch World Upstream Agreement Across Both Policies
(`execFnEntryMutRetag_mkTwoBranch_eq_upstream`, `[adv A1]`)**: on `mkTwoBranchBorrowWorld`,
`execFnEntryMutRetag` (`requireInit = false`) agrees with `execFnEntryMutRetagUpstream` across
**both** `.writableChildWrite` and `.rustcNoWritable` for every `len ≤ bytes.length`! -/
theorem execFnEntryMutRetag_mkTwoBranch_eq_upstream
    (allocId len : Nat) (bytes : List AbstractByte) (facts : RetagTypeFacts)
    (implicitWrites : Bool) (paramPolicy : FnEntryRetagPolicy)
    (hbound : len ≤ bytes.length) :
    let w := mkTwoBranchBorrowWorld allocId len bytes
    execFnEntryMutRetag w 1 0 len facts implicitWrites paramPolicy false =
      execFnEntryMutRetagUpstream w 1 0 len facts implicitWrites paramPolicy := by
  cases paramPolicy with
  | rustcNoWritable =>
    exact execFnEntryMutRetag_eq_upstream_when_no_implicitWrite _ _ _ _ _ _ _ (.inl rfl)
  | writableChildWrite =>
    cases implicitWrites with
    | false =>
      exact execFnEntryMutRetag_eq_upstream_when_no_implicitWrite _ _ _ _ _ _ _ (.inr (.inl rfl))
    | true =>
      cases len with
      | zero =>
        exact execFnEntryMutRetag_eq_upstream_when_no_implicitWrite _ _ _ _ _ _ _ (.inr (.inr rfl))
      | succ k =>
        cases hunpin : facts.tyIsUnpin
        · unfold execFnEntryMutRetag execFnEntryMutRetagUpstream selectFnEntryPolicy
          simp [hunpin]
        · have hb : ¬ (bytes.length < k + 1) := by omega
          have hk0 : Nat.beq (k + 1) 0 = false := rfl
          have hov : ∀ (tg : Nat) (p : AbstractPerm) (pr : Option Nat),
              byteRangeOverlapsWrite ⟨tg, allocId, 0, k + 1, p, pr⟩ allocId 0 (k + 1) = true := by
            intro tg p pr
            unfold byteRangeOverlapsWrite
            simp only [Nat.beq_refl, Bool.true_and]
            rfl
          unfold mkTwoBranchBorrowWorld execFnEntryMutRetag execFnEntryMutRetagUpstream
            selectFnEntryPolicy
          simp [hunpin, hb, hk0, findTagNode?, mapNodesM,
            stepNodeOnRangeRead, stepNodeOnRangeWrite,
            isDescendantOrSelf, isDescendantOrSelfAux, List.find?,
            TreeTagNode.toByteRangePerm, TreeBorrowPerm.toAbstractPerm,
            TreeTagNode.isProtected, hov, Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- **Disabled-Grandparent Diagnostic Separation (`execFnEntryMutRetag_disabledGrandparent_diverges_from_upstream`,
`[adv A1]`)**: witnesses *one* case where read-then-child-write diverges from upstream's single
parent write: when `parentTag = 2` (`.unique`) has a `.disabled` grandparent `tag = 1` and
`performsImplicitWrite = true` (`len > 0`), `execFnEntryMutRetag` reports `.parentDisabled` during
its preliminary read pass whereas `execFnEntryMutRetagUpstream` reports `.ancestorWriteForbidden`.
`[adv B2]`: A1 called this "the *sole* case"; it is not —
`execFnEntryMutRetag_frozenParent_protectedChild_diverges_from_upstream` diverges with no `.disabled`
node at all. -/
theorem execFnEntryMutRetag_disabledGrandparent_diverges_from_upstream
    (allocId len : Nat) (bytes : List AbstractByte) (facts : RetagTypeFacts)
    (hlen : 0 < len) (hbound : len ≤ bytes.length) (hunpin : facts.tyIsUnpin = true) :
    let w : FnEntryBorrowWorld := {
      allocId := allocId
      bytes := bytes
      nodes := [
        ⟨2, allocId, 0, len, .unique, none, some 1⟩,
        ⟨1, allocId, 0, len, .disabled, none, none⟩
      ]
      activeProtectors := ProtectorSet.empty
      nextTag := 3
      nextProtector := 1
    }
    execFnEntryMutRetag w 2 0 len facts true .writableChildWrite false = .error .parentDisabled ∧
    execFnEntryMutRetagUpstream w 2 0 len facts true .writableChildWrite =
      .error .ancestorWriteForbidden := by
  have hlen0 : Nat.beq len 0 = false := by
    cases len with
    | zero => omega
    | succ _ => rfl
  refine ⟨?_, ?_⟩
  · unfold execFnEntryMutRetag selectFnEntryPolicy
    simp [hunpin, findTagNode?, hbound, hlen0, mapNodesM, stepNodeOnRangeRead,
      isDescendantOrSelf, isDescendantOrSelfAux, Bind.bind, Except.bind,
      throw, throwThe, MonadExceptOf.throw]
  · unfold execFnEntryMutRetagUpstream selectFnEntryPolicy
    simp [hunpin, findTagNode?, hbound, hlen0, mapNodesM, stepNodeOnRangeWrite,
      isDescendantOrSelf, isDescendantOrSelfAux, Bind.bind, Except.bind,
      throw, throwThe, MonadExceptOf.throw]

/-- **List-Order Diagnostic Divergence Without Any `.disabled` Node
(`execFnEntryMutRetag_frozenParent_protectedChild_diverges_from_upstream`, `[adv B2]`)**: the
node-level `stepNode_read_then_childWrite_eq_parentWrite` does **not** lift to worlds, because the
two-pass model runs the *whole* read pass before any write. With a `.frozen` parent listed before a
protected `.unique` foreign node, the two-pass model reports the read pass's
`.protectedForeignConflict`, whereas upstream's single parent write stops first at the frozen parent
with `.ancestorWriteForbidden` — refuting A1's "sole case" claim. (Both models still report UB; only
the diagnostic differs, and this configuration may be unreachable by legal Tree Borrows histories.) -/
theorem execFnEntryMutRetag_frozenParent_protectedChild_diverges_from_upstream
    (allocId len : Nat) (bytes : List AbstractByte) (facts : RetagTypeFacts)
    (hlen : 0 < len) (hbound : len ≤ bytes.length) (hunpin : facts.tyIsUnpin = true) :
    let w : FnEntryBorrowWorld := {
      allocId := allocId
      bytes := bytes
      nodes := [
        ⟨1, allocId, 0, len, .frozen, none, none⟩,
        ⟨5, allocId, 0, len, .unique, some 7, some 1⟩
      ]
      activeProtectors := ProtectorSet.empty.insert 7
      nextTag := 6
      nextProtector := 8
    }
    execFnEntryMutRetag w 1 0 len facts true .writableChildWrite false =
      .error .protectedForeignConflict ∧
    execFnEntryMutRetagUpstream w 1 0 len facts true .writableChildWrite =
      .error .ancestorWriteForbidden := by
  have hlen0 : Nat.beq len 0 = false := by
    cases len with
    | zero => omega
    | succ _ => rfl
  have hov : ∀ (tg : Nat) (p : AbstractPerm) (pr : Option Nat),
      byteRangeOverlapsWrite ⟨tg, allocId, 0, len, p, pr⟩ allocId 0 len = true := by
    intro tg p pr
    unfold byteRangeOverlapsWrite
    simp only [Nat.beq_refl, Bool.true_and]
    unfold byteRangesOverlapBool
    cases len with
    | zero => omega
    | succ _ => rfl
  have hprot7 : (ProtectorSet.empty.insert 7).contains 7 = true :=
    ProtectorSet.contains_insert_self _ _
  refine ⟨?_, ?_⟩
  · unfold execFnEntryMutRetag selectFnEntryPolicy
    simp [hunpin, findTagNode?, hbound, hlen0, mapNodesM, stepNodeOnRangeRead,
      isDescendantOrSelf, isDescendantOrSelfAux, TreeTagNode.toByteRangePerm,
      TreeBorrowPerm.toAbstractPerm, TreeTagNode.isProtected, hov, hprot7,
      Bind.bind, Except.bind, throw, throwThe, MonadExceptOf.throw]
  · unfold execFnEntryMutRetagUpstream selectFnEntryPolicy
    simp [hunpin, findTagNode?, hbound, hlen0, mapNodesM, stepNodeOnRangeWrite,
      isDescendantOrSelf, isDescendantOrSelfAux,
      Bind.bind, Except.bind, throw, throwThe, MonadExceptOf.throw]

/-- Preliminary ancestor-first pass (`[adv A2]`), mirroring `Miri.TreeBorrows.TraversalTree.traverse`
(`Traversal.lean:102–118`, `localEvents ++ foreignEvents`), which **always** traverses the accessed
node and its ancestors before any foreign subtree regardless of flat-list insertion order. -/
def checkAncestorsM (allNodes : List TreeTagNode) (targetTag : Nat)
    (stepFn : TreeTagNode → Except RetagStepErr TreeTagNode) :
    List TreeTagNode → Except RetagStepErr Unit
  | [] => .ok ()
  | n :: ns => do
    if isDescendantOrSelf allNodes targetTag n.tag then
      let _ ← stepFn n
      checkAncestorsM allNodes targetTag stepFn ns
    else
      checkAncestorsM allNodes targetTag stepFn ns

def stepNodesAncestorFirst (allNodes : List TreeTagNode) (targetTag : Nat)
    (stepFn : TreeTagNode → Except RetagStepErr TreeTagNode)
    (nodes : List TreeTagNode) : Except RetagStepErr (List TreeTagNode) := do
  checkAncestorsM allNodes targetTag stepFn nodes
  mapNodesM stepFn nodes

/-- **Upstream Traversal-Order-Faithful `FnEntry` Mutable Retag (`execFnEntryMutRetagSourceOrder`,
`[adv A2]`)**: matches both `RetagPipeline.accessTreeForReborrow`'s single-parent-access rule AND
`TraversalTree.traverse`'s `localEvents ++ foreignEvents` ancestor-before-foreign order. -/
def execFnEntryMutRetagSourceOrder (w : FnEntryBorrowWorld) (parentTag off len : Nat)
    (facts : RetagTypeFacts) (implicitWrites : Bool) (paramPolicy : FnEntryRetagPolicy) :
    Except RetagStepErr (FnEntryBorrowWorld × Option Nat) := do
  match selectFnEntryPolicy facts .mutable implicitWrites paramPolicy with
  | none =>
    return (w, none)
  | some selected =>
    let some parentNode := findTagNode? w.nodes parentTag
      | throw RetagStepErr.parentTagMissing
    if parentNode.perm == .disabled then
      throw RetagStepErr.parentDisabled
    if off + len > w.bytes.length then
      throw RetagStepErr.outOfBounds
    let childTag := w.nextTag
    let protId := w.nextProtector
    let ps' := w.activeProtectors.insert protId
    let doWrite := selected.performsImplicitWrite && !(Nat.beq len 0)
    let nodesAfterParent ←
      if Nat.beq len 0 then
        .ok w.nodes
      else if doWrite then
        stepNodesAncestorFirst w.nodes parentTag
          (stepNodeOnRangeWrite w.nodes w.activeProtectors w.allocId off len parentTag) w.nodes
      else
        stepNodesAncestorFirst w.nodes parentTag
          (stepNodeOnRangeRead w.nodes w.activeProtectors w.allocId off len parentTag) w.nodes
    let childNode : TreeTagNode := {
      tag := childTag
      allocId := w.allocId
      offset := off
      len := len
      perm := if doWrite then .unique else .reservedFrz false
      protector := some protId
      parentTag := some parentTag
    }
    return ({
      w with
      nodes := childNode :: nodesAfterParent
      activeProtectors := ps'
      nextTag := childTag + 1
      nextProtector := protId + 1
    }, some childTag)

/-- **Traversal-Order Bug in `execFnEntryMutRetagUpstream` on Actual `childNode :: nodes` Order
(`execFnEntryMutRetagUpstream_reversedList_violates_traversalOrder`, `[adv A2]`)**: B2's witness
`execFnEntryMutRetag_frozenParent_protectedChild_diverges_from_upstream` hand-placed parent `1`
*before* child `5` (`[⟨1⟩, ⟨5⟩]`), the opposite of `childNode :: nodes` insertion order! On the
actual `childNode :: nodes` order `[⟨5 (protected .unique child)⟩, ⟨1 (.frozen parent)⟩]`,
`execFnEntryMutRetagUpstream` visits foreign child `5` *before* accessed parent `1` and falsely
reports `.protectedForeignConflict`, violating `TraversalTree.traverse` (`localEvents ++
foreignEvents`), whereas `execFnEntryMutRetagSourceOrder` visits accessed parent `1` first and
reports `.ancestorWriteForbidden`. -/
theorem execFnEntryMutRetagUpstream_reversedList_violates_traversalOrder
    (allocId len : Nat) (bytes : List AbstractByte) (facts : RetagTypeFacts)
    (hlen : 0 < len) (hbound : len ≤ bytes.length) (hunpin : facts.tyIsUnpin = true) :
    let wChildFirst : FnEntryBorrowWorld := {
      allocId := allocId
      bytes := bytes
      nodes := [
        ⟨5, allocId, 0, len, .unique, some 7, some 1⟩,
        ⟨1, allocId, 0, len, .frozen, none, none⟩
      ]
      activeProtectors := ProtectorSet.empty.insert 7
      nextTag := 6
      nextProtector := 8
    }
    execFnEntryMutRetagUpstream wChildFirst 1 0 len facts true .writableChildWrite =
      .error .protectedForeignConflict ∧
    execFnEntryMutRetagSourceOrder wChildFirst 1 0 len facts true .writableChildWrite =
      .error .ancestorWriteForbidden := by
  have hlen0 : Nat.beq len 0 = false := by
    cases len with
    | zero => omega
    | succ _ => rfl
  have hov : ∀ (tg : Nat) (p : AbstractPerm) (pr : Option Nat),
      byteRangeOverlapsWrite ⟨tg, allocId, 0, len, p, pr⟩ allocId 0 len = true := by
    intro tg p pr
    unfold byteRangeOverlapsWrite
    simp only [Nat.beq_refl, Bool.true_and]
    unfold byteRangesOverlapBool
    cases len with
    | zero => omega
    | succ _ => rfl
  have hprot7 : (ProtectorSet.empty.insert 7).contains 7 = true :=
    ProtectorSet.contains_insert_self _ _
  refine ⟨?_, ?_⟩
  · unfold execFnEntryMutRetagUpstream selectFnEntryPolicy
    simp [hunpin, findTagNode?, hbound, hlen0, mapNodesM, stepNodeOnRangeWrite,
      isDescendantOrSelf, isDescendantOrSelfAux, TreeTagNode.toByteRangePerm,
      TreeBorrowPerm.toAbstractPerm, TreeTagNode.isProtected, hov, hprot7,
      Bind.bind, Except.bind, throw, throwThe, MonadExceptOf.throw]
  · unfold execFnEntryMutRetagSourceOrder selectFnEntryPolicy stepNodesAncestorFirst
    simp [hunpin, findTagNode?, hbound, hlen0, checkAncestorsM, stepNodeOnRangeWrite,
      isDescendantOrSelf, isDescendantOrSelfAux,
      Bind.bind, Except.bind, throw, throwThe, MonadExceptOf.throw]

private theorem checkAncestorsM_ok_of_anc_ok
    (allNodes : List TreeTagNode) (targetTag : Nat)
    (stepFn : TreeTagNode → Except RetagStepErr TreeTagNode) :
    ∀ (ns : List TreeTagNode),
      (∀ n ∈ ns, isDescendantOrSelf allNodes targetTag n.tag = true → ∃ n', stepFn n = .ok n') →
      checkAncestorsM allNodes targetTag stepFn ns = .ok ()
  | [], _ => rfl
  | n :: rest, hok => by
    unfold checkAncestorsM
    have ih := checkAncestorsM_ok_of_anc_ok allNodes targetTag stepFn rest
      (fun m hm hanc => hok m (List.mem_cons_of_mem _ hm) hanc)
    cases hanc : isDescendantOrSelf allNodes targetTag n.tag
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact ih
    · obtain ⟨n', hn'⟩ := hok n (List.mem_cons_self ..) hanc
      simp only [↓reduceIte, hn', Bind.bind, Except.bind]
      exact ih

private theorem mapNodesM_error_eq {ε : Type} (f : TreeTagNode → Except ε TreeTagNode) (err₀ : ε) :
    ∀ (ns : List TreeTagNode) (e : ε),
      (∀ n ∈ ns, ∀ e', f n = .error e' → e' = err₀) →
      mapNodesM f ns = .error e → e = err₀
  | [], _, _, h => nomatch h
  | n :: rest, e, herr, h => by
    unfold mapNodesM at h
    cases hfn : f n with
    | error en =>
      rw [hfn] at h
      injection h with he
      exact he ▸ herr n (List.mem_cons_self ..) en hfn
    | ok _ =>
      rw [hfn] at h
      dsimp only [Bind.bind, Except.bind] at h
      cases hrest : mapNodesM f rest with
      | error er =>
        rw [hrest] at h
        injection h with he
        exact he ▸ mapNodesM_error_eq f err₀ rest er
          (fun m hm => herr m (List.mem_cons_of_mem _ hm)) hrest
      | ok _ =>
        rw [hrest] at h
        nomatch h

/-- **Two-Pass Monadic Traverse Collapse Under Uniform Error (`mapNodesM_twoPass_eq_singlePass`,
`[adv A2]`)**: whenever `(f₁ n >>= f₂) = g n` pointwise on `ns` and every error thrown by `f₁` or
`g` on `ns` equals the same `err₀` (here `.protectedForeignConflict`), running `mapNodesM f₁ ns >>=
mapNodesM f₂` is propositionally equal to `mapNodesM g ns` despite two-pass vs. single-pass
short-circuit order! -/
theorem mapNodesM_twoPass_eq_singlePass {ε : Type}
    (f₁ f₂ g : TreeTagNode → Except ε TreeTagNode) (err₀ : ε) :
    ∀ (ns : List TreeTagNode),
      (∀ n ∈ ns, (f₁ n >>= f₂) = g n) →
      (∀ n ∈ ns, ∀ e, f₁ n = .error e → e = err₀) →
      (∀ n ∈ ns, ∀ e, g n = .error e → e = err₀) →
      (mapNodesM f₁ ns >>= mapNodesM f₂) = mapNodesM g ns
  | [], _, _, _ => rfl
  | n :: rest, hcomp, herr₁, herrg => by
    have ih := mapNodesM_twoPass_eq_singlePass f₁ f₂ g err₀ rest
      (fun m hm => hcomp m (List.mem_cons_of_mem _ hm))
      (fun m hm => herr₁ m (List.mem_cons_of_mem _ hm))
      (fun m hm => herrg m (List.mem_cons_of_mem _ hm))
    have hn_comp := hcomp n (List.mem_cons_self ..)
    change Except.bind (mapNodesM f₁ (n :: rest)) (mapNodesM f₂) = mapNodesM g (n :: rest)
    unfold mapNodesM
    cases hf₁ : f₁ n with
    | error e₁ =>
      rw [hf₁] at hn_comp
      have he₁ : e₁ = err₀ := herr₁ n (List.mem_cons_self ..) e₁ hf₁
      subst he₁
      change Except.error e₁ = Except.bind (g n) _
      rw [← hn_comp]
      rfl
    | ok n₁ =>
      rw [hf₁] at hn_comp
      change f₂ n₁ = g n at hn_comp
      dsimp only [Bind.bind, Except.bind]
      cases hrest₁ : mapNodesM f₁ rest with
      | error eRest =>
        have heRest : eRest = err₀ :=
          mapNodesM_error_eq f₁ err₀ rest eRest
            (fun m hm => herr₁ m (List.mem_cons_of_mem _ hm)) hrest₁
        rw [hrest₁, heRest] at ih
        dsimp only [Bind.bind, Except.bind] at ih
        dsimp only [Pure.pure, Except.pure, Bind.bind, Except.bind]
        rw [heRest]
        cases hg : g n with
        | error eg =>
          have heg : eg = err₀ := herrg n (List.mem_cons_self ..) eg hg
          rw [heg]
        | ok _ =>
          rw [← ih]
      | ok rest₁ =>
        rw [hrest₁] at ih
        dsimp only [Bind.bind, Except.bind] at ih
        dsimp only [Pure.pure, Except.pure, Bind.bind, Except.bind]
        change (do let n' ← f₂ n₁; let ns' ← mapNodesM f₂ rest₁; pure (n' :: ns')) =
          (do let n' ← g n; let ns' ← mapNodesM g rest; pure (n' :: ns'))
        rw [hn_comp, ih]

/-- Tag & protector supply well-formedness on `FnEntryBorrowWorld` (`[adv A2]`): existing tags and
parent links are `< w.nextTag`, and existing protector tokens are `< w.nextProtector`. -/
def BorrowTreeTagsWF (w : FnEntryBorrowWorld) : Prop :=
  ∀ n ∈ w.nodes,
    n.tag < w.nextTag ∧
    (∀ p, n.parentTag = some p → p < w.nextTag) ∧
    (∀ pr, n.protector = some pr → pr < w.nextProtector)

/-- Predicate that every same-allocation ancestor of `parentTag` in `w` permits a local write. -/
def AncestorsWritableIn (w : FnEntryBorrowWorld) (parentTag : Nat) : Prop :=
  ∀ n ∈ w.nodes,
    isDescendantOrSelf w.nodes parentTag n.tag = true →
    Nat.beq n.allocId w.allocId = true →
    n.perm ≠ .frozen ∧ n.perm ≠ .disabled ∧
      (n.perm = .reservedFrz true → n.isProtected w.activeProtectors = false)

private theorem stepNodeOnRangeRead_preserves_tag_parent
    (allNodes : List TreeTagNode) (ps : ProtectorSet) (allocId off len readerTag : Nat)
    (n n' : TreeTagNode)
    (hok : stepNodeOnRangeRead allNodes ps allocId off len readerTag n = .ok n') :
    n'.tag = n.tag ∧ n'.parentTag = n.parentTag := by
  rcases n with ⟨tg, nAlloc, nOff, nLen, perm, prot, pTag⟩
  unfold stepNodeOnRangeRead at hok
  cases hlen : Nat.beq len 0
  · rw [hlen] at hok
    simp only [Bool.false_eq_true, ↓reduceIte] at hok
    cases hanc : isDescendantOrSelf allNodes readerTag tg
    · rw [hanc] at hok
      simp only [Bool.false_eq_true, ↓reduceIte] at hok
      cases hov : byteRangeOverlapsWrite
          (TreeTagNode.toByteRangePerm ⟨tg, nAlloc, nOff, nLen, perm, prot, pTag⟩) allocId off len
      · rw [hov] at hok
        simp only [Bool.false_eq_true, ↓reduceIte, Except.ok.injEq] at hok
        subst hok; exact ⟨rfl, rfl⟩
      · rw [hov] at hok
        simp only [↓reduceIte] at hok
        cases perm
        case reservedFrz conf =>
          injection hok with h'; subst h'; exact ⟨rfl, rfl⟩
        case unique =>
          cases hpr : TreeTagNode.isProtected ⟨tg, nAlloc, nOff, nLen, .unique, prot, pTag⟩ ps
          · rw [hpr] at hok
            simp only [Bool.false_eq_true, ↓reduceIte, Except.ok.injEq] at hok
            subst hok; exact ⟨rfl, rfl⟩
          · rw [hpr] at hok; nomatch hok
        all_goals
          injection hok with h'; subst h'; exact ⟨rfl, rfl⟩
    · rw [hanc] at hok
      simp only [↓reduceIte] at hok
      cases ha : Nat.beq nAlloc allocId
      · rw [ha] at hok
        simp only [Bool.not_false, ↓reduceIte, Except.ok.injEq] at hok
        subst hok; exact ⟨rfl, rfl⟩
      · rw [ha] at hok
        simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hok
        cases perm
        case disabled => nomatch hok
        all_goals
          injection hok with h'; subst h'; exact ⟨rfl, rfl⟩
  · rw [hlen] at hok
    simp only [↓reduceIte, Except.ok.injEq] at hok
    subst hok; exact ⟨rfl, rfl⟩

private theorem mapNodesM_read_length_and_findTag
    (allNodes : List TreeTagNode) (ps : ProtectorSet) (allocId off len readerTag : Nat) :
    ∀ (ns ns' : List TreeTagNode),
      mapNodesM (stepNodeOnRangeRead allNodes ps allocId off len readerTag) ns = .ok ns' →
      ns'.length = ns.length ∧
      (∀ q, (findTagNode? ns' q).map TreeTagNode.parentTag =
        (findTagNode? ns q).map TreeTagNode.parentTag)
  | [], ns', h => by
    injection h with h'; subst h'; exact ⟨rfl, fun _ => rfl⟩
  | n :: rest, ns', h => by
    unfold mapNodesM at h
    cases hfn : stepNodeOnRangeRead allNodes ps allocId off len readerTag n with
    | error _ => rw [hfn] at h; nomatch h
    | ok n' =>
      rw [hfn] at h
      dsimp only [Bind.bind, Except.bind] at h
      cases hrest : mapNodesM _ rest with
      | error _ => rw [hrest] at h; nomatch h
      | ok rest' =>
        rw [hrest] at h
        injection h with hcons
        subst hcons
        obtain ⟨htag, hpar⟩ := stepNodeOnRangeRead_preserves_tag_parent _ _ _ _ _ _ _ _ hfn
        obtain ⟨hlen, hfind⟩ := mapNodesM_read_length_and_findTag _ _ _ _ _ _ rest rest' hrest
        refine ⟨congrArg Nat.succ hlen, fun q => ?_⟩
        unfold findTagNode? at hfind ⊢
        simp only [List.find?, htag]
        cases Nat.beq n.tag q
        · exact hfind q
        · simp [hpar]

private theorem findTagNode?_some_mem :
    ∀ (ns : List TreeTagNode) (q : Nat) (nd : TreeTagNode),
      findTagNode? ns q = some nd → nd ∈ ns
  | [], _, _, h => nomatch h
  | n :: rest, q, nd, h => by
    unfold findTagNode? at h
    simp only [List.find?] at h
    cases hbeq : Nat.beq n.tag q
    · rw [hbeq] at h
      exact List.mem_cons_of_mem _ (findTagNode?_some_mem rest q nd h)
    · rw [hbeq] at h
      injection h with h'
      subst h'
      exact List.mem_cons_self ..

private theorem isDescendantOrSelfAux_cons_fresh
    (w : FnEntryBorrowWorld) (hwf : BorrowTreeTagsWF w)
    (childNode : TreeTagNode) (hchildTag : childNode.tag = w.nextTag)
    (ns' : List TreeTagNode)
    (hfind : ∀ q, (findTagNode? ns' q).map TreeTagNode.parentTag =
      (findTagNode? w.nodes q).map TreeTagNode.parentTag) :
    ∀ (fuel cur ancTag : Nat),
      cur < w.nextTag →
      isDescendantOrSelfAux fuel (childNode :: ns') cur ancTag =
        isDescendantOrSelfAux fuel w.nodes cur ancTag
  | 0, _, _, _ => rfl
  | fuel + 1, cur, ancTag, hlt => by
    unfold isDescendantOrSelfAux
    cases Nat.beq cur ancTag
    · simp only [Bool.false_eq_true, ↓reduceIte]
      have hne : Nat.beq childNode.tag cur = false := by
        rw [hchildTag]
        cases h : Nat.beq w.nextTag cur with
        | false => rfl
        | true =>
          have heq := Nat.eq_of_beq_eq_true h
          omega
      have hfCons : findTagNode? (childNode :: ns') cur = findTagNode? ns' cur := by
        unfold findTagNode?; simp [List.find?, hne]
      rw [hfCons]
      have hmapEq := hfind cur
      cases hf1 : findTagNode? ns' cur with
      | none =>
        rw [hf1] at hmapEq
        cases hf2 : findTagNode? w.nodes cur with
        | none => rfl
        | some _ => rw [hf2] at hmapEq; nomatch hmapEq
      | some nd1 =>
        rw [hf1] at hmapEq
        cases hf2 : findTagNode? w.nodes cur with
        | none => rw [hf2] at hmapEq; nomatch hmapEq
        | some nd2 =>
          rw [hf2] at hmapEq
          simp only [Option.map, Option.some.injEq] at hmapEq
          dsimp only
          rw [hmapEq]
          cases hp : nd2.parentTag with
          | none => rfl
          | some p =>
            have hmem2 := findTagNode?_some_mem w.nodes cur nd2 hf2
            have hplt : p < w.nextTag := (hwf nd2 hmem2).2.1 p hp
            exact isDescendantOrSelfAux_cons_fresh w hwf childNode hchildTag ns' hfind fuel p ancTag hplt
    · rfl

private theorem findTagNode?_some_tag :
    ∀ (ns : List TreeTagNode) (q : Nat) (nd : TreeTagNode),
      findTagNode? ns q = some nd → nd.tag = q
  | [], _, _, h => nomatch h
  | n :: rest, q, nd, h => by
    unfold findTagNode? at h
    simp only [List.find?] at h
    cases hbeq : Nat.beq n.tag q
    · rw [hbeq] at h
      exact findTagNode?_some_tag rest q nd h
    · rw [hbeq] at h
      simp only [Option.some.injEq] at h
      subst h
      exact Nat.eq_of_beq_eq_true hbeq

private theorem stepNodeOnRangeRead_error_eq_foreign
    (w : FnEntryBorrowWorld) (parentTag off len : Nat) (n : TreeTagNode) (e : RetagStepErr)
    (hwrit : AncestorsWritableIn w parentTag)
    (hmem : n ∈ w.nodes)
    (herr : stepNodeOnRangeRead w.nodes w.activeProtectors w.allocId off len parentTag n = .error e) :
    e = .protectedForeignConflict := by
  unfold stepNodeOnRangeRead at herr
  cases hlen : Nat.beq len 0
  · rw [hlen] at herr
    simp only [Bool.false_eq_true, ↓reduceIte] at herr
    cases hanc : isDescendantOrSelf w.nodes parentTag n.tag
    · rw [hanc] at herr
      simp only [Bool.false_eq_true, ↓reduceIte] at herr
      cases hov : byteRangeOverlapsWrite n.toByteRangePerm w.allocId off len
      · rw [hov] at herr; nomatch herr
      · rw [hov] at herr
        simp only [↓reduceIte] at herr
        cases hp : n.perm <;> rw [hp] at herr
        case unique =>
          cases hpr : n.isProtected w.activeProtectors <;> rw [hpr] at herr
          · nomatch herr
          · simp only [↓reduceIte, Except.error.injEq] at herr
            exact herr.symm
        all_goals nomatch herr
    · rw [hanc] at herr
      simp only [↓reduceIte] at herr
      cases ha : Nat.beq n.allocId w.allocId
      · rw [ha] at herr; nomatch herr
      · rw [ha] at herr
        have hnd := (hwrit n hmem hanc ha).2.1
        cases hp : n.perm <;> rw [hp] at herr
        case disabled => exact False.elim (hnd hp)
        all_goals nomatch herr
  · rw [hlen] at herr; nomatch herr

private theorem stepNodeOnRangeWrite_error_eq_foreign
    (w : FnEntryBorrowWorld) (parentTag off len : Nat) (n : TreeTagNode) (e : RetagStepErr)
    (hwrit : AncestorsWritableIn w parentTag)
    (hmem : n ∈ w.nodes)
    (herr : stepNodeOnRangeWrite w.nodes w.activeProtectors w.allocId off len parentTag n = .error e) :
    e = .protectedForeignConflict := by
  unfold stepNodeOnRangeWrite at herr
  cases hlen : Nat.beq len 0
  · rw [hlen] at herr
    simp only [Bool.false_eq_true, ↓reduceIte] at herr
    cases hanc : isDescendantOrSelf w.nodes parentTag n.tag
    · rw [hanc] at herr
      simp only [Bool.false_eq_true, ↓reduceIte] at herr
      cases hov : byteRangeOverlapsWrite n.toByteRangePerm w.allocId off len
      · rw [hov] at herr; nomatch herr
      · rw [hov] at herr
        simp only [↓reduceIte] at herr
        cases hpr : n.isProtected w.activeProtectors <;> rw [hpr] at herr
        · nomatch herr
        · simp only [↓reduceIte] at herr
          cases hp : n.perm <;> rw [hp] at herr
          case disabled => nomatch herr
          case cell => nomatch herr
          all_goals
            simp only [Except.error.injEq] at herr
            exact herr.symm
    · rw [hanc] at herr
      simp only [↓reduceIte] at herr
      cases ha : Nat.beq n.allocId w.allocId
      · rw [ha] at herr; nomatch herr
      · rw [ha] at herr
        obtain ⟨hnf, hnd, hnc⟩ := hwrit n hmem hanc ha
        cases hp : n.perm <;> rw [hp] at herr
        case frozen => exact False.elim (hnf hp)
        case disabled => exact False.elim (hnd hp)
        case reservedFrz conf =>
          cases conf
          · nomatch herr
          · have hnp := hnc hp
            simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, hnp] at herr
            nomatch herr
        all_goals nomatch herr
  · rw [hlen] at herr; nomatch herr

private theorem stepNodeOnRangeWrite_anc_ok_of_writable
    (w : FnEntryBorrowWorld) (parentTag off len : Nat) (n : TreeTagNode)
    (hanc : isDescendantOrSelf w.nodes parentTag n.tag = true)
    (hwrit : Nat.beq n.allocId w.allocId = true →
      n.perm ≠ .frozen ∧ n.perm ≠ .disabled ∧
        (n.perm = .reservedFrz true → n.isProtected w.activeProtectors = false)) :
    ∃ n', stepNodeOnRangeWrite w.nodes w.activeProtectors w.allocId off len parentTag n = .ok n' := by
  unfold stepNodeOnRangeWrite
  cases Nat.beq len 0
  · simp only [Bool.false_eq_true, ↓reduceIte, hanc]
    cases halloc : Nat.beq n.allocId w.allocId
    · exact ⟨n, rfl⟩
    · obtain ⟨hnf, hnd, hnc⟩ := hwrit halloc
      cases hp : n.perm
      case frozen => exact False.elim (hnf hp)
      case disabled => exact False.elim (hnd hp)
      case reservedFrz conf =>
        cases conf
        · exact ⟨{ n with perm := .unique }, rfl⟩
        · have hnp := hnc hp
          simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, hnp]
          exact ⟨{ n with perm := .unique }, rfl⟩
      case cell => exact ⟨n, rfl⟩
      case reservedIM => exact ⟨{ n with perm := .unique }, rfl⟩
      case unique => exact ⟨{ n with perm := .unique }, rfl⟩
  · exact ⟨n, rfl⟩

private theorem stepNodeOnRangeRead_anc_ok_of_not_disabled
    (w : FnEntryBorrowWorld) (parentTag off len : Nat) (n : TreeTagNode)
    (hanc : isDescendantOrSelf w.nodes parentTag n.tag = true)
    (hnd : Nat.beq n.allocId w.allocId = true → n.perm ≠ .disabled) :
    ∃ n', stepNodeOnRangeRead w.nodes w.activeProtectors w.allocId off len parentTag n = .ok n' := by
  refine ⟨n, ?_⟩
  unfold stepNodeOnRangeRead
  cases Nat.beq len 0
  · simp only [Bool.false_eq_true, ↓reduceIte, hanc]
    cases halloc : Nat.beq n.allocId w.allocId
    · rfl
    · have hnd' := hnd halloc
      cases hp : n.perm
      case disabled => exact False.elim (hnd' hp)
      all_goals rfl
  · rfl

private theorem isDescendantOrSelf_withChild_eq
    (w : FnEntryBorrowWorld) (hwf : BorrowTreeTagsWF w)
    (parentTag : Nat) (hparLt : parentTag < w.nextTag)
    (childNode : TreeTagNode) (hchildTag : childNode.tag = w.nextTag)
    (hchildPar : childNode.parentTag = some parentTag)
    (ns' : List TreeTagNode) (hlenEq : ns'.length = w.nodes.length)
    (hfind : ∀ q, (findTagNode? ns' q).map TreeTagNode.parentTag =
      (findTagNode? w.nodes q).map TreeTagNode.parentTag)
    (n : TreeTagNode) (hnMem : n ∈ w.nodes) :
    isDescendantOrSelf (childNode :: ns') w.nextTag n.tag =
      isDescendantOrSelf w.nodes parentTag n.tag := by
  have hnLt : n.tag < w.nextTag := (hwf n hnMem).1
  have hne : Nat.beq w.nextTag n.tag = false := by
    cases h : Nat.beq w.nextTag n.tag with
    | false => rfl
    | true => have := Nat.eq_of_beq_eq_true h; omega
  have hself : Nat.beq childNode.tag w.nextTag = true := by
    rw [hchildTag]; exact Nat.beq_refl _
  unfold isDescendantOrSelf
  simp only [List.length_cons, hlenEq]
  change isDescendantOrSelfAux ((w.nodes.length + 1) + 1) (childNode :: ns') w.nextTag n.tag =
    isDescendantOrSelfAux (w.nodes.length + 1) w.nodes parentTag n.tag
  unfold isDescendantOrSelfAux
  simp only [hne, Bool.false_eq_true, ↓reduceIte, findTagNode?, List.find?, hself, hchildPar]
  exact isDescendantOrSelfAux_cons_fresh w hwf childNode hchildTag ns' hfind
    (w.nodes.length + 1) parentTag n.tag hparLt

private theorem isProtected_insert_fresh
    (w : FnEntryBorrowWorld) (hwf : BorrowTreeTagsWF w)
    (n : TreeTagNode) (hnMem : n ∈ w.nodes) :
    n.isProtected (w.activeProtectors.insert w.nextProtector) =
      n.isProtected w.activeProtectors := by
  unfold TreeTagNode.isProtected
  cases hpr : n.protector with
  | none => rfl
  | some lft =>
    have hlt : lft < w.nextProtector := (hwf n hnMem).2.2 lft hpr
    have hb1 : Nat.beq w.nextProtector lft = false := by
      cases h : Nat.beq w.nextProtector lft with
      | false => rfl
      | true => have := Nat.eq_of_beq_eq_true h; omega
    simp [ProtectorSet.insert, ProtectorSet.contains, natListContainsBool, hb1]

/-- **Arbitrary-World Three-Model Equivalence Under Writable Ancestors
(`execFnEntryMutRetag_eq_sourceOrder_of_writableAncestors`, `[adv A2]`)**: for **every**
`w : FnEntryBorrowWorld` with fresh tag/protector counters (`BorrowTreeTagsWF w`) and writable
ancestors of `parentTag` (`AncestorsWritableIn w parentTag`), two-pass `execFnEntryMutRetag`
(`requireInit = false`), single-pass `execFnEntryMutRetagUpstream`, AND ancestor-first
`execFnEntryMutRetagSourceOrder` are **propositionally equal** across all policies, lengths, and
arbitrary foreign subtrees! -/
theorem execFnEntryMutRetag_eq_sourceOrder_of_writableAncestors
    (w : FnEntryBorrowWorld) (parentTag off len : Nat)
    (facts : RetagTypeFacts) (implicitWrites : Bool) (paramPolicy : FnEntryRetagPolicy)
    (hwf : BorrowTreeTagsWF w)
    (hwrit : AncestorsWritableIn w parentTag) :
    execFnEntryMutRetag w parentTag off len facts implicitWrites paramPolicy false =
      execFnEntryMutRetagUpstream w parentTag off len facts implicitWrites paramPolicy ∧
    execFnEntryMutRetagUpstream w parentTag off len facts implicitWrites paramPolicy =
      execFnEntryMutRetagSourceOrder w parentTag off len facts implicitWrites paramPolicy := by
  have hcaRead : checkAncestorsM w.nodes parentTag
      (stepNodeOnRangeRead w.nodes w.activeProtectors w.allocId off len parentTag) w.nodes = .ok () :=
    checkAncestorsM_ok_of_anc_ok _ _ _ w.nodes (fun n hm hanc =>
      stepNodeOnRangeRead_anc_ok_of_not_disabled w parentTag off len n hanc
        (fun ha => (hwrit n hm hanc ha).2.1))
  have hcaWrite : checkAncestorsM w.nodes parentTag
      (stepNodeOnRangeWrite w.nodes w.activeProtectors w.allocId off len parentTag) w.nodes = .ok () :=
    checkAncestorsM_ok_of_anc_ok _ _ _ w.nodes (fun n hm hanc =>
      stepNodeOnRangeWrite_anc_ok_of_writable w parentTag off len n hanc (hwrit n hm hanc))
  refine ⟨?_, ?_⟩
  · by_cases hnoWr : paramPolicy = .rustcNoWritable ∨ implicitWrites = false ∨ len = 0
    · exact execFnEntryMutRetag_eq_upstream_when_no_implicitWrite _ _ _ _ _ _ _ hnoWr
    · have hpol : paramPolicy = .writableChildWrite := by
        cases paramPolicy with
        | writableChildWrite => rfl
        | rustcNoWritable => exact False.elim (hnoWr (.inl rfl))
      have himp : implicitWrites = true := by
        cases implicitWrites with
        | true => rfl
        | false => exact False.elim (hnoWr (.inr (.inl rfl)))
      have hlen0 : Nat.beq len 0 = false := by
        cases len with
        | zero => exact False.elim (hnoWr (.inr (.inr rfl)))
        | succ _ => rfl
      subst hpol himp
      unfold execFnEntryMutRetag execFnEntryMutRetagUpstream
      cases hunpin : facts.tyIsUnpin
      · have hselNone : selectFnEntryPolicy facts .mutable true .writableChildWrite = none := by
          simp [selectFnEntryPolicy, hunpin]
        rw [hselNone]
      · have hselSome : selectFnEntryPolicy facts .mutable true .writableChildWrite =
            some ⟨.active, .active, .reservedFrz false, .strong, true⟩ := by
          simp [selectFnEntryPolicy, hunpin]
        rw [hselSome]
        dsimp only [Bind.bind, Except.bind]
        cases hf : findTagNode? w.nodes parentTag with
        | none => rfl
        | some parentNode =>
          dsimp only
          cases hdis : (parentNode.perm == .disabled)
          · simp only [Bool.false_eq_true, ↓reduceIte]
            if hob : w.bytes.length < off + len then
              simp [hob, throw, throwThe, MonadExceptOf.throw]
            else
              simp only [hob, ↓reduceIte, hlen0, Bool.false_eq_true, Bool.not_false, Bool.true_and,
                Bool.false_and]
              have hpMem := findTagNode?_some_mem w.nodes parentTag parentNode hf
              have hpTag := findTagNode?_some_tag w.nodes parentTag parentNode hf
              have hparLt : parentTag < w.nextTag := hpTag ▸ (hwf parentNode hpMem).1
              let ps' := w.activeProtectors.insert w.nextProtector
              let childBase : TreeTagNode :=
                ⟨w.nextTag, w.allocId, off, len, .reservedFrz false, some w.nextProtector, some parentTag⟩
              let fRead := stepNodeOnRangeRead w.nodes w.activeProtectors w.allocId off len parentTag
              let gWrite := stepNodeOnRangeWrite w.nodes w.activeProtectors w.allocId off len parentTag
              cases hread : mapNodesM fRead w.nodes with
              | error eRead =>
                have heEq : eRead = .protectedForeignConflict :=
                  mapNodesM_error_eq fRead .protectedForeignConflict w.nodes eRead
                    (fun n hm e he => stepNodeOnRangeRead_error_eq_foreign w parentTag off len n e hwrit hm he)
                    hread
                subst heEq
                let f₂0 := stepNodeOnRangeWrite (childBase :: w.nodes) ps' w.allocId off len w.nextTag
                have htwo0 := mapNodesM_twoPass_eq_singlePass fRead f₂0 gWrite .protectedForeignConflict w.nodes
                  (fun n hm => stepNode_read_then_childWrite_eq_parentWrite w.nodes (childBase :: w.nodes)
                    w.activeProtectors ps' w.allocId off len parentTag w.nextTag n
                    (isDescendantOrSelf_withChild_eq w hwf parentTag hparLt childBase rfl rfl
                      w.nodes rfl (fun _ => rfl) n hm)
                    (isProtected_insert_fresh w hwf n hm)
                    (fun hanc ha => (hwrit n hm hanc ha).2.1))
                  (fun n hm e he => stepNodeOnRangeRead_error_eq_foreign w parentTag off len n e hwrit hm he)
                  (fun n hm e he => stepNodeOnRangeWrite_error_eq_foreign w parentTag off len n e hwrit hm he)
                rw [hread] at htwo0
                change Except.error RetagStepErr.protectedForeignConflict = mapNodesM gWrite w.nodes at htwo0
                rw [← htwo0]
              | ok nsRead =>
                obtain ⟨hlenEq, hfindEq⟩ := mapNodesM_read_length_and_findTag
                  w.nodes w.activeProtectors w.allocId off len parentTag w.nodes nsRead hread
                let f₂ := stepNodeOnRangeWrite (childBase :: nsRead) ps' w.allocId off len w.nextTag
                have htwo := mapNodesM_twoPass_eq_singlePass fRead f₂ gWrite .protectedForeignConflict w.nodes
                  (fun n hm => stepNode_read_then_childWrite_eq_parentWrite w.nodes (childBase :: nsRead)
                    w.activeProtectors ps' w.allocId off len parentTag w.nextTag n
                    (isDescendantOrSelf_withChild_eq w hwf parentTag hparLt childBase rfl rfl
                      nsRead hlenEq hfindEq n hm)
                    (isProtected_insert_fresh w hwf n hm)
                    (fun hanc ha => (hwrit n hm hanc ha).2.1))
                  (fun n hm e he => stepNodeOnRangeRead_error_eq_foreign w parentTag off len n e hwrit hm he)
                  (fun n hm e he => stepNodeOnRangeWrite_error_eq_foreign w parentTag off len n e hwrit hm he)
                rw [hread] at htwo
                change mapNodesM f₂ nsRead = mapNodesM gWrite w.nodes at htwo
                have hchildSelf : f₂ childBase = .ok { childBase with perm := .unique } := by
                  unfold f₂ stepNodeOnRangeWrite
                  have hselfDesc : isDescendantOrSelf (childBase :: nsRead) w.nextTag childBase.tag = true := by
                    unfold isDescendantOrSelf isDescendantOrSelfAux
                    simp [childBase, Nat.beq_refl]
                  simp [hlen0, hselfDesc, childBase, Nat.beq_refl]
                have hconsDef : mapNodesM f₂ (childBase :: nsRead) =
                    (f₂ childBase >>= fun n' => mapNodesM f₂ nsRead >>= fun ns' => pure (n' :: ns')) := rfl
                have hconsMap : mapNodesM f₂ (childBase :: nsRead) =
                    (mapNodesM gWrite w.nodes >>= fun ns' => pure ({ childBase with perm := .unique } :: ns')) := by
                  rw [hconsDef, hchildSelf, htwo]
                  rfl
                change (do
                  let nsAfterWrite ← mapNodesM f₂ (childBase :: nsRead)
                  pure ({ w with
                          nodes := nsAfterWrite
                          activeProtectors := ps'
                          nextTag := w.nextTag + 1
                          nextProtector := w.nextProtector + 1 }, some w.nextTag)) =
                  (do
                    let nsAfterParent ← mapNodesM gWrite w.nodes
                    pure ({ w with
                            nodes := { childBase with perm := .unique } :: nsAfterParent
                            activeProtectors := ps'
                            nextTag := w.nextTag + 1
                            nextProtector := w.nextProtector + 1 }, some w.nextTag))
                rw [hconsMap]
                cases mapNodesM gWrite w.nodes <;> rfl
          · rfl
  · unfold execFnEntryMutRetagUpstream execFnEntryMutRetagSourceOrder stepNodesAncestorFirst
    cases selectFnEntryPolicy facts .mutable implicitWrites paramPolicy with
    | none => rfl
    | some selected =>
      dsimp only [Bind.bind, Except.bind]
      cases findTagNode? w.nodes parentTag with
      | none => rfl
      | some parentNode =>
        dsimp only
        cases parentNode.perm == .disabled
        · simp only [Bool.false_eq_true, ↓reduceIte]
          if hob : w.bytes.length < off + len then
            simp [hob, throw, throwThe, MonadExceptOf.throw]
          else
            simp only [hob, ↓reduceIte]
            cases Nat.beq len 0
            · simp only [Bool.false_eq_true, ↓reduceIte]
              cases selected.performsImplicitWrite && !false
              · rw [hcaRead]; rfl
              · rw [hcaWrite]; rfl
            · rfl
        · rfl

private theorem mapNodesM_preserves_fixed_mem
    (f : TreeTagNode → Except RetagStepErr TreeTagNode) :
    ∀ (ns ns' : List TreeTagNode) (n : TreeTagNode),
      mapNodesM f ns = .ok ns' → n ∈ ns → f n = .ok n → n ∈ ns'
  | [], _, _, _, hmem, _ => nomatch hmem
  | hd :: tl, ns', n, hmap, hmem, hfix => by
    unfold mapNodesM at hmap
    cases hhd : f hd with
    | error _ => rw [hhd] at hmap; nomatch hmap
    | ok hd' =>
      rw [hhd] at hmap
      dsimp only [Bind.bind, Except.bind] at hmap
      cases htl : mapNodesM f tl with
      | error _ => rw [htl] at hmap; nomatch hmap
      | ok tl' =>
        rw [htl] at hmap
        injection hmap with hcons
        subst hcons
        rcases List.mem_cons.mp hmem with rfl | hmemTl
        · have heq : hd' = n := by
            have h := hhd.symm.trans hfix
            injection h
          rw [heq]
          exact List.mem_cons_self ..
        · exact List.mem_cons_of_mem _ (mapNodesM_preserves_fixed_mem f tl tl' n htl hmemTl hfix)

/-- **Arbitrary-World `#[rustc_no_writable]` `.frozen` Node Preservation
(`sourceOrder_rustcNoWritable_preserves_all_frozen_nodes`, `[adv A2]`)**: lifts Part 2A's `.frozen`
reader survival guarantee off the concrete 2-node `mkTwoBranchBorrowWorld` fixture to **arbitrary**
`w : FnEntryBorrowWorld` under upstream source-order execution: whenever `execFnEntryMutRetagSourceOrder`
with `.rustcNoWritable` mints a child tag `(w', some childTag)`, *every* `.frozen` node in `w.nodes`
(at any tree depth, offset, or protector state) survives unchanged in `w'.nodes`! -/
theorem sourceOrder_rustcNoWritable_preserves_all_frozen_nodes
    (w w' : FnEntryBorrowWorld) (parentTag off len childTag : Nat)
    (facts : RetagTypeFacts) (implicitWrites : Bool)
    (hok : execFnEntryMutRetagSourceOrder w parentTag off len facts implicitWrites .rustcNoWritable =
      .ok (w', some childTag)) :
    ∀ n ∈ w.nodes, n.perm = .frozen → n ∈ w'.nodes := by
  unfold execFnEntryMutRetagSourceOrder at hok
  cases hunpin : facts.tyIsUnpin
  · have hselNone : selectFnEntryPolicy facts .mutable implicitWrites .rustcNoWritable = none :=
      pinned_mutable_or_box_fnEntry_skips_retag facts .mutable implicitWrites .rustcNoWritable (.inl rfl) hunpin
    rw [hselNone] at hok
    nomatch hok
  · rw [selectFnEntryPolicy_rustcNoWritable_mut facts implicitWrites hunpin] at hok
    dsimp only [Bind.bind, Except.bind] at hok
    cases hf : findTagNode? w.nodes parentTag with
    | none => rw [hf] at hok; nomatch hok
    | some pNode =>
      rw [hf] at hok
      dsimp only at hok
      cases hdis : (pNode.perm == .disabled) with
      | true => rw [hdis] at hok; nomatch hok
      | false =>
        simp only [hdis, Bool.false_eq_true, ↓reduceIte] at hok
        if hob : w.bytes.length < off + len then
          simp only [hob, ↓reduceIte] at hok; nomatch hok
        else
          simp only [hob, ↓reduceIte] at hok
          intro n hmem hfrz
          cases hlen0 : Nat.beq len 0
          · simp only [hlen0, Bool.false_eq_true, Bool.false_and, ↓reduceIte,
              stepNodesAncestorFirst] at hok
            cases hca : checkAncestorsM w.nodes parentTag
                (stepNodeOnRangeRead w.nodes w.activeProtectors w.allocId off len parentTag) w.nodes with
            | error _ => rw [hca] at hok; nomatch hok
            | ok _ =>
              rw [hca] at hok
              dsimp only [Bind.bind, Except.bind] at hok
              cases hmap : mapNodesM
                  (stepNodeOnRangeRead w.nodes w.activeProtectors w.allocId off len parentTag) w.nodes with
              | error _ => rw [hmap] at hok; nomatch hok
              | ok ns' =>
                rw [hmap] at hok
                injection hok with hpair
                injection hpair with hw' _
                subst hw'
                apply List.mem_cons_of_mem
                refine mapNodesM_preserves_fixed_mem _ w.nodes ns' n hmap hmem ?_
                unfold stepNodeOnRangeRead
                simp only [hlen0, Bool.false_eq_true, ↓reduceIte, hfrz]
                cases isDescendantOrSelf w.nodes parentTag n.tag
                · cases byteRangeOverlapsWrite n.toByteRangePerm w.allocId off len <;> rfl
                · cases Nat.beq n.allocId w.allocId <;> rfl
          · simp only [hlen0, ↓reduceIte] at hok
            injection hok with hpair
            injection hpair with hw' _
            subst hw'
            exact List.mem_cons_of_mem _ hmem

/-- **Operational `Trusted.MirSemantics` Overlay (`applyParamFnEntryImplicitWrite`)**:
upgrades `evalStmt` on `StatementKind.retag .fnEntry place` with per-parameter
`FnEntryRetagPolicy` (`charon#1619` + `minirust#295`), gating the implicit child write on
`implicitWrites = true`, `paramMap.policyFor place.local_ == .writableChildWrite`, `tyIsUnpin`,
fresh child creation, AND `0 < head.rangeLen` (preserving ZST `&mut ()` safety). -/
def applyParamFnEntryImplicitWrite (preTag : Nat) (node : MirStepNode)
    (localDecls : List LocalDecl) (layouts : LayoutTable) (place : Place)
    (implicitWrites : Bool) (paramMap : FnParamRetagMap) (tyIsUnpin : Bool := true) :
    MirStepNode :=
  let policy := paramMap.policyFor place.local_
  match implicitWrites && (policy == .writableChildWrite) && tyIsUnpin with
  | false => node
  | true =>
    match placeTy localDecls layouts place with
    | some { kind := .ref .mut _, .. } =>
      match node with
      | .tau (.running s') =>
        match s'.memory.borrows with
        | head :: tail =>
          match Nat.beq head.tag preTag && Nat.beq s'.memory.nextTag (preTag + 1) &&
              !(Nat.beq head.rangeLen 0) with
          | true =>
            let allBorrows := head :: tail
            let writeUB :=
              treeBorrowAncestorsChildAccessUB .write allBorrows head.parentTag ||
                hasProtectedTreeWriteConflict allBorrows allBorrows s'.memory.activeProtectors
                  head.targetLocal (.some head.tag) head.targetProjection
                  head.rangeOffset head.rangeLen head.targetFrameDepth
            match writeUB with
            | true => MirStepNode.fail .ub
            | false =>
              MirStepNode.step
                { s' with memory := { s'.memory with
                    borrows :=
                      invalidateTreeBorrowsAtProj allBorrows allBorrows head.targetLocal
                        (.some head.tag) head.targetProjection head.rangeOffset
                        head.rangeLen head.targetFrameDepth } }
          | false => node
        | [] => node
      | _ => node
    | _ => node

def evalFnEntryRetagWithParamMap (s : MachineState) (place : Place) (span : String)
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (implicitWrites : Bool) (paramMap : FnParamRetagMap) (tyIsUnpin : Bool := true) :
    MirStepNode :=
  let raw := evalStmt s ⟨.retag .fnEntry place, span⟩ localDecls layouts
  applyParamFnEntryImplicitWrite s.memory.nextTag raw localDecls layouts place
    implicitWrites paramMap tyIsUnpin

/-- When `place.local_` carries `#[rustc_no_writable]` in `paramMap`, `evalFnEntryRetagWithParamMap`
equals `Trusted.MirSemantics.evalStmt` (which mints the protected `.reservedFrz false` child tag
without performing an implicit child write). -/
theorem evalFnEntryRetagWithParamMap_rustcNoWritable_eq_evalStmt
    (s : MachineState) (place : Place) (span : String)
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (implicitWrites : Bool) (paramMap : FnParamRetagMap) (tyIsUnpin : Bool)
    (hno : paramMap.policyFor place.local_ = .rustcNoWritable) :
    evalFnEntryRetagWithParamMap s place span localDecls layouts implicitWrites paramMap tyIsUnpin =
      evalStmt s ⟨.retag .fnEntry place, span⟩ localDecls layouts := by
  unfold evalFnEntryRetagWithParamMap applyParamFnEntryImplicitWrite
  dsimp only
  rw [hno]
  cases implicitWrites <;> cases tyIsUnpin <;> rfl

/-- When `head.rangeLen = 0` (e.g. `&mut ()` ZST local reference), `applyParamFnEntryImplicitWrite`
leaves the `MirStepNode` completely untouched even under `.writableChildWrite` and
`implicitWrites = true`. -/
theorem applyParamFnEntryImplicitWrite_zst_noop
    (preTag : Nat) (s' : MachineState) (head : BorrowEntry) (tail : List BorrowEntry)
    (localDecls : List LocalDecl) (layouts : LayoutTable) (place : Place)
    (implicitWrites : Bool) (paramMap : FnParamRetagMap) (tyIsUnpin : Bool)
    (hborrows : s'.memory.borrows = head :: tail)
    (hzst : head.rangeLen = 0) :
    applyParamFnEntryImplicitWrite preTag (.tau (.running s')) localDecls layouts place
      implicitWrites paramMap tyIsUnpin = .tau (.running s') := by
  unfold applyParamFnEntryImplicitWrite
  dsimp only
  cases implicitWrites && (paramMap.policyFor place.local_ == .writableChildWrite) && tyIsUnpin with
  | false => rfl
  | true =>
    dsimp only
    cases placeTy localDecls layouts place with
    | none => rfl
    | some ty =>
      rcases ty with ⟨kind, layoutIdx⟩
      cases kind with
      | ref m _ =>
        cases m with
        | not => rfl
        | «mut» => simp [hborrows, hzst]
      | _ => rfl

/-! ### Part 2B: Static-Access Temporary Retag Preservation Before `&raw const STATIC` (`charon#1620`) -/

/-- Freeze-visitor classification of a byte segment inside a `static` (`Miri.TreeBorrows.FreezeVisitor`). -/
inductive StaticSegmentKind where
  | freeze
  | unsafeCell
  deriving DecidableEq, Repr

/-- Half-open byte segment `[offset, offset + len)` within a `static` allocation. -/
structure StaticLayoutSegment where
  offset : Nat
  len : Nat
  kind : StaticSegmentKind
  deriving DecidableEq, Repr

/-- Type descriptor for `FreezeVisitor` layout decomposition of a `static` item (`charon#1620`). -/
inductive StaticTyDesc where
  | freezeScalar (sizeBytes : Nat)
  | unsafeCell (sizeBytes : Nat)
  | composite (totalBytes : Nat) (fields : List (Nat × StaticTyDesc))

mutual

/-- Source-ordered `FreezeVisitor.visitFreezeSensitive` segment builder: walks fields in increasing
offset order relative to `baseOff` and flushes every inter-field gap as `.freeze`. -/
def buildFreezeSegmentsDesc (absOff : Nat) : StaticTyDesc → List StaticLayoutSegment
  | .freezeScalar sz =>
    if 0 < sz then [⟨absOff, sz, .freeze⟩] else []
  | .unsafeCell sz =>
    if 0 < sz then [⟨absOff, sz, .unsafeCell⟩] else []
  | .composite _ subFields =>
    buildFreezeSegmentsFields absOff absOff subFields

def buildFreezeSegmentsFields (baseOff cursor : Nat) :
    List (Nat × StaticTyDesc) → List StaticLayoutSegment
  | [] => []
  | (relOff, fieldDesc) :: rest =>
    let absOff := baseOff + relOff
    let padBefore :=
      if cursor < absOff then [⟨cursor, absOff - cursor, .freeze⟩] else []
    let fieldSz :=
      match fieldDesc with
      | .freezeScalar sz => sz
      | .unsafeCell sz => sz
      | .composite totalSz _ => totalSz
    padBefore ++ buildFreezeSegmentsDesc absOff fieldDesc ++
      buildFreezeSegmentsFields baseOff (absOff + fieldSz) rest

end

def endCursorOfSegments (start : Nat) : List StaticLayoutSegment → Nat
  | [] => start
  | seg :: rest => endCursorOfSegments (seg.offset + seg.len) rest

/-- Decompose a `StaticTyDesc` into contiguous `.freeze` / `.unsafeCell` byte segments, flushing
trailing padding up to `totalSizeBytes` as `.freeze` (`FreezeVisitor.visitFreezeSensitive`). -/
def staticFreezeSegments (desc : StaticTyDesc) : Nat × List StaticLayoutSegment :=
  match desc with
  | .freezeScalar sz =>
    (sz, if 0 < sz then [⟨0, sz, .freeze⟩] else [])
  | .unsafeCell sz =>
    (sz, if 0 < sz then [⟨0, sz, .unsafeCell⟩] else [])
  | .composite totalSz fields =>
    let bodySegs := buildFreezeSegmentsFields 0 0 fields
    let endCur := endCursorOfSegments 0 bodySegs
    let trail :=
      if endCur < totalSz then [⟨endCur, totalSz - endCur, .freeze⟩] else []
    (totalSz, bodySegs ++ trail)

/-- Initial shared-reborrow permission for a static byte segment (`RetagPolicy.selectedPermission .Shared`):
`.frozen` on `.freeze` bytes, `.cell` on `.unsafeCell` bytes. -/
def StaticSegmentKind.sharedRetagPerm : StaticSegmentKind → TreeBorrowPerm
  | .freeze => .frozen
  | .unsafeCell => .cell

/-- Static pointer + borrow state produced by lowering `&raw const STATIC` (`[adv A1]`: carries
`rootTag` explicitly instead of hard-coding tags `1` and `2`). -/
structure StaticRawPtrState where
  allocId : Nat
  totalBytes : Nat
  ptrTag : Nat
  perms : List ByteRangePerm
  bytes : List AbstractByte
  rootTag : Nat := 1
  deriving DecidableEq, Repr

/-- Preserved static-access temporary retag (`charon#1620`) parameterized by arbitrary
`rootTag` and `childTag` (`[adv A1]`). -/
def retagStaticPreservedAt (rootTag childTag allocId : Nat) (desc : StaticTyDesc)
    (initBytes : List AbstractByte) : StaticRawPtrState :=
  let (totalSz, segs) := staticFreezeSegments desc
  let rootPerm : ByteRangePerm := ⟨rootTag, allocId, 0, totalSz, .active, none⟩
  let childPerms : List ByteRangePerm :=
    segs.map (fun seg =>
      ⟨childTag, allocId, seg.offset, seg.len,
        TreeBorrowPerm.toAbstractPerm seg.kind.sharedRetagPerm, none⟩)
  ⟨allocId, totalSz, childTag, rootPerm :: childPerms, initBytes, rootTag⟩

/-- Erased pre-`charon#1620` `&raw const STATIC` parameterized by arbitrary `rootTag` (`[adv A1]`). -/
def retagStaticErasedAt (rootTag allocId : Nat) (desc : StaticTyDesc)
    (initBytes : List AbstractByte) : StaticRawPtrState :=
  let (totalSz, _) := staticFreezeSegments desc
  let rootPerm : ByteRangePerm := ⟨rootTag, allocId, 0, totalSz, .active, none⟩
  ⟨allocId, totalSz, rootTag, [rootPerm], initBytes, rootTag⟩

def retagStaticPreserved (allocId : Nat) (desc : StaticTyDesc)
    (initBytes : List AbstractByte) : StaticRawPtrState :=
  retagStaticPreservedAt 1 2 allocId desc initBytes

def retagStaticErased (allocId : Nat) (desc : StaticTyDesc)
    (initBytes : List AbstractByte) : StaticRawPtrState :=
  retagStaticErasedAt 1 allocId desc initBytes

inductive StaticWriteResult where
  | ok (next : StaticRawPtrState)
  | ub
  deriving DecidableEq, Repr

def stepStaticPermsOnWrite (allocId ptrTag writeOff writeLen : Nat)
    (perms : List ByteRangePerm) (rootTag : Nat := 1) : Option (List ByteRangePerm) :=
  match perms with
  | [] => some []
  | entry :: rest =>
    if Nat.beq writeLen 0 then
      match stepStaticPermsOnWrite allocId ptrTag writeOff writeLen rest rootTag with
      | some rest' => some (entry :: rest')
      | none => none
    else if Nat.beq entry.tag ptrTag then
      if byteRangeOverlapsWrite entry allocId writeOff writeLen then
        match stepSelfWriteByteRange entry with
        | none => none
        | some entry' =>
          match stepStaticPermsOnWrite allocId ptrTag writeOff writeLen rest rootTag with
          | some rest' => some (entry' :: rest')
          | none => none
      else
        match stepStaticPermsOnWrite allocId ptrTag writeOff writeLen rest rootTag with
        | some rest' => some (entry :: rest')
        | none => none
    else
      if Nat.beq entry.tag rootTag then
        if byteRangeOverlapsWrite entry allocId writeOff writeLen then
          match stepSelfWriteByteRange entry with
          | none => none
          | some entry' =>
            match stepStaticPermsOnWrite allocId ptrTag writeOff writeLen rest rootTag with
            | some rest' => some (entry' :: rest')
            | none => none
        else
          match stepStaticPermsOnWrite allocId ptrTag writeOff writeLen rest rootTag with
          | some rest' => some (entry :: rest')
          | none => none
      else
        match stepForeignWriteByteRange ProtectorSet.empty entry allocId writeOff writeLen with
        | none => none
        | some entry' =>
          match stepStaticPermsOnWrite allocId ptrTag writeOff writeLen rest rootTag with
          | some rest' => some (entry' :: rest')
          | none => none

def evalRawMutStaticWrite (st : StaticRawPtrState) (writeOff : Nat)
    (newBytes : List AbstractByte) : StaticWriteResult :=
  let writeLen := newBytes.length
  if decide (st.totalBytes < writeOff + writeLen) ||
      decide (st.bytes.length < writeOff + writeLen) then
    .ub
  else
    match stepStaticPermsOnWrite st.allocId st.ptrTag writeOff writeLen st.perms st.rootTag with
    | none => .ub
    | some perms' =>
      let bytes' := (writeAbstractBytesAt st.bytes writeOff newBytes).getD st.bytes
      .ok { st with perms := perms', bytes := bytes' }

/-- **Theorem 2B.1 (`static_pureFreeze_preserved_ub_vs_erased_unsound`)**: on any non-ZST pure
`Freeze` `static` (`sizeBytes > 0`), mutating non-empty `newBytes` at offset `0` through
`(&raw const STATIC).cast_mut()` **faults with `.ub`** when the static-access temporary retag is
preserved (`charon#1620`), whereas pre-`#1620` erased `&raw const STATIC` **unsoundly succeeds**! -/
theorem static_pureFreeze_preserved_ub_vs_erased_unsound
    (allocId sizeBytes : Nat) (initBytes newBytes : List AbstractByte)
    (hsz : 0 < sizeBytes)
    (hne : 0 < newBytes.length)
    (hbound₁ : newBytes.length ≤ sizeBytes)
    (hbound₂ : newBytes.length ≤ initBytes.length) :
    evalRawMutStaticWrite (retagStaticPreserved allocId (.freezeScalar sizeBytes) initBytes) 0 newBytes = .ub ∧
    ∃ st', evalRawMutStaticWrite (retagStaticErased allocId (.freezeScalar sizeBytes) initBytes) 0 newBytes = .ok st' := by
  have hb₁ : decide (sizeBytes < 0 + newBytes.length) = false :=
    decide_eq_false (by omega)
  have hb₂ : decide (initBytes.length < 0 + newBytes.length) = false :=
    decide_eq_false (by omega)
  have hlen0 : Nat.beq newBytes.length 0 = false := by
    cases h : newBytes.length with
    | zero => omega
    | succ _ => rfl
  have hov : byteRangeOverlapsWrite ⟨2, allocId, 0, sizeBytes, .frozen, none⟩ allocId 0 newBytes.length = true := by
    unfold byteRangeOverlapsWrite
    simp only [Nat.beq_refl, Bool.true_and]
    unfold byteRangesOverlapBool
    cases sizeBytes with
    | zero => omega
    | succ _ =>
      cases hn : newBytes.length with
      | zero => omega
      | succ _ => rfl
  have hovRoot : byteRangeOverlapsWrite ⟨1, allocId, 0, sizeBytes, .active, none⟩ allocId 0 newBytes.length = true := by
    unfold byteRangeOverlapsWrite
    simp only [Nat.beq_refl, Bool.true_and]
    unfold byteRangesOverlapBool
    cases sizeBytes with
    | zero => omega
    | succ _ =>
      cases hn : newBytes.length with
      | zero => omega
      | succ _ => rfl
  constructor
  · unfold evalRawMutStaticWrite retagStaticPreserved retagStaticPreservedAt staticFreezeSegments
    simp only [hsz, ↓reduceIte, List.map, StaticSegmentKind.sharedRetagPerm,
      TreeBorrowPerm.toAbstractPerm]
    rw [hb₁, hb₂]
    have hstep2 :
        stepStaticPermsOnWrite allocId 2 0 newBytes.length
          [⟨2, allocId, 0, sizeBytes, .frozen, none⟩] 1 = none := by
      unfold stepStaticPermsOnWrite
      simp [hlen0, hov, stepSelfWriteByteRange, permAllowsWrite]
    have hstep1 :
        stepStaticPermsOnWrite allocId 2 0 newBytes.length
          [⟨1, allocId, 0, sizeBytes, .active, none⟩, ⟨2, allocId, 0, sizeBytes, .frozen, none⟩] 1 = none := by
      unfold stepStaticPermsOnWrite
      rw [hlen0]
      simp [hovRoot, stepSelfWriteByteRange, permAllowsWrite, permAfterSelfWrite, hstep2]
    rw [hstep1]
    rfl
  · refine ⟨{
      retagStaticErased allocId (.freezeScalar sizeBytes) initBytes with
      bytes := (writeAbstractBytesAt initBytes 0 newBytes).getD initBytes
    }, ?_⟩
    unfold evalRawMutStaticWrite retagStaticErased retagStaticErasedAt staticFreezeSegments
    dsimp only
    rw [hb₁, hb₂]
    have hstep :
        stepStaticPermsOnWrite allocId 1 0 newBytes.length
          [⟨1, allocId, 0, sizeBytes, .active, none⟩] 1 =
          some [⟨1, allocId, 0, sizeBytes, .active, none⟩] := by
      unfold stepStaticPermsOnWrite
      rw [hlen0]
      simp [hovRoot, stepSelfWriteByteRange, permAllowsWrite, permAfterSelfWrite,
        stepStaticPermsOnWrite]
    rw [hstep]
    rfl

/-- **Theorem 2B.2 (`static_pureUnsafeCell_preserved_write_ok`)**: on a `!Freeze` `static`
`AtomicI32` / `UnsafeCell` (`sizeBytes > 0`), preserving the temporary retag seeds `.cell` on
`[0, sizeBytes)`, so interior-mutable writes through `(&raw const STATIC).cast_mut()` succeed
without UB and preserve `.cell` permission across arbitrarily many writes! -/
theorem static_pureUnsafeCell_preserved_write_ok
    (allocId sizeBytes : Nat) (initBytes newBytes : List AbstractByte)
    (hsz : 0 < sizeBytes)
    (hne : 0 < newBytes.length)
    (hbound₁ : newBytes.length ≤ sizeBytes)
    (hbound₂ : newBytes.length ≤ initBytes.length) :
    evalRawMutStaticWrite (retagStaticPreserved allocId (.unsafeCell sizeBytes) initBytes) 0 newBytes =
      .ok {
        retagStaticPreserved allocId (.unsafeCell sizeBytes) initBytes with
        bytes := (writeAbstractBytesAt initBytes 0 newBytes).getD initBytes
      } := by
  have hb₁ : decide (sizeBytes < 0 + newBytes.length) = false :=
    decide_eq_false (by omega)
  have hb₂ : decide (initBytes.length < 0 + newBytes.length) = false :=
    decide_eq_false (by omega)
  have hlen0 : Nat.beq newBytes.length 0 = false := by
    cases h : newBytes.length with
    | zero => omega
    | succ _ => rfl
  have hov : byteRangeOverlapsWrite ⟨2, allocId, 0, sizeBytes, .cell, none⟩ allocId 0 newBytes.length = true := by
    unfold byteRangeOverlapsWrite
    simp only [Nat.beq_refl, Bool.true_and]
    unfold byteRangesOverlapBool
    cases sizeBytes with
    | zero => omega
    | succ _ =>
      cases hn : newBytes.length with
      | zero => omega
      | succ _ => rfl
  have hovRoot : byteRangeOverlapsWrite ⟨1, allocId, 0, sizeBytes, .active, none⟩ allocId 0 newBytes.length = true := by
    unfold byteRangeOverlapsWrite
    simp only [Nat.beq_refl, Bool.true_and]
    unfold byteRangesOverlapBool
    cases sizeBytes with
    | zero => omega
    | succ _ =>
      cases hn : newBytes.length with
      | zero => omega
      | succ _ => rfl
  unfold evalRawMutStaticWrite retagStaticPreserved retagStaticPreservedAt staticFreezeSegments
  simp only [hsz, ↓reduceIte, List.map, StaticSegmentKind.sharedRetagPerm,
    TreeBorrowPerm.toAbstractPerm]
  rw [hb₁, hb₂]
  have hstep2 :
      stepStaticPermsOnWrite allocId 2 0 newBytes.length
        [⟨2, allocId, 0, sizeBytes, .cell, none⟩] 1 =
        some [⟨2, allocId, 0, sizeBytes, .cell, none⟩] := by
    unfold stepStaticPermsOnWrite
    rw [hlen0]
    simp [hov, stepSelfWriteByteRange, permAllowsWrite, permAfterSelfWrite, stepStaticPermsOnWrite]
  have hstep1 :
      stepStaticPermsOnWrite allocId 2 0 newBytes.length
        [⟨1, allocId, 0, sizeBytes, .active, none⟩, ⟨2, allocId, 0, sizeBytes, .cell, none⟩] 1 =
        some [⟨1, allocId, 0, sizeBytes, .active, none⟩, ⟨2, allocId, 0, sizeBytes, .cell, none⟩] := by
    unfold stepStaticPermsOnWrite
    rw [hlen0]
    simp [hovRoot, stepSelfWriteByteRange, permAllowsWrite, permAfterSelfWrite, hstep2]
  rw [hstep1]
  rfl

/-- Allocation mutability rustc's const-eval interner assigns an immutable `static` item
(`intern_const_alloc_recursive`, `InternKind::Static(Mutability::Not)`, `[adv B1]`):
`Mutability::Not` iff the type is `Freeze` (no `UnsafeCell` byte), `Mutability::Mut` otherwise. -/
def staticAllocMutability (desc : StaticTyDesc) : Mutability :=
  if (staticFreezeSegments desc).2.any (fun seg => seg.kind == .unsafeCell) then .mut else .not

/-- Miri-faithful raw static write (`[adv B1]`): the allocation-mutability gate (Miri's
`writeToReadOnly` / read-only allocation check) runs before any Tree Borrows transition; zero-sized
writes are always permitted. `evalRawMutStaticWrite` alone is the Tree-Borrows-only semantics
(no allocation mutability), which is the setting in which A0's pure-`Freeze` separation holds. -/
def evalRawMutStaticWriteMiri (desc : StaticTyDesc) (st : StaticRawPtrState) (writeOff : Nat)
    (newBytes : List AbstractByte) : StaticWriteResult :=
  match staticAllocMutability desc with
  | .not => if Nat.beq newBytes.length 0 then evalRawMutStaticWrite st writeOff newBytes else .ub
  | .mut => evalRawMutStaticWrite st writeOff newBytes

/-- **Pure-`Freeze` Erasure Is Caught by the Read-Only Allocation in Miri
(`static_pureFreeze_erased_write_caught_by_readOnly_alloc`, `[adv B1]`)**: an immutable `Freeze`
static lives in a `Mutability::Not` allocation, so even Charon's pre-`#1620` erased
`&raw const STATIC` cannot mutate it without UB under Miri's semantics — the separation of
`static_pureFreeze_preserved_ub_vs_erased_unsound` is specific to a Tree-Borrows-only semantics
that drops allocation mutability. The case where erasure is genuinely unsound even with allocation
mutability is a *mixed* `(Freeze, UnsafeCell)` static (mutable allocation, `.frozen` `Freeze`
bytes): see `canary_part2B_mixed_static_erasure_unsound_under_miri_mutability`. -/
theorem static_pureFreeze_erased_write_caught_by_readOnly_alloc
    (allocId sizeBytes writeOff : Nat) (initBytes newBytes : List AbstractByte)
    (hne : 0 < newBytes.length) :
    staticAllocMutability (.freezeScalar sizeBytes) = .not ∧
    evalRawMutStaticWriteMiri (.freezeScalar sizeBytes)
      (retagStaticErased allocId (.freezeScalar sizeBytes) initBytes) writeOff newBytes = .ub ∧
    evalRawMutStaticWriteMiri (.freezeScalar sizeBytes)
      (retagStaticPreserved allocId (.freezeScalar sizeBytes) initBytes) writeOff newBytes = .ub := by
  have hmut : staticAllocMutability (.freezeScalar sizeBytes) = .not := by
    unfold staticAllocMutability staticFreezeSegments
    by_cases hsz : 0 < sizeBytes
    · simp [hsz]
    · simp [hsz]
  have hlen0 : Nat.beq newBytes.length 0 = false := by
    cases h : newBytes.length with
    | zero => omega
    | succ _ => rfl
  refine ⟨hmut, ?_, ?_⟩ <;> simp only [evalRawMutStaticWriteMiri, hmut, hlen0] <;> rfl

private theorem stepStaticPermsOnWrite_childSegs_none_of_freeze_overlap
    (rootTag childTag allocId writeOff writeLen : Nat)
    (hlen0 : Nat.beq writeLen 0 = false)
    (segs : List StaticLayoutSegment)
    (hfrz : ∃ seg ∈ segs,
      seg.kind = .freeze ∧ byteRangesOverlapBool seg.offset seg.len writeOff writeLen = true) :
    stepStaticPermsOnWrite allocId childTag writeOff writeLen
      (segs.map (fun seg =>
        ⟨childTag, allocId, seg.offset, seg.len,
          TreeBorrowPerm.toAbstractPerm seg.kind.sharedRetagPerm, none⟩)) rootTag = none := by
  induction segs with
  | nil =>
    rcases hfrz with ⟨_, hmem, _⟩
    nomatch hmem
  | cons hd tl ih =>
    rcases hfrz with ⟨seg, hmem, hkind, hov⟩
    rcases List.mem_cons.mp hmem with rfl | hmemTl
    · unfold stepStaticPermsOnWrite
      simp [hlen0, Nat.beq_refl, byteRangeOverlapsWrite, hov, hkind,
        StaticSegmentKind.sharedRetagPerm, TreeBorrowPerm.toAbstractPerm,
        stepSelfWriteByteRange, permAllowsWrite]
    · have ih' := ih ⟨seg, hmemTl, hkind, hov⟩
      unfold stepStaticPermsOnWrite
      simp only [List.map, hlen0, Bool.false_eq_true, ↓reduceIte, Nat.beq_refl]
      cases byteRangeOverlapsWrite
          ⟨childTag, allocId, hd.offset, hd.len,
            TreeBorrowPerm.toAbstractPerm hd.kind.sharedRetagPerm, none⟩
          allocId writeOff writeLen
      · simp [ih']
      · simp only [↓reduceIte]
        cases stepSelfWriteByteRange
            ⟨childTag, allocId, hd.offset, hd.len,
              TreeBorrowPerm.toAbstractPerm hd.kind.sharedRetagPerm, none⟩
        · rfl
        · simp [ih']

private theorem stepStaticPermsOnWrite_childSegs_some_of_all_unsafeCell
    (rootTag childTag allocId writeOff writeLen : Nat)
    (hlen0 : Nat.beq writeLen 0 = false)
    (segs : List StaticLayoutSegment)
    (hall : ∀ seg ∈ segs,
      byteRangesOverlapBool seg.offset seg.len writeOff writeLen = true →
      seg.kind = .unsafeCell) :
    let mapped := segs.map (fun seg =>
      ⟨childTag, allocId, seg.offset, seg.len,
        TreeBorrowPerm.toAbstractPerm seg.kind.sharedRetagPerm, none⟩)
    stepStaticPermsOnWrite allocId childTag writeOff writeLen mapped rootTag = some mapped := by
  induction segs with
  | nil => rfl
  | cons hd tl ih =>
    have ih' := ih (fun s hs hov => hall s (List.mem_cons_of_mem _ hs) hov)
    dsimp only [List.map] at ih' ⊢
    unfold stepStaticPermsOnWrite
    simp only [hlen0, Bool.false_eq_true, ↓reduceIte, Nat.beq_refl]
    cases hov : byteRangesOverlapBool hd.offset hd.len writeOff writeLen
    · simp [byteRangeOverlapsWrite, hov, ih']
    · have huc : hd.kind = .unsafeCell := hall hd (List.mem_cons_self ..) hov
      rw [ih']
      simp [byteRangeOverlapsWrite, Nat.beq_refl, hov, huc,
        StaticSegmentKind.sharedRetagPerm, TreeBorrowPerm.toAbstractPerm,
        stepSelfWriteByteRange, permAllowsWrite, permAfterSelfWrite]

/-- **General Mixed-Static `charon#1620` Separation Under Miri Allocation Mutability
(`static_mixed_miri_separation`, `[adv A1]`)**: for *any* `desc : StaticTyDesc` (arbitrary nested
composite with arbitrary padding), *any* tags `rootTag ≠ childTag`, and *any* non-empty in-bounds
write at arbitrary offset `writeOff`:
1. If `(staticFreezeSegments desc).2` has at least one `.unsafeCell` segment, rustc interns the
   static with `staticAllocMutability desc = .mut`.
2. If `[writeOff, writeOff + newBytes.length)` overlaps any `.freeze` segment (whether a `Freeze`
   field, inter-field padding, or trailing padding!), `evalRawMutStaticWriteMiri` **faults with
   `.ub`** on `retagStaticPreservedAt`, whereas pre-`#1620` `retagStaticErasedAt` **unsoundly
   succeeds with `.ok`**! -/
theorem static_mixed_miri_separation
    (desc : StaticTyDesc) (rootTag childTag allocId writeOff : Nat)
    (initBytes newBytes : List AbstractByte)
    (hneTag : rootTag ≠ childTag)
    (hne : 0 < newBytes.length)
    (hbound₁ : writeOff + newBytes.length ≤ (staticFreezeSegments desc).1)
    (hbound₂ : writeOff + newBytes.length ≤ initBytes.length)
    (hhasUC : ∃ uc ∈ (staticFreezeSegments desc).2, uc.kind = .unsafeCell)
    (hfrzOv : ∃ frz ∈ (staticFreezeSegments desc).2,
      frz.kind = .freeze ∧
      byteRangesOverlapBool frz.offset frz.len writeOff newBytes.length = true) :
    staticAllocMutability desc = .mut ∧
    evalRawMutStaticWriteMiri desc
      (retagStaticPreservedAt rootTag childTag allocId desc initBytes) writeOff newBytes = .ub ∧
    ∃ st', evalRawMutStaticWriteMiri desc
      (retagStaticErasedAt rootTag allocId desc initBytes) writeOff newBytes = .ok st' := by
  have hmut : staticAllocMutability desc = .mut := by
    rcases hhasUC with ⟨uc, hucMem, hucKind⟩
    unfold staticAllocMutability
    have hany : ((staticFreezeSegments desc).2.any (fun seg => seg.kind == .unsafeCell)) = true :=
      List.any_eq_true.mpr ⟨uc, hucMem, by simp [hucKind]⟩
    simp [hany]
  have hlen0 : Nat.beq newBytes.length 0 = false := by
    cases h : newBytes.length with
    | zero => omega
    | succ _ => rfl
  have hb₁ : decide ((staticFreezeSegments desc).1 < writeOff + newBytes.length) = false :=
    decide_eq_false (by omega)
  have hb₂ : decide (initBytes.length < writeOff + newBytes.length) = false :=
    decide_eq_false (by omega)
  have htag_ne : Nat.beq rootTag childTag = false := by
    cases h : Nat.beq rootTag childTag with
    | false => rfl
    | true => exact False.elim (hneTag (Nat.eq_of_beq_eq_true h))
  refine ⟨hmut, ?_, ?_⟩
  · unfold evalRawMutStaticWriteMiri evalRawMutStaticWrite retagStaticPreservedAt
    rw [hmut]
    dsimp only
    rw [hb₁, hb₂]
    have hchildNone := stepStaticPermsOnWrite_childSegs_none_of_freeze_overlap
      rootTag childTag allocId writeOff newBytes.length hlen0 (staticFreezeSegments desc).2 hfrzOv
    unfold stepStaticPermsOnWrite
    simp only [hlen0, Bool.false_eq_true, ↓reduceIte, htag_ne, Nat.beq_refl]
    cases byteRangeOverlapsWrite ⟨rootTag, allocId, 0, (staticFreezeSegments desc).1, .active, none⟩
        allocId writeOff newBytes.length <;>
      simp [stepSelfWriteByteRange, permAllowsWrite, permAfterSelfWrite, hchildNone]
  · refine ⟨{
      retagStaticErasedAt rootTag allocId desc initBytes with
      bytes := (writeAbstractBytesAt initBytes writeOff newBytes).getD initBytes
    }, ?_⟩
    unfold evalRawMutStaticWriteMiri evalRawMutStaticWrite retagStaticErasedAt
    rw [hmut]
    dsimp only
    rw [hb₁, hb₂]
    unfold stepStaticPermsOnWrite
    simp only [hlen0, Bool.false_eq_true, ↓reduceIte, Nat.beq_refl]
    cases byteRangeOverlapsWrite ⟨rootTag, allocId, 0, (staticFreezeSegments desc).1, .active, none⟩
        allocId writeOff newBytes.length <;>
      simp [stepSelfWriteByteRange, permAllowsWrite, permAfterSelfWrite, stepStaticPermsOnWrite]

/-- **General Mixed-Static `UnsafeCell` Sub-Range Write Soundness
(`static_mixed_miri_unsafeCell_write_ok`, `[adv A1]`)**: for *any* `desc : StaticTyDesc` with at
least one `.unsafeCell` segment, any non-empty in-bounds write `[writeOff, writeOff + newBytes.length)`
whose overlapping segments are all `.unsafeCell` succeeds under `evalRawMutStaticWriteMiri` on
`retagStaticPreservedAt` and preserves every segment permission! -/
theorem static_mixed_miri_unsafeCell_write_ok
    (desc : StaticTyDesc) (rootTag childTag allocId writeOff : Nat)
    (initBytes newBytes : List AbstractByte)
    (hneTag : rootTag ≠ childTag)
    (hne : 0 < newBytes.length)
    (hbound₁ : writeOff + newBytes.length ≤ (staticFreezeSegments desc).1)
    (hbound₂ : writeOff + newBytes.length ≤ initBytes.length)
    (hhasUC : ∃ uc ∈ (staticFreezeSegments desc).2, uc.kind = .unsafeCell)
    (hallUC : ∀ seg ∈ (staticFreezeSegments desc).2,
      byteRangesOverlapBool seg.offset seg.len writeOff newBytes.length = true →
      seg.kind = .unsafeCell) :
    evalRawMutStaticWriteMiri desc
      (retagStaticPreservedAt rootTag childTag allocId desc initBytes) writeOff newBytes =
      .ok {
        retagStaticPreservedAt rootTag childTag allocId desc initBytes with
        bytes := (writeAbstractBytesAt initBytes writeOff newBytes).getD initBytes
      } := by
  have hmut : staticAllocMutability desc = .mut := by
    rcases hhasUC with ⟨uc, hucMem, hucKind⟩
    unfold staticAllocMutability
    have hany : ((staticFreezeSegments desc).2.any (fun seg => seg.kind == .unsafeCell)) = true :=
      List.any_eq_true.mpr ⟨uc, hucMem, by simp [hucKind]⟩
    simp [hany]
  have hlen0 : Nat.beq newBytes.length 0 = false := by
    cases h : newBytes.length with
    | zero => omega
    | succ _ => rfl
  have hb₁ : decide ((staticFreezeSegments desc).1 < writeOff + newBytes.length) = false :=
    decide_eq_false (by omega)
  have hb₂ : decide (initBytes.length < writeOff + newBytes.length) = false :=
    decide_eq_false (by omega)
  have htag_ne : Nat.beq rootTag childTag = false := by
    cases h : Nat.beq rootTag childTag with
    | false => rfl
    | true => exact False.elim (hneTag (Nat.eq_of_beq_eq_true h))
  have hchildOk := stepStaticPermsOnWrite_childSegs_some_of_all_unsafeCell
    rootTag childTag allocId writeOff newBytes.length hlen0 (staticFreezeSegments desc).2 hallUC
  unfold evalRawMutStaticWriteMiri evalRawMutStaticWrite retagStaticPreservedAt
  rw [hmut]
  dsimp only
  rw [hb₁, hb₂]
  unfold stepStaticPermsOnWrite
  simp only [hlen0, Bool.false_eq_true, ↓reduceIte, htag_ne, Nat.beq_refl]
  cases byteRangeOverlapsWrite ⟨rootTag, allocId, 0, (staticFreezeSegments desc).1, .active, none⟩
      allocId writeOff newBytes.length <;>
    simp [stepSelfWriteByteRange, permAllowsWrite, permAfterSelfWrite, hchildOk]

/-! ## Section 4: Part 3 — Array `[T; N]` `Sized` Fast-Path (`lean-miri#79`), Principal-Less `dyn Send` VTables (`lean-miri#75`), & Null-VTable Precedence (`lean-miri#82`) -/

/-! ### Part 3A: Syntactic `[T; N]` `Sized` Fast-Path in Raw-Pointer Validity (`lean-miri#79`) -/

/-- Maximum representable object byte size on 64-bit targets (`isize::MAX = 2^63 - 1`,
matching `Miri.Memory.PointerArithmetic.maxSizeOfVal`). -/
def maxRepresentableSize64 : Nat := 9223372036854775807

/-- Maximum unsigned 64-bit count/address (`usize::MAX = 2^64 - 1`). -/
def usizeMax64 : Nat := 18446744073709551615

/-- Prototype type syntax covering scalars, `[T; N]`, `[T]`, `str`, `dyn`, `foreign`, pointers,
tuples, and ADTs, with a total bridge `toRigidTy` to `Trusted.MirAst.RigidTy`. -/
inductive ProtoTy where
  | bool
  | char
  | u8 | u16 | u32 | u64 | usize
  | i32 | i64 | isize
  | never
  | str
  | array (elem : ProtoTy) (count : Nat)
  | slice (elem : ProtoTy)
  | rawPtr (mutability : Mutability) (pointee : ProtoTy)
  | ref (mutability : Mutability) (pointee : ProtoTy)
  | fnPtr
  | tuple (fields : List ProtoTy)
  | adt (defPath : DefPath) (fields : List ProtoTy)
  | dynamic (traitDesc : String)
  | foreign (defPath : DefPath)
  deriving Repr

mutual

/-- Bridge `ProtoTy` into real `Trusted.Rustc.V2026_06_01.MirAst.RigidTy`. -/
def ProtoTy.toRigidTy : ProtoTy → RigidTy
  | .bool => .bool
  | .char => .char
  | .u8 => .uint .u8
  | .u16 => .uint .u16
  | .u32 => .uint .u32
  | .u64 => .uint .u64
  | .usize => .uint .usize
  | .i32 => .int .i32
  | .i64 => .int .i64
  | .isize => .int .isize
  | .never => .never
  | .str => .str
  | .array elem n => .array elem.toRigidTy n
  | .slice elem => .slice elem.toRigidTy
  | .rawPtr m pt => .rawPtr m pt.toRigidTy
  | .ref m pt => .ref m pt.toRigidTy
  | .fnPtr => .fnPtr [] (.tuple []) .safe .rust
  | .tuple fs => .tuple (protoTyListToRigidTy fs)
  | .adt dp fs => .adt dp (protoTyListToRigidTy fs)
  | .dynamic tr => .dynamic tr
  | .foreign dp => .foreign dp

def protoTyListToRigidTy : List ProtoTy → List RigidTy
  | [] => []
  | t :: ts => t.toRigidTy :: protoTyListToRigidTy ts

end

/-- Raw UTF-8 byte sequence of a `String` as `List Nat` without calling `String.toList`
(`String.toList` in Lean `v4.34.1` invokes `ByteArray.utf8Decode?`, whose termination proof
transitively pulls `Classical.choice`). -/
def stringToRawNatBytes (s : String) : List Nat :=
  s.toByteArray.data.toList.map UInt8.toNat

private theorem map_uint8_toNat_inj :
    ∀ {xs ys : List UInt8}, xs.map UInt8.toNat = ys.map UInt8.toNat → xs = ys
  | [], [], _ => rfl
  | [], _ :: _, h => nomatch h
  | _ :: _, [], h => nomatch h
  | x :: xs, y :: ys, h => by
    injection h with hhd htl
    have hxy : x = y := UInt8.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq hhd)
    rw [hxy, map_uint8_toNat_inj htl]

private theorem string_eq_of_toList_map_toNat {s₁ s₂ : String}
    (h : stringToRawNatBytes s₁ = stringToRawNatBytes s₂) : s₁ = s₂ := by
  cases s₁ with
  | ofByteArray b₁ v₁ =>
    cases s₂ with
    | ofByteArray b₂ v₂ =>
      cases b₁ with
      | mk a₁ =>
        cases b₂ with
        | mk a₂ =>
          cases a₁ with
          | mk l₁ =>
            cases a₂ with
            | mk l₂ =>
              have hl : l₁ = l₂ := map_uint8_toNat_inj h
              subst hl
              rfl

mutual

/-- Total injective prefix-free code for `ProtoTy` (yielding both `DecidableEq ProtoTy` and
`LawfulEqCmp` for `VTableKey` without `Classical.choice`). -/
def encodeProtoTyCode : ProtoTy → List Nat
  | .bool => [0]
  | .char => [1]
  | .u8 => [2]
  | .u16 => [3]
  | .u32 => [4]
  | .u64 => [5]
  | .usize => [6]
  | .i32 => [7]
  | .i64 => [8]
  | .isize => [9]
  | .never => [10]
  | .str => [11]
  | .fnPtr => [12]
  | .array elem n => 13 :: n :: encodeProtoTyCode elem
  | .slice elem => 14 :: encodeProtoTyCode elem
  | .rawPtr m pt => 15 :: (match m with | .not => 0 | .mut => 1) :: encodeProtoTyCode pt
  | .ref m pt => 16 :: (match m with | .not => 0 | .mut => 1) :: encodeProtoTyCode pt
  | .tuple fs => 17 :: fs.length :: encodeProtoTyListCode fs
  | .adt dp fs =>
    let bs := stringToRawNatBytes dp
    18 :: bs.length :: (bs ++ (fs.length :: encodeProtoTyListCode fs))
  | .dynamic tr =>
    let bs := stringToRawNatBytes tr
    19 :: bs.length :: bs
  | .foreign dp =>
    let bs := stringToRawNatBytes dp
    20 :: bs.length :: bs

def encodeProtoTyListCode : List ProtoTy → List Nat
  | [] => []
  | t :: ts => encodeProtoTyCode t ++ encodeProtoTyListCode ts

end

private theorem append_inj_of_len_eq {α : Type} :
    ∀ {a₁ a₂ b₁ b₂ : List α}, a₁.length = a₂.length → a₁ ++ b₁ = a₂ ++ b₂ → a₁ = a₂ ∧ b₁ = b₂
  | [], [], _, _, _, h => ⟨rfl, h⟩
  | [], _ :: _, _, _, hlen, _ => nomatch hlen
  | _ :: _, [], _, _, hlen, _ => nomatch hlen
  | x :: xs, y :: ys, b₁, b₂, hlen, h => by
    injection h with hxy hrest
    obtain ⟨hxs, hb⟩ := append_inj_of_len_eq (Nat.succ.inj hlen) hrest
    exact ⟨by rw [hxy, hxs], hb⟩

mutual

private theorem encodeProtoTyCode_prefix_inj :
    ∀ (t₁ t₂ : ProtoTy) (r₁ r₂ : List Nat),
      encodeProtoTyCode t₁ ++ r₁ = encodeProtoTyCode t₂ ++ r₂ → t₁ = t₂ ∧ r₁ = r₂
  | .bool, t₂, _, _, h => by
    cases t₂ <;> first | (injection h with _ hr; exact ⟨rfl, hr⟩) | nomatch h
  | .char, t₂, _, _, h => by
    cases t₂ <;> first | (injection h with _ hr; exact ⟨rfl, hr⟩) | nomatch h
  | .u8, t₂, _, _, h => by
    cases t₂ <;> first | (injection h with _ hr; exact ⟨rfl, hr⟩) | nomatch h
  | .u16, t₂, _, _, h => by
    cases t₂ <;> first | (injection h with _ hr; exact ⟨rfl, hr⟩) | nomatch h
  | .u32, t₂, _, _, h => by
    cases t₂ <;> first | (injection h with _ hr; exact ⟨rfl, hr⟩) | nomatch h
  | .u64, t₂, _, _, h => by
    cases t₂ <;> first | (injection h with _ hr; exact ⟨rfl, hr⟩) | nomatch h
  | .usize, t₂, _, _, h => by
    cases t₂ <;> first | (injection h with _ hr; exact ⟨rfl, hr⟩) | nomatch h
  | .i32, t₂, _, _, h => by
    cases t₂ <;> first | (injection h with _ hr; exact ⟨rfl, hr⟩) | nomatch h
  | .i64, t₂, _, _, h => by
    cases t₂ <;> first | (injection h with _ hr; exact ⟨rfl, hr⟩) | nomatch h
  | .isize, t₂, _, _, h => by
    cases t₂ <;> first | (injection h with _ hr; exact ⟨rfl, hr⟩) | nomatch h
  | .never, t₂, _, _, h => by
    cases t₂ <;> first | (injection h with _ hr; exact ⟨rfl, hr⟩) | nomatch h
  | .str, t₂, _, _, h => by
    cases t₂ <;> first | (injection h with _ hr; exact ⟨rfl, hr⟩) | nomatch h
  | .fnPtr, t₂, _, _, h => by
    cases t₂ <;> first | (injection h with _ hr; exact ⟨rfl, hr⟩) | nomatch h
  | .array e₁ n₁, t₂, r₁, r₂, h => by
    cases t₂ with
    | array e₂ n₂ =>
      simp only [encodeProtoTyCode, List.cons_append] at h
      injection h with _ h₁
      injection h₁ with hn h₂
      obtain ⟨he, hr⟩ := encodeProtoTyCode_prefix_inj e₁ e₂ r₁ r₂ h₂
      subst hn he
      exact ⟨rfl, hr⟩
    | _ => nomatch h
  | .slice e₁, t₂, r₁, r₂, h => by
    cases t₂ with
    | slice e₂ =>
      simp only [encodeProtoTyCode, List.cons_append] at h
      injection h with _ h₁
      obtain ⟨he, hr⟩ := encodeProtoTyCode_prefix_inj e₁ e₂ r₁ r₂ h₁
      subst he
      exact ⟨rfl, hr⟩
    | _ => nomatch h
  | .rawPtr m₁ p₁, t₂, r₁, r₂, h => by
    cases t₂ with
    | rawPtr m₂ p₂ =>
      simp only [encodeProtoTyCode, List.cons_append] at h
      injection h with _ h₁
      injection h₁ with hm h₂
      obtain ⟨hp, hr⟩ := encodeProtoTyCode_prefix_inj p₁ p₂ r₁ r₂ h₂
      have hm_eq : m₁ = m₂ := by
        cases m₁ <;> cases m₂ <;> first | rfl | nomatch hm
      subst hm_eq hp
      exact ⟨rfl, hr⟩
    | _ => nomatch h
  | .ref m₁ p₁, t₂, r₁, r₂, h => by
    cases t₂ with
    | ref m₂ p₂ =>
      simp only [encodeProtoTyCode, List.cons_append] at h
      injection h with _ h₁
      injection h₁ with hm h₂
      obtain ⟨hp, hr⟩ := encodeProtoTyCode_prefix_inj p₁ p₂ r₁ r₂ h₂
      have hm_eq : m₁ = m₂ := by
        cases m₁ <;> cases m₂ <;> first | rfl | nomatch hm
      subst hm_eq hp
      exact ⟨rfl, hr⟩
    | _ => nomatch h
  | .tuple fs₁, t₂, r₁, r₂, h => by
    cases t₂ with
    | tuple fs₂ =>
      simp only [encodeProtoTyCode, List.cons_append] at h
      injection h with _ h₁
      injection h₁ with hlen h₂
      obtain ⟨hfs, hr⟩ := encodeProtoTyListCode_prefix_inj fs₁ fs₂ r₁ r₂ hlen h₂
      subst hfs
      exact ⟨rfl, hr⟩
    | _ => nomatch h
  | .adt dp₁ fs₁, t₂, r₁, r₂, h => by
    cases t₂ with
    | adt dp₂ fs₂ =>
      simp only [encodeProtoTyCode, List.cons_append, List.append_assoc] at h
      injection h with _ h₁
      injection h₁ with hdplen h₂
      obtain ⟨hdp_cs, h₃⟩ := append_inj_of_len_eq hdplen h₂
      have hdp : dp₁ = dp₂ := string_eq_of_toList_map_toNat hdp_cs
      injection h₃ with hfslen h₄
      obtain ⟨hfs, hr⟩ := encodeProtoTyListCode_prefix_inj fs₁ fs₂ r₁ r₂ hfslen h₄
      subst hdp hfs
      exact ⟨rfl, hr⟩
    | _ => nomatch h
  | .dynamic tr₁, t₂, r₁, r₂, h => by
    cases t₂ with
    | dynamic tr₂ =>
      simp only [encodeProtoTyCode, List.cons_append] at h
      injection h with _ h₁
      injection h₁ with hlen h₂
      obtain ⟨hcs, hr⟩ := append_inj_of_len_eq hlen h₂
      exact ⟨congrArg ProtoTy.dynamic (string_eq_of_toList_map_toNat hcs), hr⟩
    | _ => nomatch h
  | .foreign dp₁, t₂, r₁, r₂, h => by
    cases t₂ with
    | foreign dp₂ =>
      simp only [encodeProtoTyCode, List.cons_append] at h
      injection h with _ h₁
      injection h₁ with hlen h₂
      obtain ⟨hcs, hr⟩ := append_inj_of_len_eq hlen h₂
      exact ⟨congrArg ProtoTy.foreign (string_eq_of_toList_map_toNat hcs), hr⟩
    | _ => nomatch h

private theorem encodeProtoTyListCode_prefix_inj :
    ∀ (fs₁ fs₂ : List ProtoTy) (r₁ r₂ : List Nat),
      fs₁.length = fs₂.length →
      encodeProtoTyListCode fs₁ ++ r₁ = encodeProtoTyListCode fs₂ ++ r₂ →
      fs₁ = fs₂ ∧ r₁ = r₂
  | [], [], _, _, _, h => ⟨rfl, h⟩
  | [], _ :: _, _, _, hlen, _ => nomatch hlen
  | _ :: _, [], _, _, hlen, _ => nomatch hlen
  | f₁ :: fs₁, f₂ :: fs₂, r₁, r₂, hlen, h => by
    simp only [encodeProtoTyListCode, List.append_assoc] at h
    obtain ⟨hf, hrest⟩ := encodeProtoTyCode_prefix_inj f₁ f₂ _ _ h
    obtain ⟨hfs, hr⟩ := encodeProtoTyListCode_prefix_inj fs₁ fs₂ r₁ r₂ (Nat.succ.inj hlen) hrest
    exact ⟨by rw [hf, hfs], hr⟩

end

instance : DecidableEq ProtoTy := fun a b =>
  if h : encodeProtoTyCode a = encodeProtoTyCode b then
    isTrue ((encodeProtoTyCode_prefix_inj a b [] [] (by simpa using h)).1)
  else
    isFalse (fun heq => h (congrArg encodeProtoTyCode heq))

inductive LayoutComputeErr where
  | sizeOverflow (computedBytes maxBytes : Nat)
  | unsizedNonTailField
  | unsizedArrayElement
  deriving DecidableEq, Repr

structure ComputedTyLayout where
  sizeBytes : Nat
  alignBytes : Nat
  isSized : Bool
  isInhabited : Bool := true
  deriving DecidableEq, Repr

mutual

def computeTyLayout (maxSize : Nat) : ProtoTy → Except LayoutComputeErr ComputedTyLayout
  | .bool | .u8 => .ok ⟨1, 1, true, true⟩
  | .u16 => .ok ⟨2, 2, true, true⟩
  | .char | .u32 | .i32 => .ok ⟨4, 4, true, true⟩
  | .u64 | .usize | .i64 | .isize => .ok ⟨8, 8, true, true⟩
  | .never => .ok ⟨0, 1, true, false⟩
  | .str => .ok ⟨0, 1, false, true⟩
  | .rawPtr _ _ | .ref _ _ | .fnPtr => .ok ⟨8, 8, true, true⟩
  | .dynamic _ | .foreign _ => .ok ⟨0, 1, false, true⟩
  | .slice elem => do
    let el ← computeTyLayout maxSize elem
    if !el.isSized then throw LayoutComputeErr.unsizedArrayElement
    return ⟨0, el.alignBytes, false, true⟩
  | .array elem count => do
    let el ← computeTyLayout maxSize elem
    if !el.isSized then throw LayoutComputeErr.unsizedArrayElement
    let total := el.sizeBytes * count
    if total > maxSize then
      throw (LayoutComputeErr.sizeOverflow total maxSize)
    return ⟨total, el.alignBytes, true, count == 0 || el.isInhabited⟩
  | .tuple fields => computeFieldsLayout maxSize 0 1 true fields
  | .adt _ fields => computeFieldsLayout maxSize 0 1 true fields

def computeFieldsLayout (maxSize accSize accAlign : Nat) (accInhab : Bool) :
    List ProtoTy → Except LayoutComputeErr ComputedTyLayout
  | [] =>
    let finalSz := roundUpToAlign accSize accAlign
    if finalSz > maxSize then .error (.sizeOverflow finalSz maxSize)
    else .ok ⟨finalSz, accAlign, true, accInhab⟩
  | f :: rest =>
    match rest with
    | [] => do
      let l ← computeTyLayout maxSize f
      let nextAlign := Nat.max accAlign l.alignBytes
      let alignedOff := roundUpToAlign accSize l.alignBytes
      if !l.isSized then
        if alignedOff > maxSize then throw (LayoutComputeErr.sizeOverflow alignedOff maxSize)
        return ⟨alignedOff, nextAlign, false, accInhab && l.isInhabited⟩
      else
        let rawEnd := alignedOff + l.sizeBytes
        let finalSz := roundUpToAlign rawEnd nextAlign
        if finalSz > maxSize then throw (LayoutComputeErr.sizeOverflow finalSz maxSize)
        return ⟨finalSz, nextAlign, true, accInhab && l.isInhabited⟩
    | _ :: _ => do
      let l ← computeTyLayout maxSize f
      if !l.isSized then throw LayoutComputeErr.unsizedNonTailField
      let nextAlign := Nat.max accAlign l.alignBytes
      let alignedOff := roundUpToAlign accSize l.alignBytes
      let nextSize := alignedOff + l.sizeBytes
      if nextSize > maxSize then throw (LayoutComputeErr.sizeOverflow nextSize maxSize)
      computeFieldsLayout maxSize nextSize nextAlign (accInhab && l.isInhabited) rest

end

mutual

/-- **Syntactic `Sized` Fast-Path (`lean-miri#79`)**: recognizes `[T; N]` (`.array _ _`), scalars,
pointers, and aggregates with syntactically `Sized` tails *without* computing `elemSize * N`!
Compiled via pure structural recursion (`ProtoTy.rec`), so `isSyntacticallySized (.array _ _)`
reduces in `O(1)` in the kernel without inspecting element layout. -/
def isSyntacticallySized : ProtoTy → Bool
  | .bool | .char | .u8 | .u16 | .u32 | .u64 | .usize | .i32 | .i64 | .isize | .never => true
  | .rawPtr _ _ | .ref _ _ | .fnPtr => true
  | .array _ _ => true
  | .str | .slice _ | .dynamic _ | .foreign _ => false
  | .tuple fields => fieldsTailSyntacticallySized true fields
  | .adt _ fields => fieldsTailSyntacticallySized true fields

def fieldsTailSyntacticallySized (acc : Bool) : List ProtoTy → Bool
  | [] => acc
  | f :: fs => fieldsTailSyntacticallySized (isSyntacticallySized f) fs

end

mutual

/-- **Soundness of `isSyntacticallySized` vs. `computeTyLayout`**: on *every* type whose layout
succeeds (`computeTyLayout maxSize ty = .ok layout`), `isSyntacticallySized ty` equals
`layout.isSized`! -/
theorem isSyntacticallySized_eq_of_computeTyLayout_ok (maxSize : Nat) :
    ∀ (ty : ProtoTy) (layout : ComputedTyLayout),
      computeTyLayout maxSize ty = .ok layout →
      isSyntacticallySized ty = layout.isSized
  | .bool, layout, h => by unfold computeTyLayout at h; injection h with h'; subst h'; rfl
  | .char, layout, h => by unfold computeTyLayout at h; injection h with h'; subst h'; rfl
  | .u8, layout, h => by unfold computeTyLayout at h; injection h with h'; subst h'; rfl
  | .u16, layout, h => by unfold computeTyLayout at h; injection h with h'; subst h'; rfl
  | .u32, layout, h => by unfold computeTyLayout at h; injection h with h'; subst h'; rfl
  | .u64, layout, h => by unfold computeTyLayout at h; injection h with h'; subst h'; rfl
  | .usize, layout, h => by unfold computeTyLayout at h; injection h with h'; subst h'; rfl
  | .i32, layout, h => by unfold computeTyLayout at h; injection h with h'; subst h'; rfl
  | .i64, layout, h => by unfold computeTyLayout at h; injection h with h'; subst h'; rfl
  | .isize, layout, h => by unfold computeTyLayout at h; injection h with h'; subst h'; rfl
  | .never, layout, h => by unfold computeTyLayout at h; injection h with h'; subst h'; rfl
  | .str, layout, h => by unfold computeTyLayout at h; injection h with h'; subst h'; rfl
  | .rawPtr _ _, layout, h => by unfold computeTyLayout at h; injection h with h'; subst h'; rfl
  | .ref _ _, layout, h => by unfold computeTyLayout at h; injection h with h'; subst h'; rfl
  | .fnPtr, layout, h => by unfold computeTyLayout at h; injection h with h'; subst h'; rfl
  | .dynamic _, layout, h => by unfold computeTyLayout at h; injection h with h'; subst h'; rfl
  | .foreign _, layout, h => by unfold computeTyLayout at h; injection h with h'; subst h'; rfl
  | .slice elem, layout, h => by
    unfold computeTyLayout at h
    cases hc : computeTyLayout maxSize elem with
    | error _ => rw [hc] at h; nomatch h
    | ok el =>
      rw [hc] at h
      cases hs : el.isSized with
      | false =>
        simp [hs, Bind.bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
      | true =>
        simp [hs, Bind.bind, Except.bind, Pure.pure, Except.pure] at h
        subst h
        rfl
  | .array elem count, layout, h => by
    unfold computeTyLayout at h
    cases hc : computeTyLayout maxSize elem with
    | error _ => rw [hc] at h; nomatch h
    | ok el =>
      rw [hc] at h
      dsimp only [Bind.bind, Except.bind] at h
      cases hs : el.isSized with
      | false =>
        simp [hs, throw, throwThe, MonadExceptOf.throw] at h
      | true =>
        simp only [hs, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
        split at h
        · simp [throw, throwThe, MonadExceptOf.throw] at h
        · simp [Pure.pure, Except.pure] at h
          subst h
          rfl
  | .tuple fields, layout, h => by
    unfold computeTyLayout at h
    unfold isSyntacticallySized
    exact fieldsTailSyntacticallySized_eq_of_ok maxSize 0 1 true fields true layout
      (fun _ => rfl) h
  | .adt _ fields, layout, h => by
    unfold computeTyLayout at h
    unfold isSyntacticallySized
    exact fieldsTailSyntacticallySized_eq_of_ok maxSize 0 1 true fields true layout
      (fun _ => rfl) h

theorem fieldsTailSyntacticallySized_eq_of_ok (maxSize accSize accAlign : Nat) (accInhab : Bool) :
    ∀ (fields : List ProtoTy) (acc : Bool) (layout : ComputedTyLayout),
      (fields = [] → acc = true) →
      computeFieldsLayout maxSize accSize accAlign accInhab fields = .ok layout →
      fieldsTailSyntacticallySized acc fields = layout.isSized
  | [], acc, layout, hemp, h => by
    unfold computeFieldsLayout at h
    dsimp only at h
    split at h
    · nomatch h
    · injection h with h'
      subst h'
      exact hemp rfl
  | [last], acc, layout, _, h => by
    unfold computeFieldsLayout at h
    cases hc : computeTyLayout maxSize last with
    | error _ => rw [hc] at h; nomatch h
    | ok l =>
      rw [hc] at h
      dsimp only [Bind.bind, Except.bind] at h
      have ih := isSyntacticallySized_eq_of_computeTyLayout_ok maxSize last l hc
      unfold fieldsTailSyntacticallySized
      unfold fieldsTailSyntacticallySized
      rw [ih]
      cases hs : l.isSized with
      | false =>
        simp only [hs, Bool.not_false, ↓reduceIte] at h
        split at h
        · simp [throw, throwThe, MonadExceptOf.throw] at h
        · simp [Pure.pure, Except.pure] at h
          subst h
          rfl
      | true =>
        simp only [hs, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
        split at h
        · simp [throw, throwThe, MonadExceptOf.throw] at h
        · simp [Pure.pure, Except.pure] at h
          subst h
          rfl
  | f :: r₁ :: rs, acc, layout, _, h => by
    unfold computeFieldsLayout at h
    cases hc : computeTyLayout maxSize f with
    | error _ => rw [hc] at h; nomatch h
    | ok l =>
      rw [hc] at h
      dsimp only [Bind.bind, Except.bind] at h
      cases hs : l.isSized with
      | false =>
        simp [hs, throw, throwThe, MonadExceptOf.throw] at h
      | true =>
        simp only [hs, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
        split at h
        · simp [throw, throwThe, MonadExceptOf.throw] at h
        · unfold fieldsTailSyntacticallySized
          exact fieldsTailSyntacticallySized_eq_of_ok maxSize _ _ _ (r₁ :: rs)
            (isSyntacticallySized f) layout (fun hnil => nomatch hnil) h

end

/-- Runtime representation of a raw or safe pointer value (`ValidityVisitor.lean`). -/
inductive PtrReprVal where
  | thin (addr : UInt64) (prov : Option MiriAllocId)
  | wideSlice (addr : UInt64) (prov : Option MiriAllocId) (elemCount : UInt64)
  | wideDyn (addr : UInt64) (prov : Option MiriAllocId) (vtableAddr : UInt64)
      (vtableProv : Option MiriAllocId)
  deriving DecidableEq, Repr

inductive PtrValErr where
  | layoutErr (err : LayoutComputeErr)
  | expectedThinRawPtr
  | expectedWideSliceMeta
  | expectedWideDynMeta
  | nullSafePtr
  | unalignedSafePtr
  | danglingOrOutOfBoundsSafePtr
  | uninhabitedSafePtr
  deriving DecidableEq, Repr

/-- Pointer metadata kind required by a type's unsized tail (`rustc_middle::ty::Ty::struct_tail_for_codegen`
and `ValidityVisitor.lean:184–195`, `[adv A2]`):
- `sliceMeta`: `[T]`, `str`, or a tuple/ADT whose recursive last field has a `sliceMeta` tail,
- `dynMeta`: `dyn Trait`, or a tuple/ADT whose recursive last field has a `dynMeta` tail,
- `externThin`: `extern type` (`foreign`), or a tuple/ADT wrapping a `foreign` tail (unsized, yet
  thin pointer representation!). -/
inductive UnsizedMetaKind where
  | sliceMeta
  | dynMeta
  | externThin
  deriving DecidableEq, Repr

mutual

/-- Recursive unsized-tail metadata classification (`[adv A2]`): `none` iff syntactically `Sized`,
and `some kind` for slice, `dyn`, or `extern type` tails (including custom struct/tuple DSTs such as
`(u32, [u8])`, `([u8; usize::MAX], [u8])`, and `MyDst<dyn Send>`, which A0–B2 rejected with
`.expectedWideSliceMeta` even when supplied valid wide metadata!). -/
def unsizedMetadataTail : ProtoTy → Option UnsizedMetaKind
  | .bool | .char | .u8 | .u16 | .u32 | .u64 | .usize | .i32 | .i64 | .isize | .never => none
  | .rawPtr _ _ | .ref _ _ | .fnPtr => none
  | .array _ _ => none
  | .str | .slice _ => some .sliceMeta
  | .dynamic _ => some .dynMeta
  | .foreign _ => some .externThin
  | .tuple fields => fieldsUnsizedMetadataTail none fields
  | .adt _ fields => fieldsUnsizedMetadataTail none fields

def fieldsUnsizedMetadataTail (acc : Option UnsizedMetaKind) :
    List ProtoTy → Option UnsizedMetaKind
  | [] => acc
  | f :: fs => fieldsUnsizedMetadataTail (unsizedMetadataTail f) fs

end

mutual

/-- **Syntactic `Sized` Iff `unsizedMetadataTail = none` (`isSyntacticallySized_eq_metadataTail_isNone`,
`[adv A2]`)**: `isSyntacticallySized ty` agrees identically with `(unsizedMetadataTail ty).isNone`
across all `ProtoTy` trees. -/
theorem isSyntacticallySized_eq_metadataTail_isNone :
    ∀ (ty : ProtoTy), isSyntacticallySized ty = (unsizedMetadataTail ty).isNone
  | .bool | .char | .u8 | .u16 | .u32 | .u64 | .usize | .i32 | .i64 | .isize | .never => rfl
  | .rawPtr _ _ | .ref _ _ | .fnPtr => rfl
  | .array _ _ => rfl
  | .str | .slice _ | .dynamic _ | .foreign _ => rfl
  | .tuple fields => fieldsTailSized_eq_metadataTail_isNone none fields
  | .adt _ fields => fieldsTailSized_eq_metadataTail_isNone none fields

theorem fieldsTailSized_eq_metadataTail_isNone (acc : Option UnsizedMetaKind) :
    ∀ (fields : List ProtoTy),
      fieldsTailSyntacticallySized acc.isNone fields = (fieldsUnsizedMetadataTail acc fields).isNone
  | [] => rfl
  | f :: fs => by
    unfold fieldsTailSyntacticallySized fieldsUnsizedMetadataTail
    rw [isSyntacticallySized_eq_metadataTail_isNone f]
    exact fieldsTailSized_eq_metadataTail_isNone (unsizedMetadataTail f) fs

end

def validateUnsizedRawPtrMeta (metaKind : UnsizedMetaKind) (val : PtrReprVal) :
    Except PtrValErr Unit :=
  match metaKind, val with
  | .sliceMeta, .wideSlice _ _ _ => .ok ()
  | .sliceMeta, _ => .error .expectedWideSliceMeta
  | .dynMeta, .wideDyn _ _ vAddr vProv =>
    if vAddr == 0 && vProv.isNone then .error .expectedWideDynMeta else .ok ()
  | .dynMeta, _ => .error .expectedWideDynMeta
  | .externThin, .thin _ _ => .ok ()
  | .externThin, _ => .error .expectedThinRawPtr

/-- Legacy layout-first raw-pointer validator (pre-`lean-miri#79`, custom-DST tail fixed in
`[adv A2]`): queries `computeTyLayout` *before* checking whether the pointee is `Sized`. -/
def validateRawPtrLayoutFirst (maxSize : Nat) (pointee : ProtoTy) (val : PtrReprVal) :
    Except PtrValErr Unit := do
  let layout ← (computeTyLayout maxSize pointee).mapError PtrValErr.layoutErr
  if layout.isSized then
    match val with
    | .thin _ _ => .ok ()
    | _ => .error .expectedThinRawPtr
  else
    match unsizedMetadataTail pointee with
    | none => .error .expectedWideSliceMeta
    | some mk => validateUnsizedRawPtrMeta mk val

/-- **`lean-miri#79` Syntactic `Sized` & Tail-Metadata Fast-Path Raw-Pointer Validator
(`[adv A2]` custom-DST fix)**: consults `isSyntacticallySized pointee` (and `unsizedMetadataTail`
only when unsized) *without* invoking `computeTyLayout`! -/
def validateRawPtrFastPath (pointee : ProtoTy) (val : PtrReprVal) :
    Except PtrValErr Unit :=
  if isSyntacticallySized pointee then
    match val with
    | .thin _ _ => .ok ()
    | _ => .error .expectedThinRawPtr
  else
    match unsizedMetadataTail pointee with
    | none => .error .expectedWideSliceMeta
    | some mk => validateUnsizedRawPtrMeta mk val

/-- Safe-reference validator (`&pointee` / `&mut pointee`): *always* enforces `computeTyLayout`,
non-nullness, alignment, inhabitedness, and live allocation bounds! -/
def validateSafeThinRef (maxSize : Nat) (w : KeyedAllocWorld) (pointee : ProtoTy)
    (addr : UInt64) (prov : Option MiriAllocId) : Except PtrValErr Unit := do
  let layout ← (computeTyLayout maxSize pointee).mapError PtrValErr.layoutErr
  if !layout.isSized then throw PtrValErr.expectedWideSliceMeta
  if addr == 0 && prov.isNone then throw PtrValErr.nullSafePtr
  if !layout.isInhabited then throw PtrValErr.uninhabitedSafePtr
  if layout.alignBytes > 0 && (addr.toNat % layout.alignBytes != 0) then
    throw PtrValErr.unalignedSafePtr
  if layout.sizeBytes > 0 then
    let some id := prov | throw PtrValErr.danglingOrOutOfBoundsSafePtr
    let some live := w.findLive? id | throw PtrValErr.danglingOrOutOfBoundsSafePtr
    if layout.sizeBytes > live.sizeBytes.toNat then throw PtrValErr.danglingOrOutOfBoundsSafePtr
  return ()

/-- **Agreement Theorem (`validateRawPtrFastPath_eq_layoutFirst_of_layoutOk`)**: for *every*
`pointee` whose layout computation succeeds, `validateRawPtrFastPath` and
`validateRawPtrLayoutFirst` return the **exact same** validation outcome on every `PtrReprVal`. -/
theorem validateRawPtrFastPath_eq_layoutFirst_of_layoutOk
    (maxSize : Nat) (pointee : ProtoTy) (layout : ComputedTyLayout) (val : PtrReprVal)
    (hok : computeTyLayout maxSize pointee = .ok layout) :
    validateRawPtrFastPath pointee val = validateRawPtrLayoutFirst maxSize pointee val := by
  unfold validateRawPtrFastPath validateRawPtrLayoutFirst
  rw [hok, isSyntacticallySized_eq_of_computeTyLayout_ok maxSize pointee layout hok]
  rfl

/-- **Strict Separation Theorem (`oversized_array_rawPtr_separation`)**: on `*const [elem; count]`
whenever `elem` has layout size `elemSz > 0` and `elemSz * count > maxSize` (such as
`*const [u8; usize::MAX]` and `*const [[u8; 2]; usize::MAX]` on 64-bit targets):
1. `validateRawPtrFastPath` succeeds (`.ok ()`) for every thin pointer (including `null` and
   dangling addresses),
2. `validateRawPtrLayoutFirst` spuriously fails with `.error (.layoutErr (.sizeOverflow ...))`, AND
3. Safe reference `validateSafeThinRef` still rejects `&[elem; count]` with layout overflow! -/
theorem oversized_array_rawPtr_separation
    (maxSize : Nat) (w : KeyedAllocWorld) (elem : ProtoTy) (el : ComputedTyLayout)
    (count : Nat) (addr : UInt64) (prov : Option MiriAllocId)
    (hel : computeTyLayout maxSize elem = .ok el)
    (hsized : el.isSized = true)
    (hoverflow : el.sizeBytes * count > maxSize) :
    validateRawPtrFastPath (.array elem count) (.thin addr prov) = .ok () ∧
    validateRawPtrLayoutFirst maxSize (.array elem count) (.thin addr prov) =
      .error (.layoutErr (.sizeOverflow (el.sizeBytes * count) maxSize)) ∧
    validateSafeThinRef maxSize w (.array elem count) addr prov =
      .error (.layoutErr (.sizeOverflow (el.sizeBytes * count) maxSize)) := by
  refine ⟨rfl, ?_, ?_⟩
  · unfold validateRawPtrLayoutFirst computeTyLayout
    simp [hel, hsized, hoverflow, Except.mapError, Bind.bind, Except.bind,
      throw, throwThe, MonadExceptOf.throw]
  · unfold validateSafeThinRef computeTyLayout
    simp [hel, hsized, hoverflow, Except.mapError, Bind.bind, Except.bind,
      throw, throwThe, MonadExceptOf.throw]

/-- **Slice DST Contrast Theorem (`slice_dst_rawPtr_requires_wideSliceMeta`)**: unlike fixed-length
arrays `[T; N]`, unsized slice DSTs `[T]` (`.slice elem`) are **not** syntactically `Sized`; a thin
raw pointer `*const [T]` fails with `.expectedWideSliceMeta`, whereas a wide slice raw pointer
carrying `elemCount` metadata succeeds! -/
theorem slice_dst_rawPtr_requires_wideSliceMeta
    (elem : ProtoTy) (addr elemCount : UInt64) (prov : Option MiriAllocId) :
    isSyntacticallySized (.slice elem) = false ∧
    validateRawPtrFastPath (.slice elem) (.thin addr prov) = .error .expectedWideSliceMeta ∧
    validateRawPtrFastPath (.slice elem) (.wideSlice addr prov elemCount) = .ok () :=
  ⟨rfl, rfl, rfl⟩

/-- **Custom Struct/Tuple DST Raw-Pointer Fast-Path & Oversized-Head Separation
(`customDst_oversizedHead_rawPtr_separation`, `[adv A2]`)**: on a custom tuple DST
`*const ([elem; count], [tailElem])` whose sized head field `[elem; count]` overflows `maxSize`:
1. `validateRawPtrFastPath` walks `unsizedMetadataTail` (`some .sliceMeta`) without computing
   `el.sizeBytes * count`, **succeeding** on `.wideSlice` and rejecting `.thin` with
   `.expectedWideSliceMeta` (A0–B2 rejected `.wideSlice` on *all* custom tuple/ADT DSTs!),
2. `validateRawPtrLayoutFirst` spuriously fails with `.error (.layoutErr (.sizeOverflow ...))`! -/
theorem customDst_oversizedHead_rawPtr_separation
    (maxSize : Nat) (elem tailElem : ProtoTy) (el : ComputedTyLayout)
    (count : Nat) (addr elemCount : UInt64) (prov : Option MiriAllocId)
    (hel : computeTyLayout maxSize elem = .ok el)
    (hsized : el.isSized = true)
    (hoverflow : el.sizeBytes * count > maxSize) :
    let dstTy : ProtoTy := .tuple [.array elem count, .slice tailElem]
    unsizedMetadataTail dstTy = some .sliceMeta ∧
    validateRawPtrFastPath dstTy (.wideSlice addr prov elemCount) = .ok () ∧
    validateRawPtrFastPath dstTy (.thin addr prov) = .error .expectedWideSliceMeta ∧
    validateRawPtrLayoutFirst maxSize dstTy (.wideSlice addr prov elemCount) =
      .error (.layoutErr (.sizeOverflow (el.sizeBytes * count) maxSize)) := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  have harr : computeTyLayout maxSize (.array elem count) =
      .error (.sizeOverflow (el.sizeBytes * count) maxSize) := by
    unfold computeTyLayout
    simp [hel, hsized, hoverflow, Bind.bind, Except.bind,
      throw, throwThe, MonadExceptOf.throw]
  unfold validateRawPtrLayoutFirst computeTyLayout computeFieldsLayout
  simp [harr, Except.mapError, Bind.bind, Except.bind]

/-! ### Part 3B: Principal-Less Auto-Trait `dyn Send` VTable Keys & Registry (`lean-miri#75`) -/

/-- Rust auto-traits permitted in trait-object existential bounds (`dyn Send`, `dyn Sync`, etc.). -/
inductive AutoTrait where
  | send
  | sync
  | unpin
  | unwindSafe
  | refUnwindSafe
  deriving DecidableEq, Repr

def AutoTrait.rank : AutoTrait → Nat
  | .send => 0
  | .sync => 1
  | .unpin => 2
  | .unwindSafe => 3
  | .refUnwindSafe => 4

theorem AutoTrait.rank_injective {a b : AutoTrait} (h : a.rank = b.rank) : a = b := by
  cases a <;> cases b <;> first | rfl | nomatch h

instance : Ord AutoTrait where
  compare a b := compare a.rank b.rank

instance : TransCmp (compare : AutoTrait → AutoTrait → Ordering) where
  eq_swap {a b} := nat_compare_eq_swap a.rank b.rank
  isLE_trans := nat_compare_isLE_trans

instance : LawfulEqCmp (compare : AutoTrait → AutoTrait → Ordering) where
  eq_of_compare h := AutoTrait.rank_injective (nat_compare_eq_of_compare h)
  compare_self {a} := nat_compare_self a.rank

def insertAutoTraitCanon (t : AutoTrait) : List AutoTrait → List AutoTrait
  | [] => [t]
  | h :: rest =>
    match compare t h with
    | .lt => t :: h :: rest
    | .eq => h :: rest
    | .gt => h :: insertAutoTraitCanon t rest

def canonicalizeAutoTraits : List AutoTrait → List AutoTrait
  | [] => []
  | t :: ts => insertAutoTraitCanon t (canonicalizeAutoTraits ts)

/-- Canonicalized set of auto-trait markers (`dyn Send + Sync` == `dyn Sync + Send`). -/
structure AutoTraitSet where
  traits : List AutoTrait
  deriving DecidableEq, Repr

def AutoTraitSet.ofList (ts : List AutoTrait) : AutoTraitSet :=
  ⟨canonicalizeAutoTraits ts⟩

def AutoTraitSet.contains (s : AutoTraitSet) (t : AutoTrait) : Bool :=
  s.traits.any (· == t)

def AutoTraitSet.containsAll (sup sub : AutoTraitSet) : Bool :=
  sub.traits.all (fun t => sup.contains t)

private theorem strictlySorted_insertAutoTraitCanon (t : AutoTrait) {xs : List AutoTrait}
    (hxs : List.Pairwise (fun a b => compare a b = .lt) xs) :
    List.Pairwise (fun a b => compare a b = .lt) (insertAutoTraitCanon t xs) := by
  induction xs with
  | nil => simp [insertAutoTraitCanon]
  | cons q rest ih =>
    obtain ⟨hq_rest, hrest⟩ := List.pairwise_cons.mp hxs
    unfold insertAutoTraitCanon
    cases hcq : compare t q with
    | lt =>
      rw [List.pairwise_cons]
      refine ⟨?_, hxs⟩
      intro p hp
      rcases List.mem_cons.mp hp with rfl | hp_rest
      · exact hcq
      · exact TransCmp.lt_trans hcq (hq_rest p hp_rest)
    | eq => exact hxs
    | gt =>
      rw [List.pairwise_cons]
      refine ⟨?_, ih hrest⟩
      intro p hp
      have hmem : p = t ∨ p ∈ rest := by
        clear hxs hq_rest hrest ih hcq
        induction rest with
        | nil =>
          simp [insertAutoTraitCanon] at hp
          exact .inl hp
        | cons r rs ihr =>
          unfold insertAutoTraitCanon at hp
          split at hp
          · rcases List.mem_cons.mp hp with rfl | hrs
            · exact .inl rfl
            · exact .inr hrs
          · exact .inr hp
          · rcases List.mem_cons.mp hp with rfl | hrs
            · exact .inr (List.mem_cons_self ..)
            · rcases ihr hrs with rfl | hm
              · exact .inl rfl
              · exact .inr (List.mem_cons_of_mem _ hm)
      rcases hmem with rfl | hp_rest
      · exact OrientedCmp.lt_of_gt hcq
      · exact hq_rest p hp_rest

private theorem strictlySorted_canonicalizeAutoTraits (ts : List AutoTrait) :
    List.Pairwise (fun a b => compare a b = .lt) (canonicalizeAutoTraits ts) := by
  induction ts with
  | nil => exact List.Pairwise.nil
  | cons t rest ih => exact strictlySorted_insertAutoTraitCanon t ih

private theorem mem_insertAutoTraitCanon (t x : AutoTrait) (xs : List AutoTrait) :
    x ∈ insertAutoTraitCanon t xs ↔ x = t ∨ x ∈ xs := by
  induction xs with
  | nil => simp [insertAutoTraitCanon]
  | cons q rest ih =>
    unfold insertAutoTraitCanon
    cases hcq : compare t q with
    | lt => simp
    | eq =>
      have htq : t = q := LawfulEqCmp.eq_of_compare hcq
      subst htq
      simp
    | gt =>
      simp only [List.mem_cons, ih]
      constructor
      · rintro (rfl | rfl | hr)
        · exact .inr (.inl rfl)
        · exact .inl rfl
        · exact .inr (.inr hr)
      · rintro (rfl | rfl | hr)
        · exact .inr (.inl rfl)
        · exact .inl rfl
        · exact .inr (.inr hr)

theorem mem_canonicalizeAutoTraits_iff (ts : List AutoTrait) (x : AutoTrait) :
    x ∈ canonicalizeAutoTraits ts ↔ x ∈ ts := by
  induction ts with
  | nil => simp [canonicalizeAutoTraits]
  | cons t rest ih =>
    simp [canonicalizeAutoTraits, mem_insertAutoTraitCanon, ih]

private theorem strictlySorted_autoTrait_eq_of_mem_iff {xs ys : List AutoTrait}
    (hxs : List.Pairwise (fun a b => compare a b = .lt) xs)
    (hys : List.Pairwise (fun a b => compare a b = .lt) ys)
    (hmem : ∀ x, x ∈ xs ↔ x ∈ ys) : xs = ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons q _ =>
      have hq := (hmem q).mpr (List.mem_cons_self ..)
      nomatch hq
  | cons p xr ih =>
    obtain ⟨hp_xr, hxr⟩ := List.pairwise_cons.mp hxs
    cases ys with
    | nil =>
      have hp := (hmem p).mp (List.mem_cons_self ..)
      nomatch hp
    | cons q yr =>
      obtain ⟨hq_yr, hyr⟩ := List.pairwise_cons.mp hys
      cases hpq : compare p q with
      | lt =>
        have hp_in_y := (hmem p).mp (List.mem_cons_self ..)
        rcases List.mem_cons.mp hp_in_y with rfl | hp_yr
        · rw [ReflCmp.compare_self (cmp := compare)] at hpq; nomatch hpq
        · have hqp : compare q p = .lt := hq_yr p hp_yr
          have hpp : compare p p = .lt := TransCmp.lt_trans hpq hqp
          rw [ReflCmp.compare_self (cmp := compare)] at hpp; nomatch hpp
      | gt =>
        have hqp : compare q p = .lt := OrientedCmp.lt_of_gt hpq
        have hq_in_x := (hmem q).mpr (List.mem_cons_self ..)
        rcases List.mem_cons.mp hq_in_x with rfl | hq_xr
        · rw [ReflCmp.compare_self (cmp := compare)] at hqp; nomatch hqp
        · have hpq' : compare p q = .lt := hp_xr q hq_xr
          have hqq : compare q q = .lt := TransCmp.lt_trans hqp hpq'
          rw [ReflCmp.compare_self (cmp := compare)] at hqq; nomatch hqq
      | eq =>
        have heq : p = q := LawfulEqCmp.eq_of_compare hpq
        subst heq
        congr 1
        apply ih hxr hyr
        intro x
        constructor
        · intro hx
          have hx_ne_p : x ≠ p := by
            intro rfl
            have hlt := hp_xr x hx
            rw [ReflCmp.compare_self (cmp := compare)] at hlt; nomatch hlt
          have hxy := (hmem x).mp (List.mem_cons_of_mem _ hx)
          rcases List.mem_cons.mp hxy with rfl | hy
          · exact absurd rfl hx_ne_p
          · exact hy
        · intro hy
          have hx_ne_p : x ≠ p := by
            intro rfl
            have hlt := hq_yr x hy
            rw [ReflCmp.compare_self (cmp := compare)] at hlt; nomatch hlt
          have hyx := (hmem x).mpr (List.mem_cons_of_mem _ hy)
          rcases List.mem_cons.mp hyx with rfl | hx
          · exact absurd rfl hx_ne_p
          · exact hx

/-- **Auto-Trait Canonicalization Theorem (`AutoTraitSet.ofList_eq_of_mem_iff`)**: any two lists of
auto-traits with the same membership canonicalize to the **identical** `AutoTraitSet`. -/
theorem AutoTraitSet.ofList_eq_of_mem_iff {ts₁ ts₂ : List AutoTrait}
    (h : ∀ x, x ∈ ts₁ ↔ x ∈ ts₂) :
    AutoTraitSet.ofList ts₁ = AutoTraitSet.ofList ts₂ := by
  unfold AutoTraitSet.ofList
  congr 1
  apply strictlySorted_autoTrait_eq_of_mem_iff
    (strictlySorted_canonicalizeAutoTraits ts₁)
    (strictlySorted_canonicalizeAutoTraits ts₂)
  intro x
  rw [mem_canonicalizeAutoTraits_iff, mem_canonicalizeAutoTraits_iff]
  exact h x

/-- Principal trait reference (`dyn PrincipalTrait<...> + AutoTraits`). -/
structure PrincipalTraitRef where
  traitDefPath : DefPath
  normalizedPredicates : List Nat := []
  methodNames : List DefPath := []
  deriving DecidableEq, Repr

/-- Existential trait-object specification (`lean-miri#75`). -/
structure DynExistentialSpec where
  principal : Option PrincipalTraitRef
  autoTraits : AutoTraitSet
  deriving DecidableEq, Repr

def DynExistentialSpec.principalLess (ts : List AutoTrait) : DynExistentialSpec :=
  ⟨none, AutoTraitSet.ofList ts⟩

/-- VTable entry slot (`Miri.Interpreter.VTableEntry`). -/
inductive VTableSlot where
  | dropInPlace (fnDef : DefPath)
  | size (bytes : UInt64)
  | align (bytes : UInt64)
  | vacant
  | method (fnDef : DefPath)
  deriving DecidableEq, Repr

/-- Symbolic vtable descriptor stored in global memory (`lean-miri#75`). -/
structure VTableDescriptor where
  allocId : MiriAllocId
  concreteTy : ProtoTy
  spec : DynExistentialSpec
  dropInPlaceFn : DefPath
  sizeBytes : UInt64
  alignBytes : UInt64
  entries : List VTableSlot
  deriving DecidableEq, Repr

/-- Canonical vtable deduplication key (`concreteTy, principal, autoTraits`). -/
structure VTableKey where
  concreteTy : ProtoTy
  principal : Option PrincipalTraitRef
  autoTraits : AutoTraitSet
  deriving DecidableEq, Repr

def encodeStringCode (s : String) : List Nat :=
  let cs := stringToRawNatBytes s
  cs.length :: cs

def encodeStringListCode : List String → List Nat
  | [] => [0]
  | s :: ss => 1 :: (encodeStringCode s ++ encodeStringListCode ss)

def encodeVTableKeyCode (k : VTableKey) : List Nat :=
  let principalCode : List Nat :=
    match k.principal with
    | none => [0]
    | some p =>
      1 :: (encodeStringCode p.traitDefPath ++
        (p.normalizedPredicates.length :: p.normalizedPredicates) ++
        encodeStringListCode p.methodNames)
  let autoCode : List Nat := k.autoTraits.traits.map AutoTrait.rank
  principalCode ++ (autoCode.length :: autoCode) ++ encodeProtoTyCode k.concreteTy

private theorem encodeStringCode_prefix_inj {s₁ s₂ : String} {r₁ r₂ : List Nat}
    (h : encodeStringCode s₁ ++ r₁ = encodeStringCode s₂ ++ r₂) : s₁ = s₂ ∧ r₁ = r₂ := by
  unfold encodeStringCode at h
  simp only [List.cons_append] at h
  injection h with hlen hrest
  obtain ⟨hcs, hr⟩ := append_inj_of_len_eq hlen hrest
  exact ⟨string_eq_of_toList_map_toNat hcs, hr⟩

private theorem encodeStringListCode_prefix_inj :
    ∀ {xs ys : List String} {r₁ r₂ : List Nat},
      encodeStringListCode xs ++ r₁ = encodeStringListCode ys ++ r₂ → xs = ys ∧ r₁ = r₂
  | [], [], _, _, h => by
    simp only [encodeStringListCode, List.cons_append, List.nil_append] at h
    injection h with _ hr
    exact ⟨rfl, hr⟩
  | [], _ :: _, _, _, h => by
    simp only [encodeStringListCode, List.cons_append] at h
    nomatch h
  | _ :: _, [], _, _, h => by
    simp only [encodeStringListCode, List.cons_append] at h
    nomatch h
  | x :: xs, y :: ys, r₁, r₂, h => by
    simp only [encodeStringListCode, List.cons_append, List.append_assoc] at h
    injection h with _ hrest
    obtain ⟨hxy, htail⟩ := encodeStringCode_prefix_inj hrest
    obtain ⟨hxs, hr⟩ := encodeStringListCode_prefix_inj htail
    exact ⟨by rw [hxy, hxs], hr⟩

private theorem map_autoTrait_rank_inj :
    ∀ {xs ys : List AutoTrait}, xs.map AutoTrait.rank = ys.map AutoTrait.rank → xs = ys
  | [], [], _ => rfl
  | [], _ :: _, h => nomatch h
  | _ :: _, [], h => nomatch h
  | x :: xs, y :: ys, h => by
    injection h with hhd htl
    rw [AutoTrait.rank_injective hhd, map_autoTrait_rank_inj htl]

theorem encodeVTableKeyCode_injective {k₁ k₂ : VTableKey}
    (h : encodeVTableKeyCode k₁ = encodeVTableKeyCode k₂) : k₁ = k₂ := by
  rcases k₁ with ⟨ty₁, pr₁, ⟨at₁⟩⟩
  rcases k₂ with ⟨ty₂, pr₂, ⟨at₂⟩⟩
  unfold encodeVTableKeyCode at h
  have h_principal : pr₁ = pr₂ ∧
      ((at₁.map AutoTrait.rank).length :: at₁.map AutoTrait.rank) ++ encodeProtoTyCode ty₁ =
      ((at₂.map AutoTrait.rank).length :: at₂.map AutoTrait.rank) ++ encodeProtoTyCode ty₂ := by
    cases pr₁ with
    | none =>
      cases pr₂ with
      | none =>
        simp only [List.cons_append, List.nil_append] at h
        injection h with _ hrest
        exact ⟨rfl, hrest⟩
      | some _ =>
        simp only [List.cons_append] at h
        nomatch h
    | some p₁ =>
      cases pr₂ with
      | none =>
        simp only [List.cons_append] at h
        nomatch h
      | some p₂ =>
        rcases p₁ with ⟨dp₁, np₁, mn₁⟩
        rcases p₂ with ⟨dp₂, np₂, mn₂⟩
        simp only [List.cons_append, List.append_assoc] at h
        injection h with _ h₁
        obtain ⟨hdp, h₂⟩ := encodeStringCode_prefix_inj h₁
        injection h₂ with hnplen h₃
        obtain ⟨hnp, h₄⟩ := append_inj_of_len_eq hnplen h₃
        obtain ⟨hmn, h₅⟩ := encodeStringListCode_prefix_inj h₄
        subst hdp hnp hmn
        exact ⟨rfl, h₅⟩
  obtain ⟨hpr, hrem⟩ := h_principal
  simp only [List.cons_append] at hrem
  injection hrem with hatlen hrem₂
  obtain ⟨hat_ranks, hty_code⟩ := append_inj_of_len_eq hatlen hrem₂
  have hat : at₁ = at₂ := map_autoTrait_rank_inj hat_ranks
  have hty_app : encodeProtoTyCode ty₁ ++ [] = encodeProtoTyCode ty₂ ++ [] := by
    simpa using hty_code
  obtain ⟨hty, _⟩ := encodeProtoTyCode_prefix_inj ty₁ ty₂ [] [] hty_app
  subst hpr hat hty
  rfl

def compareNatList : List Nat → List Nat → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | x :: xs, y :: ys =>
    match compare x y with
    | .lt => .lt
    | .gt => .gt
    | .eq => compareNatList xs ys

private theorem compareNatList_eq_swap : ∀ (xs ys : List Nat),
    compareNatList xs ys = (compareNatList ys xs).swap
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | x :: xs, y :: ys => by
    unfold compareNatList
    rw [nat_compare_eq_swap x y]
    cases compare y x <;> simp [Ordering.swap, compareNatList_eq_swap xs ys]

private theorem compareNatList_isLE_trans :
    ∀ {xs ys zs : List Nat},
      (compareNatList xs ys).isLE → (compareNatList ys zs).isLE → (compareNatList xs zs).isLE
  | [], _, [], _, _ => rfl
  | [], _, _ :: _, _, _ => rfl
  | _ :: _, [], _, h₁, _ => nomatch h₁
  | _ :: _, _ :: _, [], _, h₂ => nomatch h₂
  | x :: xs, y :: ys, z :: zs, h₁, h₂ => by
    unfold compareNatList at h₁ h₂ ⊢
    cases hxy : compare x y with
    | lt =>
      cases hyz : compare y z with
      | lt =>
        rw [TransCmp.lt_trans (cmp := (compare : Nat → Nat → Ordering)) hxy hyz]; rfl
      | eq =>
        rw [TransCmp.lt_of_lt_of_eq (cmp := (compare : Nat → Nat → Ordering)) hxy hyz]; rfl
      | gt =>
        rw [hyz] at h₂; nomatch h₂
    | eq =>
      rw [hxy] at h₁
      have hxeq : x = y := nat_compare_eq_of_compare hxy
      subst hxeq
      cases hyz : compare x z with
      | lt => rfl
      | eq =>
        rw [hyz] at h₂
        exact compareNatList_isLE_trans h₁ h₂
      | gt =>
        rw [hyz] at h₂; nomatch h₂
    | gt =>
      rw [hxy] at h₁; nomatch h₁

private theorem compareNatList_eq_iff :
    ∀ {xs ys : List Nat}, compareNatList xs ys = .eq ↔ xs = ys
  | [], [] => ⟨(fun _ => rfl), (fun _ => rfl)⟩
  | [], _ :: _ => ⟨(fun h => nomatch h), (fun h => nomatch h)⟩
  | _ :: _, [] => ⟨(fun h => nomatch h), (fun h => nomatch h)⟩
  | x :: xs, y :: ys => by
    unfold compareNatList
    constructor
    · intro h
      cases hxy : compare x y with
      | lt => rw [hxy] at h; nomatch h
      | gt => rw [hxy] at h; nomatch h
      | eq =>
        rw [hxy] at h
        rw [nat_compare_eq_of_compare hxy, compareNatList_eq_iff.mp h]
    · rintro ⟨⟩
      rw [nat_compare_self x]
      exact compareNatList_eq_iff.mpr rfl

instance : Ord VTableKey where
  compare a b := compareNatList (encodeVTableKeyCode a) (encodeVTableKeyCode b)

instance : TransCmp (compare : VTableKey → VTableKey → Ordering) where
  eq_swap {a b} := compareNatList_eq_swap (encodeVTableKeyCode a) (encodeVTableKeyCode b)
  isLE_trans := compareNatList_isLE_trans

instance : LawfulEqCmp (compare : VTableKey → VTableKey → Ordering) where
  eq_of_compare h := encodeVTableKeyCode_injective (compareNatList_eq_iff.mp h)
  compare_self := compareNatList_eq_iff.mpr rfl

def mkCanonicalVTableKey (concreteTy : ProtoTy) (principal : Option PrincipalTraitRef)
    (rawAutoTraits : List AutoTrait) : VTableKey :=
  ⟨concreteTy, principal, AutoTraitSet.ofList rawAutoTraits⟩

/-- **Non-Collision Theorem (`vtableKey_principalLess_ne_principalBearing`)**: a principal-less
auto-trait vtable key (`principal = none`, e.g. `dyn Send`) **never** equals or collides in
`ExtTreeMap0` with a principal-bearing vtable key (`principal = some p`). -/
theorem vtableKey_principalLess_ne_principalBearing
    (ty₁ ty₂ : ProtoTy) (p : PrincipalTraitRef) (as₁ as₂ : List AutoTrait) :
    mkCanonicalVTableKey ty₁ none as₁ ≠ mkCanonicalVTableKey ty₂ (some p) as₂ := by
  intro heq
  injection heq with _ hpr _
  nomatch hpr

/-- **Permutation-Canonical `VTableKey` (`mkCanonicalVTableKey_perm_eq`)**: permuting or
duplicating auto-traits (`dyn Send + Sync` vs. `dyn Sync + Send`) yields the **exact same**
`VTableKey`. -/
theorem mkCanonicalVTableKey_perm_eq (ty : ProtoTy) (pr : Option PrincipalTraitRef)
    (as₁ as₂ : List AutoTrait) (hmem : ∀ x, x ∈ as₁ ↔ x ∈ as₂) :
    mkCanonicalVTableKey ty pr as₁ = mkCanonicalVTableKey ty pr as₂ := by
  unfold mkCanonicalVTableKey
  rw [AutoTraitSet.ofList_eq_of_mem_iff hmem]

inductive VTableBuildErr where
  | layoutErr (err : LayoutComputeErr)
  | unsizedConcreteType
  | allocIdErr (err : AllocIdErr)
  | vtableNotFound
  | invalidVTableTrait
  | notAMethodSlot
  deriving DecidableEq, Repr

/-- Build the canonical `VTableDescriptor` for `(concreteTy, spec)` (`lean-miri#75`). -/
def buildVTableDescriptor (maxSize : Nat) (allocId : MiriAllocId) (concreteTy : ProtoTy)
    (dropFn : DefPath) (spec : DynExistentialSpec) :
    Except VTableBuildErr VTableDescriptor := do
  let layout ← (computeTyLayout maxSize concreteTy).mapError VTableBuildErr.layoutErr
  if !layout.isSized then throw VTableBuildErr.unsizedConcreteType
  let sz := UInt64.ofNat layout.sizeBytes
  let al := UInt64.ofNat layout.alignBytes
  let methodSlots : List VTableSlot :=
    match spec.principal with
    | none => []
    | some p => p.methodNames.map VTableSlot.method
  let entries := [.dropInPlace dropFn, .size sz, .align al] ++ methodSlots
  return ⟨allocId, concreteTy, spec, dropFn, sz, al, entries⟩

/-- **`lean-miri#75` Header Preservation Theorem (`buildPrincipalLessVTable_spec`)**: on any `Sized`
`concreteTy`, building a principal-less auto-trait vtable (`dyn Send`, `dyn Send + Sync`) preserves
`dropInPlace`, `size`, `align`, and `autoTraits` with **zero** synthetic method slots! -/
theorem buildPrincipalLessVTable_spec (maxSize : Nat) (allocId : MiriAllocId)
    (concreteTy : ProtoTy) (layout : ComputedTyLayout) (dropFn : DefPath)
    (autoTraits : List AutoTrait)
    (hlay : computeTyLayout maxSize concreteTy = .ok layout)
    (hsized : layout.isSized = true) :
    buildVTableDescriptor maxSize allocId concreteTy dropFn (.principalLess autoTraits) =
      .ok {
        allocId := allocId
        concreteTy := concreteTy
        spec := .principalLess autoTraits
        dropInPlaceFn := dropFn
        sizeBytes := UInt64.ofNat layout.sizeBytes
        alignBytes := UInt64.ofNat layout.alignBytes
        entries := [
          .dropInPlace dropFn,
          .size (UInt64.ofNat layout.sizeBytes),
          .align (UInt64.ofNat layout.alignBytes)
        ]
      } := by
  unfold buildVTableDescriptor DynExistentialSpec.principalLess
  simp [hlay, hsized, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- `ExtTreeMap0`-backed global vtable registry (`byKey` deduplication + `byAlloc` reverse map). -/
structure VTableRegistry where
  byKey : ExtTreeMap0 VTableKey VTableDescriptor := ∅
  byAlloc : ExtTreeMap0 MiriAllocId VTableDescriptor := ∅

/-- Intern or reuse the canonical vtable for `(concreteTy, principal, rawAutoTraits)`. -/
def VTableRegistry.intern (reg : VTableRegistry) (w : KeyedAllocWorld) (maxSize : Nat)
    (concreteTy : ProtoTy) (dropFn : DefPath) (principal : Option PrincipalTraitRef)
    (rawAutoTraits : List AutoTrait) :
    Except VTableBuildErr (VTableRegistry × KeyedAllocWorld × VTableDescriptor) := do
  let key := mkCanonicalVTableKey concreteTy principal rawAutoTraits
  match reg.byKey.get? key with
  | some existing => return (reg, w, existing)
  | none =>
    let (wRes, idRes) := w.reserveAllocId
    let id ← idRes.mapError VTableBuildErr.allocIdErr
    let spec : DynExistentialSpec := ⟨principal, key.autoTraits⟩
    let desc ← buildVTableDescriptor maxSize id concreteTy dropFn spec
    let wGlob := wRes.registerGlobal ⟨id, .vtable, 0, desc.alignBytes, .not⟩
    let reg' : VTableRegistry := {
      byKey := reg.byKey.insert key desc
      byAlloc := reg.byAlloc.insert id desc
    }
    return (reg', wGlob, desc)

/-- **Canonical Registry Reuse Theorem (`vtableRegistry_intern_idempotent`)**: interning a vtable
under any permutation or duplication of auto-traits (`as₂` with the same membership as `as₁`) reuses
the already-interned `VTableDescriptor` without reserving a duplicate `MiriAllocId`. -/
theorem vtableRegistry_intern_idempotent
    (reg : VTableRegistry) (w : KeyedAllocWorld) (maxSize : Nat)
    (concreteTy : ProtoTy) (dropFn : DefPath) (principal : Option PrincipalTraitRef)
    (as₁ as₂ : List AutoTrait) (desc : VTableDescriptor)
    (hmem : ∀ x, x ∈ as₁ ↔ x ∈ as₂)
    (hexist : reg.byKey.get? (mkCanonicalVTableKey concreteTy principal as₁) = some desc) :
    reg.intern w maxSize concreteTy dropFn principal as₂ = .ok (reg, w, desc) := by
  unfold VTableRegistry.intern
  dsimp only
  rw [← mkCanonicalVTableKey_perm_eq concreteTy principal as₁ as₂ hmem, hexist]
  rfl

/-- Decidable subset test on normalized predicate ids (`[adv B1]`, `0` axioms). -/
def natListSubset (xs ys : List Nat) : Bool :=
  xs.all (fun x => ys.any (fun y => x == y))

theorem natListSubset_iff (xs ys : List Nat) :
    natListSubset xs ys = true ↔ ∀ x ∈ xs, x ∈ ys := by
  simp [natListSubset, List.all_eq_true, List.any_eq_true]

/-- Upstream `VTable.checkForTypeRead` (`[adv B1]`; A0 additionally demanded
`actual.autoTraits.containsAll expected.autoTraits`, a false-UB divergence): auto traits are
dropped (`filter (!·.autoTrait)`), the remaining principal predicates are sorted by stable key and
deduplicated (`sortPredicates` + `eraseDups`), and the two lists are compared pointwise — i.e.
principal-trait equality plus set equality of the normalized predicates. -/
def vtableMatchesExpectedSpec (actual expected : DynExistentialSpec) : Bool :=
  match actual.principal, expected.principal with
  | none, none => true
  | some actP, some expP =>
    decide (actP.traitDefPath = expP.traitDefPath) &&
      natListSubset actP.normalizedPredicates expP.normalizedPredicates &&
      natListSubset expP.normalizedPredicates actP.normalizedPredicates
  | _, _ => false

/-- **Auto Traits Never Affect the VTable Trait Check
(`vtableMatchesExpectedSpec_ignores_autoTraits`, `[adv B1]`)**: replacing the auto-trait sets on
either side never changes the verdict (so a `dyn Send` vtable is accepted where `dyn Sync` is
expected, and a `dyn Debug + Send` vtable where `dyn Debug` is expected), exactly as upstream
`checkForTypeRead` filters auto traits before comparing. -/
theorem vtableMatchesExpectedSpec_ignores_autoTraits (p₁ p₂ : Option PrincipalTraitRef)
    (a₁ b₁ a₂ b₂ : AutoTraitSet) :
    vtableMatchesExpectedSpec ⟨p₁, a₁⟩ ⟨p₂, a₂⟩ = vtableMatchesExpectedSpec ⟨p₁, b₁⟩ ⟨p₂, b₂⟩ := rfl

/-- **Predicate Order/Duplicates Never Affect the VTable Trait Check
(`vtableMatchesExpectedSpec_predicate_perm`, `[adv B1]`)**: permuting or duplicating the actual
vtable's normalized predicates leaves the verdict unchanged (upstream `sortPredicates` + `eraseDups`). -/
theorem vtableMatchesExpectedSpec_predicate_perm (dp₁ dp₂ : DefPath) (ps₁ ps₁' ps₂ : List Nat)
    (ms₁ ms₂ : List DefPath) (a₁ a₂ : AutoTraitSet) (hperm : ∀ x, x ∈ ps₁ ↔ x ∈ ps₁') :
    vtableMatchesExpectedSpec ⟨some ⟨dp₁, ps₁, ms₁⟩, a₁⟩ ⟨some ⟨dp₂, ps₂, ms₂⟩, a₂⟩ =
      vtableMatchesExpectedSpec ⟨some ⟨dp₁, ps₁', ms₁⟩, a₁⟩ ⟨some ⟨dp₂, ps₂, ms₂⟩, a₂⟩ := by
  have h1 : natListSubset ps₁ ps₂ = natListSubset ps₁' ps₂ := by
    apply Bool.eq_iff_iff.mpr
    rw [natListSubset_iff, natListSubset_iff]
    exact ⟨fun h x hx => h x ((hperm x).mpr hx), fun h x hx => h x ((hperm x).mp hx)⟩
  have h2 : natListSubset ps₂ ps₁ = natListSubset ps₂ ps₁' := by
    apply Bool.eq_iff_iff.mpr
    rw [natListSubset_iff, natListSubset_iff]
    exact ⟨fun h x hx => (hperm x).mp (h x hx), fun h x hx => (hperm x).mpr (h x hx)⟩
  simp only [vtableMatchesExpectedSpec, h1, h2]

def unpackDynFromRegistry (reg : VTableRegistry) (vtableAllocId : MiriAllocId)
    (expected : DynExistentialSpec) : Except VTableBuildErr VTableDescriptor := do
  let some desc := reg.byAlloc.get? vtableAllocId | throw VTableBuildErr.vtableNotFound
  if !vtableMatchesExpectedSpec desc.spec expected then
    throw VTableBuildErr.invalidVTableTrait
  return desc

def resolveVirtualMethod (desc : VTableDescriptor) (slotIdx : Nat) :
    Except VTableBuildErr DefPath :=
  match desc.entries[slotIdx]? with
  | some (.method fnDef) => .ok fnDef
  | _ => .error .notAMethodSlot

/-- Upcast a trait-object vtable `srcDesc` to a principal-less auto-trait existential `targetTraits`
(e.g. `dyn Debug + Send + Sync -> dyn Send`), verifying `srcDesc.spec.autoTraits` covers
`targetTraits` and interning the principal-less target vtable preserving `concreteTy` and `dropFn`.
*Honest scope (`[adv B1]`)*: the auto-trait coverage check models rustc's *static* unsizing-coercion
rule (`dyn Send -> dyn Sync` is a type error); it is not a runtime vtable-validity check, which
ignores auto traits (`vtableMatchesExpectedSpec_ignores_autoTraits`). -/
def upcastVTableToAutoTraits (reg : VTableRegistry) (w : KeyedAllocWorld) (maxSize : Nat)
    (srcDesc : VTableDescriptor) (targetTraits : List AutoTrait) :
    Except VTableBuildErr (VTableRegistry × KeyedAllocWorld × VTableDescriptor) := do
  let targetSet := AutoTraitSet.ofList targetTraits
  if !srcDesc.spec.autoTraits.containsAll targetSet then
    throw VTableBuildErr.invalidVTableTrait
  reg.intern w maxSize srcDesc.concreteTy srcDesc.dropInPlaceFn none targetTraits

/-- Calling any slot on a principal-less `dyn Send` vtable faults with `.notAMethodSlot`. -/
theorem principalLess_resolveVirtualMethod_fails (allocId : MiriAllocId) (ty : ProtoTy)
    (dropFn : DefPath) (sz al : UInt64) (ts : List AutoTrait) (slotIdx : Nat) :
    resolveVirtualMethod
      ⟨allocId, ty, .principalLess ts, dropFn, sz, al, [.dropInPlace dropFn, .size sz, .align al]⟩
      slotIdx = .error .notAMethodSlot := by
  unfold resolveVirtualMethod
  match slotIdx with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | _ + 3 => rfl

/-- Well-formedness predicate tying a `VTableDescriptor` to its `VTableKey`, canonical `dropFnOf`
map, and `computeTyLayout` (`[adv A1]`). -/
def VTableEntryWF (maxSize : Nat) (dropFnOf : ProtoTy → DefPath)
    (k : VTableKey) (d : VTableDescriptor) : Prop :=
  d.concreteTy = k.concreteTy ∧
  d.spec = ⟨k.principal, k.autoTraits⟩ ∧
  d.dropInPlaceFn = dropFnOf k.concreteTy ∧
  (∃ lay : ComputedTyLayout,
    computeTyLayout maxSize k.concreteTy = .ok lay ∧
    lay.isSized = true ∧
    d.sizeBytes = UInt64.ofNat lay.sizeBytes ∧
    d.alignBytes = UInt64.ofNat lay.alignBytes) ∧
  d.entries =
    [.dropInPlace d.dropInPlaceFn, .size d.sizeBytes, .align d.alignBytes] ++
      (match k.principal with
       | none => []
       | some p => p.methodNames.map VTableSlot.method)

/-- Registry key-table well-formedness (`[adv A1]`): every interned descriptor matches its key's
`concreteTy`, canonical `dropFnOf`, `computeTyLayout` `(size, align)`, and header/method entries. -/
def VTableRegistry.KeyWF (maxSize : Nat) (dropFnOf : ProtoTy → DefPath)
    (reg : VTableRegistry) : Prop :=
  ∀ (k : VTableKey) (d : VTableDescriptor),
    reg.byKey.get? k = some d → VTableEntryWF maxSize dropFnOf k d

theorem VTableRegistry.keyWF_empty (maxSize : Nat) (dropFnOf : ProtoTy → DefPath) :
    VTableRegistry.KeyWF maxSize dropFnOf {} := by
  intro k d hget
  rw [ExtTreeMap0.get?_empty] at hget
  nomatch hget

/-- **`VTableRegistry.intern` Preserves `KeyWF` (`VTableRegistry.keyWF_intern`, `[adv A1]`)**:
interning with `dropFn = dropFnOf concreteTy` preserves `KeyWF` and guarantees the returned
descriptor satisfies `VTableEntryWF` whether freshly allocated or reused from `byKey`. -/
theorem VTableRegistry.keyWF_intern
    (maxSize : Nat) (dropFnOf : ProtoTy → DefPath)
    (reg reg' : VTableRegistry) (w w' : KeyedAllocWorld)
    (concreteTy : ProtoTy) (principal : Option PrincipalTraitRef)
    (rawAutoTraits : List AutoTrait) (desc : VTableDescriptor)
    (hwf : reg.KeyWF maxSize dropFnOf)
    (hres : reg.intern w maxSize concreteTy (dropFnOf concreteTy) principal rawAutoTraits =
      .ok (reg', w', desc)) :
    reg'.KeyWF maxSize dropFnOf ∧
    VTableEntryWF maxSize dropFnOf (mkCanonicalVTableKey concreteTy principal rawAutoTraits) desc := by
  unfold VTableRegistry.intern at hres
  dsimp only at hres
  cases hex : reg.byKey.get? (mkCanonicalVTableKey concreteTy principal rawAutoTraits) with
  | some existing =>
    rw [hex] at hres
    simp only [Pure.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hres
    rcases hres with ⟨rfl, _, rfl⟩
    exact ⟨hwf, hwf _ _ hex⟩
  | none =>
    rw [hex] at hres
    cases hid : (w.reserveAllocId).2 with
    | error e =>
      simp [hid, Except.mapError, Bind.bind, Except.bind] at hres
    | ok id =>
      rw [hid] at hres
      simp only [Except.mapError, Bind.bind, Except.bind] at hres
      unfold buildVTableDescriptor at hres
      cases hlay : computeTyLayout maxSize concreteTy with
      | error le =>
        simp [hlay, Except.mapError, Bind.bind, Except.bind] at hres
      | ok lay =>
        rw [hlay] at hres
        simp only [Except.mapError, Bind.bind, Except.bind] at hres
        cases hsz : lay.isSized with
        | false =>
          simp [hsz, throw, throwThe, MonadExceptOf.throw] at hres
        | true =>
          simp only [hsz, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
            Pure.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hres
          rcases hres with ⟨hreg', _, hdesc'⟩
          subst hreg' hdesc'
          have hentry : VTableEntryWF maxSize dropFnOf
              (mkCanonicalVTableKey concreteTy principal rawAutoTraits)
              ⟨id, concreteTy, ⟨principal, (mkCanonicalVTableKey concreteTy principal rawAutoTraits).autoTraits⟩,
                dropFnOf concreteTy, UInt64.ofNat lay.sizeBytes, UInt64.ofNat lay.alignBytes,
                [.dropInPlace (dropFnOf concreteTy),
                  .size (UInt64.ofNat lay.sizeBytes),
                  .align (UInt64.ofNat lay.alignBytes)] ++
                  match principal with
                  | none => []
                  | some p => p.methodNames.map VTableSlot.method⟩ := by
            refine ⟨rfl, rfl, rfl, ⟨lay, hlay, hsz, rfl, rfl⟩, rfl⟩
          refine ⟨?_, hentry⟩
          intro k' d' hget'
          rw [ExtTreeMap0.get?_insert] at hget'
          split at hget'
          · rename_i hcmp
            have hkeq : mkCanonicalVTableKey concreteTy principal rawAutoTraits = k' :=
              LawfulEqCmp.eq_of_compare hcmp
            subst hkeq
            injection hget' with hd'
            subst hd'
            exact hentry
          · exact hwf k' d' hget'

/-- **General Upcast Drop-Glue, Size, & Align Preservation Theorem
(`upcastVTableToAutoTraits_preserves_drop_size_align`, `[adv A1]`)**: for *every* `KeyWF` registry,
*every* source descriptor `srcDesc` consistent with `dropFnOf` and `computeTyLayout`, and *every*
`targetTraits` list:
1. If `srcDesc.spec.autoTraits` does **not** cover `targetTraits`, `upcastVTableToAutoTraits`
   fails with `.error .invalidVTableTrait`.
2. Whenever `upcastVTableToAutoTraits` returns `.ok (reg', w', dstDesc)` (whether freshly allocated
   or reused from `reg.byKey`!), `reg'` remains `KeyWF` and `dstDesc` preserves `concreteTy`,
   `dropInPlaceFn`, `sizeBytes`, `alignBytes`, canonical `targetTraits`, and the exact 3-slot
   principal-less header `[.dropInPlace, .size, .align]`! -/
theorem upcastVTableToAutoTraits_preserves_drop_size_align
    (maxSize : Nat) (dropFnOf : ProtoTy → DefPath)
    (reg : VTableRegistry) (w : KeyedAllocWorld)
    (srcDesc : VTableDescriptor) (srcLay : ComputedTyLayout) (targetTraits : List AutoTrait)
    (hwf : reg.KeyWF maxSize dropFnOf)
    (hdrop : srcDesc.dropInPlaceFn = dropFnOf srcDesc.concreteTy)
    (hlay : computeTyLayout maxSize srcDesc.concreteTy = .ok srcLay)
    (hszEq : srcDesc.sizeBytes = UInt64.ofNat srcLay.sizeBytes)
    (halEq : srcDesc.alignBytes = UInt64.ofNat srcLay.alignBytes) :
    (srcDesc.spec.autoTraits.containsAll (AutoTraitSet.ofList targetTraits) = false →
      upcastVTableToAutoTraits reg w maxSize srcDesc targetTraits = .error .invalidVTableTrait) ∧
    (∀ reg' w' dstDesc,
      upcastVTableToAutoTraits reg w maxSize srcDesc targetTraits = .ok (reg', w', dstDesc) →
      reg'.KeyWF maxSize dropFnOf ∧
      dstDesc.concreteTy = srcDesc.concreteTy ∧
      dstDesc.spec = .principalLess targetTraits ∧
      dstDesc.dropInPlaceFn = srcDesc.dropInPlaceFn ∧
      dstDesc.sizeBytes = srcDesc.sizeBytes ∧
      dstDesc.alignBytes = srcDesc.alignBytes ∧
      dstDesc.entries =
        [.dropInPlace srcDesc.dropInPlaceFn, .size srcDesc.sizeBytes, .align srcDesc.alignBytes]) := by
  refine ⟨?_, ?_⟩
  · intro hnot
    unfold upcastVTableToAutoTraits
    simp [hnot, Bind.bind, Except.bind, throw, throwThe, MonadExceptOf.throw]
  · intro reg' w' dstDesc hok
    unfold upcastVTableToAutoTraits at hok
    cases hcov : srcDesc.spec.autoTraits.containsAll (AutoTraitSet.ofList targetTraits) with
    | false =>
      simp [hcov, Bind.bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at hok
    | true =>
      simp only [hcov, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hok
      rw [hdrop] at hok
      obtain ⟨hwf', hcty, hspec, hdrop', ⟨lay', hlay', _, hdSz, hdAl⟩, hentries⟩ :=
        VTableRegistry.keyWF_intern maxSize dropFnOf reg reg' w w'
          srcDesc.concreteTy none targetTraits dstDesc hwf hok
      have hlayEq : lay' = srcLay := by
        have h1 : (.ok lay' : Except LayoutComputeErr ComputedTyLayout) = .ok srcLay :=
          hlay'.symm.trans hlay
        injection h1
      subst hlayEq
      simp only [mkCanonicalVTableKey, List.append_nil] at hcty hspec hdrop' hdSz hdAl hentries
      have hdropFinal : dstDesc.dropInPlaceFn = srcDesc.dropInPlaceFn := hdrop'.trans hdrop.symm
      have hszFinal : dstDesc.sizeBytes = srcDesc.sizeBytes := hdSz.trans hszEq.symm
      have halFinal : dstDesc.alignBytes = srcDesc.alignBytes := hdAl.trans halEq.symm
      refine ⟨hwf', hcty, hspec, hdropFinal, hszFinal, halFinal, ?_⟩
      rw [hentries, hdropFinal, hszFinal, halFinal]

/-- `byAlloc` coherence (`[adv B2]`): `validateVTableHalf` resolves descriptors through
`reg.byAlloc`, which A1's `KeyWF` (a `byKey`-only invariant) left unconstrained. Every `byAlloc`
entry is keyed by its own `allocId` and is well-formed for some canonical key. -/
def VTableRegistry.AllocWF (maxSize : Nat) (dropFnOf : ProtoTy → DefPath)
    (reg : VTableRegistry) : Prop :=
  ∀ (id : MiriAllocId) (d : VTableDescriptor),
    reg.byAlloc.get? id = some d → d.allocId = id ∧ ∃ k, VTableEntryWF maxSize dropFnOf k d

theorem VTableRegistry.allocWF_empty (maxSize : Nat) (dropFnOf : ProtoTy → DefPath) :
    VTableRegistry.AllocWF maxSize dropFnOf {} := by
  intro id d hget
  rw [ExtTreeMap0.get?_empty] at hget
  nomatch hget

/-- **`VTableRegistry.intern` Preserves `AllocWF` (`VTableRegistry.allocWF_intern`, `[adv B2]`)**:
on a `KeyWF ∧ AllocWF` registry, interning with `dropFn = dropFnOf concreteTy` keeps every
`byAlloc` entry self-keyed and well-formed (fresh entries are built with `allocId := id`; reused
entries leave the registry unchanged). -/
theorem VTableRegistry.allocWF_intern
    (maxSize : Nat) (dropFnOf : ProtoTy → DefPath)
    (reg reg' : VTableRegistry) (w w' : KeyedAllocWorld)
    (concreteTy : ProtoTy) (principal : Option PrincipalTraitRef)
    (rawAutoTraits : List AutoTrait) (desc : VTableDescriptor)
    (hkwf : reg.KeyWF maxSize dropFnOf) (hawf : reg.AllocWF maxSize dropFnOf)
    (hres : reg.intern w maxSize concreteTy (dropFnOf concreteTy) principal rawAutoTraits =
      .ok (reg', w', desc)) :
    reg'.AllocWF maxSize dropFnOf := by
  have hentry := (VTableRegistry.keyWF_intern maxSize dropFnOf reg reg' w w'
    concreteTy principal rawAutoTraits desc hkwf hres).2
  unfold VTableRegistry.intern at hres
  dsimp only at hres
  cases hex : reg.byKey.get? (mkCanonicalVTableKey concreteTy principal rawAutoTraits) with
  | some existing =>
    rw [hex] at hres
    simp only [Pure.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hres
    rcases hres with ⟨rfl, _, rfl⟩
    exact hawf
  | none =>
    rw [hex] at hres
    cases hid : (w.reserveAllocId).2 with
    | error e =>
      simp [hid, Except.mapError, Bind.bind, Except.bind] at hres
    | ok id =>
      rw [hid] at hres
      simp only [Except.mapError, Bind.bind, Except.bind] at hres
      unfold buildVTableDescriptor at hres
      cases hlay : computeTyLayout maxSize concreteTy with
      | error le =>
        simp [hlay, Except.mapError, Bind.bind, Except.bind] at hres
      | ok lay =>
        rw [hlay] at hres
        simp only [Except.mapError, Bind.bind, Except.bind] at hres
        cases hsz : lay.isSized with
        | false =>
          simp [hsz, throw, throwThe, MonadExceptOf.throw] at hres
        | true =>
          simp only [hsz, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
            Pure.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hres
          rcases hres with ⟨hreg', _, hdesc'⟩
          subst hreg' hdesc'
          intro id' d' hget'
          rw [ExtTreeMap0.get?_insert] at hget'
          split at hget'
          · rename_i hcmp
            have hideq : id = id' := LawfulEqCmp.eq_of_compare hcmp
            subst hideq
            injection hget' with hd'
            subst hd'
            exact ⟨rfl, _, hentry⟩
          · exact hawf id' d' hget'

/-- Salted vtable key (`Miri.Interpreter.VTable.getPointer`, `[adv A1]`): Miri draws a global
allocation salt (`globalSalt`) per non-CTFE vtable request so two vtable expressions for the same
`(concreteTy, dynSpec)` can receive distinct `MiriAllocId`s while carrying identical layout/trait
metadata. -/
structure SaltedVTableKey where
  base : VTableKey
  salt : Nat
  deriving DecidableEq, Repr

def encodeSaltedVTableKeyCode (sk : SaltedVTableKey) : List Nat :=
  sk.salt :: encodeVTableKeyCode sk.base

theorem encodeSaltedVTableKeyCode_injective {a b : SaltedVTableKey}
    (h : encodeSaltedVTableKeyCode a = encodeSaltedVTableKeyCode b) : a = b := by
  rcases a with ⟨ba, sa⟩
  rcases b with ⟨bb, sb⟩
  dsimp [encodeSaltedVTableKeyCode] at h
  injection h with hs hb
  rw [hs, encodeVTableKeyCode_injective hb]

instance : Ord SaltedVTableKey where
  compare a b := compareNatList (encodeSaltedVTableKeyCode a) (encodeSaltedVTableKeyCode b)

instance : TransCmp (compare : SaltedVTableKey → SaltedVTableKey → Ordering) where
  eq_swap {a b} := compareNatList_eq_swap (encodeSaltedVTableKeyCode a) (encodeSaltedVTableKeyCode b)
  isLE_trans := compareNatList_isLE_trans

instance : LawfulEqCmp (compare : SaltedVTableKey → SaltedVTableKey → Ordering) where
  eq_of_compare h := encodeSaltedVTableKeyCode_injective (compareNatList_eq_iff.mp h)
  compare_self := compareNatList_eq_iff.mpr rfl

/-- Salted global vtable registry (`[adv A1]`), sharing `byAlloc` with `VTableRegistry` via
`toVTableRegistry` (`validateVTableHalf` only inspects `byAlloc` and `w.globals`, just like Miri's
`globalVTable`). -/
structure SaltedVTableRegistry where
  bySaltedKey : ExtTreeMap0 SaltedVTableKey VTableDescriptor := ∅
  byAlloc : ExtTreeMap0 MiriAllocId VTableDescriptor := ∅

def SaltedVTableRegistry.toVTableRegistry (sreg : SaltedVTableRegistry) : VTableRegistry :=
  { byKey := ∅, byAlloc := sreg.byAlloc }

def SaltedVTableRegistry.internSalted (sreg : SaltedVTableRegistry) (w : KeyedAllocWorld)
    (maxSize : Nat) (concreteTy : ProtoTy) (dropFn : DefPath)
    (principal : Option PrincipalTraitRef) (rawAutoTraits : List AutoTrait) (salt : Nat) :
    Except VTableBuildErr (SaltedVTableRegistry × KeyedAllocWorld × VTableDescriptor) := do
  let skey : SaltedVTableKey := ⟨mkCanonicalVTableKey concreteTy principal rawAutoTraits, salt⟩
  match sreg.bySaltedKey.get? skey with
  | some existing => return (sreg, w, existing)
  | none =>
    let (wRes, idRes) := w.reserveAllocId
    let id ← idRes.mapError VTableBuildErr.allocIdErr
    let spec : DynExistentialSpec := ⟨principal, skey.base.autoTraits⟩
    let desc ← buildVTableDescriptor maxSize id concreteTy dropFn spec
    let wGlob := wRes.registerGlobal ⟨id, .vtable, 0, desc.alignBytes, .not⟩
    let sreg' : SaltedVTableRegistry := {
      bySaltedKey := sreg.bySaltedKey.insert skey desc
      byAlloc := sreg.byAlloc.insert id desc
    }
    return (sreg', wGlob, desc)

/-! ### Part 3C: Wide `dyn` Pointer Validity & Null-VTable Precedence (`lean-miri#82`) -/

/-- Wide pointer scalar half (`data` or `vtable` metadata pointer in `Validity.lean` + `VTable.lean`). -/
inductive ScalarPtrHalf where
  | null
  | danglingInt (addr : UInt64)
  | maybeNull (allocId : MiriAllocId) (offsetBytes : UInt64)
  | provenanced (addr : UInt64) (allocId : MiriAllocId) (offsetBytes : UInt64)
  deriving DecidableEq, Repr

/-- Exact UB diagnostic categories for wide `dyn` safe-pointer validation (`lean-miri#82`,
`addressTooClose` added in `[adv A2]` matching `ValidityVisitor.lean:217–218`). -/
inductive WideDynValidityErr where
  | invalidVTableNull
  | invalidVTableMaybeNull
  | invalidVTableDanglingInt
  | invalidVTableNonzeroOffset
  | invalidVTableNotGlobalVTable
  | invalidVTableTrait
  | addressTooClose (sizeBytes : UInt64)
  | nullSafePointer (maybe : Bool)
  | danglingSafePointer
  | uninhabitedPointee
  | unalignedSafePointer (requiredAlign actualAddr : UInt64)
  deriving DecidableEq, Repr

def WideDynValidityErr.isVTableErr : WideDynValidityErr → Bool
  | .invalidVTableNull
  | .invalidVTableMaybeNull
  | .invalidVTableDanglingInt
  | .invalidVTableNonzeroOffset
  | .invalidVTableNotGlobalVTable
  | .invalidVTableTrait => true
  | _ => false

/-- Validate the vtable metadata pointer half of a wide `dyn` pointer (`VTable.getPtrVTableTypeRead`). -/
def validateVTableHalf (w : KeyedAllocWorld) (reg : VTableRegistry)
    (vtablePtr : ScalarPtrHalf) (expectedSpec : DynExistentialSpec) :
    Except WideDynValidityErr VTableDescriptor :=
  match vtablePtr with
  | .null => .error .invalidVTableNull
  | .maybeNull _ _ => .error .invalidVTableMaybeNull
  | .danglingInt _ => .error .invalidVTableDanglingInt
  | .provenanced _ allocId offsetBytes =>
    if offsetBytes != 0 then
      .error .invalidVTableNonzeroOffset
    else
      match w.findGlobal? allocId, reg.byAlloc.get? allocId with
      | some glob, some desc =>
        if glob.kind != .vtable then
          .error .invalidVTableNotGlobalVTable
        else if !vtableMatchesExpectedSpec desc.spec expectedSpec then
          .error .invalidVTableTrait
        else
          .ok desc
      | _, _ => .error .invalidVTableNotGlobalVTable

/-- **Auto-Trait-Only Mismatch Is Not `invalidVTableTrait`
(`validateVTableHalf_principalLess_ignores_autoTraits`, `[adv B1]`)**: a registered principal-less
vtable (e.g. `u64 as dyn Send`) validates against *every* expected principal-less spec (e.g.
`dyn Sync`, `dyn Send + Sync`). A0's validator reported `.invalidVTableTrait` here — a false UB
that upstream `checkForTypeRead` (and rustc's `check_vtable_for_type`) never raises. -/
theorem validateVTableHalf_principalLess_ignores_autoTraits
    (w : KeyedAllocWorld) (reg : VTableRegistry) (addr : UInt64) (vtId : MiriAllocId)
    (glob : GlobalAllocEntry) (desc : VTableDescriptor) (expectedTraits : AutoTraitSet)
    (hglob : w.findGlobal? vtId = some glob) (hkind : glob.kind = .vtable)
    (hdesc : reg.byAlloc.get? vtId = some desc) (hprin : desc.spec.principal = none) :
    validateVTableHalf w reg (.provenanced addr vtId 0) ⟨none, expectedTraits⟩ = .ok desc := by
  have hk : (glob.kind != .vtable) = false := by rw [hkind]; rfl
  unfold validateVTableHalf
  simp [hglob, hdesc, hk, vtableMatchesExpectedSpec, hprin]

/-- **Principal Mismatch Remains `invalidVTableTrait`
(`validateVTableHalf_principalLess_vs_principal_invalidTrait`, `[adv B1]`)**: a principal-less vtable
used where a principal-bearing trait object (`dyn Debug + …`) is expected still fails with
`.invalidVTableTrait`, whatever the auto traits (the non-auto predicate lists differ in length). -/
theorem validateVTableHalf_principalLess_vs_principal_invalidTrait
    (w : KeyedAllocWorld) (reg : VTableRegistry) (addr : UInt64) (vtId : MiriAllocId)
    (glob : GlobalAllocEntry) (desc : VTableDescriptor) (p : PrincipalTraitRef)
    (expectedTraits : AutoTraitSet)
    (hglob : w.findGlobal? vtId = some glob) (hkind : glob.kind = .vtable)
    (hdesc : reg.byAlloc.get? vtId = some desc) (hprin : desc.spec.principal = none) :
    validateVTableHalf w reg (.provenanced addr vtId 0) ⟨some p, expectedTraits⟩ =
      .error .invalidVTableTrait := by
  have hk : (glob.kind != .vtable) = false := by rw [hkind]; rfl
  unfold validateVTableHalf
  simp [hglob, hdesc, hk, vtableMatchesExpectedSpec, hprin]

/-- **Validated VTables Carry Their Concrete Type's Layout & Drop Glue
(`validateVTableHalf_sound_of_allocWF`, `[adv B2]`)**: on an `AllocWF` registry, every descriptor
that `validateVTableHalf` accepts — for *any* pointer and *any* expected spec — has
`dropInPlaceFn = dropFnOf concreteTy` and `(sizeBytes, alignBytes)` equal to the `computeTyLayout`
of its concrete type (which is `Sized`). This is the key-lookup soundness the wide-pointer validator
relies on when it reports `(size, align)` "from the vtable"; A1's `KeyWF` alone could not give it
because validation never consults `byKey`. -/
theorem validateVTableHalf_sound_of_allocWF
    (maxSize : Nat) (dropFnOf : ProtoTy → DefPath)
    (w : KeyedAllocWorld) (reg : VTableRegistry) (vtablePtr : ScalarPtrHalf)
    (expectedSpec : DynExistentialSpec) (desc : VTableDescriptor)
    (hawf : reg.AllocWF maxSize dropFnOf)
    (hv : validateVTableHalf w reg vtablePtr expectedSpec = .ok desc) :
    desc.dropInPlaceFn = dropFnOf desc.concreteTy ∧
    ∃ lay : ComputedTyLayout, computeTyLayout maxSize desc.concreteTy = .ok lay ∧
      lay.isSized = true ∧
      desc.sizeBytes = UInt64.ofNat lay.sizeBytes ∧
      desc.alignBytes = UInt64.ofNat lay.alignBytes := by
  cases vtablePtr with
  | null => simp [validateVTableHalf] at hv
  | maybeNull _ _ => simp [validateVTableHalf] at hv
  | danglingInt _ => simp [validateVTableHalf] at hv
  | provenanced addr allocId off =>
    unfold validateVTableHalf at hv
    by_cases hoff : (off != 0) = true
    · simp [hoff] at hv
    · have hoff' : (off != 0) = false := Bool.eq_false_iff.mpr hoff
      simp only [hoff', Bool.false_eq_true, ↓reduceIte] at hv
      cases hg : w.findGlobal? allocId with
      | none => simp [hg] at hv
      | some glob =>
        cases ha : reg.byAlloc.get? allocId with
        | none => simp [hg, ha] at hv
        | some d =>
          simp only [hg, ha] at hv
          by_cases hk : (glob.kind != .vtable) = true
          · simp [hk] at hv
          · have hk' : (glob.kind != .vtable) = false := Bool.eq_false_iff.mpr hk
            simp only [hk', Bool.false_eq_true, ↓reduceIte] at hv
            by_cases hm : (!vtableMatchesExpectedSpec d.spec expectedSpec) = true
            · simp [hm] at hv
            · have hm' : (!vtableMatchesExpectedSpec d.spec expectedSpec) = false :=
                Bool.eq_false_iff.mpr hm
              simp only [hm', Bool.false_eq_true, ↓reduceIte] at hv
              injection hv with hdeq
              subst hdeq
              obtain ⟨_, k, hcty, _, hdrop, ⟨lay, hlay, hsz, hszEq, halEq⟩, _⟩ := hawf allocId _ ha
              refine ⟨?_, lay, ?_, hsz, hszEq, halEq⟩
              · rw [hdrop, hcty]
              · rw [hcty]
                exact hlay

/-- Joint world + registry coherence invariant (`[adv A2]`): closes B2's cross-table & global-table
gap where `KeyWF ∧ AllocWF` neither linked `byKey` to `(byAlloc, w.globals)` (allowing `intern`'s
cached `some existing` branch to return a descriptor rejected by `validateVTableHalf`) nor linked
`byAlloc` to `w.containsId = true` (allowing a fresh `reserveAllocId` to clobber `byAlloc`). -/
def VTableWorldWF (maxSize : Nat) (dropFnOf : ProtoTy → DefPath)
    (w : KeyedAllocWorld) (reg : VTableRegistry) : Prop :=
  reg.KeyWF maxSize dropFnOf ∧
  reg.AllocWF maxSize dropFnOf ∧
  (∀ (k : VTableKey) (d : VTableDescriptor),
    reg.byKey.get? k = some d →
      reg.byAlloc.get? d.allocId = some d ∧
      w.findGlobal? d.allocId = some ⟨d.allocId, .vtable, 0, d.alignBytes, .not⟩) ∧
  (∀ (id : MiriAllocId) (d : VTableDescriptor),
    reg.byAlloc.get? id = some d → w.containsId id = true)

theorem VTableWorldWF.empty (maxSize : Nat) (dropFnOf : ProtoTy → DefPath) :
    VTableWorldWF maxSize dropFnOf KeyedAllocWorld.empty {} := by
  refine ⟨VTableRegistry.keyWF_empty _ _, VTableRegistry.allocWF_empty _ _, ?_, ?_⟩
  · intro k d hget
    rw [ExtTreeMap0.get?_empty] at hget; nomatch hget
  · intro id d hget
    rw [ExtTreeMap0.get?_empty] at hget; nomatch hget

private theorem registerGlobal_preserves_containsId (w : KeyedAllocWorld) (g : GlobalAllocEntry)
    (x : MiriAllocId) (hx : w.containsId x = true) :
    (w.registerGlobal g).containsId x = true := by
  unfold KeyedAllocWorld.containsId at hx ⊢
  unfold KeyedAllocWorld.registerGlobal
  dsimp only
  have hor := Bool.or_eq_true_iff.mp hx
  rcases hor with h3 | hg
  · have hor2 := Bool.or_eq_true_iff.mp h3
    rcases hor2 with h2 | hd
    · have hor1 := Bool.or_eq_true_iff.mp h2
      rcases hor1 with hi | hl
      · have hi' : (w.issuedIds.insert g.allocId ()).contains x = true := by
          rw [ExtTreeMap0.contains_eq_isSome_get?, ExtTreeMap0.get?_insert]
          split
          · rfl
          · rw [← ExtTreeMap0.contains_eq_isSome_get?]; exact hi
        simp [hi']
      · simp [hl]
    · simp [hd]
  · have hg' : (w.globals.insert g.allocId g).contains x = true := by
      rw [ExtTreeMap0.contains_eq_isSome_get?, ExtTreeMap0.get?_insert]
      split
      · rfl
      · rw [← ExtTreeMap0.contains_eq_isSome_get?]; exact hg
    simp [hg']

private theorem reserveAllocId_fresh_not_contains
    (w wRes : KeyedAllocWorld) (id : MiriAllocId)
    (hres : w.reserveAllocId = (wRes, .ok id)) :
    w.containsId id = false ∧
    wRes.globals = w.globals ∧
    (∀ x, w.containsId x = true → wRes.containsId x = true) ∧
    wRes.containsId id = true := by
  unfold KeyedAllocWorld.reserveAllocId at hres
  split at hres
  · nomatch hres
  · cases hof : MiriAllocId.ofUInt64 w.nextAllocId with
    | none => simp [hof] at hres
    | some cand =>
      rw [hof] at hres
      dsimp only at hres
      cases hc : w.containsId cand with
      | true => simp [hc] at hres
      | false =>
        simp only [hc, Bool.false_eq_true, ↓reduceIte, Prod.mk.injEq, Except.ok.injEq] at hres
        rcases hres with ⟨hwRes, rfl⟩
        subst hwRes
        refine ⟨hc, rfl, ?_, ?_⟩
        · intro x hx
          unfold KeyedAllocWorld.containsId at hx ⊢
          dsimp only
          have hor := Bool.or_eq_true_iff.mp hx
          rcases hor with h3 | hg
          · have hor2 := Bool.or_eq_true_iff.mp h3
            rcases hor2 with h2 | hd
            · have hor1 := Bool.or_eq_true_iff.mp h2
              rcases hor1 with hi | hl
              · have hi' : (w.issuedIds.insert cand ()).contains x = true := by
                  rw [ExtTreeMap0.contains_eq_isSome_get?, ExtTreeMap0.get?_insert]
                  split
                  · rfl
                  · rw [← ExtTreeMap0.contains_eq_isSome_get?]; exact hi
                simp [hi']
              · simp [hl]
            · simp [hd]
          · simp [hg]
        · unfold KeyedAllocWorld.containsId
          dsimp only
          rw [ExtTreeMap0.contains_eq_isSome_get?, ExtTreeMap0.get?_insert_self]
          rfl

/-- **Full `intern` → `validateVTableHalf` Round-Trip Soundness (`VTableWorldWF.intern_roundTrip`,
`[adv A2]`)**: on any `VTableWorldWF` world+registry pair, interning `(concreteTy, principal,
rawAutoTraits)` preserves `VTableWorldWF` (without clobbering existing `byAlloc` or `w.globals`
entries) AND guarantees `validateVTableHalf` succeeds with `.ok desc` on **both** fresh allocations
and cached `byKey` hits! -/
theorem VTableWorldWF.intern_roundTrip
    (maxSize : Nat) (dropFnOf : ProtoTy → DefPath)
    (w w' : KeyedAllocWorld) (reg reg' : VTableRegistry)
    (concreteTy : ProtoTy) (principal : Option PrincipalTraitRef)
    (rawAutoTraits : List AutoTrait) (desc : VTableDescriptor) (addr : UInt64)
    (hwf : VTableWorldWF maxSize dropFnOf w reg)
    (hres : reg.intern w maxSize concreteTy (dropFnOf concreteTy) principal rawAutoTraits =
      .ok (reg', w', desc)) :
    VTableWorldWF maxSize dropFnOf w' reg' ∧
    validateVTableHalf w' reg' (.provenanced addr desc.allocId 0)
      ⟨principal, AutoTraitSet.ofList rawAutoTraits⟩ = .ok desc := by
  obtain ⟨hkwf, hawf, hcoh, hcont⟩ := hwf
  have ⟨hkwf', hentry⟩ := VTableRegistry.keyWF_intern maxSize dropFnOf reg reg' w w'
    concreteTy principal rawAutoTraits desc hkwf hres
  have hawf' := VTableRegistry.allocWF_intern maxSize dropFnOf reg reg' w w'
    concreteTy principal rawAutoTraits desc hkwf hawf hres
  have hselfMatch : vtableMatchesExpectedSpec ⟨principal, AutoTraitSet.ofList rawAutoTraits⟩
      ⟨principal, AutoTraitSet.ofList rawAutoTraits⟩ = true := by
    unfold vtableMatchesExpectedSpec
    cases principal with
    | none => rfl
    | some p =>
      have hdp : decide (p.traitDefPath = p.traitDefPath) = true := decide_eq_true rfl
      have hsub : natListSubset p.normalizedPredicates p.normalizedPredicates = true :=
        (natListSubset_iff _ _).mpr (fun _ hx => hx)
      dsimp only
      rw [hdp, hsub]
      rfl
  have hcoh' :
      (∀ (k : VTableKey) (d : VTableDescriptor),
        reg'.byKey.get? k = some d →
          reg'.byAlloc.get? d.allocId = some d ∧
          w'.findGlobal? d.allocId = some ⟨d.allocId, .vtable, 0, d.alignBytes, .not⟩) ∧
      (∀ (id : MiriAllocId) (d : VTableDescriptor),
        reg'.byAlloc.get? id = some d → w'.containsId id = true) ∧
      reg'.byKey.get? (mkCanonicalVTableKey concreteTy principal rawAutoTraits) = some desc := by
    unfold VTableRegistry.intern at hres
    dsimp only at hres
    cases hex : reg.byKey.get? (mkCanonicalVTableKey concreteTy principal rawAutoTraits) with
    | some existing =>
      rw [hex] at hres
      simp only [Pure.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hres
      rcases hres with ⟨rfl, rfl, rfl⟩
      exact ⟨hcoh, hcont, hex⟩
    | none =>
      rw [hex] at hres
      cases hresPair : w.reserveAllocId with
      | mk wRes idRes =>
        rw [hresPair] at hres
        cases idRes with
        | error e => simp [Except.mapError, Bind.bind, Except.bind] at hres
        | ok id =>
          obtain ⟨hnotContId, hglobEq, hmonoCont, hcontNew⟩ :=
            reserveAllocId_fresh_not_contains w wRes id hresPair
          simp only [Except.mapError, Bind.bind, Except.bind] at hres
          cases hb : buildVTableDescriptor maxSize id concreteTy (dropFnOf concreteTy)
              ⟨principal, (mkCanonicalVTableKey concreteTy principal rawAutoTraits).autoTraits⟩ with
          | error _ => rw [hb] at hres; nomatch hres
          | ok built =>
            rw [hb] at hres
            simp only [Pure.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hres
            rcases hres with ⟨hreg', hw', hdesc⟩
            subst hreg' hw' hdesc
            have hbuiltId : built.allocId = id :=
              (hawf' id built (ExtTreeMap0.get?_insert_self _ _ _)).1
            refine ⟨?_, ?_, ?_⟩
            · intro k' d' hgetK
              dsimp only at hgetK ⊢
              rw [ExtTreeMap0.get?_insert] at hgetK
              split at hgetK
              · injection hgetK with hd'; subst hd'
                rw [hbuiltId]
                refine ⟨ExtTreeMap0.get?_insert_self _ _ _, ?_⟩
                unfold KeyedAllocWorld.registerGlobal KeyedAllocWorld.findGlobal?
                dsimp only
                exact ExtTreeMap0.get?_insert_self _ _ _
              · obtain ⟨haOld, hgOld⟩ := hcoh k' d' hgetK
                have hcOld : w.containsId d'.allocId = true := hcont d'.allocId d' haOld
                have hneId : id ≠ d'.allocId := by
                  intro heq; subst heq; rw [hnotContId] at hcOld; nomatch hcOld
                refine ⟨?_, ?_⟩
                · rw [ExtTreeMap0.get?_insert_ne _ hneId]
                  exact haOld
                · unfold KeyedAllocWorld.registerGlobal KeyedAllocWorld.findGlobal?
                  dsimp only
                  rw [ExtTreeMap0.get?_insert_ne _ hneId, hglobEq]
                  exact hgOld
            · intro id' d' hgetA
              dsimp only at hgetA
              rw [ExtTreeMap0.get?_insert] at hgetA
              split at hgetA
              · rename_i hcmp
                have hideq : id = id' := LawfulEqCmp.eq_of_compare hcmp
                subst hideq
                exact registerGlobal_preserves_containsId wRes _ id hcontNew
              · exact registerGlobal_preserves_containsId wRes _ id'
                  (hmonoCont id' (hcont id' d' hgetA))
            · dsimp only
              exact ExtTreeMap0.get?_insert_self _ _ _
  obtain ⟨hcohMap, hcontMap, hkeyDesc⟩ := hcoh'
  obtain ⟨haDesc, hgDesc⟩ := hcohMap _ _ hkeyDesc
  have hspecEq : desc.spec = ⟨principal, AutoTraitSet.ofList rawAutoTraits⟩ := hentry.2.1
  refine ⟨⟨hkwf', hawf', hcohMap, hcontMap⟩, ?_⟩
  unfold validateVTableHalf
  simp [haDesc, hgDesc, hspecEq, hselfMatch]

/-- Joint world + salted-registry coherence invariant (`[adv A2]`). -/
def SaltedVTableWorldWF (maxSize : Nat) (dropFnOf : ProtoTy → DefPath)
    (w : KeyedAllocWorld) (sreg : SaltedVTableRegistry) : Prop :=
  (∀ (sk : SaltedVTableKey) (d : VTableDescriptor),
    sreg.bySaltedKey.get? sk = some d →
      VTableEntryWF maxSize dropFnOf sk.base d ∧
      sreg.byAlloc.get? d.allocId = some d ∧
      w.findGlobal? d.allocId = some ⟨d.allocId, .vtable, 0, d.alignBytes, .not⟩) ∧
  sreg.toVTableRegistry.AllocWF maxSize dropFnOf ∧
  (∀ (id : MiriAllocId) (d : VTableDescriptor),
    sreg.byAlloc.get? id = some d → w.containsId id = true)

theorem SaltedVTableWorldWF.empty (maxSize : Nat) (dropFnOf : ProtoTy → DefPath) :
    SaltedVTableWorldWF maxSize dropFnOf KeyedAllocWorld.empty {} := by
  refine ⟨?_, VTableRegistry.allocWF_empty _ _, ?_⟩
  · intro sk d hget; rw [ExtTreeMap0.get?_empty] at hget; nomatch hget
  · intro id d hget; rw [ExtTreeMap0.get?_empty] at hget; nomatch hget

/-- **Salted `internSalted` `AllocWF` Preservation & Round-Trip Soundness
(`SaltedVTableWorldWF.internSalted_roundTrip`, `[adv A2]`)**: discharges B2's salted-registry gap by
proving `SaltedVTableRegistry.internSalted` preserves `SaltedVTableWorldWF`, preserves
`sreg'.toVTableRegistry.AllocWF`, AND guarantees `validateVTableHalf = .ok desc` on both fresh and
cached-salt paths! -/
theorem SaltedVTableWorldWF.internSalted_roundTrip
    (maxSize : Nat) (dropFnOf : ProtoTy → DefPath)
    (w w' : KeyedAllocWorld) (sreg sreg' : SaltedVTableRegistry)
    (concreteTy : ProtoTy) (principal : Option PrincipalTraitRef)
    (rawAutoTraits : List AutoTrait) (salt : Nat) (desc : VTableDescriptor) (addr : UInt64)
    (hwf : SaltedVTableWorldWF maxSize dropFnOf w sreg)
    (hres : sreg.internSalted w maxSize concreteTy (dropFnOf concreteTy) principal rawAutoTraits salt =
      .ok (sreg', w', desc)) :
    SaltedVTableWorldWF maxSize dropFnOf w' sreg' ∧
    sreg'.toVTableRegistry.AllocWF maxSize dropFnOf ∧
    validateVTableHalf w' sreg'.toVTableRegistry (.provenanced addr desc.allocId 0)
      ⟨principal, AutoTraitSet.ofList rawAutoTraits⟩ = .ok desc := by
  obtain ⟨hsk, hawf, hcont⟩ := hwf
  have hselfMatch : vtableMatchesExpectedSpec ⟨principal, AutoTraitSet.ofList rawAutoTraits⟩
      ⟨principal, AutoTraitSet.ofList rawAutoTraits⟩ = true := by
    unfold vtableMatchesExpectedSpec
    cases principal with
    | none => rfl
    | some p =>
      have hdp : decide (p.traitDefPath = p.traitDefPath) = true := decide_eq_true rfl
      have hsub : natListSubset p.normalizedPredicates p.normalizedPredicates = true :=
        (natListSubset_iff _ _).mpr (fun _ hx => hx)
      dsimp only
      rw [hdp, hsub]
      rfl
  unfold SaltedVTableRegistry.internSalted at hres
  dsimp only at hres
  let skey : SaltedVTableKey := ⟨mkCanonicalVTableKey concreteTy principal rawAutoTraits, salt⟩
  cases hex : sreg.bySaltedKey.get? skey with
  | some existing =>
    rw [hex] at hres
    simp only [Pure.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hres
    rcases hres with ⟨rfl, rfl, hdescEq⟩
    subst hdescEq
    obtain ⟨hentry, haEx, hgEx⟩ := hsk skey existing hex
    have hspecEq : existing.spec = ⟨principal, AutoTraitSet.ofList rawAutoTraits⟩ := hentry.2.1
    refine ⟨⟨hsk, hawf, hcont⟩, hawf, ?_⟩
    unfold validateVTableHalf SaltedVTableRegistry.toVTableRegistry
    simp [haEx, hgEx, hspecEq, hselfMatch]
  | none =>
    rw [hex] at hres
    cases hresPair : w.reserveAllocId with
    | mk wRes idRes =>
      rw [hresPair] at hres
      cases idRes with
      | error _ => simp [Except.mapError, Bind.bind, Except.bind] at hres
      | ok id =>
        obtain ⟨hnotContId, hglobEq, hmonoCont, hcontNew⟩ :=
          reserveAllocId_fresh_not_contains w wRes id hresPair
        simp only [Except.mapError, Bind.bind, Except.bind] at hres
        unfold buildVTableDescriptor at hres
        cases hlay : computeTyLayout maxSize concreteTy with
        | error _ => simp [hlay, Except.mapError, Bind.bind, Except.bind] at hres
        | ok lay =>
          rw [hlay] at hres
          simp only [Except.mapError, Bind.bind, Except.bind] at hres
          cases hsz : lay.isSized with
          | false => simp [hsz, throw, throwThe, MonadExceptOf.throw] at hres
          | true =>
            simp only [hsz, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
              Pure.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hres
            rcases hres with ⟨hsreg', hw', hdesc⟩
            subst hsreg' hw' hdesc
            let newDesc : VTableDescriptor :=
              ⟨id, concreteTy, ⟨principal, skey.base.autoTraits⟩,
                dropFnOf concreteTy, UInt64.ofNat lay.sizeBytes, UInt64.ofNat lay.alignBytes,
                [.dropInPlace (dropFnOf concreteTy),
                  .size (UInt64.ofNat lay.sizeBytes),
                  .align (UInt64.ofNat lay.alignBytes)] ++
                  match principal with
                  | none => []
                  | some p => p.methodNames.map VTableSlot.method⟩
            let gNew : GlobalAllocEntry := ⟨id, .vtable, 0, UInt64.ofNat lay.alignBytes, .not⟩
            have hentry : VTableEntryWF maxSize dropFnOf skey.base newDesc :=
              ⟨rfl, rfl, rfl, ⟨lay, hlay, hsz, rfl, rfl⟩, rfl⟩
            have hawf' : ({ bySaltedKey := sreg.bySaltedKey.insert skey newDesc
                            byAlloc := sreg.byAlloc.insert id newDesc } :
                SaltedVTableRegistry).toVTableRegistry.AllocWF maxSize dropFnOf := by
              intro id' d' hgetA
              unfold SaltedVTableRegistry.toVTableRegistry at hgetA
              dsimp only at hgetA
              rw [ExtTreeMap0.get?_insert] at hgetA
              split at hgetA
              · rename_i hcmp
                have hideq : id = id' := LawfulEqCmp.eq_of_compare hcmp
                subst hideq
                injection hgetA with hd'; subst hd'
                exact ⟨rfl, skey.base, hentry⟩
              · exact hawf id' d' hgetA
            have hsk' : ∀ (sk' : SaltedVTableKey) (d' : VTableDescriptor),
                (sreg.bySaltedKey.insert skey newDesc).get? sk' = some d' →
                  VTableEntryWF maxSize dropFnOf sk'.base d' ∧
                  (sreg.byAlloc.insert id newDesc).get? d'.allocId = some d' ∧
                  (wRes.registerGlobal gNew).findGlobal? d'.allocId =
                    some ⟨d'.allocId, .vtable, 0, d'.alignBytes, .not⟩ := by
              intro sk' d' hgetK
              rw [ExtTreeMap0.get?_insert] at hgetK
              split at hgetK
              · rename_i hcmp
                have hskeq : skey = sk' := LawfulEqCmp.eq_of_compare hcmp
                subst hskeq
                injection hgetK with hd'; subst hd'
                refine ⟨hentry, ExtTreeMap0.get?_insert_self _ _ _, ?_⟩
                unfold KeyedAllocWorld.registerGlobal KeyedAllocWorld.findGlobal?
                dsimp only
                exact ExtTreeMap0.get?_insert_self _ _ _
              · obtain ⟨heOld, haOld, hgOld⟩ := hsk sk' d' hgetK
                have hcOld : w.containsId d'.allocId = true := hcont d'.allocId d' haOld
                have hneId : id ≠ d'.allocId := by
                  intro heq; subst heq; rw [hnotContId] at hcOld; nomatch hcOld
                refine ⟨heOld, (ExtTreeMap0.get?_insert_ne sreg.byAlloc hneId newDesc).trans haOld, ?_⟩
                unfold KeyedAllocWorld.registerGlobal KeyedAllocWorld.findGlobal?
                dsimp only
                rw [ExtTreeMap0.get?_insert_ne _ hneId, hglobEq]
                exact hgOld
            have hcont' : ∀ (id' : MiriAllocId) (d' : VTableDescriptor),
                (sreg.byAlloc.insert id newDesc).get? id' = some d' →
                  (wRes.registerGlobal gNew).containsId id' = true := by
              intro id' d' hgetA
              rw [ExtTreeMap0.get?_insert] at hgetA
              split at hgetA
              · rename_i hcmp
                have hideq : id = id' := LawfulEqCmp.eq_of_compare hcmp
                subst hideq
                exact registerGlobal_preserves_containsId wRes gNew id hcontNew
              · exact registerGlobal_preserves_containsId wRes gNew id'
                  (hmonoCont id' (hcont id' d' hgetA))
            refine ⟨⟨hsk', hawf', hcont'⟩, hawf', ?_⟩
            change validateVTableHalf (wRes.registerGlobal gNew)
              ({ bySaltedKey := sreg.bySaltedKey.insert skey newDesc
                 byAlloc := sreg.byAlloc.insert id newDesc } : SaltedVTableRegistry).toVTableRegistry
              (.provenanced addr newDesc.allocId 0)
              ⟨principal, AutoTraitSet.ofList rawAutoTraits⟩ = .ok newDesc
            have haSelf := ExtTreeMap0.get?_insert_self sreg.byAlloc id newDesc
            have hgSelf : (wRes.registerGlobal gNew).findGlobal? id = some gNew :=
              ExtTreeMap0.get?_insert_self _ _ _
            have hspecEqNew : newDesc.spec = ⟨principal, AutoTraitSet.ofList rawAutoTraits⟩ := rfl
            have hidEqNew : newDesc.allocId = id := rfl
            unfold validateVTableHalf SaltedVTableRegistry.toVTableRegistry
            dsimp only
            rw [hidEqNew, hgSelf, haSelf]
            dsimp only
            rw [hspecEqNew]
            simp [gNew, hselfMatch]

/-- **`lean-miri#82` Source-Ordered Wide `dyn` Safe-Pointer Validator (`validateWideDynSafePtr`,
`[adv A2]` `mayDangle` & inhabitedness ordering fixes)**:
1. Validates `vtablePtr` metadata **FIRST** (`validateVTableHalf`), extracting `(sizeBytes, alignBytes)`
   and concrete pointee type from the validated vtable.
2. When `!mayDangle`, checks `dataPtr` access/liveness (`[adv A1]`: `.maybeNull` undergoes the
   non-ZST `getAllocInfo` check *before* `scalarMayBeNull`, and `.danglingInt 0` classifies as
   `.nullSafePointer false`, `ValidityVisitor.lean:131–133, 205–208`).
3. When `mayDangle = true`, enforces the integer `.danglingInt addr` address-space end guard
   `addr.toNat + sz.toNat ≥ usizeMax64` (`ValidityVisitor.lean:215–218`, `.addressTooClose sz`,
   `[adv A2]`).
4. Checks non-nullness (`scalarMayBeNull`, line 225) and alignment (`checkPointerAlignResult`,
   lines 227–228) **before** `!mayDangle` recursive `unpackDynTrait` concrete-pointee inhabitedness
   (lines 230 & 412–418; at line 226 `place.layout.ty` is `dyn Trait`, which is inhabited, so
   `mayDangle = true` e.g. `ManuallyDrop<Box<dyn Send>>` from `!` does NOT raise
   `.uninhabitedPointee`, and under `mayDangle = false` `.unalignedSafePointer` precedes
   `.uninhabitedPointee`, `[adv A2]`). -/
def validateWideDynSafePtr (w : KeyedAllocWorld) (reg : VTableRegistry) (maxSize : Nat)
    (expectedSpec : DynExistentialSpec) (mayDangle : Bool)
    (dataPtr vtablePtr : ScalarPtrHalf) :
    Except WideDynValidityErr (ProtoTy × UInt64 × UInt64) := do
  let desc ← validateVTableHalf w reg vtablePtr expectedSpec
  let sz := desc.sizeBytes
  let al := desc.alignBytes
  if !mayDangle then
    match dataPtr with
    | .null => throw (WideDynValidityErr.nullSafePointer false)
    | .danglingInt addr =>
      if sz > 0 then
        if addr == 0 then throw (WideDynValidityErr.nullSafePointer false)
        else throw WideDynValidityErr.danglingSafePointer
      else pure ()
    | .maybeNull dataId dataOff | .provenanced _ dataId dataOff =>
      if sz > 0 then
        match w.getAllocInfo dataId with
        | .ok info =>
          if info.kind != .liveData || dataOff.toNat + sz.toNat > info.sizeBytes.toNat then
            throw WideDynValidityErr.danglingSafePointer
        | .error _ => throw WideDynValidityErr.danglingSafePointer
      else pure ()
  else
    match dataPtr with
    | .danglingInt addr =>
      if decide (addr.toNat + sz.toNat ≥ usizeMax64) then
        throw (WideDynValidityErr.addressTooClose sz)
    | _ => pure ()
  match dataPtr with
  | .null => throw (WideDynValidityErr.nullSafePointer false)
  | .maybeNull _ _ => throw (WideDynValidityErr.nullSafePointer true)
  | .danglingInt addr | .provenanced addr _ _ =>
    if addr == 0 then throw (WideDynValidityErr.nullSafePointer false)
    if al > 0 && (addr % al != 0) then
      throw (WideDynValidityErr.unalignedSafePointer al addr)
    if !mayDangle then
      let inhabited :=
        match computeTyLayout maxSize desc.concreteTy with
        | .ok l => l.isInhabited
        | .error _ => false
      if !inhabited then throw WideDynValidityErr.uninhabitedPointee
    return (desc.concreteTy, sz, al)

/-- Pre-`lean-miri#82` data-first validator (buggy precedence): checks `dataPtr` nullness before
validating `vtablePtr`, reporting `nullSafePointer` instead of `invalidVTableNull` on `(null, null)`. -/
def validateWideDynLegacyDataFirst (w : KeyedAllocWorld) (reg : VTableRegistry) (maxSize : Nat)
    (expectedSpec : DynExistentialSpec) (mayDangle : Bool)
    (dataPtr vtablePtr : ScalarPtrHalf) :
    Except WideDynValidityErr (ProtoTy × UInt64 × UInt64) := do
  match dataPtr with
  | .null => throw (WideDynValidityErr.nullSafePointer false)
  | .maybeNull _ _ => throw (WideDynValidityErr.nullSafePointer true)
  | _ => validateWideDynSafePtr w reg maxSize expectedSpec mayDangle dataPtr vtablePtr

/-- **General Precedence Theorem (`wideDyn_invalidVTable_precedes_all_data_ub`, `lean-miri#82`)**:
whenever `validateVTableHalf` fails with `vErr`, `validateWideDynSafePtr` deterministically returns
`.error vErr` **regardless** of `dataPtr` (even when `dataPtr` is simultaneously `.null`,
`.maybeNull`, `.danglingInt`, dead, out-of-bounds, or unaligned)! -/
theorem wideDyn_invalidVTable_precedes_all_data_ub
    (w : KeyedAllocWorld) (reg : VTableRegistry) (maxSize : Nat)
    (expectedSpec : DynExistentialSpec) (mayDangle : Bool)
    (dataPtr vtablePtr : ScalarPtrHalf) (vErr : WideDynValidityErr)
    (hv : validateVTableHalf w reg vtablePtr expectedSpec = .error vErr) :
    validateWideDynSafePtr w reg maxSize expectedSpec mayDangle dataPtr vtablePtr = .error vErr := by
  unfold validateWideDynSafePtr
  simp [hv, Bind.bind, Except.bind]

/-- **Null-VTable vs. Null-Data Double-Null Separation (`wideDyn_doubleNull_separation`)**: on
`(dataPtr = .null, vtablePtr = .null)`, `validateWideDynSafePtr` reports `.invalidVTableNull`,
whereas `validateWideDynLegacyDataFirst` reports `.nullSafePointer false`! -/
theorem wideDyn_doubleNull_separation
    (w : KeyedAllocWorld) (reg : VTableRegistry) (maxSize : Nat)
    (expectedSpec : DynExistentialSpec) (mayDangle : Bool) :
    validateWideDynSafePtr w reg maxSize expectedSpec mayDangle .null .null =
      .error .invalidVTableNull ∧
    validateWideDynLegacyDataFirst w reg maxSize expectedSpec mayDangle .null .null =
      .error (.nullSafePointer false) := by
  exact ⟨rfl, rfl⟩

/-- **Valid-VTable Preservation Theorem (`wideDyn_validVTable_nullData_reports_nullSafePointer`)**:
whenever `vtablePtr` resolves to a valid matching `VTableDescriptor`, a null `dataPtr` still
deterministically faults with `.error (.nullSafePointer false)` under both `mayDangle = false` and
`mayDangle = true` (even for zero-sized `sizeBytes = 0` concrete types!). -/
theorem wideDyn_validVTable_nullData_reports_nullSafePointer
    (w : KeyedAllocWorld) (reg : VTableRegistry) (maxSize : Nat)
    (expectedSpec : DynExistentialSpec) (mayDangle : Bool)
    (vtablePtr : ScalarPtrHalf) (desc : VTableDescriptor)
    (hv : validateVTableHalf w reg vtablePtr expectedSpec = .ok desc) :
    validateWideDynSafePtr w reg maxSize expectedSpec mayDangle .null vtablePtr =
      .error (.nullSafePointer false) := by
  unfold validateWideDynSafePtr
  cases mayDangle <;> simp [hv, Bind.bind, Except.bind, throw, throwThe, MonadExceptOf.throw]

/-- **Valid-VTable Dangling & Alignment Preservation (`wideDyn_validVTable_dangling_and_unaligned`,
`[adv A2]` refined)**: when `vtablePtr` is valid (`validateVTableHalf = .ok desc`), non-ZST dangling
data pointers fault with `.danglingSafePointer` when `mayDangle = false`, and in-address-space
(`addr.toNat + desc.sizeBytes.toNat < usizeMax64`) non-null unaligned data addresses fault with
`.unalignedSafePointer desc.alignBytes addr` when `mayDangle = true` regardless of concrete
inhabitedness! -/
theorem wideDyn_validVTable_dangling_and_unaligned
    (w : KeyedAllocWorld) (reg : VTableRegistry) (maxSize : Nat)
    (expectedSpec : DynExistentialSpec) (vtablePtr : ScalarPtrHalf)
    (desc : VTableDescriptor) (addr : UInt64)
    (hv : validateVTableHalf w reg vtablePtr expectedSpec = .ok desc)
    (hsz : desc.sizeBytes > 0)
    (hnz : addr ≠ 0)
    (hnotClose : addr.toNat + desc.sizeBytes.toNat < usizeMax64)
    (hal_pos : desc.alignBytes > 0)
    (hunalign : addr % desc.alignBytes ≠ 0) :
    validateWideDynSafePtr w reg maxSize expectedSpec false (.danglingInt addr) vtablePtr =
      .error .danglingSafePointer ∧
    validateWideDynSafePtr w reg maxSize expectedSpec true (.danglingInt addr) vtablePtr =
      .error (.unalignedSafePointer desc.alignBytes addr) := by
  have haddr0 : (addr == 0) = false := beq_false_of_ne hnz
  have hclose : decide (addr.toNat + desc.sizeBytes.toNat ≥ usizeMax64) = false :=
    decide_eq_false (by omega)
  have hmod : (addr % desc.alignBytes != 0) = true := bne_iff_ne.mpr hunalign
  refine ⟨?_, ?_⟩
  · unfold validateWideDynSafePtr
    simp [hv, hsz, haddr0, Bind.bind, Except.bind, throw, throwThe, MonadExceptOf.throw]
  · unfold validateWideDynSafePtr
    simp [hv, hclose, haddr0, hal_pos, hmod,
      Bind.bind, Except.bind, throw, throwThe, MonadExceptOf.throw]

/-- **`maybeNull` Access-Before-Null Precedence (`wideDyn_validVTable_maybeNull_dangling_precedes_null`,
`[adv A1]`)**: matching `Miri.Interpreter.ValidityVisitor.checkSafe` lines 205–225, when
`vtablePtr` is valid, `desc.sizeBytes > 0`, and `dataId` is unavailable or dead (`w.getAllocInfo
dataId = .error _`), `(.maybeNull dataId dataOff)` faults with `.danglingSafePointer` under
`mayDangle = false`, whereas under `mayDangle = true` (which skips `checkPointerAccess`) it reaches
`scalarMayBeNull` and reports `.nullSafePointer true`! -/
theorem wideDyn_validVTable_maybeNull_dangling_precedes_null
    (w : KeyedAllocWorld) (reg : VTableRegistry) (maxSize : Nat)
    (expectedSpec : DynExistentialSpec) (vtablePtr : ScalarPtrHalf)
    (desc : VTableDescriptor) (dataId : MiriAllocId) (dataOff : UInt64)
    (err : AllocLookupErr)
    (hv : validateVTableHalf w reg vtablePtr expectedSpec = .ok desc)
    (hsz : desc.sizeBytes > 0)
    (hdead : w.getAllocInfo dataId = .error err) :
    validateWideDynSafePtr w reg maxSize expectedSpec false (.maybeNull dataId dataOff) vtablePtr =
      .error .danglingSafePointer ∧
    validateWideDynSafePtr w reg maxSize expectedSpec true (.maybeNull dataId dataOff) vtablePtr =
      .error (.nullSafePointer true) := by
  refine ⟨?_, ?_⟩
  · unfold validateWideDynSafePtr
    simp [hv, hsz, hdead, Bind.bind, Except.bind, throw, throwThe, MonadExceptOf.throw]
  · unfold validateWideDynSafePtr
    simp [hv, Bind.bind, Except.bind, throw, throwThe, MonadExceptOf.throw]

/-- **Dangling-Integer Zero Address Classifies as Null (`wideDyn_validVTable_danglingIntZero_reports_null`,
`[adv A1]`, `hszMax` guard `[adv A2]`)**: matching `ValidityVisitor.lean` lines 132 & 217–225, when
`desc.sizeBytes.toNat < usizeMax64` (true of every representable layout since `isize::MAX <
usize::MAX`), `.danglingInt 0` deterministically reports `.nullSafePointer false` under both
`mayDangle = false` and `mayDangle = true`! -/
theorem wideDyn_validVTable_danglingIntZero_reports_null
    (w : KeyedAllocWorld) (reg : VTableRegistry) (maxSize : Nat)
    (expectedSpec : DynExistentialSpec) (mayDangle : Bool)
    (vtablePtr : ScalarPtrHalf) (desc : VTableDescriptor)
    (hv : validateVTableHalf w reg vtablePtr expectedSpec = .ok desc)
    (hszMax : desc.sizeBytes.toNat < usizeMax64) :
    validateWideDynSafePtr w reg maxSize expectedSpec mayDangle (.danglingInt 0) vtablePtr =
      .error (.nullSafePointer false) := by
  have h0 : ((0 : UInt64) == 0) = true := rfl
  have hclose0 : decide ((0 : UInt64).toNat + desc.sizeBytes.toNat ≥ usizeMax64) = false := by
    have hz : (0 : UInt64).toNat = 0 := rfl
    rw [hz]
    exact decide_eq_false (by omega)
  unfold validateWideDynSafePtr
  cases mayDangle
  · if hsz : desc.sizeBytes > 0 then
      simp only [hv, hsz, h0, Bool.not_false, ↓reduceIte, Bind.bind, Except.bind,
        throw, throwThe, MonadExceptOf.throw]
    else
      simp only [hv, hsz, h0, Bool.not_false, ↓reduceIte,
        Bind.bind, Except.bind, throw, throwThe, MonadExceptOf.throw]
  · simp only [hv, hclose0, h0, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      Bind.bind, Except.bind, throw, throwThe, MonadExceptOf.throw]

/-- **`mayDangle` Address-Space End Guard & Uninhabited Concrete Type Soundness
(`wideDyn_mayDangle_addressTooClose_and_uninhabited_concrete_ok`, `[adv A2]`)**: matching
`ValidityVisitor.lean` lines 215–230 & 412–418:
1. Under `mayDangle = true`, a `.danglingInt closeAddr` with `closeAddr.toNat + desc.sizeBytes.toNat ≥
   usizeMax64` faults with `.error (.addressTooClose desc.sizeBytes)` *before* alignment or nullness!
2. Under `mayDangle = true`, an in-bounds aligned nonzero `.danglingInt okAddr` **succeeds** with
   `.ok (desc.concreteTy, desc.sizeBytes, desc.alignBytes)` **even when `desc.concreteTy` is
   uninhabited** (e.g. `ManuallyDrop<Box<dyn Send>>` constructed from `!`), whereas `mayDangle =
   false` on a live aligned pointer to the same uninhabited concrete type faults with
   `.error .uninhabitedPointee`! -/
theorem wideDyn_mayDangle_addressTooClose_and_uninhabited_concrete_ok
    (w : KeyedAllocWorld) (reg : VTableRegistry) (maxSize : Nat)
    (expectedSpec : DynExistentialSpec) (vtablePtr : ScalarPtrHalf)
    (desc : VTableDescriptor) (lay : ComputedTyLayout)
    (closeAddr okAddr : UInt64) (dataId : MiriAllocId) (info : AllocInfo)
    (hv : validateVTableHalf w reg vtablePtr expectedSpec = .ok desc)
    (hclose : closeAddr.toNat + desc.sizeBytes.toNat ≥ usizeMax64)
    (hokNz : okAddr ≠ 0)
    (hokNotClose : okAddr.toNat + desc.sizeBytes.toNat < usizeMax64)
    (hokAlign : desc.alignBytes > 0 → okAddr % desc.alignBytes = 0)
    (hlive : w.getAllocInfo dataId = .ok info)
    (hkind : info.kind = .liveData)
    (hfit : desc.sizeBytes.toNat ≤ info.sizeBytes.toNat)
    (hlay : computeTyLayout maxSize desc.concreteTy = .ok lay)
    (huninh : lay.isInhabited = false) :
    validateWideDynSafePtr w reg maxSize expectedSpec true (.danglingInt closeAddr) vtablePtr =
      .error (.addressTooClose desc.sizeBytes) ∧
    validateWideDynSafePtr w reg maxSize expectedSpec true (.danglingInt okAddr) vtablePtr =
      .ok (desc.concreteTy, desc.sizeBytes, desc.alignBytes) ∧
    validateWideDynSafePtr w reg maxSize expectedSpec false (.provenanced okAddr dataId 0) vtablePtr =
      .error .uninhabitedPointee := by
  have hcloseD : decide (closeAddr.toNat + desc.sizeBytes.toNat ≥ usizeMax64) = true :=
    decide_eq_true hclose
  have hnotCloseD : decide (okAddr.toNat + desc.sizeBytes.toNat ≥ usizeMax64) = false :=
    decide_eq_false (by omega)
  have hok0 : (okAddr == 0) = false := beq_false_of_ne hokNz
  have halFalse : (decide (desc.alignBytes > 0) && (okAddr % desc.alignBytes != 0)) = false := by
    by_cases hal : desc.alignBytes > 0
    · simp [hal, hokAlign hal]
    · simp [hal]
  refine ⟨?_, ?_, ?_⟩
  · unfold validateWideDynSafePtr
    simp [hv, hcloseD, Bind.bind, Except.bind, throw, throwThe, MonadExceptOf.throw]
  · unfold validateWideDynSafePtr
    simp [hv, hnotCloseD, hok0, halFalse, Pure.pure, Except.pure, Bind.bind, Except.bind]
  · have hkindF : (info.kind != .liveData) = false := by rw [hkind]; rfl
    unfold validateWideDynSafePtr
    if hsz : desc.sizeBytes > 0 then
      simp [hv, hsz, hlive, hkindF, hfit, hok0, halFalse, hlay, huninh,
        Bind.bind, Except.bind, throw, throwThe, MonadExceptOf.throw]
    else
      simp [hv, hsz, hok0, halFalse, hlay, huninh,
        Bind.bind, Except.bind, throw, throwThe, MonadExceptOf.throw]

/-- **Alignment Precedes Concrete-Type Uninhabitedness (`wideDyn_unaligned_precedes_concrete_uninhabited`,
`[adv A2]`)**: matching `ValidityVisitor.lean` lines 227–228 (`checkPointerAlignResult` inside
`checkSafe`) vs. lines 412–418 (`unpackDynTrait` during recursive place visitation), an unaligned
live non-null wide `dyn` safe pointer whose concrete type is uninhabited (e.g. `(u32, !) as dyn Send`
at `addr = 2`) reports `.unalignedSafePointer` **before** `.uninhabitedPointee`! -/
theorem wideDyn_unaligned_precedes_concrete_uninhabited
    (w : KeyedAllocWorld) (reg : VTableRegistry) (maxSize : Nat)
    (expectedSpec : DynExistentialSpec) (vtablePtr : ScalarPtrHalf)
    (desc : VTableDescriptor) (lay : ComputedTyLayout)
    (addr : UInt64) (dataId : MiriAllocId) (info : AllocInfo)
    (hv : validateVTableHalf w reg vtablePtr expectedSpec = .ok desc)
    (hlive : w.getAllocInfo dataId = .ok info)
    (hkind : info.kind = .liveData)
    (hfit : desc.sizeBytes.toNat ≤ info.sizeBytes.toNat)
    (hnz : addr ≠ 0)
    (hal_pos : desc.alignBytes > 0)
    (hunalign : addr % desc.alignBytes ≠ 0)
    (hlay : computeTyLayout maxSize desc.concreteTy = .ok lay)
    (huninh : lay.isInhabited = false) :
    validateWideDynSafePtr w reg maxSize expectedSpec false (.provenanced addr dataId 0) vtablePtr =
      .error (.unalignedSafePointer desc.alignBytes addr) ∧
    (computeTyLayout maxSize desc.concreteTy).map ComputedTyLayout.isInhabited = .ok false := by
  have haddr0 : (addr == 0) = false := beq_false_of_ne hnz
  have hmod : (addr % desc.alignBytes != 0) = true := bne_iff_ne.mpr hunalign
  have hkindF : (info.kind != .liveData) = false := by rw [hkind]; rfl
  refine ⟨?_, by rw [hlay]; exact congrArg Except.ok huninh⟩
  unfold validateWideDynSafePtr
  if hsz : desc.sizeBytes > 0 then
    simp [hv, hsz, hlive, hkindF, hfit, haddr0, hal_pos, hmod,
      Bind.bind, Except.bind, throw, throwThe, MonadExceptOf.throw]
  else
    simp [hv, hsz, haddr0, hal_pos, hmod,
      Bind.bind, Except.bind, throw, throwThe, MonadExceptOf.throw]

/-- **Salted VTable Distinct-Allocation & Shared-Validity Theorem
(`saltedVTable_distinct_salts_distinct_allocIds_both_valid`, `[adv A1]`)**: matching
`Miri.Interpreter.VTable.getPointer` (`globalSalt`), interning the same `(concreteTy, principal,
rawAutoTraits)` twice with distinct salts `salt₁ ≠ salt₂` from `KeyedAllocWorld.empty` succeeds for
any `Sized` type with valid layout, allocates **two distinct `MiriAllocId`s** (`desc₁.allocId ≠
desc₂.allocId`), and **both** salted vtables pass `validateVTableHalf` with identical
`(concreteTy, sizeBytes, alignBytes)`! -/
theorem saltedVTable_distinct_salts_distinct_allocIds_both_valid
    (maxSize : Nat) (concreteTy : ProtoTy) (lay : ComputedTyLayout) (dropFn : DefPath)
    (principal : Option PrincipalTraitRef) (rawAutoTraits : List AutoTrait)
    (salt₁ salt₂ : Nat) (addr₁ addr₂ : UInt64)
    (hlay : computeTyLayout maxSize concreteTy = .ok lay)
    (hsized : lay.isSized = true)
    (hneSalt : salt₁ ≠ salt₂) :
    ∃ sreg₂ w₂ desc₁ desc₂,
      (do
        let (sreg₁, w₁, d₁) ←
          ({} : SaltedVTableRegistry).internSalted KeyedAllocWorld.empty maxSize
            concreteTy dropFn principal rawAutoTraits salt₁
        let (sreg₂, w₂, d₂) ←
          sreg₁.internSalted w₁ maxSize concreteTy dropFn principal rawAutoTraits salt₂
        return (sreg₂, w₂, d₁, d₂)) = .ok (sreg₂, w₂, desc₁, desc₂) ∧
      desc₁.allocId ≠ desc₂.allocId ∧
      desc₁.concreteTy = desc₂.concreteTy ∧
      desc₁.sizeBytes = desc₂.sizeBytes ∧
      desc₁.alignBytes = desc₂.alignBytes ∧
      validateVTableHalf w₂ sreg₂.toVTableRegistry (.provenanced addr₁ desc₁.allocId 0)
        ⟨principal, AutoTraitSet.ofList rawAutoTraits⟩ = .ok desc₁ ∧
      validateVTableHalf w₂ sreg₂.toVTableRegistry (.provenanced addr₂ desc₂.allocId 0)
        ⟨principal, AutoTraitSet.ofList rawAutoTraits⟩ = .ok desc₂ := by
  let kBase := mkCanonicalVTableKey concreteTy principal rawAutoTraits
  let sk₁ : SaltedVTableKey := ⟨kBase, salt₁⟩
  let sk₂ : SaltedVTableKey := ⟨kBase, salt₂⟩
  have hneSk : sk₁ ≠ sk₂ := by
    intro heq
    injection heq with _ hs
    exact hneSalt hs
  let id₁ : MiriAllocId := ⟨1, by decide⟩
  let id₂ : MiriAllocId := ⟨2, by decide⟩
  have hneId : id₁ ≠ id₂ := by decide
  have hres1 : KeyedAllocWorld.empty.reserveAllocId =
      ({ KeyedAllocWorld.empty with
          nextAllocId := 2
          issuedIds := (∅ : ExtTreeMap0 MiriAllocId Unit).insert id₁ () }, .ok id₁) := by
    unfold KeyedAllocWorld.empty KeyedAllocWorld.reserveAllocId MiriAllocId.ofUInt64
      KeyedAllocWorld.containsId
    simp [ExtTreeMap0.contains_eq_isSome_get?, ExtTreeMap0.get?_empty]
    exact ⟨rfl, rfl⟩
  let alU := UInt64.ofNat lay.alignBytes
  let szU := UInt64.ofNat lay.sizeBytes
  let mslots := match principal with | none => [] | some p => p.methodNames.map VTableSlot.method
  let d₁ : VTableDescriptor :=
    ⟨id₁, concreteTy, ⟨principal, kBase.autoTraits⟩, dropFn, szU, alU,
      [.dropInPlace dropFn, .size szU, .align alU] ++ mslots⟩
  let d₂ : VTableDescriptor :=
    ⟨id₂, concreteTy, ⟨principal, kBase.autoTraits⟩, dropFn, szU, alU,
      [.dropInPlace dropFn, .size szU, .align alU] ++ mslots⟩
  have hb1 : buildVTableDescriptor maxSize id₁ concreteTy dropFn ⟨principal, kBase.autoTraits⟩ = .ok d₁ := by
    unfold buildVTableDescriptor
    simp [hlay, hsized, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure, d₁, szU, alU, mslots]
  have hb2 : buildVTableDescriptor maxSize id₂ concreteTy dropFn ⟨principal, kBase.autoTraits⟩ = .ok d₂ := by
    unfold buildVTableDescriptor
    simp [hlay, hsized, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure, d₂, szU, alU, mslots]
  let w₁ := ({ KeyedAllocWorld.empty with
      nextAllocId := 2
      issuedIds := (∅ : ExtTreeMap0 MiriAllocId Unit).insert id₁ () }).registerGlobal
    ⟨id₁, .vtable, 0, alU, .not⟩
  have hnotCont2 : w₁.containsId id₂ = false := by
    unfold w₁ KeyedAllocWorld.registerGlobal KeyedAllocWorld.containsId KeyedAllocWorld.empty
    dsimp only
    rw [ExtTreeMap0.contains_eq_isSome_get?,
      ExtTreeMap0.get?_insert_ne _ hneId, ExtTreeMap0.get?_insert_ne _ hneId,
      ExtTreeMap0.get?_empty,
      ExtTreeMap0.contains_eq_isSome_get?, ExtTreeMap0.get?_empty,
      ExtTreeMap0.contains_eq_isSome_get?, ExtTreeMap0.get?_empty,
      ExtTreeMap0.contains_eq_isSome_get?, ExtTreeMap0.get?_insert_ne _ hneId,
      ExtTreeMap0.get?_empty]
    rfl
  have hres2 : w₁.reserveAllocId =
      ({ w₁ with nextAllocId := 3, issuedIds := w₁.issuedIds.insert id₂ () }, .ok id₂) := by
    unfold KeyedAllocWorld.reserveAllocId
    have hexh : w₁.idSupplyExhausted = false := rfl
    have hnext : w₁.nextAllocId = 2 := rfl
    have hof2 : MiriAllocId.ofUInt64 2 = some id₂ := rfl
    rw [hexh, hnext, hof2]
    simp [hnotCont2]
  let sreg₁ : SaltedVTableRegistry := {
    bySaltedKey := (∅ : ExtTreeMap0 SaltedVTableKey VTableDescriptor).insert sk₁ d₁
    byAlloc := (∅ : ExtTreeMap0 MiriAllocId VTableDescriptor).insert id₁ d₁
  }
  have hmiss2 : sreg₁.bySaltedKey.get? sk₂ = none :=
    (ExtTreeMap0.get?_insert_ne ∅ hneSk d₁).trans (ExtTreeMap0.get?_empty sk₂)
  let w₂ := ({ w₁ with nextAllocId := 3, issuedIds := w₁.issuedIds.insert id₂ () }).registerGlobal
    ⟨id₂, .vtable, 0, alU, .not⟩
  let sreg₂ : SaltedVTableRegistry := {
    bySaltedKey := sreg₁.bySaltedKey.insert sk₂ d₂
    byAlloc := sreg₁.byAlloc.insert id₂ d₂
  }
  have hselfMatch : vtableMatchesExpectedSpec ⟨principal, kBase.autoTraits⟩
      ⟨principal, AutoTraitSet.ofList rawAutoTraits⟩ = true := by
    unfold vtableMatchesExpectedSpec kBase mkCanonicalVTableKey
    cases principal with
    | none => rfl
    | some p =>
      have hdp : decide (p.traitDefPath = p.traitDefPath) = true := decide_eq_true rfl
      have hsub : natListSubset p.normalizedPredicates p.normalizedPredicates = true :=
        (natListSubset_iff _ _).mpr (fun _ hx => hx)
      dsimp only
      rw [hdp, hsub]
      rfl
  refine ⟨sreg₂, w₂, d₁, d₂, ?_, hneId, rfl, rfl, rfl, ?_, ?_⟩
  · unfold SaltedVTableRegistry.internSalted
    change (do
      let (sreg₁', w₁', d₁') ← (do
        match (∅ : ExtTreeMap0 SaltedVTableKey VTableDescriptor).get? sk₁ with
        | some existing => return (({} : SaltedVTableRegistry), KeyedAllocWorld.empty, existing)
        | none =>
          let (wRes, idRes) := KeyedAllocWorld.empty.reserveAllocId
          let id ← idRes.mapError VTableBuildErr.allocIdErr
          let desc ← buildVTableDescriptor maxSize id concreteTy dropFn ⟨principal, kBase.autoTraits⟩
          let wGlob := wRes.registerGlobal ⟨id, .vtable, 0, desc.alignBytes, .not⟩
          return ({ bySaltedKey := (∅ : ExtTreeMap0 SaltedVTableKey VTableDescriptor).insert sk₁ desc
                    byAlloc := (∅ : ExtTreeMap0 MiriAllocId VTableDescriptor).insert id desc }, wGlob, desc))
      SaltedVTableRegistry.internSalted sreg₁' w₁' maxSize concreteTy dropFn principal rawAutoTraits salt₂ >>=
        fun (sreg₂', w₂', d₂') => pure (sreg₂', w₂', d₁', d₂')) = .ok (sreg₂, w₂, d₁, d₂)
    rw [ExtTreeMap0.get?_empty, hres1]
    simp only [Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure, hb1]
    unfold SaltedVTableRegistry.internSalted
    change (match sreg₁.bySaltedKey.get? sk₂ with
      | some existing => Except.ok (sreg₁, w₁, existing)
      | none => do
        let (wRes, idRes) := w₁.reserveAllocId
        let id ← idRes.mapError VTableBuildErr.allocIdErr
        let desc ← buildVTableDescriptor maxSize id concreteTy dropFn ⟨principal, kBase.autoTraits⟩
        let wGlob := wRes.registerGlobal ⟨id, .vtable, 0, desc.alignBytes, .not⟩
        return ({ bySaltedKey := sreg₁.bySaltedKey.insert sk₂ desc
                  byAlloc := sreg₁.byAlloc.insert id desc }, wGlob, desc)) >>=
      (fun (sreg₂', w₂', d₂') => pure (sreg₂', w₂', d₁, d₂')) = .ok (sreg₂, w₂, d₁, d₂)
    rw [hmiss2, hres2]
    simp only [Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure, hb2]
    rfl
  · have hg1 : w₂.findGlobal? id₁ = some ⟨id₁, .vtable, 0, alU, .not⟩ := by
      unfold w₂ w₁ KeyedAllocWorld.registerGlobal KeyedAllocWorld.findGlobal?
      dsimp only
      rw [ExtTreeMap0.get?_insert_ne _ hneId.symm, ExtTreeMap0.get?_insert_self]
    have ha1 : sreg₂.toVTableRegistry.byAlloc.get? id₁ = some d₁ := by
      unfold sreg₂ sreg₁ SaltedVTableRegistry.toVTableRegistry
      dsimp only
      rw [ExtTreeMap0.get?_insert_ne _ hneId.symm, ExtTreeMap0.get?_insert_self]
    unfold validateVTableHalf
    simp [d₁, hg1, ha1, hselfMatch]
  · have hg2 : w₂.findGlobal? id₂ = some ⟨id₂, .vtable, 0, alU, .not⟩ := by
      unfold w₂ KeyedAllocWorld.registerGlobal KeyedAllocWorld.findGlobal?
      dsimp only
      rw [ExtTreeMap0.get?_insert_self]
    have ha2 : sreg₂.toVTableRegistry.byAlloc.get? id₂ = some d₂ := by
      unfold sreg₂ SaltedVTableRegistry.toVTableRegistry
      dsimp only
      rw [ExtTreeMap0.get?_insert_self]
    unfold validateVTableHalf
    simp [d₂, hg2, ha2, hselfMatch]

end Anneal.ExtTreeMapAllocAndNoWritableProto
