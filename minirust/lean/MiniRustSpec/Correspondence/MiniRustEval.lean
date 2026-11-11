/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import MiniRustSpec.Correspondence.Lemmas

/-!
# Symbolic evaluation of the MiniRust interpretation on related machines

Each lemma computes one interpreted MiniRust function on a machine whose
thread, active-thread, and allocation fields have the shape fixed by
`StateRel` (`Shape`). The lemmas are stated in terms of the generated MiniRust
types and the interpretation in `MiniRustSpec.Interp`; Anneal does not appear.
-/

namespace MiniRustSpec.Correspondence

open Trusted.Rustc.V2026_06_01
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open MiniRustSpec
open MiniRustSpec.LibSpecr
open MiniRustSpec.Interp

@[simp] theorem pure_ok {ε α : Type} (a : α) : (pure a : Except ε α) = .ok a := rfl
@[simp] theorem ok_bind {ε α β : Type} (a : α) (f : α → Except ε β) :
    (Except.ok a >>= f) = f a := rfl
@[simp] theorem error_bind {ε α β : Type} (e : ε) (f : α → Except ε β) :
    (Except.error e >>= f) = .error e := rfl
@[simp] theorem natCast_lt_zero (n : Nat) : ((n : Int) < 0) ↔ False :=
  iff_of_false (Int.not_lt.mpr (Int.natCast_nonneg n)) id

-- Rewriting with these instead of unfolding `expect_size`/`expect_align`
-- keeps the panic-message string literals out of the proof term (unfolding
-- them in some contexts makes the kernel evaluate the message concatenation,
-- which overflows its recursion limit).
@[simp] theorem expect_size_sized (sz : Size) (al : Align) (msg : String) :
    LayoutStrategy.expect_size (.Sized sz al) msg = .ok sz := rfl
@[simp] theorem expect_align_sized (sz : Size) (al : Align) (msg : String) :
    LayoutStrategy.expect_align (.Sized sz al) msg = .ok al := rfl
@[simp] theorem computeSize_sized (m : Mach) (sz : Size) (al : Align) :
    computeSize m (.Sized sz al) none = .ok sz := rfl

/-! ## Sizes of fragment integer types -/

/-- The byte sizes of Rust integer types on `x86_64`. -/
def GoodSize (n : Nat) : Prop := n = 1 ∨ n = 2 ∨ n = 4 ∨ n = 8 ∨ n = 16

theorem intTyBytes_good {k : MirAst.RigidTy} {s : Signedness} {n : Nat}
    (h : intTyBytes k = some (s, n)) : GoodSize n := by
  unfold intTyBytes at h
  split at h <;> simp at h <;> (obtain ⟨_, rfl⟩ := h) <;> simp [GoodSize]

theorem intTypeOf_good {t : MirAst.Ty} {it : Gen.IntType} (h : intTypeOf t = some it) :
    GoodSize it.size.bytes := by
  unfold intTypeOf at h
  cases hk : intTyBytes t.kind with
  | none => simp [hk] at h
  | some p =>
    obtain ⟨s, n⟩ := p
    simp [hk] at h
    subst h
    exact intTyBytes_good hk

theorem intBoolTupleOf_good {t : MirAst.Ty} {it : Gen.IntType}
    (h : intBoolTupleOf t = some it) : GoodSize it.size.bytes := by
  unfold intBoolTupleOf at h
  revert h
  cases t.kind with
  | tuple ts =>
    cases ts with
    | nil => simp
    | cons t0 ts' =>
      cases ts' with
      | nil => simp
      | cons t1 ts'' =>
        cases ts'' with
        | cons _ _ => simp
        | nil =>
          cases t1 with
          | bool =>
            intro h
            cases hk : intTyBytes t0 with
            | none => simp [hk] at h
            | some p =>
              obtain ⟨s, n⟩ := p
              simp [hk] at h
              subst h
              exact intTyBytes_good hk
          | _ => simp
  | _ => simp

theorem GoodSize.pos {n : Nat} (h : GoodSize n) : 0 < n := by
  rcases h with h | h | h | h | h <;> omega

theorem align_eq (it : Gen.IntType) (h : GoodSize it.size.bytes) :
    IntType.align it = .ok ⟨it.size.bytes⟩ := by
  unfold IntType.align alignFromBytes
  rcases h with h | h | h | h | h <;> rw [h] <;> rfl

theorem layout_eq (it : Gen.IntType) (h : GoodSize it.size.bytes) :
    Type.layout (.Int it) = .ok (.Sized it.size ⟨it.size.bytes⟩) := by
  simp [Type.layout, align_eq it h]

theorem withOverflow_eq (it : Gen.IntType) (h : GoodSize it.size.bytes) :
    IntType.with_overflow it = .ok (intBoolTupleTy it) := by
  rcases h with h | h | h | h | h <;>
    cases it with | mk s sz => cases sz with | mk n =>
      simp at h; subst h; cases s <;> rfl

theorem head_size_and_align_tuple (it : Gen.IntType) (h : GoodSize it.size.bytes) :
    TupleHeadLayout.head_size_and_align
      ⟨⟨it.size.bytes + it.size.bytes⟩, ⟨it.size.bytes⟩, none⟩ =
      (⟨it.size.bytes + it.size.bytes⟩, ⟨it.size.bytes⟩) := by
  rcases h with h | h | h | h | h <;>
    cases it with | mk s sz => cases sz with | mk n =>
      simp at h; subst h; cases s <;> rfl

theorem layout_tuple (it : Gen.IntType) (h : GoodSize it.size.bytes) :
    Type.layout (intBoolTupleTy it) =
      .ok (.Sized ⟨it.size.bytes + it.size.bytes⟩ ⟨it.size.bytes⟩) := by
  simp [intBoolTupleTy, Type.layout, head_size_and_align_tuple it h]

theorem goodAlignBytes_iff (n : Nat) : goodAlignBytes n = true ↔ GoodSize n := by
  simp [goodAlignBytes, GoodSize]

theorem arrayTypeOf_good {t : MirAst.Ty} {elemIt : Gen.IntType} {count : Nat}
    (h : arrayTypeOf t = some (elemIt, count)) : GoodSize elemIt.size.bytes := by
  unfold arrayTypeOf at h
  cases hk : t.kind with
  | array elemKind c =>
    simp only [hk] at h
    cases hb : intTyBytes elemKind with
    | none => simp [hb] at h
    | some p =>
      obtain ⟨s, n⟩ := p
      simp [hb] at h
      obtain ⟨rfl, rfl⟩ := h
      exact intTyBytes_good hb
  | _ => simp [hk] at h

theorem translateFn_local_ty {body : CapturedMir} {f : Gen.Function} (hf : translateFn body = some f)
    (i : Nat) (d : LocalDecl) (ty : Gen.Type) (hd : body.localDecls[i]? = some d)
    (hty : translateTy body.layouts d.ty = some ty) :
    mapGet f.locals (localName i) = some ty := by
  obtain ⟨hty', hget⟩ := (translateFn_spec body f hf).2.1 i d hd
  rw [hty] at hty'; cases hty'; exact hget

@[simp] theorem ensureElseUb_true (msg : String) :
    ensureElseUb true msg = .ok () := rfl

@[simp] theorem ensureElseUb_false (msg : String) :
    ensureElseUb false msg = .error (.ub msg) := rfl

@[simp] theorem int_add_sub_cancel_left (a b : Int) : a + b - a = b := by omega

@[simp] theorem toNat_cast_mul (a b : Nat) : ((a : Int) * (b : Int)).toNat = a * b := by
  have : (a : Int) * (b : Int) = ((a * b : Nat) : Int) := by push_cast; rfl
  rw [this, Int.toNat_natCast]

@[simp] theorem cast_mul_lt_zero (a b : Nat) : ¬ ((a : Int) * (b : Int) < 0) :=
  Int.not_lt.mpr (Int.mul_nonneg (Int.natCast_nonneg a) (Int.natCast_nonneg b))

@[simp] theorem zero_le_cast_mul (a b : Nat) : (0 : Int) ≤ (a : Int) * (b : Int) :=
  Int.mul_nonneg (Int.natCast_nonneg a) (Int.natCast_nonneg b)

@[simp] theorem sizeMulInt_size (s : Size) (m : Nat) :
    Size.mulInt s (Int.ofNat m) = .ok ⟨m * s.bytes⟩ := by
  simp [Size.mulInt, Size.from_bytes, Nat.mul_comm]

@[simp] theorem sizeMulInt_natCast (s : Size) (m : Nat) :
    Size.mulInt s (m : Int) = .ok ⟨m * s.bytes⟩ := by
  simp [Size.mulInt, Size.from_bytes, Nat.mul_comm]

theorem layout_array_eq (elemIt : Gen.IntType) (count : Nat) (h : GoodSize elemIt.size.bytes) :
    Type.layout (.Array (.Int elemIt) (count : Int)) =
      .ok (.Sized ⟨count * elemIt.size.bytes⟩ ⟨elemIt.size.bytes⟩) := by
  unfold Type.layout
  rw [layout_eq elemIt h]
  simp

theorem head_size_and_align_mk (size align : Nat) (hmod : size % align = 0) (hpos : 0 < align) :
    TupleHeadLayout.head_size_and_align
      { «end» := ⟨size⟩, align := ⟨align⟩, packed_align := none } =
      (⟨size⟩, ⟨align⟩) := by
  simp [TupleHeadLayout.head_size_and_align, Size.align_to]
  have hdvd : align ∣ size := Nat.dvd_of_mod_eq_zero hmod
  rcases hdvd with ⟨k, rfl⟩
  have h1 : align * k + align - 1 = (align - 1) + align * k := by omega
  rw [h1, Nat.add_mul_div_left _ _ hpos]
  have h2 : (align - 1) / align = 0 := Nat.div_eq_of_lt (by omega)
  rw [h2, Nat.zero_add, Nat.mul_comm]

theorem layout_tupleSpec (s : TupleSpec) (hwf : s.wf = true) :
    Type.layout s.toMiniRustTy = .ok (.Sized ⟨s.size⟩ ⟨s.align⟩) := by
  cases s with
  | scalar it =>
    simp only [TupleSpec.wf] at hwf
    exact layout_eq it ((goodAlignBytes_iff it.size.bytes).mp hwf)
  | tuple fields size align =>
    simp only [TupleSpec.wf, Bool.and_eq_true, decide_eq_true_eq] at hwf
    obtain ⟨⟨⟨hpos, hmod⟩, _⟩, _⟩ := hwf
    simp [TupleSpec.toMiniRustTy, Type.layout, head_size_and_align_mk size align hmod ((goodAlignBytes_iff align).mp hpos).pos,
      TupleSpec.size, TupleSpec.align]

/-! ## The callee's allocations and locals map -/

theorem scalarBytes_length (it : Gen.IntType) (bits : Nat) :
    (scalarBytes it bits).length = it.size.bytes := by
  simp [scalarBytes, leBytes_length]

theorem slotData_length (it : Gen.IntType) (slot : LocalSlot) :
    (slotData it slot).length = it.size.bytes := by
  unfold slotData
  split <;> simp [scalarBytes, uninitBytes, leBytes_length]

theorem tupleBytes_length (it : Gen.IntType) (bits b : Nat) (h : 0 < it.size.bytes) :
    (tupleBytes it bits b).length = it.size.bytes + it.size.bytes := by
  have hu8 : u8Ty.size.bytes = 1 := rfl
  simp only [tupleBytes, List.length_append, scalarBytes_length, hu8, List.length_replicate]
  omega

theorem tupleSlotData_length (it : Gen.IntType) (slot : LocalSlot) (h : 0 < it.size.bytes) :
    (tupleSlotData it slot).length = it.size.bytes + it.size.bytes := by
  unfold tupleSlotData
  split
  · exact tupleBytes_length it _ _ h
  · simp

theorem localAllocsFrom_getElem? (ctx : Ctx) (k : Nat) (ds : List LocalDecl) (slots : List LocalSlot)
    (j : Nat) (d : LocalDecl) (slot : LocalSlot) (hd : ds[j]? = some d) (hs : slots[j]? = some slot)
    (layouts : Layout.LayoutTable := ⟨64, true, []⟩) :
    (localAllocsFrom ctx k ds slots layouts)[j]? =
      some (localAlloc ctx (k + j) (itOf d layouts) (declSlotData d slot layouts)) := by
  induction ds generalizing k slots j with
  | nil => simp at hd
  | cons d' ds ih =>
    cases slots with
    | nil => simp at hs
    | cons s' ss =>
      cases j with
      | zero => simp at hd hs; subst hd; subst hs; simp [localAllocsFrom]
      | succ j =>
        simp at hd hs
        simp only [localAllocsFrom, List.getElem?_cons_succ]
        rw [ih (k + 1) ss j hd hs, show k + 1 + j = k + (j + 1) by omega]

theorem localAllocsFrom_set (ctx : Ctx) (k : Nat) (ds : List LocalDecl) (slots : List LocalSlot)
    (j : Nat) (d : LocalDecl) (slot' : LocalSlot) (hd : ds[j]? = some d)
    (layouts : Layout.LayoutTable := ⟨64, true, []⟩) :
    (localAllocsFrom ctx k ds slots layouts).set j
        (localAlloc ctx (k + j) (itOf d layouts) (declSlotData d slot' layouts)) =
      localAllocsFrom ctx k ds (slots.set j slot') layouts := by
  induction ds generalizing k slots j with
  | nil => simp at hd
  | cons d' ds ih =>
    cases slots with
    | nil => simp [localAllocsFrom]
    | cons s' ss =>
      cases j with
      | zero => simp at hd; subst hd; simp [localAllocsFrom]
      | succ j =>
        simp at hd
        simp only [localAllocsFrom, List.set_cons_succ]
        rw [show k + (j + 1) = k + 1 + j by omega, ih (k + 1) ss j hd]

theorem localAllocsFrom_length (ctx : Ctx) (k : Nat) (ds : List LocalDecl) (slots : List LocalSlot)
    (layouts : Layout.LayoutTable := ⟨64, true, []⟩) :
    (localAllocsFrom ctx k ds slots layouts).length = min ds.length slots.length := by
  induction ds generalizing k slots with
  | nil => simp [localAllocsFrom]
  | cons d ds ih =>
    cases slots with
    | nil => simp [localAllocsFrom]
    | cons s ss => simp [localAllocsFrom, ih, Nat.min_def]; split <;> omega

theorem mapGet_range_map {V : Type} (g : Nat → V) (n i : Nat) :
    mapGet (⟨(List.range n).map (fun i => (localName i, g i))⟩ : Map Gen.LocalName V) (localName i) =
      if i < n then some (g i) else none := by
  induction n with
  | zero => simp [mapGet]
  | succ n ih =>
    rw [List.range_succ, List.map_append]
    unfold mapGet at ih ⊢
    rw [List.find?_append]
    by_cases hi : i < n
    · have hi' : i < n + 1 := by omega
      simp only [hi, hi', ↓reduceIte] at ih ⊢
      cases h : List.find? (fun e => decide (e.1 = localName i))
        (List.map (fun i => (localName i, g i)) (List.range n)) <;> simp_all
    · cases h : List.find? (fun e => decide (e.1 = localName i))
        (List.map (fun i => (localName i, g i)) (List.range n))
      · by_cases hin : i = n
        · subst hin; simp
        · have : ¬ i < n + 1 := by omega
          simp [localName_inj, Ne.symm hin, this]
      · simp [h, hi] at ih

theorem mapGet_localsMap (ctx : Ctx) (n i : Nat) (hi : i < n) :
    mapGet (localsMap ctx n) (localName i) = some (localPtr ctx i) := by
  simp [localsMap, mapGet_range_map, hi]

/-! ## Machine shape -/

/-- The fields of a MiniRust machine that the fragment's execution reads and
writes: one enabled thread with stack `frames`, active, and the allocation
list. -/
structure Shape (m : Mach) (ctx : Ctx) (frames : List Frame) (allocs : List Gen.Allocation) : Prop where
  threads : m.threads = [thread1 ctx frames]
  active : m.active_thread = 0
  allocs : m.mem.memory.allocations = allocs

theorem curFrame_eq {m : Mach} {ctx : Ctx} {fr : Frame} {allocs : List Gen.Allocation}
    (h : Shape m ctx [ctx.caller, fr] allocs) : curFrame m = .ok fr := by
  simp [curFrame, activeThread, listIndex, h.threads, h.active, thread1]

theorem pick_eq {m : Mach} {ctx : Ctx} {frs : List Frame} (hthr : m.threads = [thread1 ctx frs]) :
    pickActiveThread m = .ok 0 := by
  simp [pickActiveThread, hthr, thread1]

theorem check_ok (cm : Gen.ConcurrentMemory BM) (S : Set Gen.ThreadId) (acc : List Gen.Access) :
    CM.check_data_races cm 0 (setInsert S 0, acc) = .ok () := by
  unfold CM.check_data_races setContains setInsert
  split <;> simp_all

/-! ## Lists and integer casts -/

@[simp] theorem toNat_cast_add (a b : Nat) : ((a : Int) + (b : Int)).toNat = a + b := by omega

@[simp] theorem cast_add_nonneg (a b : Nat) : (0 : Int) ≤ (a : Int) + (b : Int) := by omega

theorem getElem?_base_append {α : Type} (base L : List α) (i : Nat) :
    (base ++ L)[base.length + i]? = L[i]? := by
  simp [List.getElem?_append_right]

theorem set_base_append {α : Type} (base L : List α) (i : Nat) (x : α) :
    (base ++ L).set (base.length + i) x = base ++ L.set i x := by
  simp

theorem set_self_of_getElem? {α : Type} (L : List α) (i : Nat) (x : α) (h : L[i]? = some x) :
    L.set i x = L := by
  apply List.ext_getElem?
  intro j
  by_cases hij : i = j
  · subst hij; simp [List.getElem?_set_self (List.getElem?_eq_some_iff.mp h).1, h]
  · simp [List.getElem?_set_ne hij]

/-! ## Byte encodings -/

theorem mapM_data_scalarBytes (it : Gen.IntType) (bits : Nat) :
    (scalarBytes it bits).mapM AbstractByte.data = some (leBytes bits it.size.bytes) := by
  unfold scalarBytes
  generalize leBytes bits it.size.bytes = bs
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [List.mapM_cons, AbstractByte.data] at ih ⊢; rw [ih]; rfl

theorem mapM_data_uninitBytes (it : Gen.IntType) (h : 0 < it.size.bytes) :
    (uninitBytes it).mapM AbstractByte.data = none := by
  unfold uninitBytes
  obtain ⟨k, hk⟩ : ∃ k, it.size.bytes = k + 1 := ⟨it.size.bytes - 1, by omega⟩
  rw [hk, List.replicate_succ]
  simp [List.mapM_cons, AbstractByte.data]

theorem decode_leBytes (signed : Signedness) (k bits : Nat) (hb : bits < 2 ^ (8 * k)) :
    Endianness.decode .LittleEndian signed (leBytes bits k) = intFromBits bits ⟨signed, ⟨k⟩⟩ := by
  have hv : leValue (leBytes bits k) = bits := by
    rw [leValue_leBytes, show (256 : Nat) ^ k = 2 ^ (8 * k) by rw [Nat.pow_mul]]
    exact Nat.mod_eq_of_lt hb
  cases signed with
  | Unsigned => simp [Endianness.decode, intFromBits, hv]
  | Signed =>
    simp only [Endianness.decode, intFromBits, hv, leBytes_length]
    by_cases hlt : bits < 2 ^ (8 * k - 1)
    · have : (bits : Int) < 2 ^ (8 * k - 1) := by exact_mod_cast hlt
      simp [hlt, this]
    · have : ¬ (bits : Int) < 2 ^ (8 * k - 1) := by
        intro h'; exact hlt (by exact_mod_cast h')
      simp [hlt, this]

theorem encode_eq (signed : Signedness) (size : Size) (v : Int) (h : inBounds v signed size = true) :
    Endianness.encode .LittleEndian signed size v =
      some (leBytes (v % 2 ^ Size.bits size).toNat size.bytes) := by
  simp [Endianness.encode, h]

theorem canRepresent_intFromBits (it : Gen.IntType) (bits : Nat) (hgood : GoodSize it.size.bytes)
    (hb : bits < 2 ^ (8 * it.size.bytes)) : IntType.can_represent it (intFromBits bits it) = true := by
  have hn : 0 < 8 * it.size.bytes := by have := hgood.pos; omega
  unfold IntType.can_represent
  rw [inBounds_iff _ _ _ (by simpa [Size.bits] using hn)]
  simpa [Size.bits] using intFromBits_window bits it hn hb

theorem checkValue_int {t : Gen.IntType} {i : Int} {m? : Option Mach}
    (h : IntType.can_represent t i = true) :
    checkValue (.Int i) (.Int t) m? = .ok () := by
  simp only [checkValue, ensureElseUb, h]; rfl

theorem checkValue_bool (b : Bool) {m? : Option Mach} :
    checkValue (.Bool b) .Bool m? = .ok () := rfl

/-- Encoding an in-window integer at an integer type yields the little-endian
bytes of its residue. -/
theorem encode_int (it : Gen.IntType) (v : Int) (hgood : GoodSize it.size.bytes)
    (hv : IntType.can_represent it v = true) :
    Type.encode (.Int it) (.Int v) = .ok (scalarBytes it (v % 2 ^ (8 * it.size.bytes)).toNat) := by
  obtain ⟨signed, size⟩ := it
  have h : inBounds v signed size = true := hv
  simp [Type.encode, Type.encodeInt, x86_64.ENDIANNESS, encode_eq signed size v h, scalarBytes,
    Size.bits]

/-! ## Loads and stores of the callee's locals -/

@[simp] theorem stackAlloc_live (addr : Int) (it : Gen.IntType) (data : List Byte) :
    (stackAlloc addr it data).live = true := rfl
@[simp] theorem stackAlloc_addr (addr : Int) (it : Gen.IntType) (data : List Byte) :
    (stackAlloc addr it data).addr = addr := rfl
@[simp] theorem stackAlloc_data (addr : Int) (it : Gen.IntType) (data : List Byte) :
    (stackAlloc addr it data).data = data := rfl
@[simp] theorem stackAlloc_align (addr : Int) (it : Gen.IntType) (data : List Byte) :
    (stackAlloc addr it data).align = ⟨it.size.bytes⟩ := rfl
@[simp] theorem stackAlloc_kind (addr : Int) (it : Gen.IntType) (data : List Byte) :
    (stackAlloc addr it data).kind = .Stack := rfl
@[simp] theorem stackAlloc_extra (addr : Int) (it : Gen.IntType) (data : List Byte) :
    (stackAlloc addr it data).extra = () := rfl

@[simp] theorem localAlloc_live (ctx : Ctx) (i : Nat) (it : Gen.IntType) (data : List Byte) :
    (localAlloc ctx i it data).live = true := rfl
@[simp] theorem localAlloc_addr (ctx : Ctx) (i : Nat) (it : Gen.IntType) (data : List Byte) :
    (localAlloc ctx i it data).addr = ctx.addrs.getD i 0 := rfl
@[simp] theorem localAlloc_data (ctx : Ctx) (i : Nat) (it : Gen.IntType) (data : List Byte) :
    (localAlloc ctx i it data).data = data := rfl
@[simp] theorem localAlloc_align (ctx : Ctx) (i : Nat) (it : Gen.IntType) (data : List Byte) :
    (localAlloc ctx i it data).align = ⟨it.size.bytes⟩ := rfl
@[simp] theorem localAlloc_kind (ctx : Ctx) (i : Nat) (it : Gen.IntType) (data : List Byte) :
    (localAlloc ctx i it data).kind = .Stack := rfl
@[simp] theorem localAlloc_extra (ctx : Ctx) (i : Nat) (it : Gen.IntType) (data : List Byte) :
    (localAlloc ctx i it data).extra = () := rfl

/-- The machine after loading or storing: the access is logged, the
allocations are `allocs`, and nothing else changes. -/
def withMem (m : Mach) (allocs : List Gen.Allocation) (acc : Gen.Access) : Mach :=
  { m with mem := { memory := { m.mem.memory with allocations := allocs },
                    accesses := m.mem.accesses ++ [acc] } }

theorem withMem_shape {m : Mach} {ctx : Ctx} {frames : List Frame} {allocs allocs' : List Gen.Allocation}
    (h : Shape m ctx frames allocs) (acc : Gen.Access) :
    Shape (withMem m allocs' acc) ctx frames allocs' :=
  ⟨h.threads, h.active, rfl⟩

/-- `Align::ONE`, and the natural alignment of a local, accept its address. -/
@[simp] theorem isAligned_one (a : Int) : Align.is_aligned ⟨1⟩ a = true := by
  simp [Align.is_aligned]

theorem typedLoad_local_init {m : Mach} {ctx : Ctx} {frames : List Frame} {L : List Gen.Allocation}
    (h : Shape m ctx frames (ctx.base ++ L)) (i : Nat) (it : Gen.IntType) (bits : Nat)
    (hgood : GoodSize it.size.bytes) (hb : bits < 2 ^ (8 * it.size.bytes))
    (hL : L[i]? = some (localAlloc ctx i it (scalarBytes it bits)))
    (align : Align) (hal : Align.is_aligned align (ctx.addrs.getD i 0) = true) :
    ∃ m', typedLoad m (localPtr ctx i) (.Int it) align .None = .ok (.Int (intFromBits bits it), m') ∧
      Shape m' ctx frames (ctx.base ++ L) := by
  have hpos := hgood.pos
  obtain ⟨hi, hLi⟩ := List.getElem?_eq_some_iff.mp hL
  have hlen : (scalarBytes it bits).length = it.size.bytes := by
    simp [scalarBytes, leBytes_length]
  have hset := set_self_of_getElem? L i _ hL
  refine ⟨withMem m (ctx.base ++ L) ⟨.Load, .None, ctx.addrs.getD i 0, it.size⟩, ?_,
    withMem_shape h _⟩
  obtain ⟨signed, size⟩ := it
  simp only [typedLoad, layout_eq _ hgood, LayoutStrategy.expect_size, CM.load, BM.load, hal,
    BM.check_ptr, localPtr, listIndex, h.allocs]
  simp [Nat.ne_of_gt hpos, hi, hLi, Allocation.size, hlen, listSet, subsliceWithLength, hset,
    List.take_of_length_le, Type.decode, Type.decodeInt, mapM_data_scalarBytes, x86_64.ENDIANNESS,
    decode_leBytes signed size.bytes bits hb,
    checkValue_int (canRepresent_intFromBits ⟨signed, size⟩ bits hgood hb), withMem]

theorem typedLoad_local_uninit {m : Mach} {ctx : Ctx} {frames : List Frame} {L : List Gen.Allocation}
    (h : Shape m ctx frames (ctx.base ++ L)) (i : Nat) (it : Gen.IntType)
    (hgood : GoodSize it.size.bytes) (hL : L[i]? = some (localAlloc ctx i it (uninitBytes it)))
    (align : Align) (hal : Align.is_aligned align (ctx.addrs.getD i 0) = true) :
    ∃ msg, typedLoad m (localPtr ctx i) (.Int it) align .None = .error (.ub msg) := by
  have hpos := hgood.pos
  obtain ⟨hi, hLi⟩ := List.getElem?_eq_some_iff.mp hL
  have hlen : (uninitBytes it).length = it.size.bytes := by simp [uninitBytes]
  have hset := set_self_of_getElem? L i _ hL
  refine ⟨"load at type but the data in memory violates the language invariant", ?_⟩
  obtain ⟨signed, size⟩ := it
  simp only [typedLoad, layout_eq _ hgood, LayoutStrategy.expect_size, CM.load, BM.load, hal,
    BM.check_ptr, localPtr, listIndex, h.allocs]
  simp [Nat.ne_of_gt hpos, hi, hLi, Allocation.size, hlen, listSet, subsliceWithLength, hset,
    List.take_of_length_le, Type.decode, Type.decodeInt, mapM_data_uninitBytes _ hpos, ub]

theorem localAlloc_with_data (ctx : Ctx) (i : Nat) (it : Gen.IntType) (data data' : List Byte) :
    { localAlloc ctx i it data with data := data' } = localAlloc ctx i it data' := rfl

theorem typedStore_local {m : Mach} {ctx : Ctx} {frames : List Frame} {L : List Gen.Allocation}
    (h : Shape m ctx frames (ctx.base ++ L)) (i : Nat) (it : Gen.IntType) (data : List Byte) (v : Int)
    (hgood : GoodSize it.size.bytes) (hL : L[i]? = some (localAlloc ctx i it data))
    (hlen : data.length = it.size.bytes) (hv : IntType.can_represent it v = true)
    (align : Align) (hal : Align.is_aligned align (ctx.addrs.getD i 0) = true) :
    typedStore m (localPtr ctx i) (.Int v) (.Int it) align .None =
      .ok (withMem m (ctx.base ++ L.set i
              (localAlloc ctx i it (scalarBytes it (v % 2 ^ (8 * it.size.bytes)).toNat)))
            ⟨.Store, .None, ctx.addrs.getD i 0, it.size⟩) := by
  have hpos := hgood.pos
  obtain ⟨hi, hLi⟩ := List.getElem?_eq_some_iff.mp hL
  have hblen : (scalarBytes it (v % 2 ^ (8 * it.size.bytes)).toNat).length = it.size.bytes := by
    simp [scalarBytes, leBytes_length]
  have hck : checkValue (.Int v) (.Int it) (some m) = .ok () := checkValue_int hv
  have hne : scalarBytes it (v % 2 ^ (8 * it.size.bytes)).toNat ≠ [] :=
    List.ne_nil_of_length_pos (by omega)
  simp only [typedStore, hck, encode_int it v hgood hv, CM.store, BM.store, hal, BM.check_ptr,
    localPtr, listIndex, h.allocs]
  obtain ⟨signed, size⟩ := it
  have hdrop : data.drop size.bytes = [] := List.drop_eq_nil_of_le (by simp at hlen; omega)
  simp [hne, hi, hLi, Allocation.size, hlen, hblen, writeSubsliceAtIndex, listSet, withMem, hdrop]
  simp [localAlloc, stackAlloc]

/-! ## `bool` locals

A `bool` local is stored like a `u8` local (`u8Ty`: one byte, alignment one);
its byte must be `0` or `1` to decode at `Type::Bool`. -/

theorem layout_bool : Type.layout .Bool = .ok (.Sized u8Ty.size ⟨u8Ty.size.bytes⟩) := rfl

theorem scalarBytes_u8 (bits : Nat) :
    scalarBytes u8Ty bits = [.Init (UInt8.ofNat (bits % 256)) none] := by
  simp [scalarBytes, u8Ty, leBytes]

theorem decode_bool (bits : Nat) (hb : bits < 2) :
    Type.decode .Bool (scalarBytes u8Ty bits) = .ok (some (.Bool (decide (bits = 1)))) := by
  rcases (by omega : bits = 0 ∨ bits = 1) with rfl | rfl <;> rfl

theorem encode_bool (b : Bool) :
    Type.encode .Bool (.Bool b) = .ok (scalarBytes u8Ty (if b then 1 else 0)) := by
  cases b <;> rfl

theorem typedLoad_local_bool {m : Mach} {ctx : Ctx} {frames : List Frame} {L : List Gen.Allocation}
    (h : Shape m ctx frames (ctx.base ++ L)) (i : Nat) (bits : Nat) (hb : bits < 2)
    (hL : L[i]? = some (localAlloc ctx i u8Ty (scalarBytes u8Ty bits)))
    (align : Align) (hal : Align.is_aligned align (ctx.addrs.getD i 0) = true) :
    ∃ m', typedLoad m (localPtr ctx i) .Bool align .None = .ok (.Bool (decide (bits = 1)), m') ∧
      Shape m' ctx frames (ctx.base ++ L) := by
  obtain ⟨hi, hLi⟩ := List.getElem?_eq_some_iff.mp hL
  have hu8 : u8Ty.size.bytes = 1 := rfl
  have hlen : (scalarBytes u8Ty bits).length = u8Ty.size.bytes := by
    simp [scalarBytes, leBytes_length]
  have hset := set_self_of_getElem? L i _ hL
  refine ⟨withMem m (ctx.base ++ L) ⟨.Load, .None, ctx.addrs.getD i 0, u8Ty.size⟩, ?_,
    withMem_shape h _⟩
  simp only [typedLoad, layout_bool, LayoutStrategy.expect_size, CM.load, BM.load, hal,
    BM.check_ptr, localPtr, listIndex, h.allocs]
  simp [hu8, hi, hLi, Allocation.size, hlen, listSet, subsliceWithLength, hset,
    List.take_of_length_le, decode_bool bits hb, checkValue_bool, withMem]

theorem typedLoad_local_bool_uninit {m : Mach} {ctx : Ctx} {frames : List Frame}
    {L : List Gen.Allocation} (h : Shape m ctx frames (ctx.base ++ L)) (i : Nat)
    (hL : L[i]? = some (localAlloc ctx i u8Ty (uninitBytes u8Ty)))
    (align : Align) (hal : Align.is_aligned align (ctx.addrs.getD i 0) = true) :
    ∃ msg, typedLoad m (localPtr ctx i) .Bool align .None = .error (.ub msg) := by
  obtain ⟨hi, hLi⟩ := List.getElem?_eq_some_iff.mp hL
  have hu8 : u8Ty.size.bytes = 1 := rfl
  have hlen : (uninitBytes u8Ty).length = u8Ty.size.bytes := by simp [uninitBytes]
  have hdec : Type.decode .Bool (uninitBytes u8Ty) = .ok none := rfl
  have hset := set_self_of_getElem? L i _ hL
  refine ⟨"load at type but the data in memory violates the language invariant", ?_⟩
  simp only [typedLoad, layout_bool, LayoutStrategy.expect_size, CM.load, BM.load, hal,
    BM.check_ptr, localPtr, listIndex, h.allocs]
  simp [hu8, hi, hLi, Allocation.size, hlen, listSet, subsliceWithLength, hset,
    List.take_of_length_le, hdec, ub]

theorem typedStore_local_bool {m : Mach} {ctx : Ctx} {frames : List Frame} {L : List Gen.Allocation}
    (h : Shape m ctx frames (ctx.base ++ L)) (i : Nat) (data : List Byte) (b : Bool)
    (hL : L[i]? = some (localAlloc ctx i u8Ty data)) (hlen : data.length = u8Ty.size.bytes)
    (align : Align) (hal : Align.is_aligned align (ctx.addrs.getD i 0) = true) :
    typedStore m (localPtr ctx i) (.Bool b) .Bool align .None =
      .ok (withMem m (ctx.base ++ L.set i
              (localAlloc ctx i u8Ty (scalarBytes u8Ty (if b then 1 else 0))))
            ⟨.Store, .None, ctx.addrs.getD i 0, u8Ty.size⟩) := by
  obtain ⟨hi, hLi⟩ := List.getElem?_eq_some_iff.mp hL
  have hu8 : u8Ty.size.bytes = 1 := rfl
  have hck : checkValue (.Bool b) .Bool (some m) = .ok () := rfl
  have hblen : (scalarBytes u8Ty (if b then 1 else 0)).length = u8Ty.size.bytes := by
    simp [scalarBytes, leBytes_length]
  have hne : scalarBytes u8Ty (if b then 1 else 0) ≠ [] :=
    List.ne_nil_of_length_pos (by rw [hblen, hu8]; omega)
  have hdrop : data.drop u8Ty.size.bytes = [] := List.drop_eq_nil_of_le (by omega)
  simp only [typedStore, hck, encode_bool, CM.store, BM.store, hal, BM.check_ptr, localPtr,
    listIndex, h.allocs]
  simp [hne, hi, hLi, Allocation.size, hlen, hblen, writeSubsliceAtIndex, listSet, withMem, hdrop]
  simp [localAlloc, stackAlloc, hu8]

/-! ## `core::cmp::Ordering` locals

An `Ordering` local is stored like a `u8` local (`u8Ty`: one byte, alignment
one), and its byte must be a tag that `orderingTy`'s discriminator accepts:
`255` (`Less`, the `i8` `-1`), `0` (`Equal`), or `1` (`Greater`). The loads and
stores below are stated for any one-byte type `T` whose decoding, checking,
and encoding of the stored byte are known; for `orderingTy` these facts are
computed for each of the three tags. -/

theorem typedLoad_local_byte {m : Mach} {ctx : Ctx} {frames : List Frame} {L : List Gen.Allocation}
    (h : Shape m ctx frames (ctx.base ++ L)) (i : Nat) (T : Gen.Type) (bits : Nat) (v : Val)
    (hlay : Type.layout T = .ok (.Sized u8Ty.size ⟨u8Ty.size.bytes⟩))
    (hdec : Type.decode T (scalarBytes u8Ty bits) = .ok (some v))
    (hck : ∀ {m? : Option Mach}, checkValue v T m? = .ok ())
    (hL : L[i]? = some (localAlloc ctx i u8Ty (scalarBytes u8Ty bits)))
    (align : Align) (hal : Align.is_aligned align (ctx.addrs.getD i 0) = true) :
    ∃ m', typedLoad m (localPtr ctx i) T align .None = .ok (v, m') ∧
      Shape m' ctx frames (ctx.base ++ L) := by
  obtain ⟨hi, hLi⟩ := List.getElem?_eq_some_iff.mp hL
  have hu8 : u8Ty.size.bytes = 1 := rfl
  have hlen : (scalarBytes u8Ty bits).length = u8Ty.size.bytes := by
    simp [scalarBytes, leBytes_length]
  have hset := set_self_of_getElem? L i _ hL
  refine ⟨withMem m (ctx.base ++ L) ⟨.Load, .None, ctx.addrs.getD i 0, u8Ty.size⟩, ?_,
    withMem_shape h _⟩
  simp only [typedLoad, hlay, LayoutStrategy.expect_size, CM.load, BM.load, hal,
    BM.check_ptr, localPtr, listIndex, h.allocs]
  simp [hu8, hi, hLi, Allocation.size, hlen, listSet, subsliceWithLength, hset,
    List.take_of_length_le, hdec, hck, withMem]

theorem typedLoad_local_byte_uninit {m : Mach} {ctx : Ctx} {frames : List Frame}
    {L : List Gen.Allocation} (h : Shape m ctx frames (ctx.base ++ L)) (i : Nat) (T : Gen.Type)
    (hlay : Type.layout T = .ok (.Sized u8Ty.size ⟨u8Ty.size.bytes⟩))
    (hdec : Type.decode T (uninitBytes u8Ty) = .ok none)
    (hL : L[i]? = some (localAlloc ctx i u8Ty (uninitBytes u8Ty)))
    (align : Align) (hal : Align.is_aligned align (ctx.addrs.getD i 0) = true) :
    ∃ msg, typedLoad m (localPtr ctx i) T align .None = .error (.ub msg) := by
  obtain ⟨hi, hLi⟩ := List.getElem?_eq_some_iff.mp hL
  have hu8 : u8Ty.size.bytes = 1 := rfl
  have hlen : (uninitBytes u8Ty).length = u8Ty.size.bytes := by simp [uninitBytes]
  have hset := set_self_of_getElem? L i _ hL
  refine ⟨"load at type but the data in memory violates the language invariant", ?_⟩
  simp only [typedLoad, hlay, LayoutStrategy.expect_size, CM.load, BM.load, hal,
    BM.check_ptr, localPtr, listIndex, h.allocs]
  simp [hu8, hi, hLi, Allocation.size, hlen, listSet, subsliceWithLength, hset,
    List.take_of_length_le, hdec, ub]

theorem typedStore_local_byte {m : Mach} {ctx : Ctx} {frames : List Frame} {L : List Gen.Allocation}
    (h : Shape m ctx frames (ctx.base ++ L)) (i : Nat) (T : Gen.Type) (data : List Byte) (v : Val)
    (bits : Nat) (hck : ∀ {m? : Option Mach}, checkValue v T m? = .ok ())
    (henc : Type.encode T v = .ok (scalarBytes u8Ty bits))
    (hL : L[i]? = some (localAlloc ctx i u8Ty data)) (hlen : data.length = u8Ty.size.bytes)
    (align : Align) (hal : Align.is_aligned align (ctx.addrs.getD i 0) = true) :
    typedStore m (localPtr ctx i) v T align .None =
      .ok (withMem m (ctx.base ++ L.set i (localAlloc ctx i u8Ty (scalarBytes u8Ty bits)))
            ⟨.Store, .None, ctx.addrs.getD i 0, u8Ty.size⟩) := by
  obtain ⟨hi, hLi⟩ := List.getElem?_eq_some_iff.mp hL
  have hu8 : u8Ty.size.bytes = 1 := rfl
  have hblen : (scalarBytes u8Ty bits).length = u8Ty.size.bytes := by
    simp [scalarBytes, leBytes_length]
  have hne : scalarBytes u8Ty bits ≠ [] :=
    List.ne_nil_of_length_pos (by rw [hblen, hu8]; omega)
  have hdrop : data.drop u8Ty.size.bytes = [] := List.drop_eq_nil_of_le (by omega)
  simp only [typedStore, hck, henc, CM.store, BM.store, hal, BM.check_ptr, localPtr,
    listIndex, h.allocs]
  simp [hne, hi, hLi, Allocation.size, hlen, hblen, writeSubsliceAtIndex, listSet, withMem, hdrop]
  simp [localAlloc, stackAlloc, hu8]

theorem layout_ordering : Type.layout orderingTy = .ok (.Sized u8Ty.size ⟨u8Ty.size.bytes⟩) := rfl

/-- `validBits` on every one-byte pattern: exactly the tags `255`, `0`, and
`1` decode at `orderingTy` (computed by the kernel). -/
theorem validBits_ordering_table :
    (List.range 256).all (fun b => validBits orderingTy b == (b == 255 || b == 0 || b == 1)) =
      true := by
  decide +kernel

/-- The bit patterns valid at `orderingTy` are its three tags. -/
theorem validBits_ordering (bits : Nat) :
    ValidBits orderingTy bits ↔ bits = 255 ∨ bits = 0 ∨ bits = 1 := by
  constructor
  · intro h
    have hlt : bits < 256 := by
      have := h.1
      simpa using this
    have hv : validBits orderingTy bits = true := (validBits_iff _ _).mpr h
    have ht := List.all_eq_true.mp validBits_ordering_table bits (List.mem_range.mpr hlt)
    rw [hv] at ht
    simpa [or_assoc] using ht
  · rintro (rfl | rfl | rfl) <;> exact (validBits_iff _ _).mp rfl

theorem decode_ordering_uninit : Type.decode orderingTy (uninitBytes u8Ty) = .ok none := rfl

/-! ## Fragment types

`FragTy T it` says that `T` is a fragment type stored like the integer type
`it`: an integer type of good size is stored as itself, and `bool` and
`core::cmp::Ordering` (`orderingTy`) as `u8`. -/

/-- Fragment types and their storage integer types. -/
inductive FragTy : Gen.Type → Gen.IntType → Prop
  | int (it : Gen.IntType) (h : GoodSize it.size.bytes) : FragTy (.Int it) it
  | bool : FragTy .Bool u8Ty
  | ordering : FragTy orderingTy u8Ty

/-- The fragment types that MiniRust's `BinOp::Rel` compares: integers (by
value) and `bool` (`false < true`); an `Ordering` value is not comparable. -/
inductive RelTy : Gen.Type → Gen.IntType → Prop
  | int (it : Gen.IntType) (h : GoodSize it.size.bytes) : RelTy (.Int it) it
  | bool : RelTy .Bool u8Ty

theorem RelTy.frag {T : Gen.Type} {it : Gen.IntType} (h : RelTy T it) : FragTy T it := by
  cases h with
  | int it h => exact .int it h
  | bool => exact .bool

/-- The MiniRust value that the bit pattern `bits` encodes at fragment type
`T`; for an enum, the value that its little-endian bytes decode to. -/
def valOf : Gen.Type → Nat → Val
  | .Int it, bits => .Int (intFromBits bits it)
  | .Bool, bits => .Bool (decide (bits = 1))
  | T@(.Enum _ _ _ size _), bits =>
    match Type.decode T (scalarBytes ⟨.Unsigned, size⟩ bits) with
    | .ok (some v) => v
    | _ => .Int 0
  | _, _ => .Int 0

theorem decode_ordering {bits : Nat} (hb : ValidBits orderingTy bits) :
    Type.decode orderingTy (scalarBytes u8Ty bits) = .ok (some (valOf orderingTy bits)) := by
  rcases (validBits_ordering bits).mp hb with rfl | rfl | rfl <;> rfl

theorem checkValue_ordering {bits : Nat} {m? : Option Mach} (hb : ValidBits orderingTy bits) :
    checkValue (valOf orderingTy bits) orderingTy m? = .ok () := by
  rcases (validBits_ordering bits).mp hb with rfl | rfl | rfl <;> rfl

theorem encode_ordering {bits : Nat} (hb : ValidBits orderingTy bits) :
    Type.encode orderingTy (valOf orderingTy bits) = .ok (scalarBytes u8Ty bits) := by
  rcases (validBits_ordering bits).mp hb with rfl | rfl | rfl <;> rfl

theorem FragTy.good {T : Gen.Type} {it : Gen.IntType} (h : FragTy T it) : GoodSize it.size.bytes := by
  cases h with
  | int _ h => exact h
  | bool => simp [u8Ty, GoodSize]
  | ordering => simp [u8Ty, GoodSize]

theorem FragTy.layout {T : Gen.Type} {it : Gen.IntType} (h : FragTy T it) :
    Type.layout T = .ok (.Sized it.size ⟨it.size.bytes⟩) := by
  cases h with
  | int _ h => exact layout_eq _ h
  | bool => exact layout_bool
  | ordering => exact layout_ordering

theorem FragTy.tyBytes {T : Gen.Type} {it : Gen.IntType} (h : FragTy T it) :
    tyBytes T = it.size.bytes := by
  cases h <;> rfl

theorem FragTy.validBits_lt {T : Gen.Type} {it : Gen.IntType} (h : FragTy T it) {bits : Nat}
    (hb : ValidBits T bits) : bits < 2 ^ (8 * it.size.bytes) := by
  cases h with
  | int _ _ => exact hb
  | bool => simp [ValidBits] at hb; simp [u8Ty]; omega
  | ordering =>
    rcases (validBits_ordering bits).mp hb with rfl | rfl | rfl <;> simp [u8Ty]

theorem FragTy.not_tuple {d : LocalDecl} {layouts : Layout.LayoutTable}
    (h : FragTy (tyOf d layouts) (itOf d layouts)) :
    intBoolTupleOf d.ty = none := by
  cases ht : intBoolTupleOf d.ty with
  | none => rfl
  | some it =>
    obtain ⟨h1, _⟩ := tyOf_tuple (layouts := layouts) ht
    rw [h1] at h
    cases h

theorem FragTy.not_array {d : LocalDecl} {layouts : Layout.LayoutTable}
    (h : FragTy (tyOf d layouts) (itOf d layouts)) :
    arrayTypeOf d.ty = none := by
  cases ha : arrayTypeOf d.ty with
  | none => rfl
  | some p =>
    obtain ⟨elemIt, count⟩ := p
    obtain ⟨h1, _⟩ := tyOf_array (layouts := layouts) ha
    rw [h1] at h
    cases h

theorem FragTy.not_tupleSpec {d : LocalDecl} {layouts : Layout.LayoutTable}
    (h : FragTy (tyOf d layouts) (itOf d layouts)) :
    tupleTypeOf layouts d.ty = none := by
  cases ht : tupleTypeOf layouts d.ty with
  | none => rfl
  | some p =>
    obtain ⟨fields, size, align⟩ := p
    obtain ⟨h1, _⟩ := tyOf_tupleSpec ht
    rw [h1] at h
    cases h

theorem FragTy.declSlotData {d : LocalDecl} {layouts : Layout.LayoutTable}
    (h : FragTy (tyOf d layouts) (itOf d layouts)) (slot : LocalSlot) :
    declSlotData d slot layouts = slotData (itOf d layouts) slot :=
  declSlotData_of_none h.not_tuple h.not_array h.not_tupleSpec slot

theorem FragTy.unique {T : Gen.Type} {it it' : Gen.IntType} (h : FragTy T it) (h' : FragTy T it') :
    it = it' := by
  cases h <;> cases h' <;> rfl

theorem typedLoad_local_frag {m : Mach} {ctx : Ctx} {frames : List Frame} {L : List Gen.Allocation}
    (h : Shape m ctx frames (ctx.base ++ L)) (i : Nat) {T : Gen.Type} {it : Gen.IntType}
    (hT : FragTy T it) (bits : Nat) (hb : ValidBits T bits)
    (hL : L[i]? = some (localAlloc ctx i it (scalarBytes it bits)))
    (align : Align) (hal : Align.is_aligned align (ctx.addrs.getD i 0) = true) :
    ∃ m', typedLoad m (localPtr ctx i) T align .None = .ok (valOf T bits, m') ∧
      Shape m' ctx frames (ctx.base ++ L) := by
  cases hT with
  | int it hgood => exact typedLoad_local_init h i it bits hgood hb hL align hal
  | bool => exact typedLoad_local_bool h i bits (by simpa [ValidBits] using hb) hL align hal
  | ordering =>
    exact typedLoad_local_byte h i orderingTy bits _ layout_ordering (decode_ordering hb)
      (checkValue_ordering hb) hL align hal

theorem typedLoad_local_frag_uninit {m : Mach} {ctx : Ctx} {frames : List Frame}
    {L : List Gen.Allocation} (h : Shape m ctx frames (ctx.base ++ L)) (i : Nat) {T : Gen.Type}
    {it : Gen.IntType} (hT : FragTy T it) (hL : L[i]? = some (localAlloc ctx i it (uninitBytes it)))
    (align : Align) (hal : Align.is_aligned align (ctx.addrs.getD i 0) = true) :
    ∃ msg, typedLoad m (localPtr ctx i) T align .None = .error (.ub msg) := by
  cases hT with
  | int it hgood => exact typedLoad_local_uninit h i it hgood hL align hal
  | bool => exact typedLoad_local_bool_uninit h i hL align hal
  | ordering =>
    exact typedLoad_local_byte_uninit h i orderingTy layout_ordering decode_ordering_uninit hL
      align hal

theorem typedStore_local_frag {m : Mach} {ctx : Ctx} {frames : List Frame} {L : List Gen.Allocation}
    (h : Shape m ctx frames (ctx.base ++ L)) (i : Nat) {T : Gen.Type} {it : Gen.IntType}
    (hT : FragTy T it) (data : List Byte) (bits : Nat) (hb : ValidBits T bits)
    (hL : L[i]? = some (localAlloc ctx i it data)) (hlen : data.length = it.size.bytes)
    (align : Align) (hal : Align.is_aligned align (ctx.addrs.getD i 0) = true) :
    typedStore m (localPtr ctx i) (valOf T bits) T align .None =
      .ok (withMem m (ctx.base ++ L.set i (localAlloc ctx i it (scalarBytes it bits)))
            ⟨.Store, .None, ctx.addrs.getD i 0, it.size⟩) := by
  cases hT with
  | int it hgood =>
    have hb' : bits < 2 ^ (8 * it.size.bytes) := hb
    have hst := typedStore_local h i it data (intFromBits bits it) hgood hL hlen
      (canRepresent_intFromBits it bits hgood hb') align hal
    have hres : (intFromBits bits it % 2 ^ (8 * it.size.bytes)).toNat = bits := by
      rw [intFromBits_emod bits _ hb']; simp
    rw [hres] at hst
    exact hst
  | bool =>
    have hb' : bits < 2 := by simpa [ValidBits] using hb
    have hst := typedStore_local_bool h i data (decide (bits = 1)) hL hlen align hal
    have hres : (if decide (bits = 1) then 1 else 0) = bits := by
      rcases (by omega : bits = 0 ∨ bits = 1) with rfl | rfl <;> rfl
    rw [hres] at hst
    exact hst
  | ordering =>
    exact typedStore_local_byte h i orderingTy data _ bits (checkValue_ordering hb)
      (encode_ordering hb) hL hlen align hal

/-- All fragment local types (scalar `FragTy`, 2-tuples `intBoolTupleTy it`,
homogeneous arrays, layout-backed tuples/structs, thin raw pointers, and thin
scalar references) and their alignment storage integer types. -/
inductive LocalTy : Gen.Type → Gen.IntType → Prop
  | frag {T : Gen.Type} {it : Gen.IntType} (h : FragTy T it) : LocalTy T it
  | tuple (it : Gen.IntType) (h : GoodSize it.size.bytes) : LocalTy (intBoolTupleTy it) it
  | array (elemIt : Gen.IntType) (count : Nat) (h : GoodSize elemIt.size.bytes) :
      LocalTy (.Array (.Int elemIt) (Int.ofNat count)) elemIt
  | tupleSpec (fields : List (Nat × TupleSpec)) (size align : Nat)
      (hwf : (TupleSpec.tuple fields size align).wf = true) :
      LocalTy ((TupleSpec.tuple fields size align).toMiniRustTy) ⟨.Unsigned, ⟨align⟩⟩
  | rawPtr : LocalTy thinRawPtrTy usizeIt
  | refPtr (mutbl : MirAst.Mutability) (it : Gen.IntType) (hgood : GoodSize it.size.bytes) :
      LocalTy (refTy mutbl it) usizeIt

theorem refPointeeOf_good {t : MirAst.Ty} {mutbl : MirAst.Mutability} {it : Gen.IntType}
    (h : refPointeeOf t = some (mutbl, it)) : GoodSize it.size.bytes := by
  unfold refPointeeOf at h
  cases hk : t.kind with
  | ref pointee mutbl' =>
    simp only [hk, Option.map_eq_some_iff] at h
    obtain ⟨⟨s, n⟩, hit, hEq⟩ := h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hEq
    exact intTyBytes_good hit
  | _ => simp [hk] at h

theorem LocalTy.good {T : Gen.Type} {it : Gen.IntType} (h : LocalTy T it) :
    GoodSize it.size.bytes := by
  cases h with
  | frag hf => exact hf.good
  | tuple _ hg => exact hg
  | array _ _ hg => exact hg
  | tupleSpec fields size align hwf =>
    simp only [TupleSpec.wf, Bool.and_eq_true] at hwf
    exact (goodAlignBytes_iff align).mp hwf.1.1.1
  | rawPtr => simp [GoodSize, usizeIt]
  | refPtr _ _ _ => simp [GoodSize, usizeIt]

theorem LocalTy.layout {T : Gen.Type} {it : Gen.IntType} (h : LocalTy T it) :
    Type.layout T = .ok (.Sized ⟨tyBytes T⟩ ⟨it.size.bytes⟩) := by
  cases h with
  | frag hf => rw [hf.tyBytes]; exact hf.layout
  | tuple _ hg => exact layout_tuple it hg
  | array _ count hg =>
    simpa [tyBytes] using layout_array_eq it count hg
  | tupleSpec fields size align hwf =>
    simpa [TupleSpec.toMiniRustTy, TupleSpec.size, TupleSpec.align, tyBytes] using
      layout_tupleSpec (.tuple fields size align) hwf
  | rawPtr => rfl
  | refPtr _ _ _ => rfl

/-- Storage integer type associated with a `LocalTy` type `T`. -/
def storageIt : Gen.Type → Gen.IntType
  | .Int it => it
  | .Tuple fields head _ =>
    if fields.length = 2 then
      match fields with
      | [(_, .Int it), (_, .Bool)] => it
      | _ => ⟨.Unsigned, ⟨head.align.bytes⟩⟩
    else
      ⟨.Unsigned, ⟨head.align.bytes⟩⟩
  | .Array (.Int elemIt) _ => elemIt
  | .Ptr (.Raw .None) => usizeIt
  | .Ptr (.Ref _ _) => usizeIt
  | _ => u8Ty

theorem TupleSpec.toMiniRustTy_ne_bool (s : TupleSpec) : s.toMiniRustTy ≠ .Bool := by
  cases s <;> simp [TupleSpec.toMiniRustTy]

theorem LocalTy.storageIt_eq {T : Gen.Type} {it : Gen.IntType} (h : LocalTy T it) :
    storageIt T = it := by
  cases h with
  | frag hf => cases hf <;> rfl
  | tuple _ _ => rfl
  | array _ _ _ => rfl
  | tupleSpec fields size align _ =>
    cases fields with
    | nil => rfl
    | cons f0 fs =>
      cases fs with
      | nil => rfl
      | cons f1 fs' =>
        cases fs' with
        | cons _ _ => rfl
        | nil =>
          have hne := TupleSpec.toMiniRustTy_ne_bool f1.2
          cases hf1 : f1.2.toMiniRustTy <;> simp_all [TupleSpec.toMiniRustTy, TupleSpec.fieldsToMiniRust, storageIt]
  | rawPtr => rfl
  | refPtr _ _ _ => rfl

theorem LocalTy.unique {T : Gen.Type} {it it' : Gen.IntType} (h : LocalTy T it)
    (h' : LocalTy T it') : it = it' := by
  rw [← h.storageIt_eq, h'.storageIt_eq]

theorem LocalTy.of_validBits {T : Gen.Type} {it : Gen.IntType} (h : LocalTy T it) {bits : Nat}
    (hb : ValidBits T bits) : FragTy T it := by
  cases h with
  | frag hf => exact hf
  | tuple _ _ => simp [intBoolTupleTy, ValidBits] at hb
  | array _ _ _ => simp [ValidBits] at hb
  | tupleSpec _ _ _ _ => simp [TupleSpec.toMiniRustTy, ValidBits] at hb
  | rawPtr => simp [thinRawPtrTy, ValidBits] at hb
  | refPtr _ _ _ => simp [refTy, ValidBits] at hb

/-- A scalar-family fragment local's declared MiniRust type is a `LocalTy`
aligned like `itOf d layouts`. -/
theorem localTy_of_decl {d : LocalDecl} {layouts : Layout.LayoutTable}
    (h : scalarTypeOf d.ty = some (tyOf d layouts)) :
    LocalTy (tyOf d layouts) (itOf d layouts) := by
  rcases scalarTypeOf_cases h with ⟨hb, _⟩ | ⟨it, hit, _⟩ | ⟨ho, _⟩ | ⟨it, ht, _⟩
  · obtain ⟨h1, h2⟩ := tyOf_bool (layouts := layouts) hb; rw [h1, h2]; exact .frag .bool
  · obtain ⟨h1, h2⟩ := tyOf_int (layouts := layouts) hit; rw [h1, h2]; exact .frag (.int it (intTypeOf_good hit))
  · obtain ⟨h1, h2⟩ := tyOf_ordering (layouts := layouts) ho; rw [h1, h2]; exact .frag .ordering
  · obtain ⟨h1, h2⟩ := tyOf_tuple (layouts := layouts) ht; rw [h1, h2]; exact .tuple it (intBoolTupleOf_good ht)

/-- Any well-formed fragment local declaration has a `LocalTy` aligned like
`itOf d layouts`. -/
theorem localTy_of_declOk {d : LocalDecl} {layouts : Layout.LayoutTable}
    (hdok : localDeclOk layouts d = true) :
    LocalTy (tyOf d layouts) (itOf d layouts) := by
  unfold localDeclOk at hdok
  cases hs : scalarTypeOf d.ty with
  | some T =>
    have hT : tyOf d layouts = T := tyOf_of_scalarTypeOf hs
    exact localTy_of_decl (hT ▸ hs)
  | none =>
    simp only [hs, Option.isSome_none, Bool.false_or] at hdok
    cases ha : arrayTypeOf d.ty with
    | some p =>
      obtain ⟨elemIt, count⟩ := p
      obtain ⟨h1, h2⟩ := tyOf_array (layouts := layouts) ha
      rw [h1, h2]
      exact .array elemIt count (arrayTypeOf_good ha)
    | none =>
      simp only [ha] at hdok
      cases ht : tupleTypeOf layouts d.ty with
      | none =>
        simp only [ht, Bool.or_false, Bool.and_eq_true] at hdok
        obtain ⟨h1, h2⟩ := tyOf_isPtrTy (layouts := layouts) hdok.1
        rw [h1, h2]
        rcases declPtrTy_cases d.ty with hraw | ⟨mutbl, it, href, h1'⟩
        · rw [hraw]; exact .rawPtr
        · rw [h1']; exact .refPtr mutbl it (refPointeeOf_good href)
      | some p =>
        obtain ⟨fields, size, align⟩ := p
        simp only [ht] at hdok
        have hnp : isPtrTy d.ty = false := isPtrTy_false_of_tupleTypeOf ht
        simp only [hnp] at hdok
        obtain ⟨h1, h2⟩ := tyOf_tupleSpec ht
        rw [h1, h2]
        exact .tupleSpec fields size align hdok

theorem declSlotData_of_isPtrTy {d : LocalDecl} {layouts : Layout.LayoutTable}
    (hp : isPtrTy d.ty = true) (slot : LocalSlot) :
    declSlotData d slot layouts = slotData usizeIt slot := by
  obtain ⟨hib, hb, ho, hi, harr, ha, _⟩ := not_other_of_isPtrTy (layouts := layouts) hp
  obtain ⟨_, h2⟩ := tyOf_isPtrTy (layouts := layouts) hp
  simp [declSlotData, hib, hb, ho, hi, harr, ha, h2]

theorem declSlotData_length {d : LocalDecl} {layouts : Layout.LayoutTable}
    (hd : scalarTypeOf d.ty = some (tyOf d layouts))
    (slot : LocalSlot) : (declSlotData d slot layouts).length = tyBytes (tyOf d layouts) := by
  rcases scalarTypeOf_cases hd with ⟨hb, _⟩ | ⟨it, hit, _⟩ | ⟨ho, _⟩ | ⟨it, ht, _⟩
  · obtain ⟨h1, h2⟩ := tyOf_bool (layouts := layouts) hb
    have hf : FragTy (tyOf d layouts) (itOf d layouts) := by rw [h1, h2]; exact .bool
    rw [hf.declSlotData, slotData_length, hf.tyBytes]
  · obtain ⟨h1, h2⟩ := tyOf_int (layouts := layouts) hit
    have hf : FragTy (tyOf d layouts) (itOf d layouts) := by rw [h1, h2]; exact .int it (intTypeOf_good hit)
    rw [hf.declSlotData, slotData_length, hf.tyBytes]
  · obtain ⟨h1, h2⟩ := tyOf_ordering (layouts := layouts) ho
    have hf : FragTy (tyOf d layouts) (itOf d layouts) := by rw [h1, h2]; exact .ordering
    rw [hf.declSlotData, slotData_length, hf.tyBytes]
  · obtain ⟨h1, _⟩ := tyOf_tuple (layouts := layouts) ht
    rw [declSlotData_of_some ht, h1, tupleSlotData_length it slot (intBoolTupleOf_good ht).pos]
    rfl

theorem declSlotData_length_of_declOk {d : LocalDecl} {layouts : Layout.LayoutTable}
    {slot : LocalSlot} (hdok : localDeclOk layouts d = true)
    (hsl : DeclSlotOk d slot layouts) :
    (declSlotData d slot layouts).length = tyBytes (tyOf d layouts) := by
  unfold localDeclOk at hdok
  cases hs : scalarTypeOf d.ty with
  | some T =>
    have hT : tyOf d layouts = T := tyOf_of_scalarTypeOf hs
    exact declSlotData_length (hT ▸ hs) slot
  | none =>
    simp only [hs, Option.isSome_none, Bool.false_or] at hdok
    unfold DeclSlotOk at hsl
    simp only [hs, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hsl
    cases ha : arrayTypeOf d.ty with
    | some p =>
      obtain ⟨elemIt, count⟩ := p
      simp only [ha] at hsl
      obtain ⟨h1, _⟩ := tyOf_array (layouts := layouts) ha
      rw [declSlotData_of_array ha, h1]
      cases slot with
      | dead => simp [tyBytes]
      | uninit => simp [tyBytes]
      | init v =>
        cases v with
        | aggregate vidx elems =>
          cases vidx with
          | zero =>
            simp only [tyBytes, Int.ofNat_eq_natCast, Int.toNat_natCast]
            rw [flatten_map_length (valBytes elemIt) elemIt.size.bytes elems
              (fun x _ => valBytes_length elemIt x), hsl.1]
          | succ _ => simp at hsl
        | _ => simp at hsl
    | none =>
      simp only [ha] at hdok hsl
      cases ht : tupleTypeOf layouts d.ty with
      | none =>
        simp only [ht, Bool.or_false, Bool.and_eq_true] at hdok
        obtain ⟨h1, _⟩ := tyOf_isPtrTy (layouts := layouts) hdok.1
        rw [declSlotData_of_isPtrTy hdok.1, h1, slotData_length, tyBytes_declPtrTy]
        rfl
      | some p =>
        obtain ⟨fields, size, align⟩ := p
        simp only [ht] at hdok hsl
        obtain ⟨h1, _⟩ := tyOf_tupleSpec ht
        rw [declSlotData_of_tupleSpec ht, h1]
        cases slot with
        | dead => simp [TupleSpec.toMiniRustTy, tyBytes]
        | uninit => simp [TupleSpec.toMiniRustTy, tyBytes]
        | init v =>
          simpa [TupleSpec.toMiniRustTy, tyBytes, TupleSpec.size] using
            TupleSpec.encodeVal_length (.tuple fields size align) v hsl.1

/-! ## `(Int, bool)` 2-tuple locals -/

/-- MiniRust `Value::Tuple` corresponding to bit patterns `(bits, b)` at
`intBoolTupleTy it`. -/
def tupleVal (it : Gen.IntType) (bits b : Nat) : Val :=
  .Tuple [.Int (intFromBits bits it), .Bool (decide (b = 1))]

theorem checkValue_tuple (it : Gen.IntType) (bits b : Nat) (hgood : GoodSize it.size.bytes)
    (hbits : bits < 2 ^ (8 * it.size.bytes)) {m? : Option Mach} :
    checkValue (tupleVal it bits b) (intBoolTupleTy it) m? = .ok () := by
  simp [tupleVal, intBoolTupleTy, checkValue, ensureElseUb, checkFields,
    canRepresent_intFromBits it bits hgood hbits]

theorem encode_tuple (it : Gen.IntType) (bits b : Nat) (hgood : GoodSize it.size.bytes)
    (hbits : bits < 2 ^ (8 * it.size.bytes)) (hb : b < 2) :
    Type.encode (intBoolTupleTy it) (tupleVal it bits b) = .ok (tupleBytes it bits b) := by
  have hpos := hgood.pos
  have henc0 : Type.encodeInt it (.Int (intFromBits bits it)) = .ok (scalarBytes it bits) := by
    have h := encode_int it (intFromBits bits it) hgood (canRepresent_intFromBits it bits hgood hbits)
    have hres0 : (intFromBits bits it % 2 ^ (8 * it.size.bytes)).toNat = bits := by
      rw [intFromBits_emod bits _ hbits]; simp
    rw [hres0] at h
    exact h
  have hb_eq : [Gen.AbstractByte.Init (if b = 1 then 1 else 0) none] = scalarBytes u8Ty b := by
    rcases (by omega : b = 0 ∨ b = 1) with rfl | rfl <;> rfl
  have hlen0 := scalarBytes_length it bits
  have hlen1 : (scalarBytes u8Ty b).length = 1 := scalarBytes_length u8Ty b
  have hle0 : (it.size.bytes : Int) ≤ (it.size.bytes : Int) + it.size.bytes := by omega
  have hle1 : (it.size.bytes : Int) + 1 ≤ (it.size.bytes : Int) + it.size.bytes := by omega
  have htk : (scalarBytes it bits ++ List.replicate it.size.bytes Gen.AbstractByte.Uninit).take it.size.bytes =
      scalarBytes it bits := by
    rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
  have hdr : (scalarBytes it bits ++ List.replicate it.size.bytes Gen.AbstractByte.Uninit).drop (it.size.bytes + 1) =
      List.replicate (it.size.bytes - 1) Gen.AbstractByte.Uninit := by
    rw [List.drop_append, hlen0, List.drop_eq_nil_of_le (by omega), List.nil_append, List.drop_replicate]
    congr 1; omega
  simp [intBoolTupleTy, tupleVal, Type.encode, Type.encodeFields, head_size_and_align_tuple it hgood,
    henc0, hb_eq, writeSubsliceAtIndex, hlen0, hlen1, hle0, hle1, List.drop_replicate, htk, hdr,
    tupleBytes, List.append_assoc]

theorem decode_int_scalarBytes (it : Gen.IntType) (bits : Nat)
    (hbits : bits < 2 ^ (8 * it.size.bytes)) :
    Type.decode (.Int it) (scalarBytes it bits) = .ok (some (.Int (intFromBits bits it))) := by
  obtain ⟨signed, size⟩ := it
  have hlen : (scalarBytes ⟨signed, size⟩ bits).length = size.bytes := by
    simp [scalarBytes, leBytes_length]
  simp [Type.decode, Type.decodeInt, hlen, mapM_data_scalarBytes, x86_64.ENDIANNESS,
    decode_leBytes signed size.bytes bits hbits]

theorem decode_int_uninitBytes (it : Gen.IntType) (hgood : GoodSize it.size.bytes) :
    Type.decode (.Int it) (uninitBytes it) = .ok none := by
  have hpos := hgood.pos
  obtain ⟨signed, size⟩ := it
  have hlen : (uninitBytes ⟨signed, size⟩).length = size.bytes := by simp [uninitBytes]
  simp [Type.decode, Type.decodeInt, hlen, mapM_data_uninitBytes _ hpos]

theorem take_tupleBytes_field0 (it : Gen.IntType) (bits b : Nat) :
    (tupleBytes it bits b).take it.size.bytes = scalarBytes it bits := by
  have hlen0 := scalarBytes_length it bits
  rw [tupleBytes, List.append_assoc, List.take_append_of_le_length (by omega),
    List.take_of_length_le (by omega)]

theorem drop_take_tupleBytes_field1 (it : Gen.IntType) (bits b : Nat) :
    ((tupleBytes it bits b).drop it.size.bytes).take 1 = scalarBytes u8Ty b := by
  have hlen0 := scalarBytes_length it bits
  have hlen1 : (scalarBytes u8Ty b).length = 1 := scalarBytes_length u8Ty b
  rw [tupleBytes, List.append_assoc, List.drop_append_of_le_length (by omega),
    List.drop_eq_nil_of_le (by omega), List.nil_append, List.take_append_of_le_length (by omega),
    List.take_of_length_le (by omega)]

theorem decode_tuple (it : Gen.IntType) (bits b : Nat) (hgood : GoodSize it.size.bytes)
    (hbits : bits < 2 ^ (8 * it.size.bytes)) (hb : b < 2) :
    Type.decode (intBoolTupleTy it) (tupleBytes it bits b) = .ok (some (tupleVal it bits b)) := by
  have hpos := hgood.pos
  have hpos1 : 1 ≤ it.size.bytes := hpos
  have hlen := tupleBytes_length it bits b hpos
  have ht0 := take_tupleBytes_field0 it bits b
  have ht1 := drop_take_tupleBytes_field1 it bits b
  have hle0 : (it.size.bytes : Int) ≤ (it.size.bytes : Int) + it.size.bytes := by omega
  have hu8 : u8Ty.size.bytes = 1 := rfl
  rw [intBoolTupleTy, Type.decode]
  simp [Type.decodeFields, head_size_and_align_tuple it hgood,
    hlen, layout_eq it hgood, layout_bool, LayoutStrategy.expect_size, subsliceWithLength,
    hle0, hu8, hpos1, ht0, ht1, decode_int_scalarBytes it bits hbits, decode_bool b hb, tupleVal]

theorem decode_tuple_uninit (it : Gen.IntType) (hgood : GoodSize it.size.bytes) :
    Type.decode (intBoolTupleTy it) (List.replicate (it.size.bytes + it.size.bytes) .Uninit) =
      .ok none := by
  have hpos := hgood.pos
  have hmin : min it.size.bytes (it.size.bytes + it.size.bytes) = it.size.bytes :=
    Nat.min_eq_left (by omega)
  have hle0 : (it.size.bytes : Int) ≤ (it.size.bytes : Int) + it.size.bytes := by omega
  have hdec0 := decode_int_uninitBytes it hgood
  rw [uninitBytes] at hdec0
  rw [intBoolTupleTy, Type.decode]
  simp [Type.decodeFields, head_size_and_align_tuple it hgood,
    layout_eq it hgood, LayoutStrategy.expect_size, subsliceWithLength, hle0, hmin, hdec0]

theorem typedLoad_local_tuple {m : Mach} {ctx : Ctx} {frames : List Frame} {L : List Gen.Allocation}
    (h : Shape m ctx frames (ctx.base ++ L)) (i : Nat) (it : Gen.IntType)
    (hgood : GoodSize it.size.bytes) (bits b : Nat) (hbits : bits < 2 ^ (8 * it.size.bytes))
    (hb : b < 2) (hL : L[i]? = some (localAlloc ctx i it (tupleBytes it bits b)))
    (align : Align) (hal : Align.is_aligned align (ctx.addrs.getD i 0) = true) :
    ∃ m', typedLoad m (localPtr ctx i) (intBoolTupleTy it) align .None =
        .ok (tupleVal it bits b, m') ∧
      Shape m' ctx frames (ctx.base ++ L) := by
  have hpos := hgood.pos
  obtain ⟨hi, hLi⟩ := List.getElem?_eq_some_iff.mp hL
  have hlen := tupleBytes_length it bits b hpos
  have hset := set_self_of_getElem? L i _ hL
  refine ⟨withMem m (ctx.base ++ L)
      ⟨.Load, .None, ctx.addrs.getD i 0, ⟨it.size.bytes + it.size.bytes⟩⟩, ?_, withMem_shape h _⟩
  simp only [typedLoad, layout_tuple it hgood, LayoutStrategy.expect_size, CM.load, BM.load, hal,
    BM.check_ptr, localPtr, listIndex, h.allocs]
  simp [Nat.ne_of_gt hpos, hi, hLi, Allocation.size, hlen, listSet, subsliceWithLength, hset,
    List.take_of_length_le, decode_tuple it bits b hgood hbits hb,
    checkValue_tuple it bits b hgood hbits, withMem]

theorem typedLoad_local_tuple_uninit {m : Mach} {ctx : Ctx} {frames : List Frame}
    {L : List Gen.Allocation} (h : Shape m ctx frames (ctx.base ++ L)) (i : Nat) (it : Gen.IntType)
    (hgood : GoodSize it.size.bytes)
    (hL : L[i]? = some (localAlloc ctx i it (List.replicate (it.size.bytes + it.size.bytes) .Uninit)))
    (align : Align) (hal : Align.is_aligned align (ctx.addrs.getD i 0) = true) :
    ∃ msg, typedLoad m (localPtr ctx i) (intBoolTupleTy it) align .None = .error (.ub msg) := by
  have hpos := hgood.pos
  obtain ⟨hi, hLi⟩ := List.getElem?_eq_some_iff.mp hL
  have hset := set_self_of_getElem? L i _ hL
  refine ⟨"load at type but the data in memory violates the language invariant", ?_⟩
  simp only [typedLoad, layout_tuple it hgood, LayoutStrategy.expect_size, CM.load, BM.load, hal,
    BM.check_ptr, localPtr, listIndex, h.allocs]
  simp [Nat.ne_of_gt hpos, hi, hLi, Allocation.size, listSet, subsliceWithLength, hset,
    List.take_of_length_le, decode_tuple_uninit it hgood, ub]

theorem typedStore_local_tuple {m : Mach} {ctx : Ctx} {frames : List Frame} {L : List Gen.Allocation}
    (h : Shape m ctx frames (ctx.base ++ L)) (i : Nat) (it : Gen.IntType)
    (hgood : GoodSize it.size.bytes) (data : List Byte) (bits b : Nat)
    (hbits : bits < 2 ^ (8 * it.size.bytes)) (hb : b < 2)
    (hL : L[i]? = some (localAlloc ctx i it data)) (hlen : data.length = it.size.bytes + it.size.bytes)
    (align : Align) (hal : Align.is_aligned align (ctx.addrs.getD i 0) = true) :
    typedStore m (localPtr ctx i) (tupleVal it bits b) (intBoolTupleTy it) align .None =
      .ok (withMem m (ctx.base ++ L.set i (localAlloc ctx i it (tupleBytes it bits b)))
            ⟨.Store, .None, ctx.addrs.getD i 0, ⟨it.size.bytes + it.size.bytes⟩⟩) := by
  have hpos := hgood.pos
  obtain ⟨hi, hLi⟩ := List.getElem?_eq_some_iff.mp hL
  have hblen := tupleBytes_length it bits b hpos
  have hck : checkValue (tupleVal it bits b) (intBoolTupleTy it) (some m) = .ok () :=
    checkValue_tuple it bits b hgood hbits
  have henc := encode_tuple it bits b hgood hbits hb
  have hne : tupleBytes it bits b ≠ [] := List.ne_nil_of_length_pos (by omega)
  have hdrop : data.drop (it.size.bytes + it.size.bytes) = [] := List.drop_eq_nil_of_le (by omega)
  simp only [typedStore, hck, henc, CM.store, BM.store, hal, BM.check_ptr, localPtr,
    listIndex, h.allocs]
  simp [hne, hi, hLi, Allocation.size, hlen, hblen, writeSubsliceAtIndex, listSet, withMem, hdrop,
    localAlloc, stackAlloc]

/-- MiniRust `Value` corresponding to an Anneal `Value` of fragment local type `T`. -/
def valOfValue (T : Gen.Type) : Value → Val
  | .scalar sc => valOf T sc.bits
  | .aggregate 0 [.scalar sc0, .scalar sc1] =>
    match tupleIntOfTy T with
    | some it => tupleVal it sc0.bits sc1.bits
    | none => .Int 0
  | _ => .Int 0

theorem typedLoad_local_localTy {m : Mach} {ctx : Ctx} {frames : List Frame} {L : List Gen.Allocation}
    {layouts : Layout.LayoutTable}
    (h : Shape m ctx frames (ctx.base ++ L)) (i : Nat) (d : LocalDecl)
    (hd : scalarTypeOf d.ty = some (tyOf d layouts)) (v : Value)
    (hv : SlotOk (tyOf d layouts) (.init v))
    (hL : L[i]? = some (localAlloc ctx i (itOf d layouts) (declSlotData d (.init v) layouts)))
    (align : Align) (hal : Align.is_aligned align (ctx.addrs.getD i 0) = true) :
    ∃ m', typedLoad m (localPtr ctx i) (tyOf d layouts) align .None =
        .ok (valOfValue (tyOf d layouts) v, m') ∧
      Shape m' ctx frames (ctx.base ++ L) := by
  rcases scalarTypeOf_cases hd with ⟨hb, _⟩ | ⟨it, hit, _⟩ | ⟨ho, _⟩ | ⟨it, ht, _⟩
  · obtain ⟨h1, h2⟩ := tyOf_bool (layouts := layouts) hb
    have hf : FragTy (tyOf d layouts) (itOf d layouts) := by rw [h1, h2]; exact .bool
    rw [hf.declSlotData] at hL
    match v, hv with
    | .scalar sc, ⟨_, hvb⟩ =>
      exact typedLoad_local_frag h i hf sc.bits hvb hL align hal
    | .aggregate 0 [.scalar sc0, .scalar sc1], ⟨_, hty, _⟩ =>
      rw [h1] at hty; simp at hty
  · obtain ⟨h1, h2⟩ := tyOf_int (layouts := layouts) hit
    have hf : FragTy (tyOf d layouts) (itOf d layouts) := by rw [h1, h2]; exact .int it (intTypeOf_good hit)
    rw [hf.declSlotData] at hL
    match v, hv with
    | .scalar sc, ⟨_, hvb⟩ =>
      exact typedLoad_local_frag h i hf sc.bits hvb hL align hal
    | .aggregate 0 [.scalar sc0, .scalar sc1], ⟨_, hty, _⟩ =>
      rw [h1] at hty; simp at hty
  · obtain ⟨h1, h2⟩ := tyOf_ordering (layouts := layouts) ho
    have hf : FragTy (tyOf d layouts) (itOf d layouts) := by rw [h1, h2]; exact .ordering
    rw [hf.declSlotData] at hL
    match v, hv with
    | .scalar sc, ⟨_, hvb⟩ =>
      exact typedLoad_local_frag h i hf sc.bits hvb hL align hal
    | .aggregate 0 [.scalar sc0, .scalar sc1], ⟨_, hty, _⟩ =>
      rw [h1] at hty; simp at hty
  · obtain ⟨h1, h2⟩ := tyOf_tuple (layouts := layouts) ht
    rw [declSlotData_of_some ht] at hL
    match v, hv with
    | .scalar sc, ⟨_, hvb⟩ =>
      rw [h1] at hvb; simp [intBoolTupleTy, ValidBits] at hvb
    | .aggregate 0 [.scalar sc0, .scalar sc1], ⟨it'', hty, _, hb0, _, hb1⟩ =>
      rw [h1, tupleIntOfTy_intBoolTupleTy, Option.some.injEq] at hty
      subst hty
      rw [h2] at hL
      rw [h1]
      simpa [valOfValue, tupleSlotData] using typedLoad_local_tuple h i it (intBoolTupleOf_good ht)
        sc0.bits sc1.bits hb0 hb1 hL align hal

theorem typedLoad_local_localTy_uninit {m : Mach} {ctx : Ctx} {frames : List Frame}
    {L : List Gen.Allocation} {layouts : Layout.LayoutTable}
    (h : Shape m ctx frames (ctx.base ++ L)) (i : Nat) (d : LocalDecl)
    (hd : scalarTypeOf d.ty = some (tyOf d layouts))
    (hL : L[i]? = some (localAlloc ctx i (itOf d layouts) (declSlotData d .uninit layouts)))
    (align : Align) (hal : Align.is_aligned align (ctx.addrs.getD i 0) = true) :
    ∃ msg, typedLoad m (localPtr ctx i) (tyOf d layouts) align .None = .error (.ub msg) := by
  rcases scalarTypeOf_cases hd with ⟨hb, _⟩ | ⟨it, hit, _⟩ | ⟨ho, _⟩ | ⟨it, ht, _⟩
  · obtain ⟨h1, h2⟩ := tyOf_bool (layouts := layouts) hb
    have hfrag : FragTy (tyOf d layouts) (itOf d layouts) := by rw [h1, h2]; exact .bool
    rw [hfrag.declSlotData] at hL
    exact typedLoad_local_frag_uninit h i hfrag hL align hal
  · obtain ⟨h1, h2⟩ := tyOf_int (layouts := layouts) hit
    have hfrag : FragTy (tyOf d layouts) (itOf d layouts) := by rw [h1, h2]; exact .int it (intTypeOf_good hit)
    rw [hfrag.declSlotData] at hL
    exact typedLoad_local_frag_uninit h i hfrag hL align hal
  · obtain ⟨h1, h2⟩ := tyOf_ordering (layouts := layouts) ho
    have hfrag : FragTy (tyOf d layouts) (itOf d layouts) := by rw [h1, h2]; exact .ordering
    rw [hfrag.declSlotData] at hL
    exact typedLoad_local_frag_uninit h i hfrag hL align hal
  · obtain ⟨h1, h2⟩ := tyOf_tuple (layouts := layouts) ht
    rw [declSlotData_of_some ht, h2] at hL
    simp only [tupleSlotData] at hL
    rw [h1]
    exact typedLoad_local_tuple_uninit h i it (intBoolTupleOf_good ht) hL align hal

/-! ## Places of the callee's locals -/

/-- `Machine::eval_place` on a local of a callee frame with locals map `lm`:
the local's pointer if it is live, and UB for a dead local. -/
theorem evalPlace_localL {m : Mach} {ctx : Ctx} {f : Gen.Function} {lm : Map Gen.LocalName Ptr}
    {blk stmt : Nat} {allocs : List Gen.Allocation}
    (h : Shape m ctx [ctx.caller, calleeFrameL f ctx lm blk stmt] allocs) (i : Nat)
    (T : Gen.Type) (hT : mapGet f.locals (localName i) = some T) :
    evalPlace m (.Local (localName i)) =
      match mapGet lm (localName i) with
      | none => .error (.ub "access to a dead local")
      | some p => .ok (({ ptr := { thin_pointer := p, metadata := none }, aligned := true }, T), m) := by
  simp only [evalPlace, curFrame_eq h, mapIndex, calleeFrameL, hT, ok_bind]
  cases mapGet lm (localName i) <;> rfl

theorem evalPlace_local_some {m : Mach} {ctx : Ctx} {f : Gen.Function}
    {lm : Map Gen.LocalName Ptr} {blk stmt : Nat} {allocs : List Gen.Allocation}
    (h : Shape m ctx [ctx.caller, calleeFrameL f ctx lm blk stmt] allocs) (i : Nat)
    (T : Gen.Type) (hT : mapGet f.locals (localName i) = some T) (p : Ptr)
    (hp : mapGet lm (localName i) = some p) :
    evalPlace m (.Local (localName i)) =
      .ok (({ ptr := { thin_pointer := p, metadata := none }, aligned := true }, T), m) := by
  rw [evalPlace_localL h i T hT, hp]

theorem evalPlace_local_none {m : Mach} {ctx : Ctx} {f : Gen.Function}
    {lm : Map Gen.LocalName Ptr} {blk stmt : Nat} {allocs : List Gen.Allocation}
    (h : Shape m ctx [ctx.caller, calleeFrameL f ctx lm blk stmt] allocs) (i : Nat)
    (T : Gen.Type) (hT : mapGet f.locals (localName i) = some T)
    (hp : mapGet lm (localName i) = none) :
    evalPlace m (.Local (localName i)) = .error (.ub "access to a dead local") := by
  rw [evalPlace_localL h i T hT, hp]

/-- A field projection of a dead local is UB too: `eval_place` evaluates the
root first. -/
theorem evalPlace_field_none {m : Mach} {ctx : Ctx} {f : Gen.Function}
    {lm : Map Gen.LocalName Ptr} {blk stmt : Nat} {allocs : List Gen.Allocation}
    (h : Shape m ctx [ctx.caller, calleeFrameL f ctx lm blk stmt] allocs) (i : Nat)
    (T : Gen.Type) (hT : mapGet f.locals (localName i) = some T)
    (hp : mapGet lm (localName i) = none) (fld : Int) :
    evalPlace m (.Field (.Local (localName i)) fld) = .error (.ub "access to a dead local") := by
  rw [evalPlace]
  simp [evalPlace_local_none h i T hT hp]

theorem evalPlace_fieldPath_error {m : Mach} {rootPe pe : Gen.PlaceExpr} {projs : List ProjectionElem}
    {msg : String} (herr : evalPlace m rootPe = .error (.ub msg))
    (hpe : translateFieldPlace rootPe projs = some pe) :
    evalPlace m pe = .error (.ub msg) := by
  induction projs generalizing rootPe with
  | nil =>
    simp [translateFieldPlace] at hpe
    subst hpe
    exact herr
  | cons pr rest ih =>
    cases pr with
    | field idx fieldTy =>
      simp only [translateFieldPlace] at hpe
      have hstep : evalPlace m (.Field rootPe (idx : Int)) = .error (.ub msg) := by
        rw [evalPlace]; simp [herr]
      exact ih hstep hpe
    | _ => simp [translateFieldPlace] at hpe

theorem evalPlace_index_root_error {m : Mach} {rootPe : Gen.PlaceExpr} {idxExpr : Gen.ValueExpr}
    {msg : String} (herr : evalPlace m rootPe = .error (.ub msg)) :
    evalPlace m (.Index rootPe idxExpr) = .error (.ub msg) := by
  rw [evalPlace]
  simp [herr]

/-- Pointer to field 1 (offset `it.size.bytes`) of an `(it, bool)` tuple
local whose pointer is `p`. -/
def field1Ptr (p : Ptr) (it : Gen.IntType) : Ptr :=
  { addr := p.addr + it.size.bytes, provenance := p.provenance }

/-- Pointer to field 1 (offset `it.size.bytes`) of an `(it, bool)` tuple local `_i`. -/
def localField1Ptr (ctx : Ctx) (i : Nat) (it : Gen.IntType) : Ptr :=
  { addr := ctx.addrs.getD i 0 + it.size.bytes,
    provenance := some (⟨((ctx.base.length + i : Nat) : Int)⟩, ()) }

theorem inBounds_unsigned_ptrSize (addr : Int) (h0 : 0 ≤ addr) (hlt : addr < 2 ^ 64) :
    inBounds addr .Unsigned x86_64.PTR_SIZE = true := by
  have hb : (2 : Int) ^ Size.bits x86_64.PTR_SIZE = 2 ^ 64 := rfl
  simp only [inBounds, hb, decide_eq_true_eq, Bool.and_eq_true]
  exact ⟨h0, hlt⟩

theorem inBounds_goodSize_ptrSize (it : Gen.IntType) (hgood : GoodSize it.size.bytes) :
    inBounds (it.size.bytes : Int) .Signed x86_64.PTR_SIZE = true := by
  rcases hgood with h | h | h | h | h <;> rw [h] <;> decide

theorem evalPlace_field0L {m : Mach} {ctx : Ctx} {f : Gen.Function}
    {lm : Map Gen.LocalName Ptr} {blk stmt : Nat} {allocs : List Gen.Allocation}
    (h : Shape m ctx [ctx.caller, calleeFrameL f ctx lm blk stmt] allocs) (i : Nat)
    (it : Gen.IntType) (hgood : GoodSize it.size.bytes)
    (hT : mapGet f.locals (localName i) = some (intBoolTupleTy it)) (p : Ptr)
    (hp : mapGet lm (localName i) = some p) (haddr : AddrOk p.addr it) :
    evalPlace m (.Field (.Local (localName i)) 0) =
      .ok (({ ptr := { thin_pointer := p, metadata := none }, aligned := true }, .Int it), m) := by
  have hloc := evalPlace_local_some h i (intBoolTupleTy it) hT p hp
  have hin0 : inBounds (0 : Int) .Signed x86_64.PTR_SIZE = true := by decide
  have hinAddr : inBounds p.addr .Unsigned x86_64.PTR_SIZE = true :=
    inBounds_unsigned_ptrSize _ haddr.nonneg (by have := haddr.2.2; omega)
  have hptr : ptrOffsetInbounds m p 0 = .ok p := by
    simp [ptrOffsetInbounds, CM.signed_dereferenceable, BM.signed_dereferenceable,
      BM.dereferenceable, BM.check_ptr, hin0, hinAddr]
  rw [evalPlace]
  simp [hloc, intBoolTupleTy, listIndex, Type.layout, head_size_and_align_tuple it hgood,
    computeSize, LayoutStrategy.compute_size_and_align, hptr, align_eq it hgood,
    LayoutStrategy.is_sized, ThinPointer.widen]

theorem evalPlace_field1L {m : Mach} {ctx : Ctx} {f : Gen.Function}
    {lm : Map Gen.LocalName Ptr} {blk stmt : Nat}
    (h : Shape m ctx [ctx.caller, calleeFrameL f ctx lm blk stmt] m.mem.memory.allocations)
    (i : Nat) (it : Gen.IntType) (hgood : GoodSize it.size.bytes)
    (hT : mapGet f.locals (localName i) = some (intBoolTupleTy it)) (p : Ptr)
    (hp : mapGet lm (localName i) = some p) (k : Nat) (hpk : p.provenance = some (⟨(k : Int)⟩, ()))
    (data : List Byte) (hA : m.mem.memory.allocations[k]? = some (stackAlloc p.addr it data))
    (hlen : data.length = it.size.bytes + it.size.bytes) (haddr : AddrOk p.addr it) :
    evalPlace m (.Field (.Local (localName i)) 1) =
      .ok (({ ptr := { thin_pointer := field1Ptr p it, metadata := none }, aligned := true }, .Bool), m) := by
  have hpos := hgood.pos
  obtain ⟨hkL, hAk⟩ := List.getElem?_eq_some_iff.mp hA
  have hloc := evalPlace_local_some h i (intBoolTupleTy it) hT p hp
  have hbounds : ¬ ((it.size.bytes : Int) + it.size.bytes < it.size.bytes) := by omega
  have hinAddr : inBounds (p.addr + (it.size.bytes : Int)) .Unsigned x86_64.PTR_SIZE = true :=
    inBounds_unsigned_ptrSize _ (by have := haddr.nonneg; omega) haddr.2.2
  have hptr : ptrOffsetInbounds m p (it.size.bytes : Int) = .ok (field1Ptr p it) := by
    simp only [ptrOffsetInbounds, CM.signed_dereferenceable, BM.signed_dereferenceable,
      Int.toNat_natCast, BM.dereferenceable]
    simp [Nat.ne_of_gt hpos, BM.check_ptr, hpk, field1Ptr, listIndex, hkL, hAk, stackAlloc,
      Allocation.size, hlen, hbounds, inBounds_goodSize_ptrSize it hgood, hinAddr]
  have hnotlt : ¬ (it.size.bytes + it.size.bytes < it.size.bytes) := by omega
  rw [evalPlace]
  simp [hloc, intBoolTupleTy, listIndex, Type.layout, head_size_and_align_tuple it hgood,
    computeSize, LayoutStrategy.compute_size_and_align, hnotlt, hptr,
    LayoutStrategy.is_sized, ThinPointer.widen]

/-! ## Allocations at arbitrary positions

The load and store lemmas above describe local `_i` of the callee's initial
frame: allocation `base.length + i` at address `addrs[i]`. `StorageLive`
places a local's allocation anywhere in the allocation list. `focusCtx` reads
allocation `k` of a list `A` as local `0` of a context whose `base` is the
prefix `A.take k` and whose only address is `addr`, so the same lemmas
describe any allocation. -/

/-- The context in which allocation `k` of `A`, at address `addr`, is local
`0`. -/
def focusCtx (ctx : Ctx) (A : List Gen.Allocation) (k : Nat) (addr : Int) : Ctx :=
  { ctx with base := A.take k, addrs := [addr] }

theorem focusCtx_append (ctx : Ctx) (A : List Gen.Allocation) (k : Nat) (addr : Int) :
    (focusCtx ctx A k addr).base ++ A.drop k = A :=
  List.take_append_drop k A

theorem focusCtx_addr (ctx : Ctx) (A : List Gen.Allocation) (k : Nat) (addr : Int) :
    (focusCtx ctx A k addr).addrs.getD 0 0 = addr := rfl

theorem focusCtx_localPtr (ctx : Ctx) (A : List Gen.Allocation) (k : Nat) (hk : k ≤ A.length)
    (p : Ptr) (hp : p.provenance = some (⟨(k : Int)⟩, ())) :
    localPtr (focusCtx ctx A k p.addr) 0 = p := by
  obtain ⟨addr, prov⟩ := p
  simp only at hp
  subst hp
  simp [localPtr, focusCtx, List.length_take, Nat.min_eq_left hk]

theorem focusCtx_localField1Ptr (ctx : Ctx) (A : List Gen.Allocation) (k : Nat)
    (hk : k ≤ A.length) (p : Ptr) (hp : p.provenance = some (⟨(k : Int)⟩, ())) (it : Gen.IntType) :
    localField1Ptr (focusCtx ctx A k p.addr) 0 it = field1Ptr p it := by
  obtain ⟨addr, prov⟩ := p
  simp only at hp
  subst hp
  simp [localField1Ptr, field1Ptr, focusCtx, List.length_take, Nat.min_eq_left hk]

theorem focusCtx_localAlloc (ctx : Ctx) (A : List Gen.Allocation) (k : Nat) (addr : Int)
    (it : Gen.IntType) (data : List Byte) :
    localAlloc (focusCtx ctx A k addr) 0 it data = stackAlloc addr it data := rfl

theorem Shape.toFocus {m : Mach} {ctx : Ctx} {frames : List Frame} {A : List Gen.Allocation}
    (h : Shape m ctx frames A) (k : Nat) (addr : Int) :
    Shape m (focusCtx ctx A k addr) frames ((focusCtx ctx A k addr).base ++ A.drop k) := by
  rw [focusCtx_append]
  exact ⟨h.threads, h.active, h.allocs⟩

theorem Shape.ofFocus {m : Mach} {ctx : Ctx} {frames : List Frame} {A X : List Gen.Allocation}
    {k : Nat} {addr : Int} (h : Shape m (focusCtx ctx A k addr) frames X) : Shape m ctx frames X :=
  ⟨h.threads, h.active, h.allocs⟩

theorem focusCtx_drop_get {A : List Gen.Allocation} {k : Nat} {a : Gen.Allocation}
    (hA : A[k]? = some a) : (A.drop k)[0]? = some a := by
  simp [hA]

theorem focusCtx_set (ctx : Ctx) (A : List Gen.Allocation) (k : Nat) (addr : Int)
    (hk : k < A.length) (x : Gen.Allocation) :
    (focusCtx ctx A k addr).base ++ (A.drop k).set 0 x = A.set k x := by
  apply List.ext_getElem?
  intro j
  simp only [focusCtx]
  by_cases hjk : j < k
  · rw [List.getElem?_append_left (by simp [List.length_take]; omega),
      List.getElem?_set_ne (by omega), List.getElem?_take_of_lt hjk]
  · rw [List.getElem?_append_right (by simp [List.length_take]; omega)]
    have hlen : (A.take k).length = k := by simp [List.length_take]; omega
    rw [hlen]
    by_cases hjk' : j = k
    · subst hjk'
      have h0 : 0 < (A.drop j).length := by simp; omega
      simp [List.getElem?_set_self hk, List.getElem?_set_self h0]
    · rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
      simp [List.getElem?_drop]
      congr 1
      omega

theorem typedLoad_local_tuple_field0 {m : Mach} {ctx : Ctx} {frames : List Frame}
    {L : List Gen.Allocation} (h : Shape m ctx frames (ctx.base ++ L)) (i : Nat) (it : Gen.IntType)
    (hgood : GoodSize it.size.bytes) (bits b : Nat) (hbits : bits < 2 ^ (8 * it.size.bytes))
    (hL : L[i]? = some (localAlloc ctx i it (tupleBytes it bits b)))
    (align : Align) (hal : Align.is_aligned align (ctx.addrs.getD i 0) = true) :
    ∃ m', typedLoad m (localPtr ctx i) (.Int it) align .None =
        .ok (.Int (intFromBits bits it), m') ∧
      Shape m' ctx frames (ctx.base ++ L) := by
  have hpos := hgood.pos
  obtain ⟨hi, hLi⟩ := List.getElem?_eq_some_iff.mp hL
  have hlen := tupleBytes_length it bits b hpos
  have hset := set_self_of_getElem? L i _ hL
  have ht0 := take_tupleBytes_field0 it bits b
  have hbounds : ¬ ((it.size.bytes : Int) + it.size.bytes < it.size.bytes) := by omega
  refine ⟨withMem m (ctx.base ++ L) ⟨.Load, .None, ctx.addrs.getD i 0, it.size⟩, ?_,
    withMem_shape h _⟩
  simp only [typedLoad, layout_eq _ hgood, LayoutStrategy.expect_size, CM.load, BM.load, hal,
    BM.check_ptr, localPtr, listIndex, h.allocs]
  simp [Nat.ne_of_gt hpos, hi, hLi, Allocation.size, hlen, hbounds, listSet,
    subsliceWithLength, hset, ht0, decode_int_scalarBytes it bits hbits,
    checkValue_int (canRepresent_intFromBits it bits hgood hbits), withMem]

theorem typedLoad_local_tuple_field0_uninit {m : Mach} {ctx : Ctx} {frames : List Frame}
    {L : List Gen.Allocation} (h : Shape m ctx frames (ctx.base ++ L)) (i : Nat) (it : Gen.IntType)
    (hgood : GoodSize it.size.bytes)
    (hL : L[i]? = some (localAlloc ctx i it (List.replicate (it.size.bytes + it.size.bytes) .Uninit)))
    (align : Align) (hal : Align.is_aligned align (ctx.addrs.getD i 0) = true) :
    ∃ msg, typedLoad m (localPtr ctx i) (.Int it) align .None = .error (.ub msg) := by
  have hpos := hgood.pos
  obtain ⟨hi, hLi⟩ := List.getElem?_eq_some_iff.mp hL
  have hset := set_self_of_getElem? L i _ hL
  have hmin : min it.size.bytes (it.size.bytes + it.size.bytes) = it.size.bytes :=
    Nat.min_eq_left (by omega)
  have htk0 : (List.replicate (it.size.bytes + it.size.bytes) Gen.AbstractByte.Uninit).take it.size.bytes =
      uninitBytes it := by
    simp [uninitBytes, List.take_replicate, hmin]
  have hbounds : ¬ ((it.size.bytes : Int) + it.size.bytes < it.size.bytes) := by omega
  refine ⟨"load at type but the data in memory violates the language invariant", ?_⟩
  simp only [typedLoad, layout_eq _ hgood, LayoutStrategy.expect_size, CM.load, BM.load, hal,
    BM.check_ptr, localPtr, listIndex, h.allocs]
  simp [Nat.ne_of_gt hpos, hi, hLi, Allocation.size, hbounds, listSet, subsliceWithLength,
    hset, htk0, decode_int_uninitBytes it hgood, ub]

theorem typedLoad_local_tuple_field1 {m : Mach} {ctx : Ctx} {frames : List Frame}
    {L : List Gen.Allocation} (h : Shape m ctx frames (ctx.base ++ L)) (i : Nat) (it : Gen.IntType)
    (hgood : GoodSize it.size.bytes) (bits b : Nat) (hb : b < 2)
    (hL : L[i]? = some (localAlloc ctx i it (tupleBytes it bits b)))
    (align : Align) (hal : Align.is_aligned align (ctx.addrs.getD i 0 + it.size.bytes) = true) :
    ∃ m', typedLoad m (localField1Ptr ctx i it) .Bool align .None =
        .ok (.Bool (decide (b = 1)), m') ∧
      Shape m' ctx frames (ctx.base ++ L) := by
  have hpos := hgood.pos
  have hposI : (1 : Int) ≤ (it.size.bytes : Int) := by omega
  obtain ⟨hi, hLi⟩ := List.getElem?_eq_some_iff.mp hL
  have hlen := tupleBytes_length it bits b hpos
  have hset := set_self_of_getElem? L i _ hL
  have ht1 := drop_take_tupleBytes_field1 it bits b
  have hu8 : u8Ty.size.bytes = 1 := rfl
  have hsub : ctx.addrs[i]?.getD 0 + (it.size.bytes : Int) - ctx.addrs[i]?.getD 0 =
      (it.size.bytes : Int) := by omega
  have hnonneg : ¬ ((it.size.bytes : Int) < 0) := by omega
  refine ⟨withMem m (ctx.base ++ L)
      ⟨.Load, .None, ctx.addrs.getD i 0 + it.size.bytes, u8Ty.size⟩, ?_, withMem_shape h _⟩
  simp only [typedLoad, layout_bool, LayoutStrategy.expect_size, CM.load, BM.load, hal,
    BM.check_ptr, localField1Ptr, listIndex, h.allocs]
  simp [hu8, Nat.ne_of_gt hpos, hposI, hi, hLi, Allocation.size, hlen, hsub, hnonneg,
    Int.toNat_natCast, listSet, subsliceWithLength, hset, ht1,
    decode_bool b hb, checkValue_bool, withMem]

theorem typedLoad_local_tuple_field1_uninit {m : Mach} {ctx : Ctx} {frames : List Frame}
    {L : List Gen.Allocation} (h : Shape m ctx frames (ctx.base ++ L)) (i : Nat) (it : Gen.IntType)
    (hgood : GoodSize it.size.bytes)
    (hL : L[i]? = some (localAlloc ctx i it (List.replicate (it.size.bytes + it.size.bytes) .Uninit)))
    (align : Align) (hal : Align.is_aligned align (ctx.addrs.getD i 0 + it.size.bytes) = true) :
    ∃ msg, typedLoad m (localField1Ptr ctx i it) .Bool align .None = .error (.ub msg) := by
  have hpos := hgood.pos
  have hposI : (1 : Int) ≤ (it.size.bytes : Int) := by omega
  obtain ⟨hi, hLi⟩ := List.getElem?_eq_some_iff.mp hL
  have hset := set_self_of_getElem? L i _ hL
  have hu8 : u8Ty.size.bytes = 1 := rfl
  have hmin1 : min 1 it.size.bytes = 1 := Nat.min_eq_left (by omega)
  have hdec1 : Type.decode .Bool [Gen.AbstractByte.Uninit] = .ok none := rfl
  have hsub : ctx.addrs[i]?.getD 0 + (it.size.bytes : Int) - ctx.addrs[i]?.getD 0 =
      (it.size.bytes : Int) := by omega
  have hnonneg : ¬ ((it.size.bytes : Int) < 0) := by omega
  refine ⟨"load at type but the data in memory violates the language invariant", ?_⟩
  simp only [typedLoad, layout_bool, LayoutStrategy.expect_size, CM.load, BM.load, hal,
    BM.check_ptr, localField1Ptr, listIndex, h.allocs]
  simp [hu8, Nat.ne_of_gt hpos, hposI, hi, hLi, Allocation.size, hsub, hnonneg,
    Int.toNat_natCast, listSet, subsliceWithLength, hset, hmin1, hdec1, ub]

/-! ## Loads and stores through a local's pointer

The lemmas above, through `focusCtx`, for a pointer `p` with provenance `k`
into the allocation list `A` whose allocation `k` is a live stack allocation
at `p.addr`. -/

theorem typedLoad_ptr_frag {m : Mach} {ctx : Ctx} {frames : List Frame} {A : List Gen.Allocation}
    (h : Shape m ctx frames A) (p : Ptr) (k : Nat) (hp : p.provenance = some (⟨(k : Int)⟩, ()))
    {T : Gen.Type} {it : Gen.IntType} (hT : FragTy T it) (bits : Nat) (hb : ValidBits T bits)
    (hA : A[k]? = some (stackAlloc p.addr it (scalarBytes it bits))) :
    ∃ m', typedLoad m p T ⟨1⟩ .None = .ok (valOf T bits, m') ∧ Shape m' ctx frames A := by
  have hk : k < A.length := (List.getElem?_eq_some_iff.mp hA).1
  obtain ⟨m', hm', hs⟩ := typedLoad_local_frag (h.toFocus k p.addr) 0 hT bits hb
    (focusCtx_drop_get hA) ⟨1⟩ (isAligned_one _)
  rw [focusCtx_localPtr ctx A k (Nat.le_of_lt hk) p hp] at hm'
  rw [focusCtx_append] at hs
  exact ⟨m', hm', hs.ofFocus⟩

theorem typedLoad_ptr_frag_uninit {m : Mach} {ctx : Ctx} {frames : List Frame}
    {A : List Gen.Allocation} (h : Shape m ctx frames A) (p : Ptr) (k : Nat)
    (hp : p.provenance = some (⟨(k : Int)⟩, ())) {T : Gen.Type} {it : Gen.IntType}
    (hT : FragTy T it) (hA : A[k]? = some (stackAlloc p.addr it (uninitBytes it))) :
    ∃ msg, typedLoad m p T ⟨1⟩ .None = .error (.ub msg) := by
  have hk : k < A.length := (List.getElem?_eq_some_iff.mp hA).1
  obtain ⟨msg, hmsg⟩ := typedLoad_local_frag_uninit (h.toFocus k p.addr) 0 hT
    (focusCtx_drop_get hA) ⟨1⟩ (isAligned_one _)
  rw [focusCtx_localPtr ctx A k (Nat.le_of_lt hk) p hp] at hmsg
  exact ⟨msg, hmsg⟩

theorem typedStore_ptr_frag {m : Mach} {ctx : Ctx} {frames : List Frame} {A : List Gen.Allocation}
    (h : Shape m ctx frames A) (p : Ptr) (k : Nat) (hp : p.provenance = some (⟨(k : Int)⟩, ()))
    {T : Gen.Type} {it : Gen.IntType} (hT : FragTy T it) (data : List Byte) (bits : Nat)
    (hb : ValidBits T bits) (hA : A[k]? = some (stackAlloc p.addr it data))
    (hlen : data.length = it.size.bytes) :
    typedStore m p (valOf T bits) T ⟨1⟩ .None =
      .ok (withMem m (A.set k (stackAlloc p.addr it (scalarBytes it bits)))
            ⟨.Store, .None, p.addr, it.size⟩) := by
  have hk : k < A.length := (List.getElem?_eq_some_iff.mp hA).1
  have hst := typedStore_local_frag (h.toFocus k p.addr) 0 hT data bits hb (focusCtx_drop_get hA)
    hlen ⟨1⟩ (isAligned_one _)
  rw [focusCtx_localPtr ctx A k (Nat.le_of_lt hk) p hp, focusCtx_localAlloc, focusCtx_set ctx A k p.addr hk]
    at hst
  exact hst

theorem typedLoad_ptr_tuple {m : Mach} {ctx : Ctx} {frames : List Frame} {A : List Gen.Allocation}
    (h : Shape m ctx frames A) (p : Ptr) (k : Nat) (hp : p.provenance = some (⟨(k : Int)⟩, ()))
    (it : Gen.IntType) (hgood : GoodSize it.size.bytes) (bits b : Nat)
    (hbits : bits < 2 ^ (8 * it.size.bytes)) (hb : b < 2)
    (hA : A[k]? = some (stackAlloc p.addr it (tupleBytes it bits b))) :
    ∃ m', typedLoad m p (intBoolTupleTy it) ⟨1⟩ .None = .ok (tupleVal it bits b, m') ∧
      Shape m' ctx frames A := by
  have hk : k < A.length := (List.getElem?_eq_some_iff.mp hA).1
  obtain ⟨m', hm', hs⟩ := typedLoad_local_tuple (h.toFocus k p.addr) 0 it hgood bits b hbits hb
    (focusCtx_drop_get hA) ⟨1⟩ (isAligned_one _)
  rw [focusCtx_localPtr ctx A k (Nat.le_of_lt hk) p hp] at hm'
  rw [focusCtx_append] at hs
  exact ⟨m', hm', hs.ofFocus⟩

theorem typedLoad_ptr_tuple_uninit {m : Mach} {ctx : Ctx} {frames : List Frame}
    {A : List Gen.Allocation} (h : Shape m ctx frames A) (p : Ptr) (k : Nat)
    (hp : p.provenance = some (⟨(k : Int)⟩, ())) (it : Gen.IntType) (hgood : GoodSize it.size.bytes)
    (hA : A[k]? = some (stackAlloc p.addr it (List.replicate (it.size.bytes + it.size.bytes) .Uninit))) :
    ∃ msg, typedLoad m p (intBoolTupleTy it) ⟨1⟩ .None = .error (.ub msg) := by
  have hk : k < A.length := (List.getElem?_eq_some_iff.mp hA).1
  obtain ⟨msg, hmsg⟩ := typedLoad_local_tuple_uninit (h.toFocus k p.addr) 0 it hgood
    (focusCtx_drop_get hA) ⟨1⟩ (isAligned_one _)
  rw [focusCtx_localPtr ctx A k (Nat.le_of_lt hk) p hp] at hmsg
  exact ⟨msg, hmsg⟩

theorem typedStore_ptr_tuple {m : Mach} {ctx : Ctx} {frames : List Frame} {A : List Gen.Allocation}
    (h : Shape m ctx frames A) (p : Ptr) (k : Nat) (hp : p.provenance = some (⟨(k : Int)⟩, ()))
    (it : Gen.IntType) (hgood : GoodSize it.size.bytes) (data : List Byte) (bits b : Nat)
    (hbits : bits < 2 ^ (8 * it.size.bytes)) (hb : b < 2)
    (hA : A[k]? = some (stackAlloc p.addr it data))
    (hlen : data.length = it.size.bytes + it.size.bytes) :
    typedStore m p (tupleVal it bits b) (intBoolTupleTy it) ⟨1⟩ .None =
      .ok (withMem m (A.set k (stackAlloc p.addr it (tupleBytes it bits b)))
            ⟨.Store, .None, p.addr, ⟨it.size.bytes + it.size.bytes⟩⟩) := by
  have hk : k < A.length := (List.getElem?_eq_some_iff.mp hA).1
  have hst := typedStore_local_tuple (h.toFocus k p.addr) 0 it hgood data bits b hbits hb
    (focusCtx_drop_get hA) hlen ⟨1⟩ (isAligned_one _)
  rw [focusCtx_localPtr ctx A k (Nat.le_of_lt hk) p hp, focusCtx_localAlloc, focusCtx_set ctx A k p.addr hk]
    at hst
  exact hst

theorem typedLoad_ptr_tuple_field0 {m : Mach} {ctx : Ctx} {frames : List Frame}
    {A : List Gen.Allocation} (h : Shape m ctx frames A) (p : Ptr) (k : Nat)
    (hp : p.provenance = some (⟨(k : Int)⟩, ())) (it : Gen.IntType) (hgood : GoodSize it.size.bytes)
    (bits b : Nat) (hbits : bits < 2 ^ (8 * it.size.bytes))
    (hA : A[k]? = some (stackAlloc p.addr it (tupleBytes it bits b))) :
    ∃ m', typedLoad m p (.Int it) ⟨1⟩ .None = .ok (.Int (intFromBits bits it), m') ∧
      Shape m' ctx frames A := by
  have hk : k < A.length := (List.getElem?_eq_some_iff.mp hA).1
  obtain ⟨m', hm', hs⟩ := typedLoad_local_tuple_field0 (h.toFocus k p.addr) 0 it hgood bits b hbits
    (focusCtx_drop_get hA) ⟨1⟩ (isAligned_one _)
  rw [focusCtx_localPtr ctx A k (Nat.le_of_lt hk) p hp] at hm'
  rw [focusCtx_append] at hs
  exact ⟨m', hm', hs.ofFocus⟩

theorem typedLoad_ptr_tuple_field0_uninit {m : Mach} {ctx : Ctx} {frames : List Frame}
    {A : List Gen.Allocation} (h : Shape m ctx frames A) (p : Ptr) (k : Nat)
    (hp : p.provenance = some (⟨(k : Int)⟩, ())) (it : Gen.IntType) (hgood : GoodSize it.size.bytes)
    (hA : A[k]? = some (stackAlloc p.addr it (List.replicate (it.size.bytes + it.size.bytes) .Uninit))) :
    ∃ msg, typedLoad m p (.Int it) ⟨1⟩ .None = .error (.ub msg) := by
  have hk : k < A.length := (List.getElem?_eq_some_iff.mp hA).1
  obtain ⟨msg, hmsg⟩ := typedLoad_local_tuple_field0_uninit (h.toFocus k p.addr) 0 it hgood
    (focusCtx_drop_get hA) ⟨1⟩ (isAligned_one _)
  rw [focusCtx_localPtr ctx A k (Nat.le_of_lt hk) p hp] at hmsg
  exact ⟨msg, hmsg⟩

theorem typedLoad_ptr_tuple_field1 {m : Mach} {ctx : Ctx} {frames : List Frame}
    {A : List Gen.Allocation} (h : Shape m ctx frames A) (p : Ptr) (k : Nat)
    (hp : p.provenance = some (⟨(k : Int)⟩, ())) (it : Gen.IntType) (hgood : GoodSize it.size.bytes)
    (bits b : Nat) (hb : b < 2) (hA : A[k]? = some (stackAlloc p.addr it (tupleBytes it bits b))) :
    ∃ m', typedLoad m (field1Ptr p it) .Bool ⟨1⟩ .None = .ok (.Bool (decide (b = 1)), m') ∧
      Shape m' ctx frames A := by
  have hk : k < A.length := (List.getElem?_eq_some_iff.mp hA).1
  obtain ⟨m', hm', hs⟩ := typedLoad_local_tuple_field1 (h.toFocus k p.addr) 0 it hgood bits b hb
    (focusCtx_drop_get hA) ⟨1⟩ (isAligned_one _)
  rw [focusCtx_localField1Ptr ctx A k (Nat.le_of_lt hk) p hp] at hm'
  rw [focusCtx_append] at hs
  exact ⟨m', hm', hs.ofFocus⟩

theorem typedLoad_ptr_tuple_field1_uninit {m : Mach} {ctx : Ctx} {frames : List Frame}
    {A : List Gen.Allocation} (h : Shape m ctx frames A) (p : Ptr) (k : Nat)
    (hp : p.provenance = some (⟨(k : Int)⟩, ())) (it : Gen.IntType) (hgood : GoodSize it.size.bytes)
    (hA : A[k]? = some (stackAlloc p.addr it (List.replicate (it.size.bytes + it.size.bytes) .Uninit))) :
    ∃ msg, typedLoad m (field1Ptr p it) .Bool ⟨1⟩ .None = .error (.ub msg) := by
  have hk : k < A.length := (List.getElem?_eq_some_iff.mp hA).1
  obtain ⟨msg, hmsg⟩ := typedLoad_local_tuple_field1_uninit (h.toFocus k p.addr) 0 it hgood
    (focusCtx_drop_get hA) ⟨1⟩ (isAligned_one _)
  rw [focusCtx_localField1Ptr ctx A k (Nat.le_of_lt hk) p hp] at hmsg
  exact ⟨msg, hmsg⟩

theorem typedLoad_ptr_localTy {m : Mach} {ctx : Ctx} {frames : List Frame} {A : List Gen.Allocation}
    {layouts : Layout.LayoutTable}
    (h : Shape m ctx frames A) (p : Ptr) (k : Nat) (hp : p.provenance = some (⟨(k : Int)⟩, ()))
    (d : LocalDecl) (hd : scalarTypeOf d.ty = some (tyOf d layouts)) (v : Value)
    (hv : SlotOk (tyOf d layouts) (.init v))
    (hA : A[k]? = some (stackAlloc p.addr (itOf d layouts) (declSlotData d (.init v) layouts)))
    (align : Align) (hal : Align.is_aligned align p.addr = true) :
    ∃ m', typedLoad m p (tyOf d layouts) align .None =
        .ok (valOfValue (tyOf d layouts) v, m') ∧
      Shape m' ctx frames A := by
  have hk : k < A.length := (List.getElem?_eq_some_iff.mp hA).1
  obtain ⟨m', hm', hs⟩ := typedLoad_local_localTy (h.toFocus k p.addr) 0 d hd v hv
    (focusCtx_drop_get hA) align hal
  rw [focusCtx_localPtr ctx A k (Nat.le_of_lt hk) p hp] at hm'
  rw [focusCtx_append] at hs
  exact ⟨m', hm', hs.ofFocus⟩

theorem typedLoad_ptr_localTy_uninit {m : Mach} {ctx : Ctx} {frames : List Frame}
    {A : List Gen.Allocation} {layouts : Layout.LayoutTable}
    (h : Shape m ctx frames A) (p : Ptr) (k : Nat)
    (hp : p.provenance = some (⟨(k : Int)⟩, ())) (d : LocalDecl)
    (hd : scalarTypeOf d.ty = some (tyOf d layouts))
    (hA : A[k]? = some (stackAlloc p.addr (itOf d layouts) (declSlotData d .uninit layouts)))
    (align : Align) (hal : Align.is_aligned align p.addr = true) :
    ∃ msg, typedLoad m p (tyOf d layouts) align .None = .error (.ub msg) := by
  have hk : k < A.length := (List.getElem?_eq_some_iff.mp hA).1
  obtain ⟨msg, hmsg⟩ := typedLoad_local_localTy_uninit (h.toFocus k p.addr) 0 d hd
    (focusCtx_drop_get hA) align hal
  rw [focusCtx_localPtr ctx A k (Nat.le_of_lt hk) p hp] at hmsg
  exact ⟨msg, hmsg⟩

/-! ## Array and layout-backed tuple/struct encodings, loads, stores, and places -/

/-- MiniRust `Val` corresponding to an Anneal scalar `Value` at element type
`elemIt`. -/
def valToMiniRust (elemIt : Gen.IntType) : Value → Val
  | .scalar sc => .Int (intFromBits sc.bits elemIt)
  | _ => .Int 0

/-- Pointer `p` offset by `off` bytes within the same provenance. -/
def offsetPtr (p : Ptr) (off : Nat) : Ptr :=
  { p with addr := p.addr + (off : Int) }

@[simp] theorem offsetPtr_zero (p : Ptr) : offsetPtr p 0 = p := by
  simp [offsetPtr]

/-- Pointer to element `idx` of array local `_j` (`localPtr ctx j` offset by
`idx * elemIt.size.bytes`). -/
def elemPtr (ctx : Ctx) (j idx : Nat) (elemIt : Gen.IntType) : Ptr :=
  { (localPtr ctx j) with addr := ctx.addrs.getD j 0 + ((idx * elemIt.size.bytes : Nat) : Int) }

/-- Pointer into local `_j` at byte offset `off` (`localPtr ctx j` offset by `off`). -/
def fieldPtr (ctx : Ctx) (j off : Nat) : Ptr :=
  { (localPtr ctx j) with addr := ctx.addrs.getD j 0 + (off : Int) }

@[simp] theorem fieldPtr_zero (ctx : Ctx) (j : Nat) :
    fieldPtr ctx j 0 = localPtr ctx j := by
  simp [fieldPtr, localPtr]

theorem focusCtx_fieldPtr (ctx : Ctx) (A : List Gen.Allocation) (k : Nat)
    (hk : k ≤ A.length) (p : Ptr) (hp : p.provenance = some (⟨(k : Int)⟩, ())) (off : Nat) :
    fieldPtr (focusCtx ctx A k p.addr) 0 off = offsetPtr p off := by
  obtain ⟨addr, prov⟩ := p
  simp only at hp
  subst hp
  simp [fieldPtr, localPtr, offsetPtr, focusCtx, List.length_take, Nat.min_eq_left hk]

theorem focusCtx_elemPtr (ctx : Ctx) (A : List Gen.Allocation) (k : Nat)
    (hk : k ≤ A.length) (p : Ptr) (hp : p.provenance = some (⟨(k : Int)⟩, ()))
    (idx : Nat) (elemIt : Gen.IntType) :
    elemPtr (focusCtx ctx A k p.addr) 0 idx elemIt = offsetPtr p (idx * elemIt.size.bytes) := by
  obtain ⟨addr, prov⟩ := p
  simp only at hp
  subst hp
  simp [elemPtr, localPtr, offsetPtr, focusCtx, List.length_take, Nat.min_eq_left hk]

theorem decode_valBytes (elemIt : Gen.IntType) (v : Value) (hv : ElemOk elemIt v) :
    Type.decode (.Int elemIt) (valBytes elemIt v) = .ok (some (valToMiniRust elemIt v)) := by
  cases v <;> simp [ElemOk] at hv
  rename_i sc
  obtain ⟨_, hb⟩ := hv
  rcases elemIt with ⟨signed, ⟨k⟩⟩
  have hlen : (scalarBytes ⟨signed, ⟨k⟩⟩ sc.bits).length = k := by
    simp [scalarBytes, leBytes_length]
  simp [valBytes, valToMiniRust, Type.decode, Type.decodeInt, hlen, mapM_data_scalarBytes,
    x86_64.ENDIANNESS, decode_leBytes signed k sc.bits hb]

theorem checkValue_valToMiniRust (elemIt : Gen.IntType) (hgood : GoodSize elemIt.size.bytes)
    (v : Value) (hv : ElemOk elemIt v) {m? : Option Mach} :
    checkValue (valToMiniRust elemIt v) (.Int elemIt) m? = .ok () := by
  cases v <;> simp [ElemOk] at hv
  rename_i sc
  obtain ⟨_, hb⟩ := hv
  simp [valToMiniRust, checkValue, canRepresent_intFromBits elemIt sc.bits hgood hb]

theorem encode_valToMiniRust (elemIt : Gen.IntType) (hgood : GoodSize elemIt.size.bytes)
    (v : Value) (hv : ElemOk elemIt v) :
    Type.encode (.Int elemIt) (valToMiniRust elemIt v) = .ok (valBytes elemIt v) := by
  cases v <;> simp [ElemOk] at hv
  rename_i sc
  obtain ⟨_, hb⟩ := hv
  have hrep := canRepresent_intFromBits elemIt sc.bits hgood hb
  simp [valToMiniRust, valBytes, encode_int elemIt _ hgood hrep, intFromBits_emod sc.bits elemIt hb]

theorem mapM_except_append {ε α β : Type} (f : α → Except ε β) (xs ys : List α)
    (us vs : List β) (hx : xs.mapM f = .ok us) (hy : ys.mapM f = .ok vs) :
    (xs ++ ys).mapM f = .ok (us ++ vs) := by
  induction xs generalizing us with
  | nil => simp [List.mapM_nil] at hx; subst hx; simpa using hy
  | cons x xs ih =>
    simp only [List.mapM_cons, bind, Except.bind] at hx
    cases hfx : f x with
    | error e => simp [hfx] at hx
    | ok u =>
      cases hxs : xs.mapM f with
      | error e => simp [hfx, hxs] at hx
      | ok us' =>
        simp [hfx, hxs] at hx; subst hx
        simp [List.cons_append, List.mapM_cons, bind, Except.bind, hfx, ih us' hxs]

theorem mapM_range_prefix {ε α β : Type} (xs : List α) (f : α → β) (g : Nat → Except ε β)
    (n : Nat) (hn : n ≤ xs.length)
    (hg : ∀ (i : Nat) (hi : i < n), g i = .ok (f (xs[i]'(Nat.lt_of_lt_of_le hi hn)))) :
    (List.range n).mapM g = .ok ((xs.take n).map f) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ]
    have ih' := ih (by omega) (fun i hi => hg i (by omega))
    have hlast : [n].mapM g = .ok [f (xs[n]'(by omega))] := by
      simp [List.mapM_cons, List.mapM_nil, hg n (by omega)]
    rw [mapM_except_append g (List.range n) [n] _ _ ih' hlast]
    rw [List.take_add_one, List.getElem?_eq_getElem (by omega), Option.toList_some,
      List.map_append, List.map_singleton]

theorem mapM_decode_valBytes (elemIt : Gen.IntType) (elems : List Value)
    (he : ∀ v ∈ elems, ElemOk elemIt v) :
    tryMapM (fun elemBytes => Type.decode (.Int elemIt) elemBytes)
        (elems.map (valBytes elemIt)) =
      .ok (some (elems.map (valToMiniRust elemIt))) := by
  induction elems with
  | nil => rfl
  | cons v vs ih =>
    have hv := decode_valBytes elemIt v (he v (by simp))
    have ih' := ih (fun x hx => he x (by simp [hx]))
    simp [tryMapM, hv, ih']

theorem decode_array (elemIt : Gen.IntType) (hgood : GoodSize elemIt.size.bytes)
    (elems : List Value) (count : Nat) (hlen : elems.length = count)
    (he : ∀ v ∈ elems, ElemOk elemIt v) :
    Type.decode (.Array (.Int elemIt) (count : Int))
        ((elems.map (valBytes elemIt)).flatten) =
      .ok (some (.Tuple (elems.map (valToMiniRust elemIt)))) := by
  have hblen : ((elems.map (valBytes elemIt)).flatten).length = count * elemIt.size.bytes := by
    rw [flatten_map_length (valBytes elemIt) elemIt.size.bytes elems
      (fun x _ => valBytes_length elemIt x), hlen]
  have hchunks : (List.range count).mapM (fun (i : Nat) =>
      subsliceWithLength ((elems.map (valBytes elemIt)).flatten)
        ((i : Int) * (elemIt.size.bytes : Int)) elemIt.size.bytes) =
      .ok (elems.map (valBytes elemIt)) := by
    subst hlen
    have hpref := mapM_range_prefix elems (valBytes elemIt)
      (fun (i : Nat) =>
        subsliceWithLength ((elems.map (valBytes elemIt)).flatten)
          ((i : Int) * (elemIt.size.bytes : Int)) elemIt.size.bytes)
      elems.length (Nat.le_refl _)
      (fun i hi => by
        rw [← Int.natCast_mul]
        exact subsliceWithLength_flatten_map (valBytes elemIt) elemIt.size.bytes elems
          (fun x _ => valBytes_length elemIt x) i elems[i] (List.getElem?_eq_getElem hi))
    simpa [List.take_length] using hpref
  have hdec := mapM_decode_valBytes elemIt elems he
  unfold Type.decode
  rw [layout_eq elemIt hgood]
  simp only [LayoutStrategy.expect_size, ok_bind, pure_ok, sizeMulInt_natCast,
    Int.toNat_natCast, hblen, ne_eq, not_true_eq_false, ↓reduceIte]
  rw [hchunks]
  simp only [ok_bind]
  change (do
    let decoded ← tryMapM (fun elemBytes => Type.decode (.Int elemIt) elemBytes)
      (elems.map (valBytes elemIt))
    pure (decoded.map Gen.Value.Tuple)) = _
  rw [hdec]
  rfl

theorem checkValue_forM_valToMiniRust (elemIt : Gen.IntType) (hgood : GoodSize elemIt.size.bytes)
    (elems : List Value) (he : ∀ v ∈ elems, ElemOk elemIt v) {m? : Option Mach} :
    (elems.map (valToMiniRust elemIt)).forM (fun v => checkValue v (.Int elemIt) m?) = .ok () := by
  induction elems with
  | nil => rfl
  | cons v vs ih =>
    have hv : checkValue (valToMiniRust elemIt v) (.Int elemIt) m? = .ok () :=
      checkValue_valToMiniRust elemIt hgood v (he v (by simp))
    have ih' := ih (fun x hx => he x (by simp [hx]))
    rw [List.map_cons]
    change (do checkValue (valToMiniRust elemIt v) (.Int elemIt) m?; (vs.map (valToMiniRust elemIt)).forM (fun v => checkValue v (.Int elemIt) m?)) = .ok ()
    rw [hv, ok_bind, ih']

theorem checkValue_array (elemIt : Gen.IntType) (hgood : GoodSize elemIt.size.bytes)
    (elems : List Value) (count : Nat) (hlen : elems.length = count)
    (he : ∀ v ∈ elems, ElemOk elemIt v) {m? : Option Mach} :
    checkValue (.Tuple (elems.map (valToMiniRust elemIt)))
        (.Array (.Int elemIt) (count : Int)) m? = .ok () := by
  have hm := checkValue_forM_valToMiniRust elemIt hgood elems he (m? := m?)
  unfold checkValue
  simp [hlen, hm]

theorem encode_map_valToMiniRust (elemIt : Gen.IntType) (hgood : GoodSize elemIt.size.bytes)
    (elems : List Value) (he : ∀ v ∈ elems, ElemOk elemIt v) :
    (elems.map (valToMiniRust elemIt)).mapM (fun value => do
      let bytes ← Type.encode (.Int elemIt) value
      let elemLayout ← Type.layout (.Int elemIt)
      let elemSize ← LayoutStrategy.expect_size elemLayout "WF ensures array element is sized"
      if bytes.length ≠ elemSize.bytes then
        specPanic "encode: Type::Array element byte length mismatch"
      else
        pure bytes) = .ok (elems.map (valBytes elemIt)) := by
  induction elems with
  | nil => rfl
  | cons v vs ih =>
    have hv := encode_valToMiniRust elemIt hgood v (he v (by simp))
    have hlen := valBytes_length elemIt v
    have ih' := ih (fun x hx => he x (by simp [hx]))
    rw [List.map_cons, List.mapM_cons, hv, ih', layout_eq elemIt hgood]
    simp [hlen]

theorem encode_array (elemIt : Gen.IntType) (hgood : GoodSize elemIt.size.bytes)
    (elems : List Value) (count : Nat) (hlen : elems.length = count)
    (he : ∀ v ∈ elems, ElemOk elemIt v) :
    Type.encode (.Array (.Int elemIt) (count : Int))
        (.Tuple (elems.map (valToMiniRust elemIt))) =
      .ok ((elems.map (valBytes elemIt)).flatten) := by
  have hm := encode_map_valToMiniRust elemIt hgood elems he
  unfold Type.encode
  simp only [List.length_map, hlen, ne_eq, not_true_eq_false, ↓reduceIte]
  rw [hm]
  rfl

theorem memory_with_allocs_self (mem : BM) (allocs : List Gen.Allocation)
    (h : mem.allocations = allocs) :
    { mem with allocations := allocs } = mem := by
  cases mem; subst h; rfl

theorem typedLoad_array_local {m : Mach} {ctx : Ctx} {frames : List Frame} {L : List Gen.Allocation}
    (h : Shape m ctx frames (ctx.base ++ L)) (j : Nat) (elemIt : Gen.IntType) (count : Nat)
    (elems : List Value) (hgood : GoodSize elemIt.size.bytes) (hlen : elems.length = count)
    (he : ∀ v ∈ elems, ElemOk elemIt v)
    (hL : L[j]? = some (localAlloc ctx j elemIt ((elems.map (valBytes elemIt)).flatten))) :
    ∃ m', typedLoad m (localPtr ctx j) (.Array (.Int elemIt) (count : Int)) ⟨1⟩ .None =
        .ok (.Tuple (elems.map (valToMiniRust elemIt)), m') ∧
      Shape m' ctx frames (ctx.base ++ L) := by
  obtain ⟨hj, hLj⟩ := List.getElem?_eq_some_iff.mp hL
  have hblen : ((elems.map (valBytes elemIt)).flatten).length = count * elemIt.size.bytes := by
    rw [flatten_map_length (valBytes elemIt) elemIt.size.bytes elems (fun x _ => valBytes_length elemIt x), hlen]
  have hset := set_self_of_getElem? L j _ hL
  have hdec := decode_array elemIt hgood elems count hlen he
  have hload : CM.load m.mem (localPtr ctx j) ⟨count * elemIt.size.bytes⟩ ⟨1⟩ .None =
      .ok ((elems.map (valBytes elemIt)).flatten,
        (withMem m (ctx.base ++ L) ⟨.Load, .None, ctx.addrs.getD j 0, ⟨count * elemIt.size.bytes⟩⟩).mem) := by
    by_cases hc : count * elemIt.size.bytes = 0
    · have hc0 : count = 0 := by
        rcases Nat.eq_zero_or_pos count with rfl | hpos
        · rfl
        · exfalso; exact Nat.ne_of_gt (Nat.mul_pos hpos hgood.pos) hc
      subst hc0
      have hel0 : elems = [] := List.eq_nil_of_length_eq_zero hlen
      subst hel0
      simp [CM.load, BM.load, BM.check_ptr, localPtr, withMem,
        memory_with_allocs_self m.mem.memory _ h.allocs]
    · simp only [CM.load, BM.load, isAligned_one, BM.check_ptr, localPtr, listIndex, h.allocs]
      simp [hc, hj, hLj, Allocation.size, hblen, listSet, subsliceWithLength, hset,
        List.take_of_length_le, withMem]
  refine ⟨withMem m (ctx.base ++ L) ⟨.Load, .None, ctx.addrs.getD j 0, ⟨count * elemIt.size.bytes⟩⟩,
    ?_, withMem_shape h _⟩
  unfold typedLoad
  rw [layout_array_eq elemIt count hgood]
  simp only [expect_size_sized, ok_bind]
  rw [hload]
  simp only [ok_bind]
  rw [hdec]
  simp only [ok_bind, checkValue_array elemIt hgood elems count hlen he, pure_ok]
  cases m; rfl

theorem typedStore_array_local {m : Mach} {ctx : Ctx} {frames : List Frame} {L : List Gen.Allocation}
    (h : Shape m ctx frames (ctx.base ++ L)) (i : Nat) (elemIt : Gen.IntType) (count : Nat)
    (data : List Byte) (elems : List Value) (hgood : GoodSize elemIt.size.bytes)
    (hL : L[i]? = some (localAlloc ctx i elemIt data))
    (hdlen : data.length = count * elemIt.size.bytes)
    (hlen : elems.length = count) (he : ∀ v ∈ elems, ElemOk elemIt v) :
    typedStore m (localPtr ctx i) (.Tuple (elems.map (valToMiniRust elemIt)))
        (.Array (.Int elemIt) (count : Int)) ⟨1⟩ .None =
      .ok (withMem m (ctx.base ++ L.set i
              (localAlloc ctx i elemIt ((elems.map (valBytes elemIt)).flatten)))
            ⟨.Store, .None, ctx.addrs.getD i 0, ⟨count * elemIt.size.bytes⟩⟩) := by
  obtain ⟨hi, hLi⟩ := List.getElem?_eq_some_iff.mp hL
  have hblen : ((elems.map (valBytes elemIt)).flatten).length = count * elemIt.size.bytes := by
    rw [flatten_map_length (valBytes elemIt) elemIt.size.bytes elems (fun x _ => valBytes_length elemIt x), hlen]
  have hck := checkValue_array elemIt hgood elems count hlen he (m? := some m)
  have henc := encode_array elemIt hgood elems count hlen he
  have hstore : CM.store m.mem (localPtr ctx i) ((elems.map (valBytes elemIt)).flatten) ⟨1⟩ .None =
      .ok (withMem m (ctx.base ++ L.set i
              (localAlloc ctx i elemIt ((elems.map (valBytes elemIt)).flatten)))
            ⟨.Store, .None, ctx.addrs.getD i 0, ⟨count * elemIt.size.bytes⟩⟩).mem := by
    by_cases hc : count * elemIt.size.bytes = 0
    · have hc0 : count = 0 := by
        rcases Nat.eq_zero_or_pos count with rfl | hpos
        · rfl
        · exfalso; exact Nat.ne_of_gt (Nat.mul_pos hpos hgood.pos) hc
      subst hc0
      have hel0 : elems = [] := List.eq_nil_of_length_eq_zero hlen
      subst hel0
      have hdnil : data = [] := List.eq_nil_of_length_eq_zero (by simpa using hdlen)
      subst hdnil
      have hset := set_self_of_getElem? L i _ hL
      simp [CM.store, BM.store, BM.check_ptr, localPtr, withMem, hset,
        memory_with_allocs_self m.mem.memory _ h.allocs]
    · have hdrop : data.drop (count * elemIt.size.bytes) = [] :=
        List.drop_eq_nil_of_le (by omega)
      simp only [CM.store, BM.store, isAligned_one, BM.check_ptr, hblen, hc, ↓reduceIte,
        localPtr, listIndex, h.allocs]
      simp [hi, hLi, Allocation.size, hdlen, hblen, writeSubsliceAtIndex, listSet,
        withMem, hdrop]
      simp [localAlloc, stackAlloc]
  unfold typedStore
  rw [hck]
  simp only
  rw [henc, ok_bind, hstore]
  rfl

theorem typedLoad_array_elem {m : Mach} {ctx : Ctx} {frames : List Frame} {L : List Gen.Allocation}
    (h : Shape m ctx frames (ctx.base ++ L)) (j idx : Nat) (elemIt : Gen.IntType) (count : Nat)
    (elems : List Value) (sc : ScalarVal) (hgood : GoodSize elemIt.size.bytes)
    (hlen : elems.length = count) (he : ∀ v ∈ elems, ElemOk elemIt v)
    (hsc : elems[idx]? = some (.scalar sc))
    (hL : L[j]? = some (localAlloc ctx j elemIt ((elems.map (valBytes elemIt)).flatten))) :
    ∃ m', typedLoad m (elemPtr ctx j idx elemIt) (.Int elemIt) ⟨1⟩ .None =
        .ok (.Int (intFromBits sc.bits elemIt), m') ∧
      Shape m' ctx frames (ctx.base ++ L) := by
  obtain ⟨signed, ⟨bytes⟩⟩ := elemIt
  have hpos := hgood.pos
  obtain ⟨hj, hLj⟩ := List.getElem?_eq_some_iff.mp hL
  have hidx : idx < elems.length := (List.getElem?_eq_some_iff.mp hsc).1
  obtain ⟨hsz, hb⟩ := he (.scalar sc) (List.mem_of_getElem? hsc)
  have hblen : ((elems.map (valBytes ⟨signed, ⟨bytes⟩⟩)).flatten).length = count * bytes := by
    rw [flatten_map_length (valBytes ⟨signed, ⟨bytes⟩⟩) bytes elems (fun x _ => valBytes_length ⟨signed, ⟨bytes⟩⟩ x), hlen]
  have hscLen : (scalarBytes ⟨signed, ⟨bytes⟩⟩ sc.bits).length = bytes := by
    simp [scalarBytes, leBytes_length]
  have hsub := subsliceWithLength_flatten_map (valBytes ⟨signed, ⟨bytes⟩⟩) bytes elems
    (fun x _ => valBytes_length ⟨signed, ⟨bytes⟩⟩ x) idx (.scalar sc) hsc
  simp only [valBytes, Int.natCast_mul] at hsub
  have hset := set_self_of_getElem? L j _ hL
  have hoff_le : idx * bytes + bytes ≤ count * bytes :=
    calc idx * bytes + bytes
      _ = (idx + 1) * bytes := (Nat.succ_mul idx bytes).symm
      _ ≤ count * bytes := Nat.mul_le_mul_right _ (by omega)
  refine ⟨withMem m (ctx.base ++ L) ⟨.Load, .None, (elemPtr ctx j idx ⟨signed, ⟨bytes⟩⟩).addr, ⟨bytes⟩⟩,
    ?_, withMem_shape h _⟩
  have hchk2 : ¬ ((count : Int) * (bytes : Int) <
      (idx : Int) * (bytes : Int) + (bytes : Int)) := by
    exact_mod_cast Nat.not_lt.mpr hoff_le
  simp only [typedLoad, layout_eq _ hgood, CM.load, BM.load,
    BM.check_ptr, elemPtr, localPtr, listIndex, h.allocs]
  simp [Nat.ne_of_gt hpos, hj, hLj, Allocation.size, hblen, hchk2, listSet, hsub, hset,
    Type.decode, Type.decodeInt, hscLen, mapM_data_scalarBytes, x86_64.ENDIANNESS,
    decode_leBytes signed bytes sc.bits hb,
    checkValue, canRepresent_intFromBits _ sc.bits hgood hb, withMem]

theorem typedStore_array_elem {m : Mach} {ctx : Ctx} {frames : List Frame} {L : List Gen.Allocation}
    (h : Shape m ctx frames (ctx.base ++ L)) (i idx : Nat) (elemIt : Gen.IntType) (count : Nat)
    (elems : List Value) (r : Nat) (hgood : GoodSize elemIt.size.bytes)
    (hlen : elems.length = count) (hidx : idx < count) (hr : r < 2 ^ (8 * elemIt.size.bytes))
    (hL : L[i]? = some (localAlloc ctx i elemIt ((elems.map (valBytes elemIt)).flatten))) :
    typedStore m (elemPtr ctx i idx elemIt) (.Int (intFromBits r elemIt)) (.Int elemIt) ⟨1⟩ .None =
      .ok (withMem m (ctx.base ++ L.set i
              (localAlloc ctx i elemIt
                (((elems.set idx (.scalar ⟨r, elemIt.size.bytes⟩)).map (valBytes elemIt)).flatten)))
            ⟨.Store, .None, (elemPtr ctx i idx elemIt).addr, elemIt.size⟩) := by
  obtain ⟨signed, ⟨bytes⟩⟩ := elemIt
  have hpos := hgood.pos
  obtain ⟨hi, hLi⟩ := List.getElem?_eq_some_iff.mp hL
  have hrep := canRepresent_intFromBits ⟨signed, ⟨bytes⟩⟩ r hgood hr
  have hck : checkValue (.Int (intFromBits r ⟨signed, ⟨bytes⟩⟩)) (.Int ⟨signed, ⟨bytes⟩⟩) (some m) = .ok () := by
    simp [checkValue, hrep]
  have hblen : ((elems.map (valBytes ⟨signed, ⟨bytes⟩⟩)).flatten).length = count * bytes := by
    rw [flatten_map_length (valBytes ⟨signed, ⟨bytes⟩⟩) bytes elems (fun x _ => valBytes_length ⟨signed, ⟨bytes⟩⟩ x), hlen]
  have hscLen : (scalarBytes ⟨signed, ⟨bytes⟩⟩ r).length = bytes := by
    simp [scalarBytes, leBytes_length]
  have hres : (intFromBits r ⟨signed, ⟨bytes⟩⟩ % 2 ^ (8 * bytes)).toNat = r := by
    rw [intFromBits_emod r _ hr]; simp
  have hoff_le : idx * bytes + bytes ≤ count * bytes :=
    calc idx * bytes + bytes
      _ = (idx + 1) * bytes := (Nat.succ_mul idx bytes).symm
      _ ≤ count * bytes := Nat.mul_le_mul_right _ (by omega)
  have hsplice := splice_flatten_map (valBytes ⟨signed, ⟨bytes⟩⟩) bytes elems
    (fun x _ => valBytes_length ⟨signed, ⟨bytes⟩⟩ x) idx (.scalar ⟨r, bytes⟩) (by omega)
  simp only [valBytes] at hsplice
  have hchk2 : ¬ ((count : Int) * (bytes : Int) <
      (idx : Int) * (bytes : Int) + (bytes : Int)) := by
    exact_mod_cast Nat.not_lt.mpr hoff_le
  have hchk3 : (idx : Int) * (bytes : Int) + (bytes : Int) ≤
      (count : Int) * (bytes : Int) := by
    exact_mod_cast hoff_le
  simp only [typedStore, hck, encode_int ⟨signed, ⟨bytes⟩⟩ _ hgood hrep, hres, ok_bind,
    CM.store, BM.store, BM.check_ptr, hscLen, Nat.ne_of_gt hpos, ↓reduceIte,
    elemPtr, localPtr, listIndex, h.allocs]
  simp [hi, hLi, Allocation.size, hblen, hscLen, hchk2, hchk3,
    writeSubsliceAtIndex, listSet, withMem, localAlloc]
  rw [← List.append_assoc, hsplice, List.map_set]
  rfl

theorem ptrOffsetInbounds_local {m : Mach} {ctx : Ctx} {frames : List Frame} {L : List Gen.Allocation}
    (h : Shape m ctx frames (ctx.base ++ L)) (j : Nat) (it : Gen.IntType) (data : List Byte)
    (hL : L[j]? = some (localAlloc ctx j it data)) (off : Nat) (hoff : off ≤ data.length)
    (hbound : off < 2 ^ 63) (haddr0 : 0 ≤ ctx.addrs.getD j 0)
    (haddrMax : ctx.addrs.getD j 0 + (data.length : Int) < 2 ^ 64) :
    ptrOffsetInbounds m (localPtr ctx j) (off : Int) =
      .ok { (localPtr ctx j) with addr := ctx.addrs.getD j 0 + (off : Int) } := by
  obtain ⟨hj, hLj⟩ := List.getElem?_eq_some_iff.mp hL
  have hderef : CM.signed_dereferenceable m.mem (localPtr ctx j) (off : Int) = .ok () := by
    unfold CM.signed_dereferenceable BM.signed_dereferenceable
      BM.dereferenceable BM.check_ptr
    simp only [Int.toNat_natCast]
    by_cases hoff0 : off = 0
    · simp [hoff0]
    · have hle : ¬ ((off : Int) > (data.length : Int)) := by omega
      simp [hoff0, localPtr, listIndex, h.allocs, hj, hLj, Allocation.size, hle]
  have hb1 : inBounds (off : Int) .Signed x86_64.PTR_SIZE = true := by
    rw [inBounds_iff _ _ _ (by decide)]
    simp only [windowLo, x86_64.PTR_SIZE, Size.bits]
    omega
  have hb2 : inBounds ((localPtr ctx j).addr + (off : Int)) .Unsigned x86_64.PTR_SIZE = true := by
    rw [inBounds_iff _ _ _ (by decide)]
    simp only [windowLo, x86_64.PTR_SIZE, Size.bits, localPtr]
    omega
  unfold ptrOffsetInbounds
  rw [hderef, ok_bind, hb1, hb2]
  simp [localPtr]

theorem ptrOffsetInbounds_elem {m : Mach} {ctx : Ctx} {frames : List Frame} {L : List Gen.Allocation}
    (h : Shape m ctx frames (ctx.base ++ L)) (j idx : Nat) (elemIt : Gen.IntType) (data : List Byte)
    (hL : L[j]? = some (localAlloc ctx j elemIt data))
    (hoff : idx * elemIt.size.bytes ≤ data.length)
    (hbound : idx * elemIt.size.bytes < 2 ^ 63) (haddr0 : 0 ≤ ctx.addrs.getD j 0)
    (haddrMax : ctx.addrs.getD j 0 + (data.length : Int) < 2 ^ 64) :
    ptrOffsetInbounds m (localPtr ctx j) ((idx : Int) * (elemIt.size.bytes : Int)) =
      .ok (elemPtr ctx j idx elemIt) := by
  have hptr := ptrOffsetInbounds_local h j elemIt data hL (idx * elemIt.size.bytes) hoff hbound haddr0 haddrMax
  simpa [Int.natCast_mul, elemPtr, localPtr] using hptr

mutual

theorem decode_tupleSpec (s : TupleSpec) (v : Value)
    (hwf : s.wf = true) (hv : s.valOk v = true) :
    Type.decode s.toMiniRustTy (s.encodeVal v) = .ok (some (s.toMiniRustVal v)) := by
  cases s with
  | scalar it =>
    cases v with
    | scalar sc =>
      simp only [TupleSpec.valOk, Bool.and_eq_true, decide_eq_true_eq] at hv
      obtain ⟨hsz, hb⟩ := hv
      have hd := decode_valBytes it (.scalar sc) ⟨hsz, hb⟩
      simpa [TupleSpec.toMiniRustTy, TupleSpec.encodeVal, TupleSpec.toMiniRustVal,
        valBytes, valToMiniRust] using hd
    | _ => simp [TupleSpec.valOk] at hv
  | tuple fields size align =>
    cases v with
    | aggregate vidx vals =>
      cases vidx with
      | succ _ => simp [TupleSpec.valOk] at hv
      | zero =>
        have hblen := TupleSpec.encodeVal_length (.tuple fields size align) (.aggregate 0 vals) hwf
        simp only [TupleSpec.encodeVal, TupleSpec.size] at hblen
        simp only [TupleSpec.valOk, Bool.and_eq_true, decide_eq_true_eq] at hv
        obtain ⟨_, hfwv⟩ := hv
        simp only [TupleSpec.wf, Bool.and_eq_true, decide_eq_true_eq] at hwf
        obtain ⟨⟨⟨hpos, hmod⟩, _⟩, hfwf⟩ := hwf
        have hfields := decodeTupleFields_spec size align fields vals
          (List.replicate size Gen.AbstractByte.Uninit) hfwf hfwv (by simp)
        unfold TupleSpec.toMiniRustTy TupleSpec.encodeVal TupleSpec.toMiniRustVal Type.decode
        simp only [head_size_and_align_mk size align hmod ((goodAlignBytes_iff align).mp hpos).pos, hblen, ne_eq, not_true_eq_false, ↓reduceIte]
        rw [hfields]
        rfl
    | _ => simp [TupleSpec.valOk] at hv

theorem decodeTupleFields_spec (size align : Nat) (fields : List (Nat × TupleSpec))
    (vals : List Value) (acc : List Byte)
    (hfwf : TupleSpec.fieldsWf size align fields = true)
    (hv : TupleSpec.fieldsValOk fields vals = true)
    (hacc : acc.length = size) :
    Type.decodeFields (TupleSpec.fieldsToMiniRust fields)
        (TupleSpec.encodeFields fields vals acc) =
      .ok (some (TupleSpec.fieldsToMiniRustVal fields vals)) := by
  cases fields with
  | nil =>
    cases vals <;> simp [TupleSpec.fieldsValOk] at hv
    simp [TupleSpec.fieldsToMiniRust, TupleSpec.fieldsToMiniRustVal, Type.decodeFields]
  | cons f restF =>
    obtain ⟨off, fs⟩ := f
    cases vals with
    | nil => simp [TupleSpec.fieldsValOk] at hv
    | cons v restV =>
      have hlen_enc : (TupleSpec.encodeFields ((off, fs) :: restF) (v :: restV) acc).length = size :=
        TupleSpec.encodeFields_length size align ((off, fs) :: restF) (v :: restV) acc hfwf hacc
      obtain ⟨hfswf, hoff, _, _, hslice⟩ :=
        TupleSpec.encodeFields_field_slice size align ((off, fs) :: restF) (v :: restV) acc
          0 off fs v hfwf hacc rfl rfl
      simp only [TupleSpec.fieldsWf, Bool.and_eq_true] at hfwf
      have hrestWf := hfwf.2
      simp only [TupleSpec.fieldsValOk, Bool.and_eq_true] at hv
      obtain ⟨hvv, hrestV⟩ := hv
      have hlay := layout_tupleSpec fs hfswf
      have hsub : subsliceWithLength (TupleSpec.encodeFields ((off, fs) :: restF) (v :: restV) acc)
          (off : Int) (fs.size : Int) = .ok (fs.encodeVal v) := by
        rw [subsliceWithLength_eq_drop_take _ off fs.size (by omega), hslice]
      have hdec_head := decode_tupleSpec fs v hfswf hvv
      have hlen_v := TupleSpec.encodeVal_length fs v hfswf
      have hacc' : (spliceAt acc off (fs.encodeVal v)).length = size := by
        rw [spliceAt_length _ _ _ (by omega), hacc]
      have hdec_tail := decodeTupleFields_spec size align restF restV
        (spliceAt acc off (fs.encodeVal v)) hrestWf hrestV hacc'
      unfold TupleSpec.fieldsToMiniRust TupleSpec.fieldsToMiniRustVal Type.decodeFields
      rw [hlay]
      simp only [expect_size_sized, ok_bind]
      rw [hsub, ok_bind, hdec_head, ok_bind]
      change (do
        match ← Type.decodeFields (TupleSpec.fieldsToMiniRust restF)
            (TupleSpec.encodeFields restF restV (spliceAt acc off (fs.encodeVal v))) with
        | none => pure none
        | some vs => pure (some (fs.toMiniRustVal v :: vs))) = _
      rw [hdec_tail]
      rfl

end

mutual

theorem checkValue_tupleSpec (s : TupleSpec) (v : Value)
    (hwf : s.wf = true) (hv : s.valOk v = true) {m? : Option Mach} :
    checkValue (s.toMiniRustVal v) s.toMiniRustTy m? = .ok () := by
  cases s with
  | scalar it =>
    simp only [TupleSpec.wf] at hwf
    have hgood := (goodAlignBytes_iff it.size.bytes).mp hwf
    cases v with
    | scalar sc =>
      simp only [TupleSpec.valOk, Bool.and_eq_true, decide_eq_true_eq] at hv
      obtain ⟨hsz, hb⟩ := hv
      simpa [TupleSpec.toMiniRustVal, TupleSpec.toMiniRustTy, valToMiniRust] using
        checkValue_valToMiniRust it hgood (.scalar sc) ⟨hsz, hb⟩ (m? := m?)
    | _ => simp [TupleSpec.valOk] at hv
  | tuple fields size align =>
    cases v with
    | aggregate vidx vals =>
      cases vidx with
      | succ _ => simp [TupleSpec.valOk] at hv
      | zero =>
        simp only [TupleSpec.valOk, Bool.and_eq_true, decide_eq_true_eq] at hv
        obtain ⟨hlen_v, hfwv⟩ := hv
        simp only [TupleSpec.wf, Bool.and_eq_true] at hwf
        obtain ⟨_, hfwf⟩ := hwf
        have hlen_m := TupleSpec.fieldsToMiniRustVal_length fields vals
        have hlen_f := TupleSpec.fieldsToMiniRust_length fields
        have hchk := checkTupleFields_spec size align fields vals hfwf hfwv (m? := m?)
        unfold TupleSpec.toMiniRustVal TupleSpec.toMiniRustTy checkValue
        simp [hlen_m, hlen_f, hlen_v, hchk]
    | _ => simp [TupleSpec.valOk] at hv

theorem checkTupleFields_spec (size align : Nat) (fields : List (Nat × TupleSpec))
    (vals : List Value)
    (hfwf : TupleSpec.fieldsWf size align fields = true)
    (hv : TupleSpec.fieldsValOk fields vals = true) {m? : Option Mach} :
    checkFields (TupleSpec.fieldsToMiniRustVal fields vals)
      (TupleSpec.fieldsToMiniRust fields) m? = .ok () := by
  cases fields with
  | nil =>
    cases vals <;> simp [TupleSpec.fieldsValOk] at hv
    simp [TupleSpec.fieldsToMiniRustVal, TupleSpec.fieldsToMiniRust, checkFields]
  | cons f restF =>
    obtain ⟨off, fs⟩ := f
    cases vals with
    | nil => simp [TupleSpec.fieldsValOk] at hv
    | cons v restV =>
      simp only [TupleSpec.fieldsWf, Bool.and_eq_true] at hfwf
      obtain ⟨⟨⟨⟨⟨hfswf, _⟩, _⟩, _⟩, _⟩, hrestWf⟩ := hfwf
      simp only [TupleSpec.fieldsValOk, Bool.and_eq_true] at hv
      obtain ⟨hvv, hrestV⟩ := hv
      have hhead := checkValue_tupleSpec fs v hfswf hvv (m? := m?)
      have htail := checkTupleFields_spec size align restF restV hrestWf hrestV (m? := m?)
      unfold TupleSpec.fieldsToMiniRustVal TupleSpec.fieldsToMiniRust checkFields
      rw [hhead, ok_bind, htail]

end

mutual

theorem encode_tupleSpec (s : TupleSpec) (v : Value)
    (hwf : s.wf = true) (hv : s.valOk v = true) :
    Type.encode s.toMiniRustTy (s.toMiniRustVal v) = .ok (s.encodeVal v) := by
  cases s with
  | scalar it =>
    simp only [TupleSpec.wf] at hwf
    have hgood := (goodAlignBytes_iff it.size.bytes).mp hwf
    cases v with
    | scalar sc =>
      simp only [TupleSpec.valOk, Bool.and_eq_true, decide_eq_true_eq] at hv
      obtain ⟨hsz, hb⟩ := hv
      simpa [TupleSpec.toMiniRustTy, TupleSpec.toMiniRustVal, TupleSpec.encodeVal,
        valToMiniRust, valBytes] using
        encode_valToMiniRust it hgood (.scalar sc) ⟨hsz, hb⟩
    | _ => simp [TupleSpec.valOk] at hv
  | tuple fields size align =>
    cases v with
    | aggregate vidx vals =>
      cases vidx with
      | succ _ => simp [TupleSpec.valOk] at hv
      | zero =>
        simp only [TupleSpec.valOk, Bool.and_eq_true, decide_eq_true_eq] at hv
        obtain ⟨hlen_v, hfwv⟩ := hv
        simp only [TupleSpec.wf, Bool.and_eq_true, decide_eq_true_eq] at hwf
        obtain ⟨⟨⟨hpos, hmod⟩, _⟩, hfwf⟩ := hwf
        have hlen_m := TupleSpec.fieldsToMiniRustVal_length fields vals
        have hlen_f := TupleSpec.fieldsToMiniRust_length fields
        have henc := encodeTupleFields_spec size align fields vals
          (List.replicate size Gen.AbstractByte.Uninit) hfwf hfwv (by simp)
        unfold TupleSpec.toMiniRustTy TupleSpec.toMiniRustVal TupleSpec.encodeVal Type.encode
        simp [head_size_and_align_mk size align hmod ((goodAlignBytes_iff align).mp hpos).pos, hlen_m, hlen_f, hlen_v, henc]
    | _ => simp [TupleSpec.valOk] at hv

theorem encodeTupleFields_spec (size align : Nat) (fields : List (Nat × TupleSpec))
    (vals : List Value) (acc : List Byte)
    (hfwf : TupleSpec.fieldsWf size align fields = true)
    (hv : TupleSpec.fieldsValOk fields vals = true)
    (hacc : acc.length = size) :
    Type.encodeFields (TupleSpec.fieldsToMiniRust fields)
        (TupleSpec.fieldsToMiniRustVal fields vals) acc =
      .ok (TupleSpec.encodeFields fields vals acc) := by
  cases fields with
  | nil =>
    cases vals <;> simp [TupleSpec.fieldsValOk] at hv
    simp [TupleSpec.fieldsToMiniRust, TupleSpec.fieldsToMiniRustVal,
      TupleSpec.encodeFields, Type.encodeFields]
  | cons f restF =>
    obtain ⟨off, fs⟩ := f
    cases vals with
    | nil => simp [TupleSpec.fieldsValOk] at hv
    | cons v restV =>
      simp only [TupleSpec.fieldsWf, Bool.and_eq_true, decide_eq_true_eq] at hfwf
      obtain ⟨⟨⟨⟨⟨hfswf, hoff⟩, _⟩, _⟩, _⟩, hrestWf⟩ := hfwf
      simp only [TupleSpec.fieldsValOk, Bool.and_eq_true] at hv
      obtain ⟨hvv, hrestV⟩ := hv
      have hhead := encode_tupleSpec fs v hfswf hvv
      have hlen_e := TupleSpec.encodeVal_length fs v hfswf
      have hw : writeSubsliceAtIndex acc (off : Int) (fs.encodeVal v) =
          .ok (spliceAt acc off (fs.encodeVal v)) :=
        writeSubsliceAtIndex_eq_spliceAt acc off (fs.encodeVal v) (by omega)
      have hacc' : (spliceAt acc off (fs.encodeVal v)).length = size := by
        rw [spliceAt_length _ _ _ (by omega), hacc]
      have htail := encodeTupleFields_spec size align restF restV
        (spliceAt acc off (fs.encodeVal v)) hrestWf hrestV hacc'
      unfold TupleSpec.fieldsToMiniRust TupleSpec.fieldsToMiniRustVal
        TupleSpec.encodeFields Type.encodeFields
      rw [hhead, ok_bind, hw, ok_bind, htail]

end

theorem ptrOffsetInbounds_fieldPtr {m : Mach} {ctx : Ctx} {frames : List Frame} {L : List Gen.Allocation}
    (h : Shape m ctx frames (ctx.base ++ L)) (j : Nat) (allocIt : Gen.IntType) (data : List Byte)
    (hL : L[j]? = some (localAlloc ctx j allocIt data))
    (baseOff off : Nat) (hoff : baseOff + off ≤ data.length)
    (hbound : data.length < 2 ^ 63) (haddr0 : 0 ≤ ctx.addrs.getD j 0)
    (haddrMax : ctx.addrs.getD j 0 + (data.length : Int) < 2 ^ 64) :
    ptrOffsetInbounds m (fieldPtr ctx j baseOff) (off : Int) =
      .ok (fieldPtr ctx j (baseOff + off)) := by
  obtain ⟨hj, hLj⟩ := List.getElem?_eq_some_iff.mp hL
  have hderef : CM.signed_dereferenceable m.mem (fieldPtr ctx j baseOff) (off : Int) = .ok () := by
    unfold CM.signed_dereferenceable BM.signed_dereferenceable
      BM.dereferenceable BM.check_ptr
    simp only [Int.toNat_natCast]
    by_cases hoff0 : off = 0
    · simp [hoff0]
    · have hle : ¬ ((baseOff : Int) + (off : Int) > (data.length : Int)) := by omega
      simp [hoff0, fieldPtr, localPtr, listIndex, h.allocs, hj, hLj, Allocation.size, hle]
  have hb1 : inBounds (off : Int) .Signed x86_64.PTR_SIZE = true := by
    rw [inBounds_iff _ _ _ (by decide)]
    simp only [windowLo, x86_64.PTR_SIZE, Size.bits]
    omega
  have hb2 : inBounds ((fieldPtr ctx j baseOff).addr + (off : Int)) .Unsigned x86_64.PTR_SIZE = true := by
    rw [inBounds_iff _ _ _ (by decide)]
    simp only [windowLo, x86_64.PTR_SIZE, Size.bits, fieldPtr, localPtr]
    omega
  unfold ptrOffsetInbounds
  rw [hderef, ok_bind, hb1, hb2]
  simp [fieldPtr, localPtr, Int.add_assoc]

theorem evalPlace_fieldPath {layouts : Layout.LayoutTable}
    {m : Mach} {ctx : Ctx} {frames : List Frame} {L : List Gen.Allocation}
    (h : Shape m ctx frames (ctx.base ++ L)) (j : Nat) (allocIt : Gen.IntType) (data : List Byte)
    (hL : L[j]? = some (localAlloc ctx j allocIt data))
    (hbound : data.length < 2 ^ 63) (haddr0 : 0 ≤ ctx.addrs.getD j 0)
    (haddrMax : ctx.addrs.getD j 0 + (data.length : Int) < 2 ^ 64)
    (rootPe : Gen.PlaceExpr) (baseOff : Nat) (rootSpec : TupleSpec)
    (hrootEval : evalPlace m rootPe =
      .ok (({ ptr := { thin_pointer := fieldPtr ctx j baseOff, metadata := none },
               aligned := true }, rootSpec.toMiniRustTy), m))
    (hrootWf : rootSpec.wf = true)
    (hbaseBound : baseOff + rootSpec.size ≤ data.length)
    (projs : List ProjectionElem) (pe : Gen.PlaceExpr)
    (hpe : translateFieldPlace rootPe projs = some pe)
    (relOff : Nat) (leafSpec : TupleSpec)
    (hres : resolveFieldPath layouts rootSpec projs = some (relOff, leafSpec)) :
    evalPlace m pe =
      .ok (({ ptr := { thin_pointer := fieldPtr ctx j (baseOff + relOff), metadata := none },
               aligned := true }, leafSpec.toMiniRustTy), m) := by
  induction projs generalizing rootPe baseOff rootSpec relOff with
  | nil =>
    simp [translateFieldPlace] at hpe
    simp [resolveFieldPath] at hres
    subst hpe
    rcases hres with ⟨rfl, rfl⟩
    simpa using hrootEval
  | cons p rest ih =>
    cases p with
    | field idx fieldTy =>
      simp only [translateFieldPlace] at hpe
      cases rootSpec with
      | scalar _ => simp [resolveFieldPath] at hres
      | tuple fields size align =>
        simp only [resolveFieldPath, Option.bind_eq_bind] at hres
        cases hf : fields[idx]? with
        | none => simp [hf] at hres
        | some pair =>
          obtain ⟨off, subSpec⟩ := pair
          simp only [hf, Option.bind_some] at hres
          cases hexp : specOfRigidTy layouts fieldTy.kind fieldTy.layoutIdx with
          | none => simp [hexp] at hres
          | some expectedSpec =>
            simp only [hexp, Option.bind_some] at hres
            by_cases heq : subSpec = expectedSpec
            · simp only [heq, ↓reduceIte] at hres
              cases hrest : resolveFieldPath layouts expectedSpec rest with
              | none => simp [hrest] at hres
              | some rpair =>
                obtain ⟨restOff, leafSpec'⟩ := rpair
                simp [hrest] at hres
                rcases hres with ⟨rfl, rfl⟩
                subst heq
                have hrootLay := layout_tupleSpec (.tuple fields size align) hrootWf
                simp only [TupleSpec.wf, Bool.and_eq_true] at hrootWf
                obtain ⟨hsubWf, hoffBound, _, _⟩ := TupleSpec.fieldsWf_getElem? hrootWf.2 hf
                have hsubLay := layout_tupleSpec subSpec hsubWf
                have hgetMr := TupleSpec.fieldsToMiniRust_getElem? fields idx off subSpec hf
                have hidx_lt : idx < (TupleSpec.fieldsToMiniRust fields).length :=
                  (List.getElem?_eq_some_iff.mp hgetMr).1
                have hcond_idx : (0 : Int) ≤ (idx : Int) ∧
                    (idx : Int) < ((TupleSpec.fieldsToMiniRust fields).length : Int) := by
                  exact ⟨by omega, by exact_mod_cast hidx_lt⟩
                have hlidx : listIndex (TupleSpec.fieldsToMiniRust fields) (idx : Int)
                    "sized_fields[field]" = .ok (⟨off⟩, subSpec.toMiniRustTy) := by
                  simp [listIndex, hgetMr]
                simp only [TupleSpec.size] at hbaseBound
                have hptr := ptrOffsetInbounds_fieldPtr h j allocIt data hL baseOff off
                  (by omega) hbound haddr0 haddrMax
                have hstepEval : evalPlace m (.Field rootPe (idx : Int)) =
                    .ok (({ ptr := { thin_pointer := fieldPtr ctx j (baseOff + off), metadata := none },
                             aligned := true }, subSpec.toMiniRustTy), m) := by
                  rw [evalPlace]
                  rw [hrootEval, ok_bind]
                  simp only [TupleSpec.toMiniRustTy] at hrootLay ⊢
                  simp only [hcond_idx, and_self, ↓reduceIte, hlidx, ok_bind, pure_ok,
                    hrootLay, TupleSpec.size,
                    hptr, hsubLay, LayoutStrategy.is_sized, Bool.not_true, Bool.false_eq_true,
                    ThinPointer.widen]
                  rw [computeSize_sized]
                  simp
                  omega
                have hstep := ih (.Field rootPe (idx : Int)) (baseOff + off) subSpec
                  hstepEval hsubWf (by omega) hpe restOff hrest
                simpa [Nat.add_assoc] using hstep
            · simp [heq] at hres
    | _ => simp [translateFieldPlace] at hpe

theorem typedLoad_tuple_slice {m : Mach} {ctx : Ctx} {frames : List Frame} {L : List Gen.Allocation}
    (h : Shape m ctx frames (ctx.base ++ L)) (j : Nat) (allocIt : Gen.IntType) (data : List Byte)
    (hL : L[j]? = some (localAlloc ctx j allocIt data))
    (off : Nat) (subSpec : TupleSpec) (subVal : Value)
    (hwf : subSpec.wf = true) (hv : subSpec.valOk subVal = true)
    (hoff : off + subSpec.size ≤ data.length)
    (hslice : (data.drop off).take subSpec.size = subSpec.encodeVal subVal) :
    ∃ m', typedLoad m (fieldPtr ctx j off) subSpec.toMiniRustTy ⟨1⟩ .None =
        .ok (subSpec.toMiniRustVal subVal, m') ∧
      Shape m' ctx frames (ctx.base ++ L) := by
  obtain ⟨hj, hLj⟩ := List.getElem?_eq_some_iff.mp hL
  have hlay := layout_tupleSpec subSpec hwf
  have hdec := decode_tupleSpec subSpec subVal hwf hv
  have hset := set_self_of_getElem? L j _ hL
  have hload : CM.load m.mem (fieldPtr ctx j off) ⟨subSpec.size⟩ ⟨1⟩ .None =
      .ok (subSpec.encodeVal subVal,
        (withMem m (ctx.base ++ L) ⟨.Load, .None, (fieldPtr ctx j off).addr, ⟨subSpec.size⟩⟩).mem) := by
    by_cases hc : subSpec.size = 0
    · have hlen0 : (subSpec.encodeVal subVal).length = 0 := by
        rw [TupleSpec.encodeVal_length subSpec subVal hwf, hc]
      have hnil : subSpec.encodeVal subVal = [] := List.eq_nil_of_length_eq_zero hlen0
      simp [CM.load, BM.load, BM.check_ptr, hc, hnil, withMem,
        memory_with_allocs_self m.mem.memory _ h.allocs]
    · have hchk2 : ¬ ((data.length : Int) < (off : Int) + (subSpec.size : Int)) := by omega
      have hsub := subsliceWithLength_eq_drop_take data off subSpec.size hoff
      rw [hslice] at hsub
      simp only [CM.load, BM.load, isAligned_one, BM.check_ptr, fieldPtr, localPtr, listIndex, h.allocs]
      simp [hc, hj, hLj, Allocation.size, hchk2, listSet, hsub, hset, withMem]
  refine ⟨withMem m (ctx.base ++ L) ⟨.Load, .None, (fieldPtr ctx j off).addr, ⟨subSpec.size⟩⟩,
    ?_, withMem_shape h _⟩
  unfold typedLoad
  rw [hlay]
  simp only [expect_size_sized, ok_bind, hload, hdec, checkValue_tupleSpec subSpec subVal hwf hv, pure_ok]
  simp [withMem]

theorem typedStore_tuple_slice {m : Mach} {ctx : Ctx} {frames : List Frame} {L : List Gen.Allocation}
    (h : Shape m ctx frames (ctx.base ++ L)) (i : Nat) (allocIt : Gen.IntType) (data : List Byte)
    (hL : L[i]? = some (localAlloc ctx i allocIt data))
    (off : Nat) (subSpec : TupleSpec) (subVal : Value)
    (hwf : subSpec.wf = true) (hv : subSpec.valOk subVal = true)
    (hoff : off + subSpec.size ≤ data.length) :
    typedStore m (fieldPtr ctx i off) (subSpec.toMiniRustVal subVal) subSpec.toMiniRustTy ⟨1⟩ .None =
      .ok (withMem m (ctx.base ++ L.set i
              (localAlloc ctx i allocIt (spliceAt data off (subSpec.encodeVal subVal))))
            ⟨.Store, .None, (fieldPtr ctx i off).addr, ⟨subSpec.size⟩⟩) := by
  obtain ⟨hi, hLi⟩ := List.getElem?_eq_some_iff.mp hL
  have hck := checkValue_tupleSpec subSpec subVal hwf hv (m? := some m)
  have henc := encode_tupleSpec subSpec subVal hwf hv
  have hlen_e := TupleSpec.encodeVal_length subSpec subVal hwf
  have hstore : CM.store m.mem (fieldPtr ctx i off) (subSpec.encodeVal subVal) ⟨1⟩ .None =
      .ok (withMem m (ctx.base ++ L.set i
              (localAlloc ctx i allocIt (spliceAt data off (subSpec.encodeVal subVal))))
            ⟨.Store, .None, (fieldPtr ctx i off).addr, ⟨subSpec.size⟩⟩).mem := by
    by_cases hc : subSpec.size = 0
    · have hlen0 : (subSpec.encodeVal subVal).length = 0 := by rw [hlen_e, hc]
      have hnil : subSpec.encodeVal subVal = [] := List.eq_nil_of_length_eq_zero hlen0
      have hsp : spliceAt data off [] = data := by
        unfold spliceAt
        simp
      have hset := set_self_of_getElem? L i _ hL
      simp [CM.store, BM.store, BM.check_ptr, hc, hnil, hsp, hset, withMem,
        memory_with_allocs_self m.mem.memory _ h.allocs]
    · have hchk2 : ¬ ((data.length : Int) < (off : Int) + (subSpec.size : Int)) := by omega
      have hw := writeSubsliceAtIndex_eq_spliceAt data off (subSpec.encodeVal subVal)
        (by rw [hlen_e]; exact hoff)
      simp only [CM.store, BM.store, isAligned_one, BM.check_ptr, hlen_e, hc, ↓reduceIte,
        fieldPtr, localPtr, listIndex, h.allocs]
      simp [hi, hLi, Allocation.size, hchk2, hw, listSet, withMem, localAlloc, stackAlloc]
  unfold typedStore
  rw [hck]
  simp only
  rw [henc, ok_bind, hstore]
  rfl

/-! ### Pointer-lifted array and tuple/struct helpers (`focusCtx`) -/

theorem typedLoad_ptr_array {m : Mach} {ctx : Ctx} {frames : List Frame} {A : List Gen.Allocation}
    (h : Shape m ctx frames A) (p : Ptr) (k : Nat) (hp : p.provenance = some (⟨(k : Int)⟩, ()))
    (elemIt : Gen.IntType) (count : Nat) (elems : List Value) (hgood : GoodSize elemIt.size.bytes)
    (hlen : elems.length = count) (he : ∀ v ∈ elems, ElemOk elemIt v)
    (hA : A[k]? = some (stackAlloc p.addr elemIt ((elems.map (valBytes elemIt)).flatten))) :
    ∃ m', typedLoad m p (.Array (.Int elemIt) (count : Int)) ⟨1⟩ .None =
        .ok (.Tuple (elems.map (valToMiniRust elemIt)), m') ∧
      Shape m' ctx frames A := by
  have hk : k < A.length := (List.getElem?_eq_some_iff.mp hA).1
  obtain ⟨m', hm', hs⟩ := typedLoad_array_local (h.toFocus k p.addr) 0 elemIt count elems hgood
    hlen he (focusCtx_drop_get hA)
  rw [focusCtx_localPtr ctx A k (Nat.le_of_lt hk) p hp] at hm'
  rw [focusCtx_append] at hs
  exact ⟨m', hm', hs.ofFocus⟩

theorem typedStore_ptr_array {m : Mach} {ctx : Ctx} {frames : List Frame} {A : List Gen.Allocation}
    (h : Shape m ctx frames A) (p : Ptr) (k : Nat) (hp : p.provenance = some (⟨(k : Int)⟩, ()))
    (elemIt : Gen.IntType) (count : Nat) (data : List Byte) (elems : List Value)
    (hgood : GoodSize elemIt.size.bytes) (hA : A[k]? = some (stackAlloc p.addr elemIt data))
    (hdlen : data.length = count * elemIt.size.bytes)
    (hlen : elems.length = count) (he : ∀ v ∈ elems, ElemOk elemIt v) :
    typedStore m p (.Tuple (elems.map (valToMiniRust elemIt)))
        (.Array (.Int elemIt) (count : Int)) ⟨1⟩ .None =
      .ok (withMem m (A.set k
              (stackAlloc p.addr elemIt ((elems.map (valBytes elemIt)).flatten)))
            ⟨.Store, .None, p.addr, ⟨count * elemIt.size.bytes⟩⟩) := by
  have hk : k < A.length := (List.getElem?_eq_some_iff.mp hA).1
  have hst := typedStore_array_local (h.toFocus k p.addr) 0 elemIt count data elems hgood
    (focusCtx_drop_get hA) hdlen hlen he
  rw [focusCtx_localPtr ctx A k (Nat.le_of_lt hk) p hp, focusCtx_localAlloc,
    focusCtx_set ctx A k p.addr hk] at hst
  exact hst

theorem typedLoad_ptr_array_elem {m : Mach} {ctx : Ctx} {frames : List Frame}
    {A : List Gen.Allocation} (h : Shape m ctx frames A) (p : Ptr) (k : Nat)
    (hp : p.provenance = some (⟨(k : Int)⟩, ())) (idx : Nat) (elemIt : Gen.IntType) (count : Nat)
    (elems : List Value) (sc : ScalarVal) (hgood : GoodSize elemIt.size.bytes)
    (hlen : elems.length = count) (he : ∀ v ∈ elems, ElemOk elemIt v)
    (hsc : elems[idx]? = some (.scalar sc))
    (hA : A[k]? = some (stackAlloc p.addr elemIt ((elems.map (valBytes elemIt)).flatten))) :
    ∃ m', typedLoad m (offsetPtr p (idx * elemIt.size.bytes)) (.Int elemIt) ⟨1⟩ .None =
        .ok (.Int (intFromBits sc.bits elemIt), m') ∧
      Shape m' ctx frames A := by
  have hk : k < A.length := (List.getElem?_eq_some_iff.mp hA).1
  obtain ⟨m', hm', hs⟩ := typedLoad_array_elem (h.toFocus k p.addr) 0 idx elemIt count elems sc
    hgood hlen he hsc (focusCtx_drop_get hA)
  rw [focusCtx_elemPtr ctx A k (Nat.le_of_lt hk) p hp idx elemIt] at hm'
  rw [focusCtx_append] at hs
  exact ⟨m', hm', hs.ofFocus⟩

theorem typedStore_ptr_array_elem {m : Mach} {ctx : Ctx} {frames : List Frame}
    {A : List Gen.Allocation} (h : Shape m ctx frames A) (p : Ptr) (k : Nat)
    (hp : p.provenance = some (⟨(k : Int)⟩, ())) (idx : Nat) (elemIt : Gen.IntType) (count : Nat)
    (elems : List Value) (r : Nat) (hgood : GoodSize elemIt.size.bytes)
    (hlen : elems.length = count) (hidx : idx < count) (hr : r < 2 ^ (8 * elemIt.size.bytes))
    (hA : A[k]? = some (stackAlloc p.addr elemIt ((elems.map (valBytes elemIt)).flatten))) :
    typedStore m (offsetPtr p (idx * elemIt.size.bytes)) (.Int (intFromBits r elemIt))
        (.Int elemIt) ⟨1⟩ .None =
      .ok (withMem m (A.set k
              (stackAlloc p.addr elemIt
                (((elems.set idx (.scalar ⟨r, elemIt.size.bytes⟩)).map (valBytes elemIt)).flatten)))
            ⟨.Store, .None, (offsetPtr p (idx * elemIt.size.bytes)).addr, elemIt.size⟩) := by
  have hk : k < A.length := (List.getElem?_eq_some_iff.mp hA).1
  have hst := typedStore_array_elem (h.toFocus k p.addr) 0 idx elemIt count elems r
    hgood hlen hidx hr (focusCtx_drop_get hA)
  rw [focusCtx_elemPtr ctx A k (Nat.le_of_lt hk) p hp idx elemIt, focusCtx_localAlloc,
    focusCtx_set ctx A k p.addr hk] at hst
  exact hst

theorem ptrOffsetInbounds_ptr_elem {m : Mach} {ctx : Ctx} {frames : List Frame}
    {A : List Gen.Allocation} (h : Shape m ctx frames A) (p : Ptr) (k : Nat)
    (hp : p.provenance = some (⟨(k : Int)⟩, ())) (idx : Nat) (elemIt : Gen.IntType)
    (data : List Byte) (hA : A[k]? = some (stackAlloc p.addr elemIt data))
    (hoff : idx * elemIt.size.bytes ≤ data.length)
    (hbound : idx * elemIt.size.bytes < 2 ^ 63) (haddr0 : 0 ≤ p.addr)
    (haddrMax : p.addr + (data.length : Int) < 2 ^ 64) :
    ptrOffsetInbounds m p ((idx : Int) * (elemIt.size.bytes : Int)) =
      .ok (offsetPtr p (idx * elemIt.size.bytes)) := by
  have hk : k < A.length := (List.getElem?_eq_some_iff.mp hA).1
  have hptr := ptrOffsetInbounds_elem (h.toFocus k p.addr) 0 idx elemIt data
    (focusCtx_drop_get hA) hoff hbound haddr0 haddrMax
  rw [focusCtx_localPtr ctx A k (Nat.le_of_lt hk) p hp,
    focusCtx_elemPtr ctx A k (Nat.le_of_lt hk) p hp idx elemIt] at hptr
  exact hptr

theorem evalPlace_ptr_fieldPath {layouts : Layout.LayoutTable}
    {m : Mach} {ctx : Ctx} {frames : List Frame} {A : List Gen.Allocation}
    (h : Shape m ctx frames A) (p : Ptr) (k : Nat) (hp : p.provenance = some (⟨(k : Int)⟩, ()))
    (allocIt : Gen.IntType) (data : List Byte)
    (hA : A[k]? = some (stackAlloc p.addr allocIt data))
    (hbound : data.length < 2 ^ 63) (haddr0 : 0 ≤ p.addr)
    (haddrMax : p.addr + (data.length : Int) < 2 ^ 64)
    (rootPe : Gen.PlaceExpr) (baseOff : Nat) (rootSpec : TupleSpec)
    (hrootEval : evalPlace m rootPe =
      .ok (({ ptr := { thin_pointer := offsetPtr p baseOff, metadata := none },
               aligned := true }, rootSpec.toMiniRustTy), m))
    (hrootWf : rootSpec.wf = true)
    (hbaseBound : baseOff + rootSpec.size ≤ data.length)
    (projs : List ProjectionElem) (pe : Gen.PlaceExpr)
    (hpe : translateFieldPlace rootPe projs = some pe)
    (relOff : Nat) (leafSpec : TupleSpec)
    (hres : resolveFieldPath layouts rootSpec projs = some (relOff, leafSpec)) :
    evalPlace m pe =
      .ok (({ ptr := { thin_pointer := offsetPtr p (baseOff + relOff), metadata := none },
               aligned := true }, leafSpec.toMiniRustTy), m) := by
  have hk : k < A.length := (List.getElem?_eq_some_iff.mp hA).1
  rw [← focusCtx_fieldPtr ctx A k (Nat.le_of_lt hk) p hp baseOff] at hrootEval
  have hev := evalPlace_fieldPath (h.toFocus k p.addr) 0 allocIt data (focusCtx_drop_get hA)
    hbound haddr0 haddrMax rootPe baseOff rootSpec hrootEval hrootWf hbaseBound projs pe hpe
    relOff leafSpec hres
  rw [focusCtx_fieldPtr ctx A k (Nat.le_of_lt hk) p hp (baseOff + relOff)] at hev
  exact hev

theorem typedLoad_ptr_tuple_slice {m : Mach} {ctx : Ctx} {frames : List Frame}
    {A : List Gen.Allocation} (h : Shape m ctx frames A) (p : Ptr) (k : Nat)
    (hp : p.provenance = some (⟨(k : Int)⟩, ())) (allocIt : Gen.IntType) (data : List Byte)
    (hA : A[k]? = some (stackAlloc p.addr allocIt data))
    (off : Nat) (subSpec : TupleSpec) (subVal : Value)
    (hwf : subSpec.wf = true) (hv : subSpec.valOk subVal = true)
    (hoff : off + subSpec.size ≤ data.length)
    (hslice : (data.drop off).take subSpec.size = subSpec.encodeVal subVal) :
    ∃ m', typedLoad m (offsetPtr p off) subSpec.toMiniRustTy ⟨1⟩ .None =
        .ok (subSpec.toMiniRustVal subVal, m') ∧
      Shape m' ctx frames A := by
  have hk : k < A.length := (List.getElem?_eq_some_iff.mp hA).1
  obtain ⟨m', hm', hs⟩ := typedLoad_tuple_slice (h.toFocus k p.addr) 0 allocIt data
    (focusCtx_drop_get hA) off subSpec subVal hwf hv hoff hslice
  rw [focusCtx_fieldPtr ctx A k (Nat.le_of_lt hk) p hp off] at hm'
  rw [focusCtx_append] at hs
  exact ⟨m', hm', hs.ofFocus⟩

theorem typedStore_ptr_tuple_slice {m : Mach} {ctx : Ctx} {frames : List Frame}
    {A : List Gen.Allocation} (h : Shape m ctx frames A) (p : Ptr) (k : Nat)
    (hp : p.provenance = some (⟨(k : Int)⟩, ())) (allocIt : Gen.IntType) (data : List Byte)
    (hA : A[k]? = some (stackAlloc p.addr allocIt data))
    (off : Nat) (subSpec : TupleSpec) (subVal : Value)
    (hwf : subSpec.wf = true) (hv : subSpec.valOk subVal = true)
    (hoff : off + subSpec.size ≤ data.length) :
    typedStore m (offsetPtr p off) (subSpec.toMiniRustVal subVal) subSpec.toMiniRustTy ⟨1⟩ .None =
      .ok (withMem m (A.set k
              (stackAlloc p.addr allocIt (spliceAt data off (subSpec.encodeVal subVal))))
            ⟨.Store, .None, (offsetPtr p off).addr, ⟨subSpec.size⟩⟩) := by
  have hk : k < A.length := (List.getElem?_eq_some_iff.mp hA).1
  have hst := typedStore_tuple_slice (h.toFocus k p.addr) 0 allocIt data (focusCtx_drop_get hA)
    off subSpec subVal hwf hv hoff
  rw [focusCtx_fieldPtr ctx A k (Nat.le_of_lt hk) p hp off, focusCtx_localAlloc,
    focusCtx_set ctx A k p.addr hk] at hst
  exact hst

/-! ## Operands and rvalues -/

/-- The resolved element index of a projection element on an array of length `count`,
or `none` when evaluating the index is UB (uninitialized index local or out-of-bounds). -/
def projIdx (locals : List LocalSlot) (count : Nat) : ProjectionElem → Option Nat
  | .index idxLocal =>
    match locals[idxLocal]? with
    | some (.init (.scalar sc)) => if sc.bits < count then some sc.bits else none
    | _ => none
  | .constantIndex offset minLength fromEnd =>
    if count < minLength then none
    else
      let idx := if fromEnd then count - offset else offset
      if idx < count then some idx else none
  | _ => none

/-- The bit pattern an Anneal fragment operand evaluates to, or `none` when
reading it is UB (an uninitialized local or out-of-bounds array index). -/
def opBits (locals : List LocalSlot) : Operand → Option Nat
  | .copy ⟨j, []⟩ =>
    match locals[j]? with
    | some (.init (.scalar sc)) => some sc.bits
    | _ => none
  | .copy ⟨j, .field idx fieldTy :: rest⟩ =>
    match locals[j]? with
    | some (.init rootVal) =>
      match readFieldPath rootVal (.field idx fieldTy :: rest) with
      | some (.scalar sc) => some sc.bits
      | _ => none
    | _ => none
  | .copy ⟨j, [proj]⟩ =>
    match locals[j]? with
    | some (.init (.aggregate 0 elems)) =>
      match projIdx locals elems.length proj with
      | some idx =>
        match elems[idx]? with
        | some (.scalar sc) => some sc.bits
        | _ => none
      | none => none
    | _ => none
  | .constant c =>
    match c.val with
    | .scalar (.int sc) => some sc.bits
    | _ => none
  | _ => none

/-- The arithmetic of `eval_int_un_op` for the fragment unary operators. -/
def intUnArith : Gen.IntUnOp → Int → Int
  | .Neg, x => -x
  | .BitNot, x => -x - 1
  | _, _ => 0

theorem evalIntUnOp_eq (uop : MirAst.UnOp) (iuop : Gen.IntUnOp)
    (huop : translateUnOp uop = some iuop) (x : Int) (it : Gen.IntType) :
    evalIntUnOp iuop x it = .ok (IntType.bring_in_bounds it (intUnArith iuop x)) := by
  cases uop <;> simp [translateUnOp] at huop <;> subst huop <;> rfl

theorem intBitRec_zero_right (k : Nat) (x : Int) :
    intBitRec (fun _ => 0) (fun b => b) (fun u v => if u = 1 ∧ v = 1 then 1 else 0) k x 0 = 0 := by
  induction k generalizing x with
  | zero => simp [intBitRec]
  | succ k ih =>
    simp only [intBitRec]
    split
    · rfl
    · split
      · rfl
      · rw [show (0 : Int) / 2 = 0 from rfl, show (0 : Int) % 2 = 0 from rfl, ih (x / 2)]
        omega

/-- On `libspecr::Int`, `x & 1` (`intBitAnd x 1`) equals `x % 2` (`0` or `1`). -/
theorem intBitAnd_one (x : Int) : intBitAnd x 1 = x % 2 := by
  unfold intBitAnd
  have hmod : x % 2 = 0 ∨ x % 2 = 1 := by omega
  cases hk : intBitMeasure x with
  | zero =>
    simp only [intBitRec]
    split
    · next h0 => subst h0; rfl
    · next hne0 =>
      have hx1 : x = -1 := by
        unfold intBitMeasure at hk
        split at hk <;> omega
      subst hx1; rfl
  | succ k =>
    simp only [intBitRec]
    split
    · next h0 => subst h0; rfl
    · split
      · next hn1 => subst hn1; rfl
      · rw [show (1 : Int) / 2 = 0 from rfl, show (1 : Int) % 2 = 1 from rfl,
          intBitRec_zero_right k (x / 2)]
        rcases hmod with hmod | hmod <;> simp [hmod]

theorem countOnesLoop_bounds (n : Nat) (acc x : Int) :
    acc ≤ countOnesLoop n acc x ∧ countOnesLoop n acc x ≤ acc + n := by
  induction n generalizing acc x with
  | zero => simp [countOnesLoop]
  | succ n ih =>
    simp only [countOnesLoop, intBitAnd_one]
    have hmod : 0 ≤ x % 2 ∧ x % 2 ≤ 1 := by omega
    have ⟨hl, hr⟩ := ih (acc + x % 2) (x / 2)
    omega

/-- `Machine::eval_un_op` on `UnOp::Int(IntUnOp::CountOnes)` never triggers the
`check_value` sanity-check panic on any `GoodSize` integer type, returning
`evalCountOnes x it` at type `u32` (`spec/lang/step/operators.md`). -/
theorem evalUnOp_countOnes (x : Int) (it : Gen.IntType) (hgood : GoodSize it.size.bytes) :
    evalUnOp (.Int .CountOnes) (.Int x, .Int it) =
      .ok (.Int (evalCountOnes x it), .Int ⟨.Unsigned, ⟨4⟩⟩) := by
  have hb := countOnesLoop_bounds (Size.bits it.size) 0 x
  have hbits : (Size.bits it.size : Int) < (2 : Int) ^ Size.bits ⟨4⟩ := by
    unfold Size.bits
    rcases hgood with h | h | h | h | h <;> rw [h] <;> decide
  have hrep : IntType.can_represent ⟨.Unsigned, ⟨4⟩⟩ (evalCountOnes x it) = true := by
    unfold IntType.can_represent inBounds evalCountOnes
    dsimp only
    rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
    omega
  simp [evalUnOp, evalIntUnOp, checkValue_int hrep]

/-- Symbolic characterization of `Machine::eval_int_bin_op` on `IntBinOp::DivExact`
(`spec/lang/step/operators.md`):
* `r = 0` raises `.ub "division by zero"`,
* `r ≠ 0` and `!IntType.can_represent it (Int.tdiv l r)` raises `.ub "overflow in division"`,
* `r ≠ 0`, `IntType.can_represent it (Int.tdiv l r) = true`, and `Int.tmod l r ≠ 0`
  raises `.ub "non-zero remainder in exact division"`, and
* otherwise returns `.ok (Int.tdiv l r)`. -/
theorem evalIntBinOp_divExact (l r : Int) (it : Gen.IntType) :
    evalIntBinOp .DivExact l r it =
      if r = 0 then .error (.ub "division by zero")
      else if !IntType.can_represent it (Int.tdiv l r) then .error (.ub "overflow in division")
      else if Int.tmod l r ≠ 0 then .error (.ub "non-zero remainder in exact division")
      else .ok (Int.tdiv l r) := by
  rfl

theorem intUnArith_emod (uop : MirAst.UnOp) (iuop : Gen.IntUnOp)
    (huop : translateUnOp uop = some iuop) (x x' m : Int) (hx : x % m = x' % m) :
    intUnArith iuop x % m = intUnArith iuop x' % m := by
  cases uop <;> simp [translateUnOp] at huop <;> subst huop <;> simp only [intUnArith]
  · rw [show -x - 1 = -1 - x by omega, show -x' - 1 = -1 - x' by omega,
      Int.sub_emod, hx, ← Int.sub_emod]
  · rw [show -x = 0 - x by omega, show -x' = 0 - x' by omega,
      Int.sub_emod, hx, ← Int.sub_emod]

/-- Partial integer evaluation of `eval_int_bin_op` for the fragment binary
operators: returns `some z` when `evalIntBinOp iop l r it = .ok z` and `none`
when `evalIntBinOp` raises UB (`throw_ub!`). -/
def intBinEval (iop : Gen.IntBinOp) (l r : Int) (it : Gen.IntType) : Option Int :=
  match iop with
  | .Add => some (l + r)
  | .Sub => some (l - r)
  | .Mul => some (l * r)
  | .AddUnchecked => if IntType.can_represent it (l + r) then some (l + r) else none
  | .SubUnchecked => if IntType.can_represent it (l - r) then some (l - r) else none
  | .MulUnchecked => if IntType.can_represent it (l * r) then some (l * r) else none
  | .Div =>
    if r = 0 then none
    else if IntType.can_represent it (Int.tdiv l r) then some (Int.tdiv l r)
    else none
  | .Rem =>
    if r = 0 then none
    else if IntType.can_represent it (Int.tdiv l r) then some (Int.tmod l r)
    else none
  | .Shl =>
    let bits : Int := Size.bits it.size
    some (l * (2 : Int) ^ (r % bits).toNat)
  | .Shr =>
    let bits : Int := Size.bits it.size
    some (l / (2 : Int) ^ (r % bits).toNat)
  | .ShlUnchecked =>
    let bits : Int := Size.bits it.size
    if r < 0 ∨ r ≥ bits then none else some (l * (2 : Int) ^ r.toNat)
  | .ShrUnchecked =>
    let bits : Int := Size.bits it.size
    if r < 0 ∨ r ≥ bits then none else some (l / (2 : Int) ^ r.toNat)
  | .BitAnd => some (intBitAnd l r)
  | .BitOr => some (intBitOr l r)
  | .BitXor => some (intBitXor l r)
  | _ => none

theorem evalIntBinOp_spec (op : MirAst.BinOp) (iop : Gen.IntBinOp)
    (hop : translateBinOp op = some iop) (l r : Int) (it : Gen.IntType) :
    (∀ z, intBinEval iop l r it = some z → evalIntBinOp iop l r it = .ok z) ∧
    (intBinEval iop l r it = none → ∃ msg, evalIntBinOp iop l r it = .error (.ub msg)) := by
  match op, hop with
  | .add, hop | .sub, hop | .mul, hop | .bitXor, hop | .bitAnd, hop | .bitOr, hop
  | .shl, hop | .shr, hop =>
    simp [translateBinOp] at hop; subst hop; simp [intBinEval, evalIntBinOp]
  | .addUnchecked, hop =>
    simp [translateBinOp] at hop; subst hop
    cases hrep : IntType.can_represent it (l + r) <;> simp [intBinEval, evalIntBinOp, hrep, ub]
  | .subUnchecked, hop =>
    simp [translateBinOp] at hop; subst hop
    cases hrep : IntType.can_represent it (l - r) <;> simp [intBinEval, evalIntBinOp, hrep, ub]
  | .mulUnchecked, hop =>
    simp [translateBinOp] at hop; subst hop
    cases hrep : IntType.can_represent it (l * r) <;> simp [intBinEval, evalIntBinOp, hrep, ub]
  | .div, hop =>
    simp [translateBinOp] at hop; subst hop
    by_cases hr0 : r = 0
    · simp [intBinEval, evalIntBinOp, hr0, ub]
    · cases hrep : IntType.can_represent it (Int.tdiv l r) <;>
        simp [intBinEval, evalIntBinOp, hr0, hrep, ub]
  | .rem, hop =>
    simp [translateBinOp] at hop; subst hop
    by_cases hr0 : r = 0
    · simp [intBinEval, evalIntBinOp, hr0, ub]
    · cases hrep : IntType.can_represent it (Int.tdiv l r) <;>
        simp [intBinEval, evalIntBinOp, hr0, hrep, ub]
  | .shlUnchecked, hop =>
    simp [translateBinOp] at hop; subst hop
    by_cases hoob : r < 0 ∨ r ≥ Size.bits it.size <;> simp [intBinEval, evalIntBinOp, hoob, ub]
  | .shrUnchecked, hop =>
    simp [translateBinOp] at hop; subst hop
    by_cases hoob : r < 0 ∨ r ≥ Size.bits it.size <;> simp [intBinEval, evalIntBinOp, hoob, ub]

theorem operandIntType_of_operandOk {layouts : Layout.LayoutTable}
    {decls : List LocalDecl} {it : Gen.IntType} {op : Operand}
    (h : operandOk layouts decls it op = true) : operandIntType layouts decls op = some it := by
  match op, h with
  | .copy ⟨_, []⟩, h =>
    simp only [operandOk, placeOk, operandIntType, placeIntType,
      Bool.and_eq_true, decide_eq_true_eq] at h ⊢
    exact h.1.2
  | .copy ⟨j, proj :: rest⟩, h =>
    cases proj with
    | field idx fieldTy =>
      simp only [operandOk, placeOk, operandIntType, placeIntType,
        Bool.and_eq_true] at h ⊢
      obtain ⟨⟨_, hok⟩, _⟩ := h
      cases hd : decls[j]? with
      | none => simp [hd] at hok
      | some d =>
        simp only [hd, Option.bind_eq_bind, Option.bind_some] at hok ⊢
        cases hij : intBoolTupleOf d.ty with
        | some tupIt =>
          simp only [hij] at hok ⊢
          cases idx with
          | zero =>
            cases rest with
            | nil =>
              cases hf : intTypeOf fieldTy with
              | none => simp [hf] at hok
              | some fIt =>
                simp only [hf, Bool.and_eq_true, decide_eq_true_eq] at hok
                obtain ⟨rfl, rfl⟩ := hok
                simp
            | cons _ _ => simp at hok
          | succ _ => simp at hok
        | none =>
          simp only [hij] at hok ⊢
          cases ht : tupleTypeOf layouts d.ty with
          | none => simp [ht] at hok
          | some p =>
            obtain ⟨fields, size, align⟩ := p
            simp only [ht, Option.bind_some] at hok ⊢
            cases hres : resolveFieldPath layouts (.tuple fields size align)
                (.field idx fieldTy :: rest) with
            | none => simp [hres] at hok
            | some rpair =>
              obtain ⟨_, leafSpec⟩ := rpair
              simp only [hres, Option.bind_some] at hok ⊢
              cases leafSpec with
              | scalar leafIt =>
                simp only [decide_eq_true_eq] at hok
                subst hok
                rfl
              | tuple _ _ _ => simp at hok
    | index idxLocal =>
      cases rest with
      | nil =>
        simp only [operandOk, placeOk, operandIntType, placeIntType,
          Bool.and_eq_true, decide_eq_true_eq] at h ⊢
        obtain ⟨⟨_, hok⟩, _⟩ := h
        cases hd : decls[j]? with
        | none => simp [hd] at hok
        | some d =>
          simp only [hd, Option.bind_eq_bind, Option.bind_some] at hok ⊢
          cases ha : arrayTypeOf d.ty with
          | none => simp [ha] at hok
          | some p =>
            obtain ⟨elemIt, count⟩ := p
            simp only [ha, Bool.and_eq_true, decide_eq_true_eq, Option.map_some, Option.some.injEq] at hok ⊢
            exact hok.1
      | cons _ _ => simp [operandOk, translateOperand, translatePlace] at h
    | constantIndex offset minLen fromEnd =>
      cases rest with
      | nil =>
        simp only [operandOk, placeOk, operandIntType, placeIntType,
          Bool.and_eq_true, decide_eq_true_eq] at h ⊢
        obtain ⟨⟨_, hok⟩, _⟩ := h
        cases hd : decls[j]? with
        | none => simp [hd] at hok
        | some d =>
          simp only [hd, Option.bind_eq_bind, Option.bind_some] at hok ⊢
          cases ha : arrayTypeOf d.ty with
          | none => simp [ha] at hok
          | some p =>
            obtain ⟨elemIt, count⟩ := p
            simp only [ha, Bool.and_eq_true, decide_eq_true_eq, Option.map_some, Option.some.injEq] at hok ⊢
            exact hok.1
      | cons _ _ => simp [operandOk, translateOperand, translatePlace] at h
    | deref =>
      cases rest with
      | nil =>
        simp only [operandOk, placeOk, projOk, Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨⟨_, hok⟩, _⟩ := h
        split at hok <;> simp at hok
      | cons _ _ => simp [operandOk, placeOk] at h
    | _ => cases rest <;> simp [operandOk, placeOk, projOk, translateOperand, translatePlace] at h
  | .constant _, h =>
    simp only [operandOk, Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.1

theorem rvalueOk_binaryOp {layouts : Layout.LayoutTable} {decls : List LocalDecl} {it : Gen.IntType}
    {op : MirAst.BinOp} {a b : Operand}
    (h : rvalueOk layouts decls it (.binaryOp op a b) = true) :
    ∃ iop rhsIt,
      translateBinOp op = some iop ∧
      operandOk layouts decls it a = true ∧
      operandIntType layouts decls b = some rhsIt ∧
      operandOk layouts decls rhsIt b = true ∧
      (isShiftIntBinOp iop = false → rhsIt = it) := by
  simp only [rvalueOk] at h
  cases hiop : translateBinOp op with
  | none => simp [hiop] at h
  | some iop =>
    simp only [hiop, Bool.and_eq_true] at h
    obtain ⟨hoka, hokb⟩ := h
    cases hsh : isShiftIntBinOp iop with
    | true =>
      simp only [hsh, ↓reduceIte] at hokb
      cases hrhs : operandIntType layouts decls b with
      | none => simp [hrhs] at hokb
      | some rhsIt =>
        simp only [hrhs] at hokb
        exact ⟨iop, rhsIt, rfl, hoka, rfl, hokb, fun hf => by rw [hsh] at hf; cases hf⟩
    | false =>
      simp only [hsh, Bool.false_eq_true, ↓reduceIte] at hokb
      exact ⟨iop, it, rfl, hoka, operandIntType_of_operandOk hokb, hokb, fun _ => rfl⟩

/-- Non-scalar aggregate locals (arrays and `TupleSpec` tuples/structs, i.e.
non-scalar and non-pointer locals) in a fragment body are always initialized
(`slot = .init v`) and, when in the locals map, occupy caller-region addresses
below `2 ^ 32` (`StartRel` allocates parameters below `2 ^ 32`, and `inFragment`
forbids `StorageLive` / `StorageDead` / `Deinit` / `Operand.move` on non-scalar
non-pointer locals). -/
def NonScalarLive (body : CapturedMir) (locals : List LocalSlot)
    (lm : Map Gen.LocalName Ptr) : Prop :=
  ∀ (i : Nat) d slot, body.localDecls[i]? = some d → locals[i]? = some slot →
    scalarTypeOf d.ty = none → isPtrTy d.ty = false →
    (∃ v, slot = .init v) ∧
    (∀ p, mapGet lm (localName i) = some p →
      p.addr + (tyBytes (tyOf d body.layouts) : Int) < 2 ^ 32)

theorem NonScalarLive.set_init {body : CapturedMir} {locals : List LocalSlot}
    {lm : Map Gen.LocalName Ptr} (hns : NonScalarLive body locals lm)
    (i : Nat) (v : Value) :
    NonScalarLive body (locals.set i (.init v)) lm := by
  intro j d slot hdj hsj hnone hnp
  by_cases hij : i = j
  · subst hij
    have hil : i < locals.length := by
      by_cases hlt : i < locals.length
      · exact hlt
      · rw [List.set_eq_of_length_le (Nat.le_of_not_lt hlt)] at hsj
        exact False.elim (hlt (List.getElem?_eq_some_iff.mp hsj).1)
    rw [List.getElem?_set_self hil] at hsj
    cases hsj
    exact ⟨⟨v, rfl⟩, (hns i d locals[i] hdj (List.getElem?_eq_getElem hil) hnone hnp).2⟩
  · rw [List.getElem?_set_ne hij] at hsj
    exact hns j d slot hdj hsj hnone hnp

theorem NonScalarLive.set_scalar {body : CapturedMir} {locals : List LocalSlot}
    {lm : Map Gen.LocalName Ptr} (hns : NonScalarLive body locals lm)
    {i : Nat} {d : LocalDecl} (hd : body.localDecls[i]? = some d)
    (hscalar : (scalarTypeOf d.ty).isSome = true ∨ isPtrTy d.ty = true) (ns : LocalSlot) :
    NonScalarLive body (locals.set i ns) lm := by
  intro j dj slot hdj hsj hnone hnp
  by_cases hij : i = j
  · subst hij; rw [hd] at hdj; cases hdj
    rcases hscalar with hsc | hp
    · simp [hnone] at hsc
    · simp [hnp] at hp
  · rw [List.getElem?_set_ne hij] at hsj
    exact hns j dj slot hdj hsj hnone hnp

/-- Hypotheses describing a callee frame related to Anneal slots `locals`: `f`
is the translation of `body`, and the machine runs the callee at `(blk, stmt)`
with the locals map `lm`, which agrees with `locals` (`LocalsOk`). -/
structure FrameOk (body : CapturedMir) (f : Gen.Function) (ctx : Ctx) (locals : List LocalSlot)
    (lm : Map Gen.LocalName Ptr) (m : Mach) (blk stmt : Nat) : Prop where
  hf : FnLocalsSpec body f
  shape : Shape m ctx [ctx.caller, calleeFrameL f ctx lm blk stmt] m.mem.memory.allocations
  locs : LocalsOk body ctx locals lm m.mem.memory.allocations
  declsOk : ∀ d ∈ body.localDecls, localDeclOk body.layouts d = true
  nonScalar : NonScalarLive body locals lm

/-- `FrameOk` from a shape and a `LocalsOk` over the same allocations. -/
theorem FrameOk.mk' {body : CapturedMir} {f : Gen.Function} {ctx : Ctx} {locals : List LocalSlot}
    {lm : Map Gen.LocalName Ptr} {m : Mach} {blk stmt : Nat} (hf : FnLocalsSpec body f)
    {A : List Gen.Allocation} (hs : Shape m ctx [ctx.caller, calleeFrameL f ctx lm blk stmt] A)
    (hlo : LocalsOk body ctx locals lm A)
    (hdeclsOk : ∀ d ∈ body.localDecls, localDeclOk body.layouts d = true)
    (hns : NonScalarLive body locals lm) :
    FrameOk body f ctx locals lm m blk stmt := by
  refine ⟨hf, ?_, ?_, hdeclsOk, hns⟩
  · rw [hs.allocs]; exact hs
  · rw [hs.allocs]; exact hlo

theorem FrameOk.nlocals {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {locals : List LocalSlot} {lm : Map Gen.LocalName Ptr} {m : Mach} {blk stmt : Nat}
    (h : FrameOk body f ctx locals lm m blk stmt) :
    locals.length = body.localDecls.length :=
  h.locs.nlocals

theorem FrameOk.slots {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {locals : List LocalSlot} {lm : Map Gen.LocalName Ptr} {m : Mach} {blk stmt : Nat}
    (h : FrameOk body f ctx locals lm m blk stmt) :
    ∀ (i : Nat) d slot, body.localDecls[i]? = some d → locals[i]? = some slot →
      DeclSlotOk d slot body.layouts :=
  h.locs.slots

theorem FrameOk.decl_localTy {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {locals : List LocalSlot} {lm : Map Gen.LocalName Ptr} {m : Mach} {blk stmt : Nat}
    (h : FrameOk body f ctx locals lm m blk stmt)
    (i : Nat) (d : LocalDecl) (hd : body.localDecls[i]? = some d) :
    LocalTy (tyOf d body.layouts) (itOf d body.layouts) :=
  localTy_of_declOk (h.declsOk d (List.mem_of_getElem? hd))

theorem FrameOk.decl_good {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {locals : List LocalSlot} {lm : Map Gen.LocalName Ptr} {m : Mach} {blk stmt : Nat}
    (h : FrameOk body f ctx locals lm m blk stmt) (i : Nat) (d : LocalDecl)
    (hd : body.localDecls[i]? = some d) : GoodSize (itOf d body.layouts).size.bytes :=
  (h.decl_localTy i d hd).good

theorem FrameOk.array_bound {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {locals : List LocalSlot} {lm : Map Gen.LocalName Ptr} {m : Mach} {blk stmt : Nat}
    (h : FrameOk body f ctx locals lm m blk stmt) (i : Nat) (d : LocalDecl)
    (elemIt : Gen.IntType) (count : Nat) (hd : body.localDecls[i]? = some d)
    (ha : arrayTypeOf d.ty = some (elemIt, count)) : count * elemIt.size.bytes < 2 ^ 63 := by
  have hdok := h.declsOk d (List.mem_of_getElem? hd)
  simpa [localDeclOk, scalarTypeOf_none_of_arrayTypeOf ha, ha, isPtrTy_false_of_arrayTypeOf ha]
    using hdok

theorem FrameOk.tuple_wf {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {locals : List LocalSlot} {lm : Map Gen.LocalName Ptr} {m : Mach} {blk stmt : Nat}
    (h : FrameOk body f ctx locals lm m blk stmt) (i : Nat) (d : LocalDecl)
    (fields : List (Nat × TupleSpec)) (size align : Nat) (hd : body.localDecls[i]? = some d)
    (ht : tupleTypeOf body.layouts d.ty = some (fields, size, align)) :
    (TupleSpec.tuple fields size align).wf = true := by
  have hdok := h.declsOk d (List.mem_of_getElem? hd)
  simpa [localDeclOk, scalarTypeOf_none_of_tupleTypeOf ht, arrayTypeOf_none_of_tupleTypeOf ht, ht,
    isPtrTy_false_of_tupleTypeOf ht] using hdok

theorem FrameOk.slot_exists {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {locals : List LocalSlot} {lm : Map Gen.LocalName Ptr} {m : Mach} {blk stmt : Nat}
    (h : FrameOk body f ctx locals lm m blk stmt)
    (i : Nat) (hi : i < body.localDecls.length) :
    ∃ d slot, body.localDecls[i]? = some d ∧ locals[i]? = some slot := by
  refine ⟨body.localDecls[i], locals[i]'(by rw [h.nlocals]; exact hi), by simp [hi], by simp⟩

/-- A local that `LocalsOkA` keeps out of the locals map is dead. -/
theorem LocalsOkA.dead_of_none {body : CapturedMir} {ctx : Ctx} {al : List Nat}
    {locals : List LocalSlot} {lm : Map Gen.LocalName Ptr} {allocs : List Gen.Allocation}
    (hlo : LocalsOkA body ctx al locals lm allocs) {i : Nat} {slot : LocalSlot}
    (hs : locals[i]? = some slot) (hp : mapGet lm (localName i) = none) : slot = .dead := by
  cases slot with
  | dead => rfl
  | uninit =>
    have h := (hlo.live i _ hs).mpr (.inl (by simp))
    simp [hp] at h
  | init v =>
    have h := (hlo.live i _ hs).mpr (.inl (by simp))
    simp [hp] at h

/-- A live local is in the locals map. -/
theorem LocalsOkA.some_of_live {body : CapturedMir} {ctx : Ctx} {al : List Nat}
    {locals : List LocalSlot} {lm : Map Gen.LocalName Ptr} {allocs : List Gen.Allocation}
    (hlo : LocalsOkA body ctx al locals lm allocs) {i : Nat} {slot : LocalSlot}
    (hs : locals[i]? = some slot) (hlive : slot ≠ .dead) :
    ∃ p, mapGet lm (localName i) = some p := by
  have h := (hlo.live i slot hs).mpr (.inl hlive)
  exact Option.isSome_iff_exists.mp h

/-- A dead local outside `al` is not in the locals map. -/
theorem LocalsOkA.none_of_dead {body : CapturedMir} {ctx : Ctx} {al : List Nat}
    {locals : List LocalSlot} {lm : Map Gen.LocalName Ptr} {allocs : List Gen.Allocation}
    (hlo : LocalsOkA body ctx al locals lm allocs) {i : Nat}
    (hs : locals[i]? = some .dead) (hal : i ∉ al) :
    mapGet lm (localName i) = none := by
  cases hp : mapGet lm (localName i) with
  | none => rfl
  | some p =>
    have h := (hlo.live i .dead hs).mp (by simp [hp])
    simp [hal] at h

theorem LocalsOkA.storage_nonptr {body : CapturedMir} {ctx : Ctx} {al : List Nat}
    {locals : List LocalSlot} {lm : Map Gen.LocalName Ptr} {allocs : List Gen.Allocation}
    (hlo : LocalsOkA body ctx al locals lm allocs)
    (i : Nat) (d : LocalDecl) (slot : LocalSlot) (p : Ptr)
    (hd : body.localDecls[i]? = some d) (hs : locals[i]? = some slot)
    (hp : mapGet lm (localName i) = some p) (hnp : isPtrTy d.ty = false) :
    ∃ id : Nat, p.provenance = some (⟨(id : Int)⟩, ()) ∧ ctx.base.length ≤ id ∧
      AddrOk p.addr (itOf d body.layouts) ∧
      p.addr + (tyBytes (tyOf d body.layouts) : Int) < 2 ^ 64 ∧
      AddrClass p.addr (tyBytes (tyOf d body.layouts)) ∧
      allocs[id]? = some (stackAlloc p.addr (itOf d body.layouts) (declSlotData d slot body.layouts)) := by
  obtain ⟨id, hpid, hb, ha, hmax, hc, hA⟩ := hlo.storage i d slot p hd hs hp
  simp only [hnp, Bool.false_eq_true, ↓reduceIte] at hA
  exact ⟨id, hpid, hb, ha, hmax, hc, hA⟩

theorem LocalsOkA.storage_any {body : CapturedMir} {ctx : Ctx} {al : List Nat}
    {locals : List LocalSlot} {lm : Map Gen.LocalName Ptr} {allocs : List Gen.Allocation}
    (hlo : LocalsOkA body ctx al locals lm allocs)
    {i : Nat} {d : LocalDecl} {slot : LocalSlot} {p : Ptr}
    (hd : body.localDecls[i]? = some d) (hs : locals[i]? = some slot)
    (hp : mapGet lm (localName i) = some p)
    (hdok : localDeclOk body.layouts d = true) :
    ∃ (id : Nat) (data : List Byte),
      p.provenance = some (⟨(id : Int)⟩, ()) ∧ ctx.base.length ≤ id ∧
      AddrOk p.addr (itOf d body.layouts) ∧
      p.addr + (tyBytes (tyOf d body.layouts) : Int) < 2 ^ 64 ∧
      AddrClass p.addr (tyBytes (tyOf d body.layouts)) ∧
      data.length = tyBytes (tyOf d body.layouts) ∧
      allocs[id]? = some (stackAlloc p.addr (itOf d body.layouts) data) := by
  obtain ⟨id, hpid, hb, ha, hmax, hc, hA⟩ := hlo.storage i d slot p hd hs hp
  have hsl := hlo.slots i d slot hd hs
  cases hp_ty : isPtrTy d.ty with
  | false =>
    simp only [hp_ty, Bool.false_eq_true, ↓reduceIte] at hA
    exact ⟨id, _, hpid, hb, ha, hmax, hc, declSlotData_length_of_declOk hdok hsl, hA⟩
  | true =>
    simp only [hp_ty, ↓reduceIte] at hA
    obtain ⟨hTd, _⟩ := tyOf_isPtrTy (layouts := body.layouts) hp_ty
    match slot, hsl, hA with
    | .dead, hsl, hA =>
      exact ⟨id, _, hpid, hb, ha, hmax, hc, declSlotData_length_of_declOk hdok hsl, hA⟩
    | .uninit, hsl, hA =>
      exact ⟨id, _, hpid, hb, ha, hmax, hc, declSlotData_length_of_declOk hdok hsl, hA⟩
    | .init v, hsl, hA =>
      obtain ⟨pv, rfl⟩ := (DeclSlotOk_of_isPtrTy hp_ty (.init v)).mp hsl
      obtain ⟨tAddr, tProv, _, _, hA'⟩ := hA
      exact ⟨id, ptrBytes tAddr tProv, hpid, hb, ha, hmax, hc,
        by rw [ptrBytes_length, hTd, tyBytes_declPtrTy], hA'⟩

/-- A local that `LocalsOk` keeps out of the locals map is dead. -/
theorem LocalsOk.dead_of_none {body : CapturedMir} {ctx : Ctx} {locals : List LocalSlot}
    {lm : Map Gen.LocalName Ptr} {allocs : List Gen.Allocation}
    (hlo : LocalsOk body ctx locals lm allocs) {i : Nat} {slot : LocalSlot}
    (hs : locals[i]? = some slot) (hp : mapGet lm (localName i) = none) : slot = .dead :=
  LocalsOkA.dead_of_none hlo hs hp

/-- A live local is in the locals map. -/
theorem LocalsOk.some_of_live {body : CapturedMir} {ctx : Ctx} {locals : List LocalSlot}
    {lm : Map Gen.LocalName Ptr} {allocs : List Gen.Allocation}
    (hlo : LocalsOk body ctx locals lm allocs) {i : Nat} {slot : LocalSlot}
    (hs : locals[i]? = some slot) (hlive : slot ≠ .dead) :
    ∃ p, mapGet lm (localName i) = some p :=
  LocalsOkA.some_of_live hlo hs hlive

/-- A dead local that `minimize`'s init block does not allocate is not in the
locals map. -/
theorem LocalsOk.none_of_dead {body : CapturedMir} {ctx : Ctx} {locals : List LocalSlot}
    {lm : Map Gen.LocalName Ptr} {allocs : List Gen.Allocation}
    (hlo : LocalsOk body ctx locals lm allocs) {i : Nat}
    (hs : locals[i]? = some .dead) (hal : i ∉ alwaysStorageLiveLocals body) :
    mapGet lm (localName i) = none :=
  LocalsOkA.none_of_dead hlo hs hal

theorem fragTy_of_scalarTypeOf {d : LocalDecl} {layouts : Layout.LayoutTable}
    {T : Gen.Type} {it : Gen.IntType}
    (hs : scalarTypeOf d.ty = some T) (hT : FragTy T it) :
    FragTy (tyOf d layouts) (itOf d layouts) := by
  rcases scalarTypeOf_cases hs with ⟨hb, _⟩ | ⟨it', hit, _⟩ | ⟨ho, _⟩ | ⟨_, _, rfl⟩
  · obtain ⟨h1, h2⟩ := tyOf_bool (layouts := layouts) hb; rw [h1, h2]; exact .bool
  · obtain ⟨h1, h2⟩ := tyOf_int (layouts := layouts) hit; rw [h1, h2]; exact .int it' (intTypeOf_good hit)
  · obtain ⟨h1, h2⟩ := tyOf_ordering (layouts := layouts) ho; rw [h1, h2]; exact .ordering
  · cases hT

/-- A scalar-family fragment operand of MiniRust type `T`: projection-free
locals, constants, and single-level field projections `.field 0` and `.field 1`
on `(Int, bool)` 2-tuple locals. -/
def OperandOkT (layouts : Layout.LayoutTable := ⟨64, true, []⟩)
    (decls : List LocalDecl) (T : Gen.Type) : Operand → Prop
  | .copy ⟨j, []⟩ => j < decls.length ∧ operandType layouts decls (.copy ⟨j, []⟩) = some T
  | .copy ⟨j, [.field 0 fTy]⟩ =>
    j < decls.length ∧ (∃ d, decls[j]? = some d ∧ (intBoolTupleOf d.ty).isSome = true) ∧
      operandType layouts decls (.copy ⟨j, [.field 0 fTy]⟩) = some T
  | .copy ⟨j, [.field 1 fTy]⟩ =>
    j < decls.length ∧ (∃ d, decls[j]? = some d ∧ (intBoolTupleOf d.ty).isSome = true) ∧
      operandType layouts decls (.copy ⟨j, [.field 1 fTy]⟩) = some T
  | .constant c =>
    operandType layouts decls (.constant c) = some T ∧ (translateOperand decls (.constant c)).isSome
  | _ => False

theorem operandType_of_operandIntType {layouts : Layout.LayoutTable}
    {decls : List LocalDecl} {it : Gen.IntType} {op : Operand}
    (h : operandIntType layouts decls op = some it) :
    operandType layouts decls op = some (.Int it) := by
  match op, h with
  | .copy ⟨j, []⟩, h =>
    simp only [operandIntType, placeIntType] at h
    simp only [operandType]
    cases hd : decls[j]? with
    | none => simp [hd] at h
    | some d => simp [hd] at h ⊢; exact scalarTypeOf_int h
  | .copy ⟨j, [.field 1 fTy]⟩, h =>
    simp only [operandIntType] at h
    simp only [operandType]
    cases hd : decls[j]? with
    | none => simp [placeIntType, hd] at h
    | some d =>
      cases ht : intBoolTupleOf d.ty with
      | some _ => simp [placeIntType, hd, ht] at h
      | none => simp [ht, h]
  | .copy ⟨j, [.field 0 fTy]⟩, h
  | .copy ⟨j, [.field (.succ (.succ _)) fTy]⟩, h
  | .copy ⟨j, .field _ _ :: _ :: _⟩, h
  | .copy ⟨j, [.index _]⟩, h
  | .copy ⟨j, [.constantIndex _ _ _]⟩, h =>
    simp only [operandIntType] at h
    simp [operandType, h]
  | .copy ⟨j, [.deref]⟩, h
  | .copy ⟨j, [.subslice _ _ _]⟩, h
  | .copy ⟨j, [.downcast _ _]⟩, h
  | .copy ⟨j, [.opaqueCast _]⟩, h
  | .copy ⟨j, [.unwrapUnsafeBinder _]⟩, h
  | .copy ⟨j, .index _ :: _ :: _⟩, h
  | .copy ⟨j, .constantIndex _ _ _ :: _ :: _⟩, h
  | .copy ⟨j, .deref :: _ :: _⟩, h
  | .copy ⟨j, .subslice _ _ _ :: _ :: _⟩, h
  | .copy ⟨j, .downcast _ _ :: _ :: _⟩, h
  | .copy ⟨j, .opaqueCast _ :: _ :: _⟩, h
  | .copy ⟨j, .unwrapUnsafeBinder _ :: _ :: _⟩, h =>
    simp [operandIntType, placeIntType] at h
  | .constant c, h => simp only [operandIntType] at h; exact scalarTypeOf_int h
  | .move _, h => simp [operandIntType] at h

theorem operandIsBool_iff {layouts : Layout.LayoutTable} {decls : List LocalDecl} {op : Operand} :
    operandIsBool layouts decls op = true ↔ operandType layouts decls op = some .Bool := by
  unfold operandIsBool
  split <;> simp_all

theorem operandOkB_T {layouts : Layout.LayoutTable} {decls : List LocalDecl} {op : Operand}
    (h : operandOkB layouts decls op = true) : OperandOkT layouts decls .Bool op := by
  match op, h with
  | .copy ⟨j, []⟩, h =>
    simp only [operandOkB, Bool.and_eq_true, decide_eq_true_eq, operandIsBool_iff] at h
    exact h
  | .copy ⟨j, [.field 1 fTy]⟩, h =>
    simp only [operandOkB, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hj, hty⟩ := h
    cases hd : decls[j]? with
    | none => simp [hd] at hty
    | some d =>
      cases ht : intBoolTupleOf d.ty with
      | none => simp [hd, ht] at hty
      | some it =>
        simp only [hd, ht, Option.bind_eq_bind, Option.bind_some] at hty
        exact ⟨hj, ⟨d, hd, by simp [ht]⟩, by simp [operandType, hd, ht, hty]⟩
  | .constant c, h =>
    simp only [operandOkB, Bool.and_eq_true, operandIsBool_iff] at h
    exact h
  | .move _, h
  | .copy ⟨_, [.field 0 _]⟩, h
  | .copy ⟨_, [.field (.succ (.succ _)) _]⟩, h
  | .copy ⟨_, .field _ _ :: _ :: _⟩, h
  | .copy ⟨_, .deref :: _⟩, h
  | .copy ⟨_, .index _ :: _⟩, h
  | .copy ⟨_, .constantIndex _ _ _ :: _⟩, h
  | .copy ⟨_, .subslice _ _ _ :: _⟩, h
  | .copy ⟨_, .downcast _ _ :: _⟩, h
  | .copy ⟨_, .opaqueCast _ :: _⟩, h
  | .copy ⟨_, .unwrapUnsafeBinder _ :: _⟩, h =>
    simp [operandOkB] at h

theorem operandType_of_operandOkB {layouts : Layout.LayoutTable}
    {decls : List LocalDecl} {op : Operand}
    (h : operandOkB layouts decls op = true) : operandType layouts decls op = some .Bool := by
  have hT := operandOkB_T h
  match op, hT with
  | .copy ⟨_, []⟩, ⟨_, hty⟩ | .copy ⟨_, [.field 1 _]⟩, ⟨_, _, hty⟩ | .constant _, ⟨hty, _⟩ =>
    exact hty

theorem operandType_of_operandIsOrdering {layouts : Layout.LayoutTable}
    {decls : List LocalDecl} {op : Operand}
    (h : operandIsOrdering decls op = true) : operandType layouts decls op = some orderingTy := by
  match op, h with
  | .copy ⟨j, []⟩, h =>
    simp only [operandIsOrdering] at h
    simp only [operandType]
    cases hd : decls[j]? with
    | none => simp [hd] at h
    | some d => simp [hd] at h ⊢; exact scalarTypeOf_ordering h
  | .constant c, h => simp only [operandIsOrdering] at h; exact scalarTypeOf_ordering h

theorem operandOkO_T {layouts : Layout.LayoutTable} {decls : List LocalDecl} {op : Operand}
    (h : operandOkO decls op = true) : OperandOkT layouts decls orderingTy op := by
  match op, h with
  | .copy ⟨j, []⟩, h =>
    simp only [operandOkO, Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨h.1, operandType_of_operandIsOrdering h.2⟩
  | .constant c, h =>
    simp only [operandOkO, Bool.and_eq_true] at h
    exact ⟨operandType_of_operandIsOrdering h.1, h.2⟩
  | .move _, h | .copy ⟨_, _ :: _⟩, h => simp [operandOkO] at h

/-- Evaluating a translated fragment operand of fragment type `T`. -/
theorem evalValue_operandT {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {locals : List LocalSlot} {lm : Map Gen.LocalName Ptr} {m : Mach} {blk stmt : Nat}
    (h : FrameOk body f ctx locals lm m blk stmt)
    {T : Gen.Type} {it : Gen.IntType} (hT : FragTy T it) (op : Operand)
    (hok : OperandOkT body.layouts body.localDecls T op)
    (e : Gen.ValueExpr) (he : translateOperand body.localDecls op = some e) :
    (∀ bits, opBits locals op = some bits →
      ValidBits T bits ∧
      ∃ m', evalValue m e = .ok ((valOf T bits, T), m') ∧
        FrameOk body f ctx locals lm m' blk stmt) ∧
    (opBits locals op = none → ∃ msg, evalValue m e = .error (.ub msg)) := by
  have hshape := h.shape
  have hlo := h.locs
  match op, hok, he with
  | .copy ⟨j, []⟩, hok, he =>
    obtain ⟨hj, hty⟩ := hok
    simp only [translateOperand, translatePlace, Option.map_some, Option.some.injEq] at he
    subst he
    obtain ⟨d, slot, hd, hs⟩ := h.slot_exists j hj
    have hspec := h.hf.2 j d hd
    simp only [operandType, hd, Option.bind_eq_bind, Option.bind_some] at hty
    have hTd : tyOf d body.layouts = T := tyOf_of_scalarTypeOf hty
    have hfragd : FragTy (tyOf d body.layouts) (itOf d body.layouts) :=
      fragTy_of_scalarTypeOf hty hT
    have hitd : itOf d body.layouts = it := hfragd.unique (hTd ▸ hT)
    have hloc := hspec.2
    rw [hTd] at hloc
    have hslot := (DeclSlotOk_of_scalarTypeOf hty slot).mp (hlo.slots j d slot hd hs)
    rw [hTd] at hslot
    cases hp : mapGet lm (localName j) with
    | none =>
      have hdead := hlo.dead_of_none hs hp
      subst hdead
      refine ⟨fun bits hb => by simp [opBits, hs] at hb, fun _ => ?_⟩
      exact ⟨"access to a dead local", by simp [evalValue, evalPlace_local_none hshape j _ hloc hp]⟩
    | some p =>
      obtain ⟨k, hpk, _, _, _, _, hA⟩ :=
        hlo.storage_nonptr j d slot p hd hs hp (isPtrTy_false_of_scalarTypeOf hty)
      rw [hfragd.declSlotData, hitd] at hA
      have hplace := evalPlace_local_some hshape j _ hloc p hp
      match slot, hslot, hA with
      | .dead, _, hA =>
        refine ⟨fun bits hb => by simp [opBits, hs] at hb, fun _ => ?_⟩
        obtain ⟨msg, hmsg⟩ := typedLoad_ptr_frag_uninit hshape p k hpk hT hA
        exact ⟨msg, by simp [evalValue, hplace, placeLoad, hmsg]⟩
      | .uninit, _, hA =>
        refine ⟨fun bits hb => by simp [opBits, hs] at hb, fun _ => ?_⟩
        obtain ⟨msg, hmsg⟩ := typedLoad_ptr_frag_uninit hshape p k hpk hT hA
        exact ⟨msg, by simp [evalValue, hplace, placeLoad, hmsg]⟩
      | .init (.scalar sc), hok', hA =>
        obtain ⟨_, hb⟩ := hok'
        refine ⟨fun bits hbits => ?_, fun hnone => by simp [opBits, hs] at hnone⟩
        simp [opBits, hs] at hbits
        subst hbits
        obtain ⟨m', hm', hshape'⟩ := typedLoad_ptr_frag hshape p k hpk hT sc.bits hb hA
        exact ⟨hb, m', by simp [evalValue, hplace, placeLoad, hm'],
          FrameOk.mk' h.hf hshape' hlo h.declsOk h.nonScalar⟩
      | .init (.aggregate 0 [.scalar sc0, .scalar sc1]), ⟨_, htyT, _⟩, _ =>
        cases hT <;> simp at htyT
  | .copy ⟨j, [.field 0 fTy]⟩, hok, he =>
    obtain ⟨hj, ⟨d, hd, htSome⟩, hty⟩ := hok
    have hcast0 : ((0 : Nat) : Int) = 0 := rfl
    simp only [translateOperand, translatePlace, translateFieldPlace, hcast0,
      Option.map_some, Option.some.injEq] at he
    subst he
    obtain ⟨_, slot, _, hs⟩ := h.slot_exists j hj
    simp only [operandType, placeIntType, Option.bind_eq_bind, hd, Option.bind_some] at hty
    cases ht : intBoolTupleOf d.ty with
    | none => simp [ht] at htSome
    | some it' =>
      cases hf : intTypeOf fTy with
      | none => simp [ht, hf] at hty
      | some fIt =>
        simp only [ht, hf, Option.bind_some] at hty
        by_cases heq : fIt = it'
        · subst heq
          simp at hty
          subst hty
          cases hT with
          | int _ hgood =>
            obtain ⟨hTd, hitd⟩ := tyOf_tuple (layouts := body.layouts) ht
            have hspec := h.hf.2 j d hd
            have hloc := hspec.2
            rw [hTd] at hloc
            have hslot := (DeclSlotOk_of_scalarTypeOf (scalarTypeOf_tuple ht) slot).mp
              (hlo.slots j d slot hd hs)
            rw [hTd] at hslot
            cases hp : mapGet lm (localName j) with
            | none =>
              have hdead := hlo.dead_of_none hs hp
              subst hdead
              refine ⟨fun bits hb => by simp [opBits, hs] at hb, fun _ => ?_⟩
              exact ⟨"access to a dead local", by simp [evalValue, evalPlace_field_none hshape j _ hloc hp]⟩
            | some p =>
              obtain ⟨k, hpk, _, haddr, _, _, hA⟩ :=
                hlo.storage_nonptr j d slot p hd hs hp
                  (isPtrTy_false_of_scalarTypeOf (scalarTypeOf_tuple ht))
              rw [declSlotData_of_some ht, hitd] at hA
              rw [hitd] at haddr
              have hplace := evalPlace_field0L hshape j it hgood hloc p hp haddr
              match slot, hslot, hA with
              | .dead, _, hA =>
                refine ⟨fun bits hb => by simp [opBits, hs] at hb, fun _ => ?_⟩
                obtain ⟨msg, hmsg⟩ := typedLoad_ptr_tuple_field0_uninit hshape p k hpk it hgood hA
                exact ⟨msg, by simp [evalValue, hplace, placeLoad, hmsg]⟩
              | .uninit, _, hA =>
                refine ⟨fun bits hb => by simp [opBits, hs] at hb, fun _ => ?_⟩
                obtain ⟨msg, hmsg⟩ := typedLoad_ptr_tuple_field0_uninit hshape p k hpk it hgood hA
                exact ⟨msg, by simp [evalValue, hplace, placeLoad, hmsg]⟩
              | .init (.scalar sc), ⟨_, hb⟩, _ =>
                simp [intBoolTupleTy, ValidBits] at hb
              | .init (.aggregate 0 [.scalar sc0, .scalar sc1]), ⟨it'', htyT, _, hb0, _, _⟩, hA =>
                simp only [tupleIntOfTy_intBoolTupleTy, Option.some.injEq] at htyT
                subst htyT
                refine ⟨fun bits hbits => ?_, fun hnone => by simp [opBits, readFieldPath, hs] at hnone⟩
                simp [opBits, readFieldPath, hs] at hbits
                subst hbits
                obtain ⟨m', hm', hshape'⟩ :=
                  typedLoad_ptr_tuple_field0 hshape p k hpk it hgood sc0.bits sc1.bits hb0 hA
                exact ⟨hb0, m', by simp [evalValue, hplace, placeLoad, hm', valOf],
                  FrameOk.mk' h.hf hshape' hlo h.declsOk h.nonScalar⟩
        · simp [heq] at hty
  | .copy ⟨j, [.field 1 fTy]⟩, hok, he =>
    obtain ⟨hj, ⟨d, hd, htSome⟩, hty⟩ := hok
    have hcast1 : ((1 : Nat) : Int) = 1 := rfl
    simp only [translateOperand, translatePlace, translateFieldPlace, hcast1,
      Option.map_some, Option.some.injEq] at he
    subst he
    obtain ⟨_, slot, _, hs⟩ := h.slot_exists j hj
    simp only [operandType, Option.bind_eq_bind, hd, Option.bind_some] at hty
    cases ht : intBoolTupleOf d.ty with
    | none => simp [ht] at htSome
    | some it' =>
      simp only [ht] at hty
      by_cases hb : isBoolTy fTy = true
      · simp only [hb, ↓reduceIte, Option.some.injEq] at hty
        subst hty
        cases hT with
        | bool =>
          have hgood := intBoolTupleOf_good ht
          obtain ⟨hTd, hitd⟩ := tyOf_tuple (layouts := body.layouts) ht
          have hspec := h.hf.2 j d hd
          have hloc := hspec.2
          rw [hTd] at hloc
          have hslot := (DeclSlotOk_of_scalarTypeOf (scalarTypeOf_tuple ht) slot).mp
            (hlo.slots j d slot hd hs)
          rw [hTd] at hslot
          cases hp : mapGet lm (localName j) with
          | none =>
            have hdead := hlo.dead_of_none hs hp
            subst hdead
            refine ⟨fun bits hb => by simp [opBits, hs] at hb, fun _ => ?_⟩
            exact ⟨"access to a dead local", by simp [evalValue, evalPlace_field_none hshape j _ hloc hp]⟩
          | some p =>
            obtain ⟨k, hpk, _, haddr, _, _, hA⟩ :=
              hlo.storage_nonptr j d slot p hd hs hp
                (isPtrTy_false_of_scalarTypeOf (scalarTypeOf_tuple ht))
            rw [declSlotData_of_some ht, hitd] at hA
            rw [hitd] at haddr
            have hlen := tupleSlotData_length it' slot hgood.pos
            have hplace := evalPlace_field1L hshape j it' hgood hloc p hp k hpk _ hA hlen haddr
            match slot, hslot, hA with
            | .dead, _, hA =>
              refine ⟨fun bits hb => by simp [opBits, hs] at hb, fun _ => ?_⟩
              obtain ⟨msg, hmsg⟩ := typedLoad_ptr_tuple_field1_uninit hshape p k hpk it' hgood hA
              exact ⟨msg, by simp [evalValue, hplace, placeLoad, hmsg]⟩
            | .uninit, _, hA =>
              refine ⟨fun bits hb => by simp [opBits, hs] at hb, fun _ => ?_⟩
              obtain ⟨msg, hmsg⟩ := typedLoad_ptr_tuple_field1_uninit hshape p k hpk it' hgood hA
              exact ⟨msg, by simp [evalValue, hplace, placeLoad, hmsg]⟩
            | .init (.scalar sc), ⟨_, hb⟩, _ =>
              simp [intBoolTupleTy, ValidBits] at hb
            | .init (.aggregate 0 [.scalar sc0, .scalar sc1]), ⟨it'', htyT, _, _, _, hb1⟩, hA =>
              simp only [tupleIntOfTy_intBoolTupleTy, Option.some.injEq] at htyT
              subst htyT
              refine ⟨fun bits hbits => ?_, fun hnone => by simp [opBits, readFieldPath, hs] at hnone⟩
              simp [opBits, readFieldPath, hs] at hbits
              subst hbits
              obtain ⟨m', hm', hshape'⟩ :=
                typedLoad_ptr_tuple_field1 hshape p k hpk it' hgood sc0.bits sc1.bits hb1 hA
              exact ⟨hb1, m', by simp [evalValue, hplace, placeLoad, hm', valOf],
                FrameOk.mk' h.hf hshape' hlo h.declsOk h.nonScalar⟩
      · simp [hb] at hty
  | .constant c, hok, he =>
    obtain ⟨hty, _⟩ := hok
    simp only [operandType] at hty
    rcases scalarTypeOf_cases hty with ⟨hb, hTb⟩ | ⟨it', hit', hTi⟩ | ⟨ho, _⟩ | ⟨_, ht, _⟩
    · subst hTb
      simp only [translateOperand, hb, ↓reduceIte] at he
      match hv : c.val, he with
      | .scalar (.int ⟨bits, sz⟩), he =>
        simp only at he
        split at he
        · next hc =>
          simp only [Option.some.injEq] at he
          subst he
          obtain ⟨_, hb2⟩ := hc
          refine ⟨fun bits' hbits => ?_, fun hnone => by simp [opBits, hv] at hnone⟩
          simp [opBits, hv] at hbits
          subst hbits
          exact ⟨hb2, m, by simp [evalValue, evalConstant, valOf], h⟩
        · simp at he
    · subst hTi
      simp only [translateOperand, intTypeOf_isBoolTy hit', hit', Bool.false_eq_true,
        ↓reduceIte] at he
      match hv : c.val, he with
      | .scalar (.int ⟨bits, sz⟩), he =>
        simp only at he
        split at he
        · next hc =>
          simp only [Option.some.injEq] at he
          subst he
          obtain ⟨hsz, hb⟩ := hc
          subst hsz
          refine ⟨fun bits' hbits => ?_, fun hnone => by simp [opBits, hv] at hnone⟩
          simp [opBits, hv] at hbits
          subst hbits
          exact ⟨hb, m, by simp [evalValue, evalConstant, valOf], h⟩
        · simp at he
    · simp [translateOperand_ordering_const ho] at he
    · simp [translateOperand_tuple_const ht] at he

theorem operandOk_good {layouts : Layout.LayoutTable}
    {decls : List LocalDecl} {it : Gen.IntType} {op : Operand}
    (hok : operandOk layouts decls it op = true) : GoodSize it.size.bytes := by
  have hit := operandIntType_of_operandOk hok
  match op, hit with
  | .copy ⟨j, []⟩, hit =>
    simp only [operandIntType, placeIntType] at hit
    cases hd : decls[j]? with
    | none => simp [hd] at hit
    | some d => simp [hd] at hit; exact intTypeOf_good hit
  | .copy ⟨j, [.index _]⟩, hit | .copy ⟨j, [.constantIndex _ _ _]⟩, hit =>
    simp only [operandIntType, placeIntType, Option.bind_eq_bind] at hit
    cases hd : decls[j]? with
    | none => simp [hd] at hit
    | some d =>
      simp only [hd, Option.bind_some] at hit
      cases ha : arrayTypeOf d.ty with
      | none => simp [ha] at hit
      | some p =>
        obtain ⟨elemIt, count⟩ := p
        simp [ha] at hit
        subst hit
        exact arrayTypeOf_good ha
  | .copy ⟨j, .field idx fTy :: rest⟩, hit =>
    simp only [operandIntType, placeIntType, Option.bind_eq_bind] at hit
    cases hd : decls[j]? with
    | none => simp [hd] at hit
    | some d =>
      simp only [hd, Option.bind_some] at hit
      cases hij : intBoolTupleOf d.ty with
      | some it' =>
        simp only [hij] at hit
        cases idx with
        | zero =>
          cases rest with
          | nil =>
            cases hf : intTypeOf fTy with
            | none => simp [hf] at hit
            | some fIt =>
              simp only [hf, Option.bind_some] at hit
              by_cases heq : fIt = it'
              · simp [heq] at hit; subst hit; exact intBoolTupleOf_good hij
              · simp [heq] at hit
          | cons _ _ => simp at hit
        | succ _ => simp at hit
      | none =>
        simp only [hij] at hit
        cases ht : tupleTypeOf layouts d.ty with
        | none => simp [ht] at hit
        | some p =>
          obtain ⟨fields, size, align⟩ := p
          simp only [ht, Option.bind_some] at hit
          cases hres : resolveFieldPath layouts (.tuple fields size align) (.field idx fTy :: rest) with
          | none => simp [hres] at hit
          | some rpair =>
            obtain ⟨_, leafSpec⟩ := rpair
            simp only [hres, Option.bind_some] at hit
            cases leafSpec with
            | tuple _ _ _ => simp at hit
            | scalar leafIt =>
              simp at hit
              subst hit
              obtain ⟨leafTy, _, _, hspec⟩ :=
                resolveFieldPath_ty (specOfRigidTy_of_tupleTypeOf ht) hres
              exact intTypeOf_good (intTypeOf_of_specOfRigidTy_scalar hspec)
  | .copy ⟨j, [.deref]⟩, hit
  | .copy ⟨j, [.subslice _ _ _]⟩, hit
  | .copy ⟨j, [.downcast _ _]⟩, hit
  | .copy ⟨j, [.opaqueCast _]⟩, hit
  | .copy ⟨j, [.unwrapUnsafeBinder _]⟩, hit
  | .copy ⟨j, .index _ :: _ :: _⟩, hit
  | .copy ⟨j, .constantIndex _ _ _ :: _ :: _⟩, hit
  | .copy ⟨j, .deref :: _ :: _⟩, hit
  | .copy ⟨j, .subslice _ _ _ :: _ :: _⟩, hit
  | .copy ⟨j, .downcast _ _ :: _ :: _⟩, hit
  | .copy ⟨j, .opaqueCast _ :: _ :: _⟩, hit
  | .copy ⟨j, .unwrapUnsafeBinder _ :: _ :: _⟩, hit =>
    simp [operandIntType, placeIntType] at hit
  | .constant c, hit => simp only [operandIntType] at hit; exact intTypeOf_good hit

/-- Evaluating a translated array projection place `arr[proj]` behind pointer `p`. -/
theorem evalPlace_proj {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {locals : List LocalSlot} {lm : Map Gen.LocalName Ptr} {m : Mach} {blk stmt : Nat}
    (h : FrameOk body f ctx locals lm m blk stmt)
    (j : Nat) (d : LocalDecl) (hd : body.localDecls[j]? = some d)
    (elemIt : Gen.IntType) (count : Nat) (ha : arrayTypeOf d.ty = some (elemIt, count))
    (p : Ptr) (hp : mapGet lm (localName j) = some p)
    (proj : ProjectionElem) (hproj : projOk body.localDecls count proj = true)
    (pe : Gen.PlaceExpr) (hpe : translatePlace body.localDecls ⟨j, [proj]⟩ = some pe) :
    (∀ idx, projIdx locals count proj = some idx →
      idx < count ∧
      ∃ m', evalPlace m pe =
          .ok (({ ptr := { thin_pointer := offsetPtr p (idx * elemIt.size.bytes), metadata := none },
                   aligned := true }, .Int elemIt), m') ∧
        FrameOk body f ctx locals lm m' blk stmt) ∧
    (projIdx locals count proj = none → ∃ msg, evalPlace m pe = .error (.ub msg)) := by
  have hj : j < body.localDecls.length := (List.getElem?_eq_some_iff.mp hd).1
  have hgood := arrayTypeOf_good ha
  have hbound := h.array_bound j d elemIt count hd ha
  obtain ⟨hTd, hitd⟩ := tyOf_array (layouts := body.layouts) ha
  have hloc := (h.hf.2 j d hd).2
  rw [hTd] at hloc
  have hplaceBase := evalPlace_local_some h.shape j _ hloc p hp
  obtain ⟨_, slot, hd', hs⟩ := h.slot_exists j hj
  rw [hd] at hd'; cases hd'
  have hslot := h.slots j d slot hd hs
  have hdlen : (declSlotData d slot body.layouts).length = count * elemIt.size.bytes := by
    have hlen' := declSlotData_length_of_declOk (h.declsOk d (List.mem_of_getElem? hd)) hslot
    rw [hTd] at hlen'
    simpa [tyBytes] using hlen'
  match proj, hproj, hpe with
  | .index idxLocal, hproj, hpe =>
    simp only [translatePlace, Option.some.injEq] at hpe
    subst hpe
    simp only [projOk, Bool.and_eq_true, decide_eq_true_eq] at hproj
    obtain ⟨hidxLt, hproj⟩ := hproj
    cases hdIdx : body.localDecls[idxLocal]? with
    | none => simp [hdIdx] at hproj
    | some idxDecl =>
      simp only [hdIdx, Option.bind_eq_bind, Option.bind_some] at hproj
      cases hitIdx : intTypeOf idxDecl.ty with
      | none => simp [hitIdx] at hproj
      | some idxIt =>
        simp only [hitIdx, decide_eq_true_eq] at hproj
        have hgoodIdx := intTypeOf_good hitIdx
        have hokIdxT : OperandOkT body.layouts body.localDecls (.Int idxIt) (.copy ⟨idxLocal, []⟩) :=
          ⟨hidxLt, by simp [operandType, hdIdx, scalarTypeOf_int hitIdx]⟩
        obtain ⟨haok, hanone⟩ := evalValue_operandT h (.int idxIt hgoodIdx) (.copy ⟨idxLocal, []⟩)
          hokIdxT (.Load (.Local (localName idxLocal))) (by simp [translateOperand, translatePlace])
        cases hbIdx : opBits locals (.copy ⟨idxLocal, []⟩) with
        | none =>
          have hpjNone : projIdx locals count (.index idxLocal) = none := by
            cases hsIdx : locals[idxLocal]? with
            | none => simp [projIdx, hsIdx]
            | some sl =>
              cases sl with
              | dead | uninit => simp [projIdx, hsIdx]
              | init v =>
                cases v with
                | scalar sc => simp [opBits, hsIdx] at hbIdx
                | _ => simp [projIdx, hsIdx]
          refine ⟨fun idx hidx => by simp [hpjNone] at hidx, fun _ => ?_⟩
          obtain ⟨msg, hmsg⟩ := hanone hbIdx
          refine ⟨msg, ?_⟩
          rw [evalPlace]
          simp [hplaceBase, hmsg]
        | some bits =>
          obtain ⟨hscBits, m1, hm1, h1⟩ := haok bits hbIdx
          have hpjEq : projIdx locals count (.index idxLocal) =
              if bits < count then some bits else none := by
            cases hsIdx : locals[idxLocal]? with
            | none => simp [opBits, hsIdx] at hbIdx
            | some sl =>
              cases sl with
              | dead | uninit => simp [opBits, hsIdx] at hbIdx
              | init v =>
                cases v with
                | scalar sc =>
                  simp [opBits, hsIdx] at hbIdx
                  subst hbIdx
                  simp [projIdx, hsIdx]
                | _ => simp [opBits, hsIdx] at hbIdx
          by_cases hlt : bits < count
          · refine ⟨fun idx hidx => ?_, fun hnone => by simp [hpjEq, hlt] at hnone⟩
            simp [hpjEq, hlt] at hidx
            subst hidx
            have hib : intFromBits bits idxIt = (bits : Int) := by
              rcases hproj with huns | hcnt
              · simp [intFromBits, huns]
              · unfold intFromBits
                split
                · rfl
                · have : ¬ (bits ≥ 2 ^ (8 * idxIt.size.bytes - 1)) := by omega
                  simp [this]
            have hnot_le : ¬ (count ≤ bits) := Nat.not_le.mpr hlt
            have hoff_le : bits * elemIt.size.bytes ≤ (declSlotData d slot body.layouts).length := by
              rw [hdlen]
              exact Nat.mul_le_mul_right _ (by omega)
            have hoff_bound : bits * elemIt.size.bytes < 2 ^ 63 := by
              have : bits * elemIt.size.bytes ≤ count * elemIt.size.bytes :=
                Nat.mul_le_mul_right _ (by omega)
              omega
            obtain ⟨k, hpk, _, haddr, haddrMax, _, hA1⟩ :=
              h1.locs.storage_nonptr j d slot p hd hs hp (isPtrTy_false_of_arrayTypeOf ha)
            rw [hitd] at hA1
            rw [hTd] at haddrMax
            simp only [tyBytes, Int.ofNat_eq_natCast, Int.toNat_natCast] at haddrMax
            have hptr := ptrOffsetInbounds_ptr_elem h1.shape p k hpk bits elemIt
              (declSlotData d slot body.layouts) hA1 hoff_le hoff_bound haddr.nonneg
              (by rw [hdlen]; exact haddrMax)
            have hsz : bits * elemIt.size.bytes ≤ count * elemIt.size.bytes :=
              Nat.mul_le_mul_right _ (by omega)
            refine ⟨hlt, m1, ?_, h1⟩
            rw [evalPlace]
            simp only [valOf] at hm1
            simp [hplaceBase, hm1, hib, hnot_le, layout_eq _ hgood,
              layout_array_eq _ _ hgood, computeSize, LayoutStrategy.compute_size_and_align,
              hsz, hptr, ThinPointer.widen]
          · refine ⟨fun idx hidx => by simp [hpjEq, hlt] at hidx, fun _ => ?_⟩
            have hoob : intFromBits bits idxIt < 0 ∨ intFromBits bits idxIt ≥ (count : Int) := by
              unfold intFromBits
              split
              · right; omega
              · split
                · right; omega
                · left
                  have : (bits : Int) < (2 : Int) ^ (8 * idxIt.size.bytes) := by exact_mod_cast hscBits
                  omega
            refine ⟨"access to out-of-bounds index", ?_⟩
            rw [evalPlace]
            simp only [valOf] at hm1
            simp [hplaceBase, hm1, hoob, ub]
  | .constantIndex offset minLength fromEnd, hproj, hpe =>
    simp only [projOk, Bool.and_eq_true, decide_eq_true_eq] at hproj
    obtain ⟨⟨hmin, hoffBound⟩, hfe⟩ := hproj
    have hcond : minLength ≤ count ∧ (!fromEnd = true ∨ 1 ≤ offset ∧ offset ≤ count) := by
      refine ⟨hmin, ?_⟩
      cases fromEnd <;> simp at hfe ⊢
      exact hfe
    simp only [translatePlace, hd, Option.bind_eq_bind, Option.bind_some, ha,
      Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hpe
    have hcond' : minLength ≤ count ∧ (fromEnd = false ∨ 1 ≤ offset ∧ offset ≤ count) := by
      simpa using hcond
    simp [hcond'] at hpe
    subst hpe
    have hnot_min : ¬ (count < minLength) := by omega
    generalize hidx_eq : (if fromEnd = true then count - offset else offset) = idx
    by_cases hidx_lt : idx < count
    · refine ⟨fun idx' hidx' => ?_, fun hnone => by simp [projIdx, hnot_min, hidx_eq, hidx_lt] at hnone⟩
      simp only [projIdx, hnot_min, ↓reduceIte, hidx_eq, hidx_lt, Option.some.injEq] at hidx'
      subst hidx'
      have hnot_le : ¬ (count ≤ idx) := Nat.not_le.mpr hidx_lt
      have hoff_le : idx * elemIt.size.bytes ≤ (declSlotData d slot body.layouts).length := by
        rw [hdlen]
        exact Nat.mul_le_mul_right _ (by omega)
      have hoff_bound : idx * elemIt.size.bytes < 2 ^ 63 := by
        have : idx * elemIt.size.bytes ≤ count * elemIt.size.bytes :=
          Nat.mul_le_mul_right _ (by omega)
        omega
      obtain ⟨k, hpk, _, haddr, haddrMax, _, hA⟩ :=
        h.locs.storage_nonptr j d slot p hd hs hp (isPtrTy_false_of_arrayTypeOf ha)
      rw [hitd] at hA
      rw [hTd] at haddrMax
      simp only [tyBytes, Int.ofNat_eq_natCast, Int.toNat_natCast] at haddrMax
      have hptr := ptrOffsetInbounds_ptr_elem h.shape p k hpk idx elemIt
        (declSlotData d slot body.layouts) hA hoff_le hoff_bound haddr.nonneg
        (by rw [hdlen]; exact haddrMax)
      have hsz : idx * elemIt.size.bytes ≤ count * elemIt.size.bytes :=
        Nat.mul_le_mul_right _ (by omega)
      refine ⟨hidx_lt, m, ?_, h⟩
      rw [evalPlace]
      simp [hplaceBase, evalValue, evalConstant, hnot_le, layout_eq _ hgood,
        layout_array_eq _ _ hgood, computeSize, LayoutStrategy.compute_size_and_align,
        hsz, hptr, ThinPointer.widen]
    · refine ⟨fun idx' hidx' => by simp [projIdx, hnot_min, hidx_eq, hidx_lt] at hidx', fun _ => ?_⟩
      have hle_cnt : (count : Int) ≤ (idx : Int) := by omega
      refine ⟨"access to out-of-bounds index", ?_⟩
      rw [evalPlace]
      simp [hplaceBase, evalValue, evalConstant, hle_cnt, ub]

/-- `evalPlace_proj` for an in-bounds `ConstantIndex` projection: the index is
a constant, so evaluating the place leaves the machine unchanged. -/
theorem evalPlace_constantIndex_same {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {locals : List LocalSlot} {lm : Map Gen.LocalName Ptr} {m : Mach} {blk stmt : Nat}
    (h : FrameOk body f ctx locals lm m blk stmt)
    (j : Nat) (d : LocalDecl) (hd : body.localDecls[j]? = some d)
    (elemIt : Gen.IntType) (count : Nat) (ha : arrayTypeOf d.ty = some (elemIt, count))
    (p : Ptr) (hp : mapGet lm (localName j) = some p)
    (offset minLength : Nat) (fromEnd : Bool)
    (hproj : projOk body.localDecls count (.constantIndex offset minLength fromEnd) = true)
    (pe : Gen.PlaceExpr)
    (hpe : translatePlace body.localDecls ⟨j, [.constantIndex offset minLength fromEnd]⟩ = some pe)
    (idx : Nat) (hidx : projIdx locals count (.constantIndex offset minLength fromEnd) = some idx) :
    evalPlace m pe =
      .ok (({ ptr := { thin_pointer := offsetPtr p (idx * elemIt.size.bytes), metadata := none },
               aligned := true }, .Int elemIt), m) := by
  have hj : j < body.localDecls.length := (List.getElem?_eq_some_iff.mp hd).1
  have hgood := arrayTypeOf_good ha
  have hbound := h.array_bound j d elemIt count hd ha
  obtain ⟨hTd, hitd⟩ := tyOf_array (layouts := body.layouts) ha
  have hloc := (h.hf.2 j d hd).2
  rw [hTd] at hloc
  have hplaceBase := evalPlace_local_some h.shape j _ hloc p hp
  obtain ⟨_, slot, hd', hs⟩ := h.slot_exists j hj
  rw [hd] at hd'; cases hd'
  have hslot := h.slots j d slot hd hs
  have hdlen : (declSlotData d slot body.layouts).length = count * elemIt.size.bytes := by
    have hlen' := declSlotData_length_of_declOk (h.declsOk d (List.mem_of_getElem? hd)) hslot
    rw [hTd] at hlen'
    simpa [tyBytes] using hlen'
  simp only [projOk, Bool.and_eq_true, decide_eq_true_eq] at hproj
  obtain ⟨⟨hmin, hoffBound⟩, hfe⟩ := hproj
  have hcond : minLength ≤ count ∧ (!fromEnd = true ∨ 1 ≤ offset ∧ offset ≤ count) := by
    refine ⟨hmin, ?_⟩
    cases fromEnd <;> simp at hfe ⊢
    exact hfe
  simp only [translatePlace, hd, Option.bind_eq_bind, Option.bind_some, ha,
    Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hpe
  have hcond' : minLength ≤ count ∧ (fromEnd = false ∨ 1 ≤ offset ∧ offset ≤ count) := by
    simpa using hcond
  simp [hcond'] at hpe
  subst hpe
  have hnot_min : ¬ (count < minLength) := by omega
  generalize hidx_eq : (if fromEnd = true then count - offset else offset) = idx'
  by_cases hidx_lt : idx' < count
  · simp only [projIdx, hnot_min, ↓reduceIte, hidx_eq, hidx_lt, Option.some.injEq] at hidx
    subst hidx
    have hnot_le : ¬ (count ≤ idx') := Nat.not_le.mpr hidx_lt
    have hoff_le : idx' * elemIt.size.bytes ≤ (declSlotData d slot body.layouts).length := by
      rw [hdlen]
      exact Nat.mul_le_mul_right _ (by omega)
    have hoff_bound : idx' * elemIt.size.bytes < 2 ^ 63 := by
      have : idx' * elemIt.size.bytes ≤ count * elemIt.size.bytes :=
        Nat.mul_le_mul_right _ (by omega)
      omega
    obtain ⟨k, hpk, _, haddr, haddrMax, _, hA⟩ :=
      h.locs.storage_nonptr j d slot p hd hs hp (isPtrTy_false_of_arrayTypeOf ha)
    rw [hitd] at hA
    rw [hTd] at haddrMax
    simp only [tyBytes, Int.ofNat_eq_natCast, Int.toNat_natCast] at haddrMax
    have hptr := ptrOffsetInbounds_ptr_elem h.shape p k hpk idx' elemIt
      (declSlotData d slot body.layouts) hA hoff_le hoff_bound haddr.nonneg
      (by rw [hdlen]; exact haddrMax)
    have hsz : idx' * elemIt.size.bytes ≤ count * elemIt.size.bytes :=
      Nat.mul_le_mul_right _ (by omega)
    rw [evalPlace]
    simp [hplaceBase, evalValue, evalConstant, hnot_le, layout_eq _ hgood,
      layout_array_eq _ _ hgood, computeSize, LayoutStrategy.compute_size_and_align,
      hsz, hptr, ThinPointer.widen]
  · simp [projIdx, hnot_min, hidx_eq, hidx_lt] at hidx

theorem placeOk_single_nonfield {layouts : Layout.LayoutTable} {decls : List LocalDecl}
    {it : Gen.IntType} {j : Nat} {proj : ProjectionElem}
    (hnf : ∀ idx fieldTy, proj ≠ .field idx fieldTy) :
    placeOk layouts decls it ⟨j, [proj]⟩ =
      (decide (j < decls.length) &&
        match decls[j]? >>= (arrayTypeOf ·.ty) with
        | some (elemIt, count) => decide (elemIt = it) && projOk decls count proj
        | none => false) := by
  cases proj with
  | field idx fieldTy => exact False.elim (hnf idx fieldTy rfl)
  | _ => rfl

theorem evalValue_operand_array_proj {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {locals : List LocalSlot} {lm : Map Gen.LocalName Ptr} {m : Mach} {blk stmt : Nat}
    (h : FrameOk body f ctx locals lm m blk stmt)
    (it : Gen.IntType) (j : Nat) (proj : ProjectionElem)
    (hnf : ∀ idx fieldTy, proj ≠ .field idx fieldTy)
    (hok : operandOk body.layouts body.localDecls it (.copy ⟨j, [proj]⟩) = true)
    (e : Gen.ValueExpr) (he : translateOperand body.localDecls (.copy ⟨j, [proj]⟩) = some e) :
    (∀ bits, opBits locals (.copy ⟨j, [proj]⟩) = some bits →
      bits < 2 ^ (8 * it.size.bytes) ∧
      ∃ m', evalValue m e = .ok ((.Int (intFromBits bits it), .Int it), m') ∧
        FrameOk body f ctx locals lm m' blk stmt) ∧
    (opBits locals (.copy ⟨j, [proj]⟩) = none → ∃ msg, evalValue m e = .error (.ub msg)) := by
  simp only [operandOk, placeOk_single_nonfield hnf, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨hj, hok⟩, _⟩ := hok
  cases hd : body.localDecls[j]? with
  | none => simp [hd] at hok
  | some d =>
    simp only [hd, Option.bind_eq_bind, Option.bind_some] at hok
    cases ha : arrayTypeOf d.ty with
    | none => simp [ha] at hok
    | some pair =>
      obtain ⟨elemIt, count⟩ := pair
      simp only [ha, Bool.and_eq_true, decide_eq_true_eq] at hok
      obtain ⟨helemEq, hproj⟩ := hok
      subst helemEq
      simp only [translateOperand] at he
      cases hpe : translatePlace body.localDecls ⟨j, [proj]⟩ with
      | none => simp [hpe] at he
      | some pe =>
        simp only [hpe, Option.map_some, Option.some.injEq] at he
        subst he
        obtain ⟨_, slot, hd', hs⟩ := h.slot_exists j hj
        rw [hd] at hd'; cases hd'
        obtain ⟨⟨v, rfl⟩, _⟩ := h.nonScalar j d slot hd hs
          (scalarTypeOf_none_of_arrayTypeOf ha) (isPtrTy_false_of_arrayTypeOf ha)
        have hslot := (DeclSlotOk_of_arrayTypeOf ha (.init v)).mp (h.slots j d (.init v) hd hs)
        have hitd : itOf d body.layouts = elemIt := itOf_eq_of_arrayTypeOf ha
        have hgood := arrayTypeOf_good ha
        match v, hslot with
        | .aggregate 0 elems, ⟨hlen, he⟩ =>
          obtain ⟨p, hp⟩ := h.locs.some_of_live hs (by simp)
          obtain ⟨hpok, hpnone⟩ := evalPlace_proj h j d hd elemIt count ha p hp proj hproj pe hpe
          cases hidx : projIdx locals count proj with
          | none =>
            refine ⟨fun bits hbits => by simp [opBits, hs, hlen, hidx] at hbits, fun _ => ?_⟩
            obtain ⟨msg, hmsg⟩ := hpnone hidx
            exact ⟨msg, by simp [evalValue, hmsg]⟩
          | some idx =>
            obtain ⟨hidx_lt, m1, hm1, h1⟩ := hpok idx hidx
            obtain ⟨k, hpk, _, _, _, _, hA1⟩ :=
              h1.locs.storage_nonptr j d (.init (.aggregate 0 elems)) p hd hs hp
                (isPtrTy_false_of_arrayTypeOf ha)
            rw [hitd, declSlotData_of_array ha] at hA1
            have hget : ∃ sc, elems[idx]? = some (.scalar sc) := by
              have hex : ∃ v, elems[idx]? = some v :=
                ⟨elems[idx]'(by omega), List.getElem?_eq_getElem (by omega)⟩
              obtain ⟨v, hv⟩ := hex
              have hvok := he v (List.mem_of_getElem? hv)
              cases v with
              | scalar sc => exact ⟨sc, hv⟩
              | _ => exact False.elim hvok
            obtain ⟨sc, hsc⟩ := hget
            obtain ⟨_, hb⟩ := he (.scalar sc) (List.mem_of_getElem? hsc)
            obtain ⟨m2, hm2, hshape2⟩ := typedLoad_ptr_array_elem h1.shape p k hpk idx elemIt count
              elems sc hgood hlen he hsc hA1
            refine ⟨fun bits hbits => ?_, fun hnone => ?_⟩
            · simp [opBits, hs, hlen, hidx, hsc] at hbits
              subst hbits
              exact ⟨hb, m2, by simp [evalValue, hm1, placeLoad, hm2],
                FrameOk.mk' h1.hf hshape2 h1.locs h1.declsOk h1.nonScalar⟩
            · simp [opBits, hs, hlen, hidx, hsc] at hnone

/-- Evaluating a translated fragment operand of integer type `it`. -/
theorem evalValue_operand {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {locals : List LocalSlot} {lm : Map Gen.LocalName Ptr} {m : Mach} {blk stmt : Nat}
    (h : FrameOk body f ctx locals lm m blk stmt)
    (it : Gen.IntType) (op : Operand) (hok : operandOk body.layouts body.localDecls it op = true)
    (e : Gen.ValueExpr) (he : translateOperand body.localDecls op = some e) :
    (∀ bits, opBits locals op = some bits →
      bits < 2 ^ (8 * it.size.bytes) ∧
      ∃ m', evalValue m e = .ok ((.Int (intFromBits bits it), .Int it), m') ∧
        FrameOk body f ctx locals lm m' blk stmt) ∧
    (opBits locals op = none → ∃ msg, evalValue m e = .error (.ub msg)) := by
  have hgood := operandOk_good hok
  match op, hok, he with
  | .copy ⟨j, []⟩, hok, he =>
    have hit := operandIntType_of_operandOk hok
    simp only [operandOk, placeOk, Bool.and_eq_true, decide_eq_true_eq] at hok
    exact evalValue_operandT h (.int it hgood) (.copy ⟨j, []⟩)
      ⟨hok.1.1, operandType_of_operandIntType hit⟩ e he
  | .constant c, hok, he =>
    have hit := operandIntType_of_operandOk hok
    simp only [operandOk, Bool.and_eq_true] at hok
    exact evalValue_operandT h (.int it hgood) (.constant c)
      ⟨operandType_of_operandIntType hit, hok.2⟩ e he
  | .copy ⟨j, [.index idxLocal]⟩, hok, he =>
    exact evalValue_operand_array_proj h it j (.index idxLocal)
      (by intro _ _ hc; cases hc) hok e he
  | .copy ⟨j, [.constantIndex offset minLen fromEnd]⟩, hok, he =>
    exact evalValue_operand_array_proj h it j (.constantIndex offset minLen fromEnd)
      (by intro _ _ hc; cases hc) hok e he
  | .copy ⟨j, [.deref]⟩, hok, _ =>
    simp only [operandOk, placeOk, projOk, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨_, hok⟩, _⟩ := hok
    split at hok <;> simp at hok
  | .copy ⟨j, .deref :: _ :: _⟩, hok, _ =>
    simp [operandOk, placeOk] at hok
  | .copy ⟨j, .field idx fieldTy :: rest⟩, hok, he =>
    have hit := operandIntType_of_operandOk hok
    simp only [operandOk, placeOk, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨hj, hokP⟩, _⟩ := hok
    cases hd : body.localDecls[j]? with
    | none => simp [hd] at hokP
    | some d =>
      simp only [hd] at hokP
      cases hij : intBoolTupleOf d.ty with
      | some tupIt =>
        simp only [hij] at hokP
        cases idx with
        | zero =>
          cases rest with
          | nil =>
            exact evalValue_operandT h (.int it hgood) (.copy ⟨j, [.field 0 fieldTy]⟩)
              ⟨hj, ⟨d, hd, by simp [hij]⟩, operandType_of_operandIntType hit⟩ e he
          | cons _ _ => simp at hokP
        | succ _ => simp at hokP
      | none =>
        simp only [hij] at hokP
        cases ht : tupleTypeOf body.layouts d.ty with
        | none => simp [ht] at hokP
        | some pair =>
          obtain ⟨fields, size, align⟩ := pair
          simp only [ht] at hokP
          cases hres : resolveFieldPath body.layouts (.tuple fields size align)
              (.field idx fieldTy :: rest) with
          | none => simp [hres] at hokP
          | some rpair =>
            obtain ⟨relOff, leafSpec⟩ := rpair
            simp only [hres] at hokP
            cases leafSpec with
            | tuple _ _ _ => simp at hokP
            | scalar leafIt =>
              simp only [decide_eq_true_eq] at hokP
              subst hokP
              simp only [translateOperand, translatePlace] at he
              cases hpe : translateFieldPlace (.Local (localName j))
                  (.field idx fieldTy :: rest) with
              | none => simp [hpe] at he
              | some pe =>
                simp only [hpe, Option.map_some, Option.some.injEq] at he
                subst he
                obtain ⟨_, slot, hd', hs⟩ := h.slot_exists j hj
                rw [hd] at hd'; cases hd'
                obtain ⟨⟨rootVal, rfl⟩, _⟩ :=
                  h.nonScalar j d slot hd hs (scalarTypeOf_none_of_tupleTypeOf ht)
                    (isPtrTy_false_of_tupleTypeOf ht)
                obtain ⟨hrootWf, hrootVal⟩ :=
                  (DeclSlotOk_of_tupleTypeOf ht (.init rootVal)).mp
                    (h.slots j d (.init rootVal) hd hs)
                obtain ⟨p, hp⟩ := h.locs.some_of_live hs (by simp)
                obtain ⟨k, hpk, _, haddr, haddrMax, _, hA⟩ :=
                  h.locs.storage_nonptr j d (.init rootVal) p hd hs hp
                    (isPtrTy_false_of_tupleTypeOf ht)
                obtain ⟨hTd, _⟩ := tyOf_tupleSpec ht
                rw [declSlotData_of_tupleSpec ht] at hA
                obtain ⟨hleafWf, hrelBound⟩ := resolveFieldPath_wf hrootWf hres
                obtain ⟨leafVal, hread, hleafValOk, hslice, _⟩ :=
                  resolveFieldPath_read hrootWf hrootVal hres
                cases leafVal with
                | scalar sc =>
                  have hleafValOk' := hleafValOk
                  simp only [TupleSpec.valOk, Bool.and_eq_true, decide_eq_true_eq] at hleafValOk'
                  obtain ⟨_, hscBits⟩ := hleafValOk'
                  have hloc := (h.hf.2 j d hd).2
                  rw [hTd] at hloc
                  have hplaceBase := evalPlace_local_some h.shape j _ hloc p hp
                  have hdlen : ((TupleSpec.tuple fields size align).encodeVal rootVal).length = size :=
                    TupleSpec.encodeVal_length (.tuple fields size align) rootVal hrootWf
                  have hbound : size < 2 ^ 63 := by
                    simp only [TupleSpec.wf, Bool.and_eq_true, decide_eq_true_eq] at hrootWf
                    exact hrootWf.1.2
                  rw [hTd] at haddrMax
                  simp only [TupleSpec.toMiniRustTy, tyBytes] at haddrMax
                  have hrootEval : evalPlace m (.Local (localName j)) =
                      .ok (({ ptr := { thin_pointer := offsetPtr p 0, metadata := none },
                               aligned := true },
                             (TupleSpec.tuple fields size align).toMiniRustTy), m) := by
                    simpa using hplaceBase
                  have hpeEval := evalPlace_ptr_fieldPath h.shape p k hpk
                    (itOf d body.layouts) ((TupleSpec.tuple fields size align).encodeVal rootVal) hA
                    (by rw [hdlen]; exact hbound) haddr.nonneg (by rw [hdlen]; exact haddrMax)
                    (.Local (localName j)) 0 (.tuple fields size align) hrootEval hrootWf
                    (by simp [TupleSpec.size, hdlen]) (.field idx fieldTy :: rest) pe hpe
                    relOff (.scalar leafIt) hres
                  simp only [Nat.zero_add] at hpeEval
                  obtain ⟨m', hm', hshape'⟩ := typedLoad_ptr_tuple_slice h.shape p k hpk
                    (itOf d body.layouts) ((TupleSpec.tuple fields size align).encodeVal rootVal) hA
                    relOff (.scalar leafIt) (.scalar sc) hleafWf hleafValOk
                    (by rw [hdlen]; exact hrelBound) hslice
                  refine ⟨fun bits hbits => ?_, fun hnone => ?_⟩
                  · simp [opBits, hs, hread] at hbits
                    subst hbits
                    refine ⟨hscBits, m', ?_, FrameOk.mk' h.hf hshape' h.locs h.declsOk h.nonScalar⟩
                    simp only [TupleSpec.toMiniRustTy, TupleSpec.toMiniRustVal] at hpeEval hm' ⊢
                    simp [evalValue, hpeEval, placeLoad, hm']
                  · simp [opBits, hs, hread] at hnone
                | _ => simp [TupleSpec.valOk] at hleafValOk

/-- The bit pattern an Anneal fragment rvalue of type `it` evaluates to, or
`none` when evaluating it is UB. -/
def rvBits (decls : List LocalDecl) (locals : List LocalSlot) (it : Gen.IntType)
    (layouts : Layout.LayoutTable := ⟨64, true, []⟩) : Rvalue → Option Nat
  | .use op => opBits locals op
  | .len ⟨j, []⟩ =>
    match decls[j]? with
    | some d =>
      match arrayTypeOf d.ty with
      | some (_, count) => some count
      | none => none
    | none => none
  | .unaryOp uop op => do
    let iuop ← translateUnOp uop
    let x ← opBits locals op
    pure (intUnArith iuop x % 2 ^ (8 * it.size.bytes)).toNat
  | .binaryOp op a b => do
    let iop ← translateBinOp op
    let rhsIt ← operandIntType layouts decls b
    let x ← opBits locals a
    let y ← opBits locals b
    let z ← intBinEval iop (intFromBits x it) (intFromBits y rhsIt) it
    pure (z % 2 ^ (8 * it.size.bytes)).toNat
  | .cast .intToInt op _ => do
    let srcIt := (operandIntType layouts decls op).getD u8Ty
    let x ← opBits locals op
    pure (intFromBits x srcIt % 2 ^ (8 * it.size.bytes)).toNat
  | .discriminant p => opBits locals (.copy p)
  | _ => none

theorem bringInBounds_eq_intFromBits (it : Gen.IntType) (hgood : GoodSize it.size.bytes) (z : Int) :
    IntType.bring_in_bounds it z = intFromBits (z % 2 ^ (8 * it.size.bytes)).toNat it := by
  have hn : 0 < 8 * it.size.bytes := by have := hgood.pos; omega
  have hn' : 0 < Size.bits it.size := by simpa [Size.bits] using hn
  obtain ⟨hl, hr⟩ := bringInBounds_window z it.signed it.size hn'
  have heq := eq_intFromBits _ it hn (by simpa [Size.bits] using hl) (by simpa [Size.bits] using hr)
  unfold IntType.bring_in_bounds
  rw [heq]
  congr 2
  simpa [Size.bits] using bringInBounds_emod z it.signed it.size

theorem bringInBounds_intUnArith (uop : MirAst.UnOp) (iuop : Gen.IntUnOp)
    (huop : translateUnOp uop = some iuop) (it : Gen.IntType) (hgood : GoodSize it.size.bytes)
    (x : Nat) (hx : x < 2 ^ (8 * it.size.bytes)) :
    IntType.bring_in_bounds it (intUnArith iuop (intFromBits x it)) =
      intFromBits (intUnArith iuop x % 2 ^ (8 * it.size.bytes)).toNat it := by
  rw [bringInBounds_eq_intFromBits it hgood]
  congr 2
  have hpos := two_pow_pos (8 * it.size.bytes)
  have hx' : intFromBits x it % 2 ^ (8 * it.size.bytes) = (x : Int) % 2 ^ (8 * it.size.bytes) := by
    rw [intFromBits_emod x it hx, Int.emod_eq_of_lt (by omega) (by exact_mod_cast hx)]
  exact intUnArith_emod uop iuop huop _ _ _ hx'

theorem translateRelOp_of_translateBinOp {op : MirAst.BinOp} {iop : Gen.IntBinOp}
    (h : translateBinOp op = some iop) : translateRelOp op = none := by
  cases op <;> simp_all [translateBinOp, translateRelOp]

theorem translateRvalue_unary_int {layouts : Layout.LayoutTable} {decls : List LocalDecl}
    {targetTy : Option MirAst.Ty} {it : Gen.IntType} {uop : MirAst.UnOp}
    {op : Operand} {e : Gen.ValueExpr} (hok : operandOk layouts decls it op = true)
    (he : translateRvalue layouts decls targetTy (.unaryOp uop op) = some e) :
    ∃ iuop eo, translateUnOp uop = some iuop ∧ translateOperand decls op = some eo ∧
      e = .UnOp (.Int iuop) eo := by
  have hty := operandType_of_operandIntType (operandIntType_of_operandOk hok)
  simp only [translateRvalue, Option.bind_eq_bind] at he
  cases heo : translateOperand decls op with
  | none => simp [heo] at he
  | some eo =>
    simp only [heo, Option.bind_some, hty] at he
    cases hu : translateUnOp uop with
    | none => simp [hu] at he
    | some iuop => simp [hu] at he; exact ⟨iuop, eo, rfl, rfl, he.symm⟩

theorem translateRvalue_binary_int {layouts : Layout.LayoutTable} {decls : List LocalDecl}
    {targetTy : Option MirAst.Ty} {it : Gen.IntType} {op : MirAst.BinOp}
    {a b : Operand} {e : Gen.ValueExpr} {iop : Gen.IntBinOp} (hiop : translateBinOp op = some iop)
    (hok : operandOk layouts decls it a = true)
    (he : translateRvalue layouts decls targetTy (.binaryOp op a b) = some e) :
    ∃ ea eb, translateOperand decls a = some ea ∧ translateOperand decls b = some eb ∧
      e = .BinOp (.Int iop) ea eb := by
  have hty := operandType_of_operandIntType (operandIntType_of_operandOk hok)
  simp only [translateRvalue, Option.bind_eq_bind, translateRelOp_of_translateBinOp hiop] at he
  cases hea : translateOperand decls a with
  | none => simp [hea] at he
  | some ea =>
    cases heb : translateOperand decls b with
    | none => simp [hea, heb] at he
    | some eb =>
      simp only [hea, heb, Option.bind_some, hty, hiop] at he
      simp at he
      exact ⟨ea, eb, rfl, rfl, he.symm⟩

/-- `build::bool_to_int::<u8>` (a transmute to `u8`) maps `false`/`true` to
`0`/`1`. -/
theorem evalValue_boolToU8 (m m1 : Mach) (e : Gen.ValueExpr) (b : Bool)
    (he : evalValue m e = .ok ((.Bool b, .Bool), m1)) :
    evalValue m (boolToU8 e) = .ok ((.Int (if b then 1 else 0), .Int u8Ty), m1) := by
  cases b <;> simp [boolToU8, evalValue, he, evalUnOp] <;> rfl

theorem translateRvalue_cast_int {layouts : Layout.LayoutTable} {decls : List LocalDecl}
    {targetTy' : Option MirAst.Ty} {srcIt it : Gen.IntType} {op : Operand}
    {targetTy : MirAst.Ty} {e : Gen.ValueExpr} (htgt : intTypeOf targetTy = some it)
    (hok : operandOk layouts decls srcIt op = true)
    (he : translateRvalue layouts decls targetTy' (.cast .intToInt op targetTy) = some e) :
    ∃ eo, translateOperand decls op = some eo ∧ e = .UnOp (.Cast (.IntToInt it)) eo := by
  have hty := operandType_of_operandIntType (operandIntType_of_operandOk hok)
  simp only [translateRvalue, Option.bind_eq_bind, htgt, Option.bind_some] at he
  cases heo : translateOperand decls op with
  | none => simp [heo] at he
  | some eo =>
    simp only [heo, Option.bind_some, hty] at he
    simp at he
    exact ⟨eo, rfl, he.symm⟩

theorem translateRvalue_cast_bool {layouts : Layout.LayoutTable} {decls : List LocalDecl}
    {targetTy' : Option MirAst.Ty} {it : Gen.IntType} {op : Operand}
    {targetTy : MirAst.Ty} {e : Gen.ValueExpr} (htgt : intTypeOf targetTy = some it)
    (hok : operandOkB layouts decls op = true)
    (he : translateRvalue layouts decls targetTy' (.cast .intToInt op targetTy) = some e) :
    ∃ eo, translateOperand decls op = some eo ∧ e = .UnOp (.Cast (.IntToInt it)) (boolToU8 eo) := by
  have hty := operandType_of_operandOkB hok
  simp only [translateRvalue, Option.bind_eq_bind, htgt, Option.bind_some] at he
  cases heo : translateOperand decls op with
  | none => simp [heo] at he
  | some eo =>
    simp [heo, hty] at he
    exact ⟨eo, rfl, he.symm⟩

/-! ### `Rvalue::Discriminant` of an `Ordering` local -/

set_option maxRecDepth 8192 in
/-- `transmute::<i8>` of the `Ordering` variant with a valid tag is that tag
read as an `i8` (computed by the kernel for each of the three tags). -/
theorem evalUnOp_transmute_ordering_i8 {bits : Nat} (hb : ValidBits orderingTy bits)
    (m? : Option Mach) :
    evalUnOp (.Cast (.Transmute (.Int IntType.I8))) (valOf orderingTy bits, orderingTy) m? =
      .ok (.Int (intFromBits bits IntType.I8), .Int IntType.I8) := by
  rcases (validBits_ordering bits).mp hb with rfl | rfl | rfl <;> rfl

/-- `orderingDiscrExpr e0`, where `e0` evaluates to the `Ordering` variant with
a valid tag, evaluates to that tag read as an `i8`. -/
theorem evalValue_orderingDiscrExpr {m m' : Mach} {e0 : Gen.ValueExpr} {bits : Nat}
    (hb : ValidBits orderingTy bits)
    (h0 : evalValue m e0 = .ok ((valOf orderingTy bits, orderingTy), m')) :
    evalValue m (orderingDiscrExpr e0) =
      .ok ((.Int (intFromBits bits IntType.I8), .Int IntType.I8), m') := by
  simp only [orderingDiscrExpr, evalValue, h0, ok_bind, evalUnOp_transmute_ordering_i8 hb]
  rfl

/-- `orderingDiscrExpr e0` is UB when evaluating `e0` is. -/
theorem evalValue_orderingDiscrExpr_ub {m : Mach} {e0 : Gen.ValueExpr} {msg : String}
    (h0 : evalValue m e0 = .error (.ub msg)) :
    evalValue m (orderingDiscrExpr e0) = .error (.ub msg) := by
  simp [orderingDiscrExpr, evalValue, h0]

theorem translateRvalue_discriminant {layouts : Layout.LayoutTable} {decls : List LocalDecl}
    {targetTy : Option MirAst.Ty} {j : Nat} {d : LocalDecl} {e : Gen.ValueExpr}
    (hd : decls[j]? = some d) (hord : isOrderingTy d.ty = true)
    (he : translateRvalue layouts decls targetTy (.discriminant ⟨j, []⟩) = some e) :
    e = orderingDiscrExpr (.Load (.Local (localName j))) := by
  simp [translateRvalue, hd, hord] at he
  subst he
  rfl

/-- MiniRust's `ValueExpr::GetDiscriminant` (`spec/lang/step/expressions.md`) on
an `orderingTy` place whose one byte is `b`: the accessor loads the tag bytes
the discriminator asks for and `decode_discriminant` decodes them; `none` is
`GetDiscriminant`'s UB ("ValueExpr::GetDiscriminant encountered invalid
discriminant."). -/
def orderingGetDiscriminant (b : Byte) : Interp (Option Int) :=
  match orderingTy with
  | .Enum _ _ discriminator _ _ => do
    let accessor := fun (_ : Unit) (offset : Gen.Offset) (size : Size) => do
      let bs ← subsliceWithLength [b] offset.bytes size.bytes
      pure (bs, ())
    pure (← decodeDiscriminant accessor discriminator ()).1
  | _ => pure none

/-- The lowering `orderingDiscrExpr (Load place)` on an `orderingTy` place whose
one byte is `b`: the `Load` decodes the byte at `orderingTy` (`none` is the
load's UB, "load at type .. but the data in memory violates the validity
invariant"), and `transmute::<i8>` re-encodes the variant and decodes it at
`i8`. -/
def orderingLoweredDiscriminant (b : Byte) : Interp (Option Int) := do
  match ← Type.decode orderingTy [b] with
  | some v =>
    match ← transmute v orderingTy (.Int IntType.I8) with
    | .Int i => pure (some i)
    | _ => pure none
  | none => pure none

/-- Whether two discriminant computations both succeed with the same result. -/
def sameDiscriminant : Interp (Option Int) → Interp (Option Int) → Bool
  | .ok a, .ok b => a == b
  | _, _ => false

/-- The lowering `orderingDiscrExpr` of `Rvalue::Discriminant` agrees with
MiniRust's `GetDiscriminant` on every byte an `Ordering` local can hold in the
fragment: the uninitialized byte and each of the 256 initialized bytes without
provenance (both are UB, `none`, exactly off the tags `255`, `0`, `1`, and
otherwise return the tag read as an `i8`). -/
theorem orderingDiscrExpr_eq_getDiscriminant :
    sameDiscriminant (orderingGetDiscriminant .Uninit) (orderingLoweredDiscriminant .Uninit) = true ∧
    (List.range 256).all (fun n =>
      sameDiscriminant (orderingGetDiscriminant (.Init (UInt8.ofNat n) none))
        (orderingLoweredDiscriminant (.Init (UInt8.ofNat n) none))) = true ∧
    orderingGetDiscriminant (.Init 255 none) = .ok (some (-1)) ∧
    orderingGetDiscriminant (.Init 0 none) = .ok (some 0) ∧
    orderingGetDiscriminant (.Init 1 none) = .ok (some 1) ∧
    orderingGetDiscriminant (.Init 2 none) = .ok none ∧
    orderingGetDiscriminant .Uninit = .ok none := by
  refine ⟨rfl, ?_, rfl, rfl, rfl, rfl, rfl⟩
  decide +kernel

/-- Evaluating a translated fragment rvalue. -/
theorem evalValue_rvalue {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {locals : List LocalSlot} {lm : Map Gen.LocalName Ptr} {m : Mach} {blk stmt : Nat}
    {targetTy : Option MirAst.Ty}
    (h : FrameOk body f ctx locals lm m blk stmt)
    (it : Gen.IntType) (hgood : GoodSize it.size.bytes) (rv : Rvalue)
    (hok : rvalueOk body.layouts body.localDecls it rv = true) (e : Gen.ValueExpr)
    (he : translateRvalue body.layouts body.localDecls targetTy rv = some e) :
    (∀ r, rvBits body.localDecls locals it body.layouts rv = some r →
      r < 2 ^ (8 * it.size.bytes) ∧
      ∃ m', evalValue m e = .ok ((.Int (intFromBits r it), .Int it), m') ∧
        FrameOk body f ctx locals lm m' blk stmt) ∧
    (rvBits body.localDecls locals it body.layouts rv = none →
      ∃ msg, evalValue m e = .error (.ub msg)) := by
  match rv, hok, he with
  | .use op, hok, he =>
    simp only [rvalueOk] at hok
    simp only [translateRvalue] at he
    exact evalValue_operand h it op hok e he
  | .len ⟨j, []⟩, hok, he =>
    simp only [rvalueOk, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨rfl, _⟩, hok⟩ := hok
    cases hd : body.localDecls[j]? with
    | none => simp [translateRvalue, hd] at he
    | some d =>
      cases ha : arrayTypeOf d.ty with
      | none => simp [translateRvalue, hd, ha] at he
      | some p =>
        obtain ⟨elemIt, count⟩ := p
        simp [translateRvalue, hd, ha] at he
        subst he
        have hdok := h.array_bound j d elemIt count hd ha
        have hpos := (arrayTypeOf_good ha).pos
        have hle : count ≤ count * elemIt.size.bytes := Nat.le_mul_of_pos_right _ hpos
        have hlt : count < 2 ^ (8 * usizeIt.size.bytes) := by
          simp only [usizeIt]; omega
        refine ⟨fun r hr => ?_, fun hnone => by simp [rvBits, hd, ha] at hnone⟩
        simp [rvBits, hd, ha] at hr
        subst hr
        refine ⟨hlt, m, ?_, h⟩
        simp [evalValue, evalConstant, intFromBits, usizeIt]
  | .discriminant ⟨j, []⟩, hok, he =>
    simp only [rvalueOk, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨rfl, hj⟩, hjd⟩ := hok
    cases hd : body.localDecls[j]? with
    | none => simp [hd] at hjd
    | some d =>
      simp only [hd, Bool.and_eq_true] at hjd
      obtain ⟨hord, _⟩ := hjd
      obtain rfl := translateRvalue_discriminant hd hord he
      have hokT : OperandOkT body.layouts body.localDecls orderingTy (.copy ⟨j, []⟩) :=
        operandOkO_T (by
          simp only [operandOkO, operandIsOrdering, hd, hord, Bool.and_true, decide_eq_true_eq]
          exact hj)
      obtain ⟨hsome, hnone⟩ := evalValue_operandT h .ordering (.copy ⟨j, []⟩) hokT
        (.Load (.Local (localName j))) rfl
      refine ⟨fun r hr => ?_, fun hr => ?_⟩
      · obtain ⟨hvalid, m', hm', h'⟩ := hsome r hr
        refine ⟨?_, m', evalValue_orderingDiscrExpr hvalid hm', h'⟩
        rcases (validBits_ordering r).mp hvalid with rfl | rfl | rfl <;> decide
      · obtain ⟨msg, hmsg⟩ := hnone hr
        exact ⟨msg, evalValue_orderingDiscrExpr_ub hmsg⟩
  | .unaryOp uop op, hok, he =>
    simp only [rvalueOk, Bool.and_eq_true] at hok
    obtain ⟨huop, hok⟩ := hok
    obtain ⟨iuop, eo, hiuop, heo, rfl⟩ := translateRvalue_unary_int hok he
    obtain ⟨haok, hanone⟩ := evalValue_operand h it op hok eo heo
    cases hxo : opBits locals op with
    | none =>
      refine ⟨fun r hr => by simp [rvBits, hiuop, hxo] at hr, fun _ => ?_⟩
      obtain ⟨msg, hmsg⟩ := hanone hxo
      exact ⟨msg, by simp [evalValue, hmsg]⟩
    | some x =>
      obtain ⟨hx, m1, hm1, h1⟩ := haok x hxo
      refine ⟨fun r hr => ?_, fun hnone => by simp [rvBits, hiuop, hxo] at hnone⟩
      simp [rvBits, hiuop, hxo] at hr
      subst hr
      have hpos := two_pow_pos (8 * it.size.bytes)
      have hlt : (intUnArith iuop x % 2 ^ (8 * it.size.bytes)).toNat < 2 ^ (8 * it.size.bytes) := by
        have h0 := Int.emod_nonneg (intUnArith iuop x) (Int.ne_of_gt hpos)
        have hlt' := Int.emod_lt_of_pos (intUnArith iuop x) hpos
        have : (((intUnArith iuop x % 2 ^ (8 * it.size.bytes)).toNat : Int)) < 2 ^ (8 * it.size.bytes) := by
          rw [Int.toNat_of_nonneg h0]; exact hlt'
        exact_mod_cast this
      have hrep := canRepresent_intFromBits it _ hgood hlt
      refine ⟨hlt, m1, ?_, h1⟩
      have hbring := bringInBounds_intUnArith uop iuop hiuop it hgood x hx
      have heval := evalIntUnOp_eq uop iuop hiuop (intFromBits x it) it
      cases uop <;> simp [translateUnOp] at hiuop <;> subst hiuop <;>
        simp [evalValue, hm1, evalUnOp, heval, hbring, checkValue_int hrep]
  | .binaryOp op a b, hok, he =>
    obtain ⟨iop, rhsIt, hiop, hoka, hrhsTy, hokb, _⟩ := rvalueOk_binaryOp hok
    obtain ⟨ea, eb, hea, heb, rfl⟩ := translateRvalue_binary_int hiop hoka he
    obtain ⟨haok, hanone⟩ := evalValue_operand h it a hoka ea hea
    cases hxa : opBits locals a with
    | none =>
      refine ⟨fun r hr => by simp [rvBits, hiop, hrhsTy, hxa] at hr, fun _ => ?_⟩
      obtain ⟨msg, hmsg⟩ := hanone hxa
      exact ⟨msg, by simp [evalValue, hmsg]⟩
    | some x =>
      obtain ⟨hx, m1, hm1, h1⟩ := haok x hxa
      obtain ⟨hbok, hbnone⟩ := evalValue_operand h1 rhsIt b hokb eb heb
      cases hyb : opBits locals b with
      | none =>
        refine ⟨fun r hr => by simp [rvBits, hiop, hrhsTy, hxa, hyb] at hr, fun _ => ?_⟩
        obtain ⟨msg, hmsg⟩ := hbnone hyb
        exact ⟨msg, by simp [evalValue, hm1, hmsg]⟩
      | some y =>
        obtain ⟨_, m2, hm2, h2⟩ := hbok y hyb
        obtain ⟨hevalOk, hevalNone⟩ :=
          evalIntBinOp_spec op iop hiop (intFromBits x it) (intFromBits y rhsIt) it
        cases hz : intBinEval iop (intFromBits x it) (intFromBits y rhsIt) it with
        | none =>
          refine ⟨fun r hr => by simp [rvBits, hiop, hrhsTy, hxa, hyb, hz] at hr, fun _ => ?_⟩
          obtain ⟨msg, hmsg⟩ := hevalNone hz
          exact ⟨msg, by simp [evalValue, hm1, hm2, evalBinOp, hmsg]⟩
        | some z =>
          refine ⟨fun r hr => ?_, fun hnone => by simp [rvBits, hiop, hrhsTy, hxa, hyb, hz] at hnone⟩
          simp [rvBits, hiop, hrhsTy, hxa, hyb, hz] at hr
          subst hr
          have hpos := two_pow_pos (8 * it.size.bytes)
          refine ⟨?_, m2, ?_, h2⟩
          · have h0 := Int.emod_nonneg z (Int.ne_of_gt hpos)
            have hlt := Int.emod_lt_of_pos z hpos
            have : ((z % 2 ^ (8 * it.size.bytes)).toNat : Int) < 2 ^ (8 * it.size.bytes) := by
              rw [Int.toNat_of_nonneg h0]; exact hlt
            exact_mod_cast this
          · simp [evalValue, hm1, hm2, evalBinOp, hevalOk z hz,
              bringInBounds_eq_intFromBits it hgood z]
  | .cast .intToInt op castTy, hok, he =>
    simp only [rvalueOk, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨htgt, hsrc⟩ := hok
    cases hsrcIt : operandIntType body.layouts body.localDecls op with
    | none =>
      simp only [hsrcIt] at hsrc
      obtain ⟨eo, heo, rfl⟩ := translateRvalue_cast_bool htgt hsrc he
      obtain ⟨haok, hanone⟩ := evalValue_operandT h .bool op (operandOkB_T hsrc) eo heo
      cases hxo : opBits locals op with
      | none =>
        refine ⟨fun r hr => by simp [rvBits, hsrcIt, hxo] at hr, fun _ => ?_⟩
        obtain ⟨msg, hmsg⟩ := hanone hxo
        exact ⟨msg, by simp [boolToU8, evalValue, hmsg]⟩
      | some x =>
        obtain ⟨hvx, m1, hm1, h1⟩ := haok x hxo
        have hx2 : x < 2 := by simpa [ValidBits] using hvx
        refine ⟨fun r hr => ?_, fun hnone => by simp [rvBits, hsrcIt, hxo] at hnone⟩
        simp [rvBits, hsrcIt, hxo] at hr
        subst hr
        have hpos := two_pow_pos (8 * it.size.bytes)
        have hlt : (intFromBits x u8Ty % 2 ^ (8 * it.size.bytes)).toNat < 2 ^ (8 * it.size.bytes) := by
          have h0 := Int.emod_nonneg (intFromBits x u8Ty) (Int.ne_of_gt hpos)
          have hlt' := Int.emod_lt_of_pos (intFromBits x u8Ty) hpos
          have : (((intFromBits x u8Ty % 2 ^ (8 * it.size.bytes)).toNat : Int)) < 2 ^ (8 * it.size.bytes) := by
            rw [Int.toNat_of_nonneg h0]; exact hlt'
          exact_mod_cast this
        refine ⟨hlt, m1, ?_, h1⟩
        have h8 := evalValue_boolToU8 m m1 eo (decide (x = 1)) (by simpa [valOf] using hm1)
        have hxInt : (if decide (x = 1) then (1 : Int) else 0) = intFromBits x u8Ty := by
          rcases (by omega : x = 0 ∨ x = 1) with rfl | rfl <;> rfl
        rw [hxInt] at h8
        simp [evalValue, h8, evalUnOp, evalCastOp, bringInBounds_eq_intFromBits it hgood]
    | some srcIt =>
      simp only [hsrcIt] at hsrc
      obtain ⟨eo, heo, rfl⟩ := translateRvalue_cast_int htgt hsrc he
      obtain ⟨haok, hanone⟩ := evalValue_operand h srcIt op hsrc eo heo
      cases hxo : opBits locals op with
      | none =>
        refine ⟨fun r hr => by simp [rvBits, hsrcIt, hxo] at hr, fun _ => ?_⟩
        obtain ⟨msg, hmsg⟩ := hanone hxo
        exact ⟨msg, by simp [evalValue, hmsg]⟩
      | some x =>
        obtain ⟨_, m1, hm1, h1⟩ := haok x hxo
        refine ⟨fun r hr => ?_, fun hnone => by simp [rvBits, hsrcIt, hxo] at hnone⟩
        simp [rvBits, hsrcIt, hxo] at hr
        subst hr
        have hpos := two_pow_pos (8 * it.size.bytes)
        have hlt : (intFromBits x srcIt % 2 ^ (8 * it.size.bytes)).toNat < 2 ^ (8 * it.size.bytes) := by
          have h0 := Int.emod_nonneg (intFromBits x srcIt) (Int.ne_of_gt hpos)
          have hlt' := Int.emod_lt_of_pos (intFromBits x srcIt) hpos
          have : (((intFromBits x srcIt % 2 ^ (8 * it.size.bytes)).toNat : Int)) < 2 ^ (8 * it.size.bytes) := by
            rw [Int.toNat_of_nonneg h0]; exact hlt'
          exact_mod_cast this
        refine ⟨hlt, m1, ?_, h1⟩
        simp [evalValue, hm1, evalUnOp, evalCastOp, bringInBounds_eq_intFromBits it hgood]

/-- The element list an Anneal array-producing rvalue evaluates to, or `none`
when evaluating it is UB. -/
def arrayRvElems (locals : List LocalSlot) (elemIt : Gen.IntType) : Rvalue → Option (List Value)
  | .use (.copy ⟨j, []⟩) =>
    match locals[j]? with
    | some (.init (.aggregate 0 elems)) => some elems
    | _ => none
  | .repeat op count => do
    let b ← opBits locals op
    pure (List.replicate count (.scalar ⟨b, elemIt.size.bytes⟩))
  | .aggregate (.array _) ops =>
    ops.mapM (fun op => do
      let b ← opBits locals op
      pure (.scalar ⟨b, elemIt.size.bytes⟩))
  | _ => none

theorem evalValues_operands {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {locals : List LocalSlot} {lm : Map Gen.LocalName Ptr} {m : Mach} {blk stmt : Nat}
    (h : FrameOk body f ctx locals lm m blk stmt)
    (elemIt : Gen.IntType) (ops : List Operand)
    (hok : ops.all (operandOk body.layouts body.localDecls elemIt) = true)
    (es : List Gen.ValueExpr) (hes : ops.mapM (translateOperand body.localDecls) = some es) :
    (∀ elems, (ops.mapM (fun op => do
        let b ← opBits locals op
        pure (Value.scalar ⟨b, elemIt.size.bytes⟩))) = some elems →
      elems.length = ops.length ∧
      (∀ v ∈ elems, ElemOk elemIt v) ∧
      ∃ m', evalValues m es = .ok (elems.map (valToMiniRust elemIt), m') ∧
        FrameOk body f ctx locals lm m' blk stmt) ∧
    ((ops.mapM (fun op => do
        let b ← opBits locals op
        pure (Value.scalar ⟨b, elemIt.size.bytes⟩))) = none →
      ∃ msg, evalValues m es = .error (.ub msg)) := by
  induction ops generalizing m es with
  | nil =>
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at hes
    subst hes
    refine ⟨fun elems hel => ?_, fun hnone => by simp at hnone⟩
    simp at hel
    subst hel
    exact ⟨rfl, by intro v hv; simp at hv, m, rfl, h⟩
  | cons op ops ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hok
    obtain ⟨hok1, hoks⟩ := hok
    simp only [List.mapM_cons, Option.bind_eq_bind] at hes
    cases he1 : translateOperand body.localDecls op with
    | none => simp [he1] at hes
    | some e1 =>
      cases hes' : ops.mapM (translateOperand body.localDecls) with
      | none => simp [he1, hes'] at hes
      | some es' =>
        simp [he1, hes'] at hes
        subst hes
        obtain ⟨haok, hanone⟩ := evalValue_operand h elemIt op hok1 e1 he1
        cases hb1 : opBits locals op with
        | none =>
          refine ⟨fun elems hel => by simp [hb1] at hel, fun _ => ?_⟩
          obtain ⟨msg, hmsg⟩ := hanone hb1
          exact ⟨msg, by simp [evalValues, hmsg]⟩
        | some b1 =>
          obtain ⟨hb1_lt, m1, hm1, h1⟩ := haok b1 hb1
          obtain ⟨ihok, ihnone⟩ := ih h1 hoks es' hes'
          cases hrest : ops.mapM (fun op => do
              let b ← opBits locals op
              pure (Value.scalar ⟨b, elemIt.size.bytes⟩)) with
          | none =>
            refine ⟨fun elems hel => by rw [List.mapM_cons, hb1, hrest] at hel; simp at hel, fun _ => ?_⟩
            obtain ⟨msg, hmsg⟩ := ihnone hrest
            exact ⟨msg, by simp [evalValues, hm1, hmsg]⟩
          | some elems' =>
            obtain ⟨hlen', he', m2, hm2, h2⟩ := ihok elems' hrest
            refine ⟨fun elems hel => ?_, fun hnone => by rw [List.mapM_cons, hb1, hrest] at hnone; simp at hnone⟩
            rw [List.mapM_cons, hb1, hrest] at hel
            simp at hel
            subst hel
            refine ⟨by simp [hlen'], ?_, m2, ?_, h2⟩
            · intro v hv
              simp only [List.mem_cons] at hv
              rcases hv with rfl | hv
              · exact ⟨rfl, hb1_lt⟩
              · exact he' v hv
            · simp [evalValues, hm1, hm2, valToMiniRust]

theorem evalValues_replicate {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {locals : List LocalSlot} {lm : Map Gen.LocalName Ptr} {m : Mach} {blk stmt : Nat}
    (h : FrameOk body f ctx locals lm m blk stmt)
    (elemIt : Gen.IntType) (count : Nat) (op : Operand)
    (hok : operandOk body.layouts body.localDecls elemIt op = true)
    (eo : Gen.ValueExpr) (heo : translateOperand body.localDecls op = some eo) :
    (∀ b, opBits locals op = some b →
      b < 2 ^ (8 * elemIt.size.bytes) ∧
      ∃ m', evalValues m (List.replicate count eo) =
          .ok ((List.replicate count (Value.scalar ⟨b, elemIt.size.bytes⟩)).map (valToMiniRust elemIt), m') ∧
        FrameOk body f ctx locals lm m' blk stmt) ∧
    (0 < count → opBits locals op = none →
      ∃ msg, evalValues m (List.replicate count eo) = .error (.ub msg)) := by
  induction count generalizing m with
  | zero =>
    obtain ⟨haok, _⟩ := evalValue_operand h elemIt op hok eo heo
    refine ⟨fun b hb => ⟨(haok b hb).1, m, rfl, h⟩, fun hpos => by omega⟩
  | succ k ih =>
    obtain ⟨haok, hanone⟩ := evalValue_operand h elemIt op hok eo heo
    refine ⟨fun b hb => ?_, fun _ hnone => ?_⟩
    · obtain ⟨hb_lt, m1, hm1, h1⟩ := haok b hb
      obtain ⟨_, m2, hm2, h2⟩ := (ih h1).1 b hb
      exact ⟨hb_lt, m2, by simp [List.replicate_succ, evalValues, hm1, hm2, valToMiniRust], h2⟩
    · obtain ⟨msg, hmsg⟩ := hanone hnone
      exact ⟨msg, by simp [List.replicate_succ, evalValues, hmsg]⟩

/-- Evaluating a translated array-producing rvalue. -/
theorem evalValue_arrayRvalue {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {locals : List LocalSlot} {lm : Map Gen.LocalName Ptr} {m : Mach} {blk stmt : Nat}
    {targetTy : Option MirAst.Ty}
    (h : FrameOk body f ctx locals lm m blk stmt)
    (elemIt : Gen.IntType) (count : Nat) (hgood : GoodSize elemIt.size.bytes)
    (rv : Rvalue) (hok : arrayRvalueOk body.layouts body.localDecls elemIt count rv = true)
    (e : Gen.ValueExpr) (he : translateRvalue body.layouts body.localDecls targetTy rv = some e) :
    (∀ elems, arrayRvElems locals elemIt rv = some elems →
      elems.length = count ∧
      (∀ v ∈ elems, ElemOk elemIt v) ∧
      ∃ m', evalValue m e =
          .ok ((.Tuple (elems.map (valToMiniRust elemIt)), .Array (.Int elemIt) (count : Int)), m') ∧
        FrameOk body f ctx locals lm m' blk stmt) ∧
    (arrayRvElems locals elemIt rv = none → ∃ msg, evalValue m e = .error (.ub msg)) := by
  match rv, hok, he with
  | .use (.copy ⟨j, []⟩), hok, he =>
    simp only [arrayRvalueOk, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨hj, hty⟩ := hok
    simp only [translateRvalue, translateOperand, translatePlace,
      Option.map_some, Option.some.injEq] at he
    subst he
    obtain ⟨d, slot, hd, hs⟩ := h.slot_exists j hj
    rw [hd] at hty
    simp only [Option.bind_eq_bind, Option.bind_some] at hty
    obtain ⟨hTd, hitd⟩ := tyOf_array (layouts := body.layouts) hty
    have hloc := (h.hf.2 j d hd).2
    rw [hTd] at hloc
    obtain ⟨⟨v, rfl⟩, _⟩ := h.nonScalar j d slot hd hs (scalarTypeOf_none_of_arrayTypeOf hty)
      (isPtrTy_false_of_arrayTypeOf hty)
    have hslot := (DeclSlotOk_of_arrayTypeOf hty (.init v)).mp (h.slots j d (.init v) hd hs)
    match v, hslot with
    | .aggregate 0 elems, ⟨hlen, he⟩ =>
      obtain ⟨p, hp⟩ := h.locs.some_of_live hs (by simp)
      obtain ⟨k, hpk, _, _, _, _, hA⟩ :=
        h.locs.storage_nonptr j d (.init (.aggregate 0 elems)) p hd hs hp
          (isPtrTy_false_of_arrayTypeOf hty)
      rw [hitd, declSlotData_of_array hty] at hA
      have hplace := evalPlace_local_some h.shape j _ hloc p hp
      obtain ⟨m1, hm1, hshape1⟩ := typedLoad_ptr_array h.shape p k hpk elemIt count elems
        hgood hlen he hA
      refine ⟨fun elems' hel => ?_, fun hnone => by simp [arrayRvElems, hs] at hnone⟩
      simp [arrayRvElems, hs] at hel
      subst hel
      exact ⟨hlen, he, m1, by simp [evalValue, hplace, placeLoad, hm1],
        FrameOk.mk' h.hf hshape1 h.locs h.declsOk h.nonScalar⟩
  | .aggregate (.array elemTy) ops, hok, he =>
    simp only [arrayRvalueOk, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨heTy, hlenOps⟩, hoks⟩ := hok
    subst hlenOps
    simp only [translateRvalue, heTy, Option.bind_eq_bind, Option.bind_some] at he
    cases hes : ops.mapM (translateOperand body.localDecls) with
    | none => simp [hes] at he
    | some es =>
      simp [hes] at he
      subst he
      obtain ⟨hlok, hlnone⟩ := evalValues_operands h elemIt ops hoks es hes
      cases hel : ops.mapM (fun op => do
          let b ← opBits locals op
          pure (Value.scalar ⟨b, elemIt.size.bytes⟩)) with
      | none =>
        refine ⟨(fun elems h1 => by rw [arrayRvElems, hel] at h1; contradiction), fun _ => ?_⟩
        obtain ⟨msg, hmsg⟩ := hlnone hel
        exact ⟨msg, by simp [evalValue, hmsg]⟩
      | some elems =>
        obtain ⟨hlen, he, m1, hm1, h1⟩ := hlok elems hel
        refine ⟨fun elems' h2 => ?_, (fun hnone => by rw [arrayRvElems, hel] at hnone; contradiction)⟩
        rw [arrayRvElems, hel] at h2
        cases h2
        refine ⟨hlen, he, m1, ?_, h1⟩
        simp [evalValue, hm1]
  | .repeat op n, hok, he =>
    simp only [arrayRvalueOk, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨rfl, hcnt⟩, hokOp⟩ := hok
    have hopTy := operandIntType_of_operandOk hokOp
    simp only [translateRvalue, hopTy, Option.bind_eq_bind, Option.bind_some] at he
    cases heo : translateOperand body.localDecls op with
    | none => simp [heo] at he
    | some eo =>
      simp [heo] at he
      subst he
      obtain ⟨hrepOk, hrepNone⟩ := evalValues_replicate h elemIt n op hokOp eo heo
      cases hb : opBits locals op with
      | none =>
        refine ⟨fun elems hel => by simp [arrayRvElems, hb] at hel, fun _ => ?_⟩
        rcases hcnt with hposCnt | hconst
        · obtain ⟨msg, hmsg⟩ := hrepNone hposCnt hb
          exact ⟨msg, by simp [evalValue, hmsg]⟩
        · cases op with
          | copy _ => simp at hconst
          | move _ => simp at hconst
          | constant c =>
            simp only [translateOperand] at heo
            split at heo
            · match hv : c.val, heo with
              | .scalar (.int sc), heo => simp [opBits, hv] at hb
            · match hv : c.val, intTypeOf c.ty, heo with
              | .scalar (.int sc), some _, heo => simp [opBits, hv] at hb
      | some b =>
        obtain ⟨hb_lt, m1, hm1, h1⟩ := hrepOk b hb
        refine ⟨fun elems hel => ?_, fun hnone => by simp [arrayRvElems, hb] at hnone⟩
        simp [arrayRvElems, hb] at hel
        subst hel
        have hlen : (List.replicate n (Value.scalar ⟨b, elemIt.size.bytes⟩)).length = n := by simp
        have he : ∀ v ∈ List.replicate n (Value.scalar ⟨b, elemIt.size.bytes⟩), ElemOk elemIt v := by
          intro v hv
          rw [List.eq_of_mem_replicate hv]
          exact ⟨rfl, hb_lt⟩
        refine ⟨hlen, he, m1, ?_, h1⟩
        simp [evalValue, hm1]

/-- Value an operand `op` of `TupleSpec` `spec` evaluates to in Anneal, or `none`
when evaluating it is UB. -/
def specOpVal (locals : List LocalSlot) (spec : TupleSpec) (op : Operand) : Option Value :=
  match spec with
  | .scalar it => do
    let b ← opBits locals op
    pure (.scalar ⟨b, it.size.bytes⟩)
  | .tuple _ _ _ =>
    match op with
    | .copy ⟨j, projs⟩ =>
      match locals[j]? with
      | some (.init rootVal) => readFieldPath rootVal projs
      | _ => none
    | _ => none

/-- Pointwise evaluation of aggregate field operands against `fields`. -/
def tupleFieldsOpsVal (locals : List LocalSlot) :
    List (Nat × TupleSpec) → List Operand → Option (List Value)
  | [], [] => some []
  | (_, fSpec) :: restF, op :: restOps => do
    let v ← specOpVal locals fSpec op
    let vs ← tupleFieldsOpsVal locals restF restOps
    pure (v :: vs)
  | _, _ => none

/-- Value a tuple/struct-producing rvalue evaluates to in Anneal, or `none`
when evaluating it is UB. -/
def tupleRvVal (locals : List LocalSlot) (fields : List (Nat × TupleSpec)) :
    Rvalue → Option Value
  | .use (.copy ⟨j, projs⟩) =>
    match locals[j]? with
    | some (.init rootVal) => readFieldPath rootVal projs
    | _ => none
  | .aggregate .tuple ops => do
    let vals ← tupleFieldsOpsVal locals fields ops
    pure (.aggregate 0 vals)
  | .aggregate (.adt _ 0 none) ops => do
    let vals ← tupleFieldsOpsVal locals fields ops
    pure (.aggregate 0 vals)
  | _ => none

theorem tuplePlaceSpec_resolve {layouts : Layout.LayoutTable} {decls : List LocalDecl}
    {p : MirAst.Place} {fields : List (Nat × TupleSpec)} {size align : Nat}
    (h : tuplePlaceSpec layouts decls p = some (fields, size, align)) :
    ∃ d rootFields rootSize rootAlign relOff,
      p.local_ < decls.length ∧
      decls[p.local_]? = some d ∧
      tupleTypeOf layouts d.ty = some (rootFields, rootSize, rootAlign) ∧
      resolveFieldPath layouts (.tuple rootFields rootSize rootAlign) p.projection =
        some (relOff, .tuple fields size align) ∧
      translatePlace decls p = translateFieldPlace (.Local (localName p.local_)) p.projection := by
  match p, h with
  | ⟨j, []⟩, h =>
    simp only [tuplePlaceSpec] at h
    split at h
    · next hj =>
      cases hd : decls[j]? with
      | none => simp [hd] at h
      | some d =>
        simp only [hd, Option.bind_eq_bind, Option.bind_some] at h
        exact ⟨d, fields, size, align, 0, hj, rfl, h, rfl, rfl⟩
    · simp at h
  | ⟨j, .field idx fieldTy :: rest⟩, h =>
    simp only [tuplePlaceSpec] at h
    split at h
    · next hj =>
      cases hd : decls[j]? with
      | none => simp [hd] at h
      | some d =>
        simp only [hd, Option.bind_eq_bind, Option.bind_some] at h
        cases ht : tupleTypeOf layouts d.ty with
        | none => simp [ht] at h
        | some rpair =>
          obtain ⟨rootFields, rootSize, rootAlign⟩ := rpair
          simp only [ht, Option.bind_some] at h
          cases hres : resolveFieldPath layouts (.tuple rootFields rootSize rootAlign)
              (.field idx fieldTy :: rest) with
          | none => simp [hres] at h
          | some lpair =>
            obtain ⟨relOff, leafSpec⟩ := lpair
            simp only [hres, Option.bind_some] at h
            cases leafSpec with
            | scalar _ => simp at h
            | tuple subFields subSize subAlign =>
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              rcases h with ⟨rfl, rfl, rfl⟩
              exact ⟨d, rootFields, rootSize, rootAlign, relOff, hj, rfl, ht, hres, rfl⟩
    · simp at h

theorem evalPlace_tuplePlace {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {locals : List LocalSlot} {lm : Map Gen.LocalName Ptr} {m : Mach} {blk stmt : Nat}
    (h : FrameOk body f ctx locals lm m blk stmt)
    (pl : MirAst.Place) (fields : List (Nat × TupleSpec)) (size align : Nat)
    (htp : tuplePlaceSpec body.layouts body.localDecls pl = some (fields, size, align))
    (pe : Gen.PlaceExpr) (hpe : translatePlace body.localDecls pl = some pe) :
    ∃ d rootFields rootSize rootAlign rootVal relOff ptr,
      pl.local_ < body.localDecls.length ∧
      body.localDecls[pl.local_]? = some d ∧
      tupleTypeOf body.layouts d.ty = some (rootFields, rootSize, rootAlign) ∧
      locals[pl.local_]? = some (.init rootVal) ∧
      mapGet lm (localName pl.local_) = some ptr ∧
      (TupleSpec.tuple rootFields rootSize rootAlign).wf = true ∧
      (TupleSpec.tuple rootFields rootSize rootAlign).valOk rootVal = true ∧
      resolveFieldPath body.layouts (.tuple rootFields rootSize rootAlign) pl.projection =
        some (relOff, .tuple fields size align) ∧
      (TupleSpec.tuple fields size align).wf = true ∧
      relOff + size ≤ rootSize ∧
      evalPlace m pe =
        .ok (({ ptr := { thin_pointer := offsetPtr ptr relOff, metadata := none },
                 aligned := true },
               (TupleSpec.tuple fields size align).toMiniRustTy), m) := by
  obtain ⟨d, rootFields, rootSize, rootAlign, relOff, hj, hd, ht, hres, htrPlace⟩ :=
    tuplePlaceSpec_resolve htp
  rw [htrPlace] at hpe
  obtain ⟨_, slot, hd', hs⟩ := h.slot_exists pl.local_ hj
  rw [hd] at hd'; cases hd'
  obtain ⟨⟨rootVal, rfl⟩, _⟩ :=
    h.nonScalar pl.local_ d slot hd hs (scalarTypeOf_none_of_tupleTypeOf ht)
      (isPtrTy_false_of_tupleTypeOf ht)
  obtain ⟨hrootWf, hrootVal⟩ :=
    (DeclSlotOk_of_tupleTypeOf ht (.init rootVal)).mp (h.slots pl.local_ d (.init rootVal) hd hs)
  obtain ⟨ptr, hptr⟩ := h.locs.some_of_live hs (by simp)
  obtain ⟨k, hpk, _, haddr, haddrMax, _, hA⟩ :=
    h.locs.storage_nonptr pl.local_ d (.init rootVal) ptr hd hs hptr
      (isPtrTy_false_of_tupleTypeOf ht)
  obtain ⟨hTd, _⟩ := tyOf_tupleSpec ht
  rw [declSlotData_of_tupleSpec ht] at hA
  obtain ⟨hleafWf, hrelBound⟩ := resolveFieldPath_wf hrootWf hres
  have hloc := (h.hf.2 pl.local_ d hd).2
  rw [hTd] at hloc
  have hplaceBase := evalPlace_local_some h.shape pl.local_ _ hloc ptr hptr
  have hdlen : ((TupleSpec.tuple rootFields rootSize rootAlign).encodeVal rootVal).length = rootSize :=
    TupleSpec.encodeVal_length (.tuple rootFields rootSize rootAlign) rootVal hrootWf
  have hbound : rootSize < 2 ^ 63 := by
    simp only [TupleSpec.wf, Bool.and_eq_true, decide_eq_true_eq] at hrootWf
    exact hrootWf.1.2
  rw [hTd] at haddrMax
  simp only [TupleSpec.toMiniRustTy, tyBytes] at haddrMax
  have hrootEval : evalPlace m (.Local (localName pl.local_)) =
      .ok (({ ptr := { thin_pointer := offsetPtr ptr 0, metadata := none },
               aligned := true },
             (TupleSpec.tuple rootFields rootSize rootAlign).toMiniRustTy), m) := by
    simpa using hplaceBase
  have hpeEval := evalPlace_ptr_fieldPath h.shape ptr k hpk
    (itOf d body.layouts) ((TupleSpec.tuple rootFields rootSize rootAlign).encodeVal rootVal) hA
    (by rw [hdlen]; exact hbound) haddr.nonneg (by rw [hdlen]; exact haddrMax)
    (.Local (localName pl.local_)) 0 (.tuple rootFields rootSize rootAlign) hrootEval hrootWf
    (by simp [TupleSpec.size, hdlen]) pl.projection pe hpe
    relOff (.tuple fields size align) hres
  simp only [Nat.zero_add] at hpeEval
  exact ⟨d, rootFields, rootSize, rootAlign, rootVal, relOff, ptr,
    hj, hd, ht, hs, hptr, hrootWf, hrootVal, hres, hleafWf, hrelBound, hpeEval⟩

theorem evalValue_specOperand {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {locals : List LocalSlot} {lm : Map Gen.LocalName Ptr} {m : Mach} {blk stmt : Nat}
    (h : FrameOk body f ctx locals lm m blk stmt)
    (spec : TupleSpec) (op : Operand)
    (hok : specOperandOk body.layouts body.localDecls spec op = true)
    (e : Gen.ValueExpr) (he : translateOperand body.localDecls op = some e) :
    (∀ v, specOpVal locals spec op = some v →
      spec.valOk v = true ∧
      ∃ m', evalValue m e = .ok ((spec.toMiniRustVal v, spec.toMiniRustTy), m') ∧
        FrameOk body f ctx locals lm m' blk stmt) ∧
    (specOpVal locals spec op = none → ∃ msg, evalValue m e = .error (.ub msg)) := by
  cases spec with
  | scalar it =>
    simp only [specOperandOk] at hok
    obtain ⟨haok, hanone⟩ := evalValue_operand h it op hok e he
    cases hb : opBits locals op with
    | none =>
      refine ⟨fun v hv => by simp [specOpVal, hb] at hv, fun _ => hanone hb⟩
    | some b =>
      obtain ⟨hb_lt, m1, hm1, h1⟩ := haok b hb
      refine ⟨fun v hv => ?_, fun hnone => by simp [specOpVal, hb] at hnone⟩
      simp [specOpVal, hb] at hv
      subst hv
      exact ⟨by simp [TupleSpec.valOk, hb_lt], m1, hm1, h1⟩
  | tuple fields size align =>
    cases op with
    | move _ | constant _ => simp [specOperandOk] at hok
    | copy pl =>
      simp only [specOperandOk, Bool.and_eq_true, decide_eq_true_eq] at hok
      obtain ⟨htp, _⟩ := hok
      simp only [translateOperand] at he
      cases hpe : translatePlace body.localDecls pl with
      | none => simp [hpe] at he
      | some pe =>
        simp only [hpe, Option.map_some, Option.some.injEq] at he
        subst he
        obtain ⟨d, rootFields, rootSize, rootAlign, rootVal, relOff, ptr,
          _, hd, ht, hs, hptr, hrootWf, hrootVal, hres, hleafWf, hrelBound, hpeEval⟩ :=
          evalPlace_tuplePlace h pl fields size align htp pe hpe
        obtain ⟨leafVal, hread, hleafValOk, hslice, _⟩ :=
          resolveFieldPath_read hrootWf hrootVal hres
        obtain ⟨k, hpk, _, _, _, _, hA⟩ :=
          h.locs.storage_nonptr pl.local_ d (.init rootVal) ptr hd hs hptr
            (isPtrTy_false_of_tupleTypeOf ht)
        rw [declSlotData_of_tupleSpec ht] at hA
        have hdlen : ((TupleSpec.tuple rootFields rootSize rootAlign).encodeVal rootVal).length = rootSize :=
          TupleSpec.encodeVal_length (.tuple rootFields rootSize rootAlign) rootVal hrootWf
        obtain ⟨m', hm', hshape'⟩ := typedLoad_ptr_tuple_slice h.shape ptr k hpk
          (itOf d body.layouts) ((TupleSpec.tuple rootFields rootSize rootAlign).encodeVal rootVal) hA
          relOff (.tuple fields size align) leafVal hleafWf hleafValOk
          (by rw [hdlen]; exact hrelBound) hslice
        refine ⟨fun v hv => ?_, fun hnone => ?_⟩
        · cases pl; simp [specOpVal, hs, hread] at hv
          subst hv
          exact ⟨hleafValOk, m', by simp [evalValue, hpeEval, placeLoad, hm'],
            FrameOk.mk' h.hf hshape' h.locs h.declsOk h.nonScalar⟩
        · cases pl; simp [specOpVal, hs, hread] at hnone

theorem evalValues_tupleFields {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {locals : List LocalSlot} {lm : Map Gen.LocalName Ptr} {m : Mach} {blk stmt : Nat}
    (h : FrameOk body f ctx locals lm m blk stmt)
    (fields : List (Nat × TupleSpec)) (ops : List Operand)
    (hok : tupleFieldsOperandOk body.layouts body.localDecls fields ops = true)
    (es : List Gen.ValueExpr) (hes : ops.mapM (translateOperand body.localDecls) = some es) :
    (∀ vals, tupleFieldsOpsVal locals fields ops = some vals →
      TupleSpec.fieldsValOk fields vals = true ∧
      ∃ m', evalValues m es = .ok (TupleSpec.fieldsToMiniRustVal fields vals, m') ∧
        FrameOk body f ctx locals lm m' blk stmt) ∧
    (tupleFieldsOpsVal locals fields ops = none →
      ∃ msg, evalValues m es = .error (.ub msg)) := by
  induction fields generalizing ops m es with
  | nil =>
    cases ops <;> simp [tupleFieldsOperandOk] at hok
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at hes
    subst hes
    refine ⟨fun vals hvals => ?_, fun hnone => by simp [tupleFieldsOpsVal] at hnone⟩
    simp [tupleFieldsOpsVal] at hvals
    subst hvals
    exact ⟨rfl, m, rfl, h⟩
  | cons f restF ih =>
    obtain ⟨off, fSpec⟩ := f
    cases ops with
    | nil => simp [tupleFieldsOperandOk] at hok
    | cons op restOps =>
      simp only [tupleFieldsOperandOk, Bool.and_eq_true] at hok
      obtain ⟨hok1, hoks⟩ := hok
      simp only [List.mapM_cons, Option.bind_eq_bind] at hes
      cases he1 : translateOperand body.localDecls op with
      | none => simp [he1] at hes
      | some e1 =>
        cases hes' : restOps.mapM (translateOperand body.localDecls) with
        | none => simp [he1, hes'] at hes
        | some es' =>
          simp [he1, hes'] at hes
          subst hes
          obtain ⟨haok, hanone⟩ := evalValue_specOperand h fSpec op hok1 e1 he1
          cases hv1 : specOpVal locals fSpec op with
          | none =>
            refine ⟨fun vals hvals => by simp [tupleFieldsOpsVal, hv1] at hvals, fun _ => ?_⟩
            obtain ⟨msg, hmsg⟩ := hanone hv1
            exact ⟨msg, by simp [evalValues, hmsg]⟩
          | some v1 =>
            obtain ⟨hv1Ok, m1, hm1, h1⟩ := haok v1 hv1
            obtain ⟨ihok, ihnone⟩ := ih h1 restOps hoks es' hes'
            cases hrest : tupleFieldsOpsVal locals restF restOps with
            | none =>
              refine ⟨fun vals hvals => by simp [tupleFieldsOpsVal, hv1, hrest] at hvals, fun _ => ?_⟩
              obtain ⟨msg, hmsg⟩ := ihnone hrest
              exact ⟨msg, by simp [evalValues, hm1, hmsg]⟩
            | some vals' =>
              obtain ⟨hvals'Ok, m2, hm2, h2⟩ := ihok vals' hrest
              refine ⟨fun vals hvals => ?_, fun hnone => by simp [tupleFieldsOpsVal, hv1, hrest] at hnone⟩
              simp [tupleFieldsOpsVal, hv1, hrest] at hvals
              subst hvals
              exact ⟨by simp [TupleSpec.fieldsValOk, hv1Ok, hvals'Ok], m2,
                by simp [evalValues, hm1, hm2, TupleSpec.fieldsToMiniRustVal], h2⟩

theorem evalValue_tupleRvalue {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {locals : List LocalSlot} {lm : Map Gen.LocalName Ptr} {m : Mach} {blk stmt : Nat}
    (h : FrameOk body f ctx locals lm m blk stmt)
    (dstTy : MirAst.Ty) (fields : List (Nat × TupleSpec)) (size align : Nat)
    (rv : Rvalue) (hok : tupleRvalueOk body.layouts body.localDecls dstTy fields size align rv = true)
    (e : Gen.ValueExpr) (he : translateRvalue body.layouts body.localDecls (some dstTy) rv = some e) :
    (∀ val, tupleRvVal locals fields rv = some val →
      (TupleSpec.tuple fields size align).valOk val = true ∧
      ∃ m', evalValue m e = .ok (((TupleSpec.tuple fields size align).toMiniRustVal val,
                                    (TupleSpec.tuple fields size align).toMiniRustTy), m') ∧
        FrameOk body f ctx locals lm m' blk stmt) ∧
    (tupleRvVal locals fields rv = none → ∃ msg, evalValue m e = .error (.ub msg)) := by
  match rv, hok, he with
  | .use (.copy pl), hok, he =>
    simp only [tupleRvalueOk, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨htp, hpeSome⟩ := hok
    simp only [translateRvalue] at he
    have hspecOk : specOperandOk body.layouts body.localDecls (.tuple fields size align) (.copy pl) = true := by
      simp [specOperandOk, htp, translateOperand, hpeSome]
    have hev := evalValue_specOperand h (.tuple fields size align) (.copy pl) hspecOk e he
    cases pl; simpa [tupleRvVal, specOpVal] using hev
  | .aggregate .tuple ops, hok, he =>
    simp only [tupleRvalueOk, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨_, htup⟩, hfieldsOk⟩ := hok
    have hnoIB := (not_scalar_of_tupleTypeOf htup).2.2.1
    simp only [translateRvalue, Option.bind_eq_bind, Option.bind_some, hnoIB, htup] at he
    cases hes : ops.mapM (translateOperand body.localDecls) with
    | none => simp [hes] at he
    | some es =>
      simp [hes] at he
      subst he
      obtain ⟨hlok, hlnone⟩ := evalValues_tupleFields h fields ops hfieldsOk es hes
      cases hvals : tupleFieldsOpsVal locals fields ops with
      | none =>
        refine ⟨fun val hval => by simp [tupleRvVal, hvals] at hval, fun _ => ?_⟩
        obtain ⟨msg, hmsg⟩ := hlnone hvals
        exact ⟨msg, by simp [evalValue, hmsg]⟩
      | some vals =>
        obtain ⟨hvalsOk, m1, hm1, h1⟩ := hlok vals hvals
        refine ⟨fun val hval => ?_, fun hnone => by simp [tupleRvVal, hvals] at hnone⟩
        simp [tupleRvVal, hvals] at hval
        subst hval
        exact ⟨by simp [TupleSpec.valOk, TupleSpec.fieldsValOk_length hvalsOk, hvalsOk],
          m1, by simp [evalValue, hm1, TupleSpec.toMiniRustVal], h1⟩
  | .aggregate (.adt _ 0 none) ops, hok, he =>
    simp only [tupleRvalueOk, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨_, htup⟩, hfieldsOk⟩ := hok
    simp only [translateRvalue, Option.bind_eq_bind, Option.bind_some, htup] at he
    cases hes : ops.mapM (translateOperand body.localDecls) with
    | none => simp [hes] at he
    | some es =>
      simp [hes] at he
      subst he
      obtain ⟨hlok, hlnone⟩ := evalValues_tupleFields h fields ops hfieldsOk es hes
      cases hvals : tupleFieldsOpsVal locals fields ops with
      | none =>
        refine ⟨fun val hval => by simp [tupleRvVal, hvals] at hval, fun _ => ?_⟩
        obtain ⟨msg, hmsg⟩ := hlnone hvals
        exact ⟨msg, by simp [evalValue, hmsg]⟩
      | some vals =>
        obtain ⟨hvalsOk, m1, hm1, h1⟩ := hlok vals hvals
        refine ⟨fun val hval => ?_, fun hnone => by simp [tupleRvVal, hvals] at hnone⟩
        simp [tupleRvVal, hvals] at hval
        subst hval
        exact ⟨by simp [TupleSpec.valOk, TupleSpec.fieldsValOk_length hvalsOk, hvalsOk],
          m1, by simp [evalValue, hm1, TupleSpec.toMiniRustVal], h1⟩

/-! ## Frames and control flow -/

theorem mutateCurFrame_eq {m : Mach} {ctx : Ctx} {fr : Frame} {allocs : List Gen.Allocation}
    (h : Shape m ctx [ctx.caller, fr] allocs) (g : Frame → Frame) :
    ∃ m', mutateCurFrame m g = .ok m' ∧ Shape m' ctx [ctx.caller, g fr] allocs := by
  refine ⟨{ m with threads := [thread1 ctx [ctx.caller, g fr]] }, ?_, ⟨rfl, h.active, h.allocs⟩⟩
  simp [mutateCurFrame, activeThread, listIndex, h.threads, h.active, thread1, listSet]

theorem jumpToBlock_callee {m : Mach} {ctx : Ctx} {f : Gen.Function} {lm : Map Gen.LocalName Ptr}
    {blk stmt : Nat} {allocs : List Gen.Allocation}
    (h : Shape m ctx [ctx.caller, calleeFrameL f ctx lm blk stmt] allocs) (t : Nat) :
    ∃ m', jumpToBlock m (bbName t) = .ok m' ∧
      Shape m' ctx [ctx.caller, calleeFrameL f ctx lm t 0] allocs :=
  mutateCurFrame_eq h _

theorem bumpStmt_callee {m : Mach} {ctx : Ctx} {f : Gen.Function} {lm : Map Gen.LocalName Ptr}
    {blk stmt : Nat} {allocs : List Gen.Allocation}
    (h : Shape m ctx [ctx.caller, calleeFrameL f ctx lm blk stmt] allocs) :
    ∃ m', mutateCurFrame m (fun fr => { fr with next_stmt := fr.next_stmt + 1 }) = .ok m' ∧
      Shape m' ctx [ctx.caller, calleeFrameL f ctx lm blk (stmt + 1)] allocs := by
  obtain ⟨m', hm', hs⟩ := mutateCurFrame_eq h (fun fr => { fr with next_stmt := fr.next_stmt + 1 })
  refine ⟨m', hm', ?_⟩
  have : ({ calleeFrameL f ctx lm blk stmt with
      next_stmt := (calleeFrameL f ctx lm blk stmt).next_stmt + 1 } : Frame) =
      calleeFrameL f ctx lm blk (stmt + 1) := by
    simp [calleeFrameL]
  rw [this] at hs; exact hs

theorem prov_inj (a b : Nat) :
    (some (⟨(a : Int)⟩, ()) : Option Prov) = some (⟨(b : Int)⟩, ()) ↔ a = b := by
  constructor
  · intro h; simp at h; omega
  · intro h; subst h; rfl

/-- The allocation behind a non-pointer local is the one its pointer's provenance names. -/
theorem LocalsOkA.storage_id {body : CapturedMir} {ctx : Ctx} {al : List Nat}
    {locals : List LocalSlot} {lm : Map Gen.LocalName Ptr} {A : List Gen.Allocation}
    (hlo : LocalsOkA body ctx al locals lm A)
    {i : Nat} {d : LocalDecl} {slot : LocalSlot} {p : Ptr} (hd : body.localDecls[i]? = some d)
    (hs : locals[i]? = some slot) (hp : mapGet lm (localName i) = some p) {k : Nat}
    (hpk : p.provenance = some (⟨(k : Int)⟩, ())) (hnp : isPtrTy d.ty = false) :
    ctx.base.length ≤ k ∧ AddrOk p.addr (itOf d body.layouts) ∧
      p.addr + (tyBytes (tyOf d body.layouts) : Int) < 2 ^ 64 ∧
      AddrClass p.addr (tyBytes (tyOf d body.layouts)) ∧
      A[k]? = some (stackAlloc p.addr (itOf d body.layouts) (declSlotData d slot body.layouts)) := by
  obtain ⟨id, hpid, hb, ha, hmax, hc, hA⟩ := hlo.storage_nonptr i d slot p hd hs hp hnp
  have : id = k := (prov_inj id k).mp (hpid.symm.trans hpk)
  subst this
  exact ⟨hb, ha, hmax, hc, hA⟩

/-- A layout-backed tuple/struct type is never an `(Int, bool)` 2-tuple type. -/
theorem tupleIntOfTy_tupleSpec (fields : List (Nat × TupleSpec)) (size align : Nat) :
    tupleIntOfTy (TupleSpec.tuple fields size align).toMiniRustTy = none := by
  match fields with
  | [] => rfl
  | [(o0, s0)] => simp [TupleSpec.toMiniRustTy, TupleSpec.fieldsToMiniRust, tupleIntOfTy]
  | [(o0, s0), (o1, s1)] =>
    have hne := TupleSpec.toMiniRustTy_ne_bool s1
    cases h1 : s1.toMiniRustTy <;>
      simp_all [TupleSpec.toMiniRustTy, TupleSpec.fieldsToMiniRust, tupleIntOfTy]
  | _ :: _ :: _ :: _ => simp [TupleSpec.toMiniRustTy, TupleSpec.fieldsToMiniRust, tupleIntOfTy]

/-- An initialized `SlotOk` slot holds a scalar with valid bits, or an
`(Int, bool)` 2-tuple of a 2-tuple type. -/
theorem SlotOk.init_cases {T : Gen.Type} {v : Value} (h : SlotOk T (.init v)) :
    (∃ sc, v = .scalar sc ∧ ValidBits T sc.bits) ∨ (∃ it, tupleIntOfTy T = some it) := by
  unfold SlotOk at h
  split at h
  next _ heq => cases heq
  next _ heq => cases heq
  next _ sc heq => cases heq; exact .inl ⟨sc, rfl, h.2⟩
  next _ sc0 sc1 heq => obtain ⟨it, hit, _⟩ := h; exact .inr ⟨it, hit⟩
  next => exact h.elim

/-- `SlotOk` at a local's declared type gives `DeclSlotOk`: array, layout-backed
tuple/struct, and pointer types have no initialized `SlotOk` slot. -/
theorem declSlotOk_of_slotOk_tyOf {d : LocalDecl} {L : Layout.LayoutTable} {slot : LocalSlot}
    (h : SlotOk (tyOf d L) slot) : DeclSlotOk d slot L := by
  cases hs : scalarTypeOf d.ty with
  | some T => exact (DeclSlotOk_of_scalarTypeOf hs slot).mpr h
  | none =>
    cases slot with
    | dead => unfold DeclSlotOk; split <;> trivial
    | uninit => unfold DeclSlotOk; split <;> trivial
    | init v =>
      cases ha : arrayTypeOf d.ty with
      | some p =>
        obtain ⟨elemIt, count⟩ := p
        rw [(tyOf_array ha).1] at h
        rcases h.init_cases with ⟨sc, _, hv⟩ | ⟨it, hit⟩
        · simp [ValidBits] at hv
        · simp at hit
      | none =>
        cases ht : tupleTypeOf L d.ty with
        | some p =>
          obtain ⟨fields, size, align⟩ := p
          rw [(tyOf_tupleSpec ht).1] at h
          rcases h.init_cases with ⟨sc, _, hv⟩ | ⟨it, hit⟩
          · simp [TupleSpec.toMiniRustTy, ValidBits] at hv
          · rw [tupleIntOfTy_tupleSpec] at hit; cases hit
        | none =>
          cases hp : isPtrTy d.ty with
          | true =>
            rw [(tyOf_isPtrTy hp).1] at h
            rcases h.init_cases with ⟨sc, _, hv⟩ | ⟨it, hit⟩
            · rcases declPtrTy_cases d.ty with hraw | ⟨mutbl, it', _, href⟩
              · rw [hraw] at hv; simp [thinRawPtrTy, ValidBits] at hv
              · rw [href] at hv; simp [refTy, ValidBits] at hv
            · rcases declPtrTy_cases d.ty with hraw | ⟨mutbl, it', _, href⟩
              · rw [hraw] at hit; simp [thinRawPtrTy] at hit
              · rw [href] at hit; simp [refTy] at hit
          | false =>
            simp only [DeclSlotOk, hs, ha, ht, hp, Option.isSome_none, Bool.false_eq_true,
              ↓reduceIte]
            exact h

/-- Writing the live slot `slot'` into the live local `_i`, whose allocation is
`k`, keeps `LocalsOkA` whenever `DeclSlotOk` holds and `slot'` is not a pointer
slot on a non-pointer declaration (`hnp`). -/
theorem LocalsOkA.store_decl {body : CapturedMir} {ctx : Ctx} {al : List Nat}
    {locals : List LocalSlot} {lm : Map Gen.LocalName Ptr} {A : List Gen.Allocation}
    (hlo : LocalsOkA body ctx al locals lm A)
    (i : Nat) (d : LocalDecl) (hd : body.localDecls[i]? = some d) (slot slot' : LocalSlot)
    (hs : locals[i]? = some slot) (hlive' : slot' ≠ .dead)
    (hslot' : DeclSlotOk d slot' body.layouts)
    (p : Ptr) (hp : mapGet lm (localName i) = some p) (k : Nat)
    (hpk : p.provenance = some (⟨(k : Int)⟩, ()))
    (hnp : isPtrTy d.ty = false ∨ (∀ pv, slot' ≠ .init (.ptr pv 8))) :
    LocalsOkA body ctx al (locals.set i slot') lm
      (A.set k (stackAlloc p.addr (itOf d body.layouts) (declSlotData d slot' body.layouts))) := by
  have hil : i < locals.length := (List.getElem?_eq_some_iff.mp hs).1
  obtain ⟨id0, hpid0, hbase, haddr, haddrMax, hcls, hA0⟩ := hlo.storage i d slot p hd hs hp
  have hid0 : id0 = k := (prov_inj id0 k).mp (hpid0.symm.trans hpk)
  subst id0
  have hk : k < A.length := by
    cases hp_ty : isPtrTy d.ty with
    | false =>
      simp only [hp_ty, Bool.false_eq_true, ↓reduceIte] at hA0
      exact (List.getElem?_eq_some_iff.mp hA0).1
    | true =>
      simp only [hp_ty, ↓reduceIte] at hA0
      split at hA0
      · obtain ⟨_, _, _, _, hAk⟩ := hA0
        exact (List.getElem?_eq_some_iff.mp hAk).1
      · exact (List.getElem?_eq_some_iff.mp hA0).1
  refine {
    nlocals := by simp [hlo.nlocals]
    slots := ?_
    base := ?_
    keysNodup := hlo.keysNodup
    keysLocal := hlo.keysLocal
    live := ?_
    storage := ?_
    inj := hlo.inj
    owned := ?_ }
  · intro j dj sj hdj hsj
    by_cases hij : i = j
    · subst hij
      rw [hd] at hdj; cases hdj
      rw [List.getElem?_set_self hil] at hsj; cases hsj
      exact hslot'
    · rw [List.getElem?_set_ne hij] at hsj
      exact hlo.slots j dj sj hdj hsj
  · obtain ⟨R, hR⟩ := hlo.base
    refine ⟨R.set (k - ctx.base.length)
        (stackAlloc p.addr (itOf d body.layouts) (declSlotData d slot' body.layouts)), ?_⟩
    rw [hR, List.set_append_right _ _ hbase]
  · intro j sj hsj
    by_cases hij : i = j
    · subst hij
      rw [List.getElem?_set_self hil] at hsj; cases hsj
      simp [hp, hlive']
    · rw [List.getElem?_set_ne hij] at hsj
      exact hlo.live j sj hsj
  · intro j dj sj q hdj hsj hq
    by_cases hij : i = j
    · subst hij
      rw [hd] at hdj; cases hdj
      rw [hp] at hq; cases hq
      rw [List.getElem?_set_self hil] at hsj; cases hsj
      refine ⟨k, hpk, hbase, haddr, haddrMax, hcls, ?_⟩
      cases hp_ty : isPtrTy d.ty with
      | false =>
        simp [List.getElem?_set_self hk]
      | true =>
        simp only [↓reduceIte]
        rcases hnp with hfalse | hnotPtr
        · rw [hp_ty] at hfalse; cases hfalse
        · split
          · next pv => exact False.elim (hnotPtr pv rfl)
          · exact List.getElem?_set_self hk
    · rw [List.getElem?_set_ne hij] at hsj
      obtain ⟨id, hqid, hb', ha', hmax', hc', hA'⟩ := hlo.storage j dj sj q hdj hsj hq
      have hne : k ≠ id := fun hki => hij (hlo.inj i j p q hp hq (by subst hki; rw [hpk, hqid]))
      refine ⟨id, hqid, hb', ha', hmax', hc', ?_⟩
      simpa only [List.getElem?_set_ne hne] using hA'
  · intro id a ha hlivea hb
    by_cases hki : k = id
    · subst hki
      exact ⟨i, p, hp, hpk⟩
    · rw [List.getElem?_set_ne hki] at ha
      exact hlo.owned id a ha hlivea hb

/-- Writing the live slot `slot'` into the live local `_i`, whose allocation is
`k`, keeps `LocalsOkA`. -/
theorem LocalsOkA.store {body : CapturedMir} {ctx : Ctx} {al : List Nat} {locals : List LocalSlot}
    {lm : Map Gen.LocalName Ptr} {A : List Gen.Allocation}
    (hlo : LocalsOkA body ctx al locals lm A)
    (i : Nat) (d : LocalDecl) (hd : body.localDecls[i]? = some d) (slot slot' : LocalSlot)
    (hs : locals[i]? = some slot) (hlive' : slot' ≠ .dead)
    (hslot' : SlotOk (tyOf d body.layouts) slot')
    (p : Ptr) (hp : mapGet lm (localName i) = some p) (k : Nat)
    (hpk : p.provenance = some (⟨(k : Int)⟩, ())) :
    LocalsOkA body ctx al (locals.set i slot') lm
      (A.set k (stackAlloc p.addr (itOf d body.layouts) (declSlotData d slot' body.layouts))) :=
  hlo.store_decl i d hd slot slot' hs hlive' (declSlotOk_of_slotOk_tyOf hslot') p hp k hpk
    (.inr fun pv heq => by subst heq; simp [SlotOk] at hslot')

/-- The allocation behind any well-typed local (including raw-pointer locals)
is the one its pointer's provenance names. -/
theorem LocalsOkA.storage_any_id {body : CapturedMir} {ctx : Ctx} {al : List Nat}
    {locals : List LocalSlot} {lm : Map Gen.LocalName Ptr} {A : List Gen.Allocation}
    (hlo : LocalsOkA body ctx al locals lm A)
    {i : Nat} {d : LocalDecl} {slot : LocalSlot} {p : Ptr} (hd : body.localDecls[i]? = some d)
    (hs : locals[i]? = some slot) (hp : mapGet lm (localName i) = some p) {k : Nat}
    (hpk : p.provenance = some (⟨(k : Int)⟩, ()))
    (hdok : localDeclOk body.layouts d = true) :
    ∃ data : List Byte,
      ctx.base.length ≤ k ∧ AddrOk p.addr (itOf d body.layouts) ∧
      p.addr + (tyBytes (tyOf d body.layouts) : Int) < 2 ^ 64 ∧
      AddrClass p.addr (tyBytes (tyOf d body.layouts)) ∧
      data.length = tyBytes (tyOf d body.layouts) ∧
      A[k]? = some (stackAlloc p.addr (itOf d body.layouts) data) := by
  obtain ⟨id, data, hpid, hb, ha, hmax, hc, hlen, hA⟩ := hlo.storage_any hd hs hp hdok
  have : id = k := (prov_inj id k).mp (hpid.symm.trans hpk)
  subst this
  exact ⟨data, hb, ha, hmax, hc, hlen, hA⟩

/-- Writing the live non-pointer slot `slot'` (or `.uninit` on any local) into
the live local `_i`, whose allocation is `k`, keeps `LocalsOk`. -/
theorem LocalStorage.congr_getElem? {ctx : Ctx} {A A' : List Gen.Allocation}
    {d : LocalDecl} {slot : LocalSlot} {p : Ptr} {layouts : Layout.LayoutTable}
    (h : LocalStorage ctx A d slot p layouts)
    (heq : ∀ (id : Nat), p.provenance = some (⟨(id : Int)⟩, ()) → A'[id]? = A[id]?) :
    LocalStorage ctx A' d slot p layouts := by
  obtain ⟨id, hpid, hb, ha, hmax, hc, hA⟩ := h
  refine ⟨id, hpid, hb, ha, hmax, hc, ?_⟩
  simpa only [heq id hpid] using hA

/-- The allocation number behind a local's storage is in range. -/
theorem LocalStorage.exists_id_lt {ctx : Ctx} {A : List Gen.Allocation} {d : LocalDecl}
    {slot : LocalSlot} {p : Ptr} {layouts : Layout.LayoutTable}
    (h : LocalStorage ctx A d slot p layouts) :
    ∃ id : Nat, p.provenance = some (⟨(id : Int)⟩, ()) ∧ id < A.length := by
  obtain ⟨id, hpid, _, _, _, _, hA⟩ := h
  refine ⟨id, hpid, ?_⟩
  cases hp_ty : isPtrTy d.ty with
  | false =>
    simp only [hp_ty, Bool.false_eq_true, ↓reduceIte] at hA
    exact (List.getElem?_eq_some_iff.mp hA).1
  | true =>
    simp only [hp_ty, ↓reduceIte] at hA
    split at hA
    · obtain ⟨_, _, _, _, hAk⟩ := hA
      exact (List.getElem?_eq_some_iff.mp hAk).1
    · exact (List.getElem?_eq_some_iff.mp hA).1

theorem LocalsOk.store {body : CapturedMir} {ctx : Ctx} {locals : List LocalSlot}
    {lm : Map Gen.LocalName Ptr} {A : List Gen.Allocation} (hlo : LocalsOk body ctx locals lm A)
    (i : Nat) (d : LocalDecl) (hd : body.localDecls[i]? = some d) (slot slot' : LocalSlot)
    (hs : locals[i]? = some slot) (hlive' : slot' ≠ .dead)
    (hslot' : DeclSlotOk d slot' body.layouts)
    (p : Ptr) (hp : mapGet lm (localName i) = some p) (k : Nat)
    (hpk : p.provenance = some (⟨(k : Int)⟩, ()))
    (hnp : isPtrTy d.ty = false ∨ (∀ pv, slot' ≠ .init (.ptr pv 8))) :
    LocalsOk body ctx (locals.set i slot') lm
      (A.set k (stackAlloc p.addr (itOf d body.layouts) (declSlotData d slot' body.layouts))) :=
  hlo.store_decl i d hd slot slot' hs hlive' hslot' p hp k hpk hnp

/-- Writing an initialized thin raw pointer `.init (.ptr ptrVal 8)` backed by
`ptrBytes tAddr tProv` (`tAddr < 2 ^ 64`) into raw-pointer local `_i`, whose
allocation is `k`, keeps `LocalsOk`. -/
theorem LocalsOk.store_ptr {body : CapturedMir} {ctx : Ctx} {locals : List LocalSlot}
    {lm : Map Gen.LocalName Ptr} {A : List Gen.Allocation} (hlo : LocalsOk body ctx locals lm A)
    (i : Nat) (d : LocalDecl) (hd : body.localDecls[i]? = some d) (hp_ty : isPtrTy d.ty = true)
    (slot : LocalSlot) (hs : locals[i]? = some slot)
    (ptrVal : ProvenancePtr) (tAddr : Nat) (tProv : Option Prov) (htlt : tAddr < 2 ^ 64)
    (htgt : ∀ a pr, ctx.ptrTargets ptrVal.allocId = some (a, pr) → tAddr = a ∧ tProv = pr)
    (p : Ptr) (hp : mapGet lm (localName i) = some p) (k : Nat)
    (hpk : p.provenance = some (⟨(k : Int)⟩, ())) :
    LocalsOk body ctx (locals.set i (.init (.ptr ptrVal 8))) lm
      (A.set k (stackAlloc p.addr (itOf d body.layouts) (ptrBytes tAddr tProv))) := by
  have hil : i < locals.length := (List.getElem?_eq_some_iff.mp hs).1
  obtain ⟨id0, hpid0, hbase, haddr, haddrMax, hcls, hA0⟩ := hlo.storage i d slot p hd hs hp
  have hid0 : id0 = k := (prov_inj id0 k).mp (hpid0.symm.trans hpk)
  subst id0
  have hk : k < A.length := by
    simp only [hp_ty, ↓reduceIte] at hA0
    split at hA0
    · obtain ⟨_, _, _, _, hAk⟩ := hA0
      exact (List.getElem?_eq_some_iff.mp hAk).1
    · exact (List.getElem?_eq_some_iff.mp hA0).1
  have hslot' : DeclSlotOk d (.init (.ptr ptrVal 8)) body.layouts := by
    rw [DeclSlotOk_of_isPtrTy hp_ty]
    exact ⟨ptrVal, rfl⟩
  refine {
    nlocals := by simp [hlo.nlocals]
    slots := ?_
    base := ?_
    keysNodup := hlo.keysNodup
    keysLocal := hlo.keysLocal
    live := ?_
    storage := ?_
    inj := hlo.inj
    owned := ?_ }
  · intro j dj sj hdj hsj
    by_cases hij : i = j
    · subst hij
      rw [hd] at hdj; cases hdj
      rw [List.getElem?_set_self hil] at hsj; cases hsj
      exact hslot'
    · rw [List.getElem?_set_ne hij] at hsj
      exact hlo.slots j dj sj hdj hsj
  · obtain ⟨R, hR⟩ := hlo.base
    refine ⟨R.set (k - ctx.base.length)
        (stackAlloc p.addr (itOf d body.layouts) (ptrBytes tAddr tProv)), ?_⟩
    rw [hR, List.set_append_right _ _ hbase]
  · intro j sj hsj
    by_cases hij : i = j
    · subst hij
      rw [List.getElem?_set_self hil] at hsj; cases hsj
      simp [hp]
    · rw [List.getElem?_set_ne hij] at hsj
      exact hlo.live j sj hsj
  · intro j dj sj q hdj hsj hq
    by_cases hij : i = j
    · subst hij
      rw [hd] at hdj; cases hdj
      rw [hp] at hq; cases hq
      rw [List.getElem?_set_self hil] at hsj; cases hsj
      refine ⟨k, hpk, hbase, haddr, haddrMax, hcls, ?_⟩
      simp only [hp_ty, ↓reduceIte]
      exact ⟨tAddr, tProv, htlt, htgt, List.getElem?_set_self hk⟩
    · rw [List.getElem?_set_ne hij] at hsj
      refine (hlo.storage j dj sj q hdj hsj hq).congr_getElem? (fun id hqid => ?_)
      have hne : k ≠ id := fun hki => hij (hlo.inj i j p q hp hq (by subst hki; rw [hpk, hqid]))
      exact List.getElem?_set_ne hne
  · intro id a ha hlivea hb
    by_cases hki : k = id
    · subst hki
      exact ⟨i, p, hp, hpk⟩
    · rw [List.getElem?_set_ne hki] at ha
      exact hlo.owned id a ha hlivea hb

theorem FragTy.not_isPtrTy {d : LocalDecl} {layouts : Layout.LayoutTable}
    (h : FragTy (tyOf d layouts) (itOf d layouts)) : isPtrTy d.ty = false := by
  cases hp : isPtrTy d.ty
  · rfl
  · have hT := (tyOf_isPtrTy (layouts := layouts) hp).1
    rw [hT] at h
    rcases declPtrTy_cases d.ty with hraw | ⟨mutbl, it, _, href⟩
    · rw [hraw] at h; cases h
    · rw [href] at h; cases h

theorem FragTy.declSlotOk {d : LocalDecl} {layouts : Layout.LayoutTable}
    (h : FragTy (tyOf d layouts) (itOf d layouts)) (slot : LocalSlot) :
    DeclSlotOk d slot layouts ↔ SlotOk (tyOf d layouts) slot := by
  unfold DeclSlotOk
  split
  · rfl
  · cases slot <;> simp [h.not_array, h.not_tupleSpec, h.not_isPtrTy, SlotOk]

/-- `Machine::eval_statement` on an assignment to the live local `_i` whose
source evaluates to the value of a valid bit pattern `r` of `_i`'s type
(`place_store` stores at the local's declared type and ignores the type the
source reports). -/
theorem evalStatement_assign_of {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {locals : List LocalSlot} {lm : Map Gen.LocalName Ptr} {m : Mach} {blk stmt : Nat}
    (h : FrameOk body f ctx locals lm m blk stmt)
    (i : Nat) (d : LocalDecl) (hd : body.localDecls[i]? = some d)
    (hlive : locals[i]? ≠ some .dead) (e : Gen.ValueExpr)
    (r : Nat) (hr : ValidBits (tyOf d body.layouts) r) (T' : Gen.Type) (m1 : Mach)
    (hm1 : evalValue m e = .ok ((valOf (tyOf d body.layouts) r, T'), m1))
    (h1 : FrameOk body f ctx locals lm m1 blk stmt) :
    ∃ m', evalStatement m (.Assign (.Local (localName i)) e) = .ok m' ∧
      FrameOk body f ctx (locals.set i (.init (.scalar ⟨r, (itOf d body.layouts).size.bytes⟩)))
        lm m' blk stmt := by
  have hi : i < body.localDecls.length := (List.getElem?_eq_some_iff.mp hd).1
  have hT := (h.decl_localTy i d hd).of_validBits hr
  have hspec := h.hf.2 i d hd
  obtain ⟨_, slot, _, hs⟩ := h.slot_exists i hi
  have hslive : slot ≠ .dead := fun hc => hlive (hc ▸ hs)
  obtain ⟨p, hp⟩ := h.locs.some_of_live hs hslive
  obtain ⟨k, hpk, _⟩ := h1.locs.storage i d slot p hd hs hp
  obtain ⟨_, _, _, _, hA⟩ := h1.locs.storage_id hd hs hp hpk hT.not_isPtrTy
  have hplace := evalPlace_local_some h.shape i _ hspec.2 p hp
  rw [hT.declSlotData] at hA
  have hst := typedStore_ptr_frag h1.shape p k hpk hT _ r hr hA (slotData_length _ _)
  refine ⟨withMem m1 (m1.mem.memory.allocations.set k
      (stackAlloc p.addr (itOf d body.layouts) (scalarBytes (itOf d body.layouts) r)))
      ⟨.Store, .None, p.addr, (itOf d body.layouts).size⟩,
    by simp [evalStatement, hplace, hm1, placeStore, hst], ?_⟩
  refine FrameOk.mk' h.hf (withMem_shape h1.shape _) ?_ h.declsOk (h1.nonScalar.set_init i _)
  have hslot' : DeclSlotOk d (.init (.scalar ⟨r, (itOf d body.layouts).size.bytes⟩)) body.layouts :=
    (hT.declSlotOk _).mpr ⟨hT.tyBytes.symm, hr⟩
  have hlo' := h1.locs.store i d hd slot
    (.init (.scalar ⟨r, (itOf d body.layouts).size.bytes⟩)) hs (by simp) hslot' p hp k hpk
    (.inl hT.not_isPtrTy)
  rw [hT.declSlotData] at hlo'
  exact hlo'

/-- `Machine::eval_statement` on an assignment to a dead local that
`minimize`'s init block does not allocate: `eval_place` of the destination,
which MiniRust evaluates first, is UB. -/
theorem evalStatement_assign_dead {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {locals : List LocalSlot} {lm : Map Gen.LocalName Ptr} {m : Mach} {blk stmt : Nat}
    (h : FrameOk body f ctx locals lm m blk stmt) (i : Nat) (d : LocalDecl)
    (hd : body.localDecls[i]? = some d) (hs : locals[i]? = some .dead)
    (hal : i ∉ alwaysStorageLiveLocals body) (e : Gen.ValueExpr) :
    ∃ msg, evalStatement m (.Assign (.Local (localName i)) e) = .error (.ub msg) := by
  have hspec := h.hf.2 i d hd
  have hp := h.locs.none_of_dead hs hal
  exact ⟨"access to a dead local", by simp [evalStatement, evalPlace_local_none h.shape i _ hspec.2 hp]⟩

/-- `Machine::eval_statement` on a translated fragment assignment to a live
integer local. -/
theorem evalStatement_assign {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {locals : List LocalSlot} {lm : Map Gen.LocalName Ptr} {m : Mach} {blk stmt : Nat}
    {targetTy : Option MirAst.Ty}
    (h : FrameOk body f ctx locals lm m blk stmt)
    (i : Nat) (d : LocalDecl) (hd : body.localDecls[i]? = some d)
    (hlive : locals[i]? ≠ some .dead)
    (hint : intTypeOf d.ty = some (itOf d body.layouts)) (rv : Rvalue)
    (hok : rvalueOk body.layouts body.localDecls (itOf d body.layouts) rv = true)
    (e : Gen.ValueExpr)
    (he : translateRvalue body.layouts body.localDecls targetTy rv = some e) :
    (∀ r, rvBits body.localDecls locals (itOf d body.layouts) body.layouts rv = some r →
      ∃ m', evalStatement m (.Assign (.Local (localName i)) e) = .ok m' ∧
        FrameOk body f ctx (locals.set i (.init (.scalar ⟨r, (itOf d body.layouts).size.bytes⟩)))
          lm m' blk stmt) ∧
    (rvBits body.localDecls locals (itOf d body.layouts) body.layouts rv = none →
      ∃ msg, evalStatement m (.Assign (.Local (localName i)) e) = .error (.ub msg)) := by
  have hi : i < body.localDecls.length := (List.getElem?_eq_some_iff.mp hd).1
  have hgood : GoodSize (itOf d body.layouts).size.bytes := intTypeOf_good hint
  have htyd : tyOf d body.layouts = .Int (itOf d body.layouts) :=
    (tyOf_int (layouts := body.layouts) hint).1
  have hspec := h.hf.2 i d hd
  obtain ⟨_, slot, _, hs⟩ := h.slot_exists i hi
  obtain ⟨p, hp⟩ := h.locs.some_of_live hs (fun hc => hlive (hc ▸ hs))
  have hplace := evalPlace_local_some h.shape i _ hspec.2 p hp
  obtain ⟨hrok, hrnone⟩ := evalValue_rvalue h (itOf d body.layouts) hgood rv hok e he
  refine ⟨fun r hr => ?_, fun hnone => ?_⟩
  · obtain ⟨hrlt, m1, hm1, h1⟩ := hrok r hr
    exact evalStatement_assign_of h i d hd hlive e r (by rw [htyd]; exact hrlt) _ m1
      (by rw [htyd]; exact hm1) h1
  · obtain ⟨msg, hmsg⟩ := hrnone hnone
    exact ⟨msg, by simp [evalStatement, hplace, hmsg]⟩

/-- `Machine::eval_statement` on a translated fragment array assignment. -/
theorem evalStatement_assign_array {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {locals : List LocalSlot} {lm : Map Gen.LocalName Ptr} {m : Mach} {blk stmt : Nat}
    {targetTy : Option MirAst.Ty}
    (h : FrameOk body f ctx locals lm m blk stmt)
    (i : Nat) (d : LocalDecl) (hd : body.localDecls[i]? = some d)
    (elemIt : Gen.IntType) (count : Nat) (ha : arrayTypeOf d.ty = some (elemIt, count))
    (rv : Rvalue) (hok : arrayRvalueOk body.layouts body.localDecls elemIt count rv = true)
    (e : Gen.ValueExpr)
    (he : translateRvalue body.layouts body.localDecls targetTy rv = some e) :
    (∀ elems, arrayRvElems locals elemIt rv = some elems →
      ∃ m', evalStatement m (.Assign (.Local (localName i)) e) = .ok m' ∧
        FrameOk body f ctx (locals.set i (.init (.aggregate 0 elems))) lm m' blk stmt) ∧
    (arrayRvElems locals elemIt rv = none →
      ∃ msg, evalStatement m (.Assign (.Local (localName i)) e) = .error (.ub msg)) := by
  have hi : i < body.localDecls.length := (List.getElem?_eq_some_iff.mp hd).1
  have hgood := arrayTypeOf_good ha
  obtain ⟨hTd, hitd⟩ := tyOf_array (layouts := body.layouts) ha
  have hloc := (h.hf.2 i d hd).2
  rw [hTd] at hloc
  obtain ⟨_, slot, _, hs⟩ := h.slot_exists i hi
  obtain ⟨⟨v0, rfl⟩, _⟩ := h.nonScalar i d slot hd hs (scalarTypeOf_none_of_arrayTypeOf ha)
    (isPtrTy_false_of_arrayTypeOf ha)
  obtain ⟨p, hp⟩ := h.locs.some_of_live hs (by simp)
  have hplace := evalPlace_local_some h.shape i _ hloc p hp
  obtain ⟨hrok, hrnone⟩ := evalValue_arrayRvalue h elemIt count hgood rv hok e he
  have hdlen : (declSlotData d (.init v0) body.layouts).length = count * elemIt.size.bytes := by
    have hlen' := declSlotData_length_of_declOk (h.declsOk d (List.mem_of_getElem? hd))
      (h.slots i d (.init v0) hd hs)
    rw [hTd] at hlen'
    simpa [tyBytes] using hlen'
  refine ⟨fun elems hr => ?_, fun hnone => ?_⟩
  · obtain ⟨hlen, helemOk, m1, hm1, h1⟩ := hrok elems hr
    obtain ⟨k, hpk, _, _, _, _, hA1⟩ :=
      h1.locs.storage_nonptr i d (.init v0) p hd hs hp (isPtrTy_false_of_arrayTypeOf ha)
    rw [hitd] at hA1
    have hst := typedStore_ptr_array h1.shape p k hpk elemIt count
      (declSlotData d (.init v0) body.layouts) elems hgood hA1 hdlen hlen helemOk
    refine ⟨withMem m1 (m1.mem.memory.allocations.set k
        (stackAlloc p.addr elemIt ((elems.map (valBytes elemIt)).flatten)))
        ⟨.Store, .None, p.addr, ⟨count * elemIt.size.bytes⟩⟩,
      by simp [evalStatement, hplace, hm1, placeStore, hst], ?_⟩
    refine FrameOk.mk' h.hf (withMem_shape h1.shape _) ?_ h.declsOk (h1.nonScalar.set_init i _)
    have hslot' : DeclSlotOk d (.init (.aggregate 0 elems)) body.layouts :=
      (DeclSlotOk_of_arrayTypeOf ha _).mpr ⟨hlen, helemOk⟩
    have hlo' := h1.locs.store i d hd (.init v0) (.init (.aggregate 0 elems)) hs (by simp)
      hslot' p hp k hpk (.inl (isPtrTy_false_of_arrayTypeOf ha))
    rw [hitd, declSlotData_of_array ha] at hlo'
    exact hlo'
  · obtain ⟨msg, hmsg⟩ := hrnone hnone
    exact ⟨msg, by simp [evalStatement, hplace, hmsg]⟩

/-- `Machine::eval_statement` on a translated fragment indexed array assignment `arr[proj] = rv`. -/
theorem evalStatement_assign_index {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {locals : List LocalSlot} {lm : Map Gen.LocalName Ptr} {m : Mach} {blk stmt : Nat}
    {targetTy : Option MirAst.Ty}
    (h : FrameOk body f ctx locals lm m blk stmt)
    (i : Nat) (d : LocalDecl) (hd : body.localDecls[i]? = some d)
    (elemIt : Gen.IntType) (count : Nat) (ha : arrayTypeOf d.ty = some (elemIt, count))
    (proj : ProjectionElem) (hproj : projOk body.localDecls count proj = true)
    (pe : Gen.PlaceExpr) (hpe : translatePlace body.localDecls ⟨i, [proj]⟩ = some pe)
    (rv : Rvalue) (hok : rvalueOk body.layouts body.localDecls elemIt rv = true)
    (e : Gen.ValueExpr)
    (he : translateRvalue body.layouts body.localDecls targetTy rv = some e)
    (elems : List Value) (hs : locals[i]? = some (.init (.aggregate 0 elems))) :
    (∀ idx r, projIdx locals count proj = some idx →
      rvBits body.localDecls locals elemIt body.layouts rv = some r →
      ∃ m', evalStatement m (.Assign pe e) = .ok m' ∧
        FrameOk body f ctx
          (locals.set i (.init (.aggregate 0 (elems.set idx (.scalar ⟨r, elemIt.size.bytes⟩)))))
          lm m' blk stmt) ∧
    (projIdx locals count proj = none ∨
      rvBits body.localDecls locals elemIt body.layouts rv = none →
      ∃ msg, evalStatement m (.Assign pe e) = .error (.ub msg)) := by
  have hi : i < body.localDecls.length := (List.getElem?_eq_some_iff.mp hd).1
  have hgood := arrayTypeOf_good ha
  obtain ⟨_, hitd⟩ := tyOf_array (layouts := body.layouts) ha
  obtain ⟨p, hp⟩ := h.locs.some_of_live hs (by simp)
  obtain ⟨hpok, hpnone⟩ := evalPlace_proj h i d hd elemIt count ha p hp proj hproj pe hpe
  obtain ⟨hlen, helemOk⟩ := (DeclSlotOk_of_arrayTypeOf ha _).mp (h.slots i d _ hd hs)
  refine ⟨fun idx r hidx hr => ?_, fun hnone => ?_⟩
  · obtain ⟨hidx_lt, m1, hm1, h1⟩ := hpok idx hidx
    obtain ⟨hrok, _⟩ := evalValue_rvalue h1 elemIt hgood rv hok e he
    obtain ⟨hrlt, m2, hm2, h2⟩ := hrok r hr
    obtain ⟨k, hpk, _, _, _, _, hA2⟩ :=
      h2.locs.storage_nonptr i d (.init (.aggregate 0 elems)) p hd hs hp
        (isPtrTy_false_of_arrayTypeOf ha)
    rw [hitd, declSlotData_of_array ha] at hA2
    have hst := typedStore_ptr_array_elem h2.shape p k hpk idx elemIt count elems r
      hgood hlen hidx_lt hrlt hA2
    refine ⟨withMem m2 (m2.mem.memory.allocations.set k
        (stackAlloc p.addr elemIt
          (((elems.set idx (.scalar ⟨r, elemIt.size.bytes⟩)).map (valBytes elemIt)).flatten)))
        ⟨.Store, .None, (offsetPtr p (idx * elemIt.size.bytes)).addr, elemIt.size⟩,
      by simp [evalStatement, hm1, hm2, placeStore, hst], ?_⟩
    refine FrameOk.mk' h.hf (withMem_shape h2.shape _) ?_ h.declsOk (h2.nonScalar.set_init i _)
    have helemOk' : ∀ v ∈ elems.set idx (.scalar ⟨r, elemIt.size.bytes⟩), ElemOk elemIt v := by
      intro v hv
      rcases List.mem_or_eq_of_mem_set hv with hv' | rfl
      · exact helemOk v hv'
      · exact ⟨rfl, hrlt⟩
    have hslot' : DeclSlotOk d
        (.init (.aggregate 0 (elems.set idx (.scalar ⟨r, elemIt.size.bytes⟩)))) body.layouts :=
      (DeclSlotOk_of_arrayTypeOf ha _).mpr ⟨by simp [hlen], helemOk'⟩
    have hlo' := h2.locs.store i d hd (.init (.aggregate 0 elems))
      (.init (.aggregate 0 (elems.set idx (.scalar ⟨r, elemIt.size.bytes⟩)))) hs (by simp)
      hslot' p hp k hpk (.inl (isPtrTy_false_of_arrayTypeOf ha))
    rw [hitd, declSlotData_of_array ha] at hlo'
    exact hlo'
  · cases hidx : projIdx locals count proj with
    | none =>
      obtain ⟨msg, hmsg⟩ := hpnone hidx
      exact ⟨msg, by simp [evalStatement, hmsg]⟩
    | some idx =>
      rcases hnone with hidxNone | hrNone
      · rw [hidx] at hidxNone; cases hidxNone
      · obtain ⟨_, m1, hm1, h1⟩ := hpok idx hidx
        obtain ⟨_, hrnone⟩ := evalValue_rvalue h1 elemIt hgood rv hok e he
        obtain ⟨msg, hmsg⟩ := hrnone hrNone
        exact ⟨msg, by simp [evalStatement, hm1, hmsg]⟩

/-- `Machine::eval_statement` on a translated fragment tuple/struct assignment
(either whole-local `_i = rv` or nested tuple/struct field `_i.f1...fk = rv`). -/
theorem evalStatement_assign_tuple {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {locals : List LocalSlot} {lm : Map Gen.LocalName Ptr} {m : Mach} {blk stmt : Nat}
    (h : FrameOk body f ctx locals lm m blk stmt)
    (dst : MirAst.Place) (dstTy : MirAst.Ty)
    (fields : List (Nat × TupleSpec)) (size align : Nat)
    (htp : tuplePlaceSpec body.layouts body.localDecls dst = some (fields, size, align))
    (pe : Gen.PlaceExpr) (hpe : translatePlace body.localDecls dst = some pe)
    (rv : Rvalue) (hok : tupleRvalueOk body.layouts body.localDecls dstTy fields size align rv = true)
    (e : Gen.ValueExpr) (he : translateRvalue body.layouts body.localDecls (some dstTy) rv = some e)
    (rootVal : Value) (hs : locals[dst.local_]? = some (.init rootVal)) :
    (∀ newVal, tupleRvVal locals fields rv = some newVal →
      ∃ newRootVal m',
        writeFieldPath rootVal dst.projection newVal = some newRootVal ∧
        (∀ locals', MirSemantics.writeProjectedValue locals' rootVal dst.projection newVal = .ok newRootVal) ∧
        evalStatement m (.Assign pe e) = .ok m' ∧
        FrameOk body f ctx (locals.set dst.local_ (.init newRootVal)) lm m' blk stmt) ∧
    (tupleRvVal locals fields rv = none →
      ∃ msg, evalStatement m (.Assign pe e) = .error (.ub msg)) := by
  obtain ⟨d, rootFields, rootSize, rootAlign, rootVal', relOff, ptr,
    hj, hd, ht, hs', hptr, hrootWf, hrootVal, hres, hleafWf, hrelBound, hpeEval⟩ :=
    evalPlace_tuplePlace h dst fields size align htp pe hpe
  rw [hs] at hs'; cases hs'
  obtain ⟨hrok, hrnone⟩ := evalValue_tupleRvalue h dstTy fields size align rv hok e he
  have hdlen : ((TupleSpec.tuple rootFields rootSize rootAlign).encodeVal rootVal).length = rootSize :=
    TupleSpec.encodeVal_length (.tuple rootFields rootSize rootAlign) rootVal hrootWf
  refine ⟨fun newVal hr => ?_, fun hnone => ?_⟩
  · obtain ⟨hnewValOk, m1, hm1, h1⟩ := hrok newVal hr
    obtain ⟨newRootVal, hwpath, hnewRootOk, hnewEnc, hwsem⟩ :=
      resolveFieldPath_write hrootWf hrootVal hres hnewValOk
    obtain ⟨k, hpk, _, _, _, _, hA1⟩ :=
      h1.locs.storage_nonptr dst.local_ d (.init rootVal) ptr hd hs hptr
        (isPtrTy_false_of_tupleTypeOf ht)
    rw [declSlotData_of_tupleSpec ht] at hA1
    have hst := typedStore_ptr_tuple_slice h1.shape ptr k hpk (itOf d body.layouts)
      ((TupleSpec.tuple rootFields rootSize rootAlign).encodeVal rootVal) hA1
      relOff (.tuple fields size align) newVal hleafWf hnewValOk
      (by rw [hdlen]; exact hrelBound)
    rw [← hnewEnc] at hst
    refine ⟨newRootVal, withMem m1 (m1.mem.memory.allocations.set k
        (stackAlloc ptr.addr (itOf d body.layouts)
          ((TupleSpec.tuple rootFields rootSize rootAlign).encodeVal newRootVal)))
        ⟨.Store, .None, (offsetPtr ptr relOff).addr, ⟨size⟩⟩, hwpath, hwsem,
      by simp [evalStatement, hpeEval, hm1, placeStore, TupleSpec.size] at hst ⊢; exact hst, ?_⟩
    refine FrameOk.mk' h.hf (withMem_shape h1.shape _) ?_ h.declsOk (h1.nonScalar.set_init dst.local_ _)
    have hslot' : DeclSlotOk d (.init newRootVal) body.layouts :=
      (DeclSlotOk_of_tupleTypeOf ht _).mpr ⟨hrootWf, hnewRootOk⟩
    have hlo' := h1.locs.store dst.local_ d hd (.init rootVal) (.init newRootVal) hs (by simp)
      hslot' ptr hptr k hpk (.inl (isPtrTy_false_of_tupleTypeOf ht))
    rw [declSlotData_of_tupleSpec ht] at hlo'
    exact hlo'
  · obtain ⟨msg, hmsg⟩ := hrnone hnone
    exact ⟨msg, by simp [evalStatement, hpeEval, hmsg]⟩

/-- `Machine::eval_statement` on a translated fragment scalar field assignment `_i.f1...fk = rv`. -/
theorem evalStatement_assign_field_scalar {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {locals : List LocalSlot} {lm : Map Gen.LocalName Ptr} {m : Mach} {blk stmt : Nat}
    {targetTy : Option MirAst.Ty}
    (h : FrameOk body f ctx locals lm m blk stmt)
    (i idx : Nat) (fieldTy : MirAst.Ty) (rest : List ProjectionElem)
    (htupSome : (body.localDecls[i]? >>= (tupleTypeOf body.layouts ·.ty)).isSome = true)
    (it : Gen.IntType)
    (hpok : placeOk body.layouts body.localDecls it ⟨i, .field idx fieldTy :: rest⟩ = true)
    (pe : Gen.PlaceExpr) (hpe : translatePlace body.localDecls ⟨i, .field idx fieldTy :: rest⟩ = some pe)
    (rv : Rvalue) (hok : rvalueOk body.layouts body.localDecls it rv = true)
    (e : Gen.ValueExpr)
    (he : translateRvalue body.layouts body.localDecls targetTy rv = some e)
    (rootVal : Value) (hs : locals[i]? = some (.init rootVal)) :
    (∀ r, rvBits body.localDecls locals it body.layouts rv = some r →
      ∃ newRootVal m',
        writeFieldPath rootVal (.field idx fieldTy :: rest) (.scalar ⟨r, it.size.bytes⟩) = some newRootVal ∧
        (∀ locals', MirSemantics.writeProjectedValue locals' rootVal (.field idx fieldTy :: rest)
          (.scalar ⟨r, it.size.bytes⟩) = .ok newRootVal) ∧
        evalStatement m (.Assign pe e) = .ok m' ∧
        FrameOk body f ctx (locals.set i (.init newRootVal)) lm m' blk stmt) ∧
    (rvBits body.localDecls locals it body.layouts rv = none →
      ∃ msg, evalStatement m (.Assign pe e) = .error (.ub msg)) := by
  simp only [placeOk, Bool.and_eq_true, decide_eq_true_eq] at hpok
  obtain ⟨hi, hpok⟩ := hpok
  cases hd : body.localDecls[i]? with
  | none => simp [hd] at htupSome
  | some d =>
    simp only [hd, Option.bind_eq_bind, Option.bind_some] at htupSome
    obtain ⟨⟨rootFields, rootSize, rootAlign⟩, ht⟩ := Option.isSome_iff_exists.mp htupSome
    have hnoIB := (not_scalar_of_tupleTypeOf ht).2.2.1
    simp only [hd, hnoIB, ht] at hpok
    cases hres : resolveFieldPath body.layouts (.tuple rootFields rootSize rootAlign)
        (.field idx fieldTy :: rest) with
    | none => simp [hres] at hpok
    | some lpair =>
      obtain ⟨relOff, leafSpec⟩ := lpair
      simp only [hres] at hpok
      cases leafSpec with
      | tuple _ _ _ => simp at hpok
      | scalar leafIt =>
        simp only [decide_eq_true_eq] at hpok
        subst hpok
        simp only [translatePlace] at hpe
        obtain ⟨hrootWf, hrootVal⟩ :=
          (DeclSlotOk_of_tupleTypeOf ht _).mp (h.slots i d (.init rootVal) hd hs)
        obtain ⟨hleafWf, hrelBound⟩ := resolveFieldPath_wf hrootWf hres
        have hgood : GoodSize leafIt.size.bytes := by
          simp only [TupleSpec.wf] at hleafWf
          exact (goodAlignBytes_iff leafIt.size.bytes).mp hleafWf
        obtain ⟨hTd, _⟩ := tyOf_tupleSpec ht
        have hloc := (h.hf.2 i d hd).2
        rw [hTd] at hloc
        obtain ⟨ptr, hptr⟩ := h.locs.some_of_live hs (by simp)
        obtain ⟨k, hpk, _, haddr, haddrMax, _, hA⟩ :=
          h.locs.storage_nonptr i d (.init rootVal) ptr hd hs hptr
            (isPtrTy_false_of_tupleTypeOf ht)
        rw [declSlotData_of_tupleSpec ht] at hA
        have hplaceBase := evalPlace_local_some h.shape i _ hloc ptr hptr
        have hdlen : ((TupleSpec.tuple rootFields rootSize rootAlign).encodeVal rootVal).length = rootSize :=
          TupleSpec.encodeVal_length (.tuple rootFields rootSize rootAlign) rootVal hrootWf
        have hbound : rootSize < 2 ^ 63 := by
          simp only [TupleSpec.wf, Bool.and_eq_true, decide_eq_true_eq] at hrootWf
          exact hrootWf.1.2
        rw [hTd] at haddrMax
        simp only [TupleSpec.toMiniRustTy, tyBytes] at haddrMax
        have hrootEval : evalPlace m (.Local (localName i)) =
            .ok (({ ptr := { thin_pointer := offsetPtr ptr 0, metadata := none },
                     aligned := true },
                   (TupleSpec.tuple rootFields rootSize rootAlign).toMiniRustTy), m) := by
          simpa using hplaceBase
        have hpeEval := evalPlace_ptr_fieldPath h.shape ptr k hpk (itOf d body.layouts)
          ((TupleSpec.tuple rootFields rootSize rootAlign).encodeVal rootVal) hA
          (by rw [hdlen]; exact hbound) haddr.nonneg (by rw [hdlen]; exact haddrMax)
          (.Local (localName i)) 0 (.tuple rootFields rootSize rootAlign) hrootEval hrootWf
          (by simp [TupleSpec.size, hdlen]) (.field idx fieldTy :: rest) pe hpe
          relOff (.scalar leafIt) hres
        simp only [Nat.zero_add] at hpeEval
        obtain ⟨hrok, hrnone⟩ := evalValue_rvalue h leafIt hgood rv hok e he
        refine ⟨fun r hr => ?_, fun hnone => ?_⟩
        · obtain ⟨hrlt, m1, hm1, h1⟩ := hrok r hr
          have hnewValOk : (TupleSpec.scalar leafIt).valOk (.scalar ⟨r, leafIt.size.bytes⟩) = true := by
            simp [TupleSpec.valOk, hrlt]
          obtain ⟨newRootVal, hwpath, hnewRootOk, hnewEnc, hwsem⟩ :=
            resolveFieldPath_write hrootWf hrootVal hres hnewValOk
          obtain ⟨k1, hpk1, _, _, _, _, hA1⟩ :=
            h1.locs.storage_nonptr i d (.init rootVal) ptr hd hs hptr
              (isPtrTy_false_of_tupleTypeOf ht)
          have hkEq : k1 = k := (prov_inj k1 k).mp (hpk1.symm.trans hpk)
          subst hkEq
          rw [declSlotData_of_tupleSpec ht] at hA1
          have hst := typedStore_ptr_tuple_slice h1.shape ptr k1 hpk1 (itOf d body.layouts)
            ((TupleSpec.tuple rootFields rootSize rootAlign).encodeVal rootVal) hA1
            relOff (.scalar leafIt) (.scalar ⟨r, leafIt.size.bytes⟩) hleafWf hnewValOk
            (by rw [hdlen]; exact hrelBound)
          rw [← hnewEnc] at hst
          refine ⟨newRootVal, withMem m1 (m1.mem.memory.allocations.set k1
              (stackAlloc ptr.addr (itOf d body.layouts)
                ((TupleSpec.tuple rootFields rootSize rootAlign).encodeVal newRootVal)))
              ⟨.Store, .None, (offsetPtr ptr relOff).addr, leafIt.size⟩, hwpath, hwsem,
            by simp only [TupleSpec.toMiniRustVal, TupleSpec.toMiniRustTy, TupleSpec.size] at hst hpeEval
               simp [evalStatement, hpeEval, hm1, placeStore, hst], ?_⟩
          refine FrameOk.mk' h.hf (withMem_shape h1.shape _) ?_ h.declsOk (h1.nonScalar.set_init i _)
          have hslot' : DeclSlotOk d (.init newRootVal) body.layouts :=
            (DeclSlotOk_of_tupleTypeOf ht _).mpr ⟨hrootWf, hnewRootOk⟩
          have hlo' := h1.locs.store i d hd (.init rootVal) (.init newRootVal) hs (by simp)
            hslot' ptr hptr k1 hpk1 (.inl (isPtrTy_false_of_tupleTypeOf ht))
          rw [declSlotData_of_tupleSpec ht] at hlo'
          exact hlo'
        · obtain ⟨msg, hmsg⟩ := hrnone hnone
          exact ⟨msg, by simp [evalStatement, hpeEval, hmsg]⟩

/-- `Machine::eval_statement` on a translated fragment `PlaceMention` (covering
unprojected locals `_i`, field projections `_i.0` and `_i.1` on an `(Int, bool)`
2-tuple local, and valid field projection chains `_i.f1...fk` on a `TupleSpec`
local): it succeeds on a live local and is UB on a dead local that `minimize`'s
init block does not allocate. -/
theorem evalStatement_placeMention_place {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {locals : List LocalSlot} {lm : Map Gen.LocalName Ptr} {m : Mach} {blk stmt : Nat}
    (h : FrameOk body f ctx locals lm m blk stmt)
    (p : Place) (hp : mentionPlaceOk body.layouts body.localDecls p = true) (pe : Gen.PlaceExpr)
    (hpe : translatePlace body.localDecls p = some pe) :
    mentionPlaceOk body.layouts body.localDecls p = true ∧
    (locals[p.local_]? ≠ some .dead → evalStatement m (.PlaceMention pe) = .ok m) ∧
    (locals[p.local_]? = some .dead → p.local_ ∉ alwaysStorageLiveLocals body →
      ∃ msg, evalStatement m (.PlaceMention pe) = .error (.ub msg)) := by
  have hp0 := hp
  match p, hp, hpe with
  | ⟨i, []⟩, hp, hpe =>
    simp only [mentionPlaceOk, decide_eq_true_eq] at hp
    simp only [translatePlace, Option.some.injEq] at hpe
    subst hpe
    obtain ⟨d, slot, hd, hs⟩ := h.slot_exists i hp
    have hspec := h.hf.2 i d hd
    refine ⟨hp0, fun hlive => ?_, fun hdead hal => ?_⟩
    · obtain ⟨q, hq⟩ := h.locs.some_of_live hs (fun hc => hlive (hc ▸ hs))
      simp [evalStatement, evalPlace_local_some h.shape i _ hspec.2 q hq]
    · have hq := h.locs.none_of_dead hdead hal
      exact ⟨"access to a dead local",
        by simp [evalStatement, evalPlace_local_none h.shape i _ hspec.2 hq]⟩
  | ⟨i, .field idx fieldTy :: rest⟩, hp, hpe =>
    simp only [mentionPlaceOk, Bool.and_eq_true, decide_eq_true_eq] at hp
    obtain ⟨hi, ht⟩ := hp
    obtain ⟨d, slot, hd, hs⟩ := h.slot_exists i hi
    simp only [hd] at ht
    cases htup : intBoolTupleOf d.ty with
    | some it =>
      simp only [htup] at ht
      match idx, rest, ht, hpe with
      | 0, [], ht, hpe =>
        simp only [decide_eq_true_eq] at ht
        simp only [translatePlace, translateFieldPlace, Option.some.injEq] at hpe
        subst hpe
        obtain ⟨hTd, hitd⟩ := tyOf_tuple (layouts := body.layouts) htup
        have hloc := (h.hf.2 i d hd).2
        rw [hTd] at hloc
        refine ⟨hp0, fun hlive => ?_, fun hdead hal => ?_⟩
        · obtain ⟨q, hq⟩ := h.locs.some_of_live hs (fun hc => hlive (hc ▸ hs))
          obtain ⟨k, hqk, _⟩ := h.locs.storage i d slot q hd hs hq
          obtain ⟨_, haddr, _, _, _⟩ :=
            h.locs.storage_id hd hs hq hqk (isPtrTy_false_of_scalarTypeOf (scalarTypeOf_tuple htup))
          rw [hitd] at haddr
          have hplace := evalPlace_field0L h.shape i it (intBoolTupleOf_good htup) hloc q hq haddr
          simp [evalStatement, hplace]
        · have hq := h.locs.none_of_dead hdead hal
          exact ⟨"access to a dead local",
            by simp [evalStatement, evalPlace_field_none h.shape i _ hloc hq]⟩
      | 1, [], ht, hpe =>
        simp only [translatePlace, translateFieldPlace, Option.some.injEq] at hpe
        subst hpe
        obtain ⟨hTd, hitd⟩ := tyOf_tuple (layouts := body.layouts) htup
        have hgood := intBoolTupleOf_good htup
        have hloc := (h.hf.2 i d hd).2
        rw [hTd] at hloc
        refine ⟨hp0, fun hlive => ?_, fun hdead hal => ?_⟩
        · obtain ⟨q, hq⟩ := h.locs.some_of_live hs (fun hc => hlive (hc ▸ hs))
          obtain ⟨k, hqk, _⟩ := h.locs.storage i d slot q hd hs hq
          obtain ⟨_, haddr, _, _, hA⟩ :=
            h.locs.storage_id hd hs hq hqk (isPtrTy_false_of_scalarTypeOf (scalarTypeOf_tuple htup))
          rw [declSlotData_of_some htup, hitd] at hA
          rw [hitd] at haddr
          have hlen := tupleSlotData_length it slot hgood.pos
          have hplace := evalPlace_field1L h.shape i it hgood hloc q hq k hqk _ hA hlen haddr
          simp [evalStatement, hplace]
        · have hq := h.locs.none_of_dead hdead hal
          exact ⟨"access to a dead local",
            by simp [evalStatement, evalPlace_field_none h.shape i _ hloc hq]⟩
    | none =>
      simp only [htup] at ht
      cases htspec : tupleTypeOf body.layouts d.ty with
      | none => simp [htspec] at ht
      | some rpair =>
        obtain ⟨fields, size, align⟩ := rpair
        simp only [htspec] at ht
        obtain ⟨⟨relOff, leafSpec⟩, hres⟩ := Option.isSome_iff_exists.mp ht
        simp only [translatePlace] at hpe
        obtain ⟨⟨rootVal, rfl⟩, _⟩ :=
          h.nonScalar i d slot hd hs (scalarTypeOf_none_of_tupleTypeOf htspec)
            (isPtrTy_false_of_tupleTypeOf htspec)
        obtain ⟨hrootWf, _⟩ :=
          (DeclSlotOk_of_tupleTypeOf htspec (.init rootVal)).mp
            (h.slots i d (.init rootVal) hd hs)
        refine ⟨hp0, fun _ => ?_, fun hdead _ => by rw [hs] at hdead; cases hdead⟩
        obtain ⟨q, hq⟩ := h.locs.some_of_live hs (by simp)
        obtain ⟨k, hqk, _, haddr, haddrMax, _, hA⟩ :=
          h.locs.storage_nonptr i d (.init rootVal) q hd hs hq
            (isPtrTy_false_of_tupleTypeOf htspec)
        obtain ⟨hTd, _⟩ := tyOf_tupleSpec htspec
        rw [declSlotData_of_tupleSpec htspec] at hA
        have hloc := (h.hf.2 i d hd).2
        rw [hTd] at hloc
        have hplaceBase := evalPlace_local_some h.shape i _ hloc q hq
        have hdlen : ((TupleSpec.tuple fields size align).encodeVal rootVal).length = size :=
          TupleSpec.encodeVal_length (.tuple fields size align) rootVal hrootWf
        have hbound : size < 2 ^ 63 := by
          simp only [TupleSpec.wf, Bool.and_eq_true, decide_eq_true_eq] at hrootWf
          exact hrootWf.1.2
        rw [hTd] at haddrMax
        simp only [TupleSpec.toMiniRustTy, tyBytes] at haddrMax
        have hrootEval : evalPlace m (.Local (localName i)) =
            .ok (({ ptr := { thin_pointer := offsetPtr q 0, metadata := none },
                     aligned := true },
                   (TupleSpec.tuple fields size align).toMiniRustTy), m) := by
          simpa using hplaceBase
        have hpeEval := evalPlace_ptr_fieldPath h.shape q k hqk (itOf d body.layouts)
          ((TupleSpec.tuple fields size align).encodeVal rootVal) hA
          (by rw [hdlen]; exact hbound) haddr.nonneg (by rw [hdlen]; exact haddrMax)
          (.Local (localName i)) 0 (.tuple fields size align) hrootEval hrootWf
          (by simp [TupleSpec.size, hdlen]) (.field idx fieldTy :: rest) pe hpe
          relOff leafSpec hres
        simp [evalStatement, hpeEval]

/-! ## `bool` rvalues -/

/-- The outcome MiniRust's `BinOp::Rel` computes for two fragment values of
type `T`, given by their bit patterns: integers compare as mathematical
integers (`intCmp` of the decoded values) and `bool`s with `false < true`. -/
def cmpOf : Gen.Type → Nat → Nat → Ordering
  | .Int it, x, y => intCmp (intFromBits x it) (intFromBits y it)
  | .Bool, x, y => boolCmp (decide (x = 1)) (decide (y = 1))
  | _, _, _ => .eq

/-- The `bool` that `eval_rel_op` returns for a relational operator other than
`Cmp`. -/
def relBool : Gen.RelOp → Ordering → Bool
  | .Lt, o => o.isLT
  | .Gt, o => o.isGT
  | .Le, o => o.isLE
  | .Ge, o => o.isGE
  | .Eq, o => o.isEq
  | .Ne, o => o.isNe
  | .Cmp, _ => false

theorem translateRelOp_ne_cmp {op : MirAst.BinOp} {rel : Gen.RelOp}
    (h : translateRelOp op = some rel) : rel ≠ .Cmp := by
  cases op <;> simp [translateRelOp] at h <;> subst h <;> simp

theorem evalRelOp_bool (rel : Gen.RelOp) (hrel : rel ≠ .Cmp) (o : Ordering) :
    evalRelOp rel o = (.Bool (relBool rel o), .Bool) := by
  cases rel <;> simp_all [evalRelOp, relBool]

/-- `BinOp::Rel` on two fragment values of the same fragment type. -/
theorem evalBinOp_rel_frag {T : Gen.Type} {it : Gen.IntType} (hT : RelTy T it) (rel : Gen.RelOp)
    (hrel : rel ≠ .Cmp) (x y : Nat) :
    evalBinOp (.Rel rel) (valOf T x, T) (valOf T y, T) =
      .ok (.Bool (relBool rel (cmpOf T x y)), .Bool) := by
  cases hT <;> simp [evalBinOp, valOf, cmpOf, evalRelOp_bool rel hrel]

/-- `build::not` negates a `bool`: both of its transmutes succeed because
`1 - 0` and `1 - 1` are valid `bool` bytes. -/
theorem evalValue_boolNot (m m1 : Mach) (e : Gen.ValueExpr) (b : Bool)
    (he : evalValue m e = .ok ((.Bool b, .Bool), m1)) :
    evalValue m (boolNot e) = .ok ((.Bool (!b), .Bool), m1) := by
  have h8 := evalValue_boolToU8 m m1 e b he
  cases b <;> simp [boolNot, evalValue, h8, evalConstant, evalUnOp] <;> rfl

theorem translateRvalue_not_bool {layouts : Layout.LayoutTable} {decls : List LocalDecl}
    {targetTy : Option MirAst.Ty} {op : Operand} {e : Gen.ValueExpr}
    (hok : operandOkB layouts decls op = true)
    (he : translateRvalue layouts decls targetTy (.unaryOp .not op) = some e) :
    ∃ eo, translateOperand decls op = some eo ∧ e = boolNot eo := by
  have hty := operandType_of_operandOkB hok
  simp only [translateRvalue, Option.bind_eq_bind] at he
  cases heo : translateOperand decls op with
  | none => simp [heo] at he
  | some eo => simp [heo, hty] at he; exact ⟨eo, rfl, he.symm⟩

theorem translateRvalue_rel {layouts : Layout.LayoutTable} {decls : List LocalDecl}
    {targetTy : Option MirAst.Ty} {op : MirAst.BinOp} {a b : Operand}
    {e : Gen.ValueExpr} {rel : Gen.RelOp} (hrel : translateRelOp op = some rel)
    (he : translateRvalue layouts decls targetTy (.binaryOp op a b) = some e) :
    ∃ ea eb, translateOperand decls a = some ea ∧ translateOperand decls b = some eb ∧
      e = .BinOp (.Rel rel) ea eb := by
  simp only [translateRvalue, Option.bind_eq_bind] at he
  cases hea : translateOperand decls a with
  | none => simp [hea] at he
  | some ea =>
    cases heb : translateOperand decls b with
    | none => simp [hea, heb] at he
    | some eb => simp [hea, heb, hrel] at he; exact ⟨ea, eb, rfl, rfl, he.symm⟩

/-- Bitwise evaluation of `BitAnd`, `BitOr`, and `BitXor` on `bool` bits (`0`
or `1`). -/
def boolBitEval : Gen.IntBinOp → Nat → Nat → Nat
  | .BitAnd, x, y => if x = 1 ∧ y = 1 then 1 else 0
  | .BitOr, x, y => if x = 1 ∨ y = 1 then 1 else 0
  | .BitXor, x, y => if (x = 1) ≠ (y = 1) then 1 else 0
  | _, _, _ => 0

theorem boolBitEval_lt (iop : Gen.IntBinOp) (x y : Nat) : boolBitEval iop x y < 2 := by
  unfold boolBitEval
  split <;> try split
  all_goals omega

/-- `build::bool_and`, `build::bool_or`, and `build::bool_xor` on two `bool`
operands: all three transmutes succeed because `0` and `1` are valid `bool`
bytes and their bitwise combinations are also `0` or `1`. -/
theorem evalValue_boolBitOp {op : MirAst.BinOp} {iop : Gen.IntBinOp}
    (hop : translateBoolBitOp op = some iop) (m m1 m2 : Mach) (ea eb : Gen.ValueExpr)
    (x y : Nat) (hx : x < 2) (hy : y < 2)
    (ha : evalValue m ea = .ok ((valOf .Bool x, .Bool), m1))
    (hb : evalValue m1 eb = .ok ((valOf .Bool y, .Bool), m2)) :
    evalValue m (boolBitOp iop ea eb) =
      .ok ((valOf .Bool (boolBitEval iop x y), .Bool), m2) := by
  have ha8 := evalValue_boolToU8 m m1 ea (decide (x = 1)) ha
  have hb8 := evalValue_boolToU8 m1 m2 eb (decide (y = 1)) hb
  cases op <;> simp [translateBoolBitOp] at hop <;> subst hop <;>
    rcases (by omega : x = 0 ∨ x = 1) with rfl | rfl <;>
    rcases (by omega : y = 0 ∨ y = 1) with rfl | rfl <;>
    simp [boolBitOp, evalValue, ha8, hb8] <;> rfl

theorem translateRvalue_boolBit {layouts : Layout.LayoutTable} {decls : List LocalDecl}
    {targetTy : Option MirAst.Ty} {op : MirAst.BinOp} {a b : Operand}
    {e : Gen.ValueExpr} {iop : Gen.IntBinOp} (hop : translateBoolBitOp op = some iop)
    (hty : operandType layouts decls a = some .Bool)
    (he : translateRvalue layouts decls targetTy (.binaryOp op a b) = some e) :
    ∃ ea eb, translateOperand decls a = some ea ∧ translateOperand decls b = some eb ∧
      e = boolBitOp iop ea eb := by
  have hrel : translateRelOp op = none := by
    cases op <;> simp [translateBoolBitOp] at hop <;> rfl
  have hbin : translateBinOp op = some iop := by
    cases op <;> simp [translateBoolBitOp] at hop <;> subst hop <;> rfl
  simp only [translateRvalue, Option.bind_eq_bind] at he
  cases hea : translateOperand decls a with
  | none => simp [hea] at he
  | some ea =>
    cases heb : translateOperand decls b with
    | none => simp [hea, heb] at he
    | some eb =>
      simp [hea, heb, hrel, hbin, hty, hop] at he
      exact ⟨ea, eb, rfl, rfl, he.symm⟩

/-- The bit pattern an Anneal fragment rvalue of type `bool` evaluates to, or
`none` when evaluating it is UB. -/
def rvBitsB (decls : List LocalDecl) (locals : List LocalSlot) (rv : Rvalue)
    (layouts : Layout.LayoutTable := ⟨64, true, []⟩) : Option Nat :=
  match rv with
  | .use op => opBits locals op
  | .unaryOp .not op => (opBits locals op).map (fun x => 1 - x)
  | .binaryOp op a b =>
    match translateRelOp op with
    | some rel => do
      let T ← operandType layouts decls a
      let x ← opBits locals a
      let y ← opBits locals b
      pure (if relBool rel (cmpOf T x y) then 1 else 0)
    | none => do
      let iop ← translateBoolBitOp op
      let x ← opBits locals a
      let y ← opBits locals b
      pure (boolBitEval iop x y)
  | _ => none

/-- Comparable operand predicate: either an integer operand (`operandOk`,
including array element and `TupleSpec` scalar field projections) or a `bool`
operand (`operandOkB`). -/
inductive RelOperandOk (layouts : Layout.LayoutTable) (decls : List LocalDecl) :
    Gen.Type → Gen.IntType → Operand → Prop
  | int (it : Gen.IntType) (op : Operand)
      (hok : operandOk layouts decls it op = true) :
      RelOperandOk layouts decls (.Int it) it op
  | bool (op : Operand)
      (hok : operandOkB layouts decls op = true) :
      RelOperandOk layouts decls .Bool u8Ty op

/-- Evaluating a comparable operand (`RelOperandOk`). -/
theorem evalValue_relOperand {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {locals : List LocalSlot} {lm : Map Gen.LocalName Ptr} {m : Mach} {blk stmt : Nat}
    (h : FrameOk body f ctx locals lm m blk stmt) {T : Gen.Type} {it : Gen.IntType}
    (op : Operand) (hok : RelOperandOk body.layouts body.localDecls T it op)
    (e : Gen.ValueExpr) (he : translateOperand body.localDecls op = some e) :
    (∀ r, opBits locals op = some r →
      ValidBits T r ∧
      ∃ m', evalValue m e = .ok ((valOf T r, T), m') ∧
        FrameOk body f ctx locals lm m' blk stmt) ∧
    (opBits locals op = none → ∃ msg, evalValue m e = .error (.ub msg)) := by
  cases hok with
  | int it op hok =>
    simpa [ValidBits, valOf] using evalValue_operand h it op hok e he
  | bool op hok =>
    exact evalValue_operandT h .bool op (operandOkB_T hok) e he

/-- The operands of a fragment comparison have one fragment type. -/
theorem relOperandsOk_spec {layouts : Layout.LayoutTable} {decls : List LocalDecl} {a b : Operand}
    (h : relOperandsOk layouts decls a b = true) :
    ∃ T it, RelTy T it ∧ operandType layouts decls a = some T ∧
      RelOperandOk layouts decls T it a ∧ RelOperandOk layouts decls T it b := by
  unfold relOperandsOk at h
  split at h
  · next it hty =>
    simp only [Bool.and_eq_true] at h
    exact ⟨.Int it, it, .int it (operandOk_good h.1), hty, .int it a h.1, .int it b h.2⟩
  · next hty =>
    simp only [Bool.and_eq_true] at h
    exact ⟨.Bool, u8Ty, .bool, hty, .bool a h.1, .bool b h.2⟩
  · simp at h

/-- Evaluating a translated fragment rvalue of type `bool`. -/
theorem evalValue_rvalueB {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {locals : List LocalSlot} {lm : Map Gen.LocalName Ptr} {m : Mach} {blk stmt : Nat}
    {targetTy : Option MirAst.Ty}
    (h : FrameOk body f ctx locals lm m blk stmt)
    (rv : Rvalue) (hok : rvalueOkB body.layouts body.localDecls rv = true) (e : Gen.ValueExpr)
    (he : translateRvalue body.layouts body.localDecls targetTy rv = some e) :
    (∀ r, rvBitsB body.localDecls locals rv body.layouts = some r →
      r < 2 ∧
      ∃ m', evalValue m e = .ok ((valOf .Bool r, .Bool), m') ∧
        FrameOk body f ctx locals lm m' blk stmt) ∧
    (rvBitsB body.localDecls locals rv body.layouts = none →
      ∃ msg, evalValue m e = .error (.ub msg)) := by
  match rv, hok, he with
  | .use op, hok, he =>
    simp only [rvalueOkB] at hok
    simp only [translateRvalue] at he
    obtain ⟨hsome, hnone⟩ := evalValue_operandT h .bool op (operandOkB_T hok) e he
    refine ⟨fun r hr => ?_, fun hr => hnone hr⟩
    obtain ⟨hb, m', hm', h'⟩ := hsome r hr
    exact ⟨by simpa [ValidBits] using hb, m', hm', h'⟩
  | .unaryOp .not op, hok, he =>
    simp only [rvalueOkB] at hok
    obtain ⟨eo, heo, rfl⟩ := translateRvalue_not_bool hok he
    obtain ⟨hsome, hnone⟩ := evalValue_operandT h .bool op (operandOkB_T hok) eo heo
    cases hxo : opBits locals op with
    | none =>
      refine ⟨fun r hr => by simp [rvBitsB, hxo] at hr, fun _ => ?_⟩
      obtain ⟨msg, hmsg⟩ := hnone hxo
      exact ⟨msg, by simp [boolNot, boolToU8, evalValue, hmsg, evalConstant]⟩
    | some x =>
      obtain ⟨hx, m1, hm1, h1⟩ := hsome x hxo
      have hx2 : x < 2 := by simpa [ValidBits] using hx
      refine ⟨fun r hr => ?_, fun hr => by simp [rvBitsB, hxo] at hr⟩
      simp [rvBitsB, hxo] at hr
      subst hr
      refine ⟨by omega, m1, ?_, h1⟩
      rw [evalValue_boolNot m m1 eo _ hm1]
      rcases (by omega : x = 0 ∨ x = 1) with rfl | rfl <;> rfl
  | .unaryOp .neg _, hok, _ => simp [rvalueOkB] at hok
  | .unaryOp .ptrMetadata _, hok, _ => simp [rvalueOkB] at hok
  | .binaryOp op a b, hok, he =>
    cases hrel : translateRelOp op with
    | some rel =>
      simp [rvalueOkB, hrel] at hok
      obtain ⟨ea, eb, hea, heb, rfl⟩ := translateRvalue_rel hrel he
      obtain ⟨T, it, hT, htyA, hokA, hokB⟩ := relOperandsOk_spec hok
      obtain ⟨hasome, hanone⟩ := evalValue_relOperand h a hokA ea hea
      cases hxa : opBits locals a with
      | none =>
        refine ⟨fun r hr => by simp [rvBitsB, hrel, htyA, hxa] at hr, fun _ => ?_⟩
        obtain ⟨msg, hmsg⟩ := hanone hxa
        exact ⟨msg, by simp [evalValue, hmsg]⟩
      | some x =>
        obtain ⟨_, m1, hm1, h1⟩ := hasome x hxa
        obtain ⟨hbsome, hbnone⟩ := evalValue_relOperand h1 b hokB eb heb
        cases hyb : opBits locals b with
        | none =>
          refine ⟨fun r hr => by simp [rvBitsB, hrel, htyA, hxa, hyb] at hr, fun _ => ?_⟩
          obtain ⟨msg, hmsg⟩ := hbnone hyb
          exact ⟨msg, by simp [evalValue, hm1, hmsg]⟩
        | some y =>
          obtain ⟨_, m2, hm2, h2⟩ := hbsome y hyb
          refine ⟨fun r hr => ?_, fun hr => by simp [rvBitsB, hrel, htyA, hxa, hyb] at hr⟩
          simp [rvBitsB, hrel, htyA, hxa, hyb] at hr
          subst hr
          refine ⟨by split <;> omega, m2, ?_, h2⟩
          simp only [evalValue, hm1, hm2, ok_bind, evalBinOp_rel_frag hT rel
            (translateRelOp_ne_cmp hrel) x y]
          cases relBool rel (cmpOf T x y) <;> rfl
    | none =>
      simp [rvalueOkB, hrel] at hok
      obtain ⟨⟨hbitSome, hokA'⟩, hokB'⟩ := hok
      cases hiop : translateBoolBitOp op with
      | none => simp [hiop] at hbitSome
      | some iop =>
        have hokA := operandOkB_T hokA'
        have hokB := operandOkB_T hokB'
        have htyA := operandType_of_operandOkB hokA'
        obtain ⟨ea, eb, hea, heb, rfl⟩ := translateRvalue_boolBit hiop htyA he
        obtain ⟨hasome, hanone⟩ := evalValue_operandT h .bool a hokA ea hea
        cases hxa : opBits locals a with
        | none =>
          refine ⟨fun r hr => by simp [rvBitsB, hrel, hiop, hxa] at hr, fun _ => ?_⟩
          obtain ⟨msg, hmsg⟩ := hanone hxa
          exact ⟨msg, by simp [boolBitOp, boolToU8, evalValue, hmsg]⟩
        | some x =>
          obtain ⟨hx, m1, hm1, h1⟩ := hasome x hxa
          have hx2 : x < 2 := by simpa [ValidBits] using hx
          have ha8 := evalValue_boolToU8 m m1 ea (decide (x = 1)) hm1
          obtain ⟨hbsome, hbnone⟩ := evalValue_operandT h1 .bool b hokB eb heb
          cases hyb : opBits locals b with
          | none =>
            refine ⟨fun r hr => by simp [rvBitsB, hrel, hiop, hxa, hyb] at hr, fun _ => ?_⟩
            obtain ⟨msg, hmsg⟩ := hbnone hyb
            refine ⟨msg, by simp [boolBitOp, evalValue, ha8]; simp [boolToU8, evalValue, hmsg]⟩
          | some y =>
            obtain ⟨hy, m2, hm2, h2⟩ := hbsome y hyb
            have hy2 : y < 2 := by simpa [ValidBits] using hy
            refine ⟨fun r hr => ?_, fun hr => by simp [rvBitsB, hrel, hiop, hxa, hyb] at hr⟩
            simp [rvBitsB, hrel, hiop, hxa, hyb] at hr
            subst hr
            exact ⟨boolBitEval_lt iop x y, m2,
              evalValue_boolBitOp hiop m m1 m2 ea eb x y hx2 hy2 hm1 hm2, h2⟩
  | .cast _ _ _, hok, _ => simp [rvalueOkB] at hok
  | .copyForDeref _, hok, _ => simp [rvalueOkB] at hok
  | .repeat _ _, hok, _ => simp [rvalueOkB] at hok
  | .ref _ _, hok, _ => simp [rvalueOkB] at hok
  | .rawPtr _ _, hok, _ => simp [rvalueOkB] at hok
  | .len _, hok, _ => simp [rvalueOkB] at hok
  | .discriminant _, hok, _ => simp [rvalueOkB] at hok
  | .aggregate _ _, hok, _ => simp [rvalueOkB] at hok
  | .threadLocalRef _, hok, _ => simp [rvalueOkB] at hok
  | .nullaryOp _ _, hok, _ => simp [rvalueOkB] at hok
  | .shallowInitBox _ _, hok, _ => simp [rvalueOkB] at hok
  | .wrapUnsafeBinder _ _, hok, _ => simp [rvalueOkB] at hok

/-- `Machine::eval_statement` on a translated fragment assignment to a `bool`
local. -/
theorem evalStatement_assignB {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {locals : List LocalSlot} {lm : Map Gen.LocalName Ptr} {m : Mach} {blk stmt : Nat}
    {targetTy : Option MirAst.Ty}
    (h : FrameOk body f ctx locals lm m blk stmt)
    (i : Nat) (d : LocalDecl) (hd : body.localDecls[i]? = some d) (hlive : locals[i]? ≠ some .dead)
    (hbool : isBoolTy d.ty = true)
    (rv : Rvalue) (hok : rvalueOkB body.layouts body.localDecls rv = true) (e : Gen.ValueExpr)
    (he : translateRvalue body.layouts body.localDecls targetTy rv = some e) :
    (∀ r, rvBitsB body.localDecls locals rv body.layouts = some r →
      ∃ m', evalStatement m (.Assign (.Local (localName i)) e) = .ok m' ∧
        FrameOk body f ctx (locals.set i (.init (.scalar ⟨r, (itOf d body.layouts).size.bytes⟩)))
          lm m' blk stmt) ∧
    (rvBitsB body.localDecls locals rv body.layouts = none →
      ∃ msg, evalStatement m (.Assign (.Local (localName i)) e) = .error (.ub msg)) := by
  have hi : i < body.localDecls.length := (List.getElem?_eq_some_iff.mp hd).1
  have htyd : tyOf d body.layouts = .Bool := (tyOf_bool (layouts := body.layouts) hbool).1
  have hspec := h.hf.2 i d hd
  obtain ⟨_, slot, _, hs⟩ := h.slot_exists i hi
  obtain ⟨p, hp⟩ := h.locs.some_of_live hs (fun hc => hlive (hc ▸ hs))
  have hplace := evalPlace_local_some h.shape i _ hspec.2 p hp
  obtain ⟨hrok, hrnone⟩ := evalValue_rvalueB h rv hok e he
  refine ⟨fun r hr => ?_, fun hnone => ?_⟩
  · obtain ⟨hrlt, m1, hm1, h1⟩ := hrok r hr
    exact evalStatement_assign_of h i d hd hlive e r (by rw [htyd]; exact hrlt) _ m1
      (by rw [htyd]; exact hm1) h1
  · obtain ⟨msg, hmsg⟩ := hrnone hnone
    exact ⟨msg, by simp [evalStatement, hplace, hmsg]⟩

/-! ## `Ordering` rvalues -/

/-- The tag of the `Ordering` variant for a comparison outcome: `Less` is the
`i8` `-1` (bit pattern `255`), `Equal` is `0`, and `Greater` is `1`. -/
def ordBits : Ordering → Nat
  | .lt => 255
  | .eq => 0
  | .gt => 1

theorem validBits_ordBits (o : Ordering) : ValidBits orderingTy (ordBits o) := by
  cases o <;> exact (validBits_iff _ _).mp rfl

/-- The transmute of `translateCmp` turns the `i8` that `RelOp::Cmp` returns
for the outcome `o` into the `Ordering` variant with tag `ordBits o`. -/
theorem evalUnOp_transmute_ordering (o : Ordering) :
    evalUnOp (.Cast (.Transmute orderingTy)) (evalRelOp .Cmp o) =
      .ok (valOf orderingTy (ordBits o), orderingTy) := by
  cases o <;> rfl

/-- `BinOp::Rel(RelOp::Cmp)` on two values of one comparable fragment type. -/
theorem evalBinOp_cmp_frag {T : Gen.Type} {it : Gen.IntType} (hT : RelTy T it) (x y : Nat) :
    evalBinOp (.Rel .Cmp) (valOf T x, T) (valOf T y, T) = .ok (evalRelOp .Cmp (cmpOf T x y)) := by
  cases hT <;> simp [evalBinOp, valOf, cmpOf]

/-- `translateCmp` on two operands of one comparable fragment type evaluates
to the `Ordering` variant of their comparison. -/
theorem evalValue_translateCmp {T : Gen.Type} {it : Gen.IntType} (hT : RelTy T it)
    (m m1 m2 : Mach) (ea eb : Gen.ValueExpr) (x y : Nat)
    (ha : evalValue m ea = .ok ((valOf T x, T), m1))
    (hb : evalValue m1 eb = .ok ((valOf T y, T), m2)) :
    evalValue m (translateCmp ea eb) =
      .ok ((valOf orderingTy (ordBits (cmpOf T x y)), orderingTy), m2) := by
  simp only [translateCmp, evalValue, ha, hb, ok_bind, evalBinOp_cmp_frag hT x y]
  generalize cmpOf T x y = o
  cases o <;> rfl

theorem translateRvalue_cmp {layouts : Layout.LayoutTable} {decls : List LocalDecl}
    {targetTy : Option MirAst.Ty} {a b : Operand} {e : Gen.ValueExpr}
    (he : translateRvalue layouts decls targetTy (.binaryOp .cmp a b) = some e) :
    ∃ ea eb, translateOperand decls a = some ea ∧ translateOperand decls b = some eb ∧
      e = translateCmp ea eb := by
  simp only [translateRvalue, Option.bind_eq_bind] at he
  cases hea : translateOperand decls a with
  | none => simp [hea] at he
  | some ea =>
    cases heb : translateOperand decls b with
    | none => simp [hea, heb] at he
    | some eb =>
      simp [hea, heb, translateRelOp, translateBinOp, translateCheckedBinOp] at he
      exact ⟨ea, eb, rfl, rfl, he.symm⟩

/-- A fragment rvalue of type `Ordering` is either a `Use` of an `Ordering`
operand or a three-way comparison `Cmp`. -/
theorem rvalueOkO_spec {layouts : Layout.LayoutTable} {decls : List LocalDecl} {rv : Rvalue}
    (h : rvalueOkO layouts decls rv = true) :
    (∃ op, rv = .use op ∧ operandOkO decls op = true) ∨
    (∃ a b, rv = .binaryOp .cmp a b ∧ relOperandsOk layouts decls a b = true) := by
  unfold rvalueOkO at h
  split at h
  · exact .inl ⟨_, rfl, h⟩
  · exact .inr ⟨_, _, rfl, h⟩
  · simp at h

/-- The bit pattern an Anneal fragment rvalue of type `Ordering` evaluates to,
or `none` when evaluating it is UB. -/
def rvBitsO (decls : List LocalDecl) (locals : List LocalSlot) (rv : Rvalue)
    (layouts : Layout.LayoutTable := ⟨64, true, []⟩) : Option Nat :=
  match rv with
  | .use op => opBits locals op
  | .binaryOp .cmp a b => do
    let T ← operandType layouts decls a
    let x ← opBits locals a
    let y ← opBits locals b
    pure (ordBits (cmpOf T x y))
  | _ => none

/-- Evaluating a translated fragment rvalue of type `Ordering`. -/
theorem evalValue_rvalueO {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {locals : List LocalSlot} {lm : Map Gen.LocalName Ptr} {m : Mach} {blk stmt : Nat}
    {targetTy : Option MirAst.Ty}
    (h : FrameOk body f ctx locals lm m blk stmt)
    (rv : Rvalue) (hok : rvalueOkO body.layouts body.localDecls rv = true) (e : Gen.ValueExpr)
    (he : translateRvalue body.layouts body.localDecls targetTy rv = some e) :
    (∀ r, rvBitsO body.localDecls locals rv body.layouts = some r →
      ValidBits orderingTy r ∧
      ∃ m', evalValue m e = .ok ((valOf orderingTy r, orderingTy), m') ∧
        FrameOk body f ctx locals lm m' blk stmt) ∧
    (rvBitsO body.localDecls locals rv body.layouts = none →
      ∃ msg, evalValue m e = .error (.ub msg)) := by
  rcases rvalueOkO_spec hok with ⟨op, rfl, hokOp⟩ | ⟨a, b, rfl, hops⟩
  · simp only [translateRvalue] at he
    exact evalValue_operandT h .ordering op (operandOkO_T hokOp) e he
  · obtain ⟨ea, eb, hea, heb, rfl⟩ := translateRvalue_cmp he
    obtain ⟨T, it, hT, htyA, hokA, hokB⟩ := relOperandsOk_spec hops
    obtain ⟨hasome, hanone⟩ := evalValue_relOperand h a hokA ea hea
    cases hxa : opBits locals a with
    | none =>
      refine ⟨fun r hr => by simp [rvBitsO, htyA, hxa] at hr, fun _ => ?_⟩
      obtain ⟨msg, hmsg⟩ := hanone hxa
      exact ⟨msg, by simp [translateCmp, evalValue, hmsg]⟩
    | some x =>
      obtain ⟨_, m1, hm1, h1⟩ := hasome x hxa
      obtain ⟨hbsome, hbnone⟩ := evalValue_relOperand h1 b hokB eb heb
      cases hyb : opBits locals b with
      | none =>
        refine ⟨fun r hr => by simp [rvBitsO, htyA, hxa, hyb] at hr, fun _ => ?_⟩
        obtain ⟨msg, hmsg⟩ := hbnone hyb
        exact ⟨msg, by simp [translateCmp, evalValue, hm1, hmsg]⟩
      | some y =>
        obtain ⟨_, m2, hm2, h2⟩ := hbsome y hyb
        refine ⟨fun r hr => ?_, fun hr => by simp [rvBitsO, htyA, hxa, hyb] at hr⟩
        simp [rvBitsO, htyA, hxa, hyb] at hr
        subst hr
        exact ⟨validBits_ordBits _, m2, evalValue_translateCmp hT m m1 m2 ea eb x y hm1 hm2, h2⟩

/-- `Machine::eval_statement` on a translated fragment assignment to an
`Ordering` local. -/
theorem evalStatement_assignO {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {locals : List LocalSlot} {lm : Map Gen.LocalName Ptr} {m : Mach} {blk stmt : Nat}
    {targetTy : Option MirAst.Ty}
    (h : FrameOk body f ctx locals lm m blk stmt)
    (i : Nat) (d : LocalDecl) (hd : body.localDecls[i]? = some d) (hlive : locals[i]? ≠ some .dead)
    (hord : isOrderingTy d.ty = true)
    (rv : Rvalue) (hok : rvalueOkO body.layouts body.localDecls rv = true) (e : Gen.ValueExpr)
    (he : translateRvalue body.layouts body.localDecls targetTy rv = some e) :
    (∀ r, rvBitsO body.localDecls locals rv body.layouts = some r →
      ∃ m', evalStatement m (.Assign (.Local (localName i)) e) = .ok m' ∧
        FrameOk body f ctx (locals.set i (.init (.scalar ⟨r, (itOf d body.layouts).size.bytes⟩)))
          lm m' blk stmt) ∧
    (rvBitsO body.localDecls locals rv body.layouts = none →
      ∃ msg, evalStatement m (.Assign (.Local (localName i)) e) = .error (.ub msg)) := by
  have hi : i < body.localDecls.length := (List.getElem?_eq_some_iff.mp hd).1
  have htyd : tyOf d body.layouts = orderingTy := (tyOf_ordering (layouts := body.layouts) hord).1
  have hspec := h.hf.2 i d hd
  obtain ⟨_, slot, _, hs⟩ := h.slot_exists i hi
  obtain ⟨p, hp⟩ := h.locs.some_of_live hs (fun hc => hlive (hc ▸ hs))
  have hplace := evalPlace_local_some h.shape i _ hspec.2 p hp
  obtain ⟨hrok, hrnone⟩ := evalValue_rvalueO h rv hok e he
  refine ⟨fun r hr => ?_, fun hnone => ?_⟩
  · obtain ⟨hrlt, m1, hm1, h1⟩ := hrok r hr
    exact evalStatement_assign_of h i d hd hlive e r (by rw [htyd]; exact hrlt) _ m1
      (by rw [htyd]; exact hm1) h1
  · obtain ⟨msg, hmsg⟩ := hrnone hnone
    exact ⟨msg, by simp [evalStatement, hplace, hmsg]⟩

/-! ## `(Int, bool)` 2-tuple rvalues and checked integer arithmetic -/

/-- Mathematical integer arithmetic of `eval_int_bin_op_with_overflow`. -/
def intCheckedArith : Gen.IntBinOpWithOverflow → Int → Int → Int
  | .Add, l, r => l + r
  | .Sub, l, r => l - r
  | .Mul, l, r => l * r

/-- `Machine::eval_bin_op` on `BinOp::IntWithOverflow(cop)` returns the
2-tuple `(res_wrapped, !can_represent(res))` at `intBoolTupleTy it`. -/
theorem evalBinOp_intWithOverflow (cop : Gen.IntBinOpWithOverflow) (it : Gen.IntType)
    (hgood : GoodSize it.size.bytes) (l r : Int) :
    evalBinOp (.IntWithOverflow cop) (.Int l, .Int it) (.Int r, .Int it) =
      let res := intCheckedArith cop l r
      let wrappedBits := (res % 2 ^ (8 * it.size.bytes)).toNat
      let ovfBit := if IntType.can_represent it res then 0 else 1
      .ok (tupleVal it wrappedBits ovfBit, intBoolTupleTy it) := by
  let res := intCheckedArith cop l r
  have heval : evalIntBinOpWithOverflow cop l r = res := by cases cop <;> rfl
  have hovf : decide ((if IntType.can_represent it res = true then 0 else 1) = 1) =
      !IntType.can_represent it res := by
    cases IntType.can_represent it res <;> rfl
  simp only [evalBinOp, heval, withOverflow_eq it hgood,
    bringInBounds_eq_intFromBits it hgood res, tupleVal, ← hovf]
  rfl

/-- Pair of bit patterns `(bits, b)` an Anneal 2-tuple operand evaluates to, or
`none` when reading it is UB. -/
def opTupleBits (locals : List LocalSlot) : Operand → Option (Nat × Nat)
  | .copy ⟨j, []⟩ =>
    match locals[j]? with
    | some (.init (.aggregate 0 [.scalar sc0, .scalar sc1])) => some (sc0.bits, sc1.bits)
    | _ => none
  | _ => none

/-- Pair of bit patterns `(bits, b)` an Anneal 2-tuple rvalue of type
`(it, bool)` evaluates to, or `none` when evaluating it is UB. -/
def rvTupleBits (locals : List LocalSlot) (it : Gen.IntType) : Rvalue → Option (Nat × Nat)
  | .use op => opTupleBits locals op
  | .binaryOp op a b => do
    let cop ← translateCheckedBinOp op
    let x ← opBits locals a
    let y ← opBits locals b
    let res := intCheckedArith cop (intFromBits x it) (intFromBits y it)
    let wrappedBits := (res % 2 ^ (8 * it.size.bytes)).toNat
    let ovfBit := if IntType.can_represent it res then 0 else 1
    pure (wrappedBits, ovfBit)
  | .aggregate .tuple [a, b] => do
    let x ← opBits locals a
    let y ← opBits locals b
    pure (x, y)
  | _ => none

theorem translateRelOp_of_translateCheckedBinOp {op : MirAst.BinOp}
    {cop : Gen.IntBinOpWithOverflow} (h : translateCheckedBinOp op = some cop) :
    translateRelOp op = none := by
  cases op <;> simp_all [translateCheckedBinOp, translateRelOp]

theorem translateBinOp_of_translateCheckedBinOp {op : MirAst.BinOp}
    {cop : Gen.IntBinOpWithOverflow} (h : translateCheckedBinOp op = some cop) :
    translateBinOp op = none := by
  cases op <;> simp_all [translateCheckedBinOp, translateBinOp]

theorem translateRvalue_checked {layouts : Layout.LayoutTable} {decls : List LocalDecl}
    {targetTy : Option MirAst.Ty} {op : MirAst.BinOp} {a b : Operand}
    {e : Gen.ValueExpr} {cop : Gen.IntBinOpWithOverflow}
    (hcop : translateCheckedBinOp op = some cop)
    (he : translateRvalue layouts decls targetTy (.binaryOp op a b) = some e) :
    ∃ ea eb, translateOperand decls a = some ea ∧ translateOperand decls b = some eb ∧
      e = .BinOp (.IntWithOverflow cop) ea eb := by
  simp only [translateRvalue, Option.bind_eq_bind, translateRelOp_of_translateCheckedBinOp hcop,
    translateBinOp_of_translateCheckedBinOp hcop, hcop] at he
  cases hea : translateOperand decls a with
  | none => simp [hea] at he
  | some ea =>
    cases heb : translateOperand decls b with
    | none => simp [hea, heb] at he
    | some eb => simp [hea, heb] at he; exact ⟨ea, eb, rfl, rfl, he.symm⟩

theorem translateRvalue_tuple_agg {layouts : Layout.LayoutTable} {decls : List LocalDecl}
    {targetTy : Option MirAst.Ty} {it : Gen.IntType} {a b : Operand}
    {e : Gen.ValueExpr} (htgt : (targetTy >>= intBoolTupleOf) = some it)
    (he : translateRvalue layouts decls targetTy (.aggregate .tuple [a, b]) = some e) :
    ∃ ea eb, translateOperand decls a = some ea ∧ translateOperand decls b = some eb ∧
      e = .Tuple [ea, eb] (intBoolTupleTy it) := by
  simp only [translateRvalue, List.mapM_cons, List.mapM_nil, Option.bind_eq_bind, htgt] at he
  cases hea : translateOperand decls a with
  | none => simp [hea] at he
  | some ea =>
    cases heb : translateOperand decls b with
    | none => simp [hea, heb] at he
    | some eb => simp [hea, heb] at he; exact ⟨ea, eb, rfl, rfl, he.symm⟩

/-- Evaluating a translated fragment 2-tuple operand of type `intBoolTupleTy it`. -/
theorem evalValue_operandTuple {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {locals : List LocalSlot} {lm : Map Gen.LocalName Ptr} {m : Mach} {blk stmt : Nat}
    (h : FrameOk body f ctx locals lm m blk stmt)
    (it : Gen.IntType) (hgood : GoodSize it.size.bytes) (op : Operand)
    (hok : operandOkTuple body.localDecls it op = true) (e : Gen.ValueExpr)
    (he : translateOperand body.localDecls op = some e) :
    (∀ bits b, opTupleBits locals op = some (bits, b) →
      bits < 2 ^ (8 * it.size.bytes) ∧ b < 2 ∧
      ∃ m', evalValue m e = .ok ((tupleVal it bits b, intBoolTupleTy it), m') ∧
        FrameOk body f ctx locals lm m' blk stmt) ∧
    (opTupleBits locals op = none → ∃ msg, evalValue m e = .error (.ub msg)) := by
  match op, hok, he with
  | .copy ⟨j, []⟩, hok, he =>
    simp only [operandOkTuple, operandTupleIntType, Option.bind_eq_bind, Bool.and_eq_true,
      decide_eq_true_eq] at hok
    obtain ⟨hj, ht⟩ := hok
    simp only [translateOperand, translatePlace, Option.map_some, Option.some.injEq] at he
    subst he
    obtain ⟨d, slot, hd, hs⟩ := h.slot_exists j hj
    simp only [hd, Option.bind_some, decide_eq_true_eq] at ht
    obtain ⟨hTd, hitd⟩ := tyOf_tuple (layouts := body.layouts) ht
    have hspec := h.hf.2 j d hd
    have hloc := hspec.2
    rw [hTd] at hloc
    have hslot := (DeclSlotOk_of_scalarTypeOf (scalarTypeOf_tuple ht) slot).mp
      (h.slots j d slot hd hs)
    rw [hTd] at hslot
    cases hp : mapGet lm (localName j) with
    | none =>
      have hdead := h.locs.dead_of_none hs hp
      subst hdead
      refine ⟨fun bits b hbb => by simp [opTupleBits, hs] at hbb, fun _ => ?_⟩
      exact ⟨"access to a dead local", by simp [evalValue, evalPlace_local_none h.shape j _ hloc hp]⟩
    | some p =>
      obtain ⟨k, hpk, _⟩ := h.locs.storage j d slot p hd hs hp
      obtain ⟨_, _, _, _, hA⟩ :=
        h.locs.storage_id hd hs hp hpk (isPtrTy_false_of_scalarTypeOf (scalarTypeOf_tuple ht))
      rw [declSlotData_of_some ht, hitd] at hA
      have hplace := evalPlace_local_some h.shape j _ hloc p hp
      match slot, hslot, hA with
      | .dead, _, hA =>
        refine ⟨fun bits b hbb => by simp [opTupleBits, hs] at hbb, fun _ => ?_⟩
        obtain ⟨msg, hmsg⟩ := typedLoad_ptr_tuple_uninit h.shape p k hpk it hgood hA
        exact ⟨msg, by simp [evalValue, hplace, placeLoad, hmsg]⟩
      | .uninit, _, hA =>
        refine ⟨fun bits b hbb => by simp [opTupleBits, hs] at hbb, fun _ => ?_⟩
        obtain ⟨msg, hmsg⟩ := typedLoad_ptr_tuple_uninit h.shape p k hpk it hgood hA
        exact ⟨msg, by simp [evalValue, hplace, placeLoad, hmsg]⟩
      | .init (.scalar sc), ⟨_, hb⟩, _ =>
        simp [intBoolTupleTy, ValidBits] at hb
      | .init (.aggregate 0 [.scalar sc0, .scalar sc1]), ⟨it', htyT, _, hb0, _, hb1⟩, hA =>
        simp only [tupleIntOfTy_intBoolTupleTy, Option.some.injEq] at htyT
        subst htyT
        refine ⟨fun bits b hbb => ?_, fun hnone => by simp [opTupleBits, hs] at hnone⟩
        simp [opTupleBits, hs] at hbb
        rcases hbb with ⟨rfl, rfl⟩
        obtain ⟨m', hm', hshape⟩ :=
          typedLoad_ptr_tuple h.shape p k hpk it hgood sc0.bits sc1.bits hb0 hb1 hA
        exact ⟨hb0, hb1, m', by simp [evalValue, hplace, placeLoad, hm'],
          FrameOk.mk' h.hf hshape h.locs h.declsOk h.nonScalar⟩

/-- Evaluating a translated fragment rvalue of 2-tuple type `intBoolTupleTy it`. -/
theorem evalValue_rvalueTuple {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {locals : List LocalSlot} {lm : Map Gen.LocalName Ptr} {m : Mach} {blk stmt : Nat}
    {targetTy : Option MirAst.Ty}
    (h : FrameOk body f ctx locals lm m blk stmt)
    (it : Gen.IntType) (hgood : GoodSize it.size.bytes)
    (htgt : (targetTy >>= intBoolTupleOf) = some it) (rv : Rvalue)
    (hok : rvalueOkTuple body.layouts body.localDecls it rv = true) (e : Gen.ValueExpr)
    (he : translateRvalue body.layouts body.localDecls targetTy rv = some e) :
    (∀ bits b, rvTupleBits locals it rv = some (bits, b) →
      bits < 2 ^ (8 * it.size.bytes) ∧ b < 2 ∧
      ∃ m', evalValue m e = .ok ((tupleVal it bits b, intBoolTupleTy it), m') ∧
        FrameOk body f ctx locals lm m' blk stmt) ∧
    (rvTupleBits locals it rv = none → ∃ msg, evalValue m e = .error (.ub msg)) := by
  unfold rvalueOkTuple at hok
  split at hok
  · next op =>
    simp only [translateRvalue] at he
    exact evalValue_operandTuple h it hgood op hok e he
  · next op a b =>
    simp only [Bool.and_eq_true] at hok
    obtain ⟨⟨hcopSome, hoka⟩, hokb⟩ := hok
    cases hcop : translateCheckedBinOp op with
    | none => simp [hcop] at hcopSome
    | some cop =>
      obtain ⟨ea, eb, hea, heb, rfl⟩ := translateRvalue_checked hcop he
      obtain ⟨haok, hanone⟩ := evalValue_operand h it a hoka ea hea
      cases hxa : opBits locals a with
      | none =>
        refine ⟨fun bits b' hbb => by simp [rvTupleBits, hcop, hxa] at hbb, fun _ => ?_⟩
        obtain ⟨msg, hmsg⟩ := hanone hxa
        exact ⟨msg, by simp [evalValue, hmsg]⟩
      | some x =>
        obtain ⟨_, m1, hm1, h1⟩ := haok x hxa
        obtain ⟨hbok, hbnone⟩ := evalValue_operand h1 it b hokb eb heb
        cases hyb : opBits locals b with
        | none =>
          refine ⟨fun bits b' hbb => by simp [rvTupleBits, hcop, hxa, hyb] at hbb, fun _ => ?_⟩
          obtain ⟨msg, hmsg⟩ := hbnone hyb
          exact ⟨msg, by simp [evalValue, hm1, hmsg]⟩
        | some y =>
          obtain ⟨_, m2, hm2, h2⟩ := hbok y hyb
          refine ⟨fun bits b' hbb => ?_, fun hnone => by simp [rvTupleBits, hcop, hxa, hyb] at hnone⟩
          simp [rvTupleBits, hcop, hxa, hyb] at hbb
          rcases hbb with ⟨rfl, rfl⟩
          have hpos := two_pow_pos (8 * it.size.bytes)
          let res := intCheckedArith cop (intFromBits x it) (intFromBits y it)
          have h0 := Int.emod_nonneg res (Int.ne_of_gt hpos)
          have hlt := Int.emod_lt_of_pos res hpos
          have hbits : (res % 2 ^ (8 * it.size.bytes)).toNat < 2 ^ (8 * it.size.bytes) := by
            have : (((res % 2 ^ (8 * it.size.bytes)).toNat : Int)) < 2 ^ (8 * it.size.bytes) := by
              rw [Int.toNat_of_nonneg h0]; exact hlt
            exact_mod_cast this
          have hb' : (if IntType.can_represent it res then 0 else 1) < 2 := by split <;> omega
          exact ⟨hbits, hb', m2,
            by simp [evalValue, hm1, hm2, evalBinOp_intWithOverflow cop it hgood], h2⟩
  · next a b =>
    simp only [Bool.and_eq_true] at hok
    obtain ⟨hoka, hokb⟩ := hok
    obtain ⟨ea, eb, hea, heb, rfl⟩ := translateRvalue_tuple_agg htgt he
    obtain ⟨haok, hanone⟩ := evalValue_operand h it a hoka ea hea
    cases hxa : opBits locals a with
    | none =>
      refine ⟨fun bits b' hbb => by simp [rvTupleBits, hxa] at hbb, fun _ => ?_⟩
      obtain ⟨msg, hmsg⟩ := hanone hxa
      exact ⟨msg, by simp [evalValue, evalValues, hmsg]⟩
    | some x =>
      obtain ⟨hx, m1, hm1, h1⟩ := haok x hxa
      obtain ⟨hbok, hbnone⟩ := evalValue_operandT h1 .bool b (operandOkB_T hokb) eb heb
      cases hyb : opBits locals b with
      | none =>
        refine ⟨fun bits b' hbb => by simp [rvTupleBits, hxa, hyb] at hbb, fun _ => ?_⟩
        obtain ⟨msg, hmsg⟩ := hbnone hyb
        exact ⟨msg, by simp [evalValue, evalValues, hm1, hmsg]⟩
      | some y =>
        obtain ⟨hy, m2, hm2, h2⟩ := hbok y hyb
        have hy2 : y < 2 := by simpa [ValidBits] using hy
        refine ⟨fun bits b' hbb => ?_, fun hnone => by simp [rvTupleBits, hxa, hyb] at hnone⟩
        simp [rvTupleBits, hxa, hyb] at hbb
        rcases hbb with ⟨rfl, rfl⟩
        refine ⟨hx, hy2, m2, ?_, h2⟩
        simp [evalValue, evalValues, hm1, hm2, valOf, tupleVal]
  · simp at hok

/-- `Machine::eval_statement` on a translated fragment assignment to an
`(it, bool)` 2-tuple local. -/
theorem evalStatement_assignTuple {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {locals : List LocalSlot} {lm : Map Gen.LocalName Ptr} {m : Mach} {blk stmt : Nat}
    (h : FrameOk body f ctx locals lm m blk stmt)
    (i : Nat) (d : LocalDecl) (hd : body.localDecls[i]? = some d)
    (hlive : locals[i]? ≠ some .dead)
    (htup : intBoolTupleOf d.ty = some (itOf d body.layouts)) (rv : Rvalue)
    (hok : rvalueOkTuple body.layouts body.localDecls (itOf d body.layouts) rv = true)
    (e : Gen.ValueExpr)
    (he : translateRvalue body.layouts body.localDecls (some d.ty) rv = some e) :
    (∀ bits b, rvTupleBits locals (itOf d body.layouts) rv = some (bits, b) →
      ∃ m', evalStatement m (.Assign (.Local (localName i)) e) = .ok m' ∧
        FrameOk body f ctx
          (locals.set i (.init (.aggregate 0
            [.scalar ⟨bits, (itOf d body.layouts).size.bytes⟩, .scalar ⟨b, 1⟩])))
          lm m' blk stmt) ∧
    (rvTupleBits locals (itOf d body.layouts) rv = none →
      ∃ msg, evalStatement m (.Assign (.Local (localName i)) e) = .error (.ub msg)) := by
  have hi : i < body.localDecls.length := (List.getElem?_eq_some_iff.mp hd).1
  have hgood := h.decl_good i d hd
  have htyd : tyOf d body.layouts = intBoolTupleTy (itOf d body.layouts) :=
    (tyOf_tuple (layouts := body.layouts) htup).1
  have hspec := h.hf.2 i d hd
  obtain ⟨_, slot, _, hs⟩ := h.slot_exists i hi
  have hslive : slot ≠ .dead := fun hc => hlive (hc ▸ hs)
  obtain ⟨p, hp⟩ := h.locs.some_of_live hs hslive
  have hplace := evalPlace_local_some h.shape i _ hspec.2 p hp
  obtain ⟨hrok, hrnone⟩ := evalValue_rvalueTuple h (itOf d body.layouts) hgood
    (by simpa using htup) rv hok e he
  refine ⟨fun bits b hbb => ?_, fun hnone => ?_⟩
  · obtain ⟨hbits, hb, m1, hm1, h1⟩ := hrok bits b hbb
    obtain ⟨k, hpk, _⟩ := h1.locs.storage i d slot p hd hs hp
    obtain ⟨_, _, _, _, hA⟩ :=
      h1.locs.storage_id hd hs hp hpk (isPtrTy_false_of_scalarTypeOf (scalarTypeOf_tuple htup))
    rw [declSlotData_of_some htup] at hA
    have hlen := tupleSlotData_length (itOf d body.layouts) slot hgood.pos
    have hst := typedStore_ptr_tuple h1.shape p k hpk (itOf d body.layouts) hgood _
      bits b hbits hb hA hlen
    let newSlot : LocalSlot :=
      .init (.aggregate 0 [.scalar ⟨bits, (itOf d body.layouts).size.bytes⟩, .scalar ⟨b, 1⟩])
    refine ⟨withMem m1 (m1.mem.memory.allocations.set k
        (stackAlloc p.addr (itOf d body.layouts) (tupleBytes (itOf d body.layouts) bits b)))
        ⟨.Store, .None, p.addr,
         ⟨(itOf d body.layouts).size.bytes + (itOf d body.layouts).size.bytes⟩⟩, ?_, ?_⟩
    · rw [htyd] at hplace
      simp [evalStatement, hplace, hm1, placeStore, hst]
    · refine FrameOk.mk' h.hf (withMem_shape h1.shape _) ?_ h.declsOk (h1.nonScalar.set_init i _)
      have hslot' : DeclSlotOk d newSlot body.layouts :=
        (DeclSlotOk_of_scalarTypeOf (scalarTypeOf_tuple htup) newSlot).mpr
          ⟨itOf d body.layouts, by rw [htyd, tupleIntOfTy_intBoolTupleTy], rfl, hbits, rfl, hb⟩
      have hlo' := h1.locs.store i d hd slot newSlot hs (by simp [newSlot]) hslot' p hp k hpk
        (.inl (isPtrTy_false_of_scalarTypeOf (scalarTypeOf_tuple htup)))
      simp only [declSlotData_of_some htup, newSlot, tupleSlotData] at hlo'
      exact hlo'
  · obtain ⟨msg, hmsg⟩ := hrnone hnone
    exact ⟨msg, by simp [evalStatement, hplace, hmsg]⟩

/-! ## `Switch` -/

theorem intFromBits_inj (it : Gen.IntType) (a b : Nat) (ha : a < 2 ^ (8 * it.size.bytes))
    (hb : b < 2 ^ (8 * it.size.bytes)) : intFromBits a it = intFromBits b it ↔ a = b := by
  constructor
  · intro h
    have := congrArg (· % (2 : Int) ^ (8 * it.size.bytes)) h
    simp only [intFromBits_emod a it ha, intFromBits_emod b it hb] at this
    exact_mod_cast this
  · intro h; rw [h]

theorem switch_lookup (it : Gen.IntType) (bits : Nat) (hb : bits < 2 ^ (8 * it.size.bytes))
    (branches : List (Nat × Nat)) (hbr : ∀ p ∈ branches, p.1 < 2 ^ (8 * it.size.bytes))
    (otherwise : Nat) :
    (mapGet (switchCases it branches) (intFromBits bits it)).getD (bbName otherwise) =
      bbName (MirSemantics.lookupSwitchTarget bits branches otherwise) := by
  induction branches with
  | nil => simp [switchCases, mapGet, MirSemantics.lookupSwitchTarget]
  | cons p ps ih =>
    obtain ⟨v, t⟩ := p
    have hv : v < 2 ^ (8 * it.size.bytes) := hbr (v, t) (by simp)
    have ih' := ih (fun q hq => hbr q (by simp [hq]))
    simp only [switchCases] at ih' ⊢
    rw [List.map_cons, mapGet_cons]
    simp only [MirSemantics.lookupSwitchTarget]
    by_cases hvb : v = bits
    · subst hvb; simp
    · have hne : intFromBits v it ≠ intFromBits bits it := by
        rw [Ne, intFromBits_inj it v bits hv hb]; exact hvb
      have hbeq : Nat.beq bits v = false := by
        cases h : Nat.beq bits v
        · rfl
        · exact absurd (Nat.eq_of_beq_eq_true h).symm hvb
      simp only [hne, ite_false, hbeq]
      exact ih'

/-! ## Deallocated allocations -/

/-- A deallocated allocation (`allocation.live = false`). -/
def kill (a : Gen.Allocation) : Gen.Allocation := { a with live := false }

/-- `L` with the allocations at indices `is` deallocated. -/
def killAt (L : List Gen.Allocation) (is : List Nat) : List Gen.Allocation :=
  L.mapIdx (fun j a => if j ∈ is then kill a else a)

theorem killAt_nil (L : List Gen.Allocation) : killAt L [] = L := by
  apply List.ext_getElem?
  intro j
  simp only [killAt, List.getElem?_mapIdx]
  cases L[j]? <;> simp

theorem killAt_cons (L : List Gen.Allocation) (i : Nat) (is : List Nat) (a : Gen.Allocation)
    (hi : L[i]? = some a) (hni : i ∉ is) :
    killAt L (i :: is) = killAt (L.set i (kill a)) is := by
  apply List.ext_getElem?
  intro j
  simp only [killAt, List.getElem?_mapIdx]
  by_cases hij : i = j
  · subst hij
    simp [hi, hni, List.getElem?_set_self (List.getElem?_eq_some_iff.mp hi).1]
  · simp [List.getElem?_set_ne hij, Ne.symm hij]

theorem killAt_range (L : List Gen.Allocation) : killAt L (List.range L.length) = L.map kill := by
  apply List.ext_getElem?
  intro j
  simp only [killAt, List.getElem?_mapIdx, List.getElem?_map]
  cases h : L[j]? with
  | none => simp
  | some a =>
    have := (List.getElem?_eq_some_iff.mp h).1
    simp [List.mem_range, this]

/-! ## Locals maps -/

theorem mapGet_mem {K V : Type} [DecidableEq K] {es : List (K × V)} {k : K} {v : V}
    (h : mapGet ⟨es⟩ k = some v) : (k, v) ∈ es := by
  induction es with
  | nil => simp [mapGet] at h
  | cons e es ih =>
    obtain ⟨k', v'⟩ := e
    rw [mapGet_cons] at h
    by_cases hk : k' = k
    · subst hk; simp at h; subst h; simp
    · simp [hk] at h; exact List.mem_cons_of_mem _ (ih h)

theorem mapGet_isSome_of_mem {K V : Type} [DecidableEq K] {es : List (K × V)} {k : K} {v : V}
    (h : (k, v) ∈ es) : (mapGet ⟨es⟩ k).isSome = true := by
  induction es with
  | nil => simp at h
  | cons e es ih =>
    obtain ⟨k', v'⟩ := e
    rw [mapGet_cons]
    by_cases hk : k' = k
    · simp [hk]
    · simp only [hk, ↓reduceIte]
      rcases List.mem_cons.mp h with h | h
      · simp only [Prod.mk.injEq] at h; exact absurd h.1.symm hk
      · exact ih h

theorem mapGet_filter_key {V : Type} (es : List (Gen.LocalName × V)) (key k : Gen.LocalName) :
    mapGet ⟨es.filter (fun e => !decide (e.1 = key))⟩ k =
      if k = key then none else mapGet ⟨es⟩ k := by
  induction es with
  | nil => simp [mapGet]
  | cons e es ih =>
    obtain ⟨k', v'⟩ := e
    by_cases hk' : k' = key
    · subst hk'
      rw [List.filter_cons_of_neg (by simp), ih, mapGet_cons]
      by_cases hkk : k = k'
      · simp [hkk]
      · simp [hkk, Ne.symm hkk]
    · rw [List.filter_cons_of_pos (by simp [hk']), mapGet_cons, mapGet_cons, ih]
      by_cases hkk : k = key
      · subst hkk; simp [hk']
      · simp [hkk]

theorem mapGet_append_single {V : Type} (es : List (Gen.LocalName × V)) (key k : Gen.LocalName)
    (v : V) (hnot : ∀ e ∈ es, e.1 ≠ key) :
    mapGet ⟨es ++ [(key, v)]⟩ k = if k = key then some v else mapGet ⟨es⟩ k := by
  induction es with
  | nil =>
    rw [List.nil_append, mapGet_cons]
    by_cases hkk : k = key
    · subst hkk; simp
    · simp [hkk, Ne.symm hkk, mapGet_nil]
  | cons e es ih =>
    obtain ⟨k', v'⟩ := e
    have hk' : k' ≠ key := hnot (k', v') (by simp)
    rw [List.cons_append, mapGet_cons, mapGet_cons,
      ih (fun e he => hnot e (List.mem_cons_of_mem _ he))]
    by_cases hkk : k = key
    · subst hkk; simp [hk']
    · simp [hkk]

theorem mapInsert_absent {K V : Type} [DecidableEq K] (es : List (K × V)) (k : K) (v : V)
    (hnot : ∀ e ∈ es, e.1 ≠ k) : mapInsert es k v = es ++ [(k, v)] := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    obtain ⟨k', v'⟩ := e
    have hk' : k' ≠ k := hnot (k', v') (by simp)
    simp only [mapInsert, hk', ↓reduceIte, List.cons_append]
    rw [ih (fun e he => hnot e (List.mem_cons_of_mem _ he))]

theorem filter_key_not_mem {V : Type} (es : List (Gen.LocalName × V)) (key : Gen.LocalName) :
    ∀ e ∈ es.filter (fun e => !decide (e.1 = key)), e.1 ≠ key := by
  intro e he
  simp only [List.mem_filter, Bool.not_eq_true', decide_eq_false_iff_not] at he
  exact he.2

theorem filter_key_nodup {V : Type} (es : List (Gen.LocalName × V)) (key : Gen.LocalName)
    (h : (es.map Prod.fst).Nodup) : ((es.filter (fun e => !decide (e.1 = key))).map Prod.fst).Nodup :=
  (List.filter_sublist.map Prod.fst).nodup h

/-- The locals map has at most one entry per local of the body. -/
theorem LocalsOkA.entries_length {body : CapturedMir} {ctx : Ctx} {al : List Nat}
    {locals : List LocalSlot} {lm : Map Gen.LocalName Ptr} {A : List Gen.Allocation}
    (hlo : LocalsOkA body ctx al locals lm A) :
    lm.entries.length ≤ body.localDecls.length := by
  have hsub : lm.entries.map Prod.fst ⊆ (List.range body.localDecls.length).map localName := by
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨e, he, rfl⟩ := hx
    obtain ⟨i, hi, hei⟩ := hlo.keysLocal e he
    simp only [List.mem_map, List.mem_range]
    exact ⟨i, hi, hei.symm⟩
  have := List.Nodup.length_le_of_subset hlo.keysNodup hsub
  simpa using this

theorem NonScalarLive.filter_scalar {body : CapturedMir} {locals : List LocalSlot}
    {lm : Map Gen.LocalName Ptr} (hns : NonScalarLive body locals lm)
    {i : Nat} {d : LocalDecl} (hd : body.localDecls[i]? = some d)
    (hscalar : (scalarTypeOf d.ty).isSome = true ∨ isPtrTy d.ty = true) (ns : LocalSlot) :
    NonScalarLive body (locals.set i ns)
      ⟨lm.entries.filter (fun e => !decide (e.1 = localName i))⟩ := by
  intro j dj slot hdj hsj hnone hnp
  by_cases hij : i = j
  · subst hij; rw [hd] at hdj; cases hdj
    rcases hscalar with hsc | hp
    · simp [hnone] at hsc
    · simp [hnp] at hp
  · rw [List.getElem?_set_ne hij] at hsj
    obtain ⟨hv, hp⟩ := hns j dj slot hdj hsj hnone hnp
    refine ⟨hv, fun p hget => hp p ?_⟩
    rw [mapGet_filter_key] at hget
    have hne : localName j ≠ localName i := by simp [localName_inj, Ne.symm hij]
    simpa [hne] using hget

theorem NonScalarLive.append_scalar {body : CapturedMir} {locals : List LocalSlot}
    {lm : Map Gen.LocalName Ptr} (hns : NonScalarLive body locals lm)
    {i : Nat} {d : LocalDecl} (hd : body.localDecls[i]? = some d)
    (hscalar : (scalarTypeOf d.ty).isSome = true ∨ isPtrTy d.ty = true)
    (hnot : ∀ e ∈ lm.entries, e.1 ≠ localName i) (newPtr : Ptr) :
    NonScalarLive body locals ⟨lm.entries ++ [(localName i, newPtr)]⟩ := by
  intro j dj slot hdj hsj hnone hnp
  by_cases hij : i = j
  · subst hij; rw [hd] at hdj; cases hdj
    rcases hscalar with hsc | hp
    · simp [hnone] at hsc
    · simp [hnp] at hp
  · obtain ⟨hv, hp⟩ := hns j dj slot hdj hsj hnone hnp
    refine ⟨hv, fun p hget => hp p ?_⟩
    rw [mapGet_append_single _ _ _ _ hnot] at hget
    have hne : localName j ≠ localName i := by simp [localName_inj, Ne.symm hij]
    simpa [hne] using hget

/-! ## Storage statements and `Deinit` -/

/-- `ConcurrentMemory::store` of `bytes` that fill a whole live allocation. -/
theorem CM_store_whole {cm : Gen.ConcurrentMemory BM} {p : Ptr} {k : Nat}
    (hp : p.provenance = some (⟨(k : Int)⟩, ())) {a : Gen.Allocation}
    (hA : cm.memory.allocations[k]? = some a) (hlive : a.live = true) (haddr : a.addr = p.addr)
    (bytes : List Byte) (hne : bytes ≠ []) (hlen : bytes.length = a.data.length) :
    CM.store cm p bytes ⟨1⟩ .None =
      .ok { memory := { cm.memory with allocations := cm.memory.allocations.set k { a with data := bytes } },
            accesses := cm.accesses ++ [⟨.Store, .None, p.addr, ⟨bytes.length⟩⟩] } := by
  obtain ⟨hk, hAk⟩ := List.getElem?_eq_some_iff.mp hA
  have hne' : a.data ≠ [] := by
    intro h; rw [h] at hlen; exact hne (List.eq_nil_of_length_eq_zero hlen)
  simp [CM.store, BM.store, isAligned_one, BM.check_ptr, hp, listIndex, hk, hAk, hlive, haddr,
    Allocation.size, hlen, writeSubsliceAtIndex, listSet, hne']

theorem scalar_tyBytes_pos {d : LocalDecl} {layouts : Layout.LayoutTable}
    (h : (scalarTypeOf d.ty).isSome = true ∨ isPtrTy d.ty = true) :
    0 < tyBytes (tyOf d layouts) := by
  rcases h with h | hp
  · obtain ⟨T, hs⟩ := Option.isSome_iff_exists.mp h
    rcases scalarTypeOf_cases hs with ⟨hb, _⟩ | ⟨it, hit, _⟩ | ⟨ho, _⟩ | ⟨it, ht, _⟩
    · obtain ⟨h1, h2⟩ := tyOf_bool (layouts := layouts) hb
      have hf : FragTy (tyOf d layouts) (itOf d layouts) := by rw [h1, h2]; exact .bool
      rw [hf.tyBytes]; exact hf.good.pos
    · obtain ⟨h1, h2⟩ := tyOf_int (layouts := layouts) hit
      have hf : FragTy (tyOf d layouts) (itOf d layouts) :=
        by rw [h1, h2]; exact .int it (intTypeOf_good hit)
      rw [hf.tyBytes]; exact hf.good.pos
    · obtain ⟨h1, h2⟩ := tyOf_ordering (layouts := layouts) ho
      have hf : FragTy (tyOf d layouts) (itOf d layouts) := by rw [h1, h2]; exact .ordering
      rw [hf.tyBytes]; exact hf.good.pos
    · obtain ⟨h1, _⟩ := tyOf_tuple (layouts := layouts) ht
      rw [h1]; simp only [intBoolTupleTy, tyBytes]; have := (intBoolTupleOf_good ht).pos; omega
  · obtain ⟨h1, _⟩ := tyOf_isPtrTy (layouts := layouts) hp
    rw [h1, tyBytes_declPtrTy]; decide

theorem scalar_size_le_tyBytes {d : LocalDecl} {layouts : Layout.LayoutTable}
    (h : (scalarTypeOf d.ty).isSome = true ∨ isPtrTy d.ty = true) :
    (itOf d layouts).size.bytes ≤ tyBytes (tyOf d layouts) := by
  rcases h with h | hp
  · obtain ⟨T, hs⟩ := Option.isSome_iff_exists.mp h
    rcases scalarTypeOf_cases hs with ⟨hb, _⟩ | ⟨it, hit, _⟩ | ⟨ho, _⟩ | ⟨it, ht, _⟩
    · obtain ⟨h1, h2⟩ := tyOf_bool (layouts := layouts) hb
      have hf : FragTy (tyOf d layouts) (itOf d layouts) := by rw [h1, h2]; exact .bool
      rw [hf.tyBytes]; exact Nat.le_refl _
    · obtain ⟨h1, h2⟩ := tyOf_int (layouts := layouts) hit
      have hf : FragTy (tyOf d layouts) (itOf d layouts) :=
        by rw [h1, h2]; exact .int it (intTypeOf_good hit)
      rw [hf.tyBytes]; exact Nat.le_refl _
    · obtain ⟨h1, h2⟩ := tyOf_ordering (layouts := layouts) ho
      have hf : FragTy (tyOf d layouts) (itOf d layouts) := by rw [h1, h2]; exact .ordering
      rw [hf.tyBytes]; exact Nat.le_refl _
    · obtain ⟨h1, h2⟩ := tyOf_tuple (layouts := layouts) ht
      rw [h1, h2]; simp only [intBoolTupleTy, tyBytes]; omega
  · obtain ⟨h1, h2⟩ := tyOf_isPtrTy (layouts := layouts) hp
    rw [h1, h2, tyBytes_declPtrTy]; decide

theorem scalar_tyBytes_le {d : LocalDecl} {layouts : Layout.LayoutTable}
    (h : (scalarTypeOf d.ty).isSome = true ∨ isPtrTy d.ty = true) :
    tyBytes (tyOf d layouts) ≤ 32 := by
  rcases h with h | hp
  · obtain ⟨T, hs⟩ := Option.isSome_iff_exists.mp h
    rcases scalarTypeOf_cases hs with ⟨hb, _⟩ | ⟨it, hit, _⟩ | ⟨ho, _⟩ | ⟨it, ht, _⟩
    · obtain ⟨h1, h2⟩ := tyOf_bool (layouts := layouts) hb
      have hf : FragTy (tyOf d layouts) (itOf d layouts) := by rw [h1, h2]; exact .bool
      rw [hf.tyBytes]; rcases hf.good with hg | hg | hg | hg | hg <;> omega
    · obtain ⟨h1, h2⟩ := tyOf_int (layouts := layouts) hit
      have hf : FragTy (tyOf d layouts) (itOf d layouts) :=
        by rw [h1, h2]; exact .int it (intTypeOf_good hit)
      rw [hf.tyBytes]; rcases hf.good with hg | hg | hg | hg | hg <;> omega
    · obtain ⟨h1, h2⟩ := tyOf_ordering (layouts := layouts) ho
      have hf : FragTy (tyOf d layouts) (itOf d layouts) := by rw [h1, h2]; exact .ordering
      rw [hf.tyBytes]; rcases hf.good with hg | hg | hg | hg | hg <;> omega
    · obtain ⟨h1, _⟩ := tyOf_tuple (layouts := layouts) ht
      rw [h1]; simp only [intBoolTupleTy, tyBytes]
      rcases intBoolTupleOf_good ht with hg | hg | hg | hg | hg <;> omega
  · obtain ⟨h1, _⟩ := tyOf_isPtrTy (layouts := layouts) hp
    rw [h1, tyBytes_declPtrTy]; decide

theorem declSlotOk_dead (d : LocalDecl) (layouts : Layout.LayoutTable) :
    DeclSlotOk d .dead layouts := by
  unfold DeclSlotOk; split <;> trivial

theorem declSlotOk_uninit (d : LocalDecl) (layouts : Layout.LayoutTable) :
    DeclSlotOk d .uninit layouts := by
  unfold DeclSlotOk; split <;> trivial

theorem declSlotData_dead (d : LocalDecl) (layouts : Layout.LayoutTable := ⟨64, true, []⟩) :
    declSlotData d .dead layouts = declSlotData d .uninit layouts := by
  unfold declSlotData
  split
  · rfl
  · split
    · rfl
    · split
      · rfl
      · split <;> rfl

theorem declSlotData_uninit {d : LocalDecl} {layouts : Layout.LayoutTable}
    (hd : scalarTypeOf d.ty = some (tyOf d layouts)) :
    declSlotData d .uninit layouts = List.replicate (tyBytes (tyOf d layouts)) .Uninit := by
  rcases scalarTypeOf_cases hd with ⟨hb, _⟩ | ⟨it, hit, _⟩ | ⟨ho, _⟩ | ⟨it, ht, _⟩
  · obtain ⟨h1, h2⟩ := tyOf_bool (layouts := layouts) hb
    have hf : FragTy (tyOf d layouts) (itOf d layouts) := by rw [h1, h2]; exact .bool
    rw [hf.declSlotData, hf.tyBytes]; rfl
  · obtain ⟨h1, h2⟩ := tyOf_int (layouts := layouts) hit
    have hf : FragTy (tyOf d layouts) (itOf d layouts) :=
      by rw [h1, h2]; exact .int it (intTypeOf_good hit)
    rw [hf.declSlotData, hf.tyBytes]; rfl
  · obtain ⟨h1, h2⟩ := tyOf_ordering (layouts := layouts) ho
    have hf : FragTy (tyOf d layouts) (itOf d layouts) := by rw [h1, h2]; exact .ordering
    rw [hf.declSlotData, hf.tyBytes]; rfl
  · obtain ⟨h1, _⟩ := tyOf_tuple (layouts := layouts) ht
    rw [declSlotData_of_some ht, h1]; rfl

theorem declSlotData_uninit_of_declOk {d : LocalDecl} {layouts : Layout.LayoutTable}
    (hdok : localDeclOk layouts d = true) :
    declSlotData d .uninit layouts = List.replicate (tyBytes (tyOf d layouts)) .Uninit := by
  unfold localDeclOk at hdok
  cases hs : scalarTypeOf d.ty with
  | some T =>
    have hT : tyOf d layouts = T := tyOf_of_scalarTypeOf hs
    exact declSlotData_uninit (hT ▸ hs)
  | none =>
    simp only [hs, Option.isSome_none, Bool.false_or] at hdok
    cases ha : arrayTypeOf d.ty with
    | some p =>
      obtain ⟨elemIt, count⟩ := p
      obtain ⟨h1, _⟩ := tyOf_array (layouts := layouts) ha
      rw [declSlotData_of_array ha, h1]
      simp [tyBytes]
    | none =>
      simp only [ha] at hdok
      cases ht : tupleTypeOf layouts d.ty with
      | none =>
        simp only [ht, Bool.or_false, Bool.and_eq_true] at hdok
        obtain ⟨h1, _⟩ := tyOf_isPtrTy (layouts := layouts) hdok.1
        rw [declSlotData_of_isPtrTy hdok.1, h1, tyBytes_declPtrTy]
        rfl
      | some p =>
        obtain ⟨fields, size, align⟩ := p
        obtain ⟨h1, _⟩ := tyOf_tupleSpec ht
        rw [declSlotData_of_tupleSpec ht, h1]
        simp [TupleSpec.toMiniRustTy, tyBytes]

/-- `Machine::eval_statement` on `Deinit(_i)`: on a live local, the local's
bytes become `Uninit` (the encoding of an uninitialized slot); on a dead local
that `minimize`'s init block does not allocate, `eval_place` is UB. -/
theorem evalStatement_deinit {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {locals : List LocalSlot} {lm : Map Gen.LocalName Ptr} {m : Mach} {blk stmt : Nat}
    (h : FrameOk body f ctx locals lm m blk stmt) (i : Nat) (d : LocalDecl)
    (hd : body.localDecls[i]? = some d)
    (hscalar : (scalarTypeOf d.ty).isSome = true ∨ isPtrTy d.ty = true) :
    (locals[i]? ≠ some .dead → ∃ m', evalStatement m (.Deinit (.Local (localName i))) = .ok m' ∧
      FrameOk body f ctx (locals.set i .uninit) lm m' blk stmt) ∧
    (locals[i]? = some .dead → i ∉ alwaysStorageLiveLocals body →
      ∃ msg, evalStatement m (.Deinit (.Local (localName i))) = .error (.ub msg)) := by
  have hi : i < body.localDecls.length := (List.getElem?_eq_some_iff.mp hd).1
  have hspec := h.hf.2 i d hd
  have hlt := h.decl_localTy i d hd
  obtain ⟨_, slot, _, hs⟩ := h.slot_exists i hi
  refine ⟨fun hlive => ?_, fun hdead hal => ?_⟩
  · have hslive : slot ≠ .dead := fun hc => hlive (hc ▸ hs)
    obtain ⟨p, hp⟩ := h.locs.some_of_live hs hslive
    obtain ⟨k, data, hpk, _, _, _, _, hlen, hA⟩ :=
      h.locs.storage_any hd hs hp (h.declsOk d (List.mem_of_getElem? hd))
    have hplace := evalPlace_local_some h.shape i _ hspec.2 p hp
    have hne : List.replicate (tyBytes (tyOf d body.layouts)) (Gen.AbstractByte.Uninit : Byte) ≠ [] :=
      List.ne_nil_of_length_pos (by simp; exact scalar_tyBytes_pos hscalar)
    have hst := CM_store_whole hpk hA rfl rfl (List.replicate (tyBytes (tyOf d body.layouts)) .Uninit)
      hne (by simp [stackAlloc, hlen])
    refine ⟨withMem m (m.mem.memory.allocations.set k
        (stackAlloc p.addr (itOf d body.layouts) (declSlotData d .uninit body.layouts)))
        ⟨.Store, .None, p.addr, ⟨tyBytes (tyOf d body.layouts)⟩⟩,
      ?_, ?_⟩
    · simp [evalStatement, hplace, hlt.layout, LayoutStrategy.expect_size, CM.deinit, hst, withMem,
        declSlotData_uninit_of_declOk (h.declsOk d (List.mem_of_getElem? hd)), stackAlloc]
    · refine FrameOk.mk' h.hf (withMem_shape h.shape _) ?_ h.declsOk
        (h.nonScalar.set_scalar hd hscalar .uninit)
      exact h.locs.store i d hd slot .uninit hs (by simp) (declSlotOk_uninit d body.layouts) p hp k hpk
        (.inr (by simp))
  · have hq := h.locs.none_of_dead hdead hal
    exact ⟨"access to a dead local", by simp [evalStatement, evalPlace_local_none h.shape i _ hspec.2 hq]⟩

/-- `StackFrame::storage_dead` on a live local. -/
theorem storageDead_some {fr : Frame} {cm : Gen.ConcurrentMemory BM} {key : Gen.LocalName}
    {T : Gen.Type} {it : Gen.IntType} (hT : LocalTy T it) (hty : mapGet fr.func.locals key = some T)
    {p : Ptr} (hp : mapGet fr.locals key = some p) {k : Nat}
    (hpk : p.provenance = some (⟨(k : Int)⟩, ())) {a : Gen.Allocation}
    (hA : cm.memory.allocations[k]? = some a) (hlive : a.live = true) (haddr : a.addr = p.addr)
    (hkind : a.kind = .Stack) (hlen : a.data.length = tyBytes T) (halign : a.align = ⟨it.size.bytes⟩) :
    storageDead fr cm key =
      .ok ({ fr with locals := ⟨fr.locals.entries.filter (fun e => !decide (e.1 = key))⟩ },
           { cm with memory := { cm.memory with allocations := cm.memory.allocations.set k (kill a) } }) := by
  obtain ⟨hk, hAk⟩ := List.getElem?_eq_some_iff.mp hA
  simp [storageDead, mapIndex, hty, hT.layout, LayoutStrategy.expect_size,
    LayoutStrategy.expect_align, mapRemove, hp, CM.deallocate, BM.deallocate, hpk, listIndex, hk,
    hAk, hlive, haddr, hkind, Allocation.size, hlen, halign, listSet, kill]

/-- `StackFrame::storage_dead` on a dead local is a no-op on memory. -/
theorem storageDead_none {fr : Frame} {cm : Gen.ConcurrentMemory BM} {key : Gen.LocalName}
    {T : Gen.Type} {it : Gen.IntType} (hT : LocalTy T it) (hty : mapGet fr.func.locals key = some T)
    (hp : mapGet fr.locals key = none) :
    storageDead fr cm key =
      .ok ({ fr with locals := ⟨fr.locals.entries.filter (fun e => !decide (e.1 = key))⟩ }, cm) := by
  simp [storageDead, mapIndex, hty, hT.layout, LayoutStrategy.expect_size,
    LayoutStrategy.expect_align, mapRemove, hp]

/-- `StackFrame::storage_dead` on a local that is not in the locals map
changes nothing. -/
theorem storageDead_none' {fr : Frame} {cm : Gen.ConcurrentMemory BM} {key : Gen.LocalName}
    {T : Gen.Type} {it : Gen.IntType} (hT : LocalTy T it) (hty : mapGet fr.func.locals key = some T)
    (hp : mapGet fr.locals key = none) :
    storageDead fr cm key = .ok (fr, cm) := by
  rw [storageDead_none hT hty hp]
  have hnot : ∀ e ∈ fr.locals.entries, e.1 ≠ key := by
    intro e he hek
    have h1 : (mapGet ⟨fr.locals.entries⟩ e.1).isSome = true :=
      mapGet_isSome_of_mem (v := e.2) (by simpa using he)
    rw [hek] at h1
    have h2 : mapGet (⟨fr.locals.entries⟩ : Map Gen.LocalName Ptr) key = mapGet fr.locals key := rfl
    rw [h2, hp] at h1
    simp at h1
  have hf : fr.locals.entries.filter (fun e => !decide (e.1 = key)) = fr.locals.entries :=
    List.filter_eq_self.mpr (fun e he => by simp [hnot e he])
  rw [hf]

/-- `Machine::try_mutate_cur_frame` on the callee frame. -/
theorem tryMutateCurFrame_callee {m : Mach} {ctx : Ctx} {f : Gen.Function}
    {lm : Map Gen.LocalName Ptr} {blk stmt : Nat} {A : List Gen.Allocation}
    (h : Shape m ctx [ctx.caller, calleeFrameL f ctx lm blk stmt] A)
    (g : Frame → Gen.ConcurrentMemory BM → Interp (Frame × Gen.ConcurrentMemory BM))
    (lm' : Map Gen.LocalName Ptr) (cm' : Gen.ConcurrentMemory BM)
    (hg : g (calleeFrameL f ctx lm blk stmt) m.mem =
      .ok ({ calleeFrameL f ctx lm blk stmt with locals := lm' }, cm')) :
    tryMutateCurFrame m g =
      .ok { m with mem := cm', threads := [thread1 ctx [ctx.caller, calleeFrameL f ctx lm' blk stmt]] } := by
  have hact : activeThread m = .ok (thread1 ctx [ctx.caller, calleeFrameL f ctx lm blk stmt]) := by
    simp [activeThread, listIndex, h.threads, h.active]
  simp only [tryMutateCurFrame, hact, ok_bind, thread1, List.getLast?_cons_cons,
    List.getLast?_singleton, hg]
  simp [listSet, h.active, h.threads, thread1, calleeFrameL]

/-- `StorageDead` of the live local `_i`, which `minimize`'s init block does
not allocate, keeps `LocalsOk` with `_i` dead. -/
theorem LocalsOk.killLocal {body : CapturedMir} {ctx : Ctx} {locals : List LocalSlot}
    {lm : Map Gen.LocalName Ptr} {A : List Gen.Allocation} (hlo : LocalsOk body ctx locals lm A)
    (i : Nat) (d : LocalDecl) (hd : body.localDecls[i]? = some d) (slot : LocalSlot)
    (hs : locals[i]? = some slot) (hal : i ∉ alwaysStorageLiveLocals body) (p : Ptr)
    (hp : mapGet lm (localName i) = some p) (k : Nat) (hpk : p.provenance = some (⟨(k : Int)⟩, ()))
    (a : Gen.Allocation) (hA : A[k]? = some a) :
    LocalsOk body ctx (locals.set i .dead)
      ⟨lm.entries.filter (fun e => !decide (e.1 = localName i))⟩ (A.set k (kill a)) := by
  have hil : i < locals.length := (List.getElem?_eq_some_iff.mp hs).1
  obtain ⟨id0, hpid0, hbase, _, _, _, _⟩ := hlo.storage i d slot p hd hs hp
  have hid0 : id0 = k := (prov_inj id0 k).mp (hpid0.symm.trans hpk)
  subst id0
  have hmap : ∀ j, mapGet ⟨lm.entries.filter (fun e => !decide (e.1 = localName i))⟩ (localName j) =
      if j = i then none else mapGet lm (localName j) := by
    intro j
    rw [mapGet_filter_key]
    by_cases hji : j = i
    · simp [hji]
    · simp [hji, localName_inj]
  refine {
    nlocals := by simp [hlo.nlocals]
    slots := ?_
    base := ?_
    keysNodup := filter_key_nodup _ _ hlo.keysNodup
    keysLocal := fun e he => hlo.keysLocal e (List.mem_filter.mp he).1
    live := ?_
    storage := ?_
    inj := ?_
    owned := ?_ }
  · intro j dj sj hdj hsj
    by_cases hij : i = j
    · subst hij; rw [List.getElem?_set_self hil] at hsj; cases hsj; exact declSlotOk_dead dj body.layouts
    · rw [List.getElem?_set_ne hij] at hsj; exact hlo.slots j dj sj hdj hsj
  · obtain ⟨R, hR⟩ := hlo.base
    exact ⟨R.set (k - ctx.base.length) (kill a), by rw [hR, List.set_append_right _ _ hbase]⟩
  · intro j sj hsj
    rw [hmap j]
    by_cases hij : i = j
    · subst hij
      rw [List.getElem?_set_self hil] at hsj; cases hsj
      simp [hal]
    · rw [List.getElem?_set_ne hij] at hsj
      simp only [Ne.symm hij, ↓reduceIte]
      exact hlo.live j sj hsj
  · intro j dj sj q hdj hsj hq
    rw [hmap j] at hq
    by_cases hij : i = j
    · subst hij; simp at hq
    · simp only [Ne.symm hij, ↓reduceIte] at hq
      rw [List.getElem?_set_ne hij] at hsj
      refine (hlo.storage j dj sj q hdj hsj hq).congr_getElem? (fun id hqid => ?_)
      have hne : k ≠ id := fun hki => hij (hlo.inj i j p q hp hq (by subst hki; rw [hpk, hqid]))
      exact List.getElem?_set_ne hne
  · intro j j' q q' hq hq' hprov
    rw [hmap j] at hq; rw [hmap j'] at hq'
    by_cases hji : j = i
    · simp [hji] at hq
    · by_cases hj'i : j' = i
      · simp [hj'i] at hq'
      · simp only [hji, hj'i, ↓reduceIte] at hq hq'
        exact hlo.inj j j' q q' hq hq' hprov
  · intro id b hb hliveb hbid
    by_cases hki : k = id
    · subst hki
      rw [List.getElem?_set_self (List.getElem?_eq_some_iff.mp hA).1] at hb
      cases hb; simp [kill] at hliveb
    · rw [List.getElem?_set_ne hki] at hb
      obtain ⟨j, q, hq, hqid⟩ := hlo.owned id b hb hliveb hbid
      have hji : j ≠ i := by
        intro hji; subst hji
        rw [hp] at hq; cases hq
        exact hki ((prov_inj k id).mp (hpk.symm.trans hqid))
      exact ⟨j, q, by rw [hmap j]; simp [hji, hq], hqid⟩

/-- `StorageDead` of a dead local keeps `LocalsOk`. -/
theorem LocalsOk.forget {body : CapturedMir} {ctx : Ctx} {locals : List LocalSlot}
    {lm : Map Gen.LocalName Ptr} {A : List Gen.Allocation} (hlo : LocalsOk body ctx locals lm A)
    (i : Nat) (hs : locals[i]? = some .dead) (hp : mapGet lm (localName i) = none) :
    LocalsOk body ctx (locals.set i .dead)
      ⟨lm.entries.filter (fun e => !decide (e.1 = localName i))⟩ A := by
  have hset : locals.set i .dead = locals := set_self_of_getElem? locals i .dead hs
  have hmap : ∀ j, mapGet ⟨lm.entries.filter (fun e => !decide (e.1 = localName i))⟩ (localName j) =
      mapGet lm (localName j) := by
    intro j
    rw [mapGet_filter_key]
    by_cases hji : j = i
    · subst hji; simp [hp]
    · simp [hji, localName_inj]
  rw [hset]
  exact {
    nlocals := hlo.nlocals
    slots := hlo.slots
    base := hlo.base
    keysNodup := filter_key_nodup _ _ hlo.keysNodup
    keysLocal := fun e he => hlo.keysLocal e (List.mem_filter.mp he).1
    live := fun j sj hsj => by rw [hmap j]; exact hlo.live j sj hsj
    storage := fun j dj sj q hdj hsj hq => hlo.storage j dj sj q hdj hsj (by rw [← hmap j]; exact hq)
    inj := fun j j' q q' hq hq' => hlo.inj j j' q q' (by rw [← hmap j]; exact hq)
      (by rw [← hmap j']; exact hq')
    owned := fun id b hb hliveb hbid => by
      obtain ⟨j, q, hq, hqid⟩ := hlo.owned id b hb hliveb hbid
      exact ⟨j, q, by rw [hmap j]; exact hq, hqid⟩ }

/-- `StorageLive`'s allocation for the dead local `_i`, at a fresh allocation
number `A.length` and an address `addr` that is well formed for its storage
type, keeps `LocalsOk` with `_i` live and uninitialized. -/
theorem LocalsOkA.alloc' {body : CapturedMir} {ctx : Ctx} {al al' : List Nat}
    {locals : List LocalSlot} {lm : Map Gen.LocalName Ptr} {A : List Gen.Allocation}
    (hlo : LocalsOkA body ctx al locals lm A)
    (i : Nat) (d : LocalDecl) (hd : body.localDecls[i]? = some d) (hs : locals[i]? = some .dead)
    (hp : mapGet lm (localName i) = none) (addr : Int)
    (haddr : AddrOk addr (itOf d body.layouts))
    (haddrMax : addr + (tyBytes (tyOf d body.layouts) : Int) < 2 ^ 64)
    (hcls : AddrClass addr (tyBytes (tyOf d body.layouts)))
    (ns : LocalSlot) (hns : DeclSlotOk d ns body.layouts)
    (hns_np : isPtrTy d.ty = false ∨ (∀ pv, ns ≠ .init (.ptr pv 8)))
    (hlive : ns ≠ .dead ∨ i ∈ al') (hal : ∀ j, j ≠ i → (j ∈ al' ↔ j ∈ al)) :
    LocalsOkA body ctx al' (locals.set i ns)
      ⟨lm.entries ++ [(localName i, { addr := addr, provenance := some (⟨(A.length : Int)⟩, ()) })]⟩
      (A ++ [stackAlloc addr (itOf d body.layouts) (declSlotData d ns body.layouts)]) := by
  have hil : i < locals.length := (List.getElem?_eq_some_iff.mp hs).1
  have hin : i < body.localDecls.length := (List.getElem?_eq_some_iff.mp hd).1
  have hnot : ∀ e ∈ lm.entries, e.1 ≠ localName i := by
    intro e he hei
    obtain ⟨k', v'⟩ := e
    simp only at hei
    subst hei
    have := mapGet_isSome_of_mem (es := lm.entries) he
    rw [hp] at this
    simp at this
  let newPtr : Ptr := { addr := addr, provenance := some (⟨(A.length : Int)⟩, ()) }
  have hmap : ∀ j, mapGet ⟨lm.entries ++ [(localName i, newPtr)]⟩ (localName j) =
      if j = i then some newPtr else mapGet lm (localName j) := by
    intro j
    rw [mapGet_append_single _ _ _ _ hnot]
    by_cases hji : j = i
    · simp [hji]
    · simp [hji, localName_inj]
  have hidlt : ∀ (j : Nat) q, mapGet lm (localName j) = some q →
      ∃ id : Nat, q.provenance = some (⟨(id : Int)⟩, ()) ∧ id < A.length := by
    intro j q hq
    obtain ⟨e, he⟩ : ∃ e, e ∈ lm.entries ∧ e.1 = localName j := ⟨(localName j, q), mapGet_mem hq, rfl⟩
    obtain ⟨j', hj', hej⟩ := hlo.keysLocal e he.1
    rw [he.2, localName_inj] at hej
    subst hej
    obtain ⟨dj, hdj⟩ : ∃ dj, body.localDecls[j]? = some dj := ⟨_, List.getElem?_eq_getElem hj'⟩
    obtain ⟨sj, hsj⟩ : ∃ sj, locals[j]? = some sj :=
      ⟨_, List.getElem?_eq_getElem (by rw [hlo.nlocals]; exact hj')⟩
    obtain ⟨id, hqid, _, _, _, _, hA'⟩ := hlo.storage j dj sj q hdj hsj hq
    refine ⟨id, hqid, ?_⟩
    cases hpj : isPtrTy dj.ty with
    | false =>
      simp only [hpj, Bool.false_eq_true, ↓reduceIte] at hA'
      exact (List.getElem?_eq_some_iff.mp hA').1
    | true =>
      simp only [hpj, ↓reduceIte] at hA'
      split at hA'
      · obtain ⟨_, _, _, _, hAid⟩ := hA'
        exact (List.getElem?_eq_some_iff.mp hAid).1
      · exact (List.getElem?_eq_some_iff.mp hA').1
  refine {
    nlocals := by simp [hlo.nlocals]
    slots := ?_
    base := ?_
    keysNodup := ?_
    keysLocal := ?_
    live := ?_
    storage := ?_
    inj := ?_
    owned := ?_ }
  · intro j dj sj hdj hsj
    by_cases hij : i = j
    · subst hij; rw [List.getElem?_set_self hil] at hsj; cases hsj; rw [hd] at hdj; cases hdj; exact hns
    · rw [List.getElem?_set_ne hij] at hsj; exact hlo.slots j dj sj hdj hsj
  · obtain ⟨R, hR⟩ := hlo.base
    exact ⟨R ++ [stackAlloc addr (itOf d body.layouts) (declSlotData d ns body.layouts)],
      by rw [hR, List.append_assoc]⟩
  · rw [List.map_append, List.nodup_append]
    refine ⟨hlo.keysNodup, by simp, ?_⟩
    intro x hx y hy
    simp at hy; subst hy
    simp only [List.mem_map] at hx
    obtain ⟨e, he, rfl⟩ := hx
    exact hnot e he
  · intro e he
    rcases List.mem_append.mp he with he | he
    · exact hlo.keysLocal e he
    · simp at he; subst he; exact ⟨i, hin, rfl⟩
  · intro j sj hsj
    rw [hmap j]
    by_cases hij : i = j
    · subst hij
      rw [List.getElem?_set_self hil] at hsj; cases hsj
      simpa using hlive
    · rw [List.getElem?_set_ne hij] at hsj
      simp only [Ne.symm hij, ↓reduceIte]
      rw [hal j (Ne.symm hij)]
      exact hlo.live j sj hsj
  · intro j dj sj q hdj hsj hq
    rw [hmap j] at hq
    by_cases hij : i = j
    · subst hij
      simp at hq; subst hq
      rw [hd] at hdj; cases hdj
      rw [List.getElem?_set_self hil] at hsj; cases hsj
      refine ⟨A.length, rfl, ?_, haddr, haddrMax, hcls, ?_⟩
      · obtain ⟨R, hR⟩ := hlo.base
        rw [hR, List.length_append]; omega
      · cases hp_ty : isPtrTy d.ty with
        | false => simp [newPtr]
        | true =>
          simp only [↓reduceIte]
          rcases hns_np with hfalse | hnotPtr
          · rw [hp_ty] at hfalse; cases hfalse
          · split
            · next pv => exact False.elim (hnotPtr pv rfl)
            · simp [newPtr]
    · simp only [Ne.symm hij, ↓reduceIte] at hq
      rw [List.getElem?_set_ne hij] at hsj
      refine (hlo.storage j dj sj q hdj hsj hq).congr_getElem? (fun id hqid => ?_)
      obtain ⟨id', hqid', hlt⟩ := hidlt j q hq
      have heq : id' = id := (prov_inj id' id).mp (hqid'.symm.trans hqid)
      subst id'
      exact List.getElem?_append_left hlt
  · intro j j' q q' hq hq' hprov
    rw [hmap j] at hq; rw [hmap j'] at hq'
    by_cases hji : j = i
    · by_cases hj'i : j' = i
      · rw [hji, hj'i]
      · simp only [hji, ↓reduceIte, Option.some.injEq] at hq
        simp only [hj'i, ↓reduceIte] at hq'
        subst hq
        obtain ⟨id, hqid, hlt⟩ := hidlt j' q' hq'
        rw [hqid] at hprov
        have := (prov_inj _ _).mp (by simpa [newPtr] using hprov)
        omega
    · by_cases hj'i : j' = i
      · simp only [hj'i, ↓reduceIte, Option.some.injEq] at hq'
        simp only [hji, ↓reduceIte] at hq
        subst hq'
        obtain ⟨id, hqid, hlt⟩ := hidlt j q hq
        rw [hqid] at hprov
        have := (prov_inj _ _).mp (by simpa [newPtr] using hprov)
        omega
      · simp only [hji, hj'i, ↓reduceIte] at hq hq'
        exact hlo.inj j j' q q' hq hq' hprov
  · intro id b hb hliveb hbid
    by_cases hid : id < A.length
    · rw [List.getElem?_append_left hid] at hb
      obtain ⟨j, q, hq, hqid⟩ := hlo.owned id b hb hliveb hbid
      have hji : j ≠ i := by intro hji; subst hji; rw [hp] at hq; cases hq
      exact ⟨j, q, by rw [hmap j]; simp [hji, hq], hqid⟩
    · have hidA : id = A.length := by
        have := (List.getElem?_eq_some_iff.mp hb).1
        simp at this; omega
      subst hidA
      exact ⟨i, newPtr, by rw [hmap i]; simp, rfl⟩

/-- `StorageLive` of the dead local `_i` that is not in the locals map, as the
body's `StorageLive(_i)` does it: `_i` becomes uninitialized. -/
theorem LocalsOkA.alloc {body : CapturedMir} {ctx : Ctx} {al : List Nat}
    {locals : List LocalSlot} {lm : Map Gen.LocalName Ptr} {A : List Gen.Allocation}
    (hlo : LocalsOkA body ctx al locals lm A)
    (i : Nat) (d : LocalDecl) (hd : body.localDecls[i]? = some d) (hs : locals[i]? = some .dead)
    (hp : mapGet lm (localName i) = none) (addr : Int)
    (haddr : AddrOk addr (itOf d body.layouts))
    (haddrMax : addr + (tyBytes (tyOf d body.layouts) : Int) < 2 ^ 64)
    (hcls : AddrClass addr (tyBytes (tyOf d body.layouts))) :
    LocalsOkA body ctx al (locals.set i .uninit)
      ⟨lm.entries ++ [(localName i, { addr := addr, provenance := some (⟨(A.length : Int)⟩, ()) })]⟩
      (A ++ [stackAlloc addr (itOf d body.layouts) (declSlotData d .uninit body.layouts)]) :=
  LocalsOkA.alloc' hlo i d hd hs hp addr haddr haddrMax hcls .uninit
    (declSlotOk_uninit d body.layouts) (.inr (by simp)) (.inl (by simp)) (fun _ _ => Iff.rfl)

/-- `StorageLive` of the dead local `_i` that is not in the locals map, as the
body's `StorageLive(_i)` does it: `_i` becomes uninitialized. -/
theorem LocalsOk.alloc {body : CapturedMir} {ctx : Ctx} {locals : List LocalSlot}
    {lm : Map Gen.LocalName Ptr} {A : List Gen.Allocation} (hlo : LocalsOk body ctx locals lm A)
    (i : Nat) (d : LocalDecl) (hd : body.localDecls[i]? = some d) (hs : locals[i]? = some .dead)
    (hp : mapGet lm (localName i) = none) (addr : Int)
    (haddr : AddrOk addr (itOf d body.layouts))
    (haddrMax : addr + (tyBytes (tyOf d body.layouts) : Int) < 2 ^ 64)
    (hcls : AddrClass addr (tyBytes (tyOf d body.layouts))) :
    LocalsOk body ctx (locals.set i .uninit)
      ⟨lm.entries ++ [(localName i, { addr := addr, provenance := some (⟨(A.length : Int)⟩, ()) })]⟩
      (A ++ [stackAlloc addr (itOf d body.layouts) (declSlotData d .uninit body.layouts)]) :=
  LocalsOkA.alloc hlo i d hd hs hp addr haddr haddrMax hcls

/-! ### The first-fit address of `StorageLive` -/

theorem overlaps_low (a : Gen.Allocation) (k : Nat) (size : Size)
    (h : a.addr + (a.data.length : Int) < 2 ^ 32) :
    Allocation.overlaps a (allocCandidate k) size = false := by
  -- `Address` arithmetic is `Int` arithmetic, but `omega` only recognizes
  -- it once the `Address` abbreviation is unfolded.
  unfold Allocation.overlaps Allocation.size allocCandidate
  unfold Gen.Address at h ⊢
  dsimp only
  split
  · exact decide_eq_false (by omega)
  · exfalso; omega

theorem overlaps_cand (a : Gen.Allocation) (j k : Nat) (size : Size)
    (hj : a.addr = allocCandidate j) (hne : j ≠ k) (hla : a.data.length ≤ 2 ^ 32)
    (hs : size.bytes ≤ 2 ^ 32) :
    Allocation.overlaps a (allocCandidate k) size = false := by
  unfold Allocation.overlaps Allocation.size allocCandidate at *
  unfold Gen.Address at hj ⊢
  dsimp only
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · split
    · exact decide_eq_false (by omega)
    · exfalso; omega
  · split
    · exact decide_eq_false (by omega)
    · exfalso; omega

theorem inBounds_unsigned_ptrSize_iff (x : Int) :
    inBounds x .Unsigned x86_64.PTR_SIZE = true ↔ 0 ≤ x ∧ x < 2 ^ 64 := by
  have hb : (2 : Int) ^ Size.bits x86_64.PTR_SIZE = 2 ^ 64 := rfl
  simp only [inBounds, hb, decide_eq_true_eq, Bool.and_eq_true]

theorem allocAddrOk_cand (mem : BM) (size : Size) (align : Align) (k : Nat) (hk : k < 2 ^ 31)
    (hsize : size.bytes ≤ 32) (halign : GoodSize align.bytes)
    (hfree : ∀ a ∈ mem.allocations, a.live = true → Allocation.overlaps a (allocCandidate k) size = false) :
    BM.allocAddrOk mem size align (allocCandidate k) = true := by
  have hpos : ¬ (allocCandidate k ≤ 0) := by simp only [allocCandidate]; omega
  have hal : Align.is_aligned align (allocCandidate k) = true := by
    simp only [Align.is_aligned, allocCandidate, beq_iff_eq]
    rcases halign with h | h | h | h | h <;> rw [h] <;> omega
  have hin : inBounds (allocCandidate k + (size.bytes : Int)) .Unsigned x86_64.PTR_SIZE = true := by
    rw [inBounds_unsigned_ptrSize_iff]
    simp only [allocCandidate]
    omega
  have hany : mem.allocations.any (fun a => a.live && Allocation.overlaps a (allocCandidate k) size) =
      false := by
    rw [List.any_eq_false]
    intro a ha
    cases hl : a.live with
    | false => simp
    | true => simp [hfree a ha hl]
  simp [BM.allocAddrOk, hpos, hal, hin, hany]

theorem firstFitAddr_spec (mem : BM) (size : Size) (align : Align) :
    ∀ (fuel k0 k : Nat), k0 ≤ k → k < k0 + fuel →
      BM.allocAddrOk mem size align (allocCandidate k) = true →
      ∃ k', k0 ≤ k' ∧ k' ≤ k ∧ firstFitAddr mem size align fuel k0 = some (allocCandidate k') ∧
        BM.allocAddrOk mem size align (allocCandidate k') = true := by
  intro fuel
  induction fuel with
  | zero => intro k0 k h1 h2; omega
  | succ fuel ih =>
    intro k0 k h1 h2 hok
    simp only [firstFitAddr]
    by_cases h0 : BM.allocAddrOk mem size align (allocCandidate k0) = true
    · exact ⟨k0, Nat.le_refl _, h1, by simp [h0], h0⟩
    · simp only [h0, Bool.false_eq_true, ↓reduceIte]
      have hk0 : k0 ≠ k := by intro h; subst h; exact h0 hok
      obtain ⟨k', h1', h2', h3', h4'⟩ := ih (k0 + 1) k (by omega) (by omega) hok
      exact ⟨k', by omega, h2', h3', h4'⟩

theorem exists_not_mem_le (L : List Nat) : ∃ k, k ≤ L.length ∧ k ∉ L := by
  apply Classical.byContradiction
  intro hne
  have hsub : List.range (L.length + 1) ⊆ L := by
    intro x hx
    rw [List.mem_range] at hx
    apply Classical.byContradiction
    intro hxL
    exact hne ⟨x, by omega, hxL⟩
  have := List.Nodup.length_le_of_subset List.nodup_range hsub
  simp at this
  omega

/-- The candidate number of an address `(k + 1) * 2^32`. -/
def candIdx (addr : Int) : Nat := (addr / 2 ^ 32).toNat - 1

theorem candIdx_cand (k : Nat) : candIdx (allocCandidate k) = k := by
  simp only [candIdx, allocCandidate]
  omega

/-- A scalar declaration's `tyOf` does not depend on the layout table. -/
theorem scalarTypeOf_tyOf_layouts {d : LocalDecl} (L : Layout.LayoutTable)
    (h : scalarTypeOf d.ty = some (tyOf d)) : scalarTypeOf d.ty = some (tyOf d L) := by
  rw [tyOf_of_scalarTypeOf (layouts := L) h]; exact h

/-- Under `LocalsOkA` for a body whose locals are all scalars, the allocations
`A` stay `BaseCandBounded` with one extra candidate per local: every live
allocation above `base` is a local's (at most `32`-byte) storage, below `2^32`
or at a first-fit candidate address. -/
theorem LocalsOkA.baseCandBounded_of_scalar {body : CapturedMir} {ctx : Ctx} {al : List Nat}
    {locals : List LocalSlot} {lm : Map Gen.LocalName Ptr} {A : List Gen.Allocation}
    {bound : Nat} (hlo : LocalsOkA body ctx al locals lm A)
    (hbase : BaseCandBounded ctx.base bound)
    (hdecls : ∀ (i : Nat) d, body.localDecls[i]? = some d → scalarTypeOf d.ty = some (tyOf d)) :
    BaseCandBounded A (bound + body.localDecls.length) := by
  obtain ⟨cands, hcands, hbaseA⟩ := hbase
  refine ⟨cands ++ lm.entries.map (fun e => candIdx e.2.addr), ?_, ?_⟩
  · simp only [List.length_append, List.length_map]
    have := hlo.entries_length
    omega
  · intro a ha hlive
    obtain ⟨id, hid⟩ := List.getElem_of_mem ha
    have hAid : A[id]? = some a := by rw [List.getElem?_eq_getElem hid.1]; simp [hid.2]
    obtain ⟨R, hR⟩ := hlo.base
    by_cases hidb : id < ctx.base.length
    · have hab : a ∈ ctx.base := by
        have : (ctx.base ++ R)[id]? = some a := hR ▸ hAid
        rw [List.getElem?_append_left hidb] at this
        exact List.mem_of_getElem? this
      rcases hbaseA a hab hlive with hlow | ⟨j, hjc, hjaddr, hjlen⟩
      · exact .inl hlow
      · exact .inr ⟨j, List.mem_append_left _ hjc, hjaddr, hjlen⟩
    · obtain ⟨i, q, hq, hqid⟩ := hlo.owned id a hAid hlive (by omega)
      have hmemq := mapGet_mem hq
      obtain ⟨i', hi', hei⟩ := hlo.keysLocal _ hmemq
      simp only [localName_inj] at hei; subst hei
      obtain ⟨d, hd⟩ : ∃ d, body.localDecls[i]? = some d := ⟨_, List.getElem?_eq_getElem hi'⟩
      obtain ⟨sl, hsl⟩ : ∃ sl, locals[i]? = some sl :=
        ⟨_, List.getElem?_eq_getElem (by rw [hlo.nlocals]; exact hi')⟩
      have hsc := scalarTypeOf_tyOf_layouts body.layouts (hdecls i d hd)
      obtain ⟨_, _, _, hcls, hAq⟩ :=
        hlo.storage_id hd hsl hq hqid (isPtrTy_false_of_scalarTypeOf hsc)
      rw [hAid] at hAq; cases hAq
      have hlen := declSlotData_length hsc sl
      have hle : tyBytes (tyOf d body.layouts) ≤ 32 := scalar_tyBytes_le (.inl (by simp [hsc]))
      rcases hcls with hlow | ⟨_, j, hj⟩
      · exact .inl (by simp only [stackAlloc]; rw [hlen]; exact hlow)
      · refine .inr ⟨j, List.mem_append_right _ ?_, by simp [stackAlloc, hj],
          by simp only [stackAlloc]; rw [hlen]; exact hle⟩
        exact List.mem_map.mpr ⟨(localName i, q), hmemq, by simp [hj, candIdx_cand]⟩

/-- Every declaration of a body whose locals are all scalars is `localDeclOk`. -/
theorem localDeclOk_of_scalar {body : CapturedMir}
    (hdecls : ∀ (i : Nat) d, body.localDecls[i]? = some d → scalarTypeOf d.ty = some (tyOf d)) :
    ∀ d ∈ body.localDecls, localDeclOk body.layouts d = true := by
  intro d hd
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hd
  simp [localDeclOk, hdecls i d hi]

/-- `NonScalarLive` holds vacuously in a body whose locals are all scalars. -/
theorem NonScalarLive.of_scalar {body : CapturedMir} {locals : List LocalSlot}
    {lm : Map Gen.LocalName Ptr}
    (hdecls : ∀ (i : Nat) d, body.localDecls[i]? = some d → scalarTypeOf d.ty = some (tyOf d)) :
    NonScalarLive body locals lm := by
  intro i d _ hd _ hnone _
  rw [hdecls i d hd] at hnone
  cases hnone

/-- Under `LocalsOkA`, `NonScalarLive`, and `BaseCandBounded ctx.base bound`,
when `bound + body.localDecls.length < 2^31`, some first-fit candidate below
`2^31` is free of every live allocation in `A`. -/
theorem LocalsOkA.free_candidate_cand_ns {body : CapturedMir} {ctx : Ctx} {al : List Nat}
    {locals : List LocalSlot} {lm : Map Gen.LocalName Ptr} {A : List Gen.Allocation}
    {bound : Nat} (hlo : LocalsOkA body ctx al locals lm A)
    (hns : NonScalarLive body locals lm)
    (hbase : BaseCandBounded ctx.base bound) (hn : bound + body.localDecls.length < 2 ^ 31)
    (size : Size) (hsize : size.bytes ≤ 32)
    (hdeclsOk : ∀ d ∈ body.localDecls, localDeclOk body.layouts d = true) :
    ∃ k, k < 2 ^ 31 ∧
      ∀ a ∈ A, a.live = true → Allocation.overlaps a (allocCandidate k) size = false := by
  obtain ⟨cands, hcands, hbaseA⟩ := hbase
  let L := cands ++ lm.entries.map (fun e => candIdx e.2.addr)
  obtain ⟨k, hkL, hknot⟩ := exists_not_mem_le L
  have hLlen : L.length ≤ bound + body.localDecls.length := by
    simp only [L, List.length_append, List.length_map]
    have := hlo.entries_length
    omega
  refine ⟨k, by omega, ?_⟩
  intro a ha hlive
  obtain ⟨id, hid⟩ := List.getElem_of_mem ha
  have hAid : A[id]? = some a := by rw [List.getElem?_eq_getElem hid.1]; simp [hid.2]
  obtain ⟨R, hR⟩ := hlo.base
  by_cases hidb : id < ctx.base.length
  · have hab : a ∈ ctx.base := by
      have : (ctx.base ++ R)[id]? = some a := hR ▸ hAid
      rw [List.getElem?_append_left hidb] at this
      exact List.mem_of_getElem? this
    rcases hbaseA a hab hlive with hlow | ⟨j, hjc, hjaddr, hjlen⟩
    · exact overlaps_low a k size hlow
    · have hjk : j ≠ k := by
        intro hjk; subst hjk
        exact hknot (List.mem_append_left _ hjc)
      exact overlaps_cand a j k size hjaddr hjk (by omega) (by omega)
  · obtain ⟨i, q, hq, hqid⟩ := hlo.owned id a hAid hlive (by omega)
    have hmemq := mapGet_mem hq
    obtain ⟨i', hi', hei⟩ := hlo.keysLocal _ hmemq
    simp only [localName_inj] at hei; subst hei
    obtain ⟨d, hd⟩ : ∃ d, body.localDecls[i]? = some d := ⟨_, List.getElem?_eq_getElem hi'⟩
    obtain ⟨sl, hsl⟩ : ∃ sl, locals[i]? = some sl :=
      ⟨_, List.getElem?_eq_getElem (by rw [hlo.nlocals]; exact hi')⟩
    obtain ⟨data, _, _, _, hcls, hlen, hAq⟩ :=
      hlo.storage_any_id hd hsl hq hqid (hdeclsOk d (List.mem_of_getElem? hd))
    rw [hAid] at hAq
    injection hAq with hAq'
    subst a
    have hcand : ∀ (j : Nat), q.addr = allocCandidate j → j ≠ k := by
      intro j hj hjk; subst hjk
      apply hknot
      apply List.mem_append_right
      simp only [List.mem_map]
      exact ⟨(localName i, q), hmemq, by simp [hj, candIdx_cand]⟩
    cases hsc : scalarTypeOf d.ty with
    | none =>
      cases hp_ty : isPtrTy d.ty with
      | false =>
        have hlow := (hns i d sl hd hsl hsc hp_ty).2 q hq
        exact overlaps_low _ k size (by simp only [stackAlloc]; rw [hlen]; exact hlow)
      | true =>
        have hle : tyBytes (tyOf d body.layouts) ≤ 32 := scalar_tyBytes_le (.inr hp_ty)
        rcases hcls with hlow | ⟨_, j, hj⟩
        · exact overlaps_low _ k size (by simp only [stackAlloc]; rw [hlen]; exact hlow)
        · exact overlaps_cand _ j k size (by simp [stackAlloc, hj]) (hcand j hj)
            (by simp only [stackAlloc]; rw [hlen]; omega) (by omega)
    | some T =>
      have hle : tyBytes (tyOf d body.layouts) ≤ 32 := scalar_tyBytes_le (.inl (by simp [hsc]))
      rcases hcls with hlow | ⟨_, j, hj⟩
      · exact overlaps_low _ k size (by simp only [stackAlloc]; rw [hlen]; exact hlow)
      · exact overlaps_cand _ j k size (by simp [stackAlloc, hj]) (hcand j hj)
          (by simp only [stackAlloc]; rw [hlen]; omega) (by omega)

/-- Under `LocalsOkA` and `BaseCandBounded ctx.base bound`, when
`bound + body.localDecls.length < 2^31`, some first-fit candidate below `2^31`
is free of every live allocation in `A`
(`free_candidate_cand_ns` for a body whose locals are all scalars). -/
theorem LocalsOkA.free_candidate_cand {body : CapturedMir} {ctx : Ctx} {al : List Nat}
    {locals : List LocalSlot} {lm : Map Gen.LocalName Ptr} {A : List Gen.Allocation}
    {bound : Nat} (hlo : LocalsOkA body ctx al locals lm A)
    (hbase : BaseCandBounded ctx.base bound) (hn : bound + body.localDecls.length < 2 ^ 31)
    (size : Size) (hsize : size.bytes ≤ 32)
    (hdecls : ∀ (i : Nat) d, body.localDecls[i]? = some d → scalarTypeOf d.ty = some (tyOf d)) :
    ∃ k, k < 2 ^ 31 ∧
      ∀ a ∈ A, a.live = true → Allocation.overlaps a (allocCandidate k) size = false :=
  hlo.free_candidate_cand_ns (NonScalarLive.of_scalar hdecls) hbase hn size hsize
    (localDeclOk_of_scalar hdecls)

/-- Under `LocalsOk` and `BaseLow`, some first-fit candidate below `2^31` is
free: the caller's allocations lie below `2^32`, and each candidate that a
live callee allocation occupies belongs to one entry of the locals map, which
has at most `localDecls.length < 2^31` entries
(`free_candidate_cand_ns` at `bound = 0`). -/
theorem LocalsOkA.free_candidate {body : CapturedMir} {ctx : Ctx} {al : List Nat}
    {locals : List LocalSlot} {lm : Map Gen.LocalName Ptr} {A : List Gen.Allocation}
    (hlo : LocalsOkA body ctx al locals lm A)
    (hns : NonScalarLive body locals lm)
    (hbaseLow : BaseLow ctx) (hn : body.localDecls.length < 2 ^ 31) (size : Size)
    (hsize : size.bytes ≤ 32)
    (hdeclsOk : ∀ d ∈ body.localDecls, localDeclOk body.layouts d = true) :
    ∃ k, k < 2 ^ 31 ∧
      ∀ a ∈ A, a.live = true → Allocation.overlaps a (allocCandidate k) size = false :=
  hlo.free_candidate_cand_ns hns hbaseLow.toBaseCandBounded (by omega) size hsize hdeclsOk

/-- `BasicMemory::allocate` of a callee local of at most `32` bytes under
`LocalsOkA`, `NonScalarLive`, and `BaseCandBounded`. -/
theorem BM_allocate_local_cand_ns {body : CapturedMir} {ctx : Ctx} {al : List Nat}
    {locals : List LocalSlot} {lm : Map Gen.LocalName Ptr} {mem : BM} {bound : Nat}
    (hlo : LocalsOkA body ctx al locals lm mem.allocations)
    (hns : NonScalarLive body locals lm)
    (hbase : BaseCandBounded ctx.base bound) (hn : bound + body.localDecls.length < 2 ^ 31)
    (hdeclsOk : ∀ d ∈ body.localDecls, localDeclOk body.layouts d = true)
    {T : Gen.Type} {it : Gen.IntType} (hT : LocalTy T it) (hle : tyBytes T ≤ 32) :
    ∃ k, k < 2 ^ 31 ∧
      BM.allocate mem .Stack ⟨tyBytes T⟩ ⟨it.size.bytes⟩ =
        .ok ({ addr := allocCandidate k, provenance := some (⟨(mem.allocations.length : Int)⟩, ()) },
             { mem with allocations := mem.allocations ++
                [{ addr := allocCandidate k, align := ⟨it.size.bytes⟩, kind := .Stack, live := true,
                   data := List.replicate (tyBytes T) .Uninit, extra := () }] }) ∧
      AddrOk (allocCandidate k) it ∧ allocCandidate k + (tyBytes T : Int) < 2 ^ 64 := by
  obtain ⟨k0, hk0, hfree⟩ := hlo.free_candidate_cand_ns hns hbase hn ⟨tyBytes T⟩ hle hdeclsOk
  have hok0 := allocAddrOk_cand mem ⟨tyBytes T⟩ ⟨it.size.bytes⟩ k0 hk0 hle hT.good hfree
  obtain ⟨k, _, hkk0, hff, hok⟩ := firstFitAddr_spec mem ⟨tyBytes T⟩ ⟨it.size.bytes⟩
    (2 ^ 32 - 1) 0 k0 (Nat.zero_le _) (by omega) hok0
  have hvalid : x86_64.valid_size ⟨tyBytes T⟩ = true := by
    have hb : (2 : Int) ^ (Size.bits x86_64.PTR_SIZE - 1) = 2 ^ 63 := rfl
    simp only [x86_64.valid_size, inBounds, hb, decide_eq_true_eq, Bool.and_eq_true]
    constructor <;> omega
  have hpick : BM.pickAddr mem ⟨tyBytes T⟩ ⟨it.size.bytes⟩ = some (allocCandidate k) := hff
  have hgs : it.size.bytes ≤ 16 := by rcases hT.good with h | h | h | h | h <;> omega
  refine ⟨k, by omega, by simp [BM.allocate, hvalid, hpick], ?_, ?_⟩
  · simp only [BM.allocAddrOk] at hok
    split at hok
    · simp at hok
    · next hpos =>
      split at hok
      · simp at hok
      · next hal =>
        simp only [Bool.not_eq_true', Bool.not_eq_false] at hal
        simp only [Align.is_aligned, beq_iff_eq] at hal
        refine ⟨hal, ?_, ?_⟩
        · simp only [allocCandidate]; omega
        · simp only [allocCandidate]; omega
  · simp only [allocCandidate]
    omega

/-- `BasicMemory::allocate` of a callee local under `LocalsOkA` and
`BaseCandBounded`
(`BM_allocate_local_cand_ns` for a body whose locals are all scalars). -/
theorem BM_allocate_local_cand {body : CapturedMir} {ctx : Ctx} {al : List Nat}
    {locals : List LocalSlot} {lm : Map Gen.LocalName Ptr} {mem : BM} {bound : Nat}
    (hlo : LocalsOkA body ctx al locals lm mem.allocations)
    (hbase : BaseCandBounded ctx.base bound) (hn : bound + body.localDecls.length < 2 ^ 31)
    (hdecls : ∀ (i : Nat) d, body.localDecls[i]? = some d → scalarTypeOf d.ty = some (tyOf d))
    {T : Gen.Type} {it : Gen.IntType} (hT : LocalTy T it) (hle : tyBytes T ≤ 32) :
    ∃ k, k < 2 ^ 31 ∧
      BM.allocate mem .Stack ⟨tyBytes T⟩ ⟨it.size.bytes⟩ =
        .ok ({ addr := allocCandidate k, provenance := some (⟨(mem.allocations.length : Int)⟩, ()) },
             { mem with allocations := mem.allocations ++
                [{ addr := allocCandidate k, align := ⟨it.size.bytes⟩, kind := .Stack, live := true,
                   data := List.replicate (tyBytes T) .Uninit, extra := () }] }) ∧
      AddrOk (allocCandidate k) it ∧ allocCandidate k + (tyBytes T : Int) < 2 ^ 64 :=
  BM_allocate_local_cand_ns hlo (NonScalarLive.of_scalar hdecls) hbase hn
    (localDeclOk_of_scalar hdecls) hT hle

/-- `BasicMemory::allocate` of a callee local under `LocalsOk` and `BaseLow`
succeeds at a free first-fit candidate
(`BM_allocate_local_cand_ns` at `bound = 0`; `hT` already bounds the alignment,
so the size bound `_hsz` is not needed). -/
theorem BM_allocate_local {body : CapturedMir} {ctx : Ctx} {al : List Nat}
    {locals : List LocalSlot} {lm : Map Gen.LocalName Ptr} {mem : BM}
    (hlo : LocalsOkA body ctx al locals lm mem.allocations)
    (hns : NonScalarLive body locals lm)
    (hbaseLow : BaseLow ctx) (hn : body.localDecls.length < 2 ^ 31)
    (hdeclsOk : ∀ d ∈ body.localDecls, localDeclOk body.layouts d = true)
    {T : Gen.Type} {it : Gen.IntType} (hT : LocalTy T it)
    (hle : tyBytes T ≤ 32) :
    ∃ k, k < 2 ^ 31 ∧
      BM.allocate mem .Stack ⟨tyBytes T⟩ ⟨it.size.bytes⟩ =
        .ok ({ addr := allocCandidate k, provenance := some (⟨(mem.allocations.length : Int)⟩, ()) },
             { mem with allocations := mem.allocations ++
                [{ addr := allocCandidate k, align := ⟨it.size.bytes⟩, kind := .Stack, live := true,
                   data := List.replicate (tyBytes T) .Uninit, extra := () }] }) ∧
      AddrOk (allocCandidate k) it ∧ allocCandidate k + (tyBytes T : Int) < 2 ^ 64 :=
  BM_allocate_local_cand_ns hlo hns hbaseLow.toBaseCandBounded (by omega) hdeclsOk hT hle

/-- `Machine::eval_statement` on `StorageDead(_i)` for a local that
`minimize`'s init block does not allocate: the local leaves the locals map
and its allocation (if any) is deallocated. -/
theorem evalStatement_storageDead {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {locals : List LocalSlot} {lm : Map Gen.LocalName Ptr} {m : Mach} {blk stmt : Nat}
    (h : FrameOk body f ctx locals lm m blk stmt) (i : Nat) (d : LocalDecl)
    (hd : body.localDecls[i]? = some d) (hal : i ∉ alwaysStorageLiveLocals body)
    (hscalar : (scalarTypeOf d.ty).isSome = true ∨ isPtrTy d.ty = true) :
    ∃ m', evalStatement m (.StorageDead (localName i)) = .ok m' ∧
      FrameOk body f ctx (locals.set i .dead)
        ⟨lm.entries.filter (fun e => !decide (e.1 = localName i))⟩ m' blk stmt := by
  have hi : i < body.localDecls.length := (List.getElem?_eq_some_iff.mp hd).1
  have hspec := h.hf.2 i d hd
  have hlt := h.decl_localTy i d hd
  obtain ⟨_, slot, _, hs⟩ := h.slot_exists i hi
  cases hp : mapGet lm (localName i) with
  | none =>
    have hdead := h.locs.dead_of_none hs hp
    subst hdead
    have hsd := storageDead_none (fr := calleeFrameL f ctx lm blk stmt) (cm := m.mem) hlt hspec.2
      (by simpa [calleeFrameL] using hp)
    have htm := tryMutateCurFrame_callee h.shape
      (fun fr cm => storageDead fr cm (localName i)) _ _ hsd
    refine ⟨_, by simp only [evalStatement]; exact htm, ?_⟩
    exact FrameOk.mk' h.hf ⟨rfl, h.shape.active, rfl⟩ (h.locs.forget i hs hp) h.declsOk
      (h.nonScalar.filter_scalar hd hscalar .dead)
  | some p =>
    obtain ⟨k, data, hpk, _, _, _, _, hlen, hA⟩ :=
      h.locs.storage_any hd hs hp (h.declsOk d (List.mem_of_getElem? hd))
    have hsd := storageDead_some (fr := calleeFrameL f ctx lm blk stmt) (cm := m.mem) hlt hspec.2
      (by simpa [calleeFrameL] using hp) hpk hA rfl rfl rfl hlen rfl
    have htm := tryMutateCurFrame_callee h.shape
      (fun fr cm => storageDead fr cm (localName i)) _ _ hsd
    refine ⟨_, by simp only [evalStatement]; exact htm, ?_⟩
    exact FrameOk.mk' h.hf ⟨rfl, h.shape.active, rfl⟩
      (h.locs.killLocal i d hd slot hs hal p hp k hpk _ hA) h.declsOk
      (h.nonScalar.filter_scalar hd hscalar .dead)

/-- `Machine::eval_statement` on `StorageLive(_i)` under `BaseCandBounded` for
a local that `minimize`'s init block does not allocate: `storage_dead` of the
old storage (if any), then a fresh `Stack` allocation at the first free
candidate address of `BM.pickAddr`, which exists because the caller's live
allocations occupy at most `bound` candidates and `bound` plus the number of
locals stays below `2^31`. The locals map changes only at `_i`. -/
theorem evalStatement_storageLive_cand_ns {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {locals : List LocalSlot} {lm : Map Gen.LocalName Ptr} {m : Mach} {blk stmt bound : Nat}
    (h : FrameOk body f ctx locals lm m blk stmt) (i : Nat) (d : LocalDecl)
    (hd : body.localDecls[i]? = some d) (hal : i ∉ alwaysStorageLiveLocals body)
    (hscalar : (scalarTypeOf d.ty).isSome = true ∨ isPtrTy d.ty = true)
    (hbase : BaseCandBounded ctx.base bound) (hn : bound + body.localDecls.length < 2 ^ 31) :
    ∃ m' lm', evalStatement m (.StorageLive (localName i)) = .ok m' ∧
      FrameOk body f ctx (locals.set i .uninit) lm' m' blk stmt ∧
      (∀ j, j ≠ i → mapGet lm' (localName j) = mapGet lm (localName j)) := by
  have hi : i < body.localDecls.length := (List.getElem?_eq_some_iff.mp hd).1
  have hspec := h.hf.2 i d hd
  have hlt := h.decl_localTy i d hd
  obtain ⟨_, slot, _, hs⟩ := h.slot_exists i hi
  have hil : i < locals.length := (List.getElem?_eq_some_iff.mp hs).1
  let lm2 : Map Gen.LocalName Ptr := ⟨lm.entries.filter (fun e => !decide (e.1 = localName i))⟩
  obtain ⟨cm2, hsd, hlo2⟩ : ∃ cm2 : Gen.ConcurrentMemory BM,
      storageDead (calleeFrameL f ctx lm blk stmt) m.mem (localName i) =
        .ok ({ calleeFrameL f ctx lm blk stmt with locals := lm2 }, cm2) ∧
      LocalsOk body ctx (locals.set i .dead) lm2 cm2.memory.allocations := by
    cases hp : mapGet lm (localName i) with
    | none =>
      have hdead := h.locs.dead_of_none hs hp
      subst hdead
      exact ⟨m.mem, storageDead_none hlt hspec.2 (by simpa [calleeFrameL] using hp),
        h.locs.forget i hs hp⟩
    | some p =>
      obtain ⟨k, data, hpk, _, _, _, _, hlen, hA⟩ :=
        h.locs.storage_any hd hs hp (h.declsOk d (List.mem_of_getElem? hd))
      exact ⟨_, storageDead_some hlt hspec.2 (by simpa [calleeFrameL] using hp) hpk hA rfl rfl rfl
        hlen rfl,
        h.locs.killLocal i d hd slot hs hal p hp k hpk _ hA⟩
  have hp2 : mapGet lm2 (localName i) = none := by simp [lm2, mapGet_filter_key]
  have hs2 : (locals.set i .dead)[i]? = some .dead := List.getElem?_set_self hil
  have hns2 : NonScalarLive body (locals.set i .dead) lm2 :=
    h.nonScalar.filter_scalar hd hscalar .dead
  have hle_sc := scalar_tyBytes_le (layouts := body.layouts) hscalar
  obtain ⟨k, _, halloc, haddr, haddrMax⟩ :=
    BM_allocate_local_cand_ns (mem := cm2.memory) hlo2 hns2 hbase hn h.declsOk hlt hle_sc
  let newPtr : Ptr :=
    { addr := allocCandidate k, provenance := some (⟨(cm2.memory.allocations.length : Int)⟩, ()) }
  have hins : mapInsertMap lm2 (localName i) newPtr = ⟨lm2.entries ++ [(localName i, newPtr)]⟩ := by
    simp only [mapInsertMap]
    rw [mapInsert_absent _ _ _ (filter_key_not_mem _ _)]
  have hsl : storageLive (calleeFrameL f ctx lm blk stmt) m.mem (localName i) =
      .ok ({ calleeFrameL f ctx lm blk stmt with locals := ⟨lm2.entries ++ [(localName i, newPtr)]⟩ },
        { cm2 with memory := { cm2.memory with allocations := cm2.memory.allocations ++
          [stackAlloc (allocCandidate k) (itOf d body.layouts) (declSlotData d .uninit body.layouts)] } }) := by
    have hmi : mapIndex (calleeFrameL f ctx lm blk stmt).func.locals (localName i)
        "self.func.locals[local]" = .ok (tyOf d body.layouts) := by
      simp [mapIndex, calleeFrameL, hspec.2]
    have hca : CM.allocate cm2 .Stack ⟨tyBytes (tyOf d body.layouts)⟩ ⟨(itOf d body.layouts).size.bytes⟩ =
        .ok (newPtr, { cm2 with memory := { cm2.memory with allocations := cm2.memory.allocations ++
          [stackAlloc (allocCandidate k) (itOf d body.layouts) (declSlotData d .uninit body.layouts)] } }) := by
      rw [declSlotData_uninit_of_declOk (h.declsOk d (List.mem_of_getElem? hd))]
      simp only [CM.allocate, halloc, ok_bind, pure_ok]
      rfl
    simp only [storageLive, hsd, ok_bind]
    rw [hmi, ok_bind, hlt.layout, ok_bind, expect_size_sized, ok_bind, expect_align_sized, ok_bind]
    rw [hca, ok_bind, hins]
    rfl
  have htm := tryMutateCurFrame_callee h.shape
    (fun fr cm => storageLive fr cm (localName i)) _ _ hsl
  refine ⟨_, ⟨lm2.entries ++ [(localName i, newPtr)]⟩, by simp only [evalStatement]; exact htm, ?_, ?_⟩
  · have hns3 : NonScalarLive body (locals.set i .uninit) ⟨lm2.entries ++ [(localName i, newPtr)]⟩ :=
      (h.nonScalar.filter_scalar hd hscalar .uninit).append_scalar hd hscalar
        (filter_key_not_mem _ _) newPtr
    refine FrameOk.mk' h.hf ⟨rfl, h.shape.active, rfl⟩ ?_ h.declsOk hns3
    have hlo3 := hlo2.alloc i d hd hs2 hp2 (allocCandidate k) haddr haddrMax
      (Or.inr ⟨by omega, k, rfl⟩)
    rw [List.set_set] at hlo3
    exact hlo3
  · intro j hji
    have hne : localName j ≠ localName i := by simp [localName_inj, hji]
    rw [mapGet_append_single _ _ _ _ (filter_key_not_mem _ _)]
    simp only [hne, ↓reduceIte]
    rw [mapGet_filter_key]
    simp [hne]

/-- `Machine::eval_statement` on `StorageLive(_i)` under `BaseCandBounded` for
a local that `minimize`'s init block does not allocate: `storage_dead` of the
old storage (if any), then a fresh `Stack` allocation at the first free
candidate address of `BM.pickAddr`
(`evalStatement_storageLive_cand_ns` without its frame condition). -/
theorem evalStatement_storageLive_cand {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {locals : List LocalSlot} {lm : Map Gen.LocalName Ptr} {m : Mach} {blk stmt bound : Nat}
    (h : FrameOk body f ctx locals lm m blk stmt) (i : Nat) (d : LocalDecl)
    (hd : body.localDecls[i]? = some d) (hal : i ∉ alwaysStorageLiveLocals body)
    (hscalar : (scalarTypeOf d.ty).isSome = true ∨ isPtrTy d.ty = true)
    (hbase : BaseCandBounded ctx.base bound) (hn : bound + body.localDecls.length < 2 ^ 31) :
    ∃ m' lm', evalStatement m (.StorageLive (localName i)) = .ok m' ∧
      FrameOk body f ctx (locals.set i .uninit) lm' m' blk stmt := by
  obtain ⟨m', lm', hm', h', -⟩ := evalStatement_storageLive_cand_ns h i d hd hal hscalar hbase hn
  exact ⟨m', lm', hm', h'⟩

/-- `Machine::eval_statement` on `StorageLive(_i)` for a local that
`minimize`'s init block does not allocate: `storage_dead` of the old storage
(if any), then a fresh `Stack` allocation at the first free candidate address
of `BM.pickAddr`, which exists because the caller's allocations lie below
`2^32` (`BaseLow`) and the body has fewer than `2^31` locals
(`evalStatement_storageLive_cand_ns` at `bound = 0`). -/
theorem evalStatement_storageLive {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {locals : List LocalSlot} {lm : Map Gen.LocalName Ptr} {m : Mach} {blk stmt : Nat}
    (h : FrameOk body f ctx locals lm m blk stmt) (i : Nat) (d : LocalDecl)
    (hd : body.localDecls[i]? = some d) (hal : i ∉ alwaysStorageLiveLocals body)
    (hscalar : (scalarTypeOf d.ty).isSome = true ∨ isPtrTy d.ty = true)
    (hbaseLow : BaseLow ctx) (hn : body.localDecls.length < 2 ^ 31) :
    ∃ m' lm', evalStatement m (.StorageLive (localName i)) = .ok m' ∧
      FrameOk body f ctx (locals.set i .uninit) lm' m' blk stmt ∧
      (∀ j, j ≠ i → mapGet lm' (localName j) = mapGet lm (localName j)) :=
  evalStatement_storageLive_cand_ns h i d hd hal hscalar hbaseLow.toBaseCandBounded (by omega)

/-- `StorageLive(_i)` of `minimize`'s init block under `BaseCandBounded` for a
temporary `_i` of `alwaysStorageLiveLocals`, which Anneal keeps dead and which
is not yet in the locals map: a fresh allocation at the first free candidate
address, keeping `NonScalarLive` and changing the locals map only at `_i`. -/
theorem evalStatement_storageLive_init_cand_ns {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {al : List Nat} {locals : List LocalSlot} {lm : Map Gen.LocalName Ptr} {m : Mach}
    {blk stmt bound : Nat} (hf : FnLocalsSpec body f)
    (hsh : Shape m ctx [ctx.caller, calleeFrameL f ctx lm blk stmt] m.mem.memory.allocations)
    (hlo : LocalsOkA body ctx al locals lm m.mem.memory.allocations)
    (hdeclsOk : ∀ d ∈ body.localDecls, localDeclOk body.layouts d = true)
    (hns : NonScalarLive body locals lm)
    (i : Nat) (d : LocalDecl) (hd : body.localDecls[i]? = some d)
    (hscalar : (scalarTypeOf d.ty).isSome = true ∨ isPtrTy d.ty = true)
    (hsi : locals[i]? = some .dead) (hp : mapGet lm (localName i) = none)
    (hbase : BaseCandBounded ctx.base bound) (hn : bound + body.localDecls.length < 2 ^ 31) :
    ∃ m' lm', evalStatement m (.StorageLive (localName i)) = .ok m' ∧
      Shape m' ctx [ctx.caller, calleeFrameL f ctx lm' blk stmt] m'.mem.memory.allocations ∧
      LocalsOkA body ctx (al ++ [i]) locals lm' m'.mem.memory.allocations ∧
      NonScalarLive body locals lm' ∧
      (∀ j, j ≠ i → mapGet lm' (localName j) = mapGet lm (localName j)) := by
  have hspec := hf.2 i d hd
  have hlt := localTy_of_declOk (hdeclsOk d (List.mem_of_getElem? hd))
  have hil : i < locals.length := (List.getElem?_eq_some_iff.mp hsi).1
  have hnot : ∀ e ∈ lm.entries, e.1 ≠ localName i := by
    intro e he hei
    obtain ⟨k', v'⟩ := e
    simp only at hei
    subst hei
    have := mapGet_isSome_of_mem (es := lm.entries) he
    rw [hp] at this
    simp at this
  have hsd : storageDead (calleeFrameL f ctx lm blk stmt) m.mem (localName i) =
      .ok ({ calleeFrameL f ctx lm blk stmt with locals := lm }, m.mem) :=
    storageDead_none' hlt hspec.2 (by simpa [calleeFrameL] using hp)
  have hle_sc := scalar_tyBytes_le (layouts := body.layouts) hscalar
  obtain ⟨k, _, halloc, haddr, haddrMax⟩ :=
    BM_allocate_local_cand_ns (mem := m.mem.memory) hlo hns hbase hn hdeclsOk hlt hle_sc
  let newPtr : Ptr :=
    { addr := allocCandidate k, provenance := some (⟨(m.mem.memory.allocations.length : Int)⟩, ()) }
  have hins : mapInsertMap lm (localName i) newPtr = ⟨lm.entries ++ [(localName i, newPtr)]⟩ := by
    simp only [mapInsertMap]
    rw [mapInsert_absent _ _ _ hnot]
  have hsl : storageLive (calleeFrameL f ctx lm blk stmt) m.mem (localName i) =
      .ok ({ calleeFrameL f ctx lm blk stmt with locals := ⟨lm.entries ++ [(localName i, newPtr)]⟩ },
        { m.mem with memory := { m.mem.memory with allocations := m.mem.memory.allocations ++
          [stackAlloc (allocCandidate k) (itOf d body.layouts) (declSlotData d .dead body.layouts)] } }) := by
    have hmi : mapIndex (calleeFrameL f ctx lm blk stmt).func.locals (localName i)
        "self.func.locals[local]" = .ok (tyOf d body.layouts) := by
      simp [mapIndex, calleeFrameL, hspec.2]
    have hca : CM.allocate m.mem .Stack ⟨tyBytes (tyOf d body.layouts)⟩ ⟨(itOf d body.layouts).size.bytes⟩ =
        .ok (newPtr, { m.mem with memory := { m.mem.memory with
          allocations := m.mem.memory.allocations ++
            [stackAlloc (allocCandidate k) (itOf d body.layouts) (declSlotData d .dead body.layouts)] } }) := by
      rw [declSlotData_dead d body.layouts, declSlotData_uninit_of_declOk (hdeclsOk d (List.mem_of_getElem? hd))]
      simp only [CM.allocate, halloc, ok_bind, pure_ok]
      rfl
    simp only [storageLive, hsd, ok_bind]
    rw [hmi, ok_bind, hlt.layout, ok_bind, expect_size_sized, ok_bind, expect_align_sized, ok_bind]
    rw [hca, ok_bind, hins]
    rfl
  have htm := tryMutateCurFrame_callee hsh
    (fun fr cm => storageLive fr cm (localName i)) _ _ hsl
  refine ⟨_, ⟨lm.entries ++ [(localName i, newPtr)]⟩, by simp only [evalStatement]; exact htm, ?_⟩
  refine ⟨⟨rfl, hsh.active, rfl⟩, ?_, hns.append_scalar hd hscalar hnot newPtr, fun j hji => ?_⟩
  · have hlo3 := hlo.alloc' (al' := al ++ [i]) i d hd hsi hp (allocCandidate k) haddr haddrMax
      (Or.inr ⟨by omega, k, rfl⟩) .dead (declSlotOk_dead d body.layouts) (.inr (by simp))
      (.inr (by simp)) (fun j hj => by simp [hj])
    have hset : locals.set i .dead = locals := by
      have h1 := List.set_getElem_self (as := locals) hil
      rwa [show locals[i] = .dead from
        Option.some.inj ((List.getElem?_eq_getElem hil).symm.trans hsi)] at h1
    rw [hset] at hlo3
    exact hlo3
  · have hne : localName j ≠ localName i := by simp [localName_inj, hji]
    rw [mapGet_append_single _ _ _ _ hnot]
    simp [hne]

/-- `StorageLive(_i)` of `minimize`'s init block under `FnLocalsSpec` and
`BaseCandBounded`
(`evalStatement_storageLive_init_cand_ns` for a body whose locals are all scalars). -/
theorem evalStatement_storageLive_init_cand {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {al : List Nat} {locals : List LocalSlot} {lm : Map Gen.LocalName Ptr} {m : Mach}
    {blk stmt bound : Nat} (hf : FnLocalsSpec body f)
    (hsh : Shape m ctx [ctx.caller, calleeFrameL f ctx lm blk stmt] m.mem.memory.allocations)
    (hlo : LocalsOkA body ctx al locals lm m.mem.memory.allocations)
    (i : Nat) (d : LocalDecl) (hd : body.localDecls[i]? = some d)
    (hsi : locals[i]? = some .dead) (hp : mapGet lm (localName i) = none)
    (hbase : BaseCandBounded ctx.base bound) (hn : bound + body.localDecls.length < 2 ^ 31)
    (hdecls : ∀ (i : Nat) d, body.localDecls[i]? = some d → scalarTypeOf d.ty = some (tyOf d)) :
    ∃ m' lm', evalStatement m (.StorageLive (localName i)) = .ok m' ∧
      Shape m' ctx [ctx.caller, calleeFrameL f ctx lm' blk stmt] m'.mem.memory.allocations ∧
      LocalsOkA body ctx (al ++ [i]) locals lm' m'.mem.memory.allocations := by
  obtain ⟨m', lm', hm', hsh', hlo', -⟩ := evalStatement_storageLive_init_cand_ns hf hsh hlo
    (localDeclOk_of_scalar hdecls) (NonScalarLive.of_scalar hdecls) i d hd
    (.inl (by simp [hdecls i d hd])) hsi hp hbase hn
  exact ⟨m', lm', hm', hsh', hlo'⟩

/-- `StorageLive(_i)` of `minimize`'s init block for a temporary `_i` of
`alwaysStorageLiveLocals`, which Anneal keeps dead and which is not yet in the
locals map: a fresh allocation at the first free candidate address
(`evalStatement_storageLive_init_cand_ns` at `bound = 0`). -/
theorem evalStatement_storageLive_init {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {al : List Nat} {locals : List LocalSlot} {lm : Map Gen.LocalName Ptr} {m : Mach}
    {blk stmt : Nat} (hf : FnLocalsSpec body f)
    (hsh : Shape m ctx [ctx.caller, calleeFrameL f ctx lm blk stmt] m.mem.memory.allocations)
    (hlo : LocalsOkA body ctx al locals lm m.mem.memory.allocations)
    (hdeclsOk : ∀ d ∈ body.localDecls, localDeclOk body.layouts d = true)
    (hns : NonScalarLive body locals lm)
    (i : Nat) (d : LocalDecl) (hd : body.localDecls[i]? = some d)
    (hscalar : (scalarTypeOf d.ty).isSome = true ∨ isPtrTy d.ty = true)
    (hsi : locals[i]? = some .dead) (hp : mapGet lm (localName i) = none)
    (hbaseLow : BaseLow ctx) (hn : body.localDecls.length < 2 ^ 31) :
    ∃ m' lm', evalStatement m (.StorageLive (localName i)) = .ok m' ∧
      Shape m' ctx [ctx.caller, calleeFrameL f ctx lm' blk stmt] m'.mem.memory.allocations ∧
      LocalsOkA body ctx (al ++ [i]) locals lm' m'.mem.memory.allocations ∧
      NonScalarLive body locals lm' ∧
      (∀ j, j ≠ i → mapGet lm' (localName j) = mapGet lm (localName j)) :=
  evalStatement_storageLive_init_cand_ns hf hsh hlo hdeclsOk hns i d hd hscalar hsi hp
    hbaseLow.toBaseCandBounded (by omega)

/-! ## `Return` -/

/-- The allocation number that a pointer's provenance names (`0` without
provenance). -/
def provId (p : Ptr) : Nat :=
  match p.provenance with
  | some (id, ()) => id._0.toNat
  | none => 0

theorem provId_of {p : Ptr} {k : Nat} (h : p.provenance = some (⟨(k : Int)⟩, ())) :
    provId p = k := by
  simp [provId, h]

theorem nodup_map_of_inj_on {α β : Type} (f : α → β) (l : List α) (hl : l.Nodup)
    (hinj : ∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y) : (l.map f).Nodup := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.nodup_cons] at hl
    rw [List.map_cons, List.nodup_cons]
    refine ⟨fun hfa => ?_, ih hl.2 (fun x hx y hy => hinj x (by simp [hx]) y (by simp [hy]))⟩
    obtain ⟨x, hx, hfx⟩ := List.mem_map.mp hfa
    have := hinj x (by simp [hx]) a (by simp) hfx
    subst this
    exact hl.1 hx

theorem nodup_of_map {α β : Type} (f : α → β) {l : List α} (h : (l.map f).Nodup) : l.Nodup := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, List.nodup_cons] at h
    rw [List.nodup_cons]
    exact ⟨fun ha => h.1 (List.mem_map_of_mem ha), ih h.2⟩

theorem mapGet_of_mem_nodup {V : Type} {es : List (Gen.LocalName × V)} {k : Gen.LocalName}
    {v : V} (hmem : (k, v) ∈ es) (hnd : (es.map Prod.fst).Nodup) : mapGet ⟨es⟩ k = some v := by
  induction es with
  | nil => simp at hmem
  | cons e es ih =>
    obtain ⟨k', v'⟩ := e
    rw [List.map_cons, List.nodup_cons] at hnd
    rw [mapGet_cons]
    rcases List.mem_cons.mp hmem with h | h
    · simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp
    · have hk : k' ≠ k := by
        intro hk
        subst hk
        exact hnd.1 (List.mem_map.mpr ⟨(k', v), h, rfl⟩)
      simp only [hk, ↓reduceIte]
      exact ih h hnd.2

theorem filter_key_cons_self {V : Type} (key : Gen.LocalName) (v : V)
    (rest : List (Gen.LocalName × V)) (hrest : ∀ e ∈ rest, e.1 ≠ key) :
    ((key, v) :: rest).filter (fun e => !decide (e.1 = key)) = rest := by
  rw [List.filter_cons_of_neg (by simp), List.filter_eq_self]
  intro e he
  simp [hrest e he]

/-- The teardown loop of `Return` on a frame whose locals map `es` has
distinct keys, each pointing to its own live `Stack` allocation of its local's
layout: it empties the map and deallocates exactly those allocations. -/
theorem deallocAll_gen (fuel : Nat) (fr : Frame) (cm : Gen.ConcurrentMemory BM)
    (es : List (Gen.LocalName × Ptr)) (hfuel : es.length ≤ fuel) (hloc : fr.locals = ⟨es⟩)
    (hnodup : (es.map Prod.fst).Nodup) (hidnd : (es.map (fun e => provId e.2)).Nodup)
    (hok : ∀ e ∈ es, ∃ T it a, mapGet fr.func.locals e.1 = some T ∧ LocalTy T it ∧
      e.2.provenance = some (⟨(provId e.2 : Int)⟩, ()) ∧
      cm.memory.allocations[provId e.2]? = some a ∧ a.live = true ∧ a.addr = e.2.addr ∧
      a.kind = .Stack ∧ a.data.length = tyBytes T ∧ a.align = ⟨it.size.bytes⟩) :
    ∃ cm', deallocAll fuel fr cm = .ok ({ fr with locals := ⟨[]⟩ }, cm') ∧
      cm'.memory.allocations = killAt cm.memory.allocations (es.map (fun e => provId e.2)) := by
  induction es generalizing fuel fr cm with
  | nil =>
    refine ⟨cm, ?_, by simp [killAt_nil]⟩
    have hfr : fr = { fr with locals := ⟨[]⟩ } := by
      cases fr; simp at hloc; simp [hloc]
    cases fuel <;> (simp only [deallocAll, hloc]; rw [← hfr]; rfl)
  | cons e es ih =>
    obtain ⟨key, p⟩ := e
    obtain ⟨fuel', rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by simp at hfuel; omega⟩
    rw [List.map_cons, List.nodup_cons] at hnodup hidnd
    obtain ⟨hni, hnd⟩ := hnodup
    obtain ⟨hnid, hndid⟩ := hidnd
    obtain ⟨T, it, a, hty, hT, hpk, ha, hlive, haddr, hkind, hlen, halign⟩ := hok (key, p) (by simp)
    have hrest : ∀ e ∈ es, e.1 ≠ key := by
      intro e he hek
      exact hni (List.mem_map.mpr ⟨e, he, hek⟩)
    have hp : mapGet fr.locals key = some p := by rw [hloc, mapGet_cons]; simp
    have hsd := storageDead_some hT hty hp hpk ha hlive haddr hkind hlen halign
    have hfil : fr.locals.entries.filter (fun e => !decide (e.1 = key)) = es := by
      rw [hloc]; exact filter_key_cons_self key p es hrest
    rw [hfil] at hsd
    obtain ⟨cm', hcm', hcm'mem⟩ := ih fuel' { fr with locals := ⟨es⟩ }
      { cm with memory := { cm.memory with
          allocations := cm.memory.allocations.set (provId p) (kill a) } }
      (by simp at hfuel; omega) rfl hnd hndid
      (by
        intro e he
        obtain ⟨T', it', a', hty', hT', hpk', ha', h1, h2, h3, h4, h5⟩ := hok e (by simp [he])
        have hij : provId p ≠ provId e.2 := by
          intro hij
          exact hnid (List.mem_map.mpr ⟨e, he, hij.symm⟩)
        exact ⟨T', it', a', hty', hT', hpk', by simp only; rw [List.getElem?_set_ne hij]; exact ha',
          h1, h2, h3, h4, h5⟩)
    refine ⟨cm', ?_, ?_⟩
    · rw [deallocAll]
      simp only [hloc]
      rw [hsd]
      simpa using hcm'
    · rw [hcm'mem, List.map_cons, killAt_cons _ _ _ a ha hnid]

/-- Deallocating allocations above `base` that include every live one leaves
`base` unchanged and only dead allocations above it. -/
theorem killAt_append_dead (base R : List Gen.Allocation) (ids : List Nat)
    (hlow : ∀ id ∈ ids, base.length ≤ id)
    (hall : ∀ (j : Nat) b, R[j]? = some b → b.live = true → base.length + j ∈ ids) :
    ∃ R', killAt (base ++ R) ids = base ++ R' ∧ ∀ b ∈ R', b.live = false := by
  refine ⟨R.mapIdx (fun j b => if base.length + j ∈ ids then kill b else b), ?_, ?_⟩
  · apply List.ext_getElem?
    intro x
    simp only [killAt, List.getElem?_mapIdx]
    by_cases hx : x < base.length
    · rw [List.getElem?_append_left hx, List.getElem?_append_left hx]
      have hnot : x ∉ ids := fun hm => by have := hlow x hm; omega
      cases base[x]? <;> simp [hnot]
    · rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega),
        List.getElem?_mapIdx]
      have hx' : base.length + (x - base.length) = x := by omega
      cases R[x - base.length]? <;> simp [hx']
  · intro b hb
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hb
    rw [List.getElem_mapIdx]
    have hjR : j < R.length := by simpa using hj
    by_cases hm : base.length + j ∈ ids
    · simp [hm, kill]
    · simp only [hm, ↓reduceIte]
      cases hl : R[j].live with
      | false => rfl
      | true => exact absurd (hall j _ (List.getElem?_eq_getElem hjR) hl) hm

/-- The facts about the callee's locals map that `Return`'s teardown loop
needs, from `LocalsOk`. -/
theorem LocalsOkA.teardown {body : CapturedMir} {f : Gen.Function} {ctx : Ctx} {al : List Nat}
    {locals : List LocalSlot} {lm : Map Gen.LocalName Ptr} {A : List Gen.Allocation}
    (hf : FnLocalsSpec body f) (hlo : LocalsOkA body ctx al locals lm A)
    (hdeclsOk : ∀ d ∈ body.localDecls, localDeclOk body.layouts d = true) :
    (lm.entries.map (fun e => provId e.2)).Nodup ∧
    (∀ e ∈ lm.entries, ∃ T it a, mapGet f.locals e.1 = some T ∧ LocalTy T it ∧
      e.2.provenance = some (⟨(provId e.2 : Int)⟩, ()) ∧ A[provId e.2]? = some a ∧
      a.live = true ∧ a.addr = e.2.addr ∧ a.kind = .Stack ∧ a.data.length = tyBytes T ∧
      a.align = ⟨it.size.bytes⟩) ∧
    (∀ id ∈ lm.entries.map (fun e => provId e.2), ctx.base.length ≤ id) ∧
    (∀ (id : Nat) a, A[id]? = some a → a.live = true → ctx.base.length ≤ id →
      id ∈ lm.entries.map (fun e => provId e.2)) := by
  have hspec := hf
  -- Each entry is `(localName i, q)` for a local `_i` whose storage `q` names.
  have hentry : ∀ e ∈ lm.entries, ∃ i d slot, body.localDecls[i]? = some d ∧
      locals[i]? = some slot ∧ e.1 = localName i ∧ mapGet lm (localName i) = some e.2 := by
    intro e he
    obtain ⟨i, hi, hei⟩ := hlo.keysLocal e he
    have hil : i < locals.length := by rw [hlo.nlocals]; exact hi
    refine ⟨i, _, _, List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hil, hei, ?_⟩
    rw [← hei]
    exact mapGet_of_mem_nodup (by simpa using he) hlo.keysNodup
  have hstore : ∀ e ∈ lm.entries, ∃ i d slot data, body.localDecls[i]? = some d ∧
      locals[i]? = some slot ∧ e.1 = localName i ∧
      e.2.provenance = some (⟨(provId e.2 : Int)⟩, ()) ∧ ctx.base.length ≤ provId e.2 ∧
      data.length = tyBytes (tyOf d body.layouts) ∧
      A[provId e.2]? = some (stackAlloc e.2.addr (itOf d body.layouts) data) := by
    intro e he
    obtain ⟨i, d, slot, hd, hs, hei, hmg⟩ := hentry e he
    obtain ⟨id, data, hpid, hb, _, _, _, hlen, hA⟩ :=
      hlo.storage_any hd hs hmg (hdeclsOk d (List.mem_of_getElem? hd))
    rw [provId_of hpid]
    exact ⟨i, d, slot, data, hd, hs, hei, hpid, hb, hlen, hA⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply nodup_map_of_inj_on _ _ (nodup_of_map Prod.fst hlo.keysNodup)
    intro x hx y hy hxy
    obtain ⟨i, _, _, _, _, _, hxi, hpx, _, _, _⟩ := hstore x hx
    obtain ⟨j, _, _, _, _, _, hyj, hpy, _, _, _⟩ := hstore y hy
    obtain ⟨i', _, _, _, _, hxi', hmx'⟩ := hentry x hx
    obtain ⟨j', _, _, _, _, hyj', hmy'⟩ := hentry y hy
    have hii : i' = i := by rw [hxi'] at hxi; simpa [localName_inj] using hxi
    have hjj : j' = j := by rw [hyj'] at hyj; simpa [localName_inj] using hyj
    subst hii hjj
    have hij : i' = j' := hlo.inj i' j' x.2 y.2 hmx' hmy' (by rw [hpx, hpy, hxy])
    subst hij
    have hv : x.2 = y.2 := by rw [hmx'] at hmy'; exact Option.some.inj hmy'
    obtain ⟨x1, x2⟩ := x
    obtain ⟨y1, y2⟩ := y
    simp only at hxi' hyj' hv
    rw [hxi', hyj', hv]
  · intro e he
    obtain ⟨i, d, slot, data, hd, hs, hei, hpid, _, hlen, hA⟩ := hstore e he
    have hdok := hdeclsOk d (List.mem_of_getElem? hd)
    have hlt := localTy_of_declOk hdok
    exact ⟨tyOf d body.layouts, itOf d body.layouts, _, by rw [hei]; exact (hspec.2 i d hd).2,
      hlt, hpid, hA, rfl, rfl, rfl, hlen, rfl⟩
  · intro id hid
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hid
    obtain ⟨_, _, _, _, _, _, _, _, hb, _, _⟩ := hstore e he
    exact hb
  · intro id a hA hlive hb
    obtain ⟨i, q, hq, hqid⟩ := hlo.owned id a hA hlive hb
    exact List.mem_map.mpr ⟨(localName i, q), mapGet_mem hq, provId_of hqid⟩

theorem typedStore_base {m : Mach} {ctx : Ctx} {frames : List Frame} {L : List Gen.Allocation}
    (h : Shape m ctx frames (ctx.base ++ L)) (p : Ptr) (r : Nat) (a : Gen.Allocation)
    (hp : p.provenance = some (⟨(r : Int)⟩, ())) (hr : ctx.base[r]? = some a) (hlive : a.live = true)
    (haddr : a.addr = p.addr) (it : Gen.IntType) (hgood : GoodSize it.size.bytes)
    (hlen : a.data.length = it.size.bytes) (v : Int) (hv : IntType.can_represent it v = true)
    (align : Align) (hal : Align.is_aligned align p.addr = true) :
    typedStore m p (.Int v) (.Int it) align .None =
      .ok (withMem m (ctx.base.set r { a with data := scalarBytes it (v % 2 ^ (8 * it.size.bytes)).toNat } ++ L)
            ⟨.Store, .None, p.addr, it.size⟩) := by
  have hpos := hgood.pos
  obtain ⟨hri, hai⟩ := List.getElem?_eq_some_iff.mp hr
  have hblen : (scalarBytes it (v % 2 ^ (8 * it.size.bytes)).toNat).length = it.size.bytes := by
    simp [scalarBytes, leBytes_length]
  have hck : checkValue (.Int v) (.Int it) (some m) = .ok () := checkValue_int hv
  have hne : scalarBytes it (v % 2 ^ (8 * it.size.bytes)).toNat ≠ [] :=
    List.ne_nil_of_length_pos (by omega)
  have hdrop : a.data.drop it.size.bytes = [] := List.drop_eq_nil_of_le (by omega)
  have hrlt : r < ctx.base.length + L.length := by omega
  simp only [typedStore, hck, encode_int it v hgood hv, CM.store, BM.store, hal, BM.check_ptr, hp,
    listIndex, h.allocs]
  obtain ⟨signed, size⟩ := it
  simp [hne, hlive, haddr, Allocation.size, hlen, hblen, writeSubsliceAtIndex, listSet, withMem,
    hdrop, List.set_append_left _ _ hri, hri, hrlt, hai]

theorem typedStore_base_bool {m : Mach} {ctx : Ctx} {frames : List Frame} {L : List Gen.Allocation}
    (h : Shape m ctx frames (ctx.base ++ L)) (p : Ptr) (r : Nat) (a : Gen.Allocation)
    (hp : p.provenance = some (⟨(r : Int)⟩, ())) (hr : ctx.base[r]? = some a) (hlive : a.live = true)
    (haddr : a.addr = p.addr) (hlen : a.data.length = u8Ty.size.bytes) (b : Bool)
    (align : Align) (hal : Align.is_aligned align p.addr = true) :
    typedStore m p (.Bool b) .Bool align .None =
      .ok (withMem m (ctx.base.set r { a with data := scalarBytes u8Ty (if b then 1 else 0) } ++ L)
            ⟨.Store, .None, p.addr, u8Ty.size⟩) := by
  obtain ⟨hri, hai⟩ := List.getElem?_eq_some_iff.mp hr
  have hu8 : u8Ty.size.bytes = 1 := rfl
  have hck : checkValue (.Bool b) .Bool (some m) = .ok () := rfl
  have hblen : (scalarBytes u8Ty (if b then 1 else 0)).length = u8Ty.size.bytes := by
    simp [scalarBytes, leBytes_length]
  have hne : scalarBytes u8Ty (if b then 1 else 0) ≠ [] :=
    List.ne_nil_of_length_pos (by rw [hblen, hu8]; omega)
  have hdrop : a.data.drop u8Ty.size.bytes = [] := List.drop_eq_nil_of_le (by omega)
  have hrlt : r < ctx.base.length + L.length := by omega
  simp only [typedStore, hck, encode_bool, CM.store, BM.store, hal, BM.check_ptr, hp,
    listIndex, h.allocs]
  simp [hne, hlive, haddr, Allocation.size, hlen, hblen, writeSubsliceAtIndex, listSet, withMem,
    hdrop, List.set_append_left _ _ hri, hri, hrlt, hai]

theorem typedStore_base_byte {m : Mach} {ctx : Ctx} {frames : List Frame} {L : List Gen.Allocation}
    (h : Shape m ctx frames (ctx.base ++ L)) (p : Ptr) (r : Nat) (a : Gen.Allocation)
    (hp : p.provenance = some (⟨(r : Int)⟩, ())) (hr : ctx.base[r]? = some a) (hlive : a.live = true)
    (haddr : a.addr = p.addr) (hlen : a.data.length = u8Ty.size.bytes) (T : Gen.Type) (v : Val)
    (bits : Nat) (hck : ∀ {m? : Option Mach}, checkValue v T m? = .ok ())
    (henc : Type.encode T v = .ok (scalarBytes u8Ty bits))
    (align : Align) (hal : Align.is_aligned align p.addr = true) :
    typedStore m p v T align .None =
      .ok (withMem m (ctx.base.set r { a with data := scalarBytes u8Ty bits } ++ L)
            ⟨.Store, .None, p.addr, u8Ty.size⟩) := by
  obtain ⟨hri, hai⟩ := List.getElem?_eq_some_iff.mp hr
  have hu8 : u8Ty.size.bytes = 1 := rfl
  have hblen : (scalarBytes u8Ty bits).length = u8Ty.size.bytes := by
    simp [scalarBytes, leBytes_length]
  have hne : scalarBytes u8Ty bits ≠ [] :=
    List.ne_nil_of_length_pos (by rw [hblen, hu8]; omega)
  have hdrop : a.data.drop u8Ty.size.bytes = [] := List.drop_eq_nil_of_le (by omega)
  have hrlt : r < ctx.base.length + L.length := by omega
  simp only [typedStore, hck, henc, CM.store, BM.store, hal, BM.check_ptr, hp,
    listIndex, h.allocs]
  simp [hne, hlive, haddr, Allocation.size, hlen, hblen, writeSubsliceAtIndex, listSet, withMem,
    hdrop, List.set_append_left _ _ hri, hri, hrlt, hai]

/-- `typed_store` of the value of a valid bit pattern of a fragment type into
the caller's return place (an allocation in `base`). -/
theorem typedStore_base_frag {m : Mach} {ctx : Ctx} {frames : List Frame} {L : List Gen.Allocation}
    (h : Shape m ctx frames (ctx.base ++ L)) (p : Ptr) (r : Nat) (a : Gen.Allocation)
    (hp : p.provenance = some (⟨(r : Int)⟩, ())) (hr : ctx.base[r]? = some a) (hlive : a.live = true)
    (haddr : a.addr = p.addr) {T : Gen.Type} {it : Gen.IntType} (hT : FragTy T it)
    (hlen : a.data.length = it.size.bytes) (bits : Nat) (hb : ValidBits T bits)
    (align : Align) (hal : Align.is_aligned align p.addr = true) :
    typedStore m p (valOf T bits) T align .None =
      .ok (withMem m (ctx.base.set r { a with data := scalarBytes it bits } ++ L)
            ⟨.Store, .None, p.addr, it.size⟩) := by
  cases hT with
  | int it hgood =>
    have hb' : bits < 2 ^ (8 * it.size.bytes) := hb
    have hst := typedStore_base h p r a hp hr hlive haddr it hgood hlen (intFromBits bits it)
      (canRepresent_intFromBits it bits hgood hb') align hal
    have hres : (intFromBits bits it % 2 ^ (8 * it.size.bytes)).toNat = bits := by
      rw [intFromBits_emod bits _ hb']; simp
    rw [hres] at hst
    exact hst
  | bool =>
    have hb' : bits < 2 := by simpa [ValidBits] using hb
    have hst := typedStore_base_bool h p r a hp hr hlive haddr hlen (decide (bits = 1)) align hal
    have hres : (if decide (bits = 1) then 1 else 0) = bits := by
      rcases (by omega : bits = 0 ∨ bits = 1) with rfl | rfl <;> rfl
    rw [hres] at hst
    exact hst
  | ordering =>
    exact typedStore_base_byte h p r a hp hr hlive haddr hlen orderingTy _ bits
      (checkValue_ordering hb) (encode_ordering hb) align hal

theorem typedStore_base_tuple {m : Mach} {ctx : Ctx} {frames : List Frame} {L : List Gen.Allocation}
    (h : Shape m ctx frames (ctx.base ++ L)) (p : Ptr) (r : Nat) (a : Gen.Allocation)
    (hp : p.provenance = some (⟨(r : Int)⟩, ())) (hr : ctx.base[r]? = some a) (hlive : a.live = true)
    (haddr : a.addr = p.addr) (it : Gen.IntType) (hgood : GoodSize it.size.bytes)
    (hlen : a.data.length = it.size.bytes + it.size.bytes) (bits b : Nat)
    (hbits : bits < 2 ^ (8 * it.size.bytes)) (hb : b < 2)
    (align : Align) (hal : Align.is_aligned align p.addr = true) :
    typedStore m p (tupleVal it bits b) (intBoolTupleTy it) align .None =
      .ok (withMem m (ctx.base.set r { a with data := tupleBytes it bits b } ++ L)
            ⟨.Store, .None, p.addr, ⟨it.size.bytes + it.size.bytes⟩⟩) := by
  have hpos := hgood.pos
  obtain ⟨hri, hai⟩ := List.getElem?_eq_some_iff.mp hr
  have hblen := tupleBytes_length it bits b hpos
  have hck : checkValue (tupleVal it bits b) (intBoolTupleTy it) (some m) = .ok () :=
    checkValue_tuple it bits b hgood hbits
  have henc := encode_tuple it bits b hgood hbits hb
  have hne : tupleBytes it bits b ≠ [] := List.ne_nil_of_length_pos (by omega)
  have hdrop : a.data.drop (it.size.bytes + it.size.bytes) = [] := List.drop_eq_nil_of_le (by omega)
  have hrlt : r < ctx.base.length + L.length := by omega
  simp only [typedStore, hck, henc, CM.store, BM.store, hal, BM.check_ptr, hp,
    listIndex, h.allocs]
  simp [hne, hlive, haddr, Allocation.size, hlen, hblen, writeSubsliceAtIndex, listSet, withMem,
    hdrop, List.set_append_left _ _ hri, hri, hrlt, hai]

theorem typedStore_base_localTy {layouts : Layout.LayoutTable}
    {m : Mach} {ctx : Ctx} {frames : List Frame} {L : List Gen.Allocation}
    (h : Shape m ctx frames (ctx.base ++ L)) (p : Ptr) (r : Nat) (a : Gen.Allocation)
    (hp : p.provenance = some (⟨(r : Int)⟩, ())) (hr : ctx.base[r]? = some a) (hlive : a.live = true)
    (haddr : a.addr = p.addr) (d : LocalDecl)
    (hd : scalarTypeOf d.ty = some (tyOf d layouts))
    (hlen : a.data.length = tyBytes (tyOf d layouts)) (v : Value)
    (hv : SlotOk (tyOf d layouts) (.init v))
    (align : Align) (hal : Align.is_aligned align p.addr = true) :
    ∃ acc, typedStore m p (valOfValue (tyOf d layouts) v) (tyOf d layouts) align .None =
      .ok (withMem m (ctx.base.set r { a with data := declSlotData d (.init v) layouts } ++ L) acc) := by
  rcases scalarTypeOf_cases hd with ⟨hb, _⟩ | ⟨it, hit, _⟩ | ⟨ho, _⟩ | ⟨it, ht, _⟩
  · obtain ⟨h1, h2⟩ := tyOf_bool (layouts := layouts) hb
    have hfrag : FragTy (tyOf d layouts) (itOf d layouts) := by rw [h1, h2]; exact .bool
    rw [hfrag.declSlotData]
    rw [hfrag.tyBytes] at hlen
    match v, hv with
    | .scalar sc, ⟨_, hvb⟩ =>
      exact ⟨_, typedStore_base_frag h p r a hp hr hlive haddr hfrag hlen sc.bits hvb align hal⟩
    | .aggregate 0 [.scalar sc0, .scalar sc1], ⟨_, htyT, _⟩ =>
      rw [h1] at htyT; simp at htyT
  · obtain ⟨h1, h2⟩ := tyOf_int (layouts := layouts) hit
    have hfrag : FragTy (tyOf d layouts) (itOf d layouts) :=
      by rw [h1, h2]; exact .int it (intTypeOf_good hit)
    rw [hfrag.declSlotData]
    rw [hfrag.tyBytes] at hlen
    match v, hv with
    | .scalar sc, ⟨_, hvb⟩ =>
      exact ⟨_, typedStore_base_frag h p r a hp hr hlive haddr hfrag hlen sc.bits hvb align hal⟩
    | .aggregate 0 [.scalar sc0, .scalar sc1], ⟨_, htyT, _⟩ =>
      rw [h1] at htyT; simp at htyT
  · obtain ⟨h1, h2⟩ := tyOf_ordering (layouts := layouts) ho
    have hfrag : FragTy (tyOf d layouts) (itOf d layouts) := by rw [h1, h2]; exact .ordering
    rw [hfrag.declSlotData]
    rw [hfrag.tyBytes] at hlen
    match v, hv with
    | .scalar sc, ⟨_, hvb⟩ =>
      exact ⟨_, typedStore_base_frag h p r a hp hr hlive haddr hfrag hlen sc.bits hvb align hal⟩
    | .aggregate 0 [.scalar sc0, .scalar sc1], ⟨_, htyT, _⟩ =>
      rw [h1] at htyT; simp at htyT
  · obtain ⟨h1, _⟩ := tyOf_tuple (layouts := layouts) ht
    rw [declSlotData_of_some ht]
    match v, hv with
    | .scalar sc, ⟨_, hvb⟩ =>
      rw [h1] at hvb; simp [intBoolTupleTy, ValidBits] at hvb
    | .aggregate 0 [.scalar sc0, .scalar sc1], ⟨it', htyT, _, hb0, _, hb1⟩ =>
      rw [h1, tupleIntOfTy_intBoolTupleTy, Option.some.injEq] at htyT
      subst htyT
      have hlen' : a.data.length = it.size.bytes + it.size.bytes := by
        rw [h1] at hlen; exact hlen
      refine ⟨⟨.Store, .None, p.addr, ⟨it.size.bytes + it.size.bytes⟩⟩, ?_⟩
      rw [h1]
      simpa [valOfValue, tupleIntOfTy_intBoolTupleTy, tupleSlotData] using
        typedStore_base_tuple h p r a hp hr hlive haddr it (intBoolTupleOf_good ht) hlen'
          sc0.bits sc1.bits hb0 hb1 align hal

/-! ## Multi-frame stack lifting and `Terminator::Call` / `Return` (`MR-4.1`) -/

/-- Replace `m.threads` with a single enabled thread carrying `frames` and
`ctx.payloads`. -/
def rethread (m : Mach) (ctx : Ctx) (frames : List Frame) : Mach :=
  { m with threads := [thread1 ctx frames] }

theorem ProgEnvOk.of_eq {prog : Gen.Program} {fnMap : FnMap}
    {m m' : Mach} (h : ProgEnvOk prog fnMap m)
    (hp : m'.prog = m.prog) (hf : m'.fn_ptrs = m.fn_ptrs) :
    ProgEnvOk prog fnMap m' := by
  rcases h with ⟨h1, h2⟩
  unfold ProgEnvOk
  rw [hp, hf]
  exact ⟨h1, h2⟩

theorem ProgEnvOk.withMem {prog : Gen.Program} {fnMap : FnMap}
    {m : Mach} {allocs : List Gen.Allocation} {acc : Gen.Access}
    (h : ProgEnvOk prog fnMap m) :
    ProgEnvOk prog fnMap (withMem m allocs acc) :=
  h.of_eq rfl rfl

theorem ProgEnvOk.rethread {prog : Gen.Program} {fnMap : FnMap}
    {m : Mach} {ctx : Ctx} {frames : List Frame}
    (h : ProgEnvOk prog fnMap m) :
    ProgEnvOk prog fnMap (MiniRustSpec.Correspondence.rethread m ctx frames) :=
  h.of_eq rfl rfl

private theorem getLast?_append_singleton {α : Type} (pre : List α) (x : α) :
    (pre ++ [x]).getLast? = some x := by
  induction pre with
  | nil => rfl
  | cons a tl ih =>
    cases tl with
    | nil => rfl
    | cons b tl' =>
      simp only [List.cons_append, List.getLast?_cons_cons]
      exact ih

private theorem dropLast_append_singleton {α : Type} (pre : List α) (x : α) :
    (pre ++ [x]).dropLast = pre := by
  induction pre with
  | nil => rfl
  | cons a tl ih =>
    cases tl with
    | nil => rfl
    | cons b tl' =>
      simp only [List.cons_append, List.dropLast_cons_cons]
      rw [← List.cons_append, ih]

private theorem mach_mem_mem (m : Mach) (cm1 cm2 : Gen.ConcurrentMemory BM) :
    ({ { m with mem := cm1 } with mem := cm2 } : Mach) = { m with mem := cm2 } := rfl

private theorem rethread_with_mem_eq {m : Mach} {rootCtx curCtx : Ctx} {pre : List Frame}
    {fr : Frame} (hthr : m.threads = [thread1 rootCtx (pre ++ [fr])])
    (cm : Gen.ConcurrentMemory BM) :
    rethread { rethread m curCtx [curCtx.caller, fr] with mem := cm } rootCtx (pre ++ [fr]) =
      { m with mem := cm } := by
  cases m
  simp [rethread] at hthr ⊢
  exact hthr.symm

theorem curFrame_append {m : Mach} {ctx : Ctx} {pre : List Frame} {fr : Frame}
    {allocs : List Gen.Allocation} (h : Shape m ctx (pre ++ [fr]) allocs) :
    curFrame m = .ok fr := by
  have hlast := getLast?_append_singleton pre fr
  simp [curFrame, activeThread, listIndex, h.threads, h.active, thread1, hlast]

theorem mutateCurFrame_append {m : Mach} {ctx : Ctx} {pre : List Frame} {fr : Frame}
    {allocs : List Gen.Allocation} (h : Shape m ctx (pre ++ [fr]) allocs)
    (g : Frame → Frame) :
    mutateCurFrame m g = .ok (rethread m ctx (pre ++ [g fr])) := by
  have hlast := getLast?_append_singleton pre fr
  have hdrop := dropLast_append_singleton pre fr
  simp [mutateCurFrame, activeThread, listIndex, h.threads, h.active, thread1,
    hlast, hdrop, listSet, rethread]

theorem jumpToBlock_append {m : Mach} {ctx curCtx : Ctx} {pre : List Frame}
    {f : Gen.Function} {lm : Map Gen.LocalName Ptr} {blk stmt : Nat}
    {allocs : List Gen.Allocation}
    (h : Shape m ctx (pre ++ [calleeFrameL f curCtx lm blk stmt]) allocs) (t : Nat) :
    jumpToBlock m (bbName t) =
      .ok (rethread m ctx (pre ++ [calleeFrameL f curCtx lm t 0])) := by
  simpa [jumpToBlock, calleeFrameL] using
    mutateCurFrame_append h (fun fr => { fr with next_block := bbName t, next_stmt := 0 })

theorem bumpStmt_append {m : Mach} {ctx curCtx : Ctx} {pre : List Frame}
    {f : Gen.Function} {lm : Map Gen.LocalName Ptr} {blk stmt : Nat}
    {allocs : List Gen.Allocation}
    (h : Shape m ctx (pre ++ [calleeFrameL f curCtx lm blk stmt]) allocs) :
    mutateCurFrame m (fun fr => { fr with next_stmt := fr.next_stmt + 1 }) =
      .ok (rethread m ctx (pre ++ [calleeFrameL f curCtx lm blk (stmt + 1)])) := by
  have hm := mutateCurFrame_append h (fun fr => { fr with next_stmt := fr.next_stmt + 1 })
  have heq : ({ calleeFrameL f curCtx lm blk stmt with
      next_stmt := (calleeFrameL f curCtx lm blk stmt).next_stmt + 1 } : Frame) =
      calleeFrameL f curCtx lm blk (stmt + 1) := by
    simp [calleeFrameL]
  rwa [heq] at hm

theorem mutateCurStack_append {m : Mach} {ctx : Ctx} {frames : List Frame}
    {allocs : List Gen.Allocation} (h : Shape m ctx frames allocs) (fr : Frame) :
    mutateCurStack m (fun stack => pure ((), stack ++ [fr])) =
      .ok ((), rethread m ctx (frames ++ [fr])) := by
  simp [mutateCurStack, activeThread, listIndex, h.threads, h.active, thread1, listSet, rethread]

/-- `Machine::check_ptr` reads only the machine's memory and vtables. -/
theorem checkPtr_congr_mach {M1 M2 : Mach} (hmem : M1.mem = M2.mem)
    (hvt : M1.vtable_ptrs = M2.vtable_ptrs) (hprog : M1.prog = M2.prog)
    (ptr : Gen.Pointer Prov) (ptrTy : Gen.PtrType) :
    checkPtr ptr ptrTy (some M1) = checkPtr ptr ptrTy (some M2) := by
  have hvl : vtableLookup M1 = vtableLookup M2 := by
    funext p; unfold vtableLookup; rw [hvt, hprog]
  unfold checkPtr
  simp only [hvl, hmem]

/-- `Machine::check_value` reads only the machine's memory and vtables. -/
theorem checkValue_congr_mach {M1 M2 : Mach} (hmem : M1.mem = M2.mem)
    (hvt : M1.vtable_ptrs = M2.vtable_ptrs) (hprog : M1.prog = M2.prog)
    (v : Val) (t : Gen.Type) :
    checkValue v t (some M1) = checkValue v t (some M2) := by
  have hptr := checkPtr_congr_mach hmem hvt hprog
  suffices h : some M1 = some M1 → checkValue v t (some M1) = checkValue v t (some M2) from h rfl
  refine checkValue.induct
    (motive_1 := fun v t mo => mo = some M1 → checkValue v t mo = checkValue v t (some M2))
    (motive_2 := fun vs d data mo => mo = some M1 →
      checkVariant vs d data mo = checkVariant vs d data (some M2))
    (motive_3 := fun vals fs mo => mo = some M1 →
      checkFields vals fs mo = checkFields vals fs (some M2))
    ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7 ?c8 ?c9 ?c10 ?c11 ?c12 ?c13 ?c14 ?c15 ?c16 ?c17 ?c18 ?c19 ?c20
    ?c21 ?c22 v t (some M1)
  case c1 => intro m i t hm; subst hm; rfl
  case c2 => intro m b hm; subst hm; rfl
  case c3 => intro m ptr ptrTy hm; subst hm; exact hptr ptr ptrTy
  case c4 => intro m vals fields shl val hm; subst hm; rfl
  case c5 =>
    intro m vals fields shl ih hm; subst hm
    simp only [checkValue, ih rfl]
  case c6 =>
    intro m vals elem count ih hm; subst hm
    have ih' : ∀ val, checkValue val elem (some M1) = checkValue val elem (some M2) :=
      fun val => ih val rfl
    simp only [checkValue, ih']
  case c7 => intro m cd fields chunks size align hm; subst hm; rfl
  case c8 =>
    intro m disc data variants dty dtor size align ih hm; subst hm
    simp only [checkValue, ih rfl]
  case c9 => intro val m elem hm; subst hm; cases val <;> rfl
  case c10 => intro val m tn hm; subst hm; cases val <;> rfl
  case c11 => intro val m it hne hm; subst hm; cases val <;> rfl
  case c12 => intro val m hne hm; subst hm; cases val <;> rfl
  case c13 =>
    intro val m sf shl uf hne hm; subst hm
    cases val <;> first | rfl | exact absurd rfl (hne _)
  case c14 =>
    intro val m elem count hne hm; subst hm
    cases val <;> first | rfl | exact absurd rfl (hne _)
  case c15 =>
    intro val m fields chunks size align hne hm; subst hm
    cases val <;> first | rfl | exact absurd rfl (hne _)
  case c16 =>
    intro val m variants dty dtor size align hne hm; subst hm
    cases val <;> first | rfl | exact (hne _ _ variants.entries rfl rfl).elim
  case c17 =>
    intro val m pt hne hm; subst hm
    cases val <;> first | rfl | exact absurd rfl (hne _)
  case c18 =>
    intro val vals fst ty fields m ih1 ih2 hm; subst hm
    simp only [checkFields, ih1 rfl, ih2 rfl]
  case c19 =>
    intro t m x hne hm; subst hm
    cases x with
    | nil => cases t <;> rfl
    | cons val vals =>
      cases t with
      | nil => rfl
      | cons p fields => exact absurd rfl (hne val vals p.1 p.2 fields rfl)
  case c20 => intro m x data hm; subst hm; rfl
  case c21 =>
    intro ty tagger rest disc data m ih hm; subst hm
    simp only [checkVariant, ↓reduceIte, ih rfl]
  case c22 =>
    intro d ty tagger rest disc data m hne ih hm; subst hm
    simp only [checkVariant, hne, ↓reduceIte, ih rfl]

/-- `Machine::eval_un_op` reads only the machine's memory and vtables. -/
theorem evalUnOp_congr_mach {M1 M2 : Mach} (hmem : M1.mem = M2.mem)
    (hvt : M1.vtable_ptrs = M2.vtable_ptrs) (hprog : M1.prog = M2.prog)
    (op : Gen.UnOp) (arg : Val × Gen.Type) :
    evalUnOp op arg (some M1) = evalUnOp op arg (some M2) := by
  have hcv := checkValue_congr_mach hmem hvt hprog
  unfold evalUnOp evalCastOp transmute
  simp only [hcv]

/-- `retag_ptr` of `BasicMemory` on a machine whose single thread has a
non-empty stack is the identity. -/
theorem retagPtrBM_thread1 {M : Mach} {ctx : Ctx} {frames : List Frame}
    (hthr : M.threads = [thread1 ctx frames]) (hact : M.active_thread = 0) (hne : frames ≠ [])
    (ptr : Gen.Pointer Prov) : retagPtrBM M ptr = .ok ptr := by
  simp [retagPtrBM, listIndex, hthr, hact, thread1, hne]

/-- `List.mapM` congruence over the members of the list. -/
theorem mapM_congr_mem {α β : Type} {f g : α → Interp β} :
    ∀ (l : List α), (∀ x ∈ l, f x = g x) → l.mapM f = l.mapM g
  | [], _ => rfl
  | x :: xs, h => by
    simp only [List.mapM_cons, h x List.mem_cons_self,
      mapM_congr_mem xs (fun y hy => h y (List.mem_cons_of_mem _ hy))]

/-- `Machine::retag_val` depends on the machine only through `retagPtrBM`. -/
theorem retagVal_congr_mach {M1 M2 : Mach} (h : ∀ ptr, retagPtrBM M1 ptr = retagPtrBM M2 ptr)
    (fe : Bool) (v : Val) (t : Gen.Type) :
    retagVal M1 fe v t = retagVal M2 fe v t := by
  refine retagVal.induct
    (motive1 := fun v t => retagVal M1 fe v t = retagVal M2 fe v t)
    (motive2 := fun vals fs => retagTupleFields M1 fe vals fs = retagTupleFields M2 fe vals fs)
    ?d1 ?d2 ?d3 ?d4 ?d5 ?d6 ?d7 ?d8 ?d9 ?d10 ?d11 ?d12 ?d13 ?d14 ?d15 ?d16 ?d17 ?d18 ?d19 v t
  case d1 => intro i x; simp only [retagVal]
  case d2 => intro b x; simp only [retagVal]
  case d3 => intro c x; simp only [retagVal]
  case d4 => intro ptr pt; simp only [retagVal, h]
  case d5 => intro vals sf shl uf ih; simp only [retagVal, ih]
  case d6 =>
    intro vals elemTy count ih
    simp only [retagVal, mapM_congr_mem vals ih]
  case d7 =>
    intro d data variants dty dtor size align ih
    simp only [retagVal, ih]
  case d8 => intro x it h1 h2 h3; cases x <;> simp_all [retagVal]
  case d9 => intro x h1 h2 h3; cases x <;> simp_all [retagVal]
  case d10 => intro x fs cs sz al h1 h2 h3; cases x <;> simp_all [retagVal]
  case d11 => intro x pt h1 h2 h3 h4; cases x <;> simp_all [retagVal]
  case d12 => intro x sf shl uf h1 h2 h3 h4; cases x <;> simp_all [retagVal]
  case d13 => intro x el ct h1 h2 h3 h4; cases x <;> simp_all [retagVal]
  case d14 => intro x vs dty dtor sz al h1 h2 h3 h4; cases x <;> simp_all [retagVal]
  case d15 => intro x el h1 h2 h3; cases x <;> simp_all [retagVal]
  case d16 => intro x tn h1 h2 h3; cases x <;> simp_all [retagVal]
  case d17 => simp only [retagTupleFields]
  case d18 => intro val vals fst ty fields ih1 ih2; simp only [retagTupleFields, ih1, ih2]
  case d19 =>
    intro x x1 h1 h2
    cases x with
    | nil => cases x1 with
      | nil => exact (h1 rfl rfl).elim
      | cons p fs => simp only [retagTupleFields]
    | cons val vals => cases x1 with
      | nil => simp only [retagTupleFields]
      | cons p fs => exact (h2 val vals p.1 p.2 fs rfl rfl).elim

/-- `PlaceExpr::Field` evaluation is root evaluation followed by `fieldPlace`
on the machine the root evaluation returns, which it leaves unchanged. -/
theorem evalPlace_field_eq (m : Mach) (root : Gen.PlaceExpr) (field : Int) :
    evalPlace m (.Field root field) =
      evalPlace m root >>= fun ((rp, ty), m1) =>
        fieldPlace m1 rp ty field >>= fun r => pure (r, m1) := by
  rw [evalPlace]
  congr 1
  funext x
  obtain ⟨⟨rp, ty⟩, m1⟩ := x
  unfold fieldPlace
  dsimp only
  cases ty with
  | Tuple sizedFields sizedHeadLayout unsizedField =>
    dsimp only
    by_cases h1 : 0 ≤ field ∧ field < (sizedFields.length : Int)
    · simp only [h1, and_self, ↓reduceIte, bind_assoc]
      congr 1
      funext x
      obtain ⟨offset, fieldTy⟩ := x
      simp only
      congr 1
      funext lay
      congr 1
      funext rootSize
      split
      · rfl
      · simp only [bind_assoc, pure_bind]
    · simp only [h1, ↓reduceIte]
      by_cases h2 : field = (sizedFields.length : Int)
      · simp only [h2, ↓reduceIte]
        cases unsizedField with
        | none => rfl
        | some tailTy =>
          simp only [bind_assoc, pure_bind]
          congr 1
          funext lay
          congr 1
          funext tailAlign
          congr 1
          funext lay2
          congr 1
          funext rootSize
          split
          · rfl
          · simp only [bind_assoc, pure_bind]
      · simp only [h2, ↓reduceIte]
        rfl
  | Union fields chunks size align =>
    dsimp only
    simp only [bind_assoc]
    congr 1
    funext x
    obtain ⟨offset, fieldTy⟩ := x
    simp only
    congr 1
    funext lay
    congr 1
    funext rootSize
    split
    · rfl
    · simp only [bind_assoc, pure_bind]
  | _ => rfl

/-- `PlaceExpr::Deref` evaluation is operand evaluation followed by
`derefPlace` on the machine the operand evaluation returns, which it leaves
unchanged. -/
theorem evalPlace_deref_eq (m : Mach) (operand : Gen.ValueExpr) (ty : Gen.Type) :
    evalPlace m (.Deref operand ty) =
      evalValue m operand >>= fun ((v, vTy), m1) =>
        match v, vTy with
        | .Ptr ptr, .Ptr ptrType => derefPlace m1 ptr ptrType ty >>= fun r => pure (r, m1)
        | _, _ => specPanic "dereferencing a non-pointer" := by
  rw [evalPlace]
  congr 1
  funext x
  obtain ⟨⟨v, vTy⟩, m1⟩ := x
  dsimp only
  cases v <;> cases vTy <;> try rfl
  rename_i ptr ptrType
  unfold derefPlace
  dsimp only
  cases PtrType.safe_pointee ptrType with
  | none =>
    simp only [bind_assoc, pure_bind]
  | some pointee =>
    simp only [bind_assoc]
    congr 1
    funext al
    split
    · rfl
    · simp only [bind_assoc, pure_bind]

/-- The projection of `Machine::eval_place` for `PlaceExpr::Index` once the
root place `root` of type `ty` and the index value `idxVal` are known
(`spec/lang/step/expressions.md`); none of its steps changes the machine. -/
def indexPlaceAux (m : Mach) (root : Gen.Place BM) (ty : Gen.Type) (idxVal : Val) :
    Interp (Gen.Place BM × Gen.Type) := do
  let idx ← match idxVal with
    | .Int i => pure i
    | _ => specPanic "non-integer operand for array index"
  let (elemTy, count) ← match ty with
    | .Array elem count => pure (elem, count)
    | .Slice elem =>
      match root.ptr.metadata with
      | some (.ElementCount count) => pure (elem, count)
      | _ => specPanic "eval_place should always return a ptr which matches meta for the LayoutStrategy of ty"
    | _ => specPanic "index projection on non-indexable type"
  if idx < 0 ∨ idx ≥ count then
    ub "access to out-of-bounds index"
  else do
    let elemLayout ← Type.layout elemTy
    let elemSize ← LayoutStrategy.expect_size elemLayout "WF ensures array & slice elements are sized"
    let offset ← Size.mulInt elemSize idx
    let rootSize ← computeSize m (← Type.layout ty) root.ptr.metadata
    if offset.bytes ≤ rootSize.bytes then
      let ptr ← ptrOffsetInbounds m root.ptr.thin_pointer (offset.bytes : Int)
      pure ({ root with ptr := ThinPointer.widen ptr none }, elemTy)
    else
      specPanic "sanity check: the indexed offset should not be outside what the type allows."

/-- `PlaceExpr::Index` evaluation is root evaluation, index evaluation, and
`indexPlaceAux` on the machine the index evaluation returns, which it leaves
unchanged. -/
theorem evalPlace_index_eq (m : Mach) (root : Gen.PlaceExpr) (index : Gen.ValueExpr) :
    evalPlace m (.Index root index) =
      evalPlace m root >>= fun ((rp, ty), m1) =>
        evalValue m1 index >>= fun ((iv, _), m2) =>
          indexPlaceAux m2 rp ty iv >>= fun r => pure (r, m2) := by
  rw [evalPlace]
  congr 1
  funext x
  obtain ⟨⟨rp, ty⟩, m1⟩ := x
  dsimp only
  congr 1
  funext y
  obtain ⟨⟨iv, ivTy⟩, m2⟩ := y
  dsimp only
  unfold indexPlaceAux
  cases iv <;> try rfl
  rename_i i
  simp only [pure_bind]
  cases ty <;> try rfl
  · -- Array
    simp only
    split
    · rfl
    · simp only [bind_assoc]
      congr 1; funext el
      congr 1; funext es
      congr 1; funext off
      congr 1; funext lay
      congr 1; funext rs
      split
      · simp only [bind_assoc, pure_bind]
      · rfl
  · -- Slice
    rename_i elem
    cases hmd : rp.ptr.metadata with
    | none => rfl
    | some md =>
      cases md with
      | ElementCount count =>
        simp only
        split
        · rfl
        · simp only [bind_assoc]
          congr 1; funext el
          congr 1; funext es
          congr 1; funext off
          congr 1; funext lay
          congr 1; funext rs
          split
          · simp only [bind_assoc, pure_bind]
          · rfl
      | _ => rfl


/-- The operator step of `Machine::eval_value` for `ValueExpr::BinOp` on the
machine after both operands. -/
def binOpStep (m : Mach) (op : Gen.BinOp) (l r : Val × Gen.Type) : Interp (Val × Gen.Type) :=
  match op with
  | .PtrOffset inbounds => evalPtrOffset m inbounds l r
  | .PtrOffsetFrom inbounds nonneg => evalPtrOffsetFrom m inbounds nonneg l r
  | op => evalBinOp op l r

/-- `ValueExpr::BinOp` evaluation factors through `binOpStep`. -/
theorem evalValue_binOp_eq (m : Mach) (op : Gen.BinOp) (left right : Gen.ValueExpr) :
    evalValue m (.BinOp op left right) =
      evalValue m left >>= fun (l, m1) => evalValue m1 right >>= fun (r, m2) =>
        binOpStep m2 op l r >>= fun v => pure (v, m2) := by
  cases op <;> rfl

theorem placeLoad_rethread (m : Mach) (c : Ctx) (fs : List Frame) (pl : Gen.Place BM) (ty : Gen.Type) :
    (∀ v m2, placeLoad (rethread m c fs) pl ty = .ok (v, m2) →
      ∃ cm, m2 = { rethread m c fs with mem := cm } ∧
        placeLoad m pl ty = .ok (v, { m with mem := cm })) ∧
    (∀ err, placeLoad (rethread m c fs) pl ty = .error err →
      placeLoad m pl ty = .error err) := by
  unfold placeLoad
  by_cases hal : !pl.aligned
  · simp [hal, ub]
  · simp only [hal, Bool.false_eq_true, ↓reduceIte, typedLoad]
    cases hlay : Type.layout ty with
    | error e => simp
    | ok lay =>
      cases hsz : LayoutStrategy.expect_size lay "the callers ensure `ty` is sized" with
      | error e => simp [hsz]
      | ok sz =>
        simp only [hsz, ok_bind]
        have hmem : (rethread m c fs).mem = m.mem := rfl
        rw [hmem]
        cases hld : CM.load m.mem pl.ptr.thin_pointer sz ⟨1⟩ .None with
        | error e => simp
        | ok bc =>
          obtain ⟨bytes, cm⟩ := bc
          simp only [ok_bind]
          cases hdec : Type.decode ty bytes with
          | error e => simp
          | ok optVal =>
            cases optVal with
            | none => simp [ub]
            | some val =>
              simp only [ok_bind]
              have hcv : checkValue val ty (some { rethread m c fs with mem := cm }) =
                  checkValue val ty (some { m with mem := cm }) :=
                checkValue_congr_mach (M1 := { rethread m c fs with mem := cm })
                  (M2 := { m with mem := cm }) rfl rfl rfl val ty
              rw [hcv]
              cases hck : checkValue val ty (some { m with mem := cm }) with
              | error e => simp
              | ok u =>
                cases u
                simp

theorem placeStore_rethread (m : Mach) (c : Ctx) (fs : List Frame)
    (pl : Gen.Place BM) (val : Val) (ty : Gen.Type) :
    (∀ m2, placeStore (rethread m c fs) pl val ty = .ok m2 →
      ∃ cm, m2 = { rethread m c fs with mem := cm } ∧
        placeStore m pl val ty = .ok { m with mem := cm }) ∧
    (∀ err, placeStore (rethread m c fs) pl val ty = .error err →
      placeStore m pl val ty = .error err) := by
  unfold placeStore
  by_cases hal : !pl.aligned
  · simp [hal, ub]
  · simp only [hal, Bool.false_eq_true, ↓reduceIte, typedStore]
    have hcv : checkValue val ty (some (rethread m c fs)) = checkValue val ty (some m) :=
      checkValue_congr_mach (M1 := rethread m c fs) (M2 := m) rfl rfl rfl val ty
    rw [hcv]
    cases hck : checkValue val ty (some m) with
    | error e => simp [specPanic]
    | ok u =>
      cases u
      cases henc : Type.encode ty val with
      | error e => simp
      | ok bytes =>
        simp only [ok_bind]
        have hmem : (rethread m c fs).mem = m.mem := rfl
        rw [hmem]
        cases hst : CM.store m.mem pl.ptr.thin_pointer bytes ⟨1⟩ .None with
        | error e => simp
        | ok cm => simp

mutual

/-- `evalPlace` reads only `curFrame`, `prog.vtables`, `vtable_ptrs`, and `mem`
(and, for `PlaceExpr::Deref`, whatever `evalValue` reads), so replacing any
stack prefix ending in `fr` with `[curCtx.caller, fr]` changes neither its
result nor its effect on memory. -/
theorem evalPlace_rethread (pe : Gen.PlaceExpr) (m : Mach) (rootCtx curCtx : Ctx)
    (pre : List Frame) (fr : Frame)
    (hthr : m.threads = [thread1 rootCtx (pre ++ [fr])]) (hact : m.active_thread = 0) :
    (∀ pt m2, evalPlace (rethread m curCtx [curCtx.caller, fr]) pe = .ok (pt, m2) →
      ∃ cm, m2 = { rethread m curCtx [curCtx.caller, fr] with mem := cm } ∧
        evalPlace m pe = .ok (pt, { m with mem := cm })) ∧
    (∀ err, evalPlace (rethread m curCtx [curCtx.caller, fr]) pe = .error err →
      evalPlace m pe = .error err) := by
  match pe with
  | .Local name =>
    have hc1 : curFrame (rethread m curCtx [curCtx.caller, fr]) = .ok fr :=
      curFrame_eq ⟨rfl, hact, rfl⟩
    have hc2 : curFrame m = .ok fr :=
      curFrame_append ⟨hthr, hact, rfl⟩
    simp only [evalPlace, hc1, hc2, ok_bind]
    cases hT : mapIndex fr.func.locals name "self.cur_frame().func.locals[name]" with
    | error err => simp
    | ok T =>
      simp only [ok_bind]
      cases mapGet fr.locals name with
      | none => simp [ub]
      | some p =>
        refine ⟨fun pt m2 h => ?_, fun err h => by simp at h⟩
        simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨m.mem, rfl, by cases m; rfl⟩
  | .Deref operand ty =>
    obtain ⟨hvok, hverr⟩ := evalValue_rethread operand m rootCtx curCtx pre fr hthr hact
    rw [evalPlace_deref_eq, evalPlace_deref_eq]
    cases hev : evalValue (rethread m curCtx [curCtx.caller, fr]) operand with
    | error err => simp [hverr err hev]
    | ok vtm =>
      obtain ⟨⟨val, opTy⟩, m1⟩ := vtm
      obtain ⟨cm, rfl, hm1⟩ := hvok _ m1 hev
      simp only [hm1, ok_bind]
      have hd : ∀ ptr ptrType, derefPlace ({ rethread m curCtx [curCtx.caller, fr] with mem := cm } : Mach)
          ptr ptrType ty = derefPlace { m with mem := cm } ptr ptrType ty := fun _ _ => rfl
      cases val <;> cases opTy <;> try (simp [specPanic]; done)
      rename_i ptr ptrType
      simp only [hd]
      cases hdp : derefPlace { m with mem := cm } ptr ptrType ty with
      | error err => simp
      | ok r =>
        refine ⟨fun pt m2 h => ?_, fun err h => by simp at h⟩
        simp only [ok_bind, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨cm, rfl, rfl⟩
  | .Field root field =>
    obtain ⟨hrok, hrerr⟩ := evalPlace_rethread root m rootCtx curCtx pre fr hthr hact
    rw [evalPlace_field_eq, evalPlace_field_eq]
    cases hep : evalPlace (rethread m curCtx [curCtx.caller, fr]) root with
    | error err => simp [hrerr err hep]
    | ok ptm =>
      obtain ⟨⟨rp, ty⟩, m1⟩ := ptm
      obtain ⟨cm, rfl, hm1⟩ := hrok _ m1 hep
      simp only [hm1, ok_bind]
      have hfp : fieldPlace ({ rethread m curCtx [curCtx.caller, fr] with mem := cm } : Mach)
          rp ty field = fieldPlace { m with mem := cm } rp ty field := rfl
      rw [hfp]
      cases hf : fieldPlace { m with mem := cm } rp ty field with
      | error err => simp
      | ok r =>
        refine ⟨fun pt m2 h => ?_, fun err h => by simp at h⟩
        simp only [ok_bind, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨cm, rfl, rfl⟩
  | .Index root index =>
    obtain ⟨hrok, hrerr⟩ := evalPlace_rethread root m rootCtx curCtx pre fr hthr hact
    rw [evalPlace_index_eq, evalPlace_index_eq]
    cases hep : evalPlace (rethread m curCtx [curCtx.caller, fr]) root with
    | error err => simp [hrerr err hep]
    | ok ptm =>
      obtain ⟨⟨rp, ty⟩, m1⟩ := ptm
      obtain ⟨cm1, rfl, hm1⟩ := hrok _ m1 hep
      simp only [hm1, ok_bind]
      have hsub : ({ rethread m curCtx [curCtx.caller, fr] with mem := cm1 } : Mach) =
          rethread { m with mem := cm1 } curCtx [curCtx.caller, fr] := rfl
      rw [hsub]
      obtain ⟨hiok, hierr⟩ :=
        evalValue_rethread index { m with mem := cm1 } rootCtx curCtx pre fr hthr hact
      cases hiv : evalValue (rethread { m with mem := cm1 } curCtx [curCtx.caller, fr]) index with
      | error err => simp [hierr err hiv]
      | ok ivm =>
        obtain ⟨⟨iv, ivTy⟩, m2⟩ := ivm
        obtain ⟨cm2, rfl, hm2⟩ := hiok _ m2 hiv
        rw [mach_mem_mem] at hm2
        simp only [hm2, ok_bind]
        have hip : indexPlaceAux ({ rethread { m with mem := cm1 } curCtx [curCtx.caller, fr] with
            mem := cm2 } : Mach) rp ty iv = indexPlaceAux { m with mem := cm2 } rp ty iv := rfl
        rw [hip]
        cases hix : indexPlaceAux { m with mem := cm2 } rp ty iv with
        | error err => simp
        | ok r =>
          refine ⟨fun pt m3 h => ?_, fun err h => by simp at h⟩
          simp only [ok_bind, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨cm2, rfl, rfl⟩
  | .Downcast _ _ =>
    simp [evalPlace, unsupported]

/-- Lifting `evalValue` from `[curCtx.caller, fr]` to an arbitrary stack prefix
`pre ++ [fr]`. -/
theorem evalValue_rethread (e : Gen.ValueExpr) (m : Mach) (rootCtx curCtx : Ctx)
    (pre : List Frame) (fr : Frame)
    (hthr : m.threads = [thread1 rootCtx (pre ++ [fr])]) (hact : m.active_thread = 0) :
    (∀ vt m2, evalValue (rethread m curCtx [curCtx.caller, fr]) e = .ok (vt, m2) →
      ∃ cm, m2 = { rethread m curCtx [curCtx.caller, fr] with mem := cm } ∧
        evalValue m e = .ok (vt, { m with mem := cm })) ∧
    (∀ err, evalValue (rethread m curCtx [curCtx.caller, fr]) e = .error err →
      evalValue m e = .error err) := by
  match e with
  | .Constant cst ty =>
    have hc : evalConstant (rethread m curCtx [curCtx.caller, fr]) cst = evalConstant m cst := rfl
    simp only [evalValue, hc]
    cases hec : evalConstant m cst with
    | error err => simp
    | ok v =>
      refine ⟨fun vt m2 h => ?_, fun err h => by simp at h⟩
      simp at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨m.mem, rfl, rfl⟩
  | .Tuple exprs ty =>
    obtain ⟨hok, herr⟩ := evalValues_rethread exprs m rootCtx curCtx pre fr hthr hact
    simp only [evalValue]
    cases hev : evalValues (rethread m curCtx [curCtx.caller, fr]) exprs with
    | error err =>
      simp [herr err hev]
    | ok vm =>
      obtain ⟨vals, m1⟩ := vm
      obtain ⟨cm, rfl, hm1⟩ := hok vals m1 hev
      simp [hm1]
  | .Load source =>
    obtain ⟨hpok, hperr⟩ := evalPlace_rethread source m rootCtx curCtx pre fr hthr hact
    simp only [evalValue]
    cases hep : evalPlace (rethread m curCtx [curCtx.caller, fr]) source with
    | error err => simp [hperr err hep]
    | ok ptm =>
      obtain ⟨⟨pl, ty⟩, m1⟩ := ptm
      obtain ⟨cm1, rfl, hpm⟩ := hpok _ m1 hep
      simp only [hpm, ok_bind]
      have hsub : ({ rethread m curCtx [curCtx.caller, fr] with mem := cm1 } : Mach) =
          rethread { m with mem := cm1 } curCtx [curCtx.caller, fr] := rfl
      rw [hsub]
      obtain ⟨hlok, hlerr⟩ :=
        placeLoad_rethread { m with mem := cm1 } curCtx [curCtx.caller, fr] pl ty
      cases hld : placeLoad (rethread { m with mem := cm1 } curCtx [curCtx.caller, fr]) pl ty with
      | error err => simp [hlerr err hld]
      | ok vm =>
        obtain ⟨v, m2⟩ := vm
        obtain ⟨cm, rfl, hm2⟩ := hlok v m2 hld
        rw [mach_mem_mem] at hm2
        simp only [hm2, ok_bind]
        refine ⟨fun vt m3 h => ?_, fun err h => by simp at h⟩
        simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨cm, rfl, rfl⟩
  | .AddrOf target ptrTy =>
    obtain ⟨hpok, hperr⟩ := evalPlace_rethread target m rootCtx curCtx pre fr hthr hact
    simp only [evalValue]
    cases hep : evalPlace (rethread m curCtx [curCtx.caller, fr]) target with
    | error err => simp [hperr err hep]
    | ok ptm =>
      obtain ⟨⟨pl, ty⟩, m1⟩ := ptm
      obtain ⟨cm1, rfl, hpm⟩ := hpok _ m1 hep
      simp only [hpm, ok_bind]
      have hcv : checkValue (.Ptr pl.ptr) (.Ptr ptrTy)
          (some ({ rethread m curCtx [curCtx.caller, fr] with mem := cm1 } : Mach)) =
          checkValue (.Ptr pl.ptr) (.Ptr ptrTy) (some { m with mem := cm1 }) :=
        checkValue_congr_mach (M1 := { rethread m curCtx [curCtx.caller, fr] with mem := cm1 })
          (M2 := { m with mem := cm1 }) rfl rfl rfl _ _
      have hr1 : retagPtrBM ({ rethread m curCtx [curCtx.caller, fr] with mem := cm1 } : Mach)
          pl.ptr = .ok pl.ptr :=
        retagPtrBM_thread1 (M := { rethread m curCtx [curCtx.caller, fr] with mem := cm1 })
          (ctx := curCtx) (frames := [curCtx.caller, fr]) rfl hact (by simp) pl.ptr
      have hr2 : retagPtrBM ({ m with mem := cm1 } : Mach) pl.ptr = .ok pl.ptr :=
        retagPtrBM_thread1 (M := { m with mem := cm1 }) (ctx := rootCtx) (frames := pre ++ [fr])
          hthr hact (by simp) pl.ptr
      rw [hcv, hr1, hr2]
      cases hck : checkValue (.Ptr pl.ptr) (.Ptr ptrTy) (some { m with mem := cm1 }) with
      | error err => simp
      | ok u =>
        cases u
        refine ⟨fun vt m2 h => ?_, fun err h => by simp at h⟩
        simp at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨cm1, rfl, rfl⟩
  | .UnOp op operand =>
    obtain ⟨hok, herr⟩ := evalValue_rethread operand m rootCtx curCtx pre fr hthr hact
    simp only [evalValue]
    cases hev : evalValue (rethread m curCtx [curCtx.caller, fr]) operand with
    | error err => simp [herr err hev]
    | ok am =>
      obtain ⟨arg, m1⟩ := am
      obtain ⟨cm, rfl, hm1⟩ := hok arg m1 hev
      simp only [hm1, ok_bind]
      have huo : evalUnOp op arg (some ({ rethread m curCtx [curCtx.caller, fr] with mem := cm } : Mach)) =
          evalUnOp op arg (some { m with mem := cm }) :=
        evalUnOp_congr_mach (M1 := { rethread m curCtx [curCtx.caller, fr] with mem := cm })
          (M2 := { m with mem := cm }) rfl rfl rfl op arg
      rw [huo]
      cases evalUnOp op arg (some { m with mem := cm }) with
      | error err => simp
      | ok v =>
        refine ⟨fun vt m2 h => ?_, fun err h => by simp at h⟩
        simp at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨cm, rfl, rfl⟩
  | .BinOp op left right =>
    obtain ⟨hlok, hlerr⟩ := evalValue_rethread left m rootCtx curCtx pre fr hthr hact
    rw [evalValue_binOp_eq, evalValue_binOp_eq]
    cases hlv : evalValue (rethread m curCtx [curCtx.caller, fr]) left with
    | error err => simp [hlerr err hlv]
    | ok lm1 =>
      obtain ⟨l, m1⟩ := lm1
      obtain ⟨cm1, rfl, hml⟩ := hlok l m1 hlv
      have hsub : ({ rethread m curCtx [curCtx.caller, fr] with mem := cm1 } : Mach) =
          rethread { m with mem := cm1 } curCtx [curCtx.caller, fr] := rfl
      simp only [hml, ok_bind]
      rw [hsub]
      obtain ⟨hrok, hrerr⟩ :=
        evalValue_rethread right { m with mem := cm1 } rootCtx curCtx pre fr hthr hact
      cases hrv : evalValue (rethread { m with mem := cm1 } curCtx [curCtx.caller, fr]) right with
      | error err => simp [hrerr err hrv]
      | ok rm2 =>
        obtain ⟨r, m2⟩ := rm2
        obtain ⟨cm2, rfl, hmr⟩ := hrok r m2 hrv
        rw [mach_mem_mem] at hmr
        simp only [hmr, ok_bind]
        have hbo : binOpStep ({ rethread { m with mem := cm1 } curCtx [curCtx.caller, fr] with
            mem := cm2 } : Mach) op l r = binOpStep { m with mem := cm2 } op l r := by
          cases op <;> rfl
        rw [hbo]
        cases binOpStep { m with mem := cm2 } op l r with
        | error err => simp
        | ok vt =>
          refine ⟨fun vt' m3 h => ?_, fun err h => by simp at h⟩
          simp at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨cm2, rfl, rfl⟩
  | .Union _ _ _ | .Variant _ _ _ | .GetDiscriminant _ =>
    simp [evalValue, unsupported]

theorem evalValues_rethread (es : List Gen.ValueExpr) (m : Mach) (rootCtx curCtx : Ctx)
    (pre : List Frame) (fr : Frame)
    (hthr : m.threads = [thread1 rootCtx (pre ++ [fr])]) (hact : m.active_thread = 0) :
    (∀ vs m2, evalValues (rethread m curCtx [curCtx.caller, fr]) es = .ok (vs, m2) →
      ∃ cm, m2 = { rethread m curCtx [curCtx.caller, fr] with mem := cm } ∧
        evalValues m es = .ok (vs, { m with mem := cm })) ∧
    (∀ err, evalValues (rethread m curCtx [curCtx.caller, fr]) es = .error err →
      evalValues m es = .error err) := by
  cases es with
  | nil =>
    refine ⟨fun vs m2 h => ?_, fun err h => by simp [evalValues] at h⟩
    simp [evalValues] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨m.mem, rfl, rfl⟩
  | cons e rest =>
    obtain ⟨hok1, herr1⟩ := evalValue_rethread e m rootCtx curCtx pre fr hthr hact
    simp only [evalValues]
    cases he1 : evalValue (rethread m curCtx [curCtx.caller, fr]) e with
    | error err => simp [herr1 err he1]
    | ok vtm1 =>
      obtain ⟨⟨v, _⟩, m1⟩ := vtm1
      obtain ⟨cm1, rfl, hm1⟩ := hok1 _ m1 he1
      have hsub : ({ rethread m curCtx [curCtx.caller, fr] with mem := cm1 } : Mach) =
          rethread { m with mem := cm1 } curCtx [curCtx.caller, fr] := rfl
      rw [hsub]
      obtain ⟨hokr, herrr⟩ :=
        evalValues_rethread rest { m with mem := cm1 } rootCtx curCtx pre fr hthr hact
      simp only [hm1, ok_bind]
      cases her : evalValues (rethread { m with mem := cm1 } curCtx [curCtx.caller, fr]) rest with
      | error err => simp [herrr err her]
      | ok vsm2 =>
        obtain ⟨vs, m2⟩ := vsm2
        obtain ⟨cm2, rfl, hmr⟩ := hokr vs m2 her
        rw [mach_mem_mem] at hmr
        simp only [hmr, ok_bind, pure_ok]
        refine ⟨fun vs' m3 h => ?_, fun err h => by simp at h⟩
        simp at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨cm2, rfl, rfl⟩

end

/-- Deref-free place expressions (`PlaceExpr::Local` and chains of
`PlaceExpr::Field`): every place the fragment's statements, operands, call
arguments, and call destinations translate to (`translatePlace`). Only
`unit_place()` (an intrinsic's destination) dereferences. -/
def derefFreePlace : Gen.PlaceExpr → Bool
  | .Local _ => true
  | .Field root _ => derefFreePlace root
  | _ => false

/-- A deref-free place evaluates without touching the machine. -/
theorem evalPlace_derefFree_mach : ∀ (pe : Gen.PlaceExpr), derefFreePlace pe = true →
    ∀ (m : Mach) r m', evalPlace m pe = .ok (r, m') → m' = m
  | .Local name, _, m, r, m', h => by
    simp only [evalPlace] at h
    cases hcf : curFrame m with
    | error e => simp [hcf] at h
    | ok fr =>
      simp only [hcf, ok_bind] at h
      cases hT : mapIndex fr.func.locals name "self.cur_frame().func.locals[name]" with
      | error e => simp [hT] at h
      | ok T =>
        simp only [hT, ok_bind] at h
        split at h
        · simp [ub] at h
        · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
          exact h.2.symm
  | .Field root field, hdf, m, r, m', h => by
    rw [evalPlace_field_eq] at h
    cases hep : evalPlace m root with
    | error e => simp [hep] at h
    | ok ptm =>
      obtain ⟨⟨rp, ty⟩, m1⟩ := ptm
      have hm1 := evalPlace_derefFree_mach root (by simpa [derefFreePlace] using hdf) m _ _ hep
      simp only [hep, ok_bind] at h
      cases hf : fieldPlace m1 rp ty field with
      | error e => simp [hf] at h
      | ok r' =>
        simp only [hf, ok_bind, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        rw [← h.2]
        exact hm1
  | .Deref _ _, hdf, _, _, _, _ => by simp [derefFreePlace] at hdf
  | .Index _ _, hdf, _, _, _, _ => by simp [derefFreePlace] at hdf
  | .Downcast _ _, hdf, _, _, _, _ => by simp [derefFreePlace] at hdf

/-- For a deref-free place, `evalPlace` on any stack prefix ending in `fr`
agrees with `evalPlace` on `[curCtx.caller, fr]`, up to the (unchanged)
machine it returns. -/
theorem evalPlace_rethread_derefFree (pe : Gen.PlaceExpr) (hdf : derefFreePlace pe = true)
    (m : Mach) (rootCtx curCtx : Ctx) (pre : List Frame) (fr : Frame)
    (hthr : m.threads = [thread1 rootCtx (pre ++ [fr])]) (hact : m.active_thread = 0) :
    evalPlace m pe =
      (evalPlace (rethread m curCtx [curCtx.caller, fr]) pe).map (fun r => (r.1, m)) := by
  obtain ⟨hok, herr⟩ := evalPlace_rethread pe m rootCtx curCtx pre fr hthr hact
  cases h : evalPlace (rethread m curCtx [curCtx.caller, fr]) pe with
  | error e => simp [herr e h, Except.map]
  | ok r =>
    obtain ⟨pt, m2⟩ := r
    obtain ⟨cm, _, hpm⟩ := hok pt m2 h
    have hm := evalPlace_derefFree_mach pe hdf m _ _ hpm
    rw [hm] at hpm
    simp [hpm, Except.map]

/-- A field chain on a deref-free root is deref-free. -/
theorem translateFieldPlace_derefFree : ∀ (projs : List ProjectionElem) (root pe : Gen.PlaceExpr),
    derefFreePlace root = true → translateFieldPlace root projs = some pe →
    derefFreePlace pe = true
  | [], root, pe, hr, h => by
    simp only [translateFieldPlace, Option.some.injEq] at h
    subst h; exact hr
  | .field idx _ :: rest, root, pe, hr, h => by
    simp only [translateFieldPlace] at h
    exact translateFieldPlace_derefFree rest _ pe (by simpa [derefFreePlace] using hr) h
  | .deref :: _, _, _, _, h | .index _ :: _, _, _, _, h | .constantIndex _ _ _ :: _, _, _, _, h
  | .subslice _ _ _ :: _, _, _, _, h | .downcast _ _ :: _, _, _, _, h
  | .opaqueCast _ :: _, _, _, _, h => by simp [translateFieldPlace] at h

theorem translatePlace_derefFree {p : Place} {pe : Gen.PlaceExpr}
    (h : translatePlace decls p = some pe)
    (hfld : ∀ e ∈ p.projection, ∃ idx ty, e = .field idx ty) : derefFreePlace pe = true := by
  obtain ⟨i, proj⟩ := p
  cases proj with
  | nil =>
    simp only [translatePlace, Option.some.injEq] at h
    subst h; rfl
  | cons e rest =>
    obtain ⟨idx, ty, rfl⟩ := hfld e (by simp)
    simp only [translatePlace] at h
    exact translateFieldPlace_derefFree _ _ pe rfl h

private theorem tryMutateCurFrame_rethread_aux (m : Mach) (rootCtx curCtx : Ctx)
    (pre : List Frame) (fr : Frame)
    (hthr : m.threads = [thread1 rootCtx (pre ++ [fr])]) (hact : m.active_thread = 0)
    (g : Frame → Gen.ConcurrentMemory BM → Interp (Frame × Gen.ConcurrentMemory BM)) :
    (∀ m2 fr' A',
      tryMutateCurFrame (rethread m curCtx [curCtx.caller, fr]) g = .ok m2 →
      Shape m2 curCtx [curCtx.caller, fr'] A' →
      tryMutateCurFrame m g = .ok (rethread m2 rootCtx (pre ++ [fr'])) ∧
        Shape (rethread m2 rootCtx (pre ++ [fr'])) rootCtx (pre ++ [fr']) A' ∧
        (rethread m2 rootCtx (pre ++ [fr'])).prog = m.prog ∧
        (rethread m2 rootCtx (pre ++ [fr'])).fn_ptrs = m.fn_ptrs) ∧
    (∀ err, tryMutateCurFrame (rethread m curCtx [curCtx.caller, fr]) g = .error err →
      tryMutateCurFrame m g = .error err) := by
  have hact1 : activeThread (rethread m curCtx [curCtx.caller, fr]) =
      .ok (thread1 curCtx [curCtx.caller, fr]) := by
    simp [activeThread, listIndex, rethread, hact]
  have hact2 : activeThread m = .ok (thread1 rootCtx (pre ++ [fr])) := by
    simp [activeThread, listIndex, hthr, hact]
  have hlast := getLast?_append_singleton pre fr
  have hdrop := dropLast_append_singleton pre fr
  have hmem : (rethread m curCtx [curCtx.caller, fr]).mem = m.mem := rfl
  simp only [tryMutateCurFrame, hact1, hact2, ok_bind, thread1, List.getLast?_cons_cons,
    List.getLast?_singleton, hlast, hdrop, hmem]
  cases hg : g fr m.mem with
  | error err => simp
  | ok fc =>
    obtain ⟨fr1, cm1⟩ := fc
    simp only [ok_bind, listSet, rethread, hact, hthr, List.dropLast]
    refine ⟨fun m2 fr' A' hm2 hsh2 => ?_, fun err herr => by simp at herr⟩
    simp at hm2
    subst hm2
    have hthrEq := hsh2.threads
    simp [thread1] at hthrEq
    subst hthrEq
    exact ⟨rfl, ⟨rfl, hsh2.active, hsh2.allocs⟩, rfl, rfl⟩

private theorem frame_eq_of_shape {m : Mach} {ctx : Ctx} {fr fr' : Frame} {A' : List Gen.Allocation}
    (hthr : m.threads = [thread1 ctx [ctx.caller, fr]])
    (hsh : Shape m ctx [ctx.caller, fr'] A') : fr' = fr := by
  have h := hsh.threads
  rw [hthr] at h
  simp [thread1] at h
  exact h.symm

/-- Lifting `evalStatement` from `[curCtx.caller, fr]` to an arbitrary stack
prefix `pre ++ [fr]`. -/
theorem evalStatement_rethread (st : Gen.Statement) (m : Mach) (rootCtx curCtx : Ctx)
    (pre : List Frame) (fr : Frame)
    (hthr : m.threads = [thread1 rootCtx (pre ++ [fr])]) (hact : m.active_thread = 0) :
    (∀ m2 fr' A',
      evalStatement (rethread m curCtx [curCtx.caller, fr]) st = .ok m2 →
      Shape m2 curCtx [curCtx.caller, fr'] A' →
      evalStatement m st = .ok (rethread m2 rootCtx (pre ++ [fr'])) ∧
        Shape (rethread m2 rootCtx (pre ++ [fr'])) rootCtx (pre ++ [fr']) A' ∧
        (rethread m2 rootCtx (pre ++ [fr'])).prog = m.prog ∧
        (rethread m2 rootCtx (pre ++ [fr'])).fn_ptrs = m.fn_ptrs) ∧
    (∀ err, evalStatement (rethread m curCtx [curCtx.caller, fr]) st = .error err →
      evalStatement m st = .error err) := by
  match st with
  | .Assign dst src =>
    obtain ⟨hpok, hperr⟩ := evalPlace_rethread dst m rootCtx curCtx pre fr hthr hact
    simp only [evalStatement]
    cases hep : evalPlace (rethread m curCtx [curCtx.caller, fr]) dst with
    | error err => simp [hperr err hep]
    | ok ptm =>
      obtain ⟨⟨pl, ty⟩, m0⟩ := ptm
      obtain ⟨cm0, rfl, hpm⟩ := hpok _ m0 hep
      simp only [hpm, ok_bind]
      have hsub0 : ({ rethread m curCtx [curCtx.caller, fr] with mem := cm0 } : Mach) =
          rethread { m with mem := cm0 } curCtx [curCtx.caller, fr] := rfl
      rw [hsub0]
      obtain ⟨hvok, hverr⟩ :=
        evalValue_rethread src { m with mem := cm0 } rootCtx curCtx pre fr hthr hact
      cases hev : evalValue (rethread { m with mem := cm0 } curCtx [curCtx.caller, fr]) src with
      | error err => simp [hverr err hev]
      | ok vtm1 =>
        obtain ⟨⟨val, _⟩, m1⟩ := vtm1
        obtain ⟨cm1, rfl, hm1⟩ := hvok _ m1 hev
        rw [mach_mem_mem] at hm1
        have hsub : ({ rethread { m with mem := cm0 } curCtx [curCtx.caller, fr] with
            mem := cm1 } : Mach) = rethread { m with mem := cm1 } curCtx [curCtx.caller, fr] := rfl
        rw [hsub]
        obtain ⟨hsok, hserr⟩ :=
          placeStore_rethread { m with mem := cm1 } curCtx [curCtx.caller, fr] pl val ty
        simp only [hm1, ok_bind]
        cases hps : placeStore (rethread { m with mem := cm1 } curCtx [curCtx.caller, fr]) pl val ty with
        | error err => simp [hserr err hps]
        | ok m2 =>
          obtain ⟨cm2, rfl, hms⟩ := hsok m2 hps
          rw [mach_mem_mem] at hms
          refine ⟨fun m2' fr' A' hm2' hsh2 => ?_, fun err herr => by simp at herr⟩
          simp at hm2'
          subst hm2'
          have hfrEq := frame_eq_of_shape rfl hsh2
          cases hfrEq
          have hre := rethread_with_mem_eq (curCtx := curCtx) hthr cm2
          have hre0 :
              rethread { rethread { m with mem := cm1 } curCtx [curCtx.caller, fr] with mem := cm2 }
                rootCtx (pre ++ [fr]) = { m with mem := cm2 } := hre
          rw [hre0]
          exact ⟨hms, ⟨hthr, hact, hsh2.allocs⟩, rfl, rfl⟩
  | .PlaceMention pl =>
    obtain ⟨hpok, hperr⟩ := evalPlace_rethread pl m rootCtx curCtx pre fr hthr hact
    simp only [evalStatement]
    cases hep : evalPlace (rethread m curCtx [curCtx.caller, fr]) pl with
    | error err => simp [hperr err hep]
    | ok ptm =>
      obtain ⟨pt, m0⟩ := ptm
      obtain ⟨cm0, rfl, hpm⟩ := hpok _ m0 hep
      simp only [hpm, ok_bind]
      refine ⟨fun m2 fr' A' hm2 hsh2 => ?_, fun err herr => by simp at herr⟩
      simp only [pure, Except.pure, Except.ok.injEq] at hm2
      subst hm2
      have hfrEq := frame_eq_of_shape rfl hsh2
      cases hfrEq
      have hre : rethread { rethread m curCtx [curCtx.caller, fr] with mem := cm0 } rootCtx
          (pre ++ [fr]) = { m with mem := cm0 } :=
        rethread_with_mem_eq (curCtx := curCtx) hthr cm0
      rw [hre]
      exact ⟨rfl, ⟨hthr, hact, hsh2.allocs⟩, rfl, rfl⟩
  | .Validate place fnEntry =>
    obtain ⟨hpok, hperr⟩ := evalPlace_rethread place m rootCtx curCtx pre fr hthr hact
    simp only [evalStatement]
    cases hep : evalPlace (rethread m curCtx [curCtx.caller, fr]) place with
    | error err => simp [hperr err hep]
    | ok ptm =>
      obtain ⟨⟨p, ty⟩, m0⟩ := ptm
      obtain ⟨cm0, rfl, hpm⟩ := hpok _ m0 hep
      simp only [hpm, ok_bind]
      have hsub0 : ({ rethread m curCtx [curCtx.caller, fr] with mem := cm0 } : Mach) =
          rethread { m with mem := cm0 } curCtx [curCtx.caller, fr] := rfl
      rw [hsub0]
      obtain ⟨hlok, hlerr⟩ :=
        placeLoad_rethread { m with mem := cm0 } curCtx [curCtx.caller, fr] p ty
      cases hld : placeLoad (rethread { m with mem := cm0 } curCtx [curCtx.caller, fr]) p ty with
      | error err => simp [hlerr err hld]
      | ok vm =>
        obtain ⟨val, m1⟩ := vm
        obtain ⟨cm1, rfl, hm1⟩ := hlok val m1 hld
        rw [mach_mem_mem] at hm1
        simp only [hm1, ok_bind]
        have hsub1 : ({ rethread { m with mem := cm0 } curCtx [curCtx.caller, fr] with
            mem := cm1 } : Mach) = rethread { m with mem := cm1 } curCtx [curCtx.caller, fr] := rfl
        rw [hsub1]
        have hrv : retagVal (rethread { m with mem := cm1 } curCtx [curCtx.caller, fr]) fnEntry val ty =
            retagVal { m with mem := cm1 } fnEntry val ty :=
          retagVal_congr_mach (fun ptr => by
            rw [retagPtrBM_thread1 (M := rethread { m with mem := cm1 } curCtx [curCtx.caller, fr])
                (ctx := curCtx) (frames := [curCtx.caller, fr]) rfl hact (by simp) ptr,
              retagPtrBM_thread1 (M := { m with mem := cm1 }) (ctx := rootCtx)
                (frames := pre ++ [fr]) hthr hact (by simp) ptr]) fnEntry val ty
        rw [hrv]
        cases hrt : retagVal { m with mem := cm1 } fnEntry val ty with
        | error err => simp
        | ok val' =>
          simp only [ok_bind]
          obtain ⟨hsok, hserr⟩ :=
            placeStore_rethread { m with mem := cm1 } curCtx [curCtx.caller, fr] p val' ty
          cases hps : placeStore (rethread { m with mem := cm1 } curCtx [curCtx.caller, fr]) p val' ty with
          | error err => simp [hserr err hps]
          | ok m2 =>
            obtain ⟨cm2, rfl, hms⟩ := hsok m2 hps
            rw [mach_mem_mem] at hms
            refine ⟨fun m2' fr' A' hm2' hsh2 => ?_, fun err herr => by simp at herr⟩
            simp at hm2'
            subst hm2'
            have hfrEq := frame_eq_of_shape rfl hsh2
            cases hfrEq
            have hre := rethread_with_mem_eq (curCtx := curCtx) hthr cm2
            have hre0 :
                rethread { rethread { m with mem := cm1 } curCtx [curCtx.caller, fr] with mem := cm2 }
                  rootCtx (pre ++ [fr]) = { m with mem := cm2 } := hre
            rw [hre0]
            exact ⟨hms, ⟨hthr, hact, hsh2.allocs⟩, rfl, rfl⟩
  | .StorageLive loc =>
    exact tryMutateCurFrame_rethread_aux m rootCtx curCtx pre fr hthr hact
      (fun f cm => storageLive f cm loc)
  | .StorageDead loc =>
    exact tryMutateCurFrame_rethread_aux m rootCtx curCtx pre fr hthr hact
      (fun f cm => storageDead f cm loc)
  | .Deinit pl =>
    obtain ⟨hpok, hperr⟩ := evalPlace_rethread pl m rootCtx curCtx pre fr hthr hact
    simp only [evalStatement]
    cases hep : evalPlace (rethread m curCtx [curCtx.caller, fr]) pl with
    | error err => simp [hperr err hep]
    | ok ptm =>
      obtain ⟨⟨p, ty⟩, m0⟩ := ptm
      obtain ⟨cm0, rfl, hpm⟩ := hpok _ m0 hep
      simp only [hpm, ok_bind]
      by_cases hal : !p.aligned
      · simp [hal, ub]
      · simp only [hal, Bool.false_eq_true, ↓reduceIte]
        cases hlay : Type.layout ty with
        | error err => simp
        | ok lay =>
          cases hsz : LayoutStrategy.expect_size lay "WF ensures deinits are sized" with
          | error err => simp [hsz]
          | ok sz =>
            simp only [hsz, ok_bind]
            cases hdi : CM.deinit cm0 p.ptr.thin_pointer sz ⟨1⟩ with
            | error err => simp
            | ok cm2 =>
              simp only [ok_bind]
              refine ⟨fun m2 fr' A' hm2 hsh2 => ?_, fun err herr => by simp at herr⟩
              simp only [pure, Except.pure, Except.ok.injEq] at hm2
              subst hm2
              have hfrEq := frame_eq_of_shape rfl hsh2
              cases hfrEq
              have hre : rethread { { rethread m curCtx [curCtx.caller, fr] with mem := cm0 } with
                  mem := cm2 } rootCtx (pre ++ [fr]) = { m with mem := cm2 } :=
                rethread_with_mem_eq (curCtx := curCtx) hthr cm2
              rw [hre]
              exact ⟨rfl, ⟨hthr, hact, hsh2.allocs⟩, rfl, rfl⟩
  | .SetDiscriminant _ _ =>
    simp [evalStatement, unsupported]

/-! ### `LocalsOkA`, `BaseCandBounded`, ABI reflexivity, and `CallerDestRel` helpers -/

theorem LocalsOkA.append_dead {body : CapturedMir} {ctx : Ctx} {al : List Nat}
    {locals : List LocalSlot} {lm : Map Gen.LocalName Ptr} {A R : List Gen.Allocation}
    (hlo : LocalsOkA body ctx al locals lm A) (hdead : ∀ b ∈ R, b.live = false) :
    LocalsOkA body ctx al locals lm (A ++ R) := by
  refine {
    nlocals := hlo.nlocals
    slots := hlo.slots
    base := by obtain ⟨R0, hR0⟩ := hlo.base; exact ⟨R0 ++ R, by rw [hR0, List.append_assoc]⟩
    keysNodup := hlo.keysNodup
    keysLocal := hlo.keysLocal
    live := hlo.live
    storage := fun i d slot p hd hs hp => by
      have hst := hlo.storage i d slot p hd hs hp
      obtain ⟨id0, hpid0, hlt⟩ := hst.exists_id_lt
      refine hst.congr_getElem? (fun id hpid => ?_)
      have : id0 = id := (prov_inj id0 id).mp (hpid0.symm.trans hpid)
      subst this
      exact List.getElem?_append_left hlt
    inj := hlo.inj
    owned := fun id a ha hlive hb => by
      by_cases hid : id < A.length
      · rw [List.getElem?_append_left hid] at ha
        exact hlo.owned id a ha hlive hb
      · rw [List.getElem?_append_right (by omega)] at ha
        have hmem := List.mem_of_getElem? ha
        rw [hdead a hmem] at hlive
        cases hlive }

theorem LocalsOkA.empty (body : CapturedMir) (ctx : Ctx) :
    LocalsOkA body ctx [] (List.replicate body.localDecls.length .dead) ⟨[]⟩ ctx.base := by
  refine {
    nlocals := List.length_replicate
    slots := by
      intro i d slot _ hs
      rw [List.getElem?_replicate] at hs
      split at hs <;> simp at hs
      subst hs; exact declSlotOk_dead d body.layouts
    base := ⟨[], by simp⟩
    keysNodup := by simp
    keysLocal := fun _ he => by simp at he
    live := fun i slot hs => by
      rw [List.getElem?_replicate] at hs
      split at hs <;> simp at hs
      subst hs
      simp [mapGet]
    storage := fun _ _ _ _ _ _ hp => by simp [mapGet] at hp
    inj := fun _ _ _ _ hp _ _ => by simp [mapGet] at hp
    owned := fun id a ha _ hb => by
      have := (List.getElem?_eq_some_iff.mp ha).1
      omega }

theorem LocalsOkA.toBaseCandBounded {body : CapturedMir} {ctx : Ctx} {al : List Nat}
    {locals : List LocalSlot} {lm : Map Gen.LocalName Ptr} {A : List Gen.Allocation}
    {bound : Nat} (hlo : LocalsOkA body ctx al locals lm A)
    (hbase : BaseCandBounded ctx.base bound)
    (hdecls : ∀ (i : Nat) d, body.localDecls[i]? = some d → scalarTypeOf d.ty = some (tyOf d)) :
    BaseCandBounded A (bound + body.localDecls.length) :=
  hlo.baseCandBounded_of_scalar hbase hdecls

theorem BaseCandBounded.of_set_same_geom {A : List Gen.Allocation} {bound id : Nat}
    {a a' : Gen.Allocation} (h : BaseCandBounded A bound) (hA : A[id]? = some a)
    (hlive : a'.live = a.live) (haddr : a'.addr = a.addr)
    (hlen : a'.data.length = a.data.length) :
    BaseCandBounded (A.set id a') bound := by
  obtain ⟨cands, hcands, hok⟩ := h
  refine ⟨cands, hcands, fun b hb hblive => ?_⟩
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hb
  by_cases hjid : j = id
  · subst hjid
    have hjA : j < A.length := by simpa using hj
    have heq : (A.set j a')[j] = a' := by simp
    rw [heq] at hblive ⊢
    rw [hlive] at hblive
    have haMem : a ∈ A := List.mem_of_getElem? hA
    rcases hok a haMem hblive with hlow | ⟨k, hk, hkaddr, hklen⟩
    · exact .inl (by rw [haddr, hlen]; exact hlow)
    · exact .inr ⟨k, hk, by rw [haddr]; exact hkaddr, by rw [hlen]; exact hklen⟩
  · have heq : (A.set id a')[j] = A[j]'(by simpa using hj) :=
      List.getElem_set_ne (Ne.symm hjid) _
    rw [heq] at hblive ⊢
    exact hok _ (List.getElem_mem _) hblive

theorem typedStore_ptr_localTy {m : Mach} {ctx : Ctx} {frames : List Frame}
    {A : List Gen.Allocation} (h : Shape m ctx frames A) (p : Ptr) (k : Nat)
    (hp : p.provenance = some (⟨(k : Int)⟩, ())) (d : LocalDecl)
    (hd : scalarTypeOf d.ty = some (tyOf d)) (data : List Byte)
    (hA : A[k]? = some (stackAlloc p.addr (itOf d) data))
    (hlen : data.length = tyBytes (tyOf d)) (v : Value)
    (hv : SlotOk (tyOf d) (.init v)) (align : Align)
    (hal : Align.is_aligned align p.addr = true) :
    ∃ acc, typedStore m p (valOfValue (tyOf d) v) (tyOf d) align .None =
      .ok (withMem m (A.set k (stackAlloc p.addr (itOf d) (declSlotData d (.init v)))) acc) := by
  have hk : k < A.length := (List.getElem?_eq_some_iff.mp hA).1
  let ctxF : Ctx := { ctx with base := A.take (k + 1) }
  have hlenTake : (A.take (k + 1)).length = k + 1 := by simp [List.length_take]; omega
  have hr : ctxF.base[k]? = some (stackAlloc p.addr (itOf d) data) := by
    simp only [ctxF]
    rw [List.getElem?_take_of_lt (by omega)]
    exact hA
  have hshF : Shape m ctxF frames (ctxF.base ++ A.drop (k + 1)) := by
    refine ⟨h.threads, h.active, ?_⟩
    simpa [ctxF] using h.allocs
  obtain ⟨acc, hst⟩ :=
    typedStore_base_localTy hshF p k (stackAlloc p.addr (itOf d) data) hp hr rfl rfl d hd
      hlen v hv align hal
  have hrecEq :
      ({ stackAlloc p.addr (itOf d) data with data := declSlotData d (.init v) } : Gen.Allocation) =
        stackAlloc p.addr (itOf d) (declSlotData d (.init v)) := rfl
  rw [hrecEq] at hst
  have hsetEq :
      ctxF.base.set k (stackAlloc p.addr (itOf d) (declSlotData d (.init v))) ++ A.drop (k + 1) =
        A.set k (stackAlloc p.addr (itOf d) (declSlotData d (.init v))) := by
    simp only [ctxF]
    rw [← List.set_append_left _ _ (by rw [hlenTake]; omega), List.take_append_drop]
  rw [hsetEq] at hst
  exact ⟨acc, hst⟩

/-! ### Scalar-family locals, ABI reflexivity, and MR-4-style storage helpers -/

mutual
/-- `check_abi_compatibility(T, T)` for every layout-backed tuple/struct type. -/
theorem checkAbiCompatibility_refl_tupleSpec : ∀ s : TupleSpec,
    checkAbiCompatibility s.toMiniRustTy s.toMiniRustTy = .ok true
  | .scalar it => by simp [TupleSpec.toMiniRustTy, checkAbiCompatibility]
  | .tuple fields size align => by
    simp [TupleSpec.toMiniRustTy, checkAbiCompatibility,
      checkAbiFields_refl_tupleSpec fields]

/-- `check_abi_compatibility` on the fields of a layout-backed tuple/struct type. -/
theorem checkAbiFields_refl_tupleSpec : ∀ fs : List (Nat × TupleSpec),
    checkAbiFields (TupleSpec.fieldsToMiniRust fs) (TupleSpec.fieldsToMiniRust fs) = .ok true
  | [] => by simp [TupleSpec.fieldsToMiniRust, checkAbiFields]
  | (off, s) :: rest => by
    simp [TupleSpec.fieldsToMiniRust, checkAbiFields, checkAbiCompatibility_refl_tupleSpec s,
      checkAbiFields_refl_tupleSpec rest]
end

/-- `itOf` of a scalar-family local does not depend on the layout table. -/
theorem itOf_scalar_layouts {d : LocalDecl} (h : (scalarTypeOf d.ty).isSome = true)
    (L L' : Layout.LayoutTable) : itOf d L = itOf d L' := by
  obtain ⟨T, hs⟩ := Option.isSome_iff_exists.mp h
  rcases scalarTypeOf_cases hs with ⟨hb, _⟩ | ⟨it, hit, _⟩ | ⟨ho, _⟩ | ⟨it, ht, _⟩
  · rw [(tyOf_bool (layouts := L) hb).2, (tyOf_bool (layouts := L') hb).2]
  · rw [(tyOf_int (layouts := L) hit).2, (tyOf_int (layouts := L') hit).2]
  · rw [(tyOf_ordering (layouts := L) ho).2, (tyOf_ordering (layouts := L') ho).2]
  · rw [(tyOf_tuple (layouts := L) ht).2, (tyOf_tuple (layouts := L') ht).2]

/-- `tyOf` of a scalar-family local does not depend on the layout table. -/
theorem tyOf_scalar_layouts {d : LocalDecl} (h : (scalarTypeOf d.ty).isSome = true)
    (L L' : Layout.LayoutTable) : tyOf d L = tyOf d L' := by
  obtain ⟨T, hs⟩ := Option.isSome_iff_exists.mp h
  rw [tyOf_of_scalarTypeOf (layouts := L) hs, tyOf_of_scalarTypeOf (layouts := L') hs]

/-- `declSlotData` of a scalar-family local does not depend on the layout table. -/
theorem declSlotData_scalar_layouts {d : LocalDecl} (h : (scalarTypeOf d.ty).isSome = true)
    (slot : LocalSlot) (L L' : Layout.LayoutTable) :
    declSlotData d slot L = declSlotData d slot L' := by
  obtain ⟨T, hs⟩ := Option.isSome_iff_exists.mp h
  cases ht : intBoolTupleOf d.ty with
  | some it => rw [declSlotData_of_some ht, declSlotData_of_some ht]
  | none =>
    rw [declSlotData_of_none ht (arrayTypeOf_none_of_scalarTypeOf hs)
        (tupleTypeOf_none_of_scalarTypeOf hs),
      declSlotData_of_none ht (arrayTypeOf_none_of_scalarTypeOf hs)
        (tupleTypeOf_none_of_scalarTypeOf hs),
      itOf_scalar_layouts h L L']

theorem scalarTypeOf_tyOf_of_isSome {d : LocalDecl} (h : (scalarTypeOf d.ty).isSome = true)
    (L : Layout.LayoutTable) : scalarTypeOf d.ty = some (tyOf d L) := by
  obtain ⟨T, hs⟩ := Option.isSome_iff_exists.mp h
  rw [tyOf_of_scalarTypeOf hs, hs]

/-- MR-4-style (default-layout) storage facts for a scalar-family local. -/
theorem LocalsOkA.storage_scalar {body : CapturedMir} {ctx : Ctx} {al : List Nat}
    {locals : List LocalSlot} {lm : Map Gen.LocalName Ptr} {A : List Gen.Allocation}
    (hlo : LocalsOkA body ctx al locals lm A)
    {i : Nat} {d : LocalDecl} {slot : LocalSlot} {p : Ptr} (hd : body.localDecls[i]? = some d)
    (hsc : (scalarTypeOf d.ty).isSome = true)
    (hs : locals[i]? = some slot) (hp : mapGet lm (localName i) = some p) :
    ∃ id : Nat, p.provenance = some (⟨(id : Int)⟩, ()) ∧ ctx.base.length ≤ id ∧
      AddrOk p.addr (itOf d) ∧ AddrClass p.addr (tyBytes (tyOf d)) ∧
      A[id]? = some (stackAlloc p.addr (itOf d) (declSlotData d slot)) := by
  obtain ⟨T, hT⟩ := Option.isSome_iff_exists.mp hsc
  obtain ⟨id, hpid, hb, ha, _, hc, hA⟩ :=
    hlo.storage_nonptr i d slot p hd hs hp (isPtrTy_false_of_scalarTypeOf hT)
  rw [itOf_scalar_layouts hsc body.layouts ⟨64, true, []⟩] at ha
  rw [tyOf_scalar_layouts hsc body.layouts ⟨64, true, []⟩] at hc
  rw [itOf_scalar_layouts hsc body.layouts ⟨64, true, []⟩,
    declSlotData_scalar_layouts hsc slot body.layouts ⟨64, true, []⟩] at hA
  exact ⟨id, hpid, hb, ha, hc, hA⟩

/-- `LocalsOkA.store` specialized to a scalar-family local, in MR-4's default-layout form. -/
theorem LocalsOkA.store_scalar {body : CapturedMir} {ctx : Ctx} {al : List Nat}
    {locals : List LocalSlot} {lm : Map Gen.LocalName Ptr} {A : List Gen.Allocation}
    (hlo : LocalsOkA body ctx al locals lm A)
    (i : Nat) (d : LocalDecl) (hd : body.localDecls[i]? = some d)
    (hsc : (scalarTypeOf d.ty).isSome = true) (slot slot' : LocalSlot)
    (hs : locals[i]? = some slot) (hlive' : slot' ≠ .dead) (hslot' : SlotOk (tyOf d) slot')
    (p : Ptr) (hp : mapGet lm (localName i) = some p) (k : Nat)
    (hpk : p.provenance = some (⟨(k : Int)⟩, ())) :
    LocalsOkA body ctx al (locals.set i slot') lm
      (A.set k (stackAlloc p.addr (itOf d) (declSlotData d slot'))) := by
  have h := hlo.store i d hd slot slot' hs hlive'
    (by rw [tyOf_scalar_layouts hsc body.layouts ⟨64, true, []⟩]; exact hslot') p hp k hpk
  rw [itOf_scalar_layouts hsc body.layouts ⟨64, true, []⟩,
    declSlotData_scalar_layouts hsc slot' body.layouts ⟨64, true, []⟩] at h
  exact h

/-- `LocalsOk.store` specialized to a scalar-family local, in MR-4's default-layout form. -/
theorem LocalsOk.store_scalar {body : CapturedMir} {ctx : Ctx} {locals : List LocalSlot}
    {lm : Map Gen.LocalName Ptr} {A : List Gen.Allocation} (hlo : LocalsOk body ctx locals lm A)
    (i : Nat) (d : LocalDecl) (hd : body.localDecls[i]? = some d)
    (hsc : (scalarTypeOf d.ty).isSome = true) (slot slot' : LocalSlot)
    (hs : locals[i]? = some slot) (hlive' : slot' ≠ .dead) (hslot' : SlotOk (tyOf d) slot')
    (p : Ptr) (hp : mapGet lm (localName i) = some p) (k : Nat)
    (hpk : p.provenance = some (⟨(k : Int)⟩, ())) :
    LocalsOk body ctx (locals.set i slot') lm
      (A.set k (stackAlloc p.addr (itOf d) (declSlotData d slot'))) :=
  LocalsOkA.store_scalar hlo i d hd hsc slot slot' hs hlive' hslot' p hp k hpk

/-- `LocalsOkA.alloc'` for `StorageLive` of a dead scalar-family local, in MR-4's
default-layout form. -/
theorem LocalsOkA.alloc_scalar {body : CapturedMir} {ctx : Ctx} {al : List Nat}
    {locals : List LocalSlot} {lm : Map Gen.LocalName Ptr} {A : List Gen.Allocation}
    (hlo : LocalsOkA body ctx al locals lm A)
    (i : Nat) (d : LocalDecl) (hd : body.localDecls[i]? = some d)
    (hsc : (scalarTypeOf d.ty).isSome = true) (hs : locals[i]? = some .dead)
    (hp : mapGet lm (localName i) = none) (addr : Int) (haddr : AddrOk addr (itOf d))
    (haddrMax : addr + (tyBytes (tyOf d) : Int) < 2 ^ 64)
    (hcls : AddrClass addr (tyBytes (tyOf d))) :
    LocalsOkA body ctx al (locals.set i .uninit)
      ⟨lm.entries ++ [(localName i, { addr := addr, provenance := some (⟨(A.length : Int)⟩, ()) })]⟩
      (A ++ [stackAlloc addr (itOf d) (declSlotData d .uninit)]) := by
  have hI := itOf_scalar_layouts hsc body.layouts ⟨64, true, []⟩
  have hT := tyOf_scalar_layouts hsc body.layouts ⟨64, true, []⟩
  have h := LocalsOkA.alloc' hlo i d hd hs hp addr (by rw [hI]; exact haddr)
    (by rw [hT]; exact haddrMax) (by rw [hT]; exact hcls) .uninit
    (declSlotOk_uninit d body.layouts) (.inr (by simp)) (.inl (by simp)) (fun _ _ => Iff.rfl)
  rw [hI, declSlotData_scalar_layouts hsc .uninit body.layouts ⟨64, true, []⟩] at h
  exact h

/-- `check_abi_compatibility(T, T)` evaluates to `.ok true` on every fragment
local type `T`. -/
theorem checkAbiCompatibility_refl_localTy {T : Gen.Type} {it : Gen.IntType}
    (h : LocalTy T it) : checkAbiCompatibility T T = .ok true := by
  cases h with
  | frag hf =>
    cases hf with
    | int it hgood => simp [checkAbiCompatibility]
    | bool => rfl
    | ordering => rfl
  | tuple it hgood =>
    simp [intBoolTupleTy, checkAbiCompatibility, checkAbiFields]
  | array elemIt count hgood => simp [checkAbiCompatibility]
  | tupleSpec fields size align hwf =>
    exact checkAbiCompatibility_refl_tupleSpec (.tuple fields size align)
  | rawPtr => simp [thinRawPtrTy, checkAbiCompatibility]
  | refPtr mutbl it hgood => simp [refTy, checkAbiCompatibility]

/-- Evaluating `fnPtrExpr fn` and resolving `fnFromPtr` on a machine satisfying
`ProgEnvOk`. -/
theorem evalValue_fnPtr_and_lookup {prog : Gen.Program} {fnMap : FnMap}
    {m : Mach} (henv : ProgEnvOk prog fnMap m) {dp : String} {fn : Gen.FnName}
    {fCallee : Gen.Function} (hlk : lookupFnName fnMap dp = some fn)
    (hfn : mapGet prog.functions fn = some fCallee) :
    ∃ ptr : Ptr,
      evalValue m (fnPtrExpr fn) = .ok ((.Ptr (ThinPointer.widen ptr none), .Ptr .FnPtr), m) ∧
      fnFromPtr m (.Ptr (ThinPointer.widen ptr none)) = .ok fCallee := by
  obtain ⟨hprog, hptrs⟩ := henv
  obtain ⟨ptr, hget, hfind⟩ := hptrs dp fn hlk
  refine ⟨ptr, ?_, ?_⟩
  · simp [fnPtrExpr, evalValue, evalConstant, mapIndex, hget]
  · have hfind2 : m.fn_ptrs.entries.find? (fun x => decide (x.2 = ptr)) = some (fn, ptr) := by
      have hfnEq : (fun x : Gen.FnName × Ptr => decide (x.2 = ptr)) =
          (fun (_, (fp : Ptr)) => decide (fp = ptr)) :=
        funext fun ⟨_, _⟩ => rfl
      exact Eq.trans (congrArg (List.find? · m.fn_ptrs.entries) hfnEq) hfind
    unfold fnFromPtr ThinPointer.widen
    dsimp only
    rw [hfind2]
    simp [mapIndex, hprog, hfn]

/-- `ConcurrentMemory::store` of `bytes` filling a whole live allocation at an
aligned pointer. -/
theorem CM_store_whole_align {cm : Gen.ConcurrentMemory BM} {p : Ptr} {k : Nat}
    (hp : p.provenance = some (⟨(k : Int)⟩, ())) {a : Gen.Allocation}
    (hA : cm.memory.allocations[k]? = some a) (hlive : a.live = true) (haddr : a.addr = p.addr)
    (bytes : List Byte) (hne : bytes ≠ []) (hlen : bytes.length = a.data.length)
    (align : Align) (hal : Align.is_aligned align p.addr = true) :
    CM.store cm p bytes align .None =
      .ok { memory := { cm.memory with allocations := cm.memory.allocations.set k { a with data := bytes } },
            accesses := cm.accesses ++ [⟨.Store, .None, p.addr, ⟨bytes.length⟩⟩] } := by
  obtain ⟨hk, hAk⟩ := List.getElem?_eq_some_iff.mp hA
  have hne' : a.data ≠ [] := by
    intro h; rw [h] at hlen; exact hne (List.eq_nil_of_length_eq_zero hlen)
  simp [CM.store, BM.store, hal, BM.check_ptr, hp, listIndex, hk, hAk, hlive, haddr,
    Allocation.size, hlen, writeSubsliceAtIndex, listSet, hne']

theorem prepareForInplacePassing_ptr_whole {m : Mach} {p : Ptr} {k : Nat}
    (hp : p.provenance = some (⟨(k : Int)⟩, ())) (d : LocalDecl)
    (hd : scalarTypeOf d.ty = some (tyOf d)) (data : List Byte)
    (hA : m.mem.memory.allocations[k]? = some (stackAlloc p.addr (itOf d) data))
    (hlen : data.length = tyBytes (tyOf d)) (haddr : AddrOk p.addr (itOf d)) :
    prepareForInplacePassing m { ptr := ThinPointer.widen p none, aligned := true } (tyOf d) =
      .ok (withMem m
        (m.mem.memory.allocations.set k (stackAlloc p.addr (itOf d) (declSlotData d .uninit)))
        ⟨.Store, .None, p.addr, ⟨tyBytes (tyOf d)⟩⟩) := by
  have hlt := localTy_of_decl hd
  have hne : List.replicate (tyBytes (tyOf d)) (Gen.AbstractByte.Uninit : Byte) ≠ [] :=
    List.ne_nil_of_length_pos (by simp; exact scalar_tyBytes_pos (.inl (by simp [hd])))
  have hal : Align.is_aligned ⟨(itOf d).size.bytes⟩ p.addr = true := by
    simp [Align.is_aligned, haddr.1]
  have hst := CM_store_whole_align hp hA rfl rfl
    (List.replicate (tyBytes (tyOf d)) .Uninit) hne (by simp [stackAlloc, hlen])
    ⟨(itOf d).size.bytes⟩ hal
  simp [prepareForInplacePassing, hlt.layout, expect_size_sized, expect_align_sized,
    ThinPointer.widen, CM.deinit, hst, withMem, declSlotData_uninit hd, stackAlloc]

theorem prepareForInplacePassing_ptr_field0 {m : Mach} {p : Ptr} {k : Nat}
    (hp : p.provenance = some (⟨(k : Int)⟩, ())) {it : Gen.IntType}
    (hgood : GoodSize it.size.bytes) (bits b : Nat)
    (hA : m.mem.memory.allocations[k]? = some (stackAlloc p.addr it (tupleBytes it bits b)))
    (haddr : AddrOk p.addr it) :
    prepareForInplacePassing m { ptr := ThinPointer.widen p none, aligned := true } (.Int it) =
      .ok (withMem m
        (m.mem.memory.allocations.set k
          (stackAlloc p.addr it
            (uninitBytes it ++ scalarBytes u8Ty b ++ List.replicate (it.size.bytes - 1) .Uninit)))
        ⟨.Store, .None, p.addr, it.size⟩) := by
  have hpos := hgood.pos
  obtain ⟨hk, hAk⟩ := List.getElem?_eq_some_iff.mp hA
  have hlen := tupleBytes_length it bits b hpos
  have hal : Align.is_aligned ⟨it.size.bytes⟩ p.addr = true := by
    simp [Align.is_aligned, haddr.1]
  have hne : List.replicate it.size.bytes (Gen.AbstractByte.Uninit : Byte) ≠ [] :=
    List.ne_nil_of_length_pos (by simp; exact hpos)
  have hdrop : (tupleBytes it bits b).drop it.size.bytes =
      scalarBytes u8Ty b ++ List.replicate (it.size.bytes - 1) .Uninit := by
    have hlen0 := scalarBytes_length it bits
    rw [tupleBytes, List.append_assoc, List.drop_append_of_le_length (by omega),
      List.drop_eq_nil_of_le (by omega), List.nil_append]
  have hbounds : ¬ ((it.size.bytes : Int) + it.size.bytes < it.size.bytes) := by omega
  simp only [prepareForInplacePassing, layout_eq it hgood, expect_size_sized, expect_align_sized,
    ok_bind, ThinPointer.widen, CM.deinit, CM.store, BM.store, hal, BM.check_ptr, hp, listIndex]
  simp [Nat.ne_of_gt hpos, hk, hAk, stackAlloc, Allocation.size, hlen, hbounds,
    writeSubsliceAtIndex, hdrop, listSet, withMem, uninitBytes, List.append_assoc]

theorem prepareForInplacePassing_ptr_field1 {m : Mach} {p : Ptr} {k : Nat}
    (hp : p.provenance = some (⟨(k : Int)⟩, ())) {it : Gen.IntType}
    (hgood : GoodSize it.size.bytes) (bits b : Nat)
    (hA : m.mem.memory.allocations[k]? = some (stackAlloc p.addr it (tupleBytes it bits b))) :
    prepareForInplacePassing m { ptr := ThinPointer.widen (field1Ptr p it) none, aligned := true } .Bool =
      .ok (withMem m
        (m.mem.memory.allocations.set k
          (stackAlloc p.addr it
            (scalarBytes it bits ++ [.Uninit] ++ List.replicate (it.size.bytes - 1) .Uninit)))
        ⟨.Store, .None, (field1Ptr p it).addr, u8Ty.size⟩) := by
  have hpos := hgood.pos
  have hposI : (1 : Int) ≤ (it.size.bytes : Int) := by omega
  obtain ⟨hk, hAk⟩ := List.getElem?_eq_some_iff.mp hA
  have hlen := tupleBytes_length it bits b hpos
  have hu8 : u8Ty.size.bytes = 1 := rfl
  have hsub : ∀ x : Int, x + (it.size.bytes : Int) - x = (it.size.bytes : Int) := fun _ => by omega
  have hnonneg : ¬ ((it.size.bytes : Int) < 0) := by omega
  have hbounds : ¬ ((it.size.bytes : Int) + it.size.bytes < (it.size.bytes : Int) + 1) := by omega
  have htk : (tupleBytes it bits b).take it.size.bytes = scalarBytes it bits :=
    take_tupleBytes_field0 it bits b
  have hdr : (tupleBytes it bits b).drop (it.size.bytes + 1) =
      List.replicate (it.size.bytes - 1) .Uninit := by
    have hlen0 := scalarBytes_length it bits
    have hlen1 : (scalarBytes u8Ty b).length = 1 := scalarBytes_length u8Ty b
    rw [tupleBytes, List.append_assoc, List.drop_append, hlen0,
      List.drop_eq_nil_of_le (by omega), List.nil_append,
      show it.size.bytes + 1 - it.size.bytes = 1 by omega,
      List.drop_append, hlen1, List.drop_eq_nil_of_le (by omega), List.nil_append,
      List.drop_zero]
  simp only [prepareForInplacePassing, layout_bool, expect_size_sized, expect_align_sized,
    ok_bind, ThinPointer.widen, CM.deinit, CM.store, BM.store, hu8, isAligned_one,
    BM.check_ptr, field1Ptr, hp, listIndex]
  simp [hk, hAk, stackAlloc, Allocation.size, hlen, hsub, hnonneg, hbounds, hposI,
    Int.toNat_natCast, writeSubsliceAtIndex, htk, hdr, listSet, withMem, u8Ty, List.append_assoc]

/-- Evaluating the caller's `ret` place and `prepare_for_inplace_passing` in
`Terminator::Call` establishes `CallerDestRel`. -/
theorem evalCallRet_spec {callerBody : CapturedMir} {callerFn : Gen.Function}
    {rootCtx callerCtx : Ctx} {callerFrames : List Frame}
    {callerActual callerView : List LocalSlot} {callerLm : Map Gen.LocalName Ptr}
    {blk stmt : Nat} {m : Mach} {calleeRetDecl : LocalDecl} {destination : Place}
    {retExpr : Gen.PlaceExpr}
    (hf : FnLocalsSpec callerBody callerFn)
    (hsh : Shape m rootCtx
      (callerFrames ++ [calleeFrameL callerFn callerCtx callerLm blk stmt])
      m.mem.memory.allocations)
    (hlo : LocalsOk callerBody callerCtx callerView callerLm m.mem.memory.allocations)
    (halen : callerActual.length = callerView.length)
    (hret : translatePlace callerBody.localDecls destination = some retExpr)
    (hdstLive : callerActual[destination.local_]? ≠ some .dead ∧
      callerView[destination.local_]? ≠ some .dead)
    (hdestOk :
      match destination with
      | ⟨dst, []⟩ =>
        ∃ d, callerBody.localDecls[dst]? = some d ∧
          sameFragmentTy d.ty calleeRetDecl.ty = true
      | ⟨dst, [.field 0 fTy]⟩ =>
        ∃ d it sc0 sc1,
          callerBody.localDecls[dst]? = some d ∧
          intBoolTupleOf d.ty = some it ∧ intTypeOf fTy = some it ∧
          intTypeOf calleeRetDecl.ty = some it ∧
          callerActual[dst]? = some (.init (.aggregate 0 [.scalar sc0, .scalar sc1])) ∧
          callerView[dst]? = some (.init (.aggregate 0 [.scalar sc0, .scalar sc1]))
      | ⟨dst, [.field 1 fTy]⟩ =>
        ∃ d it sc0 sc1,
          callerBody.localDecls[dst]? = some d ∧
          intBoolTupleOf d.ty = some it ∧ isBoolTy fTy = true ∧
          isBoolTy calleeRetDecl.ty = true ∧
          callerActual[dst]? = some (.init (.aggregate 0 [.scalar sc0, .scalar sc1])) ∧
          callerView[dst]? = some (.init (.aggregate 0 [.scalar sc0, .scalar sc1]))
      | _ => False) :
    ∃ retPlace m1 view1,
      evalPlace m retExpr = .ok ((retPlace, tyOf calleeRetDecl), m) ∧
      prepareForInplacePassing m retPlace (tyOf calleeRetDecl) = .ok m1 ∧
      Shape m1 rootCtx
        (callerFrames ++ [calleeFrameL callerFn callerCtx callerLm blk stmt])
        m1.mem.memory.allocations ∧
      m1.prog = m.prog ∧ m1.fn_ptrs = m.fn_ptrs ∧
      (∀ j, j ≠ destination.local_ → view1[j]? = callerView[j]?) ∧
      view1.length = callerView.length ∧
      CallerDestRel callerBody callerCtx callerActual view1 callerLm calleeRetDecl
        m1.mem.memory.allocations retPlace.ptr.thin_pointer destination := by
  let fr := calleeFrameL callerFn callerCtx callerLm blk stmt
  have hshR : Shape (rethread m callerCtx [callerCtx.caller, fr]) callerCtx
      [callerCtx.caller, fr] m.mem.memory.allocations :=
    ⟨rfl, hsh.active, hsh.allocs⟩
  have hplEq : (∀ e ∈ destination.projection, ∃ idx ty, e = .field idx ty) →
      evalPlace m retExpr =
        (evalPlace (rethread m callerCtx [callerCtx.caller, fr]) retExpr).map (fun r => (r.1, m)) :=
    fun hfld => evalPlace_rethread_derefFree retExpr (translatePlace_derefFree hret hfld) m
      rootCtx callerCtx callerFrames fr hsh.threads hsh.active
  match destination, hret, hdstLive, hdestOk, hplEq with
  | ⟨dst, []⟩, hret, hdstLive, ⟨d, hd, hsame⟩, hplEq =>
    have hplEq := hplEq (by simp)
    simp only [translatePlace, Option.some.injEq] at hret
    subst hret
    obtain ⟨hTyEq, _, ⟨T', hscDst, _⟩, _⟩ := sameFragmentTy_spec hsame
    have hsc : (scalarTypeOf d.ty).isSome = true := by simp [hscDst]
    have hdSc : scalarTypeOf d.ty = some (tyOf d) := scalarTypeOf_tyOf_of_isSome hsc _
    have hdlt : dst < callerBody.localDecls.length := (List.getElem?_eq_some_iff.mp hd).1
    have hvlt : dst < callerView.length := by rw [hlo.nlocals]; exact hdlt
    have halt : dst < callerActual.length := by rw [halen]; exact hvlt
    obtain ⟨aSlot, haSlot⟩ : ∃ s, callerActual[dst]? = some s := ⟨_, List.getElem?_eq_getElem halt⟩
    obtain ⟨vSlot, hvSlot⟩ : ∃ s, callerView[dst]? = some s := ⟨_, List.getElem?_eq_getElem hvlt⟩
    have haNe : aSlot ≠ .dead := fun hc => hdstLive.1 (hc ▸ haSlot)
    have hvNe : vSlot ≠ .dead := fun hc => hdstLive.2 (hc ▸ hvSlot)
    obtain ⟨p, hp⟩ := hlo.some_of_live hvSlot hvNe
    obtain ⟨k, hpk, _, haddr, _, hA⟩ := hlo.storage_scalar hd hsc hvSlot hp
    have hloc : mapGet callerFn.locals (localName dst) = some (tyOf d) := by
      rw [(hf.2 dst d hd).2, tyOf_scalar_layouts hsc callerBody.layouts ⟨64, true, []⟩]
    have hplaceR := evalPlace_local_some hshR dst (tyOf d) hloc p hp
    have hplace : evalPlace m (.Local (localName dst)) =
        .ok (({ ptr := ThinPointer.widen p none, aligned := true }, tyOf calleeRetDecl), m) := by
      rw [hplEq, hplaceR, ← hTyEq]
      rfl
    have hlen := declSlotData_length hdSc vSlot
    have hprep := prepareForInplacePassing_ptr_whole (m := m) hpk d hdSc _ hA hlen haddr
    rw [hTyEq] at hprep
    let m1 := withMem m
      (m.mem.memory.allocations.set k (stackAlloc p.addr (itOf d) (declSlotData d .uninit)))
      ⟨.Store, .None, p.addr, ⟨tyBytes (tyOf calleeRetDecl)⟩⟩
    have hlo1 := hlo.store_scalar dst d hd hsc vSlot .uninit hvSlot (by simp) trivial p hp k hpk
    refine ⟨{ ptr := ThinPointer.widen p none, aligned := true }, m1,
      callerView.set dst .uninit, hplace, hprep, withMem_shape hsh _, rfl, rfl,
      fun j hj => List.getElem?_set_ne (Ne.symm hj), by simp, ?_⟩
    exact .root dst d aSlot haSlot haNe (List.getElem?_set_self hvlt) hd hsame hlo1 hp
  | ⟨dst, [.field 0 fTy]⟩, hret, _, ⟨d, it, sc0, sc1, hd, htup, hfTy, hRetTy, haSlot, hvSlot⟩,
      hplEq =>
    have hplEq := hplEq (by simp)
    have hcast0 : ((0 : Nat) : Int) = 0 := rfl
    simp only [translatePlace, translateFieldPlace, hcast0, Option.some.injEq] at hret
    subst hret
    have hsc : (scalarTypeOf d.ty).isSome = true := by simp [scalarTypeOf_tuple htup]
    have hgood := intBoolTupleOf_good htup
    obtain ⟨hTd, hitd⟩ := tyOf_tuple (layouts := ⟨64, true, []⟩) htup
    have hRetTd : tyOf calleeRetDecl = .Int it := (tyOf_int hRetTy).1
    have hloc : mapGet callerFn.locals (localName dst) = some (intBoolTupleTy it) := by
      rw [(hf.2 dst d hd).2, (tyOf_tuple (layouts := callerBody.layouts) htup).1]
    have hslot0 := hlo.slots dst d _ hd hvSlot
    rw [DeclSlotOk_of_scalarTypeOf (scalarTypeOf_tuple htup),
      (tyOf_tuple (layouts := callerBody.layouts) htup).1] at hslot0
    obtain ⟨it', htyT, _, _, hsc1Sz, hsc1Lt⟩ := hslot0
    simp only [tupleIntOfTy_intBoolTupleTy, Option.some.injEq] at htyT
    subst htyT
    obtain ⟨p, hp⟩ := hlo.some_of_live hvSlot (by simp)
    obtain ⟨k, hpk, _, haddr, _, hA⟩ := hlo.storage_scalar hd hsc hvSlot hp
    rw [declSlotData_of_some htup, hitd] at hA
    rw [hitd] at haddr
    have hplaceR := evalPlace_field0L hshR dst it hgood hloc p hp haddr
    have hplace : evalPlace m (.Field (.Local (localName dst)) 0) =
        .ok (({ ptr := ThinPointer.widen p none, aligned := true }, tyOf calleeRetDecl), m) := by
      rw [hplEq, hplaceR, hRetTd]
      rfl
    have hprep := prepareForInplacePassing_ptr_field0 (m := m) hpk hgood sc0.bits sc1.bits hA haddr
    rw [← hRetTd] at hprep
    let m1 := withMem m
      (m.mem.memory.allocations.set k
        (stackAlloc p.addr it
          (uninitBytes it ++ scalarBytes u8Ty sc1.bits ++ List.replicate (it.size.bytes - 1) .Uninit)))
      ⟨.Store, .None, p.addr, it.size⟩
    refine ⟨{ ptr := ThinPointer.widen p none, aligned := true }, m1, callerView,
      hplace, hprep, withMem_shape hsh _, rfl, rfl, fun _ _ => rfl, rfl, ?_⟩
    exact .field0 dst fTy d it sc0 sc1 m.mem.memory.allocations k haSlot hvSlot hd htup
      hfTy hRetTy ⟨hsc1Sz, hsc1Lt⟩ hlo hp hpk hA rfl
  | ⟨dst, [.field 1 fTy]⟩, hret, _, ⟨d, it, sc0, sc1, hd, htup, hfTy, hRetTy, haSlot, hvSlot⟩,
      hplEq =>
    have hplEq := hplEq (by simp)
    have hcast1 : ((1 : Nat) : Int) = 1 := rfl
    simp only [translatePlace, translateFieldPlace, hcast1, Option.some.injEq] at hret
    subst hret
    have hsc : (scalarTypeOf d.ty).isSome = true := by simp [scalarTypeOf_tuple htup]
    have hgood := intBoolTupleOf_good htup
    obtain ⟨hTd, hitd⟩ := tyOf_tuple (layouts := ⟨64, true, []⟩) htup
    have hRetTd : tyOf calleeRetDecl = .Bool := (tyOf_bool hRetTy).1
    have hloc : mapGet callerFn.locals (localName dst) = some (intBoolTupleTy it) := by
      rw [(hf.2 dst d hd).2, (tyOf_tuple (layouts := callerBody.layouts) htup).1]
    have hslot0 := hlo.slots dst d _ hd hvSlot
    rw [DeclSlotOk_of_scalarTypeOf (scalarTypeOf_tuple htup),
      (tyOf_tuple (layouts := callerBody.layouts) htup).1] at hslot0
    obtain ⟨it', htyT, hsc0Sz, hsc0Lt, _, _⟩ := hslot0
    simp only [tupleIntOfTy_intBoolTupleTy, Option.some.injEq] at htyT
    subst htyT
    obtain ⟨p, hp⟩ := hlo.some_of_live hvSlot (by simp)
    obtain ⟨k, hpk, _, haddr, _, hA⟩ := hlo.storage_scalar hd hsc hvSlot hp
    rw [declSlotData_of_some htup, hitd] at hA
    rw [hitd] at haddr
    have hlen := tupleBytes_length it sc0.bits sc1.bits hgood.pos
    have hplaceR : evalPlace (rethread m callerCtx [callerCtx.caller, fr])
        (.Field (.Local (localName dst)) 1) =
        .ok (({ ptr := ThinPointer.widen (field1Ptr p it) none, aligned := true }, .Bool),
          rethread m callerCtx [callerCtx.caller, fr]) :=
      evalPlace_field1L hshR dst it hgood hloc p hp k hpk _ hA hlen haddr
    have hplace : evalPlace m (.Field (.Local (localName dst)) 1) =
        .ok (({ ptr := ThinPointer.widen (field1Ptr p it) none, aligned := true },
          tyOf calleeRetDecl), m) := by
      rw [hplEq, hplaceR, hRetTd]
      rfl
    have hprep := prepareForInplacePassing_ptr_field1 (m := m) hpk hgood sc0.bits sc1.bits hA
    rw [← hRetTd] at hprep
    let m1 := withMem m
      (m.mem.memory.allocations.set k
        (stackAlloc p.addr it
          (scalarBytes it sc0.bits ++ [.Uninit] ++ List.replicate (it.size.bytes - 1) .Uninit)))
      ⟨.Store, .None, (field1Ptr p it).addr, u8Ty.size⟩
    refine ⟨{ ptr := ThinPointer.widen (field1Ptr p it) none, aligned := true }, m1, callerView,
      hplace, hprep, withMem_shape hsh _, rfl, rfl, fun _ _ => rfl, rfl, ?_⟩
    exact .field1 dst fTy d it sc0 sc1 m.mem.memory.allocations p k haSlot hvSlot hd htup
      hfTy hRetTy ⟨hsc0Sz, hsc0Lt⟩ hlo hp hpk rfl hA rfl

theorem CallerDestRel.nlocals {callerBody : CapturedMir} {callerCtx : Ctx}
    {callerActual callerView : List LocalSlot} {callerLm : Map Gen.LocalName Ptr}
    {calleeRetDecl : LocalDecl} {calleeBase : List Gen.Allocation}
    {calleeRetPtr : Ptr} {destination : Place}
    (h : CallerDestRel callerBody callerCtx callerActual callerView callerLm
      calleeRetDecl calleeBase calleeRetPtr destination) :
    callerView.length = callerBody.localDecls.length := by
  cases h with
  | root _ _ _ _ _ _ _ _ hLocs _ => exact hLocs.nlocals
  | field0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hLocs _ _ _ _ => exact hLocs.nlocals
  | field1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hLocs _ _ _ _ _ => exact hLocs.nlocals

theorem CallerDestRel.slots {callerBody : CapturedMir} {callerCtx : Ctx}
    {callerActual callerView : List LocalSlot} {callerLm : Map Gen.LocalName Ptr}
    {calleeRetDecl : LocalDecl} {calleeBase : List Gen.Allocation}
    {calleeRetPtr : Ptr} {destination : Place}
    (h : CallerDestRel callerBody callerCtx callerActual callerView callerLm
      calleeRetDecl calleeBase calleeRetPtr destination) :
    ∀ (i : Nat) d slot, callerBody.localDecls[i]? = some d → callerView[i]? = some slot →
      DeclSlotOk d slot callerBody.layouts := by
  cases h with
  | root _ _ _ _ _ _ _ _ hLocs _ => exact hLocs.slots
  | field0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hLocs _ _ _ _ => exact hLocs.slots
  | field1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hLocs _ _ _ _ _ => exact hLocs.slots

theorem CallerDestRel.none_of_dead {callerBody : CapturedMir} {callerCtx : Ctx}
    {callerActual callerView : List LocalSlot} {callerLm : Map Gen.LocalName Ptr}
    {calleeRetDecl : LocalDecl} {calleeBase : List Gen.Allocation}
    {calleeRetPtr : Ptr} {destination : Place}
    (h : CallerDestRel callerBody callerCtx callerActual callerView callerLm
      calleeRetDecl calleeBase calleeRetPtr destination) {j : Nat}
    (hs : callerView[j]? = some .dead) (hal : j ∉ alwaysStorageLiveLocals callerBody) :
    mapGet callerLm (localName j) = none := by
  cases h with
  | root _ _ _ _ _ _ _ _ hLocs _ => exact hLocs.none_of_dead hs hal
  | field0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hLocs _ _ _ _ => exact hLocs.none_of_dead hs hal
  | field1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hLocs _ _ _ _ _ => exact hLocs.none_of_dead hs hal

theorem CallerDestRel.dead_of_none {callerBody : CapturedMir} {callerCtx : Ctx}
    {callerActual callerView : List LocalSlot} {callerLm : Map Gen.LocalName Ptr}
    {calleeRetDecl : LocalDecl} {calleeBase : List Gen.Allocation}
    {calleeRetPtr : Ptr} {destination : Place}
    (h : CallerDestRel callerBody callerCtx callerActual callerView callerLm
      calleeRetDecl calleeBase calleeRetPtr destination) {j : Nat} {slot : LocalSlot}
    (hs : callerView[j]? = some slot) (hp : mapGet callerLm (localName j) = none) :
    slot = .dead := by
  cases h with
  | root _ _ _ _ _ _ _ _ hLocs _ => exact hLocs.dead_of_none hs hp
  | field0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hLocs _ _ _ _ => exact hLocs.dead_of_none hs hp
  | field1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hLocs _ _ _ _ _ => exact hLocs.dead_of_none hs hp

/-- Any caller local `j ≠ destination.local_` in `callerLm` retains its full
`declSlotData` in `calleeBase`, unaffected by `prepare_for_inplace_passing` on
`destination`. -/
theorem CallerDestRel.storage_ne {callerBody : CapturedMir} {callerCtx : Ctx}
    {callerActual callerView : List LocalSlot} {callerLm : Map Gen.LocalName Ptr}
    {calleeRetDecl : LocalDecl} {calleeBase : List Gen.Allocation}
    {calleeRetPtr : Ptr} {destination : Place}
    (h : CallerDestRel callerBody callerCtx callerActual callerView callerLm
      calleeRetDecl calleeBase calleeRetPtr destination)
    {j : Nat} (hne : j ≠ destination.local_) {d : LocalDecl} {slot : LocalSlot} {p : Ptr}
    (hd : callerBody.localDecls[j]? = some d) (hsc : (scalarTypeOf d.ty).isSome = true)
    (hs : callerView[j]? = some slot)
    (hp : mapGet callerLm (localName j) = some p) :
    ∃ id : Nat, p.provenance = some (⟨(id : Int)⟩, ()) ∧
      AddrOk p.addr (itOf d) ∧
      calleeBase[id]? = some (stackAlloc p.addr (itOf d) (declSlotData d slot)) := by
  cases h with
  | root dst _ _ _ _ _ _ _ hLocs _ =>
    obtain ⟨id, hpid, _, haddr, _, hA⟩ := hLocs.storage_scalar hd hsc hs hp
    exact ⟨id, hpid, haddr, hA⟩
  | field0 dst _ _ _ _ _ allocPre idDst _ _ _ _ _ _ _ hLocs hPtrDst hProvDst _ hBase =>
    simp only at hne
    obtain ⟨id, hpid, _, haddr, _, hA⟩ := hLocs.storage_scalar hd hsc hs hp
    have hidNe : idDst ≠ id := by
      intro heq
      subst heq
      exact hne (hLocs.inj j dst p calleeRetPtr hp hPtrDst (hpid.trans hProvDst.symm))
    exact ⟨id, hpid, haddr, by rw [hBase, List.getElem?_set_ne hidNe]; exact hA⟩
  | field1 dst _ _ _ _ _ allocPre pDst idDst _ _ _ _ _ _ _ hLocs hPtrDst hProvDst _ _ hBase =>
    simp only at hne
    obtain ⟨id, hpid, _, haddr, _, hA⟩ := hLocs.storage_scalar hd hsc hs hp
    have hidNe : idDst ≠ id := by
      intro heq
      subst heq
      exact hne (hLocs.inj j dst p pDst hp hPtrDst (hpid.trans hProvDst.symm))
    exact ⟨id, hpid, haddr, by rw [hBase, List.getElem?_set_ne hidNe]; exact hA⟩

/-- Moving a root argument local `j ≠ destination.local_` via
`ArgumentExpr::InPlace` preserves `CallerDestRel`. -/
theorem CallerDestRel.moveArg {callerBody : CapturedMir} {callerCtx : Ctx}
    {callerActual callerView : List LocalSlot} {callerLm : Map Gen.LocalName Ptr}
    {calleeRetDecl : LocalDecl} {calleeBase : List Gen.Allocation}
    {calleeRetPtr : Ptr} {destination : Place}
    (h : CallerDestRel callerBody callerCtx callerActual callerView callerLm
      calleeRetDecl calleeBase calleeRetPtr destination)
    {j : Nat} (hne : j ≠ destination.local_) {d : LocalDecl} {slot : LocalSlot}
    {p : Ptr} {id : Nat}
    (hd : callerBody.localDecls[j]? = some d) (hsc : (scalarTypeOf d.ty).isSome = true)
    (hs : callerView[j]? = some slot)
    (hp : mapGet callerLm (localName j) = some p)
    (hpid : p.provenance = some (⟨(id : Int)⟩, ())) :
    CallerDestRel callerBody callerCtx (callerActual.set j .uninit) (callerView.set j .uninit)
      callerLm calleeRetDecl
      (calleeBase.set id (stackAlloc p.addr (itOf d) (declSlotData d .uninit)))
      calleeRetPtr destination := by
  cases h with
  | root dst dDst callerSlot hActual hLive hView hdDst hSame hLocs hPtrDst =>
    simp only at hne
    have hlo' := hLocs.store_scalar j d hd hsc slot .uninit hs (by simp) trivial p hp id hpid
    exact .root dst dDst callerSlot (by rw [List.getElem?_set_ne hne]; exact hActual) hLive
      (by rw [List.getElem?_set_ne hne]; exact hView) hdDst hSame hlo' hPtrDst
  | field0 dst fTy dDst it sc0 sc1 allocPre idDst hActual hView hdDst hTup hfTy hRetTy
      hsc1 hLocs hPtrDst hProvDst hAllocPre hBase =>
    simp only at hne
    have hlo' := hLocs.store_scalar j d hd hsc slot .uninit hs (by simp) trivial p hp id hpid
    have hidNe : idDst ≠ id := by
      intro heq
      subst heq
      exact hne (hLocs.inj j dst p calleeRetPtr hp hPtrDst (hpid.trans hProvDst.symm))
    refine .field0 dst fTy dDst it sc0 sc1
      (allocPre.set id (stackAlloc p.addr (itOf d) (declSlotData d .uninit))) idDst
      (by rw [List.getElem?_set_ne hne]; exact hActual)
      (by rw [List.getElem?_set_ne hne]; exact hView)
      hdDst hTup hfTy hRetTy hsc1 hlo' hPtrDst hProvDst
      (by rw [List.getElem?_set_ne (Ne.symm hidNe)]; exact hAllocPre) ?_
    rw [hBase, List.set_comm _ _ hidNe]
  | field1 dst fTy dDst it sc0 sc1 allocPre pDst idDst hActual hView hdDst hTup hfTy hRetTy
      hsc0 hLocs hPtrDst hProvDst hRetPtr hAllocPre hBase =>
    simp only at hne
    have hlo' := hLocs.store_scalar j d hd hsc slot .uninit hs (by simp) trivial p hp id hpid
    have hidNe : idDst ≠ id := by
      intro heq
      subst heq
      exact hne (hLocs.inj j dst p pDst hp hPtrDst (hpid.trans hProvDst.symm))
    refine .field1 dst fTy dDst it sc0 sc1
      (allocPre.set id (stackAlloc p.addr (itOf d) (declSlotData d .uninit))) pDst idDst
      (by rw [List.getElem?_set_ne hne]; exact hActual)
      (by rw [List.getElem?_set_ne hne]; exact hView)
      hdDst hTup hfTy hRetTy hsc0 hlo' hPtrDst hProvDst hRetPtr
      (by rw [List.getElem?_set_ne (Ne.symm hidNe)]; exact hAllocPre) ?_
    rw [hBase, List.set_comm _ _ hidNe]

theorem CallerDestRel.baseCandBounded {callerBody : CapturedMir} {callerCtx : Ctx}
    {callerActual callerView : List LocalSlot} {callerLm : Map Gen.LocalName Ptr}
    {calleeRetDecl : LocalDecl} {calleeBase : List Gen.Allocation}
    {calleeRetPtr : Ptr} {destination : Place} {bound : Nat}
    (h : CallerDestRel callerBody callerCtx callerActual callerView callerLm
      calleeRetDecl calleeBase calleeRetPtr destination)
    (hbase : BaseCandBounded callerCtx.base bound)
    (hdecls : ∀ (i : Nat) d, callerBody.localDecls[i]? = some d →
      scalarTypeOf d.ty = some (tyOf d)) :
    BaseCandBounded calleeBase (bound + callerBody.localDecls.length) := by
  cases h with
  | root _ _ _ _ _ _ _ _ hLocs _ =>
    exact hLocs.toBaseCandBounded hbase hdecls
  | field0 _ _ _ it sc0 sc1 allocPre idDst _ _ _ hTup _ _ _ hLocs _ _ hAllocPre hBase =>
    have hbPre := hLocs.toBaseCandBounded hbase hdecls
    have hpos := (intBoolTupleOf_good hTup).pos
    have hlenOld := tupleBytes_length it sc0.bits sc1.bits hpos
    have hlenNew :
        (uninitBytes it ++ scalarBytes u8Ty sc1.bits ++
          List.replicate (it.size.bytes - 1) Gen.AbstractByte.Uninit).length =
        (tupleBytes it sc0.bits sc1.bits).length := by
      have hu8 : u8Ty.size.bytes = 1 := rfl
      simp only [hlenOld, List.length_append, uninitBytes, List.length_replicate,
        scalarBytes_length, hu8]
      omega
    rw [hBase]
    exact hbPre.of_set_same_geom hAllocPre rfl rfl (by simpa [stackAlloc] using hlenNew)
  | field1 _ _ _ it sc0 sc1 allocPre pDst idDst _ _ _ hTup _ _ _ hLocs _ _ _ hAllocPre hBase =>
    have hbPre := hLocs.toBaseCandBounded hbase hdecls
    have hpos := (intBoolTupleOf_good hTup).pos
    have hlenOld := tupleBytes_length it sc0.bits sc1.bits hpos
    have hlenNew :
        (scalarBytes it sc0.bits ++ [Gen.AbstractByte.Uninit] ++
          List.replicate (it.size.bytes - 1) Gen.AbstractByte.Uninit).length =
        (tupleBytes it sc0.bits sc1.bits).length := by
      simp only [hlenOld, List.length_append, scalarBytes_length, List.length_singleton,
        List.length_replicate]
      omega
    rw [hBase]
    exact hbPre.of_set_same_geom hAllocPre rfl rfl (by simpa [stackAlloc] using hlenNew)

/-! ### Call argument evaluation, frame creation, `Terminator::Call`, and caller `Return` -/

/-- Transition of a local-slot list when evaluating a call argument operand `op`
(`Operand.move ⟨j, []⟩` deinitializes slot `j` in both Anneal and MiniRust). -/
def opMoveLocal (L : List LocalSlot) (op : Operand) : List LocalSlot :=
  match opMoved op with
  | some j => L.set j .uninit
  | none => L

/-- Value produced by evaluating a fragment call argument `op` against `locals`
(`none` when reading `op` raises UB). -/
def callArgVal (locals : List LocalSlot) : Operand → Option Value
  | .copy ⟨j, []⟩ | .move ⟨j, []⟩ =>
    match locals[j]? with
    | some (.init v) => some v
    | _ => none
  | .copy ⟨j, [.field 0 _]⟩ =>
    match locals[j]? with
    | some (.init (.aggregate 0 [.scalar sc0, .scalar _])) => some (.scalar sc0)
    | _ => none
  | .copy ⟨j, [.field 1 _]⟩ =>
    match locals[j]? with
    | some (.init (.aggregate 0 [.scalar _, .scalar sc1])) => some (.scalar sc1)
    | _ => none
  | .constant c =>
    match c.val with
    | .scalar (.int sc) => some (.scalar sc)
    | _ => none
  | _ => none

/-- Sequential left-to-right evaluation of call argument operands `ops`,
threading `opMoveLocal` after each argument (`none` if any argument raises UB). -/
def callArgsEval (locals : List LocalSlot) : List Operand → Option (List Value × List LocalSlot)
  | [] => some ([], locals)
  | op :: ops => do
    let v ← callArgVal locals op
    let (vs, locals') ← callArgsEval (opMoveLocal locals op) ops
    pure (v :: vs, locals')

/-- Caller slot list after writing return value `v` to `destination` (matching
Anneal's `writePlaceValue` on fragment call destinations `_dst`, `_dst.0`, and
`_dst.1`). -/
def writeCallDest (callerSlots : List LocalSlot) (destination : Place) (v : Value) :
    List LocalSlot :=
  match destination with
  | ⟨dst, []⟩ => callerSlots.set dst (.init v)
  | ⟨dst, [.field 0 _]⟩ =>
    match callerSlots[dst]? with
    | some (.init (.aggregate 0 [_, v1])) =>
      callerSlots.set dst (.init (.aggregate 0 [v, v1]))
    | _ => callerSlots
  | ⟨dst, [.field 1 _]⟩ =>
    match callerSlots[dst]? with
    | some (.init (.aggregate 0 [v0, _])) =>
      callerSlots.set dst (.init (.aggregate 0 [v0, v]))
    | _ => callerSlots
  | _ => callerSlots

private theorem typedLoad_mem_only {m m' : Mach} {p : Ptr} {ty : Gen.Type} {align : Align}
    {atom : Gen.Atomicity} {v : Val} (h : typedLoad m p ty align atom = .ok (v, m')) :
    ∃ cm, m' = { m with mem := cm } := by
  unfold typedLoad at h
  cases hlay : Type.layout ty with
  | error e => simp [hlay] at h
  | ok lay =>
    cases hsz : LayoutStrategy.expect_size lay "the callers ensure `ty` is sized" with
    | error e => simp [hlay, hsz] at h
    | ok sz =>
      cases hld : CM.load m.mem p sz align atom with
      | error e => simp [hlay, hsz, hld] at h
      | ok bc =>
        obtain ⟨bytes, cm⟩ := bc
        cases hdec : Type.decode ty bytes with
        | error e => simp [hlay, hsz, hld, hdec] at h
        | ok optVal =>
          cases optVal with
          | none => simp [hlay, hsz, hld, hdec, ub] at h
          | some val =>
            cases hck : checkValue val ty (some { m with mem := cm }) with
            | error e => simp [hlay, hsz, hld, hdec, hck] at h
            | ok u =>
              cases u
              simp [hlay, hsz, hld, hdec, hck] at h
              exact ⟨cm, h.2.symm⟩

private theorem isBoolTy_of_scalarTypeOf {t : MirAst.Ty} (h : scalarTypeOf t = some .Bool) :
    isBoolTy t = true := by
  rcases scalarTypeOf_cases h with ⟨hb, _⟩ | ⟨_, _, hc⟩ | ⟨_, hc⟩ | ⟨_, _, hc⟩
  · exact hb
  · cases hc
  · simp [orderingTy] at hc
  · simp [intBoolTupleTy] at hc

private theorem sameFragmentTy_of_bool {t1 t2 : MirAst.Ty}
    (h1 : isBoolTy t1 = true) (h2 : isBoolTy t2 = true) :
    sameFragmentTy t1 t2 = true := by
  simp [sameFragmentTy, h1, h2]

private theorem sameFragmentTy_of_ordering {t1 t2 : MirAst.Ty}
    (h1 : isOrderingTy t1 = true) (h2 : isOrderingTy t2 = true) :
    sameFragmentTy t1 t2 = true := by
  simp [sameFragmentTy, h1, h2]

private theorem sameFragmentTy_of_tuple {t1 t2 : MirAst.Ty} {it : Gen.IntType}
    (h1 : intBoolTupleOf t1 = some it) (h2 : intBoolTupleOf t2 = some it) :
    sameFragmentTy t1 t2 = true := by
  simp [sameFragmentTy, h1, h2]

private theorem sameFragmentTy_of_int {t1 t2 : MirAst.Ty} {it : Gen.IntType}
    (h1 : intTypeOf t1 = some it) (h2 : intTypeOf t2 = some it) :
    sameFragmentTy t1 t2 = true := by
  simp [sameFragmentTy, h1, h2]

/-- Syntactic and typing cases of a fragment call argument `op` checked by
`callArgOk` and translated by `translateCallArg`. -/
inductive CallArgShape (decls : List LocalDecl) (pd : LocalDecl) :
    Operand → Gen.ArgumentExpr → Prop where
  | copyRoot (j : Nat) (hj : j < decls.length)
      (hsame : ∀ d, decls[j]? = some d → sameFragmentTy d.ty pd.ty = true) :
      CallArgShape decls pd (.copy ⟨j, []⟩) (.ByValue (.Load (.Local (localName j))))
  | moveRoot (j : Nat) (hj : j < decls.length)
      (hsame : ∀ d, decls[j]? = some d → sameFragmentTy d.ty pd.ty = true) :
      CallArgShape decls pd (.move ⟨j, []⟩) (.InPlace (.Local (localName j)))
  | copyField0 (j : Nat) (fTy : Ty) (it : Gen.IntType) (hj : j < decls.length)
      (hpd : intTypeOf pd.ty = some it) (hfTy : intTypeOf fTy = some it)
      (htup : ∀ d, decls[j]? = some d → intBoolTupleOf d.ty = some it) :
      CallArgShape decls pd (.copy ⟨j, [.field 0 fTy]⟩)
        (.ByValue (.Load (.Field (.Local (localName j)) 0)))
  | copyField1 (j : Nat) (fTy : Ty) (hj : j < decls.length)
      (hpd : isBoolTy pd.ty = true) (hfTy : isBoolTy fTy = true)
      (htup : ∀ d, decls[j]? = some d → ∃ it, intBoolTupleOf d.ty = some it) :
      CallArgShape decls pd (.copy ⟨j, [.field 1 fTy]⟩)
        (.ByValue (.Load (.Field (.Local (localName j)) 1)))
  | constScalar (c : MirAst.ConstOperand) (sc : ScalarInt) (e : Gen.ValueExpr)
      (hc : c.val = .scalar (.int sc))
      (hslot : SlotOk (tyOf pd) (.init (.scalar sc)))
      (heval : ∀ m : Mach, evalValue m e = .ok ((valOfValue (tyOf pd) (.scalar sc), tyOf pd), m)) :
      CallArgShape decls pd (.constant c) (.ByValue e)

/-- Under scalar-only declarations, a fragment integer place is a root integer
local `_j` or field `0` of an `(it, bool)` tuple local. -/
theorem placeOk_scalar_cases {layouts : Layout.LayoutTable} {decls : List LocalDecl}
    {it : Gen.IntType} {j : Nat} {proj : List ProjectionElem}
    (hsc : ∀ (j : Nat) (d : LocalDecl), decls[j]? = some d → (scalarTypeOf d.ty).isSome = true)
    (h : placeOk layouts decls it ⟨j, proj⟩ = true) :
    (proj = [] ∧ j < decls.length ∧ ∀ d, decls[j]? = some d → intTypeOf d.ty = some it) ∨
    (∃ fTy, proj = [.field 0 fTy] ∧ j < decls.length ∧ intTypeOf fTy = some it ∧
      ∀ d, decls[j]? = some d → intBoolTupleOf d.ty = some it) := by
  have hnone : ∀ d, decls[j]? = some d →
      arrayTypeOf d.ty = none ∧ tupleTypeOf layouts d.ty = none := by
    intro d hd
    obtain ⟨T, hT⟩ := Option.isSome_iff_exists.mp (hsc j d hd)
    exact ⟨arrayTypeOf_none_of_scalarTypeOf hT, tupleTypeOf_none_of_scalarTypeOf hT⟩
  cases proj with
  | nil =>
    simp only [placeOk, Bool.and_eq_true, decide_eq_true_eq] at h
    refine .inl ⟨rfl, h.1, fun d hd => ?_⟩
    simpa [hd] using h.2
  | cons e rest =>
    cases e with
    | field idx fTy =>
      simp only [placeOk, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨hj, h⟩ := h
      cases hd : decls[j]? with
      | none => simp [hd] at h
      | some d =>
        simp only [hd] at h
        cases ht : intBoolTupleOf d.ty with
        | none => simp [ht, (hnone d hd).2] at h
        | some tupIt =>
          simp only [ht] at h
          split at h
          · next fIt hfIt =>
            simp only [Bool.and_eq_true, decide_eq_true_eq] at h
            obtain ⟨rfl, rfl⟩ := h
            refine .inr ⟨fTy, rfl, hj, hfIt, fun d' hd' => ?_⟩
            simp only [Option.some.injEq] at hd'
            subst hd'
            exact ht
          · simp at h
    | deref | index _ | constantIndex _ _ _ | subslice _ _ _ | downcast _ _ | opaqueCast _
    | unwrapUnsafeBinder _ =>
      cases rest with
      | nil =>
        simp only [placeOk, Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨hj, h⟩ := h
        cases hd : decls[j]? with
        | none => simp [hd] at h
        | some d => simp [hd, (hnone d hd).1] at h
      | cons e2 rest2 => simp [placeOk] at h

theorem callArgOk_cases {decls : List LocalDecl} {pd : LocalDecl} {op : Operand}
    {argExpr : Gen.ArgumentExpr} (hdecls : decls.all (fun d => (scalarTypeOf d.ty).isSome) = true)
    (hok : callArgOk layouts decls pd op = true)
    (htr : translateCallArg decls op = some argExpr) :
    CallArgShape decls pd op argExpr := by
  have hsc : ∀ (j : Nat) (d : LocalDecl), decls[j]? = some d → (scalarTypeOf d.ty).isSome = true :=
    fun j d hd => List.all_eq_true.mp hdecls d (List.mem_of_getElem? hd)
  unfold callArgOk at hok
  simp only [Bool.and_eq_true] at hok
  obtain ⟨hshape, hty⟩ := hok
  by_cases hpb : isBoolTy pd.ty = true
  · simp only [hpb, ↓reduceIte] at hty
    match op, hshape, hty, htr with
    | .copy ⟨j, []⟩, _, hty, htr =>
      simp only [copyOp, operandOkB, Bool.and_eq_true, decide_eq_true_eq, operandIsBool,
        operandType] at hty
      simp only [translateCallArg, translateOperand, translatePlace, Option.map_some,
        Option.some.injEq] at htr
      subst htr
      refine .copyRoot j hty.1 (fun d hd => ?_)
      rw [hd] at hty
      cases hs : scalarTypeOf d.ty with
      | none => simp [hs] at hty
      | some T =>
        have hTB : T = .Bool := by split at hty <;> simp_all
        subst hTB
        exact sameFragmentTy_of_bool (isBoolTy_of_scalarTypeOf hs) hpb
    | .move ⟨j, []⟩, _, hty, htr =>
      simp only [copyOp, operandOkB, Bool.and_eq_true, decide_eq_true_eq, operandIsBool,
        operandType] at hty
      simp only [translateCallArg, translatePlace, Option.map_some, Option.some.injEq] at htr
      subst htr
      refine .moveRoot j hty.1 (fun d hd => ?_)
      rw [hd] at hty
      cases hs : scalarTypeOf d.ty with
      | none => simp [hs] at hty
      | some T =>
        have hTB : T = .Bool := by split at hty <;> simp_all
        subst hTB
        exact sameFragmentTy_of_bool (isBoolTy_of_scalarTypeOf hs) hpb
    | .move ⟨_, _ :: _⟩, hshape, _, _ => simp at hshape
    | .copy ⟨j, [.field 1 fTy]⟩, _, hty, htr =>
      simp only [copyOp, operandOkB, Bool.and_eq_true, decide_eq_true_eq,
        Option.bind_eq_bind] at hty
      have hcast1 : ((1 : Nat) : Int) = 1 := rfl
      simp only [translateCallArg, translateOperand, translatePlace, translateFieldPlace, hcast1,
        Option.map_some, Option.some.injEq] at htr
      subst htr
      obtain ⟨hj, hb⟩ := hty
      obtain ⟨d0, hd0⟩ : ∃ d, decls[j]? = some d := ⟨_, List.getElem?_eq_getElem hj⟩
      rw [hd0] at hb
      simp only [Option.bind_some] at hb
      cases ht0 : intBoolTupleOf d0.ty with
      | none => simp [ht0] at hb
      | some it0 =>
        simp only [ht0] at hb
        by_cases hfB : isBoolTy fTy = true
        · refine .copyField1 j fTy hj hpb hfB (fun d hd => ?_)
          rw [hd0] at hd; cases hd; exact ⟨it0, ht0⟩
        · simp [hfB] at hb
    | .copy ⟨_, [.field 0 _]⟩, _, hty, _ => simp [copyOp, operandOkB] at hty
    | .copy ⟨_, [.field (_ + 2) _]⟩, _, hty, _ => simp [copyOp, operandOkB] at hty
    | .copy ⟨_, [.deref]⟩, _, hty, _ => simp [copyOp, operandOkB] at hty
    | .copy ⟨_, [.index _]⟩, _, hty, _ => simp [copyOp, operandOkB] at hty
    | .copy ⟨_, [.constantIndex _ _ _]⟩, _, hty, _ => simp [copyOp, operandOkB] at hty
    | .copy ⟨_, [.subslice _ _ _]⟩, _, hty, _ => simp [copyOp, operandOkB] at hty
    | .copy ⟨_, [.downcast _ _]⟩, _, hty, _ => simp [copyOp, operandOkB] at hty
    | .copy ⟨_, [.opaqueCast _]⟩, _, hty, _ => simp [copyOp, operandOkB] at hty
    | .copy ⟨_, [.unwrapUnsafeBinder _]⟩, _, hty, _ => simp [copyOp, operandOkB] at hty
    | .copy ⟨_, _ :: _ :: _⟩, _, hty, _ => simp [copyOp, operandOkB] at hty
    | .constant c, _, hty, htr =>
      simp only [copyOp, operandOkB, Bool.and_eq_true, operandIsBool, operandType] at hty
      obtain ⟨hcb, _⟩ := hty
      have hcBool : isBoolTy c.ty = true := by
        cases hs : scalarTypeOf c.ty with
        | none => simp [hs] at hcb
        | some T =>
          have hTB : T = .Bool := by split at hcb <;> simp_all
          subst hTB
          exact isBoolTy_of_scalarTypeOf hs
      simp only [translateCallArg, Option.map_eq_some_iff] at htr
      obtain ⟨e, he, rfl⟩ := htr
      simp only [translateOperand, hcBool, ↓reduceIte] at he
      cases hv : c.val with
      | zeroSized | unevaluated _ | indirect _ _ | slice _ _ => simp [hv] at he
      | scalar sv =>
        cases sv with
        | ptr => simp [hv] at he
        | int sc =>
          cases sc with
          | mk bits sz =>
            simp only [hv] at he
            split at he
            · next hc =>
              simp only [Option.some.injEq] at he
              subst he
              obtain ⟨rfl, hbits⟩ := hc
              have hpdTy : tyOf pd = .Bool := (tyOf_bool hpb).1
              refine .constScalar c ⟨bits, 1⟩ _ hv ?_ (fun m => ?_)
              · rw [hpdTy]; exact ⟨rfl, hbits⟩
              · rw [hpdTy]; simp [evalValue, evalConstant, valOfValue, valOf]
            · simp at he
  · simp only [hpb, Bool.false_eq_true, ↓reduceIte] at hty
    by_cases hpo : isOrderingTy pd.ty = true
    · simp only [hpo, ↓reduceIte] at hty
      match op, hshape, hty, htr with
      | .copy ⟨j, []⟩, _, hty, htr =>
        simp only [copyOp, operandOkO, Bool.and_eq_true, decide_eq_true_eq,
          operandIsOrdering] at hty
        simp only [translateCallArg, translateOperand, translatePlace, Option.map_some,
          Option.some.injEq] at htr
        subst htr
        refine .copyRoot j hty.1 (fun d hd => ?_)
        rw [hd] at hty
        exact sameFragmentTy_of_ordering hty.2 hpo
      | .move ⟨j, []⟩, _, hty, htr =>
        simp only [copyOp, operandOkO, Bool.and_eq_true, decide_eq_true_eq,
          operandIsOrdering] at hty
        simp only [translateCallArg, translatePlace, Option.map_some, Option.some.injEq] at htr
        subst htr
        refine .moveRoot j hty.1 (fun d hd => ?_)
        rw [hd] at hty
        exact sameFragmentTy_of_ordering hty.2 hpo
      | .move ⟨_, _ :: _⟩, hshape, _, _ => simp at hshape
      | .copy ⟨_, _ :: _⟩, _, hty, _ => simp [copyOp, operandOkO] at hty
      | .constant c, _, hty, _ =>
        simp only [copyOp, operandOkO, Bool.and_eq_true] at hty
        rw [translateOperand_ordering_const hty.1] at hty
        simp at hty
    · simp only [hpo, Bool.false_eq_true, ↓reduceIte] at hty
      cases hpt : intBoolTupleOf pd.ty with
      | some it =>
        simp only [hpt] at hty
        match op, hshape, hty, htr with
        | .copy ⟨j, []⟩, _, hty, htr =>
          simp only [copyOp, operandOkTuple, Bool.and_eq_true, decide_eq_true_eq] at hty
          simp only [translateCallArg, translateOperand, translatePlace, Option.map_some,
            Option.some.injEq] at htr
          subst htr
          refine .copyRoot j hty.1 (fun d hd => ?_)
          have htu := hty.2
          simp [operandTupleIntType, hd] at htu
          exact sameFragmentTy_of_tuple htu hpt
        | .move ⟨j, []⟩, _, hty, htr =>
          simp only [copyOp, operandOkTuple, Bool.and_eq_true, decide_eq_true_eq] at hty
          simp only [translateCallArg, translatePlace, Option.map_some, Option.some.injEq] at htr
          subst htr
          refine .moveRoot j hty.1 (fun d hd => ?_)
          have htu := hty.2
          simp [operandTupleIntType, hd] at htu
          exact sameFragmentTy_of_tuple htu hpt
        | .move ⟨_, _ :: _⟩, hshape, _, _ => simp at hshape
        | .copy ⟨_, _ :: _⟩, _, hty, _ => simp [copyOp, operandOkTuple] at hty
        | .constant _, _, hty, _ => simp [copyOp, operandOkTuple] at hty
      | none =>
        simp only [hpt] at hty
        cases hpi : intTypeOf pd.ty with
        | none => simp [hpi] at hty
        | some it =>
          simp only [hpi] at hty
          match op, hshape, hty, htr with
          | .copy ⟨j, proj⟩, _, hty, htr =>
            simp only [copyOp, operandOk, Bool.and_eq_true] at hty
            rcases placeOk_scalar_cases hsc hty.1 with ⟨rfl, hj, hi⟩ | ⟨fTy, rfl, hj, hf0, ht0⟩
            · simp only [translateCallArg, translateOperand, translatePlace, Option.map_some,
                Option.some.injEq] at htr
              subst htr
              exact .copyRoot j hj (fun d hd => sameFragmentTy_of_int (hi d hd) hpi)
            · have hcast0 : ((0 : Nat) : Int) = 0 := rfl
              simp only [translateCallArg, translateOperand, translatePlace, translateFieldPlace,
                hcast0, Option.map_some, Option.some.injEq] at htr
              subst htr
              exact .copyField0 j fTy it hj hpi hf0 ht0
          | .move ⟨j, []⟩, _, hty, htr =>
            simp only [copyOp, operandOk, Bool.and_eq_true] at hty
            rcases placeOk_scalar_cases hsc hty.1 with ⟨_, hj, hi⟩ | ⟨fTy, hc, _⟩
            · simp only [translateCallArg, translatePlace, Option.map_some,
                Option.some.injEq] at htr
              subst htr
              exact .moveRoot j hj (fun d hd => sameFragmentTy_of_int (hi d hd) hpi)
            · cases hc
          | .move ⟨_, _ :: _⟩, hshape, _, _ => simp at hshape
          | .constant c, _, hty, htr =>
            simp only [copyOp, operandOk, Bool.and_eq_true] at hty
            have hci : intTypeOf c.ty = some it := by
              have := of_decide_eq_true hty.1
              simpa [operandIntType] using this
            simp only [translateCallArg, Option.map_eq_some_iff] at htr
            obtain ⟨e, he, rfl⟩ := htr
            simp only [translateOperand, intTypeOf_isBoolTy hci, hci, Bool.false_eq_true,
              ↓reduceIte] at he
            cases hv : c.val with
            | zeroSized | unevaluated _ | indirect _ _ | slice _ _ => simp [hv] at he
            | scalar sv =>
              cases sv with
              | ptr => simp [hv] at he
              | int sc =>
                cases sc with
                | mk bits sz =>
                  simp only [hv] at he
                  split at he
                  · next hc =>
                    simp only [Option.some.injEq] at he
                    subst he
                    obtain ⟨rfl, hbits⟩ := hc
                    have hpdTy : tyOf pd = .Int it := (tyOf_int hpi).1
                    refine .constScalar c ⟨bits, it.size.bytes⟩ _ hv ?_ (fun m => ?_)
                    · rw [hpdTy]; exact ⟨rfl, hbits⟩
                    · rw [hpdTy]; simp [evalValue, evalConstant, valOfValue, valOf]
                  · simp at he

/-- Evaluating one call argument `argExpr` (`ByValue` or `InPlace`) under
`CallerDestRel` and multi-frame `Shape`. -/
theorem evalArgument_spec {callerBody : CapturedMir} {callerFn : Gen.Function}
    {rootCtx callerCtx : Ctx} {callerFrames : List Frame}
    {actual view : List LocalSlot} {callerLm : Map Gen.LocalName Ptr}
    {blk stmt : Nat} {m : Mach} {calleeRetDecl pd : LocalDecl}
    {calleeRetPtr : Ptr} {destination : Place} {mo0 : List Nat}
    {op : Operand} {argExpr : Gen.ArgumentExpr}
    (hf : FnLocalsSpec callerBody callerFn)
    (hcallerScalar : callerBody.localDecls.all (fun d => (scalarTypeOf d.ty).isSome) = true)
    (hsh : Shape m rootCtx
      (callerFrames ++ [calleeFrameL callerFn callerCtx callerLm blk stmt])
      m.mem.memory.allocations)
    (hdest : CallerDestRel callerBody callerCtx actual view callerLm calleeRetDecl
      m.mem.memory.allocations calleeRetPtr destination)
    (halen : actual.length = view.length)
    (hstale : ∀ k : Nat, k ≠ destination.local_ → actual[k]? ≠ view[k]? →
      k ∈ mo0 ∧ actual[k]? = some .uninit ∧ view[k]? ≠ some .dead)
    (hnotMo : ∀ j, opRead op = some j → j ∉ mo0)
    (hnotDst : opRead op ≠ some destination.local_)
    (hok : callArgOk callerBody.layouts callerBody.localDecls pd op = true)
    (htr : translateCallArg callerBody.localDecls op = some argExpr) :
    (∀ v, callArgVal actual op = some v →
      SlotOk (tyOf pd) (.init v) ∧
      ∃ m' view',
        evalArgument m argExpr = .ok ((valOfValue (tyOf pd) v, tyOf pd), m') ∧
        Shape m' rootCtx
          (callerFrames ++ [calleeFrameL callerFn callerCtx callerLm blk stmt])
          m'.mem.memory.allocations ∧
        m'.prog = m.prog ∧ m'.fn_ptrs = m.fn_ptrs ∧
        (opMoveLocal actual op).length = view'.length ∧
        (∀ k : Nat, k ≠ destination.local_ → (opMoveLocal actual op)[k]? ≠ view'[k]? →
          k ∈ mo0 ∧ (opMoveLocal actual op)[k]? = some .uninit ∧ view'[k]? ≠ some .dead) ∧
        CallerDestRel callerBody callerCtx (opMoveLocal actual op) view' callerLm calleeRetDecl
          m'.mem.memory.allocations calleeRetPtr destination) ∧
    (callArgVal actual op = none →
      ∃ msg, evalArgument m argExpr = .error (.ub msg)) := by
  let fr := calleeFrameL callerFn callerCtx callerLm blk stmt
  have hshR : Shape (rethread m callerCtx [callerCtx.caller, fr]) callerCtx
      [callerCtx.caller, fr] m.mem.memory.allocations :=
    ⟨rfl, hsh.active, hsh.allocs⟩
  have hscOf : ∀ (j : Nat) (d : LocalDecl), callerBody.localDecls[j]? = some d →
      (scalarTypeOf d.ty).isSome = true :=
    fun j d hd => List.all_eq_true.mp hcallerScalar d (List.mem_of_getElem? hd)
  -- MR-4-style facts for a scalar local `_j`: its translated type and slot invariant.
  have hspecOf : ∀ (j : Nat) (d : LocalDecl), callerBody.localDecls[j]? = some d →
      scalarTypeOf d.ty = some (tyOf d) ∧ mapGet callerFn.locals (localName j) = some (tyOf d) :=
    fun j d hd => ⟨scalarTypeOf_tyOf_of_isSome (hscOf j d hd) _,
      by rw [(hf.2 j d hd).2, tyOf_scalar_layouts (hscOf j d hd) callerBody.layouts ⟨64, true, []⟩]⟩
  have hslotsOf : ∀ (j : Nat) (d : LocalDecl) (slot : LocalSlot),
      callerBody.localDecls[j]? = some d → view[j]? = some slot → SlotOk (tyOf d) slot := by
    intro j d slot hd hvs
    have h := hdest.slots j d slot hd hvs
    obtain ⟨T, hT⟩ := Option.isSome_iff_exists.mp (hscOf j d hd)
    rwa [DeclSlotOk_of_scalarTypeOf hT,
      tyOf_scalar_layouts (hscOf j d hd) callerBody.layouts ⟨64, true, []⟩] at h
  cases callArgOk_cases hcallerScalar hok htr with
  | copyRoot j hj hsame =>
    have hjNeDst : j ≠ destination.local_ := fun heq => hnotDst (by simp [opRead, heq])
    have hjNotMo : j ∉ mo0 := hnotMo j rfl
    have havEq : actual[j]? = view[j]? := by
      exact Classical.byContradiction fun hne => hjNotMo (hstale j hjNeDst hne).1
    obtain ⟨d, hd⟩ : ∃ d, callerBody.localDecls[j]? = some d := ⟨_, List.getElem?_eq_getElem hj⟩
    have hvlt : j < view.length := by rw [hdest.nlocals]; exact hj
    obtain ⟨slot, hvs⟩ : ∃ s, view[j]? = some s := ⟨_, List.getElem?_eq_getElem hvlt⟩
    have has : actual[j]? = some slot := havEq.trans hvs
    obtain ⟨hTyEq, _, _, _⟩ := sameFragmentTy_spec (hsame d hd)
    have hspec := hspecOf j d hd
    have hslotOk := hslotsOf j d slot hd hvs
    have hplEq := evalPlace_rethread_derefFree (.Local (localName j)) rfl m rootCtx callerCtx
      callerFrames fr hsh.threads hsh.active
    cases hp : mapGet callerLm (localName j) with
    | none =>
      have hdead := hdest.dead_of_none hvs hp
      subst hdead
      refine ⟨fun v hv => by simp [callArgVal, has] at hv, fun _ => ?_⟩
      have hplR := evalPlace_local_none hshR j (tyOf d) hspec.2 hp
      exact ⟨"access to a dead local", by simp [evalArgument, evalValue, hplEq, hplR, Except.map]⟩
    | some p =>
      obtain ⟨id, hpid, _, hA⟩ := hdest.storage_ne hjNeDst hd (hscOf j d hd) hvs hp
      have hplR := evalPlace_local_some hshR j (tyOf d) hspec.2 p hp
      have hpl : evalPlace m (.Local (localName j)) =
          .ok (({ ptr := ThinPointer.widen p none, aligned := true }, tyOf pd), m) := by
        rw [hplEq, hplR, ← hTyEq]; rfl
      cases slot with
      | dead =>
        refine ⟨fun v hv => by simp [callArgVal, has] at hv, fun _ => ?_⟩
        rw [declSlotData_dead] at hA
        obtain ⟨msg, hmsg⟩ :=
          typedLoad_ptr_localTy_uninit hsh p id hpid d hspec.1 hA ⟨1⟩ (isAligned_one _)
        rw [hTyEq] at hmsg
        exact ⟨msg, by simp [evalArgument, evalValue, hpl, placeLoad, ThinPointer.widen, hmsg]⟩
      | uninit =>
        refine ⟨fun v hv => by simp [callArgVal, has] at hv, fun _ => ?_⟩
        obtain ⟨msg, hmsg⟩ :=
          typedLoad_ptr_localTy_uninit hsh p id hpid d hspec.1 hA ⟨1⟩ (isAligned_one _)
        rw [hTyEq] at hmsg
        exact ⟨msg, by simp [evalArgument, evalValue, hpl, placeLoad, ThinPointer.widen, hmsg]⟩
      | init v0 =>
        refine ⟨fun v hv => ?_, fun hn => by simp [callArgVal, has] at hn⟩
        simp [callArgVal, has] at hv; subst hv
        have hslotPd : SlotOk (tyOf pd) (.init v0) := hTyEq ▸ hslotOk
        obtain ⟨m', hm', hsh'⟩ :=
          typedLoad_ptr_localTy hsh p id hpid d hspec.1 v0 hslotOk hA ⟨1⟩ (isAligned_one _)
        obtain ⟨cm', rfl⟩ := typedLoad_mem_only hm'
        rw [hTyEq] at hm'
        refine ⟨hslotPd, _, view, ?_, ⟨hsh'.threads, hsh'.active, rfl⟩, rfl, rfl, halen, hstale, ?_⟩
        · simp [evalArgument, evalValue, hpl, placeLoad, ThinPointer.widen, hm']
        · have hmemEq : cm'.memory.allocations = m.mem.memory.allocations := hsh'.allocs
          simpa [opMoveLocal, opMoved, hmemEq] using hdest
  | moveRoot j hj hsame =>
    have hjNeDst : j ≠ destination.local_ := fun heq => hnotDst (by simp [opRead, heq])
    have hjNotMo : j ∉ mo0 := hnotMo j rfl
    have havEq : actual[j]? = view[j]? := by
      exact Classical.byContradiction fun hne => hjNotMo (hstale j hjNeDst hne).1
    obtain ⟨d, hd⟩ : ∃ d, callerBody.localDecls[j]? = some d := ⟨_, List.getElem?_eq_getElem hj⟩
    have hvlt : j < view.length := by rw [hdest.nlocals]; exact hj
    have halt : j < actual.length := by rw [halen]; exact hvlt
    obtain ⟨slot, hvs⟩ : ∃ s, view[j]? = some s := ⟨_, List.getElem?_eq_getElem hvlt⟩
    have has : actual[j]? = some slot := havEq.trans hvs
    obtain ⟨hTyEq, _, _, _⟩ := sameFragmentTy_spec (hsame d hd)
    have hspec := hspecOf j d hd
    have hslotOk := hslotsOf j d slot hd hvs
    have hplEq := evalPlace_rethread_derefFree (.Local (localName j)) rfl m rootCtx callerCtx
      callerFrames fr hsh.threads hsh.active
    cases hp : mapGet callerLm (localName j) with
    | none =>
      have hdead := hdest.dead_of_none hvs hp
      subst hdead
      refine ⟨fun v hv => by simp [callArgVal, has] at hv, fun _ => ?_⟩
      have hplR := evalPlace_local_none hshR j (tyOf d) hspec.2 hp
      exact ⟨"access to a dead local", by simp [evalArgument, hplEq, hplR, Except.map]⟩
    | some p =>
      obtain ⟨id, hpid, haddr, hA⟩ := hdest.storage_ne hjNeDst hd (hscOf j d hd) hvs hp
      have hplR := evalPlace_local_some hshR j (tyOf d) hspec.2 p hp
      have hpl : evalPlace m (.Local (localName j)) =
          .ok (({ ptr := ThinPointer.widen p none, aligned := true }, tyOf pd), m) := by
        rw [hplEq, hplR, ← hTyEq]; rfl
      cases slot with
      | dead =>
        refine ⟨fun v hv => by simp [callArgVal, has] at hv, fun _ => ?_⟩
        rw [declSlotData_dead] at hA
        obtain ⟨msg, hmsg⟩ :=
          typedLoad_ptr_localTy_uninit hsh p id hpid d hspec.1 hA ⟨1⟩ (isAligned_one _)
        rw [hTyEq] at hmsg
        exact ⟨msg, by simp [evalArgument, hpl, placeLoad, ThinPointer.widen, hmsg]⟩
      | uninit =>
        refine ⟨fun v hv => by simp [callArgVal, has] at hv, fun _ => ?_⟩
        obtain ⟨msg, hmsg⟩ :=
          typedLoad_ptr_localTy_uninit hsh p id hpid d hspec.1 hA ⟨1⟩ (isAligned_one _)
        rw [hTyEq] at hmsg
        exact ⟨msg, by simp [evalArgument, hpl, placeLoad, ThinPointer.widen, hmsg]⟩
      | init v0 =>
        refine ⟨fun v hv => ?_, fun hn => by simp [callArgVal, has] at hn⟩
        simp [callArgVal, has] at hv; subst hv
        have hslotPd : SlotOk (tyOf pd) (.init v0) := hTyEq ▸ hslotOk
        obtain ⟨m1, hm1, hsh1⟩ :=
          typedLoad_ptr_localTy hsh p id hpid d hspec.1 v0 hslotOk hA ⟨1⟩ (isAligned_one _)
        obtain ⟨cm1, rfl⟩ := typedLoad_mem_only hm1
        have hmem1 : cm1.memory.allocations = m.mem.memory.allocations := hsh1.allocs
        have hA1 : cm1.memory.allocations[id]? =
            some (stackAlloc p.addr (itOf d) (declSlotData d (.init v0))) := by
          rw [hmem1]; exact hA
        have hlen := declSlotData_length hspec.1 (.init v0)
        have hprep :=
          prepareForInplacePassing_ptr_whole (m := { m with mem := cm1 }) hpid d hspec.1 _ hA1 hlen haddr
        rw [hTyEq] at hm1 hprep
        let m2 := withMem { m with mem := cm1 }
          (cm1.memory.allocations.set id (stackAlloc p.addr (itOf d) (declSlotData d .uninit)))
          ⟨.Store, .None, p.addr, ⟨tyBytes (tyOf pd)⟩⟩
        refine ⟨hslotPd, m2, view.set j .uninit, ?_, withMem_shape hsh1 _, rfl, rfl, ?_, ?_, ?_⟩
        · unfold evalArgument
          dsimp only
          rw [hpl, ok_bind]
          have hld : placeLoad m { ptr := ThinPointer.widen p none, aligned := true } (tyOf pd) =
              .ok (valOfValue (tyOf pd) v0, { m with mem := cm1 }) := by
            simp [placeLoad, ThinPointer.widen, hm1]
          rw [hld, ok_bind, hprep, ok_bind]
          rfl
        · simp [opMoveLocal, opMoved, halen]
        · intro k hkDst hkne
          simp only [opMoveLocal, opMoved] at hkne ⊢
          by_cases hkj : k = j
          · subst hkj
            rw [List.getElem?_set_self halt, List.getElem?_set_self hvlt] at hkne
            exact absurd rfl hkne
          · rw [List.getElem?_set_ne (Ne.symm hkj), List.getElem?_set_ne (Ne.symm hkj)] at hkne ⊢
            exact hstale k hkDst hkne
        · have hdestMove := hdest.moveArg hjNeDst hd (hscOf j d hd) hvs hp hpid
          simpa [opMoveLocal, opMoved, m2, withMem, hmem1] using hdestMove
  | copyField0 j fTy it hj hpd hfTy htup =>
    have hjNeDst : j ≠ destination.local_ := fun heq => hnotDst (by simp [opRead, heq])
    have hjNotMo : j ∉ mo0 := hnotMo j rfl
    have havEq : actual[j]? = view[j]? := by
      exact Classical.byContradiction fun hne => hjNotMo (hstale j hjNeDst hne).1
    obtain ⟨d, hd⟩ : ∃ d, callerBody.localDecls[j]? = some d := ⟨_, List.getElem?_eq_getElem hj⟩
    have hvlt : j < view.length := by rw [hdest.nlocals]; exact hj
    obtain ⟨slot, hvs⟩ : ∃ s, view[j]? = some s := ⟨_, List.getElem?_eq_getElem hvlt⟩
    have has : actual[j]? = some slot := havEq.trans hvs
    have hdTup := htup d hd
    have hgood := intBoolTupleOf_good hdTup
    obtain ⟨hTd, hitd⟩ := tyOf_tuple (layouts := ⟨64, true, []⟩) hdTup
    have hpdTy : tyOf pd = .Int it := (tyOf_int hpd).1
    have hspec := hspecOf j d hd
    have hloc := hspec.2; rw [hTd] at hloc
    have hslotOk := hslotsOf j d slot hd hvs; rw [hTd] at hslotOk
    have hplEq := evalPlace_rethread_derefFree (.Field (.Local (localName j)) 0) rfl m rootCtx callerCtx
      callerFrames fr hsh.threads hsh.active
    cases hp : mapGet callerLm (localName j) with
    | none =>
      have hdead := hdest.dead_of_none hvs hp
      subst hdead
      refine ⟨fun v hv => by simp [callArgVal, has] at hv, fun _ => ?_⟩
      exact ⟨"access to a dead local",
        by simp [evalArgument, evalValue, hplEq, evalPlace_field_none hshR j _ hloc hp, Except.map]⟩
    | some p =>
      obtain ⟨id, hpid, haddr, hA⟩ := hdest.storage_ne hjNeDst hd (hscOf j d hd) hvs hp
      rw [declSlotData_of_some hdTup, hitd] at hA
      rw [hitd] at haddr
      have hplR := evalPlace_field0L hshR j it hgood hloc p hp haddr
      have hpl : evalPlace m (.Field (.Local (localName j)) 0) =
          .ok (({ ptr := ThinPointer.widen p none, aligned := true }, .Int it), m) := by
        rw [hplEq, hplR]; rfl
      match slot, hslotOk, hA with
      | .dead, _, hA =>
        refine ⟨fun v hv => by simp [callArgVal, has] at hv, fun _ => ?_⟩
        obtain ⟨msg, hmsg⟩ := typedLoad_ptr_tuple_field0_uninit hsh p id hpid it hgood hA
        exact ⟨msg, by simp [evalArgument, evalValue, hpl, placeLoad, ThinPointer.widen, hmsg]⟩
      | .uninit, _, hA =>
        refine ⟨fun v hv => by simp [callArgVal, has] at hv, fun _ => ?_⟩
        obtain ⟨msg, hmsg⟩ := typedLoad_ptr_tuple_field0_uninit hsh p id hpid it hgood hA
        exact ⟨msg, by simp [evalArgument, evalValue, hpl, placeLoad, ThinPointer.widen, hmsg]⟩
      | .init (.scalar _), ⟨_, hb⟩, _ =>
        simp [intBoolTupleTy, ValidBits] at hb
      | .init (.aggregate 0 [.scalar sc0, .scalar sc1]), ⟨it', htyT, hsz0, hb0, _, _⟩, hA =>
        simp only [tupleIntOfTy_intBoolTupleTy, Option.some.injEq] at htyT
        subst htyT
        refine ⟨fun v hv => ?_, fun hn => by simp [callArgVal, has] at hn⟩
        simp [callArgVal, has] at hv; subst hv
        obtain ⟨m', hm', hsh'⟩ :=
          typedLoad_ptr_tuple_field0 hsh p id hpid it hgood sc0.bits sc1.bits hb0 hA
        obtain ⟨cm', rfl⟩ := typedLoad_mem_only hm'
        have hmemEq : cm'.memory.allocations = m.mem.memory.allocations := hsh'.allocs
        refine ⟨by rw [hpdTy]; exact ⟨hsz0, hb0⟩, _, view, ?_, ⟨hsh'.threads, hsh'.active, rfl⟩,
          rfl, rfl, halen, hstale, ?_⟩
        · rw [hpdTy]
          simp [evalArgument, evalValue, hpl, placeLoad, ThinPointer.widen, hm', valOfValue, valOf]
        · simpa [opMoveLocal, opMoved, hmemEq] using hdest
  | copyField1 j fTy hj hpd hfTy htup =>
    have hjNeDst : j ≠ destination.local_ := fun heq => hnotDst (by simp [opRead, heq])
    have hjNotMo : j ∉ mo0 := hnotMo j rfl
    have havEq : actual[j]? = view[j]? := by
      exact Classical.byContradiction fun hne => hjNotMo (hstale j hjNeDst hne).1
    obtain ⟨d, hd⟩ : ∃ d, callerBody.localDecls[j]? = some d := ⟨_, List.getElem?_eq_getElem hj⟩
    have hvlt : j < view.length := by rw [hdest.nlocals]; exact hj
    obtain ⟨slot, hvs⟩ : ∃ s, view[j]? = some s := ⟨_, List.getElem?_eq_getElem hvlt⟩
    have has : actual[j]? = some slot := havEq.trans hvs
    obtain ⟨it, hdTup⟩ := htup d hd
    have hgood := intBoolTupleOf_good hdTup
    obtain ⟨hTd, hitd⟩ := tyOf_tuple (layouts := ⟨64, true, []⟩) hdTup
    have hpdTy : tyOf pd = .Bool := (tyOf_bool hpd).1
    have hspec := hspecOf j d hd
    have hloc := hspec.2; rw [hTd] at hloc
    have hslotOk := hslotsOf j d slot hd hvs; rw [hTd] at hslotOk
    have hplEq := evalPlace_rethread_derefFree (.Field (.Local (localName j)) 1) rfl m rootCtx callerCtx
      callerFrames fr hsh.threads hsh.active
    cases hp : mapGet callerLm (localName j) with
    | none =>
      have hdead := hdest.dead_of_none hvs hp
      subst hdead
      refine ⟨fun v hv => by simp [callArgVal, has] at hv, fun _ => ?_⟩
      exact ⟨"access to a dead local",
        by simp [evalArgument, evalValue, hplEq, evalPlace_field_none hshR j _ hloc hp, Except.map]⟩
    | some p =>
      obtain ⟨id, hpid, haddr, hA⟩ := hdest.storage_ne hjNeDst hd (hscOf j d hd) hvs hp
      rw [declSlotData_of_some hdTup, hitd] at hA
      rw [hitd] at haddr
      have hlen := tupleSlotData_length it slot hgood.pos
      have hplR := evalPlace_field1L hshR j it hgood hloc p hp id hpid _ hA hlen haddr
      have hpl : evalPlace m (.Field (.Local (localName j)) 1) =
          .ok (({ ptr := ThinPointer.widen (field1Ptr p it) none, aligned := true }, .Bool), m) := by
        rw [hplEq, hplR]; rfl
      match slot, hslotOk, hA with
      | .dead, _, hA =>
        refine ⟨fun v hv => by simp [callArgVal, has] at hv, fun _ => ?_⟩
        obtain ⟨msg, hmsg⟩ := typedLoad_ptr_tuple_field1_uninit hsh p id hpid it hgood hA
        exact ⟨msg, by simp [evalArgument, evalValue, hpl, placeLoad, ThinPointer.widen, hmsg]⟩
      | .uninit, _, hA =>
        refine ⟨fun v hv => by simp [callArgVal, has] at hv, fun _ => ?_⟩
        obtain ⟨msg, hmsg⟩ := typedLoad_ptr_tuple_field1_uninit hsh p id hpid it hgood hA
        exact ⟨msg, by simp [evalArgument, evalValue, hpl, placeLoad, ThinPointer.widen, hmsg]⟩
      | .init (.scalar _), ⟨_, hb⟩, _ =>
        simp [intBoolTupleTy, ValidBits] at hb
      | .init (.aggregate 0 [.scalar sc0, .scalar sc1]), ⟨it', htyT, _, _, hsz1, hb1⟩, hA =>
        simp only [tupleIntOfTy_intBoolTupleTy, Option.some.injEq] at htyT
        subst htyT
        refine ⟨fun v hv => ?_, fun hn => by simp [callArgVal, has] at hn⟩
        simp [callArgVal, has] at hv; subst hv
        obtain ⟨m', hm', hsh'⟩ :=
          typedLoad_ptr_tuple_field1 hsh p id hpid it hgood sc0.bits sc1.bits hb1 hA
        obtain ⟨cm', rfl⟩ := typedLoad_mem_only hm'
        have hmemEq : cm'.memory.allocations = m.mem.memory.allocations := hsh'.allocs
        refine ⟨by rw [hpdTy]; exact ⟨hsz1, hb1⟩, _, view, ?_, ⟨hsh'.threads, hsh'.active, rfl⟩,
          rfl, rfl, halen, hstale, ?_⟩
        · rw [hpdTy]
          simp [evalArgument, evalValue, hpl, placeLoad, ThinPointer.widen, hm', valOfValue, valOf]
        · simpa [opMoveLocal, opMoved, hmemEq] using hdest
  | constScalar c sc e hc hslot heval =>
    refine ⟨fun v hv => ?_, fun hn => by simp [callArgVal, hc] at hn⟩
    simp [callArgVal, hc] at hv; subst hv
    exact ⟨hslot, m, view, by simp [evalArgument, heval m], hsh, rfl, rfl, halen, hstale,
      by simpa [opMoveLocal, opMoved] using hdest⟩

/-- The root local of an operand is among the locals it reads. -/
theorem mem_opLocals_of_opRead {op : Operand} {j : Nat} (h : opRead op = some j) :
    j ∈ opLocals op := by
  cases op with
  | constant _ => simp [opRead] at h
  | copy p | move p =>
    simp only [opRead, Option.some.injEq] at h
    subst h
    obtain ⟨jj, proj⟩ := p
    simp only [opLocals, placeLocals]
    split <;> simp_all

/-- Sequential `evalArguments` correspondence over `argOps` against parameter
declarations `paramDecls`. -/
theorem evalArguments_spec {callerBody : CapturedMir} {callerFn : Gen.Function}
    {rootCtx callerCtx : Ctx} {callerFrames : List Frame}
    {actual view : List LocalSlot} {callerLm : Map Gen.LocalName Ptr}
    {blk stmt : Nat} {m : Mach} {calleeRetDecl : LocalDecl}
    {calleeRetPtr : Ptr} {destination : Place} {mo0 mo : List Nat}
    {paramDecls : List LocalDecl} {argOps : List Operand} {argExprs : List Gen.ArgumentExpr}
    (hf : FnLocalsSpec callerBody callerFn)
    (hcallerScalar : callerBody.localDecls.all (fun d => (scalarTypeOf d.ty).isSome) = true)
    (hsh : Shape m rootCtx
      (callerFrames ++ [calleeFrameL callerFn callerCtx callerLm blk stmt])
      m.mem.memory.allocations)
    (hdest : CallerDestRel callerBody callerCtx actual view callerLm calleeRetDecl
      m.mem.memory.allocations calleeRetPtr destination)
    (halen : actual.length = view.length)
    (hstale : ∀ k : Nat, k ≠ destination.local_ → actual[k]? ≠ view[k]? →
      k ∈ mo0 ∧ actual[k]? = some .uninit ∧ view[k]? ≠ some .dead)
    (hsub : ∀ k ∈ mo0, k ∈ mo)
    (hreads : readsOk mo argOps = true)
    (hnotDst : ∀ op ∈ argOps, opRead op ≠ some destination.local_)
    (hok : callArgsOk callerBody.layouts callerBody.localDecls paramDecls argOps = true)
    (htr : argOps.mapM (translateCallArg callerBody.localDecls) = some argExprs) :
    (∀ vs actual', callArgsEval actual argOps = some (vs, actual') →
      vs.length = paramDecls.length ∧
      (∀ (i : Nat) pd v, paramDecls[i]? = some pd → vs[i]? = some v → SlotOk (tyOf pd) (.init v)) ∧
      ∃ m' view',
        evalArguments m argExprs =
          .ok ((paramDecls.zip vs).map (fun (pd, v) => (valOfValue (tyOf pd) v, tyOf pd)), m') ∧
        Shape m' rootCtx
          (callerFrames ++ [calleeFrameL callerFn callerCtx callerLm blk stmt])
          m'.mem.memory.allocations ∧
        m'.prog = m.prog ∧ m'.fn_ptrs = m.fn_ptrs ∧
        actual'.length = view'.length ∧
        (∀ k : Nat, k ≠ destination.local_ → actual'[k]? ≠ view'[k]? →
          k ∈ mo0 ∧ actual'[k]? = some .uninit ∧ view'[k]? ≠ some .dead) ∧
        CallerDestRel callerBody callerCtx actual' view' callerLm calleeRetDecl
          m'.mem.memory.allocations calleeRetPtr destination) ∧
    (callArgsEval actual argOps = none →
      ∃ msg, evalArguments m argExprs = .error (.ub msg)) := by
  induction argOps generalizing m actual view mo paramDecls argExprs with
  | nil =>
    cases paramDecls with
    | cons _ _ => simp [callArgsOk] at hok
    | nil =>
      simp at htr; subst htr
      refine ⟨fun vs actual' hce => ?_, fun hn => by simp [callArgsEval] at hn⟩
      simp [callArgsEval] at hce
      obtain ⟨rfl, rfl⟩ := hce
      refine ⟨rfl, fun i _ _ hp _ => by simp at hp, m, view, ?_, hsh, rfl, rfl, halen, hstale, hdest⟩
      simp [evalArguments]
  | cons op ops ih =>
    cases paramDecls with
    | nil => simp [callArgsOk] at hok
    | cons pd pds =>
      simp only [callArgsOk, Bool.and_eq_true] at hok
      simp only [readsOk, Bool.and_eq_true] at hreads
      simp only [List.mapM_cons, Option.bind_eq_bind] at htr
      cases htr1 : translateCallArg callerBody.localDecls op with
      | none => simp [htr1] at htr
      | some ae =>
        cases htrRest : ops.mapM (translateCallArg callerBody.localDecls) with
        | none => simp [htr1, htrRest] at htr
        | some aes =>
          simp [htr1, htrRest] at htr
          subst htr
          have hnotMo1 : ∀ j, opRead op = some j → j ∉ mo0 := by
            intro j hj hm0
            have h1 := hreads.1.2
            have hjmem : j ∈ opLocals op := mem_opLocals_of_opRead hj
            have h2 := List.all_eq_true.mp h1 j hjmem
            simp only [Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not] at h2
            exact h2 (hsub j hm0)
          have hsub' : ∀ k ∈ mo0, k ∈ moveOut mo op := by
            intro k hk
            unfold moveOut
            cases opMoved op with
            | none => exact hsub k hk
            | some j => exact List.mem_cons_of_mem j (hsub k hk)
          obtain ⟨hevalOk, hevalUb⟩ :=
            evalArgument_spec hf hcallerScalar hsh hdest halen hstale hnotMo1
              (hnotDst op (by simp)) hok.1 htr1
          refine ⟨fun vs actual' hce => ?_, fun hn => ?_⟩
          · simp only [callArgsEval, Option.bind_eq_bind] at hce
            cases hv1 : callArgVal actual op with
            | none => simp [hv1] at hce
            | some v =>
              cases hvRest : callArgsEval (opMoveLocal actual op) ops with
              | none => simp [hv1, hvRest] at hce
              | some pRest =>
                obtain ⟨vRest, actual''⟩ := pRest
                simp [hv1, hvRest] at hce
                obtain ⟨rfl, rfl⟩ := hce
                obtain ⟨hslot1, m1, view1, hm1, hsh1, hp1, hfp1, halen1, hstale1, hdest1⟩ :=
                  hevalOk v hv1
                obtain ⟨ihOk, _⟩ := ih hsh1 hdest1 halen1 hstale1 hsub' hreads.2
                  (fun op' hop' => hnotDst op' (by simp [hop'])) hok.2 htrRest
                obtain ⟨hlenR, hslotsR, m2, view2, hm2, hsh2, hp2, hfp2, halen2, hstale2, hdest2⟩ :=
                  ihOk vRest actual'' hvRest
                refine ⟨by simp [hlenR], fun i pd' v' hpd' hv' => ?_, m2, view2, ?_, hsh2,
                  hp2.trans hp1, hfp2.trans hfp1, halen2, hstale2, hdest2⟩
                · cases i with
                  | zero =>
                    simp at hpd' hv'; subst hpd' hv'; exact hslot1
                  | succ i =>
                    simp at hpd' hv'; exact hslotsR i pd' v' hpd' hv'
                · simp [evalArguments, hm1, hm2]
          · simp only [callArgsEval, Option.bind_eq_bind] at hn
            cases hv1 : callArgVal actual op with
            | none =>
              obtain ⟨msg, hmsg⟩ := hevalUb hv1
              exact ⟨msg, by simp [evalArguments, hmsg]⟩
            | some v =>
              simp only [hv1, Option.bind_some] at hn
              have hvRest : callArgsEval (opMoveLocal actual op) ops = none := by
                cases h : callArgsEval (opMoveLocal actual op) ops with
                | none => rfl
                | some p => obtain ⟨_, _⟩ := p; simp [h] at hn
              obtain ⟨_, m1, view1, hm1, hsh1, _, _, halen1, hstale1, hdest1⟩ := hevalOk v hv1
              obtain ⟨_, ihUb⟩ := ih hsh1 hdest1 halen1 hstale1 hsub' hreads.2
                (fun op' hop' => hnotDst op' (by simp [hop'])) hok.2 htrRest
              obtain ⟨msg, hmsg⟩ := ihUb hvRest
              exact ⟨msg, by simp [evalArguments, hm1, hmsg]⟩

/-- Allocating a single dead local `_i` via `storageLive` inside `createFrame`
under `BaseCandBounded`. -/
private theorem storageLive_fresh_cand {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {locals : List LocalSlot} {lm : Map Gen.LocalName Ptr} {cm : Gen.ConcurrentMemory BM}
    {blk stmt bound : Nat} (hf : FnLocalsSpec body f)
    (hdecls : ∀ (i : Nat) d, body.localDecls[i]? = some d → scalarTypeOf d.ty = some (tyOf d))
    (hlo : LocalsOkA body ctx [] locals lm cm.memory.allocations)
    (i : Nat) (d : LocalDecl) (hd : body.localDecls[i]? = some d)
    (hsi : locals[i]? = some .dead)
    (hbase : BaseCandBounded ctx.base bound) (hn : bound + body.localDecls.length < 2 ^ 31) :
    ∃ lm' cm',
      storageLive (calleeFrameL f ctx lm blk stmt) cm (localName i) =
        .ok (calleeFrameL f ctx lm' blk stmt, cm') ∧
      LocalsOkA body ctx [] (locals.set i .uninit) lm' cm'.memory.allocations := by
  have hp : mapGet lm (localName i) = none := hlo.none_of_dead hsi (by simp)
  have hdSc := hdecls i d hd
  have hsc : (scalarTypeOf d.ty).isSome = true := by simp [hdSc]
  have hloc : mapGet f.locals (localName i) = some (tyOf d) := by
    rw [(hf.2 i d hd).2, tyOf_scalar_layouts hsc body.layouts ⟨64, true, []⟩]
  have hlt := localTy_of_decl hdSc
  have hnot : ∀ e ∈ lm.entries, e.1 ≠ localName i := by
    intro e he hei
    obtain ⟨k', v'⟩ := e
    simp only at hei; subst hei
    have := mapGet_isSome_of_mem (es := lm.entries) he
    rw [hp] at this; simp at this
  have hsd : storageDead (calleeFrameL f ctx lm blk stmt) cm (localName i) =
      .ok (calleeFrameL f ctx lm blk stmt, cm) :=
    storageDead_none' hlt hloc (by simpa [calleeFrameL] using hp)
  have hle : tyBytes (tyOf d) ≤ 32 := scalar_tyBytes_le (.inl hsc)
  obtain ⟨k, _, halloc, haddr, hmax⟩ :=
    BM_allocate_local_cand (mem := cm.memory) hlo hbase hn hdecls hlt hle
  let newPtr : Ptr :=
    { addr := allocCandidate k, provenance := some (⟨(cm.memory.allocations.length : Int)⟩, ()) }
  have hins : mapInsertMap lm (localName i) newPtr = ⟨lm.entries ++ [(localName i, newPtr)]⟩ := by
    simp only [mapInsertMap]; rw [mapInsert_absent _ _ _ hnot]
  have hmi : mapIndex (calleeFrameL f ctx lm blk stmt).func.locals (localName i)
      "self.func.locals[local]" = .ok (tyOf d) := by
    simp [mapIndex, calleeFrameL, hloc]
  have hca : CM.allocate cm .Stack ⟨tyBytes (tyOf d)⟩ ⟨(itOf d).size.bytes⟩ =
      .ok (newPtr,
        { cm with memory := { cm.memory with
          allocations := cm.memory.allocations ++
            [stackAlloc (allocCandidate k) (itOf d) (declSlotData d .uninit)] } }) := by
    rw [declSlotData_uninit hdSc]
    simp only [CM.allocate, halloc, ok_bind, pure_ok]
    rfl
  refine ⟨⟨lm.entries ++ [(localName i, newPtr)]⟩,
    { cm with memory := { cm.memory with
      allocations := cm.memory.allocations ++
        [stackAlloc (allocCandidate k) (itOf d) (declSlotData d .uninit)] } }, ?_, ?_⟩
  · simp only [storageLive, hsd, ok_bind]
    rw [hmi, ok_bind, hlt.layout, ok_bind, expect_size_sized, ok_bind, expect_align_sized, ok_bind]
    dsimp only [calleeFrameL]
    rw [hca, ok_bind, hins]
    rfl
  · exact hlo.alloc_scalar i d hd hsc hsi hp (allocCandidate k) haddr hmax
      (.inr ⟨by omega, k, rfl⟩)

/-- Allocating argument locals `start .. start + k - 1` via `allocFrameArgs`. -/
private theorem allocFrameArgs_from {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {locals : List LocalSlot} {lm : Map Gen.LocalName Ptr} {cm : Gen.ConcurrentMemory BM}
    {blk stmt bound : Nat} (hf : FnLocalsSpec body f)
    (hdecls : ∀ (i : Nat) d, body.localDecls[i]? = some d → scalarTypeOf d.ty = some (tyOf d))
    (hbase : BaseCandBounded ctx.base bound) (hn : bound + body.localDecls.length < 2 ^ 31)
    (start k : Nat) (hbound : start + k ≤ body.localDecls.length)
    (hdead : ∀ j, start ≤ j → j < start + k → locals[j]? = some .dead)
    (hlo : LocalsOkA body ctx [] locals lm cm.memory.allocations) :
    ∃ locals' lm' cm',
      allocFrameArgs (calleeFrameL f ctx lm blk stmt) cm
        ((List.range k).map (fun r => localName (start + r))) =
        .ok (calleeFrameL f ctx lm' blk stmt, cm') ∧
      locals'.length = locals.length ∧
      (∀ j, (j < start ∨ start + k ≤ j) → locals'[j]? = locals[j]?) ∧
      (∀ j, start ≤ j → j < start + k → locals'[j]? = some .uninit) ∧
      LocalsOkA body ctx [] locals' lm' cm'.memory.allocations := by
  induction k generalizing start locals lm cm with
  | zero =>
    refine ⟨locals, lm, cm, by simp [allocFrameArgs], rfl, fun _ _ => rfl,
      fun _ h1 h2 => by omega, hlo⟩
  | succ k ih =>
    have hlt : start < body.localDecls.length := by omega
    obtain ⟨d, hd⟩ : ∃ d, body.localDecls[start]? = some d := ⟨_, List.getElem?_eq_getElem hlt⟩
    have hs0 : locals[start]? = some .dead := hdead start (Nat.le_refl _) (by omega)
    obtain ⟨lm1, cm1, hsl1, hlo1⟩ :=
      storageLive_fresh_cand (blk := blk) (stmt := stmt) hf hdecls hlo start d hd hs0 hbase hn
    have hfn : (fun r => localName (start + (r + 1))) = (fun r => localName (start + 1 + r)) :=
      funext fun r => congrArg localName (by omega)
    have hrange : (List.range (k + 1)).map (fun r => localName (start + r)) =
        localName start :: (List.range k).map (fun r => localName (start + 1 + r)) := by
      rw [List.range_succ_eq_map, List.map_cons, List.map_map, Nat.add_zero]
      exact congrArg (localName start :: List.map · (List.range k)) hfn
    obtain ⟨locals2, lm2, cm2, halRest, hlen2, hout2, hin2, hlo2⟩ :=
      ih (start + 1) (by omega)
        (fun j hj1 hj2 => by
          rw [List.getElem?_set_ne (by omega)]
          exact hdead j (by omega) (by omega))
        hlo1
    refine ⟨locals2, lm2, cm2, ?_, by simpa using hlen2, fun j hj => ?_, fun j hj1 hj2 => ?_, hlo2⟩
    · rw [hrange]; simp [allocFrameArgs, hsl1, halRest]
    · rw [hout2 j (by omega), List.getElem?_set_ne (by omega)]
    · by_cases hjs : j = start
      · subst j
        rw [hout2 start (by omega), List.getElem?_set_self (by rw [hlo.nlocals]; exact hlt)]
      · exact hin2 j (by omega) (by omega)

/-- Storing passed argument values into `_start .. _(start + vs.length - 1)` via
`initFrameArgs`. -/
private theorem initFrameArgs_from {body : CapturedMir} {f : Gen.Function} {ctx rootCtx : Ctx}
    {frames : List Frame} {locals : List LocalSlot} {lm : Map Gen.LocalName Ptr} {m : Mach}
    {blk stmt : Nat} (hf : FnLocalsSpec body f)
    (hdecls : ∀ (i : Nat) d, body.localDecls[i]? = some d → scalarTypeOf d.ty = some (tyOf d))
    (hsh : Shape m rootCtx frames m.mem.memory.allocations)
    (start : Nat) (pds : List LocalDecl) (vs : List Value)
    (hlenPv : vs.length = pds.length)
    (hpds : ∀ (r : Nat) pd, pds[r]? = some pd → body.localDecls[start + r]? = some pd)
    (hslots : ∀ (r : Nat) pd v, pds[r]? = some pd → vs[r]? = some v → SlotOk (tyOf pd) (.init v))
    (huninit : ∀ j, start ≤ j → j < start + vs.length → locals[j]? = some .uninit)
    (hlo : LocalsOkA body ctx [] locals lm m.mem.memory.allocations) :
    ∃ locals' m',
      initFrameArgs m (calleeFrameL f ctx lm blk stmt)
        ((List.range vs.length).map (fun r => localName (start + r)))
        ((pds.zip vs).map (fun (pd, v) => (valOfValue (tyOf pd) v, tyOf pd))) = .ok m' ∧
      Shape m' rootCtx frames m'.mem.memory.allocations ∧
      m'.prog = m.prog ∧ m'.fn_ptrs = m.fn_ptrs ∧
      locals'.length = locals.length ∧
      (∀ j, (j < start ∨ start + vs.length ≤ j) → locals'[j]? = locals[j]?) ∧
      (∀ (r : Nat) v, vs[r]? = some v → locals'[start + r]? = some (.init v)) ∧
      LocalsOkA body ctx [] locals' lm m'.mem.memory.allocations := by
  induction vs generalizing start pds locals m with
  | nil =>
    cases pds with
    | cons _ _ => simp at hlenPv
    | nil =>
      refine ⟨locals, m, by simp [initFrameArgs], hsh, rfl, rfl, rfl, fun _ _ => rfl,
        fun _ _ hv => by simp at hv, hlo⟩
  | cons v vs ih =>
    cases pds with
    | nil => simp at hlenPv
    | cons pd pds =>
      have hpd0 : body.localDecls[start]? = some pd := by simpa using hpds 0 pd rfl
      have hdSc := hdecls start pd hpd0
      have hsc : (scalarTypeOf pd.ty).isSome = true := by simp [hdSc]
      have hloc : mapGet f.locals (localName start) = some (tyOf pd) := by
        rw [(hf.2 start pd hpd0).2, tyOf_scalar_layouts hsc body.layouts ⟨64, true, []⟩]
      have hlt := localTy_of_decl hdSc
      have hvOk : SlotOk (tyOf pd) (.init v) := hslots 0 pd v rfl rfl
      have hs0 : locals[start]? = some .uninit := huninit start (Nat.le_refl _) (by simp)
      obtain ⟨p, hp⟩ := hlo.some_of_live hs0 (by simp)
      obtain ⟨id, hpid, _, haddr, _, hA⟩ := hlo.storage_scalar hpd0 hsc hs0 hp
      have hal : Align.is_aligned ⟨(itOf pd).size.bytes⟩ p.addr = true := by
        simp [Align.is_aligned, haddr.1]
      have hlenData := declSlotData_length hdSc .uninit
      obtain ⟨acc, hst⟩ :=
        typedStore_ptr_localTy hsh p id hpid pd hdSc _ hA hlenData v hvOk ⟨(itOf pd).size.bytes⟩ hal
      let m1 := withMem m
        (m.mem.memory.allocations.set id (stackAlloc p.addr (itOf pd) (declSlotData pd (.init v)))) acc
      have hlo1 := hlo.store_scalar start pd hpd0 hsc .uninit (.init v) hs0 (by simp) hvOk p hp id hpid
      have hsh1 : Shape m1 rootCtx frames m1.mem.memory.allocations := withMem_shape hsh _
      have hmiTy : mapIndex (calleeFrameL f ctx lm blk stmt).func.locals (localName start)
          "func.locals[callee_local]" = .ok (tyOf pd) := by
        simp [mapIndex, calleeFrameL, hloc]
      have hmiPtr : mapIndex (calleeFrameL f ctx lm blk stmt).locals (localName start)
          "frame.locals[callee_local]" = .ok p := by
        simp [mapIndex, calleeFrameL, hp]
      have habi := checkAbiCompatibility_refl_localTy hlt
      have hfn : (fun r => localName (start + (r + 1))) = (fun r => localName (start + 1 + r)) :=
        funext fun r => congrArg localName (by omega)
      have hrange : (List.range (vs.length + 1)).map (fun r => localName (start + r)) =
          localName start :: (List.range vs.length).map (fun r => localName (start + 1 + r)) := by
        rw [List.range_succ_eq_map, List.map_cons, List.map_map, Nat.add_zero]
        exact congrArg (localName start :: List.map · (List.range vs.length)) hfn
      obtain ⟨locals2, m2, hinitRest, hsh2, hp2, hfp2, hlen2, hout2, hin2, hlo2⟩ :=
        ih hsh1 (start + 1) pds (by simp at hlenPv; exact hlenPv)
          (fun r pd' hpd' => by
            have := hpds (r + 1) pd' (by simpa using hpd')
            simpa [Nat.add_right_comm, Nat.add_assoc] using this)
          (fun r pd' v' hpd' hv' => hslots (r + 1) pd' v' (by simpa using hpd') (by simpa using hv'))
          (fun j hj1 hj2 => by
            rw [List.getElem?_set_ne (by omega)]
            exact huninit j (by omega) (by simp; omega))
          hlo1
      refine ⟨locals2, m2, ?_, hsh2, hp2, hfp2, by simpa using hlen2,
        fun j hj => ?_, fun r v' hv' => ?_, hlo2⟩
      · simp only [List.length_cons]
        rw [hrange]
        simp only [List.zip_cons_cons, List.map_cons, initFrameArgs, hmiTy, ok_bind, habi,
          Bool.not_true, Bool.false_eq_true, ↓reduceIte, hlt.layout, expect_align_sized,
          hmiPtr, hst]
        exact hinitRest
      · rw [hout2 j (by simp at hj; omega), List.getElem?_set_ne (by simp at hj; omega)]
      · cases r with
        | zero =>
          simp at hv'; subst hv'
          have hltLoc : start < locals.length :=
            by rw [hlo.nlocals]; exact (List.getElem?_eq_some_iff.mp hpd0).1
          rw [Nat.add_zero, hout2 start (by omega), List.getElem?_set_self hltLoc]
        | succ r =>
          simp at hv'
          simpa [Nat.add_assoc, Nat.add_comm 1 r] using hin2 r v' hv'

theorem initLocalsAux_getElem? (idx : Nat) (decls : List LocalDecl) (args : List Value) :
    (MirSemantics.initLocalsAux idx decls args).length = decls.length ∧
    ∀ k, k < decls.length →
      (MirSemantics.initLocalsAux idx decls args)[k]? =
        if idx = 0 ∧ k = 0 then some .uninit
        else if k < (if idx = 0 then args.length + 1 else args.length) then
          some (.init (args[if idx = 0 then k - 1 else k]?.getD (.scalar ⟨0, 0⟩)))
        else some .dead := by
  induction decls generalizing idx args with
  | nil => simp [MirSemantics.initLocalsAux]
  | cons d ds ih =>
    cases idx with
    | zero =>
      obtain ⟨hlen, hget⟩ := ih 1 args
      refine ⟨by simp [MirSemantics.initLocalsAux, hlen], fun k hk => ?_⟩
      cases k with
      | zero => simp [MirSemantics.initLocalsAux]
      | succ k =>
        simp only [MirSemantics.initLocalsAux, List.getElem?_cons_succ]
        rw [hget k (by simp at hk; omega)]
        simp
    | succ n =>
      cases args with
      | nil =>
        obtain ⟨hlen, hget⟩ := ih (n + 1) []
        refine ⟨by simp [MirSemantics.initLocalsAux, Nat.add_eq, hlen], fun k hk => ?_⟩
        cases k with
        | zero => simp [MirSemantics.initLocalsAux]
        | succ k =>
          simp only [MirSemantics.initLocalsAux, Nat.add_eq, List.getElem?_cons_succ]
          rw [hget k (by simp at hk; omega)]
          simp
      | cons a rest =>
        obtain ⟨hlen, hget⟩ := ih (n + 1) rest
        refine ⟨by simp [MirSemantics.initLocalsAux, Nat.add_eq, hlen], fun k hk => ?_⟩
        cases k with
        | zero => simp [MirSemantics.initLocalsAux]
        | succ k =>
          simp only [MirSemantics.initLocalsAux, Nat.add_eq, List.getElem?_cons_succ]
          rw [hget k (by simp at hk; omega)]
          simp [Nat.succ_lt_succ_iff]

/-- Exact characterization of Anneal's `MirSemantics.initLocals calleeBody vs`
when `vs.length + 1 ≤ calleeBody.localDecls.length`. -/
theorem initLocals_eq_of_slots {calleeBody : CapturedMir} {vs : List Value} {slots : List LocalSlot}
    (hlen : slots.length = calleeBody.localDecls.length)
    (h0 : slots[0]? = some .uninit)
    (harg : ∀ (r : Nat) v, vs[r]? = some v → slots[1 + r]? = some (.init v))
    (hdead : ∀ j, 1 + vs.length ≤ j → j < calleeBody.localDecls.length → slots[j]? = some .dead) :
    slots = MirSemantics.initLocals calleeBody vs := by
  obtain ⟨hILlen, hILget⟩ := initLocalsAux_getElem? 0 calleeBody.localDecls vs
  apply List.ext_getElem?
  intro k
  by_cases hk : k < calleeBody.localDecls.length
  · rw [MirSemantics.initLocals, hILget k hk]
    by_cases hk0 : k = 0
    · subst hk0; simpa using h0
    · simp only [true_and, hk0, ↓reduceIte]
      by_cases hkArg : k < vs.length + 1
      · have hrlt : k - 1 < vs.length := by omega
        obtain ⟨v, hv⟩ : ∃ v, vs[k - 1]? = some v := ⟨_, List.getElem?_eq_getElem hrlt⟩
        have hk1 : 1 + (k - 1) = k := by omega
        have hs := harg (k - 1) v hv
        rw [hk1] at hs
        simp [hkArg, hv, hs]
      · simp [hkArg, hdead k (by omega) hk]
  · rw [List.getElem?_eq_none (by omega),
      List.getElem?_eq_none (by rw [MirSemantics.initLocals, hILlen]; omega)]

/-- `createFrame` + `mutateCurStack` (`evalCall`) allocates `_0` and `_1 .. _argCount`,
passes ABI checks, writes `argVals`, and pushes the callee frame at `calleeFn.start`
satisfying `LocalsOkA calleeBody calleeCtx [] (initLocals calleeBody argVals)`. -/
theorem evalCall_spec {calleeBody : CapturedMir} {calleeFn : Gen.Function}
    {rootCtx : Ctx} {callerStack : List Frame} {callerTop : Frame}
    {m : Mach} {retPlace : Gen.Place BM} {targetBb unwindBb : Gen.BbName}
    {bound : Nat} {calleeRetDecl : LocalDecl} {paramDecls : List LocalDecl} {argVals : List Value}
    (hsh : Shape m rootCtx (callerStack ++ [callerTop]) m.mem.memory.allocations)
    (hCalleeTr : translateFnInProg (fnMap := []) calleeBody = some calleeFn ∨
      (FnLocalsSpec calleeBody calleeFn ∧
        calleeFn.args = (List.range calleeBody.argCount).map (fun k => localName (k + 1)) ∧
        calleeFn.start = bbName calleeBody.basicBlocks.length))
    (hd0 : calleeBody.localDecls[0]? = some calleeRetDecl)
    (hcalleeScalar : calleeBody.localDecls.all (fun d => (scalarTypeOf d.ty).isSome) = true)
    (hargc : calleeBody.argCount + 1 ≤ calleeBody.localDecls.length)
    (hpds : paramDecls = (calleeBody.localDecls.drop 1).take calleeBody.argCount)
    (hlenArgs : argVals.length = calleeBody.argCount)
    (hslots : ∀ (r : Nat) pd v, paramDecls[r]? = some pd → argVals[r]? = some v →
      SlotOk (tyOf pd) (.init v))
    (hbase : BaseCandBounded m.mem.memory.allocations bound)
    (hn : bound + calleeBody.localDecls.length < 2 ^ 31) :
    let calleeCtx : Ctx := {
      caller := callerTop
      payloads := rootCtx.payloads
      base := m.mem.memory.allocations
      addrs := []
      nextBlock := targetBb
      unwindBlock := some unwindBb
      retPtr := retPlace.ptr.thin_pointer
    }
    ∃ calleeLm m',
      evalCall m calleeFn calleeFn.calling_convention
        ((paramDecls.zip argVals).map (fun (pd, v) => (valOfValue (tyOf pd) v, tyOf pd)))
        (retPlace, tyOf calleeRetDecl) (some targetBb) (some unwindBb) = .ok m' ∧
      Shape m' rootCtx
        ((callerStack ++ [callerTop]) ++
          [calleeFrameL calleeFn calleeCtx calleeLm calleeBody.basicBlocks.length 0])
        m'.mem.memory.allocations ∧
      m'.prog = m.prog ∧ m'.fn_ptrs = m.fn_ptrs ∧
      LocalsOkA calleeBody calleeCtx [] (MirSemantics.initLocals calleeBody argVals)
        calleeLm m'.mem.memory.allocations := by
  have ⟨hf, hargsEq, hstartEq⟩ :
      FnLocalsSpec calleeBody calleeFn ∧
      calleeFn.args = (List.range calleeBody.argCount).map (fun k => localName (k + 1)) ∧
      calleeFn.start = bbName calleeBody.basicBlocks.length := by
    rcases hCalleeTr with htr | hpack
    · obtain ⟨h1, _, h3, h4, _, _⟩ := translateFnInProg_spec [] calleeBody calleeFn htr
      exact ⟨h1, h3, h4⟩
    · exact hpack
  have hdecls : ∀ (i : Nat) d, calleeBody.localDecls[i]? = some d →
      scalarTypeOf d.ty = some (tyOf d) := fun i d hd =>
    scalarTypeOf_tyOf_of_isSome (List.all_eq_true.mp hcalleeScalar d (List.mem_of_getElem? hd)) _
  have hsc0 : (scalarTypeOf calleeRetDecl.ty).isSome = true := by simp [hdecls 0 calleeRetDecl hd0]
  intro calleeCtx
  let blkStart := calleeBody.basicBlocks.length
  let slots0 := List.replicate calleeBody.localDecls.length LocalSlot.dead
  have hlo0 : LocalsOkA calleeBody calleeCtx [] slots0 ⟨[]⟩ m.mem.memory.allocations :=
    LocalsOkA.empty calleeBody calleeCtx
  have hs0 : slots0[0]? = some .dead := by
    simp [slots0, show 0 < calleeBody.localDecls.length by omega]
  obtain ⟨lm1, cm1, hslRet, hlo1⟩ :=
    storageLive_fresh_cand (blk := blkStart) (stmt := 0) hf hdecls hlo0 0 calleeRetDecl hd0 hs0
      hbase hn
  have hargsEq1 : calleeFn.args = (List.range calleeBody.argCount).map (fun r => localName (1 + r)) := by
    rw [hargsEq]; congr 1; funext r; congr 1; omega
  obtain ⟨slots2, lm2, cm2, halArgs, hlen2, hout2, hin2, hlo2⟩ :=
    allocFrameArgs_from (blk := blkStart) (stmt := 0) hf hdecls hbase hn 1 calleeBody.argCount
      (by omega)
      (fun j hj1 hj2 => by
        rw [List.getElem?_set_ne (by omega)]
        simp [slots0, show j < calleeBody.localDecls.length by omega])
      hlo1
  let mAlloc : Mach := { m with mem := cm2 }
  have hshAlloc : Shape mAlloc rootCtx (callerStack ++ [callerTop]) mAlloc.mem.memory.allocations :=
    ⟨hsh.threads, hsh.active, rfl⟩
  have hpdsLen : paramDecls.length = calleeBody.argCount := by
    rw [hpds]; simp; omega
  have hpdsGet : ∀ (r : Nat) pd, paramDecls[r]? = some pd → calleeBody.localDecls[1 + r]? = some pd := by
    intro r pd hpd
    rw [hpds] at hpd
    have hrlt : r < calleeBody.argCount := by
      have := (List.getElem?_eq_some_iff.mp hpd).1; simp at this; omega
    rw [List.getElem?_take_of_lt hrlt, List.getElem?_drop] at hpd
    exact hpd
  obtain ⟨slots3, mInit, hinitArgs, hshInit, hpInit, hfpInit, hlen3, hout3, hin3, hlo3⟩ :=
    initFrameArgs_from (blk := blkStart) (stmt := 0) hf hdecls hshAlloc 1 paramDecls argVals
      (hlenArgs.trans hpdsLen.symm) hpdsGet hslots
      (fun j hj1 hj2 => hin2 j hj1 (by rw [← hlenArgs]; exact hj2)) hlo2
  have hslots3Eq : slots3 = MirSemantics.initLocals calleeBody argVals := by
    apply initLocals_eq_of_slots
    · rw [hlen3, hlen2]; simp [slots0]
    · rw [hout3 0 (by omega), hout2 0 (by omega),
        List.getElem?_set_self (by simp [slots0]; omega)]
    · exact hin3
    · intro j hj1 hj2
      rw [hout3 j (by omega), hout2 j (by rw [← hlenArgs]; omega), List.getElem?_set_ne (by omega)]
      simp [slots0, hj2]
  rw [hslots3Eq] at hlo3
  have hfr0Eq : ({
      func := calleeFn
      locals := ⟨[]⟩
      stack_pop_action := .BackToCaller (some targetBb) (some unwindBb) retPlace.ptr.thin_pointer
      next_block := calleeFn.start
      next_stmt := 0
      extra := () } : Frame) = calleeFrameL calleeFn calleeCtx ⟨[]⟩ blkStart 0 := by
    simp [calleeFrameL, calleeCtx, blkStart, hstartEq]
  have hloc0 : mapGet calleeFn.locals (localName 0) = some (tyOf calleeRetDecl) := by
    rw [(hf.2 0 calleeRetDecl hd0).2, tyOf_scalar_layouts hsc0 calleeBody.layouts ⟨64, true, []⟩]
  have hretMi : mapIndex (calleeFrameL calleeFn calleeCtx lm2 blkStart 0).func.locals
      (calleeFrameL calleeFn calleeCtx lm2 blkStart 0).func.ret "func.locals[func.ret]" =
      .ok (tyOf calleeRetDecl) := by
    simp [mapIndex, calleeFrameL, hf.1, hloc0]
  have habiRet := checkAbiCompatibility_refl_localTy (localTy_of_decl (hdecls 0 calleeRetDecl hd0))
  have hcallerArgsLen :
      ((paramDecls.zip argVals).map (fun (pd, v) => (valOfValue (tyOf pd) v, tyOf pd))).length =
      calleeFn.args.length := by
    simp [hargsEq, hpdsLen, hlenArgs]
  have hcf : createFrame m calleeFn
      (.BackToCaller (some targetBb) (some unwindBb) retPlace.ptr.thin_pointer)
      calleeFn.calling_convention (tyOf calleeRetDecl)
      ((paramDecls.zip argVals).map (fun (pd, v) => (valOfValue (tyOf pd) v, tyOf pd))) =
      .ok (calleeFrameL calleeFn calleeCtx lm2 blkStart 0, mInit) := by
    unfold createFrame
    rw [hfr0Eq]
    dsimp only
    rw [hf.1, hslRet]
    simp only [ok_bind]
    rw [hargsEq1, halArgs]
    simp only [ok_bind]
    simp only [ne_eq, not_true_eq_false, ↓reduceIte]
    rw [hretMi, ok_bind, habiRet, ok_bind]
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    have hneArgs : (((List.range calleeBody.argCount).map (fun r => localName (1 + r))).length ≠
        ((paramDecls.zip argVals).map (fun (pd, v) => (valOfValue (tyOf pd) v, tyOf pd))).length) =
        False := by
      simp [hpdsLen, hlenArgs]
    simp only [hneArgs, ↓reduceIte]
    rw [← hlenArgs]
    dsimp only [mAlloc] at hinitArgs
    rw [hinitArgs, ok_bind]
    rfl
  have hpush := mutateCurStack_append hshInit (calleeFrameL calleeFn calleeCtx lm2 blkStart 0)
  refine ⟨lm2, rethread mInit rootCtx
    ((callerStack ++ [callerTop]) ++ [calleeFrameL calleeFn calleeCtx lm2 blkStart 0]), ?_,
    ⟨rfl, hshInit.active, hshInit.allocs⟩, hpInit.trans rfl, hfpInit.trans rfl, hlo3⟩
  unfold evalCall
  dsimp only
  rw [hcf, ok_bind, hpush, ok_bind]
  rfl

/-- `ConcurrentMemory::store` of a non-empty subslice `bytes` at byte offset `off`
within a live allocation `a` at an aligned pointer `p`. -/
theorem CM_store_subslice_align {cm : Gen.ConcurrentMemory BM} {p : Ptr} {id : Nat}
    (hp : p.provenance = some (⟨(id : Int)⟩, ())) {a : Gen.Allocation}
    (hA : cm.memory.allocations[id]? = some a) (hlive : a.live = true)
    (off : Nat) (haddr : p.addr = a.addr + (off : Int))
    (bytes : List Byte) (hne : bytes ≠ []) (hbound : off + bytes.length ≤ a.data.length)
    (align : Align) (hal : Align.is_aligned align p.addr = true) :
    CM.store cm p bytes align .None =
      .ok { memory := { cm.memory with
              allocations := cm.memory.allocations.set id
                ({ a with data := a.data.take off ++ bytes ++ a.data.drop (off + bytes.length) }) },
            accesses := cm.accesses ++ [⟨.Store, .None, p.addr, ⟨bytes.length⟩⟩] } := by
  obtain ⟨hid, hAid⟩ := List.getElem?_eq_some_iff.mp hA
  have hsubAux : ∀ x : Int, x + (off : Int) - x = (off : Int) := fun x => by omega
  have hsub : a.addr + (off : Int) - a.addr = (off : Int) := hsubAux a.addr
  have hnonneg : ¬ ((off : Int) < 0) := by omega
  have hboundsI : ¬ ((a.data.length : Int) < (off : Int) + (bytes.length : Int)) := by omega
  have hleI : (off : Int) + (bytes.length : Int) ≤ (a.data.length : Int) := by omega
  have hlenPos : bytes.length ≠ 0 := fun h => hne (List.eq_nil_of_length_eq_zero h)
  simp only [CM.store, BM.store, hal, BM.check_ptr, hp, listIndex]
  simp [hlenPos, hid, hAid, hlive, haddr, Allocation.size, hsub, hnonneg, hboundsI,
    hleI, Int.toNat_natCast, writeSubsliceAtIndex, listSet, List.append_assoc]

/-- `typed_store` into field `0` of a suspended caller's `(it, bool)` tuple local
after `prepareForInplacePassing_ptr_field0` restores `tupleBytes it bitsNew b`. -/
theorem typedStore_ptr_tuple_field0_after_prep {m : Mach} {ctx : Ctx} {frames : List Frame}
    {A : List Gen.Allocation} (h : Shape m ctx frames A) {p : Ptr} {id : Nat}
    (hp : p.provenance = some (⟨(id : Int)⟩, ())) {it : Gen.IntType}
    (hgood : GoodSize it.size.bytes) (bitsNew b : Nat)
    (hbits : bitsNew < 2 ^ (8 * it.size.bytes))
    (hA : A[id]? = some (stackAlloc p.addr it
      (uninitBytes it ++ scalarBytes u8Ty b ++ List.replicate (it.size.bytes - 1) .Uninit)))
    (haddr : AddrOk p.addr it) :
    typedStore m p (.Int (intFromBits bitsNew it)) (.Int it) ⟨it.size.bytes⟩ .None =
      .ok (withMem m (A.set id (stackAlloc p.addr it (tupleBytes it bitsNew b)))
        ⟨.Store, .None, p.addr, it.size⟩) := by
  have hpos := hgood.pos
  have hu8 : u8Ty.size.bytes = 1 := rfl
  have hal : Align.is_aligned ⟨it.size.bytes⟩ p.addr = true := by
    simp [Align.is_aligned, haddr.1]
  have hrep := canRepresent_intFromBits it bitsNew hgood hbits
  have hck := checkValue_int (m? := some m) hrep
  have henc := encode_int it (intFromBits bitsNew it) hgood hrep
  have hmod : (intFromBits bitsNew it % 2 ^ (8 * it.size.bytes)).toNat = bitsNew := by
    rw [intFromBits_emod bitsNew _ hbits]; simp
  rw [hmod] at henc
  have hblen := scalarBytes_length it bitsNew
  have hne : scalarBytes it bitsNew ≠ [] := List.ne_nil_of_length_pos (by omega)
  have hAmem : m.mem.memory.allocations[id]? = some (stackAlloc p.addr it
      (uninitBytes it ++ scalarBytes u8Ty b ++ List.replicate (it.size.bytes - 1) .Uninit)) := by
    rw [h.allocs]; exact hA
  have hbound : 0 + (scalarBytes it bitsNew).length ≤
      (uninitBytes it ++ scalarBytes u8Ty b ++
        List.replicate (it.size.bytes - 1) Gen.AbstractByte.Uninit).length := by
    simp only [List.length_append, uninitBytes, List.length_replicate, scalarBytes_length, hu8]
    omega
  have hst := CM_store_subslice_align hp hAmem rfl 0 (by simp [stackAlloc])
    (scalarBytes it bitsNew) hne hbound ⟨it.size.bytes⟩ hal
  have hdrop :
      (uninitBytes it ++ scalarBytes u8Ty b ++
        List.replicate (it.size.bytes - 1) Gen.AbstractByte.Uninit).drop it.size.bytes =
      scalarBytes u8Ty b ++ List.replicate (it.size.bytes - 1) .Uninit := by
    have hlenU : (uninitBytes it).length = it.size.bytes := by simp [uninitBytes]
    rw [List.append_assoc, List.drop_append_of_le_length (by omega),
      List.drop_eq_nil_of_le (by omega), List.nil_append]
  unfold typedStore
  rw [hck]
  dsimp only
  rw [henc, ok_bind, hst, ok_bind]
  dsimp only [stackAlloc, withMem]
  rw [List.take_zero, List.nil_append, Nat.zero_add, hblen, hdrop, h.allocs]
  simp [tupleBytes, List.append_assoc]

/-- `typed_store` into field `1` of a suspended caller's `(it, bool)` tuple local
after `prepareForInplacePassing_ptr_field1` restores `tupleBytes it bits bNew`. -/
theorem typedStore_ptr_tuple_field1_after_prep {m : Mach} {ctx : Ctx} {frames : List Frame}
    {A : List Gen.Allocation} (h : Shape m ctx frames A) {p : Ptr} {id : Nat}
    (hp : p.provenance = some (⟨(id : Int)⟩, ())) {it : Gen.IntType}
    (hgood : GoodSize it.size.bytes) (bits bNew : Nat) (hb : bNew < 2)
    (hA : A[id]? = some (stackAlloc p.addr it
      (scalarBytes it bits ++ [.Uninit] ++ List.replicate (it.size.bytes - 1) .Uninit))) :
    typedStore m (field1Ptr p it) (.Bool (decide (bNew = 1))) .Bool ⟨u8Ty.size.bytes⟩ .None =
      .ok (withMem m (A.set id (stackAlloc p.addr it (tupleBytes it bits bNew)))
        ⟨.Store, .None, (field1Ptr p it).addr, u8Ty.size⟩) := by
  have hpos := hgood.pos
  have hu8 : u8Ty.size.bytes = 1 := rfl
  have hck : checkValue (.Bool (decide (bNew = 1))) .Bool (some m) = .ok () := rfl
  have henc := encode_bool (decide (bNew = 1))
  have hbEq : (if decide (bNew = 1) = true then 1 else 0) = bNew := by
    rcases (by omega : bNew = 0 ∨ bNew = 1) with rfl | rfl <;> rfl
  rw [hbEq] at henc
  have hblen : (scalarBytes u8Ty bNew).length = 1 := scalarBytes_length u8Ty bNew
  have hne : scalarBytes u8Ty bNew ≠ [] := List.ne_nil_of_length_pos (by omega)
  have hAmem : m.mem.memory.allocations[id]? = some (stackAlloc p.addr it
      (scalarBytes it bits ++ [.Uninit] ++ List.replicate (it.size.bytes - 1) .Uninit)) := by
    rw [h.allocs]; exact hA
  have hbound : it.size.bytes + (scalarBytes u8Ty bNew).length ≤
      (scalarBytes it bits ++ [Gen.AbstractByte.Uninit] ++
        List.replicate (it.size.bytes - 1) Gen.AbstractByte.Uninit).length := by
    simp only [List.length_append, scalarBytes_length, List.length_singleton,
      List.length_replicate, hu8]
    omega
  have hal : Align.is_aligned ⟨u8Ty.size.bytes⟩ (field1Ptr p it).addr = true := by
    rw [hu8]; exact isAligned_one _
  have hst := CM_store_subslice_align (p := field1Ptr p it) (by simpa [field1Ptr] using hp)
    hAmem rfl it.size.bytes (by simp [field1Ptr, stackAlloc])
    (scalarBytes u8Ty bNew) hne hbound ⟨u8Ty.size.bytes⟩ hal
  have htk :
      (scalarBytes it bits ++ [Gen.AbstractByte.Uninit] ++
        List.replicate (it.size.bytes - 1) Gen.AbstractByte.Uninit).take it.size.bytes =
      scalarBytes it bits := by
    have hlen0 := scalarBytes_length it bits
    rw [List.append_assoc, List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
  have hdr :
      (scalarBytes it bits ++ [Gen.AbstractByte.Uninit] ++
        List.replicate (it.size.bytes - 1) Gen.AbstractByte.Uninit).drop (it.size.bytes + 1) =
      List.replicate (it.size.bytes - 1) .Uninit := by
    have hlen0 := scalarBytes_length it bits
    rw [List.append_assoc, List.drop_append, hlen0, List.drop_eq_nil_of_le (by omega),
      List.nil_append, show it.size.bytes + 1 - it.size.bytes = 1 by omega,
      List.drop_append, List.length_singleton, List.drop_eq_nil_of_le (by simp),
      List.nil_append, List.drop_zero]
  unfold typedStore
  rw [hck]
  dsimp only
  rw [henc, ok_bind, hst, ok_bind]
  dsimp only [stackAlloc, withMem]
  rw [hblen, htk, hdr, h.allocs]
  simp [tupleBytes, u8Ty, List.append_assoc]

private theorem not_slotOk_aggregate {T : Gen.Type} (hT : tupleIntOfTy T = none) :
    ∀ v fs, ¬ SlotOk T (.init (.aggregate v fs))
  | 0, [.scalar _, .scalar _], ⟨_, ht, _⟩ => by rw [hT] at ht; cases ht
  | _ + 1, _, h => by simp [SlotOk] at h
  | 0, [], h => by simp [SlotOk] at h
  | 0, [_], h => by simp [SlotOk] at h
  | 0, _ :: _ :: _ :: _, h => by simp [SlotOk] at h
  | 0, [.unit, _], h | 0, [.ptr _ _, _], h | 0, [.aggregate _ _, _], h => by simp [SlotOk] at h
  | 0, [.scalar _, .unit], h | 0, [.scalar _, .ptr _ _], h
  | 0, [.scalar _, .aggregate _ _], h => by simp [SlotOk] at h

/-- `evalReturn` on a non-root callee frame (`StackPopAction::BackToCaller`)
under `CallerDestRel`: either `_0` is uninitialized and `evalReturn` raises UB,
or `_0` holds `retVal`, all callee allocations are killed, `retVal` is written
to the caller's `destination` restoring `LocalsOk` on the caller frame, and the
caller jumps to `returnTarget`. -/
theorem evalReturn_caller_spec {callerBody calleeBody : CapturedMir}
    {callerFn calleeFn : Gen.Function} {rootCtx callerCtx calleeCtx : Ctx}
    {preFrames : List Frame} {callerActual callerView calleeView : List LocalSlot}
    {callerLm calleeLm : Map Gen.LocalName Ptr}
    {callerBlk callerStmt calleeBlk calleeStmt returnTarget : Nat}
    {calleeRetDecl : LocalDecl} {destination : Place} {m : Mach}
    (hfCallee : FnLocalsSpec calleeBody calleeFn)
    (hsh : Shape m rootCtx
      ((preFrames ++ [calleeCtx.caller]) ++
        [calleeFrameL calleeFn calleeCtx calleeLm calleeBlk calleeStmt])
      m.mem.memory.allocations)
    (hCallerFr : calleeCtx.caller =
      calleeFrameL callerFn callerCtx callerLm callerBlk callerStmt)
    (hNextBlk : calleeCtx.nextBlock = bbName returnTarget)
    (hd0 : calleeBody.localDecls[0]? = some calleeRetDecl)
    (hcalleeScalar : calleeBody.localDecls.all (fun d => (scalarTypeOf d.ty).isSome) = true)
    (hloCallee : LocalsOk calleeBody calleeCtx calleeView calleeLm m.mem.memory.allocations)
    (hRetLive : calleeView[0]? ≠ some .dead)
    (hDest : CallerDestRel callerBody callerCtx callerActual callerView callerLm
      calleeRetDecl calleeCtx.base calleeCtx.retPtr destination) :
    (∀ retVal, calleeView[0]? = some (.init retVal) →
      ∃ callerView' m',
        evalReturn m = .ok m' ∧
        Shape m' rootCtx
          (preFrames ++ [calleeFrameL callerFn callerCtx callerLm returnTarget 0])
          m'.mem.memory.allocations ∧
        m'.prog = m.prog ∧ m'.fn_ptrs = m.fn_ptrs ∧
        callerView'.length = callerView.length ∧
        (writeCallDest callerActual destination retVal)[destination.local_]? =
          callerView'[destination.local_]? ∧
        (callerView'[destination.local_]? ≠ some .dead) ∧
        (∀ j, j ≠ destination.local_ → callerView'[j]? = callerView[j]?) ∧
        (∀ j, j ≠ destination.local_ →
          (writeCallDest callerActual destination retVal)[j]? = callerActual[j]?) ∧
        LocalsOk callerBody callerCtx callerView' callerLm m'.mem.memory.allocations) ∧
    (calleeView[0]? = some .uninit → ∃ msg, evalReturn m = .error (.ub msg)) := by
  let fr := calleeFrameL calleeFn calleeCtx calleeLm calleeBlk calleeStmt
  let callerStack := preFrames ++ [calleeCtx.caller]
  have hthr0 : m.threads = [thread1 rootCtx (callerStack ++ [fr])] := hsh.threads
  have hact0 : activeThread m = .ok (thread1 rootCtx (callerStack ++ [fr])) := by
    simp [activeThread, listIndex, hthr0, hsh.active]
  have hlast := getLast?_append_singleton callerStack fr
  have hdrop := dropLast_append_singleton callerStack fr
  have hls : listSet m.threads m.active_thread
      { thread1 rootCtx (callerStack ++ [fr]) with stack := callerStack } "pop" =
      .ok [thread1 rootCtx callerStack] := by
    rw [hthr0, hsh.active]; rfl
  let mPop : Mach := { m with threads := [thread1 rootCtx callerStack] }
  have hshPop : Shape mPop rootCtx callerStack m.mem.memory.allocations :=
    ⟨rfl, hsh.active, hsh.allocs⟩
  have hscOf : ∀ d ∈ calleeBody.localDecls, (scalarTypeOf d.ty).isSome = true :=
    fun d hd => List.all_eq_true.mp hcalleeScalar d hd
  have hsc0 : (scalarTypeOf calleeRetDecl.ty).isSome = true := hscOf _ (List.mem_of_getElem? hd0)
  have hdSc0 : scalarTypeOf calleeRetDecl.ty = some (tyOf calleeRetDecl) :=
    scalarTypeOf_tyOf_of_isSome hsc0 _
  have hloc0 : mapGet calleeFn.locals (localName 0) = some (tyOf calleeRetDecl) := by
    rw [(hfCallee.2 0 calleeRetDecl hd0).2,
      tyOf_scalar_layouts hsc0 calleeBody.layouts ⟨64, true, []⟩]
  have hdeclsOk : ∀ d ∈ calleeBody.localDecls, localDeclOk calleeBody.layouts d = true := by
    intro d hd
    simp [localDeclOk, hscOf d hd]
  have hlt0 := localTy_of_decl hdSc0
  have hmiTy : mapIndex fr.func.locals fr.func.ret "frame.func.locals[frame.func.ret]" =
      .ok (tyOf calleeRetDecl) := by
    simp [fr, calleeFrameL, mapIndex, hfCallee.1, hloc0]
  have hvlt0 : 0 < calleeView.length :=
    by rw [hloCallee.nlocals]; exact (List.getElem?_eq_some_iff.mp hd0).1
  obtain ⟨slot0, hs0⟩ : ∃ s, calleeView[0]? = some s := ⟨_, List.getElem?_eq_getElem hvlt0⟩
  have hs0Ne : slot0 ≠ .dead := fun hc => hRetLive (hc ▸ hs0)
  obtain ⟨retPtr, hretPtr⟩ := hloCallee.some_of_live hs0 hs0Ne
  have hmiPtr : mapIndex fr.locals fr.func.ret "frame.locals[frame.func.ret]" = .ok retPtr := by
    simp [fr, calleeFrameL, mapIndex, hfCallee.1, hretPtr]
  obtain ⟨retId, hretProv, _, hretAddr, _, hA0⟩ := hloCallee.storage_scalar hd0 hsc0 hs0 hretPtr
  have hretAlign : Align.is_aligned ⟨(itOf calleeRetDecl).size.bytes⟩ retPtr.addr = true := by
    simp [Align.is_aligned, hretAddr.1]
  refine ⟨fun retVal hinit => ?_, fun huninit => ?_⟩
  · rw [hs0] at hinit; simp at hinit; subst hinit
    have hvOk : SlotOk (tyOf calleeRetDecl) (.init retVal) := by
      have h := hloCallee.slots 0 calleeRetDecl (.init retVal) hd0 hs0
      rwa [DeclSlotOk_of_scalarTypeOf hdSc0,
        tyOf_scalar_layouts hsc0 calleeBody.layouts ⟨64, true, []⟩] at h
    obtain ⟨mLd, hmLd, hshLd⟩ :=
      typedLoad_ptr_localTy hshPop retPtr retId hretProv calleeRetDecl hdSc0
        retVal hvOk hA0 ⟨(itOf calleeRetDecl).size.bytes⟩ hretAlign
    obtain ⟨cmLd, hcmLd⟩ := typedLoad_mem_only hmLd
    have hmemLd : mLd.mem.memory.allocations = m.mem.memory.allocations := hshLd.allocs
    obtain ⟨hidnd, hokTd, hlowTd, hallTd⟩ := hloCallee.teardown hfCallee hdeclsOk
    obtain ⟨R0, hR0⟩ := hloCallee.base
    obtain ⟨cmDe, hde, hdeMem⟩ :=
      deallocAll_gen fr.locals.entries.length fr mLd.mem calleeLm.entries
        (Nat.le_refl _) rfl hloCallee.keysNodup hidnd
        (fun e he => by simpa [fr, calleeFrameL, hmemLd] using hokTd e he)
    obtain ⟨R', hkillEq, hdeadR'⟩ :=
      killAt_append_dead calleeCtx.base R0 (calleeLm.entries.map (fun e => provId e.2))
        hlowTd (fun j b hb hbl => hallTd (calleeCtx.base.length + j) b
          (by rw [hR0, List.getElem?_append_right (Nat.le_add_right _ _)]; simpa using hb)
          hbl (Nat.le_add_right _ _))
    have hcmDeAllocs : cmDe.memory.allocations = calleeCtx.base ++ R' := by
      rw [hdeMem, hmemLd, hR0, hkillEq]
    let mDe : Mach := { mLd with mem := cmDe }
    have hshDe : Shape mDe rootCtx (preFrames ++ [calleeFrameL callerFn callerCtx callerLm callerBlk callerStmt])
        (calleeCtx.base ++ R') := by
      refine ⟨?_, hshLd.active, hcmDeAllocs⟩
      simpa [mDe, callerStack, hCallerFr] using hshLd.threads
    have hactDe : activeThread mDe =
        .ok (thread1 rootCtx (preFrames ++ [calleeFrameL callerFn callerCtx callerLm callerBlk callerStmt])) := by
      simp [activeThread, listIndex, hshDe.threads, hshDe.active]
    dsimp only [mDe] at hactDe
    have hstackNe : (thread1 rootCtx
        (preFrames ++ [calleeFrameL callerFn callerCtx callerLm callerBlk callerStmt])).stack.length ≠ 0 := by
      simp [thread1]
    have hmDeEnv : mDe.prog = m.prog ∧ mDe.fn_ptrs = m.fn_ptrs := by
      simp [mDe, hcmLd, mPop]
    have hspa : fr.stack_pop_action =
        .BackToCaller (some (bbName returnTarget)) calleeCtx.unwindBlock calleeCtx.retPtr := by
      simp [fr, calleeFrameL, hNextBlk]
    cases hDest with
    | root dst dDst callerSlot hActual hLive hView hdDst hSameTy hLocs hPtr =>
      have hLocsR := hLocs.append_dead hdeadR'
      obtain ⟨hTyEq, hItEq, ⟨T', hscDst, _⟩, hDataEq⟩ := sameFragmentTy_spec hSameTy
      have hscD : (scalarTypeOf dDst.ty).isSome = true := by simp [hscDst]
      have hdDstSc : scalarTypeOf dDst.ty = some (tyOf dDst) := scalarTypeOf_tyOf_of_isSome hscD _
      obtain ⟨idDst, hprovDst, _, haddrDst, _, hADst⟩ :=
        hLocsR.storage_scalar hdDst hscD hView hPtr
      have halDst : Align.is_aligned ⟨(itOf dDst).size.bytes⟩ calleeCtx.retPtr.addr = true := by
        simp [Align.is_aligned, haddrDst.1]
      have hlenDst := declSlotData_length hdDstSc .uninit
      have hvOkDst : SlotOk (tyOf dDst) (.init retVal) := hTyEq ▸ hvOk
      obtain ⟨acc, hst⟩ :=
        typedStore_ptr_localTy hshDe calleeCtx.retPtr idDst hprovDst dDst hdDstSc _ hADst
          hlenDst retVal hvOkDst ⟨(itOf dDst).size.bytes⟩ halDst
      rw [hTyEq, hItEq] at hst
      let mSt := withMem mDe
        ((calleeCtx.base ++ R').set idDst
          (stackAlloc calleeCtx.retPtr.addr (itOf dDst) (declSlotData dDst (.init retVal)))) acc
      have hshSt : Shape mSt rootCtx
          (preFrames ++ [calleeFrameL callerFn callerCtx callerLm callerBlk callerStmt])
          mSt.mem.memory.allocations := withMem_shape hshDe _
      have hjmp := jumpToBlock_append hshSt returnTarget
      have hloNew := hLocsR.store_scalar dst dDst hdDst hscD .uninit (.init retVal) hView (by simp)
        hvOkDst calleeCtx.retPtr hPtr idDst hprovDst
      have hvltDst : dst < callerView.length := (List.getElem?_eq_some_iff.mp hView).1
      have haltDst : dst < callerActual.length := (List.getElem?_eq_some_iff.mp hActual).1
      refine ⟨callerView.set dst (.init retVal),
        rethread mSt rootCtx (preFrames ++ [calleeFrameL callerFn callerCtx callerLm returnTarget 0]),
        ?_, ⟨rfl, hshSt.active, hshSt.allocs⟩, hmDeEnv.1, hmDeEnv.2, by simp, ?_, ?_,
        fun j hj => List.getElem?_set_ne (Ne.symm hj),
        fun j hj => by simp [writeCallDest]; exact List.getElem?_set_ne (Ne.symm hj),
        hloNew⟩
      · unfold evalReturn
        rw [hact0, ok_bind]
        have hst0 : (thread1 rootCtx (callerStack ++ [fr])).stack = callerStack ++ [fr] := rfl
        rw [hst0, hlast]
        dsimp only
        rw [pure_ok, ok_bind, hdrop, hls, ok_bind, hmiTy, ok_bind, hlt0.layout, ok_bind,
          expect_align_sized, ok_bind, hmiPtr, ok_bind, hmLd, ok_bind, hde, ok_bind]
        dsimp only
        rw [hspa]
        dsimp only
        rw [hactDe, ok_bind]
        simp only [hstackNe, ↓reduceIte]
        rw [hst, ok_bind, ← hItEq]
        exact hjmp
      · simp [writeCallDest, List.getElem?_set_self haltDst, List.getElem?_set_self hvltDst]
      · simp [List.getElem?_set_self hvltDst]
    | field0 dst fTy dDst it sc0 sc1 allocPre idDst hActual hView hdDst hTup hfTy hRetTy
        hsc1 hLocs hPtr hProv hAllocPre hBase =>
      have hgood := intBoolTupleOf_good hTup
      obtain ⟨hTdDst, hitDst⟩ := tyOf_tuple (layouts := ⟨64, true, []⟩) hTup
      obtain ⟨hTyRet, hItRet⟩ := tyOf_int (layouts := ⟨64, true, []⟩) hRetTy
      have hscD : (scalarTypeOf dDst.ty).isSome = true := by simp [scalarTypeOf_tuple hTup]
      rw [hTyRet] at hvOk
      cases retVal with
      | aggregate v fs =>
        exact False.elim (not_slotOk_aggregate rfl v fs hvOk)
      | unit | ptr =>
        simp [SlotOk] at hvOk
      | scalar scNew =>
        obtain ⟨hscNewSz, hscNewLt⟩ := hvOk
        simp only [tyBytes, ValidBits] at hscNewSz hscNewLt
        have hidLt : idDst < calleeCtx.base.length := by
          rw [hBase, List.length_set]; exact (List.getElem?_eq_some_iff.mp hAllocPre).1
        have hABase : (calleeCtx.base ++ R')[idDst]? =
            some (stackAlloc calleeCtx.retPtr.addr it
              (uninitBytes it ++ scalarBytes u8Ty sc1.bits ++
                List.replicate (it.size.bytes - 1) .Uninit)) := by
          rw [List.getElem?_append_left hidLt, hBase,
            List.getElem?_set_self (List.getElem?_eq_some_iff.mp hAllocPre).1]
        obtain ⟨_, _, _, haddrDst, _, _⟩ := hLocs.storage_scalar hdDst hscD hView hPtr
        rw [hitDst] at haddrDst
        have hst := typedStore_ptr_tuple_field0_after_prep hshDe hProv hgood scNew.bits sc1.bits
          hscNewLt hABase haddrDst
        let newTuple : Value := .aggregate 0 [.scalar scNew, .scalar sc1]
        have hsetEq :
            (calleeCtx.base ++ R').set idDst
              (stackAlloc calleeCtx.retPtr.addr it (tupleBytes it scNew.bits sc1.bits)) =
            (allocPre ++ R').set idDst
              (stackAlloc calleeCtx.retPtr.addr (itOf dDst) (declSlotData dDst (.init newTuple))) := by
          have hidPre : idDst < allocPre.length := (List.getElem?_eq_some_iff.mp hAllocPre).1
          rw [List.set_append_left _ _ hidLt, hBase, List.set_set,
            List.set_append_left _ _ hidPre, hitDst, declSlotData_of_some hTup]
          rfl
        have hLocsR := hLocs.append_dead hdeadR'
        have hvOkTup : SlotOk (tyOf dDst) (.init newTuple) := by
          rw [hTdDst]
          exact ⟨it, tupleIntOfTy_intBoolTupleTy it, hscNewSz, hscNewLt, hsc1.1, hsc1.2⟩
        let mSt := withMem mDe
          ((calleeCtx.base ++ R').set idDst
            (stackAlloc calleeCtx.retPtr.addr it (tupleBytes it scNew.bits sc1.bits)))
          ⟨.Store, .None, calleeCtx.retPtr.addr, it.size⟩
        have hshSt : Shape mSt rootCtx
            (preFrames ++ [calleeFrameL callerFn callerCtx callerLm callerBlk callerStmt])
            mSt.mem.memory.allocations := withMem_shape hshDe _
        have hjmp := jumpToBlock_append hshSt returnTarget
        have hloNew := hLocsR.store_scalar dst dDst hdDst hscD _ (.init newTuple) hView (by simp)
          hvOkTup calleeCtx.retPtr hPtr idDst hProv
        rw [← hsetEq] at hloNew
        have hvltDst : dst < callerView.length := (List.getElem?_eq_some_iff.mp hView).1
        have haltDst : dst < callerActual.length := (List.getElem?_eq_some_iff.mp hActual).1
        refine ⟨callerView.set dst (.init newTuple),
          rethread mSt rootCtx (preFrames ++ [calleeFrameL callerFn callerCtx callerLm returnTarget 0]),
          ?_, ⟨rfl, hshSt.active, hshSt.allocs⟩, hmDeEnv.1, hmDeEnv.2, by simp, ?_, ?_,
          fun j hj => List.getElem?_set_ne (Ne.symm hj),
          fun j hj => by simp [writeCallDest, hActual]; exact List.getElem?_set_ne (Ne.symm hj),
          hloNew⟩
        · unfold evalReturn
          rw [hact0, ok_bind]
          have hst0 : (thread1 rootCtx (callerStack ++ [fr])).stack = callerStack ++ [fr] := rfl
          rw [hst0, hlast]
          dsimp only
          rw [pure_ok, ok_bind, hdrop, hls, ok_bind, hmiTy, ok_bind, hlt0.layout, ok_bind,
            expect_align_sized, ok_bind, hmiPtr, ok_bind, hmLd, ok_bind, hde, ok_bind]
          dsimp only
          rw [hspa]
          dsimp only
          rw [hactDe, ok_bind]
          simp only [hstackNe, ↓reduceIte, hTyRet, hItRet, valOfValue, valOf]
          rw [hst, ok_bind]
          exact hjmp
        · simp [writeCallDest, hActual, List.getElem?_set_self haltDst, List.getElem?_set_self hvltDst, newTuple]
        · simp [List.getElem?_set_self hvltDst]
    | field1 dst fTy dDst it sc0 sc1 allocPre pDst idDst hActual hView hdDst hTup hfTy hRetTy
        hsc0 hLocs hPtr hProv hRetPtr hAllocPre hBase =>
      have hgood := intBoolTupleOf_good hTup
      obtain ⟨hTdDst, hitDst⟩ := tyOf_tuple (layouts := ⟨64, true, []⟩) hTup
      obtain ⟨hTyRet, hItRet⟩ := tyOf_bool (layouts := ⟨64, true, []⟩) hRetTy
      have hscD : (scalarTypeOf dDst.ty).isSome = true := by simp [scalarTypeOf_tuple hTup]
      rw [hTyRet] at hvOk
      cases retVal with
      | aggregate v fs =>
        exact False.elim (not_slotOk_aggregate rfl v fs hvOk)
      | unit | ptr =>
        simp [SlotOk] at hvOk
      | scalar scNew =>
        obtain ⟨hscNewSz, hscNewLt⟩ := hvOk
        simp only [tyBytes, ValidBits] at hscNewSz hscNewLt
        have hidLt : idDst < calleeCtx.base.length := by
          rw [hBase, List.length_set]; exact (List.getElem?_eq_some_iff.mp hAllocPre).1
        have hABase : (calleeCtx.base ++ R')[idDst]? =
            some (stackAlloc pDst.addr it
              (scalarBytes it sc0.bits ++ [.Uninit] ++
                List.replicate (it.size.bytes - 1) .Uninit)) := by
          rw [List.getElem?_append_left hidLt, hBase,
            List.getElem?_set_self (List.getElem?_eq_some_iff.mp hAllocPre).1]
        have hRetPtrEq : calleeCtx.retPtr = field1Ptr pDst it := hRetPtr
        have hst := typedStore_ptr_tuple_field1_after_prep hshDe hProv hgood sc0.bits scNew.bits
          hscNewLt hABase
        let newTuple : Value := .aggregate 0 [.scalar sc0, .scalar scNew]
        have hsetEq :
            (calleeCtx.base ++ R').set idDst
              (stackAlloc pDst.addr it (tupleBytes it sc0.bits scNew.bits)) =
            (allocPre ++ R').set idDst
              (stackAlloc pDst.addr (itOf dDst) (declSlotData dDst (.init newTuple))) := by
          have hidPre : idDst < allocPre.length := (List.getElem?_eq_some_iff.mp hAllocPre).1
          rw [List.set_append_left _ _ hidLt, hBase, List.set_set,
            List.set_append_left _ _ hidPre, hitDst, declSlotData_of_some hTup]
          rfl
        have hLocsR := hLocs.append_dead hdeadR'
        have hvOkTup : SlotOk (tyOf dDst) (.init newTuple) := by
          rw [hTdDst]
          exact ⟨it, tupleIntOfTy_intBoolTupleTy it, hsc0.1, hsc0.2, hscNewSz, hscNewLt⟩
        let mSt := withMem mDe
          ((calleeCtx.base ++ R').set idDst
            (stackAlloc pDst.addr it (tupleBytes it sc0.bits scNew.bits)))
          ⟨.Store, .None, (field1Ptr pDst it).addr, u8Ty.size⟩
        have hshSt : Shape mSt rootCtx
            (preFrames ++ [calleeFrameL callerFn callerCtx callerLm callerBlk callerStmt])
            mSt.mem.memory.allocations := withMem_shape hshDe _
        have hjmp := jumpToBlock_append hshSt returnTarget
        have hloNew := hLocsR.store_scalar dst dDst hdDst hscD _ (.init newTuple) hView (by simp)
          hvOkTup pDst hPtr idDst hProv
        rw [← hsetEq] at hloNew
        have hvltDst : dst < callerView.length := (List.getElem?_eq_some_iff.mp hView).1
        have haltDst : dst < callerActual.length := (List.getElem?_eq_some_iff.mp hActual).1
        refine ⟨callerView.set dst (.init newTuple),
          rethread mSt rootCtx (preFrames ++ [calleeFrameL callerFn callerCtx callerLm returnTarget 0]),
          ?_, ⟨rfl, hshSt.active, hshSt.allocs⟩, hmDeEnv.1, hmDeEnv.2, by simp, ?_, ?_,
          fun j hj => List.getElem?_set_ne (Ne.symm hj),
          fun j hj => by simp [writeCallDest, hActual]; exact List.getElem?_set_ne (Ne.symm hj),
          hloNew⟩
        · unfold evalReturn
          rw [hact0, ok_bind]
          have hst0 : (thread1 rootCtx (callerStack ++ [fr])).stack = callerStack ++ [fr] := rfl
          rw [hst0, hlast]
          dsimp only
          rw [pure_ok, ok_bind, hdrop, hls, ok_bind, hmiTy, ok_bind, hlt0.layout, ok_bind,
            expect_align_sized, ok_bind, hmiPtr, ok_bind, hmLd, ok_bind, hde, ok_bind]
          dsimp only
          rw [hspa]
          dsimp only
          rw [hactDe, ok_bind]
          simp only [hstackNe, ↓reduceIte, hRetPtrEq, hTyRet, hItRet, valOfValue, valOf]
          rw [hst, ok_bind]
          exact hjmp
        · simp [writeCallDest, hActual, List.getElem?_set_self haltDst, List.getElem?_set_self hvltDst, newTuple]
        · simp [List.getElem?_set_self hvltDst]
  · rw [hs0] at huninit; simp at huninit; subst huninit
    obtain ⟨msg, hmsg⟩ :=
      typedLoad_ptr_localTy_uninit hshPop retPtr retId hretProv calleeRetDecl hdSc0
        hA0 ⟨(itOf calleeRetDecl).size.bytes⟩ hretAlign
    refine ⟨msg, ?_⟩
    unfold evalReturn
    rw [hact0, ok_bind]
    have hst0 : (thread1 rootCtx (callerStack ++ [fr])).stack = callerStack ++ [fr] := rfl
    rw [hst0, hlast]
    dsimp only
    rw [pure_ok, ok_bind, hdrop, hls, ok_bind, hmiTy, ok_bind, hlt0.layout, ok_bind,
      expect_align_sized, ok_bind, hmiPtr, ok_bind, hmsg]
    rfl

theorem evalPlace_unitPlace (m : Mach) :
    evalPlace m unitPlace = .ok ((⟨⟨⟨1, none⟩, none⟩, true⟩, Interp.unitType), m) := rfl

theorem placeStore_unitValue (m : Mach) :
    placeStore m ⟨⟨⟨1, none⟩, none⟩, true⟩ Interp.unitValue Interp.unitType =
      .ok (withMem m m.mem.memory.allocations ⟨.Store, .None, 1, ⟨0⟩⟩) := rfl

theorem evalTerminator_assume_spec {curBody : CapturedMir} {curFn : Gen.Function}
    {rootCtx curCtx : Ctx} {callerFrames : List Frame} {view : List LocalSlot}
    {curLm : Map Gen.LocalName Ptr} {m : Mach} {curSeg segStmt nextSeg : Nat}
    {op : Operand} {op' : Gen.ValueExpr}
    (hshape : Shape m rootCtx
      (callerFrames ++ [calleeFrameL curFn curCtx curLm curSeg segStmt])
      m.mem.memory.allocations)
    (hframe : FrameOk curBody curFn curCtx view curLm
      (rethread m curCtx
        [curCtx.caller, calleeFrameL curFn curCtx curLm curSeg segStmt])
      curSeg segStmt)
    (hokB : operandOkB curBody.layouts curBody.localDecls (copyOp op) = true)
    (hop : translateOperand curBody.localDecls op = some op') :
    (opBits view (copyOp op) = none →
      ∃ msg, Interp.evalTerminator m
        (.Intrinsic .Assume [op'] unitPlace (some (bbName nextSeg))) = .error (.ub msg)) ∧
    (opBits view (copyOp op) = some 0 →
      Interp.evalTerminator m
        (.Intrinsic .Assume [op'] unitPlace (some (bbName nextSeg))) =
        .error (.ub "`Assume` intrinsic called on condition that is violated")) ∧
    (∀ bits, opBits view (copyOp op) = some bits → bits ≠ 0 →
      ∃ m4, Interp.evalTerminator m
          (.Intrinsic .Assume [op'] unitPlace (some (bbName nextSeg))) = .ok m4 ∧
        Shape m4 rootCtx
          (callerFrames ++ [calleeFrameL curFn curCtx curLm nextSeg 0])
          m4.mem.memory.allocations ∧
        m4.prog = m.prog ∧ m4.fn_ptrs = m.fn_ptrs ∧
        LocalsOk curBody curCtx view curLm m4.mem.memory.allocations) := by
  have hopCopy : translateOperand curBody.localDecls (copyOp op) = some op' := by
    rw [translateOperand_copyOp]
    exact hop
  obtain ⟨hMok, hMnone⟩ :=
    evalValue_operandT hframe (.bool : FragTy .Bool u8Ty) (copyOp op)
      (operandOkB_T hokB) op' hopCopy
  obtain ⟨hvOkRe, hvErrRe⟩ := evalValue_rethread op' m rootCtx curCtx
    callerFrames (calleeFrameL curFn curCtx curLm curSeg segStmt) hshape.threads hshape.active
  refine ⟨fun hnone => ?_, fun h0 => ?_, fun bits hb hne0 => ?_⟩
  · obtain ⟨msg, hmsgR⟩ := hMnone hnone
    have hmsg := hvErrRe (.ub msg) hmsgR
    exact ⟨msg, by
      simp [Interp.evalTerminator, evalPlace_unitPlace,
        evalArgs, hmsg]⟩
  · obtain ⟨_, m3R, hm3R, _⟩ := hMok 0 h0
    obtain ⟨cm3, _, hm3⟩ := hvOkRe _ m3R hm3R
    simp [Interp.evalTerminator, evalPlace_unitPlace,
      evalArgs, hm3, valOf, evalIntrinsic, Interp.unitType, ub]
  · obtain ⟨hvbits, m3R, hm3R, h3R⟩ := hMok bits hb
    simp only [ValidBits] at hvbits
    have hb1 : bits = 1 := by omega
    subst hb1
    obtain ⟨cm3, hcm3, hm3⟩ := hvOkRe _ m3R hm3R
    let m3 : Mach := { m with mem := cm3 }
    have hev : evalIntrinsic m3 .Assume [(valOf .Bool 1, .Bool)] Interp.unitType =
        .ok (Interp.unitValue, m3) := rfl
    let mSt : Mach := withMem m3 m3.mem.memory.allocations ⟨.Store, .None, 1, ⟨0⟩⟩
    have hshSt : Shape mSt rootCtx
        (callerFrames ++ [calleeFrameL curFn curCtx curLm curSeg segStmt])
        cm3.memory.allocations := ⟨hshape.threads, hshape.active, rfl⟩
    have hjmp := jumpToBlock_append hshSt nextSeg
    refine ⟨rethread mSt rootCtx (callerFrames ++ [calleeFrameL curFn curCtx curLm nextSeg 0]),
      ?_, ⟨rfl, hshape.active, rfl⟩, rfl, rfl, ?_⟩
    · simp only [Interp.evalTerminator, evalPlace_unitPlace, ok_bind,
        evalArgs, hm3, pure_ok]
      rw [hev, ok_bind, placeStore_unitValue, ok_bind]
      exact hjmp
    · have hlo3 := h3R.locs
      rw [hcm3] at hlo3
      exact hlo3

end MiniRustSpec.Correspondence
