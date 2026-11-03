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

theorem GoodSize.pos {n : Nat} (h : GoodSize n) : 0 < n := by
  rcases h with h | h | h | h | h <;> omega

theorem align_eq (it : Gen.IntType) (h : GoodSize it.size.bytes) :
    IntType.align it = .ok ⟨it.size.bytes⟩ := by
  unfold IntType.align alignFromBytes
  rcases h with h | h | h | h | h <;> rw [h] <;> rfl

theorem layout_eq (it : Gen.IntType) (h : GoodSize it.size.bytes) :
    Type.layout (.Int it) = .ok (.Sized it.size ⟨it.size.bytes⟩) := by
  simp [Type.layout, align_eq it h]

/-! ## The callee's allocations and locals map -/

theorem slotData_length (it : Gen.IntType) (slot : LocalSlot) :
    (slotData it slot).length = it.size.bytes := by
  unfold slotData
  split <;> simp [scalarBytes, uninitBytes, leBytes_length]

theorem localAllocsFrom_getElem? (ctx : Ctx) (k : Nat) (ds : List LocalDecl) (slots : List LocalSlot)
    (j : Nat) (d : LocalDecl) (slot : LocalSlot) (hd : ds[j]? = some d) (hs : slots[j]? = some slot) :
    (localAllocsFrom ctx k ds slots)[j]? =
      some (localAlloc ctx (k + j) (itOf d) (slotData (itOf d) slot)) := by
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
    (j : Nat) (d : LocalDecl) (slot' : LocalSlot) (hd : ds[j]? = some d) :
    (localAllocsFrom ctx k ds slots).set j (localAlloc ctx (k + j) (itOf d) (slotData (itOf d) slot')) =
      localAllocsFrom ctx k ds (slots.set j slot') := by
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

theorem localAllocsFrom_length (ctx : Ctx) (k : Nat) (ds : List LocalDecl) (slots : List LocalSlot) :
    (localAllocsFrom ctx k ds slots).length = min ds.length slots.length := by
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

/-- Encoding an in-window integer at an integer type yields the little-endian
bytes of its residue. -/
theorem encode_int (it : Gen.IntType) (v : Int) (hgood : GoodSize it.size.bytes)
    (hv : IntType.can_represent it v = true) :
    Type.encode (.Int it) (.Int v) = .ok (scalarBytes it (v % 2 ^ (8 * it.size.bytes)).toNat) := by
  obtain ⟨signed, size⟩ := it
  have h : inBounds v signed size = true := hv
  simp [Type.encode, x86_64.ENDIANNESS, encode_eq signed size v h, scalarBytes, Size.bits]

/-! ## Loads and stores of the callee's locals -/

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
theorem isAligned_one (a : Int) : Align.is_aligned ⟨1⟩ a = true := by
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
    List.take_of_length_le, Type.decode, mapM_data_scalarBytes, x86_64.ENDIANNESS,
    decode_leBytes signed size.bytes bits hb, checkValue, canRepresent_intFromBits _ bits hgood hb,
    withMem]

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
    List.take_of_length_le, Type.decode, mapM_data_uninitBytes _ hpos, ub]

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
  have hck : checkValue (.Int v) (.Int it) = .ok () := by simp [checkValue, hv]
  have hne : scalarBytes it (v % 2 ^ (8 * it.size.bytes)).toNat ≠ [] :=
    List.ne_nil_of_length_pos (by omega)
  simp only [typedStore, hck, encode_int it v hgood hv, CM.store, BM.store, hal, BM.check_ptr,
    localPtr, listIndex, h.allocs]
  obtain ⟨signed, size⟩ := it
  have hdrop : data.drop size.bytes = [] := List.drop_eq_nil_of_le (by simp at hlen; omega)
  simp [hne, hi, hLi, Allocation.size, hlen, hblen, writeSubsliceAtIndex, listSet, withMem, hdrop]
  simp [localAlloc]

/-! ## Places of the callee's locals -/

theorem evalPlace_local {m : Mach} {ctx : Ctx} {f : Gen.Function} {n blk stmt : Nat}
    {allocs : List Gen.Allocation}
    (h : Shape m ctx [ctx.caller, calleeFrame f ctx n blk stmt] allocs) (i : Nat) (hi : i < n)
    (T : Gen.Type) (hT : mapGet f.locals (localName i) = some T) :
    evalPlace m (.Local (localName i)) =
      .ok ({ ptr := { thin_pointer := localPtr ctx i, metadata := none }, aligned := true }, T) := by
  simp [evalPlace, curFrame_eq h, mapIndex, calleeFrame, hT, mapGet_localsMap ctx n i hi]

/-! ## Operands and rvalues -/

/-- The bit pattern an Anneal fragment operand evaluates to, or `none` when
reading it is UB (an uninitialized local). -/
def opBits (locals : List LocalSlot) : Operand → Option Nat
  | .copy ⟨j, []⟩ =>
    match locals[j]? with
    | some (.init (.scalar sc)) => some sc.bits
    | _ => none
  | .constant c =>
    match c.val with
    | .scalar (.int sc) => some sc.bits
    | _ => none
  | _ => none

/-- The arithmetic of `eval_int_bin_op` for the fragment operators. -/
def intArith : Gen.IntBinOp → Int → Int → Int
  | .Add, x, y => x + y
  | .Sub, x, y => x - y
  | .Mul, x, y => x * y
  | _, _, _ => 0

theorem evalIntBinOp_eq (op : MirAst.BinOp) (iop : Gen.IntBinOp) (hop : translateBinOp op = some iop)
    (x y : Int) (it : Gen.IntType) : evalIntBinOp iop x y it = .ok (intArith iop x y) := by
  cases op <;> simp [translateBinOp] at hop <;> subst hop <;> rfl

theorem intArith_emod (op : MirAst.BinOp) (iop : Gen.IntBinOp) (hop : translateBinOp op = some iop)
    (x y x' y' m : Int) (hx : x % m = x' % m) (hy : y % m = y' % m) :
    intArith iop x y % m = intArith iop x' y' % m := by
  cases op <;> simp [translateBinOp] at hop <;> subst hop <;> simp only [intArith]
  · rw [Int.add_emod, hx, hy, ← Int.add_emod]
  · rw [Int.sub_emod, hx, hy, ← Int.sub_emod]
  · rw [Int.mul_emod, hx, hy, ← Int.mul_emod]

/-- Hypotheses describing a callee frame related to Anneal locals `locals`. -/
structure FrameOk (body : CapturedMir) (f : Gen.Function) (ctx : Ctx) (locals : List LocalSlot)
    (m : Mach) (blk stmt : Nat) : Prop where
  hf : translateFn body = some f
  shape : Shape m ctx [ctx.caller, calleeFrame f ctx body.localDecls.length blk stmt]
    (ctx.base ++ localAllocs ctx body.localDecls locals)
  nlocals : locals.length = body.localDecls.length
  slots : ∀ (i : Nat) d slot, body.localDecls[i]? = some d → locals[i]? = some slot →
    SlotOk (itOf d) slot

theorem FrameOk.decl_good {body : CapturedMir} {f : Gen.Function} {ctx : Ctx} {locals : List LocalSlot}
    {m : Mach} {blk stmt : Nat} (h : FrameOk body f ctx locals m blk stmt) (i : Nat) (d : LocalDecl)
    (hd : body.localDecls[i]? = some d) : GoodSize (itOf d).size.bytes :=
  intTypeOf_good ((translateFn_spec body f h.hf).2.1 i d hd).1

theorem FrameOk.localAllocs_get {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {locals : List LocalSlot} {m : Mach} {blk stmt : Nat} (_h : FrameOk body f ctx locals m blk stmt)
    (i : Nat) (d : LocalDecl) (slot : LocalSlot) (hd : body.localDecls[i]? = some d)
    (hs : locals[i]? = some slot) :
    (localAllocs ctx body.localDecls locals)[i]? =
      some (localAlloc ctx i (itOf d) (slotData (itOf d) slot)) := by
  simpa [localAllocs] using localAllocsFrom_getElem? ctx 0 body.localDecls locals i d slot hd hs

theorem FrameOk.slot_exists {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {locals : List LocalSlot} {m : Mach} {blk stmt : Nat} (h : FrameOk body f ctx locals m blk stmt)
    (i : Nat) (hi : i < body.localDecls.length) :
    ∃ d slot, body.localDecls[i]? = some d ∧ locals[i]? = some slot := by
  refine ⟨body.localDecls[i], locals[i]'(by rw [h.nlocals]; exact hi), by simp [hi], by simp⟩

/-- Evaluating a translated fragment operand. -/
theorem evalValue_operand {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {locals : List LocalSlot} {m : Mach} {blk stmt : Nat} (h : FrameOk body f ctx locals m blk stmt)
    (it : Gen.IntType) (op : Operand) (hok : operandOk body.localDecls it op = true)
    (e : Gen.ValueExpr) (he : translateOperand op = some e) :
    (∀ bits, opBits locals op = some bits →
      bits < 2 ^ (8 * it.size.bytes) ∧
      ∃ m', evalValue m e = .ok ((.Int (intFromBits bits it), .Int it), m') ∧
        FrameOk body f ctx locals m' blk stmt) ∧
    (opBits locals op = none → ∃ msg, evalValue m e = .error (.ub msg)) := by
  match op, hok, he with
  | .copy ⟨j, []⟩, hok, he =>
    simp only [operandOk, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨hj, hty⟩ := hok
    simp only [translateOperand, Option.some.injEq] at he
    subst he
    obtain ⟨d, slot, hd, hs⟩ := h.slot_exists j hj
    have hit : itOf d = it := by
      simp [operandIntType, hd] at hty
      simp [itOf, hty]
    subst hit
    have hspec := (translateFn_spec body f h.hf).2.1 j d hd
    have hplace := evalPlace_local h.shape j hj _ hspec.2
    have hgood := h.decl_good j d hd
    have hL := h.localAllocs_get j d slot hd hs
    have hslot := h.slots j d slot hd hs
    match slot, hslot, hL with
    | .uninit, _, hL =>
      refine ⟨fun bits hb => by simp [opBits, hs] at hb, fun _ => ?_⟩
      obtain ⟨msg, hmsg⟩ := typedLoad_local_uninit h.shape j (itOf d) hgood hL ⟨1⟩ (isAligned_one _)
      exact ⟨msg, by simp [evalValue, hplace, placeLoad, hmsg]⟩
    | .init (.scalar sc), hok', hL =>
      obtain ⟨_, hb⟩ := hok'
      refine ⟨fun bits hbits => ?_, fun hnone => by simp [opBits, hs] at hnone⟩
      simp [opBits, hs] at hbits
      subst hbits
      obtain ⟨m', hm', hshape⟩ :=
        typedLoad_local_init h.shape j (itOf d) sc.bits hgood hb hL ⟨1⟩ (isAligned_one _)
      exact ⟨hb, m', by simp [evalValue, hplace, placeLoad, hm'],
        ⟨h.hf, hshape, h.nlocals, h.slots⟩⟩
  | .constant c, hok, he =>
    simp only [operandOk, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨hty, _⟩ := hok
    simp only [operandIntType] at hty
    simp only [translateOperand, hty] at he
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
        exact ⟨hb, m, by simp [evalValue, evalConstant], h⟩
      · simp at he

/-- The bit pattern an Anneal fragment rvalue of type `it` evaluates to, or
`none` when evaluating it is UB. -/
def rvBits (locals : List LocalSlot) (it : Gen.IntType) : Rvalue → Option Nat
  | .use op => opBits locals op
  | .unaryOp .neg op => do
    let x ← opBits locals op
    pure ((- (x : Int)) % 2 ^ (8 * it.size.bytes)).toNat
  | .binaryOp op a b => do
    let iop ← translateBinOp op
    let x ← opBits locals a
    let y ← opBits locals b
    pure (intArith iop x y % 2 ^ (8 * it.size.bytes)).toNat
  | _ => none

theorem bringInBounds_intArith (op : MirAst.BinOp) (iop : Gen.IntBinOp)
    (hop : translateBinOp op = some iop) (it : Gen.IntType) (hgood : GoodSize it.size.bytes)
    (x y : Nat) (hx : x < 2 ^ (8 * it.size.bytes)) (hy : y < 2 ^ (8 * it.size.bytes)) :
    IntType.bring_in_bounds it (intArith iop (intFromBits x it) (intFromBits y it)) =
      intFromBits (intArith iop x y % 2 ^ (8 * it.size.bytes)).toNat it := by
  have hn : 0 < 8 * it.size.bytes := by have := hgood.pos; omega
  have hn' : 0 < Size.bits it.size := by simpa [Size.bits] using hn
  obtain ⟨hl, hr⟩ := bringInBounds_window (intArith iop (intFromBits x it) (intFromBits y it))
    it.signed it.size hn'
  have heq := eq_intFromBits _ it hn (by simpa [Size.bits] using hl) (by simpa [Size.bits] using hr)
  unfold IntType.bring_in_bounds
  rw [heq]
  congr 2
  have := bringInBounds_emod (intArith iop (intFromBits x it) (intFromBits y it)) it.signed it.size
  simp only [Size.bits] at this
  rw [this]
  have hpos := two_pow_pos (8 * it.size.bytes)
  have hx' : intFromBits x it % 2 ^ (8 * it.size.bytes) = (x : Int) % 2 ^ (8 * it.size.bytes) := by
    rw [intFromBits_emod x it hx, Int.emod_eq_of_lt (by omega) (by exact_mod_cast hx)]
  have hy' : intFromBits y it % 2 ^ (8 * it.size.bytes) = (y : Int) % 2 ^ (8 * it.size.bytes) := by
    rw [intFromBits_emod y it hy, Int.emod_eq_of_lt (by omega) (by exact_mod_cast hy)]
  exact intArith_emod op iop hop _ _ _ _ _ hx' hy'

theorem intFromBits_zero (it : Gen.IntType) : intFromBits 0 it = 0 := by
  rcases it with ⟨s, sz⟩
  cases s <;> simp [intFromBits, Nat.two_pow_pos]

theorem bringInBounds_neg (it : Gen.IntType) (hgood : GoodSize it.size.bytes)
    (x : Nat) (hx : x < 2 ^ (8 * it.size.bytes)) :
    IntType.bring_in_bounds it (- intFromBits x it) =
      intFromBits ((- (x : Int)) % 2 ^ (8 * it.size.bytes)).toNat it := by
  have h := bringInBounds_intArith .sub .Sub rfl it hgood 0 x (Nat.two_pow_pos _) hx
  simpa [intArith, intFromBits_zero] using h

/-- Evaluating a translated fragment rvalue. -/
theorem evalValue_rvalue {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {locals : List LocalSlot} {m : Mach} {blk stmt : Nat} (h : FrameOk body f ctx locals m blk stmt)
    (it : Gen.IntType) (hgood : GoodSize it.size.bytes) (rv : Rvalue)
    (hok : rvalueOk body.localDecls it rv = true) (e : Gen.ValueExpr) (he : translateRvalue rv = some e) :
    (∀ r, rvBits locals it rv = some r →
      r < 2 ^ (8 * it.size.bytes) ∧
      ∃ m', evalValue m e = .ok ((.Int (intFromBits r it), .Int it), m') ∧
        FrameOk body f ctx locals m' blk stmt) ∧
    (rvBits locals it rv = none → ∃ msg, evalValue m e = .error (.ub msg)) := by
  match rv, hok, he with
  | .use op, hok, he =>
    simp only [rvalueOk] at hok
    simp only [translateRvalue] at he
    exact evalValue_operand h it op hok e he
  | .unaryOp .neg op, hok, he =>
    simp only [rvalueOk] at hok
    simp only [translateRvalue, Option.bind_eq_bind] at he
    cases heo : translateOperand op with
    | none => simp [heo] at he
    | some eo =>
      simp [heo] at he
      subst he
      obtain ⟨haok, hanone⟩ := evalValue_operand h it op hok eo heo
      cases hxo : opBits locals op with
      | none =>
        refine ⟨fun r hr => by simp [rvBits, hxo] at hr, fun _ => ?_⟩
        obtain ⟨msg, hmsg⟩ := hanone hxo
        exact ⟨msg, by simp [evalValue, hmsg]⟩
      | some x =>
        obtain ⟨hx, m1, hm1, h1⟩ := haok x hxo
        refine ⟨fun r hr => ?_, fun hnone => by simp [rvBits, hxo] at hnone⟩
        simp [rvBits, hxo] at hr
        subst hr
        have hpos := two_pow_pos (8 * it.size.bytes)
        have hlt : ((- (x : Int)) % 2 ^ (8 * it.size.bytes)).toNat < 2 ^ (8 * it.size.bytes) := by
          have h0 := Int.emod_nonneg (- (x : Int)) (Int.ne_of_gt hpos)
          have hlt' := Int.emod_lt_of_pos (- (x : Int)) hpos
          have : (((- (x : Int)) % 2 ^ (8 * it.size.bytes)).toNat : Int) < 2 ^ (8 * it.size.bytes) := by
            rw [Int.toNat_of_nonneg h0]; exact hlt'
          exact_mod_cast this
        have hrep := canRepresent_intFromBits it _ hgood hlt
        refine ⟨hlt, m1, ?_, h1⟩
        simp [evalValue, hm1, evalUnOp, evalIntUnOp, bringInBounds_neg it hgood x hx,
          checkValue, hrep]
  | .binaryOp op a b, hok, he =>
    simp only [rvalueOk, Bool.and_eq_true] at hok
    obtain ⟨⟨hop, hoka⟩, hokb⟩ := hok
    obtain ⟨iop, hiop⟩ := Option.isSome_iff_exists.mp hop
    simp only [translateRvalue, hiop, Option.bind_eq_bind] at he
    cases hea : translateOperand a with
    | none => simp [hea] at he
    | some ea =>
      cases heb : translateOperand b with
      | none => simp [hea, heb] at he
      | some eb =>
        simp [hea, heb] at he
        subst he
        obtain ⟨haok, hanone⟩ := evalValue_operand h it a hoka ea hea
        cases hxa : opBits locals a with
        | none =>
          refine ⟨fun r hr => by simp [rvBits, hiop, hxa] at hr, fun _ => ?_⟩
          obtain ⟨msg, hmsg⟩ := hanone hxa
          exact ⟨msg, by simp [evalValue, hmsg]⟩
        | some x =>
          obtain ⟨hx, m1, hm1, h1⟩ := haok x hxa
          obtain ⟨hbok, hbnone⟩ := evalValue_operand h1 it b hokb eb heb
          cases hyb : opBits locals b with
          | none =>
            refine ⟨fun r hr => by simp [rvBits, hiop, hxa, hyb] at hr, fun _ => ?_⟩
            obtain ⟨msg, hmsg⟩ := hbnone hyb
            exact ⟨msg, by simp [evalValue, hm1, hmsg]⟩
          | some y =>
            obtain ⟨hy, m2, hm2, h2⟩ := hbok y hyb
            refine ⟨fun r hr => ?_, fun hnone => by simp [rvBits, hiop, hxa, hyb] at hnone⟩
            simp [rvBits, hiop, hxa, hyb] at hr
            subst hr
            have hpos := two_pow_pos (8 * it.size.bytes)
            refine ⟨?_, m2, ?_, h2⟩
            · have h0 := Int.emod_nonneg (intArith iop x y) (Int.ne_of_gt hpos)
              have h1 := Int.emod_lt_of_pos (intArith iop x y) hpos
              have : ((intArith iop x y % 2 ^ (8 * it.size.bytes)).toNat : Int) < 2 ^ (8 * it.size.bytes) := by
                rw [Int.toNat_of_nonneg h0]; exact h1
              exact_mod_cast this
            · simp [evalValue, hm1, hm2, evalBinOp, evalIntBinOp_eq op iop hiop,
                bringInBounds_intArith op iop hiop it hgood x y hx hy]

/-! ## Frames and control flow -/

theorem mutateCurFrame_eq {m : Mach} {ctx : Ctx} {fr : Frame} {allocs : List Gen.Allocation}
    (h : Shape m ctx [ctx.caller, fr] allocs) (g : Frame → Frame) :
    ∃ m', mutateCurFrame m g = .ok m' ∧ Shape m' ctx [ctx.caller, g fr] allocs := by
  refine ⟨{ m with threads := [thread1 ctx [ctx.caller, g fr]] }, ?_, ⟨rfl, h.active, h.allocs⟩⟩
  simp [mutateCurFrame, activeThread, listIndex, h.threads, h.active, thread1, listSet]

theorem jumpToBlock_callee {m : Mach} {ctx : Ctx} {f : Gen.Function} {n blk stmt : Nat}
    {allocs : List Gen.Allocation} (h : Shape m ctx [ctx.caller, calleeFrame f ctx n blk stmt] allocs)
    (t : Nat) :
    ∃ m', jumpToBlock m (bbName t) = .ok m' ∧ Shape m' ctx [ctx.caller, calleeFrame f ctx n t 0] allocs :=
  mutateCurFrame_eq h _

theorem bumpStmt_callee {m : Mach} {ctx : Ctx} {f : Gen.Function} {n blk stmt : Nat}
    {allocs : List Gen.Allocation} (h : Shape m ctx [ctx.caller, calleeFrame f ctx n blk stmt] allocs) :
    ∃ m', mutateCurFrame m (fun fr => { fr with next_stmt := fr.next_stmt + 1 }) = .ok m' ∧
      Shape m' ctx [ctx.caller, calleeFrame f ctx n blk (stmt + 1)] allocs := by
  obtain ⟨m', hm', hs⟩ := mutateCurFrame_eq h (fun fr => { fr with next_stmt := fr.next_stmt + 1 })
  refine ⟨m', hm', ?_⟩
  have : ({ calleeFrame f ctx n blk stmt with
      next_stmt := (calleeFrame f ctx n blk stmt).next_stmt + 1 } : Frame) =
      calleeFrame f ctx n blk (stmt + 1) := by
    simp [calleeFrame]
  rw [this] at hs; exact hs

/-- `Machine::eval_statement` on a translated fragment assignment. -/
theorem evalStatement_assign {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {locals : List LocalSlot} {m : Mach} {blk stmt : Nat} (h : FrameOk body f ctx locals m blk stmt)
    (i : Nat) (d : LocalDecl) (hd : body.localDecls[i]? = some d) (rv : Rvalue)
    (hok : rvalueOk body.localDecls (itOf d) rv = true) (e : Gen.ValueExpr)
    (he : translateRvalue rv = some e) :
    (∀ r, rvBits locals (itOf d) rv = some r →
      ∃ m', evalStatement m (.Assign (.Local (localName i)) e) = .ok m' ∧
        FrameOk body f ctx (locals.set i (.init (.scalar ⟨r, (itOf d).size.bytes⟩))) m' blk stmt) ∧
    (rvBits locals (itOf d) rv = none →
      ∃ msg, evalStatement m (.Assign (.Local (localName i)) e) = .error (.ub msg)) := by
  have hi : i < body.localDecls.length := (List.getElem?_eq_some_iff.mp hd).1
  have hgood := h.decl_good i d hd
  have hspec := (translateFn_spec body f h.hf).2.1 i d hd
  have hplace := evalPlace_local h.shape i hi _ hspec.2
  obtain ⟨hrok, hrnone⟩ := evalValue_rvalue h (itOf d) hgood rv hok e he
  obtain ⟨_, slot, _, hs⟩ := h.slot_exists i hi
  have hL := h.localAllocs_get i d slot hd hs
  refine ⟨fun r hr => ?_, fun hnone => ?_⟩
  · obtain ⟨hrlt, m1, hm1, h1⟩ := hrok r hr
    have hL1 := h1.localAllocs_get i d slot hd hs
    have hrep := canRepresent_intFromBits (itOf d) r hgood hrlt
    have hst := typedStore_local h1.shape i (itOf d) _ (intFromBits r (itOf d)) hgood hL1
      (slotData_length _ _) hrep ⟨1⟩ (isAligned_one _)
    have hres : (intFromBits r (itOf d) % 2 ^ (8 * (itOf d).size.bytes)).toNat = r := by
      rw [intFromBits_emod r _ hrlt]; simp
    rw [hres] at hst
    have hset := localAllocsFrom_set ctx 0 body.localDecls locals i d
      (.init (.scalar ⟨r, (itOf d).size.bytes⟩)) hd
    simp only [Nat.zero_add, slotData] at hset
    refine ⟨withMem m1 (ctx.base ++ localAllocs ctx body.localDecls
        (locals.set i (.init (.scalar ⟨r, (itOf d).size.bytes⟩))))
        ⟨.Store, .None, ctx.addrs.getD i 0, (itOf d).size⟩, ?_, ?_⟩
    · have hst' := hst
      simp only [localAllocs] at hst'
      rw [hset] at hst'
      simp [evalStatement, hplace, hm1, placeStore, hst', localAllocs]
    refine ⟨h.hf, withMem_shape h1.shape _, by simp [h.nlocals], ?_⟩
    · intro j d' slot' hd' hs'
      by_cases hij : i = j
      · subst hij
        rw [hd] at hd'; cases hd'
        simp [List.getElem?_set_self (by rw [h.nlocals]; exact hi)] at hs'
        subst hs'
        exact ⟨rfl, hrlt⟩
      · rw [List.getElem?_set_ne hij] at hs'
        exact h.slots j d' slot' hd' hs'
  · obtain ⟨msg, hmsg⟩ := hrnone hnone
    exact ⟨msg, by simp [evalStatement, hplace, hmsg]⟩

/-- `Machine::eval_statement` on a translated fragment `PlaceMention`. -/
theorem evalStatement_placeMention {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {locals : List LocalSlot} {m : Mach} {blk stmt : Nat} (h : FrameOk body f ctx locals m blk stmt)
    (i : Nat) (hi : i < body.localDecls.length) :
    evalStatement m (.PlaceMention (.Local (localName i))) = .ok m := by
  obtain ⟨d, _, hd, _⟩ := h.slot_exists i hi
  have hspec := (translateFn_spec body f h.hf).2.1 i d hd
  have hplace := evalPlace_local h.shape i hi _ hspec.2
  simp [evalStatement, hplace]

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

/-! ## `Return` -/

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

theorem storageDead_callee {fr : Frame} {cm : Gen.ConcurrentMemory BM} {ctx : Ctx} (i : Nat)
    (rest : List (Gen.LocalName × Ptr)) (hloc : fr.locals = ⟨(localName i, localPtr ctx i) :: rest⟩)
    (hrest : ∀ e ∈ rest, e.1 ≠ localName i) (it : Gen.IntType) (hgood : GoodSize it.size.bytes)
    (hty : mapGet fr.func.locals (localName i) = some (.Int it)) (L' : List Gen.Allocation)
    (hmem : cm.memory.allocations = ctx.base ++ L') (a : Gen.Allocation) (ha : L'[i]? = some a)
    (hlive : a.live = true) (haddr : a.addr = ctx.addrs.getD i 0) (hkind : a.kind = .Stack)
    (hlen : a.data.length = it.size.bytes) (halign : a.align = ⟨it.size.bytes⟩) :
    storageDead fr cm (localName i) =
      .ok ({ fr with locals := ⟨rest⟩ },
           { cm with memory := { cm.memory with allocations := ctx.base ++ L'.set i (kill a) } }) := by
  obtain ⟨hi, hai⟩ := List.getElem?_eq_some_iff.mp ha
  have hrest' : ∀ (x : Gen.LocalName) (y : Gen.ThinPointer (Gen.Memory.Provenance BM)),
      (x, y) ∈ rest → ¬x = localName i :=
    fun x y hxy => hrest (x, y) hxy
  simp [storageDead, mapIndex, hty, layout_eq it hgood, LayoutStrategy.expect_size,
    LayoutStrategy.expect_align, mapRemove, hloc, mapGet_cons, CM.deallocate,
    BM.deallocate, localPtr, listIndex, hmem, hi, hai, hlive, haddr, hkind, Allocation.size, hlen,
    halign, listSet, kill]
  exact hrest'

theorem deallocAll_callee (ctx : Ctx) (fuel : Nat) (fr : Frame) (cm : Gen.ConcurrentMemory BM)
    (is : List Nat) (L' : List Gen.Allocation) (hfuel : is.length ≤ fuel)
    (hloc : fr.locals = ⟨is.map (fun i => (localName i, localPtr ctx i))⟩) (hnodup : is.Nodup)
    (hmem : cm.memory.allocations = ctx.base ++ L')
    (hok : ∀ i ∈ is, ∃ it a, mapGet fr.func.locals (localName i) = some (.Int it) ∧
      GoodSize it.size.bytes ∧ L'[i]? = some a ∧ a.live = true ∧ a.addr = ctx.addrs.getD i 0 ∧
      a.kind = .Stack ∧ a.data.length = it.size.bytes ∧ a.align = ⟨it.size.bytes⟩) :
    ∃ cm', deallocAll fuel fr cm = .ok ({ fr with locals := ⟨[]⟩ }, cm') ∧
      cm'.memory.allocations = ctx.base ++ killAt L' is := by
  induction is generalizing fuel fr cm L' with
  | nil =>
    refine ⟨cm, ?_, by simp [hmem, killAt_nil]⟩
    have hfr : fr = { fr with locals := ⟨[]⟩ } := by
      cases fr; simp at hloc; simp [hloc]
    cases fuel <;> (simp only [deallocAll, hloc, List.map_nil]; rw [← hfr]; rfl)
  | cons i is ih =>
    obtain ⟨fuel', rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by simp at hfuel; omega⟩
    simp only [List.nodup_cons] at hnodup
    obtain ⟨hni, hnd⟩ := hnodup
    obtain ⟨it, a, hty, hgood, ha, hlive, haddr, hkind, hlen, halign⟩ := hok i (by simp)
    have hrest : ∀ e ∈ is.map (fun i => (localName i, localPtr ctx i)), e.1 ≠ localName i := by
      intro e he
      simp only [List.mem_map] at he
      obtain ⟨j, hj, rfl⟩ := he
      simp only [ne_eq, localName_inj]
      intro hji; subst hji; exact hni hj
    have hsd := storageDead_callee i _ (by simpa using hloc) hrest it hgood hty L' hmem a ha hlive
      haddr hkind hlen halign
    obtain ⟨cm', hcm', hcm'mem⟩ := ih fuel' { fr with locals := ⟨is.map (fun i => (localName i, localPtr ctx i))⟩ }
      { cm with memory := { cm.memory with allocations := ctx.base ++ L'.set i (kill a) } }
      (L'.set i (kill a)) (by simp at hfuel; omega) rfl hnd rfl
      (by
        intro j hj
        obtain ⟨it', a', hty', hgood', ha', h1, h2, h3, h4, h5⟩ := hok j (by simp [hj])
        have hij : i ≠ j := fun h => hni (h ▸ hj)
        exact ⟨it', a', hty', hgood', by rw [List.getElem?_set_ne hij]; exact ha', h1, h2, h3, h4, h5⟩)
    refine ⟨cm', ?_, ?_⟩
    · rw [deallocAll]
      simp only [hloc, List.map_cons]
      rw [hsd]
      simpa using hcm'
    · rw [hcm'mem, killAt_cons L' i is a ha hni]

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
  have hck : checkValue (.Int v) (.Int it) = .ok () := by simp [checkValue, hv]
  have hne : scalarBytes it (v % 2 ^ (8 * it.size.bytes)).toNat ≠ [] :=
    List.ne_nil_of_length_pos (by omega)
  have hdrop : a.data.drop it.size.bytes = [] := List.drop_eq_nil_of_le (by omega)
  have hrlt : r < ctx.base.length + L.length := by omega
  simp only [typedStore, hck, encode_int it v hgood hv, CM.store, BM.store, hal, BM.check_ptr, hp,
    listIndex, h.allocs]
  obtain ⟨signed, size⟩ := it
  simp [hne, hlive, haddr, Allocation.size, hlen, hblen, writeSubsliceAtIndex, listSet, withMem,
    hdrop, List.set_append_left _ _ hri, hri, hrlt, hai]

end MiniRustSpec.Correspondence
