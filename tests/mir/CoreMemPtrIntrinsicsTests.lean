/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import Lean
import Anneal.Mir.CoreMemPtrIntrinsicsBundle
import MiniRustSpec.CoreMemPtrIntrinsicsMR
import Trusted.Rustc.V2026_08_01.MirSemantics.Machine

/-!
# Episode 2 Dual-Authority Correspondence Tests & Cross-Root Kernel Bridge
# (the 8 core memory & pointer intrinsics)

Verifies `core::intrinsics::{copy, compare_bytes, raw_eq,
typed_swap_nonoverlapping, ptr_offset_from, ptr_offset_from_unsigned, ptr_mask,
black_box}` end-to-end across all three authorities:

1. **Root-Lake witnesses**: positive, UB, flip-direction, and mode-sensitivity
   witnesses on Trusted Anneal (`stepMirFn`) and MiniRust (`Mach`/`MachTB`);
   edge cases on Trusted (`copy` null/misaligned at `count = 0`, `compare_bytes`
   null at `bytes = 0`, `typed_swap_nonoverlapping` overlap and invalid `bool`
   (`kani#5205`), `ptr_mask` without `exposedAllocIds` mutation, diverging calls
   to returning intrinsics); and `V2026_06_01` <-> `V2026_08_01` dialect parity
   on the corpus fixtures (re-elaborated in the `V2026_08_01` AST and executed
   by `Trusted.Rustc.V2026_08_01.MirSemantics.stepMirFn`).
2. **Cross-root kernel bridge (`run_cmd`)**: loads `.lake/build/lib/lean`
   (`Anneal.Mir.CoreMemPtrIntrinsicsBundle`, `MiniRustSpec.CoreMemPtrIntrinsicsMR`)
   and `examples/.lake/build/lib/lean` (`LeanMiriSpec.CoreMemPtrIntrinsicsLM`)
   into one kernel environment, builds the LeanMiri `ObsAuthority` directly over
   `LeanMiriSpec.CoreMemPtrIntrinsicsLM.cmLmObserve`, and kernel-checks the
   unified and all 8 per-intrinsic `DualCorrespondenceBundle`s, the lifted
   theorems, `Eq.refl` locks of all 18 shared fixtures, negative controls each
   paired with an accepted positive control, transitive reachability of
   `Trusted` (`stepMirFn` + the 7 `eval*Call` evaluators), `MiniRustSpec.Interp`,
   and vendored `Miri.Interpreter.{Step.step, Intrinsics.eval}`, and the axiom /
   non-triviality audit.
3. **Constructive audit** of the bundle (`[propext, Quot.sound]`).
-/

/-! ## §0. `V2026_08_01` Renderings of the Corpus Fixtures (dialect parity, §1) -/

namespace Anneal.Mir.CoreMemPtrIntrinsicsTests.V08

open Trusted.Rustc.V2026_08_01 Trusted.Rustc.V2026_08_01.MirAst
open Trusted.Rustc.V2026_08_01.MirSemantics

/-- The `V2026_08_01` rendering of the corpus body builder. -/
def body08 (name : String) (decls : List MirAst.Ty) (argCount : Nat) (f : String)
    (tys : List RigidTy) (args : List Operand) (dest : Nat) (after : List MirAst.Statement)
    (allocs : List CapturedAllocation) : CapturedMir :=
  { defPath := name, phase := .runtimePostCleanup, role := .subject, argCount,
    localDecls := decls.map fun ty => { mutability := .mut, ty, debugName := none },
    basicBlocks :=
      [{ statements := [],
         terminator := { kind := .call (.constant { ty := { kind := .fnDef f tys, layoutIdx := 0 },
                                                       val := .zeroSized })
                                  args { local_ := dest, projection := [] } (some 1) .continue_,
                         span := "ep2.rs:1:1" },
         isCleanup := false },
       { statements := after, terminator := { kind := .return_, span := "ep2.rs:1:1" },
         isCleanup := false }],
    layouts := emptyLayoutTable, allocations := allocs,
    fnAbi := { args := [], ret := { layout := { size := ⟨1⟩, align := ⟨1⟩, backendRepr := .scalar (.initialized (.int 8 true) ⟨0, 255⟩), fields := .primitive, variants := .single 0, isUninhabited := false }, mode := .direct },
               conv := .rust, canUnwind := true } }

def ty (k : RigidTy) : MirAst.Ty := { kind := k, layoutIdx := 0 }
def loc (i : Nat) (proj : List ProjectionElem := []) : Place := { local_ := i, projection := proj }
def usz (n : Nat) : Operand := .constant { ty := ty (.uint .usize), val := .scalar (.int ⟨n, 8⟩) }
def glob (aid : Nat) (bytes : List (Option UInt8)) (al : Nat := 4) : CapturedAllocation :=
  { allocId := aid, bytes, relocations := [], align := ⟨al⟩, mutability := .mut }
def readDeref (i : Nat) : MirAst.Statement :=
  { kind := .assign (loc 0) (.use (.copy (loc i [.deref]))), span := "ep2.rs:1:1" }

def copy08 : CapturedMir :=
  body08 "cm::copy_u32" [ty (.uint .u32), ty (.rawPtr .not (.uint .u32)), ty (.rawPtr .mut (.uint .u32)),
    ty (.tuple [])] 2 "core::intrinsics::copy" [.uint .u32] [.copy (loc 1), .copy (loc 2), usz 1] 3
    [readDeref 2] [glob 100 [some 42, some 0, some 0, some 0], glob 101 [some 1, some 2, some 3, some 4]]
def copyMode08 : CapturedMir :=
  body08 "cm::copy_mode" [ty (.uint .u32), ty (.rawPtr .not (.uint .u32)), ty (.rawPtr .mut (.uint .u32)),
    ty (.uint .u32), ty (.tuple [])] 2 "core::intrinsics::copy" [.uint .u32]
    [.copy (loc 1), .copy (loc 2), usz 1] 4
    [{ kind := .assign (loc 0) (.use (.copy (loc 3))), span := "ep2.rs:1:1" }]
    [glob 100 [some 42, some 0, some 0, some 0]]
def cmp08 : CapturedMir :=
  body08 "cm::compare_bytes_3" [ty (.int .i32), ty (.rawPtr .not (.uint .u8)), ty (.rawPtr .not (.uint .u8))] 2
    "core::intrinsics::compare_bytes" [] [.copy (loc 1), .copy (loc 2), usz 3] 0 []
    [glob 100 [some 1, some 2, some 3] 1, glob 101 [some 1, some 2, some 4] 1, glob 102 [some 2, some 0, none] 1]
def rawEq08 : CapturedMir :=
  body08 "cm::raw_eq_u32" [ty .bool, ty (.ref .not (.uint .u32)), ty (.ref .not (.uint .u32))] 2
    "core::intrinsics::raw_eq" [.uint .u32] [.copy (loc 1), .copy (loc 2)] 0 []
    [glob 100 [some 7, some 0, some 0, some 0], glob 101 [some 7, some 0, some 0, some 0],
     glob 103 [some 7, none, some 0, some 0]]
def swap08 : CapturedMir :=
  body08 "cm::typed_swap_read_x" [ty (.uint .u32), ty (.rawPtr .mut (.uint .u32)), ty (.rawPtr .mut (.uint .u32)),
    ty (.tuple [])] 2 "core::intrinsics::typed_swap_nonoverlapping" [.uint .u32] [.copy (loc 1), .copy (loc 2)] 3
    [readDeref 1] [glob 100 [some 7, some 0, some 0, some 0], glob 101 [some 9, some 0, some 0, some 0]]
def swapMode08 : CapturedMir :=
  body08 "cm::typed_swap_mode" [ty (.uint .u32), ty (.rawPtr .mut (.uint .u32)), ty (.rawPtr .mut (.uint .u32)),
    ty (.uint .u32), ty (.tuple [])] 2 "core::intrinsics::typed_swap_nonoverlapping" [.uint .u32]
    [.copy (loc 1), .copy (loc 2)] 4 [readDeref 1] [glob 100 [some 7, some 0, some 0, some 0]]
def pof08 (unsigned : Bool) : CapturedMir :=
  body08 "cm::pof" [ty (if unsigned then .uint .usize else .int .isize), ty (.rawPtr .not (.uint .u32)),
    ty (.rawPtr .not (.uint .u32))] 2
    (if unsigned then "core::intrinsics::ptr_offset_from_unsigned" else "core::intrinsics::ptr_offset_from")
    [.uint .u32] [.copy (loc 1), .copy (loc 2)] 0 [] [glob 100 (List.replicate 16 (some 0)), glob 101 (List.replicate 16 (some 0))]
def mask08 : CapturedMir :=
  body08 "cm::ptr_mask_not7" [ty (.rawPtr .not (.uint .u32)), ty (.rawPtr .not (.uint .u32))] 1
    "core::intrinsics::ptr_mask" [.uint .u32] [.copy (loc 1), usz (2 ^ 64 - 8)] 0 [] [glob 100 (List.replicate 16 (some 0)) 16]
def bb08 : CapturedMir :=
  body08 "cm::black_box_u32" [ty (.uint .u32), ty (.uint .u32)] 1 "core::intrinsics::black_box" [.uint .u32]
    [.copy (loc 1)] 0 [] []

/-- Initial `V2026_08_01` state with all locals live. -/
def init08 (body : CapturedMir) (args : List Value) : MachineState :=
  let base := initMachineState body args
  { base with frame := { base.frame with locals := base.frame.locals.map fun
      | .dead => .uninit
      | slot => slot } }

/-- Mode-sensitive `V2026_08_01` state for `copyMode08` or `swapMode08`. -/
def modeInit08 (body : CapturedMir) (local3Val : Nat) (protectedMode : Bool) : MachineState :=
  let base := init08 body [.ptr ⟨100, 0⟩ 8, .ptr ⟨2, 0⟩ 8]
  let b1 : BorrowEntry :=
    { tag := 1, targetLocal := 3, targetProjection := [], perm := TreeBorrowPerm.frozen,
      rangeOffset := 0, rangeLen := 4, protector := (if protectedMode then some 1 else none),
      parentTag := none, targetFrameDepth := 0, allocDead := false }
  let b2 : BorrowEntry :=
    { tag := 2, targetLocal := 3, targetProjection := [], perm := TreeBorrowPerm.unique,
      rangeOffset := 0, rangeLen := 4, protector := none, parentTag := none,
      targetFrameDepth := 0, allocDead := false }
  { base with
    frame := { base.frame with
      locals := [.uninit, .init (.ptr ⟨100, 0⟩ 8), .init (.ptr ⟨2, 0⟩ 8),
                 .init (.scalar ⟨local3Val, 4⟩), .uninit] },
    memory := { base.memory with
      borrows := [b1, b2], nextTag := 3,
      activeProtectors := (if protectedMode then [1] else []) } }

/-- Bounded `V2026_08_01` `stepMirFn` run, observed in the shared observation type. -/
def run08 (body : CapturedMir) : Nat → MachineState → MiniRustSpec.CoreMemPtrIntrinsicsMR.CmTrustedObs
  | 0, _ => .stuck
  | n + 1, s =>
    match stepMirFn body s with
    | .tau (.running s') => run08 body n s'
    | .ret (.normal r) =>
      match r.1 with
      | .scalar sc => .scalar sc.bits sc.sizeBytes
      | .ptr p 8 => .ptr p.allocId p.offsetBytes
      | _ => .stuck
    | .vis (.inl (.fail .ub)) _ => .ub
    | .vis (.inl (.fail .unsupported)) _ => .unsupported
    | _ => .stuck

def gp (aid off : Nat) : Value := .ptr ⟨aid, off⟩ 8

/-! ### `V2026_08_01` renderings of the hardened edge-case fixtures -/

def ip (addr : Nat) : Value := .ptr ⟨0, addr⟩ 8
def ret7 : MirAst.Statement :=
  { kind := .assign (loc 0) (.use (.constant { ty := ty (.uint .u32), val := .scalar (.int ⟨7, 4⟩) })),
    span := "ep2.rs:1:1" }
/-- `copy::<u32>(_1, _2, 0); _0 = 7u32`. -/
def copy0_08 : CapturedMir :=
  body08 "cm::copy_0" [ty (.uint .u32), ty (.rawPtr .not (.uint .u32)), ty (.rawPtr .mut (.uint .u32)),
    ty (.tuple [])] 2 "core::intrinsics::copy" [.uint .u32] [.copy (loc 1), .copy (loc 2), usz 0] 3 [ret7] []
/-- `compare_bytes(_1, _2, 0)`. -/
def cmp0_08 : CapturedMir :=
  body08 "cm::compare_bytes_0" [ty (.int .i32), ty (.rawPtr .not (.uint .u8)), ty (.rawPtr .not (.uint .u8))] 2
    "core::intrinsics::compare_bytes" [] [.copy (loc 1), .copy (loc 2), usz 0] 0 [] []
/-- `typed_swap_nonoverlapping::<()>(_1, _2); _0 = 7u32`. -/
def swapZst08 : CapturedMir :=
  body08 "cm::typed_swap_zst" [ty (.uint .u32), ty (.rawPtr .mut (.tuple [])), ty (.rawPtr .mut (.tuple [])),
    ty (.tuple [])] 2 "core::intrinsics::typed_swap_nonoverlapping" [.tuple []]
    [.copy (loc 1), .copy (loc 2)] 3 [ret7] []
/-- `typed_swap_nonoverlapping::<u32>` within one global `100 = [5u32, 6u32]`. -/
def swapSame08 : CapturedMir :=
  body08 "cm::typed_swap_same_alloc" [ty (.uint .u32), ty (.rawPtr .mut (.uint .u32)),
    ty (.rawPtr .mut (.uint .u32)), ty (.tuple [])] 2 "core::intrinsics::typed_swap_nonoverlapping" [.uint .u32]
    [.copy (loc 1), .copy (loc 2)] 3 [readDeref 1]
    [glob 100 [some 5, some 0, some 0, some 0, some 6, some 0, some 0, some 0]]
/-- `typed_swap_nonoverlapping::<bool>` with `100 = 2` (invalid) and `101 = 1`. -/
def swapBool08 : CapturedMir :=
  body08 "cm::typed_swap_bool" [ty .bool, ty (.rawPtr .mut .bool), ty (.rawPtr .mut .bool), ty (.tuple [])] 2
    "core::intrinsics::typed_swap_nonoverlapping" [.bool] [.copy (loc 1), .copy (loc 2)] 3 [readDeref 1]
    [glob 100 [some 2] 1, glob 101 [some 1] 1]
/-- `ptr_offset_from::<()>(_1, _2)` (ZST). -/
def pofZst08 : CapturedMir :=
  body08 "cm::pof_zst" [ty (.int .isize), ty (.rawPtr .not (.tuple [])), ty (.rawPtr .not (.tuple []))] 2
    "core::intrinsics::ptr_offset_from" [.tuple []] [.copy (loc 1), .copy (loc 2)] 0 [] []
/-- `ptr_mask::<u32>(_1, mask)` over the 16-aligned global `100`. -/
def maskWith08 (mask : Nat) : CapturedMir :=
  body08 "cm::ptr_mask" [ty (.rawPtr .not (.uint .u32)), ty (.rawPtr .not (.uint .u32))] 1
    "core::intrinsics::ptr_mask" [.uint .u32] [.copy (loc 1), usz mask] 0 []
    [glob 100 (List.replicate 16 (some 0)) 16]
/-- `black_box::<bool>(_1)`. -/
def bbBool08 : CapturedMir :=
  body08 "cm::black_box_bool" [ty .bool, ty .bool] 1 "core::intrinsics::black_box" [.bool] [.copy (loc 1)] 0 [] []
/-- Diverging (`target = none`) call to returning intrinsic `raw_eq::<u32>` (parity for `cmRawEqDivergingMir`). -/
def rawEqDiv08 : CapturedMir :=
  { body08 "cm::raw_eq_diverging" [ty .bool, ty (.ref .not (.uint .u32)), ty (.ref .not (.uint .u32))] 2
      "core::intrinsics::raw_eq" [.uint .u32] [.copy (loc 1), .copy (loc 2)] 0 []
      [glob 100 [some 7, some 0, some 0, some 0], glob 101 [some 7, some 0, some 0, some 0]] with
    basicBlocks :=
      [{ statements := [],
         terminator := { kind := .call (.constant { ty := ty (.fnDef "core::intrinsics::raw_eq" [.uint .u32]),
                                                    val := .zeroSized })
                           [.copy (loc 1), .copy (loc 2)] (loc 0) none .continue_,
                         span := "ep2.rs:1:1" },
         isCleanup := false }] }
/-- `raw_eq::<&!>` (layout-inhabited reference to `!`). -/
def rawEqRefNever08 : CapturedMir :=
  body08 "cm::raw_eq_ref_never" [ty .bool, ty (.ref .not (.ref .not .never)), ty (.ref .not (.ref .not .never))] 2
    "core::intrinsics::raw_eq" [.ref .not .never] [.copy (loc 1), .copy (loc 2)] 0 []
    [glob 100 [some 0x20, some 0, some 0, some 0, some 0, some 0, some 0, some 0] 8,
     glob 101 [some 0x20, some 0, some 0, some 0, some 0, some 0, some 0, some 0] 8]
/-- `raw_eq::<!>` (layout-uninhabited `!` -> `.ub`). -/
def rawEqNever08 : CapturedMir :=
  body08 "cm::raw_eq_never" [ty .bool, ty (.ref .not .never), ty (.ref .not .never)] 2
    "core::intrinsics::raw_eq" [.never] [.copy (loc 1), .copy (loc 2)] 0 [] []
/-- `black_box::<&!>(_1)` (uninhabited pointee -> `.ub`). -/
def bbRefNever08 : CapturedMir :=
  body08 "cm::bb_ref_never" [ty (.ref .not .never), ty (.ref .not .never)] 1
    "core::intrinsics::black_box" [.ref .not .never] [.copy (loc 1)] 0 [] []
/-- `black_box::<&&!>(_1)` (pointer to `&!` -> accepted). -/
def bbRefRefNever08 : CapturedMir :=
  body08 "cm::bb_ref_ref_never" [ty (.ref .not (.ref .not .never)), ty (.ref .not (.ref .not .never))] 1
    "core::intrinsics::black_box" [.ref .not (.ref .not .never)] [.copy (loc 1)] 0 [] []
/-- `black_box::<&[u8]>(_1)` (null wide ref -> `.ub`). -/
def bbWideNull08 : CapturedMir :=
  body08 "cm::bb_wide_null" [ty (.ref .not (.slice (.uint .u8))), ty (.ref .not (.slice (.uint .u8)))] 1
    "core::intrinsics::black_box" [.ref .not (.slice (.uint .u8))] [.copy (loc 1)] 0 [] []
/-- `black_box::<fn()>(_1)` (null fn ptr -> `.ub`). -/
def bbFnNull08 : CapturedMir :=
  body08 "cm::bb_fn_null"
    [ty (.fnPtr [] (.tuple []) .safe .rust), ty (.fnPtr [] (.tuple []) .safe .rust)] 1
    "core::intrinsics::black_box" [.fnPtr [] (.tuple []) .safe .rust] [.copy (loc 1)] 0 [] []
def ctFn08 : Operand := .constant { ty := ty (.fnDef "cm::ct_dummy" []), val := .zeroSized }
/-- `const_eval_select` forwarding to `raw_eq::<u32>`, `ptr_mask::<u32>`, `black_box::<u32>`, and diverging. -/
def cesRawEq08 : CapturedMir :=
  body08 "cm::ces_raw_eq" [ty .bool, ty (.tuple [.ref .not (.uint .u32), .ref .not (.uint .u32)])] 1
    "core::intrinsics::const_eval_select"
    [.tuple [.ref .not (.uint .u32), .ref .not (.uint .u32)], .fnDef "cm::ct_dummy" [],
     .fnDef "core::intrinsics::raw_eq" [.uint .u32], .bool]
    [.copy (loc 1), ctFn08, .constant { ty := ty (.fnDef "core::intrinsics::raw_eq" [.uint .u32]), val := .zeroSized }]
    0 [] [glob 100 [some 7, some 0, some 0, some 0], glob 101 [some 7, some 0, some 0, some 0]]
def cesMask08 : CapturedMir :=
  body08 "cm::ces_ptr_mask" [ty (.rawPtr .not (.uint .u32)), ty (.tuple [.rawPtr .not (.uint .u32), .uint .usize])] 1
    "core::intrinsics::const_eval_select"
    [.tuple [.rawPtr .not (.uint .u32), .uint .usize], .fnDef "cm::ct_dummy" [],
     .fnDef "core::intrinsics::ptr_mask" [.uint .u32], .rawPtr .not (.uint .u32)]
    [.copy (loc 1), ctFn08, .constant { ty := ty (.fnDef "core::intrinsics::ptr_mask" [.uint .u32]), val := .zeroSized }]
    0 [] [glob 100 (List.replicate 16 (some 0)) 16]
def cesBb08 : CapturedMir :=
  body08 "cm::ces_black_box" [ty (.uint .u32), ty (.tuple [.uint .u32])] 1
    "core::intrinsics::const_eval_select"
    [.tuple [.uint .u32], .fnDef "cm::ct_dummy" [],
     .fnDef "core::intrinsics::black_box" [.uint .u32], .uint .u32]
    [.copy (loc 1), ctFn08, .constant { ty := ty (.fnDef "core::intrinsics::black_box" [.uint .u32]), val := .zeroSized }]
    0 [] []
def cesDiv08 : CapturedMir :=
  { body08 "cm::ces_diverging" [ty .never, ty (.tuple [])] 1
      "core::intrinsics::const_eval_select" [.tuple [], .fnDef "cm::ct_dummy" [], .fnDef "cm::rt_div" [], .never]
      [.copy (loc 1), ctFn08, .constant { ty := ty (.fnDef "cm::rt_div" []), val := .zeroSized }] 0 [] [] with
    basicBlocks :=
      [{ statements := [],
         terminator := { kind := .call
                           (.constant { ty := ty (.fnDef "core::intrinsics::const_eval_select"
                                          [.tuple [], .fnDef "cm::ct_dummy" [], .fnDef "cm::rt_div" [], .never]),
                                        val := .zeroSized })
                           [.copy (loc 1), ctFn08,
                            .constant { ty := ty (.fnDef "cm::rt_div" []), val := .zeroSized }]
                           (loc 0) none .continue_,
                         span := "ep2.rs:1:1" },
         isCleanup := false }] }

end Anneal.Mir.CoreMemPtrIntrinsicsTests.V08

namespace Anneal.Mir.CoreMemPtrIntrinsicsTests

open Anneal.DualCorrespondenceBundle
open Anneal.Mir.CoreMemPtrIntrinsicsBundle
open Trusted.Rustc.V2026_06_01 Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open MiniRustSpec MiniRustSpec.Gen MiniRustSpec.Interp
open MiniRustSpec.Correspondence
open MiniRustSpec.Correspondence.RefWitness
open MiniRustSpec.UnwindSetDiscrAndFnPtrMR
open MiniRustSpec.CoreMemPtrIntrinsicsMR

/-! ## §1. Root-Lake Witnesses -/

/-- Constructive codec laws & tight validity witness for `cmCodec`. -/
theorem cm_codec_constructive_laws :
    cmCodec.decode (cmCodec.encode (.scalar 42 4)) = some (.scalar 42 4) ∧
    cmCodec.decode (cmCodec.encode (.ptr 100 8)) = some (.ptr 100 8) ∧
    cmCodec.decode (7, 0, 0) = none ∧
    cmCodec.TightValidRep :=
  ⟨rfl, rfl, rfl, cmCodec_tight⟩

/-- Every one of the 8 intrinsics has a non-vacuous positive normal return AND a
non-vacuous UB fault on BOTH Trusted Anneal and MiniRust (each conjunct
evaluated by the kernel running `stepMirFn`, respectively `Interp.steps`). -/
theorem cm_all_8_intrinsics_flip_verdict :
    ∀ v : CmVariant,
      (∃ a, cmAnnealEval .basic v .okPrimary () = some (.returns a) ∧
            mrAuthority.verdict (.basic, v, .okPrimary) = some (.returns a)) ∧
      cmAnnealEval .basic v .ubFault () = some .undefinedBehavior ∧
      mrAuthority.verdict (.basic, v, .ubFault) = some .undefinedBehavior := by
  intro v
  cases v with
  | copy => exact ⟨⟨.scalar 42 4, by decide +kernel, by decide +kernel⟩, by decide +kernel, by decide +kernel⟩
  | compareBytes =>
    exact ⟨⟨.scalar 0xFFFFFFFF 4, by decide +kernel, by decide +kernel⟩, by decide +kernel, by decide +kernel⟩
  | rawEq => exact ⟨⟨.scalar 1 1, by decide +kernel, by decide +kernel⟩, by decide +kernel, by decide +kernel⟩
  | typedSwap => exact ⟨⟨.scalar 9 4, by decide +kernel, by decide +kernel⟩, by decide +kernel, by decide +kernel⟩
  | ptrOffsetFrom => exact ⟨⟨.scalar 2 8, by decide +kernel, by decide +kernel⟩, by decide +kernel, by decide +kernel⟩
  | ptrOffsetFromUnsigned =>
    exact ⟨⟨.scalar 2 8, by decide +kernel, by decide +kernel⟩, by decide +kernel, by decide +kernel⟩
  | ptrMask => exact ⟨⟨.ptr 100 8, by decide +kernel, by decide +kernel⟩, by decide +kernel, by decide +kernel⟩
  | blackBox => exact ⟨⟨.scalar 77 4, by decide +kernel, by decide +kernel⟩, by decide +kernel, by decide +kernel⟩

/-- Genuine mode sensitivity across Trusted Anneal and MiniRust on BOTH `copy`
and `typed_swap_nonoverlapping`: `basic` / `BasicMemory` returns (`42`, `9`)
while `protectedTB` / `TreeBorrowsMemory` faults `.undefinedBehavior`. -/
theorem cm_copy_mode_sensitivity_root :
    cmAnnealEval .basic .copy .modeCase () = some (.returns (.scalar 42 4)) ∧
    mrAuthority.verdict (.basic, .copy, .modeCase) = some (.returns (.scalar 42 4)) ∧
    cmAnnealEval .protectedTB .copy .modeCase () = some .undefinedBehavior ∧
    mrAuthority.verdict (.protectedTB, .copy, .modeCase) = some .undefinedBehavior ∧
    (mrSide.flipW cmModel mrSide_check).isSome = true ∧
    cmAnnealEval .basic .typedSwap .modeCase () = some (.returns (.scalar 9 4)) ∧
    mrAuthority.verdict (.basic, .typedSwap, .modeCase) = some (.returns (.scalar 9 4)) ∧
    cmAnnealEval .protectedTB .typedSwap .modeCase () = some .undefinedBehavior ∧
    mrAuthority.verdict (.protectedTB, .typedSwap, .modeCase) = some .undefinedBehavior ∧
    ((mrVariantSide .typedSwap).flipW cmModel (mrVariantSide_check .typedSwap)).isSome = true :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
   mr_modeSensitivity_present,
   by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
   mr_typedSwap_modeSensitivity_present⟩

/-- Both root-Lake authorities realize the frozen 64-key verdict table. -/
theorem cm_two_authority_table_root (mode : CmMode) (v : CmVariant) (c : CmCase) :
    cmAnnealEval mode v c () = cmExpectedVerdict mode v c ∧
    mrAuthority.verdict (mode, v, c) = cmExpectedVerdict mode v c :=
  ⟨cmAnnealEval_eq mode v c (), mrAuthority_verdict_eq mode v c⟩

/-- Re-exported MR universal laws and witnesses (reachable from this module). -/
theorem cm_mr_deep_theorems_used :
    cmMrObsDictDistinct = true ∧
    cmMrObserve .basicMemory .copy .modeCase =
      .retBytes ((scalarBytes cmU32It 42).map (projByteTB ∘ liftByteTB)) ∧
    cmMrObserve .treeBorrows .copy .modeCase = .ub ∧
    cmMrObserve .basicMemory .typedSwap .modeCase =
      .retBytes ((scalarBytes cmU32It 9).map (projByteTB ∘ liftByteTB)) ∧
    cmMrObserve .treeBorrows .typedSwap .modeCase = .ub := by
  have _ := @cm_classify_core_mem_ptr_intrinsics
  have _ := @cm_evalCoreMemPtrIntrinsicCall?_routes
  have _ := @cm_compareUnsignedBytesI32_refl
  have _ := @cm_compareUnsignedBytesI32_range
  have _ := @cm_compareUnsignedBytesI32_antisymm
  have _ := @cm_evalPtrOffsetFromDistance_same_offset
  have _ := @cm_evalPtrOffsetFromDistance_zst
  have _ := @cm_evalPtrOffsetFromDistance_unsigned_negative
  have _ := @cm_evalPtrOffsetFromDistance_exact
  have _ := @cm_evalPtrOffsetFromDistance_neg_exact
  have _ := @cm_evalPtrOffsetFromDistance_isize_min_ub
  have _ := @cm_evalPtrOffsetFromDistance_nondiv_ub
  have _ := @cm_evalPtrOffsetFromDistance_oversized_elem_ub
  have _ := @cm_divExact_byte_distance
  have _ := @cm_bitwiseAndBits_testBit
  have _ := @cm_bitwiseAndBits_allOnes
  have _ := @cm_bitwiseAndBits_baseAddr_invariant
  have _ := @cm_evalPtrMaskCall_identity
  have _ := @cm_writeReturnDestination_preserves_exposed
  have _ := @cm_evalPtrMaskCall_preserves_exposed
  have _ := @cm_evalPtrMaskCall_direct_preserves_exposed
  have _ := @cm_minirust_rawEq_evalIntrinsic
  have _ := @cm_minirust_loadRawData_uninit_ub
  have _ := @cm_mr_listByteEq_eq_beq
  have _ := @cm_minirust_rawEq_eq_trusted_listByteEq
  have _ := @cm_minirust_evalPtrOffsetFrom_divExact_agree
  have _ := @cm_minirust_evalPtrOffsetFrom_neg_divExact_agree
  have _ := @cm_minirust_evalPtrOffsetFrom_unsigned_underflow_ub
  have _ := @cm_minirust_evalPtrOffset_wrapping_preserves_prov
  have _ := @cm_minirust_bytes_uninit_iff
  have _ := @cm_evalBlackBoxCall_u32_valid
  have _ := @cm_evalBlackBoxCall_invalid_bool_ub
  have _ := @cm_evalBlackBoxCall_rawPtr_preserves_prov
  have _ := @cm_minirust_loadRawDataM_tb_wfLive
  have _ := @cm_minirust_rawEq_evalIntrinsicM
  have _ := @cm_minirust_rawEq_evalIntrinsicM_eq_trusted_listByteEq
  have _ := @cm_minirust_rawEq_evalIntrinsicM_tb_wfLive
  have _ := @cm_minirust_evalPtrOffsetFromM_pos_neg_underflow_agree
  have _ := @cm_minirust_evalPtrOffsetM_wrapping_preserves_prov
  have _ := @cm_minirust_copy_snapshot_memmove_tb_wfLive
  have _ := @cm_minirust_typedSwap_four_access_tb_wfLive
  have _ := @cm_minirust_compareBytes_uninit_and_eq_iff
  have _ := @cm_minirust_stepsTB_wfLive_all_ok
  have _ := @cm_copy_three_way_witness
  have _ := @cm_compareBytes_three_way_witness
  have _ := @cm_rawEq_three_way_witness
  have _ := @cm_typedSwap_three_way_witness
  have _ := @cm_ptrOffsetFrom_three_way_witness
  have _ := @cm_ptrOffsetFromUnsigned_three_way_witness
  have _ := @cm_ptrMask_three_way_witness
  have _ := @cm_blackBox_three_way_witness
  have _ := @cm_rawEq_padded_struct_three_way_witness
  have _ := @cm_copy_tb_read_then_write_witness
  have _ := @cm_typedSwap_invalid_bool_three_way_witness
  have _ := @cmTrustedObserve_table
  have _ := @cmMrObserveClass_table
  have _ := @cm_variant_outcomes_distinct
  exact ⟨cmMrObsDict_distinct, cmMrObserve_copy_mode_sensitivity.1,
    cmMrObserve_copy_mode_sensitivity.2, cmMrObserve_typedSwap_mode_sensitivity.1,
    cmMrObserve_typedSwap_mode_sensitivity.2⟩

/-! ### Trusted edge cases (`V2026_06_01`) -/

/-- Run `stepMirFn` and observe the returned memory's exposed allocation ids. -/
def cmRunTrustedExposed (body : CapturedMir) : Nat → MachineState → Option (List Nat)
  | 0, _ => none
  | n + 1, s =>
    match stepMirFn body s with
    | .tau (.running s') => cmRunTrustedExposed body n s'
    | .ret (.normal r) => some r.2.exposedAllocIds
    | _ => none

/-- A diverging (`target = none`) call to a returning intrinsic. -/
def cmRawEqDivergingMir : CapturedMir :=
  { mkMirBody "cm::raw_eq_diverging" [mkDecl boolMirTy, mkDecl cmRefU32Ty, mkDecl cmRefU32Ty] 2
      [mkBb [] (.call (cmIntrinsicOp "core::intrinsics::raw_eq" [.uint .u32])
        [.copy (locPlace 1), .copy (locPlace 2)] (locPlace 0) none .continue_)] with
    allocations := [cmGlobal 100 (cmU32Bytes 7), cmGlobal 101 (cmU32Bytes 7)] }

/-- `typed_swap_nonoverlapping::<bool>` over a global holding an invalid `bool`
(`2`) and a valid one. -/
def cmSwapBoolMir : CapturedMir :=
  cmCallBody "cm::typed_swap_bool"
    [mkDecl boolMirTy, mkDecl { kind := .rawPtr .mut .bool, layoutIdx := 0 },
     mkDecl { kind := .rawPtr .mut .bool, layoutIdx := 0 }, mkDecl unitMirTy] 2
    (cmIntrinsicOp "core::intrinsics::typed_swap_nonoverlapping" [.bool])
    [.copy (locPlace 1), .copy (locPlace 2)] 3
    [mkSt (.assign (locPlace 0) (.use (.copy (locPlace 1 [.deref]))))]
    [cmGlobal 100 [some 2] 1, cmGlobal 101 [some 1] 1]

/-- **Trusted edge cases on `stepMirFn`**:
1. `copy::<u32>` with null pointers at `count = 0` completes (alignment checked,
   validity exempted); with a misaligned source at `count = 0` it is UB;
2. `compare_bytes` with null pointers at `bytes = 0` is UB (deliberate delta);
3. `typed_swap_nonoverlapping::<u32>` on overlapping ranges (`&G[0]`, `&G[2]`)
   is UB, while disjoint elements of one allocation swap (`okSecondary`);
4. `typed_swap_nonoverlapping::<bool>` with an invalid `bool` (`2`) is UB
   (`kani#5205` typed validity);
5. `typed_swap_nonoverlapping::<()>` with null pointers is UB (deliberate delta);
6. `ptr_mask` returns a pointer with the SAME provenance and leaves
   `exposedAllocIds` empty (no `expose`, `ucg#630`);
7. a diverging (`target = none`) call to the returning intrinsic `raw_eq` is UB. -/
theorem cm_trusted_edge_cases :
    cmRunTrusted cmCopy0Mir 8 (cmInitLiveState cmCopy0Mir [cmIntPtr 0, cmIntPtr 0]) = .scalar 7 4 ∧
    cmRunTrusted cmCopy0Mir 8 (cmInitLiveState cmCopy0Mir [cmIntPtr 2, cmIntPtr 0]) = .ub ∧
    cmRunTrusted cmCmpBytes0Mir 8 (cmInitLiveState cmCmpBytes0Mir [cmIntPtr 0, cmIntPtr 0]) = .ub ∧
    cmRunTrusted cmSwapSameAllocMir 8
      (cmInitLiveState cmSwapSameAllocMir [cmGPtr 100 0, cmGPtr 100 2]) = .ub ∧
    cmRunTrusted cmSwapBoolMir 8 (cmInitLiveState cmSwapBoolMir [cmGPtr 100 0, cmGPtr 101 0]) = .ub ∧
    cmRunTrusted cmSwapZstMir 8 (cmInitLiveState cmSwapZstMir [cmIntPtr 0, cmIntPtr 0]) = .ub ∧
    cmRunTrustedExposed cmMaskAlign8Mir 8 (cmInitLiveState cmMaskAlign8Mir [cmGPtr 100 12]) = some [] ∧
    cmRunTrusted cmRawEqDivergingMir 8
      (cmInitLiveState cmRawEqDivergingMir [cmGPtr 100 0, cmGPtr 101 0]) = .ub := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- Layout table for `MaybeUninit<(u8, u32)>` (entry `0`: `()`, entry `1`: `(u8, u32)`
size 8 align 4 offsets `[0, 4]`, entry `2`: union `MaybeUninit<(u8, u32)>` with
`fieldLayouts = [0, 1]`, entry `3`: `MaybeUninit<u8>`, entry `4`: `[MaybeUninit<u8>; 2]`,
entry `5`: `(u32, MaybeUninit<u32>)`, entry `6`: `MaybeUninit<u32>`, entry `7`: `u8`,
entry `8`: `u32`, entry `9`: `[u8; 16]` align 4). -/
def cmHardenedLayouts : Trusted.Rustc.V2026_06_01.Layout.LayoutTable :=
  let u8L : Trusted.Rustc.V2026_06_01.Layout.TypeLayout :=
    { size := ⟨1⟩, align := ⟨1⟩, fields := .primitive, variants := .single 0,
      backendRepr := .scalar (.initialized (.int 8 false) ⟨0, 255⟩),
      isUninhabited := false, fieldLayouts := [] }
  let u32L : Trusted.Rustc.V2026_06_01.Layout.TypeLayout :=
    { size := ⟨4⟩, align := ⟨4⟩, fields := .primitive, variants := .single 0,
      backendRepr := .scalar (.initialized (.int 32 false) ⟨0, 0xFFFFFFFF⟩),
      isUninhabited := false, fieldLayouts := [] }
  let unitL : Trusted.Rustc.V2026_06_01.Layout.TypeLayout :=
    { size := ⟨0⟩, align := ⟨1⟩, fields := .arbitrary [] [], variants := .single 0,
      backendRepr := .memory, isUninhabited := false, fieldLayouts := [] }
  let padL : Trusted.Rustc.V2026_06_01.Layout.TypeLayout :=
    { size := ⟨8⟩, align := ⟨4⟩, fields := .arbitrary [⟨0⟩, ⟨4⟩] [0, 1], variants := .single 0,
      backendRepr := .scalarPair (.initialized (.int 8 false) ⟨0, 255⟩)
        (.initialized (.int 32 false) ⟨0, 0xFFFFFFFF⟩),
      isUninhabited := false, fieldLayouts := [7, 8] }
  let muPadL : Trusted.Rustc.V2026_06_01.Layout.TypeLayout :=
    { size := ⟨8⟩, align := ⟨4⟩, fields := .union 2, variants := .single 0,
      backendRepr := .memory, isUninhabited := false, fieldLayouts := [0, 1] }
  let muU8L : Trusted.Rustc.V2026_06_01.Layout.TypeLayout :=
    { size := ⟨1⟩, align := ⟨1⟩, fields := .union 2, variants := .single 0,
      backendRepr := .scalar (.union (.int 8 false)), isUninhabited := false, fieldLayouts := [0, 7] }
  let arrMuU8L : Trusted.Rustc.V2026_06_01.Layout.TypeLayout :=
    { size := ⟨2⟩, align := ⟨1⟩, fields := .array ⟨1⟩ 2, variants := .single 0,
      backendRepr := .memory, isUninhabited := false, fieldLayouts := [3] }
  let muU32L : Trusted.Rustc.V2026_06_01.Layout.TypeLayout :=
    { size := ⟨4⟩, align := ⟨4⟩, fields := .union 2, variants := .single 0,
      backendRepr := .scalar (.union (.int 32 false)), isUninhabited := false, fieldLayouts := [0, 8] }
  let tupMuU32L : Trusted.Rustc.V2026_06_01.Layout.TypeLayout :=
    { size := ⟨8⟩, align := ⟨4⟩, fields := .arbitrary [⟨0⟩, ⟨4⟩] [0, 1], variants := .single 0,
      backendRepr := .memory, isUninhabited := false, fieldLayouts := [8, 6] }
  let buf16L : Trusted.Rustc.V2026_06_01.Layout.TypeLayout :=
    { size := ⟨16⟩, align := ⟨4⟩, fields := .array ⟨1⟩ 16, variants := .single 0,
      backendRepr := .memory, isUninhabited := false, fieldLayouts := [7] }
  Trusted.Rustc.V2026_06_01.Layout.LayoutTable.mk 64 true
    [unitL, padL, muPadL, muU8L, arrMuU8L, tupMuU32L, muU32L, u8L, u32L, buf16L]

/-- **Hardened Episode 1/2 edge-case witnesses on `V2026_06_01.MirSemantics.stepMirFn`**:
1. `compare_bytes` eager `.uninit`-before-provenance: a slice carrying a relocated
   pointer at bytes `0..8` followed by `.uninit` at byte `8` deterministically
   faults `.ub` (never `.unsupported`);
2. `raw_eq::<&!>` returns `true` (`&!` is layout-inhabited), while `raw_eq::<!>`
   faults `.ub` (`!` is layout-uninhabited);
3. `typed_swap_nonoverlapping`:
   (a) global padding reset on `(u8, u32)` clears padding bytes `1..3` to `.uninit`
       (subsequent `compare_bytes(..., 4)` faults `.ub`, while byte `0` equals `2`);
   (b) stack byte-buffer (`[u8; 16]` align 4) padding reset clears padding bytes
       `1..3` to `.uninit`;
   (c) union `MaybeUninit<(u8, u32)>` common-padding reset clears bytes `1..3` to
       `.uninit`;
   (d) invalid surrogate `char` (`0xD800`) faults `.ub` (`kani#5205`);
4. `ptr_offset_from`:
   (a) `isize::MIN` (`0` vs `2^63`) faults `.ub`;
   (b) ZST `()` faults `.ub`;
   (c) dead-tag borrow-first resolution: two distinct dead tags at differing
       offsets fault `.ub`, at equal offsets fail closed `.unsupported`, and a
       dead tag colliding with live global id `100` faults `.ub` against live
       global `100` (never adopts global `100`);
5. `ptr_mask`:
   (a) mask `!31` on 16-aligned global `100` fails closed `.unsupported` (touches
       unknown symbolic base bits);
   (b) dead tag `100` colliding with live 16-aligned global `100` fails closed
       `.unsupported` on mask `!7` (never adopts global `100`'s alignment);
   (c) identity mask `usize::MAX` succeeds even on a dead borrow tag;
6. `black_box`:
   (a) `[MaybeUninit<u8>; 2]` with `.uninit` succeeds;
   (b) `(u32, MaybeUninit<u32>)` with `.uninit` field succeeds;
   (c) null wide `&[u8]` faults `.ub`;
   (d) null `fn()` faults `.ub`;
   (e) `&!` faults `.ub`, while `&&!` succeeds;
7. `const_eval_select`:
   (a) runtime forwarding to `raw_eq`, `ptr_mask`, and `black_box` executes inline
       (never escapes to `extCall`);
   (b) diverging `const_eval_select` (`target = none`) fails closed `.unsupported`
       (never `.ub`). -/
theorem cm_trusted_hardened_edge_cases :
    -- 1. compare_bytes eager .uninit before provenance
    let gProvUninit : CapturedAllocation :=
      { allocId := 100,
        bytes := [some 0, some 0, some 0, some 0, some 0, some 0, some 0, some 0, none],
        relocations := [(0, ⟨101, 0⟩)],
        align := ⟨8⟩, mutability := .mut }
    let cmpProvUninitMir :=
      cmCallBody "cm::cmp_uninit_before_prov"
        [mkDecl i32MirTy, mkDecl cmRawConstU8Ty, mkDecl cmRawConstU8Ty] 2
        (cmIntrinsicOp "core::intrinsics::compare_bytes" [])
        [.copy (locPlace 1), .copy (locPlace 2), cmUsizeConst 9] 0 []
        [gProvUninit, cmGlobal 101 (List.replicate 9 (some 0)) 8]
    -- 2. raw_eq::<&!> valid vs raw_eq::<!> UB
    let rawEqRefNeverMir :=
      cmCallBody "cm::raw_eq_ref_never"
        [mkDecl boolMirTy,
         mkDecl { kind := .ref .not (.ref .not .never), layoutIdx := 0 },
         mkDecl { kind := .ref .not (.ref .not .never), layoutIdx := 0 }] 2
        (cmIntrinsicOp "core::intrinsics::raw_eq" [.ref .not .never])
        [.copy (locPlace 1), .copy (locPlace 2)] 0 []
        [cmGlobal 100 (List.replicate 8 (some 1)) 8, cmGlobal 101 (List.replicate 8 (some 1)) 8]
    let rawEqNeverMir :=
      cmCallBody "cm::raw_eq_never"
        [mkDecl boolMirTy,
         mkDecl { kind := .ref .not .never, layoutIdx := 0 },
         mkDecl { kind := .ref .not .never, layoutIdx := 0 }] 2
        (cmIntrinsicOp "core::intrinsics::raw_eq" [.never])
        [.copy (locPlace 1), .copy (locPlace 2)] 0 [] []
    -- 3a. typed_swap global padding reset
    let padKind : RigidTy := .tuple [.uint .u8, .uint .u32]
    let padDeclTy : MirAst.Ty := { kind := padKind, layoutIdx := 1 }
    let rawMutPadTy : MirAst.Ty := { kind := .rawPtr .mut padKind, layoutIdx := 10 }
    let swapPadGlobalMir : CapturedMir :=
      { mkMirBody "cm::swap_pad_global"
          [mkDecl i32MirTy, mkDecl rawMutPadTy, mkDecl rawMutPadTy, mkDecl padDeclTy, mkDecl unitMirTy] 2
          [mkBb [] (.call (cmIntrinsicOp "core::intrinsics::typed_swap_nonoverlapping" [padKind])
              [.copy (locPlace 1), .copy (locPlace 2)] (locPlace 4) (some 1) .continue_),
           mkBb [] (.call (cmIntrinsicOp "core::intrinsics::compare_bytes" [])
              [.copy (locPlace 1), .copy (locPlace 1), cmUsizeConst 4] (locPlace 0) (some 2) .continue_),
           mkBb [] .return_] with
        layouts := cmHardenedLayouts,
        allocations :=
          [cmGlobal 100 [some 1, some 0xAA, some 0xAA, some 0xAA, some 5, some 0, some 0, some 0] 4,
           cmGlobal 101 [some 2, some 0xBB, some 0xBB, some 0xBB, some 6, some 0, some 0, some 0] 4] }
    -- 3b. typed_swap stack byte-buffer padding reset
    let buf16Ty : MirAst.Ty := { kind := .array (.uint .u8) 16, layoutIdx := 9 }
    let swapPadStackMir : CapturedMir :=
      { mkMirBody "cm::swap_pad_stack"
          [mkDecl i32MirTy, mkDecl rawMutPadTy, mkDecl rawMutPadTy, mkDecl buf16Ty,
           mkDecl padDeclTy, mkDecl unitMirTy] 2
          [mkBb [] (.call (cmIntrinsicOp "core::intrinsics::typed_swap_nonoverlapping" [padKind])
              [.copy (locPlace 1), .copy (locPlace 2)] (locPlace 5) (some 1) .continue_),
           mkBb [] (.call (cmIntrinsicOp "core::intrinsics::compare_bytes" [])
              [.copy (locPlace 1), .copy (locPlace 1), cmUsizeConst 4] (locPlace 0) (some 2) .continue_),
           mkBb [] .return_] with
        layouts := cmHardenedLayouts }
    let buf16Val : Value :=
      .aggregate 0 ([1, 0xAA, 0xAA, 0xAA, 5, 0, 0, 0, 2, 0xBB, 0xBB, 0xBB, 6, 0, 0, 0].map
        fun b => Value.scalar ⟨b, 1⟩)
    let bBuf : BorrowEntry :=
      { tag := 1, targetLocal := 3, targetProjection := [], perm := .unique,
        rangeOffset := 0, rangeLen := 16, protector := none, parentTag := none,
        targetFrameDepth := 0, allocDead := false }
    let swapPadStackBase := cmInitLiveState swapPadStackMir [.ptr ⟨1, 0⟩ 8, .ptr ⟨1, 8⟩ 8]
    let swapPadStackSt : MachineState :=
      { swapPadStackBase with
        frame := { swapPadStackBase.frame with
          locals := [.uninit, .init (.ptr ⟨1, 0⟩ 8), .init (.ptr ⟨1, 8⟩ 8),
                     .init buf16Val, .uninit, .uninit] },
        memory := { swapPadStackBase.memory with borrows := [bBuf], nextTag := 2 } }
    -- 3c. typed_swap union MaybeUninit<(u8, u32)> common-padding reset
    let muPadKind : RigidTy := .adt "core::mem::maybe_uninit::MaybeUninit" [padKind]
    let muPadDeclTy : MirAst.Ty := { kind := muPadKind, layoutIdx := 2 }
    let rawMutMuPadTy : MirAst.Ty := { kind := .rawPtr .mut muPadKind, layoutIdx := 10 }
    let swapUnionPadMir : CapturedMir :=
      { mkMirBody "cm::swap_union_pad"
          [mkDecl i32MirTy, mkDecl rawMutMuPadTy, mkDecl rawMutMuPadTy,
           mkDecl muPadDeclTy, mkDecl unitMirTy] 2
          [mkBb [] (.call (cmIntrinsicOp "core::intrinsics::typed_swap_nonoverlapping" [muPadKind])
              [.copy (locPlace 1), .copy (locPlace 2)] (locPlace 4) (some 1) .continue_),
           mkBb [] (.call (cmIntrinsicOp "core::intrinsics::compare_bytes" [])
              [.copy (locPlace 1), .copy (locPlace 1), cmUsizeConst 4] (locPlace 0) (some 2) .continue_),
           mkBb [] .return_] with
        layouts := cmHardenedLayouts,
        allocations :=
          [cmGlobal 100 [some 1, some 0xAA, some 0xAA, some 0xAA, some 5, some 0, some 0, some 0] 4,
           cmGlobal 101 [some 2, some 0xBB, some 0xBB, some 0xBB, some 6, some 0, some 0, some 0] 4] }
    -- 3d. typed_swap invalid char surrogate 0xD800
    let swapCharMir :=
      cmCallBody "cm::swap_char_surrogate"
        [mkDecl u32MirTy, mkDecl { kind := .rawPtr .mut .char, layoutIdx := 0 },
         mkDecl { kind := .rawPtr .mut .char, layoutIdx := 0 }, mkDecl unitMirTy] 2
        (cmIntrinsicOp "core::intrinsics::typed_swap_nonoverlapping" [.char])
        [.copy (locPlace 1), .copy (locPlace 2)] 3
        [mkSt (.assign (locPlace 0) (.use (.constant { ty := u32MirTy, val := .scalar (.int ⟨1, 4⟩) })))]
        [cmGlobal 100 [some 0x00, some 0xD8, some 0x00, some 0x00] 4,
         cmGlobal 101 [some 0x41, some 0x00, some 0x00, some 0x00] 4]
    -- 4. ptr_offset_from: isize::MIN, ZST, dead-tag borrow-first
    let pofZstMir :=
      cmCallBody "cm::pof_zst"
        [mkDecl cmIsizeTy, mkDecl { kind := .rawPtr .not (.tuple []), layoutIdx := 0 },
         mkDecl { kind := .rawPtr .not (.tuple []), layoutIdx := 0 }] 2
        (cmIntrinsicOp "core::intrinsics::ptr_offset_from" [.tuple []])
        [.copy (locPlace 1), .copy (locPlace 2)] 0 [] []
    let deadB1 : BorrowEntry :=
      { tag := 1, targetLocal := 0, targetProjection := [], perm := .unique,
        rangeOffset := 0, rangeLen := 4, protector := none, parentTag := none,
        targetFrameDepth := 0, allocDead := true }
    let deadB2 : BorrowEntry :=
      { tag := 2, targetLocal := 0, targetProjection := [], perm := .unique,
        rangeOffset := 0, rangeLen := 4, protector := none, parentTag := none,
        targetFrameDepth := 0, allocDead := true }
    let deadB100 : BorrowEntry :=
      { tag := 100, targetLocal := 0, targetProjection := [], perm := .unique,
        rangeOffset := 0, rangeLen := 4, protector := none, parentTag := none,
        targetFrameDepth := 0, allocDead := true }
    let pofDeadDiffSt : MachineState :=
      let b := cmInitLiveState cmPofMir [.ptr ⟨1, 4⟩ 8, .ptr ⟨2, 0⟩ 8]
      { b with memory := { b.memory with borrows := [deadB1, deadB2], nextTag := 3 } }
    let pofDeadEqSt : MachineState :=
      let b := cmInitLiveState cmPofMir [.ptr ⟨1, 0⟩ 8, .ptr ⟨2, 0⟩ 8]
      { b with memory := { b.memory with borrows := [deadB1, deadB2], nextTag := 3 } }
    let pofDeadCollideSt : MachineState :=
      let b := cmInitLiveState cmPofMir [.ptr ⟨100, 4⟩ 8, .ptr ⟨100, 0⟩ 8]
      { b with memory := { b.memory with borrows := [deadB100], nextTag := 101 } }
    -- 5. ptr_mask: base-touching mask unsupported, dead-tag colliding with global 100 unsupported, identity mask ok
    let maskTouchBaseMir := cmMaskMir "cm::ptr_mask_not31" (2 ^ 64 - 32)
    let maskDeadCollideSt : MachineState :=
      let b := cmInitLiveState cmMaskAlign8Mir [.ptr ⟨100, 12⟩ 8]
      { b with memory := { b.memory with borrows := [deadB100], nextTag := 101 } }
    let maskDeadIdSt : MachineState :=
      let b := cmInitLiveState cmMaskIdentityMir [.ptr ⟨100, 12⟩ 8]
      { b with memory := { b.memory with borrows := [deadB100], nextTag := 101 } }
    -- 6. black_box: nested MaybeUninit, null wide ref, null fn(), &!, &&!
    let muU8Kind : RigidTy := .adt "core::mem::maybe_uninit::MaybeUninit" [.uint .u8]
    let arrMuU8Ty : MirAst.Ty := { kind := .array muU8Kind 2, layoutIdx := 4 }
    let bbArrMuMir : CapturedMir :=
      { cmCallBody "cm::bb_arr_mu" [mkDecl u32MirTy, mkDecl arrMuU8Ty, mkDecl arrMuU8Ty] 1
          (cmIntrinsicOp "core::intrinsics::black_box" [.array muU8Kind 2])
          [.copy (locPlace 1)] 2
          [mkSt (.assign (locPlace 0) (.use (.constant { ty := u32MirTy, val := .scalar (.int ⟨55, 4⟩) })))]
          [] with
        layouts := cmHardenedLayouts }
    let muU32Kind : RigidTy := .adt "core::mem::maybe_uninit::MaybeUninit" [.uint .u32]
    let tupMuU32Ty : MirAst.Ty := { kind := .tuple [.uint .u32, muU32Kind], layoutIdx := 5 }
    let bbTupMuMir : CapturedMir :=
      { cmCallBody "cm::bb_tup_mu" [mkDecl u32MirTy, mkDecl tupMuU32Ty, mkDecl tupMuU32Ty] 1
          (cmIntrinsicOp "core::intrinsics::black_box" [.tuple [.uint .u32, muU32Kind]])
          [.copy (locPlace 1)] 2
          [mkSt (.assign (locPlace 0) (.use (.constant { ty := u32MirTy, val := .scalar (.int ⟨66, 4⟩) })))]
          [] with
        layouts := cmHardenedLayouts }
    let sliceRefTy : MirAst.Ty := { kind := .ref .not (.slice (.uint .u8)), layoutIdx := 0 }
    let bbWideNullMir :=
      cmCallBody "cm::bb_wide_null" [mkDecl sliceRefTy, mkDecl sliceRefTy] 1
        (cmIntrinsicOp "core::intrinsics::black_box" [.ref .not (.slice (.uint .u8))])
        [.copy (locPlace 1)] 0 [] []
    let fnPtrKind : RigidTy := .fnPtr [] (.tuple []) .safe .rust
    let fnPtrTy : MirAst.Ty := { kind := fnPtrKind, layoutIdx := 0 }
    let bbFnNullMir :=
      cmCallBody "cm::bb_fn_null" [mkDecl fnPtrTy, mkDecl fnPtrTy] 1
        (cmIntrinsicOp "core::intrinsics::black_box" [fnPtrKind])
        [.copy (locPlace 1)] 0 [] []
    let refNeverTy : MirAst.Ty := { kind := .ref .not .never, layoutIdx := 0 }
    let bbRefNeverMir :=
      cmCallBody "cm::bb_ref_never" [mkDecl refNeverTy, mkDecl refNeverTy] 1
        (cmIntrinsicOp "core::intrinsics::black_box" [.ref .not .never])
        [.copy (locPlace 1)] 0 [] []
    let refRefNeverTy : MirAst.Ty := { kind := .ref .not (.ref .not .never), layoutIdx := 0 }
    let bbRefRefNeverMir :=
      cmCallBody "cm::bb_ref_ref_never" [mkDecl refRefNeverTy, mkDecl refRefNeverTy] 1
        (cmIntrinsicOp "core::intrinsics::black_box" [.ref .not (.ref .not .never)])
        [.copy (locPlace 1)] 0 [] []
    -- 7. const_eval_select forwarding + diverging const_eval_select unsupported
    let ctFnOp : Operand :=
      .constant { ty := { kind := .fnDef "cm::ct_dummy" [], layoutIdx := 0 }, val := .zeroSized }
    let cesRawEqMir :=
      cmCallBody "cm::ces_raw_eq"
        [mkDecl boolMirTy, mkDecl { kind := .tuple [.ref .not (.uint .u32), .ref .not (.uint .u32)], layoutIdx := 0 }] 1
        (cmIntrinsicOp "core::intrinsics::const_eval_select"
          [.tuple [.ref .not (.uint .u32), .ref .not (.uint .u32)],
           .fnDef "cm::ct_dummy" [], .fnDef "core::intrinsics::raw_eq" [.uint .u32], .bool])
        [.copy (locPlace 1), ctFnOp, cmIntrinsicOp "core::intrinsics::raw_eq" [.uint .u32]] 0 []
        [cmGlobal 100 (cmU32Bytes 7), cmGlobal 101 (cmU32Bytes 7)]
    let cesMaskMir :=
      cmCallBody "cm::ces_ptr_mask"
        [mkDecl rawConstU32MirTy, mkDecl { kind := .tuple [.rawPtr .not (.uint .u32), .uint .usize], layoutIdx := 0 }] 1
        (cmIntrinsicOp "core::intrinsics::const_eval_select"
          [.tuple [.rawPtr .not (.uint .u32), .uint .usize],
           .fnDef "cm::ct_dummy" [], .fnDef "core::intrinsics::ptr_mask" [.uint .u32], .rawPtr .not (.uint .u32)])
        [.copy (locPlace 1), ctFnOp, cmIntrinsicOp "core::intrinsics::ptr_mask" [.uint .u32]] 0 []
        [cmGlobal 100 (List.replicate 16 (some 0)) 16]
    let cesBbMir :=
      cmCallBody "cm::ces_black_box"
        [mkDecl u32MirTy, mkDecl { kind := .tuple [.uint .u32], layoutIdx := 0 }] 1
        (cmIntrinsicOp "core::intrinsics::const_eval_select"
          [.tuple [.uint .u32], .fnDef "cm::ct_dummy" [],
           .fnDef "core::intrinsics::black_box" [.uint .u32], .uint .u32])
        [.copy (locPlace 1), ctFnOp, cmIntrinsicOp "core::intrinsics::black_box" [.uint .u32]] 0 [] []
    let cesDivMir : CapturedMir :=
      mkMirBody "cm::ces_diverging"
        [mkDecl { kind := .never, layoutIdx := 0 }, mkDecl { kind := .tuple [], layoutIdx := 0 }] 1
        [mkBb [] (.call
          (cmIntrinsicOp "core::intrinsics::const_eval_select"
            [.tuple [], .fnDef "cm::ct_dummy" [], .fnDef "cm::rt_div" [], .never])
          [.copy (locPlace 1), ctFnOp,
           .constant { ty := { kind := .fnDef "cm::rt_div" [], layoutIdx := 0 }, val := .zeroSized }]
          (locPlace 0) none .continue_)]
    -- Assertions
    cmRunTrusted cmpProvUninitMir 8 (cmInitLiveState cmpProvUninitMir [cmGPtr 100 0, cmGPtr 101 0]) = .ub ∧
    cmRunTrusted rawEqRefNeverMir 8 (cmInitLiveState rawEqRefNeverMir [cmGPtr 100 0, cmGPtr 101 0]) = .scalar 1 1 ∧
    cmRunTrusted rawEqNeverMir 8 (cmInitLiveState rawEqNeverMir [cmIntPtr 4096, cmIntPtr 4096]) = .ub ∧
    cmRunTrusted swapPadGlobalMir 10 (cmInitLiveState swapPadGlobalMir [cmGPtr 100 0, cmGPtr 101 0]) = .ub ∧
    cmRunTrusted swapPadStackMir 10 swapPadStackSt = .ub ∧
    cmRunTrusted swapUnionPadMir 10 (cmInitLiveState swapUnionPadMir [cmGPtr 100 0, cmGPtr 101 0]) = .ub ∧
    cmRunTrusted swapCharMir 8 (cmInitLiveState swapCharMir [cmGPtr 100 0, cmGPtr 101 0]) = .ub ∧
    cmRunTrusted cmPofMir 8 (cmInitLiveState cmPofMir [cmIntPtr 0, cmIntPtr (2 ^ 63)]) = .ub ∧
    cmRunTrusted pofZstMir 8 (cmInitLiveState pofZstMir [cmIntPtr 4096, cmIntPtr 4096]) = .ub ∧
    cmRunTrusted cmPofMir 8 pofDeadDiffSt = .ub ∧
    cmRunTrusted cmPofMir 8 pofDeadEqSt = .unsupported ∧
    cmRunTrusted cmPofMir 8 pofDeadCollideSt = .ub ∧
    cmRunTrusted maskTouchBaseMir 8 (cmInitLiveState maskTouchBaseMir [cmGPtr 100 12]) = .unsupported ∧
    cmRunTrusted cmMaskAlign8Mir 8 maskDeadCollideSt = .unsupported ∧
    cmRunTrusted cmMaskIdentityMir 8 maskDeadIdSt = .ptr 100 12 ∧
    cmRunTrusted bbArrMuMir 8
      (cmInitLiveState bbArrMuMir [.aggregate 0 [.aggregate 0 [.unit], .aggregate 0 [.unit]]]) = .scalar 55 4 ∧
    validateBlackBoxValue emptyMemory bbArrMuMir.localDecls cmHardenedLayouts defaultCodecFuel arrMuU8Ty .uninit = .valid ∧
    validateBlackBoxValue emptyMemory bbArrMuMir.localDecls cmHardenedLayouts defaultCodecFuel
      { kind := .array (.uint .u8) 2, layoutIdx := 0 } .uninit = .ub ∧
    cmRunTrusted bbTupMuMir 8
      (cmInitLiveState bbTupMuMir [.aggregate 0 [.scalar ⟨9, 4⟩, .aggregate 0 [.unit]]]) = .scalar 66 4 ∧
    validateBlackBoxValue emptyMemory bbTupMuMir.localDecls cmHardenedLayouts defaultCodecFuel tupMuU32Ty
      (.aggregate 0 [.scalar ⟨9, 4⟩, .uninit]) = .valid ∧
    cmRunTrusted bbWideNullMir 8 (cmInitLiveState bbWideNullMir [.aggregate 0 [cmIntPtr 0, .scalar ⟨0, 8⟩]]) = .ub ∧
    cmRunTrusted bbFnNullMir 8 (cmInitLiveState bbFnNullMir [cmIntPtr 0]) = .ub ∧
    cmRunTrusted bbRefNeverMir 8 (cmInitLiveState bbRefNeverMir [cmIntPtr 4096]) = .ub ∧
    cmRunTrusted bbRefRefNeverMir 8 (cmInitLiveState bbRefRefNeverMir [cmIntPtr 4096]) = .ptr 0 4096 ∧
    cmRunTrusted cesRawEqMir 8 (cmInitLiveState cesRawEqMir [.aggregate 0 [cmGPtr 100 0, cmGPtr 101 0]]) = .scalar 1 1 ∧
    cmRunTrusted cesMaskMir 8 (cmInitLiveState cesMaskMir [.aggregate 0 [cmGPtr 100 12, .scalar ⟨2 ^ 64 - 8, 8⟩]]) = .ptr 100 8 ∧
    cmRunTrusted cesBbMir 8 (cmInitLiveState cesBbMir [.aggregate 0 [.scalar ⟨77, 4⟩]]) = .scalar 77 4 ∧
    cmRunTrusted cesDivMir 8 (cmInitLiveState cesDivMir [.unit]) = .unsupported := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    first | rfl | decide +kernel

/-! ### Paired controls for the hardened negative witnesses

Each hardened UB / fail-closed witness above is paired here with a control
that differs in exactly ONE ingredient and is ACCEPTED, so the fault is
attributable to that ingredient rather than to an unrelated fixture defect. -/

/-- `compare_bytes(&G100, &G101, 9)` where `G100` carries a relocated pointer at
bytes `0..8` and byte `8` is `.uninit` (`uninitTail = true`) or `0`. -/
def cmCmpProvMir (uninitTail : Bool) : CapturedMir :=
  cmCallBody "cm::cmp_uninit_before_prov"
    [mkDecl i32MirTy, mkDecl cmRawConstU8Ty, mkDecl cmRawConstU8Ty] 2
    (cmIntrinsicOp "core::intrinsics::compare_bytes" [])
    [.copy (locPlace 1), .copy (locPlace 2), cmUsizeConst 9] 0 []
    [{ allocId := 100,
       bytes := [some 0, some 0, some 0, some 0, some 0, some 0, some 0, some 0,
                 if uninitTail then none else some 0],
       relocations := [(0, ⟨101, 0⟩)], align := ⟨8⟩, mutability := .mut },
     cmGlobal 101 (List.replicate 9 (some 0)) 8]

/-- `(u8, u32)` and `MaybeUninit<(u8, u32)>` (layout entries `1` / `2` of
`cmHardenedLayouts`). -/
def cmPadKind : RigidTy := .tuple [.uint .u8, .uint .u32]
def cmMuPadKind : RigidTy := .adt "core::mem::maybe_uninit::MaybeUninit" [cmPadKind]

/-- `[typed_swap_nonoverlapping::<T>(_1, _2);] compare_bytes(_1, _rhs, cnt)`:
the swap is executed iff `doSwap` (otherwise bb0 is a plain `goto`). -/
def cmPadSwapCmpMir (name : String) (kind : RigidTy) (midDecls : List MirAst.Ty)
    (allocs : List CapturedAllocation) (doSwap : Bool) (rhs cnt : Nat) : CapturedMir :=
  let rawMut : MirAst.Ty := { kind := .rawPtr .mut kind, layoutIdx := 10 }
  let unitLoc := 3 + midDecls.length
  { mkMirBody name
      ([mkDecl i32MirTy, mkDecl rawMut, mkDecl rawMut] ++ midDecls.map mkDecl ++ [mkDecl unitMirTy]) 2
      [mkBb [] (if doSwap then
          .call (cmIntrinsicOp "core::intrinsics::typed_swap_nonoverlapping" [kind])
            [.copy (locPlace 1), .copy (locPlace 2)] (locPlace unitLoc) (some 1) .continue_
        else .goto 1),
       mkBb [] (.call (cmIntrinsicOp "core::intrinsics::compare_bytes" [])
          [.copy (locPlace 1), .copy (locPlace rhs), cmUsizeConst cnt] (locPlace 0) (some 2) .continue_),
       mkBb [] .return_] with
    layouts := cmHardenedLayouts, allocations := allocs }

/-- Globals `100 = (1, pad 0xAA, 5)` and `101 = (2, pad 0xBB, 6)`. -/
def cmPadGlobals : List CapturedAllocation :=
  [cmGlobal 100 [some 1, some 0xAA, some 0xAA, some 0xAA, some 5, some 0, some 0, some 0] 4,
   cmGlobal 101 [some 2, some 0xBB, some 0xBB, some 0xBB, some 6, some 0, some 0, some 0] 4]

def cmPadGlobalMir (doSwap : Bool) (rhs cnt : Nat) : CapturedMir :=
  cmPadSwapCmpMir "cm::swap_pad_global" cmPadKind [{ kind := cmPadKind, layoutIdx := 1 }]
    cmPadGlobals doSwap rhs cnt

def cmPadUnionMir (doSwap : Bool) (rhs cnt : Nat) : CapturedMir :=
  cmPadSwapCmpMir "cm::swap_union_pad" cmMuPadKind [{ kind := cmMuPadKind, layoutIdx := 2 }]
    cmPadGlobals doSwap rhs cnt

def cmPadStackMir (doSwap : Bool) (rhs cnt : Nat) : CapturedMir :=
  cmPadSwapCmpMir "cm::swap_pad_stack" cmPadKind
    [{ kind := .array (.uint .u8) 16, layoutIdx := 9 }, { kind := cmPadKind, layoutIdx := 1 }]
    [] doSwap rhs cnt

/-- Stack byte buffer `_3 : [u8; 16]` (align 4) holding the two padded images,
borrowed by unique tag `1`; `_1 = &_3[0]`, `_2 = &_3[8]`. -/
def cmPadStackState (body : CapturedMir) (yOff : Nat := 8) : MachineState :=
  let buf16Val : Value :=
    .aggregate 0 ([1, 0xAA, 0xAA, 0xAA, 5, 0, 0, 0, 2, 0xBB, 0xBB, 0xBB, 6, 0, 0, 0].map
      fun b => Value.scalar ⟨b, 1⟩)
  let bBuf : BorrowEntry :=
    { tag := 1, targetLocal := 3, targetProjection := [], perm := .unique,
      rangeOffset := 0, rangeLen := 16, protector := none, parentTag := none,
      targetFrameDepth := 0, allocDead := false }
  let base := cmInitLiveState body [.ptr ⟨1, 0⟩ 8, .ptr ⟨1, yOff⟩ 8]
  { base with
    frame := { base.frame with
      locals := [.uninit, .init (.ptr ⟨1, 0⟩ 8), .init (.ptr ⟨1, yOff⟩ 8),
                 .init buf16Val, .uninit, .uninit] },
    memory := { base.memory with borrows := [bBuf], nextTag := 2 } }

/-- **Paired controls on `V2026_06_01.MirSemantics.stepMirFn`**:
1. `compare_bytes` eager `.uninit`-before-provenance: the SAME relocated slice
   faults `.ub` with an `.uninit` tail but fails closed `.unsupported`
   (provenance) once the tail byte is initialized, so the `.ub` is caused by the
   eager `.uninit` scan preceding the provenance check;
2. `typed_swap_nonoverlapping` padding reset on a global, a union
   `MaybeUninit<(u8, u32)>`, and a stack `[u8; 16]` buffer: for EACH, without
   the swap `compare_bytes(x, x, 4) = 0` (the padding bytes are initialized),
   with the swap `compare_bytes(x, x, 4)` faults `.ub` (the swap reset padding
   bytes `1..3` to `.uninit`), and with the swap `compare_bytes(x, y, 1) = 1`
   (the swap really exchanged the data byte: `x[0] = 2 > y[0] = 1`);
3. same-tag stack swap: the SAME borrow tag `1` at disjoint offsets `0`/`8`
   swaps (item 2), while at overlapping offsets `0`/`4` it faults `.ub`. -/
theorem cm_trusted_hardened_paired_controls :
    cmRunTrusted (cmCmpProvMir true) 8
      (cmInitLiveState (cmCmpProvMir true) [cmGPtr 100 0, cmGPtr 101 0]) = .ub ∧
    cmRunTrusted (cmCmpProvMir false) 8
      (cmInitLiveState (cmCmpProvMir false) [cmGPtr 100 0, cmGPtr 101 0]) = .unsupported ∧
    cmRunTrusted (cmPadGlobalMir false 1 4) 10
      (cmInitLiveState (cmPadGlobalMir false 1 4) [cmGPtr 100 0, cmGPtr 101 0]) = .scalar 0 4 ∧
    cmRunTrusted (cmPadGlobalMir true 1 4) 10
      (cmInitLiveState (cmPadGlobalMir true 1 4) [cmGPtr 100 0, cmGPtr 101 0]) = .ub ∧
    cmRunTrusted (cmPadGlobalMir true 2 1) 10
      (cmInitLiveState (cmPadGlobalMir true 2 1) [cmGPtr 100 0, cmGPtr 101 0]) = .scalar 1 4 ∧
    cmRunTrusted (cmPadUnionMir false 1 4) 10
      (cmInitLiveState (cmPadUnionMir false 1 4) [cmGPtr 100 0, cmGPtr 101 0]) = .scalar 0 4 ∧
    cmRunTrusted (cmPadUnionMir true 1 4) 10
      (cmInitLiveState (cmPadUnionMir true 1 4) [cmGPtr 100 0, cmGPtr 101 0]) = .ub ∧
    cmRunTrusted (cmPadUnionMir true 2 1) 10
      (cmInitLiveState (cmPadUnionMir true 2 1) [cmGPtr 100 0, cmGPtr 101 0]) = .scalar 1 4 ∧
    cmRunTrusted (cmPadStackMir false 1 4) 10 (cmPadStackState (cmPadStackMir false 1 4)) = .scalar 0 4 ∧
    cmRunTrusted (cmPadStackMir true 1 4) 10 (cmPadStackState (cmPadStackMir true 1 4)) = .ub ∧
    cmRunTrusted (cmPadStackMir true 2 1) 10 (cmPadStackState (cmPadStackMir true 2 1)) = .scalar 1 4 ∧
    cmRunTrusted (cmPadStackMir true 2 1) 10 (cmPadStackState (cmPadStackMir true 2 1) 4) = .ub := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-! ### `V2026_06_01` <-> `V2026_08_01` dialect parity -/


/-- **`V2026_06_01` <-> `V2026_08_01` parity**: the `V2026_08_01` dialect's
`stepMirFn`, run on the `V2026_08_01` rendering of the corpus fixtures, yields
exactly the `V2026_06_01` corpus observations (`cmTrustedObserve`) for ALL 8
intrinsics, on BOTH positive AND UB keys, PLUS `protectedTB` mode sensitivity
for BOTH `copy` and `typed_swap_nonoverlapping`. -/
theorem cm_v2026_08_01_parity :
    V08.run08 V08.copy08 8 (V08.init08 V08.copy08 [V08.gp 100 0, V08.gp 101 0]) =
      cmTrustedObserve false .copy .okPrimary ∧
    V08.run08 V08.copy08 8 (V08.init08 V08.copy08 [.ptr ⟨0, 0⟩ 8, V08.gp 101 0]) =
      cmTrustedObserve false .copy .ubFault ∧
    V08.run08 V08.copyMode08 8 (V08.modeInit08 V08.copyMode08 11 false) =
      cmTrustedObserve false .copy .modeCase ∧
    V08.run08 V08.copyMode08 8 (V08.modeInit08 V08.copyMode08 11 true) =
      cmTrustedObserve true .copy .modeCase ∧
    V08.run08 V08.cmp08 8 (V08.init08 V08.cmp08 [V08.gp 100 0, V08.gp 101 0]) =
      cmTrustedObserve false .compareBytes .okPrimary ∧
    V08.run08 V08.cmp08 8 (V08.init08 V08.cmp08 [V08.gp 102 0, V08.gp 101 0]) =
      cmTrustedObserve false .compareBytes .ubFault ∧
    V08.run08 V08.rawEq08 8 (V08.init08 V08.rawEq08 [V08.gp 100 0, V08.gp 101 0]) =
      cmTrustedObserve false .rawEq .okPrimary ∧
    V08.run08 V08.rawEq08 8 (V08.init08 V08.rawEq08 [V08.gp 103 0, V08.gp 101 0]) =
      cmTrustedObserve false .rawEq .ubFault ∧
    V08.run08 V08.swap08 8 (V08.init08 V08.swap08 [V08.gp 100 0, V08.gp 101 0]) =
      cmTrustedObserve false .typedSwap .okPrimary ∧
    V08.run08 V08.swap08 8 (V08.init08 V08.swap08 [.ptr ⟨0, 0⟩ 8, V08.gp 101 0]) =
      cmTrustedObserve false .typedSwap .ubFault ∧
    V08.run08 V08.swapMode08 8 (V08.modeInit08 V08.swapMode08 9 false) =
      cmTrustedObserve false .typedSwap .modeCase ∧
    V08.run08 V08.swapMode08 8 (V08.modeInit08 V08.swapMode08 9 true) =
      cmTrustedObserve true .typedSwap .modeCase ∧
    V08.run08 (V08.pof08 false) 8 (V08.init08 (V08.pof08 false) [V08.gp 100 4, V08.gp 100 12]) =
      cmTrustedObserve false .ptrOffsetFrom .okSecondary ∧
    V08.run08 (V08.pof08 false) 8 (V08.init08 (V08.pof08 false) [V08.gp 100 4, V08.gp 101 12]) =
      cmTrustedObserve false .ptrOffsetFrom .ubFault ∧
    V08.run08 (V08.pof08 true) 8 (V08.init08 (V08.pof08 true) [V08.gp 100 12, V08.gp 100 4]) =
      cmTrustedObserve false .ptrOffsetFromUnsigned .okPrimary ∧
    V08.run08 (V08.pof08 true) 8 (V08.init08 (V08.pof08 true) [V08.gp 100 4, V08.gp 100 12]) =
      cmTrustedObserve false .ptrOffsetFromUnsigned .ubFault ∧
    V08.run08 V08.mask08 8 (V08.init08 V08.mask08 [V08.gp 100 12]) =
      cmTrustedObserve false .ptrMask .okPrimary ∧
    V08.run08 V08.mask08 8 (V08.init08 V08.mask08 []) =
      cmTrustedObserve false .ptrMask .ubFault ∧
    V08.run08 V08.bb08 8 (V08.init08 V08.bb08 [.scalar ⟨77, 4⟩]) =
      cmTrustedObserve false .blackBox .okPrimary ∧
    V08.run08 V08.bb08 8 (V08.init08 V08.bb08 []) =
      cmTrustedObserve false .blackBox .ubFault := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- **`V2026_06_01` <-> `V2026_08_01` parity on the hardened edge cases**: for
EACH Episode 1/2 hardened case, the `V2026_08_01` `stepMirFn` run equals the
`V2026_06_01` run AND that shared observation is the documented verdict:
`copy` null at `count = 0` completes (`7`, agreement with `lean-miri`);
`compare_bytes` null at `bytes = 0` and `typed_swap_nonoverlapping::<()>` null
are `.ub` (the two deliberate deltas); `typed_swap_nonoverlapping` overlap and
misalignment are `.ub` while disjoint same-allocation elements swap (`6`);
invalid `bool` swap is `.ub` (`kani#5205`); `ptr_offset_from` `isize::MIN` and
ZST are `.ub`; `ptr_mask` touching unknown base bits fails closed
`.unsupported` while the identity mask preserves the pointer; `black_box(2u8 as
bool)` is `.ub`. -/
theorem cm_v2026_08_01_hardened_parity :
    V08.run08 V08.copy0_08 8 (V08.init08 V08.copy0_08 [V08.ip 0, V08.ip 0]) =
      cmRunTrusted cmCopy0Mir 8 (cmInitLiveState cmCopy0Mir [cmIntPtr 0, cmIntPtr 0]) ∧
    cmRunTrusted cmCopy0Mir 8 (cmInitLiveState cmCopy0Mir [cmIntPtr 0, cmIntPtr 0]) = .scalar 7 4 ∧
    V08.run08 V08.copy0_08 8 (V08.init08 V08.copy0_08 [V08.ip 2, V08.ip 0]) =
      cmRunTrusted cmCopy0Mir 8 (cmInitLiveState cmCopy0Mir [cmIntPtr 2, cmIntPtr 0]) ∧
    cmRunTrusted cmCopy0Mir 8 (cmInitLiveState cmCopy0Mir [cmIntPtr 2, cmIntPtr 0]) = .ub ∧
    V08.run08 V08.cmp0_08 8 (V08.init08 V08.cmp0_08 [V08.ip 0, V08.ip 0]) =
      cmRunTrusted cmCmpBytes0Mir 8 (cmInitLiveState cmCmpBytes0Mir [cmIntPtr 0, cmIntPtr 0]) ∧
    cmRunTrusted cmCmpBytes0Mir 8 (cmInitLiveState cmCmpBytes0Mir [cmIntPtr 0, cmIntPtr 0]) = .ub ∧
    V08.run08 V08.swapZst08 8 (V08.init08 V08.swapZst08 [V08.ip 0, V08.ip 0]) =
      cmRunTrusted cmSwapZstMir 8 (cmInitLiveState cmSwapZstMir [cmIntPtr 0, cmIntPtr 0]) ∧
    cmRunTrusted cmSwapZstMir 8 (cmInitLiveState cmSwapZstMir [cmIntPtr 0, cmIntPtr 0]) = .ub ∧
    V08.run08 V08.swapZst08 8 (V08.init08 V08.swapZst08 [V08.ip 4096, V08.ip 4096]) =
      cmRunTrusted cmSwapZstMir 8 (cmInitLiveState cmSwapZstMir [cmIntPtr 4096, cmIntPtr 4096]) ∧
    cmRunTrusted cmSwapZstMir 8 (cmInitLiveState cmSwapZstMir [cmIntPtr 4096, cmIntPtr 4096]) = .scalar 7 4 ∧
    V08.run08 V08.swapSame08 8 (V08.init08 V08.swapSame08 [V08.gp 100 0, V08.gp 100 4]) =
      cmRunTrusted cmSwapSameAllocMir 8 (cmInitLiveState cmSwapSameAllocMir [cmGPtr 100 0, cmGPtr 100 4]) ∧
    cmRunTrusted cmSwapSameAllocMir 8 (cmInitLiveState cmSwapSameAllocMir [cmGPtr 100 0, cmGPtr 100 4]) =
      .scalar 6 4 ∧
    V08.run08 V08.swapSame08 8 (V08.init08 V08.swapSame08 [V08.gp 100 0, V08.gp 100 2]) =
      cmRunTrusted cmSwapSameAllocMir 8 (cmInitLiveState cmSwapSameAllocMir [cmGPtr 100 0, cmGPtr 100 2]) ∧
    cmRunTrusted cmSwapSameAllocMir 8 (cmInitLiveState cmSwapSameAllocMir [cmGPtr 100 0, cmGPtr 100 2]) = .ub ∧
    V08.run08 V08.swapBool08 8 (V08.init08 V08.swapBool08 [V08.gp 100 0, V08.gp 101 0]) =
      cmRunTrusted cmSwapBoolMir 8 (cmInitLiveState cmSwapBoolMir [cmGPtr 100 0, cmGPtr 101 0]) ∧
    cmRunTrusted cmSwapBoolMir 8 (cmInitLiveState cmSwapBoolMir [cmGPtr 100 0, cmGPtr 101 0]) = .ub ∧
    V08.run08 (V08.pof08 false) 8 (V08.init08 (V08.pof08 false) [V08.ip 0, V08.ip (2 ^ 63)]) =
      cmRunTrusted cmPofMir 8 (cmInitLiveState cmPofMir [cmIntPtr 0, cmIntPtr (2 ^ 63)]) ∧
    cmRunTrusted cmPofMir 8 (cmInitLiveState cmPofMir [cmIntPtr 0, cmIntPtr (2 ^ 63)]) = .ub ∧
    V08.run08 V08.pofZst08 8 (V08.init08 V08.pofZst08 [V08.ip 4096, V08.ip 4096]) = .ub ∧
    V08.run08 (V08.maskWith08 (2 ^ 64 - 32)) 8
      (V08.init08 (V08.maskWith08 (2 ^ 64 - 32)) [V08.gp 100 12]) =
      cmRunTrusted (cmMaskMir "cm::ptr_mask_not31" (2 ^ 64 - 32)) 8
        (cmInitLiveState (cmMaskMir "cm::ptr_mask_not31" (2 ^ 64 - 32)) [cmGPtr 100 12]) ∧
    cmRunTrusted (cmMaskMir "cm::ptr_mask_not31" (2 ^ 64 - 32)) 8
      (cmInitLiveState (cmMaskMir "cm::ptr_mask_not31" (2 ^ 64 - 32)) [cmGPtr 100 12]) = .unsupported ∧
    V08.run08 (V08.maskWith08 (2 ^ 64 - 1)) 8 (V08.init08 (V08.maskWith08 (2 ^ 64 - 1)) [V08.gp 100 12]) =
      cmRunTrusted cmMaskIdentityMir 8 (cmInitLiveState cmMaskIdentityMir [cmGPtr 100 12]) ∧
    cmRunTrusted cmMaskIdentityMir 8 (cmInitLiveState cmMaskIdentityMir [cmGPtr 100 12]) = .ptr 100 12 ∧
    V08.run08 V08.bbBool08 8 (V08.init08 V08.bbBool08 [.scalar ⟨2, 1⟩]) =
      cmRunTrusted cmBlackBoxBoolMir 8 (cmInitLiveState cmBlackBoxBoolMir [.scalar ⟨2, 1⟩]) ∧
    cmRunTrusted cmBlackBoxBoolMir 8 (cmInitLiveState cmBlackBoxBoolMir [.scalar ⟨2, 1⟩]) = .ub ∧
    V08.run08 V08.bbBool08 8 (V08.init08 V08.bbBool08 [.scalar ⟨1, 1⟩]) =
      cmRunTrusted cmBlackBoxBoolMir 8 (cmInitLiveState cmBlackBoxBoolMir [.scalar ⟨1, 1⟩]) ∧
    cmRunTrusted cmBlackBoxBoolMir 8 (cmInitLiveState cmBlackBoxBoolMir [.scalar ⟨1, 1⟩]) = .scalar 1 1 ∧
    V08.run08 V08.rawEqDiv08 8 (V08.init08 V08.rawEqDiv08 [V08.gp 100 0, V08.gp 101 0]) =
      cmRunTrusted cmRawEqDivergingMir 8 (cmInitLiveState cmRawEqDivergingMir [cmGPtr 100 0, cmGPtr 101 0]) ∧
    cmRunTrusted cmRawEqDivergingMir 8 (cmInitLiveState cmRawEqDivergingMir [cmGPtr 100 0, cmGPtr 101 0]) = .ub ∧
    V08.run08 V08.rawEqRefNever08 8 (V08.init08 V08.rawEqRefNever08 [V08.gp 100 0, V08.gp 101 0]) = .scalar 1 1 ∧
    V08.run08 V08.rawEqNever08 8 (V08.init08 V08.rawEqNever08 [V08.ip 4096, V08.ip 4096]) = .ub ∧
    V08.run08 V08.bbRefNever08 8 (V08.init08 V08.bbRefNever08 [V08.ip 4096]) = .ub ∧
    V08.run08 V08.bbRefRefNever08 8 (V08.init08 V08.bbRefRefNever08 [V08.ip 4096]) = .ptr 0 4096 ∧
    V08.run08 V08.bbWideNull08 8 (V08.init08 V08.bbWideNull08 [.aggregate 0 [V08.ip 0, .scalar ⟨0, 8⟩]]) = .ub ∧
    V08.run08 V08.bbFnNull08 8 (V08.init08 V08.bbFnNull08 [V08.ip 0]) = .ub ∧
    V08.run08 V08.cesRawEq08 8 (V08.init08 V08.cesRawEq08 [.aggregate 0 [V08.gp 100 0, V08.gp 101 0]]) = .scalar 1 1 ∧
    V08.run08 V08.cesMask08 8 (V08.init08 V08.cesMask08 [.aggregate 0 [V08.gp 100 12, .scalar ⟨2 ^ 64 - 8, 8⟩]]) =
      .ptr 100 8 ∧
    V08.run08 V08.cesBb08 8 (V08.init08 V08.cesBb08 [.aggregate 0 [.scalar ⟨77, 4⟩]]) = .scalar 77 4 ∧
    V08.run08 V08.cesDiv08 8 (V08.init08 V08.cesDiv08 [.unit]) = .unsupported := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- **Episode 2 Root Capstone**: the root-Lake projection of
`ep2_core_mem_ptr_intrinsics_capstone` for EVERY LeanMiri authority passing the
unified 64-key check. -/
theorem ep2_core_mem_ptr_intrinsics_root_capstone
    (lmAuth : Anneal.Mir.DropBinderAndSubtypeBundle.Corpus.ObsAuthority CmKey CmObsVal)
    (hLM : lmCheckOf lmAuth = true) :
    cmCodec.TightValidRep ∧
    mrAuthority.denoteConsistent = true ∧
    mrSide.check cmModel = true ∧
    (∀ v, (mrVariantSide v).check cmModel = true) ∧
    (mrSide.flipW cmModel mrSide_check).isSome = true ∧
    ((lmSideOf lmAuth).flipW cmModel hLM).isSome = true ∧
    (∀ (mMR : CmMrMode) (mLM : Bool) (p : CmVariant) (q : CmCase),
      ExactBehaviorEq (bundleOf lmAuth hLM).mrRel mMR p q ∧
      ExactBehaviorEq (bundleOf lmAuth hLM).lmRel mLM p q) ∧
    cmMrObsDictDistinct = true := by
  obtain ⟨hTight, hDen, hSide, hVar, _, _, hExact, hMrFlip, hLmFlip, _, _⟩ :=
    ep2_core_mem_ptr_intrinsics_capstone lmAuth hLM
  exact ⟨hTight, hDen, hSide, hVar, hMrFlip, hLmFlip, hExact, cmMrObsDict_distinct⟩

/-! ## §2. Cross-Root Dual-Authority Kernel Bridge (`MiniRustSpec` + `LeanMiriSpec`) -/

open Lean Elab Command Meta in
run_cmd do
  let opts := (← getOptions).setBool `Elab.async false
  let sp : SearchPath := [System.FilePath.mk ".lake/build/lib/lean",
                          System.FilePath.mk "examples/.lake/build/lib/lean"]
  initSearchPath (← findSysroot) sp
  let baseEnv ← importModules
    #[{ module := `Anneal.Mir.CoreMemPtrIntrinsicsBundle },
      { module := `MiniRustSpec.CoreMemPtrIntrinsicsMR },
      { module := `LeanMiriSpec.CoreMemPtrIntrinsicsLM }]
    {} 0
  let ns := `Anneal.Mir.CoreMemPtrIntrinsicsTests.CrossRoot
  let bNs := `Anneal.Mir.CoreMemPtrIntrinsicsBundle
  let cNs := `Anneal.Mir.DropBinderAndSubtypeBundle.Corpus
  let mrNs := `MiniRustSpec.CoreMemPtrIntrinsicsMR
  let lmNs := `LeanMiriSpec.CoreMemPtrIntrinsicsLM
  let act : CoreM (Nat × Nat × Nat × Nat × Array Name) := do
    let addDef (name : Name) (val : Expr) : CoreM Expr := do
      let ty ← MetaM.run' <| inferType val
      addDecl <| .defnDecl {
        name, levelParams := [], type := ty, value := val,
        hints := .regular 0, safety := .safe }
      return ty
    let addThm (name : Name) (ty pf : Expr) : CoreM Unit := do
      addDecl <| .thmDecl { name, levelParams := [], type := ty, value := pf }
    let boolTy := mkConst ``Bool
    let boolTrue := mkConst ``Bool.true
    let boolFalse := mkConst ``Bool.false
    let natTy := mkConst ``Nat
    let eqTrue (e : Expr) : Expr := mkApp3 (mkConst ``Eq [1]) boolTy e boolTrue
    let reflTrue : Expr := mkApp2 (mkConst ``Eq.refl [1]) boolTy boolTrue
    let eqFalse (e : Expr) : Expr := mkApp3 (mkConst ``Eq [1]) boolTy e boolFalse
    let reflFalse : Expr := mkApp2 (mkConst ``Eq.refl [1]) boolTy boolFalse

    -- Encoders from `CmVariant` / `CmCase` to the Nat indices of `cmLmObserve`.
    let mkVariantToNat : MetaM Expr := do
      let varTy := mkConst (mrNs ++ `CmVariant)
      withLocalDeclD `v varTy fun v => do
        let recApp := mkAppN (mkConst (mrNs ++ `CmVariant.rec) [1])
          #[mkLambda `x .default varTy natTy,
            mkNatLit 0, mkNatLit 1, mkNatLit 2, mkNatLit 3, mkNatLit 4, mkNatLit 5, mkNatLit 6,
            mkNatLit 7, v]
        mkLambdaFVars #[v] recApp
    let mkCaseToNat : MetaM Expr := do
      let caseTy := mkConst (mrNs ++ `CmCase)
      withLocalDeclD `c caseTy fun c => do
        let recApp := mkAppN (mkConst (mrNs ++ `CmCase.rec) [1])
          #[mkLambda `x .default caseTy natTy, mkNatLit 0, mkNatLit 1, mkNatLit 2, mkNatLit 3, c]
        mkLambdaFVars #[c] recApp
    let varToNatName := ns ++ `variantToNat
    let caseToNatName := ns ++ `caseToNat
    let _ ← addDef varToNatName (← MetaM.run' mkVariantToNat)
    let _ ← addDef caseToNatName (← MetaM.run' mkCaseToNat)

    -- 1. The genuine LeanMiri `ObsAuthority CmKey CmObsVal` over `cmLmObserve`.
    let keyTy := mkConst (bNs ++ `CmKey)
    let obsValTy := mkConst (bNs ++ `CmObsVal)
    let lmObsTy := mkConst (lmNs ++ `CmLmObs)
    let verdTy := mkApp (mkConst (cNs ++ `Verdict)) obsValTy
    let mkRet (v : Expr) : Expr := mkApp2 (mkConst (cNs ++ `Verdict.returns)) obsValTy v
    let mkSc (b s : Nat) : Expr := mkRet (mkApp2 (mkConst (bNs ++ `CmObsVal.scalar)) (mkNatLit b) (mkNatLit s))
    let mkPtr (a o : Nat) : Expr := mkRet (mkApp2 (mkConst (bNs ++ `CmObsVal.ptr)) (mkNatLit a) (mkNatLit o))
    let mkScO (b s : Nat) : Expr := mkApp2 (mkConst (lmNs ++ `CmLmObs.scalar)) (mkNatLit b) (mkNatLit s)
    let mkPtrO (a o : Nat) : Expr := mkApp2 (mkConst (lmNs ++ `CmLmObs.ptr)) (mkNatLit a) (mkNatLit o)
    let mkPair (a b : Expr) : Expr := mkApp4 (mkConst ``Prod.mk [0, 0]) verdTy lmObsTy a b
    let mkLmAuth (invertMode : Bool := false) (collideDenote : Bool := false) : MetaM Expr := do
      let decLmObs := mkConst (lmNs ++ `instDecidableEqCmLmObs)
      let observeFn ← withLocalDeclD `k keyTy fun k => do
        let mExpr := mkProj ``Prod 0 k
        let rest := mkProj ``Prod 1 k
        let vExpr := mkProj ``Prod 0 rest
        let cExpr := mkProj ``Prod 1 rest
        let tb0 := mkApp (mkConst (bNs ++ `cmModeToLmTreeBorrows)) mExpr
        let tb := if invertMode then mkApp (mkConst ``Bool.not) tb0 else tb0
        let call := mkApp3 (mkConst (lmNs ++ `cmLmObserve)) tb
          (mkApp (mkConst varToNatName) vExpr) (mkApp (mkConst caseToNatName) cExpr)
        mkLambdaFVars #[k] (mkApp2 (mkConst ``Option.some [0]) lmObsTy call)
      let entries : List Expr :=
        [ mkPair (mkSc 42 4) (mkScO 42 4),
          mkPair (mkSc 0x08070403 4) (mkScO 0x08070403 4),
          mkPair (mkSc 0xFFFFFFFF 4) (mkScO 0xFFFFFFFF 4),
          mkPair (mkSc 1 4) (mkScO 1 4),
          mkPair (mkSc 0 4) (mkScO 0 4),
          mkPair (mkSc 1 1) (mkScO 1 1),
          mkPair (mkSc 0 1) (if collideDenote then mkScO 1 1 else mkScO 0 1),
          mkPair (mkSc 9 4) (mkScO 9 4),
          mkPair (mkSc 7 4) (mkScO 7 4),
          mkPair (mkSc 6 4) (mkScO 6 4),
          mkPair (mkSc 2 8) (mkScO 2 8),
          mkPair (mkSc (2 ^ 64 - 2) 8) (mkScO (2 ^ 64 - 2) 8),
          mkPair (mkSc 0 8) (mkScO 0 8),
          mkPair (mkSc 4 8) (mkScO 4 8),
          mkPair (mkPtr 100 8) (mkPtrO 100 1032),
          mkPair (mkPtr 100 12) (mkPtrO 100 1036),
          mkPair (mkPtr 100 4) (mkPtrO 100 1028),
          mkPair (mkSc 77 4) (mkScO 77 4),
          mkPair (mkApp (mkConst (cNs ++ `Verdict.undefinedBehavior)) obsValTy)
            (mkConst (lmNs ++ `CmLmObs.ub)),
          mkPair (mkApp (mkConst (cNs ++ `Verdict.unsupported)) obsValTy)
            (mkConst (lmNs ++ `CmLmObs.unsupported)) ]
      let pairTy := mkApp2 (mkConst ``Prod [0, 0]) verdTy lmObsTy
      let denoteList := entries.foldr (fun h t => mkApp3 (mkConst ``List.cons [0]) pairTy h t)
        (mkApp (mkConst ``List.nil [0]) pairTy)
      return mkApp6 (mkConst (cNs ++ `ObsAuthority.mk))
        keyTy obsValTy lmObsTy decLmObs observeFn denoteList

    let lmAuthName := ns ++ `lmAuthority
    let _ ← addDef lmAuthName (← MetaM.run' <| mkLmAuth false false)
    let lmAuthC := mkConst lmAuthName
    let mut added : Array Name := #[varToNatName, caseToNatName, lmAuthName]

    -- 2. Kernel-checked `denoteConsistent`, unified `lmSide_check`, lifted theorems.
    let decObsVal := mkConst (bNs ++ `instDecidableEqCmObsVal)
    let denoteConsExpr := mkApp4 (mkConst (cNs ++ `ObsAuthority.denoteConsistent))
      keyTy obsValTy decObsVal lmAuthC
    let denoteConsName := ns ++ `lmAuthority_denoteConsistent
    addThm denoteConsName (eqTrue denoteConsExpr) reflTrue
    added := added.push denoteConsName
    let lmCheckName := ns ++ `lmSide_check
    addThm lmCheckName (eqTrue (mkApp (mkConst (bNs ++ `lmCheckOf)) lmAuthC)) reflTrue
    added := added.push lmCheckName
    let unifiedBundleName := ns ++ `unifiedDualBundle
    let unifiedTy ← addDef unifiedBundleName
      (mkApp2 (mkConst (bNs ++ `bundleOf)) lmAuthC (mkConst lmCheckName))
    unless unifiedTy.getAppFn.isConstOf ``Anneal.DualCorrespondenceBundle.DualCorrespondenceBundle do
      throwError "cross-root: {unifiedBundleName} is not a DualCorrespondenceBundle"
    added := added.push unifiedBundleName
    for thmName in [`threeWayNormalAgreement, `crossAuthorityFaultEquiv,
                    `exactBehaviorEq_both, `lm_modeSensitivity_present,
                    `ep2_core_mem_ptr_intrinsics_capstone] do
      let val := mkApp2 (mkConst (bNs ++ thmName)) lmAuthC (mkConst lmCheckName)
      let ty ← MetaM.run' <| inferType val
      addThm (ns ++ thmName) ty val
      added := added.push (ns ++ thmName)
    let unifiedC := mkConst unifiedBundleName
    let projPosVal ← MetaM.run' <| mkAppM ``DualCorrespondenceBundle.projectPositive #[unifiedC]
    addThm (ns ++ `unified_projectPositive) (← MetaM.run' <| inferType projPosVal) projPosVal
    added := added.push (ns ++ `unified_projectPositive)
    let projFaultVal ← MetaM.run' <| mkAppM ``DualCorrespondenceBundle.projectFault #[unifiedC]
    addThm (ns ++ `unified_projectFault) (← MetaM.run' <| inferType projFaultVal) projFaultVal
    added := added.push (ns ++ `unified_projectFault)

    -- All 8 per-intrinsic bundles, claims, and projections.
    let variantCtors : List Name :=
      [`copy, `compareBytes, `rawEq, `typedSwap, `ptrOffsetFrom, `ptrOffsetFromUnsigned,
       `ptrMask, `blackBox]
    let mut bundleCount : Nat := 1
    for vc in variantCtors do
      let vConst := mkConst (mrNs ++ `CmVariant ++ vc)
      let chkName := ns ++ `variantCheck ++ vc
      addThm chkName (eqTrue (mkApp2 (mkConst (bNs ++ `lmVariantCheckOf)) vConst lmAuthC)) reflTrue
      added := added.push chkName
      let vbName := ns ++ `variantBundle ++ vc
      let vbTy ← addDef vbName
        (mkApp3 (mkConst (bNs ++ `variantBundleOf)) vConst lmAuthC (mkConst chkName))
      unless vbTy.getAppFn.isConstOf ``Anneal.DualCorrespondenceBundle.DualCorrespondenceBundle do
        throwError "cross-root: {vbName} is not a DualCorrespondenceBundle"
      added := added.push vbName
      bundleCount := bundleCount + 1
      let clName := ns ++ `variantClaims ++ vc
      let clVal := mkApp3 (mkConst (bNs ++ `variant_bundle_claims)) vConst lmAuthC (mkConst chkName)
      addThm clName (← MetaM.run' <| inferType clVal) clVal
      added := added.push clName
      let vbC := mkConst vbName
      let vpVal ← MetaM.run' <| mkAppM ``DualCorrespondenceBundle.projectPositive #[vbC]
      addThm (ns ++ `variantProjectPositive ++ vc) (← MetaM.run' <| inferType vpVal) vpVal
      added := added.push (ns ++ `variantProjectPositive ++ vc)
      let vfVal ← MetaM.run' <| mkAppM ``DualCorrespondenceBundle.projectFault #[vbC]
      addThm (ns ++ `variantProjectFault ++ vc) (← MetaM.run' <| inferType vfVal) vfVal
      added := added.push (ns ++ `variantProjectFault ++ vc)

    -- 3. Definitional `Eq.refl` locks of ALL 22 shared `CapturedMir` fixtures.
    let capMirTy := mkConst `Trusted.Rustc.V2026_06_01.MirAst.CapturedMir
    let fixtureNames : List Name :=
      [ `cmCopyMir, `cmCopyOverlapMir, `cmCopyModeMir, `cmCmpBytes3Mir, `cmCmpBytes1Mir,
        `cmRawEqU32Mir, `cmRawEqZstMir, `cmSwapReadXMir, `cmSwapReadYMir, `cmSwapSameAllocMir,
        `cmSwapModeMir, `cmPofMir, `cmPofuMir, `cmMaskAlign8Mir, `cmMaskIdentityMir,
        `cmMaskAlign4Mir, `cmBlackBoxU32Mir, `cmBlackBoxPtrMir, `cmBlackBoxBoolMir,
        `cmCmpBytes0Mir, `cmSwapZstMir, `cmCopy0Mir ]
    let mut lockCount : Nat := 0
    for tag in fixtureNames do
      let lockName := ns ++ `fixtureLock ++ tag
      let lhs := mkConst (mrNs ++ tag)
      let rhs := mkConst (lmNs ++ tag)
      addThm lockName (mkApp3 (mkConst ``Eq [1]) capMirTy lhs rhs)
        (mkApp2 (mkConst ``Eq.refl [1]) capMirTy lhs)
      added := added.push lockName
      lockCount := lockCount + 1
    unless lockCount = 22 do
      throwError "cross-root: expected 22 fixture locks, got {lockCount}"

    -- 4. Negative controls, each paired with a positive control that the kernel
    -- ACCEPTS in the same scratch environment (so a rejection is never caused by
    -- an unrelated elaboration failure).
    let saved ← getEnv
    let accepts (d : Declaration) : CoreM Bool := do
      let r ← try addDecl d; pure true catch _ => pure false
      setEnv saved
      return r
    let invertedAuth ← MetaM.run' <| mkLmAuth true false
    let collidingAuth ← MetaM.run' <| mkLmAuth false true
    let denoteOf (a : Expr) : Expr :=
      mkApp4 (mkConst (cNs ++ `ObsAuthority.denoteConsistent)) keyTy obsValTy decObsVal a
    let lmObsEq (tb v c : Nat) (o : Expr) : Expr :=
      mkApp3 (mkConst ``Eq [1]) lmObsTy
        (mkApp3 (mkConst (lmNs ++ `cmLmObserve)) (if tb = 1 then boolTrue else boolFalse) (mkNatLit v) (mkNatLit c)) o
    let lmObsRefl (tb v c : Nat) : Expr :=
      mkApp2 (mkConst ``Eq.refl [1]) lmObsTy
        (mkApp3 (mkConst (lmNs ++ `cmLmObserve)) (if tb = 1 then boolTrue else boolFalse) (mkNatLit v) (mkNatLit c))
    let trObsTy := mkConst (mrNs ++ `CmTrustedObs)
    let trEq (pm : Bool) (v c : Name) (o : Expr) : Expr :=
      mkApp3 (mkConst ``Eq [1]) trObsTy
        (mkApp3 (mkConst (mrNs ++ `cmTrustedObserve)) (if pm then boolTrue else boolFalse)
          (mkConst (mrNs ++ `CmVariant ++ v)) (mkConst (mrNs ++ `CmCase ++ c))) o
    let trRefl (pm : Bool) (v c : Name) : Expr :=
      mkApp2 (mkConst ``Eq.refl [1]) trObsTy
        (mkApp3 (mkConst (mrNs ++ `cmTrustedObserve)) (if pm then boolTrue else boolFalse)
          (mkConst (mrNs ++ `CmVariant ++ v)) (mkConst (mrNs ++ `CmCase ++ c)))
    let trSc (b s : Nat) : Expr := mkApp2 (mkConst (mrNs ++ `CmTrustedObs.scalar)) (mkNatLit b) (mkNatLit s)
    let thm (n : Name) (ty pf : Expr) : Declaration := .thmDecl { name := ns ++ n, levelParams := [], type := ty, value := pf }
    let pairs : List (String × Declaration × Declaration) :=
      [ ("LM check certificate (true vs. negated false)",
          thm `pos.lmCheckTrue (eqTrue (mkApp (mkConst (bNs ++ `lmCheckOf)) lmAuthC)) reflTrue,
          thm `neg.lmCheckFalse (eqFalse (mkApp (mkConst (bNs ++ `lmCheckOf)) lmAuthC)) reflFalse),
        ("LM authority mode (faithful vs. mode-inverted)",
          thm `pos.modeFaithful (eqTrue (mkApp (mkConst (bNs ++ `lmCheckOf)) lmAuthC)) reflTrue,
          thm `neg.modeInverted (eqTrue (mkApp (mkConst (bNs ++ `lmCheckOf)) invertedAuth)) reflTrue),
        ("per-variant copy certificate (faithful vs. mode-inverted)",
          thm `pos.copyVariant (eqTrue (mkApp2 (mkConst (bNs ++ `lmVariantCheckOf))
            (mkConst (mrNs ++ `CmVariant.copy)) lmAuthC)) reflTrue,
          thm `neg.copyVariantInverted (eqTrue (mkApp2 (mkConst (bNs ++ `lmVariantCheckOf))
            (mkConst (mrNs ++ `CmVariant.copy)) invertedAuth)) reflTrue),
        ("LM denote table (consistent vs. colliding)",
          thm `pos.denote (eqTrue (denoteOf lmAuthC)) reflTrue,
          thm `neg.collidingDenote (eqTrue (denoteOf collidingAuth)) reflTrue),
        ("fixture lock (same fixture vs. swapped copy/compare_bytes)",
          thm `pos.lockCopy (mkApp3 (mkConst ``Eq [1]) capMirTy (mkConst (mrNs ++ `cmCopyMir))
            (mkConst (lmNs ++ `cmCopyMir))) (mkApp2 (mkConst ``Eq.refl [1]) capMirTy (mkConst (mrNs ++ `cmCopyMir))),
          thm `neg.lockSwapped (mkApp3 (mkConst ``Eq [1]) capMirTy (mkConst (mrNs ++ `cmCopyMir))
            (mkConst (lmNs ++ `cmCmpBytes3Mir))) (mkApp2 (mkConst ``Eq.refl [1]) capMirTy (mkConst (mrNs ++ `cmCopyMir)))),
        ("fixture lock (same mask vs. swapped !7/!3 masks)",
          thm `pos.lockMask (mkApp3 (mkConst ``Eq [1]) capMirTy (mkConst (mrNs ++ `cmMaskAlign8Mir))
            (mkConst (lmNs ++ `cmMaskAlign8Mir))) (mkApp2 (mkConst ``Eq.refl [1]) capMirTy (mkConst (mrNs ++ `cmMaskAlign8Mir))),
          thm `neg.lockMaskSwapped (mkApp3 (mkConst ``Eq [1]) capMirTy (mkConst (mrNs ++ `cmMaskAlign8Mir))
            (mkConst (lmNs ++ `cmMaskAlign4Mir))) (mkApp2 (mkConst ``Eq.refl [1]) capMirTy (mkConst (mrNs ++ `cmMaskAlign8Mir)))),
        ("vendored copy observation (42 vs. forged 43)",
          thm `pos.lmCopy42 (lmObsEq 0 0 0 (mkScO 42 4)) (lmObsRefl 0 0 0),
          thm `neg.lmCopy43 (lmObsEq 0 0 0 (mkScO 43 4)) (lmObsRefl 0 0 0)),
        ("vendored ptr_mask provenance/address (1032 vs. forged 1036)",
          thm `pos.lmMask1032 (lmObsEq 0 6 0 (mkPtrO 100 1032)) (lmObsRefl 0 6 0),
          thm `neg.lmMask1036 (lmObsEq 0 6 0 (mkPtrO 100 1036)) (lmObsRefl 0 6 0)),
        ("vendored copy mode case under Tree Borrows (UB vs. forged 42)",
          thm `pos.lmCopyModeTbUb (lmObsEq 1 0 3 (mkConst (lmNs ++ `CmLmObs.ub))) (lmObsRefl 1 0 3),
          thm `neg.lmCopyModeTb42 (lmObsEq 1 0 3 (mkScO 42 4)) (lmObsRefl 1 0 3)),
        ("per-variant typed_swap_nonoverlapping certificate (faithful vs. mode-inverted)",
          thm `pos.swapVariant (eqTrue (mkApp2 (mkConst (bNs ++ `lmVariantCheckOf))
            (mkConst (mrNs ++ `CmVariant.typedSwap)) lmAuthC)) reflTrue,
          thm `neg.swapVariantInverted (eqTrue (mkApp2 (mkConst (bNs ++ `lmVariantCheckOf))
            (mkConst (mrNs ++ `CmVariant.typedSwap)) invertedAuth)) reflTrue),
        ("vendored typed_swap mode case under Tree Borrows (UB vs. forged 9)",
          thm `pos.lmSwapModeTbUb (lmObsEq 1 3 3 (mkConst (lmNs ++ `CmLmObs.ub))) (lmObsRefl 1 3 3),
          thm `neg.lmSwapModeTb9 (lmObsEq 1 3 3 (mkScO 9 4)) (lmObsRefl 1 3 3)),
        ("Trusted compare_bytes (-1 vs. forged +1)",
          thm `pos.trCmpNeg (trEq false `compareBytes `okPrimary (trSc 0xFFFFFFFF 4)) (trRefl false `compareBytes `okPrimary),
          thm `neg.trCmpPos (trEq false `compareBytes `okPrimary (trSc 1 4)) (trRefl false `compareBytes `okPrimary)) ]
    let mut rejected : Nat := 0
    let mut acceptedPos : Nat := 0
    for (what, pos, neg) in pairs do
      unless ← accepts pos do
        throwError "cross-root positive control FAILED: kernel rejected {what}"
      acceptedPos := acceptedPos + 1
      if ← accepts neg then
        throwError "cross-root negative control FAILED: kernel accepted {what}"
      rejected := rejected + 1

    -- 5. Axiom, safety, non-triviality, & transitive reachability audit.
    let env ← getEnv
    let isStdAx (a : Name) : Bool :=
      a == ``propext || a == ``Classical.choice || a == ``Quot.sound
    let rec isTrivialProp : Expr → Bool
      | .forallE _ _ body _ => isTrivialProp body
      | .letE _ _ _ body _ => isTrivialProp body
      | e =>
        if e.isConstOf ``True then true
        else if e.isAppOfArity ``Eq 3 then e.appFn!.appArg! == e.appArg!
        else if e.isAppOfArity ``Iff 2 then e.appFn!.appArg! == e.appArg!
        else false
    let mut crAxioms : NameSet := {}
    for n in added do
      let some ci := env.find? n | throwError "cross-root: {n} missing"
      match ci with
      | .defnInfo v =>
        if v.safety != .safe then throwError "cross-root: {n} is not safe"
      | .thmInfo v =>
        if isTrivialProp v.type then throwError "cross-root: {n} is a trivial theorem"
      | _ => throwError "cross-root: {n} is not a defn or thm"
      for a in ← collectAxioms n do
        unless isStdAx a do
          throwError "cross-root: {n} depends on non-standard axiom {a}"
        crAxioms := crAxioms.insert a
    let lmDeepThms : List Name :=
      [ lmNs ++ `cmMemCopy_basic_mode, lmNs ++ `cmIntrinsic_ofDefId_defId,
        lmNs ++ `cmIntrinsic_ofDefPath_defPath, lmNs ++ `cmDecodeFnItemTyId_cmFnItemTyId,
        lmNs ++ `cmIntrinsic_names,
        lmNs ++ `cm_compareUnsignedBytesI32_eq_miriBytesCompare,
        lmNs ++ `cmMiriBytesCompare_eq_vendored,
        lmNs ++ `cm_miri_ofInt32_bits,
        lmNs ++ `cm_compareUnsignedBytesI32_eq_vendored,
        lmNs ++ `cm_miri_compareBytes_eval_universal,
        lmNs ++ `cm_evalPtrOffsetFromDistance_eq_miriSpec,
        lmNs ++ `cm_miri_ptrOffsetFrom_vendored_matrix,
        lmNs ++ `cm_miriPtrOffsetFromVendored_eq_spec,
        lmNs ++ `cm_evalPtrOffsetFromDistance_eq_vendored,
        lmNs ++ `cm_bitwiseAndBits_64_eq_u64_land,
        lmNs ++ `cm_miri_ptrMask_u64_baseAddr_invariant,
        lmNs ++ `cm_miri_ptrMask_eval_universal,
        lmNs ++ `cm_miri_blackBox_eval_universal,
        lmNs ++ `cm_miri_copyWith_eval_universal,
        lmNs ++ `cm_miri_typedSwap_eval_universal,
        lmNs ++ `cm_miri_rawEq_eval_universal,
        lmNs ++ `cm_miri_compareBytes_cmHooks_universal,
        lmNs ++ `cm_miri_rawEq_cmHooks_universal,
        lmNs ++ `cm_listByteEq_eq_beq,
        lmNs ++ `cm_rawEq_vendored_eq_trusted_listByteEq,
        lmNs ++ `cm_miri_copyWith_cmHooks_zero_count_and_overflow_universal,
        lmNs ++ `cm_miri_typedSwap_and_validatePlace_cmHooks_universal,
        lmNs ++ `cmLmTableCheck_true, lmNs ++ `cmLmObserve_table,
        lmNs ++ `cmLmObserve_copy_mode_sensitivity,
        lmNs ++ `cmLmObserve_typedSwap_mode_sensitivity,
        lmNs ++ `cmLm_hardened_hooks_witness,
        lmNs ++ `cm_lm_trusted_null_zero_size_deltas,
        lmNs ++ `cm_lm_trusted_side_witness ]
    for n in lmDeepThms do
      let some (.thmInfo v) := env.find? n
        | throwError "cross-root: required LM theorem {n} missing"
      if isTrivialProp v.type then
        throwError "cross-root: LM theorem {n} is trivial"
      for a in ← collectAxioms n do
        unless isStdAx a do
          throwError "cross-root: LM theorem {n} depends on non-standard axiom {a}"
        crAxioms := crAxioms.insert a
    unless !(← collectAxioms ``sorryAx).all isStdAx do
      throwError "cross-root self-test: sorryAx was not detected"
    unless !(← collectAxioms ``Lean.ofReduceBool).all isStdAx do
      throwError "cross-root self-test: Lean.ofReduceBool was not detected"
    let trivEq := mkApp3 (mkConst ``Eq [1]) natTy (mkNatLit 1) (mkNatLit 1)
    let nonTrivEq := mkApp3 (mkConst ``Eq [1]) natTy (mkNatLit 1) (mkNatLit 2)
    unless isTrivialProp (mkConst ``True) && isTrivialProp trivEq && !isTrivialProp nonTrivEq do
      throwError "cross-root self-test: trivial theorem detector failed"
    let mut reach : NameSet := {}
    let mut todo : Array Name := #[unifiedBundleName]
    while !todo.isEmpty do
      let n := todo.back!
      todo := todo.pop
      if reach.contains n then continue
      reach := reach.insert n
      if let some ci := env.find? n then
        for d in ci.getUsedConstantsAsSet do
          if !reach.contains d then todo := todo.push d
    let requiredReach : List Name :=
      [ `Trusted.Rustc.V2026_06_01.MirSemantics.stepMirFn,
        `Trusted.Rustc.V2026_06_01.MirSemantics.evalCopyCall,
        `Trusted.Rustc.V2026_06_01.MirSemantics.evalCompareBytesCall,
        `Trusted.Rustc.V2026_06_01.MirSemantics.evalRawEqCall,
        `Trusted.Rustc.V2026_06_01.MirSemantics.evalTypedSwapNonOverlappingCall,
        `Trusted.Rustc.V2026_06_01.MirSemantics.evalPtrOffsetFromCall,
        `Trusted.Rustc.V2026_06_01.MirSemantics.evalPtrMaskCall,
        `Trusted.Rustc.V2026_06_01.MirSemantics.evalBlackBoxCall,
        `MiniRustSpec.Interp.steps,
        `MiniRustSpec.Interp.stepsTB,
        `MiniRustSpec.Interp.evalIntrinsic,
        `MiniRustSpec.Interp.evalPtrOffsetFrom,
        `MiniRustSpec.CoreMemPtrIntrinsicsMR.cmRunTrusted,
        `MiniRustSpec.CoreMemPtrIntrinsicsMR.cmMrObserve,
        `MiniRustSpec.CoreMemPtrIntrinsicsMR.cmTrustedObserve_table,
        `MiniRustSpec.CoreMemPtrIntrinsicsMR.cmMrObserveClass_table,
        `Miri.Interpreter.Step.step,
        `Miri.Interpreter.Intrinsics.eval,
        `Miri.Interpreter.Intrinsics.copyWith,
        `Miri.Interpreter.Intrinsics.compareBytes,
        `Miri.Interpreter.Intrinsics.rawEq,
        `Miri.Interpreter.Intrinsics.typedSwap,
        `Miri.Interpreter.Intrinsics.pointerOffsetFrom,
        `LeanMiriSpec.CoreMemPtrIntrinsicsLM.cmLmObserve,
        `LeanMiriSpec.CoreMemPtrIntrinsicsLM.cmIntrinsicHooks ]
    for req in requiredReach do
      unless reach.contains req do
        throwError "cross-root reachability failure: unifiedDualBundle does not reach {req}"
    -- Vendored anchoring of the universal LM correspondence theorems: each one
    -- must transitively reach the UNMODIFIED vendored constant it claims to
    -- characterize (never only a local re-implementation).
    let closureOf : Name → NameSet := fun root => Id.run do
      let mut seen : NameSet := {}
      let mut stack : Array Name := #[root]
      while !stack.isEmpty do
        let n := stack.back!
        stack := stack.pop
        if seen.contains n then continue
        seen := seen.insert n
        if let some ci := env.find? n then
          for d in ci.getUsedConstantsAsSet do
            if !seen.contains d then stack := stack.push d
      return seen
    let privBytesCompare : Name :=
      (Name.mkNum (`_private ++ `Miri.Interpreter.Intrinsics) 0) ++ `Miri.Interpreter.Intrinsics.bytesCompare
    unless env.contains privBytesCompare do
      throwError "cross-root: vendored private bytesCompare not found"
    let vendoredAnchors : List (Name × Name) :=
      [ (lmNs ++ `cmMiriBytesCompare_eq_vendored, privBytesCompare),
        (lmNs ++ `cm_compareUnsignedBytesI32_eq_vendored, privBytesCompare),
        (lmNs ++ `cm_miri_compareBytes_eval_universal, `Miri.Interpreter.Intrinsics.compareBytes),
        (lmNs ++ `cm_miri_compareBytes_eval_universal, privBytesCompare),
        (lmNs ++ `cm_miri_compareBytes_cmHooks_universal, `Miri.Interpreter.Intrinsics.compareBytes),
        (lmNs ++ `cm_miri_compareBytes_cmHooks_universal, lmNs ++ `cmIntrinsicHooks),
        (lmNs ++ `cm_miri_compareBytes_cmHooks_universal, `Trusted.Rustc.V2026_06_01.MirSemantics.compareUnsignedBytesI32),
        (lmNs ++ `cm_miri_copyWith_eval_universal, `Miri.Interpreter.Intrinsics.copyWith),
        (lmNs ++ `cm_miri_copyWith_cmHooks_zero_count_and_overflow_universal, `Miri.Interpreter.Intrinsics.copyWith),
        (lmNs ++ `cm_miri_copyWith_cmHooks_zero_count_and_overflow_universal, lmNs ++ `cmIntrinsicHooks),
        (lmNs ++ `cm_miri_typedSwap_eval_universal, `Miri.Interpreter.Intrinsics.typedSwap),
        (lmNs ++ `cm_miri_typedSwap_and_validatePlace_cmHooks_universal, `Miri.Interpreter.Intrinsics.typedSwap),
        (lmNs ++ `cm_miri_typedSwap_and_validatePlace_cmHooks_universal, lmNs ++ `cmIntrinsicHooks),
        (lmNs ++ `cm_miri_rawEq_eval_universal, `Miri.Interpreter.Intrinsics.rawEq),
        (lmNs ++ `cm_miri_rawEq_cmHooks_universal, `Miri.Interpreter.Intrinsics.rawEq),
        (lmNs ++ `cm_miri_rawEq_cmHooks_universal, lmNs ++ `cmIntrinsicHooks),
        (lmNs ++ `cm_miri_rawEq_cmHooks_universal, `Trusted.Rustc.V2026_06_01.MirSemantics.listByteEq),
        (lmNs ++ `cm_rawEq_vendored_eq_trusted_listByteEq, `Trusted.Rustc.V2026_06_01.MirSemantics.listByteEq),
        (lmNs ++ `cm_miri_ptrMask_eval_universal, `Miri.Interpreter.Intrinsics.eval),
        (lmNs ++ `cm_miri_blackBox_eval_universal, `Miri.Interpreter.Intrinsics.eval),
        (lmNs ++ `cm_miri_ptrOffsetFrom_vendored_matrix, `Miri.Interpreter.IntegerOps.binary),
        (lmNs ++ `cm_miri_ptrOffsetFrom_vendored_matrix,
          `Miri.Interpreter.IntegerArithmeticIntrinsic.exactDiv),
        (lmNs ++ `cm_miriPtrOffsetFromVendored_eq_spec, `Miri.Interpreter.IntegerOps.binary),
        (lmNs ++ `cm_miriPtrOffsetFromVendored_eq_spec,
          `Miri.Interpreter.IntegerArithmeticIntrinsic.exactDiv),
        (lmNs ++ `cm_evalPtrOffsetFromDistance_eq_vendored, `Miri.Interpreter.IntegerOps.binary),
        (lmNs ++ `cm_evalPtrOffsetFromDistance_eq_vendored,
          `Miri.Interpreter.IntegerArithmeticIntrinsic.exactDiv),
        (lmNs ++ `cm_bitwiseAndBits_64_eq_u64_land, `UInt64.land),
        (lmNs ++ `cmLmObserve_table, `Miri.Interpreter.Step.step),
        (lmNs ++ `cmLmObserve_table, `Miri.Interpreter.Intrinsics.typedSwap),
        -- MR polymorphic & MachTB.wfLive anchoring
        (mrNs ++ `cm_minirust_rawEq_evalIntrinsicM_eq_trusted_listByteEq, `MiniRustSpec.Interp.evalIntrinsicM),
        (mrNs ++ `cm_minirust_rawEq_evalIntrinsicM_eq_trusted_listByteEq,
          `Trusted.Rustc.V2026_06_01.MirSemantics.listByteEq),
        (mrNs ++ `cm_minirust_rawEq_evalIntrinsicM_tb_wfLive, `MiniRustSpec.Correspondence.MachTB.wfLive),
        (mrNs ++ `cm_minirust_evalPtrOffsetFromM_pos_neg_underflow_agree,
          `MiniRustSpec.Interp.evalPtrOffsetFromM),
        (mrNs ++ `cm_minirust_evalPtrOffsetFromM_pos_neg_underflow_agree,
          `Trusted.Rustc.V2026_06_01.MirSemantics.evalPtrOffsetFromDistance),
        (mrNs ++ `cm_minirust_evalPtrOffsetM_wrapping_preserves_prov, `MiniRustSpec.Interp.evalPtrOffsetM),
        (mrNs ++ `cm_minirust_stepsTB_wfLive_all_ok, `MiniRustSpec.Correspondence.MachTB.wfLive),
        (mrNs ++ `cm_minirust_stepsTB_wfLive_all_ok, `MiniRustSpec.Interp.stepsTB) ]
    for (thm, anchor) in vendoredAnchors do
      unless (closureOf thm).contains anchor do
        throwError "cross-root vendored-anchor failure: {thm} does not reach {anchor}"
    -- Discrimination self-tests: the documented local mirrors alone do NOT reach
    -- the vendored constants, so the anchor checks above are not vacuous.
    if (closureOf (lmNs ++ `cmMiriBytesCompare)).contains privBytesCompare then
      throwError "cross-root self-test: local bytesCompare mirror unexpectedly reaches vendored bytesCompare"
    if (closureOf (lmNs ++ `cmMiriPtrOffsetFromSpec)).contains `Miri.Interpreter.IntegerOps.binary then
      throwError "cross-root self-test: local ptrOffsetFrom spec unexpectedly reaches vendored IntegerOps.binary"
    if (closureOf (lmNs ++ `cmMiriPtrOffsetFromSpec)).contains `Miri.Interpreter.IntegerArithmeticIntrinsic.exactDiv then
      throwError "cross-root self-test: local ptrOffsetFrom spec unexpectedly reaches vendored exactDiv"
    return (added.size, bundleCount, acceptedPos, rejected, crAxioms.toArray)

  let ctx : Core.Context :=
    { fileName := "<cm-cross-root>", fileMap := default, options := opts, maxHeartbeats := 0 }
  let ((addedCount, bundleCount, acceptedCount, rejectedCount, crAxioms), _) ←
    liftCoreM <| act.toIO ctx { env := baseEnv }
  unless addedCount ≥ 74 && bundleCount = 9 && acceptedCount = 12 && rejectedCount = 12 do
    throwError "cross-root: unexpected counts (added={addedCount}, bundles={bundleCount}, accepted={acceptedCount}, rejected={rejectedCount})"
  logInfo m!"cm cross-root kernel bridge: added {addedCount} declarations ({bundleCount} bundles, 22 fixture locks), {acceptedCount} positive controls accepted / {rejectedCount} paired negative controls rejected, reached Trusted+MiniRust+Miri, axioms {crAxioms}"

/-! ## §3. Constructive Axiom Audit of `Anneal.Mir.CoreMemPtrIntrinsicsBundle` & Test Module -/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let constructiveDecls : List Name :=
    [ ``Anneal.Mir.CoreMemPtrIntrinsicsBundle.cmCodec,
      ``Anneal.Mir.CoreMemPtrIntrinsicsBundle.cmCodec_tight,
      ``Anneal.Mir.CoreMemPtrIntrinsicsBundle.allCmModes_complete,
      ``Anneal.Mir.CoreMemPtrIntrinsicsBundle.allCmMrModes_complete,
      ``Anneal.Mir.CoreMemPtrIntrinsicsBundle.allCmLmModes_complete,
      ``Anneal.Mir.CoreMemPtrIntrinsicsBundle.allCmVariants_complete,
      ``Anneal.Mir.CoreMemPtrIntrinsicsBundle.allCmCases_complete,
      ``Anneal.Mir.CoreMemPtrIntrinsicsBundle.cmAnnealEval,
      ``Anneal.Mir.CoreMemPtrIntrinsicsBundle.cmAnnealEval_eq,
      ``Anneal.Mir.CoreMemPtrIntrinsicsBundle.cmAnnealEval_funext,
      ``Anneal.Mir.CoreMemPtrIntrinsicsBundle.mrAuthority,
      ``Anneal.Mir.CoreMemPtrIntrinsicsBundle.mrAuthority_denoteConsistent,
      ``Anneal.Mir.CoreMemPtrIntrinsicsBundle.mrAuthority_verdict_eq,
      ``Anneal.Mir.CoreMemPtrIntrinsicsBundle.mrVerdictFn_funext,
      ``Anneal.Mir.CoreMemPtrIntrinsicsBundle.mrSide_check,
      ``Anneal.Mir.CoreMemPtrIntrinsicsBundle.mrVariantSide_check,
      ``Anneal.Mir.CoreMemPtrIntrinsicsBundle.lmCheckOf_congr,
      ``Anneal.Mir.CoreMemPtrIntrinsicsBundle.lmVariantCheckOf_congr,
      ``Anneal.Mir.CoreMemPtrIntrinsicsBundle.bundleOf,
      ``Anneal.Mir.CoreMemPtrIntrinsicsBundle.variantBundleOf,
      ``Anneal.Mir.CoreMemPtrIntrinsicsBundle.threeWayNormalAgreement,
      ``Anneal.Mir.CoreMemPtrIntrinsicsBundle.crossAuthorityFaultEquiv,
      ``Anneal.Mir.CoreMemPtrIntrinsicsBundle.exactBehaviorEq_both,
      ``Anneal.Mir.CoreMemPtrIntrinsicsBundle.mr_modeSensitivity_present,
      ``Anneal.Mir.CoreMemPtrIntrinsicsBundle.mr_typedSwap_modeSensitivity_present,
      ``Anneal.Mir.CoreMemPtrIntrinsicsBundle.lm_modeSensitivity_present,
      ``Anneal.Mir.CoreMemPtrIntrinsicsBundle.lm_typedSwap_modeSensitivity_present,
      ``Anneal.Mir.CoreMemPtrIntrinsicsBundle.variant_bundle_claims,
      ``Anneal.Mir.CoreMemPtrIntrinsicsBundle.cm_variant_outcomes_distinct,
      ``Anneal.Mir.CoreMemPtrIntrinsicsBundle.ep2_core_mem_ptr_intrinsics_capstone ]
  for d in constructiveDecls do
    let axs ← liftCoreM <| Lean.collectAxioms d
    for a in axs do
      unless a == ``propext || a == ``Quot.sound do
        throwError "constructive audit failure: {d} uses non-constructive axiom {a}"
  let rec isTrivialProp : Expr → Bool
    | .forallE _ _ body _ => isTrivialProp body
    | .letE _ _ _ body _ => isTrivialProp body
    | e =>
      if e.isConstOf ``True then true
      else if e.isAppOfArity ``Eq 3 then e.appFn!.appArg! == e.appArg!
      else if e.isAppOfArity ``Iff 2 then e.appFn!.appArg! == e.appArg!
      else false
  let mut bundleDecls : Nat := 0
  for (c, ci) in env.constants.map₁.toList do
    if (`Anneal.Mir.CoreMemPtrIntrinsicsBundle).isPrefixOf c then
      if let .thmInfo v := ci then
        let u := (Lean.privateToUserName? c).getD c
        if !u.isInternal && isTrivialProp v.type then
          throwError "bundle audit failure: {c} is a trivial theorem"
      for a in ← liftCoreM <| Lean.collectAxioms c do
        if a == ``sorryAx then throwError "bundle audit failure: {c} uses sorryAx"
        unless a == ``propext || a == ``Quot.sound do
          throwError "bundle audit failure: {c} uses non-constructive axiom {a}"
      bundleDecls := bundleDecls + 1
  for (c, ci) in env.constants.map₂.toList do
    if let .thmInfo v := ci then
      let u := (Lean.privateToUserName? c).getD c
      if !u.isInternal && isTrivialProp v.type then
        throwError "test audit failure: {c} is a trivial theorem"
    let axs ← liftCoreM <| Lean.collectAxioms c
    for a in axs do
      if a == ``sorryAx then throwError "test audit failure: {c} uses sorryAx"
      unless a == ``propext || a == ``Quot.sound || a == ``Classical.choice do
        throwError "test audit failure: {c} uses non-standard axiom {a}"
  logInfo m!"cm constructive audit: verified {constructiveDecls.length} bundle declarations in [propext, Quot.sound], {bundleDecls} bundle declarations non-trivial and sorry-free (0 Classical.choice in codecs/bundles, 0 sorryAx, 0 ofReduceBool)"

end Anneal.Mir.CoreMemPtrIntrinsicsTests
