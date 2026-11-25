/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import Lean
import MiniRustSpec.Correspondence.Run
import MiniRustSpec.Correspondence.SimulationUnionAssert

/-!
# Non-Vacuity Witnesses for `Type.Union` and `TerminatorKind.assert` (`MiniRustSpec.Correspondence.WitnessUnionAssert`)

Extracted from `MiniRustSpec.Correspondence.Witness` (`namespace MiniRustSpec.Correspondence.Witness`)
to keep every new witness module strictly `< 3,500` LOC while re-exporting all witnesses through
`Witness.lean` and auditing them under `MiniRustSpec.Audit`.
-/

namespace MiniRustSpec.Correspondence.Witness

open Trusted.Effect
open Trusted.ITree
open Trusted.Rustc.V2026_06_01
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.Rustc.V2026_06_01.Layout
open MiniRustSpec
open MiniRustSpec.LibSpecr
open MiniRustSpec.Interp
open MiniRustSpec.Correspondence

local elab "kernel_rfl" : tactic => do
  let mvarId ← Lean.Elab.Tactic.getMainGoal
  let tgt ← Lean.MVarId.getType' mvarId
  let some (ty, lhs, _) := tgt.eq? | Lean.Meta.throwTacticEx `kernel_rfl mvarId "expected equality goal"
  let u ← Lean.Meta.getLevel ty
  mvarId.assign (Lean.mkApp2 (Lean.mkConst ``Eq.refl [u]) ty lhs)
  Lean.Elab.Tactic.replaceMainGoal []

private def u32Ty : Ty := { kind := .uint .u32, layoutIdx := 0 }
private def u32Decl : LocalDecl := { mutability := .mut, ty := u32Ty, debugName := none }
private def mkStmt (k : StatementKind) : MirAst.Statement := { kind := k, span := "witness" }
private def mkTerm (k : TerminatorKind) : MirAst.Terminator := { kind := k, span := "witness" }
private def local_ (i : Nat) : Place := { local_ := i, projection := [] }
private def constU32 (n : Nat) : Operand := .constant { ty := u32Ty, val := .scalar (.int ⟨n, 4⟩) }
private def u32Layout : TypeLayout :=
  { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := .memory, fields := .primitive,
    variants := .single 0, isUninhabited := false }
private def fnAbi (nargs : Nat) : FnAbi :=
  { args := List.replicate nargs { layout := u32Layout, mode := .direct },
    ret := { layout := u32Layout, mode := .direct }, conv := .rust, canUnwind := false }
private def u32 : Gen.IntType := ⟨.Unsigned, ⟨4⟩⟩
private def boolTy : Ty := { kind := .bool, layoutIdx := 0 }
private def boolDecl : LocalDecl := { mutability := .mut, ty := boolTy, debugName := none }
private def u8TyW : Ty := { kind := .uint .u8, layoutIdx := 0 }
private def constU8 (n : Nat) : Operand := .constant { ty := u8TyW, val := .scalar (.int ⟨n, 1⟩) }
private def u8 : Gen.IntType := ⟨.Unsigned, ⟨1⟩⟩
private def retPtr : Ptr := { addr := 64, provenance := some (⟨0⟩, ()) }
private def retAlloc : Gen.Allocation :=
  { data := List.replicate 4 .Uninit, addr := 64, align := ⟨4⟩, kind := .Stack, live := true,
    extra := () }
private def callerFn : Gen.Function where
  locals := ⟨[(localName 0, .Int u32)]⟩
  args := []
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[]⟩
  start := bbName 0
  implicit_writes := true
private def callerFrame : Frame :=
  { func := callerFn, locals := ⟨[(localName 0, retPtr)]⟩, stack_pop_action := .BottomOfStack,
    next_block := bbName 0, next_stmt := 0, extra := () }
private def ctx0 : Ctx :=
  { caller := callerFrame, payloads := [], base := [retAlloc], addrs := [128, 256],
    nextBlock := bbName 7, unwindBlock := none, retPtr := retPtr }
private def emptyProg : Gen.Program :=
  { functions := ⟨[]⟩, start := ⟨⟨0⟩⟩, globals := ⟨[]⟩, traits := ⟨[]⟩, vtables := ⟨[]⟩ }
private def machineWithCtx (ctx : Ctx) (body : CapturedMir) (fn : Gen.Function) (locals : List LocalSlot)
    (blk : Gen.BbName) : Mach :=
  { prog := emptyProg,
    mem := { memory := { allocations := ctx.base ++
                           localAllocs ctx (body.localDecls.take (body.argCount + 1)) locals
                             body.layouts,
                         _phantom := {} },
             accesses := [] },
    intptrcast := ⟨⟨[]⟩⟩,
    threads := [thread1 ctx [ctx.caller,
      { calleeFrame fn ctx (body.argCount + 1) 0 0 with next_block := blk }]],
    active_thread := 0, synchronized_threads := ⟨[]⟩, locks := [], global_ptrs := ⟨[]⟩,
    fn_ptrs := ⟨[]⟩, vtable_ptrs := ⟨[]⟩, stdout := ⟨[]⟩, stderr := ⟨[]⟩ }
private def machine : CapturedMir → Gen.Function → List LocalSlot → Gen.BbName → Mach :=
  machineWithCtx ctx0
private theorem itOf_uint (m : MirAst.Mutability) (ut : UintTy) (l : Nat) (n : Option String)
    (layouts : LayoutTable) :
    itOf { mutability := m, ty := { kind := .uint ut, layoutIdx := l }, debugName := n } layouts =
      itOf { mutability := m, ty := { kind := .uint ut, layoutIdx := l }, debugName := n } := rfl
private theorem tyOf_uint (m : MirAst.Mutability) (ut : UintTy) (l : Nat) (n : Option String)
    (layouts : LayoutTable) :
    tyOf { mutability := m, ty := { kind := .uint ut, layoutIdx := l }, debugName := n } layouts =
      tyOf { mutability := m, ty := { kind := .uint ut, layoutIdx := l }, debugName := n } := rfl
private theorem itOf_bool (m : MirAst.Mutability) (l : Nat) (n : Option String)
    (layouts : LayoutTable) :
    itOf { mutability := m, ty := { kind := .bool, layoutIdx := l }, debugName := n } layouts =
      itOf { mutability := m, ty := { kind := .bool, layoutIdx := l }, debugName := n } := rfl
private theorem tyOf_bool (m : MirAst.Mutability) (l : Nat) (n : Option String)
    (layouts : LayoutTable) :
    tyOf { mutability := m, ty := { kind := .bool, layoutIdx := l }, debugName := n } layouts =
      tyOf { mutability := m, ty := { kind := .bool, layoutIdx := l }, debugName := n } := rfl

/-! ## `Type.Union` (`MaybeUninit<u32>`, `ManuallyDrop<u32>`, and Padded `[(); 4]` ZST-Arm Unions)

Kernel-checked witnesses and negative controls that run Anneal's `MirSemantics`
(`stepMirFn`, `runA_sound`) and `MiniRustSpec.Interp` on the same union
programs. The MiniRust functions are lowered by hand, because `Translate.lean`
has no union types: a union aggregate becomes `Deinit` plus a field assignment
(see the `Type.Union` section of `Simulation.lean`; on a freshly allocated
local the `Deinit` is a no-op, and `wUnionWitnessFn` omits it).

* `wUnionWitnessMir` uses `MaybeUninitShaped`, a union `{ [(); 4], u32 }` whose
  MIR type is named `MaybeUninit`, and the padded union `PU`
  (`{ [(); 4], u8, u32, VoidZst }`, `kani#5176` and `kani#5159`).
* `wMaybeUninitMir` uses the real `MaybeUninit<u32>`
  (`union { uninit: (), value: ManuallyDrop<u32> }`) and `ManuallyDrop<u32>`.
* `wUnionReaggMir` re-aggregates an initialized union and shows why the
  lowering needs `Deinit`. -/

def wU8Layout : TypeLayout :=
  { size := { bytes := 1 }, align := { bytes := 1 },
    backendRepr := .scalar (.initialized (.int 8 false) { start := 0, end_ := 255 }),
    fields := .primitive, variants := .single 0, isUninhabited := false }

def wU32Layout : TypeLayout :=
  { size := { bytes := 4 }, align := { bytes := 4 },
    backendRepr := .scalar (.initialized (.int 32 false) { start := 0, end_ := 4294967295 }),
    fields := .primitive, variants := .single 0, isUninhabited := false }

def wZstArr4Layout : TypeLayout :=
  { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := .memory,
    fields := .array ⟨0⟩ 4, variants := .single 0, isUninhabited := false, fieldLayouts := [] }

def wVoidZstLayout : TypeLayout :=
  { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := .memory,
    fields := .arbitrary [] [], variants := .empty,
    isUninhabited := true, fieldLayouts := [] }

def wPULayout : TypeLayout :=
  { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := .memory,
    fields := .union 4, variants := .single 0, isUninhabited := false,
    fieldLayouts := [2, 0, 1, 3] }

def wMaybeUninitU32Layout : TypeLayout :=
  { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := .memory,
    fields := .union 2, variants := .single 0, isUninhabited := false,
    fieldLayouts := [2, 1] }

def wUnionLayouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true,
    entries := [wU8Layout, wU32Layout, wZstArr4Layout, wVoidZstLayout, wPULayout, wMaybeUninitU32Layout] }

def wUnitTy : Ty := { kind := .tuple [], layoutIdx := 0 }
def wU32Ty : Ty := { kind := .uint .u32, layoutIdx := 1 }
def wZstArr4Ty : Ty := { kind := .array (.tuple []) 4, layoutIdx := 2 }
def wVoidZstTy : Ty := { kind := .adt "VoidZst" [], layoutIdx := 3 }
def wPUTy : Ty := { kind := .adt "PU" [], layoutIdx := 4 }
def wMaybeUninitU32Ty : Ty := { kind := .adt "core::mem::maybe_uninit::MaybeUninit" [wU32Ty.kind], layoutIdx := 5 }

def wUnitDecl : LocalDecl := { mutability := .mut, ty := wUnitTy, debugName := none }
def wU32Decl : LocalDecl := { mutability := .mut, ty := wU32Ty, debugName := none }
def wZstArr4Decl : LocalDecl := { mutability := .mut, ty := wZstArr4Ty, debugName := none }
def wVoidZstDecl : LocalDecl := { mutability := .mut, ty := wVoidZstTy, debugName := none }
def wPUDecl : LocalDecl := { mutability := .mut, ty := wPUTy, debugName := none }
def wMaybeUninitU32Decl : LocalDecl := { mutability := .mut, ty := wMaybeUninitU32Ty, debugName := none }

def wConstU32 (n : Nat) : Operand := .constant { ty := wU32Ty, val := .scalar (.int ⟨n, 4⟩) }
def wZstArr4Val : Value := .aggregate 0 [.aggregate 0 [], .aggregate 0 [], .aggregate 0 [], .aggregate 0 []]

/-- Anneal MIR body exercising `MaybeUninitShaped` (`_1`, `_2`: a union whose MIR
type is named `MaybeUninit<u32>` but whose layout has the fields `[(); 4]` and
`u32`) and the padded `[(); 4]` union `PU`:
* `bb0` (init via payload, whole-union copy, field read):
  `_1 = MaybeUninit { value: 42_u32 }; _2 = copy _1; _0 = copy (_2.1: u32); return`
* `bb1` (init via ZST arm, whole-union copy, ZST read, then uninit scalar read UB):
  `_1 = MaybeUninit { uninit: copy _3 }; _2 = copy _1; _3 = copy (_2.0: [(); 4]); _0 = copy (_2.1: u32)` (UB)
* `bb2` (padded union `PU` narrower `u8` init `0x55`, whole-union copy preserving
  3 uninit padding bytes, `[(); 4]` ZST arm overwrite retaining `0x55`, ZST arm
  read, and `u8` payload read):
  `_4 = PU { a: 0x55_u8 }; _5 = copy _4; _5.0 = copy _3; _3 = copy (_5.0: [(); 4]); _6 = copy (_5.1: u8); _0 = Cast(IntToInt, copy _6, u32); return`
* `bb3` (padded union `PU` narrower `u8` init `0x55`, copy, wider `u32` read UB):
  `_4 = PU { a: 0x55_u8 }; _5 = copy _4; _0 = copy (_5.2: u32)` (UB)
* `bb4` (padded union `PU` full `u32` init, uninhabited 0-byte field read UB, `kani#5159`):
  `_4 = PU { b: 0x01020304_u32 }; _7 = copy (_4.3: VoidZst)` (UB) -/
def wUnionWitnessMir : CapturedMir where
  defPath := "witness::union_correspondence"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [
    wU32Decl,              -- _0: u32
    wMaybeUninitU32Decl,   -- _1: MaybeUninit<u32>
    wMaybeUninitU32Decl,   -- _2: MaybeUninit<u32>
    wZstArr4Decl,          -- _3: [(); 4]
    wPUDecl,               -- _4: PU
    wPUDecl,               -- _5: PU
    { mutability := .mut, ty := u8TyW, debugName := none }, -- _6: u8
    wVoidZstDecl           -- _7: VoidZst
  ]
  basicBlocks := [
    -- `bb0`: `MaybeUninit<u32>` init `42`, copy, read `42`
    { statements := [
        mkStmt (.assign (local_ 1) (.aggregate (.adt "core::mem::maybe_uninit::MaybeUninit" 0 (some 1)) [wConstU32 42])),
        mkStmt (.assign (local_ 2) (.use (.copy (local_ 1)))),
        mkStmt (.assign (local_ 0) (.use (.copy ⟨2, [.field 1 wU32Ty]⟩)))],
      terminator := mkTerm .return_, isCleanup := false },
    -- `bb1`: `MaybeUninit<u32>` uninit ZST arm, copy, ZST read, uninit `u32` read UB
    { statements := [
        mkStmt (.assign (local_ 3) (.repeat (.constant { ty := wUnitTy, val := .zeroSized }) 4)),
        mkStmt (.assign (local_ 1) (.aggregate (.adt "core::mem::maybe_uninit::MaybeUninit" 0 (some 0)) [.copy (local_ 3)])),
        mkStmt (.assign (local_ 2) (.use (.copy (local_ 1)))),
        mkStmt (.assign (local_ 3) (.use (.copy ⟨2, [.field 0 wZstArr4Ty]⟩))),
        mkStmt (.assign (local_ 0) (.use (.copy ⟨2, [.field 1 wU32Ty]⟩)))],
      terminator := mkTerm .return_, isCleanup := false },
    -- `bb2`: `PU` narrower `0x55_u8` init, whole-union copy, `[(); 4]` ZST arm overwrite retaining `0x55`, ZST read, `u8` read -> `0x55`
    { statements := [
        mkStmt (.assign (local_ 3) (.repeat (.constant { ty := wUnitTy, val := .zeroSized }) 4)),
        mkStmt (.assign (local_ 4) (.aggregate (.adt "PU" 0 (some 1)) [constU8 0x55])),
        mkStmt (.assign (local_ 5) (.use (.copy (local_ 4)))),
        mkStmt (.assign ⟨5, [.field 0 wZstArr4Ty]⟩ (.use (.copy (local_ 3)))),
        mkStmt (.assign (local_ 3) (.use (.copy ⟨5, [.field 0 wZstArr4Ty]⟩))),
        mkStmt (.assign (local_ 6) (.use (.copy ⟨5, [.field 1 u8TyW]⟩))),
        mkStmt (.assign (local_ 0) (.cast .intToInt (.copy (local_ 6)) wU32Ty))],
      terminator := mkTerm .return_, isCleanup := false },
    -- `bb3`: `PU` narrower `0x55_u8` init, copy, wider `u32` read -> UB
    { statements := [
        mkStmt (.assign (local_ 4) (.aggregate (.adt "PU" 0 (some 1)) [constU8 0x55])),
        mkStmt (.assign (local_ 5) (.use (.copy (local_ 4)))),
        mkStmt (.assign (local_ 0) (.use (.copy ⟨5, [.field 2 wU32Ty]⟩)))],
      terminator := mkTerm .return_, isCleanup := false },
    -- `bb4`: `PU` full `u32` init, uninhabited 0-byte field read -> UB (`kani#5159`)
    { statements := [
        mkStmt (.assign (local_ 4) (.aggregate (.adt "PU" 0 (some 2)) [wConstU32 0x01020304])),
        mkStmt (.assign (local_ 7) (.use (.copy ⟨4, [.field 3 wVoidZstTy]⟩)))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbi 0
  layouts := wUnionLayouts
  allocations := []

/-- The MiniRust type of `MaybeUninitShaped`: the union `{ [(); 4], u32 }`, not
`mrMaybeUninitTy` (for the real `MaybeUninit<u32>`, see `wMaybeUninitFn`). -/
def mrMaybeUninitU32 : Gen.«Type» :=
  mrUnionTy [(⟨0⟩, mrZstArrayTy 4), (⟨0⟩, .Int u32)] 4 4

def mrPU : Gen.«Type» :=
  mrUnionTy [(⟨0⟩, mrZstArrayTy 4), (⟨0⟩, .Int u8), (⟨0⟩, .Int u32), (⟨0⟩, mrUninhabitedZstTy)] 4 4

def wUnionWitnessFn : Gen.Function where
  locals := ⟨[
    (localName 0, .Int u32),
    (localName 1, mrMaybeUninitU32),
    (localName 2, mrMaybeUninitU32),
    (localName 3, mrZstArrayTy 4),
    (localName 4, mrPU),
    (localName 5, mrPU),
    (localName 6, .Int u8),
    (localName 7, mrUninhabitedZstTy)]⟩
  args := []
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    -- `bb0`: `_1.1 = 42_u32; _2 = copy _1; _0 = Transmute(copy _2); return`
    (bbName 0, ⟨[
      .StorageLive (localName 1),
      .StorageLive (localName 2),
      .Assign (.Field (.Local (localName 1)) 1) (.Constant (.Int 42) (.Int u32)),
      .Assign (.Local (localName 2)) (.Load (.Local (localName 1))),
      .Assign (.Local (localName 0)) (.UnOp (.Cast (.Transmute (.Int u32))) (.Load (.Local (localName 2)))),
      .StorageDead (localName 2),
      .StorageDead (localName 1)],
      .Return, .Regular⟩),
    -- `bb1`: `_1` uninit ZST arm, `_2 = copy _1` (copies 4 `.Uninit` bytes!), `_3 = copy _2.0` (0-byte ZST read succeeds!), `_0 = copy _2.1` (UB!)
    (bbName 1, ⟨[
      .StorageLive (localName 1),
      .StorageLive (localName 2),
      .StorageLive (localName 3),
      .Assign (.Field (.Local (localName 1)) 0) (.Load (.Field (.Local (localName 1)) 0)),
      .Assign (.Local (localName 2)) (.Load (.Local (localName 1))),
      .Assign (.Local (localName 3)) (.Load (.Field (.Local (localName 2)) 0)),
      .Assign (.Local (localName 0)) (.Load (.Field (.Local (localName 2)) 1))],
      .Return, .Regular⟩),
    -- `bb2`: `_4.1 = 0x55_u8` (`[0x55, Uninit, Uninit, Uninit]`), `_5 = copy _4` (preserves 3 `.Uninit` padding bytes!), `_5.0 = copy _3` (0-byte ZST write retains `0x55`!), `_3 = copy _5.0`, `_6 = copy _5.1`, `_0 = _6 as u32`, return `0x55`
    (bbName 2, ⟨[
      .StorageLive (localName 3),
      .StorageLive (localName 4),
      .StorageLive (localName 5),
      .StorageLive (localName 6),
      .Assign (.Field (.Local (localName 4)) 1) (.Constant (.Int 0x55) (.Int u8)),
      .Assign (.Local (localName 5)) (.Load (.Local (localName 4))),
      .Assign (.Field (.Local (localName 5)) 0) (.Load (.Field (.Local (localName 4)) 0)),
      .Assign (.Local (localName 3)) (.Load (.Field (.Local (localName 5)) 0)),
      .Assign (.Local (localName 6)) (.Load (.Field (.Local (localName 5)) 1)),
      .Assign (.Local (localName 0)) (.UnOp (.Cast (.IntToInt u32)) (.Load (.Local (localName 6)))),
      .StorageDead (localName 6),
      .StorageDead (localName 5),
      .StorageDead (localName 4),
      .StorageDead (localName 3)],
      .Return, .Regular⟩),
    -- `bb3`: `_4.1 = 0x55_u8`, `_5 = copy _4`, `_0 = copy _5.2` (reading `u32` across 3 `.Uninit` padding bytes -> UB!)
    (bbName 3, ⟨[
      .StorageLive (localName 4),
      .StorageLive (localName 5),
      .Assign (.Field (.Local (localName 4)) 1) (.Constant (.Int 0x55) (.Int u8)),
      .Assign (.Local (localName 5)) (.Load (.Local (localName 4))),
      .Assign (.Local (localName 0)) (.Load (.Field (.Local (localName 5)) 2))],
      .Return, .Regular⟩),
    -- `bb4`: `_4.2 = 0x01020304_u32`, `_7 = copy _4.3` (reading uninhabited 0-byte `VoidZst` arm -> UB, `kani#5159`!)
    (bbName 4, ⟨[
      .StorageLive (localName 4),
      .StorageLive (localName 7),
      .Assign (.Field (.Local (localName 4)) 2) (.Constant (.Int 0x01020304) (.Int u32)),
      .Assign (.Local (localName 7)) (.Load (.Field (.Local (localName 4)) 3))],
      .Return, .Regular⟩)]⟩
  start := bbName 0
  implicit_writes := true

def wUnionS0 (b : Nat) : MachineState :=
  { (initMachineState wUnionWitnessMir []) with
    frame := { blockIdx := b, stmtIdx := 0, locals := List.replicate 8 .uninit } }

def wUnionMach (b : Nat) : Mach :=
  machine wUnionWitnessMir wUnionWitnessFn (wUnionS0 b).frame.locals (bbName b)

/-- **Witness 1 (`MaybeUninit<u32>` init, whole-union copy, and `assume_init` / field read)**:
In `bb0`, both Anneal (`ReachesRet`) and MiniRust (`Interp.steps 8`) initialize
`_1 : MaybeUninit<u32>` to `42_u32`, copy the union into `_2`, extract `42_u32`
into `_0`, and return `42_u32`. -/
theorem maybeUninit_init_copy_read_witness :
    ReachesRet (mirTree wUnionWitnessMir (wUnionS0 0)) []
      (.normal (.scalar ⟨42, 4⟩, (wUnionS0 0).memory)) ∧
    (Interp.steps 8 (wUnionMach 0)).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAlloc with data := scalarBytes u32 42 }, [1]) :=
  ⟨runA_sound wUnionWitnessMir 10 _ _ _ rfl, rfl⟩

/-- **Witness 2 (`MaybeUninit<u32>` uninit ZST arm, whole-union copy of uninit bytes,
inhabited ZST read, and uninit scalar read UB)**:
In `bb1`:
1. Constructing `MaybeUninit` via its 0-byte ZST arm, copying the whole uninitialized
   union `_2 = copy _1`, and reading back the 0-byte ZST arm `_3 = copy _2.0`
   all succeed in both Anneal (`stepMirFn`) and MiniRust (`Interp.steps 6`);
2. Reading the uninitialized `u32` arm `_0 = copy _2.1` faults with `.ub` in both
   Anneal (`faultsA_sound`) and MiniRust (`Interp.steps 7 = .error (.ub ...)`). -/
theorem maybeUninit_uninit_copy_zst_read_and_scalar_ub_witness :
    (∃ s1 s2 s3 s4,
      stepMirFn wUnionWitnessMir (wUnionS0 1) = .step s1 ∧
      stepMirFn wUnionWitnessMir s1 = .step s2 ∧
      stepMirFn wUnionWitnessMir s2 = .step s3 ∧
      stepMirFn wUnionWitnessMir s3 = .step s4 ∧
      stepMirFn wUnionWitnessMir s4 = .fail .ub) ∧
    (Interp.steps 6 (wUnionMach 1)).isOk = true ∧
    Interp.steps 7 (wUnionMach 1) =
      .error (.ub "load at type but the data in memory violates the language invariant") :=
  ⟨⟨_, _, _, _, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl⟩

private theorem reachesRet_step_tau {body : CapturedMir} {s s' : MachineState} {tr o}
    (hs : stepMirFn body s = .step s')
    (hrest : ReachesRet (mirTree body s') tr o) :
    ReachesRet (mirTree body s) tr o := by
  have hobs := mirTree_observe body s
  rw [hs] at hobs
  obtain ⟨u, hr, hu⟩ := hrest
  exact ⟨u, .tau hobs hr, hu⟩

private def wUnionBb2StepState (stmtIdx : Nat) (locals : List LocalSlot) : MachineState :=
  { (wUnionS0 2) with frame := { blockIdx := 2, stmtIdx := stmtIdx, locals := locals } }

/-- **Witness 3 (`kani#5176` padded union `PU` narrower `u8` init, whole-union
copy preserving `.Uninit` padding bytes, `[(); 4]` ZST arm overwrite retaining
payload byte `0`, ZST read, and `u8` payload read)**:
In `bb2`, both Anneal (`ReachesRet` returning `0x55_u32`) and MiniRust
(`Interp.steps 15` returning `scalarBytes u32 0x55` in `retAlloc`) execute the
entire 7-statement padded-union pipeline without UB. The run itself shows the
padding bytes: after `_5 = copy _4` (step 6), both `_4`'s allocation (index 3)
and `_5`'s (index 4) hold `[.Init 0x55 none, .Uninit, .Uninit, .Uninit]`, and
the 0-byte write `_5.0 = copy _3` (step 7) leaves `_5`'s bytes unchanged. The
Anneal value of `_4` relates to those bytes (`MiniRustUnionBytesRel`). -/
theorem paddedZstUnion_copy_zst_overwrite_and_read_witness :
    ReachesRet (mirTree wUnionWitnessMir (wUnionS0 2)) []
      (.normal (.scalar ⟨0x55, 4⟩, (wUnionS0 2).memory)) ∧
    MiniRustUnionBytesRel wUnionLayouts wPUTy 4
      (.aggregate 0 [.unit, .scalar ⟨0x55, 1⟩, .unit, .unit])
      [.Init 0x55 none, .Uninit, .Uninit, .Uninit] ∧
    (Interp.steps 6 (wUnionMach 2)).toOption.map
        (fun m => (m.mem.memory.allocations[3]?.map (·.data),
          m.mem.memory.allocations[4]?.map (·.data))) =
      some (some [.Init 0x55 none, .Uninit, .Uninit, .Uninit],
        some [.Init 0x55 none, .Uninit, .Uninit, .Uninit]) ∧
    (Interp.steps 7 (wUnionMach 2)).toOption.map
        (fun m => m.mem.memory.allocations[4]?.map (·.data)) =
      some (some [.Init 0x55 none, .Uninit, .Uninit, .Uninit]) ∧
    (Interp.steps 15 (wUnionMach 2)).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAlloc with data := scalarBytes u32 0x55 }, [1]) := by
  let zst4 : Value := .aggregate 0 (List.replicate 4 .unit)
  let puU8 : Value := .aggregate 0 [.unit, .scalar ⟨0x55, 1⟩, .unit, .unit]
  let puOv : Value := .aggregate 0 ([.unit, .unit, .unit, .unit] ++
    [.aggregate 0 (MirSemantics.encodeRawAbstractByteVals
      [.init 0x55 none, .uninit, .uninit, .uninit])])
  let s1 := wUnionBb2StepState 1 [.uninit, .uninit, .uninit, .init zst4, .uninit, .uninit, .uninit, .uninit]
  let s2 := wUnionBb2StepState 2 [.uninit, .uninit, .uninit, .init zst4, .init puU8, .uninit, .uninit, .uninit]
  let s3 := wUnionBb2StepState 3 [.uninit, .uninit, .uninit, .init zst4, .init puU8, .init puU8, .uninit, .uninit]
  let s4 := wUnionBb2StepState 4 [.uninit, .uninit, .uninit, .init zst4, .init puU8, .init puOv, .uninit, .uninit]
  let s5 := wUnionBb2StepState 5 [.uninit, .uninit, .uninit, .init zst4, .init puU8, .init puOv, .uninit, .uninit]
  let s6 := wUnionBb2StepState 6 [.uninit, .uninit, .uninit, .init zst4, .init puU8, .init puOv, .init (.scalar ⟨0x55, 1⟩), .uninit]
  let s7 := wUnionBb2StepState 7 [.init (.scalar ⟨0x55, 4⟩), .uninit, .uninit, .init zst4, .init puU8, .init puOv, .init (.scalar ⟨0x55, 1⟩), .uninit]
  have hret : ReachesRet (mirTree wUnionWitnessMir (wUnionS0 2)) []
      (.normal (.scalar ⟨0x55, 4⟩, (wUnionS0 2).memory)) :=
    reachesRet_step_tau (s' := s1) rfl <|
    reachesRet_step_tau (s' := s2) rfl <|
    reachesRet_step_tau (s' := s3) rfl <|
    reachesRet_step_tau (s' := s4) rfl <|
    reachesRet_step_tau (s' := s5) rfl <|
    reachesRet_step_tau (s' := s6) rfl <|
    reachesRet_step_tau (s' := s7) rfl <|
    runA_sound wUnionWitnessMir 2 s7 [] (.normal (.scalar ⟨0x55, 4⟩, (wUnionS0 2).memory)) rfl
  exact ⟨hret, ⟨rfl, _, rfl, rfl, rfl⟩, rfl, rfl, rfl⟩

/-- **Witness 4 (Negative control: reading wider `u32` arm across uninitialized
trailing padding bytes `[1, 4)` of a copied padded union `PU`)**:
In `bb3`, after `_4 = PU { a: 0x55_u8 }` and `_5 = copy _4` succeed in both
machines, reading `_0 = copy (_5.2: u32)` faults with `.ub` in both Anneal and
MiniRust (`Interp.steps 5`). -/
theorem paddedZstUnion_uninit_padding_read_ub_witness :
    (∃ s1 s2,
      stepMirFn wUnionWitnessMir (wUnionS0 3) = .step s1 ∧
      stepMirFn wUnionWitnessMir s1 = .step s2 ∧
      stepMirFn wUnionWitnessMir s2 = .fail .ub) ∧
    (Interp.steps 4 (wUnionMach 3)).isOk = true ∧
    Interp.steps 5 (wUnionMach 3) =
      .error (.ub "load at type but the data in memory violates the language invariant") :=
  ⟨⟨_, _, rfl, rfl, rfl⟩, rfl, rfl⟩

/-- **Witness 5 (Negative control `kani#5159`: reading uninhabited 0-byte arm
`VoidZst` of an initialized union `PU`)**:
In `bb4`, even after `_4 = PU { b: 0x01020304_u32 }` initializes all 4 bytes of
`_4`, reading the uninhabited 0-byte field `_7 = copy (_4.3: VoidZst)` faults
with `.ub` in both Anneal and MiniRust (`Interp.steps 4`). -/
theorem paddedZstUnion_uninhabited_zst_arm_ub_witness :
    (∃ s1,
      stepMirFn wUnionWitnessMir (wUnionS0 4) = .step s1 ∧
      stepMirFn wUnionWitnessMir s1 = .fail .ub) ∧
    (Interp.steps 3 (wUnionMach 4)).isOk = true ∧
    Interp.steps 4 (wUnionMach 4) =
      .error (.ub "load at type but the data in memory violates the language invariant") :=
  ⟨⟨_, rfl, rfl⟩, rfl, rfl⟩

/-! ### The real `MaybeUninit<u32>` and `ManuallyDrop<u32>`

`MaybeUninit<u32>` is `union { uninit: (), value: ManuallyDrop<u32> }`, and
`ManuallyDrop<u32>` is the struct `{ value: u32 }`. On the MiniRust side they
are `mrMaybeUninitTy (.Int u32) 4 4` and `mrManuallyDropTy (.Int u32) 4 4`, and
`assume_init` reads the nested field `_1.1.0`. -/

def wMUUnitLayout : TypeLayout :=
  { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := .memory,
    fields := .arbitrary [] [], variants := .single 0, isUninhabited := false, fieldLayouts := [] }

def wMDU32Layout : TypeLayout :=
  { size := { bytes := 4 }, align := { bytes := 4 },
    backendRepr := .scalar (.initialized (.int 32 false) { start := 0, end_ := 4294967295 }),
    fields := .arbitrary [{ bytes := 0 }] [0], variants := .single 0, isUninhabited := false,
    fieldLayouts := [1] }

def wMUU32Layout : TypeLayout :=
  { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := .memory,
    fields := .union 2, variants := .single 0, isUninhabited := false, fieldLayouts := [0, 2] }

def wMULayouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true,
    entries := [wMUUnitLayout, wU32Layout, wMDU32Layout, wMUU32Layout] }

def wMUUnitTy : Ty := { kind := .tuple [], layoutIdx := 0 }
def wMUU32Ty : Ty := { kind := .uint .u32, layoutIdx := 1 }
def wMDU32Ty : Ty :=
  { kind := .adt "core::mem::manually_drop::ManuallyDrop" [.uint .u32], layoutIdx := 2 }
def wMUTy : Ty :=
  { kind := .adt "core::mem::maybe_uninit::MaybeUninit" [.uint .u32], layoutIdx := 3 }
def wMUConstU32 (n : Nat) : Operand := .constant { ty := wMUU32Ty, val := .scalar (.int ⟨n, 4⟩) }

/-- Anneal MIR body for `MaybeUninit<u32>` and `ManuallyDrop<u32>`
(`_0: u32`, `_1: MaybeUninit<u32>`, `_2: ManuallyDrop<u32>`):
* `bb0` (`MaybeUninit::new(42).assume_init()`):
  `_2 = ManuallyDrop { value: 42_u32 }; _1 = MaybeUninit { value: move _2 };
  _0 = copy ((_1.1: ManuallyDrop<u32>).0: u32); return`
* `bb1` (`MaybeUninit::uninit().assume_init()`, UB):
  `_1 = MaybeUninit { uninit: const () }; _0 = copy ((_1.1: ManuallyDrop<u32>).0: u32)`
* `bb2` (`ManuallyDrop::into_inner(ManuallyDrop::new(7))`):
  `_2 = ManuallyDrop { value: 7_u32 }; _0 = copy (_2.0: u32); return` -/
def wMaybeUninitMir : CapturedMir where
  defPath := "witness::maybe_uninit_manually_drop"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [
    { mutability := .mut, ty := wMUU32Ty, debugName := none },
    { mutability := .mut, ty := wMUTy, debugName := none },
    { mutability := .mut, ty := wMDU32Ty, debugName := none }]
  basicBlocks := [
    { statements := [
        mkStmt (.assign (local_ 2)
          (.aggregate (.adt "core::mem::manually_drop::ManuallyDrop" 0 none) [wMUConstU32 42])),
        mkStmt (.assign (local_ 1)
          (.aggregate (.adt "core::mem::maybe_uninit::MaybeUninit" 0 (some 1)) [.move (local_ 2)])),
        mkStmt (.assign (local_ 0) (.use (.copy ⟨1, [.field 1 wMDU32Ty, .field 0 wMUU32Ty]⟩)))],
      terminator := mkTerm .return_, isCleanup := false },
    { statements := [
        mkStmt (.assign (local_ 1)
          (.aggregate (.adt "core::mem::maybe_uninit::MaybeUninit" 0 (some 0))
            [.constant { ty := wMUUnitTy, val := .zeroSized }])),
        mkStmt (.assign (local_ 0) (.use (.copy ⟨1, [.field 1 wMDU32Ty, .field 0 wMUU32Ty]⟩)))],
      terminator := mkTerm .return_, isCleanup := false },
    { statements := [
        mkStmt (.assign (local_ 2)
          (.aggregate (.adt "core::mem::manually_drop::ManuallyDrop" 0 none) [wMUConstU32 7])),
        mkStmt (.assign (local_ 0) (.use (.copy ⟨2, [.field 0 wMUU32Ty]⟩)))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbi 0
  layouts := wMULayouts
  allocations := []

def mrMDU32 : Gen.«Type» := mrManuallyDropTy (.Int u32) 4 4
def mrMUU32 : Gen.«Type» := mrMaybeUninitTy (.Int u32) 4 4

/-- The MiniRust lowering of `wMaybeUninitMir`: the struct aggregate is a
`ValueExpr::Tuple`, and each union aggregate is `Deinit` plus a field
assignment. -/
def wMaybeUninitFn : Gen.Function where
  locals := ⟨[(localName 0, .Int u32), (localName 1, mrMUU32), (localName 2, mrMDU32)]⟩
  args := []
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .StorageLive (localName 1), .StorageLive (localName 2),
      .Assign (.Local (localName 2)) (.Tuple [.Constant (.Int 42) (.Int u32)] mrMDU32),
      .Deinit (.Local (localName 1)),
      .Assign (.Field (.Local (localName 1)) 1) (.Load (.Local (localName 2))),
      .Assign (.Local (localName 0)) (.Load (.Field (.Field (.Local (localName 1)) 1) 0)),
      .StorageDead (localName 2), .StorageDead (localName 1)], .Return, .Regular⟩),
    (bbName 1, ⟨[
      .StorageLive (localName 1),
      .Deinit (.Local (localName 1)),
      .Assign (.Field (.Local (localName 1)) 0) (.Tuple [] mrUnitTy),
      .Assign (.Local (localName 0)) (.Load (.Field (.Field (.Local (localName 1)) 1) 0))],
      .Return, .Regular⟩),
    (bbName 2, ⟨[
      .StorageLive (localName 2),
      .Assign (.Local (localName 2)) (.Tuple [.Constant (.Int 7) (.Int u32)] mrMDU32),
      .Assign (.Local (localName 0)) (.Load (.Field (.Local (localName 2)) 0)),
      .StorageDead (localName 2)], .Return, .Regular⟩)]⟩
  start := bbName 0
  implicit_writes := true

def wMUS0 (b : Nat) : MachineState :=
  { (initMachineState wMaybeUninitMir []) with
    frame := { blockIdx := b, stmtIdx := 0, locals := List.replicate 3 .uninit } }

def wMUMach (b : Nat) : Mach :=
  machine wMaybeUninitMir wMaybeUninitFn (wMUS0 b).frame.locals (bbName b)

/-- **Witness (`MaybeUninit<u32>`: `new(42).assume_init()`, and
`uninit().assume_init()` UB)**: In `bb0`, both Anneal and MiniRust
(`Interp.steps 9`) return `42_u32` through the nested field `_1.1.0`. In
`bb1`, reading `_1.1.0` after initializing only the `()` arm faults with `.ub`
in both, in Anneal's second step and MiniRust's fourth. -/
theorem maybeUninitU32_new_assume_init_and_uninit_ub_witness :
    ReachesRet (mirTree wMaybeUninitMir (wMUS0 0)) []
      (.normal (.scalar ⟨42, 4⟩, (wMUS0 0).memory)) ∧
    (Interp.steps 9 (wMUMach 0)).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAlloc with data := scalarBytes u32 42 }, [1]) ∧
    (∃ s1, stepMirFn wMaybeUninitMir (wMUS0 1) = .step s1 ∧
      stepMirFn wMaybeUninitMir s1 = .fail .ub) ∧
    (Interp.steps 3 (wMUMach 1)).isOk = true ∧
    Interp.steps 4 (wMUMach 1) =
      .error (.ub "load at type but the data in memory violates the language invariant") :=
  ⟨runA_sound wMaybeUninitMir 10 _ _ _ rfl, rfl, ⟨_, rfl, rfl⟩, rfl, rfl⟩

/-- **Witness (`ManuallyDrop<u32>`)**: In `bb2`, both Anneal and MiniRust
(`Interp.steps 5`) build `ManuallyDrop { value: 7 }` and return `7_u32` from its
field. -/
theorem manuallyDropU32_new_into_inner_witness :
    ReachesRet (mirTree wMaybeUninitMir (wMUS0 2)) []
      (.normal (.scalar ⟨7, 4⟩, (wMUS0 2).memory)) ∧
    (Interp.steps 5 (wMUMach 2)).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAlloc with data := scalarBytes u32 7 }, [1]) :=
  ⟨runA_sound wMaybeUninitMir 10 _ _ _ rfl, rfl⟩

/-! ### Re-aggregating an initialized union

`_1 = PU { b: 0x01020304 }; _1 = PU { a: 0x55 }; _0 = copy (_1.2: u32)` reads
the `u32` arm after the second aggregate has replaced the whole union: Anneal
faults, because bytes `[1, 4)` are uninitialized again. MiniRust agrees only if
the second aggregate is lowered with `Deinit`, as `ValueExpr::Union`'s value
dictates; a bare field assignment keeps the stale bytes and returns
`0x01020355`. -/

/-- Anneal MIR body that re-aggregates the padded union `PU`. -/
def wUnionReaggMir : CapturedMir where
  defPath := "witness::union_reaggregate"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [wU32Decl, wPUDecl]
  basicBlocks := [
    { statements := [
        mkStmt (.assign (local_ 1) (.aggregate (.adt "PU" 0 (some 2)) [wConstU32 0x01020304])),
        mkStmt (.assign (local_ 1) (.aggregate (.adt "PU" 0 (some 1)) [constU8 0x55])),
        mkStmt (.assign (local_ 0) (.use (.copy ⟨1, [.field 2 wU32Ty]⟩)))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbi 0
  layouts := wUnionLayouts
  allocations := []

/-- The MiniRust lowering of `wUnionReaggMir`: with `deinit = true`, each union
aggregate is `Deinit` plus a field assignment; with `deinit = false`, it is the
bare field assignment. -/
def wUnionReaggFn (deinit : Bool) : Gen.Function where
  locals := ⟨[(localName 0, .Int u32), (localName 1, mrPU)]⟩
  args := []
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[(bbName 0, ⟨[.StorageLive (localName 1)] ++
    (if deinit then [.Deinit (.Local (localName 1))] else []) ++
    [.Assign (.Field (.Local (localName 1)) 2) (.Constant (.Int 0x01020304) (.Int u32))] ++
    (if deinit then [.Deinit (.Local (localName 1))] else []) ++
    [.Assign (.Field (.Local (localName 1)) 1) (.Constant (.Int 0x55) (.Int u8)),
     .Assign (.Local (localName 0)) (.Load (.Field (.Local (localName 1)) 2)),
     .StorageDead (localName 1)], .Return, .Regular⟩)]⟩
  start := bbName 0
  implicit_writes := true

def wUnionReaggS0 : MachineState :=
  { (initMachineState wUnionReaggMir []) with
    frame := { blockIdx := 0, stmtIdx := 0, locals := [.uninit, .uninit] } }

def wUnionReaggMach (deinit : Bool) : Mach :=
  machine wUnionReaggMir (wUnionReaggFn deinit) wUnionReaggS0.frame.locals (bbName 0)

/-- **Witness (union re-aggregation needs `Deinit`)**: Anneal faults on the
third statement. The `Deinit` lowering faults in MiniRust too (step 6). The
negative control without `Deinit` keeps the stale bytes `[1, 4)` and stores
`0x01020355` into `_0` (step 6) instead of faulting. -/
theorem union_reaggregate_needs_deinit_witness :
    (∃ s1 s2, stepMirFn wUnionReaggMir wUnionReaggS0 = .step s1 ∧
      stepMirFn wUnionReaggMir s1 = .step s2 ∧ stepMirFn wUnionReaggMir s2 = .fail .ub) ∧
    Interp.steps 6 (wUnionReaggMach true) =
      .error (.ub "load at type but the data in memory violates the language invariant") ∧
    (Interp.steps 6 (wUnionReaggMach false)).toOption.map
        (fun m => m.mem.memory.allocations[1]?.map (·.data)) =
      some (some (scalarBytes u32 0x01020355)) :=
  ⟨⟨_, _, rfl, rfl, rfl⟩, rfl, rfl⟩

/-! ### Computed Union Translation (`translateFnWithUnions`) and Two-Sided Union Step Simulation Instantiations (`G2`) -/

/-- **Witness (`translateFnWithUnions` on `wMaybeUninitMir`)**: the function
that `translateFnWithUnions` computes from `wMaybeUninitMir` (no hand-written
blocks) returns `42_u32` from `bb0` (`Interp.steps 7`), faults reading the
uninitialized `value` arm in `bb1` (step 4), and returns `7_u32` from `bb2`
(`Interp.steps 4`), as Anneal does
(`maybeUninitU32_new_assume_init_and_uninit_ub_witness`,
`manuallyDropU32_new_into_inner_witness`). Its runs are shorter than
`wMaybeUninitFn`'s because it emits no `StorageDead`. -/
theorem wMaybeUninit_translateFnWithUnions_witness :
    ∃ f, translateFnWithUnions wMaybeUninitMir = some f ∧
      (Interp.steps 7 (machine wMaybeUninitMir f (wMUS0 0).frame.locals (bbName 0))).toOption.map
          (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
        some (some { retAlloc with data := scalarBytes u32 42 }, [1]) ∧
      (Interp.steps 3 (machine wMaybeUninitMir f (wMUS0 1).frame.locals (bbName 1))).isOk = true ∧
      Interp.steps 4 (machine wMaybeUninitMir f (wMUS0 1).frame.locals (bbName 1)) =
        .error (.ub "load at type but the data in memory violates the language invariant") ∧
      (Interp.steps 4 (machine wMaybeUninitMir f (wMUS0 2).frame.locals (bbName 2))).toOption.map
          (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
        some (some { retAlloc with data := scalarBytes u32 7 }, [1]) :=
  ⟨_, rfl, rfl, rfl, rfl, rfl⟩

/-- The function that `translateFnWithUnions` computes from `wUnionReaggMir`
(`wUnionReaggAutoFn_eq_true`, `wUnionReaggAutoFn_eq_false`). -/
def wUnionReaggAutoFn (deinit : Bool) : Gen.Function where
  locals := ⟨[(localName 0, .Int u32), (localName 1, mrPU)]⟩
  args := []
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[(bbName 0, ⟨[.StorageLive (localName 1)] ++
    (if deinit then [.Deinit (.Local (localName 1))] else []) ++
    [.Assign (.Field (.Local (localName 1)) 2) (.Constant (.Int 0x01020304) (.Int u32))] ++
    (if deinit then [.Deinit (.Local (localName 1))] else []) ++
    [.Assign (.Field (.Local (localName 1)) 1) (.Constant (.Int 0x55) (.Int u8)),
     .Assign (.Local (localName 0)) (.Load (.Field (.Local (localName 1)) 2))],
    .Return, .Regular⟩)]⟩
  start := bbName 0
  implicit_writes := true

theorem wUnionReaggAutoFn_eq_true :
    translateFnWithUnions wUnionReaggMir true = some (wUnionReaggAutoFn true) := rfl

theorem wUnionReaggAutoFn_eq_false :
    translateFnWithUnions wUnionReaggMir false = some (wUnionReaggAutoFn false) := rfl

theorem wUnionReaggAutoFn_witness :
    Interp.steps 6 (machine wUnionReaggMir (wUnionReaggAutoFn true) wUnionReaggS0.frame.locals (bbName 0)) =
      .error (.ub "load at type but the data in memory violates the language invariant") ∧
    (Interp.steps 4 (machine wUnionReaggMir (wUnionReaggAutoFn false) wUnionReaggS0.frame.locals (bbName 0))).toOption.map
        (fun m => m.mem.memory.allocations[1]?.map (·.data)) =
      some (some (scalarBytes u32 0x01020355)) :=
  ⟨rfl, rfl⟩

/-- Concrete `Ctx`, `lm`, and `L` for instantiating `MiniRustUnionLocalStorage`
and `step_union_whole_copy_minirust_simulation` on `wUnionWitnessMir` /
`wUnionWitnessFn` (`bb2` at statement `5`, `_5 = copy _4`). -/
def wUnionCtx2 : Ctx :=
  { caller := callerFrame
    payloads := []
    base := [retAlloc]
    addrs := [128, 256, 384, 512, 640, 768, 896, 1024]
    nextBlock := bbName 7
    unwindBlock := none
    retPtr := retPtr }

def wUnionAllocs2 : List Gen.Allocation :=
  [localAlloc wUnionCtx2 0 u32 (List.replicate 4 .Uninit),
   localAlloc wUnionCtx2 1 ⟨.Unsigned, ⟨4⟩⟩ (List.replicate 4 .Uninit),
   localAlloc wUnionCtx2 2 ⟨.Unsigned, ⟨4⟩⟩ (List.replicate 4 .Uninit),
   localAlloc wUnionCtx2 3 ⟨.Unsigned, ⟨1⟩⟩ [],
   localAlloc wUnionCtx2 4 ⟨.Unsigned, ⟨4⟩⟩ [.Init 0x55 none, .Uninit, .Uninit, .Uninit],
   localAlloc wUnionCtx2 5 ⟨.Unsigned, ⟨4⟩⟩ (List.replicate 4 .Uninit),
   localAlloc wUnionCtx2 6 u8 (List.replicate 1 .Uninit),
   localAlloc wUnionCtx2 7 ⟨.Unsigned, ⟨1⟩⟩ []]

def wUnionMidAnneal2 : MachineState :=
  { frame :=
      { blockIdx := 2
        stmtIdx := 5
        locals := [.uninit, .uninit, .uninit, .init wZstArr4Val,
                   .init (.aggregate 0 [.unit, .scalar ⟨0x55, 1⟩, .unit, .unit]),
                   .uninit, .uninit, .uninit] }
    memory := (wUnionS0 2).memory }

def wUnionMidMach2 : Mach :=
  { prog := emptyProg
    mem := { memory := { allocations := wUnionCtx2.base ++ wUnionAllocs2, _phantom := {} },
             accesses := [] }
    intptrcast := ⟨⟨[]⟩⟩
    threads := [thread1 wUnionCtx2
      [wUnionCtx2.caller, calleeFrameL wUnionWitnessFn wUnionCtx2 (localsMap wUnionCtx2 8) 2 5]]
    active_thread := 0
    synchronized_threads := ⟨[]⟩
    locks := []
    global_ptrs := ⟨[]⟩
    fn_ptrs := ⟨[]⟩
    vtable_ptrs := ⟨[]⟩
    stdout := ⟨[]⟩
    stderr := ⟨[]⟩ }

theorem wUnionMid2_shape :
    Shape wUnionMidMach2 wUnionCtx2
      [wUnionCtx2.caller, calleeFrameL wUnionWitnessFn wUnionCtx2 (localsMap wUnionCtx2 8) 2 5]
      (wUnionCtx2.base ++ wUnionAllocs2) :=
  ⟨rfl, rfl, rfl⟩

theorem wUnionMid2_storage4 :
    MiniRustUnionLocalStorage wUnionCtx2 wUnionAllocs2 wUnionWitnessFn
      (localsMap wUnionCtx2 8) wUnionLayouts 4 wPUTy
      [(⟨0⟩, mrZstArrayTy 4), (⟨0⟩, .Int u8), (⟨0⟩, .Int u32), (⟨0⟩, mrUninhabitedZstTy)]
      4 4 (.init (.aggregate 0 [.unit, .scalar ⟨0x55, 1⟩, .unit, .unit]))
      [.Init 0x55 none, .Uninit, .Uninit, .Uninit] where
  pos_size := by decide
  align_ok := by decide
  addr_nonneg := by decide
  addr_lt := by decide
  fn_local := rfl
  lm_ptr := rfl
  bytes_len := rfl
  alloc_eq := rfl
  slot_rel := ⟨rfl, _, rfl, rfl, rfl⟩

theorem wUnionMid2_storage5 :
    MiniRustUnionLocalStorage wUnionCtx2 wUnionAllocs2 wUnionWitnessFn
      (localsMap wUnionCtx2 8) wUnionLayouts 5 wPUTy
      [(⟨0⟩, mrZstArrayTy 4), (⟨0⟩, .Int u8), (⟨0⟩, .Int u32), (⟨0⟩, mrUninhabitedZstTy)]
      4 4 .uninit (List.replicate 4 .Uninit) where
  pos_size := by decide
  align_ok := by decide
  addr_nonneg := by decide
  addr_lt := by decide
  fn_local := rfl
  lm_ptr := rfl
  bytes_len := rfl
  alloc_eq := rfl
  slot_rel := rfl

/-- **Instantiation of `step_union_whole_copy_minirust_simulation` and the
MiniRust union field-read lemmas (`G2`)** on `wUnionMidAnneal2` /
`wUnionMidMach2`, the state of `bb2` before `_5 = copy _4`:
1. `_5 = copy _4` steps in lockstep via `step_union_whole_copy_minirust_simulation`,
   establishing `MiniRustUnionLocalStorage` on `_5` with
   `[.Init 0x55 none, .Uninit, .Uninit, .Uninit]`;
2. reading the `[(); 4]` ZST arm (`_4.0`) succeeds in Anneal (computed) and in
   MiniRust (`evalValue_load_union_zstArray_field`);
3. reading the uninhabited `VoidZst` arm (`_4.3`) faults in Anneal (computed)
   and in MiniRust (`evalValue_load_union_uninhabited_ub`);
4. reading the `u32` arm (`_4.2`) across the 3 `.Uninit` padding bytes faults
   in Anneal (computed) and in MiniRust (`evalValue_load_union_int_uninit_ub`).
The general lemmas cover only the MiniRust side of items 2-4; the Anneal side
is evaluated on this state. -/
theorem wUnionMid2_two_sided_step_simulations :
    (evalStmt wUnionMidAnneal2 (mkStmt (.assign (local_ 5) (.use (.copy (local_ 4)))))
        wUnionWitnessMir.localDecls wUnionWitnessMir.layouts =
      MirStepNode.step (advanceStmt wUnionMidAnneal2
        (wUnionMidAnneal2.frame.locals.set 5
          (.init (.aggregate 0 [.unit, .scalar ⟨0x55, 1⟩, .unit, .unit])))
        wUnionMidAnneal2.memory) ∧
     ∃ m',
       Interp.step wUnionMidMach2 = .ok m' ∧
       Shape m' wUnionCtx2
         [wUnionCtx2.caller, calleeFrameL wUnionWitnessFn wUnionCtx2 (localsMap wUnionCtx2 8) 2 6]
         (wUnionCtx2.base ++ wUnionAllocs2.set 5
           (localAlloc wUnionCtx2 5 ⟨.Unsigned, ⟨4⟩⟩ [.Init 0x55 none, .Uninit, .Uninit, .Uninit])) ∧
       MiniRustUnionLocalStorage wUnionCtx2
         (wUnionAllocs2.set 5
           (localAlloc wUnionCtx2 5 ⟨.Unsigned, ⟨4⟩⟩ [.Init 0x55 none, .Uninit, .Uninit, .Uninit]))
         wUnionWitnessFn (localsMap wUnionCtx2 8) wUnionLayouts 5 wPUTy
         [(⟨0⟩, mrZstArrayTy 4), (⟨0⟩, .Int u8), (⟨0⟩, .Int u32), (⟨0⟩, mrUninhabitedZstTy)]
         4 4 (.init (.aggregate 0 [.unit, .scalar ⟨0x55, 1⟩, .unit, .unit]))
         [.Init 0x55 none, .Uninit, .Uninit, .Uninit]) ∧
    (∃ s', evalStmt wUnionMidAnneal2
        (mkStmt (.assign (local_ 3) (.use (.copy ⟨4, [.field 0 wZstArr4Ty]⟩))))
        wUnionWitnessMir.localDecls wUnionWitnessMir.layouts = MirStepNode.step s') ∧
    (∃ m',
      evalValue wUnionMidMach2 (.Load (.Field (.Local (localName 4)) 0)) =
        .ok ((.Tuple (List.replicate 4 (.Tuple [])), mrZstArrayTy 4), m')) ∧
    evalStmt wUnionMidAnneal2
        (mkStmt (.assign (local_ 7) (.use (.copy ⟨4, [.field 3 wVoidZstTy]⟩))))
        wUnionWitnessMir.localDecls wUnionWitnessMir.layouts = MirStepNode.fail .ub ∧
    evalValue wUnionMidMach2 (.Load (.Field (.Local (localName 4)) 3)) =
      .error (.ub "load at type but the data in memory violates the language invariant") ∧
    evalStmt wUnionMidAnneal2
        (mkStmt (.assign (local_ 0) (.use (.copy ⟨4, [.field 2 wU32Ty]⟩))))
        wUnionWitnessMir.localDecls wUnionWitnessMir.layouts = MirStepNode.fail .ub ∧
    evalValue wUnionMidMach2 (.Load (.Field (.Local (localName 4)) 2)) =
      .error (.ub "load at type but the data in memory violates the language invariant") := by
  refine ⟨step_union_whole_copy_minirust_simulation (body := wUnionWitnessMir)
      (s := wUnionMidAnneal2)
      wUnionMid2_shape wUnionMid2_storage4 wUnionMid2_storage5
      rfl rfl nofun rfl rfl rfl
      (tb := ⟨[.StorageLive (localName 3), .StorageLive (localName 4), .StorageLive (localName 5),
               .StorageLive (localName 6),
               .Assign (.Field (.Local (localName 4)) 1) (.Constant (.Int 0x55) (.Int u8)),
               .Assign (.Local (localName 5)) (.Load (.Local (localName 4))),
               .Assign (.Field (.Local (localName 5)) 0) (.Load (.Field (.Local (localName 4)) 0)),
               .Assign (.Local (localName 3)) (.Load (.Field (.Local (localName 5)) 0)),
               .Assign (.Local (localName 6)) (.Load (.Field (.Local (localName 5)) 1)),
               .Assign (.Local (localName 0)) (.UnOp (.Cast (.IntToInt u32)) (.Load (.Local (localName 6)))),
               .StorageDead (localName 6), .StorageDead (localName 5),
               .StorageDead (localName 4), .StorageDead (localName 3)],
              .Return, .Regular⟩)
      rfl (by decide) rfl,
    ⟨_, rfl⟩, ?_, rfl,
    evalValue_load_union_uninhabited_ub wUnionMid2_shape wUnionMid2_storage4 rfl,
    rfl,
    evalValue_load_union_int_uninit_ub wUnionMid2_shape wUnionMid2_storage4 rfl
      (.inr (.inr (.inl rfl))) (by decide) (by decide)⟩
  obtain ⟨m', hm', _⟩ :=
    evalValue_load_union_zstArray_field wUnionMid2_shape wUnionMid2_storage4 (j := 0) (N := 4) rfl
  exact ⟨m', hm'⟩

/-! ### Multi-Step Union Run Composition via `StateRelWithUnions`, `run_ret_withUnions`, and `run_ub_withUnions` (`R-d`)

Here `wUnionAutoFn` is computed directly by `translateFnWithUnions wUnionWitnessMir true`
(`wUnionAutoFn_eq`). We compose `step_union_whole_copy_stateRelWithUnions`
(which wraps `step_union_whole_copy_minirust_simulation`), the `[(); 4]` ZST
field write/read steps, the `u8` field read and `u32` cast, and
`step_return_withUnions` (`evalReturn_withUnions`, which tears down the live
`mrPU` union allocations and `[(); 4]` ZST allocation via `deallocAll_sized`)
into full multi-step runs via `run_ret_withUnions` (`bb2` -> `ReturnRel`) and
`run_ub_withUnions` (`bb3` -> `.error (.ub _)`). -/

/-- `translateFnWithUnions` succeeds on `wUnionWitnessMir`. -/
def wUnionAutoFn : Gen.Function :=
  (translateFnWithUnions wUnionWitnessMir true).get (by decide)

theorem wUnionAutoFn_eq :
    translateFnWithUnions wUnionWitnessMir true = some wUnionAutoFn := rfl

private def wUnionPUValU8 : Value :=
  .aggregate 0 [.unit, .scalar ⟨0x55, 1⟩, .unit, .unit]

private def wUnionPUValOverlay : Value :=
  .aggregate 0
    ([.unit, .unit, .unit, .unit] ++
      [.aggregate 0
        (MirSemantics.encodeRawAbstractByteVals
          [.init 0x55 none, .uninit, .uninit, .uninit])])

private def wUnionPUBytes55 : List Byte :=
  [.Init 0x55 none, .Uninit, .Uninit, .Uninit]

private def wUnionRunState (b k : Nat) (locs : List LocalSlot) : MachineState :=
  { frame := { blockIdx := b, stmtIdx := k, locals := locs }
    memory := (wUnionS0 b).memory }

private def wUnionRunMach (b mStmt : Nat) (L : List Gen.Allocation) : Mach :=
  { prog := emptyProg
    mem := { memory := { allocations := wUnionCtx2.base ++ L, _phantom := {} },
             accesses := [] }
    intptrcast := ⟨⟨[]⟩⟩
    threads := [thread1 wUnionCtx2
      [wUnionCtx2.caller, calleeFrameL wUnionAutoFn wUnionCtx2 (localsMap wUnionCtx2 8) b mStmt]]
    active_thread := 0
    synchronized_threads := ⟨[]⟩
    locks := []
    global_ptrs := ⟨[]⟩
    fn_ptrs := ⟨[]⟩
    vtable_ptrs := ⟨[]⟩
    stdout := ⟨[]⟩
    stderr := ⟨[]⟩ }

/-- General constructor establishing `StateRelWithUnionsAt` on `wUnionWitnessMir` /
`wUnionAutoFn` for any live 8-local allocation list `L = [a0..a7]` matching `locs`. -/
private theorem wUnionAuto_stateRelAt
    {b k mStmt : Nat} {s : MachineState} {m : Mach} {L : List Gen.Allocation}
    (hs_blk : s.frame.blockIdx = b)
    (hs_stmt : s.frame.stmtIdx = k)
    (hb : b < wUnionWitnessMir.basicBlocks.length)
    (hk : ∀ bb, wUnionWitnessMir.basicBlocks[b]? = some bb → k ≤ bb.statements.length)
    (hmem : s.memory = (wUnionS0 b).memory)
    (hsh : Shape m wUnionCtx2
      [wUnionCtx2.caller, calleeFrameL wUnionAutoFn wUnionCtx2 (localsMap wUnionCtx2 8) b mStmt]
      (wUnionCtx2.base ++ L))
    (hnloc : s.frame.locals.length = 8)
    (hL_len : L.length = 8)
    (hlive_slots : ∀ (j : Nat) (sl : LocalSlot), s.frame.locals[j]? = some sl → sl ≠ LocalSlot.dead)
    (hst0 : ∀ d slot, wUnionWitnessMir.localDecls[0]? = some d → s.frame.locals[0]? = some slot →
      LocalStorageWithUnions wUnionAutoFn wUnionCtx2 (wUnionCtx2.base ++ L)
        wUnionWitnessMir.layouts 0 d slot (localPtr wUnionCtx2 0))
    (hst1 : ∀ d slot, wUnionWitnessMir.localDecls[1]? = some d → s.frame.locals[1]? = some slot →
      LocalStorageWithUnions wUnionAutoFn wUnionCtx2 (wUnionCtx2.base ++ L)
        wUnionWitnessMir.layouts 1 d slot (localPtr wUnionCtx2 1))
    (hst2 : ∀ d slot, wUnionWitnessMir.localDecls[2]? = some d → s.frame.locals[2]? = some slot →
      LocalStorageWithUnions wUnionAutoFn wUnionCtx2 (wUnionCtx2.base ++ L)
        wUnionWitnessMir.layouts 2 d slot (localPtr wUnionCtx2 2))
    (hst3 : ∀ d slot, wUnionWitnessMir.localDecls[3]? = some d → s.frame.locals[3]? = some slot →
      LocalStorageWithUnions wUnionAutoFn wUnionCtx2 (wUnionCtx2.base ++ L)
        wUnionWitnessMir.layouts 3 d slot (localPtr wUnionCtx2 3))
    (hst4 : ∀ d slot, wUnionWitnessMir.localDecls[4]? = some d → s.frame.locals[4]? = some slot →
      LocalStorageWithUnions wUnionAutoFn wUnionCtx2 (wUnionCtx2.base ++ L)
        wUnionWitnessMir.layouts 4 d slot (localPtr wUnionCtx2 4))
    (hst5 : ∀ d slot, wUnionWitnessMir.localDecls[5]? = some d → s.frame.locals[5]? = some slot →
      LocalStorageWithUnions wUnionAutoFn wUnionCtx2 (wUnionCtx2.base ++ L)
        wUnionWitnessMir.layouts 5 d slot (localPtr wUnionCtx2 5))
    (hst6 : ∀ d slot, wUnionWitnessMir.localDecls[6]? = some d → s.frame.locals[6]? = some slot →
      LocalStorageWithUnions wUnionAutoFn wUnionCtx2 (wUnionCtx2.base ++ L)
        wUnionWitnessMir.layouts 6 d slot (localPtr wUnionCtx2 6))
    (hst7 : ∀ d slot, wUnionWitnessMir.localDecls[7]? = some d → s.frame.locals[7]? = some slot →
      LocalStorageWithUnions wUnionAutoFn wUnionCtx2 (wUnionCtx2.base ++ L)
        wUnionWitnessMir.layouts 7 d slot (localPtr wUnionCtx2 7)) :
    StateRelWithUnionsAt wUnionWitnessMir wUnionAutoFn wUnionCtx2 [] s s.frame.locals
      (localsMap wUnionCtx2 8) mStmt m where
  shape := ⟨by rw [hs_blk]; exact hsh.threads, hsh.active, rfl⟩
  retName := rfl
  locs := {
    nlocals := hnloc
    base := ⟨L, hsh.allocs⟩
    keysNodup := by decide
    keysLocal := fun e he => by
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp he
      exact ⟨i, by simp [wUnionWitnessMir]; exact List.mem_range.mp hi, rfl⟩
    live := fun i slot hs => by
      have hi : i < 8 := by have := (List.getElem?_eq_some_iff.mp hs).1; omega
      have hne := hlive_slots i slot hs
      have hmg : (mapGet (localsMap wUnionCtx2 8) (localName i)).isSome = true := by
        rw [mapGet_localsMap wUnionCtx2 8 i hi]; rfl
      exact ⟨fun _ => .inl hne, fun _ => hmg⟩
    storage := fun i d slot p hd hs hp => by
      rw [hsh.allocs]
      match i with
      | 0 => have hp' : p = localPtr wUnionCtx2 0 := Option.some.inj hp.symm; subst hp'; exact hst0 d slot hd hs
      | 1 => have hp' : p = localPtr wUnionCtx2 1 := Option.some.inj hp.symm; subst hp'; exact hst1 d slot hd hs
      | 2 => have hp' : p = localPtr wUnionCtx2 2 := Option.some.inj hp.symm; subst hp'; exact hst2 d slot hd hs
      | 3 => have hp' : p = localPtr wUnionCtx2 3 := Option.some.inj hp.symm; subst hp'; exact hst3 d slot hd hs
      | 4 => have hp' : p = localPtr wUnionCtx2 4 := Option.some.inj hp.symm; subst hp'; exact hst4 d slot hd hs
      | 5 => have hp' : p = localPtr wUnionCtx2 5 := Option.some.inj hp.symm; subst hp'; exact hst5 d slot hd hs
      | 6 => have hp' : p = localPtr wUnionCtx2 6 := Option.some.inj hp.symm; subst hp'; exact hst6 d slot hd hs
      | 7 => have hp' : p = localPtr wUnionCtx2 7 := Option.some.inj hp.symm; subst hp'; exact hst7 d slot hd hs
      | n + 8 => simp [wUnionWitnessMir] at hd
    inj := fun i j p q hp hq hpq => by
      simp only [localsMap, mapGet_range_map] at hp hq
      split at hp
      · split at hq
        · injection hp with hp; injection hq with hq; subst hp hq
          simp only [localPtr, wUnionCtx2, List.length_singleton, Option.some.injEq, Prod.mk.injEq] at hpq
          have h0 : ((1 + i : Nat) : Int) = ((1 + j : Nat) : Int) := congrArg (fun x => x._0) hpq.1
          omega
        · nomatch hq
      · nomatch hp
    owned := fun id a hA _ hb => by
      rw [hsh.allocs] at hA
      have hlen : (wUnionCtx2.base ++ L).length = 9 := by simp [wUnionCtx2, hL_len]
      have hid_lt : id < 9 := hlen ▸ (List.getElem?_eq_some_iff.mp hA).1
      have hid_ge : 1 ≤ id := by simpa [wUnionCtx2] using hb
      refine ⟨id - 1, localPtr wUnionCtx2 (id - 1),
        mapGet_localsMap wUnionCtx2 8 (id - 1) (by omega), ?_⟩
      simp only [localPtr, wUnionCtx2, List.length_singleton, Option.some.injEq, Prod.mk.injEq]
      exact ⟨by congr 1; omega, trivial⟩ }
  blk := by rw [hs_blk]; exact hb
  stmt := fun bb hbb => by rw [hs_blk] at hbb; rw [hs_stmt]; exact hk bb hbb
  stale := ⟨rfl, fun _ hj => absurd rfl hj⟩
  retLive := fun h0 => hlive_slots 0 .dead h0 rfl
  ret := fun d hd => by
    simp [wUnionWitnessMir] at hd; subst hd
    exact ⟨0, retAlloc, rfl, rfl, rfl, rfl, rfl, by decide⟩
  baseLow := by unfold BaseLow; decide
  borrows := by rw [hmem]; rfl
  callStack := by rw [hmem]; rfl
  activeCallee := by rw [hmem]; rfl
  protectors := by rw [hmem]; rfl
  callerLocals := by rw [hmem]; rfl

private theorem wUnionAuto_storage_fixed (L : List Gen.Allocation)
    (h1 : L[1]? = some (localAlloc wUnionCtx2 1 ⟨.Unsigned, ⟨4⟩⟩ (List.replicate 4 .Uninit)))
    (h2 : L[2]? = some (localAlloc wUnionCtx2 2 ⟨.Unsigned, ⟨4⟩⟩ (List.replicate 4 .Uninit)))
    (h3 : L[3]? = some (localAlloc wUnionCtx2 3 ⟨.Unsigned, ⟨1⟩⟩ []))
    (h4 : L[4]? = some (localAlloc wUnionCtx2 4 ⟨.Unsigned, ⟨4⟩⟩ wUnionPUBytes55))
    (h7 : L[7]? = some (localAlloc wUnionCtx2 7 ⟨.Unsigned, ⟨1⟩⟩ [])) :
    (∀ d slot, wUnionWitnessMir.localDecls[1]? = some d →
      (some LocalSlot.uninit) = some slot →
      LocalStorageWithUnions wUnionAutoFn wUnionCtx2 (wUnionCtx2.base ++ L)
        wUnionWitnessMir.layouts 1 d slot (localPtr wUnionCtx2 1)) ∧
    (∀ d slot, wUnionWitnessMir.localDecls[2]? = some d →
      (some LocalSlot.uninit) = some slot →
      LocalStorageWithUnions wUnionAutoFn wUnionCtx2 (wUnionCtx2.base ++ L)
        wUnionWitnessMir.layouts 2 d slot (localPtr wUnionCtx2 2)) ∧
    (∀ (slot3 : LocalSlot),
      (slot3 = .uninit ∨ slot3 = .init (.aggregate 0 (List.replicate 4 .unit)) ∨
        slot3 = .init (.aggregate 0 (List.replicate 4 (.aggregate 0 [])))) →
      ∀ d slot, wUnionWitnessMir.localDecls[3]? = some d →
        some slot3 = some slot →
        LocalStorageWithUnions wUnionAutoFn wUnionCtx2 (wUnionCtx2.base ++ L)
          wUnionWitnessMir.layouts 3 d slot (localPtr wUnionCtx2 3)) ∧
    (∀ d slot, wUnionWitnessMir.localDecls[4]? = some d →
      some (LocalSlot.init wUnionPUValU8) = some slot →
      LocalStorageWithUnions wUnionAutoFn wUnionCtx2 (wUnionCtx2.base ++ L)
        wUnionWitnessMir.layouts 4 d slot (localPtr wUnionCtx2 4)) ∧
    (∀ d slot, wUnionWitnessMir.localDecls[7]? = some d →
      (some LocalSlot.uninit) = some slot →
      LocalStorageWithUnions wUnionAutoFn wUnionCtx2 (wUnionCtx2.base ++ L)
        wUnionWitnessMir.layouts 7 d slot (localPtr wUnionCtx2 7)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro d slot hd hs
    injection hd with hd; subst hd; injection hs with hs; subst hs
    exact .union [(⟨0⟩, mrZstArrayTy 4), (⟨0⟩, .Int u32)] 4 4 2 (List.replicate 4 .Uninit)
      rfl (by decide) rfl rfl (by decide) (by decide) (by decide) (by decide) rfl
      (by simpa [wUnionCtx2, localAlloc, localPtr] using h1) rfl
  · intro d slot hd hs
    injection hd with hd; subst hd; injection hs with hs; subst hs
    exact .union [(⟨0⟩, mrZstArrayTy 4), (⟨0⟩, .Int u32)] 4 4 3 (List.replicate 4 .Uninit)
      rfl (by decide) rfl rfl (by decide) (by decide) (by decide) (by decide) rfl
      (by simpa [wUnionCtx2, localAlloc, localPtr] using h2) rfl
  · intro slot3 hsl3 d slot hd hs
    injection hd with hd; subst hd; injection hs with hs; subst hs
    exact .zstArray 4 4 rfl rfl rfl (by decide) (by decide) (by decide) hsl3
      (by simpa [wUnionCtx2, localAlloc, localPtr] using h3)
  · intro d slot hd hs
    injection hd with hd; subst hd; injection hs with hs; subst hs
    exact .union
      [(⟨0⟩, mrZstArrayTy 4), (⟨0⟩, .Int u8), (⟨0⟩, .Int u32), (⟨0⟩, mrUninhabitedZstTy)]
      4 4 5 wUnionPUBytes55 rfl (by decide) rfl rfl (by decide) (by decide) (by decide) (by decide)
      rfl (by simpa [wUnionCtx2, localAlloc, localPtr] using h4) ⟨rfl, _, rfl, rfl, rfl⟩
  · intro d slot hd hs
    injection hd with hd; subst hd; injection hs with hs; subst hs
    exact .zstUninhabited 8 rfl rfl rfl (by decide) (by decide) (by decide) rfl
      (by simpa [wUnionCtx2, localAlloc, localPtr] using h7)

private def wUnionRunAllocsCopied : List Gen.Allocation :=
  wUnionAllocs2.set 5 (localAlloc wUnionCtx2 5 ⟨.Unsigned, ⟨4⟩⟩ wUnionPUBytes55)

private def wUnionRunAllocsU8 : List Gen.Allocation :=
  wUnionRunAllocsCopied.set 6 (localAlloc wUnionCtx2 6 u8 (scalarBytes u8 0x55))

private def wUnionRunAllocsU32 : List Gen.Allocation :=
  wUnionRunAllocsU8.set 0 (localAlloc wUnionCtx2 0 u32 (scalarBytes u32 0x55))

private def wZstArr4UnitVal : Value := .aggregate 0 (List.replicate 4 .unit)

private def wUnionBb2S : Nat → MachineState
  | 0 => wUnionRunState 2 2 [.uninit, .uninit, .uninit, .init wZstArr4Val,
      .init wUnionPUValU8, .uninit, .uninit, .uninit]
  | 1 => wUnionRunState 2 3 [.uninit, .uninit, .uninit, .init wZstArr4Val,
      .init wUnionPUValU8, .init wUnionPUValU8, .uninit, .uninit]
  | 2 => wUnionRunState 2 4 [.uninit, .uninit, .uninit, .init wZstArr4Val,
      .init wUnionPUValU8, .init wUnionPUValOverlay, .uninit, .uninit]
  | 3 => wUnionRunState 2 5 [.uninit, .uninit, .uninit, .init wZstArr4UnitVal,
      .init wUnionPUValU8, .init wUnionPUValOverlay, .uninit, .uninit]
  | 4 => wUnionRunState 2 6 [.uninit, .uninit, .uninit, .init wZstArr4UnitVal,
      .init wUnionPUValU8, .init wUnionPUValOverlay, .init (.scalar ⟨0x55, 1⟩), .uninit]
  | _ => wUnionRunState 2 7 [.init (.scalar ⟨0x55, 4⟩), .uninit, .uninit, .init wZstArr4UnitVal,
      .init wUnionPUValU8, .init wUnionPUValOverlay, .init (.scalar ⟨0x55, 1⟩), .uninit]

private def wUnionBb2M0 : Mach := wUnionRunMach 2 6 wUnionAllocs2

private theorem wUnionBb2_storage4 :
    MiniRustUnionLocalStorage wUnionCtx2 wUnionAllocs2 wUnionAutoFn
      (localsMap wUnionCtx2 8) wUnionLayouts 4 wPUTy
      [(⟨0⟩, mrZstArrayTy 4), (⟨0⟩, .Int u8), (⟨0⟩, .Int u32), (⟨0⟩, mrUninhabitedZstTy)]
      4 4 (.init wUnionPUValU8) wUnionPUBytes55 where
  pos_size := by decide
  align_ok := by decide
  addr_nonneg := by decide
  addr_lt := by decide
  fn_local := rfl
  lm_ptr := rfl
  bytes_len := rfl
  alloc_eq := rfl
  slot_rel := ⟨rfl, _, rfl, rfl, rfl⟩

private theorem wUnionBb2_storage5 :
    MiniRustUnionLocalStorage wUnionCtx2 wUnionAllocs2 wUnionAutoFn
      (localsMap wUnionCtx2 8) wUnionLayouts 5 wPUTy
      [(⟨0⟩, mrZstArrayTy 4), (⟨0⟩, .Int u8), (⟨0⟩, .Int u32), (⟨0⟩, mrUninhabitedZstTy)]
      4 4 .uninit (List.replicate 4 .Uninit) where
  pos_size := by decide
  align_ok := by decide
  addr_nonneg := by decide
  addr_lt := by decide
  fn_local := rfl
  lm_ptr := rfl
  bytes_len := rfl
  alloc_eq := rfl
  slot_rel := rfl

private theorem wUnionBb2_rel0 :
    StateRelWithUnionsAt wUnionWitnessMir wUnionAutoFn wUnionCtx2 [] (wUnionBb2S 0)
      (wUnionBb2S 0).frame.locals (localsMap wUnionCtx2 8) 6 wUnionBb2M0 := by
  have hf := wUnionAuto_storage_fixed wUnionAllocs2 rfl rfl rfl rfl rfl
  refine wUnionAuto_stateRelAt (b := 2) (k := 2) (L := wUnionAllocs2) rfl rfl (by decide)
    (fun bb hbb => by simp [wUnionWitnessMir] at hbb; subst hbb; decide) rfl
    ⟨rfl, rfl, rfl⟩ rfl rfl
    (fun j sl hj => by
      match j with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => simp [wUnionBb2S, wUnionRunState] at hj; subst hj; nofun
      | n + 8 => simp [wUnionBb2S, wUnionRunState] at hj)
    (fun d slot hd hs => by
      injection hd with hd; subst hd; injection hs with hs; subst hs
      exact .base rfl rfl (declSlotOk_uninit _ _) ⟨1, rfl, by decide, ⟨by decide, by decide⟩, by decide, .inl (by decide), rfl⟩)
    hf.1 hf.2.1 (hf.2.2.1 _ (.inr (.inr rfl))) hf.2.2.2.1
    (fun d slot hd hs => by
      injection hd with hd; subst hd; injection hs with hs; subst hs
      exact LocalStorageWithUnions.ofMiniRustUnionLocalStorage rfl wUnionBb2_storage5)
    (fun d slot hd hs => by
      injection hd with hd; subst hd; injection hs with hs; subst hs
      exact .base rfl rfl (declSlotOk_uninit _ _) ⟨7, rfl, by decide, ⟨by decide, by decide⟩, by decide, .inl (by decide), rfl⟩)
    hf.2.2.2.2

private def wUnionBb2M1 : Mach := (Interp.step wUnionBb2M0).toOption.get (by decide)
private def wUnionBb2M2 : Mach := (Interp.step wUnionBb2M1).toOption.get (by decide)
private def wUnionBb2M3 : Mach := (Interp.step wUnionBb2M2).toOption.get (by decide)
private def wUnionBb2M4 : Mach := (Interp.step wUnionBb2M3).toOption.get (by decide)
private def wUnionBb2M5 : Mach := (Interp.step wUnionBb2M4).toOption.get (by decide)

private theorem wUnionBb2_step0_whole_copy :
    stepMirFn wUnionWitnessMir (wUnionBb2S 0) = .tau (.running (wUnionBb2S 1)) ∧
    Interp.step wUnionBb2M0 = .ok wUnionBb2M1 ∧
    StateRelWithUnionsAt wUnionWitnessMir wUnionAutoFn wUnionCtx2 [] (wUnionBb2S 1)
      (wUnionBb2S 1).frame.locals (localsMap wUnionCtx2 8) 7 wUnionBb2M1 ∧
    StateRelWithUnions wUnionWitnessMir wUnionAutoFn wUnionCtx2 (wUnionBb2S 1) wUnionBb2M1 := by
  obtain ⟨hA, m1, hM, hrel1, hrelU1⟩ :=
    step_union_whole_copy_stateRelWithUnions (body := wUnionWitnessMir) (f := wUnionAutoFn)
      (u := 4) (w := 5) (uDecl := wPUDecl) (wDecl := wPUDecl)
      rfl wUnionBb2_rel0 rfl wUnionBb2_storage4 wUnionBb2_storage5
      rfl rfl rfl rfl (by decide) rfl rfl nofun rfl rfl rfl (by decide) rfl (by decide)
  have hm1_eq : m1 = wUnionBb2M1 := by
    have h0 : Interp.step wUnionBb2M0 = .ok wUnionBb2M1 := rfl
    rw [h0] at hM; exact (Except.ok.inj hM).symm
  subst hm1_eq
  exact ⟨hA, rfl, hrel1, hrelU1⟩

private theorem wUnionBb2_rel2 :
    StateRelWithUnionsAt wUnionWitnessMir wUnionAutoFn wUnionCtx2 [] (wUnionBb2S 2)
      (wUnionBb2S 2).frame.locals (localsMap wUnionCtx2 8) 8 wUnionBb2M2 := by
  have hf := wUnionAuto_storage_fixed wUnionRunAllocsCopied rfl rfl rfl rfl rfl
  refine wUnionAuto_stateRelAt (b := 2) (k := 4) (L := wUnionRunAllocsCopied) rfl rfl (by decide)
    (fun bb hbb => by simp [wUnionWitnessMir] at hbb; subst hbb; decide) rfl
    ⟨rfl, rfl, rfl⟩ rfl rfl
    (fun j sl hj => by
      match j with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => simp [wUnionBb2S, wUnionRunState] at hj; subst hj; nofun
      | n + 8 => simp [wUnionBb2S, wUnionRunState] at hj)
    (fun d slot hd hs => by
      injection hd with hd; subst hd; injection hs with hs; subst hs
      exact .base rfl rfl (declSlotOk_uninit _ _) ⟨1, rfl, by decide, ⟨by decide, by decide⟩, by decide, .inl (by decide), rfl⟩)
    hf.1 hf.2.1 (hf.2.2.1 _ (.inr (.inr rfl))) hf.2.2.2.1
    (fun d slot hd hs => by
      injection hd with hd; subst hd; injection hs with hs; subst hs
      exact .union
        [(⟨0⟩, mrZstArrayTy 4), (⟨0⟩, .Int u8), (⟨0⟩, .Int u32), (⟨0⟩, mrUninhabitedZstTy)]
        4 4 6 wUnionPUBytes55 rfl (by decide) rfl rfl (by decide) (by decide) (by decide) (by decide)
        rfl rfl ⟨rfl, _, rfl, rfl, rfl⟩)
    (fun d slot hd hs => by
      injection hd with hd; subst hd; injection hs with hs; subst hs
      exact .base rfl rfl (declSlotOk_uninit _ _) ⟨7, rfl, by decide, ⟨by decide, by decide⟩, by decide, .inl (by decide), rfl⟩)
    hf.2.2.2.2

private theorem wUnionBb2_rel3 :
    StateRelWithUnionsAt wUnionWitnessMir wUnionAutoFn wUnionCtx2 [] (wUnionBb2S 3)
      (wUnionBb2S 3).frame.locals (localsMap wUnionCtx2 8) 9 wUnionBb2M3 := by
  have hf := wUnionAuto_storage_fixed wUnionRunAllocsCopied rfl rfl rfl rfl rfl
  refine wUnionAuto_stateRelAt (b := 2) (k := 5) (L := wUnionRunAllocsCopied) rfl rfl (by decide)
    (fun bb hbb => by simp [wUnionWitnessMir] at hbb; subst hbb; decide) rfl
    ⟨rfl, rfl, rfl⟩ rfl rfl
    (fun j sl hj => by
      match j with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => simp [wUnionBb2S, wUnionRunState] at hj; subst hj; nofun
      | n + 8 => simp [wUnionBb2S, wUnionRunState] at hj)
    (fun d slot hd hs => by
      injection hd with hd; subst hd; injection hs with hs; subst hs
      exact .base rfl rfl (declSlotOk_uninit _ _) ⟨1, rfl, by decide, ⟨by decide, by decide⟩, by decide, .inl (by decide), rfl⟩)
    hf.1 hf.2.1 (hf.2.2.1 _ (.inr (.inl rfl))) hf.2.2.2.1
    (fun d slot hd hs => by
      injection hd with hd; subst hd; injection hs with hs; subst hs
      exact .union
        [(⟨0⟩, mrZstArrayTy 4), (⟨0⟩, .Int u8), (⟨0⟩, .Int u32), (⟨0⟩, mrUninhabitedZstTy)]
        4 4 6 wUnionPUBytes55 rfl (by decide) rfl rfl (by decide) (by decide) (by decide) (by decide)
        rfl rfl ⟨rfl, _, rfl, rfl, rfl⟩)
    (fun d slot hd hs => by
      injection hd with hd; subst hd; injection hs with hs; subst hs
      exact .base rfl rfl (declSlotOk_uninit _ _) ⟨7, rfl, by decide, ⟨by decide, by decide⟩, by decide, .inl (by decide), rfl⟩)
    hf.2.2.2.2

private theorem wUnionBb2_rel4 :
    StateRelWithUnionsAt wUnionWitnessMir wUnionAutoFn wUnionCtx2 [] (wUnionBb2S 4)
      (wUnionBb2S 4).frame.locals (localsMap wUnionCtx2 8) 10 wUnionBb2M4 := by
  have hf := wUnionAuto_storage_fixed wUnionRunAllocsU8 rfl rfl rfl rfl rfl
  refine wUnionAuto_stateRelAt (b := 2) (k := 6) (L := wUnionRunAllocsU8) rfl rfl (by decide)
    (fun bb hbb => by simp [wUnionWitnessMir] at hbb; subst hbb; decide) rfl
    ⟨rfl, rfl, rfl⟩ rfl rfl
    (fun j sl hj => by
      match j with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => simp [wUnionBb2S, wUnionRunState] at hj; subst hj; nofun
      | n + 8 => simp [wUnionBb2S, wUnionRunState] at hj)
    (fun d slot hd hs => by
      injection hd with hd; subst hd; injection hs with hs; subst hs
      exact .base rfl rfl (declSlotOk_uninit _ _) ⟨1, rfl, by decide, ⟨by decide, by decide⟩, by decide, .inl (by decide), rfl⟩)
    hf.1 hf.2.1 (hf.2.2.1 _ (.inr (.inl rfl))) hf.2.2.2.1
    (fun d slot hd hs => by
      injection hd with hd; subst hd; injection hs with hs; subst hs
      exact .union
        [(⟨0⟩, mrZstArrayTy 4), (⟨0⟩, .Int u8), (⟨0⟩, .Int u32), (⟨0⟩, mrUninhabitedZstTy)]
        4 4 6 wUnionPUBytes55 rfl (by decide) rfl rfl (by decide) (by decide) (by decide) (by decide)
        rfl rfl ⟨rfl, _, rfl, rfl, rfl⟩)
    (fun d slot hd hs => by
      injection hd with hd; subst hd; injection hs with hs; subst hs
      exact .base rfl rfl ((DeclSlotOk_of_scalarTypeOf rfl _).mpr ⟨rfl, by decide⟩)
        ⟨7, rfl, by decide, ⟨by decide, by decide⟩, by decide, .inl (by decide), rfl⟩)
    hf.2.2.2.2

private theorem wUnionBb2_rel5 :
    StateRelWithUnionsAt wUnionWitnessMir wUnionAutoFn wUnionCtx2 [] (wUnionBb2S 5)
      (wUnionBb2S 5).frame.locals (localsMap wUnionCtx2 8) 11 wUnionBb2M5 := by
  have hf := wUnionAuto_storage_fixed wUnionRunAllocsU32 rfl rfl rfl rfl rfl
  refine wUnionAuto_stateRelAt (b := 2) (k := 7) (L := wUnionRunAllocsU32) rfl rfl (by decide)
    (fun bb hbb => by simp [wUnionWitnessMir] at hbb; subst hbb; decide) rfl
    ⟨rfl, rfl, rfl⟩ rfl rfl
    (fun j sl hj => by
      match j with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => simp [wUnionBb2S, wUnionRunState] at hj; subst hj; nofun
      | n + 8 => simp [wUnionBb2S, wUnionRunState] at hj)
    (fun d slot hd hs => by
      injection hd with hd; subst hd; injection hs with hs; subst hs
      exact .base rfl rfl ((DeclSlotOk_of_scalarTypeOf rfl _).mpr ⟨rfl, by decide⟩)
        ⟨1, rfl, by decide, ⟨by decide, by decide⟩, by decide, .inl (by decide), rfl⟩)
    hf.1 hf.2.1 (hf.2.2.1 _ (.inr (.inl rfl))) hf.2.2.2.1
    (fun d slot hd hs => by
      injection hd with hd; subst hd; injection hs with hs; subst hs
      exact .union
        [(⟨0⟩, mrZstArrayTy 4), (⟨0⟩, .Int u8), (⟨0⟩, .Int u32), (⟨0⟩, mrUninhabitedZstTy)]
        4 4 6 wUnionPUBytes55 rfl (by decide) rfl rfl (by decide) (by decide) (by decide) (by decide)
        rfl rfl ⟨rfl, _, rfl, rfl, rfl⟩)
    (fun d slot hd hs => by
      injection hd with hd; subst hd; injection hs with hs; subst hs
      exact .base rfl rfl ((DeclSlotOk_of_scalarTypeOf rfl _).mpr ⟨rfl, by decide⟩)
        ⟨7, rfl, by decide, ⟨by decide, by decide⟩, by decide, .inl (by decide), rfl⟩)
    hf.2.2.2.2

private def wUnionBb2Inv (s : MachineState) (m : Mach) : Prop :=
  (s = wUnionBb2S 0 ∧ m = wUnionBb2M0) ∨
  (s = wUnionBb2S 1 ∧ m = wUnionBb2M1) ∨
  (s = wUnionBb2S 2 ∧ m = wUnionBb2M2) ∨
  (s = wUnionBb2S 3 ∧ m = wUnionBb2M3) ∨
  (s = wUnionBb2S 4 ∧ m = wUnionBb2M4) ∨
  (s = wUnionBb2S 5 ∧ m = wUnionBb2M5)

private theorem wUnionBb2Inv_toStateRelWithUnions :
    ∀ s m, wUnionBb2Inv s m → StateRelWithUnions wUnionWitnessMir wUnionAutoFn wUnionCtx2 s m := by
  intro s m hi
  rcases hi with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨[], _, _, 6, wUnionBb2_rel0⟩
  · exact wUnionBb2_step0_whole_copy.2.2.2
  · exact ⟨[], _, _, 8, wUnionBb2_rel2⟩
  · exact ⟨[], _, _, 9, wUnionBb2_rel3⟩
  · exact ⟨[], _, _, 10, wUnionBb2_rel4⟩
  · exact ⟨[], _, _, 11, wUnionBb2_rel5⟩

private theorem wUnionBb2Inv_step :
    ∀ s m, wUnionBb2Inv s m →
      StepRelWithUnionsInv wUnionBb2Inv wUnionWitnessMir wUnionCtx2 s
        (stepMirFn wUnionWitnessMir s) m := by
  intro s m hi
  rcases hi with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · -- Step 0 (`_5 = copy _4`): discharged via `step_union_whole_copy_stateRelWithUnions`!
    rw [wUnionBb2_step0_whole_copy.1]
    exact ⟨1, wUnionBb2M1, Nat.le_refl 1, steps_one wUnionBb2_step0_whole_copy.2.1,
      .inr (.inl ⟨rfl, rfl⟩)⟩
  · -- Step 1 (`_5.0 = copy _3`)
    change StepRelWithUnionsInv wUnionBb2Inv wUnionWitnessMir wUnionCtx2 (wUnionBb2S 1)
      (.tau (.running (wUnionBb2S 2))) wUnionBb2M1
    exact ⟨1, wUnionBb2M2, Nat.le_refl 1, rfl, .inr (.inr (.inl ⟨rfl, rfl⟩))⟩
  · -- Step 2 (`_3 = copy (_5.0)`)
    change StepRelWithUnionsInv wUnionBb2Inv wUnionWitnessMir wUnionCtx2 (wUnionBb2S 2)
      (.tau (.running (wUnionBb2S 3))) wUnionBb2M2
    exact ⟨1, wUnionBb2M3, Nat.le_refl 1, rfl, .inr (.inr (.inr (.inl ⟨rfl, rfl⟩)))⟩
  · -- Step 3 (`_6 = copy (_5.1)`)
    change StepRelWithUnionsInv wUnionBb2Inv wUnionWitnessMir wUnionCtx2 (wUnionBb2S 3)
      (.tau (.running (wUnionBb2S 4))) wUnionBb2M3
    exact ⟨1, wUnionBb2M4, Nat.le_refl 1, rfl, .inr (.inr (.inr (.inr (.inl ⟨rfl, rfl⟩))))⟩
  · -- Step 4 (`_0 = _6 as u32`)
    change StepRelWithUnionsInv wUnionBb2Inv wUnionWitnessMir wUnionCtx2 (wUnionBb2S 4)
      (.tau (.running (wUnionBb2S 5))) wUnionBb2M4
    exact ⟨1, wUnionBb2M5, Nat.le_refl 1, rfl, .inr (.inr (.inr (.inr (.inr ⟨rfl, rfl⟩))))⟩
  · -- Step 5 (`return_`): discharged via `step_return_withUnions` (`deallocAll_sized`)!
    obtain ⟨hretOk, _⟩ :=
      step_return_withUnions wUnionBb2_rel5 rfl (bb := wUnionWitnessMir.basicBlocks[2]) rfl rfl rfl
        rfl rfl rfl (d0 := wU32Decl) rfl rfl rfl
    obtain ⟨hA, m', hm', hR⟩ := hretOk (.scalar ⟨0x55, 4⟩) rfl
    rw [hA]
    exact ⟨1, m', Nat.le_refl 1, steps_one hm', hR⟩

/-- **Multi-step `StateRelWithUnions` normal-return run composition (`R-d`)**:
Composes `step_union_whole_copy_stateRelWithUnions` (`step_union_whole_copy_minirust_simulation`),
0-byte `[(); 4]` ZST union arm write/read, `u8` payload read, `u32` cast, and
`step_return_withUnions` (`evalReturn_withUnions` tearing down the live `mrPU`
union allocations) via `run_ret_withUnions` on `wUnionAutoFn`
(`translateFnWithUnions wUnionWitnessMir true = some wUnionAutoFn`), proving
end-to-end `ReturnRel wUnionWitnessMir wUnionCtx2 s' (.scalar ⟨0x55, 4⟩) m'`. -/
theorem wUnionAuto_bb2_multi_step_returnRel_run :
    translateFnWithUnions wUnionWitnessMir true = some wUnionAutoFn ∧
    ∃ n s' mPre m',
      Interp.steps n wUnionBb2M0 = .ok m' ∧
      StateRelWithUnions wUnionWitnessMir wUnionAutoFn wUnionCtx2 s' mPre ∧
      ReturnRel wUnionWitnessMir wUnionCtx2 s' (.scalar ⟨0x55, 4⟩) m' := by
  have hret : ReachesRet (mirTree wUnionWitnessMir (wUnionBb2S 0)) []
      (.normal (.scalar ⟨0x55, 4⟩, (wUnionBb2S 0).memory)) :=
    reachesRet_step_tau (s' := wUnionBb2S 1) rfl <|
    reachesRet_step_tau (s' := wUnionBb2S 2) rfl <|
    reachesRet_step_tau (s' := wUnionBb2S 3) rfl <|
    reachesRet_step_tau (s' := wUnionBb2S 4) rfl <|
    reachesRet_step_tau (s' := wUnionBb2S 5) rfl <|
    runA_sound wUnionWitnessMir 2 (wUnionBb2S 5) []
      (.normal (.scalar ⟨0x55, 4⟩, (wUnionBb2S 0).memory)) rfl
  exact ⟨wUnionAutoFn_eq,
    run_ret_withUnions wUnionBb2Inv wUnionBb2Inv_toStateRelWithUnions wUnionBb2Inv_step
      (wUnionBb2S 0) wUnionBb2M0 (.inl ⟨rfl, rfl⟩) hret⟩

private def wUnionBb3S : Nat → MachineState
  | 0 => wUnionRunState 3 1 [.uninit, .uninit, .uninit, .uninit,
      .init wUnionPUValU8, .uninit, .uninit, .uninit]
  | _ => wUnionRunState 3 2 [.uninit, .uninit, .uninit, .uninit,
      .init wUnionPUValU8, .init wUnionPUValU8, .uninit, .uninit]

private def wUnionBb3M0 : Mach := wUnionRunMach 3 4 wUnionAllocs2
private def wUnionBb3M1 : Mach := (Interp.step wUnionBb3M0).toOption.get (by decide)

private theorem wUnionBb3_rel0 :
    StateRelWithUnionsAt wUnionWitnessMir wUnionAutoFn wUnionCtx2 [] (wUnionBb3S 0)
      (wUnionBb3S 0).frame.locals (localsMap wUnionCtx2 8) 4 wUnionBb3M0 := by
  have hf := wUnionAuto_storage_fixed wUnionAllocs2 rfl rfl rfl rfl rfl
  refine wUnionAuto_stateRelAt (b := 3) (k := 1) (L := wUnionAllocs2) rfl rfl (by decide)
    (fun bb hbb => by simp [wUnionWitnessMir] at hbb; subst hbb; decide) rfl
    ⟨rfl, rfl, rfl⟩ rfl rfl
    (fun j sl hj => by
      match j with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => simp [wUnionBb3S, wUnionRunState] at hj; subst hj; nofun
      | n + 8 => simp [wUnionBb3S, wUnionRunState] at hj)
    (fun d slot hd hs => by
      injection hd with hd; subst hd; injection hs with hs; subst hs
      exact .base rfl rfl (declSlotOk_uninit _ _) ⟨1, rfl, by decide, ⟨by decide, by decide⟩, by decide, .inl (by decide), rfl⟩)
    hf.1 hf.2.1 (hf.2.2.1 _ (.inl rfl)) hf.2.2.2.1
    (fun d slot hd hs => by
      injection hd with hd; subst hd; injection hs with hs; subst hs
      exact LocalStorageWithUnions.ofMiniRustUnionLocalStorage rfl wUnionBb2_storage5)
    (fun d slot hd hs => by
      injection hd with hd; subst hd; injection hs with hs; subst hs
      exact .base rfl rfl (declSlotOk_uninit _ _) ⟨7, rfl, by decide, ⟨by decide, by decide⟩, by decide, .inl (by decide), rfl⟩)
    hf.2.2.2.2

private theorem wUnionBb3_step0_whole_copy :
    stepMirFn wUnionWitnessMir (wUnionBb3S 0) = .tau (.running (wUnionBb3S 1)) ∧
    Interp.step wUnionBb3M0 = .ok wUnionBb3M1 ∧
    StateRelWithUnionsAt wUnionWitnessMir wUnionAutoFn wUnionCtx2 [] (wUnionBb3S 1)
      (wUnionBb3S 1).frame.locals (localsMap wUnionCtx2 8) 5 wUnionBb3M1 ∧
    StateRelWithUnions wUnionWitnessMir wUnionAutoFn wUnionCtx2 (wUnionBb3S 1) wUnionBb3M1 := by
  obtain ⟨hA, m1, hM, hrel1, hrelU1⟩ :=
    step_union_whole_copy_stateRelWithUnions (body := wUnionWitnessMir) (f := wUnionAutoFn)
      (u := 4) (w := 5) (uDecl := wPUDecl) (wDecl := wPUDecl)
      rfl wUnionBb3_rel0 rfl wUnionBb2_storage4 wUnionBb2_storage5
      rfl rfl rfl rfl (by decide) rfl rfl nofun rfl rfl rfl (by decide) rfl (by decide)
  have hm1_eq : m1 = wUnionBb3M1 := by
    have h0 : Interp.step wUnionBb3M0 = .ok wUnionBb3M1 := rfl
    rw [h0] at hM; exact (Except.ok.inj hM).symm
  subst hm1_eq
  exact ⟨hA, rfl, hrel1, hrelU1⟩

private def wUnionBb3Inv (s : MachineState) (m : Mach) : Prop :=
  (s = wUnionBb3S 0 ∧ m = wUnionBb3M0) ∨
  (s = wUnionBb3S 1 ∧ m = wUnionBb3M1)

private theorem wUnionBb3Inv_toStateRelWithUnions :
    ∀ s m, wUnionBb3Inv s m → StateRelWithUnions wUnionWitnessMir wUnionAutoFn wUnionCtx2 s m := by
  intro s m hi
  rcases hi with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨[], _, _, 4, wUnionBb3_rel0⟩
  · exact wUnionBb3_step0_whole_copy.2.2.2

private theorem wUnionBb3Inv_step :
    ∀ s m, wUnionBb3Inv s m →
      StepRelWithUnionsInv wUnionBb3Inv wUnionWitnessMir wUnionCtx2 s
        (stepMirFn wUnionWitnessMir s) m := by
  intro s m hi
  rcases hi with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [wUnionBb3_step0_whole_copy.1]
    exact ⟨1, wUnionBb3M1, Nat.le_refl 1, steps_one wUnionBb3_step0_whole_copy.2.1,
      .inr ⟨rfl, rfl⟩⟩
  · change StepRelWithUnionsInv wUnionBb3Inv wUnionWitnessMir wUnionCtx2 (wUnionBb3S 1)
      (MirStepNode.fail .ub) wUnionBb3M1
    exact ⟨1, "load at type but the data in memory violates the language invariant",
      Nat.le_refl 1, rfl⟩

/-- **Multi-step `StateRelWithUnions` UB run composition (`R-d`)**:
Composes `step_union_whole_copy_stateRelWithUnions` (`_5 = copy _4`, preserving
the 3 `.Uninit` padding bytes) followed by `_0 = copy (_5.2: u32)` (`FaultNow`)
via `run_ub_withUnions` on `wUnionAutoFn`. -/
theorem wUnionAuto_bb3_multi_step_ub_run :
    ∃ u,
      Trusted.ITree.Reaches (mirTree wUnionWitnessMir (wUnionBb3S 0)) [] u ∧
      Trusted.ITree.FaultNow u ∧
      ∃ n msg, Interp.steps n wUnionBb3M0 = .error (.ub msg) := by
  have hobs0 : (mirTree wUnionWitnessMir (wUnionBb3S 0)).observe =
      .tau (mirTree wUnionWitnessMir (wUnionBb3S 1)) := by
    simp [mirTree, Trusted.ITree.ITree.observe_cofix, stepMirState, wUnionBb3_step0_whole_copy.1,
      Trusted.ITree.ITreeF.map]
  have hreach : Trusted.ITree.Reaches (mirTree wUnionWitnessMir (wUnionBb3S 0)) []
      (mirTree wUnionWitnessMir (wUnionBb3S 1)) :=
    .tau hobs0 (.refl _)
  have hobs1 : (mirTree wUnionWitnessMir (wUnionBb3S 1)).observe =
      (MirStepNode.fail .ub).map (Trusted.ITree.ITree.cofix (stepMirState wUnionWitnessMir)) := by
    simp [mirTree, Trusted.ITree.ITree.observe_cofix, stepMirState]
    rfl
  have hfault : Trusted.ITree.FaultNow (mirTree wUnionWitnessMir (wUnionBb3S 1)) :=
    ⟨mirTree wUnionWitnessMir (wUnionBb3S 1), .inl (.fail .ub), _, .refl _, hobs1, trivial⟩
  exact ⟨mirTree wUnionWitnessMir (wUnionBb3S 1), hreach, hfault,
    run_ub_withUnions wUnionBb3Inv wUnionBb3Inv_toStateRelWithUnions wUnionBb3Inv_step
      (wUnionBb3S 0) wUnionBb3M0 (.inl ⟨rfl, rfl⟩) hreach hfault⟩

/-! ## `TerminatorKind.assert` (`assert cond expected target unwind`) Witnesses

`translateFnWithAssert` computes `assertWitnessFn` from `assertWitnessMir`
(`assertWitnessFn_eq`), and `assertWitnessFn` passes MiniRust's control-flow
well-formedness check (`assertWitnessFn_wf`). The witnesses cover:
1. passing `assert(cond == true)` and `assert(cond == false)`: a jump to the
   success block and a return;
2. an uninitialized `cond`: `.ub` in 1 step in both Anneal and MiniRust;
3. a failing `assert` with `unwind = .cleanup 2`: a 1-step jump to `bb2` in both;
4. a failing `assert` with `unwind = .unreachable`: `.ub` in both;
5. a failing `assert` with `unwind = .terminate`: an abort in both;
6. a failing `assert` with `unwind = .continue_` in the entry function: Anneal
   unwinds out of its root frame (`.panic`), and MiniRust aborts, as
   `mk_start_fn`'s unwind block does. -/

/-- Anneal MIR body exercising `TerminatorKind.assert`:
* `bb0`: `assert(copy _1 == true) -> [success: bb1, unwind: cleanup(bb2)]`
* `bb1`: `_0 = const 42_u32; return` (the success target)
* `bb2`: `_0 = const 99_u32; return` (the cleanup target). rustc's MIR validator
  rejects `return` in a cleanup block, but Anneal's semantics and the
  translation accept it, and it makes the cleanup edge observable as a return
  value.
* `bb3`: `assert(copy _1 == true) -> [success: bb1, unwind: unreachable]`
* `bb4`: `assert(copy _1 == false) -> [success: bb1, unwind: terminate]`
* `bb5`: `assert(copy _1 == true) -> [success: bb1, unwind: continue]` -/
def assertWitnessMir : CapturedMir where
  defPath := "witness::assert_terminator"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [u32Decl, boolDecl]
  basicBlocks := [
    -- `bb0`: `assert(copy _1 == true) -> [success: bb1, unwind: cleanup(bb2)]`
    { statements := [],
      terminator := mkTerm (.assert (.copy (local_ 1)) true 1 (.cleanup 2)),
      isCleanup := false },
    -- `bb1`: `_0 = 42_u32; return`
    { statements := [mkStmt (.assign (local_ 0) (.use (constU32 42)))],
      terminator := mkTerm .return_, isCleanup := false },
    -- `bb2`: `_0 = 99_u32; return`
    { statements := [mkStmt (.assign (local_ 0) (.use (constU32 99)))],
      terminator := mkTerm .return_, isCleanup := true },
    -- `bb3`: `assert(copy _1 == true) -> [success: bb1, unwind: unreachable]`
    { statements := [],
      terminator := mkTerm (.assert (.copy (local_ 1)) true 1 .unreachable),
      isCleanup := false },
    -- `bb4`: `assert(copy _1 == false) -> [success: bb1, unwind: terminate]`
    { statements := [],
      terminator := mkTerm (.assert (.copy (local_ 1)) false 1 .terminate),
      isCleanup := false },
    -- `bb5`: `assert(copy _1 == true) -> [success: bb1, unwind: continue]`
    { statements := [],
      terminator := mkTerm (.assert (.copy (local_ 1)) true 1 .continue_),
      isCleanup := false }]
  fnAbi := { args := [{ layout := wU8Layout, mode := .direct }],
             ret := { layout := u32Layout, mode := .direct }, conv := .rust, canUnwind := true }
  layouts := emptyLayoutTable
  allocations := []

theorem assertWitness_terms_ok :
    assertTerminatorOk assertWitnessMir.layouts assertWitnessMir.localDecls
      assertWitnessMir.basicBlocks.length (assertWitnessMir.basicBlocks[0]'(by decide)).terminator = true ∧
    assertTerminatorOk assertWitnessMir.layouts assertWitnessMir.localDecls
      assertWitnessMir.basicBlocks.length (assertWitnessMir.basicBlocks[3]'(by decide)).terminator = true ∧
    assertTerminatorOk assertWitnessMir.layouts assertWitnessMir.localDecls
      assertWitnessMir.basicBlocks.length (assertWitnessMir.basicBlocks[4]'(by decide)).terminator = true ∧
    assertTerminatorOk assertWitnessMir.layouts assertWitnessMir.localDecls
      assertWitnessMir.basicBlocks.length (assertWitnessMir.basicBlocks[5]'(by decide)).terminator = true :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The MiniRust function that `translateFnWithAssert` computes from
`assertWitnessMir` (`assertWitnessFn_eq`). `bb6` is `initBlock`. The failure
blocks of `bb3`, `bb4`, and `bb5` are the fresh blocks `bb8`, `bb10`, and
`bb12`; `assertFailTarget` skips `bb7`, `bb9`, `bb11`, and `bb13`, the names
`minimize` gives the `StartUnwind` blocks. -/
def assertWitnessFn : Gen.Function where
  locals := ⟨[(localName 0, .Int u32), (localName 1, .Bool)]⟩
  args := [localName 1]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[], .Switch (assertDiscrExpr true (.Load (.Local (localName 1))))
      ⟨[(1, bbName 1)]⟩ (bbName 2), .Regular⟩),
    (bbName 1, ⟨[.Assign (.Local (localName 0)) (.Constant (.Int 42) (.Int u32))],
      .Return, .Regular⟩),
    (bbName 2, ⟨[.Assign (.Local (localName 0)) (.Constant (.Int 99) (.Int u32))],
      .Return, .Regular⟩),
    (bbName 3, ⟨[], .Switch (assertDiscrExpr true (.Load (.Local (localName 1))))
      ⟨[(1, bbName 1)]⟩ (bbName 8), .Regular⟩),
    (bbName 4, ⟨[], .Switch (assertDiscrExpr false (.Load (.Local (localName 1))))
      ⟨[(1, bbName 1)]⟩ (bbName 10), .Regular⟩),
    (bbName 5, ⟨[], .Switch (assertDiscrExpr true (.Load (.Local (localName 1))))
      ⟨[(1, bbName 1)]⟩ (bbName 12), .Regular⟩),
    (bbName 6, ⟨[], .Goto (bbName 0), .Regular⟩),
    (bbName 8, ⟨[], .Unreachable, .Regular⟩),
    (bbName 10, ⟨[], abortTerminator, .Regular⟩),
    (bbName 12, ⟨[], abortTerminator, .Regular⟩)]⟩
  start := bbName 6
  implicit_writes := true

/-- `assertWitnessFn` is the translation of `assertWitnessMir`, not a
hand-written program. -/
theorem assertWitnessFn_eq : translateFnWithAssert assertWitnessMir = some assertWitnessFn := rfl

/-- `assertWitnessFn` is well formed: every `Switch` target has its source
block's kind (all `Regular`), and the locals, blocks, and start block are
consistent (`funcCfgWf`, MiniRust's `Function::check_wf` CFG clauses). -/
theorem assertWitnessFn_wf : funcCfgWf assertWitnessFn = true := by decide

def assertWitnessState (b : Nat) (locals : List LocalSlot) : MachineState :=
  { (initMachineState assertWitnessMir [.scalar ⟨1, 1⟩]) with
    frame := { blockIdx := b, stmtIdx := 0, locals := locals } }

def assertWitnessMach (b : Nat) (locals : List LocalSlot) : Mach :=
  machine assertWitnessMir assertWitnessFn locals (bbName b)

/-- **Witness 1 (Passing `assert(copy _1 == true)` and `assert(copy _1 == false)`)**:
* From `bb0` with `_1 = true` (`⟨1, 1⟩`), `assert(copy _1 == true)` jumps to `bb1`
  and returns `42_u32` in both Anneal and MiniRust (`Interp.steps 3`);
* From `bb4` with `_1 = false` (`⟨0, 1⟩`), `assert(copy _1 == false)` jumps to `bb1`
  and returns `42_u32` in both Anneal and MiniRust (`Interp.steps 3`). -/
theorem assert_pass_true_and_false_witness :
    let sTrue := assertWitnessState 0 [.uninit, .init (.scalar ⟨1, 1⟩)]
    let mTrue := assertWitnessMach 0 [.uninit, .init (.scalar ⟨1, 1⟩)]
    let sFalse := assertWitnessState 4 [.uninit, .init (.scalar ⟨0, 1⟩)]
    let mFalse := assertWitnessMach 4 [.uninit, .init (.scalar ⟨0, 1⟩)]
    stepMirFn assertWitnessMir sTrue =
      .step (assertWitnessState 1 [.uninit, .init (.scalar ⟨1, 1⟩)]) ∧
    ReachesRet (mirTree assertWitnessMir sTrue) [] (.normal (.scalar ⟨42, 4⟩, sTrue.memory)) ∧
    (Interp.steps 3 mTrue).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAlloc with data := scalarBytes u32 42 }, [1]) ∧
    stepMirFn assertWitnessMir sFalse =
      .step (assertWitnessState 1 [.uninit, .init (.scalar ⟨0, 1⟩)]) ∧
    ReachesRet (mirTree assertWitnessMir sFalse) [] (.normal (.scalar ⟨42, 4⟩, sFalse.memory)) ∧
    (Interp.steps 3 mFalse).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAlloc with data := scalarBytes u32 42 }, [1]) :=
  ⟨rfl, runA_sound assertWitnessMir 5 _ _ _ rfl, rfl,
   rfl, runA_sound assertWitnessMir 5 _ _ _ rfl, rfl⟩

/-- **Witness 2 (Failing `assert` with `unwind = .cleanup 2`)**:
From `bb0` with `_1 = false` (`⟨0, 1⟩`), `assert(copy _1 == true)` takes the
`.cleanup 2` branch in lockstep, jumping to `bb2` and returning `99_u32` in both
Anneal and MiniRust (`Interp.steps 3`). -/
theorem assert_fail_cleanup_witness :
    let sFail := assertWitnessState 0 [.uninit, .init (.scalar ⟨0, 1⟩)]
    let mFail := assertWitnessMach 0 [.uninit, .init (.scalar ⟨0, 1⟩)]
    stepMirFn assertWitnessMir sFail =
      .step (assertWitnessState 2 [.uninit, .init (.scalar ⟨0, 1⟩)]) ∧
    ReachesRet (mirTree assertWitnessMir sFail) [] (.normal (.scalar ⟨99, 4⟩, sFail.memory)) ∧
    (Interp.steps 3 mFail).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAlloc with data := scalarBytes u32 99 }, [1]) :=
  ⟨rfl, runA_sound assertWitnessMir 5 _ _ _ rfl, rfl⟩

/-- **Witness 3 (Uninitialized `cond` in `assert` -> 1-step `.ub`, and failing
`assert` with `unwind = .unreachable` -> `.ub`, and failing `assert` with
`unwind = .terminate` -> `retOutcome .abort` / `.abort`)**:
* From `bb3` with `_1 = .uninit`, `assert(copy _1 == true)` faults in 1 step with
  `.ub` in both Anneal (`stepMirFn = .fail .ub`) and MiniRust (`Interp.step = .error (.ub ...)`).
* From `bb3` with `_1 = false` (`⟨0, 1⟩`), `assert(copy _1 == true)` with
  `unwind = .unreachable` faults with `.ub` in Anneal and reaches
  `Interp.steps 2 = .error (.ub "reached unreachable code")` in MiniRust.
* From `bb4` with `_1 = true` (`⟨1, 1⟩`), `assert(copy _1 == false)` with
  `unwind = .terminate` returns `MirStepNode.retOutcome .abort` in Anneal and reaches
  `Interp.steps 2 = .error .abort` in MiniRust. -/
theorem assert_uninit_unreachable_and_terminate_witness :
    let sUninit := assertWitnessState 3 [.uninit, .uninit]
    let mUninit := assertWitnessMach 3 [.uninit, .uninit]
    let sUnreach := assertWitnessState 3 [.uninit, .init (.scalar ⟨0, 1⟩)]
    let mUnreach := assertWitnessMach 3 [.uninit, .init (.scalar ⟨0, 1⟩)]
    let sTerm := assertWitnessState 4 [.uninit, .init (.scalar ⟨1, 1⟩)]
    let mTerm := assertWitnessMach 4 [.uninit, .init (.scalar ⟨1, 1⟩)]
    stepMirFn assertWitnessMir sUninit = .fail .ub ∧
    Interp.step mUninit = .error (.ub "load at type but the data in memory violates the language invariant") ∧
    stepMirFn assertWitnessMir sUnreach = .fail .ub ∧
    Interp.steps 2 mUnreach = .error (.ub "reached unreachable code") ∧
    stepMirFn assertWitnessMir sTerm = .retOutcome .abort ∧
    Interp.steps 2 mTerm = .error .abort :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **Witness 4 (Failing `assert` with `unwind = .continue_` in the entry
function)**: From `bb5` with `_1 = false` (`⟨0, 1⟩`), `assert(copy _1 == true)`
fails. Anneal unwinds out of its root frame (`MirStepNode.retOutcome .panic`);
MiniRust's `Switch` falls back to the fresh `build::abort()` block `bb12`, which
stands for `mk_start_fn`'s unwind block, and aborts in its second step. -/
theorem assert_fail_continue_witness :
    let sCont := assertWitnessState 5 [.uninit, .init (.scalar ⟨0, 1⟩)]
    let mCont := assertWitnessMach 5 [.uninit, .init (.scalar ⟨0, 1⟩)]
    stepMirFn assertWitnessMir sCont = .retOutcome .panic ∧
    (Interp.step mCont).toOption.map
        (fun m => m.threads.map (fun t => t.stack.getLast?.map (·.next_block))) =
      some [some (bbName 12)] ∧
    Interp.steps 2 mCont = .error .abort :=
  ⟨rfl, rfl, rfl⟩

/-! ### Run-Level Correspondence Instantiations for `assertWitnessMir` (`G1`) -/

theorem assertWitnessMir_inFragmentWithAssert :
    inFragmentWithAssert assertWitnessMir = true := by decide

theorem ctx0_ok_u32_bool {body : CapturedMir} (h : body.localDecls = [u32Decl, boolDecl]) :
    CtxOk body ctx0 where
  baseLow := by unfold BaseLow; decide
  addrs := by
    intro i d _ hd; rw [h] at hd
    match i, hd with
    | 0, hd => simp at hd; subst hd; rw [u32Decl, u32Ty, itOf_uint, tyOf_uint]; decide
    | 1, hd => simp at hd; subst hd; rw [boolDecl, boolTy, itOf_bool, tyOf_bool]; decide
    | _ + 2, hd => simp at hd
  ret := by
    intro d hd; rw [h] at hd; simp at hd; subst hd
    exact ⟨0, retAlloc, rfl, rfl, rfl, rfl, rfl, by rw [u32Decl, u32Ty, itOf_uint]; decide⟩

def assertPassS0 : MachineState := initMachineState assertWitnessMir [.scalar ⟨1, 1⟩]
def assertPassMInit : Mach :=
  machine assertWitnessMir assertWitnessFn assertPassS0.frame.locals assertWitnessFn.start

def assertCleanupS0 : MachineState := initMachineState assertWitnessMir [.scalar ⟨0, 1⟩]
def assertCleanupMInit : Mach :=
  machine assertWitnessMir assertWitnessFn assertCleanupS0.frame.locals assertWitnessFn.start

theorem assertPass_anneal_ret :
    ReachesRet (mirCallTree assertWitnessMir [.scalar ⟨1, 1⟩]) []
      (.normal (.scalar ⟨42, 4⟩, assertPassS0.memory)) :=
  runA_sound assertWitnessMir 5 _ _ _ rfl

theorem assertCleanup_anneal_ret :
    ReachesRet (mirCallTree assertWitnessMir [.scalar ⟨0, 1⟩]) []
      (.normal (.scalar ⟨99, 4⟩, assertCleanupS0.memory)) :=
  runA_sound assertWitnessMir 5 _ _ _ rfl

/-- **End-to-end `mirCall_ret_withAssert` instantiation (passing `assert` -> `42_u32`)**:
Discharges `inFragmentWithAssert`, `translateFnWithAssert`, `CtxOk`, `argsOk`,
and `assertPass_anneal_ret` to conclude via `mirCall_ret_withAssert` that
MiniRust started at `assertWitnessFn.start` reaches `ReturnRel` writing
`scalarBytes u32 42` into `retAlloc`. -/
theorem assertPass_minirust_ret_from_start :
    ∃ (n : Nat) (m' : Mach), Interp.steps n assertPassMInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAlloc with data := scalarBytes u32 42 } ∧
      m'.threads = [thread1 ctx0 [{ callerFrame with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCall_ret_withAssert assertWitnessMir_inFragmentWithAssert assertWitnessFn_eq
      ctx0 (ctx0_ok_u32_bool rfl) [.scalar ⟨1, 1⟩] (by decide) assertPassMInit
      rfl rfl rfl assertPass_anneal_ret
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [assertWitnessMir] at hd; subst hd
  simp [retPtr, ctx0] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctx0] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

/-- **End-to-end `mirCall_ret_withAssert` instantiation (failing `assert` with
`.cleanup 2` -> `99_u32`)**:
Discharges `mirCall_ret_withAssert` on `assertWitnessMir` with `_1 = false`
(`⟨0, 1⟩`) to conclude that MiniRust started at `assertWitnessFn.start` steps
through the `.cleanup 2` edge and writes `scalarBytes u32 99` into `retAlloc`. -/
theorem assertCleanup_minirust_ret_from_start :
    ∃ (n : Nat) (m' : Mach), Interp.steps n assertCleanupMInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAlloc with data := scalarBytes u32 99 } ∧
      m'.threads = [thread1 ctx0 [{ callerFrame with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCall_ret_withAssert assertWitnessMir_inFragmentWithAssert assertWitnessFn_eq
      ctx0 (ctx0_ok_u32_bool rfl) [.scalar ⟨0, 1⟩] (by decide) assertCleanupMInit
      rfl rfl rfl assertCleanup_anneal_ret
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [assertWitnessMir] at hd; subst hd
  simp [retPtr, ctx0] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctx0] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

/-- Multi-arm `inFragmentWithAssert` body routing `mode : u32` (`_1`) and
`flag : bool` (`_2`) from `bb0` into `unwind = .unreachable` (`bb1`),
`unwind = .terminate` (`bb2`), and `unwind = .continue_` (`bb3`), so
`mirCall_ub_withAssert` and `mirCall_abort_or_panic_withAssert` are
instantiated from `f.start`. -/
def assertAllOutcomesMir : CapturedMir where
  defPath := "witness::assert_all_outcomes"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 2
  localDecls := [u32Decl, u32Decl, boolDecl]
  basicBlocks := [
    -- `bb0`: `switchInt(copy _1) -> [0: bb1, 1: bb2, _: bb3]`
    { statements := [],
      terminator := mkTerm (.switchInt (.copy (local_ 1))
        { branches := [(0, 1), (1, 2)], otherwise := 3 }),
      isCleanup := false },
    -- `bb1`: `assert(copy _2 == true) -> [success: bb4, unwind: unreachable]`
    { statements := [],
      terminator := mkTerm (.assert (.copy (local_ 2)) true 4 .unreachable),
      isCleanup := false },
    -- `bb2`: `assert(copy _2 == false) -> [success: bb4, unwind: terminate]`
    { statements := [],
      terminator := mkTerm (.assert (.copy (local_ 2)) false 4 .terminate),
      isCleanup := false },
    -- `bb3`: `assert(copy _2 == true) -> [success: bb4, unwind: continue]`
    { statements := [],
      terminator := mkTerm (.assert (.copy (local_ 2)) true 4 .continue_),
      isCleanup := false },
    -- `bb4`: `_0 = 42_u32; return`
    { statements := [mkStmt (.assign (local_ 0) (.use (constU32 42)))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := { args := [{ layout := u32Layout, mode := .direct },
                      { layout := wU8Layout, mode := .direct }],
             ret := { layout := u32Layout, mode := .direct }, conv := .rust, canUnwind := true }
  layouts := emptyLayoutTable
  allocations := []

theorem assertAllOutcomesMir_inFragmentWithAssert :
    inFragmentWithAssert assertAllOutcomesMir = true := by decide

def assertAllOutcomesFn : Gen.Function where
  locals := ⟨[(localName 0, .Int u32), (localName 1, .Int u32), (localName 2, .Bool)]⟩
  args := [localName 1, localName 2]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[], .Switch (.Load (.Local (localName 1)))
      ⟨[(0, bbName 1), (1, bbName 2)]⟩ (bbName 3), .Regular⟩),
    (bbName 1, ⟨[], .Switch (assertDiscrExpr true (.Load (.Local (localName 2))))
      ⟨[(1, bbName 4)]⟩ (bbName 6), .Regular⟩),
    (bbName 2, ⟨[], .Switch (assertDiscrExpr false (.Load (.Local (localName 2))))
      ⟨[(1, bbName 4)]⟩ (bbName 8), .Regular⟩),
    (bbName 3, ⟨[], .Switch (assertDiscrExpr true (.Load (.Local (localName 2))))
      ⟨[(1, bbName 4)]⟩ (bbName 10), .Regular⟩),
    (bbName 4, ⟨[.Assign (.Local (localName 0)) (.Constant (.Int 42) (.Int u32))],
      .Return, .Regular⟩),
    (bbName 5, ⟨[], .Goto (bbName 0), .Regular⟩),
    (bbName 6, ⟨[], .Unreachable, .Regular⟩),
    (bbName 8, ⟨[], abortTerminator, .Regular⟩),
    (bbName 10, ⟨[], abortTerminator, .Regular⟩)]⟩
  start := bbName 5
  implicit_writes := true

theorem assertAllOutcomesFn_eq :
    translateFnWithAssert assertAllOutcomesMir = some assertAllOutcomesFn := rfl

def ctx0_3 : Ctx :=
  { ctx0 with addrs := [128, 256, 384] }

theorem ctx0_ok_u32_u32_bool {body : CapturedMir}
    (h : body.localDecls = [u32Decl, u32Decl, boolDecl]) :
    CtxOk body ctx0_3 where
  baseLow := by unfold BaseLow; decide
  addrs := by
    intro i d _ hd; rw [h] at hd
    match i, hd with
    | 0, hd => simp at hd; subst hd; rw [u32Decl, u32Ty, itOf_uint, tyOf_uint]; decide
    | 1, hd => simp at hd; subst hd; rw [u32Decl, u32Ty, itOf_uint, tyOf_uint]; decide
    | 2, hd => simp at hd; subst hd; rw [boolDecl, boolTy, itOf_bool, tyOf_bool]; decide
    | _ + 3, hd => simp at hd
  ret := by
    intro d hd; rw [h] at hd; simp at hd; subst hd
    exact ⟨0, retAlloc, rfl, rfl, rfl, rfl, rfl, by rw [u32Decl, u32Ty, itOf_uint]; decide⟩

def assertUnreachCallS0 : MachineState :=
  initMachineState assertAllOutcomesMir [.scalar ⟨0, 4⟩, .scalar ⟨0, 1⟩]
def assertUnreachCallMInit : Mach :=
  machineWithCtx ctx0_3 assertAllOutcomesMir assertAllOutcomesFn assertUnreachCallS0.frame.locals assertAllOutcomesFn.start

def assertTermCallS0 : MachineState :=
  initMachineState assertAllOutcomesMir [.scalar ⟨1, 4⟩, .scalar ⟨1, 1⟩]
def assertTermCallMInit : Mach :=
  machineWithCtx ctx0_3 assertAllOutcomesMir assertAllOutcomesFn assertTermCallS0.frame.locals assertAllOutcomesFn.start

def assertContCallS0 : MachineState :=
  initMachineState assertAllOutcomesMir [.scalar ⟨2, 4⟩, .scalar ⟨0, 1⟩]
def assertContCallMInit : Mach :=
  machineWithCtx ctx0_3 assertAllOutcomesMir assertAllOutcomesFn assertContCallS0.frame.locals assertAllOutcomesFn.start

theorem assertUnreachCall_anneal_ub :
    ∃ tr u, Reaches (mirCallTree assertAllOutcomesMir [.scalar ⟨0, 4⟩, .scalar ⟨0, 1⟩]) tr u ∧ FaultNow u :=
  faultsA_sound assertAllOutcomesMir 5 _ (by decide)

/-- **End-to-end `mirCall_ub_withAssert` instantiation (failing `assert` with
`unwind = .unreachable` from `f.start`)**. -/
theorem assertUnreachCall_minirust_ub_from_start :
    ∃ (n : Nat) (msg : String), Interp.steps n assertUnreachCallMInit = .error (.ub msg) := by
  obtain ⟨tr, u, hr, hf⟩ := assertUnreachCall_anneal_ub
  exact mirCall_ub_withAssert assertAllOutcomesMir_inFragmentWithAssert assertAllOutcomesFn_eq
    ctx0_3 (ctx0_ok_u32_u32_bool rfl) [.scalar ⟨0, 4⟩, .scalar ⟨0, 1⟩] (by decide)
    assertUnreachCallMInit rfl rfl rfl hr hf

theorem assertTermCall_anneal_abort :
    ReachesRet (mirCallTree assertAllOutcomesMir [.scalar ⟨1, 4⟩, .scalar ⟨1, 1⟩])
      [⟨.inr (.inl (.emit (.event 1))), PUnit.unit⟩] .abort :=
  runA_sound assertAllOutcomesMir 5 _ _ _ rfl

theorem assertContCall_anneal_panic :
    ReachesRet (mirCallTree assertAllOutcomesMir [.scalar ⟨2, 4⟩, .scalar ⟨0, 1⟩])
      [⟨.inr (.inl (.emit (.event 2))), PUnit.unit⟩] .panic :=
  runA_sound assertAllOutcomesMir 5 _ _ _ rfl

/-- **End-to-end `mirCall_abort_or_panic_withAssert` instantiations (failing
`assert` with `unwind = .terminate` and `unwind = .continue_` from `f.start`)**. -/
theorem assertTermAndContCall_minirust_abort_from_start :
    (∃ n, Interp.steps n assertTermCallMInit = .error .abort) ∧
    (∃ n, Interp.steps n assertContCallMInit = .error .abort) :=
  ⟨mirCall_abort_or_panic_withAssert assertAllOutcomesMir_inFragmentWithAssert assertAllOutcomesFn_eq
     ctx0_3 (ctx0_ok_u32_u32_bool rfl) [.scalar ⟨1, 4⟩, .scalar ⟨1, 1⟩] (by decide)
     assertTermCallMInit rfl rfl rfl assertTermCall_anneal_abort (.inl rfl),
   mirCall_abort_or_panic_withAssert assertAllOutcomesMir_inFragmentWithAssert assertAllOutcomesFn_eq
     ctx0_3 (ctx0_ok_u32_u32_bool rfl) [.scalar ⟨2, 4⟩, .scalar ⟨0, 1⟩] (by decide)
     assertContCallMInit rfl rfl rfl assertContCall_anneal_panic (.inr rfl)⟩

end MiniRustSpec.Correspondence.Witness
