import Anneal.PureLift.V2026_06_01Bridge

/-!
# End-to-End `PureLift` ↔ Trusted `V2026_06_01` Bridge Regressions

Every canary below runs a concrete `CapturedMir` body on the trusted
`Trusted.Rustc.V2026_06_01.MirSemantics` machine (`initMachineState`,
`PureMirExec.mirStep`, `PureMirExec.runMirToBlock`) with real `Memory` and Tree
Borrows table, and relates it to a symbolic `PureLift` evaluation through
`Anneal.PureLift.V2026_06_01Bridge` (`mirSpatialModel`,
`mirOperationalAdapter`, `mir_pure_lift_sound`, `MirTypedByteCodec`):

1. **Sibling-field disjoint `&mut` reborrows** (`&mut p.0`, `&mut p.1`): the
   `PermTree` split and the two `LoanGraph` loans are realized on the live Tree
   Borrows table (two `reserved` tags rooted at `_3.0` and `_3.1`), and the
   lifted function converges on live MIR to the refined pair. Test 1b repeats
   it through a root `&mut (u32, u32)` parameter backed by
   `Memory.callerLocals`, checking `out.mutFinals` with
   `spatialFinalBindingsHold`.
2. **Diamond conditional borrow join** (`if c { &mut p.0 } else { &mut p.1 }`):
   one symbolic `PureLift` run with `symBool c` builds a `BackTarget.choice`
   loan whose `.choice` value is realized at the live join block `bb3`
   (`runMirToBlock`) for both oracles, and the post-join functional update
   refines both live returns. Test 2b simulates the diamond block for block:
   a 4-block `PureLift` `BlockCfg` is matched by header-targeted live runs
   into `bb1`/`bb2` and `bb3` under `mirCfgStateRel` (the joined loan realized
   on the live machine at `bb3`), and `mir_blockCfg_sound` concludes. Test 2c
   runs a 3-block `while` loop with a back-edge through
   `CfgCertificate.whileLoop` and `mir_cfgCertificate_sound`. Test 2b-sym
   replays the diamond from one symbolic entry state, where `stepBasicBlock`
   joins both arms into a single `.convergedJump 1` (one delay tick, pending
   `handleFreeOutOpt` guard) that `mirCfg_forwardSim_of_waitFree` and
   `mirCfg_forwardSim_of_emitsSubIdWraps` match with one header-targeted live
   run. Test 2b-cert certifies the same live body through `CfgCertificate.diamond`
   from the plan's `HoldsFnSpec` alone (`mir_diamond_cfgCertificate_sound`), for
   the symbolic oracle (`.convergedJump`) and the concrete one (path
   `0 → 1/2 → 3`), and through the `LocalBlockVC` route of
   `mir_cfgCertificate_sound` with the exact 2-point invariant; its fuel `3` is
   exact on both modes. Test 2b-asym
   replays an asymmetric 5-block diamond (`bb1 -> bb2` vs. `bb3`, `armSteps =
   Nat.max 2 1 = 2` with `.outOfFuel` at fuel `3` and convergence at fuel `4`),
   through `mir_blockCfg_sound`, through `CfgCertificate.asymDiamond` /
   `mir_asymDiamond_cfgCertificate_sound` for the symbolic oracle and for both
   concrete oracles (the 4-step `true` arm `0 → 1 → 2 → 4` simulated block for
   block at the certificate's exact fuel `4`), and as a segment
   (`mirCfg_segmentSim_of_emitsSubIdWraps`) landing exactly on the live join
   state, while the rejection canaries check that a rejecting wrapper, a
   block-level leaked handle (`diamondLeakRetBlocks`), or a guarded
   early-return leaked handle rejected by `.convergedJump`'s wrapper
   (`diamondGuardedLeakBlocks`) faults in both `stepBasicBlock` and
   `evalFnValue`. Test 2d certifies loops from strong-descent cutpoints
   (`rank s' < rank s`) with `mir_whileLoop_cfgCertificate_of_cutpoint` and
   `mir_whileLoop_cfgCertificate_of_cutpoint_blockRel`,
   including the stride-3 `while i < 5` loop whose live header computes
   `Lt(i, 5)` and whose rank drops `5 → 2 → 0`.
3. **Hybrid `SpatialPin` freeze → `zerocopy` byte write → unpin**: the frozen
   block is the place's trusted byte window (`TypedAt`), the spatial mutation
   writes exactly the bytes produced by the live raw-pointer `*mut u8` store,
   and unpinning decodes them as the trusted decoder does. Test 3b checks the
   4-state lockstep diagram; Test 3c instantiates the general
   `freeze_spatialPinnedBlockHolds` / `unpin_eq_live_mir_decode` bridges, also
   for a field-granular pin of `p.1` inside a live `(u32, u32)` aggregate whose
   sibling field and Tree Borrows table the store leaves untouched. Test 3d
   pins `p.1` while a sibling loan `&mut p.0` stays live and is used after the
   unpin; the general frame rules carry its binding through freeze, mutation
   and the live store, and unpinning restores the full two-loan relation.
   Test 3e repeats the whole-tuple bridge at the body's own tuple type and
   captured rustc layout (`u32PairLayoutMirCodec`, `FieldsShape.arbitrary
   [0, 4]`), with a reordered-layout falsification canary, the `zerocopy`
   marker traits across layouts, and the padded `(u8, u32)` trichotomy.
4. **Negative canaries**: overlapping `&mut` borrows are rejected by `PermTree`
   (and their conflicting accesses are Tree Borrows UB on live MIR); unpinning
   `.uninit` bytes or the invalid `bool` pattern `0x02` fails. Test 4c shows a
   live padded `(u8, u32)` place cannot complete the pin lifecycle: its
   window-faithful freeze is refused and no block mirroring its window unpins.

Like a real `anneal-rustc-capture` body, every fixture carries its own layout
table (`fixtureLayouts`), in which the `(u32, u32)` locals point at their own
rustc `TypeLayout` (`u32PairRustcLayout`) rather than at the `u32` entry.
-/

open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Anneal.PureLift
open Anneal.PureLift.MirLiftCoreInterop
open Anneal.PureLift.V2026_06_01Bridge

namespace PureLiftV2026BridgeTests

/-! ## Helpers -/

/-- rustc's `tcx.layout_of((u32, u32))` as `anneal-rustc-capture` serializes it:
size `8`, align `4`, a full-range `ScalarPair` backend, and in-order
`FieldsShape.arbitrary` offsets `[0, 4]` (`memoryIndex [0, 1]`). -/
def u32PairRustcLayout : TypeLayout :=
  { size := ⟨8⟩, align := ⟨4⟩,
    backendRepr :=
      .scalarPair (.initialized (.int 32 false) ⟨0, 4294967295⟩)
        (.initialized (.int 32 false) ⟨0, 4294967295⟩),
    fields := .arbitrary [⟨0⟩, ⟨4⟩] [0, 1], variants := .single 0,
    isUninhabited := false }

/-- Fixture layout table: entry `0` is the inherited `u32` layout and entry `1`
is the captured `(u32, u32)` layout that `pairTy` points at, as in a real
capture (every type carries its own `TypeLayout`). -/
def fixtureLayouts : LayoutTable :=
  { Anneal.PureMirExec.pureAdtMultiBlockBody.layouts with
    entries := Anneal.PureMirExec.pureAdtMultiBlockBody.layouts.entries ++ [u32PairRustcLayout] }

def pairTy : Ty := { kind := .tuple [.uint .u32, .uint .u32], layoutIdx := 1 }
def refU32Ty : Ty := { kind := .ref .mut (.uint .u32), layoutIdx := 0 }
def refPairTy : Ty := { kind := .ref .mut (.tuple [.uint .u32, .uint .u32]), layoutIdx := 0 }
def rawU32Ty : Ty := { kind := .rawPtr .mut (.uint .u32), layoutIdx := 0 }
def rawU8Ty : Ty := { kind := .rawPtr .mut (.uint .u8), layoutIdx := 0 }

def u32C (n : Nat) : Operand :=
  .constant { ty := u32Ty, val := .scalar (.int { bits := n, sizeBytes := 4 }) }

def u8C (n : Nat) : Operand :=
  .constant { ty := u8Ty, val := .scalar (.int { bits := n, sizeBytes := 1 }) }

def pl (l : Nat) (proj : List ProjectionElem := []) : Place :=
  { local_ := l, projection := proj }

def mkSt (k : StatementKind) : Statement :=
  { kind := k, span := "PureLiftV2026BridgeTests" }

def mkBb (ss : List Statement) (t : TerminatorKind) : BasicBlockData :=
  { statements := ss, terminator := { kind := t, span := "PureLiftV2026BridgeTests" },
    isCleanup := false }

def decl (m : Mutability) (ty : Ty) : LocalDecl :=
  { mutability := m, ty := ty, debugName := none }

def mkBody (argCount : Nat) (ds : List LocalDecl) (bbs : List BasicBlockData) :
    CapturedMir :=
  { Anneal.PureMirExec.pureAdtMultiBlockBody with
    argCount := argCount, localDecls := ds, basicBlocks := bbs, layouts := fixtureLayouts }

/-- `PureLift` loans are created in the same order as live MIR provenance tags,
which start at `1`. -/
def tagOfLoan (lid : LoanId) : Nat := lid + 1

def stdMkPair (a b : StdVal) : Option StdVal := some (.pair a b)

/-! ## Test 1: Sibling-Field Disjoint Mutable Reborrows -/

/-- `fn sibling(a: u32, b: u32) -> (u32, u32) { let mut p = (a, b);
let x = &mut p.0; let y = &mut p.1; *x = 10; *y = 20; p }` -/
def siblingBody : CapturedMir :=
  mkBody 2
    [decl .mut pairTy, decl .not u32Ty, decl .not u32Ty, decl .mut pairTy,
     decl .not refU32Ty, decl .not refU32Ty]
    [mkBb
      [mkSt (.storageLive 3),
       mkSt (.assign (pl 3) (.aggregate .tuple [.copy (pl 1), .copy (pl 2)])),
       mkSt (.storageLive 4),
       mkSt (.assign (pl 4) (.ref (.mut false) (pl 3 [.field 0 u32Ty]))),
       mkSt (.storageLive 5),
       mkSt (.assign (pl 5) (.ref (.mut false) (pl 3 [.field 1 u32Ty]))),
       mkSt (.assign (pl 4 [.deref]) (.use (u32C 10))),
       mkSt (.assign (pl 5 [.deref]) (.use (u32C 20))),
       mkSt (.storageDead 5),
       mkSt (.storageDead 4),
       mkSt (.assign (pl 0) (.use (.copy (pl 3)))),
       mkSt (.storageDead 3)]
      .return_]

def siblingMs0 : MachineState :=
  initMachineState siblingBody [.scalar ⟨7, 4⟩, .scalar ⟨9, 4⟩]

def siblingParams : List (ParamInput StdVal) := [⟨.byVal, .nat 7⟩, ⟨.byVal, .nat 9⟩]

/-- `PureLift` locals `0, 1, 2, 3, 4` are MIR `_1 .. _5`. -/
def siblingSplitPrefix : FlowPlan StdVal :=
  .seq (.act (.assign (.localSub 2 []) (.binary stdMkPair (.localSub 0 []) (.localSub 1 []))))
    (.seq (.act (.borrow 3 .mutBorrow (.localSub 2 [0])))
      (.act (.borrow 4 .mutBorrow (.localSub 2 [1]))))

def siblingPlan : FlowPlan StdVal :=
  .seq siblingSplitPrefix
    (.seq (.act (.assign (.derefSub 3 []) (.constVal (.nat 10))))
      (.seq (.act (.assign (.derefSub 4 []) (.constVal (.nat 20))))
        (.seq (.act (.endLoan 1)) (.act (.endLoan 0)))))

def siblingSt0 : SymState StdVal :=
  ⟨[⟨.nat 7, .unborrowed⟩, ⟨.nat 9, .unborrowed⟩], [], [], [], [], 0⟩

theorem sibling_init : initFnState stdValAlg siblingParams = .ok siblingSt0 := rfl

theorem sibling_entry_rel : mirStateRel tagOfLoan [] siblingSt0 siblingMs0 :=
  ⟨⟨trivial, trivial⟩,
   mirLocalsRel_of_localsRefine
     ⟨fun _ => ⟨_, rfl, .nat (by decide)⟩, fun _ => ⟨_, rfl, .nat (by decide)⟩, trivial⟩⟩

/-- `PureLift` result: the pair `(10, 20)`. -/
theorem sibling_pureLift_eval :
    evalFnValue stdValAlg siblingParams siblingPlan (.use (.localSub 2 [])) =
      .ok ⟨.pair (.nat 10) (.nat 20), []⟩ := rfl

/-- Live MIR state after the two sibling reborrows (statements `0 .. 5`): `_4`
and `_5` point into `_3` through two `reserved` Tree Borrows tags rooted at the
sibling places `_3.0` and `_3.1`. -/
def siblingMsSplit : MachineState :=
  { frame :=
      { blockIdx := 0, stmtIdx := 6,
        locals :=
          [.uninit, .init (.scalar ⟨7, 4⟩), .init (.scalar ⟨9, 4⟩),
           .init (.aggregate 0 [.scalar ⟨7, 4⟩, .scalar ⟨9, 4⟩]),
           .init (.ptr ⟨1, 0⟩ 8), .init (.ptr ⟨2, 0⟩ 8)] }
    memory :=
      { siblingMs0.memory with
        borrows :=
          [{ tag := 2, targetLocal := 3, targetProjection := [.field 1 u32Ty],
             perm := .reservedFrz false },
           { tag := 1, targetLocal := 3, targetProjection := [.field 0 u32Ty],
             perm := .reservedFrz false }]
        nextTag := 3 } }

theorem sibling_split_path :
    StepPath (Anneal.PureMirExec.mirStep siblingBody) siblingMs0 6 siblingMsSplit :=
  stepPath_of_runSilentSteps rfl

/-- `PureLift` state after the two sibling reborrows: the `PermTree` of `p`
(local `2`) is split into two sub-places mutably locked by loans `0` and `1`,
whose `LoanGraph` entries write back to `p.0` and `p.1`. -/
def siblingStSplit : SymState StdVal :=
  ⟨[⟨.nat 7, .unborrowed⟩, ⟨.nat 9, .unborrowed⟩,
    ⟨.pair (.nat 7) (.nat 9), .split [([0], .mutLocked 0), ([1], .mutLocked 1)]⟩,
    ⟨.refVal 0 [], .unborrowed⟩, ⟨.refVal 1 [], .unborrowed⟩],
   [⟨0, .activeMut, ⟨.nat 7, .unborrowed⟩, .direct (.localReg 2) [0]⟩,
    ⟨1, .activeMut, ⟨.nat 9, .unborrowed⟩, .direct (.localReg 2) [1]⟩],
   [], [], [], 0⟩

theorem sibling_split_eval :
    evalPlan stdValAlg siblingSplitPrefix siblingSt0 = .ok (.continuing siblingStSplit) :=
  rfl

/-- **The sibling split is realized on the live Tree Borrows table**: loan `0`
(`&mut p.0`) and loan `1` (`&mut p.1`) are bound to the disjoint MIR places
`_3.0` and `_3.1`, each carried by a live `reserved` tag, and every unborrowed
local (including both handles) is refined by its MIR slot. -/
theorem sibling_split_rel :
    mirStateRel tagOfLoan [(0, 3, [0]), (1, 3, [1])] siblingStSplit siblingMsSplit :=
  ⟨⟨⟨⟨Or.inr rfl, trivial⟩, ⟨trivial, trivial⟩⟩,
    ⟨⟨rfl, ⟨_, rfl, .nat (by decide)⟩, ⟨_, rfl, rfl, rfl, rfl⟩⟩,
     ⟨⟨rfl, ⟨_, rfl, .nat (by decide)⟩, ⟨_, rfl, rfl, rfl, rfl⟩⟩, trivial⟩⟩⟩,
   mirLocalsRel_of_localsRefine
     ⟨fun _ => ⟨_, rfl, .nat (by decide)⟩,
      fun _ => ⟨_, rfl, .nat (by decide)⟩,
      (fun h => nomatch h),
      fun _ => ⟨_, rfl, .ref rfl rfl rfl⟩,
      fun _ => ⟨_, rfl, .ref rfl rfl rfl⟩,
      trivial⟩⟩

/-- The two sibling loans are disjoint in `mirSpatialModel`. -/
theorem sibling_bindings_disjoint :
    (mirSpatialModel tagOfLoan).disjointSubPlaces 3 [0] 3 [1] :=
  mirSpatialModel_disjoint_siblings tagOfLoan 3 (by decide) [] []

/-- **Test 1 (adequacy)**: the lifted sibling-reborrow function converges on
live MIR (fuel-free) to a normal return refining the `PureLift` result. -/
theorem sibling_sound :
    Anneal.MirFuelFree.MirWpConverges siblingBody siblingMs0
      (LiftedMirPost tagOfLoan (fun out => out.ret = .pair (.nat 10) (.nat 20))) :=
  mir_pure_lift_sound_of_evalFuel tagOfLoan siblingBody [] siblingParams siblingPlan
    (.use (.localSub 2 [])) _ siblingMs0 ⟨.pair (.nat 10) (.nat 20), []⟩
    (.aggregate 0 [.scalar ⟨10, 4⟩, .scalar ⟨20, 4⟩]) _ 16 []
    ⟨siblingSt0, sibling_init, sibling_entry_rel⟩ sibling_pureLift_eval rfl rfl
    (.pair (.nat (by decide)) (.nat (by decide))) rfl

/-- **Test 1 (`CfgCertificate` adequacy via `mir_cfgCertificate_sound`)**:
verifies `siblingBody` through `CfgCertificate.singleBlock` and
`mir_cfgCertificate_sound`. -/
def siblingCert : CfgCertificate stdValAlg :=
  CfgCertificate.singleBlock stdValAlg siblingPlan (.use (.localSub 2 []))

def siblingCfgInv (bb : Nat) (st : SymState StdVal) : Prop :=
  bb = 0 ∧ st = siblingSt0

theorem sibling_cfgCertificate_sound :
    Anneal.MirFuelFree.MirWpConverges siblingBody siblingMs0
      (LiftedMirPost tagOfLoan (fun out => out.ret = .pair (.nat 10) (.nat 20))) :=
  mir_cfgCertificate_sound tagOfLoan siblingBody siblingCert siblingParams
    siblingSt0 (fun out => out.ret = .pair (.nat 10) (.nat 20))
    (fun _ => []) (fun _ => 0)
    (fun bb st ms => bb = 0 ∧ st = siblingSt0 ∧ ms = siblingMs0) []
    sibling_init rfl siblingCfgInv (fun _ => True)
    (fun _ _ ⟨hBb, hSt⟩ => by subst hBb; subst hSt; exact trivial)
    (fun _ _ ⟨hBb, hSt⟩ _ _ _ _ h => by subst hBb; subst hSt; exact nomatch h)
    ⟨rfl, rfl⟩
    (mirCfg_forwardSim_of_waitFree tagOfLoan siblingBody siblingCert.blocks
      (fun _ => []) (fun _ => 0)
      (fun bb st ms => bb = 0 ∧ st = siblingSt0 ∧ ms = siblingMs0) []
      (fun _ _ _ _ ⟨_, _, _, _, hBb, hSt, hMs⟩ => by
        subst hBb
        subst hSt
        subst hMs
        exact ⟨16, _, rfl, _, _, rfl,
          .pair (.nat (by decide)) (.nat (by decide)), rfl⟩))
    ⟨subIdWrap_some, rfl, rfl, sibling_entry_rel, rfl, rfl, rfl⟩

/-- Symbolic-input `PureLift` state after the two sibling reborrows. -/
def siblingSymStSplit (a b : Nat) : SymState StdVal :=
  ⟨[⟨.nat a, .unborrowed⟩, ⟨.nat b, .unborrowed⟩,
    ⟨.pair (.nat a) (.nat b), .split [([0], .mutLocked 0), ([1], .mutLocked 1)]⟩,
    ⟨.refVal 0 [], .unborrowed⟩, ⟨.refVal 1 [], .unborrowed⟩],
   [⟨0, .activeMut, ⟨.nat a, .unborrowed⟩, .direct (.localReg 2) [0]⟩,
    ⟨1, .activeMut, ⟨.nat b, .unborrowed⟩, .direct (.localReg 2) [1]⟩],
   [], [], [], 0⟩

/-- Symbolic-input live MIR state after the two sibling reborrows (`stmtIdx = 6`). -/
def siblingSymMsSplit (a b : Nat) : MachineState :=
  let ms0 := initMachineState siblingBody [.scalar ⟨a, 4⟩, .scalar ⟨b, 4⟩]
  { frame :=
      { blockIdx := 0, stmtIdx := 6,
        locals :=
          [.uninit, .init (.scalar ⟨a, 4⟩), .init (.scalar ⟨b, 4⟩),
           .init (.aggregate 0 [.scalar ⟨a, 4⟩, .scalar ⟨b, 4⟩]),
           .init (.ptr ⟨1, 0⟩ 8), .init (.ptr ⟨2, 0⟩ 8)] }
    memory :=
      { ms0.memory with
        borrows :=
          [{ tag := 2, targetLocal := 3, targetProjection := [.field 1 u32Ty],
             perm := .reservedFrz false },
           { tag := 1, targetLocal := 3, targetProjection := [.field 0 u32Ty],
             perm := .reservedFrz false }]
        nextTag := 3 } }

/-- Symbolic-input live MIR state after `*x = 10` (`stmtIdx = 7`). -/
def siblingSymMsAfterX (a b : Nat) : MachineState :=
  let ms0 := initMachineState siblingBody [.scalar ⟨a, 4⟩, .scalar ⟨b, 4⟩]
  { frame :=
      { blockIdx := 0, stmtIdx := 7,
        locals :=
          [.uninit, .init (.scalar ⟨a, 4⟩), .init (.scalar ⟨b, 4⟩),
           .init (.aggregate 0 [.scalar ⟨10, 4⟩, .scalar ⟨b, 4⟩]),
           .init (.ptr ⟨1, 0⟩ 8), .init (.ptr ⟨2, 0⟩ 8)] }
    memory :=
      { ms0.memory with
        borrows :=
          [{ tag := 2, targetLocal := 3, targetProjection := [.field 1 u32Ty],
             perm := .reservedFrz false },
           { tag := 1, targetLocal := 3, targetProjection := [.field 0 u32Ty],
             perm := .active }]
        nextTag := 3 } }

/-- **Test 1 (symbolic-input split realization & adequacy)**: for *all* symbolic
inputs `a, b < 256 ^ 4`, `siblingBody` reaches `siblingSymMsSplit a b` realizing
`siblingSymStSplit a b` under `mirStateRel`, and converges fuel-free from
`initMachineState siblingBody [.scalar ⟨a, 4⟩, .scalar ⟨b, 4⟩]` to a normal
return refining the `PureLift` output `(10, 20)`. -/
theorem sibling_symbolic_sound (a b : Nat) (ha : a < 256 ^ 4) (hb : b < 256 ^ 4) :
    mirStateRel tagOfLoan [(0, 3, [0]), (1, 3, [1])]
      (siblingSymStSplit a b) (siblingSymMsSplit a b) ∧
    Anneal.MirFuelFree.MirWpConverges siblingBody
      (initMachineState siblingBody [.scalar ⟨a, 4⟩, .scalar ⟨b, 4⟩])
      (LiftedMirPost tagOfLoan (fun out => out.ret = .pair (.nat 10) (.nat 20))) := by
  refine ⟨?_, ?_⟩
  · exact ⟨⟨⟨⟨Or.inr rfl, trivial⟩, ⟨trivial, trivial⟩⟩,
      ⟨⟨rfl, ⟨_, rfl, .nat ha⟩, ⟨_, rfl, rfl, rfl, rfl⟩⟩,
       ⟨⟨rfl, ⟨_, rfl, .nat hb⟩, ⟨_, rfl, rfl, rfl, rfl⟩⟩, trivial⟩⟩⟩,
     mirLocalsRel_of_localsRefine
      ⟨fun _ => ⟨_, rfl, .nat ha⟩,
       fun _ => ⟨_, rfl, .nat hb⟩,
       (fun h => nomatch h),
       fun _ => ⟨_, rfl, .ref rfl rfl rfl⟩,
       fun _ => ⟨_, rfl, .ref rfl rfl rfl⟩,
       trivial⟩⟩
  · have hPath1 :
        StepPath (Anneal.PureMirExec.mirStep siblingBody)
          (initMachineState siblingBody [.scalar ⟨a, 4⟩, .scalar ⟨b, 4⟩]) 6
          (siblingSymMsSplit a b) :=
      stepPath_of_runSilentSteps rfl
    have hPath2 :
        StepPath (Anneal.PureMirExec.mirStep siblingBody)
          (siblingSymMsSplit a b) 1 (siblingSymMsAfterX a b) :=
      stepPath_of_runSilentSteps rfl
    have hRun3 :
        Anneal.PureMirExec.evalFuel (Anneal.PureMirExec.mirStep siblingBody) 8
          (siblingSymMsAfterX a b) =
        .halted (.normal (.aggregate 0 [.scalar ⟨10, 4⟩, .scalar ⟨20, 4⟩],
          { (initMachineState siblingBody [.scalar ⟨a, 4⟩, .scalar ⟨b, 4⟩]).memory with
            borrows :=
              [{ tag := 2, targetLocal := 3, targetProjection := [.field 1 u32Ty], perm := .disabled, allocDead := true },
               { tag := 1, targetLocal := 3, targetProjection := [.field 0 u32Ty], perm := .disabled, allocDead := true }]
            nextTag := 3 })) := rfl
    obtain ⟨n, mFinal, hPath3, hDone⟩ := exists_stepPath_of_evalFuel_halted hRun3
    refine mir_pure_lift_sound tagOfLoan siblingBody []
      [⟨.byVal, .nat a⟩, ⟨.byVal, .nat b⟩] siblingPlan
      (.use (.localSub 2 [])) (fun out => out.ret = .pair (.nat 10) (.nat 20))
      (initMachineState siblingBody [.scalar ⟨a, 4⟩, .scalar ⟨b, 4⟩]) []
      ⟨⟨[⟨.nat a, .unborrowed⟩, ⟨.nat b, .unborrowed⟩], [], [], [], [], 0⟩, rfl,
       ⟨⟨trivial, trivial⟩,
        mirLocalsRel_of_localsRefine
          ⟨fun _ => ⟨_, rfl, .nat ha⟩, fun _ => ⟨_, rfl, .nat hb⟩, trivial⟩⟩⟩
      rfl ?_
    intro _ out _ _ hEval
    have hEvalEq :
        evalFnValue stdValAlg [⟨.byVal, .nat a⟩, ⟨.byVal, .nat b⟩] siblingPlan
          (.use (.localSub 2 [])) = .ok ⟨.pair (.nat 10) (.nat 20), []⟩ := rfl
    rw [hEvalEq] at hEval
    injection hEval with hOut
    subst hOut
    exact ⟨6 + (1 + n), mFinal, hPath1.trans (hPath2.trans hPath3),
      .aggregate 0 [.scalar ⟨10, 4⟩, .scalar ⟨20, 4⟩], _, hDone,
      .pair (.nat (by decide)) (.nat (by decide)), rfl⟩

/-! ### Test 1b: Root `&mut (u32, u32)` Parameter with Caller-Local Writeback (`spatialFinalBindingsHold`) -/

def unitTy : Ty := { kind := .tuple [], layoutIdx := 0 }

/-- `fn sibling_mut_param(p: &mut (u32, u32)) {
  let x = &mut (*p).0; let y = &mut (*p).1; *x = 100; *y = 200;
}` where `p` (`_1`) points to caller-owned local `4` in `ms.memory.callerLocals`. -/
def siblingMutParamBody : CapturedMir :=
  mkBody 1
    [decl .mut unitTy, decl .not refPairTy, decl .not refU32Ty, decl .not refU32Ty]
    [mkBb
      [mkSt (.storageLive 2),
       mkSt (.assign (pl 2) (.ref (.mut false) (pl 1 [.deref, .field 0 u32Ty]))),
       mkSt (.storageLive 3),
       mkSt (.assign (pl 3) (.ref (.mut false) (pl 1 [.deref, .field 1 u32Ty]))),
       mkSt (.assign (pl 2 [.deref]) (.use (u32C 100))),
       mkSt (.assign (pl 3 [.deref]) (.use (u32C 200))),
       mkSt (.storageDead 3),
       mkSt (.storageDead 2),
       mkSt (.assign (pl 0) (.aggregate .tuple []))]
      .return_]

/-- Initial machine state for `siblingMutParamBody`: `_1` holds `.ptr ⟨1, 0⟩ 8`,
where Tree Borrows tag `1` (`unique`) targets caller-owned local `4` (`≥
ms.frame.locals.length = 4`) in `memory.callerLocals`. -/
def siblingMutParamMs0 : MachineState :=
  let base := initMachineState siblingMutParamBody [.ptr ⟨1, 0⟩ 8]
  { base with
    memory :=
      { base.memory with
        borrows :=
          [{ tag := 1, targetLocal := 4, targetProjection := [], perm := .unique }]
        nextTag := 2
        callerLocals :=
          [.dead, .dead, .dead, .dead,
           .init (.aggregate 0 [.scalar ⟨7, 4⟩, .scalar ⟨9, 4⟩])] } }

def siblingMutParams : List (ParamInput StdVal) :=
  [⟨.mutRef 0 [], .pair (.nat 7) (.nat 9)⟩]

def siblingMutPlan : FlowPlan StdVal :=
  .seq (.act (.borrow 1 .mutBorrow (.derefSub 0 [0])))
    (.seq (.act (.borrow 2 .mutBorrow (.derefSub 0 [1])))
      (.seq (.act (.assign (.derefSub 1 []) (.constVal (.nat 100))))
        (.seq (.act (.assign (.derefSub 2 []) (.constVal (.nat 200))))
          (.seq (.act (.endLoan 2)) (.act (.endLoan 1))))))

def siblingMutSt0 : SymState StdVal :=
  ⟨[⟨.refVal 0 [], .unborrowed⟩],
   [⟨0, .activeMut, ⟨.pair (.nat 7) (.nat 9), .unborrowed⟩, .rootParam 0⟩],
   [], [], [], 0⟩

theorem siblingMut_init :
    initFnState stdValAlg siblingMutParams = .ok siblingMutSt0 := rfl

theorem siblingMut_entry_rel :
    mirStateRel tagOfLoan [(0, 4, [])] siblingMutSt0 siblingMutParamMs0 :=
  ⟨⟨⟨trivial, trivial⟩,
    ⟨⟨rfl, ⟨_, rfl, .pair (.nat (by decide)) (.nat (by decide))⟩,
      ⟨_, rfl, rfl, rfl, rfl⟩⟩, trivial⟩⟩,
   mirLocalsRel_of_localsRefine
     ⟨fun _ => ⟨_, rfl, .ref rfl rfl rfl⟩, trivial⟩⟩

theorem siblingMut_pureLift_eval :
    evalFnValue stdValAlg siblingMutParams siblingMutPlan (.constVal .unit) =
      .ok ⟨.unit, [.pair (.nat 100) (.nat 200)]⟩ := rfl

def siblingMutParamMemFinal : Memory :=
  match Anneal.PureMirExec.evalFuel (Anneal.PureMirExec.mirStep siblingMutParamBody) 16
      siblingMutParamMs0 with
  | .halted (.normal (_, mem)) => mem
  | _ => siblingMutParamMs0.memory

/-- **Test 1b (adequacy with `out.mutFinals` and `spatialFinalBindingsHold`)**:
`siblingMutParamBody` converges fuel-free on live MIR to a normal return whose
final `memory.callerLocals[4]` holds `(100, 200)` with a live mutation-granting
Tree Borrows entry for the caller's root `&mut` loan (`rootAddrs = [(0, 4, [])]`). -/
theorem siblingMut_sound :
    Anneal.MirFuelFree.MirWpConverges siblingMutParamBody siblingMutParamMs0
      (fun o =>
        LiftedMirPost tagOfLoan
          (fun out =>
            out.ret = .unit ∧ out.mutFinals = [.pair (.nat 100) (.nat 200)])
          o [(0, 4, [])]) :=
  mir_pure_lift_sound_of_evalFuel tagOfLoan siblingMutParamBody [(0, 4, [])]
    siblingMutParams siblingMutPlan (.constVal .unit) _ siblingMutParamMs0
    ⟨.unit, [.pair (.nat 100) (.nat 200)]⟩ (.aggregate 0 []) siblingMutParamMemFinal 16 [(0, 4, [])]
    ⟨siblingMutSt0, siblingMut_init, siblingMut_entry_rel⟩
    siblingMut_pureLift_eval ⟨rfl, rfl⟩ rfl .unitAgg
    ⟨⟨⟨.aggregate 0 [.scalar ⟨100, 4⟩, .scalar ⟨200, 4⟩], rfl,
       .pair (.nat (by decide)) (.nat (by decide))⟩,
      ⟨_, rfl, rfl, rfl, rfl⟩⟩, rfl⟩

/-! ## Test 2: Diamond Conditional Borrow Join (`BackTarget.choice`) -/

/-- `fn diamond(c: bool, x: u32, y: u32) -> (u32, u32) { let mut p = (x, y);
let r = if c { &mut p.0 } else { &mut p.1 }; *r = 50; p }` -/
def diamondBody : CapturedMir :=
  mkBody 3
    [decl .mut pairTy, decl .not boolTy, decl .not u32Ty, decl .not u32Ty,
     decl .mut pairTy, decl .not refU32Ty]
    [mkBb
      [mkSt (.storageLive 4),
       mkSt (.assign (pl 4) (.aggregate .tuple [.copy (pl 2), .copy (pl 3)])),
       mkSt (.storageLive 5)]
      (.switchInt (.copy (pl 1)) { branches := [(0, 2)], otherwise := 1 }),
     mkBb [mkSt (.assign (pl 5) (.ref (.mut false) (pl 4 [.field 0 u32Ty])))] (.goto 3),
     mkBb [mkSt (.assign (pl 5) (.ref (.mut false) (pl 4 [.field 1 u32Ty])))] (.goto 3),
     mkBb
      [mkSt (.assign (pl 5 [.deref]) (.use (u32C 50))),
       mkSt (.storageDead 5),
       mkSt (.assign (pl 0) (.use (.copy (pl 4)))),
       mkSt (.storageDead 4)]
      .return_]

def diamondMs0 (c : Bool) : MachineState :=
  initMachineState diamondBody [.scalar ⟨if c then 1 else 0, 1⟩, .scalar ⟨3, 4⟩, .scalar ⟨4, 4⟩]

def diamondParams (c : Bool) : List (ParamInput StdVal) :=
  [⟨.byVal, .symBool c⟩, ⟨.byVal, .nat 3⟩, ⟨.byVal, .nat 4⟩]

/-- Prefix up to the join: build `p`, then join the two branch borrows of
`p.0` / `p.1` into canonical loan `0`. -/
def diamondJoinPrefix : FlowPlan StdVal :=
  .seq (.act (.assign (.localSub 3 []) (.binary stdMkPair (.localSub 1 []) (.localSub 2 []))))
    (.branchExplicitJoin (.use (.localSub 0 []))
      (.act (.borrow 4 .mutBorrow (.localSub 3 [0])))
      (.act (.borrow 4 .mutBorrow (.localSub 3 [1])))
      [(0, 0)])

def diamondPlan : FlowPlan StdVal :=
  .seq diamondJoinPrefix
    (.seq (.act (.assign (.derefSub 4 []) (.constVal (.nat 50))))
      (.act (.endLoan 0)))

def diamondSt0 (c : Bool) : SymState StdVal :=
  ⟨[⟨.symBool c, .unborrowed⟩, ⟨.nat 3, .unborrowed⟩, ⟨.nat 4, .unborrowed⟩],
   [], [], [], [], 0⟩

theorem diamond_init (c : Bool) : initFnState stdValAlg (diamondParams c) = .ok (diamondSt0 c) :=
  rfl

theorem diamond_entry_rel (c : Bool) : mirStateRel tagOfLoan [] (diamondSt0 c) (diamondMs0 c) :=
  ⟨⟨trivial, trivial⟩,
   mirLocalsRel_of_localsRefine
     ⟨fun _ => ⟨_, rfl, .symBool c⟩, fun _ => ⟨_, rfl, .nat (by decide)⟩,
      fun _ => ⟨_, rfl, .nat (by decide)⟩, trivial⟩⟩

/-- Post-join `PureLift` state: the explicit join merges every local under the
symbolic oracle (`choice (symBool c) v v` for unchanged locals), locks both
fields of `p` by the joined loan `0`, and gives loan `0` the symbolic value
`choice (symBool c) 3 4` and the diamond backward target
`BackTarget.choice (symBool c) (p.0) (p.1)`. -/
def diamondStJoin (c : Bool) : SymState StdVal :=
  ⟨[⟨.choice (.symBool c) (.symBool c) (.symBool c), .unborrowed⟩,
    ⟨.choice (.symBool c) (.nat 3) (.nat 3), .unborrowed⟩,
    ⟨.choice (.symBool c) (.nat 4) (.nat 4), .unborrowed⟩,
    ⟨.pair (.choice (.symBool c) (.nat 3) (.nat 3)) (.choice (.symBool c) (.nat 4) (.nat 4)),
      .split [([0], .mutLocked 0), ([1], .mutLocked 0)]⟩,
    ⟨.refVal 0 [], .unborrowed⟩],
   [⟨0, .activeMut, ⟨.choice (.symBool c) (.nat 3) (.nat 4), .unborrowed⟩,
     BackTarget.choice (.symBool c) (.direct (.localReg 3) [0]) (.direct (.localReg 3) [1])⟩],
   [], [], [], 0⟩

/-- **The join builds a `BackTarget.choice` loan** (one symbolic run, both
oracles). -/
theorem diamond_join_choice_loan (c : Bool) :
    evalPlan stdValAlg diamondJoinPrefix (diamondSt0 c) =
      .ok (.continuing (diamondStJoin c)) := by
  cases c <;> rfl

/-- `PureLift` result: one symbolic post-join functional update for both
branches. -/
theorem diamond_pureLift_eval (c : Bool) :
    evalFnValue stdValAlg (diamondParams c) diamondPlan (.use (.localSub 3 [])) =
      .ok ⟨.pair (zipStdVal (.symBool c) (.nat 50) (.nat 3))
        (zipStdVal (.symBool c) (.nat 4) (.nat 50)), []⟩ := by
  cases c <;> rfl

/-- Live MIR state at the join block `bb3`: `_5` points to the selected field
of `_4` through the `reserved` tag `1`. -/
def diamondMsJoin (c : Bool) : MachineState :=
  { frame :=
      { blockIdx := 3, stmtIdx := 0,
        locals :=
          [.uninit, .init (.scalar ⟨if c then 1 else 0, 1⟩), .init (.scalar ⟨3, 4⟩),
           .init (.scalar ⟨4, 4⟩), .init (.aggregate 0 [.scalar ⟨3, 4⟩, .scalar ⟨4, 4⟩]),
           .init (.ptr ⟨1, 0⟩ 8)] }
    memory :=
      { (diamondMs0 c).memory with
        borrows :=
          [{ tag := 1, targetLocal := 4,
             targetProjection := [.field (if c then 0 else 1) u32Ty],
             perm := .reservedFrz false }]
        nextTag := 2 } }

theorem diamond_runMirToBlock (c : Bool) :
    Anneal.PureMirExec.runMirToBlock diamondBody 3 (diamondMs0 c) = .reached (diamondMsJoin c) := by
  cases c <;> rfl

/-- **The `.choice` loan is realized at the live join block** for both
oracles: loan `0` is bound to `_4.0` when `c` and to `_4.1` otherwise, carried
by the live `reserved` tag `1`, and its symbolic `.choice` value refines the
selected field. -/
theorem diamond_join_rel (c : Bool) :
    mirStateRel tagOfLoan [(0, 4, if c then [0] else [1])] (diamondStJoin c) (diamondMsJoin c) := by
  cases c
  · exact ⟨⟨⟨trivial, trivial⟩,
      ⟨⟨rfl, ⟨_, rfl, .choiceFalse (.nat (by decide))⟩, ⟨_, rfl, rfl, rfl, rfl⟩⟩, trivial⟩⟩,
     mirLocalsRel_of_localsRefine
      ⟨fun _ => ⟨_, rfl, .choiceFalse (.symBool false)⟩,
       fun _ => ⟨_, rfl, .choiceFalse (.nat (by decide))⟩,
       fun _ => ⟨_, rfl, .choiceFalse (.nat (by decide))⟩, (fun h => nomatch h),
       fun _ => ⟨_, rfl, .ref rfl rfl rfl⟩, trivial⟩⟩
  · exact ⟨⟨⟨trivial, trivial⟩,
      ⟨⟨rfl, ⟨_, rfl, .choiceTrue (.nat (by decide))⟩, ⟨_, rfl, rfl, rfl, rfl⟩⟩, trivial⟩⟩,
     mirLocalsRel_of_localsRefine
      ⟨fun _ => ⟨_, rfl, .choiceTrue (.symBool true)⟩,
       fun _ => ⟨_, rfl, .choiceTrue (.nat (by decide))⟩,
       fun _ => ⟨_, rfl, .choiceTrue (.nat (by decide))⟩, (fun h => nomatch h),
       fun _ => ⟨_, rfl, .ref rfl rfl rfl⟩, trivial⟩⟩

/-- Live return of the diamond for oracle `c`. -/
def diamondMirRet (c : Bool) : Value :=
  if c then .aggregate 0 [.scalar ⟨50, 4⟩, .scalar ⟨4, 4⟩]
  else .aggregate 0 [.scalar ⟨3, 4⟩, .scalar ⟨50, 4⟩]

theorem diamond_ret_refines (c : Bool) :
    StdValRefines tagOfLoan
      (.pair (zipStdVal (.symBool c) (.nat 50) (.nat 3))
        (zipStdVal (.symBool c) (.nat 4) (.nat 50)))
      (diamondMirRet c) := by
  cases c
  · exact .pair (.choiceFalse (.nat (by decide))) (.choiceFalse (.nat (by decide)))
  · exact .pair (.choiceTrue (.nat (by decide))) (.choiceTrue (.nat (by decide)))

/-- **Test 2 (adequacy)**: for both oracles, the single symbolic `PureLift`
evaluation's post-join update refines the live MIR return. -/
theorem diamond_sound (c : Bool) :
    Anneal.MirFuelFree.MirWpConverges diamondBody (diamondMs0 c)
      (LiftedMirPost tagOfLoan (fun out =>
        out.ret = .pair (zipStdVal (.symBool c) (.nat 50) (.nat 3))
          (zipStdVal (.symBool c) (.nat 4) (.nat 50)))) := by
  cases c
  · exact mir_pure_lift_sound_of_evalFuel tagOfLoan diamondBody [] (diamondParams false)
      diamondPlan (.use (.localSub 3 [])) _ (diamondMs0 false) _ (diamondMirRet false) _ 16 []
      ⟨_, diamond_init false, diamond_entry_rel false⟩ (diamond_pureLift_eval false) rfl rfl
      (diamond_ret_refines false) rfl
  · exact mir_pure_lift_sound_of_evalFuel tagOfLoan diamondBody [] (diamondParams true)
      diamondPlan (.use (.localSub 3 [])) _ (diamondMs0 true) _ (diamondMirRet true) _ 16 []
      ⟨_, diamond_init true, diamond_entry_rel true⟩ (diamond_pureLift_eval true) rfl rfl
      (diamond_ret_refines true) rfl

/-- **Test 2 (join decomposition)**: the same convergence factors through the
live join block: `runMirToBlock` reaches `bb3` in a state related to the
post-join `PureLift` state, and from the join the live machine returns the
refined value. -/
theorem diamond_sound_via_join (c : Bool) :
    Anneal.MirFuelFree.MirWpConverges diamondBody (diamondMs0 c)
      (fun o => Exists fun mem => o = .normal (diamondMirRet c, mem)) := by
  refine mirWpConverges_of_runMirToBlock_join (diamond_runMirToBlock c) (diamond_join_rel c) ?_
  intro ms hms _
  subst hms
  cases c
  · exact Anneal.PureMirExec.mirWpConverges_of_wpConverges ⟨16, _, rfl, _, rfl⟩
  · exact Anneal.PureMirExec.mirWpConverges_of_wpConverges ⟨16, _, rfl, _, rfl⟩

/-- Symbolic-input post-join `PureLift` state for arbitrary `x, y : Nat`. -/
def diamondSymStJoin (c : Bool) (x y : Nat) : SymState StdVal :=
  ⟨[⟨.choice (.symBool c) (.symBool c) (.symBool c), .unborrowed⟩,
    ⟨.choice (.symBool c) (.nat x) (.nat x), .unborrowed⟩,
    ⟨.choice (.symBool c) (.nat y) (.nat y), .unborrowed⟩,
    ⟨.pair (.choice (.symBool c) (.nat x) (.nat x)) (.choice (.symBool c) (.nat y) (.nat y)),
      .split [([0], .mutLocked 0), ([1], .mutLocked 0)]⟩,
    ⟨.refVal 0 [], .unborrowed⟩],
   [⟨0, .activeMut, ⟨.choice (.symBool c) (.nat x) (.nat y), .unborrowed⟩,
     BackTarget.choice (.symBool c) (.direct (.localReg 3) [0]) (.direct (.localReg 3) [1])⟩],
   [], [], [], 0⟩

/-- Symbolic-input live MIR state at the join block `bb3` for arbitrary `x, y : Nat`. -/
def diamondSymMsJoin (c : Bool) (x y : Nat) : MachineState :=
  let ms0 :=
    initMachineState diamondBody [.scalar ⟨if c then 1 else 0, 1⟩, .scalar ⟨x, 4⟩, .scalar ⟨y, 4⟩]
  { frame :=
      { blockIdx := 3, stmtIdx := 0,
        locals :=
          [.uninit, .init (.scalar ⟨if c then 1 else 0, 1⟩), .init (.scalar ⟨x, 4⟩),
           .init (.scalar ⟨y, 4⟩), .init (.aggregate 0 [.scalar ⟨x, 4⟩, .scalar ⟨y, 4⟩]),
           .init (.ptr ⟨1, 0⟩ 8)] }
    memory :=
      { ms0.memory with
        borrows :=
          [{ tag := 1, targetLocal := 4,
             targetProjection := [.field (if c then 0 else 1) u32Ty],
             perm := .reservedFrz false }]
        nextTag := 2 } }

/-- **Test 2 (symbolic-input join realization & adequacy)**: for *all* symbolic
inputs `c : Bool` and `x, y < 256 ^ 4`, `runMirToBlock diamondBody 3` reaches the
join block `bb3` in a state satisfying `mirStateRel` against `diamondSymStJoin c x y`
(`BackTarget.choice`), and `diamondBody` converges fuel-free (`MirWpConverges`) to
`LiftedMirPost` refining the symbolic post-join pair. -/
theorem diamond_symbolic_sound (c : Bool) (x y : Nat) (hx : x < 256 ^ 4) (hy : y < 256 ^ 4) :
    let ms0 :=
      initMachineState diamondBody [.scalar ⟨if c then 1 else 0, 1⟩, .scalar ⟨x, 4⟩, .scalar ⟨y, 4⟩]
    Anneal.PureMirExec.runMirToBlock diamondBody 3 ms0 =
      .reached (diamondSymMsJoin c x y) ∧
    mirStateRel tagOfLoan [(0, 4, if c then [0] else [1])]
      (diamondSymStJoin c x y) (diamondSymMsJoin c x y) ∧
    Anneal.MirFuelFree.MirWpConverges diamondBody ms0
      (LiftedMirPost tagOfLoan (fun out =>
        out.ret = .pair (zipStdVal (.symBool c) (.nat 50) (.nat x))
          (zipStdVal (.symBool c) (.nat y) (.nat 50)))) := by
  intro ms0
  cases c
  · refine ⟨rfl, ?_, ?_⟩
    · exact ⟨⟨⟨trivial, trivial⟩,
        ⟨⟨rfl, ⟨_, rfl, .choiceFalse (.nat hy)⟩, ⟨_, rfl, rfl, rfl, rfl⟩⟩, trivial⟩⟩,
       mirLocalsRel_of_localsRefine
        ⟨fun _ => ⟨_, rfl, .choiceFalse (.symBool false)⟩,
         fun _ => ⟨_, rfl, .choiceFalse (.nat hx)⟩,
         fun _ => ⟨_, rfl, .choiceFalse (.nat hy)⟩, (fun h => nomatch h),
         fun _ => ⟨_, rfl, .ref rfl rfl rfl⟩, trivial⟩⟩
    · exact mir_pure_lift_sound_of_evalFuel tagOfLoan diamondBody []
        [⟨.byVal, .symBool false⟩, ⟨.byVal, .nat x⟩, ⟨.byVal, .nat y⟩]
        diamondPlan (.use (.localSub 3 [])) _ ms0 _
        (.aggregate 0 [.scalar ⟨x, 4⟩, .scalar ⟨50, 4⟩]) _ 16 []
        ⟨_, rfl,
         ⟨⟨trivial, trivial⟩,
          mirLocalsRel_of_localsRefine
            ⟨fun _ => ⟨_, rfl, .symBool false⟩,
             fun _ => ⟨_, rfl, .nat hx⟩,
             fun _ => ⟨_, rfl, .nat hy⟩, trivial⟩⟩⟩
        rfl rfl rfl
        (.pair (.choiceFalse (.nat hx)) (.choiceFalse (.nat (by decide)))) rfl
  · refine ⟨rfl, ?_, ?_⟩
    · exact ⟨⟨⟨trivial, trivial⟩,
        ⟨⟨rfl, ⟨_, rfl, .choiceTrue (.nat hx)⟩, ⟨_, rfl, rfl, rfl, rfl⟩⟩, trivial⟩⟩,
       mirLocalsRel_of_localsRefine
        ⟨fun _ => ⟨_, rfl, .choiceTrue (.symBool true)⟩,
         fun _ => ⟨_, rfl, .choiceTrue (.nat hx)⟩,
         fun _ => ⟨_, rfl, .choiceTrue (.nat hy)⟩, (fun h => nomatch h),
         fun _ => ⟨_, rfl, .ref rfl rfl rfl⟩, trivial⟩⟩
    · exact mir_pure_lift_sound_of_evalFuel tagOfLoan diamondBody []
        [⟨.byVal, .symBool true⟩, ⟨.byVal, .nat x⟩, ⟨.byVal, .nat y⟩]
        diamondPlan (.use (.localSub 3 [])) _ ms0 _
        (.aggregate 0 [.scalar ⟨50, 4⟩, .scalar ⟨y, 4⟩]) _ 16 []
        ⟨_, rfl,
         ⟨⟨trivial, trivial⟩,
          mirLocalsRel_of_localsRefine
            ⟨fun _ => ⟨_, rfl, .symBool true⟩,
             fun _ => ⟨_, rfl, .nat hx⟩,
             fun _ => ⟨_, rfl, .nat hy⟩, trivial⟩⟩⟩
        rfl rfl rfl
        (.pair (.choiceTrue (.nat (by decide))) (.choiceTrue (.nat hy))) rfl

/-! ### Test 2b: Block-for-Block Diamond Simulation (`BlockCfg` ↔ live MIR blocks) -/

/-- `PureLift` block CFG of `diamond`, block-for-block with `diamondBody`:
`bb0` builds `p` and branches on `c`, `bb1` / `bb2` borrow `p.0` / `p.1`, and
`bb3` writes through the handle, ends the loan, and returns `p`. -/
def diamondBlocks : List (BasicBlock StdVal) :=
  [⟨.act (.assign (.localSub 3 []) (.binary stdMkPair (.localSub 1 []) (.localSub 2 []))),
     .branch (.use (.localSub 0 [])) 1 2⟩,
   ⟨.act (.borrow 4 .mutBorrow (.localSub 3 [0])), .goto 3⟩,
   ⟨.act (.borrow 4 .mutBorrow (.localSub 3 [1])), .goto 3⟩,
   ⟨.seq (.act (.assign (.derefSub 4 []) (.constVal (.nat 50)))) (.act (.endLoan 0)),
     .ret (.use (.localSub 3 []))⟩]

/-- Block-entry `PureLift` states for a concrete oracle `c`. -/
def dbSt0 (c : Bool) : SymState StdVal :=
  ⟨[⟨.bool c, .unborrowed⟩, ⟨.nat 3, .unborrowed⟩, ⟨.nat 4, .unborrowed⟩], [], [], [], [], 0⟩

def dbSt1 (c : Bool) : SymState StdVal :=
  ⟨[⟨.bool c, .unborrowed⟩, ⟨.nat 3, .unborrowed⟩, ⟨.nat 4, .unborrowed⟩,
    ⟨.pair (.nat 3) (.nat 4), .unborrowed⟩], [], [], [], [], 0⟩

def dbSt3 (c : Bool) : SymState StdVal :=
  ⟨[⟨.bool c, .unborrowed⟩, ⟨.nat 3, .unborrowed⟩, ⟨.nat 4, .unborrowed⟩,
    ⟨.pair (.nat 3) (.nat 4), .split [(if c then [0] else [1], .mutLocked 0)]⟩,
    ⟨.refVal 0 [], .unborrowed⟩],
   [⟨0, .activeMut, ⟨.nat (if c then 3 else 4), .unborrowed⟩,
     .direct (.localReg 3) (if c then [0] else [1])⟩],
   [], [], [], 0⟩

/-- Live MIR state at the header of the taken arm (`bb1` if `c`, else `bb2`). -/
def dbMsArm (c : Bool) : MachineState :=
  { frame :=
      { blockIdx := if c then 1 else 2, stmtIdx := 0,
        locals :=
          [.uninit, .init (.scalar ⟨if c then 1 else 0, 1⟩), .init (.scalar ⟨3, 4⟩),
           .init (.scalar ⟨4, 4⟩), .init (.aggregate 0 [.scalar ⟨3, 4⟩, .scalar ⟨4, 4⟩]),
           .uninit] }
    memory := (diamondMs0 c).memory }

/-- The block-level relation pins, for each `PureLift` block entry, the live MIR
state at the matching block header (`extra`), so every simulation obligation
is a concrete header-targeted live run; `mirCfgStateRel` additionally requires
the block-entry `PureLift` state to be realized there (the joined loan at
`bb3`). -/
def dbExtra (c : Bool) (bb : Nat) (st : SymState StdVal) (ms : MachineState) : Prop :=
  (bb = 0 ∧ st = dbSt0 c ∧ ms = diamondMs0 c) ∨
  (bb = (if c then 1 else 2) ∧ st = dbSt1 c ∧ ms = dbMsArm c) ∨
  (bb = 3 ∧ st = dbSt3 c ∧ ms = diamondMsJoin c)

def dbBindingsAt (c : Bool) (bb : Nat) : List (LoanId × Local × SubPath) :=
  if bb = 3 then [(0, 4, if c then [0] else [1])] else []

/-- `PureLift` result of the block CFG for oracle `c`. -/
def dbOut (c : Bool) : FuncOut StdVal :=
  ⟨if c then .pair (.nat 50) (.nat 4) else .pair (.nat 3) (.nat 50), []⟩

theorem db_cfg_wpConverges (c : Bool) :
    Anneal.PureMirExec.WpConverges (blockCfgStep (stepBasicBlock stdValAlg diamondBlocks))
      ⟨some, 0, dbSt0 c, 0⟩ (· = dbOut c) := by
  cases c <;> exact ⟨5, _, rfl, rfl⟩

theorem db_rel_arm (c : Bool) :
    mirStateRel tagOfLoan [] (dbSt1 c) (dbMsArm c) := by
  cases c <;>
  exact ⟨⟨trivial, trivial⟩,
    mirLocalsRel_of_localsRefine
      ⟨fun _ => ⟨_, rfl, .bool _⟩, fun _ => ⟨_, rfl, .nat (by decide)⟩,
       fun _ => ⟨_, rfl, .nat (by decide)⟩,
       fun _ => ⟨_, rfl, .pair (.nat (by decide)) (.nat (by decide))⟩, trivial⟩⟩

theorem db_rel_join (c : Bool) :
    mirStateRel tagOfLoan [(0, 4, if c then [0] else [1])] (dbSt3 c) (diamondMsJoin c) := by
  cases c <;>
  exact ⟨⟨⟨trivial, trivial⟩,
      ⟨⟨rfl, ⟨_, rfl, .nat (by decide)⟩, ⟨_, rfl, rfl, rfl, rfl⟩⟩, trivial⟩⟩,
    mirLocalsRel_of_localsRefine
      ⟨fun _ => ⟨_, rfl, .bool _⟩, fun _ => ⟨_, rfl, .nat (by decide)⟩,
       fun _ => ⟨_, rfl, .nat (by decide)⟩, (fun h => nomatch h),
       fun _ => ⟨_, rfl, .ref rfl rfl rfl⟩, trivial⟩⟩

/-- **Block-level forward simulation of the diamond**: every `PureLift` block
step is matched by a header-targeted live MIR run (`runMirToBlock`) into the
corresponding MIR block, and the return block by a live return refining the
`PureLift` output. -/
theorem db_forwardSim (c : Bool) :
    ForwardSim (blockCfgStep (stepBasicBlock stdValAlg diamondBlocks))
      (Anneal.PureMirExec.mirStep diamondBody)
      (mirCfgStateRel tagOfLoan (dbBindingsAt c) id (dbExtra c))
      (MirOutcomeRel tagOfLoan []) := by
  refine mirCfg_forwardSim_of_waitFree tagOfLoan diamondBody diamondBlocks
    (dbBindingsAt c) id (dbExtra c) [] ?_
  intro w bb st ms ⟨hW, _, _, _, hExtra⟩
  rcases hExtra with ⟨hBb, hSt, hMs⟩ | ⟨hBb, hSt, hMs⟩ | ⟨hBb, hSt, hMs⟩
  · subst hBb; subst hSt; subst hMs
    cases c
    · exact stepsTo_of_runMirToBlock_reached (rfl :
        Anneal.PureMirExec.runMirToBlock diamondBody 2 (diamondMs0 false) =
          .reached (dbMsArm false))
        ⟨hW, rfl, rfl, db_rel_arm false, Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)⟩
    · exact stepsTo_of_runMirToBlock_reached (rfl :
        Anneal.PureMirExec.runMirToBlock diamondBody 1 (diamondMs0 true) =
          .reached (dbMsArm true))
        ⟨hW, rfl, rfl, db_rel_arm true, Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)⟩
  · subst hSt; subst hMs
    cases c
    · subst hBb
      exact stepsTo_of_runMirToBlock_reached (rfl :
        Anneal.PureMirExec.runMirToBlock diamondBody 3 (dbMsArm false) =
          .reached (diamondMsJoin false))
        ⟨hW, rfl, rfl, db_rel_join false, Or.inr (Or.inr ⟨rfl, rfl, rfl⟩)⟩
    · subst hBb
      exact stepsTo_of_runMirToBlock_reached (rfl :
        Anneal.PureMirExec.runMirToBlock diamondBody 3 (dbMsArm true) =
          .reached (diamondMsJoin true))
        ⟨hW, rfl, rfl, db_rel_join true, Or.inr (Or.inr ⟨rfl, rfl, rfl⟩)⟩
  · subst hBb; subst hSt; subst hMs
    cases c
    · exact ⟨16, _, rfl, _, _, rfl, .pair (.nat (by decide)) (.nat (by decide)), rfl⟩
    · exact ⟨16, _, rfl, _, _, rfl, .pair (.nat (by decide)) (.nat (by decide)), rfl⟩

/-- **Test 2b (block-level adequacy)**: for each oracle, the `PureLift` block
CFG of the diamond simulates `diamondBody` block for block, realizing the
joined loan on the live machine at `bb3`, and the live body converges to the
refined post-join update (`mir_blockCfg_sound`). -/
theorem db_sound (c : Bool) :
    Anneal.MirFuelFree.MirWpConverges diamondBody (diamondMs0 c)
      (fun o => LiftedMirPost tagOfLoan (· = dbOut c) o []) :=
  mir_blockCfg_sound tagOfLoan diamondBody diamondBlocks (· = dbOut c)
    (dbBindingsAt c) id (dbExtra c) [] (db_forwardSim c) (db_cfg_wpConverges c)
    ⟨subIdWrap_some, rfl, rfl, ⟨⟨trivial, trivial⟩,
      mirLocalsRel_of_localsRefine
        ⟨fun _ => ⟨_, rfl, .bool c⟩, fun _ => ⟨_, rfl, .nat (by decide)⟩,
         fun _ => ⟨_, rfl, .nat (by decide)⟩, trivial⟩⟩,
     Or.inl ⟨rfl, rfl, rfl⟩⟩

/-! ### Test 2c: 3-Block `while` Loop with Back-Edge (`CfgCertificate.whileLoop` + `mir_cfgCertificate_sound`) -/

/-- `fn loop_borrow(mut flag: bool, mut x: u32) -> u32 {
  while flag { let r = &mut x; *r = 42; flag = false; } x
}` across 3 basic blocks (`bb0` header, `bb1` loop body with back-edge `.goto 0`,
`bb2` exit). -/
def loopBorrowBody : CapturedMir :=
  mkBody 2
    [decl .mut u32Ty, decl .mut boolTy, decl .mut u32Ty, decl .not refU32Ty]
    [mkBb [] (.switchInt (.copy (pl 1)) ⟨[(1, 1)], 2⟩),
     mkBb
       [mkSt (.storageLive 3),
        mkSt (.assign (pl 3) (.ref (.mut false) (pl 2))),
        mkSt (.assign (pl 3 [.deref]) (.use (u32C 42))),
        mkSt (.assign (pl 1) (.use (.constant { ty := boolTy, val := .scalar (.int ⟨0, 1⟩) })))]
       (.goto 0),
     mkBb
       [mkSt (.assign (pl 0) (.use (.copy (pl 2)))),
        mkSt (.storageDead 3)]
       .return_]

def lbMs0 : MachineState :=
  initMachineState loopBorrowBody [.scalar ⟨1, 1⟩, .scalar ⟨7, 4⟩]

def lbBodyPlan : FlowPlan StdVal :=
  .seq (.act (.borrow 2 .mutBorrow (.localSub 1 [])))
    (.seq (.act (.assign (.derefSub 2 []) (.constVal (.nat 42))))
      (.seq (.act (.endLoan 0))
        (.act (.assign (.localSub 0 []) (.constVal (.bool false))))))

theorem lbBodyPlan_wf : WfPlan stdValAlg lbBodyPlan := fun _ _ => rfl

theorem lbBodyPlan_continuing :
    ∀ s f, evalPlan stdValAlg lbBodyPlan s = .ok f → Exists fun s' => f = .continuing s' :=
  evalPlan_seq_continuing stdValAlg (fun _ _ => rfl) (fun _ _ => rfl)
    (evalPlan_act_continuing stdValAlg _)
    (evalPlan_seq_continuing stdValAlg (fun _ _ => rfl) (fun _ _ => rfl)
      (evalPlan_act_continuing stdValAlg _)
      (evalPlan_seq_continuing stdValAlg (fun _ _ => rfl) (fun _ _ => rfl)
        (evalPlan_act_continuing stdValAlg _) (evalPlan_act_continuing stdValAlg _)))

def loopBorrowCert : CfgCertificate stdValAlg :=
  CfgCertificate.whileLoop stdValAlg 1 (.use (.localSub 0 [])) lbBodyPlan
    (.use (.localSub 1 [])) lbBodyPlan_wf lbBodyPlan_continuing

def lbSt0 : SymState StdVal :=
  ⟨[⟨.bool true, .unborrowed⟩, ⟨.nat 7, .unborrowed⟩], [], [], [], [], 0⟩

def lbStAfterIter : SymState StdVal :=
  ⟨[⟨.bool false, .unborrowed⟩, ⟨.nat 42, .unborrowed⟩, ⟨.refVal 0 [], .unborrowed⟩],
   [⟨0, .ended, ⟨.nat 42, .unborrowed⟩, .direct (.localReg 1) []⟩],
   [], [], [], 0⟩

def lbMsBody : MachineState :=
  { lbMs0 with frame := { lbMs0.frame with blockIdx := 1, stmtIdx := 0 } }

def lbMsAfterIter : MachineState :=
  { frame :=
      { blockIdx := 0, stmtIdx := 0,
        locals :=
          [.uninit, .init (.scalar ⟨0, 1⟩), .init (.scalar ⟨42, 4⟩), .init (.ptr ⟨1, 0⟩ 8)] }
    memory :=
      { lbMs0.memory with
        borrows :=
          [{ tag := 1, targetLocal := 2, targetProjection := [], perm := .active }]
        nextTag := 2 } }

def lbMsExit : MachineState :=
  { lbMsAfterIter with frame := { lbMsAfterIter.frame with blockIdx := 2, stmtIdx := 0 } }

def lbBlockInv (bb : Nat) (st : SymState StdVal) : Prop :=
  (bb = 0 ∧ st = lbSt0) ∨
  (bb = 1 ∧ st = lbSt0) ∨
  (bb = 0 ∧ st = lbStAfterIter) ∨
  (bb = 2 ∧ st = lbStAfterIter)

def lbExtra (bb : Nat) (st : SymState StdVal) (ms : MachineState) : Prop :=
  (bb = 0 ∧ st = lbSt0 ∧ ms = lbMs0) ∨
  (bb = 1 ∧ st = lbSt0 ∧ ms = lbMsBody) ∨
  (bb = 0 ∧ st = lbStAfterIter ∧ ms = lbMsAfterIter) ∨
  (bb = 2 ∧ st = lbStAfterIter ∧ ms = lbMsExit)

/-- **Test 2c (3-block while-loop adequacy via `CfgCertificate.whileLoop` and
`mir_cfgCertificate_sound`)**: verifies `loopBorrowBody` across `bb0 -> bb1 ->
bb0 -> bb2`, matching the loop header branch, the back-edge jump `bb1 -> bb0`,
and the exit jump `bb0 -> bb2` with `runMirToBlock`. -/
theorem loopBorrow_cfgCertificate_sound :
    Anneal.MirFuelFree.MirWpConverges loopBorrowBody lbMs0
      (LiftedMirPost tagOfLoan (fun out => out.ret = .nat 42)) := by
  have hRel0 : mirStateRel tagOfLoan [] lbSt0 lbMs0 :=
    ⟨⟨trivial, trivial⟩,
     mirLocalsRel_of_localsRefine
       ⟨fun _ => ⟨_, rfl, .bool true⟩, fun _ => ⟨_, rfl, .nat (by decide)⟩, trivial⟩⟩
  have hRelBody : mirStateRel tagOfLoan [] lbSt0 lbMsBody :=
    ⟨⟨trivial, trivial⟩,
     mirLocalsRel_of_localsRefine
       ⟨fun _ => ⟨_, rfl, .bool true⟩, fun _ => ⟨_, rfl, .nat (by decide)⟩, trivial⟩⟩
  have hRelAfter : mirStateRel tagOfLoan [] lbStAfterIter lbMsAfterIter :=
    ⟨⟨trivial, trivial⟩,
     mirLocalsRel_of_localsRefine
       ⟨fun _ => ⟨_, rfl, .bool false⟩, fun _ => ⟨_, rfl, .nat (by decide)⟩,
        fun _ => ⟨_, rfl, .ref rfl rfl rfl⟩, trivial⟩⟩
  have hRelExit : mirStateRel tagOfLoan [] lbStAfterIter lbMsExit :=
    ⟨⟨trivial, trivial⟩,
     mirLocalsRel_of_localsRefine
       ⟨fun _ => ⟨_, rfl, .bool false⟩, fun _ => ⟨_, rfl, .nat (by decide)⟩,
        fun _ => ⟨_, rfl, .ref rfl rfl rfl⟩, trivial⟩⟩
  refine mir_cfgCertificate_sound tagOfLoan loopBorrowBody loopBorrowCert
    [⟨.byVal, .bool true⟩, ⟨.byVal, .nat 7⟩] lbSt0 (fun out => out.ret = .nat 42)
    (fun _ => []) id lbExtra [] rfl rfl lbBlockInv (fun out => out = ⟨.nat 42, []⟩)
    ?_ ?_ (Or.inl ⟨rfl, rfl⟩) ?_ ⟨subIdWrap_some, rfl, rfl, hRel0, Or.inl ⟨rfl, rfl, rfl⟩⟩
  · intro bb st hInv
    rcases hInv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))
    · exact rfl
  · intro bb st hInv _ _ _ _ h
    rcases hInv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact nomatch h
  · refine mirCfg_forwardSim_of_waitFree tagOfLoan loopBorrowBody loopBorrowCert.blocks
      (fun _ => []) id lbExtra [] ?_
    intro w bb st ms ⟨hW, _, _, _, hEx⟩
    rcases hEx with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact stepsTo_of_runMirToBlock_reached
        (rfl : Anneal.PureMirExec.runMirToBlock loopBorrowBody 1 lbMs0 = .reached lbMsBody)
        ⟨hW, rfl, rfl, hRelBody, Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)⟩
    · exact stepsTo_of_runMirToBlock_reached
        (rfl : Anneal.PureMirExec.runMirToBlock loopBorrowBody 0 lbMsBody = .reached lbMsAfterIter)
        ⟨hW, rfl, rfl, hRelAfter, Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))⟩
    · exact stepsTo_of_runMirToBlock_reached
        (rfl : Anneal.PureMirExec.runMirToBlock loopBorrowBody 2 lbMsAfterIter = .reached lbMsExit)
        ⟨hW, rfl, rfl, hRelExit, Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩))⟩
    · exact ⟨8, _, rfl, _, _, rfl, .nat (by decide), rfl⟩

/-! ### Test 2b-sym: Symbolic Diamond via `.convergedJump` (`armSteps = 1`) and `Option Ret` Acceptance vs. Rejection -/

/-- Symbolic output of `diamondBlocks` when entered at `bb0` with symbolic
`_0 = .symBool c`. -/
def diamondSymOut (c : Bool) : FuncOut StdVal :=
  ⟨.pair (zipStdVal (.symBool c) (.nat 50) (.nat 3))
    (zipStdVal (.symBool c) (.nat 4) (.nat 50)), []⟩

/-- **`.convergedJump` on `diamondBlocks` (`armSteps = 1 > 0`)**: on the
symbolic entry state `diamondSt0 c` (`_0 = .symBool c`), block `0` of
`diamondBlocks` evaluates both arm `1` (`&mut p.0`) and arm `2` (`&mut p.1`),
joins them at `bb3` into `diamondStJoin c` (`BackTarget.choice`), and emits
`.convergedJump 1 (handleFreeOutOpt stdValAlg) 3 (diamondStJoin c)`. -/
theorem diamondBlocks_convergedJump (c : Bool) :
    stepBasicBlock stdValAlg diamondBlocks 0 (diamondSt0 c) =
      .convergedJump 1 (handleFreeOutOpt stdValAlg) 3 (diamondStJoin c) := by
  cases c <;> rfl

/-- Exact `armSteps = 1` fuel accounting on `diamondBlocks` from symbolic
`diamondSt0 c`: fuel `2` (`1` step for `.convergedJump` + `1` delay tick) runs
out of fuel before `bb3` executes, while fuel `3` halts with `diamondSymOut c`. -/
theorem dbSym_cfg_wpConverges (c : Bool) :
    Anneal.PureMirExec.evalFuel
      (blockCfgStep (stepBasicBlock stdValAlg diamondBlocks)) 2
      ⟨some, 0, diamondSt0 c, 0⟩ = .outOfFuel ∧
    Anneal.PureMirExec.WpConverges
      (blockCfgStep (stepBasicBlock stdValAlg diamondBlocks))
      ⟨some, 0, diamondSt0 c, 0⟩ (· = diamondSymOut c) := by
  cases c <;> exact ⟨rfl, 3, _, rfl, rfl⟩

def dbSymExtra (c : Bool) (bb : Nat) (st : SymState StdVal)
    (ms : MachineState) : Prop :=
  (bb = 0 ∧ st = diamondSt0 c ∧ ms = diamondMs0 c) ∨
  (bb = 3 ∧ st = diamondStJoin c ∧ ms = diamondMsJoin c)

/-- **Wait-free forward simulation of the `.convergedJump` diamond**: at `bb0`,
the `.convergedJump 1 (handleFreeOutOpt stdValAlg) 3 (diamondStJoin c)` step is
matched by `diamond_runMirToBlock c` (`runMirToBlock diamondBody 3`) into
`diamondMsJoin c` with pending wrapper `composeWrap w (handleFreeOutOpt stdValAlg)`
and `wait = 1`; `mirCfg_forwardSim_of_waitFree` stutters through the `wait = 1 →
0` delay tick automatically and unwraps the sub-identity guard at `bb3`. -/
theorem dbSym_forwardSim (c : Bool) :
    ForwardSim (blockCfgStep (stepBasicBlock stdValAlg diamondBlocks))
      (Anneal.PureMirExec.mirStep diamondBody)
      (mirCfgStateRel tagOfLoan (dbBindingsAt c) id (dbSymExtra c))
      (MirOutcomeRel tagOfLoan []) := by
  refine mirCfg_forwardSim_of_waitFree tagOfLoan diamondBody diamondBlocks
    (dbBindingsAt c) id (dbSymExtra c) [] ?_
  intro w bb st ms ⟨hW, _, _, _, hExtra⟩
  rcases hExtra with ⟨hBb, hSt, hMs⟩ | ⟨hBb, hSt, hMs⟩
  · subst hBb; subst hSt; subst hMs
    cases c <;>
      exact stepsTo_of_runMirToBlock_reached (diamond_runMirToBlock _)
        ⟨subIdWrap_composeWrap hW (subIdWrap_handleFreeOutOpt stdValAlg),
         rfl, rfl, diamond_join_rel _, Or.inr ⟨rfl, rfl, rfl⟩⟩
  · subst hBb; subst hSt; subst hMs
    cases c
    · exact ⟨16, _, rfl, _, _, rfl, diamond_ret_refines false, rfl⟩
    · exact ⟨16, _, rfl, _, _, rfl, diamond_ret_refines true, rfl⟩

/-- **Test 2b-sym (live `V2026_06_01` adequacy of `.convergedJump` with
`armSteps = 1`)**: `mir_blockCfg_sound` transports `dbSym_cfg_wpConverges`
across `dbSym_forwardSim` (`SubIdWrap`-preserving `.convergedJump 1`) to prove
`MirWpConverges` of `diamondBody` for every oracle `c : Bool`. -/
theorem dbSym_sound (c : Bool) :
    Anneal.MirFuelFree.MirWpConverges diamondBody (diamondMs0 c)
      (fun o => LiftedMirPost tagOfLoan (· = diamondSymOut c) o []) :=
  mir_blockCfg_sound tagOfLoan diamondBody diamondBlocks (· = diamondSymOut c)
    (dbBindingsAt c) id (dbSymExtra c) []
    (dbSym_forwardSim c) (dbSym_cfg_wpConverges c).2
    ⟨subIdWrap_some, rfl, rfl, diamond_entry_rel c, Or.inl ⟨rfl, rfl, rfl⟩⟩

/-- `diamondBlocks` emits only sub-identity wrappers from the `dbSymExtra`
states: block `0` emits the `handleFreeOutOpt`-guarded `.convergedJump`, and
block `3` returns. -/
theorem dbSym_emitsSubIdWraps (c : Bool) :
    EmitsSubIdWraps (stepBasicBlock stdValAlg diamondBlocks)
      (fun bb st => Exists fun ms => dbSymExtra c bb st ms) := by
  intro bb st ⟨_, hEx⟩
  rcases hEx with ⟨hBb, hSt, _⟩ | ⟨hBb, hSt, _⟩
  · subst hBb
    subst hSt
    rw [diamondBlocks_convergedJump]
    exact subIdWrap_handleFreeOutOpt stdValAlg
  · subst hBb
    subst hSt
    cases c <;> exact trivial

/-- **Non-vacuity of `mirCfg_forwardSim_of_emitsSubIdWraps`**: the symbolic
`.convergedJump` diamond simulates `diamondBody` with per-block obligations that
mention neither the pending wrapper nor the delay (`mirCfgBlockRel`), and
`mir_blockCfg_sound` again yields live `MirWpConverges` for every oracle. -/
theorem dbSym_sound_of_emitsSubIdWraps (c : Bool) :
    Anneal.MirFuelFree.MirWpConverges diamondBody (diamondMs0 c)
      (fun o => LiftedMirPost tagOfLoan (· = diamondSymOut c) o []) :=
  mir_blockCfg_sound tagOfLoan diamondBody diamondBlocks (· = diamondSymOut c)
    (dbBindingsAt c) id (dbSymExtra c) []
    (mirCfg_forwardSim_of_emitsSubIdWraps tagOfLoan diamondBody diamondBlocks
      (dbBindingsAt c) id (dbSymExtra c) [] (dbSym_emitsSubIdWraps c)
      (fun bb st ms ⟨_, _, _, hExtra⟩ => by
        rcases hExtra with ⟨hBb, hSt, hMs⟩ | ⟨hBb, hSt, hMs⟩
        · subst hBb; subst hSt; subst hMs
          cases c <;>
            exact stepsTo_of_runMirToBlock_reached (diamond_runMirToBlock _)
              ⟨rfl, rfl, diamond_join_rel _, Or.inr ⟨rfl, rfl, rfl⟩⟩
        · subst hBb; subst hSt; subst hMs
          cases c
          · exact ⟨16, _, rfl, _, _, rfl, diamond_ret_refines false, rfl⟩
          · exact ⟨16, _, rfl, _, _, rfl, diamond_ret_refines true, rfl⟩))
    (dbSym_cfg_wpConverges c).2
    ⟨subIdWrap_some, rfl, rfl, diamond_entry_rel c, Or.inl ⟨rfl, rfl, rfl⟩⟩

def diamondPrePlan : FlowPlan StdVal :=
  .act (.assign (.localSub 3 []) (.binary stdMkPair (.localSub 1 []) (.localSub 2 [])))

def diamondArmTruePlan : FlowPlan StdVal :=
  .act (.borrow 4 .mutBorrow (.localSub 3 [0]))

def diamondArmFalsePlan : FlowPlan StdVal :=
  .act (.borrow 4 .mutBorrow (.localSub 3 [1]))

def diamondPostPlan : FlowPlan StdVal :=
  .seq (.act (.assign (.derefSub 4 []) (.constVal (.nat 50)))) (.act (.endLoan 0))

theorem diamondPostPlan_wf : WfPlan stdValAlg diamondPostPlan := fun _ _ => rfl

theorem diamondPostPlan_continuing :
    ∀ s f, evalPlan stdValAlg diamondPostPlan s = .ok f →
      Exists fun s' => f = .continuing s' :=
  evalPlan_seq_continuing stdValAlg (fun _ _ => rfl) (fun _ _ => rfl)
    (evalPlan_act_continuing stdValAlg _)
    (evalPlan_act_continuing stdValAlg _)

/-- 4-block diamond `CfgCertificate` for `diamondBlocks`, constructed via
`CfgCertificate.diamond` at fuel `3`. -/
def diamondCert : CfgCertificate stdValAlg :=
  CfgCertificate.diamond stdValAlg diamondPrePlan (.use (.localSub 0 []))
    diamondArmTruePlan diamondArmFalsePlan diamondPostPlan
    (.use (.localSub 3 []))
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) diamondPostPlan_wf
    (evalPlan_act_continuing stdValAlg _)
    (evalPlan_act_continuing stdValAlg _)
    (evalPlan_act_continuing stdValAlg _)
    diamondPostPlan_continuing

theorem diamondCert_blocks_eq : diamondCert.blocks = diamondBlocks := rfl

/-- Unqualified composition of `evalPlan_skip_continuing` and
`evalPlan_branch_continuing` (from `MirLiftCoreInterop`) with
`evalPlan_act_continuing` and `evalPlan_seq_continuing` (from
`V2026_06_01Bridge`), proving that both `diamondCert.plan` and a branch with a
`.skip` arm produce only `.continuing` flows (regression canary against
ambiguous duplicate declarations across namespaces). -/
theorem diamondFullPlan_and_skip_branch_continuing :
    (∀ s f, evalPlan stdValAlg diamondCert.plan s = .ok f →
      Exists fun s' => f = .continuing s') ∧
    (∀ s f,
      evalPlan stdValAlg
        (.branch (.use (.localSub 0 [])) diamondArmTruePlan .skip) s = .ok f →
      Exists fun s' => f = .continuing s') :=
  ⟨evalPlan_seq_continuing stdValAlg (fun _ _ => rfl)
     (wfPlan_seq stdValAlg
       (wfPlan_branch stdValAlg (.use (.localSub 0 []))
         (fun _ _ => rfl) (fun _ _ => rfl))
       diamondPostPlan_wf)
     (evalPlan_act_continuing stdValAlg _)
     (evalPlan_seq_continuing stdValAlg
       (wfPlan_branch stdValAlg (.use (.localSub 0 []))
         (fun _ _ => rfl) (fun _ _ => rfl))
       diamondPostPlan_wf
       (evalPlan_branch_continuing stdValAlg (.use (.localSub 0 []))
         (fun _ _ => rfl) (fun _ _ => rfl)
         (evalPlan_act_continuing stdValAlg _)
         (evalPlan_act_continuing stdValAlg _))
       diamondPostPlan_continuing),
   evalPlan_branch_continuing stdValAlg (.use (.localSub 0 []))
     (fun _ _ => rfl) (wfPlan_skip stdValAlg)
     (evalPlan_act_continuing stdValAlg _)
     (evalPlan_skip_continuing stdValAlg)⟩

/-- **Test 2b-cert (`CfgCertificate.diamond` / `mir_diamond_cfgCertificate_sound`
over a symbolic `.convergedJump 1` diamond)**: certifies `diamondBody` from
symbolic `diamondSt0 c` (`_0 = .symBool c`) through `CfgCertificate.diamond` and
`mir_cfgCertificate_sound_of_invClosedNoFork`, where block `0` genuinely emits
`.convergedJump 1 (handleFreeOutOpt stdValAlg) 3 (diamondStJoin c)`
(`diamondBlocks_convergedJump`). Only `HoldsFnSpec` of the structured plan and
the per-block live obligations are supplied: no block step is precomputed. -/
theorem diamond_cfgCertificate_sound (c : Bool) :
    Anneal.MirFuelFree.MirWpConverges diamondBody (diamondMs0 c)
      (fun o => LiftedMirPost tagOfLoan (· = diamondSymOut c) o []) :=
  mir_diamond_cfgCertificate_sound tagOfLoan diamondBody
    diamondPrePlan (.use (.localSub 0 []))
    diamondArmTruePlan diamondArmFalsePlan diamondPostPlan
    (.use (.localSub 3 []))
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) diamondPostPlan_wf
    (evalPlan_act_continuing stdValAlg _)
    (evalPlan_act_continuing stdValAlg _)
    (evalPlan_act_continuing stdValAlg _)
    diamondPostPlan_continuing
    (diamondParams c) (diamondSt0 c) (· = diamondSymOut c)
    (dbBindingsAt c) id (dbSymExtra c) []
    (diamond_init c) (by cases c <;> exact rfl)
    (fun bb st ms ⟨_, _, _, hExtra⟩ => by
      rcases hExtra with ⟨hBb, hSt, hMs⟩ | ⟨hBb, hSt, hMs⟩
      · subst hBb; subst hSt; subst hMs
        cases c <;>
          exact stepsTo_of_runMirToBlock_reached (diamond_runMirToBlock _)
            ⟨rfl, rfl, diamond_join_rel _, Or.inr ⟨rfl, rfl, rfl⟩⟩
      · subst hBb; subst hSt; subst hMs
        cases c
        · exact ⟨16, _, rfl, _, _, rfl, diamond_ret_refines false, rfl⟩
        · exact ⟨16, _, rfl, _, _, rfl, diamond_ret_refines true, rfl⟩)
    ⟨rfl, rfl, diamond_entry_rel c, Or.inl ⟨rfl, rfl, rfl⟩⟩

/-- **`LocalBlockVC` route of `mir_cfgCertificate_sound` through a
`.convergedJump`**: with both block steps of the symbolic diamond computed
(`diamondBlocks_convergedJump`, and `bb3` returning `diamondSymOut c`), the exact
2-point invariant `diamondSymBlockInv` satisfies `LocalBlockVC` with `PostRet :=
(· = diamondSymOut c)` (the pending `handleFreeOutOpt` guard must, and does,
accept the handle-free return unchanged) and never forks, so
`mir_cfgCertificate_sound` transports `diamondCert` to live `MirWpConverges`
along `dbSym_forwardSim`. -/
theorem diamond_cfgCertificate_sound_localBlockVC (c : Bool) :
    Anneal.MirFuelFree.MirWpConverges diamondBody (diamondMs0 c)
      (fun o => LiftedMirPost tagOfLoan (· = diamondSymOut c) o []) := by
  have hStep3 :
      stepBasicBlock stdValAlg diamondCert.blocks 3 (diamondStJoin c) =
        .ret (diamondSymOut c) := by
    cases c <;> rfl
  have hWrap :
      handleFreeOutOpt stdValAlg (diamondSymOut c) = some (diamondSymOut c) := by
    cases c <;> rfl
  exact mir_cfgCertificate_sound tagOfLoan diamondBody diamondCert
    (diamondParams c) (diamondSt0 c) (· = diamondSymOut c)
    (dbBindingsAt c) id (dbSymExtra c) [] (diamond_init c)
    (by cases c <;> exact rfl)
    (diamondSymBlockInv (diamondSt0 c) (diamondStJoin c)) (· = diamondSymOut c)
    (diamondSymBlockInv_localBlockVC stdValAlg diamondCert.blocks _ _ 1
      (handleFreeOutOpt stdValAlg) _ (diamondBlocks_convergedJump c) hStep3 hWrap)
    (diamondSymBlockInv_noFork stdValAlg diamondCert.blocks _ _ 1
      (handleFreeOutOpt stdValAlg) _ (diamondBlocks_convergedJump c) hStep3)
    (Or.inl ⟨rfl, rfl⟩) (dbSym_forwardSim c)
    ⟨subIdWrap_some, rfl, rfl, diamond_entry_rel c, Or.inl ⟨rfl, rfl, rfl⟩⟩

/-- Concrete-oracle parameters of `diamond` (`c : bool` passed as `.bool c`). -/
def dbParams (c : Bool) : List (ParamInput StdVal) :=
  [⟨.byVal, .bool c⟩, ⟨.byVal, .nat 3⟩, ⟨.byVal, .nat 4⟩]

/-- **Test 2b-cert (concrete condition)**: the same `CfgCertificate.diamond`
certifies the concrete diamond (`_0 = .bool c`, path `0 → 1/2 → 3`, no
`.convergedJump`) through the same `mir_diamond_cfgCertificate_sound`, with the
3-point live block relation of Test 2b (`dbExtra`). -/
theorem db_cfgCertificate_sound (c : Bool) :
    Anneal.MirFuelFree.MirWpConverges diamondBody (diamondMs0 c)
      (fun o => LiftedMirPost tagOfLoan (· = dbOut c) o []) :=
  mir_diamond_cfgCertificate_sound tagOfLoan diamondBody
    diamondPrePlan (.use (.localSub 0 []))
    diamondArmTruePlan diamondArmFalsePlan diamondPostPlan
    (.use (.localSub 3 []))
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) diamondPostPlan_wf
    (evalPlan_act_continuing stdValAlg _)
    (evalPlan_act_continuing stdValAlg _)
    (evalPlan_act_continuing stdValAlg _)
    diamondPostPlan_continuing
    (dbParams c) (dbSt0 c) (· = dbOut c)
    (dbBindingsAt c) id (dbExtra c) []
    rfl (by cases c <;> exact rfl)
    (fun bb st ms ⟨_, _, _, hExtra⟩ => by
      rcases hExtra with ⟨hBb, hSt, hMs⟩ | ⟨hBb, hSt, hMs⟩ | ⟨hBb, hSt, hMs⟩
      · subst hBb; subst hSt; subst hMs
        cases c
        · exact stepsTo_of_runMirToBlock_reached (rfl :
            Anneal.PureMirExec.runMirToBlock diamondBody 2 (diamondMs0 false) =
              .reached (dbMsArm false))
            ⟨rfl, rfl, db_rel_arm false, Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)⟩
        · exact stepsTo_of_runMirToBlock_reached (rfl :
            Anneal.PureMirExec.runMirToBlock diamondBody 1 (diamondMs0 true) =
              .reached (dbMsArm true))
            ⟨rfl, rfl, db_rel_arm true, Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)⟩
      · subst hSt; subst hMs
        cases c
        · subst hBb
          exact stepsTo_of_runMirToBlock_reached (rfl :
            Anneal.PureMirExec.runMirToBlock diamondBody 3 (dbMsArm false) =
              .reached (diamondMsJoin false))
            ⟨rfl, rfl, db_rel_join false, Or.inr (Or.inr ⟨rfl, rfl, rfl⟩)⟩
        · subst hBb
          exact stepsTo_of_runMirToBlock_reached (rfl :
            Anneal.PureMirExec.runMirToBlock diamondBody 3 (dbMsArm true) =
              .reached (diamondMsJoin true))
            ⟨rfl, rfl, db_rel_join true, Or.inr (Or.inr ⟨rfl, rfl, rfl⟩)⟩
      · subst hBb; subst hSt; subst hMs
        cases c
        · exact ⟨16, _, rfl, _, _, rfl, .pair (.nat (by decide)) (.nat (by decide)), rfl⟩
        · exact ⟨16, _, rfl, _, _, rfl, .pair (.nat (by decide)) (.nat (by decide)), rfl⟩)
    ⟨rfl, rfl, ⟨⟨trivial, trivial⟩,
      mirLocalsRel_of_localsRefine
        ⟨fun _ => ⟨_, rfl, .bool c⟩, fun _ => ⟨_, rfl, .nat (by decide)⟩,
         fun _ => ⟨_, rfl, .nat (by decide)⟩, trivial⟩⟩,
     Or.inl ⟨rfl, rfl, rfl⟩⟩

/-- **`CfgCertificate.diamond`'s fuel `3` is exact**: the concrete path
(`0 → 1/2 → 3`) and the symbolic run (`.convergedJump 1`: one step and one delay
tick, then `bb3`) both diverge at fuel `2` and return at the certificate's fuel
`3`, the latter from the certificate's own `sound` field applied to the plan's
evaluation (concrete `dbParams c` and symbolic `diamondParams c`). -/
theorem diamondCert_fuel_exact (c : Bool) :
    runBlockCfg (stepBasicBlock stdValAlg diamondCert.blocks) 0 (dbSt0 c) 2 =
      .diverged ∧
    runBlockCfg (stepBasicBlock stdValAlg diamondCert.blocks) 0 (dbSt0 c)
      diamondCert.fuel = .ret (dbOut c) ∧
    runBlockCfg (stepBasicBlock stdValAlg diamondCert.blocks) 0 (diamondSt0 c) 2 =
      .diverged ∧
    runBlockCfg (stepBasicBlock stdValAlg diamondCert.blocks) 0 (diamondSt0 c)
      diamondCert.fuel = .ret (diamondSymOut c) :=
  ⟨by cases c <;> rfl,
   diamondCert.sound (dbParams c) (dbSt0 c) (dbOut c) rfl (by cases c <;> rfl),
   by cases c <;> rfl,
   diamondCert.sound (diamondParams c) (diamondSt0 c) (diamondSymOut c)
     (diamond_init c) (by cases c <;> rfl)⟩

/-- Wrapper-level unit test for `handleFreeOutOpt stdValAlg` inside
`runBlockCfg`: block `0` emits `.convergedJump 1 (handleFreeOutOpt stdValAlg) 3
(diamondStJoin c)` and block `3` returns `⟨.refVal 0 [], []⟩`. -/
def diamondLeakStep (c : Bool) (bb : Nat) (_st : SymState StdVal) :
    BlockStepResult (SymState StdVal) (FuncOut StdVal) :=
  match bb with
  | 0 => .convergedJump 1 (handleFreeOutOpt stdValAlg) 3 (diamondStJoin c)
  | 3 => .ret ⟨.refVal 0 [], []⟩
  | _ => .fault

/-- Real `List (BasicBlock StdVal)` variant of `diamondBlocks` whose join block
`bb3` ends loan `0` (`stateCleanAtReturn = true`) and attempts to return the
stale borrow handle `_4 = .refVal 0 []` under `.convergedJump 1`. -/
def diamondLeakRetBlocks : List (BasicBlock StdVal) :=
  [⟨.act (.assign (.localSub 3 []) (.binary stdMkPair (.localSub 1 []) (.localSub 2 []))),
     .branch (.use (.localSub 0 [])) 1 2⟩,
   ⟨.act (.borrow 4 .mutBorrow (.localSub 3 [0])), .goto 3⟩,
   ⟨.act (.borrow 4 .mutBorrow (.localSub 3 [1])), .goto 3⟩,
   ⟨.seq (.act (.assign (.derefSub 4 []) (.constVal (.nat 50)))) (.act (.endLoan 0)),
     .ret (.use (.localSub 4 []))⟩]

/-- Real `List (BasicBlock StdVal)` variant of `diamondBlocks` where arm `1`
(`bb1`) contains a symbolic guarded early return `.earlyReturn [0] []
(.use (.localSub 4 []))` of the stale borrow handle `_4 = .refVal 0 []` on one
sub-path while continuing on the other, and `bb3` returns the clean handle-free
pair `.use (.localSub 3 [])`. Here `stepBasicBlock` at `bb3` succeeds with
`.ret (diamondSymOut c)`, and `.convergedJump 1`'s own `wrapJoined` rejects that
return (`none`) because merging the guarded early return introduces `.refVal 0 []`! -/
def diamondGuardedLeakBlocks : List (BasicBlock StdVal) :=
  [⟨.act (.assign (.localSub 3 []) (.binary stdMkPair (.localSub 1 []) (.localSub 2 []))),
     .branch (.use (.localSub 0 [])) 1 2⟩,
   ⟨.seq (.act (.borrow 4 .mutBorrow (.localSub 3 [0])))
      (.branch (.use (.localSub 0 []))
        (.earlyReturn [0] [] (.use (.localSub 4 [])))
        .skip),
    .goto 3⟩,
   ⟨.act (.borrow 4 .mutBorrow (.localSub 3 [1])), .goto 3⟩,
   ⟨.seq (.act (.assign (.derefSub 4 []) (.constVal (.nat 50)))) (.act (.endLoan 0)),
     .ret (.use (.localSub 3 []))⟩]

/-- Structured `FlowPlan` corresponding to `diamondGuardedLeakBlocks`: arm `1`
contains a guarded `.earlyReturn [0] [] (.use (.localSub 4 []))` of the stale
borrow handle `_4 = .refVal 0 []`. -/
def diamondGuardedLeakPlan : FlowPlan StdVal :=
  .seq diamondPrePlan
    (.seq
      (.branch (.use (.localSub 0 []))
        (.seq diamondArmTruePlan
          (.branch (.use (.localSub 0 []))
            (.earlyReturn [0] [] (.use (.localSub 4 [])))
            .skip))
        diamondArmFalsePlan)
      diamondPostPlan)

/-- **Live `stepBasicBlock` and `evalFnValue` handle-leak rejection under
`.convergedJump`**:
1. On `diamondLeakRetBlocks`, `bb0` emits `.convergedJump 1 (handleFreeOutOpt stdValAlg) 3 (diamondStJoin c)`,
   and `bb3` faults in `stepBasicBlock` when returning `_4 = .refVal 0 []`, so
   `runBlockCfg`, `blockCfgStep`, and the structured plan evaluation
   `evalFnValue stdValAlg (diamondParams c) diamondCert.plan (.use (.localSub 4 []))`
   all fault / fail (`¬ HoldsFnSpec`).
2. On `diamondGuardedLeakBlocks`, `bb0` emits `.convergedJump 1 wrapJoined 3 (diamondStJoin c)`
   (via `finishConvergedBranch`'s `.guardedContinuing` branch), `bb3` succeeds in
   `stepBasicBlock` with `.ret (diamondSymOut c)`, and `wrapJoined (diamondSymOut c) = none`
   rejects the merged output, so `runBlockCfg`, `blockCfgStep`, and the
   structured plan evaluation `evalFnValue stdValAlg (diamondParams c) diamondGuardedLeakPlan (.use (.localSub 3 []))`
   all fault / fail (`¬ HoldsFnSpec`) and converge to no postcondition `P`. -/
theorem diamondLeakBlocks_stepBasicBlock_fault_canaries
    (c : Bool) (P : FuncOut StdVal → Prop) :
    evalFnValue stdValAlg (diamondParams c) diamondCert.plan
      (.use (.localSub 4 [])) = .fail ∧
    ¬ HoldsFnSpec
      (evalFnValue stdValAlg (diamondParams c) diamondCert.plan
        (.use (.localSub 4 []))) P ∧
    stepBasicBlock stdValAlg diamondLeakRetBlocks 0 (diamondSt0 c) =
      .convergedJump 1 (handleFreeOutOpt stdValAlg) 3 (diamondStJoin c) ∧
    stepBasicBlock stdValAlg diamondLeakRetBlocks 3 (diamondStJoin c) = .fault ∧
    runBlockCfg (stepBasicBlock stdValAlg diamondLeakRetBlocks) 0
      (diamondSt0 c) 3 = .fault ∧
    Anneal.PureMirExec.evalFuel
      (blockCfgStep (stepBasicBlock stdValAlg diamondLeakRetBlocks)) 3
      ⟨some, 0, diamondSt0 c, 0⟩ = .faulted ∧
    ¬ Anneal.PureMirExec.WpConverges
      (blockCfgStep (stepBasicBlock stdValAlg diamondLeakRetBlocks))
      ⟨some, 0, diamondSt0 c, 0⟩ P ∧
    evalFnValue stdValAlg (diamondParams c) diamondGuardedLeakPlan
      (.use (.localSub 3 [])) = .fail ∧
    ¬ HoldsFnSpec
      (evalFnValue stdValAlg (diamondParams c) diamondGuardedLeakPlan
        (.use (.localSub 3 []))) P ∧
    stepBasicBlock stdValAlg diamondGuardedLeakBlocks 3 (diamondStJoin c) =
      .ret (diamondSymOut c) ∧
    (Exists fun wrapJoined =>
      stepBasicBlock stdValAlg diamondGuardedLeakBlocks 0 (diamondSt0 c) =
        .convergedJump 1 wrapJoined 3 (diamondStJoin c) ∧
      wrapJoined (diamondSymOut c) = none) ∧
    runBlockCfg (stepBasicBlock stdValAlg diamondGuardedLeakBlocks) 0
      (diamondSt0 c) 3 = .fault ∧
    Anneal.PureMirExec.evalFuel
      (blockCfgStep (stepBasicBlock stdValAlg diamondGuardedLeakBlocks)) 3
      ⟨some, 0, diamondSt0 c, 0⟩ = .faulted ∧
    ¬ Anneal.PureMirExec.WpConverges
      (blockCfgStep (stepBasicBlock stdValAlg diamondGuardedLeakBlocks))
      ⟨some, 0, diamondSt0 c, 0⟩ P := by
  have hPlanFailRet :
      evalFnValue stdValAlg (diamondParams c) diamondCert.plan
        (.use (.localSub 4 [])) = .fail := by
    cases c <;> rfl
  have hPlanFailGuarded :
      evalFnValue stdValAlg (diamondParams c) diamondGuardedLeakPlan
        (.use (.localSub 3 [])) = .fail := by
    cases c <;> rfl
  have hFaultRet :
      runBlockCfg (stepBasicBlock stdValAlg diamondLeakRetBlocks) 0
        (diamondSt0 c) 3 = .fault := by
    cases c <;> rfl
  have hFaultGuarded :
      runBlockCfg (stepBasicBlock stdValAlg diamondGuardedLeakBlocks) 0
        (diamondSt0 c) 3 = .fault := by
    cases c <;> rfl
  refine ⟨hPlanFailRet,
    by rw [hPlanFailRet]; exact holdsFnSpec_not_fail P,
    by cases c <;> rfl,
    by cases c <;> rfl,
    hFaultRet,
    by cases c <;> rfl,
    not_wpConverges_blockCfgStep_of_runBlockCfg_fault
      (stepBasicBlock stdValAlg diamondLeakRetBlocks) hFaultRet P,
    hPlanFailGuarded,
    by rw [hPlanFailGuarded]; exact holdsFnSpec_not_fail P,
    by cases c <;> rfl,
    by cases c <;> exact ⟨_, rfl, rfl⟩,
    hFaultGuarded,
    by cases c <;> rfl,
    not_wpConverges_blockCfgStep_of_runBlockCfg_fault
      (stepBasicBlock stdValAlg diamondGuardedLeakBlocks) hFaultGuarded P⟩

/-- **Non-vacuity of `Option Ret` wrapper rejection on `.convergedJump` and
`stdValAlg` `branchSplit` / `sameCond` / `sameAggregateShape` bridge laws**:
1. When a partial post-return wrapper rejects `diamondSymOut c` (`none`),
   `blockCfgStep (stepBasicBlock stdValAlg diamondBlocks)` faults at fuel `3`
   and converges to no postcondition `P`.
2. When the join block returns a leaked borrow handle `⟨.refVal 0 [], []⟩` under
   `.convergedJump`'s `handleFreeOutOpt stdValAlg` wrapper, `handleFreeOutOpt`
   returns `none`, `runBlockCfg` faults at fuel `3`, and `blockCfgStep`
   converges to no postcondition `P`.
3. `stdValAlg.branchSplit` splits the symbolic choice fields of `diamondSymOut c`,
   and `StdValRefines.of_branchSplit`, `StdValRefines.branchSplit_inv`,
   `stdValAlg_sameCond_symBool_iff`, and `stdValAlg_sameAggregateShape_pair`
   hold on the live diamond values. -/
theorem dbSym_convergedJump_rejection_and_valAlgebra_canaries
    (c : Bool) (P : FuncOut StdVal → Prop) :
    let rejectWrap : FuncOut StdVal → Option (FuncOut StdVal) :=
      fun out =>
        if stdValEq out.ret (.pair (.nat 0) (.nat 0)) then some out else none
    Anneal.PureMirExec.evalFuel
      (blockCfgStep (stepBasicBlock stdValAlg diamondBlocks)) 3
      ⟨rejectWrap, 0, diamondSt0 c, 0⟩ = .faulted ∧
    ¬ Anneal.PureMirExec.WpConverges
      (blockCfgStep (stepBasicBlock stdValAlg diamondBlocks))
      ⟨rejectWrap, 0, diamondSt0 c, 0⟩ P ∧
    handleFreeOutOpt stdValAlg ⟨.refVal 0 [], []⟩ = none ∧
    runBlockCfg (diamondLeakStep c) 0 (diamondSt0 c) 3 = .fault ∧
    ¬ Anneal.PureMirExec.WpConverges
      (blockCfgStep (diamondLeakStep c))
      ⟨some, 0, diamondSt0 c, 0⟩ P ∧
    stdValAlg.branchSplit (zipStdVal (.symBool c) (.nat 50) (.nat 3)) =
      some (.symBool c, .nat 50, .nat 3) ∧
    StdValRefines tagOfLoan (zipStdVal (.symBool c) (.nat 50) (.nat 3))
      (.scalar ⟨if c then 50 else 3, 4⟩) ∧
    (Exists fun b : Bool =>
      StdVal.symBool c = .symBool b ∧
      StdValRefines tagOfLoan
        (if b then .nat 50 else .nat 3)
        (.scalar ⟨if c then 50 else 3, 4⟩)) ∧
    (stdValAlg.sameCond (.symBool c) (.symBool (!c)) = false) ∧
    stdValAlg.sameAggregateShape (diamondSymOut c).ret (dbOut c).ret = true := by
  intro rejectWrap
  have hFault1 :
      Anneal.PureMirExec.evalFuel
        (blockCfgStep (stepBasicBlock stdValAlg diamondBlocks)) 3
        ⟨rejectWrap, 0, diamondSt0 c, 0⟩ = .faulted := by
    cases c <;> rfl
  have hFault2 :
      runBlockCfg (diamondLeakStep c) 0 (diamondSt0 c) 3 = .fault := by
    cases c <;> rfl
  have hRefField :
      StdValRefines tagOfLoan (zipStdVal (.symBool c) (.nat 50) (.nat 3))
        (.scalar ⟨if c then 50 else 3, 4⟩) :=
    StdValRefines.of_branchSplit (v := zipStdVal (.symBool c) (.nat 50) (.nat 3))
      (vt := .nat 50) (vf := .nat 3) (b := c) rfl
      (by cases c <;> exact .nat (by decide))
  refine ⟨hFault1,
    Anneal.PureMirExec.not_wpConverges_of_faulted hFault1,
    rfl, hFault2,
    not_wpConverges_blockCfgStep_of_runBlockCfg_fault (diamondLeakStep c) hFault2 P,
    rfl, hRefField,
    hRefField.branchSplit_inv rfl,
    by cases c <;> rfl,
    by cases c <;> exact stdValAlg_sameAggregateShape_pair _ _ _ _⟩

/-! ### Test 2b-asym: Asymmetric 5-Block Diamond via `.convergedJump` (`armSteps = Nat.max 2 1 = 2`) -/

/-- 5-block asymmetric diamond `CapturedMir`:
`fn asym_diamond(c: bool, mut x: u32, y: u32) -> (u32, u32)`:
- `bb0`: builds `_4 = (_2, _3)` and branches on `_1` to `bb1` (`true`) or `bb3` (`false`).
- `bb1 -> bb2 -> bb4` (`true` arm, `2` blocks): `bb1` borrows `_5 = &mut (_4.0)` and jumps to `bb2`;
  `bb2` updates `_2 = 20` and jumps to `bb4`.
- `bb3 -> bb4` (`false` arm, `1` block): `bb3` borrows `_5 = &mut (_4.1)` and jumps to `bb4`.
- `bb4` (join block): writes `(*_5) = copy _2`, ends the borrow, and returns `_4`. -/
def asymDiamondBody : CapturedMir :=
  mkBody 3
    [decl .mut pairTy, decl .not boolTy, decl .mut u32Ty, decl .not u32Ty,
     decl .mut pairTy, decl .not refU32Ty]
    [mkBb
       [mkSt (.storageLive 4),
        mkSt (.assign (pl 4) (.aggregate .tuple [.copy (pl 2), .copy (pl 3)])),
        mkSt (.storageLive 5)]
       (.switchInt (.copy (pl 1)) { branches := [(0, 3)], otherwise := 1 }),
     mkBb [mkSt (.assign (pl 5) (.ref (.mut false) (pl 4 [.field 0 u32Ty])))] (.goto 2),
     mkBb [mkSt (.assign (pl 2) (.use (u32C 20)))] (.goto 4),
     mkBb [mkSt (.assign (pl 5) (.ref (.mut false) (pl 4 [.field 1 u32Ty])))] (.goto 4),
     mkBb
       [mkSt (.assign (pl 5 [.deref]) (.use (.copy (pl 2)))),
        mkSt (.storageDead 5),
        mkSt (.assign (pl 0) (.use (.copy (pl 4)))),
        mkSt (.storageDead 4)]
       .return_]

/-- 5-block `PureLift` CFG matching `asymDiamondBody`: the `true` arm traverses
`2` blocks (`1 -> 2 -> 4`) while the `false` arm traverses `1` block (`3 -> 4`),
so `stepBasicBlock` charges `armSteps = Nat.max 2 1 = 2` delay ticks on
`.convergedJump`. -/
def asymDiamondBlocks : List (BasicBlock StdVal) :=
  [⟨.act (.assign (.localSub 3 []) (.binary stdMkPair (.localSub 1 []) (.localSub 2 []))),
     .branch (.use (.localSub 0 [])) 1 3⟩,
   ⟨.act (.borrow 4 .mutBorrow (.localSub 3 [0])), .goto 2⟩,
   ⟨.act (.assign (.localSub 1 []) (.constVal (.nat 20))), .goto 4⟩,
   ⟨.act (.borrow 4 .mutBorrow (.localSub 3 [1])), .goto 4⟩,
   ⟨.seq (.act (.assign (.derefSub 4 []) (.use (.localSub 1 [])))) (.act (.endLoan 0)),
     .ret (.use (.localSub 3 []))⟩]

/-- Joined symbolic state at `bb4` of `asymDiamondBlocks`: local `1` (`x`) holds
`.choice (.symBool c) (.nat 20) (.nat 3)` from the 2-block `true` arm (`bb2`) vs.
the 1-block `false` arm (`bb3`), and loan `0` has `BackTarget.choice`. -/
def asymDiamondStJoin (c : Bool) : SymState StdVal :=
  ⟨[⟨.choice (.symBool c) (.symBool c) (.symBool c), .unborrowed⟩,
    ⟨.choice (.symBool c) (.nat 20) (.nat 3), .unborrowed⟩,
    ⟨.choice (.symBool c) (.nat 4) (.nat 4), .unborrowed⟩,
    ⟨.pair (.choice (.symBool c) (.nat 3) (.nat 3)) (.choice (.symBool c) (.nat 4) (.nat 4)),
      .split [([0], .mutLocked 0), ([1], .mutLocked 0)]⟩,
    ⟨.refVal 0 [], .unborrowed⟩],
   [⟨0, .activeMut, ⟨.choice (.symBool c) (.nat 3) (.nat 4), .unborrowed⟩,
     BackTarget.choice (.symBool c) (.direct (.localReg 3) [0]) (.direct (.localReg 3) [1])⟩],
   [], [], [], 0⟩

def asymDiamondSymOut (c : Bool) : FuncOut StdVal :=
  ⟨.pair (zipStdVal (.symBool c) (.nat 20) (.nat 3))
    (zipStdVal (.symBool c) (.nat 4) (.nat 3)), []⟩

/-- **Asymmetric `.convergedJump` (`armSteps = Nat.max 2 1 = 2`)**: on symbolic
`diamondSt0 c`, block `0` of `asymDiamondBlocks` evaluates the 2-block `true`
arm (`bb1 -> bb2`) and the 1-block `false` arm (`bb3`), joins them at `bb4`, and
emits `.convergedJump 2 (handleFreeOutOpt stdValAlg) 4 (asymDiamondStJoin c)`. -/
theorem asymDiamondBlocks_convergedJump (c : Bool) :
    stepBasicBlock stdValAlg asymDiamondBlocks 0 (diamondSt0 c) =
      .convergedJump 2 (handleFreeOutOpt stdValAlg) 4 (asymDiamondStJoin c) := by
  cases c <;> rfl

/-- **Exact `armSteps = 2` fuel boundary on `asymDiamondBlocks`**: fuel `3`
(`1` step for `.convergedJump` + `2` delay ticks for the 2-block `true` arm)
is still `.outOfFuel` before `bb4` executes, whereas fuel `4` halts with
`asymDiamondSymOut c`. -/
theorem asymDiamond_cfg_wpConverges (c : Bool) :
    Anneal.PureMirExec.evalFuel
      (blockCfgStep (stepBasicBlock stdValAlg asymDiamondBlocks)) 3
      ⟨some, 0, diamondSt0 c, 0⟩ = .outOfFuel ∧
    Anneal.PureMirExec.evalFuel
      (blockCfgStep (stepBasicBlock stdValAlg asymDiamondBlocks)) 4
      ⟨some, 0, diamondSt0 c, 0⟩ = .halted (asymDiamondSymOut c) ∧
    Anneal.PureMirExec.WpConverges
      (blockCfgStep (stepBasicBlock stdValAlg asymDiamondBlocks))
      ⟨some, 0, diamondSt0 c, 0⟩ (· = asymDiamondSymOut c) := by
  cases c <;> exact ⟨rfl, rfl, 4, _, rfl, rfl⟩

def asymDiamondMs0 (c : Bool) : MachineState :=
  initMachineState asymDiamondBody [.scalar ⟨if c then 1 else 0, 1⟩, .scalar ⟨3, 4⟩, .scalar ⟨4, 4⟩]

def asymDiamondMsJoin (c : Bool) : MachineState :=
  { frame :=
      { blockIdx := 4, stmtIdx := 0,
        locals :=
          [.uninit, .init (.scalar ⟨if c then 1 else 0, 1⟩),
           .init (.scalar ⟨if c then 20 else 3, 4⟩), .init (.scalar ⟨4, 4⟩),
           .init (.aggregate 0 [.scalar ⟨3, 4⟩, .scalar ⟨4, 4⟩]),
           .init (.ptr ⟨1, 0⟩ 8)] }
    memory :=
      { (asymDiamondMs0 c).memory with
        borrows :=
          [{ tag := 1, targetLocal := 4,
             targetProjection := [.field (if c then 0 else 1) u32Ty],
             perm := .reservedFrz false }]
        nextTag := 2 } }

theorem asymDiamond_runMirToBlock (c : Bool) :
    Anneal.PureMirExec.runMirToBlock asymDiamondBody 4 (asymDiamondMs0 c) =
      .reached (asymDiamondMsJoin c) := by
  cases c <;> rfl

theorem asymDiamond_join_rel (c : Bool) :
    mirStateRel tagOfLoan [(0, 4, if c then [0] else [1])]
      (asymDiamondStJoin c) (asymDiamondMsJoin c) := by
  cases c
  · exact ⟨⟨⟨trivial, trivial⟩,
      ⟨⟨rfl, ⟨_, rfl, .choiceFalse (.nat (by decide))⟩, ⟨_, rfl, rfl, rfl, rfl⟩⟩, trivial⟩⟩,
     mirLocalsRel_of_localsRefine
      ⟨fun _ => ⟨_, rfl, .choiceFalse (.symBool false)⟩,
       fun _ => ⟨_, rfl, .choiceFalse (.nat (by decide))⟩,
       fun _ => ⟨_, rfl, .choiceFalse (.nat (by decide))⟩, (fun h => nomatch h),
       fun _ => ⟨_, rfl, .ref rfl rfl rfl⟩, trivial⟩⟩
  · exact ⟨⟨⟨trivial, trivial⟩,
      ⟨⟨rfl, ⟨_, rfl, .choiceTrue (.nat (by decide))⟩, ⟨_, rfl, rfl, rfl, rfl⟩⟩, trivial⟩⟩,
     mirLocalsRel_of_localsRefine
      ⟨fun _ => ⟨_, rfl, .choiceTrue (.symBool true)⟩,
       fun _ => ⟨_, rfl, .choiceTrue (.nat (by decide))⟩,
       fun _ => ⟨_, rfl, .choiceTrue (.nat (by decide))⟩, (fun h => nomatch h),
       fun _ => ⟨_, rfl, .ref rfl rfl rfl⟩, trivial⟩⟩

def asymDiamondMirRet (c : Bool) : Value :=
  if c then .aggregate 0 [.scalar ⟨20, 4⟩, .scalar ⟨4, 4⟩]
  else .aggregate 0 [.scalar ⟨3, 4⟩, .scalar ⟨3, 4⟩]

theorem asymDiamond_ret_refines (c : Bool) :
    StdValRefines tagOfLoan (asymDiamondSymOut c).ret (asymDiamondMirRet c) := by
  cases c
  · exact .pair (.choiceFalse (.nat (by decide)))
      (.choiceFalse (.nat (by decide)))
  · exact .pair (.choiceTrue (.nat (by decide)))
      (.choiceTrue (.nat (by decide)))

def asymDbBindingsAt (c : Bool) (bb : Nat) : List (LoanId × Local × SubPath) :=
  if bb = 4 then [(0, 4, if c then [0] else [1])] else []

def asymDbSymExtra (c : Bool) (bb : Nat) (st : SymState StdVal)
    (ms : MachineState) : Prop :=
  (bb = 0 ∧ st = diamondSt0 c ∧ ms = asymDiamondMs0 c) ∨
  (bb = 4 ∧ st = asymDiamondStJoin c ∧ ms = asymDiamondMsJoin c)

theorem asymDiamond_emitsSubIdWraps (c : Bool) :
    EmitsSubIdWraps (stepBasicBlock stdValAlg asymDiamondBlocks)
      (fun bb st => Exists fun ms => asymDbSymExtra c bb st ms) := by
  intro bb st ⟨_, hEx⟩
  rcases hEx with ⟨hBb, hSt, _⟩ | ⟨hBb, hSt, _⟩
  · subst hBb; subst hSt
    rw [asymDiamondBlocks_convergedJump]
    exact subIdWrap_handleFreeOutOpt stdValAlg
  · subst hBb; subst hSt
    cases c <;> exact trivial

/-- **Test 2b-asym (live `V2026_06_01` adequacy of an asymmetric `.convergedJump 2`
diamond)**: `mirCfg_forwardSim_of_emitsSubIdWraps` stutters through both
`wait = 2 → 1 → 0` delay ticks of the 2-block `true` arm (`bb1 -> bb2`) vs.
1-block `false` arm (`bb3`), and `mir_blockCfg_sound` yields live
`MirWpConverges asymDiamondBody (asymDiamondMs0 c)` for both oracles. -/
theorem asymDiamond_sound (c : Bool) :
    Anneal.MirFuelFree.MirWpConverges asymDiamondBody (asymDiamondMs0 c)
      (fun o => LiftedMirPost tagOfLoan (· = asymDiamondSymOut c) o []) :=
  mir_blockCfg_sound tagOfLoan asymDiamondBody asymDiamondBlocks
    (· = asymDiamondSymOut c)
    (asymDbBindingsAt c) id (asymDbSymExtra c) []
    (mirCfg_forwardSim_of_emitsSubIdWraps tagOfLoan asymDiamondBody
      asymDiamondBlocks (asymDbBindingsAt c) id (asymDbSymExtra c) []
      (asymDiamond_emitsSubIdWraps c)
      (fun bb st ms ⟨_, _, _, hExtra⟩ => by
        rcases hExtra with ⟨hBb, hSt, hMs⟩ | ⟨hBb, hSt, hMs⟩
        · subst hBb; subst hSt; subst hMs
          cases c <;>
            exact stepsTo_of_runMirToBlock_reached (asymDiamond_runMirToBlock _)
              ⟨rfl, rfl, asymDiamond_join_rel _, Or.inr ⟨rfl, rfl, rfl⟩⟩
        · subst hBb; subst hSt; subst hMs
          cases c
          · exact ⟨16, _, rfl, _, _, rfl, asymDiamond_ret_refines false, rfl⟩
          · exact ⟨16, _, rfl, _, _, rfl, asymDiamond_ret_refines true, rfl⟩))
    (asymDiamond_cfg_wpConverges c).2.2
    ⟨subIdWrap_some, rfl, rfl,
     ⟨⟨trivial, trivial⟩,
      mirLocalsRel_of_localsRefine
        ⟨fun _ => ⟨_, rfl, .symBool c⟩, fun _ => ⟨_, rfl, .nat (by decide)⟩,
         fun _ => ⟨_, rfl, .nat (by decide)⟩, trivial⟩⟩,
     Or.inl ⟨rfl, rfl, rfl⟩⟩

/-- `runBlockCfgToBlock` reaches the asymmetric join `bb4` only after the
`.convergedJump 2` step and both delay ticks (`wait = 2 → 1 → 0`), with the
`handleFreeOutOpt` guard pending. -/
theorem asymDiamond_runBlockCfgToBlock (c : Bool) :
    runBlockCfgToBlock (stepBasicBlock stdValAlg asymDiamondBlocks) 4 8
      ⟨some, 0, diamondSt0 c, 0⟩ =
      .reached ⟨composeWrap some (handleFreeOutOpt stdValAlg), 4,
        asymDiamondStJoin c, 0⟩ := by
  cases c <;> rfl

/-- **Segment form of Test 2b-asym (`mirCfg_segmentSim_of_emitsSubIdWraps`)**:
the wrapper-agnostic segment simulation carries the PureLift segment
`bb0 → bb4` (one `.convergedJump 2` and two stuttering delay ticks) to a live
MIR segment that lands exactly on the MIR join state `asymDiamondMsJoin c`. -/
theorem asymDiamond_segmentSim_to_join (c : Bool) :
    Anneal.PureMirExec.StepsTo (Anneal.PureMirExec.mirStep asymDiamondBody)
      (asymDiamondMs0 c) (· = asymDiamondMsJoin c) := by
  have hSeg := stepsTo_of_segmentSim
    (mirCfg_segmentSim_of_emitsSubIdWraps tagOfLoan asymDiamondBody
      asymDiamondBlocks (asymDbBindingsAt c) id (asymDbSymExtra c)
      (asymDiamond_emitsSubIdWraps c)
      (fun bb st ms ⟨_, _, _, hExtra⟩ => by
        rcases hExtra with ⟨hBb, hSt, hMs⟩ | ⟨hBb, hSt, hMs⟩
        · subst hBb; subst hSt; subst hMs
          cases c <;>
            exact stepsTo_of_runMirToBlock_reached (asymDiamond_runMirToBlock _)
              ⟨rfl, rfl, asymDiamond_join_rel _, Or.inr ⟨rfl, rfl, rfl⟩⟩
        · subst hBb; subst hSt; subst hMs
          cases c <;> exact trivial))
    (stepsTo_of_runBlockCfgToBlock_reached (asymDiamond_runBlockCfgToBlock c))
    (asymDiamondMs0 c)
    ⟨subIdWrap_some, rfl, rfl,
     ⟨⟨trivial, trivial⟩,
      mirLocalsRel_of_localsRefine
        ⟨fun _ => ⟨_, rfl, .symBool c⟩, fun _ => ⟨_, rfl, .nat (by decide)⟩,
         fun _ => ⟨_, rfl, .nat (by decide)⟩, trivial⟩⟩,
     Or.inl ⟨rfl, rfl, rfl⟩⟩
  refine hSeg.mono ?_
  intro ms ⟨s, hs, _, _, _, _, hExtra⟩
  subst hs
  rcases hExtra with ⟨h, _, _⟩ | ⟨_, _, hMs⟩
  · exact (Nat.succ_ne_zero 3 h).elim
  · exact hMs

def asymDiamondArmTrue2Plan : FlowPlan StdVal :=
  .act (.assign (.localSub 1 []) (.constVal (.nat 20)))

def asymDiamondPostPlan : FlowPlan StdVal :=
  .seq (.act (.assign (.derefSub 4 []) (.use (.localSub 1 [])))) (.act (.endLoan 0))

theorem asymDiamondPostPlan_wf : WfPlan stdValAlg asymDiamondPostPlan :=
  fun _ _ => rfl

theorem asymDiamondPostPlan_continuing :
    ∀ s f, evalPlan stdValAlg asymDiamondPostPlan s = .ok f →
      Exists fun s' => f = .continuing s' :=
  evalPlan_seq_continuing stdValAlg (fun _ _ => rfl) (fun _ _ => rfl)
    (evalPlan_act_continuing stdValAlg _)
    (evalPlan_act_continuing stdValAlg _)

/-- 5-block asymmetric diamond `CfgCertificate` for `asymDiamondBlocks`,
constructed via `CfgCertificate.asymDiamond` at fuel `4`. -/
def asymDiamondCert : CfgCertificate stdValAlg :=
  CfgCertificate.asymDiamond stdValAlg diamondPrePlan (.use (.localSub 0 []))
    diamondArmTruePlan asymDiamondArmTrue2Plan diamondArmFalsePlan
    asymDiamondPostPlan (.use (.localSub 3 []))
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    asymDiamondPostPlan_wf
    (evalPlan_act_continuing stdValAlg _)
    (evalPlan_act_continuing stdValAlg _)
    (evalPlan_act_continuing stdValAlg _)
    (evalPlan_act_continuing stdValAlg _)
    asymDiamondPostPlan_continuing

theorem asymDiamondCert_blocks_eq :
    asymDiamondCert.blocks = asymDiamondBlocks := rfl

/-- **Test 2b-asym-cert (`CfgCertificate.asymDiamond` /
`mir_asymDiamond_cfgCertificate_sound` over a symbolic `.convergedJump 2`
asymmetric diamond)**: certifies `asymDiamondBody` from symbolic `diamondSt0 c`
(`_0 = .symBool c`) through `CfgCertificate.asymDiamond` and
`mir_asymDiamond_cfgCertificate_sound` from `HoldsFnSpec` of its structured plan
alone, where block `0` emits `.convergedJump 2 (handleFreeOutOpt stdValAlg) 4
(asymDiamondStJoin c)`. -/
theorem asymDiamond_cfgCertificate_sound (c : Bool) :
    Anneal.MirFuelFree.MirWpConverges asymDiamondBody (asymDiamondMs0 c)
      (fun o => LiftedMirPost tagOfLoan (· = asymDiamondSymOut c) o []) :=
  mir_asymDiamond_cfgCertificate_sound tagOfLoan asymDiamondBody
    diamondPrePlan (.use (.localSub 0 []))
    diamondArmTruePlan asymDiamondArmTrue2Plan diamondArmFalsePlan
    asymDiamondPostPlan (.use (.localSub 3 []))
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    asymDiamondPostPlan_wf
    (evalPlan_act_continuing stdValAlg _)
    (evalPlan_act_continuing stdValAlg _)
    (evalPlan_act_continuing stdValAlg _)
    (evalPlan_act_continuing stdValAlg _)
    asymDiamondPostPlan_continuing
    (diamondParams c) (diamondSt0 c) (· = asymDiamondSymOut c)
    (asymDbBindingsAt c) id (asymDbSymExtra c) []
    (diamond_init c) (by cases c <;> exact rfl)
    (fun bb st ms ⟨_, _, _, hExtra⟩ => by
      rcases hExtra with ⟨hBb, hSt, hMs⟩ | ⟨hBb, hSt, hMs⟩
      · subst hBb; subst hSt; subst hMs
        cases c <;>
          exact stepsTo_of_runMirToBlock_reached (asymDiamond_runMirToBlock _)
            ⟨rfl, rfl, asymDiamond_join_rel _, Or.inr ⟨rfl, rfl, rfl⟩⟩
      · subst hBb; subst hSt; subst hMs
        cases c
        · exact ⟨16, _, rfl, _, _, rfl, asymDiamond_ret_refines false, rfl⟩
        · exact ⟨16, _, rfl, _, _, rfl, asymDiamond_ret_refines true, rfl⟩)
    ⟨rfl, rfl,
     ⟨⟨trivial, trivial⟩,
      mirLocalsRel_of_localsRefine
        ⟨fun _ => ⟨_, rfl, .symBool c⟩, fun _ => ⟨_, rfl, .nat (by decide)⟩,
         fun _ => ⟨_, rfl, .nat (by decide)⟩, trivial⟩⟩,
     Or.inl ⟨rfl, rfl, rfl⟩⟩

/-! #### Test 2b-asym-cert (concrete condition): the 4-step arm at the certificate's exact fuel -/

/-- Concrete result of `asym_diamond` for oracle `c`: `(20, 4)` when `c` (the
`true` arm sets `x = 20`, then writes it through `&mut p.0`), else `(3, 3)`. -/
def asymConcOut (c : Bool) : FuncOut StdVal :=
  ⟨if c then .pair (.nat 20) (.nat 4) else .pair (.nat 3) (.nat 3), []⟩

/-- **`CfgCertificate.asymDiamond`'s fuel `4` is exact on both of its longest
paths**: the concrete `true` path (`0 → 1 → 2 → 4`, four block steps) and the
symbolic run (`.convergedJump 2`: one step and two delay ticks, then `bb4`) both
diverge at fuel `3` and return at the certificate's fuel `4`, while the concrete
`false` path (`0 → 3 → 4`) already returns at fuel `3`. The fuel-`4` returns
come from the certificate's own `sound` field applied to the plan's evaluation
(concrete `dbParams c` and symbolic `diamondParams c`). -/
theorem asymDiamondCert_fuel_exact (c : Bool) :
    runBlockCfg (stepBasicBlock stdValAlg asymDiamondCert.blocks) 0 (dbSt0 true) 3 =
      .diverged ∧
    runBlockCfg (stepBasicBlock stdValAlg asymDiamondCert.blocks) 0 (dbSt0 c)
      asymDiamondCert.fuel = .ret (asymConcOut c) ∧
    runBlockCfg (stepBasicBlock stdValAlg asymDiamondCert.blocks) 0 (dbSt0 false) 3 =
      .ret (asymConcOut false) ∧
    runBlockCfg (stepBasicBlock stdValAlg asymDiamondCert.blocks) 0 (diamondSt0 c) 3 =
      .diverged ∧
    runBlockCfg (stepBasicBlock stdValAlg asymDiamondCert.blocks) 0 (diamondSt0 c)
      asymDiamondCert.fuel = .ret (asymDiamondSymOut c) :=
  ⟨rfl,
   asymDiamondCert.sound (dbParams c) (dbSt0 c) (asymConcOut c) rfl
     (by cases c <;> rfl),
   rfl,
   by cases c <;> rfl,
   asymDiamondCert.sound (diamondParams c) (diamondSt0 c) (asymDiamondSymOut c)
     (diamond_init c) (by cases c <;> rfl)⟩

/-- Live state at the header of the taken arm of `asymDiamondBody` (`bb1` if
`c`, else `bb3`), after `bb0` built `_4 = (_2, _3)`. -/
def asymConcMsArm (c : Bool) : MachineState :=
  { frame :=
      { blockIdx := if c then 1 else 3, stmtIdx := 0,
        locals :=
          [.uninit, .init (.scalar ⟨if c then 1 else 0, 1⟩), .init (.scalar ⟨3, 4⟩),
           .init (.scalar ⟨4, 4⟩), .init (.aggregate 0 [.scalar ⟨3, 4⟩, .scalar ⟨4, 4⟩]),
           .uninit] }
    memory := (asymDiamondMs0 c).memory }

/-- Live state at the header of `bb2` on the `true` arm: `_5 = &mut _4.0`
through the `reserved` tag `1`, `x` still `3`. -/
def asymConcMsMid : MachineState :=
  { frame :=
      { blockIdx := 2, stmtIdx := 0,
        locals :=
          [.uninit, .init (.scalar ⟨1, 1⟩), .init (.scalar ⟨3, 4⟩), .init (.scalar ⟨4, 4⟩),
           .init (.aggregate 0 [.scalar ⟨3, 4⟩, .scalar ⟨4, 4⟩]), .init (.ptr ⟨1, 0⟩ 8)] }
    memory :=
      { (asymDiamondMs0 true).memory with
        borrows :=
          [{ tag := 1, targetLocal := 4, targetProjection := [.field 0 u32Ty],
             perm := .reservedFrz false }]
        nextTag := 2 } }

/-- `PureLift` state at the join `bb4` on the concrete `true` path: the loan of
`p.0` from `bb1` is still active and `x = 20` (set in `bb2`). -/
def asymConcStJoinT : SymState StdVal :=
  ⟨[⟨.bool true, .unborrowed⟩, ⟨.nat 20, .unborrowed⟩, ⟨.nat 4, .unborrowed⟩,
    ⟨.pair (.nat 3) (.nat 4), .split [([0], .mutLocked 0)]⟩,
    ⟨.refVal 0 [], .unborrowed⟩],
   [⟨0, .activeMut, ⟨.nat 3, .unborrowed⟩, .direct (.localReg 3) [0]⟩],
   [], [], [], 0⟩

/-- `PureLift` state at the join `bb4` for the concrete oracle `c`. -/
def asymConcStJoin (c : Bool) : SymState StdVal :=
  if c then asymConcStJoinT else dbSt3 false

theorem asymConc_rel_arm (c : Bool) :
    mirStateRel tagOfLoan [] (dbSt1 c) (asymConcMsArm c) := by
  cases c <;>
  exact ⟨⟨trivial, trivial⟩,
    mirLocalsRel_of_localsRefine
      ⟨fun _ => ⟨_, rfl, .bool _⟩, fun _ => ⟨_, rfl, .nat (by decide)⟩,
       fun _ => ⟨_, rfl, .nat (by decide)⟩,
       fun _ => ⟨_, rfl, .pair (.nat (by decide)) (.nat (by decide))⟩, trivial⟩⟩

theorem asymConc_rel_mid :
    mirStateRel tagOfLoan [(0, 4, [0])] (dbSt3 true) asymConcMsMid :=
  ⟨⟨⟨trivial, trivial⟩,
      ⟨⟨rfl, ⟨_, rfl, .nat (by decide)⟩, ⟨_, rfl, rfl, rfl, rfl⟩⟩, trivial⟩⟩,
    mirLocalsRel_of_localsRefine
      ⟨fun _ => ⟨_, rfl, .bool _⟩, fun _ => ⟨_, rfl, .nat (by decide)⟩,
       fun _ => ⟨_, rfl, .nat (by decide)⟩, (fun h => nomatch h),
       fun _ => ⟨_, rfl, .ref rfl rfl rfl⟩, trivial⟩⟩

theorem asymConc_rel_join (c : Bool) :
    mirStateRel tagOfLoan [(0, 4, if c then [0] else [1])] (asymConcStJoin c)
      (asymDiamondMsJoin c) := by
  cases c <;>
  exact ⟨⟨⟨trivial, trivial⟩,
      ⟨⟨rfl, ⟨_, rfl, .nat (by decide)⟩, ⟨_, rfl, rfl, rfl, rfl⟩⟩, trivial⟩⟩,
    mirLocalsRel_of_localsRefine
      ⟨fun _ => ⟨_, rfl, .bool _⟩, fun _ => ⟨_, rfl, .nat (by decide)⟩,
       fun _ => ⟨_, rfl, .nat (by decide)⟩, (fun h => nomatch h),
       fun _ => ⟨_, rfl, .ref rfl rfl rfl⟩, trivial⟩⟩

def asymConcBindingsAt (c : Bool) (bb : Nat) : List (LoanId × Local × SubPath) :=
  if bb = 2 ∨ bb = 4 then [(0, 4, if c then [0] else [1])] else []

/-- Block-entry relation of the concrete asymmetric diamond: one live header
state per visited block (`bb0`, the taken arm's first block, `bb2` on the
2-block `true` arm only, and the join `bb4`). -/
def asymConcExtra (c : Bool) (bb : Nat) (st : SymState StdVal) (ms : MachineState) :
    Prop :=
  (bb = 0 ∧ st = dbSt0 c ∧ ms = asymDiamondMs0 c) ∨
  (bb = (if c then 1 else 3) ∧ st = dbSt1 c ∧ ms = asymConcMsArm c) ∨
  (c = true ∧ bb = 2 ∧ st = dbSt3 true ∧ ms = asymConcMsMid) ∨
  (bb = 4 ∧ st = asymConcStJoin c ∧ ms = asymDiamondMsJoin c)

/-- **Test 2b-asym-cert (concrete condition)**: `CfgCertificate.asymDiamond`
certifies the concrete asymmetric diamond (`_0 = .bool c`) through
`mir_asymDiamond_cfgCertificate_sound`, simulating the 2-block `true` arm block
for block (`bb0 → bb1 → bb2 → bb4`, four steps at the certificate's exact fuel)
and the 1-block `false` arm (`bb0 → bb3 → bb4`) on the live machine, so the
concrete paths of `cfg_certificate_asymDiamond_sound` and
`asymDiamondCfgInv_invClosedNoFork` are exercised end to end. -/
theorem asymDiamond_cfgCertificate_sound_concrete (c : Bool) :
    Anneal.MirFuelFree.MirWpConverges asymDiamondBody (asymDiamondMs0 c)
      (fun o => LiftedMirPost tagOfLoan (· = asymConcOut c) o []) :=
  mir_asymDiamond_cfgCertificate_sound tagOfLoan asymDiamondBody
    diamondPrePlan (.use (.localSub 0 []))
    diamondArmTruePlan asymDiamondArmTrue2Plan diamondArmFalsePlan
    asymDiamondPostPlan (.use (.localSub 3 []))
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    asymDiamondPostPlan_wf
    (evalPlan_act_continuing stdValAlg _)
    (evalPlan_act_continuing stdValAlg _)
    (evalPlan_act_continuing stdValAlg _)
    (evalPlan_act_continuing stdValAlg _)
    asymDiamondPostPlan_continuing
    (dbParams c) (dbSt0 c) (· = asymConcOut c)
    (asymConcBindingsAt c) id (asymConcExtra c) []
    rfl (by cases c <;> exact rfl)
    (fun bb st ms ⟨_, _, _, hExtra⟩ => by
      rcases hExtra with ⟨hBb, hSt, hMs⟩ | ⟨hBb, hSt, hMs⟩ | ⟨hC, hBb, hSt, hMs⟩ |
          ⟨hBb, hSt, hMs⟩
      · subst hBb; subst hSt; subst hMs
        cases c
        · exact stepsTo_of_runMirToBlock_reached (rfl :
            Anneal.PureMirExec.runMirToBlock asymDiamondBody 3 (asymDiamondMs0 false) =
              .reached (asymConcMsArm false))
            ⟨rfl, rfl, asymConc_rel_arm false, Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)⟩
        · exact stepsTo_of_runMirToBlock_reached (rfl :
            Anneal.PureMirExec.runMirToBlock asymDiamondBody 1 (asymDiamondMs0 true) =
              .reached (asymConcMsArm true))
            ⟨rfl, rfl, asymConc_rel_arm true, Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)⟩
      · subst hSt; subst hMs
        cases c
        · subst hBb
          exact stepsTo_of_runMirToBlock_reached (rfl :
            Anneal.PureMirExec.runMirToBlock asymDiamondBody 4 (asymConcMsArm false) =
              .reached (asymDiamondMsJoin false))
            ⟨rfl, rfl, asymConc_rel_join false, Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩))⟩
        · subst hBb
          exact stepsTo_of_runMirToBlock_reached (rfl :
            Anneal.PureMirExec.runMirToBlock asymDiamondBody 2 (asymConcMsArm true) =
              .reached asymConcMsMid)
            ⟨rfl, rfl, asymConc_rel_mid, Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl⟩))⟩
      · subst hC; subst hBb; subst hSt; subst hMs
        exact stepsTo_of_runMirToBlock_reached (rfl :
          Anneal.PureMirExec.runMirToBlock asymDiamondBody 4 asymConcMsMid =
            .reached (asymDiamondMsJoin true))
          ⟨rfl, rfl, asymConc_rel_join true, Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩))⟩
      · subst hBb; subst hSt; subst hMs
        cases c
        · exact ⟨16, _, rfl, _, _, rfl, .pair (.nat (by decide)) (.nat (by decide)), rfl⟩
        · exact ⟨16, _, rfl, _, _, rfl, .pair (.nat (by decide)) (.nat (by decide)), rfl⟩)
    ⟨rfl, rfl,
     ⟨⟨trivial, trivial⟩,
      mirLocalsRel_of_localsRefine
        ⟨fun _ => ⟨_, rfl, .bool c⟩, fun _ => ⟨_, rfl, .nat (by decide)⟩,
         fun _ => ⟨_, rfl, .nat (by decide)⟩, trivial⟩⟩,
     Or.inl ⟨rfl, rfl, rfl⟩⟩

/-! ### Test 2d: Multi-Step Strong-Descent (`rank s' < rank s`, `Δrank ≥ 2`) Loop Cutpoints over Live `V2026_06_01` MIR -/

/-- Strong-descent ranking function on `loopBorrowBody` (`Test 2c`): an
indicator of the loop flag (`3` while `_1 = true`, else `0`), so its single
iteration drops it by `3`. The loop runs once, so this only checks that the
cutpoint rule accepts a non-unit drop; the variable-stride, multi-iteration
canary with a natural rank is `strideLoop_strongDescent_cutpoint_sound`. -/
def lbStrongRank (s : SymState StdVal) : Nat :=
  match s.locals with
  | ⟨⟨_, .bool true⟩, _⟩ :: _ => 3
  | _ => 0

def lbCutInv (s : SymState StdVal) : Prop :=
  s = lbSt0 ∨ s = lbStAfterIter

theorem lbStrongRank_drops_by_3 :
    lbStrongRank lbSt0 = 3 ∧
    lbStrongRank lbStAfterIter = 0 ∧
    lbStrongRank lbStAfterIter < lbStrongRank lbSt0 ∧
    ¬ (lbStrongRank lbSt0 = lbStrongRank lbStAfterIter + 1) := by
  decide

theorem lbCutpoint_step : ∀ s, lbCutInv s →
    Exists fun cv => evalRval stdValAlg (.use (.localSub 0 [])) s = some cv ∧
      (stdValAlg.asBool cv = some false ∨
       (stdValAlg.asBool cv = some true ∧
        Exists fun s' =>
          evalPlan stdValAlg lbBodyPlan s = .ok (.continuing s') ∧
          lbCutInv s' ∧ lbStrongRank s' < lbStrongRank s)) := by
  intro s hs
  rcases hs with rfl | rfl
  · exact ⟨.bool true, rfl, Or.inr ⟨rfl, lbStAfterIter, rfl, Or.inr rfl, by decide⟩⟩
  · exact ⟨.bool false, rfl, Or.inl rfl⟩

theorem lbCutpoint_exit : ∀ s, lbCutInv s →
    (Exists fun cv => evalRval stdValAlg (.use (.localSub 0 [])) s = some cv ∧
      stdValAlg.asBool cv = some false) →
    stateCleanAtReturn s = true ∧
      Exists fun rv => evalRval stdValAlg (.use (.localSub 1 [])) s = some rv ∧
        handleFreeOut stdValAlg ⟨rv, collectRootMutVals s.loans⟩ = true ∧
        (⟨rv, collectRootMutVals s.loans⟩ : FuncOut StdVal).ret = .nat 42 := by
  intro s hs ⟨cv, hcv, hb⟩
  rcases hs with rfl | rfl
  · injection hcv with hcv
    subst hcv
    exact nomatch hb
  · exact ⟨rfl, .nat 42, rfl, rfl, rfl⟩

/-- **Test 2d-1 (`loopBorrowBody` certified via strong-descent cutpoint
`mir_whileLoop_cfgCertificate_of_cutpoint`)**: `lbStrongRank` drops `3 → 0`
(`Δrank = 3 ≥ 2`), and `mir_whileLoop_cfgCertificate_of_cutpoint` automatically
derives `HoldsFnSpec`, `LocalBlockVC`, and `hNoFork` from `(lbCutInv,
lbStrongRank, lbCutpoint_step, lbCutpoint_exit)`. -/
theorem loopBorrow_strongDescent_cutpoint_sound :
    Anneal.MirFuelFree.MirWpConverges loopBorrowBody lbMs0
      (LiftedMirPost tagOfLoan (fun out => out.ret = .nat 42)) := by
  have hRel0 : mirStateRel tagOfLoan [] lbSt0 lbMs0 :=
    ⟨⟨trivial, trivial⟩,
     mirLocalsRel_of_localsRefine
       ⟨fun _ => ⟨_, rfl, .bool true⟩, fun _ => ⟨_, rfl, .nat (by decide)⟩, trivial⟩⟩
  have hRelBody : mirStateRel tagOfLoan [] lbSt0 lbMsBody :=
    ⟨⟨trivial, trivial⟩,
     mirLocalsRel_of_localsRefine
       ⟨fun _ => ⟨_, rfl, .bool true⟩, fun _ => ⟨_, rfl, .nat (by decide)⟩, trivial⟩⟩
  have hRelAfter : mirStateRel tagOfLoan [] lbStAfterIter lbMsAfterIter :=
    ⟨⟨trivial, trivial⟩,
     mirLocalsRel_of_localsRefine
       ⟨fun _ => ⟨_, rfl, .bool false⟩, fun _ => ⟨_, rfl, .nat (by decide)⟩,
        fun _ => ⟨_, rfl, .ref rfl rfl rfl⟩, trivial⟩⟩
  have hRelExit : mirStateRel tagOfLoan [] lbStAfterIter lbMsExit :=
    ⟨⟨trivial, trivial⟩,
     mirLocalsRel_of_localsRefine
       ⟨fun _ => ⟨_, rfl, .bool false⟩, fun _ => ⟨_, rfl, .nat (by decide)⟩,
        fun _ => ⟨_, rfl, .ref rfl rfl rfl⟩, trivial⟩⟩
  refine mir_whileLoop_cfgCertificate_of_cutpoint tagOfLoan loopBorrowBody 3
    (.use (.localSub 0 [])) lbBodyPlan (.use (.localSub 1 []))
    lbBodyPlan_wf lbBodyPlan_continuing
    [⟨.byVal, .bool true⟩, ⟨.byVal, .nat 7⟩] lbSt0 (fun out => out.ret = .nat 42)
    lbCutInv lbStrongRank lbCutpoint_step lbCutpoint_exit
    (fun _ => []) id lbExtra [] rfl (Or.inl rfl) (Nat.le_refl 3) ?_
    ⟨subIdWrap_some, rfl, rfl, hRel0, Or.inl ⟨rfl, rfl, rfl⟩⟩
  refine mirCfg_forwardSim_of_waitFree tagOfLoan loopBorrowBody
    (CfgCertificate.whileLoop stdValAlg 3 (.use (.localSub 0 [])) lbBodyPlan
      (.use (.localSub 1 [])) lbBodyPlan_wf lbBodyPlan_continuing).blocks
    (fun _ => []) id lbExtra [] ?_
  intro w bb st ms ⟨hW, _, _, _, hEx⟩
  rcases hEx with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · exact stepsTo_of_runMirToBlock_reached
      (rfl : Anneal.PureMirExec.runMirToBlock loopBorrowBody 1 lbMs0 = .reached lbMsBody)
      ⟨hW, rfl, rfl, hRelBody, Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)⟩
  · exact stepsTo_of_runMirToBlock_reached
      (rfl : Anneal.PureMirExec.runMirToBlock loopBorrowBody 0 lbMsBody = .reached lbMsAfterIter)
      ⟨hW, rfl, rfl, hRelAfter, Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))⟩
  · exact stepsTo_of_runMirToBlock_reached
      (rfl : Anneal.PureMirExec.runMirToBlock loopBorrowBody 2 lbMsAfterIter = .reached lbMsExit)
      ⟨hW, rfl, rfl, hRelExit, Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩))⟩
  · exact ⟨8, _, rfl, _, _, rfl, .nat (by decide), rfl⟩

/-- 2-iteration stride-3 live `V2026_06_01` `CapturedMir` loop:
`fn stride_loop(mut i: u32, mut x: u32) -> u32 { while i < 5 { x += 10; i += 3; } x }`
starting at `i = 0, x = 7` (`i = 0 → 3 → 6`, `x = 7 → 17 → 27`). The header is
the rustc shape of `while i < 5`: it evaluates the comparison into the `bool`
temporary `_3` (`StorageLive(_3); _3 = Lt(copy _1, const 5_u32)`) and switches
on it (`switchInt(copy _3) -> [0: bb2, otherwise: bb1]`), and both successors
start with `StorageDead(_3)`, so the live header genuinely computes `i < 5` for
every `i` rather than enumerating the reachable values
(`strideLoop_header_computes_lt`). -/
def strideLoopBody : CapturedMir :=
  mkBody 2
    [decl .mut u32Ty, decl .mut u32Ty, decl .mut u32Ty, decl .mut boolTy]
    [mkBb
       [mkSt (.storageLive 3),
        mkSt (.assign (pl 3) (.binaryOp .lt (.copy (pl 1)) (u32C 5)))]
       (.switchInt (.copy (pl 3)) ⟨[(0, 2)], 1⟩),
     mkBb
       [mkSt (.storageDead 3),
        mkSt (.assign (pl 2) (.binaryOp .add (.copy (pl 2)) (u32C 10))),
        mkSt (.assign (pl 1) (.binaryOp .add (.copy (pl 1)) (u32C 3)))]
       (.goto 0),
     mkBb
       [mkSt (.storageDead 3),
        mkSt (.assign (pl 0) (.use (.copy (pl 2))))]
       .return_]

def strideAdd10 (v : StdVal) : Option StdVal :=
  match v with
  | ⟨_, .nat n⟩ => some (.nat (n + 10))
  | _ => none

def strideLt5 (v : StdVal) : Option StdVal :=
  match v with
  | ⟨_, .nat n⟩ => some (.bool (Nat.blt n 5))
  | _ => none

def strideCond : RvalOp StdVal :=
  .unary strideLt5 (.localSub 0 [])

def stridePlanBody : FlowPlan StdVal :=
  .seq (.act (.assign (.localSub 1 []) (.unary strideAdd10 (.localSub 1 []))))
    (.act (.assign (.localSub 0 []) (.unary stdAdd3 (.localSub 0 []))))

theorem stridePlanBody_wf : WfPlan stdValAlg stridePlanBody := fun _ _ => rfl

theorem stridePlanBody_continuing :
    ∀ s f, evalPlan stdValAlg stridePlanBody s = .ok f →
      Exists fun s' => f = .continuing s' :=
  evalPlan_seq_continuing stdValAlg (fun _ _ => rfl) (fun _ _ => rfl)
    (evalPlan_act_continuing stdValAlg _)
    (evalPlan_act_continuing stdValAlg _)

def strideSt0 : SymState StdVal :=
  ⟨[⟨.nat 0, .unborrowed⟩, ⟨.nat 7, .unborrowed⟩], [], [], [], [], 0⟩

def strideSt1 : SymState StdVal :=
  ⟨[⟨.nat 3, .unborrowed⟩, ⟨.nat 17, .unborrowed⟩], [], [], [], [], 0⟩

def strideSt2 : SymState StdVal :=
  ⟨[⟨.nat 6, .unborrowed⟩, ⟨.nat 27, .unborrowed⟩], [], [], [], [], 0⟩

/-- Natural remaining-distance ranking measure `5 - i`: drops `5 → 2 → 0`
across the two stride-3 iterations (`Δrank = 3` on iteration 1 and `Δrank = 2`
on iteration 2, refuting unit decrement on both iterations). -/
def strideLoopRank (s : SymState StdVal) : Nat :=
  match s.locals with
  | c :: _ =>
    match stdNatVal? c.val with
    | some i => 5 - i
    | none => 0
  | [] => 0

theorem strideLoopRank_multi_step_descent :
    strideLoopRank strideSt0 = 5 ∧
    strideLoopRank strideSt1 = 2 ∧
    strideLoopRank strideSt2 = 0 ∧
    ¬ (strideLoopRank strideSt0 = strideLoopRank strideSt1 + 1) ∧
    ¬ (strideLoopRank strideSt1 = strideLoopRank strideSt2 + 1) := by
  decide

def strideCutInv (s : SymState StdVal) : Prop :=
  s = strideSt0 ∨ s = strideSt1 ∨ s = strideSt2

theorem strideCutpoint_step : ∀ s, strideCutInv s →
    Exists fun cv => evalRval stdValAlg strideCond s = some cv ∧
      (stdValAlg.asBool cv = some false ∨
       (stdValAlg.asBool cv = some true ∧
        Exists fun s' =>
          evalPlan stdValAlg stridePlanBody s = .ok (.continuing s') ∧
          strideCutInv s' ∧ strideLoopRank s' < strideLoopRank s)) := by
  intro s hs
  rcases hs with rfl | rfl | rfl
  · exact ⟨.bool true, rfl,
      Or.inr ⟨rfl, strideSt1, rfl, Or.inr (Or.inl rfl), by decide⟩⟩
  · exact ⟨.bool true, rfl,
      Or.inr ⟨rfl, strideSt2, rfl, Or.inr (Or.inr rfl), by decide⟩⟩
  · exact ⟨.bool false, rfl, Or.inl rfl⟩

theorem strideCutpoint_exit : ∀ s, strideCutInv s →
    (Exists fun cv => evalRval stdValAlg strideCond s = some cv ∧
      stdValAlg.asBool cv = some false) →
    stateCleanAtReturn s = true ∧
      Exists fun rv => evalRval stdValAlg (.use (.localSub 1 [])) s = some rv ∧
        handleFreeOut stdValAlg ⟨rv, collectRootMutVals s.loans⟩ = true ∧
        (⟨rv, collectRootMutVals s.loans⟩ : FuncOut StdVal).ret = .nat 27 := by
  intro s hs ⟨cv, hcv, hb⟩
  rcases hs with rfl | rfl | rfl
  · injection hcv with hcv
    subst hcv
    exact nomatch hb
  · injection hcv with hcv
    subst hcv
    exact nomatch hb
  · exact ⟨rfl, .nat 27, rfl, rfl, rfl⟩

def strideMs0 : MachineState :=
  initMachineState strideLoopBody [.scalar ⟨0, 4⟩, .scalar ⟨7, 4⟩]

/-- Live `strideLoopBody` state at the header of block `bb` with `i`, `x`, and
the comparison temporary `_3` in slot `t`. -/
def strideMsAt (bb i x : Nat) (t : LocalSlot) : MachineState :=
  { strideMs0 with
    frame :=
      { blockIdx := bb, stmtIdx := 0,
        locals := [.uninit, .init (.scalar ⟨i, 4⟩), .init (.scalar ⟨x, 4⟩), t] } }

/-- `_3 = Lt(copy _1, const 5_u32)` as a live `bool` scalar. -/
def strideLtSlot (b : Bool) : LocalSlot :=
  .init (.scalar ⟨if b then 1 else 0, 1⟩)

def strideMsBody0 : MachineState := strideMsAt 1 0 7 (strideLtSlot true)

def strideMs1 : MachineState := strideMsAt 0 3 17 .dead

def strideMsBody1 : MachineState := strideMsAt 1 3 17 (strideLtSlot true)

def strideMs2 : MachineState := strideMsAt 0 6 27 .dead

def strideMsExit : MachineState := strideMsAt 2 6 27 (strideLtSlot false)

/-- **The live header computes `i < 5`, not a table of reachable values**: from
the header with any of `i = 2, 4` (never reached from `i = 0` by stride 3) the
live MIR still enters the body, and from `i = 5` (the boundary) it exits, with
`_3` holding `Lt(i, 5)`; the initial state has `_3` dead. -/
theorem strideLoop_header_computes_lt :
    strideMs0.frame.locals =
      [.uninit, .init (.scalar ⟨0, 4⟩), .init (.scalar ⟨7, 4⟩), .dead] ∧
    Anneal.PureMirExec.runMirToBlock strideLoopBody 1 (strideMsAt 0 2 0 .dead) =
      .reached (strideMsAt 1 2 0 (strideLtSlot true)) ∧
    Anneal.PureMirExec.runMirToBlock strideLoopBody 1 (strideMsAt 0 4 0 .dead) =
      .reached (strideMsAt 1 4 0 (strideLtSlot true)) ∧
    Anneal.PureMirExec.runMirToBlock strideLoopBody 2 (strideMsAt 0 5 0 .dead) =
      .reached (strideMsAt 2 5 0 (strideLtSlot false)) :=
  ⟨rfl, rfl, rfl, rfl⟩

def strideExtra (bb : Nat) (st : SymState StdVal) (ms : MachineState) : Prop :=
  (bb = 0 ∧ st = strideSt0 ∧ ms = strideMs0) ∨
  (bb = 1 ∧ st = strideSt0 ∧ ms = strideMsBody0) ∨
  (bb = 0 ∧ st = strideSt1 ∧ ms = strideMs1) ∨
  (bb = 1 ∧ st = strideSt1 ∧ ms = strideMsBody1) ∨
  (bb = 0 ∧ st = strideSt2 ∧ ms = strideMs2) ∨
  (bb = 2 ∧ st = strideSt2 ∧ ms = strideMsExit)

/-- **Test 2d-2 (2-iteration stride-3 strong-descent cutpoint over live
`V2026_06_01` MIR)**: `strideLoopRank` (`5 - i`) drops `5 → 2 → 0` (`Δrank = 3`
then `Δrank = 2`), and `mir_whileLoop_cfgCertificate_of_cutpoint_blockRel`
certifies `strideLoopBody` end-to-end to `MirWpConverges` returning `27` from
the wrapper-free `mirCfgBlockRel` obligations directly. -/
theorem strideLoop_strongDescent_cutpoint_sound :
    Anneal.MirFuelFree.MirWpConverges strideLoopBody strideMs0
      (LiftedMirPost tagOfLoan (fun out => out.ret = .nat 27)) := by
  have hRel0 : mirStateRel tagOfLoan [] strideSt0 strideMs0 :=
    ⟨⟨trivial, trivial⟩,
     mirLocalsRel_of_localsRefine
       ⟨fun _ => ⟨_, rfl, .nat (by decide)⟩, fun _ => ⟨_, rfl, .nat (by decide)⟩, trivial⟩⟩
  have hRelB0 : mirStateRel tagOfLoan [] strideSt0 strideMsBody0 :=
    ⟨⟨trivial, trivial⟩,
     mirLocalsRel_of_localsRefine
       ⟨fun _ => ⟨_, rfl, .nat (by decide)⟩, fun _ => ⟨_, rfl, .nat (by decide)⟩, trivial⟩⟩
  have hRel1 : mirStateRel tagOfLoan [] strideSt1 strideMs1 :=
    ⟨⟨trivial, trivial⟩,
     mirLocalsRel_of_localsRefine
       ⟨fun _ => ⟨_, rfl, .nat (by decide)⟩, fun _ => ⟨_, rfl, .nat (by decide)⟩, trivial⟩⟩
  have hRelB1 : mirStateRel tagOfLoan [] strideSt1 strideMsBody1 :=
    ⟨⟨trivial, trivial⟩,
     mirLocalsRel_of_localsRefine
       ⟨fun _ => ⟨_, rfl, .nat (by decide)⟩, fun _ => ⟨_, rfl, .nat (by decide)⟩, trivial⟩⟩
  have hRel2 : mirStateRel tagOfLoan [] strideSt2 strideMs2 :=
    ⟨⟨trivial, trivial⟩,
     mirLocalsRel_of_localsRefine
       ⟨fun _ => ⟨_, rfl, .nat (by decide)⟩, fun _ => ⟨_, rfl, .nat (by decide)⟩, trivial⟩⟩
  have hRelEx : mirStateRel tagOfLoan [] strideSt2 strideMsExit :=
    ⟨⟨trivial, trivial⟩,
     mirLocalsRel_of_localsRefine
       ⟨fun _ => ⟨_, rfl, .nat (by decide)⟩, fun _ => ⟨_, rfl, .nat (by decide)⟩, trivial⟩⟩
  refine mir_whileLoop_cfgCertificate_of_cutpoint_blockRel tagOfLoan
    strideLoopBody 5 strideCond stridePlanBody (.use (.localSub 1 []))
    stridePlanBody_wf stridePlanBody_continuing
    [⟨.byVal, .nat 0⟩, ⟨.byVal, .nat 7⟩] strideSt0 (fun out => out.ret = .nat 27)
    strideCutInv strideLoopRank strideCutpoint_step strideCutpoint_exit
    (fun _ => []) id strideExtra [] rfl (Or.inl rfl) (Nat.le_refl 5) ?_
    ⟨rfl, rfl, hRel0, Or.inl ⟨rfl, rfl, rfl⟩⟩
  intro bb st ms ⟨_, _, _, hEx⟩
  rcases hEx with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · exact stepsTo_of_runMirToBlock_reached
      (rfl : Anneal.PureMirExec.runMirToBlock strideLoopBody 1 strideMs0 = .reached strideMsBody0)
      ⟨rfl, rfl, hRelB0, Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)⟩
  · exact stepsTo_of_runMirToBlock_reached
      (rfl : Anneal.PureMirExec.runMirToBlock strideLoopBody 0 strideMsBody0 = .reached strideMs1)
      ⟨rfl, rfl, hRel1, Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))⟩
  · exact stepsTo_of_runMirToBlock_reached
      (rfl : Anneal.PureMirExec.runMirToBlock strideLoopBody 1 strideMs1 = .reached strideMsBody1)
      ⟨rfl, rfl, hRelB1, Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)))⟩
  · exact stepsTo_of_runMirToBlock_reached
      (rfl : Anneal.PureMirExec.runMirToBlock strideLoopBody 0 strideMsBody1 = .reached strideMs2)
      ⟨rfl, rfl, hRel2, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))))⟩
  · exact stepsTo_of_runMirToBlock_reached
      (rfl : Anneal.PureMirExec.runMirToBlock strideLoopBody 2 strideMs2 = .reached strideMsExit)
      ⟨rfl, rfl, hRelEx, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩))))⟩
  · exact ⟨8, _, rfl, _, _, rfl, .nat (by decide), rfl⟩

/-- The structured stride loop plan runs both iterations and falls through in
`strideSt2`, and `evalPlan_whileLoop_continuing` (from
`stridePlanBody_continuing`) shows that it can only ever fall through, which is
the `.continuing`-only premise that loop-bodied certificate arms need. -/
theorem strideLoop_plan_continuing :
    evalPlan stdValAlg (.whileLoop 5 strideCond stridePlanBody) strideSt0 =
      .ok (.continuing strideSt2) ∧
    ∀ s f, evalPlan stdValAlg (.whileLoop 5 strideCond stridePlanBody) s = .ok f →
      Exists fun s' => f = .continuing s' :=
  ⟨rfl, evalPlan_whileLoop_continuing stdValAlg 5 strideCond stridePlanBody_wf
    stridePlanBody_continuing⟩

/-! ## Test 3: Hybrid `SpatialPin` Freeze → `zerocopy` Byte Write → Unpin -/

/-- `fn patch_low_byte(v: u32) -> u32 { let mut x = v; let p = &raw mut x;
let q = p as *mut u8; unsafe { *q = 0xAB }; x }`: a `zerocopy`-style raw
byte-window store into the low byte of a `u32`. -/
def zcBody : CapturedMir :=
  mkBody 1
    [decl .mut u32Ty, decl .not u32Ty, decl .mut u32Ty, decl .not rawU32Ty, decl .not rawU8Ty]
    [mkBb
      [mkSt (.storageLive 2),
       mkSt (.assign (pl 2) (.use (.copy (pl 1)))),
       mkSt (.storageLive 3),
       mkSt (.assign (pl 3) (.rawPtr .mut (pl 2))),
       mkSt (.storageLive 4),
       mkSt (.assign (pl 4) (.cast .ptrToPtr (.copy (pl 3)) rawU8Ty)),
       mkSt (.assign (pl 4 [.deref]) (.use (u8C 0xAB))),
       mkSt (.storageDead 4),
       mkSt (.storageDead 3),
       mkSt (.assign (pl 0) (.use (.copy (pl 2)))),
       mkSt (.storageDead 2)]
      .return_]

/-- `0x11223344`. -/
def zcV0 : Nat := 287454020

/-- `0x112233AB`: `zcV0` with its low byte replaced by `0xAB`. -/
def zcV1 : Nat := 287454123

def zcLayouts : LayoutTable := zcBody.layouts

def zcMs0 : MachineState := initMachineState zcBody [.scalar ⟨zcV0, 4⟩]

/-- Live state right before the byte store: `x = zcV0` and both raw pointers
carry the `unique` tag `1` rooted at `_2`. -/
def zcMsPinned : MachineState :=
  { frame :=
      { blockIdx := 0, stmtIdx := 6,
        locals :=
          [.uninit, .init (.scalar ⟨zcV0, 4⟩), .init (.scalar ⟨zcV0, 4⟩),
           .init (.ptr ⟨1, 0⟩ 8), .init (.ptr ⟨1, 0⟩ 8)] }
    memory :=
      { zcMs0.memory with
        borrows := [{ tag := 1, targetLocal := 2, targetProjection := [], perm := .unique }]
        nextTag := 2 } }

/-- Live state right after the byte store `*q = 0xAB`. -/
def zcMsWritten : MachineState :=
  { zcMsPinned with
    frame :=
      { blockIdx := 0, stmtIdx := 7,
        locals :=
          [.uninit, .init (.scalar ⟨zcV0, 4⟩), .init (.scalar ⟨zcV1, 4⟩),
           .init (.ptr ⟨1, 0⟩ 8), .init (.ptr ⟨1, 0⟩ 8)] } }

theorem zc_pinned_path :
    StepPath (Anneal.PureMirExec.mirStep zcBody) zcMs0 6 zcMsPinned :=
  stepPath_of_runSilentSteps rfl

/-- The live raw-pointer byte store is one MIR step. -/
theorem zc_store_step :
    Anneal.PureMirExec.mirStep zcBody zcMsPinned = .cont zcMsWritten := rfl

/-- The trusted byte windows of `x` before and after the live store. -/
def zcWindowBefore : List AbstractByte := encodeLittleEndianBytes zcV0 4 none

def zcWindowAfter : List AbstractByte :=
  [.init 0xAB none, .init 0x33 none, .init 0x22 none, .init 0x11 none]

theorem zc_windows :
    placeByteWindow? zcLayouts u32Ty zcMsPinned 2 [] = some zcWindowBefore ∧
    placeByteWindow? zcLayouts u32Ty zcMsWritten 2 [] = some zcWindowAfter :=
  ⟨rfl, rfl⟩

/-- `u32` spatial codec at the body's layout table. -/
def zcCodec : SpatialCodec StdVal := u32SpatialCodec zcLayouts

/-- The spatial cells written by the `PureLift` mutation: exactly the raw-byte
cells of the live post-store window. -/
def zcCellsAfter : List (CellVal StdVal) :=
  [.rawByte 0xAB, .rawByte 0x33, .rawByte 0x22, .rawByte 0x11]

theorem zc_cells_from_live_store :
    cellsOfAbstractBytes zcWindowAfter = some zcCellsAfter := rfl

/-- **Freeze = live byte window**: freezing `x = zcV0` with the `u32` codec
produces exactly the trusted byte window of the live place `_2`, which is
`TypedAt zcV0` under the exact-width `u32` codec. -/
theorem zc_freeze_eq_live_window :
    placeByteWindow? zcLayouts u32Ty zcMsPinned 2 [] = some zcWindowBefore ∧
    abstractBytesOfCells (zcCodec.encode (.nat zcV0)) = some zcWindowBefore ∧
    Anneal.SepLogicLenses.TypedAt u32ExactLE 0 ⟨zcV0, by decide⟩ zcWindowBefore :=
  spatialCodec_freeze_eq_placeByteWindow (u32MirCodec zcLayouts) 32 u32Embed u32Embed?
    u32Embed_embed? zcMsPinned 2 [] (.nat zcV0) ⟨zcV0, by decide⟩ rfl rfl

/-- **Unpin = trusted decode**: the post-store cells unpin to `zcV1`, which is
exactly the trusted `u32` decoding of the live window, i.e. the live value of
`x`, and the window is `TypedAt zcV1`. -/
theorem zc_unpin_eq_live_decode :
    zcCodec.decode zcCellsAfter = some (.nat zcV1) ∧
    decodeValueFromBytes defaultCodecFuel zcLayouts u32Ty zcWindowAfter =
      some (.scalar ⟨zcV1, 4⟩) ∧
    placeValue? zcMsWritten 2 [] = some (.scalar ⟨zcV1, 4⟩) ∧
    Anneal.SepLogicLenses.TypedAt u32ExactLE 0 ⟨zcV1, by decide⟩ zcWindowAfter :=
  ⟨((u32MirCodec zcLayouts).spatialCodec_unpin_iff_mir_decode 32 u32Embed u32Embed?
      u32Embed_embed? zcCellsAfter zcWindowAfter rfl rfl).2 ⟨zcV1, by decide⟩ rfl,
   rfl, rfl, rfl⟩

/-- **Tree Borrows frame**: the store keeps the raw pointer's `unique` tag
rooted at `_2`, leaves the Tree Borrows table unchanged, and touches no other
local. -/
theorem zc_store_frame :
    BorrowAt zcMsWritten 1 2 [] mutGranting ∧
    zcMsWritten.memory.borrows = zcMsPinned.memory.borrows ∧
    (∀ i, i ≠ 2 → zcMsWritten.frame.locals[i]? = zcMsPinned.frame.locals[i]?) := by
  refine ⟨⟨_, rfl, rfl, rfl, rfl⟩, rfl, ?_⟩
  intro i hi
  match i, hi with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, hi => exact absurd rfl hi
  | _ + 3, _ => rfl

def zcParams : List (ParamInput StdVal) := [⟨.byVal, .nat zcV0⟩]

/-- `x = v; p = &raw mut x` (loan `0`); freeze loan `0` into spatial block `0`;
write the post-store cells; unpin; end the loan; return `x`. -/
def zcPlanWith (cells : List (CellVal StdVal)) : FlowPlan StdVal :=
  .seq (.act (.assign (.localSub 1 []) (.use (.localSub 0 []))))
    (.seq (.act (.borrow 2 .mutBorrow (.localSub 1 [])))
      (.seq (.act (.freezeSpatial 0 zcCodec))
        (.seq (.act (.mutateSpatial 0 0 cells))
          (.seq (.act (.reabsorbSpatial 0 zcCodec))
            (.act (.endLoan 0))))))

/-- `PureLift` result: `zcV1`. -/
theorem zc_pureLift_eval :
    evalFnValue stdValAlg zcParams (zcPlanWith zcCellsAfter) (.use (.localSub 1 [])) =
      .ok ⟨.nat zcV1, []⟩ := rfl

theorem zc_entry_rel : mirStateRel tagOfLoan [] ⟨[⟨.nat zcV0, .unborrowed⟩], [], [], [], [], 0⟩ zcMs0 :=
  ⟨⟨trivial, trivial⟩,
   mirLocalsRel_of_localsRefine ⟨fun _ => ⟨_, rfl, .nat (by decide)⟩, trivial⟩⟩

/-- **Test 3 (adequacy)**: the hybrid freeze → byte write → unpin function
converges on live MIR to a normal return refining the `PureLift` result. -/
theorem zc_sound :
    Anneal.MirFuelFree.MirWpConverges zcBody zcMs0
      (LiftedMirPost tagOfLoan (fun out => out.ret = .nat zcV1)) :=
  mir_pure_lift_sound_of_evalFuel tagOfLoan zcBody [] zcParams (zcPlanWith zcCellsAfter)
    (.use (.localSub 1 [])) _ zcMs0 ⟨.nat zcV1, []⟩ (.scalar ⟨zcV1, 4⟩) _ 16 []
    ⟨_, rfl, zc_entry_rel⟩ zc_pureLift_eval rfl rfl (.nat (by decide)) rfl

/-! ### Test 3b: 4-State Lockstep `spatialPinnedBlockHolds` Diagram & Multi-Field Aggregate `FieldsTyped` -/

def zcSt0 : SymState StdVal :=
  ⟨[⟨.nat zcV0, .unborrowed⟩], [], [], [], [], 0⟩

def zcStBorrowed : SymState StdVal :=
  ⟨[⟨.nat zcV0, .unborrowed⟩, ⟨.nat zcV0, .mutLocked 0⟩, ⟨.refVal 0 [], .unborrowed⟩],
   [⟨0, .activeMut, ⟨.nat zcV0, .unborrowed⟩, .direct (.localReg 1) []⟩],
   [], [], [], 0⟩

def zcStPinned : SymState StdVal :=
  ⟨[⟨.nat zcV0, .unborrowed⟩, ⟨.nat zcV0, .mutLocked 0⟩, ⟨.refVal 0 [], .unborrowed⟩],
   [⟨0, .spatialPinned 0 zcCodec, ⟨.nat zcV0, .unborrowed⟩, .direct (.localReg 1) []⟩],
   [], [],
   [⟨0, 0, .readWrite, 0, 0, [.rawByte 0x44, .rawByte 0x33, .rawByte 0x22, .rawByte 0x11]⟩],
   1⟩

def zcStWritten : SymState StdVal :=
  ⟨[⟨.nat zcV0, .unborrowed⟩, ⟨.nat zcV0, .mutLocked 0⟩, ⟨.refVal 0 [], .unborrowed⟩],
   [⟨0, .spatialPinned 0 zcCodec, ⟨.nat zcV0, .unborrowed⟩, .direct (.localReg 1) []⟩],
   [], [],
   [⟨0, 0, .readWrite, 0, 0, zcCellsAfter⟩],
   1⟩

def zcStUnpinned : SymState StdVal :=
  ⟨[⟨.nat zcV0, .unborrowed⟩, ⟨.nat zcV0, .mutLocked 0⟩, ⟨.refVal 0 [], .unborrowed⟩],
   [⟨0, .activeMut, ⟨.nat zcV1, .unborrowed⟩, .direct (.localReg 1) []⟩],
   [], [], [], 1⟩

/-- **4-state lockstep commuting diagram for `SpatialPin` over live MIR**:
1. Before freeze: `mirStateRel tagOfLoan [(0, 2, [])] zcStBorrowed zcMsPinned`
2. After `freezeToSpatialInState`: `spatialPinnedBlockHolds ... zcStPinned zcMsPinned`
   (by `freeze_spatialPinnedBlockHolds`)
3. After `mutateSpatialInState` and live store `mirStep zcBody zcMsPinned = .cont zcMsWritten`:
   `spatialPinnedBlockHolds ... zcStWritten zcMsWritten`
   (by `mutate_spatialPinnedBlockHolds`)
4. After `reabsorbFromSpatialInState`: `mirStateRel tagOfLoan [(0, 2, [])] zcStUnpinned zcMsWritten`
   (by `unpin_restores_mirStateRel`). -/
theorem zc_lockstep_pin_lifecycle :
    mirStateRel tagOfLoan [(0, 2, [])] zcStBorrowed zcMsPinned ∧
    freezeToSpatialInState stdValAlg 0 zcCodec zcStBorrowed = .ok zcStPinned ∧
    spatialPinnedBlockHolds tagOfLoan zcLayouts u32Ty 0 0 zcCodec 2 [] zcStPinned zcMsPinned ∧
    mutateSpatialInState 0 0 zcCellsAfter zcStPinned = .ok zcStWritten ∧
    spatialPinnedBlockHolds tagOfLoan zcLayouts u32Ty 0 0 zcCodec 2 [] zcStWritten zcMsWritten ∧
    reabsorbFromSpatialInState stdValAlg 0 zcCodec zcStWritten = .ok zcStUnpinned ∧
    mirStateRel tagOfLoan [(0, 2, [])] zcStUnpinned zcMsWritten := by
  have hPin :
      spatialPinnedBlockHolds tagOfLoan zcLayouts u32Ty 0 0 zcCodec 2 [] zcStPinned zcMsPinned :=
    freeze_spatialPinnedBlockHolds (u32MirCodec zcLayouts) 32 u32Embed u32Embed? u32Embed_embed?
      tagOfLoan stdValAlg 0 (st := zcStBorrowed) (x := ⟨zcV0, by decide⟩) rfl ⟨_, rfl, rfl⟩ rfl
      ⟨_, rfl, rfl, rfl, rfl⟩
  have hWritten :
      spatialPinnedBlockHolds tagOfLoan zcLayouts u32Ty 0 0 zcCodec 2 [] zcStWritten zcMsWritten :=
    mutate_spatialPinnedBlockHolds (tag := 0) (newCells := zcCellsAfter) hPin rfl rfl rfl
      ⟨_, rfl, rfl, rfl, rfl⟩
  have hUnpinned :
      mirStateRel tagOfLoan [(0, 2, [])] zcStUnpinned zcMsWritten :=
    unpin_restores_mirStateRel (u32MirCodec zcLayouts) 32 u32Embed u32Embed? u32Embed_embed?
      (u32_isIntoBytes zcLayouts) tagOfLoan stdValAlg 0 0 zcCodec (y := ⟨zcV1, by decide⟩)
      hWritten rfl rfl (.nat (by decide))
      (mirLocalsRel_of_localsRefine
        ⟨fun _ => ⟨_, rfl, .nat (by decide)⟩,
         (fun h => nomatch h),
         fun _ => ⟨_, rfl, .ref rfl rfl rfl⟩,
         trivial⟩)
  exact ⟨⟨⟨⟨trivial, trivial⟩,
     ⟨⟨rfl, ⟨_, rfl, .nat (by decide)⟩, ⟨_, rfl, rfl, rfl, rfl⟩⟩, trivial⟩⟩,
    mirLocalsRel_of_localsRefine
      ⟨fun _ => ⟨_, rfl, .nat (by decide)⟩,
       (fun h => nomatch h),
       fun _ => ⟨_, rfl, .ref rfl rfl rfl⟩,
       trivial⟩⟩,
   rfl, hPin, rfl, hWritten, rfl, hUnpinned⟩

/-- **Multi-field aggregate `(u32, u32)` freeze → byte-slice mutation → unpin**
connected to `SepLogicLenses.FieldsTyped`: freezing `(7, 9)` yields an 8-byte
block satisfying `FieldsTyped u32ExactLE 0 u32ExactLE 4`, mutating the second
field's 4 bytes (`offset 4..8`) to `zcV1` preserves field 0 (`7`), and unpins to
`(.pair (.nat 7) (.nat zcV1))`. -/
theorem zcPair_fieldsTyped_and_field1_mutation_canary :
    let p0 : {v : Nat // v < 256 ^ 4} × {v : Nat // v < 256 ^ 4} :=
      (⟨7, by decide⟩, ⟨9, by decide⟩)
    let cellsAfter : List (CellVal StdVal) :=
      [.rawByte 7, .rawByte 0, .rawByte 0, .rawByte 0,
       .rawByte 0xAB, .rawByte 0x33, .rawByte 0x22, .rawByte 0x11]
    let pairPlan : FlowPlan StdVal :=
      .seq (.act (.assign (.localSub 1 []) (.use (.localSub 0 []))))
        (.seq (.act (.borrow 2 .mutBorrow (.localSub 1 [])))
          (.seq (.act (.freezeSpatial 0 u32PairSpatialCodec))
            (.seq (.act (.mutateSpatial 0 0 cellsAfter))
              (.seq (.act (.reabsorbSpatial 0 u32PairSpatialCodec))
                (.act (.endLoan 0))))))
    Anneal.SepLogicLenses.FieldsTyped u32ExactLE 0 u32ExactLE 4
      (u32PairExactLE.encode p0) ∧
    evalFnValue stdValAlg [⟨.byVal, .pair (.nat 7) (.nat 9)⟩] pairPlan
      (.use (.localSub 1 [])) =
      .ok ⟨.pair (.nat 7) (.nat zcV1), []⟩ :=
  ⟨(u32PairExactLE_encode_fieldsTyped ⟨7, by decide⟩ ⟨9, by decide⟩).1, rfl⟩

/-! ### Test 3c: General Freeze / Unpin Bridges and a Field-Granular Pin on Live MIR -/

/-- **General freeze bridge, instantiated**: the mid-pin relation after the
`PureLift` freeze follows from `freeze_spatialPinnedBlockHolds` (the live place
`_2` holds `zcV0`, and loan `0`'s tag is live and `unique`), not from unfolding
the post-freeze state. -/
theorem zc_freeze_general :
    spatialPinnedBlockHolds tagOfLoan zcLayouts u32Ty 0 0 zcCodec 2 [] zcStPinned zcMsPinned :=
  freeze_spatialPinnedBlockHolds (u32MirCodec zcLayouts) 32 u32Embed u32Embed? u32Embed_embed?
    tagOfLoan stdValAlg 0 (st := zcStBorrowed) (x := ⟨zcV0, by decide⟩) rfl ⟨_, rfl, rfl⟩ rfl
    ⟨_, rfl, rfl, rfl, rfl⟩

/-- **General unpin bridge, instantiated**: unpinning after the live store
yields exactly the value the trusted decoder reads from the live window of `_2`
(`u32` is `zerocopy::IntoBytes`). -/
theorem zc_unpin_general :
    Exists fun x => Exists fun bs => Exists fun e' =>
      placeByteWindow? zcLayouts u32Ty zcMsWritten 2 [] = some bs ∧
      decodeValueFromBytes defaultCodecFuel zcLayouts u32Ty bs =
        some ((u32MirCodec zcLayouts).toValue x) ∧
      findLoan 0 zcStUnpinned.loans = some e' ∧ e'.phase = .activeMut ∧
      e'.cell.val = u32Embed x ∧ isUnborrowed e'.cell.perm = true :=
  unpin_eq_live_mir_decode (u32MirCodec zcLayouts) 32 u32Embed u32Embed? u32Embed_embed?
    (u32_isIntoBytes zcLayouts) tagOfLoan stdValAlg 0 0 zcCodec
    (zc_lockstep_pin_lifecycle.2.2.2.2.1) rfl

/-- `fn patch_field(a: u32, b: u32) -> (u32, u32) { let mut p = (a, b);
let q = &raw mut p.1; let r = q as *mut u8; unsafe { *r = 0xAB }; p }`: a
localized raw byte-window store into one field of a typed aggregate. -/
def fieldPinBody : CapturedMir :=
  mkBody 2
    [decl .mut pairTy, decl .not u32Ty, decl .not u32Ty, decl .mut pairTy,
     decl .not rawU32Ty, decl .not rawU8Ty]
    [mkBb
      [mkSt (.storageLive 3),
       mkSt (.assign (pl 3) (.aggregate .tuple [.copy (pl 1), .copy (pl 2)])),
       mkSt (.storageLive 4),
       mkSt (.assign (pl 4) (.rawPtr .mut (pl 3 [.field 1 u32Ty]))),
       mkSt (.storageLive 5),
       mkSt (.assign (pl 5) (.cast .ptrToPtr (.copy (pl 4)) rawU8Ty)),
       mkSt (.assign (pl 5 [.deref]) (.use (u8C 0xAB))),
       mkSt (.storageDead 5),
       mkSt (.storageDead 4),
       mkSt (.assign (pl 0) (.use (.copy (pl 3)))),
       mkSt (.storageDead 3)]
      .return_]

def fpMs0 : MachineState :=
  initMachineState fieldPinBody [.scalar ⟨7, 4⟩, .scalar ⟨zcV0, 4⟩]

/-- Live state right before the field store: the raw pointers carry the
`unique` tag `1` rooted at the field place `_3.1`. -/
def fpMsPinned : MachineState :=
  { frame :=
      { blockIdx := 0, stmtIdx := 6,
        locals :=
          [.uninit, .init (.scalar ⟨7, 4⟩), .init (.scalar ⟨zcV0, 4⟩),
           .init (.aggregate 0 [.scalar ⟨7, 4⟩, .scalar ⟨zcV0, 4⟩]),
           .init (.ptr ⟨1, 0⟩ 8), .init (.ptr ⟨1, 0⟩ 8)] }
    memory :=
      { fpMs0.memory with
        borrows :=
          [{ tag := 1, targetLocal := 3, targetProjection := [.field 1 u32Ty],
             perm := .unique }]
        nextTag := 2 } }

/-- Live state right after the field store `*r = 0xAB`. -/
def fpMsWritten : MachineState :=
  { fpMsPinned with
    frame :=
      { blockIdx := 0, stmtIdx := 7,
        locals :=
          [.uninit, .init (.scalar ⟨7, 4⟩), .init (.scalar ⟨zcV0, 4⟩),
           .init (.aggregate 0 [.scalar ⟨7, 4⟩, .scalar ⟨zcV1, 4⟩]),
           .init (.ptr ⟨1, 0⟩ 8), .init (.ptr ⟨1, 0⟩ 8)] } }

theorem fp_pinned_path :
    StepPath (Anneal.PureMirExec.mirStep fieldPinBody) fpMs0 6 fpMsPinned :=
  stepPath_of_runSilentSteps rfl

theorem fp_store_step :
    Anneal.PureMirExec.mirStep fieldPinBody fpMsPinned = .cont fpMsWritten := rfl

/-- **Field-local store with sibling and Tree Borrows frames**: the store
rewrites exactly the field window of `_3.1` (to the same post-store cells as
Test 3), leaves the sibling field `_3.0` and the Tree Borrows table unchanged,
and keeps the `unique` tag rooted at `_3.1`. -/
theorem fp_store_frame :
    placeByteWindow? zcLayouts u32Ty fpMsPinned 3 [1] = some zcWindowBefore ∧
    placeByteWindow? zcLayouts u32Ty fpMsWritten 3 [1] = some zcWindowAfter ∧
    placeValue? fpMsWritten 3 [0] = placeValue? fpMsPinned 3 [0] ∧
    fpMsWritten.memory.borrows = fpMsPinned.memory.borrows ∧
    BorrowAt fpMsWritten 1 3 [1] mutGranting :=
  ⟨rfl, rfl, rfl, rfl, ⟨_, rfl, rfl, rfl, rfl⟩⟩

def fpParams : List (ParamInput StdVal) := [⟨.byVal, .nat 7⟩, ⟨.byVal, .nat zcV0⟩]

/-- `p = (a, b)`; `q = &mut p.1` (loan `0`); pin, write, unpin; end; return `p`. -/
def fpPlan : FlowPlan StdVal :=
  .seq (.act (.assign (.localSub 2 []) (.binary stdMkPair (.localSub 0 []) (.localSub 1 []))))
    (.seq (.act (.borrow 3 .mutBorrow (.localSub 2 [1])))
      (.seq (.act (.freezeSpatial 0 zcCodec))
        (.seq (.act (.mutateSpatial 0 0 zcCellsAfter))
          (.seq (.act (.reabsorbSpatial 0 zcCodec))
            (.act (.endLoan 0))))))

/-- `PureLift` state after `q = &mut p.1`. -/
def fpStBorrowed : SymState StdVal :=
  ⟨[⟨.nat 7, .unborrowed⟩, ⟨.nat zcV0, .unborrowed⟩,
    ⟨.pair (.nat 7) (.nat zcV0), .split [([1], .mutLocked 0)]⟩, ⟨.refVal 0 [], .unborrowed⟩],
   [⟨0, .activeMut, ⟨.nat zcV0, .unborrowed⟩, .direct (.localReg 2) [1]⟩],
   [], [], [], 0⟩

theorem fp_borrowed_eval :
    evalPlan stdValAlg
        (.seq (.act (.assign (.localSub 2 [])
            (.binary stdMkPair (.localSub 0 []) (.localSub 1 []))))
          (.act (.borrow 3 .mutBorrow (.localSub 2 [1]))))
        ⟨[⟨.nat 7, .unborrowed⟩, ⟨.nat zcV0, .unborrowed⟩], [], [], [], [], 0⟩ =
      .ok (.continuing fpStBorrowed) := rfl

/-- The field loan is realized on the live machine before the freeze. -/
theorem fp_borrowed_rel :
    mirStateRel tagOfLoan [(0, 3, [1])] fpStBorrowed fpMsPinned :=
  ⟨⟨⟨trivial, trivial⟩,
    ⟨⟨rfl, ⟨_, rfl, .nat (by decide)⟩, ⟨_, rfl, rfl, rfl, rfl⟩⟩, trivial⟩⟩,
   mirLocalsRel_of_localsRefine
     ⟨fun _ => ⟨_, rfl, .nat (by decide)⟩, fun _ => ⟨_, rfl, .nat (by decide)⟩,
      (fun h => nomatch h), fun _ => ⟨_, rfl, .ref rfl rfl rfl⟩, trivial⟩⟩

def fpStPinned : SymState StdVal :=
  match freezeToSpatialInState stdValAlg 0 zcCodec fpStBorrowed with
  | .ok st => st
  | .fail => fpStBorrowed

def fpStWritten : SymState StdVal :=
  match mutateSpatialInState 0 0 zcCellsAfter fpStPinned with
  | .ok st => st
  | .fail => fpStPinned

def fpStUnpinned : SymState StdVal :=
  match unpinFromSpatialInState stdValAlg 0 zcCodec fpStWritten with
  | .ok st => st
  | .fail => fpStWritten

/-- **Field-granular hybrid pin over live MIR**:
1. the general freeze bridge materializes the field window of `_3.1` as the
   pinned block (`freeze_spatialPinnedBlockHolds`, path `[1]`);
2. the general mutation bridge (`mutate_spatialPinnedBlockHolds`) and the live
   field store keep `spatialPinnedBlockHolds`;
3. the general unpin bridges (`unpin_eq_live_mir_decode`,
   `unpin_restores_mirStateRel`) restore loan `0` to the value the trusted
   decoder reads from the live field window and re-establish `mirStateRel`;
4. the whole-tuple byte windows of `_3` in `fpMsPinned` and `fpMsWritten`
   satisfy `SepLogicLenses.FieldsTyped u32ExactLE 0 u32ExactLE 4` at field
   offsets `0` and `4` (`placeByteWindow?_u32Pair_fieldsTyped`). -/
theorem fp_pin_lifecycle :
    spatialPinnedBlockHolds tagOfLoan zcLayouts u32Ty 0 0 zcCodec 3 [1] fpStPinned fpMsPinned ∧
    mutateSpatialInState 0 0 zcCellsAfter fpStPinned = .ok fpStWritten ∧
    spatialPinnedBlockHolds tagOfLoan zcLayouts u32Ty 0 0 zcCodec 3 [1] fpStWritten fpMsWritten ∧
    unpinFromSpatialInState stdValAlg 0 zcCodec fpStWritten = .ok fpStUnpinned ∧
    mirStateRel tagOfLoan [(0, 3, [1])] fpStUnpinned fpMsWritten ∧
    (Exists fun x => Exists fun bs => Exists fun e' =>
      placeByteWindow? zcLayouts u32Ty fpMsWritten 3 [1] = some bs ∧
      decodeValueFromBytes defaultCodecFuel zcLayouts u32Ty bs =
        some ((u32MirCodec zcLayouts).toValue x) ∧
      findLoan 0 fpStUnpinned.loans = some e' ∧ e'.phase = .activeMut ∧
      e'.cell.val = u32Embed x ∧ isUnborrowed e'.cell.perm = true) ∧
    (Exists fun bsPin =>
      placeByteWindow? zcLayouts (u32PairTy 99) fpMsPinned 3 [] = some bsPin ∧
      bsPin = u32PairExactLE.encode (⟨7, by decide⟩, ⟨zcV0, by decide⟩) ∧
      Anneal.SepLogicLenses.FieldsTyped u32ExactLE 0 u32ExactLE 4 bsPin) ∧
    (Exists fun bsWr =>
      placeByteWindow? zcLayouts (u32PairTy 99) fpMsWritten 3 [] = some bsWr ∧
      bsWr = u32PairExactLE.encode (⟨7, by decide⟩, ⟨zcV1, by decide⟩) ∧
      Anneal.SepLogicLenses.FieldsTyped u32ExactLE 0 u32ExactLE 4 bsWr) := by
  have hPinned :
      spatialPinnedBlockHolds tagOfLoan zcLayouts u32Ty 0 0 zcCodec 3 [1] fpStPinned fpMsPinned :=
    freeze_spatialPinnedBlockHolds (u32MirCodec zcLayouts) 32 u32Embed u32Embed? u32Embed_embed?
      tagOfLoan stdValAlg 0 (st := fpStBorrowed) (x := ⟨zcV0, by decide⟩) rfl ⟨_, rfl, rfl⟩
      rfl ⟨_, rfl, rfl, rfl, rfl⟩
  have hWritten :
      spatialPinnedBlockHolds tagOfLoan zcLayouts u32Ty 0 0 zcCodec 3 [1] fpStWritten
        fpMsWritten :=
    mutate_spatialPinnedBlockHolds (tag := 0) (newCells := zcCellsAfter) hPinned rfl rfl rfl
      ⟨_, rfl, rfl, rfl, rfl⟩
  have hUnpinnedRel :
      mirStateRel tagOfLoan [(0, 3, [1])] fpStUnpinned fpMsWritten :=
    unpin_restores_mirStateRel (u32MirCodec zcLayouts) 32 u32Embed u32Embed? u32Embed_embed?
      (u32_isIntoBytes zcLayouts) tagOfLoan stdValAlg 0 0 zcCodec (y := ⟨zcV1, by decide⟩)
      hWritten rfl rfl (.nat (by decide))
      (mirLocalsRel_of_localsRefine
        ⟨fun _ => ⟨_, rfl, .nat (by decide)⟩, fun _ => ⟨_, rfl, .nat (by decide)⟩,
         (fun h => nomatch h), fun _ => ⟨_, rfl, .ref rfl rfl rfl⟩, trivial⟩)
  exact ⟨hPinned, rfl, hWritten, rfl, hUnpinnedRel,
    unpin_eq_live_mir_decode (u32MirCodec zcLayouts) 32 u32Embed u32Embed? u32Embed_embed?
      (u32_isIntoBytes zcLayouts) tagOfLoan stdValAlg 0 0 zcCodec hWritten rfl,
    placeByteWindow?_u32Pair_fieldsTyped rfl fpMsPinned 3 []
      ⟨7, by decide⟩ ⟨zcV0, by decide⟩ rfl,
    placeByteWindow?_u32Pair_fieldsTyped rfl fpMsWritten 3 []
      ⟨7, by decide⟩ ⟨zcV1, by decide⟩ rfl⟩

/-- `PureLift` result: `(7, zcV1)`. -/
theorem fp_pureLift_eval :
    evalFnValue stdValAlg fpParams fpPlan (.use (.localSub 2 [])) =
      .ok ⟨.pair (.nat 7) (.nat zcV1), []⟩ := rfl

theorem fp_entry_rel :
    mirStateRel tagOfLoan []
      ⟨[⟨.nat 7, .unborrowed⟩, ⟨.nat zcV0, .unborrowed⟩], [], [], [], [], 0⟩ fpMs0 :=
  ⟨⟨trivial, trivial⟩,
   mirLocalsRel_of_localsRefine
     ⟨fun _ => ⟨_, rfl, .nat (by decide)⟩, fun _ => ⟨_, rfl, .nat (by decide)⟩, trivial⟩⟩

/-- **Test 3c (adequacy)**: the field-granular pin → field store → unpin
function converges on live MIR to a normal return refining `(7, zcV1)`. -/
theorem fp_sound :
    Anneal.MirFuelFree.MirWpConverges fieldPinBody fpMs0
      (LiftedMirPost tagOfLoan (fun out => out.ret = .pair (.nat 7) (.nat zcV1))) :=
  mir_pure_lift_sound_of_evalFuel tagOfLoan fieldPinBody [] fpParams fpPlan
    (.use (.localSub 2 [])) _ fpMs0 ⟨.pair (.nat 7) (.nat zcV1), []⟩
    (.aggregate 0 [.scalar ⟨7, 4⟩, .scalar ⟨zcV1, 4⟩]) _ 16 []
    ⟨_, rfl, fp_entry_rel⟩ fp_pureLift_eval rfl rfl
    (.pair (.nat (by decide)) (.nat (by decide))) rfl

set_option maxHeartbeats 400000 in
/-- **Test 3c (symbolic-input adequacy)**: for *every* symbolic first field
`a < 256 ^ 4`, `fieldPinBody` from `initMachineState fieldPinBody [.scalar ⟨a, 4⟩, .scalar ⟨zcV0, 4⟩]`
converges fuel-free to a normal return refining `(.pair (.nat a) (.nat zcV1))`. -/
theorem fp_symbolic_sound (a : Nat) (ha : a < 256 ^ 4) :
    Anneal.MirFuelFree.MirWpConverges fieldPinBody
      (initMachineState fieldPinBody [.scalar ⟨a, 4⟩, .scalar ⟨zcV0, 4⟩])
      (LiftedMirPost tagOfLoan (fun out => out.ret = .pair (.nat a) (.nat zcV1))) :=
  mir_pure_lift_sound_of_evalFuel tagOfLoan fieldPinBody []
    [⟨.byVal, .nat a⟩, ⟨.byVal, .nat zcV0⟩] fpPlan
    (.use (.localSub 2 [])) _
    (initMachineState fieldPinBody [.scalar ⟨a, 4⟩, .scalar ⟨zcV0, 4⟩])
    ⟨.pair (.nat a) (.nat zcV1), []⟩
    (.aggregate 0 [.scalar ⟨a, 4⟩, .scalar ⟨zcV1, 4⟩]) _ 16 []
    ⟨_, rfl,
     ⟨⟨trivial, trivial⟩,
      mirLocalsRel_of_localsRefine
        ⟨fun _ => ⟨_, rfl, .nat ha⟩,
         fun _ => ⟨_, rfl, .nat (by decide)⟩, trivial⟩⟩⟩
    rfl rfl rfl (.pair (.nat ha) (.nat (by decide))) rfl

/-- **Whole-tuple `u32PairMirCodec` freeze / unpin bridge on live MIR**:
instantiating `spatialCodec_freeze_eq_placeByteWindow` and
`spatialCodec_unpin_iff_mir_decode` on `u32PairMirCodec zcLayouts 99 rfl` at the
whole tuple place `_3 []` of `fpMsPinned` and `fpMsWritten`. -/
theorem fp_whole_pair_mirTypedByteCodec_bridge :
    let mPair := u32PairMirCodec zcLayouts 99 rfl
    let cellsWr : List (CellVal StdVal) :=
      [.rawByte 7, .rawByte 0, .rawByte 0, .rawByte 0,
       .rawByte 0xAB, .rawByte 0x33, .rawByte 0x22, .rawByte 0x11]
    (placeByteWindow? zcLayouts (u32PairTy 99) fpMsPinned 3 [] =
      some (mPair.codec.encode (⟨7, by decide⟩, ⟨zcV0, by decide⟩)) ∧
     abstractBytesOfCells (u32PairSpatialCodec.encode (.pair (.nat 7) (.nat zcV0))) =
      some (mPair.codec.encode (⟨7, by decide⟩, ⟨zcV0, by decide⟩)) ∧
     Anneal.SepLogicLenses.TypedAt mPair.codec 0
      (⟨7, by decide⟩, ⟨zcV0, by decide⟩)
      (mPair.codec.encode (⟨7, by decide⟩, ⟨zcV0, by decide⟩))) ∧
    u32PairSpatialCodec.decode cellsWr = some (.pair (.nat 7) (.nat zcV1)) ∧
    decodeValueFromBytes defaultCodecFuel zcLayouts (u32PairTy 99)
      (mPair.codec.encode (⟨7, by decide⟩, ⟨zcV1, by decide⟩)) =
      some (.aggregate 0 [.scalar ⟨7, 4⟩, .scalar ⟨zcV1, 4⟩]) := by
  intro mPair cellsWr
  exact ⟨spatialCodec_freeze_eq_placeByteWindow mPair 64 u32PairEmbed u32PairEmbed?
      u32PairEmbed_embed? fpMsPinned 3 [] (.pair (.nat 7) (.nat zcV0))
      (⟨7, by decide⟩, ⟨zcV0, by decide⟩) rfl rfl,
    ((mPair.spatialCodec_unpin_iff_mir_decode 64 u32PairEmbed u32PairEmbed?
      u32PairEmbed_embed? cellsWr
      (mPair.codec.encode (⟨7, by decide⟩, ⟨zcV1, by decide⟩)) rfl rfl).2
      (⟨7, by decide⟩, ⟨zcV1, by decide⟩) rfl),
    rfl⟩

/-! ### Test 3e: Whole-Tuple Codec under the Body's Captured rustc Layout -/

/-- The whole-tuple codec at the body's own tuple type `pairTy` and layout
table, whose entry `1` is the captured `(u32, u32)` layout. -/
def fpPairCodec :
    MirTypedByteCodec zcLayouts pairTy
      ({v : Nat // v < 256 ^ 4} × {v : Nat // v < 256 ^ 4}) 8 :=
  u32PairLayoutMirCodec zcLayouts 1 u32PairRustcLayout [0, 1] rfl rfl rfl

/-- **Test 3e (captured-layout whole-tuple bridge on live MIR)**: at the
body's own layout table and tuple type `pairTy` (so the trusted encoder and
decoder take the `FieldsShape.arbitrary [0, 4]` offset-table branch rather than
the layout-less sequential fallback), the whole-tuple window of `_3` is
`u32PairExactLE.encode` before and after the live field store (`FieldsTyped`
at offsets `0` / `4`), freezing it yields that trusted window, and unpinning
the post-store cells is exactly the trusted decode of the live window. -/
theorem fp_whole_pair_rustc_layout_bridge :
    let cellsWr : List (CellVal StdVal) :=
      [.rawByte 7, .rawByte 0, .rawByte 0, .rawByte 0,
       .rawByte 0xAB, .rawByte 0x33, .rawByte 0x22, .rawByte 0x11]
    fieldPinBody.layouts = zcLayouts ∧
    LayoutTable.lookup zcLayouts pairTy.layoutIdx = some u32PairRustcLayout ∧
    (Exists fun bsPin =>
      placeByteWindow? zcLayouts pairTy fpMsPinned 3 [] = some bsPin ∧
      bsPin = u32PairExactLE.encode (⟨7, by decide⟩, ⟨zcV0, by decide⟩) ∧
      Anneal.SepLogicLenses.FieldsTyped u32ExactLE 0 u32ExactLE 4 bsPin) ∧
    (Exists fun bsWr =>
      placeByteWindow? zcLayouts pairTy fpMsWritten 3 [] = some bsWr ∧
      bsWr = u32PairExactLE.encode (⟨7, by decide⟩, ⟨zcV1, by decide⟩) ∧
      Anneal.SepLogicLenses.FieldsTyped u32ExactLE 0 u32ExactLE 4 bsWr) ∧
    abstractBytesOfCells (u32PairSpatialCodec.encode (.pair (.nat 7) (.nat zcV0))) =
      placeByteWindow? zcLayouts pairTy fpMsPinned 3 [] ∧
    u32PairSpatialCodec.decode cellsWr = some (.pair (.nat 7) (.nat zcV1)) ∧
    decodeValueFromBytes defaultCodecFuel zcLayouts pairTy
      (u32PairExactLE.encode (⟨7, by decide⟩, ⟨zcV1, by decide⟩)) =
      some (.aggregate 0 [.scalar ⟨7, 4⟩, .scalar ⟨zcV1, 4⟩]) := by
  intro cellsWr
  have hFreeze := spatialCodec_freeze_eq_placeByteWindow fpPairCodec 64 u32PairEmbed
    u32PairEmbed? u32PairEmbed_embed? fpMsPinned 3 [] (.pair (.nat 7) (.nat zcV0))
    (⟨7, by decide⟩, ⟨zcV0, by decide⟩) rfl rfl
  exact ⟨rfl, rfl,
    placeByteWindow?_u32PairLayout_fieldsTyped (idx := 1) rfl rfl rfl fpMsPinned 3 []
      ⟨7, by decide⟩ ⟨zcV0, by decide⟩ rfl,
    placeByteWindow?_u32PairLayout_fieldsTyped (idx := 1) rfl rfl rfl fpMsWritten 3 []
      ⟨7, by decide⟩ ⟨zcV1, by decide⟩ rfl,
    hFreeze.2.1.trans hFreeze.1.symm,
    ((fpPairCodec.spatialCodec_unpin_iff_mir_decode 64 u32PairEmbed u32PairEmbed?
      u32PairEmbed_embed? cellsWr
      (fpPairCodec.codec.encode (⟨7, by decide⟩, ⟨zcV1, by decide⟩)) rfl rfl).2
      (⟨7, by decide⟩, ⟨zcV1, by decide⟩) rfl),
    fpPairCodec.decode_eq_map _⟩

/-- A reordered layout for the same tuple (`FieldsShape.arbitrary [4, 0]`). -/
def u32PairSwappedLayout : TypeLayout :=
  { u32PairRustcLayout with fields := .arbitrary [⟨4⟩, ⟨0⟩] [1, 0] }

def swappedLayouts : LayoutTable :=
  { fixtureLayouts with
    entries :=
      Anneal.PureMirExec.pureAdtMultiBlockBody.layouts.entries ++ [u32PairSwappedLayout] }

/-- **Layout falsification canary**: the offset hypothesis of
`u32PairLayoutMirCodec` is load-bearing. Under a reordered layout the trusted
encoder places field `1` first, so the live window of `_3` is the *swapped*
encoding, the in-order encoding decodes to the swapped pair, and an
all-`.uninit` or 4-byte window fails the trusted exact-size / initialization
checks under the captured layout. -/
theorem pair_layout_canaries :
    placeByteWindow? swappedLayouts pairTy fpMsPinned 3 [] =
      some (u32PairExactLE.encode (⟨zcV0, by decide⟩, ⟨7, by decide⟩)) ∧
    decodeValueFromBytes defaultCodecFuel swappedLayouts pairTy
      (u32PairExactLE.encode (⟨7, by decide⟩, ⟨zcV0, by decide⟩)) =
      some (.aggregate 0 [.scalar ⟨zcV0, 4⟩, .scalar ⟨7, 4⟩]) ∧
    decodeValueFromBytes defaultCodecFuel zcLayouts pairTy (replicateUninitBytes 8) = none ∧
    decodeValueFromBytes defaultCodecFuel zcLayouts pairTy
      (u32ExactLE.encode ⟨7, by decide⟩) = none :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The live whole-tuple windows of `_3` under the captured and the reordered
layouts differ. -/
theorem swapped_layout_window_ne :
    placeByteWindow? swappedLayouts pairTy fpMsPinned 3 [] ≠
      placeByteWindow? zcLayouts pairTy fpMsPinned 3 [] := by
  have hIn : placeByteWindow? zcLayouts pairTy fpMsPinned 3 [] =
      some (u32PairExactLE.encode (⟨7, by decide⟩, ⟨zcV0, by decide⟩)) := rfl
  rw [pair_layout_canaries.1, hIn]
  intro h
  have h2 := congrArg (fun o => o.bind u32PairExactLE.decode) h
  simp only [Option.bind_some, Anneal.SepLogicLenses.ByteLensCodec.decode_encode,
    Option.some.injEq, Prod.mk.injEq, Subtype.mk.injEq] at h2
  exact absurd h2.1 (by decide)

/-- **`FromBytes` and `IntoBytes` for `(u32, u32)` across unindexed, captured
in-order (`[0, 4]`), and reordered (`[4, 0]`) rustc layouts**. -/
theorem u32Pair_bitValidity_across_layouts :
    Anneal.BitValidity.IsFromBytes zcLayouts (u32PairTy 99) ∧
    Anneal.BitValidity.IsIntoBytes zcLayouts (u32PairTy 99) ∧
    Anneal.BitValidity.IsFromBytes zcLayouts pairTy ∧
    Anneal.BitValidity.IsIntoBytes zcLayouts pairTy ∧
    Anneal.BitValidity.IsFromBytes swappedLayouts pairTy ∧
    Anneal.BitValidity.IsIntoBytes swappedLayouts pairTy ∧
    Anneal.SepLogicLenses.FieldsTyped u32ExactLE 4 u32ExactLE 0
      (u32PairReorderedExactLE.encode (⟨7, by decide⟩, ⟨zcV0, by decide⟩)) :=
  ⟨u32Pair_isFromBytes rfl,
   u32Pair_isIntoBytes rfl,
   u32PairLayout_isFromBytes (l := u32PairRustcLayout) (mem := [0, 1]) rfl rfl rfl,
   u32PairLayout_isIntoBytes (l := u32PairRustcLayout) (mem := [0, 1]) rfl rfl rfl,
   u32PairReorderedLayout_isFromBytes (l := u32PairSwappedLayout) (mem := [1, 0]) rfl rfl rfl,
   u32PairReorderedLayout_isIntoBytes (l := u32PairSwappedLayout) (mem := [1, 0]) rfl rfl rfl,
   (u32PairReorderedExactLE_encode_fieldsTyped ⟨7, by decide⟩ ⟨zcV0, by decide⟩).1⟩

/-- rustc's `tcx.layout_of((u8, u32))` with 3 alignment-padding bytes `[1..4)`:
size `8`, align `4`, and `FieldsShape.arbitrary` offsets `[0, 4]`. -/
def u8U32RustcLayout : TypeLayout :=
  { size := ⟨8⟩, align := ⟨4⟩,
    backendRepr :=
      .scalarPair (.initialized (.int 8 false) ⟨0, 255⟩)
        (.initialized (.int 32 false) ⟨0, 4294967295⟩),
    fields := .arbitrary [⟨0⟩, ⟨4⟩] [0, 1], variants := .single 0,
    isUninhabited := false }

def u8U32Layouts : LayoutTable :=
  { fixtureLayouts with
    entries :=
      Anneal.PureMirExec.pureAdtMultiBlockBody.layouts.entries ++ [u8U32RustcLayout] }

/-- **Heterogeneous padded `(u8, u32)` layout trichotomy**: under `u8U32RustcLayout`
(size `8`, offsets `[0, 4]`, 3 padding bytes at `[1..4)`):
1. `encodeValueToBytes` leaves bytes `1..3` as `.uninit`, and that padded buffer
   satisfies `FieldsTyped u8ExactLE 0 u32ExactLE 4`;
2. `decodeValueFromBytes` decodes `(u8, u32)` even when bytes `1..3` are `.uninit`;
3. `(u8, u32)` is `IsFromBytes` and `IsTryFromBytes`, but **not** `IsIntoBytes`
   (`¬ IsIntoBytes u8U32Layouts (u8U32Ty 1)`). -/
theorem u8U32_padded_layout_trichotomy :
    let padUninit : List AbstractByte := [.uninit, .uninit, .uninit]
    let bsEnc :=
      u8ExactLE.encode ⟨7, by decide⟩ ++ padUninit ++ u32ExactLE.encode ⟨zcV0, by decide⟩
    encodeValueToBytes defaultCodecFuel u8U32Layouts (u8U32Ty 1)
      (.aggregate 0 [.scalar ⟨7, 1⟩, .scalar ⟨zcV0, 4⟩]) = some bsEnc ∧
    Anneal.SepLogicLenses.FieldsTyped u8ExactLE 0 u32ExactLE 4 bsEnc ∧
    decodeValueFromBytes defaultCodecFuel u8U32Layouts (u8U32Ty 1) bsEnc =
      some (.aggregate 0 [.scalar ⟨7, 1⟩, .scalar ⟨zcV0, 4⟩]) ∧
    Anneal.BitValidity.IsFromBytes u8U32Layouts (u8U32Ty 1) ∧
    Anneal.BitValidity.IsTryFromBytes u8U32Layouts (u8U32Ty 1)
      (fun v => Exists fun (x : {v : Nat // v < 256 ^ 1}) =>
        Exists fun (y : {v : Nat // v < 256 ^ 4}) =>
          v = .aggregate 0 [.scalar ⟨x.val, 1⟩, .scalar ⟨y.val, 4⟩]) ∧
    ¬ Anneal.BitValidity.IsIntoBytes u8U32Layouts (u8U32Ty 1) := by
  intro padUninit bsEnc
  exact ⟨encodeValueToBytes_u8U32PaddedLayout
      (l := u8U32RustcLayout) (mem := [0, 1]) rfl rfl rfl ⟨7, by decide⟩ ⟨zcV0, by decide⟩,
    (u8U32Padded_encode_fieldsTyped ⟨7, by decide⟩ ⟨zcV0, by decide⟩ padUninit rfl).1,
    rfl,
    u8U32Padded_isFromBytes (l := u8U32RustcLayout) (mem := [0, 1]) rfl rfl rfl,
    u8U32Padded_isTryFromBytes (l := u8U32RustcLayout) (mem := [0, 1]) rfl rfl rfl,
    u8U32Padded_not_isIntoBytes (l := u8U32RustcLayout) (mem := [0, 1]) rfl rfl rfl⟩

/-! ### Test 3d: Hybrid Pin with an Active Unpinned Sibling Loan (General Frame Rules) -/

/-- `fn patch_with_sibling(a: u32, b: u32) -> (u32, u32) { let mut p = (a, b);
let x = &mut p.0; let q = &raw mut p.1; let r = q as *mut u8;
unsafe { *r = 0xAB }; *x = 9; p }`: the sibling loan `x` stays live across the
raw byte store into `p.1` and is used afterwards. -/
def sibPinBody : CapturedMir :=
  mkBody 2
    [decl .mut pairTy, decl .not u32Ty, decl .not u32Ty, decl .mut pairTy,
     decl .not refU32Ty, decl .not rawU32Ty, decl .not rawU8Ty]
    [mkBb
      [mkSt (.storageLive 3),
       mkSt (.assign (pl 3) (.aggregate .tuple [.copy (pl 1), .copy (pl 2)])),
       mkSt (.storageLive 4),
       mkSt (.assign (pl 4) (.ref (.mut false) (pl 3 [.field 0 u32Ty]))),
       mkSt (.storageLive 5),
       mkSt (.assign (pl 5) (.rawPtr .mut (pl 3 [.field 1 u32Ty]))),
       mkSt (.storageLive 6),
       mkSt (.assign (pl 6) (.cast .ptrToPtr (.copy (pl 5)) rawU8Ty)),
       mkSt (.assign (pl 6 [.deref]) (.use (u8C 0xAB))),
       mkSt (.storageDead 6),
       mkSt (.storageDead 5),
       mkSt (.assign (pl 4 [.deref]) (.use (u32C 9))),
       mkSt (.storageDead 4),
       mkSt (.assign (pl 0) (.use (.copy (pl 3)))),
       mkSt (.storageDead 3)]
      .return_]

def spMs0 : MachineState :=
  initMachineState sibPinBody [.scalar ⟨7, 4⟩, .scalar ⟨zcV0, 4⟩]

/-- Live state right before the store: tag `1` (`reserved`) roots the sibling
loan at `_3.0`, tag `2` (`unique`) roots the raw pointers at `_3.1`. -/
def spMsPinned : MachineState :=
  { frame :=
      { blockIdx := 0, stmtIdx := 8,
        locals :=
          [.uninit, .init (.scalar ⟨7, 4⟩), .init (.scalar ⟨zcV0, 4⟩),
           .init (.aggregate 0 [.scalar ⟨7, 4⟩, .scalar ⟨zcV0, 4⟩]),
           .init (.ptr ⟨1, 0⟩ 8), .init (.ptr ⟨2, 0⟩ 8), .init (.ptr ⟨2, 0⟩ 8)] }
    memory :=
      { spMs0.memory with
        borrows :=
          [{ tag := 2, targetLocal := 3, targetProjection := [.field 1 u32Ty],
             perm := .unique },
           { tag := 1, targetLocal := 3, targetProjection := [.field 0 u32Ty],
             perm := .reservedFrz false }]
        nextTag := 3 } }

/-- Live state right after the store `*r = 0xAB`. -/
def spMsWritten : MachineState :=
  { spMsPinned with
    frame :=
      { blockIdx := 0, stmtIdx := 9,
        locals :=
          [.uninit, .init (.scalar ⟨7, 4⟩), .init (.scalar ⟨zcV0, 4⟩),
           .init (.aggregate 0 [.scalar ⟨7, 4⟩, .scalar ⟨zcV1, 4⟩]),
           .init (.ptr ⟨1, 0⟩ 8), .init (.ptr ⟨2, 0⟩ 8), .init (.ptr ⟨2, 0⟩ 8)] } }

theorem sp_pinned_path :
    StepPath (Anneal.PureMirExec.mirStep sibPinBody) spMs0 8 spMsPinned :=
  stepPath_of_runSilentSteps rfl

theorem sp_store_step :
    Anneal.PureMirExec.mirStep sibPinBody spMsPinned = .cont spMsWritten := rfl

def spParams : List (ParamInput StdVal) := [⟨.byVal, .nat 7⟩, ⟨.byVal, .nat zcV0⟩]

/-- `p = (a, b)`; `x = &mut p.0` (loan `0`); `q = &mut p.1` (loan `1`); pin,
write, and unpin loan `1`; end it; `*x = 9`; end loan `0`; return `p`. -/
def spPlan : FlowPlan StdVal :=
  .seq (.act (.assign (.localSub 2 []) (.binary stdMkPair (.localSub 0 []) (.localSub 1 []))))
    (.seq (.act (.borrow 3 .mutBorrow (.localSub 2 [0])))
      (.seq (.act (.borrow 4 .mutBorrow (.localSub 2 [1])))
        (.seq (.act (.freezeSpatial 1 zcCodec))
          (.seq (.act (.mutateSpatial 0 0 zcCellsAfter))
            (.seq (.act (.reabsorbSpatial 1 zcCodec))
              (.seq (.act (.endLoan 1))
                (.seq (.act (.assign (.derefSub 3 []) (.constVal (.nat 9))))
                  (.act (.endLoan 0)))))))))

/-- `PureLift` state after both sibling loans are taken. -/
def spStBorrowed : SymState StdVal :=
  ⟨[⟨.nat 7, .unborrowed⟩, ⟨.nat zcV0, .unborrowed⟩,
    ⟨.pair (.nat 7) (.nat zcV0), .split [([0], .mutLocked 0), ([1], .mutLocked 1)]⟩,
    ⟨.refVal 0 [], .unborrowed⟩, ⟨.refVal 1 [], .unborrowed⟩],
   [⟨0, .activeMut, ⟨.nat 7, .unborrowed⟩, .direct (.localReg 2) [0]⟩,
    ⟨1, .activeMut, ⟨.nat zcV0, .unborrowed⟩, .direct (.localReg 2) [1]⟩],
   [], [], [], 0⟩

theorem sp_borrowed_eval :
    evalPlan stdValAlg
        (.seq (.act (.assign (.localSub 2 [])
            (.binary stdMkPair (.localSub 0 []) (.localSub 1 []))))
          (.seq (.act (.borrow 3 .mutBorrow (.localSub 2 [0])))
            (.act (.borrow 4 .mutBorrow (.localSub 2 [1])))))
        ⟨[⟨.nat 7, .unborrowed⟩, ⟨.nat zcV0, .unborrowed⟩], [], [], [], [], 0⟩ =
      .ok (.continuing spStBorrowed) := rfl

def spStPinned : SymState StdVal :=
  match freezeToSpatialInState stdValAlg 1 zcCodec spStBorrowed with
  | .ok st => st
  | .fail => spStBorrowed

def spStWritten : SymState StdVal :=
  match mutateSpatialInState 0 0 zcCellsAfter spStPinned with
  | .ok st => st
  | .fail => spStPinned

def spStUnpinned : SymState StdVal :=
  match unpinFromSpatialInState stdValAlg 1 zcCodec spStWritten with
  | .ok st => st
  | .fail => spStWritten

/-- Both sibling loans are realized on the live machine before the pin. -/
theorem sp_borrowed_rel :
    mirStateRel tagOfLoan [(0, 3, [0]), (1, 3, [1])] spStBorrowed spMsPinned :=
  ⟨⟨⟨⟨Or.inr rfl, trivial⟩, ⟨trivial, trivial⟩⟩,
    ⟨⟨rfl, ⟨_, rfl, .nat (by decide)⟩, ⟨_, rfl, rfl, rfl, rfl⟩⟩,
     ⟨⟨rfl, ⟨_, rfl, .nat (by decide)⟩, ⟨_, rfl, rfl, rfl, rfl⟩⟩, trivial⟩⟩⟩,
   mirLocalsRel_of_localsRefine
     ⟨fun _ => ⟨_, rfl, .nat (by decide)⟩, fun _ => ⟨_, rfl, .nat (by decide)⟩,
      (fun h => nomatch h), fun _ => ⟨_, rfl, .ref rfl rfl rfl⟩,
      fun _ => ⟨_, rfl, .ref rfl rfl rfl⟩, trivial⟩⟩

/-- The sibling binding alone (a sub-relation of `sp_borrowed_rel`). -/
theorem sp_sibling_rel :
    spatialBindingsHold (mirSpatialModel tagOfLoan) [(0, 3, [0])] spStBorrowed spMsPinned :=
  ⟨⟨trivial, trivial⟩, ⟨⟨rfl, ⟨_, rfl, .nat (by decide)⟩, ⟨_, rfl, rfl, rfl, rfl⟩⟩, trivial⟩⟩

/-- **Hybrid pin with an active unpinned sibling, over live MIR, by the general
frame rules**:
1. freezing loan `1` materializes the live window of `_3.1`
   (`freeze_spatialPinnedBlockHolds`) while loan `0`'s binding to `_3.0`
   survives (`freeze_preserves_bindings`);
2. the spatial mutation plus the live raw store keep the pin relation
   (`mutate_spatialPinnedBlockHolds`) and loan `0`'s binding, since the store
   leaves `_3.0` and the Tree Borrows table unchanged
   (`mutate_preserves_bindings`);
3. unpinning loan `1` restores the full two-loan relation
   (`unpin_restores_mirStateRel_frame`). -/
theorem sp_pin_lifecycle_with_sibling :
    (spatialPinnedBlockHolds tagOfLoan zcLayouts u32Ty 1 0 zcCodec 3 [1] spStPinned spMsPinned ∧
      spatialBindingsHold (mirSpatialModel tagOfLoan) [(0, 3, [0])] spStPinned spMsPinned) ∧
    (spatialPinnedBlockHolds tagOfLoan zcLayouts u32Ty 1 0 zcCodec 3 [1] spStWritten
        spMsWritten ∧
      spatialBindingsHold (mirSpatialModel tagOfLoan) [(0, 3, [0])] spStWritten spMsWritten) ∧
    mirStateRel tagOfLoan [(1, 3, [1]), (0, 3, [0])] spStUnpinned spMsWritten ∧
    mirStateRel tagOfLoan [(0, 3, [0]), (1, 3, [1])] spStUnpinned spMsWritten := by
  have hFreeze : freezeToSpatialInState stdValAlg 1 zcCodec spStBorrowed = .ok spStPinned := rfl
  have hMut : mutateSpatialInState 0 0 zcCellsAfter spStPinned = .ok spStWritten := rfl
  have hUnpin : unpinFromSpatialInState stdValAlg 1 zcCodec spStWritten = .ok spStUnpinned := rfl
  have hMem : ∀ b, b ∈ [((0 : LoanId), (3 : Local), ([0] : SubPath))] →
      b = (0, 3, [0]) := by
    intro b hb
    cases hb with
    | head => rfl
    | tail _ h => exact nomatch h
  have hPinned :
      spatialPinnedBlockHolds tagOfLoan zcLayouts u32Ty 1 0 zcCodec 3 [1] spStPinned
        spMsPinned :=
    freeze_spatialPinnedBlockHolds (u32MirCodec zcLayouts) 32 u32Embed u32Embed? u32Embed_embed?
      tagOfLoan stdValAlg 1 (st := spStBorrowed) (x := ⟨zcV0, by decide⟩) hFreeze
      ⟨_, rfl, rfl⟩ rfl ⟨_, rfl, rfl, rfl, rfl⟩
  have hSibPinned :=
    freeze_preserves_bindings tagOfLoan [(0, 3, [0])] hFreeze
      (fun b hb => by rw [hMem b hb]; decide) sp_sibling_rel
  have hWritten :
      spatialPinnedBlockHolds tagOfLoan zcLayouts u32Ty 1 0 zcCodec 3 [1] spStWritten
        spMsWritten :=
    mutate_spatialPinnedBlockHolds hPinned hMut rfl rfl ⟨_, rfl, rfl, rfl, rfl⟩
  have hSibWritten :=
    mutate_preserves_bindings tagOfLoan [(0, 3, [0])] hMut (ms' := spMsWritten) rfl
      (fun b hb => by rw [hMem b hb]) hSibPinned
  have hLocals : mirLocalsRel tagOfLoan spStWritten spMsWritten :=
    mirLocalsRel_of_localsRefine
      ⟨fun _ => ⟨_, rfl, .nat (by decide)⟩, fun _ => ⟨_, rfl, .nat (by decide)⟩,
       (fun h => nomatch h), fun _ => ⟨_, rfl, .ref rfl rfl rfl⟩,
       fun _ => ⟨_, rfl, .ref rfl rfl rfl⟩, trivial⟩
  have hUnpinFrame :=
    unpin_restores_mirStateRel_frame (u32MirCodec zcLayouts) 32 u32Embed u32Embed?
      u32Embed_embed? (u32_isIntoBytes zcLayouts) tagOfLoan stdValAlg 1 0 zcCodec
      (y := ⟨zcV1, by decide⟩) [(0, 3, [0])] hWritten hUnpin rfl (.nat (by decide)) hLocals
      hSibWritten (fun b hb => by rw [hMem b hb]; decide)
      (fun b hb => by
        rw [hMem b hb]
        exact mirSpatialModel_disjoint_siblings tagOfLoan 3 (by decide) [] [])
  exact ⟨⟨hPinned, hSibPinned⟩, ⟨hWritten, hSibWritten⟩,
    hUnpinFrame, mirStateRel_swap tagOfLoan (1, 3, [1]) (0, 3, [0]) [] hUnpinFrame⟩

/-- `PureLift` result: `(9, zcV1)`. -/
theorem sp_pureLift_eval :
    evalFnValue stdValAlg spParams spPlan (.use (.localSub 2 [])) =
      .ok ⟨.pair (.nat 9) (.nat zcV1), []⟩ := rfl

theorem sp_entry_rel :
    mirStateRel tagOfLoan []
      ⟨[⟨.nat 7, .unborrowed⟩, ⟨.nat zcV0, .unborrowed⟩], [], [], [], [], 0⟩ spMs0 :=
  ⟨⟨trivial, trivial⟩,
   mirLocalsRel_of_localsRefine
     ⟨fun _ => ⟨_, rfl, .nat (by decide)⟩, fun _ => ⟨_, rfl, .nat (by decide)⟩, trivial⟩⟩

/-- **Test 3d (adequacy)**: the hybrid pin with an active unpinned sibling loan
converges on live MIR to a normal return refining `(9, zcV1)`. -/
theorem sp_sound :
    Anneal.MirFuelFree.MirWpConverges sibPinBody spMs0
      (LiftedMirPost tagOfLoan (fun out => out.ret = .pair (.nat 9) (.nat zcV1))) :=
  mir_pure_lift_sound_of_evalFuel tagOfLoan sibPinBody [] spParams spPlan
    (.use (.localSub 2 [])) _ spMs0 ⟨.pair (.nat 9) (.nat zcV1), []⟩
    (.aggregate 0 [.scalar ⟨9, 4⟩, .scalar ⟨zcV1, 4⟩]) _ 24 []
    ⟨_, rfl, sp_entry_rel⟩ sp_pureLift_eval rfl rfl
    (.pair (.nat (by decide)) (.nat (by decide))) rfl

/-! ## Test 4: Negative Falsification Canaries -/

/-- `&mut p.0` followed by an overlapping `&mut p` while loan `0` is active. -/
def overlapWholePlan : FlowPlan StdVal :=
  .seq (.act (.assign (.localSub 2 []) (.binary stdMkPair (.localSub 0 []) (.localSub 1 []))))
    (.seq (.act (.borrow 3 .mutBorrow (.localSub 2 [0])))
      (.act (.borrow 4 .mutBorrow (.localSub 2 []))))

/-- Two conflicting `&mut p.0` loans. -/
def overlapDupPlan : FlowPlan StdVal :=
  .seq (.act (.assign (.localSub 2 []) (.binary stdMkPair (.localSub 0 []) (.localSub 1 []))))
    (.seq (.act (.borrow 3 .mutBorrow (.localSub 2 [0])))
      (.act (.borrow 4 .mutBorrow (.localSub 2 [0]))))

/-- **(a) Overlapping mutable borrows are rejected** by `PermTree` /
`LoanGraph`, and overlapping bindings are not disjoint in `mirSpatialModel`. -/
theorem overlap_rejected :
    evalFnValue stdValAlg siblingParams overlapWholePlan (.constVal .unit) = .fail ∧
    evalFnValue stdValAlg siblingParams overlapDupPlan (.constVal .unit) = .fail ∧
    ¬ spatialBindingsDisjoint (mirSpatialModel tagOfLoan) [(0, 3, [0]), (1, 3, [])] := by
  refine ⟨rfl, rfl, ?_⟩
  intro h
  rcases h.1.1 with hNe | hDisj
  · exact hNe rfl
  · exact nomatch hDisj

/-- `x = &mut p.0; y = &mut p; (*y).0 = 7; *x = 10`: the accesses that
`overlapWholePlan` would permit. -/
def overlapUseBody : CapturedMir :=
  mkBody 2
    [decl .mut pairTy, decl .not u32Ty, decl .not u32Ty, decl .mut pairTy,
     decl .not refU32Ty, decl .not refPairTy]
    [mkBb
      [mkSt (.storageLive 3),
       mkSt (.assign (pl 3) (.aggregate .tuple [.copy (pl 1), .copy (pl 2)])),
       mkSt (.storageLive 4),
       mkSt (.assign (pl 4) (.ref (.mut false) (pl 3 [.field 0 u32Ty]))),
       mkSt (.storageLive 5),
       mkSt (.assign (pl 5) (.ref (.mut false) (pl 3))),
       mkSt (.assign (pl 5 [.deref, .field 0 u32Ty]) (.use (u32C 7))),
       mkSt (.assign (pl 4 [.deref]) (.use (u32C 10))),
       mkSt (.assign (pl 0) (.use (.copy (pl 3))))]
      .return_]

/-- **(a') The rejected overlap is live Tree Borrows UB**: the write through
`y` disables `x`'s tag, so the write through `x` faults and the program never
converges. -/
theorem overlap_use_is_ub (Post : MirOutcome → Prop) :
    Anneal.PureMirExec.evalFuel (Anneal.PureMirExec.mirStep overlapUseBody) 16
        (initMachineState overlapUseBody [.scalar ⟨7, 4⟩, .scalar ⟨9, 4⟩]) = .faulted ∧
    ¬ Anneal.PureMirExec.WpConverges (Anneal.PureMirExec.mirStep overlapUseBody)
        (initMachineState overlapUseBody [.scalar ⟨7, 4⟩, .scalar ⟨9, 4⟩]) Post :=
  ⟨rfl, Anneal.PureMirExec.not_wpConverges_of_faulted (k := 16) rfl⟩

/-- Post-`StorageLive(_2)` state of `zcBody`: `x` is live but uninitialized
(`MaybeUninit` storage). -/
def zcMsLiveUninit : MachineState :=
  { zcMs0 with
    frame :=
      { blockIdx := 0, stmtIdx := 1,
        locals := [.uninit, .init (.scalar ⟨zcV0, 4⟩), .uninit, .dead, .dead] } }

theorem zc_live_uninit_path :
    StepPath (Anneal.PureMirExec.mirStep zcBody) zcMs0 1 zcMsLiveUninit :=
  stepPath_of_runSilentSteps rfl

/-- **(b) Unpinning `.uninit` bytes fails**: the live-but-uninitialized `u32`
place has an all-`.uninit` window that the trusted decoder rejects and whose
spatial cells the codec rejects, and a `PureLift` unpin of a block holding an
`.uninit` cell fails. -/
theorem uninit_unpin_rejected :
    placeByteWindow? zcLayouts u32Ty zcMsLiveUninit 2 [] = some (replicateUninitBytes 4) ∧
    decodeValueFromBytes defaultCodecFuel zcLayouts u32Ty (replicateUninitBytes 4) = none ∧
    cellsOfAbstractBytes (Val := StdVal) (replicateUninitBytes 4) =
      some [.uninit, .uninit, .uninit, .uninit] ∧
    zcCodec.decode [.uninit, .uninit, .uninit, .uninit] = none ∧
    evalFnValue stdValAlg zcParams
        (zcPlanWith [.uninit, .rawByte 0x33, .rawByte 0x22, .rawByte 0x11])
        (.use (.localSub 1 [])) = .fail :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Freeze a `bool`, overwrite its byte with `cells`, unpin, and return it. -/
def boolPlanWith (cells : List (CellVal StdVal)) : FlowPlan StdVal :=
  .seq (.act (.assign (.localSub 1 []) (.use (.localSub 0 []))))
    (.seq (.act (.borrow 2 .mutBorrow (.localSub 1 [])))
      (.seq (.act (.freezeSpatial 0 (boolSpatialCodec zcLayouts)))
        (.seq (.act (.mutateSpatial 0 0 cells))
          (.seq (.act (.reabsorbSpatial 0 (boolSpatialCodec zcLayouts)))
            (.act (.endLoan 0))))))

/-- **(c) Unpinning an invalid `bool` bit pattern fails**: `0x02` is rejected
by the trusted `bool` decoder and by the spatial codec, so the `PureLift`
unpin fails, while the valid pattern `0x00` unpins to `false` (non-vacuity). -/
theorem invalid_bool_unpin_rejected :
    decodeValueFromBytes defaultCodecFuel zcLayouts boolTy [.init 2 none] = none ∧
    (boolSpatialCodec zcLayouts).decode [.rawByte 2] = none ∧
    evalFnValue stdValAlg [⟨.byVal, .bool true⟩] (boolPlanWith [.rawByte 2])
        (.use (.localSub 1 [])) = .fail ∧
    decodeValueFromBytes defaultCodecFuel zcLayouts boolTy [.init 0 none] =
      some (.scalar ⟨0, 1⟩) ∧
    evalFnValue stdValAlg [⟨.byVal, .bool true⟩] (boolPlanWith [.rawByte 0])
        (.use (.localSub 1 [])) = .ok ⟨.bool false, []⟩ :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- **(d) Refinement is not vacuous**: a `PureLift` natural is never refined by
a scalar holding a different value. -/
theorem refines_rejects_wrong_value :
    ¬ StdValRefines tagOfLoan (.nat 10) (.scalar ⟨11, 4⟩) := by
  intro h
  obtain ⟨sz, hEq, _⟩ := h.nat_inv (n := 10) rfl
  injection hEq with hEq
  injection hEq with h11
  exact absurd h11 (by decide)

/-- **(e) Pointer offset and sub-path hygiene in `StdValRefines.ref`**: a borrow
handle `.refVal lid path` never refines a pointer with non-zero `offsetBytes` or
a handle with non-empty `path`. -/
theorem refines_rejects_nonzero_ptr_offset_and_subpath :
    ¬ StdValRefines tagOfLoan (.refVal 0 []) (.ptr ⟨1, 4⟩ 8) ∧
    ¬ StdValRefines tagOfLoan (.refVal 0 [0]) (.ptr ⟨1, 0⟩ 8) := by
  refine ⟨?_, ?_⟩
  · intro h
    obtain ⟨_, p, _, hEq, _, hOff⟩ := h.ref_inv (lid := 0) (path := []) rfl
    injection hEq with hPtr _
    subst hPtr
    exact absurd hOff (by decide)
  · intro h
    obtain ⟨hp, _⟩ := h.ref_inv (lid := 0) (path := [0]) rfl
    exact nomatch hp

/-- **(f) `tagOfLoan` is injective, so distinct loan handles never refine the
same runtime pointer**. -/
theorem tagOfLoan_injective : TagOfInjective tagOfLoan := by
  intro l1 l2 h
  exact Nat.add_right_cancel h

theorem tagOfLoan_disjoint_refs (mv : Value) :
    ¬ (StdValRefines tagOfLoan (.refVal 0 []) mv ∧
       StdValRefines tagOfLoan (.refVal 1 []) mv) := by
  rintro ⟨h0, h1⟩
  have hEq := (StdValRefines.ref_disjoint_of_injective tagOfLoan_injective h0 h1).1
  exact absurd hEq (by decide)

/-- **(g) Width-1 subdomain no-retyping canary (`boolSpatialCodec`)**: mutating a
frozen 1-byte `bool` block to a 1-cell `[.init (.nat 99)]` slice cannot retype
the `bool` loan to `.nat 99` via the subdomain fallback; `decode` returns `none`
and reabsorption fails. -/
theorem bool_retype_init_cell_rejected :
    (boolSpatialCodec zcLayouts).decode [.init (.nat 99)] = none ∧
    evalFnValue stdValAlg [⟨.byVal, .bool true⟩]
      (boolPlanWith [.init (.nat 99)]) (.use (.localSub 1 [])) = .fail :=
  ⟨rfl, rfl⟩

/-- **(h) The mid-pin relation pins the exact codec, not just its identifier**:
a codec sharing the pinned `u32` codec's identifier (`32`) but encoding and
decoding single value cells does not satisfy `spatialPinnedBlockHolds`
(codec identifiers alone cannot determine the decoder that
`unpinFromSpatialInState` will run). -/
theorem pinned_relation_rejects_colliding_codec :
    ¬ spatialPinnedBlockHolds tagOfLoan zcLayouts u32Ty 0 0
      { valueCellCodec with codecId := 32 } 2 [] zcStPinned zcMsPinned := by
  intro ⟨e, _, _, _, hFind, hPhase, _⟩
  injection hFind with he
  subst he
  obtain ⟨_, hC, _⟩ := hPhase
  have hEnc := congrArg (fun c : SpatialCodec StdVal => c.encode (.nat zcV0)) hC
  exact nomatch hEnc

/-- Freeze a `NonZeroU32` value, overwrite its 4 bytes with `cells`, unpin, and
return it. -/
def nonZeroU32PlanWith (cells : List (CellVal StdVal)) : FlowPlan StdVal :=
  .seq (.act (.assign (.localSub 1 []) (.use (.localSub 0 []))))
    (.seq (.act (.borrow 2 .mutBorrow (.localSub 1 [])))
      (.seq (.act (.freezeSpatial 0 nonZeroU32SpatialCodec))
        (.seq (.act (.mutateSpatial 0 0 cells))
          (.seq (.act (.reabsorbSpatial 0 nonZeroU32SpatialCodec))
            (.act (.endLoan 0))))))

/-- **(i) Unpinning `0` at a `NonZeroU32` niche codec fails**: all-zero bytes
`[0, 0, 0, 0]` violate the `0 < v` niche of `nonZeroU32ExactLE` /
`nonZeroU32SpatialCodec` and fail to unpin (`.fail`), while `[42, 0, 0, 0]`
unpins to `.nat 42` (non-vacuity). -/
theorem zero_nonZeroU32_unpin_rejected :
    nonZeroU32ExactLE.decode [.init 0 none, .init 0 none, .init 0 none, .init 0 none] = none ∧
    nonZeroU32SpatialCodec.decode [.rawByte 0, .rawByte 0, .rawByte 0, .rawByte 0] = none ∧
    evalFnValue stdValAlg [⟨.byVal, .nat 7⟩]
        (nonZeroU32PlanWith [.rawByte 0, .rawByte 0, .rawByte 0, .rawByte 0])
        (.use (.localSub 1 [])) = .fail ∧
    evalFnValue stdValAlg [⟨.byVal, .nat 7⟩]
        (nonZeroU32PlanWith [.rawByte 42, .rawByte 0, .rawByte 0, .rawByte 0])
        (.use (.localSub 1 [])) = .ok ⟨.nat 42, []⟩ :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- **(j) Wrong-width spatial mutations on a pinned block are rejected**:
instantiating `mutateSpatialInState_fail_of_length_ne` on `zc_freeze_general`. -/
theorem pinned_mutate_wrong_length_rejected :
    mutateSpatialInState 0 0 [.rawByte 1, .rawByte 2, .rawByte 3] zcStPinned = .fail ∧
    mutateSpatialInState 0 0
      [.rawByte 1, .rawByte 2, .rawByte 3, .rawByte 4, .rawByte 5] zcStPinned = .fail :=
  ⟨mutateSpatialInState_fail_of_length_ne rfl (u32_isIntoBytes zcLayouts)
      zc_freeze_general (by decide),
   mutateSpatialInState_fail_of_length_ne rfl (u32_isIntoBytes zcLayouts)
      zc_freeze_general (by decide)⟩

/-! ### Test 4c: Padded `(u8, u32)` Pin over Live MIR — Freeze Accepted, Unpin Refused -/

/-- `*mut (u8, u32)`. -/
def rawU8U32Ty : Ty := { kind := .rawPtr .mut (.tuple [.uint .u8, .uint .u32]), layoutIdx := 0 }

/-- `fn pin_padded(a: u8, b: u32) -> (u8, u32) { let mut p = (a, b);
let q = &raw mut p; p }` over the captured padded layout table `u8U32Layouts`
(`p : (u8, u32)` at layout entry `1`: size `8`, offsets `[0, 4]`, padding
`[1..4)`). -/
def paddedPinBody : CapturedMir :=
  { mkBody 2
      [decl .mut (u8U32Ty 1), decl .not u8Ty, decl .not u32Ty, decl .mut (u8U32Ty 1),
       decl .not rawU8U32Ty]
      [mkBb
        [mkSt (.storageLive 3),
         mkSt (.assign (pl 3) (.aggregate .tuple [.copy (pl 1), .copy (pl 2)])),
         mkSt (.storageLive 4),
         mkSt (.assign (pl 4) (.rawPtr .mut (pl 3))),
         mkSt (.storageDead 4),
         mkSt (.assign (pl 0) (.use (.copy (pl 3)))),
         mkSt (.storageDead 3)]
        .return_] with
    layouts := u8U32Layouts }

def pdMs0 : MachineState :=
  initMachineState paddedPinBody [.scalar ⟨7, 1⟩, .scalar ⟨zcV0, 4⟩]

/-- Live state right after `q = &raw mut p`: the `unique` tag `1` is rooted at
the whole padded place `_3`. -/
def pdMsPinned : MachineState :=
  { frame :=
      { blockIdx := 0, stmtIdx := 4,
        locals :=
          [.uninit, .init (.scalar ⟨7, 1⟩), .init (.scalar ⟨zcV0, 4⟩),
           .init (.aggregate 0 [.scalar ⟨7, 1⟩, .scalar ⟨zcV0, 4⟩]), .init (.ptr ⟨1, 0⟩ 8)] }
    memory :=
      { pdMs0.memory with
        borrows := [{ tag := 1, targetLocal := 3, targetProjection := [], perm := .unique }]
        nextTag := 2 } }

theorem pd_pinned_path :
    StepPath (Anneal.PureMirExec.mirStep paddedPinBody) pdMs0 4 pdMsPinned :=
  stepPath_of_runSilentSteps rfl

/-- `PureLift` state after `p = (a, b); q = &mut p` (loan `0` on the whole of `p`). -/
def pdStBorrowed : SymState StdVal :=
  ⟨[⟨.nat 7, .unborrowed⟩, ⟨.nat zcV0, .unborrowed⟩,
    ⟨.pair (.nat 7) (.nat zcV0), .mutLocked 0⟩, ⟨.refVal 0 [], .unborrowed⟩],
   [⟨0, .activeMut, ⟨.pair (.nat 7) (.nat zcV0), .unborrowed⟩, .direct (.localReg 2) []⟩],
   [], [], [], 0⟩

theorem pd_borrowed_eval :
    evalPlan stdValAlg
        (.seq (.act (.assign (.localSub 2 [])
            (.binary stdMkPair (.localSub 0 []) (.localSub 1 []))))
          (.act (.borrow 3 .mutBorrow (.localSub 2 []))))
        ⟨[⟨.nat 7, .unborrowed⟩, ⟨.nat zcV0, .unborrowed⟩], [], [], [], [], 0⟩ =
      .ok (.continuing pdStBorrowed) := rfl

/-- The padded whole-tuple codec at the body's own `(u8, u32)` type and layouts. -/
def pdCodec :
    MirTypedByteCodec u8U32Layouts (u8U32Ty 1)
      ({v : Nat // v < 256 ^ 1} × {v : Nat // v < 256 ^ 4}) 8 :=
  u8U32PaddedMirCodec u8U32Layouts 1 u8U32RustcLayout [0, 1] rfl rfl rfl

/-- `p = (a, b)`; `q = &mut p` (loan `0`); pin; unpin; end; return `p`. -/
def pdPlan : FlowPlan StdVal :=
  .seq (.act (.assign (.localSub 2 []) (.binary stdMkPair (.localSub 0 []) (.localSub 1 []))))
    (.seq (.act (.borrow 3 .mutBorrow (.localSub 2 [])))
      (.seq (.act (.freezeSpatial 0 u8U32PaddedSpatialCodec))
        (.seq (.act (.reabsorbSpatial 0 u8U32PaddedSpatialCodec))
          (.act (.endLoan 0)))))

/-- **(k) Padded aggregates cannot complete the `SpatialPin` lifecycle (live
MIR)**: at the padded `(u8, u32)` place `_3` of `paddedPinBody`, the loan is
realized on the live machine (a mutation-granting tag rooted at `_3`), but the
place's trusted window carries three `.uninit` padding bytes, and the
window-faithful codec's frozen cells are exactly that window. Hence:
1. freezing is refused (`u8U32Padded_freeze_refused`, from the live window);
2. even a block related to the live window by *any* codec can never be
   unpinned (`u8U32Padded_unpin_blocked`);
3. the lifted pin → unpin function fails in `PureLift`.
This is the `SpatialPin` face of `u8U32Padded_not_isIntoBytes`; contrast Test 3,
where the `IsIntoBytes` `u32` window pins and unpins. -/
theorem padded_pin_refused :
    placeByteWindow? u8U32Layouts (u8U32Ty 1) pdMsPinned 3 [] =
      some (u8ExactLE.encode ⟨7, by decide⟩ ++ [.uninit, .uninit, .uninit] ++
        u32ExactLE.encode ⟨zcV0, by decide⟩) ∧
    BorrowAt pdMsPinned (tagOfLoan 0) 3 [] mutGranting ∧
    abstractBytesOfCells (u8U32PaddedSpatialCodec.encode (.pair (.nat 7) (.nat zcV0))) =
      placeByteWindow? u8U32Layouts (u8U32Ty 1) pdMsPinned 3 [] ∧
    hasUninitCell (u8U32PaddedSpatialCodec.encode (.pair (.nat 7) (.nat zcV0))) = true ∧
    freezeToSpatialInState stdValAlg 0 u8U32PaddedSpatialCodec pdStBorrowed = .fail ∧
    (∀ (st : SymState StdVal) (ms : MachineState) (bid : BlockId) (c c' : SpatialCodec StdVal),
      spatialPinnedBlockHolds tagOfLoan u8U32Layouts (u8U32Ty 1) 0 bid c 3 [] st ms →
      unpinFromSpatialInState stdValAlg 0 c' st = .fail) ∧
    evalFnValue stdValAlg [⟨.byVal, .nat 7⟩, ⟨.byVal, .nat zcV0⟩] pdPlan
      (.use (.localSub 2 [])) = .fail := by
  have hFreeze := spatialCodec_freeze_eq_placeByteWindow pdCodec 40 u8U32Embed u8U32Embed?
    u8U32Embed_embed? pdMsPinned 3 [] (.pair (.nat 7) (.nat zcV0))
    (⟨7, by decide⟩, ⟨zcV0, by decide⟩) rfl rfl
  exact ⟨rfl, ⟨_, rfl, rfl, rfl, rfl⟩, hFreeze.2.1.trans hFreeze.1.symm, rfl,
    u8U32Padded_freeze_refused (layouts := u8U32Layouts) (idx := 1) (l := u8U32RustcLayout)
      (mem := [0, 1]) rfl rfl rfl stdValAlg 0 (ms := pdMsPinned) (lc := 3) (path := [])
      (x := (⟨7, by decide⟩, ⟨zcV0, by decide⟩)) ⟨_, rfl, rfl⟩ rfl,
    fun _ _ _ _ c' h =>
      u8U32Padded_unpin_blocked (layouts := u8U32Layouts) (idx := 1) (l := u8U32RustcLayout)
        (mem := [0, 1]) rfl rfl rfl h stdValAlg c',
    rfl⟩

end PureLiftV2026BridgeTests
