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
   on the live machine at `bb3`), and `mir_blockCfg_sound` concludes.
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
   [0, 4]`), with a reordered-layout falsification canary.
4. **Negative canaries**: overlapping `&mut` borrows are rejected by `PermTree`
   (and their conflicting accesses are Tree Borrows UB on live MIR); unpinning
   `.uninit` bytes or the invalid `bool` pattern `0x02` fails.

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
    (fun s ms ⟨hW, _, _, _, hBb, hSt, hMs⟩ => by
      cases s with
      | mk w bb st =>
        dsimp only at hW hBb hSt hMs
        have hwEq : w = (fun o => o) := funext hW
        subst hwEq
        subst hBb
        subst hSt
        subst hMs
        exact ⟨16, _, rfl, _, _, rfl,
          .pair (.nat (by decide)) (.nat (by decide)), rfl⟩)
    ⟨fun _ => rfl, rfl, rfl, sibling_entry_rel, rfl, rfl, rfl⟩

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
              [{ tag := 2, targetLocal := 3, targetProjection := [.field 1 u32Ty], perm := .disabled },
               { tag := 1, targetLocal := 3, targetProjection := [.field 0 u32Ty], perm := .disabled }]
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
      ⟨fun o => o, 0, dbSt0 c⟩ (· = dbOut c) := by
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
  intro s ms hR
  obtain ⟨hW, _, _, _, hExtra⟩ := hR
  cases s with
  | mk w bb st =>
    have hwEq : w = (fun o => o) := funext hW
    subst hwEq
    rcases hExtra with ⟨hBb, hSt, hMs⟩ | ⟨hBb, hSt, hMs⟩ | ⟨hBb, hSt, hMs⟩
    · subst hBb; subst hSt; subst hMs
      cases c
      · exact stepsTo_of_runMirToBlock_reached (rfl :
          Anneal.PureMirExec.runMirToBlock diamondBody 2 (diamondMs0 false) =
            .reached (dbMsArm false))
          ⟨fun _ => rfl, rfl, rfl, db_rel_arm false, Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)⟩
      · exact stepsTo_of_runMirToBlock_reached (rfl :
          Anneal.PureMirExec.runMirToBlock diamondBody 1 (diamondMs0 true) =
            .reached (dbMsArm true))
          ⟨fun _ => rfl, rfl, rfl, db_rel_arm true, Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)⟩
    · subst hSt; subst hMs
      cases c
      · subst hBb
        exact stepsTo_of_runMirToBlock_reached (rfl :
          Anneal.PureMirExec.runMirToBlock diamondBody 3 (dbMsArm false) =
            .reached (diamondMsJoin false))
          ⟨fun _ => rfl, rfl, rfl, db_rel_join false, Or.inr (Or.inr ⟨rfl, rfl, rfl⟩)⟩
      · subst hBb
        exact stepsTo_of_runMirToBlock_reached (rfl :
          Anneal.PureMirExec.runMirToBlock diamondBody 3 (dbMsArm true) =
            .reached (diamondMsJoin true))
          ⟨fun _ => rfl, rfl, rfl, db_rel_join true, Or.inr (Or.inr ⟨rfl, rfl, rfl⟩)⟩
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
    ⟨fun _ => rfl, rfl, rfl, ⟨⟨trivial, trivial⟩,
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

theorem lbBodyPlan_wf : WfPlan stdValAlg lbBodyPlan := fun _ => rfl

theorem lbBodyPlan_continuing :
    ∀ s f, evalPlan stdValAlg lbBodyPlan s = .ok f → Exists fun s' => f = .continuing s' :=
  evalPlan_seq_continuing stdValAlg (fun _ => rfl) (fun _ => rfl)
    (evalPlan_act_continuing stdValAlg _)
    (evalPlan_seq_continuing stdValAlg (fun _ => rfl) (fun _ => rfl)
      (evalPlan_act_continuing stdValAlg _)
      (evalPlan_seq_continuing stdValAlg (fun _ => rfl) (fun _ => rfl)
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
    ?_ ?_ (Or.inl ⟨rfl, rfl⟩) ?_ ⟨fun _ => rfl, rfl, rfl, hRel0, Or.inl ⟨rfl, rfl, rfl⟩⟩
  · intro bb st hInv
    rcases hInv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))
    · exact rfl
  · intro bb st hInv _ _ _ _ h
    rcases hInv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact nomatch h
  · intro s ms ⟨hW, _, _, _, hEx⟩
    cases s with
    | mk w bb st =>
      have hwEq : w = (fun o => o) := funext hW
      subst hwEq
      rcases hEx with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
      · exact stepsTo_of_runMirToBlock_reached
          (rfl : Anneal.PureMirExec.runMirToBlock loopBorrowBody 1 lbMs0 = .reached lbMsBody)
          ⟨fun _ => rfl, rfl, rfl, hRelBody, Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)⟩
      · exact stepsTo_of_runMirToBlock_reached
          (rfl : Anneal.PureMirExec.runMirToBlock loopBorrowBody 0 lbMsBody = .reached lbMsAfterIter)
          ⟨fun _ => rfl, rfl, rfl, hRelAfter, Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))⟩
      · exact stepsTo_of_runMirToBlock_reached
          (rfl : Anneal.PureMirExec.runMirToBlock loopBorrowBody 2 lbMsAfterIter = .reached lbMsExit)
          ⟨fun _ => rfl, rfl, rfl, hRelExit, Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩))⟩
      · exact ⟨8, _, rfl, _, _, rfl, .nat (by decide), rfl⟩

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

end PureLiftV2026BridgeTests
