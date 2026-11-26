-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import Anneal.CompilerQueryEnv.EnvAndLayoutBridges

/-!
# `Anneal.CompilerQueryEnv.DynDispatch`

End-to-end receiver-driven dynamic dispatch (`UnOp.vtableMethodLookup → abiCompatible →
OpaqueCalleeTable.lookup → stepBranchPruned`), demand-gated dynamic call steps
(`stepDynTerminator`, in lockstep with the trusted call / tail-call arms), the multi-site
`DynCallRegistry`, and certificate-driven dynamic-dispatch cone narrowing.
-/

namespace Anneal.CompilerQueryEnv

open Trusted.Effect (FailureKind Outcome)
open Trusted.ITree
open Trusted.Sequence
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Anneal.OpaqueCalleeTable

/-! ## End-to-end: `UnOp.vtableMethodLookup → abiCompatible → OpaqueCalleeTable.lookup → stepBranchPruned` -/

/-- `charon#1611` `UnOp.vtableMethodLookup traitRef slotIdx` with optional
supertrait vtable chain (`supertraitChain`). When `supertraitChain = []`, looks
up method `slotIdx` directly in `traitRef`'s vtable; when
`supertraitChain = [subTrait, ...]`, first walks supertrait vtable pointers
along `supertraitChain → traitRef` before looking up `slotIdx`.

`expectedTraitMethod?` is the trait-method `DefPath` that `charon#1611`'s
`UnOp::VTableMethodLookup` carries for the vtable field it reads. When present, the terminal
lookup demands that the slot be bound to that trait method (`slotBindingOk`), and slot/method
agreement holds by construction — so compiler-generated shims, whose impl path need not end
in the method's name, dispatch. When absent, dispatch falls back to the fail-closed
byte-level item-name check `implementsCalledMethod` (`slotMethodAgrees`). -/
structure VTableMethodLookupOp : Type where
  traitRef : TraitRef
  slotIdx : Nat
  supertraitChain : List TraitRef := []
  expectedTraitMethod? : Option DefPath := none
  deriving DecidableEq

/-- Unary operators of the lowered program: the trusted `UnOp` plus `charon#1611`'s
demand-time `vtableMethodLookup`. -/
inductive UnOpExt : Type where
  | base (op : UnOp)
  | vtableMethodLookup (op : VTableMethodLookupOp)
  deriving DecidableEq

/-- The initial demand-time compiler query a unary operator issues on a vtable
pointer (`none` for trusted base operators, which never consult the query
environment; `.vtableMethodLookup` when `supertraitChain = []`, and the first
`.vtableSupertraitLookup` hop when `supertraitChain` is non-empty). -/
def UnOpExt.query? : UnOpExt → ProvenancePtr → Option CompilerQuery
  | .base _, _ => none
  | .vtableMethodLookup op, vtablePtr =>
    match op.supertraitChain with
    | [] =>
      some (.vtableMethodLookup vtablePtr.allocId op.traitRef op.slotIdx op.expectedTraitMethod?)
    | curTrait :: rest =>
      some (.vtableSupertraitLookup vtablePtr.allocId curTrait (rest.headD op.traitRef))

/-- Walk a chain of `UnOp.vtableMethodLookup` supertrait vtable hops starting
at `vtId` before looking up method slot `slotIdx` on the final `traitRef`. Every
hop is one application of the `UnOp.vtableMethodLookup` operator to the current
vtable pointer: the query evaluated at each hop is exactly the one
`UnOpExt.query?` issues for the remaining chain (as in `charon#1611`, where each
supertrait hop and the final method read are separate `UnOp::VTableMethodLookup`
operations on the vtable pointer the previous one returned). The expected trait method is
checked at the terminal method read only. -/
def resolveVTableChain (env : CompilerQueryEnv) (traitRef : TraitRef) (slotIdx : Nat)
    (expectedTraitMethod? : Option DefPath) :
    List TraitRef → Nat → QueryResult (DefPath × List RigidTy)
  | [], vtId =>
    match (UnOpExt.vtableMethodLookup ⟨traitRef, slotIdx, [], expectedTraitMethod?⟩).query?
        ⟨vtId, 0⟩ with
    | none => .err .answerKindMismatch
    | some q =>
      match evalCompilerQuery env q with
      | .ok (.method p tys) => .ok (p, tys)
      | .ok _ => .err .answerKindMismatch
      | .err e => .err e
      | .unsupported m => .unsupported m
  | curTrait :: restChain, vtId =>
    match (UnOpExt.vtableMethodLookup
        ⟨traitRef, slotIdx, curTrait :: restChain, expectedTraitMethod?⟩).query? ⟨vtId, 0⟩ with
    | none => .err .answerKindMismatch
    | some q =>
      match evalCompilerQuery env q with
      | .ok (.supertraitVTable nextVtId) =>
        resolveVTableChain env traitRef slotIdx expectedTraitMethod? restChain nextVtId
      | .ok _ => .err .answerKindMismatch
      | .err e => .err e
      | .unsupported m => .unsupported m

/-- `resolveVTableChain` is monotone under `EnvExtends` for any supertrait chain. -/
theorem resolveVTableChain_mono {env₁ env₂ : CompilerQueryEnv} (h : EnvExtends env₁ env₂)
    (traitRef : TraitRef) (slotIdx : Nat) (expectedTraitMethod? : Option DefPath) :
    ∀ (chain : List TraitRef) (vtId : Nat),
      (∀ m, resolveVTableChain env₁ traitRef slotIdx expectedTraitMethod? chain vtId ≠
          .unsupported m) →
        resolveVTableChain env₂ traitRef slotIdx expectedTraitMethod? chain vtId =
          resolveVTableChain env₁ traitRef slotIdx expectedTraitMethod? chain vtId
  | [], vtId, hsup => by
    unfold resolveVTableChain at hsup ⊢
    simp only [UnOpExt.query?] at hsup ⊢
    generalize hq :
      CompilerQuery.vtableMethodLookup vtId traitRef slotIdx expectedTraitMethod? = q at hsup ⊢
    cases hv : evalCompilerQuery env₁ q with
    | unsupported m => exact absurd (by simp [hv]) (hsup m)
    | err e => rw [query_mono_schema h q (by simp [hv]), hv]
    | ok a =>
      rw [query_mono_schema h q (by simp [hv]), hv]
  | curTrait :: restChain, vtId, hsup => by
    unfold resolveVTableChain at hsup ⊢
    simp only [UnOpExt.query?] at hsup ⊢
    generalize hq :
      CompilerQuery.vtableSupertraitLookup vtId curTrait (restChain.headD traitRef) = q at hsup ⊢
    cases hv : evalCompilerQuery env₁ q with
    | unsupported m => exact absurd (by simp [hv]) (hsup m)
    | err e => rw [query_mono_schema h q (by simp [hv]), hv]
    | ok a =>
      rw [query_mono_schema h q (by simp [hv]), hv]
      rw [hv] at hsup
      cases a with
      | supertraitVTable nextVtId =>
        exact resolveVTableChain_mono h traitRef slotIdx expectedTraitMethod? restChain nextVtId hsup
      | _ => rfl

/-- A `dyn Trait` method call site, lowered as in `charon#1611`: the receiver's
vtable pointer (`PtrMetadata(recv)`) is held in local `vtableLocal` of the calling
frame and read *at call time*, so `UnOp.vtableMethodLookup lookupOp` is applied to
the runtime vtable pointer. Two receivers reaching the same call key dispatch to
their own `impl`s (`canary_dyn_two_receivers`). -/
structure DynCallSite : Type where
  /-- Local of the calling frame holding the receiver's vtable pointer. -/
  vtableLocal : Nat
  /-- The `UnOp.vtableMethodLookup` applied to it. -/
  lookupOp : VTableMethodLookupOp
  /-- Caller-side ABI of the trait method signature. -/
  callerAbi : FnAbi
  /-- CFI call-site function-pointer type, when CFI-instrumented. -/
  cfiCallSite : Option RigidTy
  /-- Call key `(defPath, typeArgs)` of the `dyn` call in the caller's terminator. -/
  dynKey : DefPath × List RigidTy
  /-- Optional `(callerDefPath, blockIdx)` scope pinning this site to a specific MIR basic-block
  terminator of a specific function (in every frame of that function). `none` scopes the site to
  the **root function** (every frame executing the verified body, any block): the site describes
  the verified body's own lowering, so it never reinterprets another function's unrelated
  `vtableLocal`; a callee's virtual call needs its own scoped site and otherwise fails closed as
  unregistered. Scoping also
  lets distinct SSA blocks call the same virtual method with different `vtableLocal` temporaries
  (`canary_dyn_scoped_ssa_and_cross_frame_registry`). -/
  callSiteLoc? : Option (DefPath × BasicBlockIdx) := none
  deriving DecidableEq

/-- Whether `site`'s scope matches the active frame at `s`: a scoped site matches its
`(callerDefPath, blockIdx)` in every frame of that function; an unscoped site matches every frame
executing the root body `body` (by definition path: the root frame before any call, after a
callee returns — when `activeCallee = some body` — and recursive invocations), never a frame of
another function. -/
def DynCallSite.matchesLoc (site : DynCallSite) (body : CapturedMir) (s : MachineState) : Bool :=
  match site.callSiteLoc? with
  | none => decide ((s.memory.activeCallee.getD body).defPath = body.defPath)
  | some loc => decide (((s.memory.activeCallee.getD body).defPath, s.frame.blockIdx) = loc)

/-- The receiver's runtime vtable pointer at `s`: local `site.vtableLocal` of the
active frame must hold an initialized pointer to the *start* of a *global* (non-stack-borrow)
allocation (`offsetBytes = 0` and `lookupBorrow s.memory.borrows p.tag = none`, matching
`Terminators.lean`'s `resolveCallTarget` provenance guard); otherwise the `dyn` call is UB.
In `MirSem`, stack borrows (`&local` / `&raw const local`) allocate Tree Borrows provenance tags
in `s.memory.borrows` inside the same `Nat` `allocId` domain as global/vtable allocation IDs
(`ProvenancePtr.tag p := p.allocId`), so omitting `lookupBorrow = none` would let a transmuted
stack pointer at offset `0` alias a global vtable (`canary_dyn_stack_borrow_vtable_is_ub`). -/
def DynCallSite.vtablePtr? (site : DynCallSite) (s : MachineState) : Option ProvenancePtr :=
  match get? s.frame.locals site.vtableLocal with
  | some (.init (.ptr p _)) =>
    if p.offsetBytes = 0 && (lookupBorrow s.memory.borrows p.tag).isNone then some p else none
  | _ => none

/-- A vtable pointer read by `DynCallSite.vtablePtr?` addresses the start of its allocation. -/
theorem DynCallSite.vtablePtr?_offset {site : DynCallSite} {s : MachineState}
    {vt : ProvenancePtr} (h : site.vtablePtr? s = some vt) : vt.offsetBytes = 0 := by
  unfold DynCallSite.vtablePtr? at h
  split at h
  · split at h
    · injection h with h
      subst h
      rename_i hc
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      exact hc.1
    · nomatch h
  · nomatch h

/-- A vtable pointer read by `DynCallSite.vtablePtr?` never carries a stack-borrow tag. -/
theorem DynCallSite.vtablePtr?_no_borrow {site : DynCallSite} {s : MachineState}
    {vt : ProvenancePtr} (h : site.vtablePtr? s = some vt) :
    lookupBorrow s.memory.borrows vt.tag = none := by
  unfold DynCallSite.vtablePtr? at h
  split at h
  · split at h
    · injection h with h
      subst h
      rename_i hc
      simp only [Bool.and_eq_true] at hc
      exact Option.isNone_iff_eq_none.mp hc.2
    · nomatch h
  · nomatch h

/-- The `dyn` trait of a call key: a virtual call `<dyn D as Trait>::method`
carries `dyn D` as its first generic argument (`none` for non-virtual keys). -/
def dynSelfTrait? (key : DefPath × List RigidTy) : Option DefPath :=
  match key.2 with
  | .dynamic d :: _ => some d
  | _ => none

/-- `lastPathSegmentAux prevColon seg bytes`: the last `::`-separated segment of the
UTF-8 bytes of a `DefPath` (`seg` is the current segment, reversed; `prevColon`
records a pending single `:`, byte `58`). Structural on `bytes`, so kernel- and
`decide`-evaluable on literals, like the trusted byte-wise `stringEq`. -/
def lastPathSegmentAux : Bool → List UInt8 → List UInt8 → List UInt8
  | prev, seg, [] => (if prev then (58 : UInt8) :: seg else seg).reverse
  | prev, seg, b :: rest =>
    if b.toNat = 58 then
      if prev then lastPathSegmentAux false [] rest else lastPathSegmentAux true seg rest
    else
      lastPathSegmentAux false (b :: if prev then (58 : UInt8) :: seg else seg) rest

/-- Last `::`-separated segment (the item name) of a `DefPath`. -/
def lastPathSegment (p : DefPath) : List UInt8 :=
  lastPathSegmentAux false [] p.toByteArray.data.toList

/-- The dispatched body implements the called trait method. Rust requires an impl
item to carry the name of the trait item it implements (and an inherited default
method *is* the trait item), so a vtable slot whose target's item name differs from
the called method's (or is empty) is never the right slot: the site's `slotIdx` does
not belong to the method in its call key. -/
def implementsCalledMethod (calledMethod target : DefPath) : Bool :=
  !(lastPathSegment calledMethod).isEmpty &&
    decide (lastPathSegment calledMethod = lastPathSegment target)

/-- Whether `calledMethod` is a method item of `traitDefPath` (`calledMethod =
traitDefPath ++ "::" ++ lastPathSegment calledMethod` with a non-empty method
segment). Without this check, a site for `<dyn Area as OtherTrait>::area` paired
with an `Area` vtable lookup passes the receiver-trait checks of `DynCallSite.wellFormed`
and `implementsCalledMethod` (because both end in `::area`!) and executes `Area::area`
for an `OtherTrait::area` call (`canary_dyn_wrong_trait_prefix_fails_closed`). -/
def methodMatchesTrait (calledMethod traitDefPath : DefPath) : Bool :=
  let seg := lastPathSegment calledMethod
  !seg.isEmpty &&
    decide (calledMethod.toByteArray.data.toList =
      traitDefPath.toByteArray.data.toList ++ [(58 : UInt8), (58 : UInt8)] ++ seg)

/-- The lookup's explicit trait-method binding, if any, names exactly the called method
`site.dynKey.1` (vacuously true when the lookup carries none). -/
def DynCallSite.expectedMethodMatches (site : DynCallSite) : Bool :=
  match site.lookupOp.expectedTraitMethod? with
  | some m => decide (m = site.dynKey.1)
  | none => true

/-- **Slot/method agreement** of a resolved vtable target path. The target path must carry a
non-empty item segment (`!(lastPathSegment target).isEmpty`). With an explicit trait-method
binding (`expectedTraitMethod? = some m`), the terminal `UnOp::VTableMethodLookup` has already
checked that the slot is bound to `m` (`slotBindingOk`), so agreement is `m = site.dynKey.1`
— independent of the target's impl item name, so compiler-generated shims dispatch. Without one,
the fail-closed byte-level item-name check `implementsCalledMethod` applies. -/
def slotMethodAgrees (site : DynCallSite) (target : DefPath) : Bool :=
  !(lastPathSegment target).isEmpty &&
    match site.lookupOp.expectedTraitMethod? with
    | some m => decide (m = site.dynKey.1)
    | none => implementsCalledMethod site.dynKey.1 target

/-- Without an explicit trait-method binding, slot/method agreement is the byte-level
item-name check. -/
theorem slotMethodAgrees_of_none {site : DynCallSite} (target : DefPath)
    (h : site.lookupOp.expectedTraitMethod? = none) :
    slotMethodAgrees site target = implementsCalledMethod site.dynKey.1 target := by
  simp only [slotMethodAgrees, h, implementsCalledMethod]
  by_cases heq : lastPathSegment site.dynKey.1 = lastPathSegment target <;> simp [heq]

/-- With an explicit trait-method binding naming the called method, slot/method agreement
holds for *every* non-empty-item target (including shims whose path does not end in the method
name). -/
theorem slotMethodAgrees_of_some {site : DynCallSite} (target : DefPath) {m : DefPath}
    (h : site.lookupOp.expectedTraitMethod? = some m) (hm : m = site.dynKey.1)
    (hne : (lastPathSegment target).isEmpty = false) :
    slotMethodAgrees site target = true := by
  simp [slotMethodAgrees, h, hm, hne]

/-- **Full vtable target validity**: the resolved `(defPath, typeArgs)` pair must be a concrete
implementation or concrete default-method instantiation (`(dynSelfTrait? target).isNone`, never
an uninstantiated `dyn` key that would fall through `stepBranchPruned` to an unlinked external
call!) and its path must satisfy `slotMethodAgrees`.

The `dyn` test is deliberately conservative: it also rejects a generic impl method instantiated
at a `dyn` type (e.g. `impl<T: ?Sized + Tr> Tr for Box<T>` at `T = dyn Tr`), since paths alone
cannot distinguish impl items from trait items; such sites fail closed (`unsupported`, a
completeness gap, never a soundness one; `canary_dyn_generic_impl_at_dyn_fails_closed`). -/
def vtableTargetAgrees (site : DynCallSite) (target : DefPath × List RigidTy) : Bool :=
  (dynSelfTrait? target).isNone && slotMethodAgrees site target.1

/-- A `dyn` call site is well formed when:
1. its call key is a virtual call whose receiver type `dyn D` names the trait of
   the *first* vtable the lookup reads (`d = firstTrait.defPath`),
2. the terminal `site.lookupOp.traitRef` and every supertrait hop in
   `site.lookupOp.supertraitChain` is a `dyn` vtable trait reference whose `Self`
   argument (`args.head?`) is `.dynamic tr.defPath` (rejecting non-`dyn` or mismatched
   `Self` arguments on intermediate or terminal vtable traits;
   `canary_dyn_terminal_trait_self_mismatch_fails_closed`),
3. the call key's full generic argument list `site.dynKey.2` equals
   `.dynamic d :: site.lookupOp.traitRef.args.tail` (`Self = dyn D` followed by
   the terminal trait's generic parameters, supporting generic supertraits
   `<dyn Sub as Conv<u32>>::conv` while rejecting mismatched generic parameters;
   `canary_dyn_trait_arg_mismatch_fails_closed`, `canary_dyn_generic_supertrait_chain`),
4. `site.dynKey.1` is a method of the terminal trait `site.lookupOp.traitRef.defPath`
   (`methodMatchesTrait site.dynKey.1 site.lookupOp.traitRef.defPath`;
   `canary_dyn_wrong_trait_prefix_fails_closed`), and
5. an explicit trait-method binding, if the lookup carries one, names exactly the called
   method (`expectedMethodMatches`). -/
def DynCallSite.wellFormed (site : DynCallSite) : Bool :=
  let firstTrait := site.lookupOp.supertraitChain.headD site.lookupOp.traitRef
  match dynSelfTrait? site.dynKey with
  | some d =>
    decide (d = firstTrait.defPath) &&
      (site.lookupOp.traitRef :: site.lookupOp.supertraitChain).all
        (fun tr => decide (tr.args.head? = some (.dynamic tr.defPath))) &&
      decide (site.dynKey.2 = .dynamic d :: site.lookupOp.traitRef.args.tail) &&
      methodMatchesTrait site.dynKey.1 site.lookupOp.traitRef.defPath &&
      site.expectedMethodMatches &&
      decide (site.callerAbi.conv ≠ .rustIntrinsic)
  | none => false

/-- Resolve a `dyn` call through the runtime vtable pointer `vtablePtr`:
`resolveVTableChain` (direct or supertrait-chained `UnOp.vtableMethodLookup`),
then `abiCompatible`. -/
def resolveDynTarget (env : CompilerQueryEnv) (site : DynCallSite) (vtablePtr : ProvenancePtr) :
    QueryResult (DefPath × List RigidTy) :=
  match resolveVTableChain env site.lookupOp.traitRef site.lookupOp.slotIdx
      site.lookupOp.expectedTraitMethod? site.lookupOp.supertraitChain vtablePtr.allocId with
  | .ok (p, tys) =>
    match evalCompilerQuery env (.abiCompatible site.callerAbi p site.cfiCallSite) with
    | .ok _ => .ok (p, tys)
    | .err e => .err e
    | .unsupported m => .unsupported m
  | .err e => .err e
  | .unsupported m => .unsupported m

/-- Resolver redirecting the `dyn` call key to the dispatched method in the opaque
table (every other key resolves through the table unchanged). -/
def redirectResolver (tbl : OpaqueCalleeTable) (dynKey target : DefPath × List RigidTy) :
    CalleeResolver :=
  fun callerLayouts p tys extra =>
    if (p, tys) = dynKey then tbl.lookup callerLayouts target.1 target.2 extra
    else tbl.lookup callerLayouts p tys extra

/-- `redirectResolver` at the redirected `dynKey` rewrites to `tbl.lookupKey` on `target`
without unfolding `tbl`. -/
theorem redirectResolver_apply_hit (tbl : OpaqueCalleeTable)
    (dynKey target : DefPath × List RigidTy) {k : CalleeKey}
    (hk : (k.defPath, k.typeArgs) = dynKey) :
    k.apply (redirectResolver tbl dynKey target) =
      tbl.lookupKey ⟨k.callerLayouts, target.1, target.2, k.extraTraitImpls⟩ := by
  simp only [CalleeKey.apply, redirectResolver, ite_eq_left_of_eq_true _ _ (eq_true hk),
    OpaqueCalleeTable.lookupKey_eq]

/-- `redirectResolver` away from `dynKey` rewrites to `tbl.lookupKey k` without unfolding `tbl`. -/
theorem redirectResolver_apply_ne (tbl : OpaqueCalleeTable)
    (dynKey target : DefPath × List RigidTy) {k : CalleeKey}
    (hk : (k.defPath, k.typeArgs) ≠ dynKey) :
    k.apply (redirectResolver tbl dynKey target) = tbl.lookupKey k := by
  simp only [CalleeKey.apply, redirectResolver, ite_eq_right_of_eq_false _ _ (eq_false hk),
    OpaqueCalleeTable.lookupKey_eq]

/-- Whether the active step at `s` demands `dynKey` (`(k.defPath, k.typeArgs) = dynKey`). -/
def demandsDynKey (dynKey : DefPath × List RigidTy) (body : CapturedMir) (s : MachineState) : Bool :=
  match demandedKey? body s with
  | some k => decide ((k.defPath, k.typeArgs) = dynKey)
  | none => false

/-- Whether the call / tail-call terminator `term` at `s` resolves as a *direct* (`FnDef`) call
(`target.isIndirect = false`), rather than an indirect `FnPtr` call through `s.memory.fnPtrs`. -/
def isDirectTerminatorCall (s : MachineState) (term : Terminator)
    (currentBody : CapturedMir) : Bool :=
  match term.kind with
  | .call func argOps _ _ _ =>
    match resolveCallTarget s func (length argOps) currentBody.localDecls currentBody.layouts with
    | .ok target _ => !target.isIndirect
    | _ => false
  | .tailCall func argOps =>
    match resolveCallTarget s func (length argOps) currentBody.localDecls currentBody.layouts with
    | .ok target _ => !target.isIndirect
    | _ => false
  | _ => false

/-- Whether the active step at `(body, s)` is a direct (`FnDef`) call terminator. Lowered
`charon#1611` virtual calls are always direct trait-method calls (`isIndirect = false`); gating
`DynCallSite` matching on `isDirectCallAt` prevents an indirect `FnPtr` call whose `FnPtrEntry`
carries a virtual key from hijacking a `DynCallSite` and reading an unrelated `vtableLocal`
(`canary_indirect_fnptr_virtual_key_not_hijacked`). -/
def isDirectCallAt (body : CapturedMir) (s : MachineState) : Bool :=
  match activeTerminator? body s with
  | some (term, cb) => isDirectTerminatorCall s term cb
  | none => false

/-- Callee-body compatibility check for a resolved dynamic dispatch target: enforces
`Terminators.lean`'s `checkCalleeTargetCompatible`, exact argument-count match against the
evaluated arguments, and ABI compatibility of the actual `CapturedMir` body `calleeBody.fnAbi`
against `site.callerAbi` (since `Terminators.lean` skips `checkCalleeTargetCompatible` when
`isIndirect = false` on direct-lowered `FnDef` virtual calls). -/
def dynCalleeBodyCompatible (site : DynCallSite) (callTarget : ResolvedCallTarget)
    (calleeBody : CapturedMir) (argCount : Nat) : Bool :=
  checkCalleeTargetCompatible callTarget calleeBody argCount &&
    decide (calleeBody.argCount = argCount) &&
    (fnAbiMismatch? site.callerAbi calleeBody.fnAbi).isNone

/-- Terminator step for a resolved dynamic call to `target = (implPath, implTypeArgs)`:
1. verifies `length argOps = site.callerAbi.args.length` and `!callTarget.isIndirect` (failing
   closed `.unsupported` if the site's `callerAbi` disagrees with the MIR call instruction's
   operand count or if the instruction is an indirect `FnPtr` call),
2. checks `dynCalleeBodyCompatible` on a `resolve` hit (faulting `.ub` if `tbl`'s `CapturedMir`
   body contradicts `site.callerAbi`), and
3. on a `resolve` miss (`none`), emits `MirStepNode.extCall` with the **resolved vtable target**
   `(target.1, target.2)` — never falling through to `isDirectExactDivTarget` or
   `evalDirectRustIntrinsic?` on the unredirected virtual key `site.dynKey` and never reporting
   the uninstantiated trait method in `MirCallReq`.

Arguments are evaluated with `evalOperandsWithBodyCast ... cb.localDecls s.memory.callStack`
(`OpaqueCast` operands), a linked tail callee is entered in `tailCalleeEntryMemory` (root
caller-referent relocation), and an unlinked external tail call resumes through
`resumeExternalTailCallWithAbi s.memory.rootUnwindCeiling (some site.callerAbi.canUnwind)`:
when `site.callerAbi.canUnwind = true`, this matches the trusted direct tail-call arm
(`externalTargetCanUnwind callTarget ... = some true`), and when `site.callerAbi.canUnwind = false`,
every ABI-compatible concrete callee is non-unwinding (`fnAbiMismatch?_eq_none_iff`) so an
external unwind faults `.ub` at every call-stack depth (matching linked `enterTailCalleeFrame`). -/
def stepDynTerminator (resolve : CalleeResolver) (site : DynCallSite)
    (target : DefPath × List RigidTy) (s : MachineState) (term : Terminator)
    (cb : CapturedMir) : MirStepNode :=
  match term.kind with
  | .call func argOps destination (.some targetBb) unwind =>
    if length argOps = site.callerAbi.args.length then
      match resolveCallTarget s func (length argOps) cb.localDecls cb.layouts with
      | .ub => MirStepNode.fail .ub
      | .unsupported => MirStepNode.unsupported
      | .ok callTarget localsAfterFunc =>
        if callTarget.isIndirect then
          MirStepNode.unsupported
        else
          match evalOperandsWithBodyCast localsAfterFunc argOps s.memory.borrows s.memory.globals
              cb.layouts s.memory.callerLocals cb.localDecls s.memory.callStack with
          | .ub => MirStepNode.fail .ub
          | .unsupported => MirStepNode.unsupported
          | .ok argVals locals' =>
            match resolve cb.layouts callTarget.defPath callTarget.typeArgs s.memory.traitImpls with
            | .some calleeBody =>
              if dynCalleeBodyCompatible site callTarget calleeBody (length argVals) then
                MirStepNode.step
                  (pushCalleeFrame s cb locals' destination targetBb calleeBody argVals unwind)
              else
                MirStepNode.fail .ub
            | .none =>
              MirStepNode.extCall
                { defPath := target.1, typeArgs := target.2, args := argVals, memory := s.memory }
                (resumeExternalCall s locals' destination targetBb unwind)
    else
      MirStepNode.unsupported
  | .call func argOps destination .none unwind =>
    if length argOps = site.callerAbi.args.length then
      match resolveCallTarget s func (length argOps) cb.localDecls cb.layouts with
      | .ub => MirStepNode.fail .ub
      | .unsupported => MirStepNode.unsupported
      | .ok callTarget localsAfterFunc =>
        if callTarget.isIndirect then
          MirStepNode.unsupported
        else
          match evalOperandsWithBodyCast localsAfterFunc argOps s.memory.borrows s.memory.globals
              cb.layouts s.memory.callerLocals cb.localDecls s.memory.callStack with
          | .ub => MirStepNode.fail .ub
          | .unsupported => MirStepNode.unsupported
          | .ok argVals locals' =>
            match resolve cb.layouts callTarget.defPath callTarget.typeArgs s.memory.traitImpls with
            | .some calleeBody =>
              if dynCalleeBodyCompatible site callTarget calleeBody (length argVals) then
                MirStepNode.step
                  (pushDivergingCalleeFrame s cb locals' destination unwind calleeBody argVals)
              else
                MirStepNode.fail .ub
            | .none =>
              MirStepNode.extCall
                { defPath := target.1, typeArgs := target.2, args := argVals, memory := s.memory }
                (resumeExternalDivergingCall s locals' unwind)
    else
      MirStepNode.unsupported
  | .tailCall func argOps =>
    if length argOps = site.callerAbi.args.length then
      match resolveCallTarget s func (length argOps) cb.localDecls cb.layouts with
      | .ub => MirStepNode.fail .ub
      | .unsupported => MirStepNode.unsupported
      | .ok callTarget localsAfterFunc =>
        if callTarget.isIndirect then
          MirStepNode.unsupported
        else
          match evalOperandsWithBodyCast localsAfterFunc argOps s.memory.borrows s.memory.globals
              cb.layouts s.memory.callerLocals cb.localDecls s.memory.callStack with
          | .ub => MirStepNode.fail .ub
          | .unsupported => MirStepNode.unsupported
          | .ok argVals _ =>
            let depth := length s.memory.callStack
            let nLocals := length s.frame.locals
            match hasFrameDeallocProtectorConflict s.memory.borrows s.memory.activeProtectors
                depth nLocals with
            | true => MirStepNode.fail .ub
            | false =>
              let memAfterTeardown : Memory :=
                { s.memory with borrows := disableFrameBorrows s.memory.borrows depth nLocals }
              match resolve cb.layouts callTarget.defPath callTarget.typeArgs
                  s.memory.traitImpls with
              | .some calleeBody =>
                if dynCalleeBodyCompatible site callTarget calleeBody (length argVals) then
                  MirStepNode.step
                    (enterTailCalleeFrame
                      (tailCalleeEntryMemory s.memory.callStack memAfterTeardown nLocals
                        (length (initLocals calleeBody argVals)))
                      calleeBody argVals)
                else
                  MirStepNode.fail .ub
              | .none =>
                MirStepNode.extCall
                  { defPath := target.1, typeArgs := target.2, args := argVals,
                    memory := memAfterTeardown }
                  (resumeExternalTailCallWithAbi s.memory.rootUnwindCeiling
                    (some site.callerAbi.canUnwind))
    else
      MirStepNode.unsupported
  | _ => MirStepNode.unsupported

/-- Target-redirected branch-pruned step for a resolved dynamic dispatch target `target`:
when `s` demands `site.dynKey`, verifies `site.matchesLoc body s` (failing closed `.unsupported`
outside `site`'s function/block scope so even eager `dynDispatchStep` never hijacks a foreign
callee frame or another SSA block) before executing `stepDynTerminator`; steps via
`stepBranchPruned tbl.lookup` on all other steps. -/
def stepDynPruned (tbl : OpaqueCalleeTable) (site : DynCallSite)
    (target : DefPath × List RigidTy) (body : CapturedMir) (s : MachineState) : MirStepNode :=
  if demandsDynKey site.dynKey body s then
    if site.matchesLoc body s then
      match activeTerminator? body s with
      | some (term, cb) =>
        stepDynTerminator (redirectResolver tbl site.dynKey target) site target s term cb
      | none => MirStepNode.unsupported
    else
      MirStepNode.unsupported
  else
    stepBranchPruned tbl.lookup body s

theorem stepDynTerminator_congr {r₁ r₂ : CalleeResolver} (site : DynCallSite)
    (target : DefPath × List RigidTy) (s : MachineState) (term : Terminator) (cb : CapturedMir)
    (h : ∀ k, terminatorKey? s term cb = some k → k.apply r₁ = k.apply r₂) :
    stepDynTerminator r₁ site target s term cb = stepDynTerminator r₂ site target s term cb := by
  obtain ⟨kind, span⟩ := term
  cases kind with
  | call func argOps destination tgt unwind =>
    by_cases har : length argOps = site.callerAbi.args.length
    · cases hrt : resolveCallTarget s func (length argOps) cb.localDecls cb.layouts with
      | ok callTarget locals =>
        cases hind : callTarget.isIndirect with
        | true =>
          cases tgt <;>
            simp only [stepDynTerminator, ite_eq_left_of_eq_true _ _ (eq_true har), hrt, hind,
              ite_true]
        | false =>
          have hk := h ⟨cb.layouts, callTarget.defPath, callTarget.typeArgs, s.memory.traitImpls⟩
            (by simp only [terminatorKey?, hrt])
          simp only [CalleeKey.apply] at hk
          cases tgt <;>
            simp only [stepDynTerminator, ite_eq_left_of_eq_true _ _ (eq_true har), hrt, hind,
              Bool.false_eq_true, ite_false, hk]
      | ub =>
        cases tgt <;> simp only [stepDynTerminator, ite_eq_left_of_eq_true _ _ (eq_true har), hrt]
      | unsupported =>
        cases tgt <;> simp only [stepDynTerminator, ite_eq_left_of_eq_true _ _ (eq_true har), hrt]
    · cases tgt <;> simp only [stepDynTerminator, ite_eq_right_of_eq_false _ _ (eq_false har)]
  | tailCall func argOps =>
    by_cases har : length argOps = site.callerAbi.args.length
    · cases hrt : resolveCallTarget s func (length argOps) cb.localDecls cb.layouts with
      | ok callTarget locals =>
        cases hind : callTarget.isIndirect with
        | true =>
          simp only [stepDynTerminator, ite_eq_left_of_eq_true _ _ (eq_true har), hrt, hind,
            ite_true]
        | false =>
          have hk := h ⟨cb.layouts, callTarget.defPath, callTarget.typeArgs, s.memory.traitImpls⟩
            (by simp only [terminatorKey?, hrt])
          simp only [CalleeKey.apply] at hk
          simp only [stepDynTerminator, ite_eq_left_of_eq_true _ _ (eq_true har), hrt, hind,
            Bool.false_eq_true, ite_false, hk]
      | ub => simp only [stepDynTerminator, ite_eq_left_of_eq_true _ _ (eq_true har), hrt]
      | unsupported => simp only [stepDynTerminator, ite_eq_left_of_eq_true _ _ (eq_true har), hrt]
    · simp only [stepDynTerminator, ite_eq_right_of_eq_false _ _ (eq_false har)]
  | _ => rfl

/-- `stepDynPruned` depends on `tbl` only through `redirectResolver` at `demandedKey? body s`. -/
theorem stepDynPruned_congr {narrowTbl fullTbl : OpaqueCalleeTable} (site : DynCallSite)
    (target : DefPath × List RigidTy) (body : CapturedMir) (s : MachineState)
    (h : ∀ k, demandedKey? body s = some k →
      k.apply (redirectResolver narrowTbl site.dynKey target) =
        k.apply (redirectResolver fullTbl site.dynKey target)) :
    stepDynPruned narrowTbl site target body s = stepDynPruned fullTbl site target body s := by
  unfold stepDynPruned
  cases hd : demandsDynKey site.dynKey body s with
  | true =>
    simp only [ite_true]
    cases hloc : site.matchesLoc body s with
    | false => rfl
    | true =>
      simp only [ite_true]
      cases hact : activeTerminator? body s with
      | none => rfl
      | some p =>
        rcases p with ⟨term, cb⟩
        exact stepDynTerminator_congr site target s term cb fun k hk =>
          h k (by simp [demandedKey?, hact, hk])
  | false =>
    simp only [Bool.false_eq_true, ite_false]
    apply stepBranchPruned_congr
    intro k hk
    have hne : (k.defPath, k.typeArgs) ≠ site.dynKey := by
      intro he
      simp [demandsDynKey, hk, he] at hd
    have hk' := h k hk
    simp only [CalleeKey.apply, redirectResolver, ite_eq_right_of_eq_false _ _ (eq_false hne)]
      at hk' ⊢
    exact hk'

theorem stepDynTerminator_frames (resolve : CalleeResolver) (site : DynCallSite)
    (target : DefPath × List RigidTy) (s : MachineState) (term : Terminator) (cb : CapturedMir) :
    FramesStep s (stepDynTerminator resolve site target s term cb) := by
  obtain ⟨kind, span⟩ := term
  cases kind with
  | call func argOps destination tgt unwind =>
    cases tgt <;>
    · dsimp only [stepDynTerminator]
      split
      · cases resolveCallTarget s func (length argOps) cb.localDecls cb.layouts with
        | ub => exact True.intro
        | unsupported => exact True.intro
        | ok callTarget locals =>
          dsimp only
          cases callTarget.isIndirect with
          | true => exact True.intro
          | false =>
            simp only [Bool.false_eq_true, ite_false]
            cases evalOperandsWithBodyCast locals argOps s.memory.borrows s.memory.globals cb.layouts
                s.memory.callerLocals cb.localDecls s.memory.callStack with
            | ub => exact True.intro
            | unsupported => exact True.intro
            | ok argVals locals' =>
              dsimp only
              cases resolve cb.layouts callTarget.defPath callTarget.typeArgs
                  s.memory.traitImpls with
              | none => exact True.intro
              | some calleeBody =>
                dsimp only
                split
                · exact ⟨rfl, rfl⟩
                · exact True.intro
      · exact True.intro
  | tailCall func argOps =>
    dsimp only [stepDynTerminator]
    split
    · cases resolveCallTarget s func (length argOps) cb.localDecls cb.layouts with
      | ub => exact True.intro
      | unsupported => exact True.intro
      | ok callTarget locals =>
        dsimp only
        cases callTarget.isIndirect with
        | true => exact True.intro
        | false =>
          simp only [Bool.false_eq_true, ite_false]
          cases evalOperandsWithBodyCast locals argOps s.memory.borrows s.memory.globals cb.layouts
              s.memory.callerLocals cb.localDecls s.memory.callStack with
          | ub => exact True.intro
          | unsupported => exact True.intro
          | ok argVals locals' =>
            dsimp only
            cases hasFrameDeallocProtectorConflict s.memory.borrows s.memory.activeProtectors
                (length s.memory.callStack) (length s.frame.locals) with
            | true => exact True.intro
            | false =>
              dsimp only
              cases resolve cb.layouts callTarget.defPath callTarget.typeArgs
                  s.memory.traitImpls with
              | none => exact True.intro
              | some calleeBody =>
                dsimp only
                split
                · exact ⟨tailCalleeEntryMemory_callees _ _ _ _,
                    tailCalleeEntryMemory_traitImpls _ _ _ _⟩
                · exact True.intro
    · exact True.intro
  | _ => exact True.intro

theorem stepDynPruned_frames (tbl : OpaqueCalleeTable) (site : DynCallSite)
    (target : DefPath × List RigidTy) (body : CapturedMir) (s : MachineState) :
    FramesStep s (stepDynPruned tbl site target body s) := by
  unfold stepDynPruned
  cases demandsDynKey site.dynKey body s with
  | true =>
    simp only [ite_true]
    cases site.matchesLoc body s with
    | false => exact True.intro
    | true =>
      simp only [ite_true]
      cases activeTerminator? body s with
      | none => exact True.intro
      | some p => exact stepDynTerminator_frames _ site target s p.1 p.2
  | false => exact stepBranchPruned_frames tbl.lookup body s

/-- **A successful dynamic call step is a direct (`!isIndirect`) trusted call step**: every `.step`
that `stepDynTerminator` takes — pushing the resolved callee's frame (returning or diverging
`.call`) or entering it in place (`.tailCall`) — is a direct (`FnDef`) call whose step equals the
resolver-parametric copy of the trusted terminator, `stepTerminatorWith`, under the same resolver.
The dynamic terminator only *adds* failure edges (operand-count mismatch against `site.callerAbi`,
indirect `FnPtr` rejection, linked callee-body ABI/arity mismatch) and names the vtable-resolved
target in an unlinked external call; it never takes a step the trusted semantics would not. -/
theorem stepTerminatorWith_of_stepDynTerminator_step {resolve : CalleeResolver}
    {site : DynCallSite} {target : DefPath × List RigidTy} {s s' : MachineState}
    {term : Terminator} {cb : CapturedMir} (prune : Bool)
    (h : stepDynTerminator resolve site target s term cb = MirStepNode.step s') :
    stepTerminatorWith prune resolve s term (some cb) = MirStepNode.step s' := by
  obtain ⟨kind, span⟩ := term
  cases kind with
  | call func argOps destination tgt unwind =>
    by_cases har : length argOps = site.callerAbi.args.length
    · cases hrt : resolveCallTarget s func (length argOps) cb.localDecls cb.layouts with
      | ub =>
        cases tgt <;>
          simp only [stepDynTerminator, ite_eq_left_of_eq_true _ _ (eq_true har), hrt] at h <;>
          simp [MirStepNode.fail, MirStepNode.step] at h
      | unsupported =>
        cases tgt <;>
          simp only [stepDynTerminator, ite_eq_left_of_eq_true _ _ (eq_true har), hrt] at h <;>
          simp [MirStepNode.unsupported, MirStepNode.fail, MirStepNode.step] at h
      | ok callTarget locals =>
        cases hind : callTarget.isIndirect with
        | true =>
          cases tgt <;>
            simp only [stepDynTerminator, ite_eq_left_of_eq_true _ _ (eq_true har), hrt, hind,
              ite_true] at h <;>
            simp [MirStepNode.unsupported, MirStepNode.fail, MirStepNode.step] at h
        | false =>
          cases hev : evalOperandsWithBodyCast locals argOps s.memory.borrows s.memory.globals cb.layouts
              s.memory.callerLocals cb.localDecls s.memory.callStack with
          | ub =>
            cases tgt <;>
              simp only [stepDynTerminator, ite_eq_left_of_eq_true _ _ (eq_true har), hrt, hind,
                Bool.false_eq_true, ite_false, hev] at h <;>
              simp [MirStepNode.fail, MirStepNode.step] at h
          | unsupported =>
            cases tgt <;>
              simp only [stepDynTerminator, ite_eq_left_of_eq_true _ _ (eq_true har), hrt, hind,
                Bool.false_eq_true, ite_false, hev] at h <;>
              simp [MirStepNode.unsupported, MirStepNode.fail, MirStepNode.step] at h
          | ok argVals locals' =>
            cases hres : resolve cb.layouts callTarget.defPath callTarget.typeArgs
                s.memory.traitImpls with
            | none =>
              cases tgt <;>
                simp only [stepDynTerminator, ite_eq_left_of_eq_true _ _ (eq_true har), hrt, hind,
                  Bool.false_eq_true, ite_false, hev, hres] at h <;>
                simp [MirStepNode.extCall, MirStepNode.step] at h
            | some calleeBody =>
              cases hcomp : dynCalleeBodyCompatible site callTarget calleeBody (length argVals) with
              | false =>
                cases tgt <;>
                  simp only [stepDynTerminator, ite_eq_left_of_eq_true _ _ (eq_true har), hrt,
                    hind, Bool.false_eq_true, ite_false, hev, hres, hcomp] at h <;>
                  simp [MirStepNode.fail, MirStepNode.step] at h
              | true =>
                have hchk : checkCalleeTargetCompatible callTarget calleeBody (length argVals) =
                    true := by
                  unfold dynCalleeBodyCompatible at hcomp
                  simp only [Bool.and_eq_true] at hcomp
                  exact hcomp.1.1
                cases tgt <;>
                  simp only [stepDynTerminator, ite_eq_left_of_eq_true _ _ (eq_true har), hrt,
                    hind, Bool.false_eq_true, ite_false, hev, hres, hcomp, ite_true] at h <;>
                  simp only [stepTerminatorWith, bodyLocalDeclsOf, hrt, hev, hres, hchk, h]
    · cases tgt <;>
        simp only [stepDynTerminator, ite_eq_right_of_eq_false _ _ (eq_false har)] at h <;>
        simp [MirStepNode.unsupported, MirStepNode.fail, MirStepNode.step] at h
  | tailCall func argOps =>
    by_cases har : length argOps = site.callerAbi.args.length
    · cases hrt : resolveCallTarget s func (length argOps) cb.localDecls cb.layouts with
      | ub =>
        simp only [stepDynTerminator, ite_eq_left_of_eq_true _ _ (eq_true har), hrt] at h
        simp [MirStepNode.fail, MirStepNode.step] at h
      | unsupported =>
        simp only [stepDynTerminator, ite_eq_left_of_eq_true _ _ (eq_true har), hrt] at h
        simp [MirStepNode.unsupported, MirStepNode.fail, MirStepNode.step] at h
      | ok callTarget locals =>
        cases hind : callTarget.isIndirect with
        | true =>
          simp only [stepDynTerminator, ite_eq_left_of_eq_true _ _ (eq_true har), hrt, hind,
            ite_true] at h
          simp [MirStepNode.unsupported, MirStepNode.fail, MirStepNode.step] at h
        | false =>
          cases hev : evalOperandsWithBodyCast locals argOps s.memory.borrows s.memory.globals cb.layouts
              s.memory.callerLocals cb.localDecls s.memory.callStack with
          | ub =>
            simp only [stepDynTerminator, ite_eq_left_of_eq_true _ _ (eq_true har), hrt, hind,
              Bool.false_eq_true, ite_false, hev] at h
            simp [MirStepNode.fail, MirStepNode.step] at h
          | unsupported =>
            simp only [stepDynTerminator, ite_eq_left_of_eq_true _ _ (eq_true har), hrt, hind,
              Bool.false_eq_true, ite_false, hev] at h
            simp [MirStepNode.unsupported, MirStepNode.fail, MirStepNode.step] at h
          | ok argVals locals' =>
            cases hpc : hasFrameDeallocProtectorConflict s.memory.borrows s.memory.activeProtectors
                (length s.memory.callStack) (length s.frame.locals) with
            | true =>
              simp only [stepDynTerminator, ite_eq_left_of_eq_true _ _ (eq_true har), hrt, hind,
                Bool.false_eq_true, ite_false, hev, hpc] at h
              simp [MirStepNode.fail, MirStepNode.step] at h
            | false =>
              cases hres : resolve cb.layouts callTarget.defPath callTarget.typeArgs
                  s.memory.traitImpls with
              | none =>
                simp only [stepDynTerminator, ite_eq_left_of_eq_true _ _ (eq_true har), hrt, hind,
                  Bool.false_eq_true, ite_false, hev, hpc, hres] at h
                simp [MirStepNode.extCall, MirStepNode.step] at h
              | some calleeBody =>
                cases hcomp : dynCalleeBodyCompatible site callTarget calleeBody (length argVals) with
                | false =>
                  simp only [stepDynTerminator, ite_eq_left_of_eq_true _ _ (eq_true har), hrt,
                    hind, Bool.false_eq_true, ite_false, hev, hpc, hres, hcomp] at h
                  simp [MirStepNode.fail, MirStepNode.step] at h
                | true =>
                  have hchk : checkCalleeTargetCompatible callTarget calleeBody (length argVals) =
                      true := by
                    unfold dynCalleeBodyCompatible at hcomp
                    simp only [Bool.and_eq_true] at hcomp
                    exact hcomp.1.1
                  simp only [stepDynTerminator, ite_eq_left_of_eq_true _ _ (eq_true har), hrt,
                    hind, Bool.false_eq_true, ite_false, hev, hpc, hres, hcomp, ite_true] at h
                  simp only [stepTerminatorWith, tailCallWith, bodyLocalDeclsOf, hrt, hev, hpc,
                    hres, hchk, h]
    · simp only [stepDynTerminator, ite_eq_right_of_eq_false _ _ (eq_false har)] at h
      simp [MirStepNode.unsupported, MirStepNode.fail, MirStepNode.step] at h
  | _ =>
    simp only [stepDynTerminator] at h
    simp [MirStepNode.unsupported, MirStepNode.fail, MirStepNode.step] at h

/-- Whenever `isDirectTerminatorCall s term cb = false` (a non-call terminator, an unresolvable
call target, or an indirect `FnPtr` call), `stepDynTerminator` faults (`.ub` or fail-closed
`.unsupported`) — never stepping or emitting an external call. -/
theorem stepDynTerminator_of_not_directCall (resolve : CalleeResolver) (site : DynCallSite)
    (target : DefPath × List RigidTy) (s : MachineState) (term : Terminator) (cb : CapturedMir)
    (hnd : isDirectTerminatorCall s term cb = false) :
    ∃ fk, viewStepNode (stepDynTerminator resolve site target s term cb) = .fault fk := by
  obtain ⟨kind, span⟩ := term
  cases kind with
  | call func argOps destination tgt unwind =>
    unfold isDirectTerminatorCall at hnd
    by_cases har : length argOps = site.callerAbi.args.length
    · cases hrt : resolveCallTarget s func (length argOps) cb.localDecls cb.layouts with
      | ub =>
        refine ⟨.ub, ?_⟩
        cases tgt <;>
          simp only [stepDynTerminator, ite_eq_left_of_eq_true _ _ (eq_true har), hrt] <;>
          rfl
      | unsupported =>
        refine ⟨.unsupported, ?_⟩
        cases tgt <;>
          simp only [stepDynTerminator, ite_eq_left_of_eq_true _ _ (eq_true har), hrt] <;>
          rfl
      | ok callTarget locals =>
        simp only [hrt, Bool.not_eq_false'] at hnd
        refine ⟨.unsupported, ?_⟩
        cases tgt <;>
          simp only [stepDynTerminator, ite_eq_left_of_eq_true _ _ (eq_true har), hrt, hnd,
            ite_true] <;>
          rfl
    · refine ⟨.unsupported, ?_⟩
      cases tgt <;>
        simp only [stepDynTerminator, ite_eq_right_of_eq_false _ _ (eq_false har)] <;>
        rfl
  | tailCall func argOps =>
    unfold isDirectTerminatorCall at hnd
    by_cases har : length argOps = site.callerAbi.args.length
    · cases hrt : resolveCallTarget s func (length argOps) cb.localDecls cb.layouts with
      | ub =>
        refine ⟨.ub, ?_⟩
        simp only [stepDynTerminator, ite_eq_left_of_eq_true _ _ (eq_true har), hrt]
        rfl
      | unsupported =>
        refine ⟨.unsupported, ?_⟩
        simp only [stepDynTerminator, ite_eq_left_of_eq_true _ _ (eq_true har), hrt]
        rfl
      | ok callTarget locals =>
        simp only [hrt, Bool.not_eq_false'] at hnd
        refine ⟨.unsupported, ?_⟩
        simp only [stepDynTerminator, ite_eq_left_of_eq_true _ _ (eq_true har), hrt, hnd, ite_true]
        rfl
    · refine ⟨.unsupported, ?_⟩
      simp only [stepDynTerminator, ite_eq_right_of_eq_false _ _ (eq_false har)]
      rfl
  | _ =>
    exact ⟨.unsupported, rfl⟩

/-- Every successful `.step` of `stepDynTerminator` is a direct (`!isIndirect`) call terminator. -/
theorem isDirectTerminatorCall_of_stepDynTerminator_step {resolve : CalleeResolver}
    {site : DynCallSite} {target : DefPath × List RigidTy} {s s' : MachineState}
    {term : Terminator} {cb : CapturedMir}
    (h : stepDynTerminator resolve site target s term cb = MirStepNode.step s') :
    isDirectTerminatorCall s term cb = true := by
  cases hd : isDirectTerminatorCall s term cb with
  | true => rfl
  | false =>
    obtain ⟨fk, hfk⟩ := stepDynTerminator_of_not_directCall resolve site target s term cb hd
    rw [h] at hfk
    simp [MirStepNode.step, viewStepNode] at hfk

/-- **Exhaustive `StepView` classification of `stepDynTerminator`** (unconditional, with no output
hypothesis): at *every* state and terminator, `stepDynTerminator` exclusively:
1. faults (`.fault fk`, i.e. fail-closed `.unsupported` or `.ub`),
2. emits an unlinked external call to the vtable-resolved `target = (req.defPath, req.typeArgs)`, or
3. takes a silent running step (`MirStepNode.step s'`) identical to the resolver-parametric trusted
   `stepTerminatorWith true resolve s term (some cb)`.

Unlike `stepTerminatorWith_of_stepDynTerminator_step` alone (which would hold vacuously if
`stepDynTerminator` fabricated `.ret out`, `.emitStep`, or `.tau (.halted out)`), this theorem rules
out every non-call outcome unconditionally. -/
theorem stepDynTerminator_view_spec (resolve : CalleeResolver) (site : DynCallSite)
    (target : DefPath × List RigidTy) (s : MachineState) (term : Terminator) (cb : CapturedMir) :
    (∃ fk, viewStepNode (stepDynTerminator resolve site target s term cb) = .fault fk) ∨
    (∃ req, viewStepNode (stepDynTerminator resolve site target s term cb) = .external req ∧
      req.defPath = target.1 ∧ req.typeArgs = target.2) ∨
    (∃ s', stepDynTerminator resolve site target s term cb = MirStepNode.step s' ∧
      stepTerminatorWith true resolve s term (some cb) = MirStepNode.step s') := by
  have h : stepDynTerminator resolve site target s term cb =
      stepDynTerminator resolve site target s term cb := rfl
  conv at h => rhs; unfold stepDynTerminator
  repeat' ((try dsimp only at h); split at h)
  all_goals
    try dsimp only at h
    first
    | exact Or.inl ⟨.ub, by rw [h]; rfl⟩
    | exact Or.inl ⟨.unsupported, by rw [h]; rfl⟩
    | exact Or.inr (Or.inl ⟨_, by rw [h]; rfl, rfl, rfl⟩)
    | exact Or.inr (Or.inr ⟨_, h, stepTerminatorWith_of_stepDynTerminator_step true h⟩)

/-- `stepDynTerminator` never produces a terminal `.ret out` node. -/
theorem stepDynTerminator_ne_ret (resolve : CalleeResolver) (site : DynCallSite)
    (target : DefPath × List RigidTy) (s : MachineState) (term : Terminator) (cb : CapturedMir)
    (out : MirOutcome) :
    stepDynTerminator resolve site target s term cb ≠ .ret out := by
  intro h
  rcases stepDynTerminator_view_spec resolve site target s term cb with
    ⟨fk, hv⟩ | ⟨req, hv, _, _⟩ | ⟨s', hs, _⟩
  · rw [h] at hv; nomatch hv
  · rw [h] at hv; nomatch hv
  · rw [h] at hs; nomatch hs

/-- `stepDynTerminator` never transitions directly to `.halted out`. -/
theorem stepDynTerminator_view_ne_halted (resolve : CalleeResolver) (site : DynCallSite)
    (target : DefPath × List RigidTy) (s : MachineState) (term : Terminator) (cb : CapturedMir)
    (obs : Option MirObs) (out : MirOutcome) :
    viewStepNode (stepDynTerminator resolve site target s term cb) ≠ .cont obs (.halted out) := by
  intro h
  rcases stepDynTerminator_view_spec resolve site target s term cb with
    ⟨fk, hv⟩ | ⟨req, hv, _, _⟩ | ⟨s', hs, _⟩
  · rw [h] at hv; nomatch hv
  · rw [h] at hv; nomatch hv
  · rw [hs] at h; simp [MirStepNode.step, viewStepNode] at h

/-- **Non-unwinding external dynamic tail-call soundness**: when `site.callerAbi.canUnwind = false`,
any unlinked external tail call emitted by `stepDynTerminator` faults `.ub` on `.panicked memAns`,
regardless of `s.memory.rootUnwindCeiling`, `s.memory.callStack`, or `memAns`. -/
theorem stepDynTerminator_tailCall_nounwind_ext_panic_ub {resolve : CalleeResolver}
    {site : DynCallSite} {target : DefPath × List RigidTy} {s : MachineState}
    {func : Operand} {argOps : List Operand} {span : String} {cb : CapturedMir}
    {req : MirCallReq} {k : MirCallAns → MirExecState}
    (hnu : site.callerAbi.canUnwind = false)
    (h : stepDynTerminator resolve site target s ⟨.tailCall func argOps, span⟩ cb =
      MirStepNode.extCall req k)
    (memAns : Memory) :
    k (.panicked memAns) = .faulted .ub := by
  unfold stepDynTerminator at h
  dsimp only at h
  repeat' ((try dsimp only at h); split at h)
  all_goals
    try (simp only [MirStepNode.fail, MirStepNode.unsupported, MirStepNode.step,
      MirStepNode.extCall] at h; cases h)
  simp [resumeExternalTailCallWithAbi, hnu]

/-- **Unified dynamic-dispatch step**: receiver vtable pointer (read from the
calling frame) `→ UnOp.vtableMethodLookup → abiCompatible →
OpaqueCalleeTable.lookup → stepDynPruned`. An ill-formed site fails closed
(`MirStepNode.unsupported`: a configuration error, never attributed to the program),
a receiver without a vtable pointer — or whose vtable pointer does not address the start
of a non-stack allocation (`DynCallSite.vtablePtr?`) — is UB, missing evidence fails closed, a CFI
type-id mismatch is the defined CFI trap (`abort`), and every other semantic error is
UB. A resolved slot that fails `vtableTargetAgrees` (either still carrying a `dyn`
receiver type or failing `slotMethodAgrees`) and a slot whose explicit binding names
another trait method (`.vtableSlotMethodMismatch`) are configuration errors and fail
closed.

`dynDispatchStep` is the dispatch step *at a demanded site*: the gated evaluators
(`dynDemandStep`, `dynRegistryStep`) apply it only when `demandsDynSite` holds (direct call, call
key, site scope). Applied eagerly elsewhere it still never dispatches out of scope or through an
indirect call — the redirected call re-checks scope and directness (`stepDynPruned`,
`stepDynTerminator`), so every successful step satisfies `demandsDynSite`
(`demandsDynSite_of_dynDispatchStep_step`) — but it reads and resolves the frame's `vtableLocal`
first, so a receiver-side outcome (UB on a missing pointer, the CFI trap) is reported before the
scope check (`canary_eager_vs_gated_out_of_scope`). -/
def dynDispatchStep (env : CompilerQueryEnv) (tbl : OpaqueCalleeTable) (site : DynCallSite)
    (body : CapturedMir) (s : MachineState) : MirStepNode :=
  if site.wellFormed then
    match site.vtablePtr? s with
    | none => MirStepNode.fail .ub
    | some vt =>
      match resolveDynTarget env site vt with
      | .ok target =>
        if vtableTargetAgrees site target then
          stepDynPruned tbl site target body s
        else MirStepNode.unsupported
      | .err .cfiTypeIdMismatch => MirStepNode.retOutcome .abort
      | .err (.vtableSlotMethodMismatch _) => MirStepNode.unsupported
      | .err _ => MirStepNode.fail .ub
      | .unsupported _ => MirStepNode.unsupported
  else MirStepNode.unsupported

/-- `resolveDynTarget` is monotone under `EnvExtends` on supported answers (for
both direct and supertrait-chained vtable lookups). -/
theorem resolveDynTarget_mono {env₁ env₂ : CompilerQueryEnv} (h : EnvExtends env₁ env₂)
    (site : DynCallSite) (vt : ProvenancePtr)
    (hsup : ∀ m, resolveDynTarget env₁ site vt ≠ .unsupported m) :
    resolveDynTarget env₂ site vt = resolveDynTarget env₁ site vt := by
  unfold resolveDynTarget at hsup ⊢
  cases hv : resolveVTableChain env₁ site.lookupOp.traitRef site.lookupOp.slotIdx
      site.lookupOp.expectedTraitMethod? site.lookupOp.supertraitChain vt.allocId with
  | unsupported m => exact absurd (by simp [hv]) (hsup m)
  | err e =>
    rw [resolveVTableChain_mono h _ _ _ _ _ (by simp [hv]), hv]
  | ok pt =>
    rcases pt with ⟨p, tys⟩
    rw [resolveVTableChain_mono h _ _ _ _ _ (by simp [hv]), hv]
    rw [hv] at hsup
    dsimp only at hsup ⊢
    cases hb : evalCompilerQuery env₁ (.abiCompatible site.callerAbi p site.cfiCallSite) with
    | unsupported m => exact absurd (by simp [hb]) (hsup m)
    | err e => rw [query_mono_schema h _ (by simp [hb]), hb]
    | ok b => rw [query_mono_schema h _ (by simp [hb]), hb]

/-- The dynamic-dispatch step on a resolved receiver is a target-redirected pruned step. -/
theorem dynDispatchStep_eq_of_resolved {env : CompilerQueryEnv} {tbl : OpaqueCalleeTable}
    {site : DynCallSite} {body : CapturedMir} {s : MachineState} {vt : ProvenancePtr}
    {target : DefPath × List RigidTy} (hwf : site.wellFormed = true)
    (hvt : site.vtablePtr? s = some vt)
    (h : resolveDynTarget env site vt = .ok target)
    (htarget : vtableTargetAgrees site target = true) :
    dynDispatchStep env tbl site body s =
      stepDynPruned tbl site target body s := by
  simp only [dynDispatchStep, hwf, ite_true, hvt, h, htarget]

/-- An ill-formed site fails closed at every state, whatever the environment,
table, or receiver. -/
theorem dynDispatchStep_of_not_wellFormed (env : CompilerQueryEnv) (tbl : OpaqueCalleeTable)
    {site : DynCallSite} (body : CapturedMir) (s : MachineState)
    (hwf : site.wellFormed = false) :
    dynDispatchStep env tbl site body s = MirStepNode.unsupported := by
  simp only [dynDispatchStep, hwf, Bool.false_eq_true, ite_false]

/-- A resolved vtable slot that does not agree with the called method fails closed
(`MirStepNode.unsupported`), whatever the callee table holds. -/
theorem dynDispatchStep_of_method_mismatch (env : CompilerQueryEnv) (tbl : OpaqueCalleeTable)
    {site : DynCallSite} (body : CapturedMir) (s : MachineState) {vt : ProvenancePtr}
    {target : DefPath × List RigidTy} (hwf : site.wellFormed = true)
    (hvt : site.vtablePtr? s = some vt)
    (hr : resolveDynTarget env site vt = .ok target)
    (hname : slotMethodAgrees site target.1 = false) :
    dynDispatchStep env tbl site body s = MirStepNode.unsupported := by
  simp only [dynDispatchStep, vtableTargetAgrees, hwf, ite_true, hvt, hr, hname,
    Bool.and_false, Bool.false_eq_true, ite_false]

/-- A resolved vtable slot whose target still carries an uninstantiated `dyn` receiver type
fails closed (`MirStepNode.unsupported`) instead of falling through to an unlinked external
call. -/
theorem dynDispatchStep_of_dyn_target (env : CompilerQueryEnv) (tbl : OpaqueCalleeTable)
    {site : DynCallSite} (body : CapturedMir) (s : MachineState) {vt : ProvenancePtr}
    {target : DefPath × List RigidTy} (hwf : site.wellFormed = true)
    (hvt : site.vtablePtr? s = some vt)
    (hr : resolveDynTarget env site vt = .ok target)
    (hdyn : (dynSelfTrait? target).isSome = true) :
    dynDispatchStep env tbl site body s = MirStepNode.unsupported := by
  have hnone : (dynSelfTrait? target).isNone = false := by
    cases hopt : dynSelfTrait? target <;> simp_all
  simp only [dynDispatchStep, vtableTargetAgrees, hwf, ite_true, hvt, hr, hnone,
    Bool.false_and, Bool.false_eq_true, ite_false]

/-- Preservation under `EnvExtends` (supportedness is only required on a well-formed site for
the receiver vtable pointer actually present at `s`). -/
theorem dynDispatchStep_envExtends {env₁ env₂ : CompilerQueryEnv} (h : EnvExtends env₁ env₂)
    (tbl : OpaqueCalleeTable) (site : DynCallSite) (body : CapturedMir) (s : MachineState)
    (hsup : site.wellFormed = true → ∀ vt, site.vtablePtr? s = some vt →
      ∀ m, resolveDynTarget env₁ site vt ≠ .unsupported m) :
    dynDispatchStep env₂ tbl site body s = dynDispatchStep env₁ tbl site body s := by
  unfold dynDispatchStep
  cases hwf : site.wellFormed with
  | false => rfl
  | true =>
    simp only [ite_true]
    cases hvt : site.vtablePtr? s with
    | none => rfl
    | some vt => simp only [resolveDynTarget_mono h site vt (hsup hwf vt hvt)]

/-- Preservation under call-cone narrowing. -/
theorem dynDispatchStep_cone_narrow (env : CompilerQueryEnv)
    (narrowTbl fullTbl : OpaqueCalleeTable) (site : DynCallSite) (body : CapturedMir)
    (s : MachineState)
    (hcone : site.wellFormed = true → ∀ vt target, site.vtablePtr? s = some vt →
      resolveDynTarget env site vt = .ok target → vtableTargetAgrees site target = true →
      ∀ k, demandedKey? body s = some k →
        k.apply (redirectResolver narrowTbl site.dynKey target) =
          k.apply (redirectResolver fullTbl site.dynKey target)) :
    dynDispatchStep env narrowTbl site body s = dynDispatchStep env fullTbl site body s := by
  unfold dynDispatchStep
  cases hwf : site.wellFormed with
  | false => rfl
  | true =>
    simp only [ite_true]
    cases hvt : site.vtablePtr? s with
    | none => rfl
    | some vt =>
      dsimp only
      cases hr : resolveDynTarget env site vt with
      | ok target =>
        dsimp only
        cases hn : vtableTargetAgrees site target with
        | false => rfl
        | true => exact stepDynPruned_congr site target body s (hcone hwf vt target hvt hr hn)
      | err e => cases e <;> rfl
      | unsupported m => rfl

/-- **End-to-end integration theorem**: the dynamic-dispatch step is preserved
simultaneously under a sound environment extension and call-cone narrowing. -/
theorem dynDispatchStep_preserved {env₁ env₂ : CompilerQueryEnv}
    {narrowTbl fullTbl : OpaqueCalleeTable} {site : DynCallSite} {body : CapturedMir}
    {s : MachineState} (h : EnvExtends env₁ env₂)
    (hsup : site.wellFormed = true → ∀ vt, site.vtablePtr? s = some vt →
      ∀ m, resolveDynTarget env₁ site vt ≠ .unsupported m)
    (hcone : site.wellFormed = true → ∀ vt target, site.vtablePtr? s = some vt →
      resolveDynTarget env₁ site vt = .ok target → vtableTargetAgrees site target = true →
      ∀ k, demandedKey? body s = some k →
        k.apply (redirectResolver narrowTbl site.dynKey target) =
          k.apply (redirectResolver fullTbl site.dynKey target)) :
    dynDispatchStep env₂ narrowTbl site body s = dynDispatchStep env₁ fullTbl site body s := by
  rw [dynDispatchStep_envExtends h narrowTbl site body s hsup]
  exact dynDispatchStep_cone_narrow env₁ narrowTbl fullTbl site body s hcone

/-- Every `dynDispatchStep` preserves `memory.callees` and `memory.traitImpls` (`FramesStep s`). -/
theorem dynDispatchStep_frames (env : CompilerQueryEnv) (tbl : OpaqueCalleeTable)
    (site : DynCallSite) (body : CapturedMir) (s : MachineState) :
    FramesStep s (dynDispatchStep env tbl site body s) := by
  unfold dynDispatchStep
  cases site.wellFormed with
  | false => exact True.intro
  | true =>
    simp only [ite_true]
    cases site.vtablePtr? s with
    | none => exact True.intro
    | some vt =>
      dsimp only
      cases resolveDynTarget env site vt with
      | ok target =>
        dsimp only
        cases vtableTargetAgrees site target with
        | false => exact True.intro
        | true =>
          simp only [ite_true]
          exact stepDynPruned_frames tbl site target body s
      | err e => cases e <;> exact True.intro
      | unsupported _ => exact True.intro



/-! ### Demand-gated dynamic dispatch -/

/-- Whether the next step at `s` demands the `dyn` call site `site` (a direct call matching both
`site.dynKey` and `site.matchesLoc body s`). -/
def demandsDynSite (site : DynCallSite) (body : CapturedMir) (s : MachineState) : Bool :=
  match demandedKey? body s with
  | some k =>
    isDirectCallAt body s && decide ((k.defPath, k.typeArgs) = site.dynKey) &&
      site.matchesLoc body s
  | none => false

/-- Whether the next step at `s` demands a *virtual* call key (first generic argument
`dyn D`) not handled by `site` at `s`: either a different virtual call key or a call to
`site.dynKey` outside `site.callSiteLoc?`. -/
def demandsUnregisteredDyn (site : DynCallSite) (body : CapturedMir) (s : MachineState) : Bool :=
  match demandedKey? body s with
  | some k =>
    (dynSelfTrait? (k.defPath, k.typeArgs)).isSome && !demandsDynSite site body s
  | none => false

/-- **Demand-gated dynamic-dispatch step**: the receiver's vtable pointer is read
and `resolveDynTarget` (`vtableMethodLookup` followed by `abiCompatible`) is issued
*only* when the active step at `s` actually demands `site.dynKey`. Any *other*
virtual call fails closed (`MirStepNode.unsupported`) instead of falling through to
the trusted static resolver, which has no vtable and would turn the `dyn` call into
an unlinked external call to the trait method's `DefPath`
(`canary_unregistered_dyn_fails_closed`). All remaining steps (literal switches,
non-virtual calls, calls on the other branch) step directly via
`stepBranchPruned tbl.lookup`. -/
def dynDemandStep (env : CompilerQueryEnv) (tbl : OpaqueCalleeTable) (site : DynCallSite)
    (body : CapturedMir) (s : MachineState) : MirStepNode :=
  if demandsDynSite site body s then
    dynDispatchStep env tbl site body s
  else if demandsUnregisteredDyn site body s then
    MirStepNode.unsupported
  else
    stepBranchPruned tbl.lookup body s

/-- Every `dynDemandStep` preserves `memory.callees` and `memory.traitImpls` (`FramesStep s`). -/
theorem dynDemandStep_frames (env : CompilerQueryEnv) (tbl : OpaqueCalleeTable)
    (site : DynCallSite) (body : CapturedMir) (s : MachineState) :
    FramesStep s (dynDemandStep env tbl site body s) := by
  unfold dynDemandStep
  cases demandsDynSite site body s with
  | true => exact dynDispatchStep_frames env tbl site body s
  | false =>
    cases demandsUnregisteredDyn site body s with
    | true => exact True.intro
    | false => exact stepBranchPruned_frames tbl.lookup body s

/-- At any state that demands `site.dynKey` (such as `dynAtCall`), `dynDemandStep`
is definitionally `dynDispatchStep`. -/
theorem dynDemandStep_eq_dynDispatchStep_of_demanded (env : CompilerQueryEnv)
    (tbl : OpaqueCalleeTable) (site : DynCallSite) (body : CapturedMir) (s : MachineState)
    (h : demandsDynSite site body s = true) :
    dynDemandStep env tbl site body s = dynDispatchStep env tbl site body s := by
  simp [dynDemandStep, h]

/-- A step that does not demand `site.dynKey` never consults the redirect. -/
theorem stepBranchPruned_redirect_of_not_demanded (tbl : OpaqueCalleeTable) (site : DynCallSite)
    (body : CapturedMir) (s : MachineState) (target : DefPath × List RigidTy)
    (hnd : demandsDynKey site.dynKey body s = false) :
    stepBranchPruned (redirectResolver tbl site.dynKey target) body s =
      stepBranchPruned tbl.lookup body s := by
  apply stepBranchPruned_congr
  intro k hk
  have hne : ¬ (k.defPath, k.typeArgs) = site.dynKey := by
    intro he
    simp only [demandsDynKey, hk, he, decide_true, Bool.true_eq_false] at hnd
  simp only [CalleeKey.apply, redirectResolver, ite_eq_right_of_eq_false _ _ (eq_false hne)]


/-- **Successful `stepDynPruned` steps are redirected trusted steps**: whenever the
target-redirected step succeeds, it equals the branch-pruned trusted step whose resolver
redirects only the virtual key `site.dynKey` to the vtable-resolved `target`. -/
theorem stepBranchPruned_redirect_of_stepDynPruned_step {tbl : OpaqueCalleeTable}
    {site : DynCallSite} {target : DefPath × List RigidTy} {body : CapturedMir}
    {s s' : MachineState}
    (h : stepDynPruned tbl site target body s = MirStepNode.step s') :
    stepBranchPruned (redirectResolver tbl site.dynKey target) body s = MirStepNode.step s' := by
  unfold stepDynPruned at h
  cases hd : demandsDynKey site.dynKey body s with
  | true =>
    simp only [hd, ite_true] at h
    cases hloc : site.matchesLoc body s with
    | false =>
      simp only [hloc, Bool.false_eq_true, ite_false] at h
      simp [MirStepNode.unsupported, MirStepNode.fail, MirStepNode.step] at h
    | true =>
      simp only [hloc, ite_true] at h
      cases hact : activeTerminator? body s with
      | none =>
        simp only [hact] at h
        simp [MirStepNode.unsupported, MirStepNode.fail, MirStepNode.step] at h
      | some p =>
        obtain ⟨term, cb⟩ := p
        simp only [hact] at h
        unfold stepBranchPruned
        rw [stepMirFnWith_of_activeTerminator _ hact]
        exact stepTerminatorWith_of_stepDynTerminator_step true h
  | false =>
    simp only [hd, Bool.false_eq_true, ite_false] at h
    rw [stepBranchPruned_redirect_of_not_demanded tbl site body s target hd]
    exact h

/-- Out-of-scope calls to `site.dynKey` (`site.matchesLoc body s = false`, including foreign callee
frames for an unscoped site or other SSA blocks for a block-scoped site) fail closed even under raw
`stepDynPruned`. -/
theorem stepDynPruned_of_not_matchesLoc (tbl : OpaqueCalleeTable) (site : DynCallSite)
    (target : DefPath × List RigidTy) (body : CapturedMir) (s : MachineState)
    (hd : demandsDynKey site.dynKey body s = true) (hloc : site.matchesLoc body s = false) :
    stepDynPruned tbl site target body s = MirStepNode.unsupported := by
  simp [stepDynPruned, hd, hloc]

/-- Whenever `stepDynPruned` advances to `.step s'` on a call to `site.dynKey`, `s` is a *direct*
call within `site`'s scope (`demandsDynSite site body s = true`). -/
theorem demandsDynSite_of_stepDynPruned_step {tbl : OpaqueCalleeTable} {site : DynCallSite}
    {target : DefPath × List RigidTy} {body : CapturedMir} {s s' : MachineState}
    (hd : demandsDynKey site.dynKey body s = true)
    (h : stepDynPruned tbl site target body s = MirStepNode.step s') :
    demandsDynSite site body s = true := by
  unfold stepDynPruned at h
  simp only [hd, ite_true] at h
  cases hloc : site.matchesLoc body s with
  | false =>
    simp only [hloc, Bool.false_eq_true, ite_false] at h
    simp [MirStepNode.unsupported, MirStepNode.fail, MirStepNode.step] at h
  | true =>
    simp only [hloc, ite_true] at h
    cases hact : activeTerminator? body s with
    | none =>
      rw [hact] at h
      simp [MirStepNode.unsupported, MirStepNode.fail, MirStepNode.step] at h
    | some p =>
      rcases p with ⟨term, cb⟩
      rw [hact] at h
      have hdir : isDirectCallAt body s = true := by
        simp only [isDirectCallAt, hact]
        exact isDirectTerminatorCall_of_stepDynTerminator_step h
      unfold demandsDynKey at hd
      cases hk : demandedKey? body s with
      | none => rw [hk] at hd; nomatch hd
      | some k =>
        rw [hk] at hd
        simp [demandsDynSite, hk, hdir, hd, hloc]

/-- Whenever eager `dynDispatchStep` advances to `.step s'` on a call to `site.dynKey`, `s` is a
direct call inside `site`'s scope (`demandsDynSite site body s = true`): eager `dynDispatchStep`
can never hijack an indirect `FnPtr` call, a foreign callee frame, or another SSA block. -/
theorem demandsDynSite_of_dynDispatchStep_step {env : CompilerQueryEnv} {tbl : OpaqueCalleeTable}
    {site : DynCallSite} {body : CapturedMir} {s s' : MachineState}
    (hd : demandsDynKey site.dynKey body s = true)
    (h : dynDispatchStep env tbl site body s = MirStepNode.step s') :
    demandsDynSite site body s = true := by
  unfold dynDispatchStep at h
  cases hwf : site.wellFormed with
  | false =>
    simp only [hwf, Bool.false_eq_true, ite_false] at h
    simp [MirStepNode.unsupported, MirStepNode.fail, MirStepNode.step] at h
  | true =>
    simp only [hwf, ite_true] at h
    cases hvt : site.vtablePtr? s with
    | none =>
      simp only [hvt] at h
      simp [MirStepNode.fail, MirStepNode.step] at h
    | some vt =>
      simp only [hvt] at h
      cases hr : resolveDynTarget env site vt with
      | ok target =>
        simp only [hr] at h
        cases hta : vtableTargetAgrees site target with
        | false =>
          simp only [hta, Bool.false_eq_true, ite_false] at h
          simp [MirStepNode.unsupported, MirStepNode.fail, MirStepNode.step] at h
        | true =>
          simp only [hta, ite_true] at h
          exact demandsDynSite_of_stepDynPruned_step hd h
      | err e =>
        simp only [hr] at h
        cases e <;> simp [MirStepNode.retOutcome, MirStepNode.unsupported, MirStepNode.fail,
          MirStepNode.step] at h
      | unsupported m =>
        simp only [hr] at h
        simp [MirStepNode.unsupported, MirStepNode.fail, MirStepNode.step] at h

/-- **Specification of a successful dynamic-dispatch step**: if `dynDispatchStep` advances to
`s'`, then the site is well formed, the receiver's vtable pointer `vt` (start of a non-stack
allocation) resolves through the compiler-query environment to a validated target
(`vtableTargetAgrees`), and `s'` is exactly the branch-pruned trusted step with the virtual key
redirected to that target. -/
theorem dynDispatchStep_step_spec {env : CompilerQueryEnv} {tbl : OpaqueCalleeTable}
    {site : DynCallSite} {body : CapturedMir} {s s' : MachineState}
    (h : dynDispatchStep env tbl site body s = MirStepNode.step s') :
    ∃ vt target, site.wellFormed = true ∧ site.vtablePtr? s = some vt ∧
      resolveDynTarget env site vt = .ok target ∧ vtableTargetAgrees site target = true ∧
      stepBranchPruned (redirectResolver tbl site.dynKey target) body s = MirStepNode.step s' := by
  unfold dynDispatchStep at h
  cases hwf : site.wellFormed with
  | false =>
    simp only [hwf, Bool.false_eq_true, ite_false] at h
    simp [MirStepNode.unsupported, MirStepNode.fail, MirStepNode.step] at h
  | true =>
    simp only [hwf, ite_true] at h
    cases hvt : site.vtablePtr? s with
    | none =>
      simp only [hvt] at h
      simp [MirStepNode.fail, MirStepNode.step] at h
    | some vt =>
      simp only [hvt] at h
      cases hr : resolveDynTarget env site vt with
      | ok target =>
        simp only [hr] at h
        cases hta : vtableTargetAgrees site target with
        | false =>
          simp only [hta, Bool.false_eq_true, ite_false] at h
          simp [MirStepNode.unsupported, MirStepNode.fail, MirStepNode.step] at h
        | true =>
          simp only [hta, ite_true] at h
          refine ⟨vt, target, ?_, ?_, ?_, ?_, stepBranchPruned_redirect_of_stepDynPruned_step h⟩ <;>
            first | rfl | assumption
      | err e =>
        simp only [hr] at h
        cases e <;> simp [MirStepNode.retOutcome, MirStepNode.unsupported, MirStepNode.fail,
          MirStepNode.step] at h
      | unsupported m =>
        simp only [hr] at h
        simp [MirStepNode.unsupported, MirStepNode.fail, MirStepNode.step] at h
/-- **Demand gating is conservative**: wherever the eager dynamic-dispatch step
resolves the receiver's method (well-formed site, `.ok target` for the vtable
pointer at `s`) and the step demands no *unregistered* virtual call, the
demand-gated step is *identical* to it. The two differ only where the eager query
fails (missing receiver, `.err`, or `.unsupported`) and the step does not demand
the `dyn` key — demand gating only removes failures of calls that are not executed
(`canary_dyn_deadBranch_schema12_succeeds`) — or where an unregistered virtual call
is demanded, which demand gating fails closed. -/
theorem dynDemandStep_eq_dynDispatchStep_of_resolved {env : CompilerQueryEnv}
    {tbl : OpaqueCalleeTable} {site : DynCallSite} {body : CapturedMir} {s : MachineState}
    {vt : ProvenancePtr} {target : DefPath × List RigidTy} (hwf : site.wellFormed = true)
    (hvt : site.vtablePtr? s = some vt) (hr : resolveDynTarget env site vt = .ok target)
    (htarget : vtableTargetAgrees site target = true)
    (hu : demandsUnregisteredDyn site body s = false) :
    dynDemandStep env tbl site body s = dynDispatchStep env tbl site body s := by
  unfold dynDemandStep
  cases hd : demandsDynSite site body s with
  | true => rfl
  | false =>
    simp only [Bool.false_eq_true, ite_false, hu]
    have hnk : demandsDynKey site.dynKey body s = false := by
      unfold demandsDynKey
      cases hk : demandedKey? body s with
      | none => rfl
      | some k =>
        by_cases he : (k.defPath, k.typeArgs) = site.dynKey
        · have hds : (dynSelfTrait? site.dynKey).isSome = true := by
            unfold DynCallSite.wellFormed at hwf
            cases hds' : dynSelfTrait? site.dynKey with
            | none => rw [hds'] at hwf; nomatch hwf
            | some _ => rfl
          simp only [demandsUnregisteredDyn, hk, hd, Bool.not_false, Bool.and_true, he, hds] at hu
          nomatch hu
        · simp [he]
    rw [dynDispatchStep_eq_of_resolved hwf hvt hr htarget]
    simp [stepDynPruned, hnk]

/-- A step that does not demand the `dyn` key is exactly the trusted `stepMirFn`
step (under the `memory.callees` frame condition): demand gating adds no new
semantics off the `dyn` call. -/
theorem dynDemandStep_eq_trusted_of_not_demanded (env : CompilerQueryEnv)
    (tbl : OpaqueCalleeTable) (site : DynCallSite) (body : CapturedMir) (s : MachineState)
    (hnd : demandsDynSite site body s = false) (hu : demandsUnregisteredDyn site body s = false)
    (hframe : tbl.toList = s.memory.callees) :
    dynDemandStep env tbl site body s = stepMirFn body s := by
  simp only [dynDemandStep, hnd, hu, Bool.false_eq_true, ite_false]
  exact stepBranchPruned_eq_trusted tbl body s hframe

/-- An unregistered virtual call fails closed under every environment and table. -/
theorem dynDemandStep_of_unregistered (env : CompilerQueryEnv) (tbl : OpaqueCalleeTable)
    (site : DynCallSite) (body : CapturedMir) (s : MachineState)
    (hu : demandsUnregisteredDyn site body s = true) :
    dynDemandStep env tbl site body s = MirStepNode.unsupported := by
  have hnd : demandsDynSite site body s = false := by
    unfold demandsUnregisteredDyn at hu
    cases hk : demandedKey? body s with
    | none => simp [hk] at hu
    | some k =>
      rw [hk] at hu
      cases hd : demandsDynSite site body s with
      | false => rfl
      | true => simp [hd] at hu
  simp only [dynDemandStep, hnd, hu, Bool.false_eq_true, ite_false, ite_true]

/-- An unscoped site matches exactly the frames executing the root function. -/
theorem DynCallSite.matchesLoc_of_unscoped {site : DynCallSite} (body : CapturedMir)
    (s : MachineState) (hun : site.callSiteLoc? = none) :
    site.matchesLoc body s = decide ((s.memory.activeCallee.getD body).defPath = body.defPath) := by
  simp [DynCallSite.matchesLoc, hun]

/-- **Unscoped sites never dispatch in another function's frame**: while a body of a different
function executes, an unscoped site is never demanded, so `dynDemandStep` is either the
branch-pruned trusted step or fails closed on the (then unregistered) virtual call — it never
reinterprets that frame's `vtableLocal`. -/
theorem dynDemandStep_of_unscoped_foreign_frame (env : CompilerQueryEnv) (tbl : OpaqueCalleeTable)
    {site : DynCallSite} {body : CapturedMir} {s : MachineState}
    (hun : site.callSiteLoc? = none)
    (hforeign : (s.memory.activeCallee.getD body).defPath ≠ body.defPath) :
    dynDemandStep env tbl site body s = stepBranchPruned tbl.lookup body s ∨
      dynDemandStep env tbl site body s = MirStepNode.unsupported := by
  have hnd : demandsDynSite site body s = false := by
    unfold demandsDynSite
    cases demandedKey? body s with
    | none => rfl
    | some k => simp [DynCallSite.matchesLoc, hun, hforeign]
  unfold dynDemandStep
  simp only [hnd, Bool.false_eq_true, ite_false]
  cases demandsUnregisteredDyn site body s with
  | true => exact Or.inr rfl
  | false => exact Or.inl rfl

/-- Fuel-bounded multi-step evaluation with demand-gated dynamic dispatch. -/
def evalDynWithOpaqueCallees (env : CompilerQueryEnv) (tbl : OpaqueCalleeTable)
    (site : DynCallSite) (body : CapturedMir) (fuel : Nat) (s : MachineState) : RunResult :=
  runSteps (dynDemandStep env tbl site body) fuel s []

/-- **Unconditional multi-step trusted agreement for non-`dyn` runs**: when no visited state
along the run demands a virtual call (`demandsDynSite = false` and `demandsUnregisteredDyn = false`,
e.g. a virtual call sitting only on a pruned dead branch) and `s.memory.callees = tbl.toList`,
`evalDynWithOpaqueCallees` equals the iterated trusted `stepMirFn` with no per-step frame
obligation. -/
theorem evalDynWithOpaqueCallees_eq_trusted_of_no_dyn_unconditional (env : CompilerQueryEnv)
    (tbl : OpaqueCalleeTable) (site : DynCallSite) (body : CapturedMir) (fuel : Nat)
    (s : MachineState) (hcallees : s.memory.callees = tbl.toList)
    (hnodyn : ∀ s' ∈ runVisited (stepBranchPruned tbl.lookup body) fuel s,
      demandsDynSite site body s' = false ∧ demandsUnregisteredDyn site body s' = false) :
    evalDynWithOpaqueCallees env tbl site body fuel s = runSteps (stepMirFn body) fuel s [] := by
  have h_opaque : evalDynWithOpaqueCallees env tbl site body fuel s =
      evalWithOpaqueCallees tbl body fuel s := by
    unfold evalDynWithOpaqueCallees evalWithOpaqueCallees
    refine runSteps_congr_visited fuel s [] fun s' hs' => ?_
    obtain ⟨h₁, h₂⟩ := hnodyn s' hs'
    simp only [dynDemandStep, h₁, h₂, Bool.false_eq_true, ite_false]
  rw [h_opaque]
  exact evalWithOpaqueCallees_eq_trusted_unconditional tbl body fuel s hcallees

/-- Per-state side conditions under which one demand-gated step is preserved by
`EnvExtends env₁ env₂` and narrowing `fullTbl` to `narrowTbl`. -/
structure DynStepPreserved (env₁ : CompilerQueryEnv) (narrowTbl fullTbl : OpaqueCalleeTable)
    (site : DynCallSite) (body : CapturedMir) (s : MachineState) : Prop where
  /-- A demanded well-formed `dyn` call's query is supported by `env₁`. -/
  supported : site.wellFormed = true → demandsDynSite site body s = true →
    ∀ vt, site.vtablePtr? s = some vt → ∀ m, resolveDynTarget env₁ site vt ≠ .unsupported m
  /-- A demanded well-formed `dyn` call's valid redirected key agrees across the tables. -/
  dynCone : site.wellFormed = true → demandsDynSite site body s = true →
    ∀ vt target, site.vtablePtr? s = some vt → resolveDynTarget env₁ site vt = .ok target →
      vtableTargetAgrees site target = true → ∀ k, demandedKey? body s = some k →
        k.apply (redirectResolver narrowTbl site.dynKey target) =
          k.apply (redirectResolver fullTbl site.dynKey target)
  /-- Any non-virtual demanded key agrees across the tables (unregistered virtual calls fail
  closed on both sides without consulting either table). -/
  cone : demandsDynSite site body s = false → demandsUnregisteredDyn site body s = false →
    ∀ k, demandedKey? body s = some k → narrowTbl.lookupKey k = fullTbl.lookupKey k

/-- Single-step preservation of `dynDemandStep` under `EnvExtends` (supportedness
is only needed when `site.wellFormed = true` and `demandsDynSite site body s = true`) and
call-cone narrowing. -/
theorem dynDemandStep_preserved {env₁ env₂ : CompilerQueryEnv}
    {narrowTbl fullTbl : OpaqueCalleeTable} {site : DynCallSite} {body : CapturedMir}
    {s : MachineState} (h : EnvExtends env₁ env₂)
    (hp : DynStepPreserved env₁ narrowTbl fullTbl site body s) :
    dynDemandStep env₂ narrowTbl site body s = dynDemandStep env₁ fullTbl site body s := by
  unfold dynDemandStep
  cases hd : demandsDynSite site body s with
  | true =>
    simp only [ite_true]
    exact dynDispatchStep_preserved h (fun hwf => hp.supported hwf hd)
      (fun hwf => hp.dynCone hwf hd)
  | false =>
    simp only [Bool.false_eq_true, ite_false]
    cases hu : demandsUnregisteredDyn site body s with
    | true => rfl
    | false =>
      simp only [Bool.false_eq_true, ite_false]
      exact stepBranchPruned_congr body s (hp.cone hd hu)

/-- **Multi-step end-to-end preservation**: if every state the `env₁`/`fullTbl`
run visits satisfies `DynStepPreserved`, the entire demand-gated dynamic-dispatch
run (receiver vtable pointer → `UnOp.vtableMethodLookup` → `abiCompatible` →
`OpaqueCalleeTable.lookup` → `stepBranchPruned`, every step) is preserved under
`EnvExtends env₁ env₂` and narrowing to `narrowTbl`. -/
theorem evalDynWithOpaqueCallees_preserved {env₁ env₂ : CompilerQueryEnv}
    {narrowTbl fullTbl : OpaqueCalleeTable} {site : DynCallSite} {body : CapturedMir}
    (h : EnvExtends env₁ env₂) (fuel : Nat) (s : MachineState)
    (hvisit : ∀ s' ∈ runVisited (dynDemandStep env₁ fullTbl site body) fuel s,
      DynStepPreserved env₁ narrowTbl fullTbl site body s') :
    evalDynWithOpaqueCallees env₂ narrowTbl site body fuel s =
      evalDynWithOpaqueCallees env₁ fullTbl site body fuel s :=
  runSteps_congr_visited fuel s [] (fun s' hs' => dynDemandStep_preserved h (hvisit s' hs'))

/-- Decidable per-state certificate for `DynStepPreserved` (what a client checks by
kernel evaluation along the run). Steps that fail closed without consulting the table
(ill-formed sites, invalid vtable targets, or unregistered virtual calls) immediately
return `true`. -/
def dynStepPreservedB (env₁ : CompilerQueryEnv) (narrowTbl fullTbl : OpaqueCalleeTable)
    (site : DynCallSite) (body : CapturedMir) (s : MachineState) : Bool :=
  match demandedKey? body s with
  | none => true
  | some k =>
    if isDirectCallAt body s && decide ((k.defPath, k.typeArgs) = site.dynKey) &&
        site.matchesLoc body s then
      if site.wellFormed then
        match site.vtablePtr? s with
        | none => true
        | some vt =>
          match resolveDynTarget env₁ site vt with
          | .ok target =>
            if vtableTargetAgrees site target then
              decide (k.apply (redirectResolver narrowTbl site.dynKey target) =
                k.apply (redirectResolver fullTbl site.dynKey target))
            else true
          | .err _ => true
          | .unsupported _ => false
      else true
    else if (dynSelfTrait? (k.defPath, k.typeArgs)).isSome then true
    else decide (narrowTbl.lookupKey k = fullTbl.lookupKey k)

/-- The decidable certificate is sound. -/
theorem dynStepPreserved_of_check {env₁ : CompilerQueryEnv} {narrowTbl fullTbl : OpaqueCalleeTable}
    {site : DynCallSite} {body : CapturedMir} {s : MachineState}
    (hc : dynStepPreservedB env₁ narrowTbl fullTbl site body s = true) :
    DynStepPreserved env₁ narrowTbl fullTbl site body s := by
  unfold dynStepPreservedB at hc
  cases hk : demandedKey? body s with
  | none =>
    refine ⟨fun _ hd => ?_, fun _ hd => ?_, fun _ _ k hk' => ?_⟩
    · simp [demandsDynSite, hk] at hd
    · simp [demandsDynSite, hk] at hd
    · rw [hk] at hk'
      exact nomatch hk'
  | some k =>
    rw [hk] at hc
    dsimp only at hc
    cases hm : (isDirectCallAt body s && decide ((k.defPath, k.typeArgs) = site.dynKey) &&
        site.matchesLoc body s) with
    | true =>
      simp only [hm, ite_true] at hc
      refine ⟨fun hwf _ vt hvt m hunsup => ?_, fun hwf _ vt target hvt hr hta k' hk' => ?_,
        fun hd => ?_⟩
      · simp only [hwf, ite_true, hvt, hunsup, Bool.false_eq_true] at hc
      · rw [hk] at hk'
        cases hk'
        simp only [hwf, ite_true, hvt, hr, hta, decide_eq_true_eq] at hc
        exact hc
      · simp [demandsDynSite, hk, hm] at hd
    | false =>
      simp only [hm, Bool.false_eq_true, ite_false] at hc
      refine ⟨fun _ hd => ?_, fun _ hd => ?_, fun _ hu k' hk' => ?_⟩
      · simp [demandsDynSite, hk, hm] at hd
      · simp [demandsDynSite, hk, hm] at hd
      · rw [hk] at hk'
        cases hk'
        have hv : (dynSelfTrait? (k.defPath, k.typeArgs)).isSome = false := by
          simp [demandsUnregisteredDyn, demandsDynSite, hk, hm] at hu
          simp [hu]
        simp only [hv, Bool.false_eq_true, ite_false] at hc
        exact of_decide_eq_true hc

/-- Multi-step preservation from per-state certificates checked along the run. -/
theorem evalDynWithOpaqueCallees_preserved_of_check {env₁ env₂ : CompilerQueryEnv}
    {narrowTbl fullTbl : OpaqueCalleeTable} {site : DynCallSite} {body : CapturedMir}
    (h : EnvExtends env₁ env₂) (fuel : Nat) (s : MachineState)
    (hcheck : (runVisited (dynDemandStep env₁ fullTbl site body) fuel s).all
      (dynStepPreservedB env₁ narrowTbl fullTbl site body) = true) :
    evalDynWithOpaqueCallees env₂ narrowTbl site body fuel s =
      evalDynWithOpaqueCallees env₁ fullTbl site body fuel s :=
  evalDynWithOpaqueCallees_preserved h fuel s
    (fun s' hs' => dynStepPreserved_of_check (List.all_eq_true.mp hcheck s' hs'))

/-- **Narrow-run multi-step end-to-end preservation**: states are collected along
the *narrowed* run `runVisited (dynDemandStep env₂ narrowTbl site body) fuel s`
(so `fullTbl` is never stepped to compute the visited-state list!). -/
theorem evalDynWithOpaqueCallees_preserved_of_narrow {env₁ env₂ : CompilerQueryEnv}
    {narrowTbl fullTbl : OpaqueCalleeTable} {site : DynCallSite} {body : CapturedMir}
    (h : EnvExtends env₁ env₂) (fuel : Nat) (s : MachineState)
    (hvisit : ∀ s' ∈ runVisited (dynDemandStep env₂ narrowTbl site body) fuel s,
      DynStepPreserved env₁ narrowTbl fullTbl site body s') :
    evalDynWithOpaqueCallees env₂ narrowTbl site body fuel s =
      evalDynWithOpaqueCallees env₁ fullTbl site body fuel s := by
  symm
  exact runSteps_congr_visited fuel s []
    (fun s' hs' => (dynDemandStep_preserved h (hvisit s' hs')).symm)

/-- Narrow-run multi-step preservation from per-state certificates checked along
the *narrowed* run (`runVisited` never steps `fullTbl`). -/
theorem evalDynWithOpaqueCallees_preserved_of_narrow_check {env₁ env₂ : CompilerQueryEnv}
    {narrowTbl fullTbl : OpaqueCalleeTable} {site : DynCallSite} {body : CapturedMir}
    (h : EnvExtends env₁ env₂) (fuel : Nat) (s : MachineState)
    (hcheck : (runVisited (dynDemandStep env₂ narrowTbl site body) fuel s).all
      (dynStepPreservedB env₁ narrowTbl fullTbl site body) = true) :
    evalDynWithOpaqueCallees env₂ narrowTbl site body fuel s =
      evalDynWithOpaqueCallees env₁ fullTbl site body fuel s :=
  evalDynWithOpaqueCallees_preserved_of_narrow h fuel s
    (fun s' hs' => dynStepPreserved_of_check (List.all_eq_true.mp hcheck s' hs'))


/-! ### Multi-site dynamic-dispatch registry (`DynCallRegistry`) -/

/-- A registry of virtual call sites (one `DynCallSite` per virtual call key in the
lowered program). -/
abbrev DynCallRegistry : Type := List DynCallSite

/-- The registered `DynCallSite` for call key `key` (`(defPath, typeArgs)`), if
exactly one site is registered for it. An ambiguous key (two or more sites) has no
site, so a virtual call on it fails closed instead of silently taking whichever
site comes first (`canary_dyn_registry_ambiguity_fails_closed`), mirroring the
trusted resolver's demand for a *unique* most-specific `impl`. -/
def DynCallRegistry.findSite? (reg : DynCallRegistry) (key : DefPath × List RigidTy) :
    Option DynCallSite :=
  match reg.filter (fun site => decide (site.dynKey = key)) with
  | [site] => some site
  | _ => none

/-- A registry is well formed when every registered site is well formed and no two
sites share a call key. -/
def DynCallRegistry.wellFormed (reg : DynCallRegistry) : Bool :=
  reg.all DynCallSite.wellFormed && decide (reg.map (·.dynKey)).Nodup

/-- Exact characterization of `DynCallRegistry.wellFormed`. -/
theorem DynCallRegistry.wellFormed_iff (reg : DynCallRegistry) :
    reg.wellFormed = true ↔
      (∀ site ∈ reg, site.wellFormed = true) ∧ (reg.map (·.dynKey)).Nodup := by
  simp [DynCallRegistry.wellFormed, List.all_eq_true]

theorem filter_dynKey_eq_nil_of_not_mem :
    ∀ (reg : DynCallRegistry) (key : DefPath × List RigidTy),
      key ∉ reg.map (·.dynKey) →
        reg.filter (fun s => decide (s.dynKey = key)) = []
  | [], _, _ => rfl
  | s :: rest, key, hnm => by
    rw [List.map_cons, List.mem_cons, not_or] at hnm
    have hne : decide (s.dynKey = key) = false := decide_eq_false (fun e => hnm.1 e.symm)
    simp only [List.filter_cons, hne, Bool.false_eq_true, ite_false]
    exact filter_dynKey_eq_nil_of_not_mem rest key hnm.2

theorem filter_dynKey_of_nodup :
    ∀ (reg : DynCallRegistry) {site : DynCallSite},
      (reg.map (·.dynKey)).Nodup → site ∈ reg →
        reg.filter (fun s => decide (s.dynKey = site.dynKey)) = [site]
  | [], _, _, hmem => nomatch hmem
  | s :: rest, site, hnd, hmem => by
    rw [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp hmem with rfl | hrest
    · simp [filter_dynKey_eq_nil_of_not_mem rest site.dynKey hnd.1]
    · have hne : s.dynKey ≠ site.dynKey :=
        fun e => hnd.1 (e ▸ List.mem_map_of_mem hrest)
      simp [hne, filter_dynKey_of_nodup rest hnd.2 hrest]

/-- Every member of a well-formed registry is uniquely resolved by `findSite?` and is
itself well formed. -/
theorem DynCallRegistry.findSite?_eq_some_of_wellFormed {reg : DynCallRegistry}
    {site : DynCallSite} (hwf : reg.wellFormed = true) (hmem : site ∈ reg) :
    reg.findSite? site.dynKey = some site ∧ site.wellFormed = true := by
  obtain ⟨hall, hnd⟩ := (DynCallRegistry.wellFormed_iff reg).mp hwf
  refine ⟨?_, hall site hmem⟩
  unfold DynCallRegistry.findSite?
  rw [filter_dynKey_of_nodup reg hnd hmem]

/-- Any site returned by `findSite?` belongs to `reg`, matches `key`, and — when `reg` is
well formed — satisfies `site.wellFormed = true`. -/
theorem DynCallRegistry.wellFormed_of_findSite? {reg : DynCallRegistry}
    {key : DefPath × List RigidTy} {site : DynCallSite}
    (hfind : reg.findSite? key = some site) :
    site ∈ reg ∧ site.dynKey = key ∧ (reg.wellFormed = true → site.wellFormed = true) := by
  unfold DynCallRegistry.findSite? at hfind
  cases hf : reg.filter (fun s => decide (s.dynKey = key)) with
  | nil => rw [hf] at hfind; nomatch hfind
  | cons a rest =>
    cases rest with
    | nil =>
      rw [hf] at hfind
      injection hfind with ha
      subst ha
      have hm : a ∈ reg.filter (fun s => decide (s.dynKey = key)) := by rw [hf]; simp
      obtain ⟨hmem, hkey⟩ := List.mem_filter.mp hm
      exact ⟨hmem, of_decide_eq_true hkey,
        fun hwf => ((DynCallRegistry.wellFormed_iff reg).mp hwf).1 a hmem⟩
    | cons _ _ => rw [hf] at hfind; nomatch hfind

/-- **Duplicate registrations fail closed**: if two entries in `pre ++ s₁ :: mid ++ s₂ :: post`
share `dynKey = key`, the registry is ill formed (`wellFormed = false`) and `findSite? key = none`. -/
theorem DynCallRegistry.findSite?_eq_none_of_duplicate
    (pre mid post : List DynCallSite) {s₁ s₂ : DynCallSite} {key : DefPath × List RigidTy}
    (hk₁ : s₁.dynKey = key) (hk₂ : s₂.dynKey = key) :
    DynCallRegistry.wellFormed (pre ++ s₁ :: mid ++ s₂ :: post) = false ∧
      DynCallRegistry.findSite? (pre ++ s₁ :: mid ++ s₂ :: post) key = none := by
  have hlen : 2 ≤ ((pre ++ s₁ :: mid ++ s₂ :: post).filter
      (fun s => decide (s.dynKey = key))).length := by
    simp [List.filter_append, hk₁, hk₂]
    omega
  have hfind : DynCallRegistry.findSite? (pre ++ s₁ :: mid ++ s₂ :: post) key = none := by
    unfold DynCallRegistry.findSite?
    cases hf : (pre ++ s₁ :: mid ++ s₂ :: post).filter (fun s => decide (s.dynKey = key)) with
    | nil => rfl
    | cons a rest =>
      cases rest with
      | nil => rw [hf] at hlen; simp at hlen
      | cons b rest' => rfl
  refine ⟨?_, hfind⟩
  cases hwf : DynCallRegistry.wellFormed (pre ++ s₁ :: mid ++ s₂ :: post) with
  | false => rfl
  | true =>
    have hs₁ := (DynCallRegistry.findSite?_eq_some_of_wellFormed hwf
      (by simp : s₁ ∈ pre ++ s₁ :: mid ++ s₂ :: post)).1
    rw [hk₁, hfind] at hs₁
    nomatch hs₁

/-- Whether two `DynCallSite` registrations overlap (same `dynKey` and compatible scopes). -/
def DynCallSite.overlaps (s₁ s₂ : DynCallSite) : Bool :=
  decide (s₁.dynKey = s₂.dynKey) &&
    match s₁.callSiteLoc?, s₂.callSiteLoc? with
    | some l₁, some l₂ => decide (l₁ = l₂)
    | _, _ => true

/-- Location-aware registry lookup at active state `(body, s)`: returns `some site` iff
**exactly one** registered site matches both `key` and `site.matchesLoc body s`. -/
def DynCallRegistry.findSiteAt? (reg : DynCallRegistry) (body : CapturedMir)
    (s : MachineState) (key : DefPath × List RigidTy) : Option DynCallSite :=
  match reg.filter (fun site => decide (site.dynKey = key) && site.matchesLoc body s) with
  | [site] => some site
  | _ => none

/-- Pairwise non-overlapping check on a list of `DynCallSite`s. -/
def DynCallRegistry.noOverlaps : DynCallRegistry → Bool
  | [] => true
  | s :: rest => rest.all (fun s' => !s.overlaps s') && noOverlaps rest

/-- Location-scoped registry well-formedness: every site is well formed and no two sites have
overlapping `(dynKey, callSiteLoc?)` domains (generalizing `DynCallRegistry.wellFormed` to
support multiple SSA blocks or caller/callee functions calling the same virtual method with
distinct `vtableLocal` temporaries). -/
def DynCallRegistry.scopedWellFormed (reg : DynCallRegistry) : Bool :=
  reg.all DynCallSite.wellFormed && DynCallRegistry.noOverlaps reg

/-- When every site in `reg` is unscoped (`callSiteLoc? = none`), `findSiteAt?` coincides
with `findSite?` in every frame of the root function. -/
theorem DynCallRegistry.findSiteAt?_eq_findSite?_of_unscoped (reg : DynCallRegistry)
    (body : CapturedMir) (s : MachineState) (key : DefPath × List RigidTy)
    (hun : reg.all (fun site => site.callSiteLoc?.isNone) = true)
    (hroot : (s.memory.activeCallee.getD body).defPath = body.defPath) :
    reg.findSiteAt? body s key = reg.findSite? key := by
  unfold DynCallRegistry.findSiteAt? DynCallRegistry.findSite?
  have hflt :
      reg.filter (fun site => decide (site.dynKey = key) && site.matchesLoc body s) =
        reg.filter (fun site => decide (site.dynKey = key)) := by
    induction reg with
    | nil => rfl
    | cons hd tl ih =>
      simp only [List.all_cons, Bool.and_eq_true] at hun
      have hloc : hd.matchesLoc body s = true := by
        unfold DynCallSite.matchesLoc
        cases hopt : hd.callSiteLoc? with
        | none => simp [hroot]
        | some _ => rw [hopt] at hun; nomatch hun.1
      simp only [List.filter_cons, hloc, Bool.and_true, ih hun.2]
  rw [hflt]


/-- Two registrations for the same call key that both match the active location overlap. -/
theorem DynCallSite.overlaps_of_matchesLoc {x y : DynCallSite} {body : CapturedMir}
    {s : MachineState} (hk : x.dynKey = y.dynKey) (hx : x.matchesLoc body s = true)
    (hy : y.matchesLoc body s = true) : x.overlaps y = true := by
  unfold DynCallSite.overlaps
  unfold DynCallSite.matchesLoc at hx hy
  rw [hk]
  cases hlx : x.callSiteLoc? with
  | none => simp
  | some lx =>
    cases hly : y.callSiteLoc? with
    | none => simp
    | some ly =>
      rw [hlx] at hx
      rw [hly] at hy
      simp only [decide_eq_true_eq] at hx hy
      simp [← hx, ← hy]

/-- `noOverlaps` is pairwise non-overlap. -/
theorem DynCallRegistry.noOverlaps_pairwise :
    ∀ {reg : DynCallRegistry}, reg.noOverlaps = true →
      reg.Pairwise (fun a b => a.overlaps b = false)
  | [], _ => List.Pairwise.nil
  | x :: rest, h => by
    unfold DynCallRegistry.noOverlaps at h
    rw [Bool.and_eq_true, List.all_eq_true] at h
    refine List.Pairwise.cons (fun b hb => ?_) (noOverlaps_pairwise h.2)
    have hb' := h.1 b hb
    simpa using hb'

/-- A filter that rejects every element is empty (axiom-free, unlike `List.filter_eq_nil_iff`,
whose proof uses `Classical.choice`). -/
theorem DynCallRegistry.filter_eq_nil_of_forall {p : DynCallSite → Bool} :
    ∀ {l : List DynCallSite}, (∀ a ∈ l, p a = false) → l.filter p = []
  | [], _ => rfl
  | a :: l, h => by
    simp only [List.filter_cons, h a (List.Mem.head _), Bool.false_eq_true, ite_false]
    exact DynCallRegistry.filter_eq_nil_of_forall fun b hb => h b (List.Mem.tail _ hb)

/-- In a pairwise non-overlapping registry, a predicate any two of whose witnesses overlap
selects exactly the one member that satisfies it. -/
theorem DynCallRegistry.filter_eq_singleton_of_pairwise {p : DynCallSite → Bool}
    {site : DynCallSite} (hov : ∀ a b, p a = true → p b = true → a.overlaps b = true) :
    ∀ {reg : DynCallRegistry}, reg.Pairwise (fun a b => a.overlaps b = false) →
      site ∈ reg → p site = true → reg.filter p = [site]
  | [], _, hmem, _ => nomatch hmem
  | x :: rest, hpw, hmem, hp => by
    rcases List.pairwise_cons.mp hpw with ⟨hx, hrest⟩
    rcases List.mem_cons.mp hmem with rfl | hmem'
    · have hnil : rest.filter p = [] := by
        refine DynCallRegistry.filter_eq_nil_of_forall fun a ha => ?_
        cases hpa : p a with
        | false => rfl
        | true =>
          have hxa := hx a ha
          rw [hov _ _ hp hpa] at hxa
          nomatch hxa
      simp only [List.filter_cons, hp, ite_true, hnil]
    · have hpx : p x = false := by
        cases hpx : p x with
        | false => rfl
        | true =>
          have hxs := hx site hmem'
          rw [hov _ _ hpx hp] at hxs
          nomatch hxs
      simp only [List.filter_cons, hpx, Bool.false_eq_true, ite_false]
      exact DynCallRegistry.filter_eq_singleton_of_pairwise hov hrest hmem' hp

/-- **Unique location-scoped resolution**: in a `scopedWellFormed` registry, every member
site is returned by `findSiteAt?` at *every* state where its scope matches, and is itself well
formed (the location-scoped analogue of `DynCallRegistry.findSite?_eq_some_of_wellFormed`). -/
theorem DynCallRegistry.findSiteAt?_eq_some_of_scopedWellFormed {reg : DynCallRegistry}
    {site : DynCallSite} (body : CapturedMir) (s : MachineState)
    (hwf : reg.scopedWellFormed = true) (hmem : site ∈ reg)
    (hloc : site.matchesLoc body s = true) :
    reg.findSiteAt? body s site.dynKey = some site ∧ site.wellFormed = true := by
  unfold DynCallRegistry.scopedWellFormed at hwf
  rw [Bool.and_eq_true, List.all_eq_true] at hwf
  refine ⟨?_, hwf.1 site hmem⟩
  have hov : ∀ a b : DynCallSite,
      (decide (a.dynKey = site.dynKey) && a.matchesLoc body s) = true →
      (decide (b.dynKey = site.dynKey) && b.matchesLoc body s) = true →
      a.overlaps b = true := by
    intro a b ha hb
    simp only [Bool.and_eq_true, decide_eq_true_eq] at ha hb
    exact DynCallSite.overlaps_of_matchesLoc (ha.1.trans hb.1.symm) ha.2 hb.2
  unfold DynCallRegistry.findSiteAt?
  rw [DynCallRegistry.filter_eq_singleton_of_pairwise hov
    (DynCallRegistry.noOverlaps_pairwise hwf.2) hmem (by simp [hloc])]

/-- A site returned by `findSiteAt?` belongs to the registry, carries the queried key, and
matches the active location. -/
theorem DynCallRegistry.findSiteAt?_spec {reg : DynCallRegistry} {body : CapturedMir}
    {s : MachineState} {key : DefPath × List RigidTy} {site : DynCallSite}
    (h : reg.findSiteAt? body s key = some site) :
    site ∈ reg ∧ site.dynKey = key ∧ site.matchesLoc body s = true := by
  unfold DynCallRegistry.findSiteAt? at h
  cases hf : reg.filter (fun x => decide (x.dynKey = key) && x.matchesLoc body s) with
  | nil => rw [hf] at h; nomatch h
  | cons a rest =>
    cases rest with
    | nil =>
      rw [hf] at h
      injection h with ha
      subst ha
      have hm : a ∈ reg.filter (fun x => decide (x.dynKey = key) && x.matchesLoc body s) := by
        rw [hf]; exact List.Mem.head _
      obtain ⟨hmem, hp⟩ := List.mem_filter.mp hm
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
      exact ⟨hmem, hp.1, hp.2⟩
    | cons b rest' => rw [hf] at h; nomatch h

/-- Distinct `dynKey`s imply `noOverlaps`. -/
theorem DynCallRegistry.noOverlaps_of_nodup :
    ∀ (reg : DynCallRegistry), (reg.map (·.dynKey)).Nodup → reg.noOverlaps = true
  | [], _ => rfl
  | s :: rest, hnd => by
    rw [List.map_cons, List.nodup_cons] at hnd
    unfold DynCallRegistry.noOverlaps
    rw [Bool.and_eq_true, List.all_eq_true]
    refine ⟨fun s' hs' => ?_, noOverlaps_of_nodup rest hnd.2⟩
    have hne : s.dynKey ≠ s'.dynKey :=
      fun he => hnd.1 (he ▸ List.mem_map_of_mem hs')
    simp [DynCallSite.overlaps, hne]

/-- `scopedWellFormed` strictly generalizes `wellFormed`: every key-disjoint well-formed registry
is also `scopedWellFormed`. -/
theorem DynCallRegistry.scopedWellFormed_of_wellFormed {reg : DynCallRegistry}
    (hwf : reg.wellFormed = true) : reg.scopedWellFormed = true := by
  obtain ⟨hall, hnd⟩ := (DynCallRegistry.wellFormed_iff reg).mp hwf
  unfold DynCallRegistry.scopedWellFormed
  rw [Bool.and_eq_true, List.all_eq_true]
  exact ⟨hall, DynCallRegistry.noOverlaps_of_nodup reg hnd⟩

theorem DynCallRegistry.nodup_of_noOverlaps_unscoped :
    ∀ (reg : DynCallRegistry),
      reg.all (fun site => site.callSiteLoc?.isNone) = true →
      reg.noOverlaps = true →
      (reg.map (·.dynKey)).Nodup
  | [], _, _ => List.Pairwise.nil
  | s :: rest, hun, hno => by
    simp only [List.all_cons, Bool.and_eq_true] at hun
    unfold DynCallRegistry.noOverlaps at hno
    rw [Bool.and_eq_true, List.all_eq_true] at hno
    rw [List.map_cons, List.nodup_cons]
    refine ⟨fun hk => ?_, nodup_of_noOverlaps_unscoped rest hun.2 hno.2⟩
    obtain ⟨s', hs', heq⟩ := List.mem_map.mp hk
    have hov := hno.1 s' hs'
    cases hloc : s.callSiteLoc? with
    | some _ => rw [hloc] at hun; nomatch hun.1
    | none =>
      simp [DynCallSite.overlaps, hloc, heq] at hov

/-- On unscoped registries (`callSiteLoc? = none` everywhere), `scopedWellFormed` coincides
exactly with `wellFormed`. -/
theorem DynCallRegistry.scopedWellFormed_eq_wellFormed_of_unscoped (reg : DynCallRegistry)
    (hun : reg.all (fun site => site.callSiteLoc?.isNone) = true) :
    reg.scopedWellFormed = reg.wellFormed := by
  cases hwf : reg.wellFormed with
  | true => exact DynCallRegistry.scopedWellFormed_of_wellFormed hwf
  | false =>
    cases hswf : reg.scopedWellFormed with
    | false => rfl
    | true =>
      unfold DynCallRegistry.scopedWellFormed at hswf
      rw [Bool.and_eq_true, List.all_eq_true] at hswf
      have hwf' : reg.wellFormed = true :=
        (DynCallRegistry.wellFormed_iff reg).mpr
          ⟨hswf.1, DynCallRegistry.nodup_of_noOverlaps_unscoped reg hun hswf.2⟩
      rw [hwf] at hwf'
      nomatch hwf'

/-- **Overlapping scoped registrations fail closed** (the location-scoped analogue of
`DynCallRegistry.findSite?_eq_none_of_duplicate`): if two entries in `pre ++ s₁ :: mid ++ s₂ :: post`
share `dynKey = key` and both match `(body, s)` (for example, an unscoped fallback site colliding
with a block-scoped site at that block), then `scopedWellFormed = false` and
`findSiteAt? body s key = none`. -/
theorem DynCallRegistry.findSiteAt?_eq_none_of_overlapping
    (pre mid post : List DynCallSite) {s₁ s₂ : DynCallSite}
    {body : CapturedMir} {s : MachineState} {key : DefPath × List RigidTy}
    (hk₁ : s₁.dynKey = key) (hk₂ : s₂.dynKey = key)
    (hm₁ : s₁.matchesLoc body s = true) (hm₂ : s₂.matchesLoc body s = true) :
    DynCallRegistry.scopedWellFormed (pre ++ s₁ :: mid ++ s₂ :: post) = false ∧
      DynCallRegistry.findSiteAt? (pre ++ s₁ :: mid ++ s₂ :: post) body s key = none := by
  have hlen : 2 ≤ ((pre ++ s₁ :: mid ++ s₂ :: post).filter
      (fun x => decide (x.dynKey = key) && x.matchesLoc body s)).length := by
    simp [List.filter_append, hk₁, hk₂, hm₁, hm₂]
    omega
  have hfind : DynCallRegistry.findSiteAt? (pre ++ s₁ :: mid ++ s₂ :: post) body s key = none := by
    unfold DynCallRegistry.findSiteAt?
    cases hf : (pre ++ s₁ :: mid ++ s₂ :: post).filter
        (fun x => decide (x.dynKey = key) && x.matchesLoc body s) with
    | nil => rfl
    | cons a rest =>
      cases rest with
      | nil => rw [hf] at hlen; simp at hlen
      | cons b rest' => rfl
  refine ⟨?_, hfind⟩
  cases hswf : DynCallRegistry.scopedWellFormed (pre ++ s₁ :: mid ++ s₂ :: post) with
  | false => rfl
  | true =>
    have hs₁ := (DynCallRegistry.findSiteAt?_eq_some_of_scopedWellFormed body s hswf
      (by simp : s₁ ∈ pre ++ s₁ :: mid ++ s₂ :: post) hm₁).1
    rw [hk₁, hfind] at hs₁
    nomatch hs₁

/-- Root-aware overlap check on two `DynCallSite` registrations for a verified root function with
`DefPath` `rootDefPath`: since `DynCallSite.matchesLoc` scopes `callSiteLoc? = none` to frames
executing `rootDefPath`, an unscoped root site and a callee-scoped site `some (dp, bb)` with
`dp ≠ rootDefPath` have disjoint location domains and never overlap. -/
def DynCallSite.overlapsFor (rootDefPath : DefPath) (s₁ s₂ : DynCallSite) : Bool :=
  decide (s₁.dynKey = s₂.dynKey) &&
    match s₁.callSiteLoc?, s₂.callSiteLoc? with
    | some l₁, some l₂ => decide (l₁ = l₂)
    | some (dp₁, _), none => decide (dp₁ = rootDefPath)
    | none, some (dp₂, _) => decide (rootDefPath = dp₂)
    | none, none => true

/-- Pairwise root-aware non-overlap check on a `DynCallRegistry`. -/
def DynCallRegistry.noOverlapsFor (rootDefPath : DefPath) : DynCallRegistry → Bool
  | [] => true
  | s :: rest => rest.all (fun s' => !s.overlapsFor rootDefPath s') && noOverlapsFor rootDefPath rest

/-- Root-aware location-scoped registry well-formedness for root body `rootDefPath`: strictly
generalizes `scopedWellFormed` (`scopedWellFormedFor_of_scopedWellFormed`) so a registry combining
an unscoped root site (`callSiteLoc? = none`) with callee-scoped sites (`some (calleePath, bb)`
for `calleePath ≠ rootDefPath`) is statically certified unambiguous. -/
def DynCallRegistry.scopedWellFormedFor (rootDefPath : DefPath) (reg : DynCallRegistry) : Bool :=
  reg.all DynCallSite.wellFormed && DynCallRegistry.noOverlapsFor rootDefPath reg

/-- Two registrations for the same call key that both match `(body, s)` satisfy
`overlapsFor body.defPath`. -/
theorem DynCallSite.overlapsFor_of_matchesLoc {x y : DynCallSite} {body : CapturedMir}
    {s : MachineState} (hk : x.dynKey = y.dynKey) (hx : x.matchesLoc body s = true)
    (hy : y.matchesLoc body s = true) : x.overlapsFor body.defPath y = true := by
  unfold DynCallSite.overlapsFor
  unfold DynCallSite.matchesLoc at hx hy
  rw [hk]
  cases hlx : x.callSiteLoc? with
  | none =>
    rw [hlx] at hx
    cases hly : y.callSiteLoc? with
    | none => simp
    | some ly =>
      rcases ly with ⟨dpy, bby⟩
      rw [hly] at hy
      simp only [decide_eq_true_eq, Prod.mk.injEq] at hx hy
      simp [← hx, hy.1]
  | some lx =>
    rcases lx with ⟨dpx, bbx⟩
    rw [hlx] at hx
    cases hly : y.callSiteLoc? with
    | none =>
      rw [hly] at hy
      simp only [decide_eq_true_eq, Prod.mk.injEq] at hx hy
      simp [← hx.1, hy]
    | some ly =>
      rw [hly] at hy
      simp only [decide_eq_true_eq] at hx hy
      simp [← hx, ← hy]

/-- Conservative root-oblivious `overlaps` over-approximates `overlapsFor rootDefPath`. -/
theorem DynCallSite.overlaps_of_overlapsFor {rootDefPath : DefPath} {x y : DynCallSite}
    (h : x.overlapsFor rootDefPath y = true) : x.overlaps y = true := by
  unfold DynCallSite.overlapsFor at h
  unfold DynCallSite.overlaps
  cases hx : x.callSiteLoc? with
  | none =>
    rw [hx] at h
    cases hy : y.callSiteLoc? with
    | none => simp_all
    | some ly => rcases ly with ⟨_, _⟩; rw [hy] at h; simp_all
  | some lx =>
    rcases lx with ⟨_, _⟩
    rw [hx] at h
    cases hy : y.callSiteLoc? with
    | none => rw [hy] at h; simp_all
    | some ly => rw [hy] at h; simp_all

theorem DynCallRegistry.noOverlapsFor_of_noOverlaps (rootDefPath : DefPath) :
    ∀ {reg : DynCallRegistry}, reg.noOverlaps = true → reg.noOverlapsFor rootDefPath = true
  | [], _ => rfl
  | s :: rest, h => by
    unfold DynCallRegistry.noOverlaps at h
    rw [Bool.and_eq_true, List.all_eq_true] at h
    unfold DynCallRegistry.noOverlapsFor
    rw [Bool.and_eq_true, List.all_eq_true]
    refine ⟨fun s' hs' => ?_, noOverlapsFor_of_noOverlaps rootDefPath h.2⟩
    cases hov : s.overlapsFor rootDefPath s' with
    | false => rfl
    | true =>
      have h' := h.1 s' hs'
      rw [DynCallSite.overlaps_of_overlapsFor hov] at h'
      nomatch h'

/-- `scopedWellFormedFor` strictly generalizes `scopedWellFormed` for every `rootDefPath`. -/
theorem DynCallRegistry.scopedWellFormedFor_of_scopedWellFormed (rootDefPath : DefPath)
    {reg : DynCallRegistry} (hwf : reg.scopedWellFormed = true) :
    reg.scopedWellFormedFor rootDefPath = true := by
  unfold DynCallRegistry.scopedWellFormed at hwf
  rw [Bool.and_eq_true] at hwf
  unfold DynCallRegistry.scopedWellFormedFor
  rw [Bool.and_eq_true]
  exact ⟨hwf.1, DynCallRegistry.noOverlapsFor_of_noOverlaps rootDefPath hwf.2⟩

/-- `scopedWellFormedFor` strictly generalizes key-disjoint `wellFormed`. -/
theorem DynCallRegistry.scopedWellFormedFor_of_wellFormed (rootDefPath : DefPath)
    {reg : DynCallRegistry} (hwf : reg.wellFormed = true) :
    reg.scopedWellFormedFor rootDefPath = true :=
  DynCallRegistry.scopedWellFormedFor_of_scopedWellFormed rootDefPath
    (DynCallRegistry.scopedWellFormed_of_wellFormed hwf)

theorem DynCallRegistry.noOverlapsFor_pairwise (rootDefPath : DefPath) :
    ∀ {reg : DynCallRegistry}, reg.noOverlapsFor rootDefPath = true →
      reg.Pairwise (fun a b => a.overlapsFor rootDefPath b = false)
  | [], _ => List.Pairwise.nil
  | x :: rest, h => by
    unfold DynCallRegistry.noOverlapsFor at h
    rw [Bool.and_eq_true, List.all_eq_true] at h
    refine List.Pairwise.cons (fun b hb => ?_) (noOverlapsFor_pairwise rootDefPath h.2)
    have hb' := h.1 b hb
    simpa using hb'

theorem DynCallRegistry.filter_eq_singleton_of_pairwiseFor {rootDefPath : DefPath}
    {p : DynCallSite → Bool} {site : DynCallSite}
    (hov : ∀ a b, p a = true → p b = true → a.overlapsFor rootDefPath b = true) :
    ∀ {reg : DynCallRegistry},
      reg.Pairwise (fun a b => a.overlapsFor rootDefPath b = false) →
      site ∈ reg → p site = true → reg.filter p = [site]
  | [], _, hmem, _ => nomatch hmem
  | x :: rest, hpw, hmem, hp => by
    rcases List.pairwise_cons.mp hpw with ⟨hx, hrest⟩
    rcases List.mem_cons.mp hmem with rfl | hmem'
    · have hnil : rest.filter p = [] := by
        refine DynCallRegistry.filter_eq_nil_of_forall fun a ha => ?_
        cases hpa : p a with
        | false => rfl
        | true =>
          have hxa := hx a ha
          rw [hov _ _ hp hpa] at hxa
          nomatch hxa
      simp only [List.filter_cons, hp, ite_true, hnil]
    · have hpx : p x = false := by
        cases hpx : p x with
        | false => rfl
        | true =>
          have hxs := hx site hmem'
          rw [hov _ _ hpx hp] at hxs
          nomatch hxs
      simp only [List.filter_cons, hpx, Bool.false_eq_true, ite_false]
      exact DynCallRegistry.filter_eq_singleton_of_pairwiseFor hov hrest hmem' hp

/-- **Unique root-aware location-scoped resolution**: in a `reg.scopedWellFormedFor body.defPath`
registry (including registries combining an unscoped root site `callSiteLoc? = none` with
callee-scoped sites `some (calleePath, bb)`), every member `site ∈ reg` is uniquely returned by
`findSiteAt?` at *every* state where `site.matchesLoc body s = true`, and is well formed. -/
theorem DynCallRegistry.findSiteAt?_eq_some_of_scopedWellFormedFor {reg : DynCallRegistry}
    {site : DynCallSite} (body : CapturedMir) (s : MachineState)
    (hwf : reg.scopedWellFormedFor body.defPath = true) (hmem : site ∈ reg)
    (hloc : site.matchesLoc body s = true) :
    reg.findSiteAt? body s site.dynKey = some site ∧ site.wellFormed = true := by
  unfold DynCallRegistry.scopedWellFormedFor at hwf
  rw [Bool.and_eq_true, List.all_eq_true] at hwf
  refine ⟨?_, hwf.1 site hmem⟩
  have hov : ∀ a b : DynCallSite,
      (decide (a.dynKey = site.dynKey) && a.matchesLoc body s) = true →
      (decide (b.dynKey = site.dynKey) && b.matchesLoc body s) = true →
      a.overlapsFor body.defPath b = true := by
    intro a b ha hb
    simp only [Bool.and_eq_true, decide_eq_true_eq] at ha hb
    exact DynCallSite.overlapsFor_of_matchesLoc (ha.1.trans hb.1.symm) ha.2 hb.2
  unfold DynCallRegistry.findSiteAt?
  rw [DynCallRegistry.filter_eq_singleton_of_pairwiseFor hov
    (DynCallRegistry.noOverlapsFor_pairwise body.defPath hwf.2) hmem (by simp [hloc])]

/-- **Root-aware overlapping registrations fail closed**: if two entries in
`pre ++ s₁ :: mid ++ s₂ :: post` share `dynKey = key` and both match `(body, s)` (for example, an
unscoped root site colliding with a block-scoped site on `body.defPath`), then
`scopedWellFormedFor body.defPath = false` and `findSiteAt? body s key = none`. -/
theorem DynCallRegistry.findSiteAt?_eq_none_of_overlappingFor
    (pre mid post : List DynCallSite) {s₁ s₂ : DynCallSite}
    {body : CapturedMir} {s : MachineState} {key : DefPath × List RigidTy}
    (hk₁ : s₁.dynKey = key) (hk₂ : s₂.dynKey = key)
    (hm₁ : s₁.matchesLoc body s = true) (hm₂ : s₂.matchesLoc body s = true) :
    DynCallRegistry.scopedWellFormedFor body.defPath (pre ++ s₁ :: mid ++ s₂ :: post) = false ∧
      DynCallRegistry.findSiteAt? (pre ++ s₁ :: mid ++ s₂ :: post) body s key = none := by
  have hfind := (DynCallRegistry.findSiteAt?_eq_none_of_overlapping pre mid post hk₁ hk₂ hm₁ hm₂).2
  refine ⟨?_, hfind⟩
  cases hswf : DynCallRegistry.scopedWellFormedFor body.defPath
      (pre ++ s₁ :: mid ++ s₂ :: post) with
  | false => rfl
  | true =>
    have hs₁ := (DynCallRegistry.findSiteAt?_eq_some_of_scopedWellFormedFor body s hswf
      (by simp : s₁ ∈ pre ++ s₁ :: mid ++ s₂ :: post) hm₁).1
    rw [hk₁, hfind] at hs₁
    nomatch hs₁

/-- Whenever no site in `reg` matches the active location `(body, s)`, `findSiteAt?` returns `none`
for every key. -/
theorem DynCallRegistry.findSiteAt?_eq_none_of_no_matching_scope (reg : DynCallRegistry)
    (body : CapturedMir) (s : MachineState) (key : DefPath × List RigidTy)
    (hno : ∀ site ∈ reg, site.matchesLoc body s = false) :
    reg.findSiteAt? body s key = none := by
  unfold DynCallRegistry.findSiteAt?
  rw [DynCallRegistry.filter_eq_nil_of_forall fun site hmem => by simp [hno site hmem]]

/-- **Complementary foreign-frame theorem to `findSiteAt?_eq_findSite?_of_unscoped`**: when every
site in `reg` is unscoped (`callSiteLoc? = none`) and `s` executes a foreign callee frame
(`(s.memory.activeCallee.getD body).defPath ≠ body.defPath`), `findSiteAt?` returns `none` for
*every* call key. -/
theorem DynCallRegistry.findSiteAt?_eq_none_of_unscoped_foreign_frame (reg : DynCallRegistry)
    (body : CapturedMir) (s : MachineState) (key : DefPath × List RigidTy)
    (hun : reg.all (fun site => site.callSiteLoc?.isNone) = true)
    (hforeign : (s.memory.activeCallee.getD body).defPath ≠ body.defPath) :
    reg.findSiteAt? body s key = none := by
  refine DynCallRegistry.findSiteAt?_eq_none_of_no_matching_scope reg body s key fun site hmem => ?_
  have hnone : site.callSiteLoc? = none :=
    Option.isNone_iff_eq_none.mp (List.all_eq_true.mp hun site hmem)
  simp [DynCallSite.matchesLoc, hnone, hforeign]

/-- Multi-site demand-gated dynamic-dispatch step (location-aware via `findSiteAt?` on direct calls):
- if the active step at `s` is a direct call uniquely resolved at `(body, s)` in `reg`,
  dispatch via that site's `dynDispatchStep`;
- if it demands an unregistered, ambiguously registered, or indirect (`FnPtr`) virtual call key
  (`dynSelfTrait?.isSome`), fail closed (`MirStepNode.unsupported`);
- otherwise step directly via `stepBranchPruned tbl.lookup`. -/
def dynRegistryStep (env : CompilerQueryEnv) (tbl : OpaqueCalleeTable) (reg : DynCallRegistry)
    (body : CapturedMir) (s : MachineState) : MirStepNode :=
  match demandedKey? body s with
  | some k =>
    match if isDirectCallAt body s then reg.findSiteAt? body s (k.defPath, k.typeArgs) else none with
    | some site => dynDispatchStep env tbl site body s
    | none =>
      if (dynSelfTrait? (k.defPath, k.typeArgs)).isSome then
        MirStepNode.unsupported
      else
        stepBranchPruned tbl.lookup body s
  | none =>
    stepBranchPruned tbl.lookup body s

/-- Every `dynRegistryStep` preserves `memory.callees` and `memory.traitImpls` (`FramesStep s`). -/
theorem dynRegistryStep_frames (env : CompilerQueryEnv) (tbl : OpaqueCalleeTable)
    (reg : DynCallRegistry) (body : CapturedMir) (s : MachineState) :
    FramesStep s (dynRegistryStep env tbl reg body s) := by
  unfold dynRegistryStep
  cases demandedKey? body s with
  | none => exact stepBranchPruned_frames tbl.lookup body s
  | some k =>
    dsimp only
    cases (if isDirectCallAt body s then reg.findSiteAt? body s (k.defPath, k.typeArgs) else none) with
    | some site => exact dynDispatchStep_frames env tbl site body s
    | none =>
      cases (dynSelfTrait? (k.defPath, k.typeArgs)).isSome with
      | true => exact True.intro
      | false => exact stepBranchPruned_frames tbl.lookup body s

/-- When the active step is a direct call demanding a uniquely matching site `site` at `(body, s)`,
`dynRegistryStep` is `dynDispatchStep env tbl site body s`. -/
theorem dynRegistryStep_eq_dynDispatchStep_of_findSite (env : CompilerQueryEnv)
    (tbl : OpaqueCalleeTable) (reg : DynCallRegistry) (body : CapturedMir) (s : MachineState)
    {k : CalleeKey} {site : DynCallSite} (hdir : isDirectCallAt body s = true)
    (hk : demandedKey? body s = some k)
    (hfind : reg.findSiteAt? body s (k.defPath, k.typeArgs) = some site) :
    dynRegistryStep env tbl reg body s = dynDispatchStep env tbl site body s := by
  simp [dynRegistryStep, hdir, hk, hfind]

/-- Any virtual call key without a unique direct-call entry in `reg` at `(body, s)` (unregistered,
ambiguous, or indirect `FnPtr`) fails closed (`MirStepNode.unsupported`). -/
theorem dynRegistryStep_of_unregistered (env : CompilerQueryEnv) (tbl : OpaqueCalleeTable)
    (reg : DynCallRegistry) (body : CapturedMir) (s : MachineState) {k : CalleeKey}
    (hk : demandedKey? body s = some k)
    (hfind : (if isDirectCallAt body s then reg.findSiteAt? body s (k.defPath, k.typeArgs)
      else none) = none)
    (hdyn : (dynSelfTrait? (k.defPath, k.typeArgs)).isSome = true) :
    dynRegistryStep env tbl reg body s = MirStepNode.unsupported := by
  simp [dynRegistryStep, hk, hfind, hdyn]

/-- **Unscoped registries never dispatch in another function's frame** (multi-site registry
generalization of `dynDemandStep_of_unscoped_foreign_frame`): when all entries of `reg` have
`callSiteLoc? = none` and `s` executes a foreign callee frame, `dynRegistryStep` is either the
branch-pruned trusted step or fails closed on the unregistered virtual call — never reinterpreting
the callee's `vtableLocal`. -/
theorem dynRegistryStep_of_unscoped_foreign_frame (env : CompilerQueryEnv) (tbl : OpaqueCalleeTable)
    (reg : DynCallRegistry) {body : CapturedMir} {s : MachineState}
    (hun : reg.all (fun site => site.callSiteLoc?.isNone) = true)
    (hforeign : (s.memory.activeCallee.getD body).defPath ≠ body.defPath) :
    dynRegistryStep env tbl reg body s = stepBranchPruned tbl.lookup body s ∨
      dynRegistryStep env tbl reg body s = MirStepNode.unsupported := by
  unfold dynRegistryStep
  cases demandedKey? body s with
  | none => exact Or.inl rfl
  | some k =>
    have hf : reg.findSiteAt? body s (k.defPath, k.typeArgs) = none :=
      DynCallRegistry.findSiteAt?_eq_none_of_unscoped_foreign_frame reg body s _ hun hforeign
    simp only [hf, ite_self]
    cases (dynSelfTrait? (k.defPath, k.typeArgs)).isSome with
    | true => exact Or.inr rfl
    | false => exact Or.inl rfl

/-- **Exhaustive `StepView` classification of `dynRegistryStep`** (unconditional): at *every*
state `s`, `dynRegistryStep` exclusively:
1. equals the branch-pruned trusted step `stepBranchPruned tbl.lookup body s` (hence `stepMirFn`
   under `tbl.toList = s.memory.callees`),
2. faults (`.fault fk`, fail-closed `.unsupported` or `.ub`),
3. traps on a Schema-13 CFI type-id mismatch (`.ret .abort`) at a uniquely resolved well-formed
   site,
4. emits an unlinked external call to the vtable-resolved `target = (req.defPath, req.typeArgs)` of
   a uniquely resolved well-formed site, or
5. takes a validated redirected `.step s'` equal to
   `stepBranchPruned (redirectResolver tbl site.dynKey target) body s`.

In particular, a virtual dispatch step can **never** fabricate a normal return `.ret (.normal _)`
or `.cont _ (.halted _)`. -/
theorem dynRegistryStep_view_spec (env : CompilerQueryEnv) (tbl : OpaqueCalleeTable)
    (reg : DynCallRegistry) (body : CapturedMir) (s : MachineState) :
    dynRegistryStep env tbl reg body s = stepBranchPruned tbl.lookup body s ∨
    (∃ fk, viewStepNode (dynRegistryStep env tbl reg body s) = .fault fk) ∨
    (∃ k site vt, isDirectCallAt body s = true ∧ demandedKey? body s = some k ∧
      reg.findSiteAt? body s (k.defPath, k.typeArgs) = some site ∧ site.wellFormed = true ∧
      site.vtablePtr? s = some vt ∧ resolveDynTarget env site vt = .err .cfiTypeIdMismatch ∧
      dynRegistryStep env tbl reg body s = MirStepNode.retOutcome .abort) ∨
    (∃ k site vt target req, isDirectCallAt body s = true ∧ demandedKey? body s = some k ∧
      reg.findSiteAt? body s (k.defPath, k.typeArgs) = some site ∧ site.wellFormed = true ∧
      site.vtablePtr? s = some vt ∧ resolveDynTarget env site vt = .ok target ∧
      vtableTargetAgrees site target = true ∧
      viewStepNode (dynRegistryStep env tbl reg body s) = .external req ∧
      req.defPath = target.1 ∧ req.typeArgs = target.2) ∨
    (∃ k site vt target s', isDirectCallAt body s = true ∧ demandedKey? body s = some k ∧
      reg.findSiteAt? body s (k.defPath, k.typeArgs) = some site ∧ site.wellFormed = true ∧
      site.vtablePtr? s = some vt ∧ resolveDynTarget env site vt = .ok target ∧
      vtableTargetAgrees site target = true ∧
      dynRegistryStep env tbl reg body s = MirStepNode.step s' ∧
      stepBranchPruned (redirectResolver tbl site.dynKey target) body s = MirStepNode.step s') := by
  unfold dynRegistryStep
  cases hk : demandedKey? body s with
  | none => exact Or.inl rfl
  | some k =>
    dsimp only
    cases hdir : isDirectCallAt body s with
    | false =>
      simp only [Bool.false_eq_true, ite_false]
      cases hv : (dynSelfTrait? (k.defPath, k.typeArgs)).isSome with
      | true => exact Or.inr (Or.inl ⟨.unsupported, by simp [MirStepNode.unsupported, MirStepNode.fail, viewStepNode]⟩)
      | false => exact Or.inl rfl
    | true =>
      simp only [ite_true]
      cases hf : reg.findSiteAt? body s (k.defPath, k.typeArgs) with
      | none =>
        cases hv : (dynSelfTrait? (k.defPath, k.typeArgs)).isSome with
        | true => exact Or.inr (Or.inl ⟨.unsupported, by simp [MirStepNode.unsupported, MirStepNode.fail, viewStepNode]⟩)
        | false => exact Or.inl rfl
      | some site =>
        dsimp only
        have hkey : site.dynKey = (k.defPath, k.typeArgs) :=
          (DynCallRegistry.findSiteAt?_spec hf).2.1
        have hloc : site.matchesLoc body s = true :=
          (DynCallRegistry.findSiteAt?_spec hf).2.2
        have hdk : demandsDynKey site.dynKey body s = true := by
          simp [demandsDynKey, hk, hkey]
        unfold dynDispatchStep
        cases hwf : site.wellFormed with
        | false =>
          exact Or.inr (Or.inl ⟨.unsupported, by simp [MirStepNode.unsupported, MirStepNode.fail, viewStepNode]⟩)
        | true =>
          simp only [ite_true]
          cases hvt : site.vtablePtr? s with
          | none =>
            exact Or.inr (Or.inl ⟨.ub, by simp [MirStepNode.fail, viewStepNode]⟩)
          | some vt =>
            dsimp only
            cases hr : resolveDynTarget env site vt with
            | unsupported _ =>
              exact Or.inr (Or.inl ⟨.unsupported, by simp [MirStepNode.unsupported, MirStepNode.fail, viewStepNode]⟩)
            | err e =>
              cases e with
              | cfiTypeIdMismatch =>
                exact Or.inr (Or.inr (Or.inl ⟨k, site, vt, by simp, rfl,
                  by simp [hf], by simp [hwf], by simp [hvt], by simp [hr], rfl⟩))
              | vtableSlotMethodMismatch _ =>
                exact Or.inr (Or.inl ⟨.unsupported, by simp [MirStepNode.unsupported, MirStepNode.fail, viewStepNode]⟩)
              | _ =>
                exact Or.inr (Or.inl ⟨.ub, by simp [MirStepNode.fail, viewStepNode]⟩)
            | ok target =>
              dsimp only
              cases hta : vtableTargetAgrees site target with
              | false =>
                exact Or.inr (Or.inl ⟨.unsupported, by simp [MirStepNode.unsupported, MirStepNode.fail, viewStepNode]⟩)
              | true =>
                simp only [ite_true]
                have hact_some : ∃ term cb, activeTerminator? body s = some (term, cb) := by
                  unfold demandedKey? at hk
                  cases hact : activeTerminator? body s with
                  | none => rw [hact] at hk; nomatch hk
                  | some p => exact ⟨p.1, p.2, rfl⟩
                obtain ⟨term, cb, hact⟩ := hact_some
                have hdp : stepDynPruned tbl site target body s =
                    stepDynTerminator (redirectResolver tbl site.dynKey target) site target s
                      term cb := by
                  simp [stepDynPruned, hdk, hloc, hact]
                rcases stepDynTerminator_view_spec (redirectResolver tbl site.dynKey target) site
                    target s term cb with ⟨fk, hfk⟩ | ⟨req, hreq, hd1, hd2⟩ | ⟨s', hs1, hs2⟩
                · exact Or.inr (Or.inl ⟨fk, by rw [hdp]; exact hfk⟩)
                · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨k, site, vt, target, req, by simp,
                    rfl, by simp [hf], by simp [hwf], by simp [hvt], by simp [hr],
                    by simp [hta], by rw [hdp]; exact hreq, hd1, hd2⟩)))
                · have hsp : stepDynPruned tbl site target body s = MirStepNode.step s' := by
                    rw [hdp]; exact hs1
                  exact Or.inr (Or.inr (Or.inr (Or.inr ⟨k, site, vt, target, s', by simp,
                    rfl, by simp [hf], by simp [hwf], by simp [hvt], by simp [hr],
                    by simp [hta], hsp, stepBranchPruned_redirect_of_stepDynPruned_step hsp⟩)))

/-- **Normal returns in `dynRegistryStep` come exclusively from the trusted machine**: whenever
`dynRegistryStep` produces `.ret (.normal p)` or `.cont obs (.halted (.normal p))`, the step is
literally `stepBranchPruned tbl.lookup body s` (never a virtual dispatch step). -/
theorem dynRegistryStep_normal_return_eq_branchPruned (env : CompilerQueryEnv)
    (tbl : OpaqueCalleeTable) (reg : DynCallRegistry) (body : CapturedMir) (s : MachineState)
    (p : Value × Memory)
    (h : viewStepNode (dynRegistryStep env tbl reg body s) = .ret (.normal p) ∨
      ∃ obs, viewStepNode (dynRegistryStep env tbl reg body s) = .cont obs (.halted (.normal p))) :
    dynRegistryStep env tbl reg body s = stepBranchPruned tbl.lookup body s := by
  rcases dynRegistryStep_view_spec env tbl reg body s with
    heq | ⟨fk, hv⟩ | ⟨_, _, _, _, _, _, _, _, _, hab⟩ | ⟨_, _, _, _, req, _, _, _, _, _, _, _, hv, _, _⟩ |
      ⟨_, _, _, _, s', _, _, _, _, _, _, _, hs, _⟩
  · exact heq
  · rcases h with hr | ⟨_, hr⟩ <;> (rw [hv] at hr; nomatch hr)
  · rcases h with hr | ⟨_, hr⟩ <;> (rw [hab] at hr; simp [MirStepNode.retOutcome, viewStepNode] at hr)
  · rcases h with hr | ⟨_, hr⟩ <;> (rw [hv] at hr; nomatch hr)
  · rcases h with hr | ⟨_, hr⟩ <;> (rw [hs] at hr; simp [MirStepNode.step, viewStepNode] at hr)

/-- Fuel-bounded multi-step evaluation with a `DynCallRegistry`. -/
def evalDynRegistryWithOpaqueCallees (env : CompilerQueryEnv) (tbl : OpaqueCalleeTable)
    (reg : DynCallRegistry) (body : CapturedMir) (fuel : Nat) (s : MachineState) : RunResult :=
  runSteps (dynRegistryStep env tbl reg body) fuel s []

/-- A singleton registry `[site]` steps identically to single-site `dynDemandStep` (for both
unscoped and `callSiteLoc?`-scoped sites, including `isDirectCallAt` gating). -/
theorem dynRegistryStep_singleton (env : CompilerQueryEnv) (tbl : OpaqueCalleeTable)
    (site : DynCallSite) (body : CapturedMir) (s : MachineState) :
    dynRegistryStep env tbl [site] body s = dynDemandStep env tbl site body s := by
  unfold dynRegistryStep dynDemandStep demandsUnregisteredDyn demandsDynSite DynCallRegistry.findSiteAt?
  cases hk : demandedKey? body s with
  | none => rfl
  | some k =>
    dsimp only
    cases hdir : isDirectCallAt body s with
    | false =>
      simp only [Bool.false_and, Bool.false_eq_true, ite_false, Bool.not_false, Bool.and_true]
    | true =>
      simp only [Bool.true_and, ite_true]
      have hcomm : (decide (site.dynKey = (k.defPath, k.typeArgs)) && site.matchesLoc body s) =
          (decide ((k.defPath, k.typeArgs) = site.dynKey) && site.matchesLoc body s) := by
        congr 1
        by_cases heq : (k.defPath, k.typeArgs) = site.dynKey
        · simp [heq]
        · have hne : site.dynKey ≠ (k.defPath, k.typeArgs) := fun h => heq h.symm
          simp [heq, hne]
      rw [List.filter_cons, List.filter_nil, hcomm]
      by_cases hb : (decide ((k.defPath, k.typeArgs) = site.dynKey) && site.matchesLoc body s) = true
      · simp [hb]
      · simp [hb]

/-- Single-site corollary of `dynRegistryStep_normal_return_eq_branchPruned`. -/
theorem dynDemandStep_normal_return_eq_branchPruned (env : CompilerQueryEnv)
    (tbl : OpaqueCalleeTable) (site : DynCallSite) (body : CapturedMir) (s : MachineState)
    (p : Value × Memory)
    (h : viewStepNode (dynDemandStep env tbl site body s) = .ret (.normal p) ∨
      ∃ obs, viewStepNode (dynDemandStep env tbl site body s) = .cont obs (.halted (.normal p))) :
    dynDemandStep env tbl site body s = stepBranchPruned tbl.lookup body s := by
  rw [← dynRegistryStep_singleton] at h ⊢
  exact dynRegistryStep_normal_return_eq_branchPruned env tbl [site] body s p h

/-- Multi-step evaluation with a singleton registry `[site]` equals `evalDynWithOpaqueCallees`. -/
theorem evalDynRegistryWithOpaqueCallees_singleton (env : CompilerQueryEnv)
    (tbl : OpaqueCalleeTable) (site : DynCallSite) (body : CapturedMir)
    (fuel : Nat) (s : MachineState) :
    evalDynRegistryWithOpaqueCallees env tbl [site] body fuel s =
      evalDynWithOpaqueCallees env tbl site body fuel s := by
  unfold evalDynRegistryWithOpaqueCallees evalDynWithOpaqueCallees
  exact runSteps_congr_visited fuel s [] (fun s' _ => dynRegistryStep_singleton env tbl site body s')

/-- A step that demands no registered site and no unregistered virtual call is
literally the trusted `stepMirFn` under the `memory.callees` frame condition. -/
theorem dynRegistryStep_eq_trusted_of_no_dyn (env : CompilerQueryEnv) (tbl : OpaqueCalleeTable)
    (reg : DynCallRegistry) (body : CapturedMir) (s : MachineState)
    (hnone : ∀ k, demandedKey? body s = some k →
      reg.findSiteAt? body s (k.defPath, k.typeArgs) = none ∧
      (dynSelfTrait? (k.defPath, k.typeArgs)).isSome = false)
    (hframe : tbl.toList = s.memory.callees) :
    dynRegistryStep env tbl reg body s = stepMirFn body s := by
  unfold dynRegistryStep
  cases hk : demandedKey? body s with
  | none => exact stepBranchPruned_eq_trusted tbl body s hframe
  | some k =>
    obtain ⟨hfind, hvirt⟩ := hnone k hk
    simp only [hfind, ite_self, hvirt, Bool.false_eq_true, ite_false]
    exact stepBranchPruned_eq_trusted tbl body s hframe

/-- **Unconditional multi-step trusted agreement for non-`dyn` registry runs**: when no visited
state along the run demands a registered site or virtual call and `s.memory.callees = tbl.toList`,
`evalDynRegistryWithOpaqueCallees` equals the iterated trusted `stepMirFn`. -/
theorem evalDynRegistryWithOpaqueCallees_eq_trusted_of_no_dyn_unconditional
    (env : CompilerQueryEnv) (tbl : OpaqueCalleeTable) (reg : DynCallRegistry)
    (body : CapturedMir) (fuel : Nat) (s : MachineState) (hcallees : s.memory.callees = tbl.toList)
    (hnodyn : ∀ s' ∈ runVisited (stepBranchPruned tbl.lookup body) fuel s,
      ∀ k, demandedKey? body s' = some k →
        reg.findSiteAt? body s' (k.defPath, k.typeArgs) = none ∧
        (dynSelfTrait? (k.defPath, k.typeArgs)).isSome = false) :
    evalDynRegistryWithOpaqueCallees env tbl reg body fuel s =
      runSteps (stepMirFn body) fuel s [] := by
  have h_opaque : evalDynRegistryWithOpaqueCallees env tbl reg body fuel s =
      evalWithOpaqueCallees tbl body fuel s := by
    unfold evalDynRegistryWithOpaqueCallees evalWithOpaqueCallees
    refine runSteps_congr_visited fuel s [] fun s' hs' => ?_
    unfold dynRegistryStep
    cases hk : demandedKey? body s' with
    | none => rfl
    | some k =>
      obtain ⟨hfind, hvirt⟩ := hnodyn s' hs' k hk
      simp only [hfind, ite_self, hvirt, Bool.false_eq_true, ite_false]
  rw [h_opaque]
  exact evalWithOpaqueCallees_eq_trusted_unconditional tbl body fuel s hcallees

/-- Decidable per-state preservation certificate for `dynRegistryStep`. -/
def dynRegistryStepPreservedB (env₁ : CompilerQueryEnv) (narrowTbl fullTbl : OpaqueCalleeTable)
    (reg : DynCallRegistry) (body : CapturedMir) (s : MachineState) : Bool :=
  match demandedKey? body s with
  | none => true
  | some k =>
    match if isDirectCallAt body s then reg.findSiteAt? body s (k.defPath, k.typeArgs) else none with
    | some site =>
      if site.wellFormed then
        match site.vtablePtr? s with
        | none => true
        | some vt =>
          match resolveDynTarget env₁ site vt with
          | .ok target =>
            if vtableTargetAgrees site target then
              decide (k.apply (redirectResolver narrowTbl site.dynKey target) =
                k.apply (redirectResolver fullTbl site.dynKey target))
            else true
          | .err _ => true
          | .unsupported _ => false
      else true
    | none =>
      if (dynSelfTrait? (k.defPath, k.typeArgs)).isSome then true
      else decide (narrowTbl.lookupKey k = fullTbl.lookupKey k)

/-- Single-step preservation of `dynRegistryStep` when `dynRegistryStepPreservedB` holds. -/
theorem dynRegistryStep_preserved_of_check {env₁ env₂ : CompilerQueryEnv}
    {narrowTbl fullTbl : OpaqueCalleeTable} {reg : DynCallRegistry}
    {body : CapturedMir} {s : MachineState} (h : EnvExtends env₁ env₂)
    (hc : dynRegistryStepPreservedB env₁ narrowTbl fullTbl reg body s = true) :
    dynRegistryStep env₂ narrowTbl reg body s = dynRegistryStep env₁ fullTbl reg body s := by
  unfold dynRegistryStep
  unfold dynRegistryStepPreservedB at hc
  cases hk : demandedKey? body s with
  | none =>
    exact stepBranchPruned_congr body s (fun k hk' => by rw [hk] at hk'; nomatch hk')
  | some k =>
    rw [hk] at hc
    dsimp only at hc ⊢
    cases hf : (if isDirectCallAt body s then reg.findSiteAt? body s (k.defPath, k.typeArgs)
        else none) with
    | some site =>
      rw [hf] at hc
      dsimp only at hc
      apply dynDispatchStep_preserved h
      · intro hwf vt hvt m hm
        simp only [hwf, ite_true, hvt, hm, Bool.false_eq_true] at hc
      · intro hwf vt target hvt hr hta k' hk'
        rw [hk] at hk'
        cases hk'
        simp only [hwf, ite_true, hvt, hr, hta, decide_eq_true_eq] at hc
        exact hc
    | none =>
      rw [hf] at hc
      dsimp only at hc
      cases hv : (dynSelfTrait? (k.defPath, k.typeArgs)).isSome with
      | true => rfl
      | false =>
        simp only [Bool.false_eq_true, ite_false]
        simp only [hv, Bool.false_eq_true, ite_false, decide_eq_true_eq] at hc
        exact stepBranchPruned_congr body s (fun k' hk' => by
          rw [hk] at hk'
          cases hk'
          exact hc)

/-- Multi-step preservation of `evalDynRegistryWithOpaqueCallees` checked along the
narrowed run (`runVisited` steps only `narrowTbl`). -/
theorem evalDynRegistryWithOpaqueCallees_preserved_of_narrow_check
    {env₁ env₂ : CompilerQueryEnv} {narrowTbl fullTbl : OpaqueCalleeTable}
    {reg : DynCallRegistry} {body : CapturedMir}
    (h : EnvExtends env₁ env₂) (fuel : Nat) (s : MachineState)
    (hcheck : (runVisited (dynRegistryStep env₂ narrowTbl reg body) fuel s).all
      (dynRegistryStepPreservedB env₁ narrowTbl fullTbl reg body) = true) :
    evalDynRegistryWithOpaqueCallees env₂ narrowTbl reg body fuel s =
      evalDynRegistryWithOpaqueCallees env₁ fullTbl reg body fuel s := by
  symm
  exact runSteps_congr_visited fuel s []
    (fun s' hs' => (dynRegistryStep_preserved_of_check h (List.all_eq_true.mp hcheck s' hs')).symm)

/-! #### `O(1)` certificate-driven dynamic-dispatch cone narrowing (`fullTbl`-free demand collection)

`dynStepPreservedB` and `dynRegistryStepPreservedB` embed `fullTbl` inside a Boolean check, which is
convenient on tiny fixture tables (`decide +kernel`) but unfolds `fullTbl.toList` in the kernel (`O(M)`
heartbeats). The collectors below depend *only* on `(env₂, narrowTbl, reg)` (zero occurrences of
`env₁` or `fullTbl`), so a client computes the demanded `(site, vt)` query pairs and redirected
concrete `CalleeKey`s once over `narrowTbl` and discharges `narrowTbl.lookupKey ck = fullTbl.lookupKey ck`
in `O(1)` heartbeats via `OpaqueCalleeTable` certificates (`o1Dyn` in the heartbeat gate). -/

/-- The `(site, vt)` query demand issued by `dynRegistryStep` at `s` (if any). -/
def dynRegistryStepQuery? (reg : DynCallRegistry) (body : CapturedMir) (s : MachineState) :
    Option (DynCallSite × ProvenancePtr) :=
  match demandedKey? body s with
  | some k =>
    match if isDirectCallAt body s then reg.findSiteAt? body s (k.defPath, k.typeArgs) else none with
    | some site =>
      if site.wellFormed then (site.vtablePtr? s).map (fun vt => (site, vt)) else none
    | none => none
  | none => none

/-- The effective `CalleeKey` consulted in `OpaqueCalleeTable` by `dynRegistryStep` at `s` (already
redirected to `(target.1, target.2)` on a validated resolved virtual call). -/
def dynRegistryStepCalleeKey? (env : CompilerQueryEnv) (reg : DynCallRegistry)
    (body : CapturedMir) (s : MachineState) : Option CalleeKey :=
  match demandedKey? body s with
  | some k =>
    match if isDirectCallAt body s then reg.findSiteAt? body s (k.defPath, k.typeArgs) else none with
    | some site =>
      if site.wellFormed then
        match site.vtablePtr? s with
        | some vt =>
          match resolveDynTarget env site vt with
          | .ok target =>
            if vtableTargetAgrees site target then
              some ⟨k.callerLayouts, target.1, target.2, k.extraTraitImpls⟩
            else none
          | _ => none
        | none => none
      else none
    | none =>
      if (dynSelfTrait? (k.defPath, k.typeArgs)).isSome then none else some k
  | none => none

/-- All `(site, vt)` query demands issued along `evalDynRegistryWithOpaqueCallees env tbl reg`. -/
def dynRegistryDemandedQueries (env : CompilerQueryEnv) (tbl : OpaqueCalleeTable)
    (reg : DynCallRegistry) (body : CapturedMir) (fuel : Nat) (s : MachineState) :
    List (DynCallSite × ProvenancePtr) :=
  (runVisited (dynRegistryStep env tbl reg body) fuel s).filterMap
    (dynRegistryStepQuery? reg body)

/-- All effective `CalleeKey`s consulted in `tbl` along `evalDynRegistryWithOpaqueCallees env tbl reg`. -/
def dynRegistryDemandedCalleeKeys (env : CompilerQueryEnv) (tbl : OpaqueCalleeTable)
    (reg : DynCallRegistry) (body : CapturedMir) (fuel : Nat) (s : MachineState) :
    List CalleeKey :=
  (runVisited (dynRegistryStep env tbl reg body) fuel s).filterMap
    (dynRegistryStepCalleeKey? env reg body)

theorem mem_filterMap_of_eq {α β : Type} {f : α → Option β} {a : α} {b : β} :
    ∀ {xs : List α}, a ∈ xs → f a = some b → b ∈ xs.filterMap f
  | [], hmem, _ => nomatch hmem
  | x :: xs, hmem, hf => by
    rcases List.mem_cons.mp hmem with rfl | hrest
    · rw [List.filterMap_cons_some hf]
      exact List.Mem.head _
    · have ih := mem_filterMap_of_eq hrest hf
      cases hfx : f x with
      | none =>
        rw [List.filterMap_cons_none hfx]
        exact ih
      | some _ =>
        rw [List.filterMap_cons_some hfx]
        exact List.Mem.tail _ ih

/-- Single-step preservation of `dynRegistryStep` from propositional per-step query & key agreement. -/
theorem dynRegistryStep_preserved_of_stepDemands {env₁ env₂ : CompilerQueryEnv}
    {narrowTbl fullTbl : OpaqueCalleeTable} {reg : DynCallRegistry}
    {body : CapturedMir} {s : MachineState} (h : EnvExtends env₁ env₂)
    (hsup : ∀ p, dynRegistryStepQuery? reg body s = some p →
      ∀ m, resolveDynTarget env₁ p.1 p.2 ≠ .unsupported m)
    (hkey : ∀ ck, dynRegistryStepCalleeKey? env₂ reg body s = some ck →
      narrowTbl.lookupKey ck = fullTbl.lookupKey ck) :
    dynRegistryStep env₂ narrowTbl reg body s = dynRegistryStep env₁ fullTbl reg body s := by
  unfold dynRegistryStep
  cases hk : demandedKey? body s with
  | none =>
    exact stepBranchPruned_congr body s (fun k hk' => by rw [hk] at hk'; nomatch hk')
  | some k =>
    dsimp only
    cases hf : (if isDirectCallAt body s then reg.findSiteAt? body s (k.defPath, k.typeArgs)
        else none) with
    | none =>
      cases hv : (dynSelfTrait? (k.defPath, k.typeArgs)).isSome with
      | true => rfl
      | false =>
        simp only [Bool.false_eq_true, ite_false]
        apply stepBranchPruned_congr body s
        intro k' hk'
        rw [hk] at hk'
        cases hk'
        exact hkey k (by simp [dynRegistryStepCalleeKey?, hk, hf, hv])
    | some site =>
      have hfind : reg.findSiteAt? body s (k.defPath, k.typeArgs) = some site := by
        cases hdir : isDirectCallAt body s <;> simp_all
      have hdkey : (k.defPath, k.typeArgs) = site.dynKey :=
        (DynCallRegistry.findSiteAt?_spec hfind).2.1.symm
      apply dynDispatchStep_preserved h
      · intro hwf vt hvt
        exact hsup (site, vt) (by simp [dynRegistryStepQuery?, hk, hf, hwf, hvt])
      · intro hwf vt target hvt hr₁ hta k' hk'
        rw [hk] at hk'
        cases hk'
        have hr₂ : resolveDynTarget env₂ site vt = .ok target :=
          (resolveDynTarget_mono h site vt
            (hsup (site, vt) (by simp [dynRegistryStepQuery?, hk, hf, hwf, hvt]))).trans hr₁
        rw [redirectResolver_apply_hit narrowTbl site.dynKey target hdkey,
          redirectResolver_apply_hit fullTbl site.dynKey target hdkey]
        exact hkey ⟨k.callerLayouts, target.1, target.2, k.extraTraitImpls⟩
          (by simp [dynRegistryStepCalleeKey?, hk, hf, hwf, hvt, hr₂, hta])

/-- **`O(1)` certificate-compatible dynamic-dispatch cone narrowing (`DynCallRegistry`)**:
neither `dynRegistryDemandedQueries` nor `dynRegistryDemandedCalleeKeys` mentions `env₁` or
`fullTbl`, so each demanded key's `narrowTbl.lookupKey ck = fullTbl.lookupKey ck` obligation can be
discharged in `O(1)` heartbeats via `OpaqueCalleeTable` lookup certificates without ever unfolding
`fullTbl.toList`. -/
theorem evalDynRegistryWithOpaqueCallees_cone_narrow_of_demands
    {env₁ env₂ : CompilerQueryEnv} {narrowTbl fullTbl : OpaqueCalleeTable}
    {reg : DynCallRegistry} {body : CapturedMir}
    (h : EnvExtends env₁ env₂) (fuel : Nat) (s : MachineState)
    (hsup : ∀ p ∈ dynRegistryDemandedQueries env₂ narrowTbl reg body fuel s,
      ∀ m, resolveDynTarget env₁ p.1 p.2 ≠ .unsupported m)
    (hkeys : ∀ ck ∈ dynRegistryDemandedCalleeKeys env₂ narrowTbl reg body fuel s,
      narrowTbl.lookupKey ck = fullTbl.lookupKey ck) :
    evalDynRegistryWithOpaqueCallees env₂ narrowTbl reg body fuel s =
      evalDynRegistryWithOpaqueCallees env₁ fullTbl reg body fuel s := by
  symm
  refine runSteps_congr_visited fuel s [] fun s' hs' => ?_
  symm
  exact dynRegistryStep_preserved_of_stepDemands h
    (fun p hp => hsup p (mem_filterMap_of_eq hs' hp))
    (fun ck hck => hkeys ck (mem_filterMap_of_eq hs' hck))

/-- Single-site corollary of `evalDynRegistryWithOpaqueCallees_cone_narrow_of_demands`. -/
theorem evalDynWithOpaqueCallees_cone_narrow_of_demands
    {env₁ env₂ : CompilerQueryEnv} {narrowTbl fullTbl : OpaqueCalleeTable}
    {site : DynCallSite} {body : CapturedMir}
    (h : EnvExtends env₁ env₂) (fuel : Nat) (s : MachineState)
    (hsup : ∀ p ∈ dynRegistryDemandedQueries env₂ narrowTbl [site] body fuel s,
      ∀ m, resolveDynTarget env₁ p.1 p.2 ≠ .unsupported m)
    (hkeys : ∀ ck ∈ dynRegistryDemandedCalleeKeys env₂ narrowTbl [site] body fuel s,
      narrowTbl.lookupKey ck = fullTbl.lookupKey ck) :
    evalDynWithOpaqueCallees env₂ narrowTbl site body fuel s =
      evalDynWithOpaqueCallees env₁ fullTbl site body fuel s := by
  rw [← evalDynRegistryWithOpaqueCallees_singleton, ← evalDynRegistryWithOpaqueCallees_singleton]
  exact evalDynRegistryWithOpaqueCallees_cone_narrow_of_demands h fuel s hsup hkeys

theorem of_mem_filterMap {α β : Type} {f : α → Option β} {b : β} :
    ∀ {xs : List α}, b ∈ xs.filterMap f → ∃ a ∈ xs, f a = some b
  | [], hmem => nomatch hmem
  | x :: xs, hmem => by
    cases hfx : f x with
    | none =>
      rw [List.filterMap_cons_none hfx] at hmem
      obtain ⟨a, ha, hfa⟩ := of_mem_filterMap hmem
      exact ⟨a, List.Mem.tail _ ha, hfa⟩
    | some y =>
      rw [List.filterMap_cons_some hfx] at hmem
      rcases List.mem_cons.mp hmem with rfl | hrest
      · exact ⟨x, List.Mem.head _, hfx⟩
      · obtain ⟨a, ha, hfa⟩ := of_mem_filterMap hrest
        exact ⟨a, List.Mem.tail _ ha, hfa⟩

/-- Any key emitted by `dynRegistryStepCalleeKey?` at `s` carries `s.memory.traitImpls`. -/
theorem dynRegistryStepCalleeKey?_extraTraitImpls {env : CompilerQueryEnv} {reg : DynCallRegistry}
    {body : CapturedMir} {s : MachineState} {ck : CalleeKey}
    (h : dynRegistryStepCalleeKey? env reg body s = some ck) :
    ck.extraTraitImpls = s.memory.traitImpls := by
  unfold dynRegistryStepCalleeKey? at h
  cases hk : demandedKey? body s with
  | none => rw [hk] at h; nomatch h
  | some k =>
    have hti : k.extraTraitImpls = s.memory.traitImpls := demandedKey?_extraTraitImpls hk
    rw [hk] at h
    dsimp only at h
    cases hf : (if isDirectCallAt body s then reg.findSiteAt? body s (k.defPath, k.typeArgs)
        else none) with
    | none =>
      rw [hf] at h
      cases hv : (dynSelfTrait? (k.defPath, k.typeArgs)).isSome with
      | true => rw [hv] at h; nomatch h
      | false =>
        rw [hv] at h
        injection h with hck
        rw [← hck, hti]
    | some site =>
      rw [hf] at h
      dsimp only at h
      cases hwf : site.wellFormed with
      | false => simp [hwf] at h
      | true =>
        simp only [hwf, ite_true] at h
        cases hvt : site.vtablePtr? s with
        | none => rw [hvt] at h; nomatch h
        | some vt =>
          rw [hvt] at h
          dsimp only at h
          cases hr : resolveDynTarget env site vt with
          | err _ => rw [hr] at h; nomatch h
          | unsupported _ => rw [hr] at h; nomatch h
          | ok target =>
            rw [hr] at h
            dsimp only at h
            cases hta : vtableTargetAgrees site target with
            | false => simp [hta] at h
            | true =>
              simp only [hta, ite_true, Option.some.injEq] at h
              rw [← h, hti]

/-- **Every key in `dynRegistryDemandedCalleeKeys` carries the initial state's `memory.traitImpls`**
(matching `OpaqueCalleeTable.demandedKeys_extraTraitImpls`): `dynRegistryStep_frames` preserves
`memory.traitImpls` across every visited state. -/
theorem dynRegistryDemandedCalleeKeys_extraTraitImpls (env : CompilerQueryEnv)
    (tbl : OpaqueCalleeTable) (reg : DynCallRegistry) (body : CapturedMir) (fuel : Nat)
    (s : MachineState) :
    ∀ ck ∈ dynRegistryDemandedCalleeKeys env tbl reg body fuel s,
      ck.extraTraitImpls = s.memory.traitImpls := by
  intro ck hck
  obtain ⟨s', hs', hstep⟩ := of_mem_filterMap hck
  rw [dynRegistryStepCalleeKey?_extraTraitImpls hstep]
  exact (runVisited_frames (dynRegistryStep_frames env tbl reg body) fuel s s' hs').2

/-- **Dynamic-dispatch + generic-callee cone narrowing from `OpaqueCalleeTable.AgreesOn`**
(connecting `OpaqueCalleeTable.AgreesOn` / `narrowToCone` directly to `evalDynRegistryWithOpaqueCallees`):
no `fullTbl` step and no per-key `lookupKey` certificate is needed when `narrowTbl` and `fullTbl`
agree on `cone` and no `dp ∈ cone` has a `TraitImplEntry`. -/
theorem evalDynRegistryWithOpaqueCallees_cone_narrow_of_agreesOn_poly
    {env₁ env₂ : CompilerQueryEnv} (cone : List DefPath)
    (narrowTbl fullTbl : OpaqueCalleeTable) (reg : DynCallRegistry)
    (body : CapturedMir) (fuel : Nat) (s : MachineState)
    (h : EnvExtends env₁ env₂)
    (hagree : OpaqueCalleeTable.AgreesOn cone narrowTbl fullTbl)
    (hno₁ : ∀ dp, dp ∈ cone →
      hasTraitImplForDefPath (s.memory.traitImpls ++ narrowTbl.traitImpls) dp = false)
    (hno₂ : ∀ dp, dp ∈ cone →
      hasTraitImplForDefPath (s.memory.traitImpls ++ fullTbl.traitImpls) dp = false)
    (hsup : ∀ p ∈ dynRegistryDemandedQueries env₂ narrowTbl reg body fuel s,
      ∀ m, resolveDynTarget env₁ p.1 p.2 ≠ .unsupported m)
    (hkeys : ∀ ck ∈ dynRegistryDemandedCalleeKeys env₂ narrowTbl reg body fuel s,
      ck.defPath ∈ cone) :
    evalDynRegistryWithOpaqueCallees env₂ narrowTbl reg body fuel s =
      evalDynRegistryWithOpaqueCallees env₁ fullTbl reg body fuel s :=
  evalDynRegistryWithOpaqueCallees_cone_narrow_of_demands h fuel s hsup fun ck hck => by
    have hextra := dynRegistryDemandedCalleeKeys_extraTraitImpls env₂ narrowTbl reg body fuel s ck hck
    have hdp := hkeys ck hck
    refine lookupKey_eq_of_agreesOn_free hagree hdp ?_ ?_
    · rw [hextra]; exact hno₁ _ hdp
    · rw [hextra]; exact hno₂ _ hdp

/-- **Full dynamic-dispatch + generic + static-trait cone narrowing from `OpaqueCalleeTable.AgreesOn`**:
composes `evalDynRegistryWithOpaqueCallees_cone_narrow_of_demands` with
`lookupKey_eq_of_agreesOn_with_traits` and `dynRegistryDemandedCalleeKeys_extraTraitImpls`, so a
program mixing receiver-driven `dyn` calls, generic functions, and static `TraitImplEntry` overrides
narrows from `OpaqueCalleeTable.AgreesOn cone narrowTbl fullTbl` without unfolding `fullTbl` along
the run. -/
theorem evalDynRegistryWithOpaqueCallees_cone_narrow_of_agreesOn_with_traits
    {env₁ env₂ : CompilerQueryEnv} (cone : List DefPath)
    (narrowTbl fullTbl : OpaqueCalleeTable) (reg : DynCallRegistry)
    (body : CapturedMir) (fuel : Nat) (s : MachineState)
    (h : EnvExtends env₁ env₂)
    (hagree : OpaqueCalleeTable.AgreesOn cone narrowTbl fullTbl)
    (htraits : ∀ dp, dp ∈ cone →
      narrowTbl.traitImpls.filter (fun e => stringEq e.traitRef.defPath dp) =
        fullTbl.traitImpls.filter (fun e => stringEq e.traitRef.defPath dp))
    (himpls : ∀ dp, dp ∈ cone → ∀ e ∈ s.memory.traitImpls ++ narrowTbl.traitImpls,
      stringEq e.traitRef.defPath dp = true → e.implPath ∈ cone)
    (hsup : ∀ p ∈ dynRegistryDemandedQueries env₂ narrowTbl reg body fuel s,
      ∀ m, resolveDynTarget env₁ p.1 p.2 ≠ .unsupported m)
    (hkeys : ∀ ck ∈ dynRegistryDemandedCalleeKeys env₂ narrowTbl reg body fuel s,
      ck.defPath ∈ cone) :
    evalDynRegistryWithOpaqueCallees env₂ narrowTbl reg body fuel s =
      evalDynRegistryWithOpaqueCallees env₁ fullTbl reg body fuel s :=
  evalDynRegistryWithOpaqueCallees_cone_narrow_of_demands h fuel s hsup fun ck hck => by
    have hextra := dynRegistryDemandedCalleeKeys_extraTraitImpls env₂ narrowTbl reg body fuel s ck hck
    have hdp := hkeys ck hck
    refine lookupKey_eq_of_agreesOn_with_traits hagree hdp (htraits _ hdp) ?_
    rw [hextra]
    exact himpls _ hdp

/-- Single-site corollary of `evalDynRegistryWithOpaqueCallees_cone_narrow_of_agreesOn_with_traits`. -/
theorem evalDynWithOpaqueCallees_cone_narrow_of_agreesOn_with_traits
    {env₁ env₂ : CompilerQueryEnv} (cone : List DefPath)
    (narrowTbl fullTbl : OpaqueCalleeTable) (site : DynCallSite)
    (body : CapturedMir) (fuel : Nat) (s : MachineState)
    (h : EnvExtends env₁ env₂)
    (hagree : OpaqueCalleeTable.AgreesOn cone narrowTbl fullTbl)
    (htraits : ∀ dp, dp ∈ cone →
      narrowTbl.traitImpls.filter (fun e => stringEq e.traitRef.defPath dp) =
        fullTbl.traitImpls.filter (fun e => stringEq e.traitRef.defPath dp))
    (himpls : ∀ dp, dp ∈ cone → ∀ e ∈ s.memory.traitImpls ++ narrowTbl.traitImpls,
      stringEq e.traitRef.defPath dp = true → e.implPath ∈ cone)
    (hsup : ∀ p ∈ dynRegistryDemandedQueries env₂ narrowTbl [site] body fuel s,
      ∀ m, resolveDynTarget env₁ p.1 p.2 ≠ .unsupported m)
    (hkeys : ∀ ck ∈ dynRegistryDemandedCalleeKeys env₂ narrowTbl [site] body fuel s,
      ck.defPath ∈ cone) :
    evalDynWithOpaqueCallees env₂ narrowTbl site body fuel s =
      evalDynWithOpaqueCallees env₁ fullTbl site body fuel s := by
  rw [← evalDynRegistryWithOpaqueCallees_singleton, ← evalDynRegistryWithOpaqueCallees_singleton]
  exact evalDynRegistryWithOpaqueCallees_cone_narrow_of_agreesOn_with_traits cone narrowTbl fullTbl
    [site] body fuel s h hagree htraits himpls hsup hkeys

end Anneal.CompilerQueryEnv
