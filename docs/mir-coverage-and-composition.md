# MIR Coverage, Generated-Assembly Composition, and Verification Scope

This document describes Anneal's MIR coverage against pinned `rustc
1.98.0-nightly (14210df0e 2026-05-31)`, the typeclass-based "Pure Generated
Assembly" architecture that connects generated MIR obligations to authored Lean
4 proofs without generate-then-edit files, the supporting memory and
bit-validity theories in `theory/Anneal/`, and the current verification scope.

## 1. MIR Coverage Against `rustc 1.98.0-nightly (14210df0e)`

Anneal separates MIR support into three layers:

1. **Syntax capture and AST modeling (`trusted/rustc-capture/` and
   `trusted/lean/Trusted/Rustc/V2026_06_01/MirAst/`)**: The `rustc_driver`
   wrapper extracts `Runtime(PostCleanup)` MIR bodies, layout tables, static
   allocations, and resolved callee `DefPath` tables, while `MirAst` represents
   every syntactic construct in Lean.
2. **Reference-backed operational semantics
   (`trusted/lean/Trusted/Rustc/V2026_06_01/MirSemantics/`)**: The operational
   evaluator transitions states for supported constructs and steps to
   `ITree.fail .unsupported` for
   unimplemented constructs so `MirNoUB` fails closed.
3. **Proof lowering and weakest preconditions (`theory/Anneal/`)**: Untrusted
   lowering passes (`Lower.lean`), scalar/bit-validity reasoning
   (`Scalars.lean`, `BitValidity.lean`), explicit unsafe side-condition
   definitions (`UnsafeObligations.lean`), byte-range Tree Borrows separation
   logic (`Memory.lean`, `SepLogic.lean`), and `WP` rules discharge
   `VerificationResult` theorems.

### Construct Coverage Table

| `rustc_middle::mir` Construct (`syntax.rs`) | Variants in `14210df0e` | Syntax Capture & `MirAst` | `MirSemantics` Operational Support |
| --- | --- | --- | --- |
| `StatementKind` | 14 variants | 14/14 captured (`FakeRead` -> `.placeMention`, `AscribeUserType` -> `.nop`; 12 constructors in `Statements.lean`) | 11/12 supported (`Assign`, `SetDiscriminant`, `Deinit`, `StorageLive`, `StorageDead`, `Retag`, `PlaceMention`, `Coverage`, `Intrinsic`, `ConstEvalCounter`, `Nop`). `.backwardIncompatibleDropHint` returns `.unsupported`. |
| `NonDivergingIntrinsic` | 2 variants (`Assume`, `CopyNonOverlapping`) | 2/2 captured in `Statements.lean` | 2/2 supported: `Assume` (fails with `.ub` on `false`) and `CopyNonOverlapping` (validates non-null, alignment, non-overlap, and transfers `count * elemSize` abstract bytes across layouts via `encodeToBytes` / `decodeFromBytesWithLayouts`). |
| `TerminatorKind` | 15 variants (11 runtime, 4 pre-runtime/coroutine) | 15/15 captured (11 runtime constructors in `Terminators.lean`) | 8/11 runtime variants supported (`.goto`, `.switchInt`, `.return_`, `.unreachable`, `.drop`, `.call` via transparent `FuncTable` or assumed `CalleeSpecTable` / `CalleeContractEntry`, `.tailCall`, `.assert`). Unwind (`Resume`, `Terminate`), `InlineAsm`, and indirect `FnPtr`/closure calls return `.unsupported`. |
| `ProjectionElem` | 8 variants (`Deref`, `Field`, `Index`, `ConstantIndex`, `Subslice`, `Downcast`, `OpaqueCast`, `UnwrapUnsafeBinder`) | 8/8 captured in `Places.lean` | 7/8 supported on read, 6/8 on write, including byte-reinterpreted union field reads/writes and full projection-chain type traversal in `placeIsSigned`. `.unwrapUnsafeBinder` returns `.unsupported`. |
| `Operand` & `ConstValue` | `Copy`, `Move`, `Constant`, `RuntimeChecks`; `Scalar`, `ZeroSized`, `Slice`, `Indirect` | All captured in `Rvalues.lean` | `.copy`, `.move`, `.zeroSized`, `.scalar` (`.int` and `.ptr`), `.slice` (producing wide `.ptr` values with slice metadata and backing static allocations), and scalar/composite `.indirect` constants decoded from `body.allocations` via `decodeFromBytesWithLayouts`. |
| `Rvalue` | 15 constructors in `Rvalues.lean` | All captured (`Reborrow` lowers to `.ref`) | 11/15 supported (`.use`, `.repeat`, `.ref`, `.rawPtr`, `.len`, `.cast`, `.binaryOp`, `.unaryOp`, `.discriminant`, `.aggregate`, `.copyForDeref`). `.threadLocalRef`, `.nullaryOp`, `.shallowInitBox`, and `.wrapUnsafeBinder` return `.unsupported`. |
| `BinOp` & `UnOp` | 26 `BinOp` variants; 3 `UnOp` variants | 26/26 `BinOp` and 3/3 `UnOp` captured | 26/26 `BinOp` supported for signed/unsigned integers (`1..16` bytes) and pointer `.offset` / `.offsetFrom`; 3/3 `UnOp` supported (`.not` bitwise complement across all integer widths `1..16` bytes and `bool`, `.neg` with signed `MIN` overflow checking, and `.ptrMetadata`). |
| `CastKind` | 11 variants | 11/11 captured in `Rvalues.lean` | 7/11 supported: `.intToInt` (sign-extending for signed sources, zero-extending/truncating otherwise), `.ptrToPtr` (updating metadata for wide casts), `.pointerCoercion` (`.unsize`, `.mutToConstPointer`, `.arrayToPointer`), `.transmute` (byte-level `encodeToBytes` + `decodeFromBytesWithLayouts` validating scalar bit-validity and preserving pointer provenance), `.subtype`, `.pointerExposeProvenance` (recording exposed allocation provenance), and `.pointerWithExposedProvenance` (reconstructing provenance from `exposedAllocs`). Float casts and `FnPtr` casts return `.unsupported`. |
| `AggregateKind` | 7 variants | 7/7 captured in `Rvalues.lean` | 4/7 supported: `.array`, `.tuple`, `.adt` (structs, enums, and single-field union construction), and `.rawPtr` (combining a thin pointer address/provenance with wide metadata). `.closure`, `.coroutine`, and `.coroutineClosure` return `.unsupported`. |

## 2. Pure Generated-Assembly Architecture

Anneal enforces a strict separation between tool-generated Lean code
(`.anneal/generated/`) and human- or agent-authored Lean code (`anneal/proofs/`)
so that **no file is ever generated once and then edited in place**:

1. **Tool-owned `.anneal/generated/` (regenerated cleanly on every `scaffold` run)**:
   - `Mir/<Crate>/<Item>.lean`: Contains the captured `body : CapturedMir` and
     `layouts : LayoutTable`.
   - `Obligations/<Crate>/<Item>.lean`: Defines `defaultPre` and `defaultPost`
     from captured Rust `#[spec]`, `#[invariant]`, `#[unsafe_fn]`, and
     `#[unsafe_impl]` companions using
     `Trusted.VerificationResult.MirBoolPredicateHolds` (referencing only
     `Trusted` and `Mir.*`, never `theory/`), registers low-priority default
     instances `instance (priority := low) defaultSpec : ItemSpec "<def_id>"`
     and `instance (priority := low) defaultStatefulSpec : StatefulItemSpec "<def_id>"`,
     and defines `def claim [spec : ItemSpec "<def_id>"] : Claim` and
     `def statefulClaim [spec : StatefulItemSpec "<def_id>"] : StatefulClaim`.
   - `Verify/<Crate>/<Item>.lean` (**Generated Assembly**): Imports
     `Mir.<Crate>.<Item>`, `Obligations.<Crate>.<Item>`, and any authored
     modules present under `anneal/proofs/` (`Specs.<Crate>.<Item>`,
     `Assumptions.<Crate>.<Item>`, `Proof.<Crate>.<Item>`), resolves
     `abbrev activeSpec := inferInstance`, binds `def claim` /
     `def statefulClaim`, and exports
     `theorem verified : VerificationResult claim := Proof.<Crate>.<Item>.verified`
     (or `theorem verified : StatefulVerificationResult statefulClaim := Proof.<Crate>.<Item>.verified`
     when `Specs.<Crate>.<Item>` provides a `StatefulItemSpec` instance or
     `Proof.<Crate>.<Item>` proves `statefulClaim`).
2. **Human/agent-owned `anneal/proofs/` (authored only, never overwritten)**:
   - When an item needs no custom Lean specification, no `Specs/<Crate>/<Item>.lean`
     file is needed; Lean's typeclass synthesis selects the `priority := low`
     `defaultSpec` from `Obligations.<Crate>.<Item>`.
   - To refine a specification in Lean without touching `.anneal/generated/`, an
     author creates `anneal/proofs/Specs/<Crate>/<Item>.lean` and provides a
     default-priority `instance : ItemSpec "<def_id>"` (or `StatefulItemSpec`).
   - Proofs live in `anneal/proofs/Proof/<Crate>/<Item>.lean`.
   - Conditional assumptions (when needed for incremental verification) live in
     `anneal/proofs/Assumptions/<Crate>/<Item>.lean`.

## 3. Supporting Theories and the `zerocopy` Verification Slice

`theory/Anneal/` provides kernel-checked libraries used by proofs in
`anneal/proofs/`:

- **Bit-validity certificate checkers and layout transfers (`Anneal/BitValidity.lean`)**:
  Defines per-layout byte validity (`BytesValidForLayout`), scalar Niche/range
  checks (`bool` in `{0, 1}`, `char` Unicode scalar values, `NonZero*` non-zero
  bounds), uninitialized/padding byte tolerances, representation-containment
  predicates mirroring `zerocopy`'s `TryFromBytes`, `FromZeros`, `FromBytes`,
  `IntoBytes`, and `Unaligned` conversion traits (`ZerocopyTrait`,
  `ValidForTrait`), decidable layout certificate checkers
  (`checkUnaligned_sound`, `checkFromZeros_sound`, `checkFromBytes_sound`,
  `checkIntoBytes_sound`) backed by inductive $N$-field contiguous struct
  checkers (`checkAdtContiguousLayout_isFromBytes`,
  `checkAdtContiguousLayout_isIntoBytes`), monomorphic span-layout checkers
  (`checkMonoAdtSpanLayout_isFromBytes`), and arbitrary-length `[T; N]` array
  induction (`decodeArrayChunksWith_of_allBytesInitialized`,
  `encodeListWith_length_and_init`, `array_uint_isFromBytes`,
  `array_uint_isIntoBytes`, `array_int_isFromBytes`, `array_int_isIntoBytes`)
  discharging layout proofs via 1-line `rfl` checks across arbitrary field counts
  and mixed scalar/array field types, complete primitive integer and unit
  `FromBytes`/`IntoBytes` theorems, `[u8; 2]` / `[u8; 4]` and `BigEndianU16` /
  `BigEndianU32` (`zerocopy::byteorder`) bit-validity and `transmute_sound`
  theorems, and 16-bit endian byte-swap algebra (`swapBytes16`).
- **Explicit unsafe side-conditions (`Anneal/UnsafeObligations.lean`)**: Packages
  alignment (`AlignedPtr`), non-null (`NonNullPtr`), disjointness
  (`NonOverlappingPtrs`), in-bounds allocation range (`ValidSliceRange`),
  constructive slice-splitting obligations (`ValidSliceSplit`,
  `sliceSplitRightPtr`, `validSliceSplit_disjoint`) for
  `PtrInner::split_at_unchecked`, and bit-validity obligations for raw pointer
  dereferences, `CopyNonOverlapping`, and `CastKind.transmute`.
- **Byte-range Tree Borrows, lifetime protectors, and footprint separation logic
  (`Anneal/Memory.lean`, `Anneal/SepLogic.lean`)**:
  - `Trusted.MirSemantics` and `Anneal/Memory.lean` track per-entry sub-place
    projection paths and byte ranges (`rangeOffset`, `rangeLen`), plus active
    function-entry lifetime protectors (`protector`, `activeProtectors`,
    `nextProtector`) allocated on `StatementKind.retag .fnEntry` and released on
    `TerminatorKind.return_`. Conflicting foreign writes to a protected
    `Reserved`/`Active`/`Frozen` entry fail immediately (`hasProtectedWriteConflict`),
    while writes to disjoint struct fields (`projectionsOverlap = false`) leave
    sibling borrows intact (`disjoint_byte_range_operational_non_interference`).
  - `Anneal/SepLogic.lean` defines a spatial partial-heap separation logic
    (`AddrCell`, `Footprint`, `PartialHeap`, `PartialHeapSplit`, `SepProp`) with
    true spatial disjointness (`pointsToSep_star_exclusive`,
    `borrowTokenSep_star_exclusive`), lifetime/protector assertions
    (`LifetimeTokenSep`, `PtrInvariantSep`, `UnalignInvariantSep`,
    `unalign_deref_unchecked_sound`, `unalign_deref_mut_unchecked_sound`,
    `unalign_set_mir_verified`), generalized structural `CapturedMir` shape
    checkers for stateful pointer/reference conversions and in-place writes
    (`isPtrAsRefMirShape`, `verifyPtrAsRefMirOfShape`, `isPtrAsMutMirShape`,
    `verifyPtrAsMutMirOfShape`, `isUnalignSetMirShape`,
    `verifyUnalignSetMirOfShape`) supporting optional `StorageLive(2)` /
    `StorageDead(2)`, two-step `_2` temporaries, and arbitrary trailing
    `localDecls`, and an automatic footprint-based frame rule
    (`AgreeOnFootprint`, `SupportedBy`, `wp_frame_disjoint`).
- **Single-pass symbolic MIR evaluation and plan-guided functional translation
  (`Anneal/Rustc/V2026_06_01/SymbolicEval.lean`,
  `Anneal/Rustc/V2026_06_01/SymReflect.lean`,
  `Anneal/FunctionalTranslation.lean`)**:
  - `SymbolicEval.lean` and `SymReflect.lean` provide single-pass continuation
    symbolic evaluators (`SymTree`, `wpMirSym`, `wpMirNoCallSym`), bounded
    Undefined Behavior counterexample refutation (`refuteClaimByBoundedUB`,
    `refuteStatefulClaimByBoundedUB`, `refuteTotalClaimByBoundedUB`),
    non-vacuity witness combinators (`proveNonVacuousPre`,
    `proveNonVacuousStatefulPre`, `proveNonVacuousBoolSpecPre`), closed-term
    scalar precondition pinning (`checkMirRequiresPinsScalars`,
    `dischargeRustEqU8`..`dischargeRustEq2U64`), bitwise masking and endian
    byte-swap `@[simp]` lemmas, and program-to-program equivalence verification
    (`verifyStatefulEquivMirSym`).
  - `FunctionalTranslation.lean` provides `TransPlan`-guided CFG/diamond-join
    and loop translation (`wpTransPlan`, `dwlp_mirTree_while_invariant`,
    `verifyByTransPlan`, `verifyStatefulByTransPlan`), composable `&mut`
    forward/backward state-update lenses (`MutLens`, `LawfulMutLens`,
    `ActiveTypedMutBorrow`, `memoryPtrMutLens`), and trace/observation-erased
    program-to-program refinement (`verifyStatefulEquivClaimByTransPlan`).

These capabilities are exercised end-to-end across extraction, scaffolding,
whole-crate `CrateVerify` (`CrateVerificationResult`) rollups, `spec-lock.json`
anti-tampering gates, and `TrustedBoundary` kernel replay in
[`crates/cargo-anneal/tests/end_to_end_pipeline.rs`](../crates/cargo-anneal/tests/end_to_end_pipeline.rs).

## 4. `TrustedBoundary` Audit, Spec-Locking, and Agentic Proof Construction

`cargo anneal verify` (and `cargo anneal agent-verify` for delegated agentic
proof sessions; see [`docs/agent-proof-workflow.md`](agent-proof-workflow.md)
and [`skills/anneal-prove/SKILL.md`](../skills/anneal-prove/SKILL.md)) invokes
Lake on `.anneal/` and runs the `TrustedBoundary` auditor (`trusted/audit/`) on
the compiled `.olean` environment:

- **Pre-build specification and assumption lock (`.anneal/spec-lock.json`)**:
  `cargo anneal lock-specs` records SHA-256 digests of all captured subject and
  companion MIR modules, `anneal/proofs/Specs/**`, and
  `anneal/proofs/Assumptions/**`. `cargo anneal agent-verify` (and
  `verify --locked-specs`) rejects any run where captured targets, `Specs/**`,
  or `Assumptions/**` were added, removed, or modified, or where a `Specs` file
  introduces a vacuous `False` precondition, ensuring that delegated agents can
  only author proofs under `anneal/proofs/Proof/<Crate>/<Item>.lean`.
- **Statement origin separation (`checkStatementOrigins`)**: Inspects the type
  (`ci.type`) of every root `Verify.<Crate>.<Item>.verified` theorem and rejects
  any theorem whose statement references constants from untrusted `theory/`
  (`Anneal.*`).
- **Kernel replay and axiom classification**: Replays all declarations in a
  fresh Lean 4 kernel environment and classifies each item:
  - `VerifiedUnconditional`: Zero `sorryAx` and zero custom project axioms
    (only standard foundational axioms `{propext, Quot.sound, Classical.choice}`).
  - `VerifiedConditional`: Zero `sorryAx`, depending only on explicitly scoped
    `Assumptions.<Crate>.<Item>.*` axioms or declared `CalleeSpecTable`
    contracts (gated behind `--allow-assumptions`, with every depended-on axiom
    and assumed callee contract enumerated in the verification report).
  - `Rejected`: Any `sorryAx`, any unapproved `axiom` outside
    `Assumptions.<Crate>.<Item>`, any `native_decide`/`unsafe`/`partial`
    declaration, or any `theory/` symbol leaking into a theorem statement.

## 5. Summary of Verified Capabilities vs. Out-of-Scope Constructs

| Category | Currently Supported & Verified | Currently Out of Scope (Steps to `.unsupported`) |
| --- | --- | --- |
| **Scalars & Arithmetic** | All signed/unsigned integer widths (`8, 16, 32, 64, 128` bits, `isize`, `usize`), `bool`, `char`; checked/wrapping/overflowing/unchecked `BinOp`s; signed/unsigned `Cmp`; multi-byte bitwise `&`, `\|`, `^`, `!`, `<<`, `>>`; two's-complement negation and `intToInt` casts; symbolic bitwise masking and endian byte-swap lemmas (`SymReflect.lean`). | IEEE-754 floating-point arithmetic and float casts (`floatToInt`, `intToFloat`, `floatToFloat`); SIMD vector intrinsics. |
| **Memory & Pointers** | Stack/static allocations, byte-level `AbstractByte` representation (`init`, `uninit`, `reloc`), union field reinterpretation, `CastKind.transmute`, wide slice pointers (`AggregateKind.rawPtr`, `UnOp.ptrMetadata`), provenance exposure (`pointerExposeProvenance` / `pointerWithExposedProvenance`), sub-place/byte-range Tree Borrows with function-entry lifetime protectors, partial-heap separation logic (`wp_frame_disjoint`), `&mut` lenses (`MutLens`, `ActiveTypedMutBorrow`), and `CopyNonOverlapping`. | Dynamic heap allocator intrinsics (`rust_alloc` / `dealloc`) without an external callee contract; volatile/atomic memory orderings; inline assembly (`TerminatorKind.inlineAsm`). |
| **Control Flow & Calls** | Structured and bounded CFG execution (`goto`, `switchInt`, `return_`, `assert`, `drop`), plan-guided diamond joining and loop invariants (`TransPlan`), transparent direct calls (`FuncTable`), and modular/external calls via `CalleeSpecTable` (`CalleeContractEntry`). | Unwinding cleanup paths (`Resume`, `Terminate`, panic catch); coroutines/generators (`Yield`, `CoroutineDrop`); indirect `FnPtr` and dynamic trait-object dispatch. |
| **Polymorphism** | Concrete monomorphized generic functions, structs, unions, and trait implementations extracted from `Runtime(PostCleanup)` MIR. | Unmonomorphized polymorphic functions prior to concrete instantiation in `rustc` capture. |
