//! Runtime trace observer and Lean 4 `TraceCheck` module generator.
//!
//! Bridges compiled Rust artifacts to Anneal's coinductive `MIR -> ITree`
//! semantics (`Anneal.Rustc.V2026_06_01.TraceCheck`) along two design axes:
//!
//! 1. **Interposition & Branch Erasure**:
//!    - **Call-boundary interposition (`check_branches = false`)**: captures
//!      raw argument and return byte slices at the root entry/exit and at
//!      unresolved external/callee boundaries (`MirCallE`), checking the
//!      resulting `RawByteTrace` against `mirObsErasedStatefulTree` via
//!      `checkRawByteTraceObsErasedBounded_sound` and
//!      `diagnoseRawByteTraceObsErasedBounded` without requiring internal
//!      `switchInt` branch instrumentation.
//!    - **Full branch + call observation (`check_branches = true`)**:
//!      additionally records `switchInt` branch tags (`MirObsE`) and checks the
//!      trace against `mirStatefulTree` via `checkRawByteTraceFullBounded_sound`
//!      and `diagnoseRawByteTraceFullBounded`.
//!    - **Inlining duality (`inlined_callee_modules`)**: callees placed in
//!      `inlinedCallees` (`Memory.callees`) are stepped transparently via
//!      `.tau` transitions in the Lean model rather than emitting `MirCallE`
//!      events.
//!
//! 2. **Raw Byte Decoding & Shadow Provenance (`ShadowProvenanceTable`)**:
//!    - **Zero-annotation raw byte capture**: [`value_as_raw_bytes`] copies the
//!      in-memory byte representation (`&[u8]`) of any Rust value at a call
//!      boundary without requiring `Serialize` or `Debug` bounds; the Lean
//!      checker decodes the raw byte slice using the compiler-extracted
//!      `LayoutTable` and `LocalDecl` metadata in `CapturedMir` (ignoring
//!      uninitialized inter-field padding bytes while enforcing scalar and
//!      niche bit-validity).
//!    - **Shadow provenance table**: [`TraceRecorder::register_allocation`]
//!      maps watched runtime virtual address ranges `[base_addr, base_addr +
//!      byte_len)` to abstract MIR `(alloc_id, tag)` provenance so thin and
//!      wide pointers/references in raw byte slices decode to `Value.ptr` with
//!      relative offset `addr - base_addr`.

use std::any::Any;
use std::fmt::Write as _;
use std::mem;
use std::panic::{self, AssertUnwindSafe};

/// Copy the raw in-memory representation of `val` as a byte vector (`Vec<u8>`).
///
/// For structs or enums with inter-field padding, reading padding bytes as
/// `u8` in a runtime observer wrapper is strictly for diagnostic trace export;
/// the Lean `decodeValueFromBytes` decoder only inspects field byte ranges
/// dictated by `TypeLayout.fields` and `TypeLayout.variants`, ignoring padding
/// offsets completely.
pub fn value_as_raw_bytes<T: ?Sized>(val: &T) -> Vec<u8> {
    let size = mem::size_of_val(val);
    if size == 0 {
        return Vec::new();
    }
    let src = (val as *const T).cast::<mem::MaybeUninit<u8>>();
    let mut dst: Vec<mem::MaybeUninit<u8>> = vec![mem::MaybeUninit::new(0); size];
    // SAFETY: `val` is a valid reference of `size` bytes, and copying as
    // `MaybeUninit<u8>` avoids forming a `&[u8]` slice reference over `val`.
    unsafe {
        std::ptr::copy_nonoverlapping(src, dst.as_mut_ptr(), size);
        let ptr = dst.as_mut_ptr().cast::<u8>();
        let cap = dst.capacity();
        mem::forget(dst);
        Vec::from_raw_parts(ptr, size, cap)
    }
}

/// Entry in the runtime observer's shadow provenance table mapping a native
/// virtual address range `[base_addr, base_addr + byte_len)` to an abstract
/// MIR `(alloc_id, tag)`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RecordedShadowAlloc {
    /// Native runtime base virtual address (`ptr as usize`).
    pub base_addr: usize,
    /// Allocation size in bytes.
    pub byte_len: usize,
    /// Abstract MIR `AllocId`.
    pub alloc_id: usize,
    /// Tree Borrows provenance tag associated with this allocation.
    pub tag: usize,
}

/// Alias preserving compatibility with JSON trace interchange descriptors.
pub type ShadowAllocEntryJson = RecordedShadowAlloc;

/// Single observable event captured by [`TraceRecorder`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RecordedEvent {
    /// A `TerminatorKind.switchInt` branch observation (`MirObs.event tag`).
    Branch {
        /// Discriminant value taken at the `switchInt` terminator.
        tag: u128,
    },
    /// An external/callee call to `def_path` that returned normally.
    ExtCall {
        /// Rust `DefPath` of the callee (e.g., `"trace_demo::ext_scale_add"`).
        def_path: String,
        /// Raw little-endian byte slices for each argument in declaration order.
        raw_args: Vec<Vec<u8>>,
        /// Raw little-endian byte slice for the returned value.
        raw_ret: Vec<u8>,
    },
    /// An external/callee call to `def_path` that unwound (panicked).
    ExtCallPanic {
        /// Rust `DefPath` of the callee.
        def_path: String,
        /// Raw little-endian byte slices for each argument in declaration order.
        raw_args: Vec<Vec<u8>>,
    },
    /// An external/callee call to `def_path` that aborted.
    ExtCallAbort {
        /// Rust `DefPath` of the callee.
        def_path: String,
        /// Raw little-endian byte slices for each argument in declaration order.
        raw_args: Vec<Vec<u8>>,
    },
}

/// Structured call-boundary event representation for interchange across fuzzing
/// and trace serialization pipelines.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RawCallEventJson {
    /// Rust `DefPath` of the callee.
    pub def_path: String,
    /// Raw little-endian byte slices for each argument in declaration order.
    pub raw_args: Vec<Vec<u8>>,
    /// Raw little-endian return bytes when the call returned normally.
    pub raw_ret: Option<Vec<u8>>,
    /// Whether the callee unwound via panic.
    pub panicked: bool,
    /// Whether the callee terminated the process via abort.
    pub aborted: bool,
}

impl RawCallEventJson {
    /// Convert this structured call record into a [`RecordedEvent`].
    pub fn into_recorded_event(self) -> RecordedEvent {
        if self.aborted {
            RecordedEvent::ExtCallAbort {
                def_path: self.def_path,
                raw_args: self.raw_args,
            }
        } else if self.panicked {
            RecordedEvent::ExtCallPanic {
                def_path: self.def_path,
                raw_args: self.raw_args,
            }
        } else {
            RecordedEvent::ExtCall {
                def_path: self.def_path,
                raw_args: self.raw_args,
                raw_ret: self.raw_ret.unwrap_or_default(),
            }
        }
    }
}

/// Alias preserving compatibility with JSON trace event descriptors.
pub type RawTraceEventJson = RecordedEvent;

/// Terminal outcome of a root function invocation captured by [`TraceRecorder`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RecordedOutcome {
    /// Normal return with the raw byte slice of the return value (`_0`).
    Normal {
        /// Raw little-endian byte slice of the return value.
        raw_ret: Vec<u8>,
    },
    /// Unwinding panic.
    Panic,
    /// Process abort.
    Abort,
}

/// Alias preserving compatibility with JSON outcome descriptors.
pub type RawOutcomeJson = RecordedOutcome;

/// Complete raw byte-level execution trace captured by [`TraceRecorder`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RecordedRawTrace {
    /// Rust `DefPath` of the root function.
    pub root_def_path: String,
    /// Raw little-endian byte slices of the root function's arguments.
    pub raw_args: Vec<Vec<u8>>,
    /// Shadow provenance table mapping native virtual addresses to abstract
    /// MIR `(alloc_id, tag)` provenance.
    pub shadow_provenance: Vec<RecordedShadowAlloc>,
    /// Sequence of observed branch and external-call events.
    pub events: Vec<RecordedEvent>,
    /// Terminal outcome of the root invocation.
    pub outcome: RecordedOutcome,
}

/// Alias preserving compatibility with JSON raw byte trace descriptors.
pub type RawByteTraceJson = RecordedRawTrace;

/// Stateful recorder that interposes at function boundaries (and optional
/// branch points) to capture a [`RecordedRawTrace`].
#[derive(Clone, Debug, Default)]
pub struct TraceRecorder {
    shadow_provenance: Vec<RecordedShadowAlloc>,
    events: Vec<RecordedEvent>,
}

impl TraceRecorder {
    /// Construct an empty [`TraceRecorder`].
    pub fn new() -> Self {
        Self::default()
    }

    /// Return the currently registered shadow provenance table entries.
    pub fn shadow_provenance(&self) -> &[RecordedShadowAlloc] {
        &self.shadow_provenance
    }

    /// Return the currently recorded interaction events.
    pub fn events(&self) -> &[RecordedEvent] {
        &self.events
    }

    /// Register a watched runtime allocation in the shadow provenance table.
    pub fn register_allocation<T: ?Sized>(
        &mut self,
        referent: &T,
        alloc_id: usize,
        tag: usize,
    ) {
        let base_addr = (referent as *const T).cast::<u8>() as usize;
        let byte_len = mem::size_of_val(referent);
        self.register_address_range(base_addr, byte_len, alloc_id, tag);
    }

    /// Register an explicit native virtual address range `[base_addr, base_addr + byte_len)`
    /// in the shadow provenance table.
    pub fn register_address_range(
        &mut self,
        base_addr: usize,
        byte_len: usize,
        alloc_id: usize,
        tag: usize,
    ) {
        self.shadow_provenance.push(RecordedShadowAlloc {
            base_addr,
            byte_len,
            alloc_id,
            tag,
        });
    }

    /// Record a `TerminatorKind.switchInt` branch observation (`MirObs.event tag`).
    pub fn record_branch(&mut self, tag: u128) {
        self.events.push(RecordedEvent::Branch { tag });
    }

    /// Record a completed external call event directly from raw argument and
    /// return byte slices.
    pub fn record_ext_call(
        &mut self,
        def_path: impl Into<String>,
        raw_args: Vec<Vec<u8>>,
        raw_ret: Vec<u8>,
    ) {
        self.events.push(RecordedEvent::ExtCall {
            def_path: def_path.into(),
            raw_args,
            raw_ret,
        });
    }

    /// Record an unwinding external call event directly from raw argument bytes.
    pub fn record_ext_call_panic(
        &mut self,
        def_path: impl Into<String>,
        raw_args: Vec<Vec<u8>>,
    ) {
        self.events.push(RecordedEvent::ExtCallPanic {
            def_path: def_path.into(),
            raw_args,
        });
    }

    /// Record an aborting external call event directly from raw argument bytes.
    pub fn record_ext_call_abort(
        &mut self,
        def_path: impl Into<String>,
        raw_args: Vec<Vec<u8>>,
    ) {
        self.events.push(RecordedEvent::ExtCallAbort {
            def_path: def_path.into(),
            raw_args,
        });
    }

    /// Interpose around an external or unlinked callee invocation `f`,
    /// recording its `raw_args` and either its normal return bytes
    /// (`RecordedEvent::ExtCall`) or an unwinding panic
    /// (`RecordedEvent::ExtCallPanic`, re-raising the panic afterward).
    pub fn observe_ext_call<R>(
        &mut self,
        def_path: impl Into<String>,
        raw_args: Vec<Vec<u8>>,
        f: impl FnOnce() -> R,
    ) -> R {
        let def_path = def_path.into();
        match panic::catch_unwind(AssertUnwindSafe(f)) {
            Ok(ret) => {
                let raw_ret = value_as_raw_bytes(&ret);
                self.events.push(RecordedEvent::ExtCall {
                    def_path,
                    raw_args,
                    raw_ret,
                });
                ret
            }
            Err(payload) => {
                self.events.push(RecordedEvent::ExtCallPanic {
                    def_path,
                    raw_args,
                });
                panic::resume_unwind(payload)
            }
        }
    }

    /// Execute and observe a root function invocation `f`, capturing its
    /// `raw_args`, all interaction events recorded on `TraceRecorder`, and its
    /// terminal `RecordedOutcome` (`Normal` or `Panic`).
    pub fn observe_root<R>(
        root_def_path: impl Into<String>,
        raw_args: Vec<Vec<u8>>,
        f: impl FnOnce(&mut TraceRecorder) -> R,
    ) -> (Result<R, Box<dyn Any + Send>>, RecordedRawTrace) {
        let mut recorder = TraceRecorder::new();
        let res = panic::catch_unwind(AssertUnwindSafe(|| f(&mut recorder)));
        let outcome = match &res {
            Ok(ret) => RecordedOutcome::Normal {
                raw_ret: value_as_raw_bytes(ret),
            },
            Err(_) => RecordedOutcome::Panic,
        };
        let trace = RecordedRawTrace {
            root_def_path: root_def_path.into(),
            raw_args,
            shadow_provenance: recorder.shadow_provenance,
            events: recorder.events,
            outcome,
        };
        (res, trace)
    }
}

/// Configuration for rendering a Lean 4 trace-verification module over one or
/// more [`RecordedRawTrace`]s.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TraceCheckModuleConfig {
    /// Lean module namespace (e.g., `"TraceVerify.Canary"`).
    pub module_namespace: String,
    /// Lean module path for the root function's captured MIR (e.g.,
    /// `"Mir.TracePkg.compute_packet"`), whose `.body` is checked.
    pub root_mir_module: String,
    /// Lean module paths for external callees whose signatures (`localDecls`
    /// and `layouts`) are used by `decodeRawByteTrace` to decode `MirCallE`
    /// argument and return byte slices.
    pub callee_sig_modules: Vec<String>,
    /// Lean module paths for transparent inlined callees placed in
    /// `RawByteTrace.inlinedCallees` (`Memory.callees`), stepped via `.tau`.
    pub inlined_callee_modules: Vec<String>,
    /// Optional Lean expression for `RawByteTrace.initMem` (defaults to
    /// `"emptyMemory"`).
    pub init_mem_expr: Option<String>,
    /// Step fuel bound passed to `checkRawByteTraceObsErasedBounded` /
    /// `checkRawByteTraceFullBounded` and `diagnoseRawByteTrace*Bounded`.
    pub fuel: usize,
    /// Whether to emit a full-trace theorem (`checkBranches = true`,
    /// `mirStatefulTree`) in addition to or instead of the branch-erased
    /// theorem (`checkBranches = false`, `mirObsErasedStatefulTree`).
    pub check_branches: bool,
}

/// Alias preserving compatibility with observer specification descriptors.
pub type TraceObserverSpec = TraceCheckModuleConfig;

/// Single case entry for batch diagnostic and kernel verification module
/// generation ([`render_batch_trace_eval_lean_module`]).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BatchTraceEvalCase {
    /// Lean identifier prefix for generated definitions and theorems (e.g.,
    /// `"case_01_packet"`).
    pub case_ident: String,
    /// Per-case module and fuel configuration.
    pub config: TraceCheckModuleConfig,
    /// Observed raw byte trace for this test case.
    pub trace: RecordedRawTrace,
    /// Optional expected `TraceReplayDiag.tagName` string (defaults to `"ok"`).
    /// When `Some("ok")` or `None`, a kernel `by rfl` soundness theorem is also
    /// emitted; when set to a non-`"ok"` tag such as `"outcome_mismatch"`, a
    /// negative diagnostic equality theorem is emitted.
    pub expected_diag_tag: Option<String>,
    /// Optional tampered outcome for emitting an additional negative diagnostic
    /// theorem asserting `(diagnoseRawByteTrace... { trace with outcome := ... }).tagName = "outcome_mismatch"`.
    pub tampered_outcome: Option<RecordedOutcome>,
}

fn render_u8_list_lean(bytes: &[u8]) -> String {
    if bytes.is_empty() {
        return "[]".to_string();
    }
    let items: Vec<String> = bytes.iter().map(|b| format!("{b}")).collect();
    format!("[{}]", items.join(", "))
}

fn render_u8_nested_list_lean(slices: &[Vec<u8>]) -> String {
    if slices.is_empty() {
        return "[]".to_string();
    }
    let items: Vec<String> = slices.iter().map(|s| render_u8_list_lean(s)).collect();
    format!("[{}]", items.join(", "))
}

fn escape_lean_string(s: &str) -> String {
    s.replace('\\', "\\\\").replace('"', "\\\"")
}

/// Render a [`RecordedOutcome`] as a Lean `RawObservedOutcome` term.
pub fn render_raw_outcome_lean(outcome: &RecordedOutcome) -> String {
    match outcome {
        RecordedOutcome::Normal { raw_ret } => {
            format!(".normal {}", render_u8_list_lean(raw_ret))
        }
        RecordedOutcome::Panic => ".panic".to_string(),
        RecordedOutcome::Abort => ".abort".to_string(),
    }
}

/// Render a [`RecordedShadowAlloc`] slice as a Lean `ShadowProvenanceTable` literal.
pub fn render_shadow_provenance_table_lean(entries: &[RecordedShadowAlloc]) -> String {
    if entries.is_empty() {
        return "[]".to_string();
    }
    let rendered: Vec<String> = entries
        .iter()
        .map(|e| {
            format!(
                "{{ baseAddr := {}, byteLen := {}, allocId := {}, tag := {} }}",
                e.base_addr, e.byte_len, e.alloc_id, e.tag
            )
        })
        .collect();
    format!("[{}]", rendered.join(", "))
}

/// Render a [`RecordedRawTrace`] as a Lean `RawByteTrace` structure literal.
pub fn render_raw_byte_trace_lean(
    trace: &RecordedRawTrace,
    init_mem_expr: &str,
    inlined_callee_modules: &[String],
) -> String {
    let raw_args = render_u8_nested_list_lean(&trace.raw_args);
    let inlined_bodies: Vec<String> = inlined_callee_modules
        .iter()
        .map(|m| format!("{m}.body"))
        .collect();
    let inlined_expr = if inlined_bodies.is_empty() {
        "[]".to_string()
    } else {
        format!("[{}]", inlined_bodies.join(", "))
    };

    let events_expr = if trace.events.is_empty() {
        "[]".to_string()
    } else {
        let evs: Vec<String> = trace
            .events
            .iter()
            .map(|ev| match ev {
                RecordedEvent::Branch { tag } => format!(".branch {tag}"),
                RecordedEvent::ExtCall {
                    def_path,
                    raw_args,
                    raw_ret,
                } => format!(
                    ".extCall \"{}\" {} {}",
                    escape_lean_string(def_path),
                    render_u8_nested_list_lean(raw_args),
                    render_u8_list_lean(raw_ret)
                ),
                RecordedEvent::ExtCallPanic { def_path, raw_args } => format!(
                    ".extCallPanic \"{}\" {}",
                    escape_lean_string(def_path),
                    render_u8_nested_list_lean(raw_args)
                ),
                RecordedEvent::ExtCallAbort { def_path, raw_args } => format!(
                    ".extCallAbort \"{}\" {}",
                    escape_lean_string(def_path),
                    render_u8_nested_list_lean(raw_args)
                ),
            })
            .collect();
        format!("[{}]", evs.join(", "))
    };

    let outcome_expr = render_raw_outcome_lean(&trace.outcome);

    format!(
        "{{\n  rawArgs := {raw_args}\n  initMem := {init_mem_expr}\n  inlinedCallees := {inlined_expr}\n  events := {events_expr}\n  outcome := {outcome_expr}\n}}"
    )
}

/// Render a named `@[reducible] def <def_name> : RawByteTrace := ...` Lean
/// declaration from a [`RecordedRawTrace`].
pub fn render_raw_byte_trace_lean_def(
    def_name: &str,
    trace: &RecordedRawTrace,
    init_mem_expr: &str,
    inlined_callee_modules: &[String],
) -> String {
    let body = render_raw_byte_trace_lean(trace, init_mem_expr, inlined_callee_modules);
    format!("@[reducible]\ndef {def_name} : RawByteTrace :=\n{body}\n")
}

/// Render a Lean 4 snippet asserting that the computable diagnostic runner
/// (`diagnoseRawByteTraceFullBounded` when `cfg.check_branches` is `true`, or
/// `diagnoseRawByteTraceObsErasedBounded` when `false`) evaluates to
/// `expected_tag` (e.g., `"ok"` or `"outcome_mismatch"`) by kernel reduction
/// (`by rfl`), with an optional `#eval` diagnostic line.
pub fn render_trace_diag_eval_lean_snippet(
    theorem_name: &str,
    cfg: &TraceCheckModuleConfig,
    callee_sigs_expr: &str,
    table_expr: &str,
    trace_expr: &str,
    expected_tag: &str,
    emit_eval: bool,
) -> String {
    let root_body = format!("{}.body", cfg.root_mir_module);
    let fuel = cfg.fuel;
    let diag_fn = if cfg.check_branches {
        "diagnoseRawByteTraceFullBounded"
    } else {
        "diagnoseRawByteTraceObsErasedBounded"
    };
    let escaped_tag = escape_lean_string(expected_tag);

    let mut out = String::new();
    let _ = writeln!(
        out,
        "set_option maxHeartbeats 2000000 in\n\
         theorem {theorem_name} :\n\
         \x20   ({diag_fn} {fuel} {root_body} {callee_sigs_expr} {table_expr} {trace_expr}).tagName = \"{escaped_tag}\" := by\n\
         \x20 rfl\n"
    );
    if emit_eval {
        let _ = writeln!(
            out,
            "#eval ({diag_fn} {fuel} {root_body} {callee_sigs_expr} {table_expr} {trace_expr}).tagName\n"
        );
    }
    out
}

/// Render a Lean 4 negative assertion snippet proving by `by rfl` that
/// replacing `trace_ident`'s `outcome` with `tampered_outcome` yields
/// `.tagName = "outcome_mismatch"` under `diagnoseRawByteTraceObsErasedBounded`
/// (or `diagnoseRawByteTraceFullBounded` when `cfg.check_branches` is `true`).
pub fn render_tampered_outcome_diag_lean_snippet(
    theorem_name: &str,
    cfg: &TraceCheckModuleConfig,
    callee_sigs_expr: &str,
    table_expr: &str,
    trace_ident: &str,
    tampered_outcome: &RecordedOutcome,
) -> String {
    let outcome_expr = render_raw_outcome_lean(tampered_outcome);
    let tampered_trace_expr = format!("{{ {trace_ident} with outcome := {outcome_expr} }}");
    render_trace_diag_eval_lean_snippet(
        theorem_name,
        cfg,
        callee_sigs_expr,
        table_expr,
        &tampered_trace_expr,
        "outcome_mismatch",
        false,
    )
}

/// Render a complete Lean 4 module that decodes `trace` via `decodeRawByteTrace`,
/// verifies its diagnostic tag (`"ok"`) via `diagnoseRawByteTrace*Bounded`,
/// and proves its consistency with the captured `Mir.*` interaction tree in the
/// Lean 4 kernel (`checkRawByteTraceFullBounded_sound` when
/// `cfg.check_branches` is `true`, or `checkRawByteTraceObsErasedBounded_sound`
/// when `cfg.check_branches` is `false`).
pub fn render_trace_check_lean_module(
    cfg: &TraceCheckModuleConfig,
    trace: &RecordedRawTrace,
) -> String {
    let mut out = String::new();
    out.push_str("import Trusted\n");
    out.push_str("import Anneal\n");
    let _ = writeln!(out, "import {}", cfg.root_mir_module);

    let mut imported = vec![cfg.root_mir_module.clone()];
    for m in cfg
        .callee_sig_modules
        .iter()
        .chain(cfg.inlined_callee_modules.iter())
    {
        if !imported.contains(m) {
            let _ = writeln!(out, "import {m}");
            imported.push(m.clone());
        }
    }

    let _ = writeln!(out, "\nnamespace {}\n", cfg.module_namespace);
    out.push_str("open Trusted.Effect\n");
    out.push_str("open Trusted.ITree\n");
    out.push_str("open Trusted.Rustc.V2026_06_01.MirAst\n");
    out.push_str("open Trusted.Rustc.V2026_06_01.MirSemantics\n");
    out.push_str("open Trusted.VerificationResult\n");
    out.push_str("open Anneal.Rustc.V2026_06_01.TraceCheck\n\n");

    let callee_sigs_list = if cfg.callee_sig_modules.is_empty() {
        "[]".to_string()
    } else {
        let items: Vec<String> = cfg
            .callee_sig_modules
            .iter()
            .map(|m| format!("{m}.body"))
            .collect();
        format!("[{}]", items.join(", "))
    };

    let init_mem_expr = cfg.init_mem_expr.as_deref().unwrap_or("emptyMemory");
    let table_expr = render_shadow_provenance_table_lean(&trace.shadow_provenance);
    let trace_expr =
        render_raw_byte_trace_lean(trace, init_mem_expr, &cfg.inlined_callee_modules);

    let _ = writeln!(
        out,
        "@[reducible]\ndef calleeSigs : List CapturedMir := {callee_sigs_list}\n"
    );
    let _ = writeln!(
        out,
        "@[reducible]\ndef shadowTable : ShadowProvenanceTable := {table_expr}\n"
    );
    let _ = writeln!(
        out,
        "@[reducible]\ndef observedRawTrace : RawByteTrace :=\n{trace_expr}\n"
    );

    let root_body = format!("{}.body", cfg.root_mir_module);
    let fuel = cfg.fuel;

    if cfg.check_branches {
        let _ = writeln!(
            out,
            "set_option maxHeartbeats 2000000 in\n\
             theorem trace_consistent :\n\
             \x20   ∃ obsTrace tr out,\n\
             \x20     decodeRawByteTrace {root_body} calleeSigs shadowTable observedRawTrace = some obsTrace ∧\n\
             \x20     MatchesObservedEvents obsTrace.events tr ∧\n\
             \x20     MatchesObservedOutcome obsTrace.outcome out ∧\n\
             \x20     ReachesRet\n\
             \x20       (mirStatefulTree {root_body} obsTrace.args\n\
             \x20         {{ obsTrace.initMem with callees := obsTrace.inlinedCallees }})\n\
             \x20       tr out :=\n\
             \x20 checkRawByteTraceFullBounded_sound {fuel} {root_body} calleeSigs shadowTable observedRawTrace rfl\n"
        );
    } else {
        let _ = writeln!(
            out,
            "set_option maxHeartbeats 2000000 in\n\
             theorem trace_consistent :\n\
             \x20   ∃ obsTrace tr out,\n\
             \x20     decodeRawByteTrace {root_body} calleeSigs shadowTable observedRawTrace = some obsTrace ∧\n\
             \x20     MatchesObservedEvents obsTrace.events tr ∧\n\
             \x20     MatchesObservedOutcome obsTrace.outcome out ∧\n\
             \x20     ReachesRet\n\
             \x20       (mirObsErasedStatefulTree {root_body} obsTrace.args\n\
             \x20         {{ obsTrace.initMem with callees := obsTrace.inlinedCallees }})\n\
             \x20       tr out :=\n\
             \x20 checkRawByteTraceObsErasedBounded_sound {fuel} {root_body} calleeSigs shadowTable observedRawTrace rfl\n"
        );
    }

    out.push_str(&render_trace_diag_eval_lean_snippet(
        "trace_diag_ok",
        cfg,
        "calleeSigs",
        "shadowTable",
        "observedRawTrace",
        "ok",
        false,
    ));

    let _ = writeln!(out, "end {}", cfg.module_namespace);
    out
}

/// Render a batched Lean 4 verification and diagnostic evaluation module across
/// multiple [`BatchTraceEvalCase`] entries, sharing a single Lake/Lean
/// invocation and import header set.
pub fn render_batch_trace_eval_lean_module(
    module_namespace: &str,
    cases: &[BatchTraceEvalCase],
    emit_eval_commands: bool,
) -> String {
    let mut out = String::new();
    out.push_str("import Trusted\n");
    out.push_str("import Anneal\n");

    let mut imported: Vec<String> = Vec::new();
    for case in cases {
        for m in std::iter::once(&case.config.root_mir_module)
            .chain(case.config.callee_sig_modules.iter())
            .chain(case.config.inlined_callee_modules.iter())
        {
            if !imported.contains(m) {
                let _ = writeln!(out, "import {m}");
                imported.push(m.clone());
            }
        }
    }

    let _ = writeln!(out, "\nnamespace {module_namespace}\n");
    out.push_str("open Trusted.Effect\n");
    out.push_str("open Trusted.ITree\n");
    out.push_str("open Trusted.Rustc.V2026_06_01.MirAst\n");
    out.push_str("open Trusted.Rustc.V2026_06_01.MirSemantics\n");
    out.push_str("open Trusted.VerificationResult\n");
    out.push_str("open Anneal.Rustc.V2026_06_01.TraceCheck\n\n");

    for case in cases {
        let id = &case.case_ident;
        let cfg = &case.config;
        let callee_sigs_list = if cfg.callee_sig_modules.is_empty() {
            "[]".to_string()
        } else {
            let items: Vec<String> = cfg
                .callee_sig_modules
                .iter()
                .map(|m| format!("{m}.body"))
                .collect();
            format!("[{}]", items.join(", "))
        };
        let init_mem_expr = cfg.init_mem_expr.as_deref().unwrap_or("emptyMemory");
        let table_expr = render_shadow_provenance_table_lean(&case.trace.shadow_provenance);
        let trace_expr =
            render_raw_byte_trace_lean(&case.trace, init_mem_expr, &cfg.inlined_callee_modules);

        let sigs_ident = format!("{id}_calleeSigs");
        let table_ident = format!("{id}_shadowTable");
        let trace_ident = format!("{id}_rawTrace");

        let _ = writeln!(
            out,
            "@[reducible]\ndef {sigs_ident} : List CapturedMir := {callee_sigs_list}\n"
        );
        let _ = writeln!(
            out,
            "@[reducible]\ndef {table_ident} : ShadowProvenanceTable := {table_expr}\n"
        );
        let _ = writeln!(
            out,
            "@[reducible]\ndef {trace_ident} : RawByteTrace :=\n{trace_expr}\n"
        );

        let expected_tag = case.expected_diag_tag.as_deref().unwrap_or("ok");
        if expected_tag == "ok" {
            let root_body = format!("{}.body", cfg.root_mir_module);
            let fuel = cfg.fuel;
            let sound_thm = format!("{id}_trace_consistent");
            if cfg.check_branches {
                let _ = writeln!(
                    out,
                    "set_option maxHeartbeats 2000000 in\n\
                     theorem {sound_thm} :\n\
                     \x20   ∃ obsTrace tr out,\n\
                     \x20     decodeRawByteTrace {root_body} {sigs_ident} {table_ident} {trace_ident} = some obsTrace ∧\n\
                     \x20     MatchesObservedEvents obsTrace.events tr ∧\n\
                     \x20     MatchesObservedOutcome obsTrace.outcome out ∧\n\
                     \x20     ReachesRet\n\
                     \x20       (mirStatefulTree {root_body} obsTrace.args\n\
                     \x20         {{ obsTrace.initMem with callees := obsTrace.inlinedCallees }})\n\
                     \x20       tr out :=\n\
                     \x20 checkRawByteTraceFullBounded_sound {fuel} {root_body} {sigs_ident} {table_ident} {trace_ident} rfl\n"
                );
            } else {
                let _ = writeln!(
                    out,
                    "set_option maxHeartbeats 2000000 in\n\
                     theorem {sound_thm} :\n\
                     \x20   ∃ obsTrace tr out,\n\
                     \x20     decodeRawByteTrace {root_body} {sigs_ident} {table_ident} {trace_ident} = some obsTrace ∧\n\
                     \x20     MatchesObservedEvents obsTrace.events tr ∧\n\
                     \x20     MatchesObservedOutcome obsTrace.outcome out ∧\n\
                     \x20     ReachesRet\n\
                     \x20       (mirObsErasedStatefulTree {root_body} obsTrace.args\n\
                     \x20         {{ obsTrace.initMem with callees := obsTrace.inlinedCallees }})\n\
                     \x20       tr out :=\n\
                     \x20 checkRawByteTraceObsErasedBounded_sound {fuel} {root_body} {sigs_ident} {table_ident} {trace_ident} rfl\n"
                );
            }
        }

        let diag_thm = format!("{id}_diag_tag");
        out.push_str(&render_trace_diag_eval_lean_snippet(
            &diag_thm,
            cfg,
            &sigs_ident,
            &table_ident,
            &trace_ident,
            expected_tag,
            emit_eval_commands,
        ));

        if let Some(ref tampered) = case.tampered_outcome {
            let tampered_thm = format!("{id}_tampered_outcome_mismatch");
            out.push_str(&render_tampered_outcome_diag_lean_snippet(
                &tampered_thm,
                cfg,
                &sigs_ident,
                &table_ident,
                &trace_ident,
                tampered,
            ));
        }
    }

    let _ = writeln!(out, "end {module_namespace}");
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[repr(C)]
    #[derive(Clone, Copy)]
    struct TestPaddedStruct {
        flag: u8,
        value: u32,
    }

    #[test]
    fn value_as_raw_bytes_preserves_exact_layout_and_padding_bytes() {
        let mut s = TestPaddedStruct {
            flag: 1,
            value: 0x0403_0201,
        };
        unsafe {
            let ptr = (&mut s as *mut TestPaddedStruct).cast::<u8>();
            *ptr.add(1) = 0xAA;
            *ptr.add(2) = 0xBB;
            *ptr.add(3) = 0xCC;
        }
        let raw = value_as_raw_bytes(&s);
        assert_eq!(raw, vec![1, 0xAA, 0xBB, 0xCC, 1, 2, 3, 4]);
        assert!(value_as_raw_bytes(&()).is_empty());
    }

    #[test]
    fn trace_recorder_captures_normal_and_panicking_external_calls() {
        let arg: u32 = 7;
        let (ok_res, ok_trace) =
            TraceRecorder::observe_root("demo::root", vec![value_as_raw_bytes(&arg)], |rec| {
                rec.record_branch(0);
                rec.observe_ext_call("demo::ext", vec![value_as_raw_bytes(&arg)], || 14u32)
            });
        assert_eq!(ok_res.expect("normal return"), 14);
        assert_eq!(
            ok_trace.events,
            vec![
                RecordedEvent::Branch { tag: 0 },
                RecordedEvent::ExtCall {
                    def_path: "demo::ext".to_string(),
                    raw_args: vec![vec![7, 0, 0, 0]],
                    raw_ret: vec![14, 0, 0, 0],
                },
            ]
        );
        assert_eq!(
            ok_trace.outcome,
            RecordedOutcome::Normal {
                raw_ret: vec![14, 0, 0, 0]
            }
        );

        let (panic_res, panic_trace) = TraceRecorder::observe_root("demo::panic_root", vec![], |rec| {
            rec.observe_ext_call("demo::boom", vec![], || -> u32 {
                panic!("simulated external panic");
            })
        });
        assert!(panic_res.is_err());
        assert_eq!(
            panic_trace.events,
            vec![RecordedEvent::ExtCallPanic {
                def_path: "demo::boom".to_string(),
                raw_args: vec![],
            }]
        );
        assert_eq!(panic_trace.outcome, RecordedOutcome::Panic);
    }

    #[test]
    fn render_single_and_batch_lean_modules_emit_soundness_and_diag_assertions() {
        let trace = RecordedRawTrace {
            root_def_path: "trace_pkg::process_packet".to_string(),
            raw_args: vec![vec![1, 0xAA, 0xBB, 0xCC, 11, 0, 0, 0], vec![10, 0, 0, 0]],
            shadow_provenance: vec![RecordedShadowAlloc {
                base_addr: 0x1000,
                byte_len: 4,
                alloc_id: 7,
                tag: 7,
            }],
            events: vec![RecordedEvent::ExtCall {
                def_path: "trace_pkg::ext_scale_add".to_string(),
                raw_args: vec![vec![10, 0, 0, 0], vec![11, 0, 0, 0]],
                raw_ret: vec![21, 0, 0, 0],
            }],
            outcome: RecordedOutcome::Normal {
                raw_ret: vec![42, 0, 0, 0],
            },
        };
        let cfg = TraceCheckModuleConfig {
            module_namespace: "TraceVerify.Unit".to_string(),
            root_mir_module: "Mir.TracePkg.process_packet".to_string(),
            callee_sig_modules: vec!["Mir.TracePkg.ext_scale_add".to_string()],
            inlined_callee_modules: vec!["Mir.TracePkg.helper_double".to_string()],
            init_mem_expr: None,
            fuel: 60,
            check_branches: false,
        };

        let single_mod = render_trace_check_lean_module(&cfg, &trace);
        assert!(single_mod.contains("checkRawByteTraceObsErasedBounded_sound 60"));
        assert!(single_mod.contains("diagnoseRawByteTraceObsErasedBounded 60"));
        assert!(single_mod.contains(".tagName = \"ok\""));
        assert!(single_mod.contains("{ baseAddr := 4096, byteLen := 4, allocId := 7, tag := 7 }"));

        let batch_mod = render_batch_trace_eval_lean_module(
            "TraceVerify.Batch",
            &[BatchTraceEvalCase {
                case_ident: "packet_case".to_string(),
                config: cfg,
                trace,
                expected_diag_tag: Some("ok".to_string()),
                tampered_outcome: Some(RecordedOutcome::Normal {
                    raw_ret: vec![99, 0, 0, 0],
                }),
            }],
            true,
        );
        assert!(batch_mod.contains("theorem packet_case_trace_consistent"));
        assert!(batch_mod.contains("theorem packet_case_diag_tag"));
        assert!(batch_mod.contains("#eval (diagnoseRawByteTraceObsErasedBounded 60"));
        assert!(batch_mod.contains("theorem packet_case_tampered_outcome_mismatch"));
        assert!(batch_mod.contains("outcome := .normal [99, 0, 0, 0]"));
        assert!(batch_mod.contains(".tagName = \"outcome_mismatch\""));
    }
}
