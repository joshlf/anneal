//! Milestone 1: Source-to-source Rust auto-instrumenter built on `syn`, `quote`,
//! and `prettyplease`.
//!
//! Emits a self-contained `#![no_std]`-compatible runtime prelude (`TraceRecorder`,
//! `RecordedEvent`, `RecordedOutcome`, `value_as_raw_bytes<T>`, `EnvSchedule` with
//! deterministic per-callee response queues and optional `PanicOnCall(usize)`
//! injection) and synthesizes per-callee wrappers plus an instrumented entry point
//! `__anneal_traced_<fn_name>`.

use std::collections::{BTreeMap, VecDeque};
use std::fmt;

use proc_macro2::{Ident, Span, TokenStream};
use quote::{format_ident, quote};
use syn::visit_mut::VisitMut;
use syn::{Expr, ExprCall, ExprPath, File, FnArg, Item, ItemFn, Pat, PatIdent, ReturnType};

/// Copies the exact in-memory byte representation of `val` (including all
/// inter-field and trailing padding bytes) into a freshly allocated `Vec<u8>`.
pub fn value_as_raw_bytes<T: ?Sized>(val: &T) -> Vec<u8> {
    let size = core::mem::size_of_val(val);
    let ptr = (val as *const T).cast::<core::mem::MaybeUninit<u8>>();
    let mut out = Vec::with_capacity(size);
    for offset in 0..size {
        // SAFETY: `offset < size_of_val(val)` stays within the live allocation of `val`.
        // Reading through `MaybeUninit<u8>` avoids typed `*const u8` load provenance traps on
        // padding bytes prior to concrete byte materialization for native trace recording.
        let byte = unsafe { (*ptr.add(offset)).assume_init() };
        out.push(byte);
    }
    out
}

/// Deterministic action prescribed by an [`EnvSchedule`] for an external call site.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EnvAction {
    /// Invoke the underlying implementation normally and record its return bytes.
    PassThrough,
    /// Return a deterministic pre-scheduled byte payload.
    ReturnBytes(Vec<u8>),
    /// Deterministically trigger a mid-call panic at call index `k`.
    PanicOnCall(usize),
}

/// Deterministic environment response schedule (`inputs-over-time`) across external
/// callees, supporting per-callee response queues and optional `PanicOnCall(usize)`
/// unwind fault injection.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct EnvSchedule {
    /// Per-callee FIFO queues of raw return-value byte buffers.
    pub callee_queues: BTreeMap<String, VecDeque<Vec<u8>>>,
    /// Per-callee fallback constant bytes when the FIFO queue is exhausted.
    pub callee_defaults: BTreeMap<String, Vec<u8>>,
    /// Optional global call index (`0`-based) at which any external call panics.
    pub global_panic_on_call: Option<usize>,
    /// Optional per-callee call index (`0`-based) at which that callee panics.
    pub callee_panic_on_call: BTreeMap<String, usize>,
    /// Per-callee count of invocations served so far.
    callee_call_counts: BTreeMap<String, usize>,
}

impl EnvSchedule {
    /// Creates an empty pass-through schedule with no injected panics.
    pub fn new() -> Self {
        Self::default()
    }

    /// Configures a deterministic global `PanicOnCall(k)` trigger.
    pub fn with_panic_on_call(mut self, call_index: usize) -> Self {
        self.global_panic_on_call = Some(call_index);
        self
    }

    /// Sets or updates the global `PanicOnCall(k)` trigger.
    pub fn set_panic_on_call(&mut self, call_index: usize) {
        self.global_panic_on_call = Some(call_index);
    }

    /// Configures a per-callee `PanicOnCall(k)` trigger for `callee`.
    pub fn set_callee_panic_on_call(&mut self, callee: &str, call_index: usize) {
        self.callee_panic_on_call.insert(callee.to_string(), call_index);
    }

    /// Appends a single scheduled raw-byte return payload to `callee`'s queue.
    pub fn push_callee_response(&mut self, callee: &str, bytes: Vec<u8>) {
        self.callee_queues
            .entry(callee.to_string())
            .or_default()
            .push_back(bytes);
    }

    /// Sets the default fallback byte payload for `callee` once its queue empties.
    pub fn set_callee_default(&mut self, callee: &str, bytes: Vec<u8>) {
        self.callee_defaults.insert(callee.to_string(), bytes);
    }

    /// Returns `true` if `global_call_index` or `callee_call_index` matches a configured
    /// `PanicOnCall` trigger.
    pub fn should_panic(&self, callee: &str, global_call_index: usize, callee_call_index: usize) -> bool {
        if self.global_panic_on_call == Some(global_call_index) {
            return true;
        }
        if self.callee_panic_on_call.get(callee).copied() == Some(callee_call_index) {
            return true;
        }
        false
    }

    /// Advances the schedule state for `callee` at `global_call_index` and returns the
    /// prescribed [`EnvAction`].
    pub fn next_action(&mut self, callee: &str, global_call_index: usize) -> EnvAction {
        let count_entry = self.callee_call_counts.entry(callee.to_string()).or_insert(0);
        let callee_call_idx = *count_entry;
        *count_entry += 1;

        if self.should_panic(callee, global_call_index, callee_call_idx) {
            return EnvAction::PanicOnCall(global_call_index);
        }

        if let Some(queue) = self.callee_queues.get_mut(callee)
            && let Some(front) = queue.pop_front()
        {
            return EnvAction::ReturnBytes(front);
        }

        if let Some(default_bytes) = self.callee_defaults.get(callee) {
            return EnvAction::ReturnBytes(default_bytes.clone());
        }

        EnvAction::PassThrough
    }
}

/// Observable trace event recorded during native or instrumented execution.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RecordedEvent {
    /// Entry into the traced target function with raw argument byte snapshots
    /// (preserving inter-field padding bytes).
    Entry {
        fn_name: String,
        arg_bytes: Vec<Vec<u8>>,
    },
    /// Execution of an observable control-flow branch tag.
    Branch {
        tag: u32,
    },
    /// Completed invocation of an external callee with raw argument and return bytes.
    ExtCall {
        callee: String,
        call_index: usize,
        arg_bytes: Vec<Vec<u8>>,
        ret_bytes: Vec<u8>,
    },
    /// Firing of a scheduled `PanicOnCall(k)` fault injection inside an external callee.
    ScheduledPanic {
        callee: String,
        call_index: usize,
    },
}

/// Terminal outcome recorded for a traced function invocation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RecordedOutcome {
    /// Normal return carrying the raw return value bytes (including padding).
    Return(Vec<u8>),
    /// Unwinding panic observed before normal return.
    Panic,
}

/// Deterministic in-memory trace recorder threaded through `__anneal_traced_<fn_name>`.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct TraceRecorder {
    /// Active environment schedule governing external callees.
    pub schedule: EnvSchedule,
    /// Ordered log of recorded entry, branch, external call, and panic events.
    pub events: Vec<RecordedEvent>,
    /// Compact sequence of visited basic-block / branch tags.
    pub branch_tags: Vec<u32>,
    /// Final execution outcome (`Return(bytes)` or `Panic`).
    pub outcome: Option<RecordedOutcome>,
    /// Total number of external calls initiated during this execution.
    pub call_count: usize,
}

impl TraceRecorder {
    /// Creates a fresh [`TraceRecorder`] with an empty pass-through schedule.
    pub fn new() -> Self {
        Self::default()
    }

    /// Creates a fresh [`TraceRecorder`] configured with `schedule`.
    pub fn with_schedule(schedule: EnvSchedule) -> Self {
        Self {
            schedule,
            events: Vec::new(),
            branch_tags: Vec::new(),
            outcome: None,
            call_count: 0,
        }
    }

    /// Records target function entry along with raw argument byte slices.
    pub fn record_entry(&mut self, fn_name: &str, arg_bytes: Vec<Vec<u8>>) {
        self.events.push(RecordedEvent::Entry {
            fn_name: fn_name.to_string(),
            arg_bytes,
        });
    }

    /// Records a control-flow branch tag.
    pub fn record_branch(&mut self, tag: u32) {
        self.branch_tags.push(tag);
        self.events.push(RecordedEvent::Branch { tag });
    }

    /// Consults the embedded [`EnvSchedule`] before invoking `callee`. If `PanicOnCall(k)`
    /// fires, records [`RecordedEvent::ScheduledPanic`] and returns `(call_index, EnvAction::PanicOnCall(k))`.
    pub fn step_ext_call(&mut self, callee: &str) -> (usize, EnvAction) {
        let idx = self.call_count;
        self.call_count += 1;
        let action = self.schedule.next_action(callee, idx);
        if matches!(action, EnvAction::PanicOnCall(_)) {
            self.events.push(RecordedEvent::ScheduledPanic {
                callee: callee.to_string(),
                call_index: idx,
            });
            self.outcome = Some(RecordedOutcome::Panic);
        }
        (idx, action)
    }

    /// Records completion of an external call with raw argument and return bytes.
    pub fn record_ext_call(
        &mut self,
        callee: &str,
        call_index: usize,
        arg_bytes: Vec<Vec<u8>>,
        ret_bytes: Vec<u8>,
    ) {
        self.events.push(RecordedEvent::ExtCall {
            callee: callee.to_string(),
            call_index,
            arg_bytes,
            ret_bytes,
        });
    }

    /// Records a normal function return by capturing `value_as_raw_bytes(val)`.
    pub fn finish_return<T: ?Sized>(&mut self, val: &T) {
        self.outcome = Some(RecordedOutcome::Return(value_as_raw_bytes(val)));
    }

    /// Records an unwinding panic outcome.
    pub fn finish_panic(&mut self) {
        self.outcome = Some(RecordedOutcome::Panic);
    }

    /// Returns `true` iff the recorded execution terminated via panic.
    pub fn is_panic(&self) -> bool {
        matches!(self.outcome, Some(RecordedOutcome::Panic))
    }

    /// Extracts the canonical external-call sequence shape `(callee_name, call_index)`
    /// across both completed calls and scheduled-panic calls.
    pub fn ext_call_sequence_shape(&self) -> Vec<(String, usize)> {
        let mut shape = Vec::new();
        for ev in &self.events {
            match ev {
                RecordedEvent::ExtCall {
                    callee, call_index, ..
                }
                | RecordedEvent::ScheduledPanic { callee, call_index } => {
                    shape.push((callee.clone(), *call_index));
                }
                RecordedEvent::Entry { .. } | RecordedEvent::Branch { .. } => {}
            }
        }
        shape
    }
}

/// Configuration knobs for [`instrument_source_with_config`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InstrumentConfig {
    /// When `true`, emit a strictly `#![no_std]` + `extern crate alloc` prelude with zero
    /// references to `std::panic::catch_unwind`. When `false` (default harness mode), emit
    /// both the `#![no_std]`-compatible core runtime types and a `std::panic::catch_unwind`
    /// entry-point wrapper.
    pub no_std_mode: bool,
    /// Whether to inject branch tag recording statements into `if` / `match` blocks inside
    /// the traced copy of `fn_name`.
    pub instrument_branches: bool,
}

impl Default for InstrumentConfig {
    fn default() -> Self {
        Self {
            no_std_mode: false,
            instrument_branches: true,
        }
    }
}

/// Detailed output returned by [`instrument_source_with_config`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InstrumentationResult {
    /// Complete, formatted Rust module source code ready for `rustc`.
    pub source: String,
    /// Name of the synthesized traced entry point (`__anneal_traced_<fn_name>`).
    pub traced_fn_name: String,
    /// Name of the synthesized panic-catching entry point (`__anneal_traced_catch_<fn_name>`)
    /// when `no_std_mode == false`.
    pub catch_unwind_fn_name: Option<String>,
    /// Names of synthesized external callee wrapper functions (`__anneal_ext_<callee>`).
    pub wrapper_fn_names: Vec<String>,
}

/// Errors produced when auto-instrumenting Rust source code.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum InstrumentationError {
    /// Input source failed `syn::parse_file`.
    ParseError(String),
    /// Requested target function `fn_name` was not found at module top level.
    TargetFunctionNotFound(String),
    /// Target function has unsupported receiver (`self`) or pattern parameter.
    UnsupportedSignature(String),
}

impl fmt::Display for InstrumentationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::ParseError(msg) => write!(f, "failed to parse Rust source: {msg}"),
            Self::TargetFunctionNotFound(name) => {
                write!(f, "target function `{name}` not found in source file")
            }
            Self::UnsupportedSignature(msg) => {
                write!(f, "unsupported function signature: {msg}")
            }
        }
    }
}

impl std::error::Error for InstrumentationError {}

/// Emits the self-contained `__anneal_rt` runtime module as a [`TokenStream`].
///
/// When `no_std_mode` is `true`, the generated module uses only `core` + `alloc` (`Vec`,
/// `String`, `BTreeMap`, `VecDeque`) and contains zero `std` imports, making it directly
/// compilable inside `#![no_std]` crates.
pub fn emit_runtime_prelude(no_std_mode: bool) -> TokenStream {
    let alloc_import = if no_std_mode {
        quote! {
            extern crate alloc;
            use alloc::collections::BTreeMap;
            use alloc::string::{String, ToString};
            use alloc::vec::Vec;
        }
    } else {
        quote! {
            use std::collections::BTreeMap;
            use std::string::{String, ToString};
            use std::vec::Vec;
        }
    };

    quote! {
        #[allow(dead_code, unused_imports, clippy::all)]
        pub mod __anneal_rt {
            #alloc_import

            pub fn value_as_raw_bytes<T: ?Sized>(val: &T) -> Vec<u8> {
                let size = core::mem::size_of_val(val);
                let ptr = (val as *const T).cast::<core::mem::MaybeUninit<u8>>();
                let mut out = Vec::with_capacity(size);
                let mut i = 0usize;
                while i < size {
                    let b = unsafe { (*ptr.add(i)).assume_init() };
                    out.push(b);
                    i += 1;
                }
                out
            }

            #[derive(Debug, Clone, PartialEq, Eq)]
            pub enum EnvAction {
                PassThrough,
                ReturnBytes(Vec<u8>),
                PanicOnCall(usize),
            }

            #[derive(Debug, Clone, Default, PartialEq, Eq)]
            pub struct EnvSchedule {
                pub callee_queues: BTreeMap<String, Vec<Vec<u8>>>,
                pub callee_defaults: BTreeMap<String, Vec<u8>>,
                pub callee_cursors: BTreeMap<String, usize>,
                pub global_panic_on_call: Option<usize>,
                pub callee_panic_on_call: BTreeMap<String, usize>,
            }

            impl EnvSchedule {
                pub fn new() -> Self {
                    Self::default()
                }

                pub fn with_panic_on_call(mut self, call_index: usize) -> Self {
                    self.global_panic_on_call = Some(call_index);
                    self
                }

                pub fn set_panic_on_call(&mut self, call_index: usize) {
                    self.global_panic_on_call = Some(call_index);
                }

                pub fn set_callee_panic_on_call(&mut self, callee: &str, call_index: usize) {
                    self.callee_panic_on_call.insert(callee.to_string(), call_index);
                }

                pub fn push_callee_response(&mut self, callee: &str, bytes: Vec<u8>) {
                    self.callee_queues
                        .entry(callee.to_string())
                        .or_default()
                        .push(bytes);
                }

                pub fn set_callee_default(&mut self, callee: &str, bytes: Vec<u8>) {
                    self.callee_defaults.insert(callee.to_string(), bytes);
                }

                pub fn next_action(&mut self, callee: &str, global_call_index: usize) -> EnvAction {
                    let cursor = self.callee_cursors.entry(callee.to_string()).or_insert(0);
                    let local_idx = *cursor;
                    *cursor += 1;

                    if self.global_panic_on_call == Some(global_call_index) {
                        return EnvAction::PanicOnCall(global_call_index);
                    }
                    if self.callee_panic_on_call.get(callee).copied() == Some(local_idx) {
                        return EnvAction::PanicOnCall(global_call_index);
                    }
                    if let Some(list) = self.callee_queues.get(callee) {
                        if let Some(item) = list.get(local_idx) {
                            return EnvAction::ReturnBytes(item.clone());
                        }
                    }
                    if let Some(default_bytes) = self.callee_defaults.get(callee) {
                        return EnvAction::ReturnBytes(default_bytes.clone());
                    }
                    EnvAction::PassThrough
                }
            }

            #[derive(Debug, Clone, PartialEq, Eq)]
            pub enum RecordedEvent {
                Entry {
                    fn_name: String,
                    arg_bytes: Vec<Vec<u8>>,
                },
                Branch {
                    tag: u32,
                },
                ExtCall {
                    callee: String,
                    call_index: usize,
                    arg_bytes: Vec<Vec<u8>>,
                    ret_bytes: Vec<u8>,
                },
                ScheduledPanic {
                    callee: String,
                    call_index: usize,
                },
            }

            #[derive(Debug, Clone, PartialEq, Eq)]
            pub enum RecordedOutcome {
                Return(Vec<u8>),
                Panic,
            }

            #[derive(Debug, Clone, Default, PartialEq, Eq)]
            pub struct TraceRecorder {
                pub schedule: EnvSchedule,
                pub events: Vec<RecordedEvent>,
                pub branch_tags: Vec<u32>,
                pub outcome: Option<RecordedOutcome>,
                pub call_count: usize,
            }

            impl TraceRecorder {
                pub fn new() -> Self {
                    Self::default()
                }

                pub fn with_schedule(schedule: EnvSchedule) -> Self {
                    Self {
                        schedule,
                        events: Vec::new(),
                        branch_tags: Vec::new(),
                        outcome: None,
                        call_count: 0,
                    }
                }

                pub fn record_entry(&mut self, fn_name: &str, arg_bytes: Vec<Vec<u8>>) {
                    self.events.push(RecordedEvent::Entry {
                        fn_name: fn_name.to_string(),
                        arg_bytes,
                    });
                }

                pub fn record_branch(&mut self, tag: u32) {
                    self.branch_tags.push(tag);
                    self.events.push(RecordedEvent::Branch { tag });
                }

                pub fn step_ext_call(&mut self, callee: &str) -> (usize, EnvAction) {
                    let idx = self.call_count;
                    self.call_count += 1;
                    let action = self.schedule.next_action(callee, idx);
                    if matches!(action, EnvAction::PanicOnCall(_)) {
                        self.events.push(RecordedEvent::ScheduledPanic {
                            callee: callee.to_string(),
                            call_index: idx,
                        });
                        self.outcome = Some(RecordedOutcome::Panic);
                    }
                    (idx, action)
                }

                pub fn record_ext_call(
                    &mut self,
                    callee: &str,
                    call_index: usize,
                    arg_bytes: Vec<Vec<u8>>,
                    ret_bytes: Vec<u8>,
                ) {
                    self.events.push(RecordedEvent::ExtCall {
                        callee: callee.to_string(),
                        call_index,
                        arg_bytes,
                        ret_bytes,
                    });
                }

                pub fn finish_return<T: ?Sized>(&mut self, val: &T) {
                    self.outcome = Some(RecordedOutcome::Return(value_as_raw_bytes(val)));
                }

                pub fn finish_panic(&mut self) {
                    self.outcome = Some(RecordedOutcome::Panic);
                }
            }
        }
    }
}

/// AST visitor that rewrites calls to registered external callees into calls to
/// `__anneal_ext_<callee>(__rec, ...)` and optionally records branch tags.
struct BodyCallRewriter<'a> {
    ext_callees: &'a [&'a str],
    rec_ident: Ident,
    instrument_branches: bool,
    next_branch_tag: u32,
}

impl VisitMut for BodyCallRewriter<'_> {
    fn visit_expr_call_mut(&mut self, node: &mut ExprCall) {
        // Rewrite nested argument expressions first.
        for arg in node.args.iter_mut() {
            self.visit_expr_mut(arg);
        }

        if let Expr::Path(ExprPath { path, .. }) = node.func.as_ref()
            && path.segments.len() == 1
        {
            let ident_str = path.segments[0].ident.to_string();
            if self.ext_callees.contains(&ident_str.as_str()) {
                let wrapper_ident = format_ident!("__anneal_ext_{}", ident_str);
                let rec_ident = &self.rec_ident;
                let mut new_args = syn::punctuated::Punctuated::new();
                let rec_expr: Expr = syn::parse_quote!(#rec_ident);
                new_args.push(rec_expr);
                for existing in node.args.iter().cloned() {
                    new_args.push(existing);
                }
                *node.func = syn::parse_quote!(#wrapper_ident);
                node.args = new_args;
                return;
            }
        }

        self.visit_expr_mut(&mut node.func);
    }

    fn visit_expr_if_mut(&mut self, node: &mut syn::ExprIf) {
        self.visit_expr_mut(&mut node.cond);
        if self.instrument_branches {
            let tag = self.next_branch_tag;
            self.next_branch_tag += 1;
            let rec_ident = &self.rec_ident;
            let record_stmt: syn::Stmt = syn::parse_quote! {
                #rec_ident.record_branch(#tag);
            };
            node.then_branch.stmts.insert(0, record_stmt);
        }
        self.visit_block_mut(&mut node.then_branch);
        if let Some((_, else_expr)) = &mut node.else_branch {
            self.visit_expr_mut(else_expr);
        }
    }

    fn visit_expr_match_mut(&mut self, node: &mut syn::ExprMatch) {
        self.visit_expr_mut(&mut node.expr);
        for arm in &mut node.arms {
            if let Some((_, guard_expr)) = &mut arm.guard {
                self.visit_expr_mut(guard_expr);
            }
            self.visit_expr_mut(&mut arm.body);
            if self.instrument_branches {
                let tag = self.next_branch_tag;
                self.next_branch_tag += 1;
                let rec_ident = &self.rec_ident;
                let prev_body = (*arm.body).clone();
                *arm.body = syn::parse_quote!({
                    #rec_ident.record_branch(#tag);
                    #prev_body
                });
            }
        }
    }
}

/// Extracts normalized `(ident, ty)` parameter pairs for a top-level function.
fn extract_fn_params(item_fn: &ItemFn) -> Result<Vec<(Ident, Box<syn::Type>)>, InstrumentationError> {
    let mut params = Vec::new();
    for (idx, input) in item_fn.sig.inputs.iter().enumerate() {
        match input {
            FnArg::Receiver(_) => {
                return Err(InstrumentationError::UnsupportedSignature(format!(
                    "method receiver `self` not supported in `{}`",
                    item_fn.sig.ident
                )));
            }
            FnArg::Typed(pat_ty) => {
                let ident = match pat_ty.pat.as_ref() {
                    Pat::Ident(PatIdent { ident, .. }) => ident.clone(),
                    _ => format_ident!("__arg_{}", idx),
                };
                params.push((ident, pat_ty.ty.clone()));
            }
        }
    }
    Ok(params)
}

/// Synthesizes `__anneal_ext_<callee>` for an external callee found in `file`.
fn synthesize_ext_wrapper(callee_fn: &ItemFn) -> Result<(String, Item), InstrumentationError> {
    let callee_ident = &callee_fn.sig.ident;
    let callee_name = callee_ident.to_string();
    let wrapper_ident = format_ident!("__anneal_ext_{}", callee_ident);
    let rec_ident = Ident::new("__rec", Span::call_site());

    let params = extract_fn_params(callee_fn)?;
    let param_decls = params.iter().map(|(id, ty)| quote!(#id: #ty));
    let capture_args = params
        .iter()
        .map(|(id, _)| quote!(__anneal_rt::value_as_raw_bytes(&#id)));
    let forward_args = params.iter().map(|(id, _)| quote!(#id));

    let output = &callee_fn.sig.output;
    let ret_ty: TokenStream = match output {
        ReturnType::Default => quote!(()),
        ReturnType::Type(_, ty) => quote!(#ty),
    };
    let wrapper_tokens = quote! {
        #[allow(dead_code, clippy::too_many_arguments)]
        pub fn #wrapper_ident(
            #rec_ident: &mut __anneal_rt::TraceRecorder,
            #(#param_decls),*
        ) #output {
            let mut __arg_bytes = Vec::new();
            #( __arg_bytes.push(#capture_args); )*
            let (__call_idx, __action) = #rec_ident.step_ext_call(#callee_name);
            match __action {
                __anneal_rt::EnvAction::PanicOnCall(__k) => {
                    panic!("anneal scheduled PanicOnCall({}) triggered in `{}`", __k, #callee_name);
                }
                __anneal_rt::EnvAction::ReturnBytes(__sched_bytes)
                    if __sched_bytes.len() == core::mem::size_of::<#ret_ty>() =>
                {
                    let mut __slot = core::mem::MaybeUninit::<#ret_ty>::zeroed();
                    unsafe {
                        core::ptr::copy_nonoverlapping(
                            __sched_bytes.as_ptr(),
                            __slot.as_mut_ptr() as *mut u8,
                            core::mem::size_of::<#ret_ty>(),
                        );
                    }
                    let __ret: #ret_ty = unsafe { __slot.assume_init() };
                    #rec_ident.record_ext_call(#callee_name, __call_idx, __arg_bytes, __sched_bytes);
                    return __ret;
                }
                _ => {}
            }
            let __ret = #callee_ident(#(#forward_args),*);
            let __ret_bytes = __anneal_rt::value_as_raw_bytes(&__ret);
            #rec_ident.record_ext_call(#callee_name, __call_idx, __arg_bytes, __ret_bytes);
            __ret
        }
    };

    let item: Item = syn::parse2(wrapper_tokens)
        .map_err(|e| InstrumentationError::ParseError(e.to_string()))?;
    Ok((wrapper_ident.to_string(), item))
}

/// Instruments `source` for target function `fn_name` and external callees `ext_callees`
/// using default [`InstrumentConfig`] settings.
pub fn instrument_source(
    source: &str,
    fn_name: &str,
    ext_callees: &[&str],
) -> Result<String, InstrumentationError> {
    Ok(
        instrument_source_with_config(source, fn_name, ext_callees, &InstrumentConfig::default())?
            .source,
    )
}

/// Instruments `source` using `syn::parse_file`, `syn::visit_mut::VisitMut`, `quote!`, and
/// `prettyplease::unparse`, returning the formatted source and synthesized symbol names.
pub fn instrument_source_with_config(
    source: &str,
    fn_name: &str,
    ext_callees: &[&str],
    config: &InstrumentConfig,
) -> Result<InstrumentationResult, InstrumentationError> {
    let mut parsed_file: File = syn::parse_str(source)
        .map_err(|e| InstrumentationError::ParseError(e.to_string()))?;

    // Check if the input file already carries `#![no_std]`.
    let source_has_no_std = parsed_file
        .attrs
        .iter()
        .any(|attr| attr.path().is_ident("no_std"));
    let effective_no_std = config.no_std_mode || source_has_no_std;

    // Locate target function and any declared external callee functions.
    let mut target_fn: Option<ItemFn> = None;
    let mut callee_fns: Vec<ItemFn> = Vec::new();

    for item in &parsed_file.items {
        if let Item::Fn(func) = item {
            let name = func.sig.ident.to_string();
            if name == fn_name {
                target_fn = Some(func.clone());
            }
            if ext_callees.contains(&name.as_str()) {
                callee_fns.push(func.clone());
            }
        }
    }

    let orig_target = target_fn
        .ok_or_else(|| InstrumentationError::TargetFunctionNotFound(fn_name.to_string()))?;

    // Emit runtime prelude module.
    let prelude_tokens = emit_runtime_prelude(effective_no_std);
    let prelude_item: Item = syn::parse2(prelude_tokens)
        .map_err(|e| InstrumentationError::ParseError(e.to_string()))?;
    parsed_file.items.push(prelude_item);

    // Emit per-callee instrumented wrappers.
    let mut wrapper_fn_names = Vec::new();
    for callee_fn in &callee_fns {
        let (wrapper_name, wrapper_item) = synthesize_ext_wrapper(callee_fn)?;
        wrapper_fn_names.push(wrapper_name);
        parsed_file.items.push(wrapper_item);
    }

    // Rewrite cloned body of `orig_target` so external calls route through `__rec`.
    let rec_ident = Ident::new("__rec", Span::call_site());
    let mut instrumented_body = *orig_target.block.clone();
    let mut rewriter = BodyCallRewriter {
        ext_callees,
        rec_ident: rec_ident.clone(),
        instrument_branches: config.instrument_branches,
        next_branch_tag: 1,
    };
    rewriter.visit_block_mut(&mut instrumented_body);

    let params = extract_fn_params(&orig_target)?;
    let param_decls: Vec<TokenStream> = params.iter().map(|(id, ty)| quote!(#id: #ty)).collect();
    let capture_entry_args: Vec<TokenStream> = params
        .iter()
        .map(|(id, _)| quote!(__anneal_rt::value_as_raw_bytes(&#id)))
        .collect();
    let forward_args: Vec<TokenStream> = params.iter().map(|(id, _)| quote!(#id)).collect();

    let traced_ident = format_ident!("__anneal_traced_{}", fn_name);
    let generics = &orig_target.sig.generics;
    let output = &orig_target.sig.output;
    let ret_ty: TokenStream = match output {
        ReturnType::Default => quote!(()),
        ReturnType::Type(_, ty) => quote!(#ty),
    };

    let vec_ctor = if effective_no_std {
        quote!(alloc::vec::Vec::new())
    } else {
        quote!(std::vec::Vec::new())
    };

    // Synthesize `__anneal_traced_<fn_name>` (works in both `#![no_std]` and `std`).
    // Wrap `#instrumented_body` in an immediately invoked closure so early `return`
    // statements inside the body still reach `#rec_ident.finish_return(&__ret)`.
    let traced_fn_tokens = quote! {
        #[allow(dead_code, clippy::too_many_arguments)]
        pub fn #traced_ident #generics (
            #rec_ident: &mut __anneal_rt::TraceRecorder,
            #(#param_decls),*
        ) #output {
            let mut __entry_arg_bytes = #vec_ctor;
            #( __entry_arg_bytes.push(#capture_entry_args); )*
            #rec_ident.record_entry(#fn_name, __entry_arg_bytes);
            let __ret: #ret_ty = (|| #output #instrumented_body)();
            #rec_ident.finish_return(&__ret);
            __ret
        }
    };
    let traced_item: Item = syn::parse2(traced_fn_tokens)
        .map_err(|e| InstrumentationError::ParseError(e.to_string()))?;
    parsed_file.items.push(traced_item);

    // In `std` harness mode, also synthesize `__anneal_traced_catch_<fn_name>` which wraps
    // the call in `std::panic::catch_unwind` and records `RecordedOutcome::Panic` on unwind.
    let catch_unwind_fn_name = if !effective_no_std {
        let catch_ident = format_ident!("__anneal_traced_catch_{}", fn_name);
        let catch_tokens = quote! {
            #[allow(dead_code, clippy::too_many_arguments)]
            pub fn #catch_ident #generics (
                #rec_ident: &mut __anneal_rt::TraceRecorder,
                #(#param_decls),*
            ) -> core::option::Option<#ret_ty> {
                let __res = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                    #traced_ident(#rec_ident, #(#forward_args),*)
                }));
                match __res {
                    Ok(__val) => Some(__val),
                    Err(_) => {
                        #rec_ident.finish_panic();
                        None
                    }
                }
            }
        };
        let catch_item: Item = syn::parse2(catch_tokens)
            .map_err(|e| InstrumentationError::ParseError(e.to_string()))?;
        parsed_file.items.push(catch_item);
        Some(catch_ident.to_string())
    } else {
        None
    };

    let formatted = prettyplease::unparse(&parsed_file);
    Ok(InstrumentationResult {
        source: formatted,
        traced_fn_name: traced_ident.to_string(),
        catch_unwind_fn_name,
        wrapper_fn_names,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[repr(C)]
    #[derive(Clone, Copy)]
    struct PaddedPair {
        tag: u8,
        // 3 bytes inter-field padding at offsets 1..4
        word: u32,
    }

    #[test]
    fn value_as_raw_bytes_preserves_exact_padding_bytes() {
        let mut raw = [0u8; core::mem::size_of::<PaddedPair>()];
        raw[0] = 0x42;
        raw[1] = 0xA5;
        raw[2] = 0x5A;
        raw[3] = 0xFF;
        raw[4..8].copy_from_slice(&0x1122_3344u32.to_le_bytes());

        // Copy directly into an aligned `MaybeUninit<PaddedPair>` stack slot so rustc's
        // `ScalarPair` return-value register ABI cannot strip the inter-field padding bytes.
        let mut slot = core::mem::MaybeUninit::<PaddedPair>::zeroed();
        // SAFETY: `raw.len() == size_of::<PaddedPair>()` and all bit patterns are valid.
        let val_ref: &PaddedPair = unsafe {
            core::ptr::copy_nonoverlapping(
                raw.as_ptr(),
                slot.as_mut_ptr() as *mut u8,
                core::mem::size_of::<PaddedPair>(),
            );
            slot.assume_init_ref()
        };
        let captured = value_as_raw_bytes(val_ref);
        assert_eq!(captured, raw);
    }

    #[test]
    fn env_schedule_queues_defaults_and_panic_on_call_work() {
        let mut sched = EnvSchedule::new().with_panic_on_call(2);
        sched.push_callee_response("oracle", vec![1, 0, 0, 0]);
        sched.set_callee_default("oracle", vec![9, 0, 0, 0]);

        let mut rec = TraceRecorder::with_schedule(sched);
        let (idx0, act0) = rec.step_ext_call("oracle");
        assert_eq!(idx0, 0);
        assert_eq!(act0, EnvAction::ReturnBytes(vec![1, 0, 0, 0]));

        let (idx1, act1) = rec.step_ext_call("oracle");
        assert_eq!(idx1, 1);
        assert_eq!(act1, EnvAction::ReturnBytes(vec![9, 0, 0, 0]));

        let (idx2, act2) = rec.step_ext_call("oracle");
        assert_eq!(idx2, 2);
        assert_eq!(act2, EnvAction::PanicOnCall(2));
        assert!(rec.is_panic());
    }

    #[test]
    fn instrument_source_synthesizes_valid_std_and_no_std_modules() {
        let sample = r#"
            pub fn ext_hash(x: u32) -> u32 {
                x.wrapping_mul(2654435761)
            }

            pub fn target_compute(a: u32, b: u32) -> u32 {
                if a > 10 {
                    ext_hash(a).wrapping_add(b)
                } else {
                    b
                }
            }
        "#;

        let res = instrument_source_with_config(
            sample,
            "target_compute",
            &["ext_hash"],
            &InstrumentConfig::default(),
        )
        .expect("std instrumentation should succeed");
        assert_eq!(res.traced_fn_name, "__anneal_traced_target_compute");
        assert_eq!(
            res.catch_unwind_fn_name.as_deref(),
            Some("__anneal_traced_catch_target_compute")
        );
        assert_eq!(res.wrapper_fn_names, vec!["__anneal_ext_ext_hash"]);
        assert!(res.source.contains("pub mod __anneal_rt"));
        assert!(res.source.contains("pub fn __anneal_ext_ext_hash"));
        assert!(res.source.contains("pub fn __anneal_traced_target_compute"));
        assert!(syn::parse_file(&res.source).is_ok());

        // Also verify strict `#![no_std]` mode emits valid AST with zero `std::` paths.
        let no_std_res = instrument_source_with_config(
            sample,
            "target_compute",
            &["ext_hash"],
            &InstrumentConfig {
                no_std_mode: true,
                instrument_branches: true,
            },
        )
        .expect("no_std instrumentation should succeed");
        assert!(no_std_res.catch_unwind_fn_name.is_none());
        assert!(!no_std_res.source.contains("std::panic::catch_unwind"));
        assert!(syn::parse_file(&no_std_res.source).is_ok());
    }
}
