// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Interception of every MIR body at `Runtime(PostCleanup)`.
//!
//! # Why a query override
//!
//! `rustc` computes the `Runtime(PostCleanup)` body of each item exactly once,
//! as the result of the `mir_drops_elaborated_and_const_checked` query, and
//! returns it inside a `Steal` cell
//! (`compiler/rustc_middle/src/queries.rs#L638-L641`):
//!
//! > ```text
//! > query mir_drops_elaborated_and_const_checked(key: LocalDefId)
//! >     -> &'tcx Steal<mir::Body<'tcx>> {
//! > ```
//!
//! Later queries take the body out of the cell: `mir_for_ctfe` steals it for
//! constants and `optimized_mir` steals it for functions
//! (`compiler/rustc_mir_transform/src/lib.rs#L495-L502` and `#L795`).
//! Constants are evaluated during `rustc`'s analysis, so by the time a
//! driver's `after_analysis` callback runs, the bodies of the constants the
//! crate uses are already gone (`is_stolen() == true` on inline-const and
//! associated-const bodies once analysis finishes).
//!
//! The capture therefore replaces the query's provider with `capture_hook`,
//! which calls `rustc`'s own provider, translates the resulting body before
//! returning it, and records the translation. This is the mechanism `rustc`
//! documents for custom drivers: `run_analysis_to_runtime_passes` is public
//! precisely "so that `mir_drops_elaborated_and_const_checked` can be
//! overridden by custom rustc drivers" (`lib.rs#L567-L569`).
//!
//! Because the hook returns `rustc`'s own result unchanged, it cannot alter
//! compilation; it only observes. Because queries are memoized, the hook runs
//! at most once per item, and the body it sees is the body every later stage
//! starts from. Two later transformations matter for reading the captured
//! body as the code that runs:
//!
//! - Constant evaluation runs `mir_for_ctfe`, which takes this body, rewrites
//!   calls to the `const_eval_select` intrinsic, and inserts
//!   `ConstEvalCounter` statements (`lib.rs#L495-L507`). The fragment has no
//!   `const_eval_select` calls (it is not a known callee), and
//!   `ConstEvalCounter` is a no-op for the result, so the captured body has
//!   the same outcome as the body `rustc` evaluates.
//! - Codegen runs `optimized_mir` (`lib.rs#L785-L819`). Whether `rustc`'s
//!   optimizations and code generation preserve the meaning of this body is
//!   part of the compiler soundness assumption documented in `THREAT_MODEL.md`.
//!
//! Source citations are paths in `rust-lang/rust` at the pinned toolchain
//! commit `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`
//! (`https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/<path>`),
//! whose sources ship in the pinned toolchain's `rustc-src` component.

use std::collections::BTreeMap;
use std::sync::{Mutex, OnceLock};

use rustc_data_structures::steal::Steal;
use rustc_middle::mir::Body;
use rustc_middle::ty::TyCtxt;
use rustc_middle::util::Providers;
use rustc_session::Session;
use rustc_span::def_id::LocalDefId;

use crate::extract;
use crate::ir;

/// `rustc`'s provider, saved so the hook can delegate to it.
type Provider =
    for<'tcx> fn(TyCtxt<'tcx>, LocalDefId) -> &'tcx Steal<Body<'tcx>>;

static DEFAULT_PROVIDER: OnceLock<Provider> = OnceLock::new();

/// Every body the hook has seen, keyed by `DefIndex`, with its translation or
/// rejection reason.
///
/// A process-wide map is required because a provider is a plain `fn` pointer
/// and cannot capture state. The capture runs its compiler sessions one after
/// another and clears the map at the start of each (`reset`), so the keys
/// are unambiguous.
static CAPTURED: Mutex<BTreeMap<ir::DefIdx, extract::Res<ir::Body>>> =
    Mutex::new(BTreeMap::new());

/// Installs `capture_hook` as the provider of
/// `mir_drops_elaborated_and_const_checked`. Passed to `rustc` as
/// `interface::Config::override_queries`, which `rustc` calls "just after we
/// have populated the list of queries"
/// (`compiler/rustc_interface/src/interface.rs#L350-L352`).
pub fn override_queries(_sess: &Session, providers: &mut Providers) {
    let _ = DEFAULT_PROVIDER
        .set(providers.queries.mir_drops_elaborated_and_const_checked);
    providers.queries.mir_drops_elaborated_and_const_checked = capture_hook;
}

fn capture_hook<'tcx>(
    tcx: TyCtxt<'tcx>,
    def: LocalDefId,
) -> &'tcx Steal<Body<'tcx>> {
    let default =
        DEFAULT_PROVIDER.get().expect("override_queries ran before any query");
    let steal = default(tcx, def);
    let result = extract::body(tcx, def, &steal.borrow());
    CAPTURED.lock().unwrap().insert(def.local_def_index.as_u32(), result);
    steal
}

/// Forgets every recorded body. Called at the start of each compiler
/// session, because `DefIndex` keys are only meaningful within one session.
pub fn reset() {
    CAPTURED.lock().unwrap().clear();
}

/// Returns the recorded translation of `def`'s body, forcing `rustc` to
/// compute the body first if no earlier stage needed it.
///
/// Forcing is needed for bodies whose `Runtime(PostCleanup)` MIR nothing in
/// the analysis phase requested. Calling the query triggers `capture_hook`
/// if and only if the body has not been computed yet; either way the map
/// then holds the result.
pub fn captured_body(
    tcx: TyCtxt<'_>,
    def: LocalDefId,
) -> extract::Res<ir::Body> {
    let key = def.local_def_index.as_u32();
    if let Some(r) = CAPTURED.lock().unwrap().get(&key) {
        return r.clone();
    }
    let _ = tcx.mir_drops_elaborated_and_const_checked(def);
    CAPTURED.lock().unwrap().get(&key).cloned().unwrap_or_else(|| {
        Err("rustc never produced a Runtime(PostCleanup) body".into())
    })
}
