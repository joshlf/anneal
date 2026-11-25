// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! `#![no_std]` peer-verifier specification-boundary soundness guards.
//!
//! This module extends the frozen three-guard taxonomy of
//! [`crate::spec_check::SpecBoundaryGuardClass`] (ranks `0..3`) with four
//! peer-verifier guards, [`PeerSpecGuardClass`] (ranks `3..7`), mirrored
//! constructor for constructor by `Anneal.InductiveReplayAndPeerSpecGuards`
//! in Lean:
//!
//! 3. [`PeerSpecGuardClass::UnsatisfiableExternEnsures`] (`creusot#2388`): an
//!    assumed contract (`#[trusted]`, `#[extern_spec]`, `extern_spec! { .. }`,
//!    `#[external_spec]`, `#[spec(trusted, ..)]`, `#[spec(assumed, ..)]`,
//!    `#[verifier::external_body]`) whose `ensures` is unsatisfiable on a
//!    function that can return derives `False` at every reachable call.
//! 4. [`PeerSpecGuardClass::FnDefGhostTokenCoercion`] (`creusot#2389`): a
//!    ghost-token constructor coerced to a first-class `FnDef` value, or called
//!    from a loop, closure, `async` block, helper, or re-entered `main`, mints
//!    duplicate unique-authority tokens.
//! 5. [`PeerSpecGuardClass::ExternalTypeDropOmission`] (`verus#3514`): an
//!    `external_type_specification` that omits an active `Drop` effect.
//! 6. [`PeerSpecGuardClass::AssumptionPolarityAndStructSealing`] (`Verifrag` +
//!    `Samite`): an assumption atom (`assumes_hold` / `assumesHold`) outside
//!    strictly negative (antecedent) polarity, or an `#[invariant(..)]`
//!    structure whose raw constructor escapes its defining boundary.
//!
//! Every checker is available in two forms: a *descriptor* checker over the
//! facts a front end has already extracted, and a fail-closed *source*
//! scanner. The scanners run over a comment- and literal-aware lexer (nested
//! block comments, raw strings, byte and C strings, character literals, and
//! lifetimes never spoof code), use only fixed-capacity tables, and reject any
//! source they cannot attribute (unterminated literals, unbalanced delimiters,
//! table overflow) with a [`PeerScanError`].
//!
//! `cfg_attr` is handled asymmetrically: `#[cfg_attr(pred, risky)]` counts as
//! present when it *introduces* a risky attribute, and never counts when it
//! would *exempt* a finding (`requires(false)`, `models_drop`, `no_drop_glue`,
//! `smart_constructor`).

use core::fmt;

use crate::spec_check::{SpecBoundaryGuardClass, VacuityClass};

// ----------------------------------------------------------------------------
// Frozen taxonomy
// ----------------------------------------------------------------------------

/// Frozen four-class peer-verifier guard taxonomy, in rank order `3..7`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum PeerSpecGuardClass {
    /// Rank 3 (`creusot#2388`): an assumed contract with an unsatisfiable
    /// `ensures` on a function that can return.
    UnsatisfiableExternEnsures,
    /// Rank 4 (`creusot#2389`): a ghost-token constructor coerced to a `FnDef`
    /// value or minted from a repeating context.
    FnDefGhostTokenCoercion,
    /// Rank 5 (`verus#3514`): an external type specification omits `Drop`.
    ExternalTypeDropOmission,
    /// Rank 6 (`Verifrag` + `Samite`): assumption polarity and structure
    /// constructor sealing.
    AssumptionPolarityAndStructSealing,
}

impl PeerSpecGuardClass {
    /// Number of peer guards.
    pub const COUNT: usize = 4;

    /// Rank of the first peer guard (one past the last
    /// [`SpecBoundaryGuardClass`] rank).
    pub const FIRST_RANK: usize = SpecBoundaryGuardClass::COUNT;

    /// All four peer guards in rank order (`PeerSpecGuardClass.all` in Lean).
    pub const ALL: [Self; 4] = [
        Self::UnsatisfiableExternEnsures,
        Self::FnDefGhostTokenCoercion,
        Self::ExternalTypeDropOmission,
        Self::AssumptionPolarityAndStructSealing,
    ];

    /// Canonical rank (`3..7`).
    pub const fn rank(self) -> usize {
        match self {
            Self::UnsatisfiableExternEnsures => 3,
            Self::FnDefGhostTokenCoercion => 4,
            Self::ExternalTypeDropOmission => 5,
            Self::AssumptionPolarityAndStructSealing => 6,
        }
    }

    /// Inverse of [`Self::rank`]; `None` outside `3..7`.
    pub const fn from_rank(rank: usize) -> Option<Self> {
        match rank {
            3 => Some(Self::UnsatisfiableExternEnsures),
            4 => Some(Self::FnDefGhostTokenCoercion),
            5 => Some(Self::ExternalTypeDropOmission),
            6 => Some(Self::AssumptionPolarityAndStructSealing),
            _ => None,
        }
    }

    /// Canonical `snake_case` wire identifier.
    pub const fn guard_id(self) -> &'static str {
        match self {
            Self::UnsatisfiableExternEnsures => "unsatisfiable_extern_ensures",
            Self::FnDefGhostTokenCoercion => "fndef_ghost_token_coercion",
            Self::ExternalTypeDropOmission => "external_type_drop_omission",
            Self::AssumptionPolarityAndStructSealing => "assumption_polarity_and_struct_sealing",
        }
    }

    /// Parses a wire identifier; exact and case-sensitive.
    pub fn from_guard_id(id: &str) -> Option<Self> {
        Self::ALL.into_iter().find(|g| g.guard_id() == id)
    }

    /// Canonical cross-language diagnostic name.
    pub const fn canonical_name(self) -> &'static str {
        match self {
            Self::UnsatisfiableExternEnsures => "UnsatisfiableExternEnsures",
            Self::FnDefGhostTokenCoercion => "FnDefGhostTokenCoercion",
            Self::ExternalTypeDropOmission => "ExternalTypeDropOmission",
            Self::AssumptionPolarityAndStructSealing => "AssumptionPolarityAndStructSealing",
        }
    }

    /// Parses a canonical diagnostic name; exact and case-sensitive.
    pub fn from_canonical_name(name: &str) -> Option<Self> {
        Self::ALL.into_iter().find(|g| g.canonical_name() == name)
    }

    /// The frozen [`VacuityClass`] a violation is reported under.
    pub const fn to_vacuity_class(self) -> VacuityClass {
        match self {
            Self::UnsatisfiableExternEnsures => VacuityClass::DeadPrecondition,
            Self::FnDefGhostTokenCoercion => VacuityClass::SpecViolation,
            Self::ExternalTypeDropOmission => VacuityClass::SpecViolation,
            Self::AssumptionPolarityAndStructSealing => VacuityClass::SurvivedAllMutants,
        }
    }

    /// Upstream soundness report the guard closes.
    pub const fn upstream_reference(self) -> &'static str {
        match self {
            Self::UnsatisfiableExternEnsures => "creusot#2388",
            Self::FnDefGhostTokenCoercion => "creusot#2389",
            Self::ExternalTypeDropOmission => "verus#3514",
            Self::AssumptionPolarityAndStructSealing => "Verifrag + Samite",
        }
    }
}

impl fmt::Display for PeerSpecGuardClass {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.canonical_name())
    }
}

/// The combined seven-guard taxonomy: base ranks `0..3` then peer ranks `3..7`
/// (`CombinedSpecGuardClass` in Lean).
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum CombinedSpecGuardClass {
    /// A base specification-boundary guard.
    Base(SpecBoundaryGuardClass),
    /// A peer-verifier guard.
    Peer(PeerSpecGuardClass),
}

impl CombinedSpecGuardClass {
    /// Number of combined guards.
    pub const COUNT: usize = SpecBoundaryGuardClass::COUNT + PeerSpecGuardClass::COUNT;

    /// All seven guards in rank order.
    pub const ALL: [Self; 7] = [
        Self::Base(SpecBoundaryGuardClass::EntryPointPrecondition),
        Self::Base(SpecBoundaryGuardClass::FixedWidthGhostLength),
        Self::Base(SpecBoundaryGuardClass::ErrorBranchWildcard),
        Self::Peer(PeerSpecGuardClass::UnsatisfiableExternEnsures),
        Self::Peer(PeerSpecGuardClass::FnDefGhostTokenCoercion),
        Self::Peer(PeerSpecGuardClass::ExternalTypeDropOmission),
        Self::Peer(PeerSpecGuardClass::AssumptionPolarityAndStructSealing),
    ];

    /// Canonical rank (`0..7`).
    pub const fn rank(self) -> usize {
        match self {
            Self::Base(g) => g.rank(),
            Self::Peer(g) => g.rank(),
        }
    }

    /// Inverse of [`Self::rank`]; `None` for `rank >= 7`.
    pub const fn from_rank(rank: usize) -> Option<Self> {
        match SpecBoundaryGuardClass::from_rank(rank) {
            Some(g) => Some(Self::Base(g)),
            None => match PeerSpecGuardClass::from_rank(rank) {
                Some(g) => Some(Self::Peer(g)),
                None => None,
            },
        }
    }

    /// Canonical wire identifier.
    pub const fn guard_id(self) -> &'static str {
        match self {
            Self::Base(g) => g.guard_id(),
            Self::Peer(g) => g.guard_id(),
        }
    }

    /// Parses a wire identifier across all seven guards.
    pub fn from_guard_id(id: &str) -> Option<Self> {
        Self::ALL.into_iter().find(|g| g.guard_id() == id)
    }

    /// Canonical diagnostic name.
    pub const fn canonical_name(self) -> &'static str {
        match self {
            Self::Base(g) => g.canonical_name(),
            Self::Peer(g) => g.canonical_name(),
        }
    }

    /// The frozen [`VacuityClass`] of the guard.
    pub const fn to_vacuity_class(self) -> VacuityClass {
        match self {
            Self::Base(g) => g.to_vacuity_class(),
            Self::Peer(g) => g.to_vacuity_class(),
        }
    }
}

/// Verdict of one peer guard (`PeerSpecGuardVerdict` in Lean).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum PeerSpecGuardVerdict {
    /// The guard holds.
    Pass(PeerSpecGuardClass),
    /// The guard is violated.
    Violation(PeerSpecGuardClass),
}

impl PeerSpecGuardVerdict {
    /// Builds a verdict from a Boolean check.
    pub const fn of_check(guard: PeerSpecGuardClass, ok: bool) -> Self {
        if ok {
            Self::Pass(guard)
        } else {
            Self::Violation(guard)
        }
    }

    /// The guard this verdict concerns.
    pub const fn guard(self) -> PeerSpecGuardClass {
        match self {
            Self::Pass(g) | Self::Violation(g) => g,
        }
    }

    /// Whether the guard holds.
    pub const fn is_pass(self) -> bool {
        matches!(self, Self::Pass(_))
    }

    /// Vacuity class reported; `None` exactly for a passing verdict.
    pub const fn vacuity_class(self) -> Option<VacuityClass> {
        match self {
            Self::Pass(_) => None,
            Self::Violation(g) => Some(g.to_vacuity_class()),
        }
    }

    /// The verdict of a checker result.
    pub fn of_result<T, E>(guard: PeerSpecGuardClass, result: &Result<T, E>) -> Self {
        Self::of_check(guard, result.is_ok())
    }
}

// ----------------------------------------------------------------------------
// Violations and errors
// ----------------------------------------------------------------------------

/// The precise reason a peer guard rejected a specification.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum PeerViolationReason {
    /// Guard 3: an assumed contract has an unsatisfiable `ensures` on a
    /// function with an inhabited return type and no unconditional
    /// `requires(false)`.
    EnsuresFalseOnReturningFn,
    /// Guard 3: a divergence claim on an inhabited return type.
    LyingDivergence,
    /// Guard 4: the constructor is used as a value instead of being called.
    FnDefValueCoercion,
    /// Guard 4: the constructor is called from a loop, closure, or `async` block.
    MintInRepeatingContext,
    /// Guard 4: the constructor is called outside `main`.
    MintOutsideMain,
    /// Guard 4: more than one constructor call site.
    MultipleMintSites,
    /// Guard 4: `main` mints a token and is referenced (re-entered or aliased).
    ReentrantMain,
    /// Guard 4: the constructor type is passed as an explicit generic argument
    /// to a function (`mk::<Tokens>()`), so a generic body may mint it.
    GenericConstructorDispatch,
    /// Guard 5: `external_body` on an external type whose `Drop` may exist.
    ExternalBodyWithDrop,
    /// Guard 5: a `Drop` impl without an unconditional `models_drop`.
    UnmodeledDropImpl,
    /// Guard 5: an opaque foreign field without `models_drop` / `no_drop_glue`.
    UnmodeledOpaqueField,
    /// Guard 5: `no_drop_glue` on a type with a `Drop` impl.
    ContradictoryDropDeclaration,
    /// Guard 6a: the assumption atom occurs in positive (postcondition) polarity.
    AssumptionPositive,
    /// Guard 6a: the assumption atom is negated inside an antecedent.
    AssumptionNegatedAntecedent,
    /// Guard 6a: the assumption atom occurs under `iff`.
    AssumptionInIff,
    /// Guard 6a: the assumption atom occurs in an `if` condition.
    AssumptionInIfCondition,
    /// Guard 6a: the assumption atom occurs inside a Boolean leaf whose polarity
    /// is not tracked (`==`, a call argument, a method receiver).
    AssumptionUncleanLeaf,
    /// Guard 6b: an invariant-bearing structure has a public field.
    InvariantPubField,
    /// Guard 6b: an invariant-bearing structure derives `Default`.
    InvariantDeriveDefault,
    /// Guard 6b: an invariant-bearing structure implements `Default`.
    InvariantDefaultImpl,
    /// Guard 6b: an invariant-bearing structure derives or implements a trait
    /// that builds values from untrusted data or bytes without checking the
    /// invariant (`Deserialize`, `FromBytes`, `Pod`, `Arbitrary`, ...).
    InvariantUncheckedConstructorTrait,
    /// Guard 6b: a public method returns a mutable reference into a field of an
    /// invariant-bearing structure, so clients mutate it unchecked.
    InvariantMutableFieldEscape,
    /// Guard 6b: a public function constructs the raw structure without a
    /// `#[smart_constructor]` invariant gate.
    InvariantRawPublicConstructor,
}

impl PeerViolationReason {
    /// The guard the reason belongs to.
    pub const fn guard(self) -> PeerSpecGuardClass {
        match self {
            Self::EnsuresFalseOnReturningFn | Self::LyingDivergence => {
                PeerSpecGuardClass::UnsatisfiableExternEnsures
            }
            Self::FnDefValueCoercion
            | Self::MintInRepeatingContext
            | Self::MintOutsideMain
            | Self::MultipleMintSites
            | Self::ReentrantMain
            | Self::GenericConstructorDispatch => PeerSpecGuardClass::FnDefGhostTokenCoercion,
            Self::ExternalBodyWithDrop
            | Self::UnmodeledDropImpl
            | Self::UnmodeledOpaqueField
            | Self::ContradictoryDropDeclaration => PeerSpecGuardClass::ExternalTypeDropOmission,
            _ => PeerSpecGuardClass::AssumptionPolarityAndStructSealing,
        }
    }

    /// Stable `snake_case` identifier.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::EnsuresFalseOnReturningFn => "ensures_false_on_returning_fn",
            Self::LyingDivergence => "lying_divergence",
            Self::FnDefValueCoercion => "fndef_value_coercion",
            Self::MintInRepeatingContext => "mint_in_repeating_context",
            Self::MintOutsideMain => "mint_outside_main",
            Self::MultipleMintSites => "multiple_mint_sites",
            Self::ReentrantMain => "reentrant_main",
            Self::GenericConstructorDispatch => "generic_constructor_dispatch",
            Self::ExternalBodyWithDrop => "external_body_with_drop",
            Self::UnmodeledDropImpl => "unmodeled_drop_impl",
            Self::UnmodeledOpaqueField => "unmodeled_opaque_field",
            Self::ContradictoryDropDeclaration => "contradictory_drop_declaration",
            Self::AssumptionPositive => "assumption_positive",
            Self::AssumptionNegatedAntecedent => "assumption_negated_antecedent",
            Self::AssumptionInIff => "assumption_in_iff",
            Self::AssumptionInIfCondition => "assumption_in_if_condition",
            Self::AssumptionUncleanLeaf => "assumption_unclean_leaf",
            Self::InvariantPubField => "invariant_pub_field",
            Self::InvariantDeriveDefault => "invariant_derive_default",
            Self::InvariantUncheckedConstructorTrait => "invariant_unchecked_constructor_trait",
            Self::InvariantMutableFieldEscape => "invariant_mutable_field_escape",
            Self::InvariantDefaultImpl => "invariant_default_impl",
            Self::InvariantRawPublicConstructor => "invariant_raw_public_constructor",
        }
    }
}

/// A peer-guard violation at a byte offset of the scanned source (`0` for
/// descriptor checks).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct PeerSoundnessGuardViolation {
    /// Why the guard rejected the specification.
    pub reason: PeerViolationReason,
    /// Byte offset of the offending token.
    pub offset: usize,
}

impl PeerSoundnessGuardViolation {
    /// The violated guard.
    pub const fn guard(&self) -> PeerSpecGuardClass {
        self.reason.guard()
    }

    /// The vacuity class the violation is reported under.
    pub const fn vacuity_class(&self) -> VacuityClass {
        self.reason.guard().to_vacuity_class()
    }
}

impl fmt::Display for PeerSoundnessGuardViolation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} ({}) at byte {}",
            self.guard(),
            self.reason.as_str(),
            self.offset
        )
    }
}

/// Why a source scanner could not attribute the source (always fail-closed).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum PeerScanErrorKind {
    /// A block comment is not closed.
    UnterminatedBlockComment,
    /// A string literal is not closed.
    UnterminatedString,
    /// A character literal or lifetime is malformed.
    MalformedCharOrLifetime,
    /// Delimiters do not balance.
    UnbalancedDelimiter,
    /// Nesting exceeds the fixed scanner capacity.
    NestingTooDeep,
    /// A fixed-capacity name table is full.
    TableFull,
    /// A `let`-alias chain exceeds the inlining depth bound.
    AliasDepthExceeded,
}

/// A fail-closed source-scanner error.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct PeerScanError {
    /// Error kind.
    pub kind: PeerScanErrorKind,
    /// Byte offset where scanning failed.
    pub offset: usize,
}

impl PeerScanError {
    const fn new(kind: PeerScanErrorKind, offset: usize) -> Self {
        Self { kind, offset }
    }
}

impl fmt::Display for PeerScanError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "unattributable source ({:?}) at byte {}",
            self.kind, self.offset
        )
    }
}

/// Error of a peer-guard source scanner: a violation, or source the scanner
/// refuses to attribute.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum PeerSoundnessGuardError {
    /// The guard is violated.
    Violation(PeerSoundnessGuardViolation),
    /// The source could not be scanned (rejected fail-closed).
    Scan(PeerScanError),
}

impl PeerSoundnessGuardError {
    /// The violation, if this error is one.
    pub const fn violation(&self) -> Option<PeerSoundnessGuardViolation> {
        match self {
            Self::Violation(v) => Some(*v),
            Self::Scan(_) => None,
        }
    }

    /// The violation reason, if this error is a violation.
    pub const fn reason(&self) -> Option<PeerViolationReason> {
        match self {
            Self::Violation(v) => Some(v.reason),
            Self::Scan(_) => None,
        }
    }
}

impl From<PeerScanError> for PeerSoundnessGuardError {
    fn from(e: PeerScanError) -> Self {
        Self::Scan(e)
    }
}

impl From<PeerSoundnessGuardViolation> for PeerSoundnessGuardError {
    fn from(v: PeerSoundnessGuardViolation) -> Self {
        Self::Violation(v)
    }
}

impl fmt::Display for PeerSoundnessGuardError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Violation(v) => v.fmt(f),
            Self::Scan(e) => e.fmt(f),
        }
    }
}

type GResult<T> = Result<T, PeerSoundnessGuardError>;

fn violation<T>(reason: PeerViolationReason, offset: usize) -> GResult<T> {
    Err(PeerSoundnessGuardError::Violation(
        PeerSoundnessGuardViolation { reason, offset },
    ))
}

const fn descriptor_violation(reason: PeerViolationReason) -> PeerSoundnessGuardViolation {
    PeerSoundnessGuardViolation { reason, offset: 0 }
}

// ----------------------------------------------------------------------------
// Comment- and literal-aware lexer
// ----------------------------------------------------------------------------

/// Source dialect of a scanned snippet.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub enum SourceDialect {
    /// Rust: `//` and nested `/* */` comments, raw strings, lifetimes.
    #[default]
    Rust,
    /// Lean 4: `--` and nested `/- -/` comments, primes in identifiers.
    Lean,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum TokKind {
    Ident,
    Lifetime,
    Literal,
    Punct,
}

#[derive(Clone, Copy, Debug)]
struct Tok<'a> {
    kind: TokKind,
    text: &'a str,
    start: usize,
    end: usize,
    /// A raw identifier (`r#name`): never a keyword.
    raw: bool,
}

impl<'a> Tok<'a> {
    fn is_punct(&self, p: &str) -> bool {
        self.kind == TokKind::Punct && self.text == p
    }

    fn is_kw(&self, s: &str) -> bool {
        self.kind == TokKind::Ident && !self.raw && self.text == s
    }

    fn is_ident(&self) -> bool {
        self.kind == TokKind::Ident
    }

    fn is_open(&self) -> bool {
        self.kind == TokKind::Punct && matches!(self.text, "(" | "[" | "{" | "⦃")
    }

    fn is_close(&self) -> bool {
        self.kind == TokKind::Punct && matches!(self.text, ")" | "]" | "}" | "⦄")
    }
}

const RUST_PUNCTS: [&str; 18] = [
    "<==>", "==>", "<==", "...", "..=", "::", "->", "=>", "==", "!=", "<=", ">=", "&&", "||", "..",
    "+=", "-=", "*=",
];

const LEAN_PUNCTS: [&str; 13] = [
    "<==>", "==>", "<->", ":=", "->", "=>", "==", "!=", "&&", "||", "::", "<=", ">=",
];

/// Longest escaped character literal body (`'\u{10FFFF}'`).
const MAX_CHAR_ESCAPE_BYTES: usize = 12;

fn is_ident_start(c: char) -> bool {
    c == '_' || (c.is_alphabetic() && c != 'λ')
}

fn is_ident_continue(c: char, dialect: SourceDialect) -> bool {
    c == '_'
        || (c.is_alphanumeric() && c != 'λ')
        || (dialect == SourceDialect::Lean && matches!(c, '\'' | '!' | '?'))
}

#[derive(Clone, Copy, Debug)]
struct Lexer<'a> {
    src: &'a str,
    pos: usize,
    end: usize,
    dialect: SourceDialect,
}

impl<'a> Lexer<'a> {
    const fn new(src: &'a str, dialect: SourceDialect) -> Self {
        Self {
            src,
            pos: 0,
            end: src.len(),
            dialect,
        }
    }

    /// A lexer over `start..end` of the same source.
    const fn range(&self, start: usize, end: usize) -> Self {
        Self {
            src: self.src,
            pos: start,
            end,
            dialect: self.dialect,
        }
    }

    fn byte(&self, i: usize) -> u8 {
        if i < self.end {
            self.src.as_bytes()[i]
        } else {
            0
        }
    }

    fn char_at(&self, i: usize) -> Option<char> {
        if i >= self.end || !self.src.is_char_boundary(i) {
            return None;
        }
        self.src[i..].chars().next()
    }

    fn starts_with(&self, i: usize, pat: &[u8]) -> bool {
        i + pat.len() <= self.end && &self.src.as_bytes()[i..i + pat.len()] == pat
    }

    fn skip_line(&mut self) {
        while self.pos < self.end && self.src.as_bytes()[self.pos] != b'\n' {
            self.pos += 1;
        }
    }

    fn skip_block(&mut self, open: &[u8], close: &[u8]) -> Result<(), PeerScanError> {
        let start = self.pos;
        self.pos += 2;
        let mut depth = 1usize;
        while self.pos < self.end {
            if self.starts_with(self.pos, open) {
                depth += 1;
                self.pos += 2;
            } else if self.starts_with(self.pos, close) {
                depth -= 1;
                self.pos += 2;
                if depth == 0 {
                    return Ok(());
                }
            } else {
                self.pos += 1;
            }
        }
        Err(PeerScanError::new(
            PeerScanErrorKind::UnterminatedBlockComment,
            start,
        ))
    }

    fn skip_trivia(&mut self) -> Result<(), PeerScanError> {
        while self.pos < self.end {
            let Some(c) = self.char_at(self.pos) else {
                break;
            };
            if c.is_whitespace() {
                self.pos += c.len_utf8();
                continue;
            }
            match self.dialect {
                SourceDialect::Rust => {
                    if self.starts_with(self.pos, b"//") {
                        self.skip_line();
                        continue;
                    }
                    if self.starts_with(self.pos, b"/*") {
                        self.skip_block(b"/*", b"*/")?;
                        continue;
                    }
                }
                SourceDialect::Lean => {
                    if self.starts_with(self.pos, b"--") {
                        self.skip_line();
                        continue;
                    }
                    if self.starts_with(self.pos, b"/-") {
                        self.skip_block(b"/-", b"-/")?;
                        continue;
                    }
                }
            }
            break;
        }
        Ok(())
    }

    fn tok(&self, kind: TokKind, start: usize, end: usize) -> Tok<'a> {
        Tok {
            kind,
            text: &self.src[start..end],
            start,
            end,
            raw: false,
        }
    }

    /// Scans an escaped string whose opening quote is at `q`; returns the
    /// offset one past the closing quote.
    fn escaped_string_end(&self, q: usize, start: usize) -> Result<usize, PeerScanError> {
        let mut i = q + 1;
        while i < self.end {
            match self.src.as_bytes()[i] {
                b'\\' => i += 2,
                b'"' => return Ok(i + 1),
                _ => i += 1,
            }
        }
        Err(PeerScanError::new(
            PeerScanErrorKind::UnterminatedString,
            start,
        ))
    }

    /// Scans a raw string whose `#` run starts at `h`.
    fn raw_string_end(&self, h: usize, start: usize) -> Result<Option<usize>, PeerScanError> {
        let mut hashes = 0usize;
        while self.byte(h + hashes) == b'#' {
            hashes += 1;
        }
        if self.byte(h + hashes) != b'"' {
            return Ok(None);
        }
        let mut i = h + hashes + 1;
        while i < self.end {
            if self.src.as_bytes()[i] == b'"' {
                let mut k = 0usize;
                while k < hashes && self.byte(i + 1 + k) == b'#' {
                    k += 1;
                }
                if k == hashes {
                    return Ok(Some(i + 1 + hashes));
                }
            }
            i += 1;
        }
        Err(PeerScanError::new(
            PeerScanErrorKind::UnterminatedString,
            start,
        ))
    }

    fn char_literal_end(&self, q: usize, start: usize) -> Result<usize, PeerScanError> {
        if q + 2 >= self.end {
            return Err(PeerScanError::new(
                PeerScanErrorKind::MalformedCharOrLifetime,
                start,
            ));
        }
        // Byte `q + 2` is the escaped byte itself (e.g. `'` in `'\''`), so the
        // closing quote cannot appear before `q + 3`.
        let mut i = q + 3;
        let limit = core::cmp::min(self.end, q + 2 + MAX_CHAR_ESCAPE_BYTES);
        while i < limit {
            if self.src.as_bytes()[i] == b'\'' {
                return Ok(i + 1);
            }
            i += 1;
        }
        Err(PeerScanError::new(
            PeerScanErrorKind::MalformedCharOrLifetime,
            start,
        ))
    }

    fn ident_end(&self, from: usize) -> usize {
        let mut i = from;
        while let Some(c) = self.char_at(i) {
            if !is_ident_continue(c, self.dialect) {
                break;
            }
            i += c.len_utf8();
        }
        i
    }

    fn rust_prefixed(&mut self, start: usize) -> Result<Option<Tok<'a>>, PeerScanError> {
        let b0 = self.byte(start);
        let b1 = self.byte(start + 1);
        if b0 == b'r' && b1 == b'#' {
            if let Some(c) = self.char_at(start + 2) {
                if is_ident_start(c) {
                    let end = self.ident_end(start + 2);
                    self.pos = end;
                    let mut t = self.tok(TokKind::Ident, start + 2, end);
                    t.start = start;
                    t.raw = true;
                    return Ok(Some(t));
                }
            }
        }
        let (raw, after) = match (b0, b1) {
            (b'b' | b'c', b'r') => (true, start + 2),
            (b'r', _) => (true, start + 1),
            (b'b' | b'c', _) => (false, start + 1),
            _ => return Ok(None),
        };
        if raw {
            if let Some(end) = self.raw_string_end(after, start)? {
                self.pos = end;
                return Ok(Some(self.tok(TokKind::Literal, start, end)));
            }
            return Ok(None);
        }
        match self.byte(after) {
            b'"' => {
                let end = self.escaped_string_end(after, start)?;
                self.pos = end;
                Ok(Some(self.tok(TokKind::Literal, start, end)))
            }
            b'\'' if b0 == b'b' => {
                let end = if self.byte(after + 1) == b'\\' {
                    self.char_literal_end(after, start)?
                } else if self.byte(after + 2) == b'\'' {
                    after + 3
                } else {
                    return Err(PeerScanError::new(
                        PeerScanErrorKind::MalformedCharOrLifetime,
                        start,
                    ));
                };
                self.pos = end;
                Ok(Some(self.tok(TokKind::Literal, start, end)))
            }
            _ => Ok(None),
        }
    }

    /// Next token, or `None` at the end of the range.
    fn next(&mut self) -> Result<Option<Tok<'a>>, PeerScanError> {
        self.skip_trivia()?;
        if self.pos >= self.end {
            return Ok(None);
        }
        let start = self.pos;
        let Some(c) = self.char_at(start) else {
            return Ok(None);
        };
        if self.dialect == SourceDialect::Rust {
            if let Some(t) = self.rust_prefixed(start)? {
                return Ok(Some(t));
            }
        }
        if c == '"' {
            let end = self.escaped_string_end(start, start)?;
            self.pos = end;
            return Ok(Some(self.tok(TokKind::Literal, start, end)));
        }
        if c == '\'' {
            if self.byte(start + 1) == b'\\' {
                let end = self.char_literal_end(start, start)?;
                self.pos = end;
                return Ok(Some(self.tok(TokKind::Literal, start, end)));
            }
            if let Some(c1) = self.char_at(start + 1) {
                let after = start + 1 + c1.len_utf8();
                if self.byte(after) == b'\'' {
                    self.pos = after + 1;
                    return Ok(Some(self.tok(TokKind::Literal, start, after + 1)));
                }
                if self.dialect == SourceDialect::Rust {
                    if is_ident_start(c1) {
                        let end = self.ident_end(start + 1);
                        self.pos = end;
                        return Ok(Some(self.tok(TokKind::Lifetime, start, end)));
                    }
                    return Err(PeerScanError::new(
                        PeerScanErrorKind::MalformedCharOrLifetime,
                        start,
                    ));
                }
            }
            self.pos = start + 1;
            return Ok(Some(self.tok(TokKind::Punct, start, start + 1)));
        }
        if is_ident_start(c) {
            let end = self.ident_end(start);
            self.pos = end;
            return Ok(Some(self.tok(TokKind::Ident, start, end)));
        }
        if c.is_ascii_digit() {
            let mut i = start;
            loop {
                while let Some(d) = self.char_at(i) {
                    if d.is_ascii_alphanumeric() || d == '_' {
                        i += 1;
                    } else {
                        break;
                    }
                }
                if self.byte(i) == b'.' && self.byte(i + 1).is_ascii_digit() {
                    i += 1;
                    continue;
                }
                break;
            }
            self.pos = i;
            return Ok(Some(self.tok(TokKind::Literal, start, i)));
        }
        let puncts: &[&str] = match self.dialect {
            SourceDialect::Rust => &RUST_PUNCTS,
            SourceDialect::Lean => &LEAN_PUNCTS,
        };
        for p in puncts {
            if self.starts_with(start, p.as_bytes()) {
                self.pos = start + p.len();
                return Ok(Some(self.tok(TokKind::Punct, start, self.pos)));
            }
        }
        self.pos = start + c.len_utf8();
        Ok(Some(self.tok(TokKind::Punct, start, self.pos)))
    }

    fn peek(&self) -> Result<Option<Tok<'a>>, PeerScanError> {
        let mut c = *self;
        c.next()
    }

    fn next_is_punct(&self, p: &str) -> Result<bool, PeerScanError> {
        Ok(matches!(self.peek()?, Some(t) if t.is_punct(p)))
    }

    fn next_is_kw(&self, k: &str) -> Result<bool, PeerScanError> {
        Ok(matches!(self.peek()?, Some(t) if t.is_kw(k)))
    }

    fn eat_punct(&mut self, p: &str) -> Result<bool, PeerScanError> {
        if self.next_is_punct(p)? {
            self.next()?;
            return Ok(true);
        }
        Ok(false)
    }

    fn is_empty(&self) -> Result<bool, PeerScanError> {
        Ok(self.peek()?.is_none())
    }
}

/// Fixed-capacity delimiter stack.
const MAX_NESTING: usize = 256;

struct DelimStack {
    buf: [u8; MAX_NESTING],
    len: usize,
}

impl DelimStack {
    const fn new() -> Self {
        Self {
            buf: [0; MAX_NESTING],
            len: 0,
        }
    }

    fn feed(&mut self, t: &Tok<'_>) -> Result<(), PeerScanError> {
        if t.kind != TokKind::Punct {
            return Ok(());
        }
        let (open, close) = match t.text {
            "(" => (Some(b')'), None),
            "[" => (Some(b']'), None),
            "{" => (Some(b'}'), None),
            "⦃" => (Some(b'>'), None),
            ")" => (None, Some(b')')),
            "]" => (None, Some(b']')),
            "}" => (None, Some(b'}')),
            "⦄" => (None, Some(b'>')),
            _ => (None, None),
        };
        if let Some(o) = open {
            if self.len == MAX_NESTING {
                return Err(PeerScanError::new(
                    PeerScanErrorKind::NestingTooDeep,
                    t.start,
                ));
            }
            self.buf[self.len] = o;
            self.len += 1;
        } else if let Some(c) = close {
            if self.len == 0 || self.buf[self.len - 1] != c {
                return Err(PeerScanError::new(
                    PeerScanErrorKind::UnbalancedDelimiter,
                    t.start,
                ));
            }
            self.len -= 1;
        }
        Ok(())
    }

    const fn depth(&self) -> usize {
        self.len
    }

    fn finish(&self, offset: usize) -> Result<(), PeerScanError> {
        if self.len == 0 {
            Ok(())
        } else {
            Err(PeerScanError::new(
                PeerScanErrorKind::UnbalancedDelimiter,
                offset,
            ))
        }
    }
}

/// `lx` is just after the opening delimiter `open`; consumes through the
/// matching closing delimiter and returns its offset.
fn skip_group(lx: &mut Lexer<'_>, open: &Tok<'_>) -> Result<usize, PeerScanError> {
    let mut st = DelimStack::new();
    st.feed(open)?;
    while let Some(t) = lx.next()? {
        st.feed(&t)?;
        if st.depth() == 0 {
            return Ok(t.start);
        }
    }
    Err(PeerScanError::new(
        PeerScanErrorKind::UnbalancedDelimiter,
        open.start,
    ))
}

/// `lx` is just after a `<`; consumes through the matching `>`.
fn skip_angles(lx: &mut Lexer<'_>, start: usize) -> Result<(), PeerScanError> {
    let mut depth = 1usize;
    while let Some(t) = lx.next()? {
        if t.is_punct("<") {
            depth += 1;
        } else if t.is_punct(">") {
            depth -= 1;
            if depth == 0 {
                return Ok(());
            }
        } else if t.is_open() {
            skip_group(lx, &t)?;
        } else if t.is_close() || t.is_punct(";") {
            break;
        }
    }
    Err(PeerScanError::new(
        PeerScanErrorKind::UnbalancedDelimiter,
        start,
    ))
}

/// If `r` is exactly one `open ... close` group, returns its interior.
fn whole_group<'a>(r: Lexer<'a>, open: &str) -> Result<Option<Lexer<'a>>, PeerScanError> {
    let mut c = r;
    let Some(t) = c.next()? else { return Ok(None) };
    if !t.is_punct(open) {
        return Ok(None);
    }
    let inner_start = c.pos;
    let close = skip_group(&mut c, &t)?;
    if c.is_empty()? {
        Ok(Some(r.range(inner_start, close)))
    } else {
        Ok(None)
    }
}

/// Splits a range at top-level commas (delimiter- and optionally angle-aware).
struct TopSplit<'a> {
    lx: Lexer<'a>,
    angles: bool,
    done: bool,
}

impl<'a> TopSplit<'a> {
    const fn new(lx: Lexer<'a>, angles: bool) -> Self {
        Self {
            lx,
            angles,
            done: false,
        }
    }

    fn next_part(&mut self) -> Result<Option<Lexer<'a>>, PeerScanError> {
        if self.done {
            return Ok(None);
        }
        let start = self.lx.pos;
        let mut angle = 0usize;
        loop {
            match self.lx.next()? {
                None => {
                    self.done = true;
                    let part = self.lx.range(start, self.lx.end);
                    return Ok(if part.is_empty()? { None } else { Some(part) });
                }
                Some(t) => {
                    if t.is_punct(",") && angle == 0 {
                        return Ok(Some(self.lx.range(start, t.start)));
                    }
                    if t.is_open() {
                        skip_group(&mut self.lx, &t)?;
                    } else if self.angles && t.is_punct("<") {
                        angle += 1;
                    } else if self.angles && t.is_punct(">") {
                        angle = angle.saturating_sub(1);
                    }
                }
            }
        }
    }
}

/// Finds the first top-level token among `ops`, stopping at any `stops`.
fn split_first_top<'a>(
    r: Lexer<'a>,
    ops: &[&str],
    stops: &[&str],
) -> Result<Option<(Lexer<'a>, Lexer<'a>, Tok<'a>)>, PeerScanError> {
    let mut c = r;
    while let Some(t) = c.next()? {
        if t.is_ident() && !t.raw && stops.contains(&t.text) {
            return Ok(None);
        }
        if (t.kind == TokKind::Punct || (t.is_ident() && !t.raw)) && ops.contains(&t.text) {
            return Ok(Some((r.range(r.pos, t.start), r.range(t.end, r.end), t)));
        }
        if t.kind == TokKind::Punct && stops.contains(&t.text) {
            return Ok(None);
        }
        if t.is_open() {
            skip_group(&mut c, &t)?;
        }
    }
    Ok(None)
}

/// Last identifier of a path range (`a::b::C<T>` gives `C`).
fn path_last_ident<'a>(r: Lexer<'a>) -> Result<Option<&'a str>, PeerScanError> {
    let mut c = r;
    let mut last = None;
    while let Some(t) = c.next()? {
        if t.is_ident() {
            last = Some(t.text);
        } else if t.is_punct("<") || t.is_open() {
            break;
        } else if !t.is_punct("::") {
            return Ok(None);
        }
    }
    Ok(last)
}

// ----------------------------------------------------------------------------
// Constant evaluation of clause bodies
// ----------------------------------------------------------------------------

const MAX_EVAL_DEPTH: usize = 32;

const INT_SUFFIXES: [&str; 12] = [
    "u8", "u16", "u32", "u64", "u128", "usize", "i8", "i16", "i32", "i64", "i128", "isize",
];

fn parse_int(text: &str) -> Option<u128> {
    if text.contains('.') {
        return None;
    }
    let (radix, digits) =
        if let Some(rest) = text.strip_prefix("0x").or_else(|| text.strip_prefix("0X")) {
            (16u128, rest)
        } else if let Some(rest) = text.strip_prefix("0o").or_else(|| text.strip_prefix("0O")) {
            (8u128, rest)
        } else if let Some(rest) = text.strip_prefix("0b").or_else(|| text.strip_prefix("0B")) {
            (2u128, rest)
        } else {
            (10u128, text)
        };
    let mut v: u128 = 0;
    let mut any = false;
    let mut tail_idx = digits.len();
    for (idx, ch) in digits.char_indices() {
        if ch == '_' {
            continue;
        }
        let d = match ch {
            '0'..='9' => Some(ch as u128 - '0' as u128),
            'a'..='f' if radix == 16 => Some(ch as u128 - 'a' as u128 + 10),
            'A'..='F' if radix == 16 => Some(ch as u128 - 'A' as u128 + 10),
            _ => None,
        };
        if let Some(d) = d.filter(|&d| d < radix) {
            v = v.checked_mul(radix)?.checked_add(d)?;
            any = true;
        } else {
            tail_idx = idx;
            break;
        }
    }
    if !any {
        return None;
    }
    let suffix = &digits[tail_idx..];
    if suffix.is_empty() || INT_SUFFIXES.contains(&suffix) {
        Some(v)
    } else {
        None
    }
}

/// Constant truth value of a clause body, when it is one.
fn const_bool(r: Lexer<'_>, depth: usize) -> Result<Option<bool>, PeerScanError> {
    if depth > MAX_EVAL_DEPTH {
        return Ok(None);
    }
    if let Some(inner) = whole_group(r, "(")? {
        return const_bool(inner, depth + 1);
    }
    if let Some(inner) = whole_group(r, "{")? {
        return const_bool(inner, depth + 1);
    }
    if let Some((l, rr, _)) = split_first_top(r, &["<==>", "↔", "<->"], &[])? {
        let a = const_bool(l, depth + 1)?;
        let b = const_bool(rr, depth + 1)?;
        return Ok(match (a, b) {
            (Some(x), Some(y)) => Some(x == y),
            _ => None,
        });
    }
    if let Some((l, rr, _)) = split_first_top(r, &["==>", "→"], &[])? {
        let a = const_bool(l, depth + 1)?;
        let b = const_bool(rr, depth + 1)?;
        return Ok(match (a, b) {
            (Some(false), _) | (_, Some(true)) => Some(true),
            (Some(true), Some(false)) => Some(false),
            _ => None,
        });
    }
    if let Some((l, rr, _)) = split_first_top(r, &["||", "∨"], &[])? {
        let a = const_bool(l, depth + 1)?;
        let b = const_bool(rr, depth + 1)?;
        return Ok(match (a, b) {
            (Some(true), _) | (_, Some(true)) => Some(true),
            (Some(false), Some(false)) => Some(false),
            _ => None,
        });
    }
    if let Some((l, rr, _)) = split_first_top(r, &["&&", "∧"], &[])? {
        let a = const_bool(l, depth + 1)?;
        let b = const_bool(rr, depth + 1)?;
        if conflicting_equalities(l, rr)? {
            return Ok(Some(false));
        }
        return Ok(match (a, b) {
            (Some(false), _) | (_, Some(false)) => Some(false),
            (Some(true), Some(true)) => Some(true),
            _ => None,
        });
    }
    if let Some((l, rr, op)) = split_first_top(r, &["==", "!="], &[])? {
        if let (Some(a), Some(b)) = (const_bool(l, depth + 1)?, const_bool(rr, depth + 1)?) {
            return Ok(Some(if op.text == "==" { a == b } else { a != b }));
        }
    }
    // A comparison of syntactically identical sides (`x != x`, `r < r`).
    if let Some((l, rr, op)) = split_first_top(r, &["==", "!=", "<", ">", "<=", ">=", "≠"], &[])?
    {
        if !l.is_empty()? && tokens_equal(l, rr)? {
            return Ok(Some(matches!(op.text, "==" | "<=" | ">=")));
        }
    }
    let mut c = r;
    let Some(t0) = c.next()? else { return Ok(None) };
    if t0.is_punct("!") || t0.is_punct("¬") || t0.is_kw("not") {
        return Ok(const_bool(r.range(c.pos, r.end), depth + 1)?.map(|b| !b));
    }
    if t0.is_kw("if") {
        let cond_start = c.pos;
        let mut open = None;
        while let Some(t) = c.next()? {
            if t.is_punct("{") {
                open = Some(t);
                break;
            }
            if t.is_open() {
                skip_group(&mut c, &t)?;
            }
        }
        if let Some(open) = open {
            let then_start = c.pos;
            let close = skip_group(&mut c, &open)?;
            let cond = const_bool(r.range(cond_start, open.start), depth + 1)?;
            if c.next_is_kw("else")? {
                c.next()?;
                let else_r = r.range(c.pos, r.end);
                let then_r = r.range(then_start, close);
                return match cond {
                    Some(true) => const_bool(then_r, depth + 1),
                    Some(false) => const_bool(else_r, depth + 1),
                    None => match (
                        const_bool(then_r, depth + 1)?,
                        const_bool(else_r, depth + 1)?,
                    ) {
                        (Some(a), Some(b)) if a == b => Ok(Some(a)),
                        _ => Ok(None),
                    },
                };
            }
        }
        return Ok(None);
    }
    let rest_empty = c.is_empty()?;
    if (t0.is_kw("false") || t0.is_kw("False")) && rest_empty {
        return Ok(Some(false));
    }
    if (t0.is_kw("true") || t0.is_kw("True")) && rest_empty {
        return Ok(Some(true));
    }
    if t0.kind == TokKind::Literal {
        let (Some(op), Some(t1)) = (c.next()?, c.next()?) else {
            return Ok(None);
        };
        if !c.is_empty()? || t1.kind != TokKind::Literal {
            return Ok(None);
        }
        let (Some(a), Some(b)) = (parse_int(t0.text), parse_int(t1.text)) else {
            return Ok(None);
        };
        return Ok(match op.text {
            "==" => Some(a == b),
            "!=" => Some(a != b),
            "<" => Some(a < b),
            ">" => Some(a > b),
            "<=" => Some(a <= b),
            ">=" => Some(a >= b),
            _ => None,
        });
    }
    Ok(None)
}

/// Whether two ranges hold the same token sequence.
fn tokens_equal(a: Lexer<'_>, b: Lexer<'_>) -> Result<bool, PeerScanError> {
    let (mut a, mut b) = (a, b);
    loop {
        match (a.next()?, b.next()?) {
            (None, None) => return Ok(true),
            (Some(x), Some(y)) if x.kind == y.kind && x.text == y.text => {}
            _ => return Ok(false),
        }
    }
}

/// `X == lit₁` and `X == lit₂` (any conjunct of either side) with the same `X`
/// and distinct literals: the conjunction is unsatisfiable.
fn conflicting_equalities(l: Lexer<'_>, r: Lexer<'_>) -> Result<bool, PeerScanError> {
    fn eq_lit<'a>(e: Lexer<'a>) -> Result<Option<(Lexer<'a>, &'a str)>, PeerScanError> {
        let Some((lhs, rhs, op)) = split_first_top(e, &["=="], &["&&", "||"])? else {
            return Ok(None);
        };
        let _ = op;
        let mut c = rhs;
        let Some(lit) = c.next()? else {
            return Ok(None);
        };
        if lit.kind != TokKind::Literal || !c.is_empty()? || lhs.is_empty()? {
            return Ok(None);
        }
        Ok(Some((lhs, lit.text)))
    }
    let mut lefts = TopAndSplit::new(l);
    while let Some(a) = lefts.next_part()? {
        let Some((xa, la)) = eq_lit(a)? else { continue };
        let mut rights = TopAndSplit::new(r);
        while let Some(b) = rights.next_part()? {
            let Some((xb, lb)) = eq_lit(b)? else { continue };
            if let (Some(va), Some(vb)) = (parse_int(la), parse_int(lb)) {
                if va != vb && tokens_equal(xa, xb)? {
                    return Ok(true);
                }
            }
        }
    }
    Ok(false)
}

/// Splits a range at top-level `&&` / `∧`.
struct TopAndSplit<'a> {
    rest: Option<Lexer<'a>>,
}

impl<'a> TopAndSplit<'a> {
    const fn new(r: Lexer<'a>) -> Self {
        Self { rest: Some(r) }
    }

    fn next_part(&mut self) -> Result<Option<Lexer<'a>>, PeerScanError> {
        let Some(r) = self.rest else { return Ok(None) };
        match split_first_top(r, &["&&", "∧"], &["||", "∨"])? {
            Some((l, rr, _)) => {
                self.rest = Some(rr);
                Ok(Some(l))
            }
            None => {
                self.rest = None;
                Ok(Some(r))
            }
        }
    }
}

/// Strips `move`, `|params|`, `||`, and an optional `-> T` from a closure
/// clause, returning its body.
fn strip_closure_params(r: Lexer<'_>) -> Result<Lexer<'_>, PeerScanError> {
    let mut c = r;
    if c.next_is_kw("move")? {
        c.next()?;
    }
    let save = c;
    match c.next()? {
        Some(t) if t.is_punct("||") => {}
        Some(t) if t.is_punct("|") => {
            let mut st = DelimStack::new();
            loop {
                let Some(p) = c.next()? else {
                    return Err(PeerScanError::new(
                        PeerScanErrorKind::UnbalancedDelimiter,
                        t.start,
                    ));
                };
                if p.is_punct("|") && st.depth() == 0 {
                    break;
                }
                st.feed(&p)?;
            }
        }
        _ => return Ok(r.range(save.pos, r.end)),
    }
    if c.next_is_punct("->")? {
        let mut probe = c;
        probe.next()?;
        while let Some(t) = probe.peek()? {
            if t.is_punct("{") {
                break;
            }
            probe.next()?;
        }
        c = probe;
    }
    Ok(r.range(c.pos, r.end))
}

/// A clause argument list: `ensures(a, b)` holds several clauses, while a
/// closure clause (`|a, b| ..`) is never split at its parameter commas.
enum ClauseList<'a> {
    Empty,
    Single(Lexer<'a>),
    Many(TopSplit<'a>),
}

fn clause_list(r: Lexer<'_>) -> Result<ClauseList<'_>, PeerScanError> {
    let mut c = r;
    if c.next_is_kw("move")?
        || c.next_is_kw("forall")?
        || c.next_is_kw("exists")?
        || c.next_is_kw("choose")?
    {
        c.next()?;
    }
    if c.next_is_punct("|")? || c.next_is_punct("||")? {
        return Ok(ClauseList::Single(r));
    }
    let mut parts = TopSplit::new(r, false);
    let Some(first) = parts.next_part()? else {
        return Ok(ClauseList::Empty);
    };
    if parts.next_part()?.is_none() {
        return Ok(ClauseList::Single(first));
    }
    Ok(ClauseList::Many(TopSplit::new(r, false)))
}

/// Whether a clause (`false`, `|r| false`, `[a, false]`, `x && false`,
/// `1 > 2`, ...) is unsatisfiable.
fn clause_is_unsatisfiable(r: Lexer<'_>, depth: usize) -> Result<bool, PeerScanError> {
    if depth > MAX_EVAL_DEPTH {
        return Ok(false);
    }
    let r = match clause_list(r)? {
        ClauseList::Empty => return Ok(false),
        ClauseList::Single(one) => one,
        ClauseList::Many(mut parts) => {
            while let Some(p) = parts.next_part()? {
                if clause_is_unsatisfiable(p, depth + 1)? {
                    return Ok(true);
                }
            }
            return Ok(false);
        }
    };
    let body = strip_closure_params(r)?;
    if let Some(inner) = whole_group(body, "[")? {
        let mut parts = TopSplit::new(inner, false);
        while let Some(p) = parts.next_part()? {
            if clause_is_unsatisfiable(p, depth + 1)? {
                return Ok(true);
            }
        }
        return Ok(false);
    }
    Ok(const_bool(body, 0)? == Some(false))
}

// ----------------------------------------------------------------------------
// Attribute classification (asymmetric `cfg_attr`)
// ----------------------------------------------------------------------------

const MAX_META_DEPTH: usize = 8;

/// Attribute facts accumulated for the next item.
#[derive(Clone, Copy, Debug, Default)]
struct AttrFlags {
    trusted_like: bool,
    external_body: bool,
    ensures_false: bool,
    diverging_claim: bool,
    ghost_token_ctor: bool,
    external_type_spec: bool,
    has_drop_impl: bool,
    invariant: bool,
    derive_default: bool,
    derive_unchecked: bool,
    requires_false: bool,
    models_drop: bool,
    no_drop_glue: bool,
    smart_constructor: bool,
}

impl AttrFlags {
    fn merge(&mut self, o: Self) {
        self.trusted_like |= o.trusted_like;
        self.external_body |= o.external_body;
        self.ensures_false |= o.ensures_false;
        self.diverging_claim |= o.diverging_claim;
        self.ghost_token_ctor |= o.ghost_token_ctor;
        self.external_type_spec |= o.external_type_spec;
        self.has_drop_impl |= o.has_drop_impl;
        self.invariant |= o.invariant;
        self.derive_default |= o.derive_default;
        self.derive_unchecked |= o.derive_unchecked;
        self.requires_false |= o.requires_false;
        self.models_drop |= o.models_drop;
        self.no_drop_glue |= o.no_drop_glue;
        self.smart_constructor |= o.smart_constructor;
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ClauseKind {
    Ensures,
    Requires,
}

trait ClauseVisitor<'a> {
    fn visit_clause(&mut self, kind: ClauseKind, clause: Lexer<'a>) -> GResult<()>;
}

struct NoClauses;

impl<'a> ClauseVisitor<'a> for NoClauses {
    fn visit_clause(&mut self, _kind: ClauseKind, _clause: Lexer<'a>) -> GResult<()> {
        Ok(())
    }
}

/// `lx` is just after `#`: consumes `[..]` or `![..]` and returns
/// `(is_inner, content)`, or `None` without consuming anything.
fn take_attribute<'a>(lx: &mut Lexer<'a>) -> Result<Option<(bool, Lexer<'a>)>, PeerScanError> {
    let mut c = *lx;
    let mut inner = false;
    let Some(mut t) = c.next()? else {
        return Ok(None);
    };
    if t.is_punct("!") {
        inner = true;
        let Some(t2) = c.next()? else { return Ok(None) };
        t = t2;
    }
    if !t.is_punct("[") {
        return Ok(None);
    }
    let start = c.pos;
    let close = skip_group(&mut c, &t)?;
    *lx = c;
    Ok(Some((inner, lx.range(start, close))))
}

fn handle_clause<'a>(
    kind: ClauseKind,
    clause: Lexer<'a>,
    in_cfg: bool,
    flags: &mut AttrFlags,
    visitor: &mut dyn ClauseVisitor<'a>,
) -> GResult<()> {
    let unsat = clause_is_unsatisfiable(clause, 0)?;
    match kind {
        ClauseKind::Ensures => flags.ensures_false |= unsat,
        ClauseKind::Requires => flags.requires_false |= unsat && !in_cfg,
    }
    visitor.visit_clause(kind, clause)
}

fn is_diverging_name(s: &str) -> bool {
    matches!(s, "diverging" | "is_diverging" | "diverges")
}

/// Classifies `key: value` and plain items of a `spec(..)`-style list.
fn classify_spec_args<'a>(
    args: Lexer<'a>,
    in_cfg: bool,
    depth: usize,
    flags: &mut AttrFlags,
    visitor: &mut dyn ClauseVisitor<'a>,
) -> GResult<()> {
    let mut lx = args;
    loop {
        let Some(first) = lx.peek()? else { break };
        if first.is_punct(",") {
            lx.next()?;
            continue;
        }
        let item_start = lx.pos;
        let mut probe = lx;
        probe.next()?;
        if first.is_ident() && probe.next_is_punct(":")? {
            probe.next()?;
            let value_start = probe.pos;
            // A closure's parameter list may contain commas.
            let mut scan = probe;
            if scan.next_is_kw("move")? {
                scan.next()?;
            }
            if scan.next_is_punct("|")? {
                let bar = scan.next()?;
                let mut st = DelimStack::new();
                loop {
                    let Some(p) = scan.next()? else {
                        let at = bar.map_or(value_start, |b| b.start);
                        return Err(
                            PeerScanError::new(PeerScanErrorKind::UnbalancedDelimiter, at).into(),
                        );
                    };
                    if p.is_punct("|") && st.depth() == 0 {
                        break;
                    }
                    st.feed(&p)?;
                }
            }
            let mut value_end = args.end;
            while let Some(t) = scan.next()? {
                if t.is_punct(",") {
                    value_end = t.start;
                    break;
                }
                if t.is_open() {
                    skip_group(&mut scan, &t)?;
                }
            }
            let value = args.range(value_start, value_end);
            match first.text {
                "ensures" | "post" | "maintains" => {
                    handle_clause(ClauseKind::Ensures, value, in_cfg, flags, visitor)?;
                }
                "requires" | "pre" => {
                    handle_clause(ClauseKind::Requires, value, in_cfg, flags, visitor)?;
                }
                "trusted" | "assumed" => {
                    if const_bool(value, 0)? != Some(false) {
                        flags.trusted_like = true;
                    }
                }
                "external_body" => {
                    if const_bool(value, 0)? != Some(false) {
                        flags.trusted_like = true;
                        flags.external_body = true;
                    }
                }
                s if is_diverging_name(s) => {
                    if const_bool(value, 0)? != Some(false) {
                        flags.diverging_claim = true;
                    }
                }
                _ => {}
            }
            lx = scan;
            continue;
        }
        let mut scan = lx;
        let mut item_end = args.end;
        while let Some(t) = scan.next()? {
            if t.is_punct(",") {
                item_end = t.start;
                break;
            }
            if t.is_open() {
                skip_group(&mut scan, &t)?;
            }
        }
        let item = args.range(item_start, item_end);
        let mut c = item;
        let single = match c.next()? {
            Some(t) if t.is_ident() && c.is_empty()? => Some(t.text),
            _ => None,
        };
        match single {
            Some("trusted" | "assumed") => flags.trusted_like = true,
            Some("external_body") => {
                flags.trusted_like = true;
                flags.external_body = true;
            }
            Some(s) if is_diverging_name(s) => flags.diverging_claim = true,
            _ => classify_meta(item, in_cfg, depth + 1, flags, visitor)?,
        }
        lx = scan;
    }
    Ok(())
}

/// Classifies one attribute meta item (`path`, `path(args)`, `path = value`).
fn classify_meta<'a>(
    meta: Lexer<'a>,
    in_cfg: bool,
    depth: usize,
    flags: &mut AttrFlags,
    visitor: &mut dyn ClauseVisitor<'a>,
) -> GResult<()> {
    if depth > MAX_META_DEPTH {
        return Err(PeerScanError::new(PeerScanErrorKind::NestingTooDeep, meta.pos).into());
    }
    let mut lx = meta;
    let mut name: Option<&'a str> = None;
    loop {
        let save = lx;
        match lx.next()? {
            Some(t) if t.is_ident() => {
                name = Some(t.text);
                if !lx.eat_punct("::")? {
                    break;
                }
            }
            Some(t) if t.is_punct("::") && name.is_none() => {}
            _ => {
                lx = save;
                break;
            }
        }
    }
    let Some(name) = name else { return Ok(()) };
    let mut args: Option<Lexer<'a>> = None;
    let mut value: Option<Lexer<'a>> = None;
    match lx.next()? {
        Some(t) if t.is_open() => {
            let s = lx.pos;
            let close = skip_group(&mut lx, &t)?;
            args = Some(meta.range(s, close));
        }
        Some(t) if t.is_punct("=") => value = Some(meta.range(lx.pos, meta.end)),
        _ => {}
    }
    match name {
        "cfg_attr" => {
            if let Some(a) = args {
                let mut parts = TopSplit::new(a, false);
                let _predicate = parts.next_part()?;
                while let Some(p) = parts.next_part()? {
                    classify_meta(p, true, depth + 1, flags, visitor)?;
                }
            }
        }
        "verifier" => {
            if let Some(a) = args {
                let mut parts = TopSplit::new(a, false);
                while let Some(p) = parts.next_part()? {
                    classify_meta(p, in_cfg, depth + 1, flags, visitor)?;
                }
            }
        }
        "spec" | "embed_spec" | "contract" | "external_spec" | "extern_spec" => {
            if matches!(name, "external_spec" | "extern_spec") {
                flags.trusted_like = true;
            }
            if let Some(a) = args {
                classify_spec_args(a, in_cfg, depth + 1, flags, visitor)?;
            }
        }
        "trusted" | "assumed" | "external" | "external_fn_specification" => {
            let explicit_false = match value {
                Some(v) => const_bool(v, 0)? == Some(false),
                None => false,
            };
            if !explicit_false {
                flags.trusted_like = true;
            }
        }
        "external_body" => {
            let explicit_false = match value {
                Some(v) => const_bool(v, 0)? == Some(false),
                None => false,
            };
            if !explicit_false {
                flags.trusted_like = true;
                flags.external_body = true;
            }
        }
        "ensures" | "post" | "maintains" => {
            if let Some(a) = args {
                handle_clause(ClauseKind::Ensures, a, in_cfg, flags, visitor)?;
            }
        }
        "requires" | "pre" => {
            if let Some(a) = args {
                handle_clause(ClauseKind::Requires, a, in_cfg, flags, visitor)?;
            }
        }
        s if is_diverging_name(s) => {
            let explicit_false = match value {
                Some(v) => const_bool(v, 0)? == Some(false),
                None => false,
            };
            if !explicit_false {
                flags.diverging_claim = true;
            }
        }
        "ghost_token_ctor" => flags.ghost_token_ctor = true,
        "external_type_specification" => flags.external_type_spec = true,
        "has_drop_impl" => flags.has_drop_impl = true,
        "models_drop" => flags.models_drop |= !in_cfg,
        "no_drop_glue" => flags.no_drop_glue |= !in_cfg,
        "invariant" | "type_invariant" => flags.invariant = true,
        "derive" => {
            if let Some(a) = args {
                let mut parts = TopSplit::new(a, false);
                while let Some(p) = parts.next_part()? {
                    match path_last_ident(p)? {
                        Some("Default") => flags.derive_default = true,
                        Some(d) if UNCHECKED_CONSTRUCTOR_TRAITS.contains(&d) => {
                            flags.derive_unchecked = true;
                        }
                        _ => {}
                    }
                }
            }
        }
        "smart_constructor" => flags.smart_constructor |= !in_cfg,
        _ => {}
    }
    Ok(())
}

/// Traits whose derives or impls build values without running a constructor
/// (deserialization, byte reinterpretation, fuzzing).
const UNCHECKED_CONSTRUCTOR_TRAITS: [&str; 12] = [
    "Deserialize",
    "Arbitrary",
    "FromBytes",
    "FromZeros",
    "FromZeroes",
    "TryFromBytes",
    "AnyBitPattern",
    "Pod",
    "Zeroable",
    "CheckedBitPattern",
    "FromBits",
    "FromRaw",
];

/// Calls that materialize a value from raw bits, bypassing constructors.
const RAW_MATERIALIZERS: [&str; 16] = [
    "transmute",
    "transmute_copy",
    "zeroed",
    "uninitialized",
    "assume_init",
    "assume_init_read",
    "assume_init_ref",
    "assume_init_mut",
    "read_unaligned",
    "read_volatile",
    "from_raw_parts",
    "from_bytes",
    "read_from_bytes",
    "read_from_prefix",
    "mut_from_bytes",
    "ref_from_bytes",
];

/// Returns the byte offset of the first raw-bit materialization call in `body`
/// (including `ptr::read`).
fn body_raw_materializer(body: Lexer<'_>) -> Result<Option<usize>, PeerScanError> {
    let mut bc = body;
    let mut prev2: Option<Tok<'_>> = None;
    let mut prev1: Option<Tok<'_>> = None;
    while let Some(n) = bc.next()? {
        if n.is_ident() {
            if RAW_MATERIALIZERS.contains(&n.text) {
                return Ok(Some(n.start));
            }
            if n.text == "read"
                && matches!(prev1, Some(p) if p.is_punct("::"))
                && matches!(prev2, Some(p) if p.is_ident() && p.text == "ptr")
            {
                return Ok(Some(n.start));
            }
        }
        prev2 = prev1;
        prev1 = Some(n);
    }
    Ok(None)
}

fn classify_attribute<'a>(
    content: Lexer<'a>,
    visitor: &mut dyn ClauseVisitor<'a>,
) -> GResult<AttrFlags> {
    let mut f = AttrFlags::default();
    classify_meta(content, false, 0, &mut f, visitor)?;
    Ok(f)
}

// ----------------------------------------------------------------------------
// Shared item parsing
// ----------------------------------------------------------------------------

/// Parsed `impl` header.
#[derive(Clone, Copy, Debug)]
struct ImplHeader<'a> {
    self_ty: &'a str,
    trait_last: Option<&'a str>,
}

fn parse_impl_header<'a>(after_impl: Lexer<'a>) -> Result<Option<ImplHeader<'a>>, PeerScanError> {
    let mut c = after_impl;
    if c.next_is_punct("<")? {
        let lt = c.next()?;
        let at = lt.map_or(c.pos, |t| t.start);
        skip_angles(&mut c, at)?;
    }
    let mut first_last: Option<&'a str> = None;
    let mut second_last: Option<&'a str> = None;
    let mut seen_for = false;
    let mut angle = 0usize;
    while let Some(t) = c.next()? {
        if angle == 0 && (t.is_punct("{") || t.is_punct(";") || t.is_kw("where")) {
            break;
        }
        if t.is_punct("<") {
            angle += 1;
        } else if t.is_punct(">") {
            angle = angle.saturating_sub(1);
        } else if t.is_open() {
            skip_group(&mut c, &t)?;
        } else if angle == 0 {
            if t.is_kw("for") {
                seen_for = true;
            } else if t.is_ident() && !matches!(t.text, "dyn" | "mut" | "const" | "unsafe") {
                if seen_for {
                    second_last = Some(t.text);
                } else {
                    first_last = Some(t.text);
                }
            }
        }
    }
    Ok(match (seen_for, first_last, second_last) {
        (true, tr, Some(s)) => Some(ImplHeader {
            self_ty: s,
            trait_last: tr,
        }),
        (false, Some(s), _) => Some(ImplHeader {
            self_ty: s,
            trait_last: None,
        }),
        _ => None,
    })
}

/// Parsed `fn` signature.
#[derive(Clone, Copy, Debug)]
struct FnSig<'a> {
    name: Tok<'a>,
    ret_uninhabited: bool,
    /// Verus-style signature clauses (`requires ..`, `ensures ..`), if any.
    clauses: Option<Lexer<'a>>,
    /// Lexer positioned at the body `{` or the terminating `;`.
    rest: Lexer<'a>,
}

/// Returns whether the source locally defines `Infallible` (so bare `Infallible`
/// must not be assumed uninhabited).
fn shadows_infallible(src: &str) -> Result<bool, PeerScanError> {
    let mut lx = Lexer::new(src, SourceDialect::Rust);
    while let Some(t) = lx.next()? {
        if t.is_kw("struct") || t.is_kw("type") || t.is_kw("union") || t.is_kw("enum") {
            if let Some(name) = lx.peek()? {
                if name.is_ident() && name.text == "Infallible" {
                    return Ok(true);
                }
            }
        }
    }
    Ok(false)
}

fn type_is_uninhabited(r: Lexer<'_>, infallible_shadowed: bool) -> Result<bool, PeerScanError> {
    // Verus named return `(r: T)`.
    if let Some(inner) = whole_group(r, "(")? {
        let mut c = inner;
        if let (Some(n), true) = (c.next()?, c.next_is_punct(":")?) {
            if n.is_ident() {
                c.next()?;
                return type_is_uninhabited(inner.range(c.pos, inner.end), infallible_shadowed);
            }
        }
    }
    let mut c = r;
    match c.next()? {
        Some(t) if t.is_punct("!") => c.is_empty(),
        Some(t) if t.is_ident() || t.is_punct("::") => {
            let mut segs: [&str; 4] = [""; 4];
            let mut len = 0usize;
            if t.is_ident() {
                segs[0] = t.text;
                len = 1;
            }
            while let Some(n) = c.next()? {
                if n.is_ident() {
                    if len == segs.len() {
                        return Ok(false);
                    }
                    segs[len] = n.text;
                    len += 1;
                } else if !n.is_punct("::") {
                    return Ok(false);
                }
            }
            Ok(match &segs[..len] {
                ["Infallible"] => !infallible_shadowed,
                ["core", "convert", "Infallible"] | ["std", "convert", "Infallible"] => true,
                _ => false,
            })
        }
        _ => Ok(false),
    }
}

/// Verus signature-clause keywords.
const SIG_CLAUSE_KEYWORDS: [&str; 7] = [
    "requires",
    "ensures",
    "recommends",
    "decreases",
    "opens_invariants",
    "no_unwind",
    "returns",
];

/// Visits each comma-separated expression of the `requires` / `ensures`
/// signature clauses (`ensures false, r > 0`), keeping balanced `|...|`
/// quantifier/closure parameter lists intact.
fn for_each_sig_clause<'a>(
    clauses: Lexer<'a>,
    f: &mut dyn FnMut(ClauseKind, Lexer<'a>) -> GResult<()>,
) -> GResult<()> {
    let mut c = clauses;
    let mut kind: Option<ClauseKind> = None;
    let mut seg_start = c.pos;
    let mut prev: Option<Tok<'a>> = None;
    loop {
        let before = c.pos;
        let t = c.next()?;
        let boundary = match t {
            None => true,
            Some(t) => {
                t.is_punct(",") || (t.is_ident() && !t.raw && SIG_CLAUSE_KEYWORDS.contains(&t.text))
            }
        };
        if boundary {
            if let Some(k) = kind {
                let seg = clauses.range(seg_start, before);
                if !seg.is_empty()? {
                    f(k, seg)?;
                }
            }
            let Some(t) = t else { break };
            if t.is_ident() {
                kind = match t.text {
                    "ensures" | "returns" => Some(ClauseKind::Ensures),
                    "requires" => Some(ClauseKind::Requires),
                    _ => None,
                };
            }
            seg_start = c.pos;
            prev = Some(t);
            continue;
        }
        if let Some(t) = t {
            if t.is_open() {
                skip_group(&mut c, &t)?;
            } else if t.is_punct("|")
                && (before == seg_start
                    || matches!(
                        prev,
                        Some(p) if p.is_kw("forall")
                            || p.is_kw("exists")
                            || p.is_kw("choose")
                            || p.is_kw("move")
                            || starts_expression(Some(p))
                    ))
            {
                let mut pst = DelimStack::new();
                loop {
                    let Some(p) = c.next()? else {
                        return Err(PeerScanError::new(
                            PeerScanErrorKind::UnbalancedDelimiter,
                            t.start,
                        )
                        .into());
                    };
                    if p.is_punct("|") && pst.depth() == 0 {
                        break;
                    }
                    pst.feed(&p)?;
                }
            }
            prev = Some(t);
        }
    }
    Ok(())
}

/// Whether a `{ ... }` seen while scanning Verus signature clauses is part of
/// a clause expression (`ensures if b { false } else { false } { body }`,
/// `ensures { false };`) rather than the function body itself.
fn brace_continues_sig_clause(
    after_open: Lexer<'_>,
    open: &Tok<'_>,
) -> Result<bool, PeerScanError> {
    let mut probe = after_open;
    skip_group(&mut probe, open)?;
    let Some(next) = probe.peek()? else {
        return Ok(false);
    };
    Ok(next.is_kw("else")
        || next.is_punct(",")
        || next.is_punct(";")
        || next.is_punct("{")
        || next.is_punct("==>")
        || next.is_punct("<==>")
        || next.is_punct("&&")
        || next.is_punct("||")
        || next.is_punct("==")
        || next.is_punct("!=")
        || (next.is_ident() && !next.raw && SIG_CLAUSE_KEYWORDS.contains(&next.text)))
}

fn scan_fn_signature<'a>(
    after_fn: Lexer<'a>,
    infallible_shadowed: bool,
) -> Result<Option<FnSig<'a>>, PeerScanError> {
    let mut c = after_fn;
    let Some(name) = c.next()? else {
        return Ok(None);
    };
    if !name.is_ident() {
        return Ok(None);
    }
    if c.next_is_punct("<")? {
        let lt = c.next()?;
        let at = lt.map_or(c.pos, |t| t.start);
        skip_angles(&mut c, at)?;
    }
    let Some(p) = c.next()? else { return Ok(None) };
    if !p.is_punct("(") {
        return Ok(None);
    }
    skip_group(&mut c, &p)?;
    let mut ret_uninhabited = false;
    if c.next_is_punct("->")? {
        c.next()?;
        let start = c.pos;
        let mut end = c.end;
        let mut angle = 0usize;
        loop {
            let save = c;
            let Some(t) = c.next()? else { break };
            if angle == 0
                && (t.is_punct("{")
                    || t.is_punct(";")
                    || t.is_kw("where")
                    || (t.is_ident() && !t.raw && SIG_CLAUSE_KEYWORDS.contains(&t.text)))
            {
                end = t.start;
                c = save;
                break;
            }
            if t.is_punct("<") {
                angle += 1;
            } else if t.is_punct(">") {
                angle = angle.saturating_sub(1);
            } else if t.is_open() {
                skip_group(&mut c, &t)?;
            }
        }
        ret_uninhabited = type_is_uninhabited(after_fn.range(start, end), infallible_shadowed)?;
    }
    let mut clause_start: Option<usize> = None;
    while let Some(t) = c.peek()? {
        if t.is_punct(";") {
            break;
        }
        if t.is_punct("{") {
            if clause_start.is_some() {
                let mut probe = c;
                probe.next()?;
                if brace_continues_sig_clause(probe, &t)? {
                    c.next()?;
                    skip_group(&mut c, &t)?;
                    continue;
                }
            }
            break;
        }
        if clause_start.is_none() && t.is_ident() && !t.raw && SIG_CLAUSE_KEYWORDS.contains(&t.text)
        {
            clause_start = Some(t.start);
        }
        c.next()?;
        if t.is_open() {
            skip_group(&mut c, &t)?;
        }
    }
    Ok(Some(FnSig {
        name,
        ret_uninhabited,
        clauses: clause_start.map(|s| after_fn.range(s, c.pos)),
        rest: c,
    }))
}

/// Advances `lx` past an `impl`/`trait`/`mod` header (skipping generics,
/// parens/brackets, and `where` bounds) to its opening `{` or terminating `;`,
/// without consuming `{` or `;`.
fn skip_item_header_to_brace(lx: &mut Lexer<'_>) -> Result<(), PeerScanError> {
    let mut angle = 0usize;
    while let Some(t) = lx.peek()? {
        if angle == 0 && (t.is_punct("{") || t.is_punct(";")) {
            return Ok(());
        }
        lx.next()?;
        if t.is_punct("<") {
            angle += 1;
        } else if t.is_punct(">") {
            angle = angle.saturating_sub(1);
        } else if t.is_open() {
            skip_group(lx, &t)?;
        }
    }
    Ok(())
}

/// One structure field.
#[derive(Clone, Copy, Debug)]
struct FieldInfo<'a> {
    is_pub: bool,
    ty: Lexer<'a>,
    offset: usize,
}

/// Parsed `struct` / `enum` / `union` item.
#[derive(Clone, Copy, Debug)]
struct StructItem<'a> {
    name: &'a str,
    /// Interior of the body group (`None` for a unit struct).
    body: Option<Lexer<'a>>,
    tuple: bool,
}

fn parse_struct_item<'a>(after_kw: Lexer<'a>) -> Result<Option<StructItem<'a>>, PeerScanError> {
    let mut c = after_kw;
    let Some(name) = c.next()? else {
        return Ok(None);
    };
    if !name.is_ident() {
        return Ok(None);
    }
    if c.next_is_punct("<")? {
        let lt = c.next()?;
        let at = lt.map_or(c.pos, |t| t.start);
        skip_angles(&mut c, at)?;
    }
    let mut in_where = false;
    let mut angle = 0usize;
    while let Some(t) = c.next()? {
        if angle == 0 && t.is_punct(";") {
            return Ok(Some(StructItem {
                name: name.text,
                body: None,
                tuple: false,
            }));
        }
        if angle == 0 && t.is_kw("where") {
            in_where = true;
            continue;
        }
        if t.is_punct("<") {
            angle += 1;
            continue;
        }
        if t.is_punct(">") {
            angle = angle.saturating_sub(1);
            continue;
        }
        if angle == 0 && ((!in_where && t.is_punct("(")) || t.is_punct("{")) {
            let s = c.pos;
            let close = skip_group(&mut c, &t)?;
            return Ok(Some(StructItem {
                name: name.text,
                body: Some(after_kw.range(s, close)),
                tuple: t.is_punct("("),
            }));
        }
        if t.is_open() {
            skip_group(&mut c, &t)?;
        }
    }
    Ok(None)
}

/// Visits the fields of a structure body (attributes and visibility stripped).
fn for_each_field<'a>(
    body: Lexer<'a>,
    tuple: bool,
    f: &mut dyn FnMut(FieldInfo<'a>) -> GResult<()>,
) -> GResult<()> {
    let mut parts = TopSplit::new(body, true);
    while let Some(part) = parts.next_part()? {
        let mut c = part;
        let mut is_pub = false;
        let mut offset = part.pos;
        loop {
            let save = c;
            let Some(t) = c.next()? else { break };
            if t.is_punct("#") {
                if take_attribute(&mut c)?.is_some() {
                    continue;
                }
            }
            if t.is_kw("pub") {
                is_pub = true;
                offset = t.start;
                if c.next_is_punct("(")? {
                    let p = c.next()?;
                    if let Some(p) = p {
                        skip_group(&mut c, &p)?;
                    }
                }
                continue;
            }
            c = save;
            break;
        }
        if !tuple {
            // `name : type`
            let mut probe = c;
            if let (Some(n), true) = (probe.next()?, probe.next_is_punct(":")?) {
                if n.is_ident() {
                    probe.next()?;
                    c = probe;
                }
            }
        }
        if !c.is_empty()? {
            f(FieldInfo {
                is_pub,
                ty: part.range(c.pos, part.end),
                offset,
            })?;
        }
    }
    Ok(())
}

const PRIMITIVE_TYPES: [&str; 17] = [
    "u8", "u16", "u32", "u64", "u128", "usize", "i8", "i16", "i32", "i64", "i128", "isize", "bool",
    "char", "f32", "f64", "str",
];

/// Whether a field type provably has no drop glue (primitives, references,
/// raw pointers, `PhantomData`, and tuples / arrays of those).
fn type_is_transparent(
    r: Lexer<'_>,
    drops: &PairTable<'_, MAX_DROP_TYPES>,
    depth: usize,
) -> Result<bool, PeerScanError> {
    if depth > MAX_EVAL_DEPTH {
        return Ok(false);
    }
    let mut c = r;
    let Some(t) = c.peek()? else { return Ok(true) };
    if t.is_punct("&") || t.is_punct("&&") || t.is_punct("*") {
        return Ok(true);
    }
    if let Some(inner) = whole_group(r, "(")? {
        let mut parts = TopSplit::new(inner, true);
        while let Some(p) = parts.next_part()? {
            if !type_is_transparent(p, drops, depth + 1)? {
                return Ok(false);
            }
        }
        return Ok(true);
    }
    if let Some(inner) = whole_group(r, "[")? {
        let elem = match split_first_top(inner, &[";"], &[])? {
            Some((l, _, _)) => l,
            None => inner,
        };
        return type_is_transparent(elem, drops, depth + 1);
    }
    let mut segs: [&str; 4] = [""; 4];
    let mut len = 0usize;
    let mut saw_angle = false;
    while let Some(n) = c.next()? {
        if n.is_ident() {
            if len == segs.len() {
                return Ok(false);
            }
            segs[len] = n.text;
            len += 1;
        } else if n.is_punct("<") {
            saw_angle = true;
            break;
        } else if !n.is_punct("::") {
            return Ok(false);
        }
    }
    if saw_angle {
        return Ok(match &segs[..len] {
            ["PhantomData"] => !drops.contains_first("PhantomData"),
            ["core", "marker", "PhantomData"] | ["std", "marker", "PhantomData"] => true,
            _ => false,
        });
    }
    Ok(len == 1 && PRIMITIVE_TYPES.contains(&segs[0]))
}

/// Fixed-capacity table of name pairs.
#[derive(Clone, Copy)]
struct PairTable<'a, const N: usize> {
    items: [(&'a str, &'a str); N],
    len: usize,
}

impl<'a, const N: usize> PairTable<'a, N> {
    const fn new() -> Self {
        Self {
            items: [("", ""); N],
            len: 0,
        }
    }

    fn entries(&self) -> &[(&'a str, &'a str)] {
        &self.items[..self.len]
    }

    fn contains(&self, a: &str, b: &str) -> bool {
        self.entries().iter().any(|&(x, y)| x == a && y == b)
    }

    fn contains_first(&self, a: &str) -> bool {
        self.entries().iter().any(|&(x, _)| x == a)
    }

    /// Inserts a pair; returns whether it was new.
    fn push(&mut self, a: &'a str, b: &'a str, offset: usize) -> Result<bool, PeerScanError> {
        if self.contains(a, b) {
            return Ok(false);
        }
        if self.len == N {
            return Err(PeerScanError::new(PeerScanErrorKind::TableFull, offset));
        }
        self.items[self.len] = (a, b);
        self.len += 1;
        Ok(true)
    }
}

// ----------------------------------------------------------------------------
// Guard 3 — unsatisfiable extern `ensures` (`creusot#2388`)
// ----------------------------------------------------------------------------

/// How a contract enters the trusted base.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ContractTrust {
    /// Verified against its body.
    Verified,
    /// `#[extern_spec]` / `extern_spec! { .. }`.
    ExternSpec,
    /// `#[external_spec]`.
    ExternalSpec,
    /// `#[trusted]` / `#[spec(trusted, ..)]`.
    Trusted,
    /// `#[spec(assumed, ..)]`.
    Assumed,
    /// `#[verifier::external_body]`.
    ExternalBody,
}

/// Facts about one function contract (`ExternContract` in Lean).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct ExternEnsuresDescriptor {
    /// How the contract is trusted.
    pub trust: ContractTrust,
    /// The `ensures` clause is unsatisfiable (`ensures(false)`).
    pub ensures_unsatisfiable: bool,
    /// An unconditional (non-`cfg_attr`) `requires(false)` is present.
    pub requires_false: bool,
    /// The contract claims divergence.
    pub is_diverging: bool,
    /// The return type is uninhabited (`!`, `Infallible`).
    pub return_uninhabited: bool,
}

/// Descriptor check of Guard 3 (`ExternalEnsuresFalseGuard`): a divergence
/// claim requires an uninhabited return type, and an assumed contract with an
/// unsatisfiable `ensures` must return an uninhabited type or be unreachable
/// (`requires(false)`).
pub fn check_extern_ensures_false(
    desc: &ExternEnsuresDescriptor,
) -> Result<(), PeerSoundnessGuardViolation> {
    if desc.is_diverging && !desc.return_uninhabited {
        return Err(descriptor_violation(PeerViolationReason::LyingDivergence));
    }
    if desc.trust != ContractTrust::Verified
        && desc.ensures_unsatisfiable
        && !desc.requires_false
        && !desc.return_uninhabited
    {
        return Err(descriptor_violation(
            PeerViolationReason::EnsuresFalseOnReturningFn,
        ));
    }
    Ok(())
}

/// Source scanner of Guard 3 over Rust source.
pub fn check_extern_ensures_false_source(src: &str) -> GResult<()> {
    let infallible_shadowed = shadows_infallible(src)?;
    let mut lx = Lexer::new(src, SourceDialect::Rust);
    let mut st = DelimStack::new();
    let mut pending = AttrFlags::default();
    let mut scope_pending = false;
    let mut trusted_depth: Option<usize> = None;
    while let Some(t) = lx.next()? {
        if t.is_punct("#") {
            if let Some((inner, content)) = take_attribute(&mut lx)? {
                let f = classify_attribute(content, &mut NoClauses)?;
                if inner {
                    if f.trusted_like && trusted_depth.is_none() {
                        trusted_depth = Some(st.depth());
                    }
                } else {
                    pending.merge(f);
                }
                continue;
            }
        }
        if t.is_open() {
            st.feed(&t)?;
            if t.is_punct("{") {
                if scope_pending && trusted_depth.is_none() {
                    trusted_depth = Some(st.depth());
                }
                scope_pending = false;
                pending = AttrFlags::default();
            }
            continue;
        }
        if t.is_close() {
            st.feed(&t)?;
            if matches!(trusted_depth, Some(d) if st.depth() < d) {
                trusted_depth = None;
            }
            if t.is_punct("}") {
                pending = AttrFlags::default();
            }
            continue;
        }
        if t.is_punct(";") {
            pending = AttrFlags::default();
            scope_pending = false;
            continue;
        }
        if !t.is_ident() || t.raw {
            continue;
        }
        match t.text {
            "fn" => {
                if let Some(sig) = scan_fn_signature(lx, infallible_shadowed)? {
                    if let Some(clauses) = sig.clauses {
                        for_each_sig_clause(clauses, &mut |kind, seg| {
                            let unsat = clause_is_unsatisfiable(seg, 0)?;
                            match kind {
                                ClauseKind::Ensures => pending.ensures_false |= unsat,
                                ClauseKind::Requires => pending.requires_false |= unsat,
                            }
                            Ok(())
                        })?;
                    }
                    let trusted = pending.trusted_like || trusted_depth.is_some();
                    if pending.diverging_claim && !sig.ret_uninhabited {
                        return violation(PeerViolationReason::LyingDivergence, sig.name.start);
                    }
                    if trusted
                        && pending.ensures_false
                        && !pending.requires_false
                        && !sig.ret_uninhabited
                    {
                        return violation(
                            PeerViolationReason::EnsuresFalseOnReturningFn,
                            sig.name.start,
                        );
                    }
                    lx = sig.rest;
                }
                pending = AttrFlags::default();
            }
            "impl" | "mod" | "trait" => {
                if pending.trusted_like {
                    scope_pending = true;
                    skip_item_header_to_brace(&mut lx)?;
                }
                pending = AttrFlags::default();
            }
            "extern_spec" => {
                if lx.eat_punct("!")? {
                    if let Some(open) = lx.next()? {
                        if open.is_open() {
                            st.feed(&open)?;
                            if trusted_depth.is_none() {
                                trusted_depth = Some(st.depth());
                            }
                        }
                    }
                }
            }
            "extern" => {
                let mut c = lx;
                let next = c.next()?;
                let block = match next {
                    Some(n) if n.is_punct("{") => true,
                    Some(n) if n.kind == TokKind::Literal => c.next_is_punct("{")?,
                    _ => false,
                };
                if block && pending.trusted_like {
                    scope_pending = true;
                }
                if matches!(next, Some(n) if n.is_kw("crate")) {
                    pending = AttrFlags::default();
                }
            }
            "struct" | "enum" | "union" | "type" | "use" | "let" | "macro_rules" | "static" => {
                pending = AttrFlags::default();
            }
            _ => {}
        }
    }
    st.finish(src.len())?;
    Ok(())
}

// ----------------------------------------------------------------------------
// Guard 4 — `FnDef` ghost-token coercion (`creusot#2389`)
// ----------------------------------------------------------------------------

/// Facts about ghost-token constructor usage (`TokProg` in Lean).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub struct GhostTokenUsageDescriptor {
    /// Non-call uses of the constructor as a value.
    pub fn_def_value_coercions: usize,
    /// Direct call sites.
    pub call_sites: usize,
    /// Call sites in a loop, closure, or `async` block.
    pub call_sites_in_repeating_context: usize,
    /// Call sites outside `main`.
    pub call_sites_outside_main: usize,
    /// `main` is re-entered or aliased.
    pub main_reentrant: bool,
    /// The constructor type is an explicit generic argument of a function call.
    pub generic_dispatches: usize,
}

/// Descriptor check of Guard 4 (`FnDefGhostTokenGuard`).
pub fn check_fndef_ghost_token_coercion(
    desc: &GhostTokenUsageDescriptor,
) -> Result<(), PeerSoundnessGuardViolation> {
    use PeerViolationReason as R;
    if desc.fn_def_value_coercions > 0 {
        return Err(descriptor_violation(R::FnDefValueCoercion));
    }
    if desc.call_sites_in_repeating_context > 0 {
        return Err(descriptor_violation(R::MintInRepeatingContext));
    }
    if desc.call_sites_outside_main > 0 {
        return Err(descriptor_violation(R::MintOutsideMain));
    }
    if desc.call_sites > 1 {
        return Err(descriptor_violation(R::MultipleMintSites));
    }
    if desc.call_sites > 0 && desc.main_reentrant {
        return Err(descriptor_violation(R::ReentrantMain));
    }
    if desc.generic_dispatches > 0 {
        return Err(descriptor_violation(R::GenericConstructorDispatch));
    }
    Ok(())
}

const MAX_GHOST_CTORS: usize = 16;
const MAX_GHOST_ALIASES: usize = 32;

struct GhostTables<'a> {
    /// `(type, method)`; the type is empty for a free constructor function.
    ctors: PairTable<'a, MAX_GHOST_CTORS>,
    /// `(alias, target)` type aliases of constructor types.
    type_aliases: PairTable<'a, MAX_GHOST_ALIASES>,
    /// Bare names bound directly to a constructor function.
    fn_aliases: PairTable<'a, MAX_GHOST_ALIASES>,
}

impl<'a> GhostTables<'a> {
    fn canonical(&self, mut name: &'a str) -> &'a str {
        for _ in 0..=self.type_aliases.len {
            match self
                .type_aliases
                .entries()
                .iter()
                .find(|&&(a, _)| a == name)
            {
                Some(&(_, b)) => name = b,
                None => break,
            }
        }
        name
    }

    fn is_ctor_type(&self, name: &'a str) -> bool {
        let c = self.canonical(name);
        self.ctors
            .entries()
            .iter()
            .any(|&(t, _)| !t.is_empty() && self.canonical(t) == c)
    }

    fn is_ctor_method(&self, ty: &'a str, m: &str) -> bool {
        let c = self.canonical(ty);
        self.ctors
            .entries()
            .iter()
            .any(|&(t, mm)| !t.is_empty() && mm == m && self.canonical(t) == c)
    }

    fn any_ctor_method(&self, m: &str) -> bool {
        self.ctors
            .entries()
            .iter()
            .any(|&(t, mm)| !t.is_empty() && mm == m)
    }

    fn is_free_ctor(&self, name: &str) -> bool {
        self.fn_aliases.contains_first(name)
            || self
                .ctors
                .entries()
                .iter()
                .any(|&(t, m)| t.is_empty() && m == name)
    }

    fn record_use(
        &mut self,
        owner: Option<&'a str>,
        item: &'a str,
        alias: &'a str,
        offset: usize,
    ) -> Result<bool, PeerScanError> {
        let mut changed = false;
        if let Some(o) = owner {
            if self.is_ctor_method(o, item) {
                changed |= self.fn_aliases.push(alias, "", offset)?;
            }
        }
        if alias != item && alias != "_" {
            if self.is_free_ctor(item) {
                changed |= self.fn_aliases.push(alias, "", offset)?;
            }
            if self.is_ctor_type(item) {
                changed |= self.type_aliases.push(alias, item, offset)?;
            }
        }
        Ok(changed)
    }

    fn glob_import(&mut self, owner: &'a str, offset: usize) -> Result<bool, PeerScanError> {
        let mut changed = false;
        let mut i = 0;
        while i < self.ctors.len {
            let (t, m) = self.ctors.items[i];
            if !t.is_empty() && self.canonical(t) == self.canonical(owner) {
                changed |= self.fn_aliases.push(m, "", offset)?;
            }
            i += 1;
        }
        Ok(changed)
    }
}

fn parse_use_tree<'a>(
    lx: &mut Lexer<'a>,
    tables: &mut GhostTables<'a>,
    owner: Option<&'a str>,
    depth: usize,
    changed: &mut bool,
) -> GResult<()> {
    if depth > MAX_META_DEPTH {
        return Err(PeerScanError::new(PeerScanErrorKind::NestingTooDeep, lx.pos).into());
    }
    let mut prev: Option<&'a str> = owner;
    let mut cur: Option<&'a str> = None;
    loop {
        let Some(t) = lx.peek()? else { return Ok(()) };
        if t.is_punct("::") {
            lx.next()?;
            continue;
        }
        if t.is_punct("{") {
            lx.next()?;
            let group_owner = cur.or(prev);
            loop {
                let Some(n) = lx.peek()? else {
                    return Err(PeerScanError::new(
                        PeerScanErrorKind::UnbalancedDelimiter,
                        t.start,
                    )
                    .into());
                };
                if n.is_punct("}") {
                    lx.next()?;
                    return Ok(());
                }
                if n.is_punct(",") {
                    lx.next()?;
                    continue;
                }
                let before = lx.pos;
                parse_use_tree(lx, tables, group_owner, depth + 1, changed)?;
                if lx.pos == before {
                    lx.next()?;
                }
            }
        }
        if t.is_punct("*") {
            lx.next()?;
            if let Some(o) = cur.or(prev) {
                *changed |= tables.glob_import(o, t.start)?;
            }
            return Ok(());
        }
        if t.is_ident() {
            lx.next()?;
            if t.text == "self" && !t.raw {
                if cur.is_none() {
                    cur = prev;
                    prev = None;
                }
            } else {
                if cur.is_some() {
                    prev = cur;
                }
                cur = Some(t.text);
            }
            if lx.next_is_punct("::")? {
                continue;
            }
            let Some(item) = cur else { return Ok(()) };
            let mut alias = item;
            if lx.next_is_kw("as")? {
                lx.next()?;
                if let Some(a) = lx.next()? {
                    alias = a.text;
                }
            }
            *changed |= tables.record_use(prev, item, alias, t.start)?;
            return Ok(());
        }
        return Ok(());
    }
}

fn collect_ghost_ctors<'a>(src: &'a str, tables: &mut GhostTables<'a>) -> GResult<()> {
    let mut lx = Lexer::new(src, SourceDialect::Rust);
    let mut st = DelimStack::new();
    let mut pending_ctor = false;
    let mut in_impl_header = false;
    let mut impl_pending: Option<&'a str> = None;
    let mut impl_scope: Option<(&'a str, usize)> = None;
    while let Some(t) = lx.next()? {
        if t.is_punct("#") {
            if let Some((_, content)) = take_attribute(&mut lx)? {
                if classify_attribute(content, &mut NoClauses)?.ghost_token_ctor {
                    pending_ctor = true;
                }
                continue;
            }
        }
        if t.is_open() {
            st.feed(&t)?;
            if t.is_punct("{") {
                if in_impl_header {
                    impl_scope = impl_pending.map(|n| (n, st.depth()));
                    in_impl_header = false;
                    impl_pending = None;
                }
                pending_ctor = false;
            }
            continue;
        }
        if t.is_close() {
            st.feed(&t)?;
            if matches!(impl_scope, Some((_, d)) if st.depth() < d) {
                impl_scope = None;
            }
            if t.is_punct("}") {
                pending_ctor = false;
            }
            continue;
        }
        if t.is_punct(";") {
            pending_ctor = false;
            in_impl_header = false;
            impl_pending = None;
            continue;
        }
        if t.is_kw("impl") {
            in_impl_header = true;
            impl_pending = parse_impl_header(lx)?.map(|h| h.self_ty);
        } else if t.is_kw("fn") {
            if let Some(name) = lx.peek()? {
                if name.is_ident() && pending_ctor {
                    let owner = impl_scope.map_or("", |(n, _)| n);
                    tables.ctors.push(owner, name.text, name.start)?;
                }
            }
            pending_ctor = false;
        }
    }
    st.finish(src.len())?;
    Ok(())
}

fn collect_ghost_aliases<'a>(src: &'a str, tables: &mut GhostTables<'a>) -> GResult<bool> {
    let mut lx = Lexer::new(src, SourceDialect::Rust);
    let mut changed = false;
    while let Some(t) = lx.next()? {
        if t.is_punct("#") {
            take_attribute(&mut lx)?;
            continue;
        }
        if t.is_kw("use") {
            parse_use_tree(&mut lx, tables, None, 0, &mut changed)?;
        } else if t.is_kw("type") {
            let mut c = lx;
            let Some(alias) = c.next()? else { continue };
            if !alias.is_ident() {
                continue;
            }
            if c.next_is_punct("<")? {
                let lt = c.next()?;
                let at = lt.map_or(c.pos, |x| x.start);
                skip_angles(&mut c, at)?;
            }
            if !c.eat_punct("=")? {
                continue;
            }
            let start = c.pos;
            let mut end = c.end;
            while let Some(n) = c.next()? {
                if n.is_punct(";") {
                    end = n.start;
                    break;
                }
            }
            if let Some(target) = path_last_ident(lx.range(start, end))? {
                if alias.text != target && tables.is_ctor_type(target) {
                    changed |= tables.type_aliases.push(alias.text, target, alias.start)?;
                }
            }
        }
    }
    Ok(changed)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum CtxKind {
    FnMain,
    FnOther,
    Repeat,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum CtxPhase {
    /// Skipping a `for <pat> in` or `while let <pat> =` pattern before `Header`.
    WaitFor(&'static str),
    /// Waiting for the body `{` at `depth` (the header itself counts).
    Header,
    /// Inside a braced body opened at `depth`.
    Body,
    /// An expression-bodied closure: ends at `,` / `;` at `depth`.
    Expr,
}

#[derive(Clone, Copy, Debug)]
struct Ctx {
    kind: CtxKind,
    phase: CtxPhase,
    depth: usize,
    /// Whether `}` followed immediately by `{` transitions back to `Header`
    /// (for `while { cond } { body }` and `for _ in { iter } { body }`).
    allow_cond_block: bool,
}

const MAX_CTX: usize = 128;

struct CtxStack {
    items: [Ctx; MAX_CTX],
    len: usize,
}

impl CtxStack {
    const fn new() -> Self {
        Self {
            items: [Ctx {
                kind: CtxKind::FnOther,
                phase: CtxPhase::Body,
                depth: 0,
                allow_cond_block: false,
            }; MAX_CTX],
            len: 0,
        }
    }

    fn push(
        &mut self,
        kind: CtxKind,
        phase: CtxPhase,
        depth: usize,
        allow_cond_block: bool,
        at: usize,
    ) -> Result<(), PeerScanError> {
        if self.len == MAX_CTX {
            return Err(PeerScanError::new(PeerScanErrorKind::NestingTooDeep, at));
        }
        self.items[self.len] = Ctx {
            kind,
            phase,
            depth,
            allow_cond_block,
        };
        self.len += 1;
        Ok(())
    }

    fn top(&self) -> Option<Ctx> {
        if self.len == 0 {
            None
        } else {
            Some(self.items[self.len - 1])
        }
    }

    /// A `{` opened at `depth_before`.
    fn on_open_brace(&mut self, depth_before: usize) {
        if let Some(top) = self.top() {
            if top.phase == CtxPhase::Header && top.depth == depth_before {
                self.items[self.len - 1].phase = CtxPhase::Body;
            }
        }
    }

    /// Transitions `WaitFor(target)` to `Header` when `target` is seen at `depth`.
    fn on_token(&mut self, depth: usize, tok: &Tok<'_>) {
        if let Some(top) = self.top() {
            if let CtxPhase::WaitFor(target) = top.phase {
                if top.depth == depth
                    && ((tok.kind == TokKind::Ident && !tok.raw && tok.text == target)
                        || (tok.kind == TokKind::Punct && tok.text == target))
                {
                    self.items[self.len - 1].phase = CtxPhase::Header;
                }
            }
        }
    }

    /// Delimiter depth dropped to `depth_after`.
    fn on_close(&mut self, depth_after: usize, next_is_lbrace: bool) {
        while let Some(top) = self.top() {
            if top.phase == CtxPhase::Body
                && depth_after == top.depth
                && top.allow_cond_block
                && next_is_lbrace
            {
                self.items[self.len - 1].phase = CtxPhase::Header;
                self.items[self.len - 1].allow_cond_block = false;
                break;
            }
            let closed = match top.phase {
                CtxPhase::Body => depth_after <= top.depth,
                CtxPhase::Expr | CtxPhase::Header | CtxPhase::WaitFor(_) => depth_after < top.depth,
            };
            if !closed {
                break;
            }
            self.len -= 1;
        }
    }

    /// `,` or `;` at `depth`.
    fn on_separator(&mut self, depth: usize, semicolon: bool) {
        while let Some(top) = self.top() {
            let ends = top.depth == depth
                && (top.phase == CtxPhase::Expr
                    || (semicolon && top.phase == CtxPhase::Header && top.kind != CtxKind::Repeat));
            if !ends {
                break;
            }
            self.len -= 1;
        }
    }

    fn in_repeat(&self) -> bool {
        self.items[..self.len]
            .iter()
            .any(|c| c.kind == CtxKind::Repeat)
    }

    fn innermost_fn(&self) -> Option<CtxKind> {
        self.items[..self.len]
            .iter()
            .rev()
            .find(|c| c.kind != CtxKind::Repeat && c.phase == CtxPhase::Body)
            .map(|c| c.kind)
    }
}

fn starts_expression(prev: Option<Tok<'_>>) -> bool {
    match prev {
        None => true,
        Some(p) => {
            (p.kind == TokKind::Punct
                && matches!(
                    p.text,
                    "(" | "[" | "{" | "," | ";" | "=" | "=>" | ":" | "+=" | "!" | "&" | "&&" | "*"
                ))
                || p.is_kw("move")
                || p.is_kw("async")
                || p.is_kw("return")
                || p.is_kw("break")
                || p.is_kw("in")
        }
    }
}

/// Source scanner of Guard 4 over Rust source. `ctor_paths` names the
/// ghost-token constructors (`"Tokens::new"`, or a free function `"mint"`);
/// functions annotated `#[ghost_token_ctor]` (also under `cfg_attr`) are added.
pub fn check_fndef_ghost_token_coercion_source<'a>(
    src: &'a str,
    ctor_paths: &[&'a str],
) -> GResult<()> {
    let mut tables = GhostTables {
        ctors: PairTable::new(),
        type_aliases: PairTable::new(),
        fn_aliases: PairTable::new(),
    };
    for path in ctor_paths {
        let (ty, m) = match path.rsplit_once("::") {
            Some((ty, m)) => (ty.rsplit("::").next().unwrap_or(ty), m),
            None => ("", *path),
        };
        tables.ctors.push(ty, m, 0)?;
    }
    collect_ghost_ctors(src, &mut tables)?;
    for _ in 0..MAX_GHOST_ALIASES {
        if !collect_ghost_aliases(src, &mut tables)? {
            break;
        }
    }
    check_ghost_references(src, &tables)
}

/// Standard non-minting container types whose `Container::<Tokens>::...`
/// turbofish does not invoke a trait constructor on `Tokens`.
const SAFE_GENERIC_CONTAINERS: [&str; 22] = [
    "Vec",
    "Option",
    "Result",
    "Box",
    "PhantomData",
    "MaybeUninit",
    "ManuallyDrop",
    "Cell",
    "RefCell",
    "UnsafeCell",
    "Arc",
    "Rc",
    "Mutex",
    "RwLock",
    "Pin",
    "NonNull",
    "BTreeMap",
    "HashMap",
    "VecDeque",
    "LinkedList",
    "BinaryHeap",
    "HashSet",
];

/// Pure metadata/drop intrinsics whose turbofish `size_of::<Tokens>()` never
/// mints a value of `Tokens`.
const SAFE_GENERIC_INTRINSICS: [&str; 7] = [
    "size_of",
    "align_of",
    "needs_drop",
    "type_name",
    "type_id",
    "drop",
    "forget",
];

/// Collects names of generic functions (`fn mk<T: ...>(...) { T::new() }`)
/// whose body invokes a ghost-token constructor method on a generic type
/// parameter `T` (so even type-inferred `let t: Tokens = mk();` is caught).
fn collect_generic_mint_fns<'a>(
    src: &'a str,
    tables: &GhostTables<'a>,
) -> GResult<PairTable<'a, MAX_GHOST_ALIASES>> {
    let mut out: PairTable<'a, MAX_GHOST_ALIASES> = PairTable::new();
    let mut lx = Lexer::new(src, SourceDialect::Rust);
    let mut st = DelimStack::new();
    // Type parameters of the enclosing `impl<..>` / `trait` block, with the
    // depth of its body.
    let mut impl_params: PairTable<'a, 16> = PairTable::new();
    let mut impl_params_pending = false;
    let mut impl_depth: Option<usize> = None;
    while let Some(t) = lx.next()? {
        if t.is_punct("#") {
            take_attribute(&mut lx)?;
            continue;
        }
        if t.is_open() {
            st.feed(&t)?;
            if t.is_punct("{") && impl_params_pending {
                impl_depth = Some(st.depth());
                impl_params_pending = false;
            }
            continue;
        }
        if t.is_close() {
            st.feed(&t)?;
            if matches!(impl_depth, Some(d) if st.depth() < d) {
                impl_depth = None;
                impl_params = PairTable::new();
            }
            continue;
        }
        if t.is_kw("impl") && impl_depth.is_none() {
            impl_params = PairTable::new();
            if lx.next_is_punct("<")? {
                let mut c = lx;
                let lt = c.next()?;
                let at = lt.map_or(c.pos, |x| x.start);
                let gen_start = c.pos;
                skip_angles(&mut c, at)?;
                let mut parts = TopSplit::new(lx.range(gen_start, c.pos.saturating_sub(1)), true);
                while let Some(mut p) = parts.next_part()? {
                    if let Some(tok) = p.next()? {
                        if tok.is_ident() && !tok.is_kw("const") {
                            impl_params.push(tok.text, "", tok.start)?;
                        }
                    }
                }
            }
            impl_params_pending = impl_params.len > 0;
            continue;
        }
        if !t.is_kw("fn") {
            continue;
        }
        let mut c = lx;
        let Some(name) = c.next()? else { continue };
        if !name.is_ident() {
            continue;
        }
        // Generic type parameter identifiers (`<T: Mint, U>`), plus those of an
        // enclosing generic `impl`.
        let mut tparams: PairTable<'a, 16> = PairTable::new();
        if impl_depth.is_some() {
            for &(p, _) in impl_params.entries() {
                tparams.push(p, "", name.start)?;
            }
        }
        if c.next_is_punct("<")? {
            let lt = c.next()?;
            let at = lt.map_or(c.pos, |x| x.start);
            let gen_start = c.pos;
            skip_angles(&mut c, at)?;
            let gen_end = c.pos.saturating_sub(1);
            let mut parts = TopSplit::new(lx.range(gen_start, gen_end), true);
            while let Some(mut p) = parts.next_part()? {
                if let Some(tok) = p.next()? {
                    if tok.is_ident() && !tok.is_kw("const") {
                        tparams.push(tok.text, "", tok.start)?;
                    }
                }
            }
        }
        if tparams.len == 0 {
            continue;
        }
        let Some(sig) = scan_fn_signature(lx, false)? else {
            continue;
        };
        let mut bc = sig.rest;
        let Some(open) = bc.next()? else { continue };
        if !open.is_punct("{") {
            continue;
        }
        let s = bc.pos;
        let close = skip_group(&mut bc, &open)?;
        let mut body = lx.range(s, close);
        while let Some(n) = body.next()? {
            if n.is_ident() && tparams.contains_first(n.text) {
                let mut p = body;
                if p.eat_punct("::")? {
                    if let Some(m) = p.next()? {
                        if m.is_ident() && tables.any_ctor_method(m.text) {
                            out.push(name.text, "", name.start)?;
                            break;
                        }
                    }
                }
            } else if n.is_punct("<") {
                let mut p = body;
                if let Some(ty) = p.next()? {
                    if ty.is_ident() && tparams.contains_first(ty.text) {
                        skip_angles(&mut p, n.start)?;
                        if p.eat_punct("::")? {
                            if let Some(m) = p.next()? {
                                if m.is_ident() && tables.any_ctor_method(m.text) {
                                    out.push(name.text, "", name.start)?;
                                    break;
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    Ok(out)
}

fn check_ghost_references<'a>(src: &'a str, tables: &GhostTables<'a>) -> GResult<()> {
    let generic_mint_fns = collect_generic_mint_fns(src, tables)?;
    let mut lx = Lexer::new(src, SourceDialect::Rust);
    let mut st = DelimStack::new();
    let mut ctx = CtxStack::new();
    let mut prev: Option<Tok<'a>> = None;
    let mut in_impl_header = false;
    let mut impl_pending: Option<&'a str> = None;
    let mut impl_scope: Option<(&'a str, usize)> = None;
    let mut mint_sites = 0usize;
    let mut main_mints = 0usize;
    let mut main_ref: Option<usize> = None;
    let mut saw_ctor_type_in_fn = false;
    let mut pending_generic_call: Option<usize> = None;
    while let Some(t) = lx.next()? {
        if t.is_punct("#") {
            if take_attribute(&mut lx)?.is_some() {
                continue;
            }
        }
        if t.is_kw("use") || (t.is_kw("type") && matches!(lx.peek()?, Some(n) if n.is_ident())) {
            // Skip the item, but notice any aliasing of `main`.
            while let Some(n) = lx.next()? {
                if n.is_ident() && n.text == "main" {
                    main_ref = main_ref.or(Some(n.start));
                }
                if n.is_punct(";") {
                    break;
                }
                if n.is_open() {
                    let mut inner = lx;
                    let close = skip_group(&mut inner, &n)?;
                    let mut scan = lx.range(lx.pos, close);
                    while let Some(m) = scan.next()? {
                        if m.is_ident() && m.text == "main" {
                            main_ref = main_ref.or(Some(m.start));
                        }
                    }
                    lx = inner;
                }
            }
            prev = None;
            continue;
        }
        if t.is_open() {
            let before = st.depth();
            st.feed(&t)?;
            if t.is_punct("{") {
                ctx.on_open_brace(before);
                if in_impl_header {
                    impl_scope = impl_pending.map(|n| (n, st.depth()));
                    in_impl_header = false;
                    impl_pending = None;
                }
            }
            prev = Some(t);
            continue;
        }
        if t.is_close() {
            st.feed(&t)?;
            let next_lbrace = t.is_punct("}") && lx.next_is_punct("{")?;
            let had_fn = ctx.innermost_fn().is_some();
            ctx.on_close(st.depth(), next_lbrace);
            if had_fn && ctx.innermost_fn().is_none() {
                if saw_ctor_type_in_fn {
                    if let Some(at) = pending_generic_call {
                        return violation(PeerViolationReason::GenericConstructorDispatch, at);
                    }
                }
                saw_ctor_type_in_fn = false;
                pending_generic_call = None;
            }
            if matches!(impl_scope, Some((_, d)) if st.depth() < d) {
                impl_scope = None;
            }
            prev = Some(t);
            continue;
        }
        ctx.on_token(st.depth(), &t);
        if t.is_punct(",") || t.is_punct(";") {
            ctx.on_separator(st.depth(), t.is_punct(";"));
            if t.is_punct(";") {
                in_impl_header = false;
                impl_pending = None;
            }
            prev = Some(t);
            continue;
        }
        // Closures.
        if (t.is_punct("|") || t.is_punct("||")) && starts_expression(prev) {
            if t.is_punct("|") {
                let mut pst = DelimStack::new();
                loop {
                    let Some(p) = lx.next()? else {
                        return Err(PeerScanError::new(
                            PeerScanErrorKind::UnbalancedDelimiter,
                            t.start,
                        )
                        .into());
                    };
                    if p.is_punct("|") && pst.depth() == 0 {
                        break;
                    }
                    pst.feed(&p)?;
                }
            }
            if lx.next_is_punct("->")? {
                lx.next()?;
                while let Some(n) = lx.peek()? {
                    if n.is_punct("{") {
                        break;
                    }
                    lx.next()?;
                    if n.is_open() {
                        skip_group(&mut lx, &n)?;
                    }
                }
            }
            let phase = if lx.next_is_punct("{")? {
                CtxPhase::Header
            } else {
                CtxPhase::Expr
            };
            ctx.push(CtxKind::Repeat, phase, st.depth(), false, t.start)?;
            prev = Some(t);
            continue;
        }
        if t.is_ident() && !t.raw {
            match t.text {
                "fn" => {
                    if let Some(name) = lx.peek()? {
                        if name.is_ident() {
                            lx.next()?;
                            let kind = if name.text == "main" && st.depth() == 0 {
                                CtxKind::FnMain
                            } else {
                                CtxKind::FnOther
                            };
                            ctx.push(kind, CtxPhase::Header, st.depth(), false, t.start)?;
                            prev = Some(name);
                            continue;
                        }
                    }
                }
                "loop" => {
                    ctx.push(
                        CtxKind::Repeat,
                        CtxPhase::Header,
                        st.depth(),
                        false,
                        t.start,
                    )?;
                }
                "while" => {
                    let phase = if lx.next_is_kw("let")? {
                        CtxPhase::WaitFor("=")
                    } else {
                        CtxPhase::Header
                    };
                    ctx.push(CtxKind::Repeat, phase, st.depth(), true, t.start)?;
                }
                "for" => {
                    if !in_impl_header && !lx.next_is_punct("<")? {
                        ctx.push(
                            CtxKind::Repeat,
                            CtxPhase::WaitFor("in"),
                            st.depth(),
                            true,
                            t.start,
                        )?;
                    }
                }
                "async" => {
                    let mut c = lx;
                    if c.next_is_kw("move")? {
                        c.next()?;
                    }
                    if c.next_is_punct("{")? {
                        ctx.push(
                            CtxKind::Repeat,
                            CtxPhase::Header,
                            st.depth(),
                            false,
                            t.start,
                        )?;
                    }
                }
                "impl" => {
                    in_impl_header = true;
                    impl_pending = parse_impl_header(lx)?.map(|h| h.self_ty);
                }
                "main" => {
                    if !matches!(prev, Some(p) if p.is_punct(".")) {
                        main_ref = main_ref.or(Some(t.start));
                    }
                }
                _ => {}
            }
        }
        if t.is_ident() && tables.is_ctor_type(t.text) && ctx.innermost_fn().is_some() {
            saw_ctor_type_in_fn = true;
        }
        // Calling or coercing a locally defined generic constructor dispatcher
        // (`fn mk<T: Mint>() -> T { T::new() }`) inside a function that mentions
        // `Tokens` (e.g. type-inferred `let a: Tokens = mk();`) can mint it.
        if t.is_ident()
            && generic_mint_fns.contains_first(t.text)
            && !matches!(prev, Some(p) if p.is_kw("fn"))
            && ctx.innermost_fn().is_some()
        {
            pending_generic_call = pending_generic_call.or(Some(t.start));
        }
        // A constructor type passed as a turbofish argument of a call, fn-value
        // coercion (`let f = mk::<Tokens>;`), or non-container helper
        // (`Helper::<Tokens>::mk()`) lets a generic body (`T::new()`) mint it.
        if t.is_ident()
            && !tables.is_ctor_type(t.text)
            && !t.is_kw("Self")
            && !SAFE_GENERIC_INTRINSICS.contains(&t.text)
        {
            let mut c = lx;
            if c.eat_punct("::")? && c.next_is_punct("<")? {
                let args_start = c.pos;
                let lt = c.next()?;
                let at = lt.map_or(c.pos, |x| x.start);
                skip_angles(&mut c, at)?;
                let is_safe_container_path =
                    SAFE_GENERIC_CONTAINERS.contains(&t.text) && c.next_is_punct("::")?;
                if !is_safe_container_path {
                    let mut a = lx.range(args_start, c.pos);
                    while let Some(n) = a.next()? {
                        if n.is_ident() && tables.is_ctor_type(n.text) {
                            return violation(
                                PeerViolationReason::GenericConstructorDispatch,
                                n.start,
                            );
                        }
                    }
                }
            }
        }
        // Constructor references.
        let mut reference: Option<(usize, Lexer<'a>)> = None;
        if t.is_ident() && (tables.is_ctor_type(t.text) || t.is_kw("Self")) {
            let mut c = lx;
            if c.eat_punct("::")? {
                if c.next_is_punct("<")? {
                    let lt = c.next()?;
                    let at = lt.map_or(c.pos, |x| x.start);
                    skip_angles(&mut c, at)?;
                    if !c.eat_punct("::")? {
                        c = lx;
                    }
                }
                if let Some(m) = c.next()? {
                    if m.is_ident() {
                        let is_ref = if t.is_kw("Self") {
                            match impl_scope {
                                Some((ty, _)) => tables.is_ctor_method(ty, m.text),
                                None => tables.any_ctor_method(m.text),
                            }
                        } else {
                            tables.is_ctor_method(t.text, m.text)
                        };
                        if is_ref {
                            reference = Some((t.start, c));
                        }
                    }
                }
            }
        } else if t.is_punct("<")
            && !matches!(prev, Some(p) if p.is_punct("::") || p.is_ident() || p.is_punct(">"))
        {
            let mut c = lx;
            let mut angle = 1usize;
            let mut ty: Option<&'a str> = None;
            let mut seen_as = false;
            let mut closed = false;
            while let Some(n) = c.next()? {
                if n.is_punct(";") || n.is_punct("{") || n.is_punct("}") {
                    break;
                }
                if n.is_punct("<") {
                    angle += 1;
                } else if n.is_punct(">") {
                    angle -= 1;
                    if angle == 0 {
                        closed = true;
                        break;
                    }
                } else if n.is_open() {
                    skip_group(&mut c, &n)?;
                } else if angle == 1 && n.is_kw("as") {
                    seen_as = true;
                } else if angle == 1 && !seen_as && n.is_ident() && !n.is_kw("dyn") {
                    ty = Some(n.text);
                }
            }
            if let (true, Some(ty)) = (closed, ty) {
                let is_self = ty == "Self";
                if (is_self || tables.is_ctor_type(ty)) && c.eat_punct("::")? {
                    if let Some(m) = c.next()? {
                        let is_ref = if is_self {
                            m.is_ident()
                                && match impl_scope {
                                    Some((scope_ty, _)) => tables.is_ctor_method(scope_ty, m.text),
                                    None => tables.any_ctor_method(m.text),
                                }
                        } else {
                            m.is_ident() && tables.is_ctor_method(ty, m.text)
                        };
                        if is_ref {
                            reference = Some((t.start, c));
                        }
                    }
                }
            }
        } else if t.is_ident()
            && tables.is_free_ctor(t.text)
            && !matches!(prev, Some(p) if p.is_punct(".") || p.is_kw("fn") || p.is_kw("let"))
            && !lx.next_is_punct("!")?
            && !lx.next_is_punct(":")?
        {
            reference = Some((t.start, lx));
        }
        if let Some((at, after)) = reference {
            let mut c = after;
            {
                let mut probe = c;
                if probe.eat_punct("::")? && probe.next_is_punct("<")? {
                    let lt = probe.next()?;
                    let at = lt.map_or(probe.pos, |x| x.start);
                    skip_angles(&mut probe, at)?;
                    c = probe;
                }
            }
            if !c.next_is_punct("(")? {
                return violation(PeerViolationReason::FnDefValueCoercion, at);
            }
            if ctx.in_repeat() {
                return violation(PeerViolationReason::MintInRepeatingContext, at);
            }
            if ctx.innermost_fn() != Some(CtxKind::FnMain) {
                return violation(PeerViolationReason::MintOutsideMain, at);
            }
            mint_sites += 1;
            if mint_sites > 1 {
                return violation(PeerViolationReason::MultipleMintSites, at);
            }
            main_mints += 1;
            lx = c;
        }
        prev = Some(t);
    }
    st.finish(src.len())?;
    if main_mints > 0 {
        if let Some(at) = main_ref {
            return violation(PeerViolationReason::ReentrantMain, at);
        }
    }
    Ok(())
}

// ----------------------------------------------------------------------------
// Guard 5 — external-type `Drop` omission (`verus#3514`)
// ----------------------------------------------------------------------------

/// Declared shape of an external type specification
/// (`ExternalTypeDropSpec` in Lean).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub struct ExternalTypeDropDescriptor {
    /// `external_type_specification` is present (also under `cfg_attr`).
    pub external_type_specification: bool,
    /// `external_body` is present (also under `cfg_attr`).
    pub external_body: bool,
    /// The type has a `Drop` impl (or `has_drop_impl` is declared).
    pub has_drop_impl: bool,
    /// Some field is opaque (may carry drop glue).
    pub opaque_foreign_field: bool,
    /// An unconditional `models_drop` is present.
    pub models_drop: bool,
    /// An unconditional `no_drop_glue` is present.
    pub no_drop_glue: bool,
}

impl ExternalTypeDropDescriptor {
    /// A `Drop` effect may exist.
    pub const fn drop_may_exist(&self) -> bool {
        self.has_drop_impl || (self.opaque_foreign_field && !self.no_drop_glue)
    }
}

/// Descriptor check of Guard 5 (`ExternalTypeDropGuard`).
pub fn check_external_type_drop_omission(
    desc: &ExternalTypeDropDescriptor,
) -> Result<(), PeerSoundnessGuardViolation> {
    use PeerViolationReason as R;
    if !desc.external_type_specification {
        return Ok(());
    }
    if desc.external_body && desc.drop_may_exist() {
        return Err(descriptor_violation(R::ExternalBodyWithDrop));
    }
    if desc.has_drop_impl && desc.no_drop_glue {
        return Err(descriptor_violation(R::ContradictoryDropDeclaration));
    }
    if desc.has_drop_impl && !desc.models_drop {
        return Err(descriptor_violation(R::UnmodeledDropImpl));
    }
    if desc.opaque_foreign_field && !(desc.models_drop || desc.no_drop_glue) {
        return Err(descriptor_violation(R::UnmodeledOpaqueField));
    }
    Ok(())
}

const MAX_DROP_TYPES: usize = 32;

/// Source scanner of Guard 5 over Rust source.
pub fn check_external_type_drop_omission_source(src: &str) -> GResult<()> {
    let mut drops: PairTable<'_, MAX_DROP_TYPES> = PairTable::new();
    {
        let mut lx = Lexer::new(src, SourceDialect::Rust);
        while let Some(t) = lx.next()? {
            if t.is_kw("impl") {
                if let Some(h) = parse_impl_header(lx)? {
                    if h.trait_last == Some("Drop") {
                        drops.push(h.self_ty, "", t.start)?;
                    }
                }
            }
        }
    }
    let mut lx = Lexer::new(src, SourceDialect::Rust);
    let mut st = DelimStack::new();
    let mut pending = AttrFlags::default();
    while let Some(t) = lx.next()? {
        if t.is_punct("#") {
            if let Some((inner, content)) = take_attribute(&mut lx)? {
                if !inner {
                    pending.merge(classify_attribute(content, &mut NoClauses)?);
                }
                continue;
            }
        }
        if t.is_open() || t.is_close() {
            st.feed(&t)?;
            if !t.is_punct("(") && !t.is_punct(")") {
                pending = AttrFlags::default();
            }
            continue;
        }
        if t.is_punct(";") {
            pending = AttrFlags::default();
            continue;
        }
        if t.is_kw("struct") || t.is_kw("enum") || t.is_kw("union") {
            let flags = pending;
            pending = AttrFlags::default();
            if !flags.external_type_spec {
                continue;
            }
            let Some(item) = parse_struct_item(lx)? else {
                continue;
            };
            let mut opaque = false;
            let mut field_drop = false;
            if let Some(body) = item.body {
                if t.is_kw("enum") {
                    let mut c = body;
                    while let Some(n) = c.next()? {
                        if n.is_punct("#") {
                            if take_attribute(&mut c)?.is_some() {
                                continue;
                            }
                        }
                        if n.is_punct("(") || n.is_punct("{") {
                            opaque = true;
                            let s = c.pos;
                            let close = skip_group(&mut c, &n)?;
                            for_each_field(body.range(s, close), n.is_punct("("), &mut |field| {
                                if !type_is_transparent(field.ty, &drops, 0)? {
                                    let mut f = field.ty;
                                    while let Some(tok) = f.next()? {
                                        if tok.is_ident() && drops.contains_first(tok.text) {
                                            field_drop = true;
                                        }
                                    }
                                }
                                Ok(())
                            })?;
                        }
                    }
                } else {
                    for_each_field(body, item.tuple, &mut |field| {
                        let transparent = type_is_transparent(field.ty, &drops, 0)?;
                        if !transparent {
                            opaque = true;
                            let mut c = field.ty;
                            while let Some(n) = c.next()? {
                                if n.is_ident() && drops.contains_first(n.text) {
                                    field_drop = true;
                                }
                            }
                        }
                        Ok(())
                    })?;
                }
            }
            let desc = ExternalTypeDropDescriptor {
                external_type_specification: true,
                external_body: flags.external_body,
                has_drop_impl: flags.has_drop_impl || drops.contains_first(item.name) || field_drop,
                opaque_foreign_field: opaque,
                models_drop: flags.models_drop,
                no_drop_glue: flags.no_drop_glue,
            };
            if let Err(v) = check_external_type_drop_omission(&desc) {
                return violation(v.reason, t.start);
            }
        }
    }
    st.finish(src.len())?;
    Ok(())
}

// ----------------------------------------------------------------------------
// Guard 6a — assumption polarity (`Verifrag`)
// ----------------------------------------------------------------------------

/// Root polarity of an analyzed proposition.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Polarity {
    /// A postcondition or theorem statement.
    Positive,
    /// A precondition or hypothesis.
    Negative,
}

/// Facts about the assumption atom's placements (`occursAt` in Lean).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub struct AssumptionPolarityDescriptor {
    /// Occurrences in positive polarity.
    pub positive: usize,
    /// Occurrences in negative polarity inside an antecedent's antecedent.
    pub negated_antecedent: usize,
    /// Occurrences under `iff`.
    pub iff: usize,
    /// Occurrences in an `if` condition.
    pub if_condition: usize,
    /// Occurrences inside Boolean leaves.
    pub unclean_leaf: usize,
}

/// Descriptor check of Guard 6a (`AssumptionPolarityGuard`): the assumption
/// atom may occur only in strictly negative polarity.
pub fn check_assumption_polarity(
    desc: &AssumptionPolarityDescriptor,
) -> Result<(), PeerSoundnessGuardViolation> {
    use PeerViolationReason as R;
    if desc.negated_antecedent > 0 {
        return Err(descriptor_violation(R::AssumptionNegatedAntecedent));
    }
    if desc.positive > 0 {
        return Err(descriptor_violation(R::AssumptionPositive));
    }
    if desc.iff > 0 {
        return Err(descriptor_violation(R::AssumptionInIff));
    }
    if desc.if_condition > 0 {
        return Err(descriptor_violation(R::AssumptionInIfCondition));
    }
    if desc.unclean_leaf > 0 {
        return Err(descriptor_violation(R::AssumptionUncleanLeaf));
    }
    Ok(())
}

/// Maximum `let`-alias inlining depth; deeper chains fail closed.
pub const MAX_LET_ALIAS_DEPTH: usize = 8;

const ASSUMPTION_ATOMS: [&str; 2] = ["assumes_hold", "assumesHold"];

const LEAN_BINDER_STOPS: [&str; 10] = [
    "if", "let", "fun", "λ", "match", "∀", "∃", "forall", "exists", "Π",
];

/// In Rust, `if cond { .. } else { .. }` has braced branches, so it never
/// absorbs a trailing top-level `==>` / `<==>` / `&&` / `||`.
const RUST_BINDER_STOPS: [&str; 9] = [
    "let", "fun", "λ", "match", "∀", "∃", "forall", "exists", "Π",
];

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Sign {
    Pos,
    Neg,
    Both(PeerViolationReason),
}

impl Sign {
    const fn flip(self) -> Self {
        match self {
            Self::Pos => Self::Neg,
            Self::Neg => Self::Pos,
            b => b,
        }
    }
}

#[derive(Clone, Copy, Debug)]
struct PCtx {
    sign: Sign,
    antecedent: bool,
    inline_depth: usize,
}

#[derive(Clone, Copy)]
struct AliasTable<'a> {
    names: [&'a str; MAX_LET_ALIAS_DEPTH],
    values: [Lexer<'a>; MAX_LET_ALIAS_DEPTH],
    len: usize,
}

struct PolarityAnalyzer<'a> {
    aliases: AliasTable<'a>,
}

impl<'a> PolarityAnalyzer<'a> {
    fn new(dialect: SourceDialect) -> Self {
        Self {
            aliases: AliasTable {
                names: [""; MAX_LET_ALIAS_DEPTH],
                values: [Lexer::new("", dialect); MAX_LET_ALIAS_DEPTH],
                len: 0,
            },
        }
    }

    fn lookup(&self, name: &str, limit: usize) -> Option<usize> {
        (0..core::cmp::min(limit, self.aliases.len))
            .rev()
            .find(|&i| self.aliases.names[i] == name)
    }

    fn mentions(&self, r: Lexer<'a>, limit: usize, depth: usize) -> GResult<Option<usize>> {
        if depth > MAX_LET_ALIAS_DEPTH {
            return Err(PeerScanError::new(PeerScanErrorKind::AliasDepthExceeded, r.pos).into());
        }
        let mut c = r;
        while let Some(t) = c.next()? {
            if !t.is_ident() {
                continue;
            }
            if ASSUMPTION_ATOMS.contains(&t.text) {
                return Ok(Some(t.start));
            }
            if let Some(i) = self.lookup(t.text, limit) {
                if self
                    .mentions(self.aliases.values[i], i, depth + 1)?
                    .is_some()
                {
                    return Ok(Some(t.start));
                }
            }
        }
        Ok(None)
    }

    fn occurrence(cx: PCtx, at: usize) -> GResult<()> {
        match cx.sign {
            Sign::Neg => Ok(()),
            Sign::Pos => violation(
                if cx.antecedent {
                    PeerViolationReason::AssumptionNegatedAntecedent
                } else {
                    PeerViolationReason::AssumptionPositive
                },
                at,
            ),
            Sign::Both(reason) => violation(reason, at),
        }
    }

    fn analyze(&mut self, r: Lexer<'a>, cx: PCtx) -> GResult<()> {
        let Some(first) = r.peek()? else {
            return Ok(());
        };
        if first.is_kw("let") {
            return self.analyze_let(r, cx);
        }
        let stops: &[&str] = match r.dialect {
            SourceDialect::Rust => &RUST_BINDER_STOPS,
            SourceDialect::Lean => &LEAN_BINDER_STOPS,
        };
        let iff: &[&str] = &["<==>", "↔", "<->", "iff"];
        let imp: &[&str] = match r.dialect {
            SourceDialect::Rust => &["==>"],
            SourceDialect::Lean => &["==>", "→", "->"],
        };
        let or: &[&str] = &["||", "∨"];
        let and: &[&str] = &["&&", "∧"];
        if let Some((l, rr, _)) = split_first_top(r, iff, stops)? {
            let both = PCtx {
                sign: Sign::Both(PeerViolationReason::AssumptionInIff),
                ..cx
            };
            self.analyze(l, both)?;
            return self.analyze(rr, both);
        }
        if let Some((l, rr, _)) = split_first_top(r, imp, stops)? {
            self.analyze(
                l,
                PCtx {
                    sign: cx.sign.flip(),
                    antecedent: true,
                    ..cx
                },
            )?;
            return self.analyze(rr, cx);
        }
        for ops in [or, and] {
            if let Some((l, rr, _)) = split_first_top(r, ops, stops)? {
                self.analyze(l, cx)?;
                return self.analyze(rr, cx);
            }
        }
        let mut c = r;
        c.next()?;
        if first.is_punct("!") || first.is_punct("¬") || first.is_kw("not") {
            return self.analyze(
                r.range(c.pos, r.end),
                PCtx {
                    sign: cx.sign.flip(),
                    ..cx
                },
            );
        }
        if first.is_kw("if") {
            return self.analyze_if(r, cx);
        }
        if first.is_punct("∀")
            || first.is_kw("forall")
            || first.is_kw("Π")
            || first.is_punct("∃")
            || first.is_kw("exists")
        {
            let universal = first.is_punct("∀") || first.is_kw("forall") || first.is_kw("Π");
            return self.analyze_quantifier(r.range(c.pos, r.end), cx, universal);
        }
        for open in ["(", "{", "⦃"] {
            if let Some(inner) = whole_group(r, open)? {
                if r.dialect == SourceDialect::Lean {
                    if let Some((lhs, ty, _)) = split_first_top(inner, &[":"], stops)? {
                        let mut lc = lhs;
                        let is_binder_name = match lc.next()? {
                            Some(n) if n.is_ident() && lc.is_empty()? => {
                                !ASSUMPTION_ATOMS.contains(&n.text)
                                    && self.lookup(n.text, self.aliases.len).is_none()
                            }
                            _ => false,
                        };
                        if is_binder_name {
                            return self.analyze(ty, cx);
                        }
                    }
                }
                return self.analyze(inner, cx);
            }
        }
        self.analyze_leaf(r, cx)
    }

    fn analyze_let(&mut self, r: Lexer<'a>, cx: PCtx) -> GResult<()> {
        let mut c = r;
        c.next()?;
        let mut name = c.next()?;
        if matches!(name, Some(n) if n.is_kw("mut")) {
            name = c.next()?;
        }
        let Some(name) = name.filter(|n| n.is_ident()) else {
            return self.analyze_leaf(r, cx);
        };
        let mut found_eq = false;
        while let Some(t) = c.next()? {
            if t.is_punct("=") || t.is_punct(":=") {
                found_eq = true;
                break;
            }
            if t.is_open() {
                skip_group(&mut c, &t)?;
            }
        }
        if !found_eq {
            return self.analyze_leaf(r, cx);
        }
        let value_start = c.pos;
        let mut value_end = r.end;
        let mut body_start = r.end;
        let mut prev_end = value_start;
        while let Some(t) = c.next()? {
            if t.is_punct(";") {
                value_end = t.start;
                body_start = t.end;
                break;
            }
            if r.dialect == SourceDialect::Lean
                && prev_end > value_start
                && r.src[prev_end..t.start].contains('\n')
            {
                value_end = t.start;
                body_start = t.start;
                break;
            }
            if t.is_open() {
                skip_group(&mut c, &t)?;
            }
            prev_end = c.pos;
        }
        let value = r.range(value_start, value_end);
        let body = r.range(body_start, r.end);
        if body.is_empty()? {
            return self.analyze_leaf(value, cx);
        }
        if self.aliases.len == MAX_LET_ALIAS_DEPTH {
            return Err(
                PeerScanError::new(PeerScanErrorKind::AliasDepthExceeded, name.start).into(),
            );
        }
        let saved = self.aliases;
        self.aliases.names[self.aliases.len] = name.text;
        self.aliases.values[self.aliases.len] = value;
        self.aliases.len += 1;
        let res = self.analyze(body, cx);
        self.aliases = saved;
        res
    }

    fn analyze_if(&mut self, r: Lexer<'a>, cx: PCtx) -> GResult<()> {
        let cond_cx = PCtx {
            sign: Sign::Both(PeerViolationReason::AssumptionInIfCondition),
            ..cx
        };
        let mut c = r;
        c.next()?;
        let cond_start = c.pos;
        match r.dialect {
            SourceDialect::Lean => {
                let mut then_tok = None;
                while let Some(t) = c.next()? {
                    if t.is_kw("then") {
                        then_tok = Some(t);
                        break;
                    }
                    if t.is_open() {
                        skip_group(&mut c, &t)?;
                    }
                }
                let Some(then_tok) = then_tok else {
                    return self.analyze_leaf(r, cx);
                };
                let mut nest = 0usize;
                let mut else_tok = None;
                while let Some(t) = c.next()? {
                    if t.is_kw("if") {
                        nest += 1;
                    } else if t.is_kw("else") {
                        if nest == 0 {
                            else_tok = Some(t);
                            break;
                        }
                        nest -= 1;
                    } else if t.is_open() {
                        skip_group(&mut c, &t)?;
                    }
                }
                let cond_r = r.range(cond_start, then_tok.start);
                let mut cond_scan = cond_r;
                let cond_expr = match cond_scan.next()? {
                    Some(n)
                        if n.is_ident()
                            && !ASSUMPTION_ATOMS.contains(&n.text)
                            && self.lookup(n.text, self.aliases.len).is_none()
                            && cond_scan.eat_punct(":")? =>
                    {
                        cond_r.range(cond_scan.pos, cond_r.end)
                    }
                    _ => cond_r,
                };
                self.analyze(cond_expr, cond_cx)?;
                match else_tok {
                    Some(e) => {
                        self.analyze(r.range(then_tok.end, e.start), cx)?;
                        self.analyze(r.range(e.end, r.end), cx)
                    }
                    None => self.analyze(r.range(then_tok.end, r.end), cx),
                }
            }
            SourceDialect::Rust => {
                let mut open = None;
                while let Some(t) = c.next()? {
                    if t.is_punct("{") {
                        open = Some(t);
                        break;
                    }
                    if t.is_open() {
                        skip_group(&mut c, &t)?;
                    }
                }
                let Some(open) = open else {
                    return self.analyze_leaf(r, cx);
                };
                let then_start = c.pos;
                let close = skip_group(&mut c, &open)?;
                self.analyze(r.range(cond_start, open.start), cond_cx)?;
                self.analyze(r.range(then_start, close), cx)?;
                if c.next_is_kw("else")? {
                    c.next()?;
                    self.analyze(r.range(c.pos, r.end), cx)
                } else {
                    self.analyze_leaf(r.range(c.pos, r.end), cx)
                }
            }
        }
    }

    fn analyze_quantifier(&mut self, r: Lexer<'a>, cx: PCtx, universal: bool) -> GResult<()> {
        let binder_cx = if universal {
            PCtx {
                sign: cx.sign.flip(),
                antecedent: true,
                ..cx
            }
        } else {
            cx
        };
        let mut c = r;
        if c.next_is_punct("|")? {
            let body = strip_closure_params(r)?;
            return self.analyze(body, cx);
        }
        let mut comma = None;
        while let Some(t) = c.next()? {
            if t.is_punct(",") {
                comma = Some(t);
                break;
            }
            if t.is_open() {
                skip_group(&mut c, &t)?;
            }
        }
        let Some(comma) = comma else {
            return self.analyze_leaf(r, cx);
        };
        let binders = r.range(r.pos, comma.start);
        // Binder groups `(h : T)`, `{h : T}`, `[C]`, `⦃h : T⦄`, or bare `h : T`.
        let mut b = binders;
        let mut saw_group = false;
        while let Some(t) = b.next()? {
            if t.is_open() {
                saw_group = true;
                let s = b.pos;
                let close = skip_group(&mut b, &t)?;
                self.analyze_binder(binders.range(s, close), binder_cx)?;
            }
        }
        if !saw_group {
            self.analyze_binder(binders, binder_cx)?;
        }
        self.analyze(r.range(comma.end, r.end), cx)
    }

    fn analyze_binder(&mut self, group: Lexer<'a>, cx: PCtx) -> GResult<()> {
        match split_first_top(group, &[":"], &[])? {
            Some((_, ty, _)) => self.analyze(ty, cx),
            None => match self.mentions(group, self.aliases.len, 0)? {
                Some(at) => violation(PeerViolationReason::AssumptionUncleanLeaf, at),
                None => Ok(()),
            },
        }
    }

    fn analyze_leaf(&mut self, r: Lexer<'a>, cx: PCtx) -> GResult<()> {
        let Some(at) = self.mentions(r, self.aliases.len, 0)? else {
            return Ok(());
        };
        // A clean leaf is `path::to::atom`, optionally applied to `()`.
        let mut c = r;
        let mut core: Option<Tok<'a>> = None;
        loop {
            let Some(t) = c.next()? else { break };
            if !t.is_ident() {
                core = None;
                break;
            }
            core = Some(t);
            if c.eat_punct("::")? || c.eat_punct(".")? {
                continue;
            }
            if c.next_is_punct("(")? {
                let open = c.next()?;
                if let Some(open) = open {
                    let s = c.pos;
                    let close = skip_group(&mut c, &open)?;
                    if !r.range(s, close).is_empty()? {
                        core = None;
                    }
                }
            }
            if !c.is_empty()? {
                core = None;
            }
            break;
        }
        match core {
            Some(t) if ASSUMPTION_ATOMS.contains(&t.text) => Self::occurrence(cx, t.start),
            Some(t) => match self.lookup(t.text, self.aliases.len) {
                Some(i) => {
                    if cx.inline_depth >= MAX_LET_ALIAS_DEPTH {
                        return Err(PeerScanError::new(
                            PeerScanErrorKind::AliasDepthExceeded,
                            t.start,
                        )
                        .into());
                    }
                    let saved = self.aliases;
                    let value = self.aliases.values[i];
                    self.aliases.len = i;
                    let res = self.analyze(
                        value,
                        PCtx {
                            inline_depth: cx.inline_depth + 1,
                            ..cx
                        },
                    );
                    self.aliases = saved;
                    res
                }
                None => violation(PeerViolationReason::AssumptionUncleanLeaf, at),
            },
            None => violation(PeerViolationReason::AssumptionUncleanLeaf, at),
        }
    }
}

/// Checks one proposition: the assumption atom (`assumes_hold` /
/// `assumesHold`, also through `let` aliases up to [`MAX_LET_ALIAS_DEPTH`])
/// may occur only in strictly negative polarity relative to `root`.
pub fn check_assumption_polarity_expr(
    expr: &str,
    dialect: SourceDialect,
    root: Polarity,
) -> GResult<()> {
    let mut an = PolarityAnalyzer::new(dialect);
    let sign = match root {
        Polarity::Positive => Sign::Pos,
        Polarity::Negative => Sign::Neg,
    };
    let lx = Lexer::new(expr, dialect);
    an.analyze(
        lx,
        PCtx {
            sign,
            antecedent: false,
            inline_depth: 0,
        },
    )
}

struct PolarityVisitor;

impl<'a> ClauseVisitor<'a> for PolarityVisitor {
    fn visit_clause(&mut self, kind: ClauseKind, clause: Lexer<'a>) -> GResult<()> {
        let sign = match kind {
            ClauseKind::Ensures => Sign::Pos,
            ClauseKind::Requires => Sign::Neg,
        };
        let cx = PCtx {
            sign,
            antecedent: false,
            inline_depth: 0,
        };
        let clause = match clause_list(clause)? {
            ClauseList::Empty => return Ok(()),
            ClauseList::Single(one) => one,
            ClauseList::Many(mut parts) => {
                while let Some(p) = parts.next_part()? {
                    self.visit_clause(kind, p)?;
                }
                return Ok(());
            }
        };
        let body = strip_closure_params(clause)?;
        if let Some(inner) = whole_group(body, "[")? {
            let mut parts = TopSplit::new(inner, false);
            while let Some(p) = parts.next_part()? {
                PolarityAnalyzer::new(clause.dialect).analyze(strip_closure_params(p)?, cx)?;
            }
            return Ok(());
        }
        PolarityAnalyzer::new(clause.dialect).analyze(body, cx)
    }
}

/// Source scanner of Guard 6a over Rust specification attributes: every
/// `ensures` clause is positive and every `requires` clause negative.
pub fn check_assumption_polarity_source(src: &str) -> GResult<()> {
    let mut lx = Lexer::new(src, SourceDialect::Rust);
    let mut st = DelimStack::new();
    while let Some(t) = lx.next()? {
        if t.is_punct("#") {
            if let Some((_, content)) = take_attribute(&mut lx)? {
                classify_attribute(content, &mut PolarityVisitor)?;
                continue;
            }
        }
        if t.is_kw("fn") {
            if let Some(sig) = scan_fn_signature(lx, false)? {
                if let Some(clauses) = sig.clauses {
                    for_each_sig_clause(clauses, &mut |kind, seg| {
                        PolarityVisitor.visit_clause(kind, seg)
                    })?;
                }
            }
        }
        st.feed(&t)?;
    }
    st.finish(src.len())?;
    Ok(())
}

const LEAN_DECL_KEYWORDS: [&str; 9] = [
    "theorem", "lemma", "def", "abbrev", "instance", "example", "axiom", "opaque", "variable",
];

/// Source scanner of Guard 6a over Lean declarations: binders are negative
/// and the declared type (and unannotated `def`/`abbrev` or equation-style
/// right-hand sides) is positive.
pub fn check_assumption_polarity_lean_source(src: &str) -> GResult<()> {
    let mut lx = Lexer::new(src, SourceDialect::Lean);
    let mut st = DelimStack::new();
    let pos_cx = PCtx {
        sign: Sign::Pos,
        antecedent: false,
        inline_depth: 0,
    };
    let neg_cx = PCtx {
        sign: Sign::Neg,
        antecedent: true,
        inline_depth: 0,
    };
    while let Some(t) = lx.next()? {
        if !(t.is_ident() && st.depth() == 0 && LEAN_DECL_KEYWORDS.contains(&t.text)) {
            st.feed(&t)?;
            continue;
        }
        let is_variable = t.text == "variable";
        let is_def_like = matches!(t.text, "def" | "abbrev");
        let mut c = lx;
        let mut sig_end = c.end;
        let mut colon: Option<Tok<'_>> = None;
        let mut saw_match = false;
        let mut stopped_at: Option<Tok<'_>> = None;
        loop {
            let save = c;
            let Some(n) = c.next()? else { break };
            if n.is_kw("match") {
                saw_match = true;
            }
            if n.is_punct(":=")
                || n.is_kw("where")
                || (n.is_punct("|") && !saw_match)
                || (n.is_ident() && LEAN_DECL_KEYWORDS.contains(&n.text))
                || (is_variable && !n.is_open())
            {
                sig_end = n.start;
                stopped_at = Some(n);
                c = save;
                break;
            }
            if n.is_open() {
                let s = c.pos;
                let close = skip_group(&mut c, &n)?;
                if colon.is_none() {
                    let mut an = PolarityAnalyzer::new(SourceDialect::Lean);
                    an.analyze_binder(lx.range(s, close), neg_cx)?;
                }
                continue;
            }
            if n.is_punct(":") && colon.is_none() {
                colon = Some(n);
            }
        }
        if let Some(col) = colon {
            let mut an = PolarityAnalyzer::new(SourceDialect::Lean);
            an.analyze(lx.range(col.end, sig_end), pos_cx)?;
        }
        // `def`/`abbrev := body` (with or without explicit `: Prop` type) or
        // equation-style `def ... | p => rhs`.
        if is_def_like {
            match stopped_at {
                Some(tok) if tok.is_punct(":=") => {
                    c.next()?;
                    let body_start = c.pos;
                    let mut body_end = c.end;
                    loop {
                        let save = c;
                        let Some(n) = c.next()? else { break };
                        if n.is_ident() && LEAN_DECL_KEYWORDS.contains(&n.text) {
                            body_end = n.start;
                            c = save;
                            break;
                        }
                        if n.is_open() {
                            skip_group(&mut c, &n)?;
                        }
                    }
                    let body = lx.range(body_start, body_end);
                    if !body.next_is_kw("by")? {
                        let mut an = PolarityAnalyzer::new(SourceDialect::Lean);
                        an.analyze(body, pos_cx)?;
                    }
                }
                Some(tok) if tok.is_punct("|") => {
                    while let Some(bar) = c.peek()? {
                        if !bar.is_punct("|") {
                            break;
                        }
                        c.next()?;
                        let mut arrow_end = None;
                        while let Some(n) = c.next()? {
                            if n.is_punct("=>") {
                                arrow_end = Some(n.end);
                                break;
                            }
                            if n.is_open() {
                                skip_group(&mut c, &n)?;
                            }
                        }
                        let Some(rhs_start) = arrow_end else { break };
                        let mut rhs_end = c.end;
                        loop {
                            let save = c;
                            let Some(n) = c.next()? else { break };
                            if n.is_punct("|")
                                || (n.is_ident() && LEAN_DECL_KEYWORDS.contains(&n.text))
                            {
                                rhs_end = n.start;
                                c = save;
                                break;
                            }
                            if n.is_open() {
                                skip_group(&mut c, &n)?;
                            }
                        }
                        let mut an = PolarityAnalyzer::new(SourceDialect::Lean);
                        an.analyze(lx.range(rhs_start, rhs_end), pos_cx)?;
                    }
                }
                _ => {}
            }
        }
        lx = c;
    }
    st.finish(src.len())?;
    Ok(())
}

// ----------------------------------------------------------------------------
// Guard 6b — invariant structure sealing (`Samite`)
// ----------------------------------------------------------------------------

/// Facts about an invariant-bearing structure (`StructSealingGuard` in Lean).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub struct StructSealingDescriptor {
    /// The structure carries an invariant.
    pub has_invariant: bool,
    /// Some field is public.
    pub pub_fields: bool,
    /// `#[derive(Default)]` is present.
    pub derives_default: bool,
    /// `impl Default` exists.
    pub default_impl: bool,
    /// An unchecked constructor trait (`Deserialize`, `FromBytes`, `Pod`, ...)
    /// is derived or implemented.
    pub unchecked_constructor_trait: bool,
    /// A public method returns `&mut` into a field.
    pub mutable_field_escape: bool,
    /// A public function builds the raw structure without a
    /// `#[smart_constructor]` gate.
    pub raw_public_constructor: bool,
}

/// Descriptor check of Guard 6b.
pub fn check_struct_sealing(
    desc: &StructSealingDescriptor,
) -> Result<(), PeerSoundnessGuardViolation> {
    use PeerViolationReason as R;
    if !desc.has_invariant {
        return Ok(());
    }
    if desc.pub_fields {
        return Err(descriptor_violation(R::InvariantPubField));
    }
    if desc.derives_default {
        return Err(descriptor_violation(R::InvariantDeriveDefault));
    }
    if desc.default_impl {
        return Err(descriptor_violation(R::InvariantDefaultImpl));
    }
    if desc.unchecked_constructor_trait {
        return Err(descriptor_violation(R::InvariantUncheckedConstructorTrait));
    }
    if desc.mutable_field_escape {
        return Err(descriptor_violation(R::InvariantMutableFieldEscape));
    }
    if desc.raw_public_constructor {
        return Err(descriptor_violation(R::InvariantRawPublicConstructor));
    }
    Ok(())
}

const MAX_INVARIANT_STRUCTS: usize = 32;

fn inv_entry_kind<'a>(invs: &PairTable<'a, MAX_INVARIANT_STRUCTS>, name: &str) -> Option<&'a str> {
    invs.entries()
        .iter()
        .find(|&&(n, _)| n == name)
        .map(|&(_, k)| k)
}

fn collect_inv_use_aliases<'a>(
    lx: &mut Lexer<'a>,
    invs: &mut PairTable<'a, MAX_INVARIANT_STRUCTS>,
    depth: usize,
    changed: &mut bool,
) -> GResult<()> {
    if depth > MAX_META_DEPTH {
        return Err(PeerScanError::new(PeerScanErrorKind::NestingTooDeep, lx.pos).into());
    }
    let mut cur: Option<&'a str> = None;
    loop {
        let Some(t) = lx.peek()? else { return Ok(()) };
        if t.is_punct("::") {
            lx.next()?;
            continue;
        }
        if t.is_punct("{") {
            lx.next()?;
            loop {
                let Some(n) = lx.peek()? else {
                    return Err(PeerScanError::new(
                        PeerScanErrorKind::UnbalancedDelimiter,
                        t.start,
                    )
                    .into());
                };
                if n.is_punct("}") {
                    lx.next()?;
                    return Ok(());
                }
                if n.is_punct(",") {
                    lx.next()?;
                    continue;
                }
                let before = lx.pos;
                collect_inv_use_aliases(lx, invs, depth + 1, changed)?;
                if lx.pos == before {
                    lx.next()?;
                }
            }
        }
        if t.is_ident() {
            lx.next()?;
            if !(t.text == "self" && !t.raw) {
                cur = Some(t.text);
            }
            if lx.next_is_punct("::")? {
                continue;
            }
            let Some(item) = cur else { return Ok(()) };
            if lx.next_is_kw("as")? {
                lx.next()?;
                if let Some(a) = lx.next()? {
                    if a.is_ident() && a.text != "_" {
                        if let Some(kind) = inv_entry_kind(invs, item) {
                            *changed |= invs.push(a.text, kind, a.start)?;
                        }
                    }
                }
            }
            return Ok(());
        }
        return Ok(());
    }
}

fn collect_inv_aliases<'a>(
    src: &'a str,
    invs: &mut PairTable<'a, MAX_INVARIANT_STRUCTS>,
) -> GResult<bool> {
    let mut lx = Lexer::new(src, SourceDialect::Rust);
    let mut changed = false;
    while let Some(t) = lx.next()? {
        if t.is_punct("#") {
            take_attribute(&mut lx)?;
            continue;
        }
        if t.is_kw("use") {
            collect_inv_use_aliases(&mut lx, invs, 0, &mut changed)?;
        } else if t.is_kw("type") {
            let mut c = lx;
            let Some(alias) = c.next()? else { continue };
            if !alias.is_ident() {
                continue;
            }
            if c.next_is_punct("<")? {
                let lt = c.next()?;
                let at = lt.map_or(c.pos, |x| x.start);
                skip_angles(&mut c, at)?;
            }
            if !c.eat_punct("=")? {
                continue;
            }
            let start = c.pos;
            let mut end = c.end;
            while let Some(n) = c.next()? {
                if n.is_punct(";") {
                    end = n.start;
                    break;
                }
            }
            if let Some(target) = path_last_ident(lx.range(start, end))? {
                if alias.text != target {
                    if let Some(kind) = inv_entry_kind(invs, target) {
                        changed |= invs.push(alias.text, kind, alias.start)?;
                    }
                }
            }
        }
    }
    Ok(changed)
}

/// Whether `after_pat` (immediately after a candidate struct/tuple pattern
/// `Pos(...)` or `Range { ... }`) is followed by a match-arm `=>`, `let` `=`,
/// or another `| ... =>` OR-pattern branch.
fn is_pattern_trailer(after_pat: Lexer<'_>) -> Result<bool, PeerScanError> {
    let mut p = after_pat;
    let Some(next) = p.next()? else {
        return Ok(false);
    };
    if next.is_punct("=>") || next.is_punct("=") {
        return Ok(true);
    }
    if next.is_punct("|") || next.is_kw("if") {
        while let Some(t) = p.next()? {
            if t.is_punct("=>") {
                return Ok(true);
            }
            if t.is_punct(";") || t.is_punct(",") {
                return Ok(false);
            }
            if t.is_open() {
                skip_group(&mut p, &t)?;
            }
        }
    }
    Ok(false)
}

fn body_constructs_raw<'a>(
    body: Lexer<'a>,
    invs: &PairTable<'a, MAX_INVARIANT_STRUCTS>,
    self_kind: Option<&'a str>,
) -> Result<Option<usize>, PeerScanError> {
    let mut c = body;
    let mut prev: Option<Tok<'a>> = None;
    while let Some(t) = c.next()? {
        let kind = if t.is_ident() {
            if let Some(k) = inv_entry_kind(invs, t.text) {
                Some(k)
            } else if t.is_kw("Self") {
                self_kind
            } else {
                None
            }
        } else {
            None
        };
        let let_pat = matches!(prev, Some(p) if p.is_kw("let"));
        if let Some(k) = kind {
            if !let_pat {
                let mut probe = c;
                let mut had_turbofish = false;
                if probe.eat_punct("::")? && probe.next_is_punct("<")? {
                    let lt = probe.next()?;
                    let at = lt.map_or(probe.pos, |x| x.start);
                    skip_angles(&mut probe, at)?;
                    had_turbofish = true;
                } else {
                    probe = c;
                }
                if let Some(open) = probe.next()? {
                    if open.is_punct("{") || open.is_punct("(") {
                        skip_group(&mut probe, &open)?;
                        if !is_pattern_trailer(probe)? {
                            return Ok(Some(t.start));
                        }
                        prev = Some(t);
                        continue;
                    }
                }
                // A tuple struct's name is also a value-namespace constructor
                // function (`let mk = Positive;`, `xs.map(Positive)`, `Positive::<T>`).
                if k == "T" {
                    let type_ctx = matches!(
                        prev,
                        Some(p)
                            if p.is_punct(":")
                                || p.is_punct("->")
                                || p.is_punct("<")
                                || p.is_kw("as")
                                || p.is_kw("impl")
                                || p.is_kw("for")
                                || p.is_kw("where")
                                || p.is_kw("struct")
                                || p.is_kw("type")
                    );
                    let method_path = !had_turbofish && c.next_is_punct("::")?;
                    let is_generic_type_arg = c.next_is_punct("<")?;
                    let is_pattern_eq = c.next_is_punct("=>")?;
                    if !type_ctx && !method_path && !is_generic_type_arg && !is_pattern_eq {
                        if had_turbofish
                            || starts_expression(prev)
                            || matches!(prev, Some(p) if p.is_punct("|"))
                        {
                            return Ok(Some(t.start));
                        }
                    }
                }
            }
        }
        prev = Some(t);
    }
    Ok(None)
}

/// Source scanner of Guard 6b over Rust source.
pub fn check_struct_sealing_source(src: &str) -> GResult<()> {
    let mut invs: PairTable<'_, MAX_INVARIANT_STRUCTS> = PairTable::new();
    // Pass 1: invariant structures, their fields, and derives.
    {
        let mut lx = Lexer::new(src, SourceDialect::Rust);
        let mut pending = AttrFlags::default();
        while let Some(t) = lx.next()? {
            if t.is_punct("#") {
                if let Some((inner, content)) = take_attribute(&mut lx)? {
                    if !inner {
                        pending.merge(classify_attribute(content, &mut NoClauses)?);
                    }
                    continue;
                }
            }
            if t.is_punct(";") || t.is_punct("{") || t.is_punct("}") {
                pending = AttrFlags::default();
                continue;
            }
            if t.is_kw("struct") {
                let flags = pending;
                pending = AttrFlags::default();
                if !flags.invariant {
                    continue;
                }
                let Some(item) = parse_struct_item(lx)? else {
                    continue;
                };
                invs.push(item.name, if item.tuple { "T" } else { "N" }, t.start)?;
                if flags.derive_default {
                    return violation(PeerViolationReason::InvariantDeriveDefault, t.start);
                }
                if flags.derive_unchecked {
                    return violation(
                        PeerViolationReason::InvariantUncheckedConstructorTrait,
                        t.start,
                    );
                }
                if let Some(body) = item.body {
                    for_each_field(body, item.tuple, &mut |field| {
                        if field.is_pub {
                            return violation(PeerViolationReason::InvariantPubField, field.offset);
                        }
                        Ok(())
                    })?;
                }
            }
        }
    }
    if invs.len == 0 {
        return Ok(());
    }
    for _ in 0..MAX_INVARIANT_STRUCTS {
        if !collect_inv_aliases(src, &mut invs)? {
            break;
        }
    }
    // Pass 2 (iterated): `impl Default`, public raw constructors, private
    // tainted `const`/`static` values, and public functions forwarding to
    // private raw-constructing helpers (transitively).
    let mut tainted: PairTable<'_, MAX_TAINTED_HELPERS> = PairTable::new();
    for _ in 0..=MAX_TAINTED_HELPERS {
        if !sealing_pass(src, &invs, &mut tainted)? {
            return Ok(());
        }
    }
    Ok(())
}

const MAX_TAINTED_HELPERS: usize = 32;

/// Whether `body` calls or coerces a tainted helper (`raw(..)`,
/// `Self::raw::<T>(..)`, `Self::raw`), references a tainted `const`/`static`,
/// or (when `names_inv` is true) calls a generic raw-materializing helper `"M"`.
fn body_calls_tainted<'a>(
    body: Lexer<'a>,
    tainted: &PairTable<'a, MAX_TAINTED_HELPERS>,
    names_inv: bool,
) -> Result<Option<usize>, PeerScanError> {
    let mut c = body;
    let mut prev: Option<Tok<'a>> = None;
    while let Some(t) = c.next()? {
        if t.is_ident() {
            if let Some(&(_, kind)) = tainted.entries().iter().find(|&&(n, _)| n == t.text) {
                if kind == "M" && !names_inv {
                    prev = Some(t);
                    continue;
                }
                let mut probe = c;
                if probe.eat_punct("::")? && probe.next_is_punct("<")? {
                    let lt = probe.next()?;
                    let at = lt.map_or(probe.pos, |x| x.start);
                    skip_angles(&mut probe, at)?;
                } else {
                    probe = c;
                }
                if probe.next_is_punct("(")? {
                    return Ok(Some(t.start));
                }
                let def_pos = matches!(prev, Some(p) if p.is_kw("fn") || p.is_kw("let") || p.is_kw("const") || p.is_kw("static"));
                if !def_pos {
                    if kind == "V"
                        || matches!(prev, Some(p) if p.is_punct("::"))
                        || starts_expression(prev)
                    {
                        return Ok(Some(t.start));
                    }
                }
            }
        }
        prev = Some(t);
    }
    Ok(None)
}

/// `&mut self.field` (or `&mut self.0`) in a body.
fn body_mut_field_borrow(body: Lexer<'_>) -> Result<Option<usize>, PeerScanError> {
    let mut c = body;
    while let Some(t) = c.next()? {
        if t.is_punct("&") {
            let mut p = c;
            if p.next_is_kw("mut")? {
                p.next()?;
                if p.next_is_kw("self")? {
                    p.next()?;
                    if p.next_is_punct(".")? {
                        return Ok(Some(t.start));
                    }
                }
            }
        }
    }
    Ok(None)
}

/// One sealing pass; returns whether the tainted-helper set grew.
fn sealing_pass<'a>(
    src: &'a str,
    invs: &PairTable<'a, MAX_INVARIANT_STRUCTS>,
    tainted: &mut PairTable<'a, MAX_TAINTED_HELPERS>,
) -> GResult<bool> {
    let mut changed = false;
    let mut lx = Lexer::new(src, SourceDialect::Rust);
    let mut st = DelimStack::new();
    let mut pending = AttrFlags::default();
    let mut pending_pub = false;
    let mut in_impl_header = false;
    let mut impl_pending: Option<ImplHeader<'a>> = None;
    let mut impl_scope: Option<(ImplHeader<'a>, usize)> = None;
    while let Some(t) = lx.next()? {
        if t.is_punct("#") {
            if let Some((inner, content)) = take_attribute(&mut lx)? {
                if !inner {
                    pending.merge(classify_attribute(content, &mut NoClauses)?);
                }
                continue;
            }
        }
        if t.is_open() {
            st.feed(&t)?;
            if t.is_punct("{") {
                if in_impl_header {
                    impl_scope = impl_pending.map(|h| (h, st.depth()));
                    in_impl_header = false;
                    impl_pending = None;
                }
                pending = AttrFlags::default();
                pending_pub = false;
            }
            continue;
        }
        if t.is_close() {
            st.feed(&t)?;
            if matches!(impl_scope, Some((_, d)) if st.depth() < d) {
                impl_scope = None;
            }
            if t.is_punct("}") {
                pending = AttrFlags::default();
                pending_pub = false;
            }
            continue;
        }
        if t.is_punct(";") {
            pending = AttrFlags::default();
            pending_pub = false;
            continue;
        }
        if t.is_kw("pub") {
            pending_pub = true;
            continue;
        }
        if t.is_kw("impl") {
            let h = parse_impl_header(lx)?;
            if let Some(h) = h {
                if h.trait_last == Some("Default") && invs.contains_first(h.self_ty) {
                    return violation(PeerViolationReason::InvariantDefaultImpl, t.start);
                }
                if matches!(h.trait_last, Some(tr) if UNCHECKED_CONSTRUCTOR_TRAITS.contains(&tr))
                    && invs.contains_first(h.self_ty)
                {
                    return violation(
                        PeerViolationReason::InvariantUncheckedConstructorTrait,
                        t.start,
                    );
                }
            }
            in_impl_header = true;
            impl_pending = h;
            skip_item_header_to_brace(&mut lx)?;
            continue;
        }
        let self_kind = match impl_scope {
            Some((h, _)) => inv_entry_kind(invs, h.self_ty),
            None => None,
        };
        let trait_impl = matches!(impl_scope, Some((h, _)) if h.trait_last.is_some());
        if t.is_kw("fn") {
            let public = pending_pub || trait_impl;
            let gated = pending.smart_constructor;
            pending = AttrFlags::default();
            pending_pub = false;
            if gated {
                continue;
            }
            let Some(sig) = scan_fn_signature(lx, false)? else {
                continue;
            };
            let mut c = sig.rest;
            let Some(open) = c.next()? else { continue };
            if !open.is_punct("{") {
                continue;
            }
            let s = c.pos;
            let close = skip_group(&mut c, &open)?;
            let body = lx.range(s, close);
            // A function whose impl or signature names the invariant type and whose
            // body materializes raw bits (`transmute`, `zeroed`, ...) is a raw
            // constructor too.
            let mut names_inv = self_kind.is_some();
            {
                let mut sc = lx.range(lx.pos, open.start);
                while let Some(n) = sc.next()? {
                    names_inv |= n.is_ident() && invs.contains_first(n.text);
                }
            }
            // A public method of the invariant type returning `&mut` into a field
            // lets clients mutate it unchecked outside the defining boundary.
            if public && self_kind.is_some() {
                let mut returns_mut = false;
                let mut sc = lx.range(lx.pos, open.start);
                let mut after_arrow = false;
                let mut prev_amp = false;
                while let Some(n) = sc.next()? {
                    if n.is_punct("->") {
                        after_arrow = true;
                    }
                    if after_arrow && prev_amp && n.is_kw("mut") {
                        returns_mut = true;
                    }
                    prev_amp = n.is_punct("&");
                }
                if returns_mut {
                    if let Some(at) = body_mut_field_borrow(body)? {
                        return violation(PeerViolationReason::InvariantMutableFieldEscape, at);
                    }
                }
            }
            let raw_mat = body_raw_materializer(body)?;
            let materializes = if names_inv { raw_mat } else { None };
            let hit = match body_constructs_raw(body, invs, self_kind)? {
                Some(at) => Some(at),
                None => match materializes {
                    Some(at) => Some(at),
                    None => body_calls_tainted(body, tainted, names_inv)?,
                },
            };
            if let Some(at) = hit {
                if public {
                    return violation(PeerViolationReason::InvariantRawPublicConstructor, at);
                }
                changed |= tainted.push(sig.name.text, "F", sig.name.start)?;
            } else if !public && raw_mat.is_some() {
                changed |= tainted.push(sig.name.text, "M", sig.name.start)?;
            }
            continue;
        }
        if (t.is_kw("const") || t.is_kw("static")) && !lx.next_is_kw("fn")? {
            let public = pending_pub;
            let gated = pending.smart_constructor;
            pending = AttrFlags::default();
            pending_pub = false;
            let mut c = lx;
            let item_name = c.next()?;
            let mut eq_pos = None;
            let mut end = c.end;
            while let Some(n) = c.next()? {
                if n.is_punct("=") && eq_pos.is_none() {
                    eq_pos = Some(n.end);
                    continue;
                }
                if n.is_punct(";") {
                    end = n.start;
                    break;
                }
                if n.is_open() {
                    skip_group(&mut c, &n)?;
                }
            }
            if !gated {
                if let Some(init_start) = eq_pos {
                    let mut names_inv = self_kind.is_some();
                    {
                        let mut sc = lx.range(lx.pos, init_start);
                        while let Some(n) = sc.next()? {
                            names_inv |= n.is_ident() && invs.contains_first(n.text);
                        }
                    }
                    let init = lx.range(init_start, end);
                    let materializes = if names_inv {
                        body_raw_materializer(init)?
                    } else {
                        None
                    };
                    let hit = match body_constructs_raw(init, invs, self_kind)? {
                        Some(at) => Some(at),
                        None => match materializes {
                            Some(at) => Some(at),
                            None => body_calls_tainted(init, tainted, names_inv)?,
                        },
                    };
                    if let Some(at) = hit {
                        if public {
                            return violation(
                                PeerViolationReason::InvariantRawPublicConstructor,
                                at,
                            );
                        }
                        if let Some(n) = item_name.filter(|n| n.is_ident()) {
                            changed |= tainted.push(n.text, "V", n.start)?;
                        }
                    }
                }
            }
        }
    }
    st.finish(src.len())?;
    Ok(changed)
}

/// Source scanner of Guard 6 (both halves) over Rust source.
pub fn check_assumption_polarity_and_sealing(src: &str) -> GResult<()> {
    check_assumption_polarity_source(src)?;
    check_struct_sealing_source(src)
}

/// Runs all four peer-guard source scanners over Rust source.
pub fn check_peer_soundness_guards_source<'a>(
    src: &'a str,
    ghost_ctor_paths: &[&'a str],
) -> GResult<()> {
    check_extern_ensures_false_source(src)?;
    check_fndef_ghost_token_coercion_source(src, ghost_ctor_paths)?;
    check_external_type_drop_omission_source(src)?;
    check_assumption_polarity_and_sealing(src)
}

/// Per-guard verdicts of [`check_peer_soundness_guards_source`].
pub fn peer_guard_verdicts<'a>(
    src: &'a str,
    ghost_ctor_paths: &[&'a str],
) -> [PeerSpecGuardVerdict; 4] {
    use PeerSpecGuardClass as G;
    [
        PeerSpecGuardVerdict::of_result(
            G::UnsatisfiableExternEnsures,
            &check_extern_ensures_false_source(src),
        ),
        PeerSpecGuardVerdict::of_result(
            G::FnDefGhostTokenCoercion,
            &check_fndef_ghost_token_coercion_source(src, ghost_ctor_paths),
        ),
        PeerSpecGuardVerdict::of_result(
            G::ExternalTypeDropOmission,
            &check_external_type_drop_omission_source(src),
        ),
        PeerSpecGuardVerdict::of_result(
            G::AssumptionPolarityAndStructSealing,
            &check_assumption_polarity_and_sealing(src),
        ),
    ]
}

#[cfg(test)]
mod tests {
    use super::*;

    const TOKENS: &[&str] = &["Tokens::new"];

    fn reason(r: GResult<()>) -> Option<PeerViolationReason> {
        r.err().and_then(|e| e.reason())
    }

    fn g3(src: &str) -> Option<PeerViolationReason> {
        reason(check_extern_ensures_false_source(src))
    }

    fn g4(src: &str) -> Option<PeerViolationReason> {
        reason(check_fndef_ghost_token_coercion_source(src, TOKENS))
    }

    fn g5(src: &str) -> Option<PeerViolationReason> {
        reason(check_external_type_drop_omission_source(src))
    }

    fn g6a(src: &str) -> Option<PeerViolationReason> {
        reason(check_assumption_polarity_source(src))
    }

    fn g6b(src: &str) -> Option<PeerViolationReason> {
        reason(check_struct_sealing_source(src))
    }

    fn expr(e: &str, d: SourceDialect, root: Polarity) -> Option<PeerViolationReason> {
        reason(check_assumption_polarity_expr(e, d, root))
    }

    use PeerViolationReason as R;

    // --- Taxonomy -----------------------------------------------------------

    #[test]
    fn peer_taxonomy_wire_table_matches_lean() {
        let table: [(usize, &str, &str, &str); 4] = [
            (
                3,
                "unsatisfiable_extern_ensures",
                "UnsatisfiableExternEnsures",
                "DeadPrecondition",
            ),
            (
                4,
                "fndef_ghost_token_coercion",
                "FnDefGhostTokenCoercion",
                "SpecViolation",
            ),
            (
                5,
                "external_type_drop_omission",
                "ExternalTypeDropOmission",
                "SpecViolation",
            ),
            (
                6,
                "assumption_polarity_and_struct_sealing",
                "AssumptionPolarityAndStructSealing",
                "SurvivedAllMutants",
            ),
        ];
        assert_eq!(PeerSpecGuardClass::COUNT, 4);
        assert_eq!(PeerSpecGuardClass::FIRST_RANK, 3);
        for (g, (rank, id, name, vac)) in PeerSpecGuardClass::ALL.into_iter().zip(table) {
            assert_eq!(g.rank(), rank);
            assert_eq!(g.guard_id(), id);
            assert_eq!(g.canonical_name(), name);
            assert_eq!(g.to_vacuity_class().canonical_name(), vac);
            assert_eq!(PeerSpecGuardClass::from_rank(rank), Some(g));
            assert_eq!(PeerSpecGuardClass::from_guard_id(id), Some(g));
            assert_eq!(PeerSpecGuardClass::from_canonical_name(name), Some(g));
        }
    }

    #[test]
    fn peer_taxonomy_rejects_out_of_range_and_base_ids() {
        for r in [0, 1, 2, 7, 8, usize::MAX] {
            assert_eq!(PeerSpecGuardClass::from_rank(r), None);
        }
        for b in SpecBoundaryGuardClass::ALL {
            assert_eq!(PeerSpecGuardClass::from_guard_id(b.guard_id()), None);
            assert_eq!(
                PeerSpecGuardClass::from_canonical_name(b.canonical_name()),
                None
            );
            for p in PeerSpecGuardClass::ALL {
                assert_ne!(p.rank(), b.rank());
            }
        }
        assert_eq!(
            PeerSpecGuardClass::from_guard_id("FnDefGhostTokenCoercion"),
            None
        );
        assert_eq!(
            PeerSpecGuardClass::from_canonical_name("fndef_ghost_token_coercion"),
            None
        );
    }

    #[test]
    fn combined_taxonomy_roundtrips_over_zero_to_six() {
        assert_eq!(CombinedSpecGuardClass::COUNT, 7);
        for (i, c) in CombinedSpecGuardClass::ALL.into_iter().enumerate() {
            assert_eq!(c.rank(), i);
            assert_eq!(CombinedSpecGuardClass::from_rank(i), Some(c));
            assert_eq!(CombinedSpecGuardClass::from_guard_id(c.guard_id()), Some(c));
        }
        assert_eq!(CombinedSpecGuardClass::from_rank(7), None);
        let mut ids = CombinedSpecGuardClass::ALL.map(|c| c.guard_id());
        ids.sort_unstable();
        for w in ids.windows(2) {
            assert_ne!(w[0], w[1]);
        }
    }

    #[test]
    fn verdict_reports_vacuity_class_only_on_violation() {
        let g = PeerSpecGuardClass::ExternalTypeDropOmission;
        assert_eq!(
            PeerSpecGuardVerdict::of_check(g, true).vacuity_class(),
            None
        );
        assert_eq!(
            PeerSpecGuardVerdict::of_check(g, false).vacuity_class(),
            Some(VacuityClass::SpecViolation)
        );
        assert_eq!(PeerSpecGuardVerdict::of_check(g, false).guard(), g);
        for r in [
            R::LyingDivergence,
            R::ReentrantMain,
            R::UnmodeledOpaqueField,
            R::AssumptionInIff,
        ] {
            assert_eq!(
                PeerSoundnessGuardViolation {
                    reason: r,
                    offset: 0
                }
                .vacuity_class(),
                r.guard().to_vacuity_class()
            );
        }
    }

    // --- Lexer ----------------------------------------------------------------

    #[test]
    fn lexer_skips_comments_strings_and_lifetimes() {
        let src = r##"
            /* outer /* #[trusted] #[ensures(false)] fn a() -> u8; */ still comment */
            // #[trusted] #[ensures(false)] fn b() -> u8;
            const S: &str = "#[trusted] #[ensures(false)] fn c() -> u8;";
            const R: &str = r#"#[trusted] #[ensures(false)] fn d() -> u8;"#;
            const B: &[u8] = br#"#[trusted]"#;
            const C: char = '"';
            fn e<'a>(x: &'a u8) -> &'a u8 { x }
        "##;
        assert_eq!(g3(src), None);
    }

    #[test]
    fn lexer_fails_closed_on_unterminated_input() {
        for src in [
            "/* never closed",
            "const S: &str = \"open;",
            "fn f() { ",
            "fn f() ) {",
        ] {
            assert!(matches!(
                check_extern_ensures_false_source(src),
                Err(PeerSoundnessGuardError::Scan(_))
            ));
        }
    }

    // --- Guard 3 --------------------------------------------------------------

    #[test]
    fn g3_descriptor_matches_lean_guard() {
        let base = ExternEnsuresDescriptor {
            trust: ContractTrust::ExternSpec,
            ensures_unsatisfiable: true,
            requires_false: false,
            is_diverging: false,
            return_uninhabited: false,
        };
        assert_eq!(
            check_extern_ensures_false(&base).map_err(|v| v.reason),
            Err(R::EnsuresFalseOnReturningFn)
        );
        assert!(
            check_extern_ensures_false(&ExternEnsuresDescriptor {
                requires_false: true,
                ..base
            })
            .is_ok()
        );
        assert!(
            check_extern_ensures_false(&ExternEnsuresDescriptor {
                is_diverging: true,
                return_uninhabited: true,
                ..base
            })
            .is_ok()
        );
        assert_eq!(
            check_extern_ensures_false(&ExternEnsuresDescriptor {
                is_diverging: true,
                ..base
            })
            .map_err(|v| v.reason),
            Err(R::LyingDivergence)
        );
        assert!(
            check_extern_ensures_false(&ExternEnsuresDescriptor {
                trust: ContractTrust::Verified,
                ..base
            })
            .is_ok()
        );
    }

    #[test]
    fn g3_catches_every_trusted_form() {
        let forms = [
            "#[trusted] #[ensures(false)] fn read_volatile(p: *const u8) -> u8;",
            "#[external_spec] #[ensures(false)] fn f() -> u8;",
            "#[extern_spec] #[ensures(false)] fn f() -> u8;",
            "#[spec(trusted, ensures: false)] fn f() -> u8 { 0 }",
            "#[spec(assumed, ensures: |r| false)] fn f() -> u8 { 0 }",
            "#[spec(trusted, ensures: [r > 0, false])] fn f() -> u8 { 0 }",
            "#[verifier::external_body] #[ensures(false)] fn f() -> u8 { 0 }",
            "#[verifier(external_body)] #[ensures(false)] fn f() -> u8 { 0 }",
            "#[external_spec(target = core::ptr::read_volatile, ensures: |r| false)] fn f() -> u8;",
            "#[trusted] #[ensures(false)] fn f() {}",
        ];
        for src in forms {
            assert_eq!(g3(src), Some(R::EnsuresFalseOnReturningFn), "{src}");
        }
    }

    #[test]
    fn g3_catches_extern_spec_scopes_and_macro() {
        let scoped = [
            "#[extern_spec] impl Foo { #[ensures(false)] fn read(&self) -> u8; }",
            "#[extern_spec] mod core { #[ensures(false)] fn read() -> u8; }",
            "#[extern_spec] trait T { #[ensures(false)] fn read() -> u8; }",
            "extern_spec! { impl Foo { #[ensures(false)] fn read(&self) -> u8; } }",
            "#![trusted]\n#[ensures(false)] fn read() -> u8;",
        ];
        for src in scoped {
            assert_eq!(g3(src), Some(R::EnsuresFalseOnReturningFn), "{src}");
        }
        // The scope closes with its block.
        assert_eq!(
            g3("#[extern_spec] mod m { fn x() -> u8; } #[ensures(false)] fn y() -> u8 { 0 }"),
            None
        );
    }

    #[test]
    fn g3_catches_semantically_false_clauses() {
        for clause in [
            "false && x",
            "x && false",
            "!true",
            "(false)",
            "1 > 2",
            "{ false }",
            "!(true || x)",
        ] {
            let src = std::format!("#[trusted] #[ensures({clause})] fn f() -> u8;");
            assert_eq!(g3(&src), Some(R::EnsuresFalseOnReturningFn), "{clause}");
        }
        for clause in ["false || x", "x", "1 < 2"] {
            let src = std::format!("#[trusted] #[ensures({clause})] fn f() -> u8;");
            assert_eq!(g3(&src), None, "{clause}");
        }
    }

    #[test]
    fn g3_cfg_attr_is_asymmetric() {
        assert_eq!(
            g3("#[cfg_attr(feature = \"v\", trusted)] #[ensures(false)] fn f() -> u8;"),
            Some(R::EnsuresFalseOnReturningFn)
        );
        assert_eq!(
            g3("#[trusted] #[cfg_attr(feature = \"v\", ensures(false))] fn f() -> u8;"),
            Some(R::EnsuresFalseOnReturningFn)
        );
        assert_eq!(
            g3("#[trusted] #[ensures(false)] #[cfg_attr(test, requires(false))] fn f() -> u8;"),
            Some(R::EnsuresFalseOnReturningFn)
        );
        assert_eq!(
            g3("#[trusted] #[ensures(false)] #[requires(false)] fn f() -> u8;"),
            None
        );
        assert_eq!(
            g3("#[spec(trusted, requires: false, ensures: false)] fn f() -> u8;"),
            None
        );
    }

    #[test]
    fn g3_allows_genuine_divergence_and_rejects_lies() {
        assert_eq!(g3("#[trusted] #[ensures(false)] fn abort() -> !;"), None);
        assert_eq!(
            g3("#[trusted] #[ensures(false)] fn abort() -> core::convert::Infallible;"),
            None
        );
        assert_eq!(
            g3("#[trusted] #[diverging] #[ensures(false)] fn abort() -> !;"),
            None
        );
        assert_eq!(
            g3("#[trusted] #[diverging] #[ensures(false)] fn read() -> u8;"),
            Some(R::LyingDivergence)
        );
        assert_eq!(
            g3("#[spec(trusted, is_diverging = true, ensures: false)] fn read() -> u8;"),
            Some(R::LyingDivergence)
        );
        assert_eq!(
            g3("#[spec(trusted, is_diverging: true)] fn read() -> u8;"),
            Some(R::LyingDivergence)
        );
        assert_eq!(g3("#[is_diverging = false] fn read() -> u8 { 0 }"), None);
        // Untrusted, verified contracts are left to the verifier.
        assert_eq!(g3("#[ensures(false)] fn f() -> u8 { loop {} }"), None);
    }

    #[test]
    fn g3_attributes_do_not_leak_across_items() {
        assert_eq!(
            g3("#[trusted] struct S; #[ensures(false)] fn f() -> u8 { 0 }"),
            None
        );
        assert_eq!(
            g3("#[trusted] fn g() {} #[ensures(false)] fn f() -> u8 { 0 }"),
            None
        );
        assert_eq!(
            g3("#[trusted] pub(crate) unsafe extern \"C\" fn f() -> u8 { 0 }"),
            None
        );
        assert_eq!(
            g3("#[trusted] #[ensures(false)] pub(crate) unsafe extern \"C\" fn f() -> u8 { 0 }"),
            Some(R::EnsuresFalseOnReturningFn)
        );
    }

    // --- Guard 4 --------------------------------------------------------------

    #[test]
    fn g4_descriptor_matches_lean_guard() {
        let ok = GhostTokenUsageDescriptor {
            call_sites: 1,
            ..Default::default()
        };
        assert!(check_fndef_ghost_token_coercion(&ok).is_ok());
        let cases = [
            (
                GhostTokenUsageDescriptor {
                    fn_def_value_coercions: 1,
                    ..ok
                },
                R::FnDefValueCoercion,
            ),
            (
                GhostTokenUsageDescriptor {
                    call_sites_in_repeating_context: 1,
                    ..ok
                },
                R::MintInRepeatingContext,
            ),
            (
                GhostTokenUsageDescriptor {
                    call_sites_outside_main: 1,
                    ..ok
                },
                R::MintOutsideMain,
            ),
            (
                GhostTokenUsageDescriptor {
                    call_sites: 2,
                    ..ok
                },
                R::MultipleMintSites,
            ),
            (
                GhostTokenUsageDescriptor {
                    main_reentrant: true,
                    ..ok
                },
                R::ReentrantMain,
            ),
        ];
        for (d, r) in cases {
            assert_eq!(
                check_fndef_ghost_token_coercion(&d).map_err(|v| v.reason),
                Err(r)
            );
        }
    }

    #[test]
    fn g4_allows_single_direct_call_in_main() {
        assert_eq!(g4("fn main() { let t = Tokens::new(); use_it(t); }"), None);
        assert_eq!(
            g4("fn main() { if cond() { let _t = Tokens::new(); } }"),
            None
        );
        assert_eq!(
            g4(
                "impl Tokens { fn new() -> Self { Tokens { id: 0 } } } fn main() { Tokens::new(); }"
            ),
            None
        );
        assert_eq!(
            g4("fn helper(x: u8) -> u8 { x } fn main() { let _t = Tokens::new(); helper(1); }"),
            None
        );
    }

    #[test]
    fn g4_catches_fndef_value_coercions() {
        let srcs = [
            "fn main() { let mk = Tokens::new; let a = mk(); let b = mk(); }",
            "fn main() { let v: Vec<_> = (0..2).map(|_| ()).map(Tokens::new).collect(); }",
            "fn main() { let f = Tokens::new as fn() -> Tokens; }",
            "fn main() { let arr = [Tokens::new]; }",
            "fn main() { let s = Holder { f: Tokens::new }; }",
            "fn main() { let t = (Tokens::new, 1); }",
            "fn main() { let f = <Tokens>::new; }",
        ];
        for src in srcs {
            assert_eq!(g4(src), Some(R::FnDefValueCoercion), "{src}");
        }
    }

    #[test]
    fn g4_canonicalizes_turbofish_ufcs_self_and_aliases() {
        assert_eq!(
            g4("fn main() { let f = Tokens::<()>::new; }"),
            Some(R::FnDefValueCoercion)
        );
        assert_eq!(
            g4("fn main() { let f = <Tokens as Mint>::new; }"),
            Some(R::FnDefValueCoercion)
        );
        assert_eq!(
            g4("use crate::ghost::Tokens as Tk; fn main() { let f = Tk::new; }"),
            Some(R::FnDefValueCoercion)
        );
        assert_eq!(
            g4("type Tk = crate::Tokens<()>; type Tk2 = Tk; fn main() { let f = Tk2::new; }"),
            Some(R::FnDefValueCoercion)
        );
        assert_eq!(
            g4("use crate::Tokens::new as mint; fn main() { let f = mint; }"),
            Some(R::FnDefValueCoercion)
        );
        assert_eq!(
            g4("use crate::Tokens::{self as Tk}; fn main() { for _ in 0..2 { Tk::new(); } }"),
            Some(R::MintInRepeatingContext)
        );
        assert_eq!(
            g4("use crate::Tokens::*; fn main() { let f = new; }"),
            Some(R::FnDefValueCoercion)
        );
        assert_eq!(
            g4("impl Tokens { fn twice() { Self::new(); } }"),
            Some(R::MintOutsideMain)
        );
        assert_eq!(
            g4("fn main() { r#Tokens::new(); r#Tokens::new(); }"),
            Some(R::MultipleMintSites)
        );
        assert_eq!(g4("fn main() { Tokens::<()>::new(); }"), None);
    }

    #[test]
    fn g4_catches_repeating_contexts() {
        let srcs = [
            "fn main() { loop { Tokens::new(); } }",
            "fn main() { while go() { let _t = Tokens::new(); } }",
            "fn main() { for _ in 0..2 { Tokens::new(); } }",
            "fn main() { while Tokens::new().live() {} }",
            "fn main() { let f = || Tokens::new(); f(); }",
            "fn main() { let f = |x: u8| { Tokens::new() }; }",
            "fn main() { let f = async || Tokens::new(); }",
            "fn main() { let fut = async move { Tokens::new() }; }",
            "fn main() { (0..2).for_each(|_| { Tokens::new(); }); }",
        ];
        for src in srcs {
            assert_eq!(g4(src), Some(R::MintInRepeatingContext), "{src}");
        }
    }

    #[test]
    fn g4_catches_helpers_multiple_sites_and_reentrant_main() {
        assert_eq!(
            g4("fn helper() -> Tokens { Tokens::new() } fn main() { helper(); helper(); }"),
            Some(R::MintOutsideMain)
        );
        assert_eq!(
            g4("static T: Tokens = Tokens::new();"),
            Some(R::MintOutsideMain)
        );
        assert_eq!(
            g4("fn main() { let a = Tokens::new(); let b = Tokens::new(); }"),
            Some(R::MultipleMintSites)
        );
        assert_eq!(
            g4("fn main() { let _t = Tokens::new(); if again() { main(); } }"),
            Some(R::ReentrantMain)
        );
        assert_eq!(
            g4("fn main() { let _t = Tokens::new(); let m = main; m(); }"),
            Some(R::ReentrantMain)
        );
        assert_eq!(
            g4("use self::main as entry; fn main() { let _t = Tokens::new(); entry(); }"),
            Some(R::ReentrantMain)
        );
        assert_eq!(
            g4("#[tokio::main] fn main() { let _t = Tokens::new(); }"),
            None
        );
    }

    #[test]
    fn g4_honors_ghost_token_ctor_attribute_including_cfg_attr() {
        let src = "impl Vault { #[ghost_token_ctor] fn issue() -> Self { Vault } } fn main() { let f = Vault::issue; }";
        assert_eq!(
            reason(check_fndef_ghost_token_coercion_source(src, &[])),
            Some(R::FnDefValueCoercion)
        );
        let src = "impl Vault { #[cfg_attr(feature = \"ghost\", ghost_token_ctor)] fn issue() -> Self { Vault } } fn main() { loop { Vault::issue(); } }";
        assert_eq!(
            reason(check_fndef_ghost_token_coercion_source(src, &[])),
            Some(R::MintInRepeatingContext)
        );
        let src = "#[ghost_token_ctor] fn mint() -> Tok { Tok } fn main() { let f = mint; }";
        assert_eq!(
            reason(check_fndef_ghost_token_coercion_source(src, &[])),
            Some(R::FnDefValueCoercion)
        );
    }

    #[test]
    fn g4_ignores_strings_comments_and_methods() {
        assert_eq!(
            g4("fn main() { let s = \"Tokens::new\"; /* Tokens::new */ let _t = Tokens::new(); }"),
            None
        );
        assert_eq!(
            g4("fn main() { let _t = Tokens::new(); x.new(); Other::new(); }"),
            None
        );
    }

    // --- Guard 5 --------------------------------------------------------------

    #[test]
    fn g5_descriptor_matches_lean_guard() {
        let base = ExternalTypeDropDescriptor {
            external_type_specification: true,
            ..Default::default()
        };
        assert!(check_external_type_drop_omission(&base).is_ok());
        let cases = [
            (
                ExternalTypeDropDescriptor {
                    external_body: true,
                    has_drop_impl: true,
                    models_drop: true,
                    ..base
                },
                R::ExternalBodyWithDrop,
            ),
            (
                ExternalTypeDropDescriptor {
                    external_body: true,
                    opaque_foreign_field: true,
                    models_drop: true,
                    ..base
                },
                R::ExternalBodyWithDrop,
            ),
            (
                ExternalTypeDropDescriptor {
                    has_drop_impl: true,
                    ..base
                },
                R::UnmodeledDropImpl,
            ),
            (
                ExternalTypeDropDescriptor {
                    has_drop_impl: true,
                    models_drop: true,
                    no_drop_glue: true,
                    ..base
                },
                R::ContradictoryDropDeclaration,
            ),
            (
                ExternalTypeDropDescriptor {
                    opaque_foreign_field: true,
                    ..base
                },
                R::UnmodeledOpaqueField,
            ),
        ];
        for (d, r) in cases {
            assert_eq!(
                check_external_type_drop_omission(&d).map_err(|v| v.reason),
                Err(r)
            );
        }
        assert!(
            check_external_type_drop_omission(&ExternalTypeDropDescriptor {
                external_body: true,
                opaque_foreign_field: true,
                no_drop_glue: true,
                ..base
            })
            .is_ok()
        );
        assert!(
            check_external_type_drop_omission(&ExternalTypeDropDescriptor {
                has_drop_impl: true,
                models_drop: true,
                ..base
            })
            .is_ok()
        );
    }

    #[test]
    fn g5_rejects_external_body_even_with_models_drop() {
        let src = "#[verifier::external_type_specification] #[verifier::external_body] #[models_drop] pub struct ExVec<T>(Vec<T>);";
        assert_eq!(g5(src), Some(R::ExternalBodyWithDrop));
        let src = "#[cfg_attr(verus, verifier::external_type_specification)] #[cfg_attr(verus, verifier::external_body)] pub struct ExFile(std::fs::File);";
        assert_eq!(g5(src), Some(R::ExternalBodyWithDrop));
        let src = "struct Guard; impl Drop for Guard { fn drop(&mut self) {} } #[verifier::external_type_specification] #[verifier::external_body] #[no_drop_glue] struct ExGuard(Guard);";
        assert_eq!(g5(src), Some(R::ExternalBodyWithDrop));
    }

    #[test]
    fn g5_fails_closed_on_unmodeled_drop_and_opaque_fields() {
        assert_eq!(
            g5("#[verifier::external_type_specification] pub struct ExFile(std::fs::File);"),
            Some(R::UnmodeledOpaqueField)
        );
        assert_eq!(
            g5(
                "#[verifier::external_type_specification] #[has_drop_impl] #[no_drop_glue] struct ExG(u8);"
            ),
            Some(R::ContradictoryDropDeclaration)
        );
        assert_eq!(
            g5("#[verifier::external_type_specification] #[has_drop_impl] struct ExG(u8);"),
            Some(R::UnmodeledDropImpl)
        );
        assert_eq!(
            g5(
                "#[verifier::external_type_specification] #[cfg_attr(verus, models_drop)] struct ExF(File);"
            ),
            Some(R::UnmodeledOpaqueField)
        );
        assert_eq!(
            g5(
                "#[verifier::external_type_specification] #[cfg_attr(verus, no_drop_glue)] struct ExF(File);"
            ),
            Some(R::UnmodeledOpaqueField)
        );
        assert_eq!(
            g5("#[verifier::external_type_specification] struct ExM { inner: HashMap<K, V> }"),
            Some(R::UnmodeledOpaqueField)
        );
    }

    #[test]
    fn g5_accepts_modeled_or_glue_free_types() {
        assert_eq!(
            g5(
                "#[verifier::external_type_specification] #[models_drop] pub struct ExFile(std::fs::File);"
            ),
            None
        );
        assert_eq!(
            g5(
                "#[verifier::external_type_specification] #[no_drop_glue] pub struct ExId(foreign::Id);"
            ),
            None
        );
        assert_eq!(
            g5(
                "#[verifier::external_type_specification] #[verifier::external_body] pub struct ExPair(u8, (u16, [u32; 4]), &'static str, *const u8, PhantomData<T>);"
            ),
            None
        );
        assert_eq!(
            g5("#[verifier::external_body] pub struct NotAnExternalType(std::fs::File);"),
            None
        );
    }

    // --- Guard 6a -------------------------------------------------------------

    #[test]
    fn g6a_descriptor_matches_lean_guard() {
        assert!(check_assumption_polarity(&AssumptionPolarityDescriptor::default()).is_ok());
        let cases = [
            (
                AssumptionPolarityDescriptor {
                    positive: 1,
                    ..Default::default()
                },
                R::AssumptionPositive,
            ),
            (
                AssumptionPolarityDescriptor {
                    negated_antecedent: 1,
                    ..Default::default()
                },
                R::AssumptionNegatedAntecedent,
            ),
            (
                AssumptionPolarityDescriptor {
                    iff: 1,
                    ..Default::default()
                },
                R::AssumptionInIff,
            ),
            (
                AssumptionPolarityDescriptor {
                    if_condition: 1,
                    ..Default::default()
                },
                R::AssumptionInIfCondition,
            ),
            (
                AssumptionPolarityDescriptor {
                    unclean_leaf: 1,
                    ..Default::default()
                },
                R::AssumptionUncleanLeaf,
            ),
        ];
        for (d, r) in cases {
            assert_eq!(check_assumption_polarity(&d).map_err(|v| v.reason), Err(r));
        }
    }

    #[test]
    fn g6a_expression_polarity_rust_dialect() {
        use Polarity::*;
        use SourceDialect::Rust;
        assert_eq!(expr("assumes_hold ==> x > 0", Rust, Positive), None);
        assert_eq!(expr("(assumes_hold && y) ==> x > 0", Rust, Positive), None);
        assert_eq!(expr("!assumes_hold || x > 0", Rust, Positive), None);
        assert_eq!(expr("assumes_hold() ==> ok", Rust, Positive), None);
        assert_eq!(expr("assumes_hold", Rust, Negative), None);
        assert_eq!(
            expr("x > 0 && assumes_hold", Rust, Positive),
            Some(R::AssumptionPositive)
        );
        assert_eq!(
            expr("!assumes_hold ==> x > 0", Rust, Positive),
            Some(R::AssumptionNegatedAntecedent)
        );
        assert_eq!(
            expr("assumes_hold <==> x > 0", Rust, Positive),
            Some(R::AssumptionInIff)
        );
        assert_eq!(
            expr("if assumes_hold { x } else { true }", Rust, Positive),
            Some(R::AssumptionInIfCondition)
        );
        assert_eq!(
            expr("(assumes_hold == true) ==> x", Rust, Positive),
            Some(R::AssumptionUncleanLeaf)
        );
        assert_eq!(
            expr("f(assumes_hold) ==> x", Rust, Positive),
            Some(R::AssumptionUncleanLeaf)
        );
        assert_eq!(
            expr("!assumes_hold", Rust, Negative),
            Some(R::AssumptionPositive)
        );
    }

    #[test]
    fn g6a_expression_polarity_lean_dialect() {
        use Polarity::*;
        use SourceDialect::Lean;
        assert_eq!(expr("assumesHold → P", Lean, Positive), None);
        assert_eq!(
            expr("∀ (h : assumesHold) (x : Nat), P x", Lean, Positive),
            None
        );
        assert_eq!(expr("(P → assumesHold) → Q", Lean, Positive), None);
        assert_eq!(
            expr("(P → ¬ assumesHold) → Q", Lean, Positive),
            Some(R::AssumptionNegatedAntecedent)
        );
        assert_eq!(
            expr("∀ ⦃h : ¬ assumesHold⦄, P", Lean, Positive),
            Some(R::AssumptionNegatedAntecedent)
        );
        assert_eq!(
            expr("∃ h : assumesHold, P", Lean, Positive),
            Some(R::AssumptionPositive)
        );
        assert_eq!(
            expr("assumesHold ↔ P", Lean, Positive),
            Some(R::AssumptionInIff)
        );
        assert_eq!(
            expr("if assumesHold then P else Q", Lean, Positive),
            Some(R::AssumptionInIfCondition)
        );
        assert_eq!(
            expr("decide assumesHold = true → P", Lean, Positive),
            Some(R::AssumptionUncleanLeaf)
        );
        assert_eq!(
            expr("P ∧ ¬ ¬ assumesHold", Lean, Positive),
            Some(R::AssumptionPositive)
        );
        assert_eq!(
            expr("Verifrag.assumesHold → P -- assumesHold", Lean, Positive),
            None
        );
    }

    #[test]
    fn g6a_inlines_let_aliases_up_to_depth_eight() {
        use Polarity::*;
        use SourceDialect::{Lean, Rust};
        assert_eq!(expr("let h = assumes_hold; h ==> x", Rust, Positive), None);
        assert_eq!(
            expr("let h = assumes_hold; x && h", Rust, Positive),
            Some(R::AssumptionPositive)
        );
        assert_eq!(
            expr("let h = !assumes_hold; h ==> x", Rust, Positive),
            Some(R::AssumptionNegatedAntecedent)
        );
        assert_eq!(
            expr(
                "let a = assumes_hold; let b = a; let c = !b; c ==> x",
                Rust,
                Positive
            ),
            Some(R::AssumptionNegatedAntecedent)
        );
        assert_eq!(
            expr("let h := assumesHold\nh ∧ P", Lean, Positive),
            Some(R::AssumptionPositive)
        );
        assert_eq!(
            expr("let h = assumes_hold; let h = true; h", Rust, Positive),
            None
        );
        let deep = "let a1 = assumes_hold; let a2 = a1; let a3 = a2; let a4 = a3; let a5 = a4; let a6 = a5; let a7 = a6; let a8 = a7; let a9 = a8; a9";
        assert!(matches!(
            check_assumption_polarity_expr(deep, Rust, Positive),
            Err(PeerSoundnessGuardError::Scan(PeerScanError {
                kind: PeerScanErrorKind::AliasDepthExceeded,
                ..
            }))
        ));
    }

    #[test]
    fn g6a_source_scans_spec_attributes() {
        assert_eq!(
            g6a("#[spec(requires: assumes_hold, ensures: |r| r > 0)] fn f() -> u8 { 1 }"),
            None
        );
        assert_eq!(
            g6a("#[spec(ensures: |r| r > 0 && assumes_hold)] fn f() -> u8 { 1 }"),
            Some(R::AssumptionPositive)
        );
        assert_eq!(
            g6a("#[ensures(assumes_hold)] fn f() {}"),
            Some(R::AssumptionPositive)
        );
        assert_eq!(
            g6a("#[requires(!assumes_hold)] fn f() {}"),
            Some(R::AssumptionPositive)
        );
        assert_eq!(
            g6a("#[spec(ensures: [r > 0, assumes_hold <==> r == 1])] fn f() -> u8 { 1 }"),
            Some(R::AssumptionInIff)
        );
        assert_eq!(
            g6a("#[cfg_attr(verify, ensures(assumes_hold))] fn f() {}"),
            Some(R::AssumptionPositive)
        );
        assert_eq!(
            g6a("// #[ensures(assumes_hold)]\nconst S: &str = \"#[ensures(assumes_hold)]\";"),
            None
        );
    }

    #[test]
    fn g6a_lean_source_scans_binders_and_types() {
        assert_eq!(
            reason(check_assumption_polarity_lean_source(
                "theorem t (h : assumesHold) : P := by simp"
            )),
            None
        );
        assert_eq!(
            reason(check_assumption_polarity_lean_source(
                "theorem t : assumesHold → P := by simp"
            )),
            None
        );
        assert_eq!(
            reason(check_assumption_polarity_lean_source(
                "theorem t : P ∧ assumesHold := by simp"
            )),
            Some(R::AssumptionPositive)
        );
        assert_eq!(
            reason(check_assumption_polarity_lean_source(
                "theorem t (h : ¬ assumesHold) : P := by simp"
            )),
            Some(R::AssumptionNegatedAntecedent)
        );
        assert_eq!(
            reason(check_assumption_polarity_lean_source(
                "variable (h : assumesHold ↔ Q)\ntheorem t : P := trivial"
            )),
            Some(R::AssumptionInIff)
        );
        assert_eq!(
            reason(check_assumption_polarity_lean_source(
                "/- theorem t : assumesHold := x -/ def ok : Nat := 1"
            )),
            None
        );
    }

    // --- Guard 6b -------------------------------------------------------------

    #[test]
    fn g6b_descriptor_matches_lean_guard() {
        let base = StructSealingDescriptor {
            has_invariant: true,
            ..Default::default()
        };
        assert!(check_struct_sealing(&base).is_ok());
        let cases = [
            (
                StructSealingDescriptor {
                    pub_fields: true,
                    ..base
                },
                R::InvariantPubField,
            ),
            (
                StructSealingDescriptor {
                    derives_default: true,
                    ..base
                },
                R::InvariantDeriveDefault,
            ),
            (
                StructSealingDescriptor {
                    default_impl: true,
                    ..base
                },
                R::InvariantDefaultImpl,
            ),
            (
                StructSealingDescriptor {
                    raw_public_constructor: true,
                    ..base
                },
                R::InvariantRawPublicConstructor,
            ),
        ];
        for (d, r) in cases {
            assert_eq!(check_struct_sealing(&d).map_err(|v| v.reason), Err(r));
        }
        assert!(
            check_struct_sealing(&StructSealingDescriptor {
                pub_fields: true,
                ..Default::default()
            })
            .is_ok()
        );
    }

    #[test]
    fn g6b_accepts_sealed_structs_with_smart_constructors() {
        let src = r#"
            #[invariant(self.lo <= self.hi)]
            pub struct Range { lo: u32, hi: u32 }
            impl Range {
                #[smart_constructor]
                pub fn new(lo: u32, hi: u32) -> Option<Self> {
                    if lo <= hi { Some(Range { lo, hi }) } else { None }
                }
                fn raw(lo: u32, hi: u32) -> Self { Self { lo, hi } }
                pub fn lo(&self) -> u32 { let Range { lo, .. } = self; *lo }
                pub fn width(&self) -> u32 { match self { Self { lo, hi } => hi - lo } }
            }
        "#;
        assert_eq!(g6b(src), None);
    }

    #[test]
    fn g6b_catches_unsealed_invariant_structs() {
        assert_eq!(
            g6b("#[invariant(self.lo <= self.hi)] pub struct R { pub lo: u32, hi: u32 }"),
            Some(R::InvariantPubField)
        );
        assert_eq!(
            g6b("#[invariant(self.0 > 0)] pub struct P(pub(crate) u32);"),
            Some(R::InvariantPubField)
        );
        assert_eq!(
            g6b(
                "#[derive(Clone, Default)] #[invariant(self.lo <= self.hi)] struct R { lo: u32, hi: u32 }"
            ),
            Some(R::InvariantDeriveDefault)
        );
        assert_eq!(
            g6b(
                "#[invariant(x)] #[cfg_attr(test, derive(core::default::Default))] struct R { lo: u32 }"
            ),
            Some(R::InvariantDeriveDefault)
        );
        assert_eq!(
            g6b(
                "#[invariant(self.lo <= self.hi)] struct R { lo: u32, hi: u32 } impl Default for R { fn default() -> Self { R { lo: 1, hi: 0 } } }"
            ),
            Some(R::InvariantDefaultImpl)
        );
        assert_eq!(
            g6b(
                "#[invariant(self.lo <= self.hi)] struct R { lo: u32, hi: u32 } impl R { pub fn mk(lo: u32, hi: u32) -> Self { Self { lo, hi } } }"
            ),
            Some(R::InvariantRawPublicConstructor)
        );
        assert_eq!(
            g6b(
                "#[invariant(self.lo <= self.hi)] struct R { lo: u32, hi: u32 } impl From<(u32, u32)> for R { fn from(p: (u32, u32)) -> Self { R { lo: p.0, hi: p.1 } } }"
            ),
            Some(R::InvariantRawPublicConstructor)
        );
        assert_eq!(
            g6b("#[invariant(self.0 > 0)] struct P(u32); pub fn make() -> P { P(0) }"),
            Some(R::InvariantRawPublicConstructor)
        );
        assert_eq!(
            g6b("#[invariant(self.0 > 0)] struct P(u32); impl P { pub const ZERO: P = P(0); }"),
            Some(R::InvariantRawPublicConstructor)
        );
        assert_eq!(
            g6b(
                "#[invariant(x)] struct R { lo: u32 } impl R { #[cfg_attr(test, smart_constructor)] pub fn mk() -> Self { R { lo: 0 } } }"
            ),
            Some(R::InvariantRawPublicConstructor)
        );
        assert_eq!(
            g6b("#[cfg_attr(verus, invariant(self.lo > 0))] pub struct R { pub lo: u32 }"),
            Some(R::InvariantPubField)
        );
    }

    #[test]
    fn g6b_catches_transitive_private_forwarders() {
        let src = r#"
            #[invariant(self.lo <= self.hi)]
            pub struct R { lo: u32, hi: u32 }
            impl R {
                fn raw(lo: u32, hi: u32) -> Self { Self { lo, hi } }
                fn relay(lo: u32, hi: u32) -> Self { Self::raw(lo, hi) }
                pub fn mk(lo: u32, hi: u32) -> Self { Self::relay(hi, lo) }
            }
        "#;
        assert_eq!(g6b(src), Some(R::InvariantRawPublicConstructor));
        let gated = r#"
            #[invariant(self.lo <= self.hi)]
            pub struct R { lo: u32, hi: u32 }
            impl R {
                #[smart_constructor]
                fn checked(lo: u32, hi: u32) -> Option<Self> { if lo <= hi { Some(Self { lo, hi }) } else { None } }
                pub fn mk(lo: u32, hi: u32) -> Option<Self> { Self::checked(lo, hi) }
            }
        "#;
        assert_eq!(g6b(gated), None);
    }

    #[test]
    fn g3_comma_separated_clause_lists_are_checked_per_clause() {
        assert_eq!(
            g3("#[trusted] #[ensures(false,)] fn f() -> u8;"),
            Some(R::EnsuresFalseOnReturningFn)
        );
        assert_eq!(
            g3("#[trusted] #[ensures(r > 0, false)] fn f() -> u8;"),
            Some(R::EnsuresFalseOnReturningFn)
        );
        assert_eq!(
            g3("#[trusted] #[ensures(r > 0, r < 9)] fn f() -> u8;"),
            None
        );
        assert_eq!(
            g3("#[trusted] #[ensures(|a, b| false)] fn f() -> u8;"),
            Some(R::EnsuresFalseOnReturningFn)
        );
        assert_eq!(
            g3("#[trusted] #[ensures(|a, b| a < b)] fn f() -> u8;"),
            None
        );
        assert_eq!(
            g6a("#[ensures(r > 0, assumes_hold)] fn f() -> u8 { 1 }"),
            Some(R::AssumptionPositive)
        );
        assert_eq!(g6a("#[requires(x > 0, assumes_hold)] fn f(x: u8) {}"), None);
    }

    #[test]
    fn a1_verus_signature_clauses_are_scanned() {
        let src = "verus! { #[verifier::external_body] pub fn read(p: *const u8) -> (r: u8) ensures false, { unimplemented!() } }";
        assert_eq!(g3(src), Some(R::EnsuresFalseOnReturningFn));
        let src =
            "#[verifier::external_body] fn read() -> (r: u8) requires x > 0 ensures r > 0, false;";
        assert_eq!(g3(src), Some(R::EnsuresFalseOnReturningFn));
        assert_eq!(
            g3("#[verifier::external_body] fn halt() -> (r: !) ensures false;"),
            None
        );
        assert_eq!(
            g3("#[verifier::external_body] fn read() -> (r: u8) requires false ensures false;"),
            None
        );
        assert_eq!(
            g3("#[verifier::external_body] fn read() -> (r: u8) ensures r > 0;"),
            None
        );
        assert_eq!(
            g6a("fn f(x: u8) -> (r: u8) requires assumes_hold ensures r > x { x }"),
            None
        );
        assert_eq!(
            g6a("fn f(x: u8) -> (r: u8) ensures r > x, assumes_hold { x }"),
            Some(R::AssumptionPositive)
        );
        assert_eq!(
            g6a("fn f(x: u8) -> (r: u8) requires !assumes_hold { x }"),
            Some(R::AssumptionPositive)
        );
    }

    #[test]
    fn a1_g6b_unchecked_constructor_traits_and_raw_materializers() {
        let inv = "#[invariant(self.0 > 0)] pub struct P(u32);";
        for extra in [
            "#[derive(serde::Deserialize)] #[invariant(self.0 > 0)] pub struct Q(u32);",
            "#[invariant(self.0 > 0)] #[cfg_attr(feature = \"z\", derive(zerocopy::FromBytes))] pub struct Q(u32);",
            "#[derive(Clone, bytemuck::Pod, bytemuck::Zeroable)] #[invariant(self.0 > 0)] pub struct Q(u32);",
        ] {
            assert_eq!(
                g6b(extra),
                Some(R::InvariantUncheckedConstructorTrait),
                "{extra}"
            );
        }
        let manual = std::format!("{inv} unsafe impl bytemuck::Zeroable for P {{}}");
        assert_eq!(g6b(&manual), Some(R::InvariantUncheckedConstructorTrait));
        let t = std::format!(
            "{inv} impl P {{ pub fn zero() -> Self {{ unsafe {{ core::mem::zeroed() }} }} }}"
        );
        assert_eq!(g6b(&t), Some(R::InvariantRawPublicConstructor));
        let t = std::format!(
            "{inv} pub fn forge(x: u32) -> P {{ unsafe {{ core::mem::transmute(x) }} }}"
        );
        assert_eq!(g6b(&t), Some(R::InvariantRawPublicConstructor));
        let t = std::format!(
            "{inv} fn helper() -> P {{ unsafe {{ core::mem::transmute(0u32) }} }} pub fn mk() -> P {{ helper() }}"
        );
        assert_eq!(g6b(&t), Some(R::InvariantRawPublicConstructor));
        let ok = std::format!(
            "{inv} pub fn bits(f: f32) -> u32 {{ unsafe {{ core::mem::transmute(f) }} }}"
        );
        assert_eq!(g6b(&ok), None);
        assert_eq!(
            g6b(
                "#[derive(Clone, Copy, PartialEq, Debug, Hash)] #[invariant(self.0 > 0)] pub struct Q(u32);"
            ),
            None
        );
        assert_eq!(
            check_struct_sealing(&StructSealingDescriptor {
                has_invariant: true,
                unchecked_constructor_trait: true,
                ..Default::default()
            })
            .map_err(|v| v.reason),
            Err(R::InvariantUncheckedConstructorTrait)
        );
    }

    // --- Combined -------------------------------------------------------------

    #[test]
    fn combined_scanner_and_verdicts() {
        let clean =
            "#[trusted] #[ensures(false)] fn abort() -> !; fn main() { let _t = Tokens::new(); }";
        assert!(check_peer_soundness_guards_source(clean, TOKENS).is_ok());
        assert!(
            peer_guard_verdicts(clean, TOKENS)
                .iter()
                .all(|v| v.is_pass())
        );
        let dirty =
            "#[trusted] #[ensures(false)] fn read() -> u8; fn main() { loop { Tokens::new(); } }";
        let v = peer_guard_verdicts(dirty, TOKENS);
        assert_eq!(
            v[0],
            PeerSpecGuardVerdict::Violation(PeerSpecGuardClass::UnsatisfiableExternEnsures)
        );
        assert_eq!(
            v[1],
            PeerSpecGuardVerdict::Violation(PeerSpecGuardClass::FnDefGhostTokenCoercion)
        );
        assert!(v[2].is_pass() && v[3].is_pass());
        let err = check_peer_soundness_guards_source(dirty, TOKENS).unwrap_err();
        assert_eq!(
            err.violation().map(|x| x.guard()),
            Some(PeerSpecGuardClass::UnsatisfiableExternEnsures)
        );
    }

    // --- Pass B1 red-team regression tests ------------------------------------

    #[test]
    fn lexer_handles_escaped_quotes_and_backslashes() {
        let src = r#"
            const Q: char = '\'';
            const BS: char = '\\';
            const BQ: u8 = b'\'';
            const BBS: u8 = b'\\';
            const U: char = '\u{10FFFF}';
            #[trusted] #[ensures(false)] fn read_after_quotes() -> u8;
        "#;
        assert_eq!(g3(src), Some(R::EnsuresFalseOnReturningFn));
    }

    #[test]
    fn g3_catches_colon_bool_qualifiers_and_hex_float_requires_bypass() {
        // `anneal_spec` colon syntax `trusted: true`, `assumed: true`, `external_body: true`.
        assert_eq!(
            g3("#[spec(trusted: true, ensures: |r| false)] fn f() -> u8 { 0 }"),
            Some(R::EnsuresFalseOnReturningFn)
        );
        assert_eq!(
            g3("#[spec(assumed: true, ensures: false)] fn f() -> u8 { 0 }"),
            Some(R::EnsuresFalseOnReturningFn)
        );
        assert_eq!(
            g3("#[spec(external_body: true, ensures: false)] fn f() -> u8 { 0 }"),
            Some(R::EnsuresFalseOnReturningFn)
        );
        assert_eq!(
            g3("#[spec(trusted: false, ensures: false)] fn f() -> u8 { loop {} }"),
            None
        );
        // Hex / binary / float literals in `requires` must never falsely fold to `false`.
        assert_eq!(
            g3("#[trusted] #[requires(0x0 != 0x1)] #[ensures(false)] fn read() -> u8;"),
            Some(R::EnsuresFalseOnReturningFn)
        );
        assert_eq!(
            g3("#[trusted] #[requires(0b0 != 0b1)] #[ensures(false)] fn read() -> u8;"),
            Some(R::EnsuresFalseOnReturningFn)
        );
        assert_eq!(
            g3("#[trusted] #[requires(1.0 != 1.5)] #[ensures(false)] fn read() -> u8;"),
            Some(R::EnsuresFalseOnReturningFn)
        );
        // Genuine hex contradiction in `ensures` is caught.
        assert_eq!(
            g3("#[trusted] #[ensures(0x0 == 0x1)] fn read() -> u8;"),
            Some(R::EnsuresFalseOnReturningFn)
        );
        // Constant implication / iff / bool equality / if-const false clauses.
        for clause in [
            "true ==> false",
            "true <==> false",
            "true == false",
            "false != false",
            "if true { false } else { true }",
        ] {
            let src = std::format!("#[trusted] #[ensures({clause})] fn read() -> u8;");
            assert_eq!(g3(&src), Some(R::EnsuresFalseOnReturningFn), "{clause}");
        }
    }

    #[test]
    fn g3_rejects_const_generic_scope_escape_and_shadowed_infallible() {
        // `{ 1 }` inside `impl<...>` must not prematurely close `#[extern_spec]` scope.
        let src =
            "#[extern_spec] impl<T: Trait<{ 1 }>> Foo<T> { #[ensures(false)] fn read() -> u8; }";
        assert_eq!(g3(src), Some(R::EnsuresFalseOnReturningFn));
        // Local `struct Infallible(u8)` must not spoof `core::convert::Infallible`.
        let shadowed =
            "struct Infallible(u8); #[trusted] #[ensures(false)] fn read() -> Infallible;";
        assert_eq!(g3(shadowed), Some(R::EnsuresFalseOnReturningFn));
        let shadowed_type =
            "type Infallible = u8; #[trusted] #[ensures(false)] fn read() -> Infallible;";
        assert_eq!(g3(shadowed_type), Some(R::EnsuresFalseOnReturningFn));
        let qualified = "struct Infallible(u8); #[trusted] #[ensures(false)] fn abort() -> core::convert::Infallible;";
        assert_eq!(g3(qualified), None);
    }

    #[test]
    fn g4_catches_b1_red_team_bypasses() {
        // UFCS `<Self as Trait>::new` and `<Self>::new` inside `impl Tokens`.
        assert_eq!(
            g4("impl Tokens { fn leak() { let f = <Self as Mint>::new; } }"),
            Some(R::FnDefValueCoercion)
        );
        assert_eq!(
            g4("impl Tokens { fn leak() { <Self>::new(); } }"),
            Some(R::MintOutsideMain)
        );
        // Closure behind `&` / `&&`.
        assert_eq!(
            g4("fn main() { let f: &dyn Fn() -> Tokens = &|| Tokens::new(); f(); f(); }"),
            Some(R::MintInRepeatingContext)
        );
        assert_eq!(
            g4("fn main() { let f = &&|_| Tokens::new(); }"),
            Some(R::MintInRepeatingContext)
        );
        // `while let Pat { a }` / `for Pat { a } in` / `while { cond } { body }`.
        assert_eq!(
            g4("fn main() { while let Foo { a } = next() { Tokens::new(); } }"),
            Some(R::MintInRepeatingContext)
        );
        assert_eq!(
            g4("fn main() { for Foo { a } in iter { Tokens::new(); } }"),
            Some(R::MintInRepeatingContext)
        );
        assert_eq!(
            g4("fn main() { while { cond() } { Tokens::new(); } }"),
            Some(R::MintInRepeatingContext)
        );
        // Closure return type containing `[T; { 1 }]` must not desync delimiters.
        assert_eq!(
            g4("fn main() { let f = || -> [Tokens; { 1 }] { [Tokens::new()] }; }"),
            Some(R::MintInRepeatingContext)
        );
        // `use crate::Tokens::{*};` braced glob import.
        assert_eq!(
            g4("use crate::Tokens::{*}; fn main() { let f = new; }"),
            Some(R::FnDefValueCoercion)
        );
        // `fn main` inside `impl` / `mod` is NOT the crate entry point.
        assert_eq!(
            g4(
                "struct S; impl S { pub fn main(&self) { let _t = Tokens::new(); } } fn c(s: &S) { s.main(); s.main(); }"
            ),
            Some(R::MintOutsideMain)
        );
        assert_eq!(
            g4("mod sub { pub fn main() { let _t = Tokens::new(); } }"),
            Some(R::MintOutsideMain)
        );
        // `#[ghost_token_ctor] pub(crate) fn issue()` must survive `)` in `pub(crate)`.
        let pub_crate = "impl Vault { #[ghost_token_ctor] pub(crate) fn issue() -> Self { Vault } } fn main() { let f = Vault::issue; }";
        assert_eq!(
            reason(check_fndef_ghost_token_coercion_source(pub_crate, &[])),
            Some(R::FnDefValueCoercion)
        );
    }

    #[test]
    fn g5_catches_where_fn_bound_and_handles_transparent_refs_to_drop_types() {
        // `where T: Fn(u8)` must not be mistaken for a tuple struct body!
        let where_fn = "#[verifier::external_type_specification] #[verifier::external_body] pub struct Ex<T> where T: Fn(u8) { f: std::fs::File }";
        assert_eq!(g5(where_fn), Some(R::ExternalBodyWithDrop));
        // Transparent reference/pointer to a `Drop` type does not itself run `Drop`.
        let ref_to_drop = "struct Guard; impl Drop for Guard { fn drop(&mut self) {} } #[verifier::external_type_specification] #[no_drop_glue] struct ExRef<'a>(&'a Guard);";
        assert_eq!(g5(ref_to_drop), None);
        // Local `struct PhantomData` with `Drop` is NOT transparent.
        let fake_phantom = "struct PhantomData<T>(T); impl<T> Drop for PhantomData<T> { fn drop(&mut self) {} } #[verifier::external_type_specification] #[verifier::external_body] struct ExP<T>(PhantomData<T>);";
        assert_eq!(g5(fake_phantom), Some(R::ExternalBodyWithDrop));
        // Fieldless enum with `#[allow(...)]` on a variant has no payload fields.
        let fieldless_enum = "#[verifier::external_type_specification] #[verifier::external_body] enum ExTag { #[allow(dead_code)] A, B }";
        assert_eq!(g5(fieldless_enum), None);
    }

    #[test]
    fn g6a_catches_if_before_implication_and_lean_match_and_abbrev() {
        use Polarity::*;
        use SourceDialect::{Lean, Rust};
        // `if cond { !assumes_hold } else { true } ==> Q` puts `!assumes_hold` in antecedent.
        assert_eq!(
            expr(
                "if cond { !assumes_hold } else { true } ==> Q",
                Rust,
                Positive
            ),
            Some(R::AssumptionNegatedAntecedent)
        );
        // Lean dependent arrow `(h : assumesHold) → P` is clean; negated is rejected.
        assert_eq!(expr("(h : assumesHold) → P", Lean, Positive), None);
        assert_eq!(
            expr("(h : ¬ assumesHold) → P", Lean, Positive),
            Some(R::AssumptionNegatedAntecedent)
        );
        assert_eq!(expr("Π (h : assumesHold), P", Lean, Positive), None);
        assert_eq!(
            expr("Π (h : ¬ assumesHold), P", Lean, Positive),
            Some(R::AssumptionNegatedAntecedent)
        );
        // `match ... with | 0 => assumesHold` inside a theorem type must not truncate at `|`.
        assert_eq!(
            reason(check_assumption_polarity_lean_source(
                "theorem t (x : Nat) : match x with | 0 => assumesHold | _ => True := trivial"
            )),
            Some(R::AssumptionUncleanLeaf)
        );
        // Unannotated `abbrev` and equation-style `def` bodies are checked.
        assert_eq!(
            reason(check_assumption_polarity_lean_source(
                "abbrev Bad := assumesHold"
            )),
            Some(R::AssumptionPositive)
        );
        assert_eq!(
            reason(check_assumption_polarity_lean_source(
                "def f : Nat → Prop | 0 => assumesHold | _ => True"
            )),
            Some(R::AssumptionPositive)
        );
    }

    #[test]
    fn g6b_catches_aliases_turbofish_tuple_fn_coercion_const_taint_and_where_bounds() {
        // `where T: Fn(u32)` must not hide `{ pub x: T }`.
        assert_eq!(
            g6b("#[invariant(self.x > 0)] pub struct R<T> where T: Fn(u32) { pub x: T }"),
            Some(R::InvariantPubField)
        );
        // Type alias & `use ... as` alias leaks.
        assert_eq!(
            g6b(
                "#[invariant(self.0 > 0)] pub struct Pos(u32); type P = Pos; pub fn leak() -> P { P(0) }"
            ),
            Some(R::InvariantRawPublicConstructor)
        );
        assert_eq!(
            g6b(
                "#[invariant(self.0 > 0)] pub struct Pos(u32); type P = Pos; impl Default for P { fn default() -> Self { Self(0) } }"
            ),
            Some(R::InvariantDefaultImpl)
        );
        assert_eq!(
            g6b(
                "#[invariant(self.0 > 0)] pub struct Pos(u32); use self::Pos as P; impl P { pub fn leak() -> Self { Self(0) } }"
            ),
            Some(R::InvariantRawPublicConstructor)
        );
        // Turbofish raw construction.
        assert_eq!(
            g6b(
                "#[invariant(self.0 > 0)] pub struct Pos<T>(u32, core::marker::PhantomData<T>); pub fn leak<T>() -> Pos<T> { Pos::<T>(0, core::marker::PhantomData) }"
            ),
            Some(R::InvariantRawPublicConstructor)
        );
        // Tuple-struct constructor coerced as a function value.
        assert_eq!(
            g6b(
                "#[invariant(self.0 > 0)] pub struct Pos(u32); pub fn leak() -> fn(u32) -> Pos { Pos }"
            ),
            Some(R::InvariantRawPublicConstructor)
        );
        assert_eq!(
            g6b(
                "#[invariant(self.0 > 0)] pub struct Pos(u32); pub fn leak(x: u32) -> Pos { let mk = Pos; mk(x) }"
            ),
            Some(R::InvariantRawPublicConstructor)
        );
        // Tainted private helper called via turbofish or coerced as a fn value.
        assert_eq!(
            g6b(
                "#[invariant(self.0 > 0)] pub struct Pos(u32); impl Pos { fn raw<T>(x: u32) -> Self { Self(x) } pub fn leak(x: u32) -> Self { Self::raw::<()>(x) } }"
            ),
            Some(R::InvariantRawPublicConstructor)
        );
        assert_eq!(
            g6b(
                "#[invariant(self.0 > 0)] pub struct Pos(u32); impl Pos { fn raw(x: u32) -> Self { Self(x) } pub fn leak() -> fn(u32) -> Self { Self::raw } }"
            ),
            Some(R::InvariantRawPublicConstructor)
        );
        // Private `const` holding a raw construction leaked by a public fn.
        assert_eq!(
            g6b(
                "#[invariant(self.0 > 0)] pub struct Pos(u32); const BAD: Pos = Pos(0); pub fn leak() -> Pos { BAD }"
            ),
            Some(R::InvariantRawPublicConstructor)
        );
        // Const generic `{ 1 }` inside `impl` header must not drop `self_kind`.
        assert_eq!(
            g6b(
                "#[invariant(self.lo <= self.hi)] pub struct R<T> { lo: u32, hi: u32, _m: core::marker::PhantomData<T> } impl<T: Trait<{ 1 }>> R<T> { pub fn leak() -> Self { Self { lo: 1, hi: 0, _m: core::marker::PhantomData } } }"
            ),
            Some(R::InvariantRawPublicConstructor)
        );
    }

    #[test]
    fn a1_g4_generic_constructor_dispatch() {
        assert_eq!(
            g4("fn mk<T: Mint>() -> T { T::new() } fn main() { mk::<Tokens>(); mk::<Tokens>(); }"),
            Some(R::GenericConstructorDispatch)
        );
        assert_eq!(
            g4("fn main() { let v = Vec::<Tokens>::new(); let _t = Tokens::new(); }"),
            None
        );
        assert_eq!(
            check_fndef_ghost_token_coercion(&GhostTokenUsageDescriptor {
                generic_dispatches: 1,
                ..Default::default()
            })
            .map_err(|v| v.reason),
            Err(R::GenericConstructorDispatch)
        );
    }

    // --- Pass B2 red-team regression tests ------------------------------------

    #[test]
    fn b2_verus_sig_clauses_handle_quantifier_commas_and_braced_expressions() {
        // Multi-binder `forall|x, y|` must not split on the comma inside `|...|`.
        assert_eq!(
            g6a(
                "fn f() -> (r: u8) ensures forall|x: int, y: int| assumes_hold ==> x + y >= 0, { 0 }"
            ),
            None
        );
        assert_eq!(
            g6a("fn f() -> (r: u8) ensures forall|x: int, y: int| assumes_hold && x == y, { 0 }"),
            Some(R::AssumptionPositive)
        );
        // Braced `if` / block expressions inside Verus `ensures` must not truncate at `{`.
        assert_eq!(
            g3(
                "#[verifier::external_body] fn read(b: bool) -> (r: u8) ensures if b { false } else { false } { 0 }"
            ),
            Some(R::EnsuresFalseOnReturningFn)
        );
        assert_eq!(
            g3("#[verifier::external_body] fn read() -> (r: u8) ensures { false } { 0 }"),
            Some(R::EnsuresFalseOnReturningFn)
        );
        assert_eq!(
            g6a("fn f(b: bool) -> (r: u8) ensures if b { assumes_hold } else { true } { 0 }"),
            Some(R::AssumptionPositive)
        );
        assert_eq!(
            g6a("fn f() -> (r: u8) ensures { assumes_hold } { 0 }"),
            Some(R::AssumptionPositive)
        );
    }

    #[test]
    fn b2_g4_catches_turbofish_coercion_helper_and_type_inferred_generic_dispatch() {
        // Coercing generic dispatcher without `(` (`let f = mk::<Tokens>;`).
        assert_eq!(
            g4("fn mk<T: Mint>() -> T { T::new() } fn main() { let f = mk::<Tokens>; f(); f(); }"),
            Some(R::GenericConstructorDispatch)
        );
        // Associated generic helper (`Helper::<Tokens>::mk()`).
        assert_eq!(
            g4(
                "struct Helper<T>(PhantomData<T>); impl<T: Mint> Helper<T> { fn mk() -> T { T::new() } } fn main() { Helper::<Tokens>::mk(); }"
            ),
            Some(R::GenericConstructorDispatch)
        );
        // Type-inferred generic dispatch without any turbofish (`let a: Tokens = mk();`).
        assert_eq!(
            g4(
                "fn mk<T: Mint>() -> T { T::new() } fn main() { let a: Tokens = mk(); let b: Tokens = mk(); }"
            ),
            Some(R::GenericConstructorDispatch)
        );
        // Pure metadata intrinsics and std containers do NOT false-positive.
        assert_eq!(
            g4("fn main() { let _sz = core::mem::size_of::<Tokens>(); let _t = Tokens::new(); }"),
            None
        );
        assert_eq!(
            g4("fn main() { let _o = Option::<Tokens>::None; let _t = Tokens::new(); }"),
            None
        );
    }

    #[test]
    fn b2_g6a_catches_typed_lean_def_bodies_and_dependent_if_conditions() {
        assert_eq!(
            reason(check_assumption_polarity_lean_source(
                "abbrev Bad : Prop := assumesHold"
            )),
            Some(R::AssumptionPositive)
        );
        assert_eq!(
            reason(check_assumption_polarity_lean_source(
                "def badSpec (x : Nat) : Prop := x > 0 ∧ assumesHold"
            )),
            Some(R::AssumptionPositive)
        );
        assert_eq!(
            reason(check_assumption_polarity_lean_source(
                "def goodSpec (x : Nat) : Prop := assumesHold → x > 0"
            )),
            None
        );
        assert_eq!(
            expr(
                "if h : assumesHold then P else Q",
                SourceDialect::Lean,
                Polarity::Positive
            ),
            Some(R::AssumptionInIfCondition)
        );
    }

    #[test]
    fn b2_g6b_catches_closure_body_const_transmute_ptr_read_and_generic_cast_helper() {
        let inv = "#[invariant(self.0 > 0)] pub struct Pos(u32);";
        // Closure `|x| Pos(x)` must NOT be treated as a `|` OR-pattern!
        assert_eq!(
            g6b(&std::format!(
                "{inv} pub fn leak() -> Pos {{ (|x| Pos(x))(0) }}"
            )),
            Some(R::InvariantRawPublicConstructor)
        );
        assert_eq!(
            g6b(&std::format!(
                "{inv} pub fn leak(xs: &[u32]) -> Vec<Pos> {{ xs.iter().map(|&x| Pos(x)).collect() }}"
            )),
            Some(R::InvariantRawPublicConstructor)
        );
        // Genuine OR-patterns in `match` remain allowed.
        assert_eq!(
            g6b(&std::format!(
                "{inv} pub fn is_small(p: Pos) -> bool {{ match p {{ Pos(1) | Pos(2) => true, _ => false }} }}"
            )),
            None
        );
        // `pub const` / private `const` raw materialization via `transmute`.
        assert_eq!(
            g6b(&std::format!(
                "{inv} pub const BAD: Pos = unsafe {{ core::mem::transmute(0u32) }};"
            )),
            Some(R::InvariantRawPublicConstructor)
        );
        assert_eq!(
            g6b(&std::format!(
                "{inv} const BAD: Pos = unsafe {{ core::mem::transmute(0u32) }}; pub fn leak() -> Pos {{ BAD }}"
            )),
            Some(R::InvariantRawPublicConstructor)
        );
        // `core::ptr::read` and `core::ptr::read_volatile` materialization.
        assert_eq!(
            g6b(&std::format!(
                "{inv} pub fn forge(p: *const Pos) -> Pos {{ unsafe {{ core::ptr::read(p) }} }}"
            )),
            Some(R::InvariantRawPublicConstructor)
        );
        // Generic raw-materializing helper not naming `Pos` in its own signature.
        assert_eq!(
            g6b(&std::format!(
                "{inv} fn cast<A, B>(a: A) -> B {{ unsafe {{ core::mem::transmute_copy(&a) }} }} pub fn forge(x: u32) -> Pos {{ cast(x) }}"
            )),
            Some(R::InvariantRawPublicConstructor)
        );
        // Calling the same generic helper on unrelated types does NOT false-positive.
        assert_eq!(
            g6b(&std::format!(
                "{inv} fn cast<A, B>(a: A) -> B {{ unsafe {{ core::mem::transmute_copy(&a) }} }} pub fn bits(f: f32) -> u32 {{ cast(f) }}"
            )),
            None
        );
    }

    #[test]
    fn a2_g6b_mutable_field_escape() {
        let inv = "#[invariant(self.lo <= self.hi)] pub struct R { lo: u32, hi: u32 } ";
        let leak = std::format!(
            "{inv} impl R {{ pub fn lo_mut(&mut self) -> &mut u32 {{ &mut self.lo }} }}"
        );
        assert_eq!(g6b(&leak), Some(R::InvariantMutableFieldEscape));
        let leak = std::format!(
            "{inv} impl core::ops::DerefMut for R {{ fn deref_mut(&mut self) -> &mut u32 {{ &mut self.hi }} }}"
        );
        assert_eq!(g6b(&leak), Some(R::InvariantMutableFieldEscape));
        let private =
            std::format!("{inv} impl R {{ fn lo_mut(&mut self) -> &mut u32 {{ &mut self.lo }} }}");
        assert_eq!(g6b(&private), None);
        let shared = std::format!("{inv} impl R {{ pub fn lo(&self) -> &u32 {{ &self.lo }} }}");
        assert_eq!(g6b(&shared), None);
        assert_eq!(
            check_struct_sealing(&StructSealingDescriptor {
                has_invariant: true,
                mutable_field_escape: true,
                ..Default::default()
            })
            .map_err(|v| v.reason),
            Err(R::InvariantMutableFieldEscape)
        );
    }

    #[test]
    fn a2_g3_syntactic_contradictions() {
        assert_eq!(
            g3("#[trusted] #[ensures(result == 1 && result == 2)] fn f() -> u8;"),
            Some(R::EnsuresFalseOnReturningFn)
        );
        assert_eq!(
            g3("#[trusted] #[ensures(x != x)] fn f(x: u8) -> u8;"),
            Some(R::EnsuresFalseOnReturningFn)
        );
        assert_eq!(
            g3("#[trusted] #[ensures(r.len() < r.len())] fn f() -> Vec<u8>;"),
            Some(R::EnsuresFalseOnReturningFn)
        );
        assert_eq!(
            g3("#[spec(trusted, ensures: |r| r > 0 && r == 3 && r == 0x4)] fn f() -> u8;"),
            Some(R::EnsuresFalseOnReturningFn)
        );
        assert_eq!(
            g3("#[spec(trusted, ensures: |r| r == 3 && r == 0x3)] fn f() -> u8;"),
            None
        );
        assert_eq!(
            g3("#[trusted] #[ensures(result == 1 && other == 2)] fn f() -> u8;"),
            None
        );
        assert_eq!(
            g3("#[trusted] #[ensures(result == 1 || result == 2)] fn f() -> u8;"),
            None
        );
        assert_eq!(
            g3("#[trusted] #[ensures(r == 3 && r == 3)] fn f() -> u8;"),
            None
        );
        assert_eq!(g3("#[trusted] #[ensures(x <= x)] fn f(x: u8) -> u8;"), None);
    }

    #[test]
    fn a2_g4_impl_level_generic_dispatch() {
        assert_eq!(
            g4(
                "struct H<T>(T); impl<T: Mint> H<T> { fn mk() -> T { T::new() } } fn main() { let a: Tokens = H::mk(); let b: Tokens = H::mk(); }"
            ),
            Some(R::GenericConstructorDispatch)
        );
        assert_eq!(
            g4(
                "struct H<T>(T); impl<T: Mint> H<T> { fn mk() -> T { <T as Mint>::new() } } fn main() { let a: Tokens = H::<Tokens>::mk(); }"
            ),
            Some(R::GenericConstructorDispatch)
        );
        assert_eq!(
            g4(
                "struct H<T>(T); impl<T> H<T> { fn get(&self) -> &T { &self.0 } } fn main() { let _t = Tokens::new(); }"
            ),
            None
        );
    }
}
