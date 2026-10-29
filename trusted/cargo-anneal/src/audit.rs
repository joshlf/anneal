// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Trusted boundary, `.olean` environment, and manifest auditor for Anneal.
//!
//! This module implements the outer boundary gate that pairs with
//! `trusted/audit/TrustedBoundary.lean`. It enforces five repository and
//! per-invocation invariants without external dependencies or shell helpers:
//!
//! 1. `trusted/lean/` import and constant-origin containment against
//!    `trusted/lean/foundation-lock.json` (Lean v4.34.1), plus `@[vetted]` vs.
//!    `@[candidate <feature>]` non-contamination.
//! 2. Statement (`ci.type`) vs. Proof (`ci.value?`) Origin Separation across
//!    downstream `theory/`, `examples/`, and `tests/` modules, as well as
//!    per-crate `Mir.lean` and `Proof.lean` verification units.
//! 3. Zero custom axioms (`{Classical.choice, Quot.sound, propext}` only),
//!    zero `sorryAx`/`isUnsafe`/`isPartial`/compiler overrides, and full
//!    `base.toKernelEnv.replay`.
//! 4. Cargo workspace DAG containment verifying that all workspace crates
//!    reside under `trusted/` and that no crate depends on a path outside
//!    `trusted/`.
//! 5. Cryptographic `CaptureManifest.json` SHA-256 and `compilation_succeeded`
//!    verification before accepting compiled `.olean` proofs.

use std::collections::{BTreeMap, BTreeSet};
use std::env;
use std::fmt::{self, Write as _};
use std::fs::{self, File};
use std::io;
use std::os::unix::process::ExitStatusExt;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::thread;
use std::time::{Duration, Instant};

/// Pure-Rust FIPS 180-4 SHA-256 implementation used to compute
/// `CaptureManifest.json` and artifact digests without external dependencies.
pub fn sha256_hex(data: &[u8]) -> String {
    const K: [u32; 64] = [
        0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1,
        0x923f82a4, 0xab1c5ed5, 0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3,
        0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174, 0xe49b69c1, 0xefbe4786,
        0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
        0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147,
        0x06ca6351, 0x14292967, 0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13,
        0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85, 0xa2bfe8a1, 0xa81a664b,
        0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
        0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a,
        0x5b9cca4f, 0x682e6ff3, 0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208,
        0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2,
    ];

    let mut state: [u32; 8] = [
        0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
        0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19,
    ];

    let compress_block = |state: &mut [u32; 8], chunk: &[u8]| {
        let mut w = [0u32; 64];
        for (i, word) in chunk.chunks_exact(4).enumerate() {
            w[i] = u32::from_be_bytes([word[0], word[1], word[2], word[3]]);
        }
        for i in 16..64 {
            let s0 = w[i - 15].rotate_right(7)
                ^ w[i - 15].rotate_right(18)
                ^ (w[i - 15] >> 3);
            let s1 = w[i - 2].rotate_right(17)
                ^ w[i - 2].rotate_right(19)
                ^ (w[i - 2] >> 10);
            w[i] = w[i - 16]
                .wrapping_add(s0)
                .wrapping_add(w[i - 7])
                .wrapping_add(s1);
        }

        let [mut a, mut b, mut c, mut d, mut e, mut f, mut g, mut h] = *state;
        for i in 0..64 {
            let s1 =
                e.rotate_right(6) ^ e.rotate_right(11) ^ e.rotate_right(25);
            let ch = (e & f) ^ ((!e) & g);
            let temp1 = h
                .wrapping_add(s1)
                .wrapping_add(ch)
                .wrapping_add(K[i])
                .wrapping_add(w[i]);
            let s0 =
                a.rotate_right(2) ^ a.rotate_right(13) ^ a.rotate_right(22);
            let maj = (a & b) ^ (a & c) ^ (b & c);
            let temp2 = s0.wrapping_add(maj);

            h = g;
            g = f;
            f = e;
            e = d.wrapping_add(temp1);
            d = c;
            c = b;
            b = a;
            a = temp1.wrapping_add(temp2);
        }

        state[0] = state[0].wrapping_add(a);
        state[1] = state[1].wrapping_add(b);
        state[2] = state[2].wrapping_add(c);
        state[3] = state[3].wrapping_add(d);
        state[4] = state[4].wrapping_add(e);
        state[5] = state[5].wrapping_add(f);
        state[6] = state[6].wrapping_add(g);
        state[7] = state[7].wrapping_add(h);
    };

    let chunks = data.chunks_exact(64);
    let rem = chunks.remainder();
    for chunk in chunks {
        compress_block(&mut state, chunk);
    }

    let bit_len = (data.len() as u64) * 8;
    let mut tail = [0u8; 128];
    tail[..rem.len()].copy_from_slice(rem);
    tail[rem.len()] = 0x80;
    let total_tail_len = if rem.len() < 56 { 64 } else { 128 };
    tail[total_tail_len - 8..total_tail_len]
        .copy_from_slice(&bit_len.to_be_bytes());
    for chunk in tail[..total_tail_len].chunks_exact(64) {
        compress_block(&mut state, chunk);
    }

    let mut hex = String::with_capacity(64);
    for word in state {
        let _ = write!(hex, "{word:08x}");
    }
    hex
}

/// Pinned Lean 4 toolchain identifier required by `foundation-lock.json`.
pub const TOOLCHAIN: &str = "leanprover/lean4:v4.34.1";

/// Compiled Lean artifact companion suffixes tracked by the foundation lock and
/// module compiler.
pub const PARTS: [&str; 5] = [
    "olean",
    "olean.server",
    "olean.private",
    "ir.sig",
    "ir",
];

/// Maximum retained staging-directory byte budget (512 MiB).
pub const MAX_BYTES: u64 = 512 * 1024 * 1024;

/// Subsystem candidate-trusted feature identifiers recognized by Anneal.
pub const VALID_CANDIDATE_FEATURES: [&str; 6] = [
    "refinement",
    "step_result",
    "memory",
    "mir_ast",
    "mir_semantics",
    "rustc_capture",
];

/// Release channel governing whether candidate-trusted TCB features may be enabled.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum ReleaseChannel {
    /// Alpha release channel: candidate features are supported when explicitly
    /// enabled by the target crate's trust policy or CLI flags, and default to
    /// `VettedOnly` when omitted.
    #[default]
    Alpha,
    /// Stable release channel: hard-locked to `VettedOnly`; candidate features
    /// cannot be enabled.
    Stable,
}

impl ReleaseChannel {
    /// Parse `"alpha"` or `"stable"`.
    pub fn parse(s: &str) -> Result<Self, String> {
        match s {
            "alpha" => Ok(Self::Alpha),
            "stable" => Ok(Self::Stable),
            other => Err(format!(
                "unknown release channel `{other}` (expected `alpha` or `stable`)"
            )),
        }
    }
}

/// Per-crate candidate-feature trust policy.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct CrateTrustPolicy {
    /// When `true` (`allow-candidate-features = ["*"]`), all candidate features
    /// in [`VALID_CANDIDATE_FEATURES`] are permitted on [`ReleaseChannel::Alpha`].
    pub allow_all: bool,
    /// Explicitly named candidate features permitted on [`ReleaseChannel::Alpha`].
    pub allowed_features: BTreeSet<String>,
}

impl CrateTrustPolicy {
    /// Default policy permitting only `@[vetted]` TCB declarations.
    pub fn vetted_only() -> Self {
        Self::default()
    }

    /// Parse and validate a list of candidate feature names (or `"*"`).
    pub fn from_feature_list<I, S>(features: I) -> Result<Self, Failure>
    where
        I: IntoIterator<Item = S>,
        S: AsRef<str>,
    {
        let mut policy = Self::default();
        for raw in features {
            let feat = raw.as_ref().trim();
            if feat == "*" {
                policy.allow_all = true;
            } else if VALID_CANDIDATE_FEATURES.contains(&feat) {
                policy.allowed_features.insert(feat.to_string());
            } else {
                return Err(Failure::new(
                    1,
                    "candidate-policy",
                    format!(
                        "unknown candidate feature `{feat}` in allow-candidate-features"
                    ),
                ));
            }
        }
        Ok(policy)
    }

    /// Merge another [`CrateTrustPolicy`] into `self`.
    pub fn merge(&mut self, other: Self) {
        self.allow_all |= other.allow_all;
        self.allowed_features.extend(other.allowed_features);
    }

    /// Return `true` if `feature` is permitted under `channel` and `self`.
    pub fn is_allowed(&self, channel: ReleaseChannel, feature: &str) -> bool {
        match channel {
            ReleaseChannel::Stable => false,
            ReleaseChannel::Alpha => {
                self.allow_all || self.allowed_features.contains(feature)
            }
        }
    }
}

/// Resolve the target crate's [`CrateTrustPolicy`] from
/// `[package.metadata.anneal.trust-policy] allow-candidate-features` in
/// `crate_dir/Cargo.toml` and any explicit CLI/API override.
pub fn load_crate_trust_policy(
    crate_dir: &Path,
    cli_override: Option<&[String]>,
) -> Result<CrateTrustPolicy, Failure> {
    let mut policy = CrateTrustPolicy::vetted_only();
    let cargo_toml_path = crate_dir.join("Cargo.toml");
    if cargo_toml_path.is_file() {
        let text = fs::read_to_string(&cargo_toml_path).map_err(|e| {
            Failure::new(
                1,
                "candidate-policy",
                format!("cannot read {}: {e}", cargo_toml_path.display()),
            )
        })?;
        let toml = parse_cargo_toml(&text).map_err(|e| {
            Failure::new(
                1,
                "candidate-policy",
                format!(
                    "malformed Cargo.toml in {}: {e}",
                    cargo_toml_path.display()
                ),
            )
        })?;
        let allow_val = toml
            .get("package")
            .and_then(|p| p.get("metadata"))
            .and_then(|m| m.get("anneal"))
            .and_then(|a| {
                a.get("trust-policy")
                    .and_then(|tp| tp.get("allow-candidate-features"))
                    .or_else(|| a.get("allow-candidate-features"))
            });
        if let Some(val) = allow_val {
            let arr = val.as_arr().ok_or_else(|| {
                Failure::new(
                    1,
                    "candidate-policy",
                    "allow-candidate-features in Cargo.toml must be an array of strings",
                )
            })?;
            let mut names = Vec::with_capacity(arr.len());
            for item in arr {
                let s = item.as_str().ok_or_else(|| {
                    Failure::new(
                        1,
                        "candidate-policy",
                        "allow-candidate-features in Cargo.toml must contain only strings",
                    )
                })?;
                names.push(s.to_string());
            }
            policy.merge(CrateTrustPolicy::from_feature_list(&names)?);
        }
    }
    if let Some(cli_list) = cli_override {
        policy.merge(CrateTrustPolicy::from_feature_list(cli_list)?);
    }
    Ok(policy)
}

static STAGE_COUNTER: AtomicUsize = AtomicUsize::new(0);


/// A downstream Lean module target audited after `trusted/lean/`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DownstreamTarget {
    /// Dot-separated Lean module name (for example, `"Anneal.Refinement"`).
    pub module: String,
    /// Repository-relative path to the `.lean` source file.
    pub path: String,
    /// Direct module imports supplied to `lean --setup`.
    pub imports: Vec<String>,
    /// Audit role (`"theory"`, `"examples"`, or `"claim"`).
    pub role: String,
}

impl DownstreamTarget {
    /// Construct a new [`DownstreamTarget`].
    pub fn new(
        module: &str,
        path: &str,
        imports: &[&str],
        role: &str,
    ) -> Self {
        Self {
            module: module.to_string(),
            path: path.to_string(),
            imports: imports.iter().map(|s| (*s).to_string()).collect(),
            role: role.to_string(),
        }
    }
}

/// Return the default downstream Lean targets for a repository checkout.
pub fn default_downstream_targets() -> Vec<DownstreamTarget> {
    vec![
        DownstreamTarget::new(
            "Anneal.Refinement",
            "theory/Anneal/Refinement.lean",
            &["Trusted"],
            "theory",
        ),
        DownstreamTarget::new(
            "Anneal.StepResult",
            "theory/Anneal/StepResult.lean",
            &["Trusted", "Anneal.Refinement"],
            "theory",
        ),
        DownstreamTarget::new(
            "Anneal",
            "theory/Anneal.lean",
            &["Trusted", "Anneal.Refinement", "Anneal.StepResult"],
            "theory",
        ),
        DownstreamTarget::new(
            "Smoke",
            "examples/Smoke.lean",
            &["Anneal"],
            "examples",
        ),
        DownstreamTarget::new(
            "SmokeTest",
            "tests/Smoke.lean",
            &["Anneal"],
            "claim",
        ),
    ]
}

/// Structured audit failure distinguishing policy rejections (`code == 1`)
/// from operational or environment failures (`code == 2`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Failure {
    /// Process exit code (`1` for policy rejection, `2` for operational error).
    pub code: i32,
    /// Audit phase in which the failure occurred.
    pub phase: String,
    /// Human-readable diagnostic message.
    pub message: String,
}

impl Failure {
    /// Construct a new [`Failure`].
    pub fn new(
        code: i32,
        phase: impl Into<String>,
        message: impl Into<String>,
    ) -> Self {
        Self {
            code,
            phase: phase.into(),
            message: message.into(),
        }
    }
}

impl fmt::Display for Failure {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.message)
    }
}

impl std::error::Error for Failure {}

/// Minimal, deterministic JSON value representation used for `foundation-lock.json`,
/// `CaptureManifest.json`, and the `TrustedBoundary.lean` IPC protocol.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Json {
    Null,
    Bool(bool),
    Int(i64),
    Str(String),
    Arr(Vec<Json>),
    Obj(BTreeMap<String, Json>),
}

impl Json {
    /// Parse a UTF-8 JSON document, rejecting trailing tokens or syntax errors.
    pub fn parse(input: &str) -> Result<Self, String> {
        let mut parser = JsonParser {
            bytes: input.as_bytes(),
            pos: 0,
        };
        let value = parser.parse_value()?;
        parser.skip_ws();
        if parser.pos != parser.bytes.len() {
            return Err("trailing characters after JSON value".to_string());
        }
        Ok(value)
    }

    /// Serialize this JSON value in compact form with lexicographically sorted
    /// object keys.
    pub fn to_compact_string(&self) -> String {
        let mut out = String::new();
        self.write_compact(&mut out);
        out
    }

    /// Serialize this JSON value with two-space indentation and sorted keys.
    pub fn to_pretty_string(&self) -> String {
        let mut out = String::new();
        self.write_pretty(&mut out, 0);
        out
    }

    fn write_compact(&self, out: &mut String) {
        match self {
            Self::Null => out.push_str("null"),
            Self::Bool(true) => out.push_str("true"),
            Self::Bool(false) => out.push_str("false"),
            Self::Int(n) => {
                let _ = write!(out, "{n}");
            }
            Self::Str(s) => write_escaped_str(out, s),
            Self::Arr(items) => {
                out.push('[');
                for (i, item) in items.iter().enumerate() {
                    if i > 0 {
                        out.push(',');
                    }
                    item.write_compact(out);
                }
                out.push(']');
            }
            Self::Obj(map) => {
                out.push('{');
                for (i, (k, v)) in map.iter().enumerate() {
                    if i > 0 {
                        out.push(',');
                    }
                    write_escaped_str(out, k);
                    out.push(':');
                    v.write_compact(out);
                }
                out.push('}');
            }
        }
    }

    fn write_pretty(&self, out: &mut String, indent: usize) {
        let pad = " ".repeat(indent);
        let inner_pad = " ".repeat(indent + 2);
        match self {
            Self::Null | Self::Bool(_) | Self::Int(_) | Self::Str(_) => {
                self.write_compact(out);
            }
            Self::Arr(items) if items.is_empty() => out.push_str("[]"),
            Self::Arr(items) => {
                out.push_str("[\n");
                for (i, item) in items.iter().enumerate() {
                    out.push_str(&inner_pad);
                    item.write_pretty(out, indent + 2);
                    if i + 1 < items.len() {
                        out.push(',');
                    }
                    out.push('\n');
                }
                out.push_str(&pad);
                out.push(']');
            }
            Self::Obj(map) if map.is_empty() => out.push_str("{}"),
            Self::Obj(map) => {
                out.push_str("{\n");
                for (i, (k, v)) in map.iter().enumerate() {
                    out.push_str(&inner_pad);
                    write_escaped_str(out, k);
                    out.push_str(": ");
                    v.write_pretty(out, indent + 2);
                    if i + 1 < map.len() {
                        out.push(',');
                    }
                    out.push('\n');
                }
                out.push_str(&pad);
                out.push('}');
            }
        }
    }

    /// Borrow as an object map.
    pub fn as_obj(&self) -> Option<&BTreeMap<String, Json>> {
        match self {
            Self::Obj(m) => Some(m),
            _ => None,
        }
    }

    /// Mutably borrow as an object map.
    pub fn as_obj_mut(&mut self) -> Option<&mut BTreeMap<String, Json>> {
        match self {
            Self::Obj(m) => Some(m),
            _ => None,
        }
    }

    /// Borrow as an array slice.
    pub fn as_arr(&self) -> Option<&[Json]> {
        match self {
            Self::Arr(a) => Some(a),
            _ => None,
        }
    }

    /// Borrow as a string slice.
    pub fn as_str(&self) -> Option<&str> {
        match self {
            Self::Str(s) => Some(s),
            _ => None,
        }
    }

    /// Extract a boolean value.
    pub fn as_bool(&self) -> Option<bool> {
        match self {
            Self::Bool(b) => Some(*b),
            _ => None,
        }
    }

    /// Extract an integer value.
    pub fn as_i64(&self) -> Option<i64> {
        match self {
            Self::Int(n) => Some(*n),
            _ => None,
        }
    }

    /// Look up a field in an object.
    pub fn get(&self, key: &str) -> Option<&Json> {
        self.as_obj()?.get(key)
    }
}

fn write_escaped_str(out: &mut String, s: &str) {
    out.push('"');
    for ch in s.chars() {
        match ch {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\x08' => out.push_str("\\b"),
            '\x0c' => out.push_str("\\f"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if (c as u32) < 0x20 => {
                let _ = write!(out, "\\u{:04x}", c as u32);
            }
            c => out.push(c),
        }
    }
    out.push('"');
}

struct JsonParser<'a> {
    bytes: &'a [u8],
    pos: usize,
}

impl<'a> JsonParser<'a> {
    fn skip_ws(&mut self) {
        while self.pos < self.bytes.len() {
            match self.bytes[self.pos] {
                b' ' | b'\t' | b'\n' | b'\r' => self.pos += 1,
                _ => break,
            }
        }
    }

    fn peek(&self) -> Option<u8> {
        self.bytes.get(self.pos).copied()
    }

    fn parse_value(&mut self) -> Result<Json, String> {
        self.skip_ws();
        match self.peek() {
            Some(b'n') => self.parse_literal(b"null", Json::Null),
            Some(b't') => self.parse_literal(b"true", Json::Bool(true)),
            Some(b'f') => self.parse_literal(b"false", Json::Bool(false)),
            Some(b'"') => self.parse_string().map(Json::Str),
            Some(b'[') => self.parse_array(),
            Some(b'{') => self.parse_object(),
            Some(b'-') | Some(b'0'..=b'9') => self.parse_number(),
            Some(b) => Err(format!("unexpected byte `{}` in JSON", b as char)),
            None => Err("unexpected end of JSON input".to_string()),
        }
    }

    fn parse_literal(&mut self, lit: &[u8], val: Json) -> Result<Json, String> {
        if self.bytes.get(self.pos..self.pos + lit.len()) == Some(lit) {
            self.pos += lit.len();
            Ok(val)
        } else {
            Err("invalid JSON literal".to_string())
        }
    }

    fn parse_string(&mut self) -> Result<String, String> {
        if self.peek() != Some(b'"') {
            return Err("expected `\"` at start of string".to_string());
        }
        self.pos += 1;
        let mut out = String::new();
        while self.pos < self.bytes.len() {
            let b = self.bytes[self.pos];
            self.pos += 1;
            match b {
                b'"' => return Ok(out),
                b'\\' => {
                    let esc = *self
                        .bytes
                        .get(self.pos)
                        .ok_or("unterminated string escape")?;
                    self.pos += 1;
                    match esc {
                        b'"' => out.push('"'),
                        b'\\' => out.push('\\'),
                        b'/' => out.push('/'),
                        b'b' => out.push('\x08'),
                        b'f' => out.push('\x0c'),
                        b'n' => out.push('\n'),
                        b'r' => out.push('\r'),
                        b't' => out.push('\t'),
                        b'u' => {
                            let hex = self
                                .bytes
                                .get(self.pos..self.pos + 4)
                                .ok_or("short \\u escape")?;
                            let hex_str = std::str::from_utf8(hex)
                                .map_err(|_| "invalid \\u hex")?;
                            let code = u32::from_str_radix(hex_str, 16)
                                .map_err(|_| "invalid \\u hex digits")?;
                            let ch = char::from_u32(code)
                                .ok_or("invalid unicode scalar in \\u")?;
                            out.push(ch);
                            self.pos += 4;
                        }
                        _ => return Err("unsupported JSON escape".to_string()),
                    }
                }
                c if c < 0x20 => {
                    return Err("unescaped control character in string".into());
                }
                c => {
                    self.pos -= 1;
                    let rest = std::str::from_utf8(&self.bytes[self.pos..])
                        .map_err(|_| "invalid UTF-8 in JSON string")?;
                    let ch = rest.chars().next().unwrap();
                    out.push(ch);
                    self.pos += ch.len_utf8();
                    let _ = c;
                }
            }
        }
        Err("unterminated JSON string".to_string())
    }

    fn parse_number(&mut self) -> Result<Json, String> {
        let start = self.pos;
        if self.peek() == Some(b'-') {
            self.pos += 1;
        }
        while let Some(b'0'..=b'9') = self.peek() {
            self.pos += 1;
        }
        if self.peek() == Some(b'.') {
            self.pos += 1;
            while let Some(b'0'..=b'9') = self.peek() {
                self.pos += 1;
            }
        }
        let s = std::str::from_utf8(&self.bytes[start..self.pos])
            .map_err(|_| "invalid number UTF-8")?;
        if let Ok(n) = s.parse::<i64>() {
            Ok(Json::Int(n))
        } else if let Ok(f) = s.parse::<f64>() {
            Ok(Json::Int(f as i64))
        } else {
            Err(format!("invalid JSON number `{s}`"))
        }
    }

    fn parse_array(&mut self) -> Result<Json, String> {
        self.pos += 1;
        self.skip_ws();
        let mut items = Vec::new();
        if self.peek() == Some(b']') {
            self.pos += 1;
            return Ok(Json::Arr(items));
        }
        loop {
            items.push(self.parse_value()?);
            self.skip_ws();
            match self.peek() {
                Some(b',') => {
                    self.pos += 1;
                }
                Some(b']') => {
                    self.pos += 1;
                    return Ok(Json::Arr(items));
                }
                _ => return Err("expected `,` or `]` in array".to_string()),
            }
        }
    }

    fn parse_object(&mut self) -> Result<Json, String> {
        self.pos += 1;
        self.skip_ws();
        let mut map = BTreeMap::new();
        if self.peek() == Some(b'}') {
            self.pos += 1;
            return Ok(Json::Obj(map));
        }
        loop {
            self.skip_ws();
            let key = self.parse_string()?;
            self.skip_ws();
            if self.peek() != Some(b':') {
                return Err("expected `:` after object key".to_string());
            }
            self.pos += 1;
            let val = self.parse_value()?;
            map.insert(key, val);
            self.skip_ws();
            match self.peek() {
                Some(b',') => {
                    self.pos += 1;
                }
                Some(b'}') => {
                    self.pos += 1;
                    return Ok(Json::Obj(map));
                }
                _ => return Err("expected `,` or `}` in object".to_string()),
            }
        }
    }
}

/// Compute the SHA-256 hex digest of a file on disk.
pub fn digest(path: &Path) -> Result<String, Failure> {
    let bytes = fs::read(path).map_err(|e| {
        Failure::new(2, "io", format!("cannot read {}: {e}", path.display()))
    })?;
    Ok(sha256_hex(&bytes))
}

/// Compute the SHA-256 hex digest of a canonicalized [`Json`] value.
pub fn fingerprint(value: &Json) -> String {
    sha256_hex(value.to_compact_string().as_bytes())
}

/// Verify that `path` exists and is a regular file (not a symlink or directory).
pub fn regular(path: &Path, phase: &str) -> Result<(), Failure> {
    let meta = fs::symlink_metadata(path).map_err(|e| {
        Failure::new(
            2,
            phase,
            format!("cannot inspect {}: {e}", path.display()),
        )
    })?;
    if meta.file_type().is_symlink() || !meta.file_type().is_file() {
        return Err(Failure::new(
            1,
            phase,
            format!("expected a regular file: {}", path.display()),
        ));
    }
    Ok(())
}

fn is_hex_sha256(s: &str) -> bool {
    s.len() == 64
        && s.bytes()
            .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
}

fn is_lean_ident(s: &str) -> bool {
    let mut chars = s.chars();
    let Some(first) = chars.next() else {
        return false;
    };
    first.is_ascii_alphabetic()
        && chars.all(|c| c.is_ascii_alphanumeric() || c == '_')
}

/// Minimal TOML parser supporting Cargo workspace and package manifests.
fn parse_cargo_toml(text: &str) -> Result<Json, String> {
    let mut root = BTreeMap::new();
    let mut current_path: Vec<String> = Vec::new();
    let mut lines = text.lines().peekable();

    while let Some(raw_line) = lines.next() {
        let line = strip_toml_comment(raw_line).trim();
        if line.is_empty() {
            continue;
        }
        if line.starts_with('[') && line.ends_with(']') {
            let header = line[1..line.len() - 1].trim();
            if header.is_empty() || header.starts_with('[') {
                return Err("unsupported TOML table header".to_string());
            }
            current_path = header
                .split('.')
                .map(|p| p.trim().trim_matches('"').to_string())
                .collect();
            ensure_toml_table(&mut root, &current_path)?;
            continue;
        }
        let Some((k_raw, v_raw)) = line.split_once('=') else {
            return Err(format!("malformed TOML line `{line}`"));
        };
        let key = k_raw.trim().trim_matches('"').to_string();
        if key.is_empty() {
            return Err("empty TOML key".to_string());
        }
        let mut rhs = v_raw.trim().to_string();
        if rhs.starts_with('[') && !rhs.ends_with(']') {
            while let Some(next_raw) = lines.next() {
                let next_clean = strip_toml_comment(next_raw).trim();
                rhs.push(' ');
                rhs.push_str(next_clean);
                if next_clean.ends_with(']') {
                    break;
                }
            }
        }
        let val = parse_toml_value(rhs.trim())?;
        let table = ensure_toml_table(&mut root, &current_path)?;
        table.insert(key, val);
    }
    Ok(Json::Obj(root))
}

fn strip_toml_comment(line: &str) -> &str {
    let mut in_quotes = false;
    let mut escaped = false;
    for (idx, ch) in line.char_indices() {
        if escaped {
            escaped = false;
            continue;
        }
        if ch == '\\' && in_quotes {
            escaped = true;
            continue;
        }
        if ch == '"' {
            in_quotes = !in_quotes;
        } else if ch == '#' && !in_quotes {
            return &line[..idx];
        }
    }
    line
}

fn ensure_toml_table<'a>(
    root: &'a mut BTreeMap<String, Json>,
    path: &[String],
) -> Result<&'a mut BTreeMap<String, Json>, String> {
    let mut cur = root;
    for segment in path {
        let entry = cur
            .entry(segment.clone())
            .or_insert_with(|| Json::Obj(BTreeMap::new()));
        cur = match entry {
            Json::Obj(m) => m,
            _ => return Err("TOML key collides with table".to_string()),
        };
    }
    Ok(cur)
}

fn parse_toml_value(rhs: &str) -> Result<Json, String> {
    if rhs == "true" {
        return Ok(Json::Bool(true));
    }
    if rhs == "false" {
        return Ok(Json::Bool(false));
    }
    if rhs.starts_with('"') && rhs.ends_with('"') && rhs.len() >= 2 {
        return Json::parse(rhs);
    }
    if rhs.starts_with('[') && rhs.ends_with(']') {
        let inner = rhs[1..rhs.len() - 1].trim();
        if inner.is_empty() {
            return Ok(Json::Arr(Vec::new()));
        }
        let mut items = Vec::new();
        for part in split_top_level(inner, ',') {
            let trimmed = part.trim();
            if !trimmed.is_empty() {
                items.push(parse_toml_value(trimmed)?);
            }
        }
        return Ok(Json::Arr(items));
    }
    if rhs.starts_with('{') && rhs.ends_with('}') {
        let inner = rhs[1..rhs.len() - 1].trim();
        let mut map = BTreeMap::new();
        if !inner.is_empty() {
            for part in split_top_level(inner, ',') {
                let trimmed = part.trim();
                if trimmed.is_empty() {
                    continue;
                }
                let Some((k, v)) = trimmed.split_once('=') else {
                    return Err("malformed TOML inline table entry".to_string());
                };
                map.insert(
                    k.trim().trim_matches('"').to_string(),
                    parse_toml_value(v.trim())?,
                );
            }
        }
        return Ok(Json::Obj(map));
    }
    if let Ok(n) = rhs.parse::<i64>() {
        return Ok(Json::Int(n));
    }
    Err(format!("unsupported TOML value `{rhs}`"))
}

fn split_top_level(input: &str, sep: char) -> Vec<&str> {
    let mut out = Vec::new();
    let mut start = 0;
    let mut in_quotes = false;
    let mut depth = 0usize;
    for (idx, ch) in input.char_indices() {
        if ch == '"' {
            in_quotes = !in_quotes;
        } else if !in_quotes {
            if ch == '[' || ch == '{' {
                depth += 1;
            } else if ch == ']' || ch == '}' {
                depth = depth.saturating_sub(1);
            } else if ch == sep && depth == 0 {
                out.push(&input[start..idx]);
                start = idx + ch.len_utf8();
            }
        }
    }
    out.push(&input[start..]);
    out
}

/// Verify Cargo workspace DAG containment: all workspace crates must reside
/// under `trusted/`, and no workspace crate may depend on a path outside
/// `trusted/`.
pub fn check_cargo_boundary(
    checkout: &Path,
) -> Result<BTreeMap<String, String>, Failure> {
    let phase = "cargo-boundary";
    let root_toml_path = checkout.join("Cargo.toml");
    let trusted_toml_path = checkout.join("trusted/rustc-capture/Cargo.toml");
    regular(&root_toml_path, phase)?;
    regular(&trusted_toml_path, phase)?;

    let root_text = fs::read_to_string(&root_toml_path).map_err(|e| {
        Failure::new(1, phase, format!("malformed Cargo manifest: {e}"))
    })?;
    let root_toml = parse_cargo_toml(&root_text).map_err(|e| {
        Failure::new(1, phase, format!("malformed Cargo manifest: {e}"))
    })?;

    let members = root_toml
        .get("workspace")
        .and_then(|w| w.get("members"))
        .and_then(Json::as_arr)
        .ok_or_else(|| {
            Failure::new(1, phase, "missing workspace.members in root Cargo.toml")
        })?;

    let checkout_canon = fs::canonicalize(checkout).map_err(|e| {
        Failure::new(2, phase, format!("cannot canonicalize checkout: {e}"))
    })?;

    let mut has_rustc_capture = false;
    let mut hashes = BTreeMap::new();
    hashes.insert("Cargo.toml".to_string(), digest(&root_toml_path)?);

    for member_val in members {
        let member = member_val.as_str().ok_or_else(|| {
            Failure::new(1, phase, "non-string workspace member")
        })?;
        if !member.starts_with("trusted/") {
            return Err(Failure::new(
                1,
                phase,
                format!("workspace member outside trusted/: {member}"),
            ));
        }
        if member == "trusted/rustc-capture" {
            has_rustc_capture = true;
        }
        let member_toml_path = checkout.join(member).join("Cargo.toml");
        regular(&member_toml_path, phase)?;
        let member_text = fs::read_to_string(&member_toml_path).map_err(|e| {
            Failure::new(
                1,
                phase,
                format!("malformed member Cargo.toml in {member}: {e}"),
            )
        })?;
        let member_toml = parse_cargo_toml(&member_text).map_err(|e| {
            Failure::new(
                1,
                phase,
                format!("malformed member Cargo.toml in {member}: {e}"),
            )
        })?;
        let _pkg_name = member_toml
            .get("package")
            .and_then(|p| p.get("name"))
            .and_then(Json::as_str)
            .filter(|s| !s.is_empty())
            .ok_or_else(|| {
                Failure::new(
                    1,
                    phase,
                    format!("missing package.name in {member}"),
                )
            })?;

        let member_parent = member_toml_path.parent().unwrap();
        let check_dep_table =
            |table_opt: Option<&Json>, section: &str| -> Result<(), Failure> {
                let Some(table_val) = table_opt else {
                    return Ok(());
                };
                let table = table_val.as_obj().ok_or_else(|| {
                    Failure::new(
                        1,
                        phase,
                        format!("invalid {section} in {member}/Cargo.toml"),
                    )
                })?;
                for (_dep_name, spec) in table {
                    if let Some(spec_obj) = spec.as_obj()
                        && let Some(dep_path) =
                            spec_obj.get("path").and_then(Json::as_str)
                    {
                        let joined = member_parent.join(dep_path);
                        let resolved =
                            fs::canonicalize(&joined).unwrap_or(joined);
                        let rel = resolved
                            .strip_prefix(&checkout_canon)
                            .map_err(|_| {
                                Failure::new(
                                    1,
                                    phase,
                                    format!(
                                        "{member} path dependency escapes checkout: {dep_path}"
                                    ),
                                )
                            })?;
                        let rel_str = rel.to_string_lossy().replace('\\', "/");
                        if !rel_str.starts_with("trusted/") {
                            return Err(Failure::new(
                                1,
                                phase,
                                format!(
                                    "{member} path dependency points outside trusted/: {rel_str}"
                                ),
                            ));
                        }
                    }
                }
                Ok(())
            };

        for section in
            ["dependencies", "dev-dependencies", "build-dependencies"]
        {
            check_dep_table(member_toml.get(section), section)?;
        }
        if let Some(targets) = member_toml.get("target").and_then(Json::as_obj)
        {
            for (cfg_name, cfg_table) in targets {
                if let Some(cfg_obj) = cfg_table.as_obj() {
                    for section in [
                        "dependencies",
                        "dev-dependencies",
                        "build-dependencies",
                    ] {
                        let label = format!("target.{cfg_name}.{section}");
                        check_dep_table(cfg_obj.get(section), &label)?;
                    }
                }
            }
        }

        hashes.insert(
            format!("{member}/Cargo.toml"),
            digest(&member_toml_path)?,
        );
    }
    if !has_rustc_capture {
        return Err(Failure::new(
            1,
            phase,
            "trusted/rustc-capture missing from workspace.members",
        ));
    }

    for rel in [
        "trusted/rustc-capture/src/lib.rs",
        "trusted/rustc-capture/src/proof_gen.rs",
    ] {
        let p = checkout.join(rel);
        regular(&p, phase)?;
        hashes.insert(rel.to_string(), digest(&p)?);
    }

    Ok(hashes)
}

/// Verify a `CaptureManifest.json` handshake against `.rs` and `Mir.lean` files
/// on disk.
pub fn verify_capture_manifest(
    manifest_path: &Path,
    root: &Path,
) -> Result<Json, Failure> {
    let phase = "manifest";
    regular(manifest_path, phase)?;
    let text = fs::read_to_string(manifest_path).map_err(|e| {
        Failure::new(
            1,
            phase,
            format!("malformed CaptureManifest.json: {e}"),
        )
    })?;
    let manifest = Json::parse(&text).map_err(|e| {
        Failure::new(
            1,
            phase,
            format!("malformed CaptureManifest.json: {e}"),
        )
    })?;
    let obj = manifest.as_obj().ok_or_else(|| {
        Failure::new(1, phase, "unexpected CaptureManifest.json schema keys")
    })?;
    let required_keys: BTreeSet<&str> =
        ["schema", "compilation_succeeded", "rust_sources", "targets"]
            .into_iter()
            .collect();
    let allowed_keys: BTreeSet<&str> = [
        "schema",
        "compilation_succeeded",
        "rust_sources",
        "targets",
        "candidate_features",
    ]
    .into_iter()
    .collect();
    let actual_keys: BTreeSet<&str> = obj.keys().map(String::as_str).collect();
    if !required_keys.is_subset(&actual_keys)
        || !actual_keys.is_subset(&allowed_keys)
    {
        return Err(Failure::new(
            1,
            phase,
            "unexpected CaptureManifest.json schema keys",
        ));
    }
    if let Some(cand_val) = obj.get("candidate_features") {
        let Some(cand_arr) = cand_val.as_arr() else {
            return Err(Failure::new(
                1,
                phase,
                "invalid candidate_features in CaptureManifest.json",
            ));
        };
        let mut seen_cand = BTreeSet::new();
        for item in cand_arr {
            let Some(feat) = item
                .as_str()
                .filter(|f| VALID_CANDIDATE_FEATURES.contains(f))
            else {
                return Err(Failure::new(
                    1,
                    phase,
                    "invalid candidate_features entry in CaptureManifest.json",
                ));
            };
            if !seen_cand.insert(feat.to_string()) {
                return Err(Failure::new(
                    1,
                    phase,
                    format!(
                        "duplicate candidate_features entry `{feat}` in CaptureManifest.json"
                    ),
                ));
            }
        }
    }
    let schema = obj.get("schema").and_then(Json::as_i64).unwrap_or(-1);
    if schema != 1 {
        return Err(Failure::new(
            1,
            phase,
            format!("unsupported CaptureManifest.json schema {schema}"),
        ));
    }
    if obj.get("compilation_succeeded").and_then(Json::as_bool) != Some(true) {
        return Err(Failure::new(
            1,
            phase,
            "compilation_succeeded is not true in CaptureManifest.json",
        ));
    }
    let rust_sources = obj
        .get("rust_sources")
        .and_then(Json::as_arr)
        .filter(|a| !a.is_empty())
        .ok_or_else(|| {
            Failure::new(
                1,
                phase,
                "CaptureManifest.json must record at least one Rust source file",
            )
        })?;
    for entry in rust_sources {
        let Some(pair) = entry.as_arr() else {
            return Err(Failure::new(
                1,
                phase,
                "invalid rust_sources entry in CaptureManifest.json",
            ));
        };
        if pair.len() != 2 {
            return Err(Failure::new(
                1,
                phase,
                "invalid rust_sources entry in CaptureManifest.json",
            ));
        }
        let Some(rel_path) = pair[0].as_str().filter(|s| !s.is_empty()) else {
            return Err(Failure::new(
                1,
                phase,
                "invalid rust_sources entry in CaptureManifest.json",
            ));
        };
        let Some(expected_sha) = pair[1].as_str().filter(|s| is_hex_sha256(s))
        else {
            return Err(Failure::new(
                1,
                phase,
                "invalid rust_sources entry in CaptureManifest.json",
            ));
        };
        let src_path = root.join(rel_path);
        regular(&src_path, phase)?;
        if digest(&src_path)? != expected_sha {
            return Err(Failure::new(
                1,
                phase,
                format!("Rust source digest mismatch for {rel_path}"),
            ));
        }
    }

    let targets = obj
        .get("targets")
        .and_then(Json::as_arr)
        .filter(|a| !a.is_empty())
        .ok_or_else(|| {
            Failure::new(
                1,
                phase,
                "CaptureManifest.json must record at least one verification target",
            )
        })?;
    let mut seen_defs = BTreeSet::new();
    for target in targets {
        let Some(t_obj) = target.as_obj() else {
            return Err(Failure::new(
                1,
                phase,
                "invalid target entry in CaptureManifest.json",
            ));
        };
        let expected_t_keys: BTreeSet<&str> =
            ["def_id", "mir_module_path", "mir_module_sha256"]
                .into_iter()
                .collect();
        let actual_t_keys: BTreeSet<&str> =
            t_obj.keys().map(String::as_str).collect();
        if actual_t_keys != expected_t_keys {
            return Err(Failure::new(
                1,
                phase,
                "invalid target entry in CaptureManifest.json",
            ));
        }
        let Some(def_id) =
            t_obj.get("def_id").and_then(Json::as_str).filter(|s| !s.is_empty())
        else {
            return Err(Failure::new(
                1,
                phase,
                "invalid target entry in CaptureManifest.json",
            ));
        };
        let Some(mir_rel) = t_obj
            .get("mir_module_path")
            .and_then(Json::as_str)
            .filter(|s| !s.is_empty())
        else {
            return Err(Failure::new(
                1,
                phase,
                "invalid target entry in CaptureManifest.json",
            ));
        };
        let Some(mir_sha) = t_obj
            .get("mir_module_sha256")
            .and_then(Json::as_str)
            .filter(|s| is_hex_sha256(s))
        else {
            return Err(Failure::new(
                1,
                phase,
                "invalid target entry in CaptureManifest.json",
            ));
        };
        if !seen_defs.insert(def_id.to_string()) {
            return Err(Failure::new(
                1,
                phase,
                format!("duplicate target def_id {def_id}"),
            ));
        }
        let mir_path = root.join(mir_rel);
        regular(&mir_path, phase)?;
        if digest(&mir_path)? != mir_sha {
            return Err(Failure::new(
                1,
                phase,
                format!("Mir module digest mismatch for {mir_rel}"),
            ));
        }
    }
    Ok(manifest)
}

/// Complete directory inventory and module map for `trusted/lean/`.
pub fn snapshot(
    root: &Path,
) -> Result<(BTreeMap<String, Json>, BTreeMap<String, String>), Failure> {
    let meta = fs::symlink_metadata(root).map_err(|_| {
        Failure::new(
            1,
            "snapshot",
            format!("expected regular source directory: {}", root.display()),
        )
    })?;
    if meta.file_type().is_symlink() || !meta.file_type().is_dir() {
        return Err(Failure::new(
            1,
            "snapshot",
            format!("expected regular source directory: {}", root.display()),
        ));
    }

    let mut inventory = BTreeMap::new();
    let mut modules = BTreeMap::new();
    let mut queue = vec![root.to_path_buf()];

    while let Some(dir) = queue.pop() {
        let mut names = Vec::new();
        for entry in fs::read_dir(&dir).map_err(|e| {
            Failure::new(2, "snapshot", format!("cannot read {}: {e}", dir.display()))
        })? {
            let entry = entry.map_err(|e| {
                Failure::new(2, "snapshot", format!("cannot read {}: {e}", dir.display()))
            })?;
            names.push(entry.file_name().to_string_lossy().into_owned());
        }
        names.sort();
        let mut subdirs = Vec::new();
        for name in names {
            let path = dir.join(&name);
            let rel_path = path.strip_prefix(root).unwrap();
            let relative = rel_path.to_string_lossy().replace('\\', "/");
            let entry_meta = fs::symlink_metadata(&path).map_err(|e| {
                Failure::new(
                    2,
                    "snapshot",
                    format!("cannot inspect {}: {e}", path.display()),
                )
            })?;
            if entry_meta.file_type().is_dir()
                && !entry_meta.file_type().is_symlink()
            {
                let mut obj = BTreeMap::new();
                obj.insert(
                    "kind".to_string(),
                    Json::Str("directory".to_string()),
                );
                inventory.insert(relative, Json::Obj(obj));
                subdirs.push(path);
                continue;
            }
            regular(&path, "snapshot")?;
            if PARTS
                .iter()
                .any(|part| relative.ends_with(&format!(".{part}")))
                || relative.ends_with(".ilean")
            {
                return Err(Failure::new(
                    1,
                    "snapshot",
                    format!("compiled artifact in source root: {relative}"),
                ));
            }
            let file_bytes = entry_meta.len();
            let sha = digest(&path)?;
            let mut obj = BTreeMap::new();
            obj.insert("kind".to_string(), Json::Str("file".to_string()));
            obj.insert("sha256".to_string(), Json::Str(sha));
            obj.insert("bytes".to_string(), Json::Int(file_bytes as i64));
            inventory.insert(relative.clone(), Json::Obj(obj));

            if let Some(stem) = relative.strip_suffix(".lean") {
                let components: Vec<&str> = stem.split('/').collect();
                if components.first().copied() != Some("Trusted")
                    || !components.iter().copied().all(is_lean_ident)
                {
                    return Err(Failure::new(
                        1,
                        "snapshot",
                        format!("unmappable Lean source: {relative}"),
                    ));
                }
                let module = components.join(".");
                if modules.contains_key(&module) {
                    return Err(Failure::new(
                        1,
                        "snapshot",
                        format!("duplicate module: {module}"),
                    ));
                }
                modules.insert(module, relative);
            }
        }
        subdirs.reverse();
        queue.extend(subdirs);
    }

    if !modules.contains_key("Trusted") {
        return Err(Failure::new(
            1,
            "snapshot",
            "missing Trusted.lean umbrella",
        ));
    }
    Ok((inventory, modules))
}

/// Resolve the default pinned Lean 4.34.1 binary path when none is explicitly
/// provided.
pub fn default_lean_path() -> PathBuf {
    if let Some(env_lean) = env::var_os("ANNEAL_LEAN_BIN") {
        return PathBuf::from(env_lean);
    }
    if let Some(tc_root) = crate::setup::resolve_installed() {
        let bundled = tc_root.join("lean/bin/lean");
        if bundled.is_file() {
            return bundled;
        }
    }
    let home = env::var_os("HOME")
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from("/root"));
    home.join(".elan/toolchains/leanprover--lean4---v4.34.1/bin/lean")
}

/// Stateful boundary and crate-verification auditor managing an isolated
/// staging directory (`stage`).
pub struct Checker {
    pub checkout: PathBuf,
    pub source: PathBuf,
    pub lean: PathBuf,
    pub stage: PathBuf,
    pub phase: String,
    pub execution_began: bool,
    pub counter: usize,
    pub environment: BTreeMap<String, String>,
    pub artifacts: BTreeMap<String, Vec<Vec<String>>>,
    pub graph: BTreeMap<String, Json>,
    pub last_status: Option<Json>,
    pub initial: BTreeMap<String, Json>,
    pub modules: BTreeMap<String, String>,
    pub tool_hashes: BTreeMap<String, String>,
    pub inspector: PathBuf,
    pub lock: Json,
    pub version: String,
    pub prefix: PathBuf,
    pub foundation: Vec<String>,
    pub trust_declarations: Vec<Json>,
    pub timeout_duration: Duration,
    pub max_bytes: u64,
}

impl Checker {
    /// Create a new [`Checker`] with a fresh private staging directory.
    pub fn new(
        checkout: &Path,
        lean: Option<&Path>,
        temp_parent: Option<&Path>,
    ) -> io::Result<Self> {
        Self::new_with_env(checkout, lean, temp_parent, env::vars())
    }

    /// Create a new [`Checker`] filtering the supplied ambient environment.
    pub fn new_with_env<I>(
        checkout: &Path,
        lean: Option<&Path>,
        temp_parent: Option<&Path>,
        ambient_env: I,
    ) -> io::Result<Self>
    where
        I: IntoIterator<Item = (String, String)>,
    {
        let checkout = fs::canonicalize(checkout)?;
        let source = checkout.join("trusted/lean");
        let lean_raw = match lean {
            Some(p) => p.to_path_buf(),
            None => default_lean_path(),
        };
        let lean = if lean_raw.is_absolute() {
            lean_raw
        } else {
            env::current_dir()?.join(lean_raw)
        };
        let parent = match temp_parent {
            Some(p) => p.to_path_buf(),
            None => env::temp_dir(),
        };
        fs::create_dir_all(&parent)?;
        let id = STAGE_COUNTER.fetch_add(1, Ordering::Relaxed);
        let stage = parent.join(format!(
            "anneal-trusted-{}-{}-{}",
            std::process::id(),
            id,
            Instant::now().elapsed().as_nanos()
        ));
        fs::create_dir_all(&stage)?;

        let mut environment = BTreeMap::new();
        for (k, v) in ambient_env {
            if !k.starts_with("LEAN")
                && !k.starts_with("LAKE")
                && !k.starts_with("ELAN")
                && !k.starts_with("DYLD_")
            {
                environment.insert(k, v);
            }
        }
        environment.insert("PATH".to_string(), "/usr/bin:/bin".to_string());

        Ok(Self {
            checkout,
            source,
            lean,
            stage,
            phase: "admission".to_string(),
            execution_began: false,
            counter: 0,
            environment,
            artifacts: BTreeMap::new(),
            graph: BTreeMap::new(),
            last_status: None,
            initial: BTreeMap::new(),
            modules: BTreeMap::new(),
            tool_hashes: BTreeMap::new(),
            inspector: PathBuf::new(),
            lock: Json::Obj(BTreeMap::new()),
            version: String::new(),
            prefix: PathBuf::new(),
            foundation: Vec::new(),
            trust_declarations: Vec::new(),
            timeout_duration: Duration::from_secs(60),
            max_bytes: MAX_BYTES,
        })
    }

    /// Enforce the 512 MiB retained staging-directory byte limit.
    pub fn budget(&self) -> Result<(), Failure> {
        let size = dir_byte_size(&self.stage).map_err(|e| {
            Failure::new(
                2,
                &self.phase,
                format!("cannot measure staging budget: {e}"),
            )
        })?;
        if size > self.max_bytes {
            return Err(Failure::new(
                2,
                &self.phase,
                "512 MiB retained-build envelope exceeded",
            ));
        }
        Ok(())
    }

    /// Execute `self.lean` with `arguments`, recording a `.status.json`
    /// observation and enforcing the 60-second child timeout.
    pub fn process(
        &mut self,
        label: &str,
        arguments: &[String],
    ) -> Result<String, Failure> {
        self.phase = label.to_string();
        self.counter += 1;
        let stem = self.stage.join(format!("{:03}-{label}", self.counter));
        let stdout_path = PathBuf::from(format!("{}.stdout", stem.display()));
        let stderr_path = PathBuf::from(format!("{}.stderr", stem.display()));
        let status_path =
            PathBuf::from(format!("{}.status.json", stem.display()));

        let out_file = File::options()
            .write(true)
            .create_new(true)
            .open(&stdout_path)
            .map_err(|e| {
                Failure::new(2, label, format!("could not execute Lean: {e}"))
            })?;
        let err_file = File::options()
            .write(true)
            .create_new(true)
            .open(&stderr_path)
            .map_err(|e| {
                Failure::new(2, label, format!("could not execute Lean: {e}"))
            })?;

        let start = Instant::now();
        let mut child = Command::new(&self.lean)
            .args(arguments)
            .current_dir(&self.stage)
            .env_clear()
            .envs(&self.environment)
            .stdout(out_file)
            .stderr(err_file)
            .spawn()
            .map_err(|e| {
                Failure::new(2, label, format!("could not execute Lean: {e}"))
            })?;

        let mut returncode: Option<i64> = None;
        let mut timed_out = false;
        loop {
            match child.try_wait() {
                Ok(Some(status)) => {
                    if let Some(code) = status.code() {
                        returncode = Some(code as i64);
                    } else if let Some(sig) = status.signal() {
                        returncode = Some(-(sig as i64));
                    } else {
                        returncode = Some(-1);
                    }
                    break;
                }
                Ok(None) => {
                    if start.elapsed() >= self.timeout_duration {
                        let _ = child.kill();
                        let _ = child.wait();
                        timed_out = true;
                        break;
                    }
                    thread::sleep(Duration::from_millis(5));
                }
                Err(e) => {
                    return Err(Failure::new(
                        2,
                        label,
                        format!("could not execute Lean: {e}"),
                    ));
                }
            }
        }

        let elapsed_secs = start.elapsed().as_secs() as i64;
        let stdout_bytes =
            fs::metadata(&stdout_path).map(|m| m.len()).unwrap_or(0) as i64;
        let stderr_bytes =
            fs::metadata(&stderr_path).map(|m| m.len()).unwrap_or(0) as i64;

        let mut argv_json =
            vec![Json::Str(self.lean.to_string_lossy().into_owned())];
        argv_json.extend(arguments.iter().cloned().map(Json::Str));

        let mut obs = BTreeMap::new();
        obs.insert("argv".to_string(), Json::Arr(argv_json));
        obs.insert(
            "returncode".to_string(),
            match returncode {
                Some(c) => Json::Int(c),
                None => Json::Null,
            },
        );
        obs.insert("timeout".to_string(), Json::Bool(timed_out));
        obs.insert("seconds".to_string(), Json::Int(elapsed_secs));
        obs.insert("stdoutBytes".to_string(), Json::Int(stdout_bytes));
        obs.insert("stderrBytes".to_string(), Json::Int(stderr_bytes));
        let obs_json = Json::Obj(obs);
        let _ = fs::write(&status_path, obs_json.to_pretty_string().as_bytes());
        self.last_status = Some(obs_json);

        self.budget()?;
        if timed_out {
            return Err(Failure::new(
                2,
                label,
                "direct Lean child exceeded 60 seconds; no retry",
            ));
        }
        if returncode != Some(0) {
            return Err(Failure::new(
                2,
                label,
                format!(
                    "Lean exited {:?}; see {}.stdout/.stderr",
                    returncode,
                    stem.display()
                ),
            ));
        }
        fs::read_to_string(&stdout_path).map_err(|e| {
            Failure::new(2, label, format!("invalid UTF-8 from Lean: {e}"))
        })
    }

    /// Write a `<module>.setup.json` descriptor for `lean --setup`.
    pub fn write_setup_json(
        &self,
        module: &str,
        imports: &[Json],
    ) -> Result<PathBuf, Failure> {
        let mut import_arts = BTreeMap::new();
        for (k, v) in &self.artifacts {
            let groups: Vec<Json> = v
                .iter()
                .map(|g| Json::Arr(g.iter().cloned().map(Json::Str).collect()))
                .collect();
            import_arts.insert(k.clone(), Json::Arr(groups));
        }
        let mut setup_obj = BTreeMap::new();
        setup_obj.insert("name".to_string(), Json::Str(module.to_string()));
        setup_obj.insert("isModule".to_string(), Json::Bool(false));
        setup_obj.insert("imports".to_string(), Json::Arr(imports.to_vec()));
        setup_obj.insert("importArts".to_string(), Json::Obj(import_arts));
        setup_obj.insert("dynlibs".to_string(), Json::Arr(Vec::new()));
        setup_obj.insert("plugins".to_string(), Json::Arr(Vec::new()));
        setup_obj.insert("options".to_string(), Json::Obj(BTreeMap::new()));

        let setup_path = self.stage.join(format!("{module}.setup.json"));
        fs::write(
            &setup_path,
            Json::Obj(setup_obj).to_compact_string().as_bytes(),
        )
        .map_err(|e| Failure::new(2, "setup", e.to_string()))?;
        Ok(setup_path)
    }

    /// Invoke `TrustedBoundary.lean` in `mode` with `extra_fields`.
    pub fn inspect(
        &mut self,
        mode: &str,
        extra_fields: BTreeMap<String, Json>,
    ) -> Result<Json, Failure> {
        self.phase = mode.to_string();
        let mut req = BTreeMap::new();
        req.insert("mode".to_string(), Json::Str(mode.to_string()));
        req.insert(
            "sysroot".to_string(),
            Json::Str(self.prefix.to_string_lossy().into_owned()),
        );
        let arts_arr: Vec<Json> = self
            .artifacts
            .iter()
            .map(|(k, parts)| {
                let parts_json: Vec<Json> = parts
                    .iter()
                    .map(|group| {
                        Json::Arr(
                            group.iter().cloned().map(Json::Str).collect(),
                        )
                    })
                    .collect();
                Json::Arr(vec![Json::Str(k.clone()), Json::Arr(parts_json)])
            })
            .collect();
        req.insert("artifacts".to_string(), Json::Arr(arts_arr));
        req.insert(
            "foundation".to_string(),
            Json::Arr(self.foundation.iter().cloned().map(Json::Str).collect()),
        );
        req.insert("graph".to_string(), Json::Obj(self.graph.clone()));
        let axioms = self
            .lock
            .get("axioms")
            .cloned()
            .unwrap_or_else(|| Json::Arr(Vec::new()));
        req.insert("axioms".to_string(), axioms);
        for (k, v) in extra_fields {
            req.insert(k, v);
        }

        let stem = self
            .stage
            .join(format!("request-{:03}-{mode}", self.counter + 1));
        let request_path = PathBuf::from(format!("{}.json", stem.display()));
        let result_path =
            PathBuf::from(format!("{}.result.json", stem.display()));
        fs::write(&request_path, Json::Obj(req).to_compact_string().as_bytes())
            .map_err(|e| {
                Failure::new(2, mode, format!("cannot write request: {e}"))
            })?;

        self.last_status = None;
        let args = vec![
            "-j1".to_string(),
            "-M2048".to_string(),
            "--run".to_string(),
            self.inspector.to_string_lossy().into_owned(),
            request_path.to_string_lossy().into_owned(),
            result_path.to_string_lossy().into_owned(),
        ];
        if let Err(failure) = self.process(mode, &args) {
            self.budget()?;
            let is_rc1 = self.last_status.as_ref().is_some_and(|st| {
                st.get("returncode").and_then(Json::as_i64) == Some(1)
                    && st.get("timeout").and_then(Json::as_bool) == Some(false)
            });
            if is_rc1
                && result_path.is_file()
                && let Ok(text) = fs::read_to_string(&result_path)
                && let Ok(resp) = Json::parse(&text)
                && let Some(obj) = resp.as_obj()
                && obj.len() == 3
                && obj.get("ok").and_then(Json::as_bool) == Some(false)
                && obj.get("category").and_then(Json::as_str) == Some("policy")
                && let Some(msg) = obj
                    .get("message")
                    .and_then(Json::as_str)
                    .filter(|s| !s.is_empty())
            {
                return Err(Failure::new(1, mode, msg));
            }
            return Err(failure);
        }

        let resp_text = fs::read_to_string(&result_path).map_err(|e| {
            Failure::new(
                2,
                mode,
                format!("missing/malformed inspector result: {e}"),
            )
        })?;
        let resp = Json::parse(&resp_text).map_err(|e| {
            Failure::new(
                2,
                mode,
                format!("missing/malformed inspector result: {e}"),
            )
        })?;
        let Some(resp_obj) = resp.as_obj() else {
            return Err(Failure::new(
                2,
                mode,
                "unexpected inspector protocol response",
            ));
        };
        if resp_obj.len() != 2
            || resp_obj.get("ok").and_then(Json::as_bool) != Some(true)
            || !resp_obj.get("result").is_some_and(|r| r.as_obj().is_some())
        {
            return Err(Failure::new(
                2,
                mode,
                "unexpected inspector protocol response",
            ));
        }
        Ok(resp_obj.get("result").unwrap().clone())
    }

    /// Snapshot `trusted/lean/`, stage `TrustedBoundary.lean`, and verify the
    /// pinned Lean 4.34.1 binary and `Init.*` artifacts against
    /// `foundation-lock.json`.
    pub fn tool_admission(&mut self) -> Result<(), Failure> {
        let (initial, modules) = snapshot(&self.source)?;
        self.initial = initial;
        self.modules = modules;

        let inspector_src =
            self.checkout.join("trusted/audit/TrustedBoundary.lean");
        regular(&inspector_src, "tool-snapshot")?;
        self.tool_hashes.clear();
        self.tool_hashes.insert(
            "trusted/audit/TrustedBoundary.lean".to_string(),
            digest(&inspector_src)?,
        );
        self.inspector = inspector_src;

        let lock_text =
            fs::read_to_string(self.source.join("foundation-lock.json"))
                .map_err(|e| {
                    Failure::new(
                        2,
                        "lock",
                        format!("cannot read foundation lock: {e}"),
                    )
                })?;
        let lock = Json::parse(&lock_text).map_err(|e| {
            Failure::new(2, "lock", format!("cannot read foundation lock: {e}"))
        })?;
        let Some(lock_obj) = lock.as_obj() else {
            return Err(Failure::new(
                2,
                "lock",
                "unsupported lock/toolchain schema",
            ));
        };
        if lock_obj.get("schema").and_then(Json::as_i64) != Some(1)
            || lock_obj.get("toolchain").and_then(Json::as_str)
                != Some(TOOLCHAIN)
        {
            return Err(Failure::new(
                2,
                "lock",
                "unsupported lock/toolchain schema",
            ));
        }
        self.lock = lock;

        let toolchain_text =
            fs::read_to_string(self.source.join("lean-toolchain")).map_err(
                |e| {
                    Failure::new(
                        2,
                        "lock",
                        format!("cannot read lean-toolchain: {e}"),
                    )
                },
            )?;
        if toolchain_text.trim() != TOOLCHAIN {
            return Err(Failure::new(
                1,
                "lock",
                "lean-toolchain differs from lock",
            ));
        }

        regular(&self.lean, "toolchain")?;
        self.lean = fs::canonicalize(&self.lean).map_err(|e| {
            Failure::new(2, "toolchain", format!("cannot resolve lean: {e}"))
        })?;
        let actual_version = self
            .process("version", &["--version".to_string()])?
            .trim()
            .to_string();
        let expected_lean_sha = self
            .lock
            .get("distributions")
            .and_then(|d| d.get(&actual_version))
            .and_then(Json::as_str)
            .map(str::to_string)
            .ok_or_else(|| {
                Failure::new(
                    2,
                    "toolchain",
                    format!(
                        "Lean version/commit differs from lock: {actual_version}"
                    ),
                )
            })?;
        if digest(&self.lean)? != expected_lean_sha {
            return Err(Failure::new(
                2,
                "toolchain",
                "unsupported toolchain distribution/launcher bytes",
            ));
        }
        self.version = actual_version;

        let prefix_raw = self
            .process("prefix", &["--print-prefix".to_string()])?
            .trim()
            .to_string();
        self.prefix = fs::canonicalize(&prefix_raw).map_err(|e| {
            Failure::new(2, "toolchain", format!("cannot resolve prefix: {e}"))
        })?;

        let modules_map =
            self.lock.get("modules").unwrap().as_obj().unwrap().clone();
        let graph_map =
            self.lock.get("graph").unwrap().as_obj().unwrap().clone();
        self.foundation = modules_map.keys().cloned().collect();

        for (module, record) in &modules_map {
            let Some(rec_obj) = record.as_obj() else {
                return Err(Failure::new(
                    2,
                    "lock",
                    format!("incomplete artifact-part policy for {module}"),
                ));
            };
            let src_sha = rec_obj
                .get("sourceSha256")
                .and_then(Json::as_str)
                .unwrap_or("");
            let Some(parts_obj) = rec_obj.get("parts").and_then(Json::as_obj)
            else {
                return Err(Failure::new(
                    2,
                    "lock",
                    format!("incomplete artifact-part policy for {module}"),
                ));
            };

            let rel_mod = module.replace('.', "/");
            let source_path =
                self.prefix.join("src/lean").join(format!("{rel_mod}.lean"));
            regular(&source_path, "foundation")?;
            if digest(&source_path)? != src_sha {
                return Err(Failure::new(
                    2,
                    "foundation",
                    format!("foundation source digest mismatch: {module}"),
                ));
            }

            let mut available = BTreeMap::new();
            for (part, expected_val) in parts_obj {
                let relative = format!("{rel_mod}.{part}");
                let installed = self.prefix.join("lib/lean").join(&relative);
                if matches!(expected_val, Json::Null) {
                    if fs::symlink_metadata(&installed).is_ok() {
                        return Err(Failure::new(
                            2,
                            "foundation",
                            format!("unexpected companion part: {relative}"),
                        ));
                    }
                    continue;
                }
                let expected = expected_val.as_str().ok_or_else(|| {
                    Failure::new(
                        2,
                        "lock",
                        format!("invalid part digest for {relative}"),
                    )
                })?;
                regular(&installed, "foundation")?;
                if digest(&installed)? != expected {
                    return Err(Failure::new(
                        2,
                        "foundation",
                        format!("artifact digest mismatch: {relative}"),
                    ));
                }
                available.insert(
                    part.clone(),
                    installed.to_string_lossy().into_owned(),
                );
            }

            let olean_group: Vec<String> = PARTS[..3]
                .iter()
                .filter_map(|p| available.get(*p).cloned())
                .collect();
            let ir_group: Vec<String> = PARTS[3..]
                .iter()
                .filter_map(|p| available.get(*p).cloned())
                .collect();
            if olean_group.is_empty() {
                return Err(Failure::new(
                    2,
                    "foundation",
                    format!("missing olean for {module}"),
                ));
            }
            self.artifacts
                .insert(module.clone(), vec![olean_group, ir_group]);
        }

        self.graph = graph_map;
        Ok(())
    }

    fn compile_lean_module(
        &mut self,
        module: &str,
        src_path: &Path,
        edge_list: Vec<Json>,
        lib_subdir: &str,
        warn_as_err: bool,
    ) -> Result<(), Failure> {
        let setup_path = self.write_setup_json(module, &edge_list)?;
        let output = self
            .stage
            .join(lib_subdir)
            .join(format!("{}.olean", module.replace('.', "/")));
        if let Some(parent) = output.parent() {
            fs::create_dir_all(parent)
                .map_err(|e| Failure::new(2, "compile", e.to_string()))?;
        }
        let mut compile_args = vec![
            "-j1".to_string(),
            "-M2048".to_string(),
            "-t0".to_string(),
            "-DElab.async=false".to_string(),
            "-Ddebug.skipKernelTC=false".to_string(),
        ];
        if warn_as_err {
            compile_args.push("-DwarningAsError=true".to_string());
        }
        compile_args.extend([
            "--setup".to_string(),
            setup_path.to_string_lossy().into_owned(),
            "-o".to_string(),
            output.to_string_lossy().into_owned(),
            src_path.to_string_lossy().into_owned(),
        ]);
        self.process(&format!("compile-{module}"), &compile_args)?;
        self.record_compiled_artifacts(module, &output, edge_list)
    }

    fn record_compiled_artifacts(
        &mut self,
        module: &str,
        output: &Path,
        edge_list: Vec<Json>,
    ) -> Result<(), Failure> {
        let stem = output
            .file_name()
            .unwrap()
            .to_string_lossy()
            .strip_suffix("olean")
            .unwrap()
            .to_string();
        let parent = output.parent().unwrap();
        let mut available = BTreeMap::new();
        for part in PARTS {
            let artifact = parent.join(format!("{stem}{part}"));
            if fs::symlink_metadata(&artifact).is_ok() {
                regular(&artifact, "compile")?;
                available.insert(
                    part.to_string(),
                    artifact.to_string_lossy().into_owned(),
                );
            }
        }
        if !available.contains_key("olean") {
            return Err(Failure::new(
                2,
                "compile",
                format!("compiler omitted output for {module}"),
            ));
        }
        let olean_group: Vec<String> = PARTS[..3]
            .iter()
            .filter_map(|p| available.get(*p).cloned())
            .collect();
        let ir_group: Vec<String> = PARTS[3..]
            .iter()
            .filter_map(|p| available.get(*p).cloned())
            .collect();
        self.artifacts
            .insert(module.to_string(), vec![olean_group, ir_group]);
        self.graph.insert(module.to_string(), Json::Arr(edge_list));
        Ok(())
    }

    /// Compile `theory/`, `examples/`, and `tests/` against the audited
    /// `Trusted` artifacts and run `downstream-audit`.
    pub fn compile_and_audit_downstream(
        &mut self,
        targets: Option<&[DownstreamTarget]>,
    ) -> Result<Json, Failure> {
        let default_targets;
        let targets = match targets {
            Some(t) => t,
            None => {
                default_targets = default_downstream_targets();
                &default_targets
            }
        };

        if targets.iter().any(|t| t.path.starts_with("examples/")) {
            let examples_toolchain =
                self.checkout.join("examples/lean-toolchain");
            let examples_lakefile =
                self.checkout.join("examples/lakefile.toml");
            regular(&examples_toolchain, "downstream-input")?;
            regular(&examples_lakefile, "downstream-input")?;
            let tc_text =
                fs::read_to_string(&examples_toolchain).map_err(|e| {
                    Failure::new(2, "downstream-input", e.to_string())
                })?;
            if tc_text.trim() != TOOLCHAIN {
                return Err(Failure::new(
                    1,
                    "downstream-input",
                    "examples/lean-toolchain differs from pinned toolchain",
                ));
            }
            let lakefile_text =
                fs::read_to_string(&examples_lakefile).map_err(|e| {
                    Failure::new(2, "downstream-input", e.to_string())
                })?;
            for t in targets {
                if t.path.starts_with("examples/")
                    && !lakefile_text.contains(&format!("\"{}\"", t.module))
                {
                    return Err(Failure::new(
                        1,
                        "downstream-input",
                        format!(
                            "examples/lakefile.toml missing target {}",
                            t.module
                        ),
                    ));
                }
            }
        }

        let mut preflight_sources = Vec::new();
        for t in targets {
            let full = self.checkout.join(&t.path);
            regular(&full, "downstream-input")?;
            preflight_sources.push(Json::Arr(vec![
                Json::Str(t.module.clone()),
                Json::Str(full.to_string_lossy().into_owned()),
            ]));
        }
        let mut pf_fields = BTreeMap::new();
        pf_fields.insert(
            "graph".to_string(),
            self.lock.get("graph").unwrap().clone(),
        );
        pf_fields.insert("sources".to_string(), Json::Arr(preflight_sources));
        self.inspect("preflight", pf_fields)?;

        for t in targets {
            let edge_list: Vec<Json> = t
                .imports
                .iter()
                .map(|name| {
                    let mut m = BTreeMap::new();
                    m.insert("module".to_string(), Json::Str(name.clone()));
                    m.insert("importAll".to_string(), Json::Bool(false));
                    m.insert("isExported".to_string(), Json::Bool(true));
                    m.insert("isMeta".to_string(), Json::Bool(false));
                    Json::Obj(m)
                })
                .collect();
            let src_path = self.checkout.join(&t.path);
            self.compile_lean_module(
                &t.module,
                &src_path,
                edge_list,
                "downstream-lib",
                true,
            )?;
        }

        let mut ds_fields = BTreeMap::new();
        ds_fields.insert(
            "trusted".to_string(),
            Json::Arr(self.modules.keys().cloned().map(Json::Str).collect()),
        );
        for (key, role) in [
            ("theory", "theory"),
            ("examples", "examples"),
            ("claimModules", "claim"),
        ] {
            let list: Vec<Json> = targets
                .iter()
                .filter(|t| t.role == role)
                .map(|t| Json::Str(t.module.clone()))
                .collect();
            ds_fields.insert(key.to_string(), Json::Arr(list));
        }
        self.inspect("downstream-audit", ds_fields)
    }

    /// Run the repository boundary check (`trusted/lean/` plus optional
    /// downstream `theory/`, `examples/`, and `tests/` modules).
    pub fn run(&mut self, check_downstream: bool) -> Result<Json, Failure> {
        self.run_with_targets(check_downstream, None)
    }

    /// Run the repository boundary check with an optional custom list of
    /// downstream targets.
    pub fn run_with_targets(
        &mut self,
        check_downstream: bool,
        targets: Option<&[DownstreamTarget]>,
    ) -> Result<Json, Failure> {
        let cargo_hashes = if self.checkout.join("Cargo.toml").exists() {
            check_cargo_boundary(&self.checkout)?
        } else {
            BTreeMap::new()
        };
        self.tool_admission()?;

        let sources: Vec<Json> = self
            .modules
            .iter()
            .map(|(n, p)| {
                Json::Arr(vec![
                    Json::Str(n.clone()),
                    Json::Str(
                        self.source.join(p).to_string_lossy().into_owned(),
                    ),
                ])
            })
            .collect();
        let mut pf_fields = BTreeMap::new();
        pf_fields.insert("sources".to_string(), Json::Arr(sources));
        let pf_res = self.inspect("preflight", pf_fields)?;
        let Some(headers) = pf_res.get("headers").and_then(Json::as_arr) else {
            return Err(Failure::new(
                2,
                "preflight",
                "incomplete source-header inventory",
            ));
        };

        let mut imports_map: BTreeMap<String, Vec<Json>> = BTreeMap::new();
        self.trust_declarations.clear();
        for h in headers {
            let mod_name = h
                .get("module")
                .and_then(Json::as_str)
                .unwrap_or("")
                .to_string();
            if let Some(decls) =
                h.get("trustDeclarations").and_then(Json::as_arr)
            {
                self.trust_declarations.extend(decls.iter().cloned());
            }
            let edges = h
                .get("imports")
                .and_then(Json::as_arr)
                .unwrap()
                .to_vec();
            for edge in &edges {
                let imp_mod = edge
                    .get("module")
                    .and_then(Json::as_str)
                    .unwrap_or("");
                if !self.artifacts.contains_key(imp_mod)
                    && !self.modules.contains_key(imp_mod)
                {
                    return Err(Failure::new(
                        1,
                        "preflight",
                        format!("foreign/missing import {imp_mod} in {mod_name}"),
                    ));
                }
            }
            imports_map.insert(mod_name, edges);
        }

        let mut pending: BTreeSet<String> =
            self.modules.keys().cloned().collect();
        let mut order = Vec::new();
        while !pending.is_empty() {
            let ready: Vec<String> = pending
                .iter()
                .filter(|n| {
                    imports_map[*n].iter().all(|e| {
                        let m = e.get("module").and_then(Json::as_str).unwrap();
                        !pending.contains(m)
                    })
                })
                .cloned()
                .collect();
            if ready.is_empty() {
                return Err(Failure::new(
                    1,
                    "preflight",
                    "Trusted import cycle",
                ));
            }
            for r in &ready {
                pending.remove(r);
            }
            order.extend(ready);
        }

        for (k, v) in &imports_map {
            self.graph.insert(k.clone(), Json::Arr(v.clone()));
        }

        for module in &order {
            let edge_list = imports_map[module].clone();
            let raw_src_path = self.source.join(&self.modules[module]);
            self.execution_began = true;
            self.compile_lean_module(
                module,
                &raw_src_path,
                edge_list,
                "lib",
                false,
            )?;
        }

        let mut audit_fields = BTreeMap::new();
        audit_fields.insert(
            "trusted".to_string(),
            Json::Arr(self.modules.keys().cloned().map(Json::Str).collect()),
        );
        audit_fields.insert(
            "trustDeclarations".to_string(),
            Json::Arr(self.trust_declarations.clone()),
        );
        let mut report = self.inspect("audit", audit_fields)?;

        if check_downstream {
            let downstream = self.compile_and_audit_downstream(targets)?;
            report
                .as_obj_mut()
                .unwrap()
                .insert("downstream".to_string(), downstream);
        }

        let mut combined_tools = BTreeMap::new();
        for (k, v) in &self.tool_hashes {
            combined_tools.insert(k.clone(), Json::Str(v.clone()));
        }
        for (k, v) in &cargo_hashes {
            combined_tools.insert(k.clone(), Json::Str(v.clone()));
        }

        let rep_obj = report.as_obj_mut().unwrap();
        rep_obj.insert(
            "sourceSha256".to_string(),
            Json::Str(fingerprint(&Json::Obj(self.initial.clone()))),
        );
        rep_obj.insert(
            "toolsSha256".to_string(),
            Json::Str(fingerprint(&Json::Obj(combined_tools))),
        );
        rep_obj.insert(
            "toolchain".to_string(),
            Json::Str(self.version.clone()),
        );
        rep_obj.insert(
            "guarantee".to_string(),
            Json::Str(
                "kernel dependency closure, statement-origin separation, and Cargo DAG boundary"
                    .to_string(),
            ),
        );

        fs::write(
            self.stage.join("report.json"),
            report.to_pretty_string().as_bytes(),
        )
        .map_err(|e| Failure::new(2, "audit", e.to_string()))?;
        self.budget()?;
        Ok(report)
    }

}

fn dir_byte_size(root: &Path) -> io::Result<u64> {
    let mut total = 0u64;
    let mut stack = vec![root.to_path_buf()];
    while let Some(dir) = stack.pop() {
        for entry in fs::read_dir(dir)? {
            let entry = entry?;
            let meta = fs::symlink_metadata(entry.path())?;
            if meta.file_type().is_dir() && !meta.file_type().is_symlink() {
                stack.push(entry.path());
            } else if meta.file_type().is_file() {
                total = total.saturating_add(meta.len());
            }
        }
    }
    Ok(total)
}
