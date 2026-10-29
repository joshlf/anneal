//! Toolchain-independent capture manifest schemas, SHA-256 hashing, and JSON
//! serialization for `anneal-rustc-capture` (#99 §3, #103 §5).
//!
//! Two manifest artifacts coordinate parallel Cargo compilation with
//! `trusted/audit/`:
//!
//! - `UnitCaptureManifest`: written by each `anneal-rustc-capture` invocation
//!   into
//!   `<ANNEAL_CAPTURE_DIR>/<crate>-<disambiguator>/UnitCaptureManifest.json`
//!   when Cargo compiles a crate graph in parallel.
//! - `CaptureManifest`: the root cryptographic handshake aggregated from unit
//!   manifests and verified by `trusted/audit/check_trusted.py` before compiled
//!   `.olean` proofs are accepted.

use std::collections::BTreeMap;

/// Environment variable specifying the directory where per-unit capture
/// manifests and generated `Mir/<Item>.lean` modules are written.
pub const ANNEAL_CAPTURE_DIR_ENV: &str = "ANNEAL_CAPTURE_DIR";

/// Environment variable specifying comma-separated substring patterns used to
/// filter which crate items are extracted during `anneal-rustc-capture`.
pub const ANNEAL_CAPTURE_FILTER_ENV: &str = "ANNEAL_CAPTURE_FILTER";

/// Pinned MIR dialect identifier for
/// `rustc 1.98.0-nightly (14210df0e 2026-05-31)`.
pub const MIR_DIALECT_V2026_06_01: &str = "V2026_06_01";

/// Pinned `rustc` git commit SHA for `nightly-2026-06-01`.
pub const RUSTC_COMMIT_SHA: &str = "14210df0e27ccd7d9e6a05b8085cbd438e4bbc65";

/// Expected `rustc --version` prefix for the `V2026_06_01` backend.
pub const RUSTC_VERSION_STRING: &str = "rustc 1.98.0-nightly (14210df0e 2026-05-31)";

/// Role of a captured item in Anneal's specification and verification pipeline
/// (#103 §3.2).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CapturedItemKind {
    /// Subject Rust item whose operational behavior is being verified.
    Subject,
    /// Synthetic precondition function lowered by `anodized`
    /// (`__anodized_fn_requires_*`).
    InlineSpecRequires,
    /// Synthetic postcondition function lowered by `anodized`
    /// (`__anodized_fn_ensures_*`).
    InlineSpecEnsures,
    /// Synthetic qualifier bitmask constant lowered by `anodized`
    /// (`__anodized_fn_qualifiers_*`).
    InlineSpecQualifiers,
    /// External sidecar specification (`#[anneal::external_spec(for = ...)]`).
    ExternalSpec,
    /// Ghost or mathematical helper item (`#[anneal::model]`).
    Model,
    /// Type invariant predicate lowered by `#[anneal_spec::invariant(...)]`
    /// (`__anneal_type_invariant_*`).
    TypeInvariant,
    /// Safety witness lowered by `#[anneal_spec::unsafe_impl(...)]`
    /// (`__anneal_unsafe_impl_*`).
    UnsafeTraitImpl,
}

impl CapturedItemKind {
    /// Returns the stable string tag stored in `UnitCaptureManifest.json`.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Subject => "subject",
            Self::InlineSpecRequires => "inline_spec_requires",
            Self::InlineSpecEnsures => "inline_spec_ensures",
            Self::InlineSpecQualifiers => "inline_spec_qualifiers",
            Self::ExternalSpec => "external_spec",
            Self::Model => "model",
            Self::TypeInvariant => "type_invariant",
            Self::UnsafeTraitImpl => "unsafe_trait_impl",
        }
    }

    /// Parses a `CapturedItemKind` from its stable JSON tag.
    pub fn from_str_tag(tag: &str) -> Option<Self> {
        match tag {
            "subject" => Some(Self::Subject),
            "inline_spec_requires" => Some(Self::InlineSpecRequires),
            "inline_spec_ensures" => Some(Self::InlineSpecEnsures),
            "inline_spec_qualifiers" => Some(Self::InlineSpecQualifiers),
            "external_spec" => Some(Self::ExternalSpec),
            "model" => Some(Self::Model),
            "type_invariant" => Some(Self::TypeInvariant),
            "unsafe_trait_impl" | "unsafe_impl" => Some(Self::UnsafeTraitImpl),
            _ => None,
        }
    }
}

/// A single captured item and its generated `Mir/<Item>.lean` module digest as
/// required by `trusted/audit/check_trusted.py`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CapturedTarget {
    /// Canonical item identifier (`DefId` path) within the crate.
    pub def_id: String,
    /// Relative path to the read-only generated `Mir/<Item>.lean` module.
    pub mir_module_path: String,
    /// SHA-256 hex digest of the generated `Mir/<Item>.lean` file.
    pub mir_module_sha256: String,
}

/// Extended per-item metadata recorded by `anneal-rustc-capture` in
/// `UnitCaptureManifest.json` so `cargo-anneal` can assemble obligation and
/// verification modules without re-parsing Rust or Lean source.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct UnitTargetRecord {
    /// Underlying `CapturedTarget` entry included in the root
    /// `CaptureManifest`.
    pub target: CapturedTarget,
    /// Dotted Lean module name (e.g., `Mir.MyCrate.foo`).
    pub lean_module_name: String,
    /// Role of this item in verification (subject code vs. specification).
    pub item_kind: CapturedItemKind,
    /// For specification items (`InlineSpec*`, `ExternalSpec`), the canonical
    /// `def_id` of the subject item to which this contract attaches.
    pub associated_subject_def_id: Option<String>,
}

/// Per-compilation-unit manifest written by a single `anneal-rustc-capture`
/// process during a parallel Cargo build.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct UnitCaptureManifest {
    /// Schema version of the unit manifest.
    pub schema: u32,
    /// Crate name passed to `rustc --crate-name`.
    pub crate_name: String,
    /// Unique compilation unit identifier (`<crate_name>-<disambiguator>`).
    pub unit_id: String,
    /// Exact `rustc` version string that produced this unit.
    pub rustc_version: String,
    /// MIR dialect identifier used in the emitted Lean modules.
    pub mir_dialect: String,
    /// True only after `rustc` completes compilation of this crate unit with
    /// zero errors.
    pub compilation_succeeded: bool,
    /// Relative path and SHA-256 hex digest of every `.rs` input file in this
    /// crate unit.
    pub rust_sources: Vec<(String, String)>,
    /// Extracted items and contract metadata for this compilation unit.
    pub unit_targets: Vec<UnitTargetRecord>,
}

impl UnitCaptureManifest {
    /// Current unit manifest schema version.
    pub const SCHEMA_VERSION: u32 = 1;

    /// Projects a unit manifest's targets into root `CapturedTarget` entries.
    pub fn into_captured_targets(&self) -> Vec<CapturedTarget> {
        self.unit_targets.iter().map(|r| r.target.clone()).collect()
    }

    /// Serializes this unit manifest to a deterministic JSON string without
    /// external crate dependencies.
    pub fn to_json_string(&self) -> String {
        let mut out = String::from("{\n");
        out.push_str(&format!("  \"schema\": {},\n", self.schema));
        out.push_str(&format!(
            "  \"crate_name\": \"{}\",\n",
            escape_json(&self.crate_name)
        ));
        out.push_str(&format!(
            "  \"unit_id\": \"{}\",\n",
            escape_json(&self.unit_id)
        ));
        out.push_str(&format!(
            "  \"rustc_version\": \"{}\",\n",
            escape_json(&self.rustc_version)
        ));
        out.push_str(&format!(
            "  \"mir_dialect\": \"{}\",\n",
            escape_json(&self.mir_dialect)
        ));
        out.push_str(&format!(
            "  \"compilation_succeeded\": {},\n",
            if self.compilation_succeeded { "true" } else { "false" }
        ));
        out.push_str("  \"rust_sources\": [\n");
        for (i, (path, hash)) in self.rust_sources.iter().enumerate() {
            let comma = if i + 1 < self.rust_sources.len() { "," } else { "" };
            out.push_str(&format!(
                "    [\"{}\", \"{}\"]{}\n",
                escape_json(path),
                escape_json(hash),
                comma
            ));
        }
        out.push_str("  ],\n");
        out.push_str("  \"unit_targets\": [\n");
        for (i, rec) in self.unit_targets.iter().enumerate() {
            let comma = if i + 1 < self.unit_targets.len() { "," } else { "" };
            out.push_str("    {\n");
            out.push_str("      \"target\": {\n");
            out.push_str(&format!(
                "        \"def_id\": \"{}\",\n",
                escape_json(&rec.target.def_id)
            ));
            out.push_str(&format!(
                "        \"mir_module_path\": \"{}\",\n",
                escape_json(&rec.target.mir_module_path)
            ));
            out.push_str(&format!(
                "        \"mir_module_sha256\": \"{}\"\n",
                escape_json(&rec.target.mir_module_sha256)
            ));
            out.push_str("      },\n");
            out.push_str(&format!(
                "      \"lean_module_name\": \"{}\",\n",
                escape_json(&rec.lean_module_name)
            ));
            out.push_str(&format!(
                "      \"item_kind\": \"{}\",\n",
                escape_json(rec.item_kind.as_str())
            ));
            match &rec.associated_subject_def_id {
                Some(subj) => out.push_str(&format!(
                    "      \"associated_subject_def_id\": \"{}\"\n",
                    escape_json(subj)
                )),
                None => out.push_str("      \"associated_subject_def_id\": null\n"),
            }
            out.push_str(&format!("    }}{comma}\n"));
        }
        out.push_str("  ]\n}\n");
        out
    }

    /// Parses a `UnitCaptureManifest` from its JSON representation.
    pub fn from_json_str(input: &str) -> Result<Self, String> {
        let root = parse_json_str(input)?;
        let obj = root
            .as_object()
            .ok_or_else(|| String::from("expected top-level JSON object"))?;

        let schema = get_u32_field(obj, "schema")?;
        let crate_name = get_string_field(obj, "crate_name")?;
        let unit_id = get_string_field(obj, "unit_id")?;
        let rustc_version = get_string_field(obj, "rustc_version")?;
        let mir_dialect = get_string_field(obj, "mir_dialect")?;
        let compilation_succeeded = get_bool_field(obj, "compilation_succeeded")?;
        let rust_sources = parse_rust_sources(obj)?;

        let targets_val = obj
            .get("unit_targets")
            .ok_or_else(|| String::from("missing field 'unit_targets'"))?;
        let targets_arr = targets_val
            .as_array()
            .ok_or_else(|| String::from("field 'unit_targets' must be an array"))?;

        let mut unit_targets = Vec::with_capacity(targets_arr.len());
        for entry in targets_arr {
            let entry_obj = entry
                .as_object()
                .ok_or_else(|| String::from("unit_targets entry must be an object"))?;
            let target = if let Some(nested) = entry_obj.get("target") {
                let nested_obj = nested
                    .as_object()
                    .ok_or_else(|| String::from("field 'target' must be an object"))?;
                parse_captured_target(nested_obj)?
            } else {
                parse_captured_target(entry_obj)?
            };
            let lean_module_name = get_string_field(entry_obj, "lean_module_name")?;
            let item_kind_str = get_string_field(entry_obj, "item_kind")?;
            let item_kind = CapturedItemKind::from_str_tag(&item_kind_str)
                .ok_or_else(|| format!("unknown item_kind '{item_kind_str}'"))?;
            let associated_subject_def_id = match entry_obj.get("associated_subject_def_id") {
                None | Some(JsonValue::Null) => None,
                Some(JsonValue::String(s)) => Some(s.clone()),
                Some(_) => {
                    return Err(String::from(
                        "field 'associated_subject_def_id' must be a string or null",
                    ));
                }
            };
            unit_targets.push(UnitTargetRecord {
                target,
                lean_module_name,
                item_kind,
                associated_subject_def_id,
            });
        }

        Ok(Self {
            schema,
            crate_name,
            unit_id,
            rustc_version,
            mir_dialect,
            compilation_succeeded,
            rust_sources,
            unit_targets,
        })
    }
}

/// Cryptographic handshake written by `anneal-rustc-capture` (or aggregated by
/// `cargo-anneal`) and verified by `trusted/audit/` before accepting compiled
/// `.olean` proofs (#103 §5).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CaptureManifest {
    /// Schema version of the capture manifest.
    pub schema: u32,
    /// True only after `rustc` completes compilation of the crate (including
    /// post-monomorphization checks) with zero errors (#99 §3).
    pub compilation_succeeded: bool,
    /// Relative path and SHA-256 hex digest of every `.rs` input file.
    pub rust_sources: Vec<(String, String)>,
    /// Verification targets extracted for this compilation unit.
    pub targets: Vec<CapturedTarget>,
}

impl CaptureManifest {
    /// Current manifest schema version.
    pub const SCHEMA_VERSION: u32 = 1;

    /// Serializes this manifest to the deterministic JSON representation
    /// checked by `trusted/audit/check_trusted.py`.
    pub fn to_json_string(&self) -> String {
        let mut out = String::from("{\n");
        out.push_str(&format!("  \"schema\": {},\n", self.schema));
        out.push_str(&format!(
            "  \"compilation_succeeded\": {},\n",
            if self.compilation_succeeded { "true" } else { "false" }
        ));
        out.push_str("  \"rust_sources\": [\n");
        for (i, (path, hash)) in self.rust_sources.iter().enumerate() {
            let comma = if i + 1 < self.rust_sources.len() { "," } else { "" };
            out.push_str(&format!(
                "    [\"{}\", \"{}\"]{}\n",
                escape_json(path),
                escape_json(hash),
                comma
            ));
        }
        out.push_str("  ],\n");
        out.push_str("  \"targets\": [\n");
        for (i, t) in self.targets.iter().enumerate() {
            let comma = if i + 1 < self.targets.len() { "," } else { "" };
            out.push_str("    {\n");
            out.push_str(&format!(
                "      \"def_id\": \"{}\",\n",
                escape_json(&t.def_id)
            ));
            out.push_str(&format!(
                "      \"mir_module_path\": \"{}\",\n",
                escape_json(&t.mir_module_path)
            ));
            out.push_str(&format!(
                "      \"mir_module_sha256\": \"{}\"\n",
                escape_json(&t.mir_module_sha256)
            ));
            out.push_str(&format!("    }}{comma}\n"));
        }
        out.push_str("  ]\n}\n");
        out
    }

    /// Parses a `CaptureManifest` from its JSON representation.
    pub fn from_json_str(input: &str) -> Result<Self, String> {
        let root = parse_json_str(input)?;
        let obj = root
            .as_object()
            .ok_or_else(|| String::from("expected top-level JSON object"))?;

        let schema = get_u32_field(obj, "schema")?;
        let compilation_succeeded = get_bool_field(obj, "compilation_succeeded")?;
        let rust_sources = parse_rust_sources(obj)?;

        let targets_val = obj
            .get("targets")
            .ok_or_else(|| String::from("missing field 'targets'"))?;
        let targets_arr = targets_val
            .as_array()
            .ok_or_else(|| String::from("field 'targets' must be an array"))?;

        let mut targets = Vec::with_capacity(targets_arr.len());
        for entry in targets_arr {
            let entry_obj = entry
                .as_object()
                .ok_or_else(|| String::from("targets entry must be an object"))?;
            targets.push(parse_captured_target(entry_obj)?);
        }

        Ok(Self {
            schema,
            compilation_succeeded,
            rust_sources,
            targets,
        })
    }
}

/// Minimal dependency-free JSON AST used to parse `CaptureManifest` and
/// `UnitCaptureManifest` artifacts.
#[derive(Clone, Debug, PartialEq, Eq)]
enum JsonValue {
    Null,
    Bool(bool),
    Number(u64),
    String(String),
    Array(Vec<JsonValue>),
    Object(BTreeMap<String, JsonValue>),
}

impl JsonValue {
    fn as_object(&self) -> Option<&BTreeMap<String, JsonValue>> {
        match self {
            Self::Object(map) => Some(map),
            _ => None,
        }
    }

    fn as_array(&self) -> Option<&[JsonValue]> {
        match self {
            Self::Array(arr) => Some(arr),
            _ => None,
        }
    }

    fn as_str(&self) -> Option<&str> {
        match self {
            Self::String(s) => Some(s),
            _ => None,
        }
    }
}

fn get_string_field(obj: &BTreeMap<String, JsonValue>, key: &str) -> Result<String, String> {
    match obj.get(key) {
        Some(JsonValue::String(s)) => Ok(s.clone()),
        Some(_) => Err(format!("field '{key}' must be a string")),
        None => Err(format!("missing field '{key}'")),
    }
}

fn get_u32_field(obj: &BTreeMap<String, JsonValue>, key: &str) -> Result<u32, String> {
    match obj.get(key) {
        Some(JsonValue::Number(n)) => {
            u32::try_from(*n).map_err(|_| format!("field '{key}' out of u32 range"))
        }
        Some(_) => Err(format!("field '{key}' must be an integer")),
        None => Err(format!("missing field '{key}'")),
    }
}

fn get_bool_field(obj: &BTreeMap<String, JsonValue>, key: &str) -> Result<bool, String> {
    match obj.get(key) {
        Some(JsonValue::Bool(b)) => Ok(*b),
        Some(_) => Err(format!("field '{key}' must be a boolean")),
        None => Err(format!("missing field '{key}'")),
    }
}

fn parse_rust_sources(obj: &BTreeMap<String, JsonValue>) -> Result<Vec<(String, String)>, String> {
    let val = obj
        .get("rust_sources")
        .ok_or_else(|| String::from("missing field 'rust_sources'"))?;
    let arr = val
        .as_array()
        .ok_or_else(|| String::from("field 'rust_sources' must be an array"))?;
    let mut sources = Vec::with_capacity(arr.len());
    for item in arr {
        let pair = item
            .as_array()
            .ok_or_else(|| String::from("rust_sources entry must be a 2-element array"))?;
        if pair.len() != 2 {
            return Err(String::from("rust_sources entry must have exactly 2 elements"));
        }
        let path = pair[0]
            .as_str()
            .ok_or_else(|| String::from("rust_sources path must be a string"))?;
        let hash = pair[1]
            .as_str()
            .ok_or_else(|| String::from("rust_sources digest must be a string"))?;
        sources.push((path.to_owned(), hash.to_owned()));
    }
    Ok(sources)
}

fn parse_captured_target(obj: &BTreeMap<String, JsonValue>) -> Result<CapturedTarget, String> {
    Ok(CapturedTarget {
        def_id: get_string_field(obj, "def_id")?,
        mir_module_path: get_string_field(obj, "mir_module_path")?,
        mir_module_sha256: get_string_field(obj, "mir_module_sha256")?,
    })
}

struct JsonParser<'a> {
    bytes: &'a [u8],
    pos: usize,
}

impl<'a> JsonParser<'a> {
    fn new(input: &'a str) -> Self {
        Self {
            bytes: input.as_bytes(),
            pos: 0,
        }
    }

    fn skip_whitespace(&mut self) {
        while self.pos < self.bytes.len() {
            match self.bytes[self.pos] {
                b' ' | b'\t' | b'\n' | b'\r' => self.pos += 1,
                _ => break,
            }
        }
    }

    fn peek(&mut self) -> Option<u8> {
        self.skip_whitespace();
        self.bytes.get(self.pos).copied()
    }

    fn parse_value(&mut self) -> Result<JsonValue, String> {
        let ch = self
            .peek()
            .ok_or_else(|| String::from("unexpected end of JSON input"))?;
        match ch {
            b'{' => self.parse_object(),
            b'[' => self.parse_array(),
            b'"' => self.parse_string().map(JsonValue::String),
            b't' | b'f' => self.parse_bool(),
            b'n' => self.parse_null(),
            b'0'..=b'9' => self.parse_number(),
            _ => Err(format!(
                "unexpected byte 0x{ch:02x} at byte offset {}",
                self.pos
            )),
        }
    }

    fn parse_object(&mut self) -> Result<JsonValue, String> {
        self.pos += 1;
        let mut map = BTreeMap::new();
        if self.peek() == Some(b'}') {
            self.pos += 1;
            return Ok(JsonValue::Object(map));
        }
        loop {
            if self.peek() != Some(b'"') {
                return Err(format!("expected string key at offset {}", self.pos));
            }
            let key = self.parse_string()?;
            if self.peek() != Some(b':') {
                return Err(format!("expected ':' after key at offset {}", self.pos));
            }
            self.pos += 1;
            let val = self.parse_value()?;
            map.insert(key, val);
            match self.peek() {
                Some(b',') => self.pos += 1,
                Some(b'}') => {
                    self.pos += 1;
                    return Ok(JsonValue::Object(map));
                }
                _ => {
                    return Err(format!(
                        "expected ',' or '}}' in object at offset {}",
                        self.pos
                    ))
                }
            }
        }
    }

    fn parse_array(&mut self) -> Result<JsonValue, String> {
        self.pos += 1;
        let mut arr = Vec::new();
        if self.peek() == Some(b']') {
            self.pos += 1;
            return Ok(JsonValue::Array(arr));
        }
        loop {
            arr.push(self.parse_value()?);
            match self.peek() {
                Some(b',') => self.pos += 1,
                Some(b']') => {
                    self.pos += 1;
                    return Ok(JsonValue::Array(arr));
                }
                _ => {
                    return Err(format!(
                        "expected ',' or ']' in array at offset {}",
                        self.pos
                    ))
                }
            }
        }
    }

    fn parse_string(&mut self) -> Result<String, String> {
        self.skip_whitespace();
        if self.bytes.get(self.pos) != Some(&b'"') {
            return Err(format!("expected '\"' at offset {}", self.pos));
        }
        self.pos += 1;
        let mut bytes = Vec::new();
        while self.pos < self.bytes.len() {
            let b = self.bytes[self.pos];
            self.pos += 1;
            match b {
                b'"' => {
                    return String::from_utf8(bytes)
                        .map_err(|_| String::from("invalid UTF-8 in JSON string"));
                }
                b'\\' => {
                    let esc = *self
                        .bytes
                        .get(self.pos)
                        .ok_or_else(|| String::from("unterminated escape sequence"))?;
                    self.pos += 1;
                    match esc {
                        b'"' => bytes.push(b'"'),
                        b'\\' => bytes.push(b'\\'),
                        b'/' => bytes.push(b'/'),
                        b'b' => bytes.push(0x08),
                        b'f' => bytes.push(0x0c),
                        b'n' => bytes.push(b'\n'),
                        b'r' => bytes.push(b'\r'),
                        b't' => bytes.push(b'\t'),
                        b'u' => {
                            if self.pos + 4 > self.bytes.len() {
                                return Err(String::from("short \\uXXXX escape"));
                            }
                            let hex = std::str::from_utf8(&self.bytes[self.pos..self.pos + 4])
                                .map_err(|_| String::from("invalid hex in \\uXXXX escape"))?;
                            let code = u32::from_str_radix(hex, 16)
                                .map_err(|_| String::from("invalid hex digits in \\uXXXX"))?;
                            self.pos += 4;
                            let ch = char::from_u32(code)
                                .ok_or_else(|| String::from("invalid Unicode scalar in \\uXXXX"))?;
                            let mut buf = [0u8; 4];
                            bytes.extend_from_slice(ch.encode_utf8(&mut buf).as_bytes());
                        }
                        other => {
                            return Err(format!("invalid JSON escape '\\{}'", other as char));
                        }
                    }
                }
                c => bytes.push(c),
            }
        }
        Err(String::from("unterminated JSON string"))
    }

    fn parse_bool(&mut self) -> Result<JsonValue, String> {
        self.skip_whitespace();
        if self.bytes[self.pos..].starts_with(b"true") {
            self.pos += 4;
            Ok(JsonValue::Bool(true))
        } else if self.bytes[self.pos..].starts_with(b"false") {
            self.pos += 5;
            Ok(JsonValue::Bool(false))
        } else {
            Err(format!("invalid boolean literal at offset {}", self.pos))
        }
    }

    fn parse_null(&mut self) -> Result<JsonValue, String> {
        self.skip_whitespace();
        if self.bytes[self.pos..].starts_with(b"null") {
            self.pos += 4;
            Ok(JsonValue::Null)
        } else {
            Err(format!("invalid null literal at offset {}", self.pos))
        }
    }

    fn parse_number(&mut self) -> Result<JsonValue, String> {
        self.skip_whitespace();
        let start = self.pos;
        while self.pos < self.bytes.len() && self.bytes[self.pos].is_ascii_digit() {
            self.pos += 1;
        }
        let s = std::str::from_utf8(&self.bytes[start..self.pos])
            .map_err(|_| String::from("invalid number bytes"))?;
        let n = s
            .parse::<u64>()
            .map_err(|_| format!("invalid integer literal '{s}'"))?;
        Ok(JsonValue::Number(n))
    }
}

fn parse_json_str(input: &str) -> Result<JsonValue, String> {
    let mut parser = JsonParser::new(input);
    let val = parser.parse_value()?;
    parser.skip_whitespace();
    if parser.pos != parser.bytes.len() {
        return Err(format!("trailing characters at offset {}", parser.pos));
    }
    Ok(val)
}

/// Escapes a string for inclusion inside a JSON string literal.
pub fn escape_json(input: &str) -> String {
    let mut out = String::with_capacity(input.len());
    for ch in input.chars() {
        match ch {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if c.is_control() => out.push_str(&format!("\\u{:04x}", c as u32)),
            c => out.push(c),
        }
    }
    out
}

/// Computes the lowercase hex-encoded FIPS 180-4 SHA-256 digest of `data`
/// without pulling external crates into `trusted/rustc-capture`.
pub fn sha256_hex(data: &[u8]) -> String {
    const K: [u32; 64] = [
        0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4,
        0xab1c5ed5, 0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe,
        0x9bdc06a7, 0xc19bf174, 0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f,
        0x4a7484aa, 0x5cb0a9dc, 0x76f988da, 0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7,
        0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967, 0x27b70a85, 0x2e1b2138, 0x4d2c6dfc,
        0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85, 0xa2bfe8a1, 0xa81a664b,
        0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070, 0x19a4c116,
        0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
        0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7,
        0xc67178f2,
    ];
    let mut h: [u32; 8] = [
        0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab,
        0x5be0cd19,
    ];

    let bit_len = (data.len() as u64) * 8;
    let mut padded = Vec::with_capacity(data.len() + 72);
    padded.extend_from_slice(data);
    padded.push(0x80);
    while (padded.len() % 64) != 56 {
        padded.push(0);
    }
    padded.extend_from_slice(&bit_len.to_be_bytes());

    for chunk in padded.chunks_exact(64) {
        let mut w = [0u32; 64];
        for i in 0..16 {
            w[i] = u32::from_be_bytes([
                chunk[4 * i],
                chunk[4 * i + 1],
                chunk[4 * i + 2],
                chunk[4 * i + 3],
            ]);
        }
        for i in 16..64 {
            let s0 = w[i - 15].rotate_right(7) ^ w[i - 15].rotate_right(18) ^ (w[i - 15] >> 3);
            let s1 = w[i - 2].rotate_right(17) ^ w[i - 2].rotate_right(19) ^ (w[i - 2] >> 10);
            w[i] = w[i - 16]
                .wrapping_add(s0)
                .wrapping_add(w[i - 7])
                .wrapping_add(s1);
        }
        let [mut a, mut b, mut c, mut d, mut e, mut f, mut g, mut hh] = h;
        for i in 0..64 {
            let s1 = e.rotate_right(6) ^ e.rotate_right(11) ^ e.rotate_right(25);
            let ch = (e & f) ^ ((!e) & g);
            let temp1 = hh
                .wrapping_add(s1)
                .wrapping_add(ch)
                .wrapping_add(K[i])
                .wrapping_add(w[i]);
            let s0 = a.rotate_right(2) ^ a.rotate_right(13) ^ a.rotate_right(22);
            let maj = (a & b) ^ (a & c) ^ (b & c);
            let temp2 = s0.wrapping_add(maj);

            hh = g;
            g = f;
            f = e;
            e = d.wrapping_add(temp1);
            d = c;
            c = b;
            b = a;
            a = temp1.wrapping_add(temp2);
        }
        h[0] = h[0].wrapping_add(a);
        h[1] = h[1].wrapping_add(b);
        h[2] = h[2].wrapping_add(c);
        h[3] = h[3].wrapping_add(d);
        h[4] = h[4].wrapping_add(e);
        h[5] = h[5].wrapping_add(f);
        h[6] = h[6].wrapping_add(g);
        h[7] = h[7].wrapping_add(hh);
    }

    let mut hex = String::with_capacity(64);
    for word in h {
        hex.push_str(&format!("{word:08x}"));
    }
    hex
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sha256_empty_and_abc_vectors() {
        assert_eq!(
            sha256_hex(b""),
            "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
        );
        assert_eq!(
            sha256_hex(b"abc"),
            "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
        );
    }

    #[test]
    fn capture_manifest_round_trip() {
        let manifest = CaptureManifest {
            schema: CaptureManifest::SCHEMA_VERSION,
            compilation_succeeded: true,
            rust_sources: vec![(
                String::from("src/lib.rs"),
                sha256_hex(b"pub fn answer() -> u32 { 42 }\n"),
            )],
            targets: vec![CapturedTarget {
                def_id: String::from("demo::answer"),
                mir_module_path: String::from("Mir/Demo/answer.lean"),
                mir_module_sha256: sha256_hex(b"prelude\n"),
            }],
        };

        let json = manifest.to_json_string();
        let parsed = CaptureManifest::from_json_str(&json).expect("valid CaptureManifest JSON");
        assert_eq!(parsed, manifest);
    }

    #[test]
    fn unit_capture_manifest_round_trip() {
        let unit = UnitCaptureManifest {
            schema: UnitCaptureManifest::SCHEMA_VERSION,
            crate_name: String::from("demo"),
            unit_id: String::from("demo-0123456789abcdef"),
            rustc_version: String::from(RUSTC_VERSION_STRING),
            mir_dialect: String::from(MIR_DIALECT_V2026_06_01),
            compilation_succeeded: true,
            rust_sources: vec![(String::from("src/lib.rs"), sha256_hex(b"fn f() {}"))],
            unit_targets: vec![
                UnitTargetRecord {
                    target: CapturedTarget {
                        def_id: String::from("demo::f"),
                        mir_module_path: String::from("Mir/Demo/f.lean"),
                        mir_module_sha256: sha256_hex(b"prelude\n"),
                    },
                    lean_module_name: String::from("Mir.Demo.f"),
                    item_kind: CapturedItemKind::Subject,
                    associated_subject_def_id: None,
                },
                UnitTargetRecord {
                    target: CapturedTarget {
                        def_id: String::from("demo::__anodized_fn_requires_f"),
                        mir_module_path: String::from("Mir/Demo/__anodized_fn_requires_f.lean"),
                        mir_module_sha256: sha256_hex(b"prelude\n"),
                    },
                    lean_module_name: String::from("Mir.Demo.__anodized_fn_requires_f"),
                    item_kind: CapturedItemKind::InlineSpecRequires,
                    associated_subject_def_id: Some(String::from("demo::f")),
                },
                UnitTargetRecord {
                    target: CapturedTarget {
                        def_id: String::from(
                            "demo::Positive::__anneal_type_invariant_positive",
                        ),
                        mir_module_path: String::from(
                            "Mir/Demo/Positive___anneal_type_invariant_positive.lean",
                        ),
                        mir_module_sha256: sha256_hex(b"prelude\n"),
                    },
                    lean_module_name: String::from(
                        "Mir.Demo.Positive___anneal_type_invariant_positive",
                    ),
                    item_kind: CapturedItemKind::TypeInvariant,
                    associated_subject_def_id: Some(String::from("demo::Positive")),
                },
                UnitTargetRecord {
                    target: CapturedTarget {
                        def_id: String::from("demo::__anneal_unsafe_impl_Zeroable_for_Positive"),
                        mir_module_path: String::from(
                            "Mir/Demo/__anneal_unsafe_impl_Zeroable_for_Positive.lean",
                        ),
                        mir_module_sha256: sha256_hex(b"prelude\n"),
                    },
                    lean_module_name: String::from(
                        "Mir.Demo.__anneal_unsafe_impl_Zeroable_for_Positive",
                    ),
                    item_kind: CapturedItemKind::UnsafeTraitImpl,
                    associated_subject_def_id: Some(String::from("Zeroable::Positive")),
                },
            ],
        };

        let json = unit.to_json_string();
        let parsed =
            UnitCaptureManifest::from_json_str(&json).expect("valid UnitCaptureManifest JSON");
        assert_eq!(parsed, unit);
        assert_eq!(parsed.into_captured_targets().len(), 4);
    }
}
