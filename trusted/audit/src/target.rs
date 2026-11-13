// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Exact-root acceptance for an external, source-authenticated proof workspace.
//!
//! The trusted runner owns Model, Capture, Specification and Expected inputs.
//! Only Proof sources and the submitted theorem name come from the proof
//! producer. This API does not establish that a caller's chosen model or
//! specification matches human intent. It authenticates those choices and
//! checks their separation from the unreviewed proof implementation.

use super::*;

/// The authority of a source module in a target verification request.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub enum TargetRole {
    /// Installed primitive semantics and the canonical verification roots.
    Model,
    /// Reviewed mathematical specifications and their authored helpers.
    Specification,
    /// Runner-generated, closed captured program data.
    Capture,
    /// Runner-generated expected proposition, independent of proof sources.
    Expected,
    /// Authored proofs, checked theory, tactics and other proof libraries.
    Proof,
}

impl TargetRole {
    /// Proofs may depend on reviewed inputs, but the reverse direction would
    /// let an unreviewed helper redefine the claim. Check this relation before
    /// elaboration and again over actual compiled declaration edges: an import
    /// graph alone cannot establish every dependency's origin. Changes must
    /// preserve both enforcement points.
    fn allows(self, other: Self) -> bool {
        match self {
            Self::Model => other == Self::Model,
            Self::Capture => matches!(other, Self::Model | Self::Capture),
            Self::Specification => {
                matches!(other, Self::Model | Self::Specification)
            }
            Self::Expected => other != Self::Proof,
            Self::Proof => true,
        }
    }
}

/// A read-only source input, authenticated before it is privately staged.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct TargetModule {
    /// Module label in the ASCII dotted-name protocol of [`TargetAuditRequest`].
    pub module: String,
    /// Native host path, used only for source admission and private staging.
    /// The inspector receives compiled artifacts, not this original path.
    pub source: PathBuf,
    pub expected_sha256: String,
    pub role: TargetRole,
}

/// Independently established subject identities reported with acceptance.
///
/// The runner must compute these from the actual configured request, capture
/// and reviewed manifests. Lean definitional equality cannot authenticate
/// metadata that the mathematical proposition does not inspect.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct TargetBindings {
    pub request_sha256: String,
    pub capture_sha256: String,
    pub model_manifest_sha256: String,
    pub specification_manifest_sha256: String,
}

/// Trusted-runner request for an exact, closed target theorem.
///
/// Expected must name a runner-generated definition of type Prop. The caller
/// must obtain Model hashes from its installed package and Specification hashes
/// from its reviewed request, rather than accepting either from proof code.
/// Adjacent caller `.olean` files are never loaded; every listed source is
/// copied into a fresh private stage and compiled against explicit artifacts.
///
/// Module and selected declaration labels currently use nonempty dot-separated
/// components, each starting with an ASCII letter and continuing with ASCII
/// letters, digits or underscores. This is a bounded wire protocol, not Lean's
/// identifier grammar. Helpers in the authored Lean source can use ordinary
/// Unicode and apostrophe identifiers; expose an ASCII root alias to select
/// such a proof. General Lean surface syntax and escaped-name transport remain
/// outside this protocol. Frontends that generate Lean source have their own
/// source-rendering obligations; accepting a name as data does not quote it.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct TargetAuditRequest {
    pub modules: Vec<TargetModule>,
    pub theorem_module: String,
    pub theorem_name: String,
    pub expected_module: String,
    pub expected_declaration: String,
    /// Fixed model root, independent of parsing the Expected source.
    pub canonical_root: String,
    /// Exact runner-generated subject declaration.
    pub subject_declaration: String,
    /// Exact reviewed specification declaration.
    pub specification_declaration: String,
    pub bindings: TargetBindings,
}

// Module routing and selected declaration labels deliberately share the
// documented protocol above. Do not mistake this bounded profile for Lean's
// general naming rules or apply it to helper declarations inside source files.
fn target_name_valid(name: &str) -> bool {
    !name.is_empty() && name.split('.').all(is_lean_ident)
}

/// Inspector data excludes original host paths: Lean uses compiled artifacts
/// and authority labels after Rust has authenticated and staged the sources.
/// Keep the hashes and bindings unchanged, but do not make a native source path
/// pass through JSON text encoding merely to audit its compiled declarations.
#[derive(Serialize)]
#[serde(rename_all = "camelCase")]
pub(super) struct InspectorTargetAuditRequest<'a> {
    modules: Vec<InspectorTargetModule<'a>>,
    theorem_module: &'a str,
    theorem_name: &'a str,
    expected_module: &'a str,
    expected_declaration: &'a str,
    canonical_root: &'a str,
    subject_declaration: &'a str,
    specification_declaration: &'a str,
    bindings: &'a TargetBindings,
}

#[derive(Serialize)]
#[serde(rename_all = "camelCase")]
struct InspectorTargetModule<'a> {
    module: &'a str,
    expected_sha256: &'a str,
    role: TargetRole,
}

impl<'a> From<&'a TargetAuditRequest> for InspectorTargetAuditRequest<'a> {
    fn from(request: &'a TargetAuditRequest) -> Self {
        Self {
            modules: request
                .modules
                .iter()
                .map(|module| InspectorTargetModule {
                    module: &module.module,
                    expected_sha256: &module.expected_sha256,
                    role: module.role,
                })
                .collect(),
            theorem_module: &request.theorem_module,
            theorem_name: &request.theorem_name,
            expected_module: &request.expected_module,
            expected_declaration: &request.expected_declaration,
            canonical_root: &request.canonical_root,
            subject_declaration: &request.subject_declaration,
            specification_declaration: &request.specification_declaration,
            bindings: &request.bindings,
        }
    }
}

impl Checker {
    /// Authenticate the requested installed-library import closure.
    ///
    /// Library hashes pin their bytes but do not admit their declarations as
    /// axioms. The inspector replays every logically reached declaration into
    /// the original foundation environment. A library can import only another
    /// locked library or the original foundation, never target source modules.
    pub(crate) fn admit_libraries(
        &mut self,
        roots: impl IntoIterator<Item = String>,
    ) -> Result<(), Failure> {
        let adm = self.admitted()?;
        let Some(lock) = adm.library_lock.clone() else {
            return Ok(());
        };
        let prefix = adm.prefix.clone();
        let foundation = adm.foundation_graph.clone();
        let mut pending: Vec<String> = roots.into_iter().collect();
        let mut needed = BTreeSet::new();
        while let Some(module) = pending.pop() {
            if foundation.contains_key(&module)
                || !lock.modules.contains_key(&module)
                || !needed.insert(module.clone())
            {
                continue;
            }
            pending.extend(lock.graph[&module].iter().map(|e| e.module.clone()));
        }
        for module in needed {
            if self.admitted()?.library_modules.contains(&module) {
                continue;
            }
            let record = &lock.modules[&module];
            if !target_name_valid(&module)
                || !is_sha256_hex(&record.source_sha256)
                || record.parts.len() != PARTS.len()
                || !PARTS.iter().all(|p| record.parts.contains_key(*p))
            {
                return Err(Failure::operational(
                    "library-lock",
                    "invalid module record",
                ));
            }
            let relative = module.replace('.', "/");
            let source = prefix.join("src/lean").join(format!("{relative}.lean"));
            if !sha256_file(&source, "library")?.eq_ignore_ascii_case(&record.source_sha256) {
                return Err(Failure::operational(
                    "library",
                    format!("source digest differs for {module}"),
                ));
            }
            let mut available = BTreeMap::new();
            for part in PARTS {
                let path = prefix.join("lib/lean").join(format!("{relative}.{part}"));
                match record.parts[part].as_deref() {
                    Some(expected) => {
                        if !is_sha256_hex(expected)
                            || !sha256_file(&path, "library")?.eq_ignore_ascii_case(expected)
                        {
                            return Err(Failure::operational(
                                "library",
                                format!("artifact digest differs for {module}.{part}"),
                            ));
                        }
                        available.insert(part, path.to_string_lossy().into_owned());
                    }
                    None if fs::symlink_metadata(&path).is_ok() => {
                        return Err(Failure::operational(
                            "library",
                            format!("unexpected companion for {module}.{part}"),
                        ));
                    }
                    None => {}
                }
            }
            let artifacts = ModuleArtifacts::from_available(&available, "library", || {
                format!("missing olean for {module}")
            })?;
            let adm = self.admitted_mut()?;
            adm.artifacts.insert(module.clone(), artifacts);
            adm.graph
                .insert(module.clone(), lock.graph[&module].clone());
            adm.library_modules.insert(module);
        }
        Ok(())
    }

    /// Check an exact target root using freshly compiled, authenticated sources.
    ///
    /// Arbitrary target elaborators may execute code under the experimental
    /// intact-host assumption. Repository source admission remains separate and
    /// retains its closed syntax policy. Reported frontend/source and policy
    /// rejections use code 1; malformed protocols, native failures, resource or
    /// kernel reports, and unavailable locked artifacts use code 2. A rejection
    /// alone does not establish that the requested proposition is false.
    pub fn run_target(&mut self, request: &TargetAuditRequest) -> Result<Json, Failure> {
        self.reset_stage()?;
        self.tool_admission()?;
        for digest in [
            &request.bindings.request_sha256,
            &request.bindings.capture_sha256,
            &request.bindings.model_manifest_sha256,
            &request.bindings.specification_manifest_sha256,
        ] {
            if !is_sha256_hex(digest) {
                return Err(Failure::policy(
                    "target-input",
                    "invalid subject binding digest",
                ));
            }
        }
        for name in [
            &request.theorem_module,
            &request.theorem_name,
            &request.expected_module,
            &request.expected_declaration,
            &request.canonical_root,
            &request.subject_declaration,
            &request.specification_declaration,
        ] {
            if !target_name_valid(name) {
                return Err(Failure::policy(
                    "target-input",
                    format!("target name is outside the ASCII dotted-name protocol: {name}"),
                ));
            }
        }
        // Authenticate each source before using its claimed role or name.
        // Compiling adjacent caller artifacts would bypass this ownership
        // partition even when their import names looked correct.
        // One role and staged path belong to each source. Reject overlap with
        // locked modules so callers cannot replace foundation or library data.
        let mut staged = BTreeMap::new();
        let mut roles = BTreeMap::new();
        for module in &request.modules {
            let adm = self.admitted()?;
            if !target_name_valid(&module.module)
                || roles.contains_key(&module.module)
                || adm.foundation_graph.contains_key(&module.module)
                || adm
                    .library_lock
                    .as_ref()
                    .is_some_and(|l| l.modules.contains_key(&module.module))
            {
                return Err(Failure::policy(
                    "target-input",
                    format!("duplicate, reserved or invalid module {}", module.module),
                ));
            }
            if !is_sha256_hex(&module.expected_sha256) {
                return Err(Failure::policy("target-input", "invalid source digest"));
            }
            let dest = self
                .stage
                .join("target-src")
                .join(format!("{}.lean", module.module.replace('.', "/")));
            stage_regular_file(&module.source, &dest, "target-input")?;
            if !sha256_file(&dest, "target-input")?.eq_ignore_ascii_case(&module.expected_sha256) {
                return Err(Failure::policy(
                    "target-input",
                    format!("source digest differs for {}", module.module),
                ));
            }
            staged.insert(module.module.clone(), dest);
            roles.insert(module.module.clone(), module.role);
        }
        if roles.get(&request.theorem_module) != Some(&TargetRole::Proof)
            || roles.get(&request.expected_module) != Some(&TargetRole::Expected)
            || !roles.values().any(|r| *r == TargetRole::Model)
            || !roles.values().any(|r| *r == TargetRole::Capture)
            || !roles.values().any(|r| *r == TargetRole::Specification)
        {
            return Err(Failure::policy(
                "target-input",
                "missing or incorrect target authority roles",
            ));
        }
        // Read imports before elaboration to establish the complete module
        // graph and reject missing or forbidden dependencies. This is an
        // early structural check; compiled dependency checks remain needed
        // because elaborators can introduce references not visible here.
        let headers: PreflightResult =
            serde_json::from_value(self.inspect(InspectorRequest::Headers {
                sources: staged.iter().map(|(n, p)| (n.clone(), p.clone())).collect(),
            })?)
            .map_err(|e| Failure::operational("headers", e.to_string()))?;
        let mut imports = BTreeMap::new();
        for header in headers.headers {
            if !staged.contains_key(&header.module) || imports.contains_key(&header.module) {
                return Err(Failure::policy(
                    "headers",
                    "duplicate or foreign source header",
                ));
            }
            imports.insert(header.module, header.imports);
        }
        if imports.len() != staged.len() {
            return Err(Failure::policy(
                "headers",
                "incomplete target source header inventory",
            ));
        }
        self.admit_libraries(imports.values().flatten().map(|e| e.module.clone()))?;
        for (module, edges) in &imports {
            for edge in edges {
                if let Some(dep) = roles.get(&edge.module) {
                    if !roles[module].allows(*dep) {
                        return Err(Failure::policy(
                            "target-role",
                            format!("{} cannot import {}", module, edge.module),
                        ));
                    }
                } else if !self.admitted()?.artifacts.contains_key(&edge.module) {
                    return Err(Failure::policy(
                        "target-import",
                        format!(
                            "unsupported import {} in {}; use explicit prelude and supported checked math imports",
                            edge.module, module
                        ),
                    ));
                }
            }
        }
        let order = topo_sort_modules(
            staged.keys().cloned().collect(),
            &imports,
            "target import cycle",
        )?;
        // Compilation consumes authenticated private copies and explicit
        // imported artifacts. Target elaboration remains under the intact-host
        // assumption; this path does not relax repository syntax admission.
        for module in order {
            self.execution_began = true;
            self.compile_lean_module(
                &module,
                &staged[&module],
                imports[&module].clone(),
                "target-lib",
                false,
                true,
            )?;
        }
        // Authenticate the staged bytes again after elaboration. This catches
        // accidental source changes; hostile host mutation remains excluded.
        for module in &request.modules {
            if !sha256_file(&staged[&module.module], "target-input")?
                .eq_ignore_ascii_case(&module.expected_sha256)
            {
                return Err(Failure::policy(
                    "target-input",
                    "staged source changed during elaboration",
                ));
            }
        }
        // Compilation success alone does not establish the exact theorem
        // type, permitted assumptions, or compiled source roles. Acceptance
        // is a separate inspection of the produced kernel declarations.
        let mut report = self.inspect(InspectorRequest::TargetAudit {
            request: request.clone(),
        })?;
        let mut provenance = Vec::new();
        for module in &request.modules {
            let artifacts = &self.admitted()?.artifacts[&module.module];
            let paths = artifacts.to_wire();
            let hashes: Result<Vec<_>, Failure> = paths
                .iter()
                .flat_map(|parts| parts.iter())
                .map(|p| Ok(json!({"sha256": sha256_file(Path::new(p), "target-artifact")?})))
                .collect();
            provenance.push(json!({"module": module.module, "role": module.role,
                "sourceSha256": module.expected_sha256, "artifacts": hashes?}));
        }
        let obj = report
            .as_object_mut()
            .ok_or_else(|| Failure::operational("target-audit", "non-object inspector result"))?;
        // Report modules determining the subject, model or specification,
        // including installed libraries used only by captured program data.
        // The logical closures exclude proof-only helpers; the source inventory
        // above separately identifies every request source, even unused ones.
        let mut identities = serde_json::Map::new();
        for key in ["subjectClosure", "modelClosure", "specificationClosure"] {
            if let Some(rows) = obj.get(key).and_then(Json::as_array) {
                for row in rows {
                    let Some(module) = row.get("module").and_then(Json::as_str) else {
                        return Err(Failure::operational(
                            "target-audit",
                            "missing closure provenance",
                        ));
                    };
                    if identities.contains_key(module) {
                        continue;
                    }
                    let adm = self.admitted()?;
                    let source_sha =
                        if let Some(source) = request.modules.iter().find(|m| m.module == module) {
                            source.expected_sha256.clone()
                        } else {
                            sha256_file(
                                &adm.prefix
                                    .join("src/lean")
                                    .join(format!("{}.lean", module.replace('.', "/"))),
                                "target-provenance",
                            )?
                        };
                    let artifacts = adm.artifacts.get(module).ok_or_else(|| {
                        Failure::operational("target-provenance", "missing closure artifact")
                    })?;
                    let paths = artifacts.to_wire();
                    let hashes: Result<Vec<_>, Failure> = paths
                        .iter()
                        .flat_map(|p| p.iter())
                        .map(|p| {
                            Ok(json!({
                                "part": Path::new(p).file_name().and_then(|s| s.to_str()),
                                "sha256": sha256_file(Path::new(p), "target-provenance")?
                            }))
                        })
                        .collect();
                    identities.insert(
                        module.into(),
                        json!({"sourceSha256": source_sha, "artifacts": hashes?}),
                    );
                }
            }
        }
        obj.insert("moduleIdentities".into(), Json::Object(identities));
        obj.insert(
            "bindings".into(),
            serde_json::to_value(&request.bindings)
                .map_err(|e| Failure::operational("target-audit", e.to_string()))?,
        );
        obj.insert("sources".into(), json!(provenance));
        obj.insert("toolchain".into(), json!(self.admitted()?.version));
        Ok(report)
    }
}
