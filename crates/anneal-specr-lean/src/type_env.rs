//! Semantic type environment (`TypeEnvironment`) across an extracted MiniRust
//! specification snapshot: resolves unique qualified names, computes type
//! dependency & mutual-recursion strongly connected components (Tarjan SCC),
//! tracks `GcCow<T>` indirection, and summarizes per-domain/per-effect metrics.

use std::collections::{BTreeMap, BTreeSet};

use crate::extractor::{ExtractedSnapshot, SpecDomain};
use crate::specr_ast::{EffectLevel, ItemKind, SpecrItem, VariantPayload, parse_block_items};

/// Aggregate statistics across a compiled MiniRust specification snapshot.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct TypeEnvStats {
    pub chapter_count: usize,
    pub block_count: usize,
    pub total_rust_lines: usize,
    pub declaration_count: usize,
    pub struct_count: usize,
    pub enum_count: usize,
    pub type_alias_count: usize,
    pub const_count: usize,
    pub trait_count: usize,
    pub fn_count: usize,
    pub impl_method_count: usize,
    pub assoc_type_count: usize,
    pub gc_cow_item_count: usize,
    pub mutually_recursive_type_count: usize,
    pub pure_count: usize,
    pub option_effect_count: usize,
    pub fallible_result_count: usize,
    pub nondet_result_count: usize,
    pub by_domain: BTreeMap<SpecDomain, usize>,
}

/// Complete resolved semantic environment for a single upstream MiniRust snapshot.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TypeEnvironment {
    pub snapshot_id: String,
    pub git_sha: String,
    pub items: Vec<SpecrItem>,
    pub by_qualified_name: BTreeMap<String, usize>,
    pub methods_by_type: BTreeMap<String, Vec<usize>>,
    pub mutual_recursion_groups: Vec<Vec<String>>,
    pub stats: TypeEnvStats,
}

impl TypeEnvironment {
    /// Builds a complete `TypeEnvironment` from an `ExtractedSnapshot`.
    #[must_use]
    pub fn build(snapshot: &ExtractedSnapshot) -> Self {
        let mut raw_items = Vec::new();
        for chapter in &snapshot.chapters {
            for block in &chapter.blocks {
                let parsed = parse_block_items(block);
                raw_items.extend(parsed);
            }
        }

        // Ensure globally unique, deterministic `qualified_name` across all chapters.
        let mut name_counts: BTreeMap<String, usize> = BTreeMap::new();
        for item in &raw_items {
            *name_counts.entry(item.qualified_name.clone()).or_insert(0) += 1;
        }

        let mut seen_disambig: BTreeMap<String, usize> = BTreeMap::new();
        for item in &mut raw_items {
            if name_counts.get(&item.qualified_name).copied().unwrap_or(0) > 1 {
                let stem = chapter_stem(&item.span.rel_path);
                let candidate = format!("{}::{}", stem, item.qualified_name);
                let count = seen_disambig.entry(candidate.clone()).or_insert(0);
                *count += 1;
                if *count == 1 {
                    item.qualified_name = candidate;
                } else {
                    item.qualified_name = format!("{candidate}_{count}");
                }
            }
        }

        // Compute mutual recursion across all nominal type declarations (`struct`, `enum`, `type`).
        let mutual_recursion_groups = mark_mutually_recursive_types(&mut raw_items);

        let mut by_qualified_name = BTreeMap::new();
        let mut methods_by_type: BTreeMap<String, Vec<usize>> = BTreeMap::new();
        let mut stats = TypeEnvStats {
            chapter_count: snapshot.chapters.len(),
            block_count: snapshot.total_blocks,
            total_rust_lines: snapshot.total_rust_lines,
            declaration_count: raw_items.len(),
            ..TypeEnvStats::default()
        };

        for (idx, item) in raw_items.iter().enumerate() {
            by_qualified_name.insert(item.qualified_name.clone(), idx);
            if let Some(ref tgt) = item.impl_target {
                methods_by_type.entry(tgt.clone()).or_default().push(idx);
            }
            *stats.by_domain.entry(item.domain).or_insert(0) += 1;
            match item.kind {
                ItemKind::Struct => stats.struct_count += 1,
                ItemKind::Enum => stats.enum_count += 1,
                ItemKind::TypeAlias => stats.type_alias_count += 1,
                ItemKind::Const => stats.const_count += 1,
                ItemKind::Trait => stats.trait_count += 1,
                ItemKind::Fn => stats.fn_count += 1,
                ItemKind::ImplMethod => stats.impl_method_count += 1,
                ItemKind::AssociatedType => stats.assoc_type_count += 1,
            }
            if item.uses_gc_cow {
                stats.gc_cow_item_count += 1;
            }
            if item.is_mutually_recursive {
                stats.mutually_recursive_type_count += 1;
            }
            match item.effect {
                EffectLevel::Pure => stats.pure_count += 1,
                EffectLevel::OptionEffect => stats.option_effect_count += 1,
                EffectLevel::FallibleResult => stats.fallible_result_count += 1,
                EffectLevel::NondetResult => stats.nondet_result_count += 1,
            }
        }

        Self {
            snapshot_id: snapshot.snapshot_id.clone(),
            git_sha: snapshot.git_sha.clone(),
            items: raw_items,
            by_qualified_name,
            methods_by_type,
            mutual_recursion_groups,
            stats,
        }
    }

    /// Looks up a declaration by exact qualified name.
    #[must_use]
    pub fn get(&self, qualified_name: &str) -> Option<&SpecrItem> {
        self.by_qualified_name.get(qualified_name).map(|&idx| &self.items[idx])
    }

    /// Returns all declarations in a specific MiniRust semantic domain.
    #[must_use]
    pub fn items_in_domain(&self, domain: SpecDomain) -> Vec<&SpecrItem> {
        self.items.iter().filter(|i| i.domain == domain).collect()
    }

    /// Returns all declarations of a specific `ItemKind`.
    #[must_use]
    pub fn items_of_kind(&self, kind: ItemKind) -> Vec<&SpecrItem> {
        self.items.iter().filter(|i| i.kind == kind).collect()
    }
}

fn chapter_stem(rel_path: &str) -> String {
    let without_spec = rel_path.strip_prefix("spec/").unwrap_or(rel_path);
    let without_ext = without_spec.strip_suffix(".md").unwrap_or(without_spec);
    without_ext.replace('/', "_")
}

/// Extracts all identifier tokens referenced in type positions of `item`.
fn collect_referenced_type_idents(item: &SpecrItem) -> BTreeSet<String> {
    let mut refs = BTreeSet::new();
    for f in &item.fields {
        collect_idents_from_type_str(&f.ty, &mut refs);
    }
    for v in &item.variants {
        match &v.payload {
            VariantPayload::Unit => {}
            VariantPayload::Tuple(tys) => {
                for t in tys {
                    collect_idents_from_type_str(t, &mut refs);
                }
            }
            VariantPayload::Struct(flds) => {
                for f in flds {
                    collect_idents_from_type_str(&f.ty, &mut refs);
                }
            }
        }
    }
    if let Some(ref aliased) = item.aliased_type {
        collect_idents_from_type_str(aliased, &mut refs);
    }
    refs
}

fn collect_idents_from_type_str(s: &str, out: &mut BTreeSet<String>) {
    let mut cur = String::new();
    for ch in s.chars() {
        if ch.is_ascii_alphanumeric() || ch == '_' {
            cur.push(ch);
        } else {
            if !cur.is_empty() && cur.starts_with(|c: char| c.is_ascii_uppercase()) {
                out.insert(cur.clone());
            }
            cur.clear();
        }
    }
    if !cur.is_empty() && cur.starts_with(|c: char| c.is_ascii_uppercase()) {
        out.insert(cur);
    }
}

/// Identifies mutually recursive or self-recursive nominal types across the snapshot
/// so `lean_emit.rs` knows which types require inductive/mutual blocks.
fn mark_mutually_recursive_types(items: &mut [SpecrItem]) -> Vec<Vec<String>> {
    let mut type_names: BTreeSet<String> = BTreeSet::new();
    for item in items.iter() {
        if matches!(item.kind, ItemKind::Struct | ItemKind::Enum | ItemKind::TypeAlias) {
            type_names.insert(item.ident.clone());
        }
    }

    let mut edges: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
    for item in items.iter() {
        if matches!(item.kind, ItemKind::Struct | ItemKind::Enum | ItemKind::TypeAlias) {
            let refs = collect_referenced_type_idents(item);
            let entry = edges.entry(item.ident.clone()).or_default();
            for r in refs {
                if type_names.contains(&r) {
                    entry.insert(r);
                }
            }
        }
    }

    // Compute transitive reachability over nominal types to detect every self/mutual cycle cleanly.
    let mut reach: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
    for src in &type_names {
        let mut visited = BTreeSet::new();
        let mut stack = vec![src.clone()];
        while let Some(u) = stack.pop() {
            if let Some(neighbors) = edges.get(&u) {
                for v in neighbors {
                    if visited.insert(v.clone()) {
                        stack.push(v.clone());
                    }
                }
            }
        }
        reach.insert(src.clone(), visited);
    }

    let mut cyclic_types = BTreeSet::new();
    for t in &type_names {
        if reach.get(t).is_some_and(|r| r.contains(t)) {
            cyclic_types.insert(t.clone());
        }
    }

    // Group cyclic types into equivalence classes (strongly connected components)
    let mut visited_scc = BTreeSet::new();
    let mut groups = Vec::new();
    for t in &cyclic_types {
        if visited_scc.contains(t) {
            continue;
        }
        let mut component = vec![t.clone()];
        visited_scc.insert(t.clone());
        for other in &cyclic_types {
            if other != t
                && reach.get(t).is_some_and(|r| r.contains(other))
                && reach.get(other).is_some_and(|r| r.contains(t))
            {
                visited_scc.insert(other.clone());
                component.push(other.clone());
            }
        }
        component.sort();
        groups.push(component);
    }
    groups.sort();

    for item in items.iter_mut() {
        if cyclic_types.contains(&item.ident)
            && matches!(item.kind, ItemKind::Struct | ItemKind::Enum | ItemKind::TypeAlias)
        {
            item.is_mutually_recursive = true;
            // In upstream `specr-transpile`, mutually recursive nominal value/type definitions
            // lower through `GcCow<T>` indirection, which erases to identity in Lean 4.
            item.uses_gc_cow = true;
        }
    }

    groups
}
