// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Shallow embedding of MiniRust *data* definitions as Lean types.
//!
//! In addition to the deep (syntax) embedding of every item, each MiniRust
//! `struct`, `enum`, and `type` alias is translated to a Lean `structure`,
//! `inductive`, or `abbrev` with the same name, the same generic parameters,
//! and fields of the corresponding Lean types. Traits contribute a Lean
//! `class` holding only their associated *types*, and `impl Trait for T`
//! blocks contribute the matching `instance`. Function bodies, associated
//! constants, and method signatures are never translated shallowly: they
//! exist only in the deep embedding, so this module cannot smuggle in a
//! hand-written interpretation of MiniRust behavior.
//!
//! The mapping rules are deliberately few and are listed here so that a
//! reviewer can check them against the generated file:
//!
//! 1. Built-in and `libspecr` types map through [`builtin`] to Lean core types
//!    or to the hand-written `MiniRustSpec.LibSpecr` prelude.
//! 2. A path `M::Assoc` whose head is a generic parameter bounded by a spec
//!    trait declaring `type Assoc` maps to the class projection
//!    `(Trait.Assoc M)`.
//! 3. Missing trailing generic arguments are filled with the item's declared
//!    defaults (`BasicMemory<T>` becomes `BasicMemory T Unit Unit`).
//! 4. Declarations are emitted in dependency order; strongly connected groups
//!    become one `mutual` block, inside which type aliases that participate
//!    in the cycle are expanded (Lean cannot define an alias in terms of a
//!    type that is not yet declared); the alias itself is emitted after the
//!    block.
//! 5. Anything outside these rules is reported as *not shallowly embedded*,
//!    with a reason, in the coverage report. Such items still have a complete
//!    deep embedding.

use std::collections::{BTreeMap, BTreeSet};

use crate::lean::{doc_text, ident};
use crate::source::SourceFile;

/// Maps built-in and `libspecr` type names to their Lean counterparts.
/// The second component is the number of type arguments the name expects.
pub fn builtin(name: &str) -> Option<(&'static str, usize)> {
    Some(match name {
        "Int" => ("Int", 0),
        "bool" => ("Bool", 0),
        "u8" => ("UInt8", 0),
        "u16" => ("UInt16", 0),
        "u32" => ("UInt32", 0),
        "u64" => ("UInt64", 0),
        "usize" => ("USize", 0),
        "String" => ("String", 0),
        "List" => ("List", 1),
        "Option" => ("Option", 1),
        "Map" => ("LibSpecr.Map", 2),
        "Set" => ("LibSpecr.Set", 1),
        "Size" => ("LibSpecr.Size", 0),
        "Align" => ("LibSpecr.Align", 0),
        "Name" => ("LibSpecr.Name", 0),
        "Signedness" => ("LibSpecr.Signedness", 0),
        "Endianness" => ("LibSpecr.Endianness", 0),
        "Mutability" => ("LibSpecr.Mutability", 0),
        "DynWrite" => ("LibSpecr.DynWrite", 0),
        "PhantomData" => ("LibSpecr.PhantomData", 1),
        "Nondet" => ("LibSpecr.Nondet", 1),
        "NdResult" => ("LibSpecr.NdResult", 2),
        _ => return None,
    })
}

/// Path prefixes that only select a module and carry no meaning of their own.
const MODULE_PREFIXES: &[&str] = &["crate", "lang", "mem", "prelude", "libspecr", "std", "marker", "core"];

#[derive(Clone)]
struct GenericInfo {
    name: String,
    /// Spec traits this parameter is bounded by.
    trait_bounds: Vec<String>,
    default: Option<syn::Type>,
}

#[derive(Clone)]
enum Kind {
    Struct(syn::ItemStruct),
    Enum(syn::ItemEnum),
    Alias(syn::ItemType),
    Class(syn::ItemTrait),
    Instance(syn::ItemImpl),
}

#[derive(Clone)]
struct Decl {
    /// Lean-facing name (type name; for instances, a synthesized name).
    name: String,
    file: String,
    line: usize,
    order: usize,
    kind: Kind,
    generics: Vec<GenericInfo>,
}

/// Per-item shallow translation status for the coverage report.
pub struct ShallowStatus {
    pub file: String,
    pub line: usize,
    pub item: String,
    pub kind: &'static str,
    /// `None` if translated; otherwise the reason it was not.
    pub skipped: Option<String>,
}

/// The shallow translation result.
pub struct ShallowOutput {
    pub lean: String,
    pub statuses: Vec<ShallowStatus>,
}

fn doc_of(attrs: &[syn::Attribute]) -> Vec<String> {
    attrs
        .iter()
        .filter_map(|a| match &a.meta {
            syn::Meta::NameValue(nv) if a.path().is_ident("doc") => match &nv.value {
                syn::Expr::Lit(syn::ExprLit { lit: syn::Lit::Str(s), .. }) => {
                    let v = s.value();
                    Some(v.strip_prefix(' ').unwrap_or(&v).to_string())
                }
                _ => None,
            },
            _ => None,
        })
        .collect()
}

fn render_doc(lines: &[String], provenance: &str, indent: &str) -> String {
    let mut body: Vec<String> = lines.iter().map(|l| doc_text(l)).collect();
    if !provenance.is_empty() {
        if !body.is_empty() {
            body.push(String::new());
        }
        body.push(provenance.to_string());
    }
    if body.is_empty() {
        return String::new();
    }
    let mut out = format!("{indent}/--");
    if body.len() == 1 {
        out.push(' ');
        out.push_str(&body[0]);
        out.push_str(" -/\n");
        return out;
    }
    out.push('\n');
    for l in body {
        if l.is_empty() {
            out.push('\n');
        } else {
            out.push_str(indent);
            out.push_str(&l);
            out.push('\n');
        }
    }
    out.push_str(indent);
    out.push_str("-/\n");
    out
}

fn generic_infos(g: &syn::Generics, traits: &BTreeSet<String>) -> Result<Vec<GenericInfo>, String> {
    let mut out = Vec::new();
    for p in &g.params {
        match p {
            syn::GenericParam::Type(t) => {
                let mut trait_bounds = Vec::new();
                for b in &t.bounds {
                    if let syn::TypeParamBound::Trait(tb) = b {
                        let n = tb.path.segments.last().map(|s| s.ident.to_string()).unwrap_or_default();
                        if traits.contains(&n) {
                            trait_bounds.push(n);
                        } else {
                            return Err(format!("generic `{}` has non-spec trait bound `{n}`", t.ident));
                        }
                    }
                }
                out.push(GenericInfo { name: t.ident.to_string(), trait_bounds, default: t.default.clone() });
            }
            syn::GenericParam::Lifetime(_) => return Err("lifetime generic parameter".into()),
            syn::GenericParam::Const(_) => return Err("const generic parameter".into()),
        }
    }
    if g.where_clause.as_ref().map(|w| !w.predicates.is_empty()).unwrap_or(false) {
        return Err("where clause".into());
    }
    Ok(out)
}

struct Ctx<'a> {
    decls: &'a BTreeMap<String, Decl>,
    /// Associated type names declared by each spec trait.
    trait_assoc: &'a BTreeMap<String, Vec<String>>,
    /// Aliases to expand inline (cycle members while emitting a mutual block).
    expand: &'a BTreeSet<String>,
}

impl<'a> Ctx<'a> {
    /// Maps a MiniRust type to Lean source, recording spec-type dependencies.
    fn ty(&self, t: &syn::Type, scope: &[GenericInfo], deps: &mut BTreeSet<String>) -> Result<String, String> {
        match t {
            syn::Type::Paren(p) => self.ty(&p.elem, scope, deps),
            syn::Type::Group(g) => self.ty(&g.elem, scope, deps),
            syn::Type::Tuple(tu) => {
                if tu.elems.is_empty() {
                    return Ok("Unit".into());
                }
                let parts: Vec<String> =
                    tu.elems.iter().map(|e| self.ty(e, scope, deps)).collect::<Result<_, _>>()?;
                Ok(format!("({})", parts.join(" × ")))
            }
            syn::Type::BareFn(f) => {
                let mut parts: Vec<String> =
                    f.inputs.iter().map(|a| self.ty(&a.ty, scope, deps)).collect::<Result<_, _>>()?;
                let out = match &f.output {
                    syn::ReturnType::Default => "Unit".to_string(),
                    syn::ReturnType::Type(_, t) => self.ty(t, scope, deps)?,
                };
                if parts.is_empty() {
                    parts.push("Unit".into());
                }
                parts.push(out);
                Ok(format!("({})", parts.join(" → ")))
            }
            syn::Type::Path(p) if p.qself.is_none() => self.path_ty(&p.path, scope, deps),
            other => Err(format!("unsupported type form `{}`", crate::deep::tokens_of(other))),
        }
    }

    fn path_ty(&self, path: &syn::Path, scope: &[GenericInfo], deps: &mut BTreeSet<String>) -> Result<String, String> {
        let mut segs: Vec<&syn::PathSegment> = path.segments.iter().collect();
        let mut external = false;
        while segs.len() > 1 && MODULE_PREFIXES.contains(&segs[0].ident.to_string().as_str()) {
            // An explicit `libspecr::`/`std::`/`core::` prefix names a type
            // outside the specification, which must not resolve to a
            // same-named specification item.
            if matches!(segs[0].ident.to_string().as_str(), "libspecr" | "std" | "core") {
                external = true;
            }
            segs.remove(0);
        }
        // Rule 2: associated type projection through a bounded generic.
        if segs.len() == 2 {
            let head = segs[0].ident.to_string();
            let assoc = segs[1].ident.to_string();
            if let Some(g) = scope.iter().find(|g| g.name == head) {
                if !matches!(segs[0].arguments, syn::PathArguments::None)
                    || !matches!(segs[1].arguments, syn::PathArguments::None)
                {
                    return Err(format!("generic arguments on associated type path `{head}::{assoc}`"));
                }
                for tr in &g.trait_bounds {
                    if self.trait_assoc.get(tr).map(|v| v.contains(&assoc)).unwrap_or(false) {
                        deps.insert(tr.clone());
                        return Ok(format!("({}.{} {})", ident(tr), ident(&assoc), ident(&head)));
                    }
                }
                return Err(format!("`{head}::{assoc}` is not an associated type of a bound of `{head}`"));
            }
        }
        if segs.len() == 2 && segs[0].ident == "result" && segs[1].ident == "Result" {
            // `std::result::Result<T, E>` is Lean's `Except E T`.
            let args = self.type_args(&segs[1].arguments, scope, deps)?;
            if args.len() != 2 {
                return Err("std::result::Result needs two arguments".into());
            }
            return Ok(format!("(Except {} {})", args[1], args[0]));
        }
        if segs.len() != 1 {
            return Err(format!("unsupported multi-segment path `{}`", crate::deep::tokens_of(path)));
        }
        let seg = segs[0];
        let name = seg.ident.to_string();
        let args = self.type_args(&seg.arguments, scope, deps)?;
        if scope.iter().any(|g| g.name == name) {
            if !args.is_empty() {
                return Err(format!("generic parameter `{name}` applied to arguments"));
            }
            return Ok(ident(&name));
        }
        if let Some(decl) = self.decls.get(&name).filter(|_| !external) {
            if matches!(decl.kind, Kind::Class(_) | Kind::Instance(_)) {
                return Err(format!("trait `{name}` used as a type"));
            }
            // Rule 3: fill defaults for missing trailing arguments.
            let mut full = args.clone();
            if full.len() > decl.generics.len() {
                return Err(format!("too many generic arguments for `{name}`"));
            }
            for g in decl.generics.iter().skip(args.len()) {
                match &g.default {
                    Some(d) => full.push(self.ty(d, &decl.generics, deps)?),
                    None => return Err(format!("missing generic argument `{}` for `{name}`", g.name)),
                }
            }
            if self.expand.contains(&name) {
                if let Kind::Alias(a) = &decl.kind {
                    // Rule 4: render the alias body with its own parameters,
                    // then substitute the actual arguments for them.
                    let mut body = self.ty(&a.ty, &decl.generics, deps)?;
                    for (g, v) in decl.generics.iter().zip(full.iter()) {
                        body = substitute_ident(&body, &ident(&g.name), v);
                    }
                    return Ok(format!("({body})"));
                }
            }
            deps.insert(name.clone());
            if full.is_empty() {
                return Ok(ident(&name));
            }
            return Ok(format!("({} {})", ident(&name), full.join(" ")));
        }
        if let Some((lean, arity)) = builtin(&name) {
            if args.len() != arity {
                return Err(format!("`{name}` expects {arity} type arguments, found {}", args.len()));
            }
            if args.is_empty() {
                return Ok(lean.to_string());
            }
            return Ok(format!("({lean} {})", args.join(" ")));
        }
        if external {
            return Err(format!(
                "`{}` is defined outside the specification and has no Lean counterpart",
                crate::deep::tokens_of(path)
            ));
        }
        Err(format!("unknown type `{name}`"))
    }

    fn type_args(
        &self,
        a: &syn::PathArguments,
        scope: &[GenericInfo],
        deps: &mut BTreeSet<String>,
    ) -> Result<Vec<String>, String> {
        match a {
            syn::PathArguments::None => Ok(vec![]),
            syn::PathArguments::AngleBracketed(ab) => ab
                .args
                .iter()
                .map(|g| match g {
                    syn::GenericArgument::Type(t) => self.ty(t, scope, deps),
                    other => Err(format!("unsupported generic argument `{}`", crate::deep::tokens_of(other))),
                })
                .collect(),
            syn::PathArguments::Parenthesized(_) => Err("parenthesized generic arguments".into()),
        }
    }
}

/// Replaces whole-identifier occurrences of `from` in Lean source `s`.
fn substitute_ident(s: &str, from: &str, to: &str) -> String {
    let mut out = String::new();
    let bytes: Vec<char> = s.chars().collect();
    let f: Vec<char> = from.chars().collect();
    let is_id = |c: char| c.is_alphanumeric() || c == '_' || c == '.' || c == '«' || c == '»';
    let mut i = 0;
    while i < bytes.len() {
        if bytes[i..].starts_with(&f)
            && (i == 0 || !is_id(bytes[i - 1]))
            && (i + f.len() == bytes.len() || !is_id(bytes[i + f.len()]))
        {
            out.push_str(to);
            i += f.len();
        } else {
            out.push(bytes[i]);
            i += 1;
        }
    }
    out
}

fn binders(generics: &[GenericInfo], ctx: &Ctx, deps: &mut BTreeSet<String>) -> Result<String, String> {
    let mut out = String::new();
    for g in generics {
        match &g.default {
            Some(d) => {
                let dv = ctx.ty(d, generics, deps)?;
                out.push_str(&format!(" ({} : Type := {dv})", ident(&g.name)));
            }
            None => out.push_str(&format!(" ({} : Type)", ident(&g.name))),
        }
        for b in &g.trait_bounds {
            deps.insert(b.clone());
            out.push_str(&format!(" [{} {}]", ident(b), ident(&g.name)));
        }
    }
    Ok(out)
}


/// Renders one declaration. `in_mutual` controls whether structures that are
/// part of a recursive group are emitted (Lean supports `structure` inside
/// `mutual`, so the form is the same either way).
fn render_decl(d: &Decl, ctx: &Ctx, commit_short: &str) -> Result<String, String> {
    let mut deps = BTreeSet::new();
    let prov = format!("Source: `{}:{}` (MiniRust `{commit_short}`).", d.file, d.line);
    let mut out = String::new();
    match &d.kind {
        Kind::Struct(s) => {
            out.push_str(&render_doc(&doc_of(&s.attrs), &prov, ""));
            let b = binders(&d.generics, ctx, &mut deps)?;
            out.push_str(&format!("structure {}{b} : Type where\n", ident(&d.name)));
            match &s.fields {
                syn::Fields::Named(n) => {
                    for f in &n.named {
                        out.push_str(&render_doc(&doc_of(&f.attrs), "", "  "));
                        let t = ctx.ty(&f.ty, &d.generics, &mut deps)?;
                        out.push_str(&format!("  {} : {t}\n", ident(&f.ident.as_ref().unwrap().to_string())));
                    }
                }
                syn::Fields::Unnamed(u) => {
                    for (i, f) in u.unnamed.iter().enumerate() {
                        out.push_str(&render_doc(&doc_of(&f.attrs), "", "  "));
                        let t = ctx.ty(&f.ty, &d.generics, &mut deps)?;
                        out.push_str(&format!("  _{i} : {t}\n"));
                    }
                }
                syn::Fields::Unit => {}
            }
        }
        Kind::Enum(e) => {
            out.push_str(&render_doc(&doc_of(&e.attrs), &prov, ""));
            let b = binders(&d.generics, ctx, &mut deps)?;
            out.push_str(&format!("inductive {}{b} : Type where\n", ident(&d.name)));
            for v in &e.variants {
                if v.discriminant.is_some() {
                    return Err(format!("explicit discriminant on variant `{}`", v.ident));
                }
                out.push_str(&render_doc(&doc_of(&v.attrs), "", "  "));
                let mut line = format!("  | {}", ident(&v.ident.to_string()));
                match &v.fields {
                    syn::Fields::Named(n) => {
                        for f in &n.named {
                            let t = ctx.ty(&f.ty, &d.generics, &mut deps)?;
                            line.push_str(&format!(" ({} : {t})", ident(&f.ident.as_ref().unwrap().to_string())));
                        }
                    }
                    syn::Fields::Unnamed(u) => {
                        for (i, f) in u.unnamed.iter().enumerate() {
                            let t = ctx.ty(&f.ty, &d.generics, &mut deps)?;
                            line.push_str(&format!(" (_{i} : {t})"));
                        }
                    }
                    syn::Fields::Unit => {}
                }
                out.push_str(&line);
                out.push('\n');
            }
        }
        Kind::Alias(a) => {
            out.push_str(&render_doc(&doc_of(&a.attrs), &prov, ""));
            let b = binders(&d.generics, ctx, &mut deps)?;
            let t = ctx.ty(&a.ty, &d.generics, &mut deps)?;
            out.push_str(&format!("abbrev {}{b} : Type := {t}\n", ident(&d.name)));
        }
        Kind::Class(t) => {
            let mut docs = doc_of(&t.attrs);
            let omitted: Vec<String> = t
                .items
                .iter()
                .filter_map(|i| match i {
                    syn::TraitItem::Const(c) => Some(format!("const `{}`", c.ident)),
                    syn::TraitItem::Fn(f) => Some(format!("fn `{}`", f.sig.ident)),
                    _ => None,
                })
                .collect();
            if !omitted.is_empty() {
                if !docs.is_empty() {
                    docs.push(String::new());
                }
                docs.push(format!(
                    "Shallow class: associated types only. Omitted (deep embedding only): {}.",
                    omitted.join(", ")
                ));
            }
            out.push_str(&render_doc(&docs, &prov, ""));
            out.push_str(&format!("class {} (Self : Type) : Type 1 where\n", ident(&d.name)));
            for i in &t.items {
                if let syn::TraitItem::Type(ty) = i {
                    if !ty.generics.params.is_empty() {
                        return Err(format!("generic associated type `{}`", ty.ident));
                    }
                    out.push_str(&render_doc(&doc_of(&ty.attrs), "", "  "));
                    out.push_str(&format!("  {} : Type\n", ident(&ty.ident.to_string())));
                }
            }
        }
        Kind::Instance(im) => {
            let (_, trait_path, _) = im.trait_.as_ref().expect("instances come from trait impls");
            let trait_name = trait_path.segments.last().unwrap().ident.to_string();
            deps.insert(trait_name.clone());
            let self_ty = ctx.ty(&im.self_ty, &d.generics, &mut deps)?;
            let mut b = String::new();
            for g in &d.generics {
                if g.default.is_some() {
                    return Err("defaulted generic on impl".into());
                }
                b.push_str(&format!(" {{{} : Type}}", ident(&g.name)));
                for tb in &g.trait_bounds {
                    deps.insert(tb.clone());
                    b.push_str(&format!(" [{} {}]", ident(tb), ident(&g.name)));
                }
            }
            let omitted: Vec<String> = im
                .items
                .iter()
                .filter_map(|i| match i {
                    syn::ImplItem::Const(c) => Some(format!("const `{}`", c.ident)),
                    syn::ImplItem::Fn(f) => Some(format!("fn `{}`", f.sig.ident)),
                    _ => None,
                })
                .collect();
            let mut docs = vec![format!("Associated types of `impl {trait_name} for {}`.", crate::deep::tokens_of(&*im.self_ty))];
            if !omitted.is_empty() {
                docs.push(String::new());
                docs.push(format!("Omitted (deep embedding only): {}.", omitted.join(", ")));
            }
            out.push_str(&render_doc(&docs, &prov, ""));
            let assoc: Vec<&syn::ImplItemType> = im
                .items
                .iter()
                .filter_map(|i| if let syn::ImplItem::Type(t) = i { Some(t) } else { None })
                .collect();
            if assoc.is_empty() {
                out.push_str(&format!("instance {}{b} : {} {self_ty} := {{}}\n", ident(&d.name), ident(&trait_name)));
            } else {
                out.push_str(&format!("instance {}{b} : {} {self_ty} where\n", ident(&d.name), ident(&trait_name)));
                for t in assoc {
                    let v = ctx.ty(&t.ty, &d.generics, &mut deps)?;
                    out.push_str(&format!("  {} := {v}\n", ident(&t.ident.to_string())));
                }
            }
        }
    }
    Ok(out)
}

fn decl_deps(d: &Decl, ctx: &Ctx) -> Result<BTreeSet<String>, String> {
    let mut deps = BTreeSet::new();
    // Rendering computes dependencies as a side effect; reuse it.
    // Self-references are kept so that self-recursive types are recognized
    // as recursive (Lean cannot derive `DecidableEq` for them).
    let _ = render_decl_collect(d, ctx, &mut deps)?;
    Ok(deps)
}

fn render_decl_collect(d: &Decl, ctx: &Ctx, deps: &mut BTreeSet<String>) -> Result<(), String> {
    let mut local = BTreeSet::new();
    let _ = binders(&d.generics, ctx, &mut local)?;
    let push = |t: &syn::Type, scope: &[GenericInfo], local: &mut BTreeSet<String>| -> Result<(), String> {
        ctx.ty(t, scope, local).map(|_| ())
    };
    match &d.kind {
        Kind::Struct(s) => {
            for f in s.fields.iter() {
                push(&f.ty, &d.generics, &mut local)?;
            }
        }
        Kind::Enum(e) => {
            for v in &e.variants {
                for f in v.fields.iter() {
                    push(&f.ty, &d.generics, &mut local)?;
                }
            }
        }
        Kind::Alias(a) => push(&a.ty, &d.generics, &mut local)?,
        Kind::Class(_) => {}
        Kind::Instance(im) => {
            let (_, p, _) = im.trait_.as_ref().unwrap();
            local.insert(p.segments.last().unwrap().ident.to_string());
            push(&im.self_ty, &d.generics, &mut local)?;
            for i in &im.items {
                if let syn::ImplItem::Type(t) = i {
                    push(&t.ty, &d.generics, &mut local)?;
                }
            }
            for g in &d.generics {
                for b in &g.trait_bounds {
                    local.insert(b.clone());
                }
            }
        }
    }
    deps.extend(local);
    Ok(())
}

/// Tarjan's SCC algorithm over `graph`, visiting nodes and successors in the
/// given deterministic order. Returns SCCs in reverse topological order of the
/// condensation (dependencies first).
fn sccs(nodes: &[String], graph: &BTreeMap<String, Vec<String>>) -> Vec<Vec<String>> {
    struct St<'a> {
        graph: &'a BTreeMap<String, Vec<String>>,
        index: usize,
        idx: BTreeMap<String, usize>,
        low: BTreeMap<String, usize>,
        on: BTreeSet<String>,
        stack: Vec<String>,
        out: Vec<Vec<String>>,
    }
    fn strong(st: &mut St, v: &str) {
        st.idx.insert(v.to_string(), st.index);
        st.low.insert(v.to_string(), st.index);
        st.index += 1;
        st.stack.push(v.to_string());
        st.on.insert(v.to_string());
        let succs = st.graph.get(v).cloned().unwrap_or_default();
        for w in succs {
            if !st.idx.contains_key(&w) {
                strong(st, &w);
                let lw = st.low[&w];
                let lv = st.low[v];
                st.low.insert(v.to_string(), lv.min(lw));
            } else if st.on.contains(&w) {
                let iw = st.idx[&w];
                let lv = st.low[v];
                st.low.insert(v.to_string(), lv.min(iw));
            }
        }
        if st.low[v] == st.idx[v] {
            let mut comp = Vec::new();
            loop {
                let w = st.stack.pop().unwrap();
                st.on.remove(&w);
                comp.push(w.clone());
                if w == v {
                    break;
                }
            }
            st.out.push(comp);
        }
    }
    let mut st = St {
        graph,
        index: 0,
        idx: BTreeMap::new(),
        low: BTreeMap::new(),
        on: BTreeSet::new(),
        stack: Vec::new(),
        out: Vec::new(),
    };
    for n in nodes {
        if !st.idx.contains_key(n) {
            strong(&mut st, n);
        }
    }
    st.out
}

/// Translates all data definitions of `files` into one Lean module body.
pub fn translate(files: &[SourceFile], commit_short: &str) -> ShallowOutput {
    let mut statuses = Vec::new();
    // Collect trait names first (needed to classify generic bounds).
    let mut traits = BTreeSet::new();
    for f in files {
        for it in &f.items {
            if let syn::Item::Trait(t) = &it.item {
                traits.insert(t.ident.to_string());
            }
        }
    }
    let mut decls: BTreeMap<String, Decl> = BTreeMap::new();
    let mut trait_assoc: BTreeMap<String, Vec<String>> = BTreeMap::new();
    let mut order = 0usize;
    let mut instance_counts: BTreeMap<String, usize> = BTreeMap::new();
    for f in files {
        for it in &f.items {
            order += 1;
            let mut record = |kind: &'static str, item: String, skipped: Option<String>| {
                statuses.push(ShallowStatus { file: f.rel_path.clone(), line: it.line, item, kind, skipped });
            };
            let (name, kind, generics) = match &it.item {
                syn::Item::Struct(s) => (s.ident.to_string(), Kind::Struct(s.clone()), &s.generics),
                syn::Item::Enum(e) => (e.ident.to_string(), Kind::Enum(e.clone()), &e.generics),
                syn::Item::Type(t) => (t.ident.to_string(), Kind::Alias(t.clone()), &t.generics),
                syn::Item::Trait(t) => {
                    let assoc: Vec<String> = t
                        .items
                        .iter()
                        .filter_map(|i| if let syn::TraitItem::Type(ty) = i { Some(ty.ident.to_string()) } else { None })
                        .collect();
                    trait_assoc.insert(t.ident.to_string(), assoc);
                    (t.ident.to_string(), Kind::Class(t.clone()), &t.generics)
                }
                syn::Item::Impl(im) => {
                    let Some((_, p, _)) = &im.trait_ else { continue };
                    let tn = p.segments.last().unwrap().ident.to_string();
                    if !traits.contains(&tn) {
                        record("instance", format!("impl {tn}"), Some(format!("trait `{tn}` is not defined by the specification")));
                        continue;
                    }
                    let self_name = match &*im.self_ty {
                        syn::Type::Path(tp) => tp.path.segments.last().unwrap().ident.to_string(),
                        _ => "Self".into(),
                    };
                    let base = format!("inst{tn}{self_name}");
                    let k = instance_counts.entry(base.clone()).or_default();
                    let name = if *k == 0 { base } else { format!("{base}{k}") };
                    *k += 1;
                    (name, Kind::Instance(im.clone()), &im.generics)
                }
                _ => continue,
            };
            let gi = match generic_infos(generics, &traits) {
                Ok(g) => g,
                Err(e) => {
                    record(kind_name(&kind), name.clone(), Some(e));
                    continue;
                }
            };
            if decls.contains_key(&name) {
                record(kind_name(&kind), name.clone(), Some("duplicate top-level name".into()));
                continue;
            }
            decls.insert(name.clone(), Decl { name, file: f.rel_path.clone(), line: it.line, order, kind, generics: gi });
        }
    }

    // Iteratively drop declarations that cannot be translated (and anything
    // depending on them) until a fixpoint is reached.
    let empty = BTreeSet::new();
    let mut graph: BTreeMap<String, Vec<String>> = BTreeMap::new();
    loop {
        let ctx = Ctx { decls: &decls, trait_assoc: &trait_assoc, expand: &empty };
        let mut bad: Vec<(String, String)> = Vec::new();
        graph.clear();
        for (n, d) in &decls {
            match decl_deps(d, &ctx) {
                Ok(deps) => {
                    let missing: Vec<&String> = deps.iter().filter(|x| !decls.contains_key(*x)).collect();
                    if let Some(m) = missing.first() {
                        bad.push((n.clone(), format!("depends on `{m}`, which is not shallowly embedded")));
                    } else {
                        graph.insert(n.clone(), deps.into_iter().collect());
                    }
                }
                Err(e) => bad.push((n.clone(), e)),
            }
        }
        if bad.is_empty() {
            break;
        }
        for (n, why) in bad {
            let d = decls.remove(&n).unwrap();
            statuses.push(ShallowStatus { file: d.file, line: d.line, item: n, kind: kind_name(&d.kind), skipped: Some(why) });
        }
    }

    // Order nodes by source order for deterministic traversal.
    let mut nodes: Vec<String> = decls.keys().cloned().collect();
    nodes.sort_by_key(|n| decls[n].order);
    for v in graph.values_mut() {
        v.sort_by_key(|n| decls[n].order);
    }
    let comps = sccs(&nodes, &graph);
    // Emit groups in dependency order, preferring source order among the
    // groups whose dependencies have all been emitted (Kahn's algorithm with
    // a source-order priority), so the output reads like the specification.
    let comp_of: BTreeMap<String, usize> =
        comps.iter().enumerate().flat_map(|(i, c)| c.iter().map(move |n| (n.clone(), i))).collect();
    let min_order: Vec<usize> = comps.iter().map(|c| c.iter().map(|n| decls[n].order).min().unwrap()).collect();
    let mut pending: Vec<BTreeSet<usize>> = vec![BTreeSet::new(); comps.len()];
    let mut dependents: Vec<BTreeSet<usize>> = vec![BTreeSet::new(); comps.len()];
    for (i, c) in comps.iter().enumerate() {
        for n in c {
            for d in graph.get(n).into_iter().flatten() {
                let j = comp_of[d];
                if j != i {
                    pending[i].insert(j);
                    dependents[j].insert(i);
                }
            }
        }
    }
    let mut ready: BTreeSet<(usize, usize)> =
        (0..comps.len()).filter(|i| pending[*i].is_empty()).map(|i| (min_order[i], i)).collect();
    let mut ordered: Vec<Vec<String>> = Vec::new();
    while let Some(&(o, i)) = ready.iter().next() {
        ready.remove(&(o, i));
        ordered.push(comps[i].clone());
        for &k in &dependents[i] {
            pending[k].remove(&i);
            if pending[k].is_empty() {
                ready.insert((min_order[k], k));
            }
        }
    }
    assert_eq!(ordered.len(), comps.len(), "condensation of the dependency graph must be acyclic");
    let comps = ordered;

    let mut out = String::new();
    for comp in comps {
        let mut comp = comp;
        comp.sort_by_key(|n| decls[n].order);
        let recursive = comp.len() > 1 || graph.get(&comp[0]).map(|s| s.contains(&comp[0])).unwrap_or(false);
        if !recursive {
            let d = &decls[&comp[0]];
            let ctx = Ctx { decls: &decls, trait_assoc: &trait_assoc, expand: &empty };
            let text = render_decl(d, &ctx, commit_short).expect("validated above");
            out.push_str(&text);
            out.push_str(&derivings(d, &decls, &graph));
            out.push('\n');
            statuses.push(ShallowStatus { file: d.file.clone(), line: d.line, item: d.name.clone(), kind: kind_name(&d.kind), skipped: None });
            continue;
        }
        if comp.len() == 1 {
            // A single self-recursive type needs no `mutual` block.
            let d = &decls[&comp[0]];
            if matches!(d.kind, Kind::Alias(_)) {
                panic!("self-recursive type alias `{}`", d.name);
            }
            let ctx = Ctx { decls: &decls, trait_assoc: &trait_assoc, expand: &empty };
            out.push_str(&format!("-- `{}` is self-recursive.\n", d.name));
            out.push_str(&render_decl(d, &ctx, commit_short).expect("validated above"));
            out.push('\n');
            statuses.push(ShallowStatus { file: d.file.clone(), line: d.line, item: d.name.clone(), kind: kind_name(&d.kind), skipped: None });
            continue;
        }
        let aliases: BTreeSet<String> =
            comp.iter().filter(|n| matches!(decls[*n].kind, Kind::Alias(_))).cloned().collect();
        let ctx = Ctx { decls: &decls, trait_assoc: &trait_assoc, expand: &aliases };
        let types: Vec<&String> = comp.iter().filter(|n| !aliases.contains(*n)).collect();
        out.push_str(&format!(
            "-- Recursive group (emitted as one `mutual` block): {}.\n",
            comp.iter().map(|n| format!("`{n}`")).collect::<Vec<_>>().join(", ")
        ));
        if !aliases.is_empty() {
            out.push_str(&format!(
                "-- Type aliases expanded inside this block (rule 4): {}.\n",
                aliases.iter().map(|n| format!("`{n}`")).collect::<Vec<_>>().join(", ")
            ));
        }
        out.push_str("mutual\n\n");
        for n in &types {
            let d = &decls[*n];
            if matches!(d.kind, Kind::Class(_) | Kind::Instance(_)) {
                panic!("class/instance `{n}` in a recursive group");
            }
            out.push_str(&render_decl(d, &ctx, commit_short).expect("validated above"));
            out.push('\n');
        }
        out.push_str("end\n\n");
        let plain = Ctx { decls: &decls, trait_assoc: &trait_assoc, expand: &empty };
        for n in &aliases {
            let d = &decls[n];
            out.push_str(&render_decl(d, &plain, commit_short).expect("validated above"));
            out.push('\n');
        }
        for n in &comp {
            let d = &decls[n];
            statuses.push(ShallowStatus { file: d.file.clone(), line: d.line, item: d.name.clone(), kind: kind_name(&d.kind), skipped: None });
        }
    }
    statuses.sort_by(|a, b| (a.file.as_str(), a.line, a.item.as_str()).cmp(&(b.file.as_str(), b.line, b.item.as_str())));
    ShallowOutput { lean: out, statuses }
}

fn kind_name(k: &Kind) -> &'static str {
    match k {
        Kind::Struct(_) => "struct",
        Kind::Enum(_) => "enum",
        Kind::Alias(_) => "type alias",
        Kind::Class(_) => "trait (class)",
        Kind::Instance(_) => "trait impl (instance)",
    }
}

/// Decides whether to derive `DecidableEq` for a non-recursive declaration:
/// only for structs and enums without trait-bounded parameters whose field
/// types avoid functions, associated-type projections, and declarations for
/// which `DecidableEq` was not derived.
fn derivings(d: &Decl, decls: &BTreeMap<String, Decl>, graph: &BTreeMap<String, Vec<String>>) -> String {
    if decidable(d, decls, graph, &mut BTreeSet::new()) {
        format!("deriving instance DecidableEq for {}\n", ident(&d.name))
    } else {
        String::new()
    }
}

fn decidable(d: &Decl, decls: &BTreeMap<String, Decl>, graph: &BTreeMap<String, Vec<String>>, visiting: &mut BTreeSet<String>) -> bool {
    if !matches!(d.kind, Kind::Struct(_) | Kind::Enum(_)) {
        return false;
    }
    if d.generics.iter().any(|g| !g.trait_bounds.is_empty()) {
        return false;
    }
    if graph.get(&d.name).map(|deps| deps.contains(&d.name)).unwrap_or(false) {
        return false;
    }
    if !visiting.insert(d.name.clone()) {
        return false;
    }
    let fields: Vec<&syn::Type> = match &d.kind {
        Kind::Struct(s) => s.fields.iter().map(|f| &f.ty).collect(),
        Kind::Enum(e) => e.variants.iter().flat_map(|v| v.fields.iter().map(|f| &f.ty)).collect(),
        _ => unreachable!(),
    };
    if !fields.iter().all(|t| type_is_plain(t)) {
        visiting.remove(&d.name);
        return false;
    }
    let ok = graph.get(&d.name).map(|deps| {
        deps.iter().all(|dep| match decls.get(dep) {
            Some(dd) => match dd.kind {
                Kind::Alias(_) => alias_decidable(dd, decls, graph, visiting),
                _ => decidable(dd, decls, graph, visiting),
            },
            None => false,
        })
    });
    visiting.remove(&d.name);
    ok.unwrap_or(true)
}

/// True if `t` contains no function types, `impl Trait` types, associated-type
/// projections, or `DynWrite` (none of which have decidable equality).
fn type_is_plain(t: &syn::Type) -> bool {
    match t {
        syn::Type::Paren(p) => type_is_plain(&p.elem),
        syn::Type::Group(g) => type_is_plain(&g.elem),
        syn::Type::Tuple(tu) => tu.elems.iter().all(type_is_plain),
        syn::Type::Path(p) if p.qself.is_none() => {
            let segs: Vec<&syn::PathSegment> = p
                .path
                .segments
                .iter()
                .skip_while(|s| MODULE_PREFIXES.contains(&s.ident.to_string().as_str()))
                .collect();
            if segs.len() != 1 || segs[0].ident == "DynWrite" {
                return false;
            }
            match &segs[0].arguments {
                syn::PathArguments::None => true,
                syn::PathArguments::AngleBracketed(ab) => ab.args.iter().all(|a| match a {
                    syn::GenericArgument::Type(t) => type_is_plain(t),
                    _ => false,
                }),
                syn::PathArguments::Parenthesized(_) => false,
            }
        }
        _ => false,
    }
}

fn alias_decidable(d: &Decl, decls: &BTreeMap<String, Decl>, graph: &BTreeMap<String, Vec<String>>, visiting: &mut BTreeSet<String>) -> bool {
    let Kind::Alias(a) = &d.kind else { return false };
    if !type_is_plain(&a.ty) || d.generics.iter().any(|g| !g.trait_bounds.is_empty()) {
        return false;
    }
    graph.get(&d.name).map(|deps| {
        deps.iter().all(|dep| match decls.get(dep) {
            Some(dd) => match dd.kind {
                Kind::Alias(_) => alias_decidable(dd, decls, graph, visiting),
                _ => decidable(dd, decls, graph, visiting),
            },
            None => false,
        })
    }).unwrap_or(true)
}
