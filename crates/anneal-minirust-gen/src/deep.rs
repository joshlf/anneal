// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Deep embedding: one-to-one translation of `syn` syntax trees into terms of
//! the hand-written Lean schema `MiniRustSpec.Syntax`
//! (`minirust/lean/MiniRustSpec/Meta/Syntax.lean`).
//!
//! Every `syn` node is mapped to exactly one Lean constructor of the same
//! syntactic category. The only lossy mappings are the explicit `verbatim`
//! and `tokens` constructors, which carry the node's source tokens as a string
//! and are counted as *opaque* in the coverage report. Nothing is dropped
//! silently: every visited node increments either a structural or an opaque
//! counter keyed by its `syn` variant name.
//!
//! Spans, token punctuation, and `//` comments are not represented; `///` doc
//! comments are kept as `#[doc = "..."]` attributes because `syn` presents
//! them that way.

use std::collections::BTreeMap;

use quote::ToTokens;
use syn::punctuated::Punctuated;

use crate::lean::Term;

/// Structural/opaque visit counts for one `syn` node kind.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct NodeCount {
    pub structural: u64,
    pub opaque: u64,
}

/// Node-kind coverage counters accumulated while emitting.
#[derive(Debug, Clone, Default)]
pub struct Coverage {
    pub kinds: BTreeMap<String, NodeCount>,
}

impl Coverage {
    fn hit(&mut self, kind: &str) {
        self.kinds.entry(kind.to_string()).or_default().structural += 1;
    }
    fn opaque(&mut self, kind: &str) {
        self.kinds.entry(kind.to_string()).or_default().opaque += 1;
    }
    pub fn merge(&mut self, other: &Coverage) {
        for (k, v) in &other.kinds {
            let e = self.kinds.entry(k.clone()).or_default();
            e.structural += v.structural;
            e.opaque += v.opaque;
        }
    }
    pub fn totals(&self) -> NodeCount {
        let mut t = NodeCount::default();
        for v in self.kinds.values() {
            t.structural += v.structural;
            t.opaque += v.opaque;
        }
        t
    }
}

/// Renders the source tokens of `node` (used only for opaque payloads).
pub fn tokens_of<T: ToTokens>(node: &T) -> String {
    node.to_token_stream().to_string()
}

fn ctor(head: &str, args: Vec<Term>) -> Term {
    Term::app(head, args)
}

fn list<T>(items: impl IntoIterator<Item = T>, mut f: impl FnMut(T) -> Term) -> Term {
    Term::List(items.into_iter().map(&mut f).collect())
}

fn ident_term(i: &syn::Ident) -> Term {
    Term::str(&i.to_string())
}

fn opt_ident(i: Option<&syn::Ident>) -> Term {
    Term::option(i.map(ident_term))
}

fn opt_label(l: &Option<syn::Label>) -> Term {
    Term::option(l.as_ref().map(|l| Term::str(&l.name.ident.to_string())))
}

fn opt_lifetime(l: &Option<syn::Lifetime>) -> Term {
    Term::option(l.as_ref().map(|l| Term::str(&l.ident.to_string())))
}

/// The emitter state: coverage counters.
#[derive(Default)]
pub struct Emitter {
    pub cov: Coverage,
}

impl Emitter {
    // ----- leaves ---------------------------------------------------------

    fn vis(&mut self, v: &syn::Visibility) -> Term {
        match v {
            syn::Visibility::Public(_) => {
                self.cov.hit("Visibility::Public");
                Term::atom("Visibility.pub")
            }
            syn::Visibility::Restricted(r) => {
                self.cov.hit("Visibility::Restricted");
                ctor("Visibility.restricted", vec![Term::str(&tokens_of(&r.path))])
            }
            syn::Visibility::Inherited => {
                self.cov.hit("Visibility::Inherited");
                Term::atom("Visibility.inherited")
            }
        }
    }

    fn meta_args(&mut self, m: &syn::Meta) -> Term {
        match m {
            syn::Meta::Path(_) => {
                self.cov.hit("Attribute::Path");
                Term::atom("AttrMeta.path")
            }
            syn::Meta::List(l) => {
                match l.parse_args_with(Punctuated::<syn::Meta, syn::Token![,]>::parse_terminated) {
                    Ok(nested) => {
                        self.cov.hit("Attribute::List");
                        let items = nested.iter().map(|nm| self.meta_item(nm)).collect();
                        ctor("AttrMeta.list", vec![Term::List(items)])
                    }
                    Err(_) => {
                        self.cov.opaque("Attribute::List");
                        ctor("AttrMeta.listTokens", vec![Term::str(&l.tokens.to_string())])
                    }
                }
            }
            syn::Meta::NameValue(nv) => {
                self.cov.hit("Attribute::NameValue");
                let value = match &nv.value {
                    syn::Expr::Lit(syn::ExprLit { lit: syn::Lit::Str(s), .. }) => s.value(),
                    other => tokens_of(other),
                };
                ctor("AttrMeta.nameValue", vec![Term::str(&value)])
            }
        }
    }

    fn meta_item(&mut self, m: &syn::Meta) -> Term {
        let path = tokens_of(m.path()).replace(' ', "");
        let args = self.meta_args(m);
        ctor("MetaItem.mk", vec![Term::str(&path), args])
    }

    fn attr(&mut self, a: &syn::Attribute) -> Term {
        let outer = matches!(a.style, syn::AttrStyle::Outer);
        let path = tokens_of(a.path()).replace(' ', "");
        let args = self.meta_args(&a.meta);
        ctor("Attr.mk", vec![Term::bool(outer), Term::str(&path), args])
    }

    fn attrs(&mut self, attrs: &[syn::Attribute]) -> Term {
        let items: Vec<Term> = attrs.iter().map(|a| self.attr(a)).collect();
        Term::List(items)
    }

    fn lit(&mut self, l: &syn::Lit) -> Term {
        match l {
            syn::Lit::Str(s) => {
                self.cov.hit("Lit::Str");
                ctor("Lit.str", vec![Term::str(&s.value())])
            }
            syn::Lit::ByteStr(b) => {
                self.cov.hit("Lit::ByteStr");
                ctor("Lit.byteStr", vec![list(b.value(), |x| Term::nat(x as u128))])
            }
            syn::Lit::Byte(b) => {
                self.cov.hit("Lit::Byte");
                ctor("Lit.byte", vec![Term::nat(b.value() as u128)])
            }
            syn::Lit::Char(c) => {
                self.cov.hit("Lit::Char");
                let v = c.value();
                ctor("Lit.char", vec![Term::atom(format!("(Char.ofNat {})", v as u32))])
            }
            syn::Lit::Int(i) => match i.base10_parse::<u128>() {
                Ok(v) => {
                    self.cov.hit("Lit::Int");
                    ctor("Lit.int", vec![Term::nat(v), Term::str(i.suffix())])
                }
                Err(_) => {
                    self.cov.opaque("Lit::Int");
                    ctor("Lit.verbatim", vec![Term::str(&tokens_of(i))])
                }
            },
            syn::Lit::Float(f) => {
                self.cov.hit("Lit::Float");
                ctor("Lit.float", vec![Term::str(f.base10_digits()), Term::str(f.suffix())])
            }
            syn::Lit::Bool(b) => {
                self.cov.hit("Lit::Bool");
                ctor("Lit.bool", vec![Term::bool(b.value)])
            }
            other => {
                self.cov.opaque("Lit::Other");
                ctor("Lit.verbatim", vec![Term::str(&tokens_of(other))])
            }
        }
    }

    fn member(&mut self, m: &syn::Member) -> Term {
        match m {
            syn::Member::Named(i) => {
                self.cov.hit("Member::Named");
                ctor("Member.named", vec![ident_term(i)])
            }
            syn::Member::Unnamed(idx) => {
                self.cov.hit("Member::Unnamed");
                ctor("Member.unnamed", vec![Term::nat(idx.index as u128)])
            }
        }
    }

    fn binop(&mut self, op: &syn::BinOp) -> Term {
        use syn::BinOp as B;
        let name = match op {
            B::Add(_) => "add",
            B::Sub(_) => "sub",
            B::Mul(_) => "mul",
            B::Div(_) => "div",
            B::Rem(_) => "rem",
            B::And(_) => "and",
            B::Or(_) => "or",
            B::BitXor(_) => "bitXor",
            B::BitAnd(_) => "bitAnd",
            B::BitOr(_) => "bitOr",
            B::Shl(_) => "shl",
            B::Shr(_) => "shr",
            B::Eq(_) => "eq",
            B::Lt(_) => "lt",
            B::Le(_) => "le",
            B::Ne(_) => "ne",
            B::Ge(_) => "ge",
            B::Gt(_) => "gt",
            B::AddAssign(_) => "addAssign",
            B::SubAssign(_) => "subAssign",
            B::MulAssign(_) => "mulAssign",
            B::DivAssign(_) => "divAssign",
            B::RemAssign(_) => "remAssign",
            B::BitXorAssign(_) => "bitXorAssign",
            B::BitAndAssign(_) => "bitAndAssign",
            B::BitOrAssign(_) => "bitOrAssign",
            B::ShlAssign(_) => "shlAssign",
            B::ShrAssign(_) => "shrAssign",
            _ => panic!("unsupported binary operator {}", tokens_of(op)),
        };
        self.cov.hit("BinOp");
        Term::atom(format!("BinOp.{name}"))
    }

    fn unop(&mut self, op: &syn::UnOp) -> Term {
        let name = match op {
            syn::UnOp::Deref(_) => "deref",
            syn::UnOp::Not(_) => "not",
            syn::UnOp::Neg(_) => "neg",
            _ => panic!("unsupported unary operator {}", tokens_of(op)),
        };
        self.cov.hit("UnOp");
        Term::atom(format!("UnOp.{name}"))
    }

    fn limits(&mut self, l: &syn::RangeLimits) -> Term {
        self.cov.hit("RangeLimits");
        match l {
            syn::RangeLimits::HalfOpen(_) => Term::atom("RangeLimits.halfOpen"),
            syn::RangeLimits::Closed(_) => Term::atom("RangeLimits.closed"),
        }
    }

    // ----- paths and types ------------------------------------------------

    pub fn path(&mut self, p: &syn::Path) -> Term {
        self.cov.hit("Path");
        let segs: Vec<Term> = p
            .segments
            .iter()
            .map(|s| {
                self.cov.hit("PathSegment");
                let args = self.path_args(&s.arguments);
                ctor("PathSegment.mk", vec![ident_term(&s.ident), args])
            })
            .collect();
        ctor("Path.mk", vec![Term::bool(p.leading_colon.is_some()), Term::List(segs)])
    }

    fn angle_args(&mut self, a: &syn::AngleBracketedGenericArguments) -> Term {
        self.cov.hit("PathArguments::AngleBracketed");
        let args: Vec<Term> = a.args.iter().map(|g| self.generic_arg(g)).collect();
        ctor("PathArguments.angleBracketed", vec![Term::bool(a.colon2_token.is_some()), Term::List(args)])
    }

    fn path_args(&mut self, a: &syn::PathArguments) -> Term {
        match a {
            syn::PathArguments::None => {
                self.cov.hit("PathArguments::None");
                Term::atom("PathArguments.none")
            }
            syn::PathArguments::AngleBracketed(a) => self.angle_args(a),
            syn::PathArguments::Parenthesized(p) => {
                self.cov.hit("PathArguments::Parenthesized");
                let inputs: Vec<Term> = p.inputs.iter().map(|t| self.ty(t)).collect();
                let output = match &p.output {
                    syn::ReturnType::Default => None,
                    syn::ReturnType::Type(_, t) => Some(self.ty(t)),
                };
                ctor("PathArguments.parenthesized", vec![Term::List(inputs), Term::option(output)])
            }
        }
    }

    fn opt_angle(&mut self, a: &Option<syn::AngleBracketedGenericArguments>) -> Term {
        match a {
            None => {
                self.cov.hit("PathArguments::None");
                Term::atom("PathArguments.none")
            }
            Some(a) => self.angle_args(a),
        }
    }

    fn generic_arg(&mut self, g: &syn::GenericArgument) -> Term {
        match g {
            syn::GenericArgument::Lifetime(l) => {
                self.cov.hit("GenericArgument::Lifetime");
                ctor("GenericArgument.lifetime", vec![Term::str(&l.ident.to_string())])
            }
            syn::GenericArgument::Type(t) => {
                self.cov.hit("GenericArgument::Type");
                ctor("GenericArgument.type", vec![self.ty(t)])
            }
            syn::GenericArgument::Const(e) => {
                self.cov.hit("GenericArgument::Const");
                ctor("GenericArgument.const", vec![self.expr(e)])
            }
            syn::GenericArgument::AssocType(a) => {
                self.cov.hit("GenericArgument::AssocType");
                let g = self.opt_angle(&a.generics);
                ctor("GenericArgument.assocType", vec![ident_term(&a.ident), g, self.ty(&a.ty)])
            }
            syn::GenericArgument::AssocConst(a) => {
                self.cov.hit("GenericArgument::AssocConst");
                let g = self.opt_angle(&a.generics);
                ctor("GenericArgument.assocConst", vec![ident_term(&a.ident), g, self.expr(&a.value)])
            }
            syn::GenericArgument::Constraint(c) => {
                self.cov.hit("GenericArgument::Constraint");
                let g = self.opt_angle(&c.generics);
                let bounds = self.bounds(&c.bounds);
                ctor("GenericArgument.constraint", vec![ident_term(&c.ident), g, bounds])
            }
            other => panic!("unsupported generic argument {}", tokens_of(other)),
        }
    }

    fn qself(&mut self, q: &Option<syn::QSelf>) -> Term {
        Term::option(q.as_ref().map(|q| {
            self.cov.hit("QSelf");
            let t = self.ty(&q.ty);
            ctor("QSelf.mk", vec![t, Term::nat(q.position as u128), Term::bool(q.as_token.is_some())])
        }))
    }

    fn bounds(&mut self, b: &Punctuated<syn::TypeParamBound, syn::Token![+]>) -> Term {
        let items: Vec<Term> = b.iter().map(|x| self.bound(x)).collect();
        Term::List(items)
    }

    fn bound(&mut self, b: &syn::TypeParamBound) -> Term {
        match b {
            syn::TypeParamBound::Trait(t) => {
                self.cov.hit("TypeParamBound::Trait");
                let lifetimes: Vec<Term> = t
                    .lifetimes
                    .iter()
                    .flat_map(|bl| bl.lifetimes.iter())
                    .map(|gp| match gp {
                        syn::GenericParam::Lifetime(l) => Term::str(&l.lifetime.ident.to_string()),
                        other => Term::str(&tokens_of(other)),
                    })
                    .collect();
                let maybe = matches!(t.modifier, syn::TraitBoundModifier::Maybe(_));
                let path = self.path(&t.path);
                ctor(
                    "TypeParamBound.trait",
                    vec![Term::bool(t.paren_token.is_some()), Term::bool(maybe), Term::List(lifetimes), path],
                )
            }
            syn::TypeParamBound::Lifetime(l) => {
                self.cov.hit("TypeParamBound::Lifetime");
                ctor("TypeParamBound.lifetime", vec![Term::str(&l.ident.to_string())])
            }
            other => {
                self.cov.opaque("TypeParamBound::Other");
                ctor("TypeParamBound.verbatim", vec![Term::str(&tokens_of(other))])
            }
        }
    }

    pub fn ty(&mut self, t: &syn::Type) -> Term {
        use syn::Type as T;
        match t {
            T::Array(a) => {
                self.cov.hit("Type::Array");
                ctor("Ty.array", vec![self.ty(&a.elem), self.expr(&a.len)])
            }
            T::BareFn(f) => {
                self.cov.hit("Type::BareFn");
                let lifetimes: Vec<Term> = f
                    .lifetimes
                    .iter()
                    .flat_map(|bl| bl.lifetimes.iter())
                    .map(|gp| Term::str(&tokens_of(gp)))
                    .collect();
                let inputs: Vec<Term> = f.inputs.iter().map(|a| self.ty(&a.ty)).collect();
                let output = match &f.output {
                    syn::ReturnType::Default => None,
                    syn::ReturnType::Type(_, t) => Some(self.ty(t)),
                };
                ctor(
                    "Ty.bareFn",
                    vec![
                        Term::List(lifetimes),
                        Term::bool(f.unsafety.is_some()),
                        Term::List(inputs),
                        Term::bool(f.variadic.is_some()),
                        Term::option(output),
                    ],
                )
            }
            T::ImplTrait(i) => {
                self.cov.hit("Type::ImplTrait");
                ctor("Ty.implTrait", vec![self.bounds(&i.bounds)])
            }
            T::TraitObject(o) => {
                self.cov.hit("Type::TraitObject");
                ctor("Ty.traitObject", vec![Term::bool(o.dyn_token.is_some()), self.bounds(&o.bounds)])
            }
            T::Infer(_) => {
                self.cov.hit("Type::Infer");
                Term::atom("Ty.infer")
            }
            T::Never(_) => {
                self.cov.hit("Type::Never");
                Term::atom("Ty.never")
            }
            T::Paren(p) => {
                self.cov.hit("Type::Paren");
                ctor("Ty.paren", vec![self.ty(&p.elem)])
            }
            T::Group(g) => {
                self.cov.hit("Type::Group");
                ctor("Ty.group", vec![self.ty(&g.elem)])
            }
            T::Path(p) => {
                self.cov.hit("Type::Path");
                let q = self.qself(&p.qself);
                ctor("Ty.path", vec![q, self.path(&p.path)])
            }
            T::Ptr(p) => {
                self.cov.hit("Type::Ptr");
                ctor("Ty.ptr", vec![Term::bool(p.mutability.is_some()), self.ty(&p.elem)])
            }
            T::Reference(r) => {
                self.cov.hit("Type::Reference");
                ctor(
                    "Ty.reference",
                    vec![opt_lifetime(&r.lifetime), Term::bool(r.mutability.is_some()), self.ty(&r.elem)],
                )
            }
            T::Slice(s) => {
                self.cov.hit("Type::Slice");
                ctor("Ty.slice", vec![self.ty(&s.elem)])
            }
            T::Tuple(tu) => {
                self.cov.hit("Type::Tuple");
                let elems: Vec<Term> = tu.elems.iter().map(|t| self.ty(t)).collect();
                ctor("Ty.tuple", vec![Term::List(elems)])
            }
            T::Macro(m) => {
                self.cov.hit("Type::Macro");
                ctor("Ty.macro", vec![self.mac(&m.mac)])
            }
            other => {
                self.cov.opaque("Type::Other");
                ctor("Ty.verbatim", vec![Term::str(&tokens_of(other))])
            }
        }
    }

    // ----- expressions ----------------------------------------------------

    fn with_attrs(&mut self, attrs: &[syn::Attribute], inner: Term) -> Term {
        if attrs.is_empty() {
            inner
        } else {
            self.cov.hit("Expr::WithAttrs");
            let a = self.attrs(attrs);
            ctor("Expr.withAttrs", vec![a, inner])
        }
    }

    fn opt_expr(&mut self, e: &Option<Box<syn::Expr>>) -> Term {
        Term::option(e.as_ref().map(|e| self.expr(e)))
    }

    pub fn block(&mut self, b: &syn::Block) -> Term {
        self.cov.hit("Block");
        let stmts: Vec<Term> = b.stmts.iter().map(|s| self.stmt(s)).collect();
        ctor("Block.mk", vec![Term::List(stmts)])
    }

    fn stmt(&mut self, s: &syn::Stmt) -> Term {
        match s {
            syn::Stmt::Local(l) => {
                self.cov.hit("Stmt::Local");
                let attrs = self.attrs(&l.attrs);
                let pat = self.pat(&l.pat);
                let (init, diverge) = match &l.init {
                    None => (None, None),
                    Some(i) => {
                        let e = self.expr(&i.expr);
                        let d = i.diverge.as_ref().map(|(_, d)| self.expr(d));
                        (Some(e), d)
                    }
                };
                ctor("Stmt.letStmt", vec![attrs, pat, Term::option(init), Term::option(diverge)])
            }
            syn::Stmt::Item(i) => {
                self.cov.hit("Stmt::Item");
                ctor("Stmt.item", vec![self.item(i)])
            }
            syn::Stmt::Expr(e, semi) => {
                self.cov.hit("Stmt::Expr");
                ctor("Stmt.expr", vec![self.expr(e), Term::bool(semi.is_some())])
            }
            syn::Stmt::Macro(m) => {
                self.cov.hit("Stmt::Macro");
                let attrs = self.attrs(&m.attrs);
                let mac = self.mac(&m.mac);
                ctor("Stmt.macro", vec![attrs, mac, Term::bool(m.semi_token.is_some())])
            }
        }
    }

    pub fn mac(&mut self, m: &syn::Macro) -> Term {
        self.cov.hit("Macro");
        let delim = match m.delimiter {
            syn::MacroDelimiter::Paren(_) => "MacroDelimiter.paren",
            syn::MacroDelimiter::Brace(_) => "MacroDelimiter.brace",
            syn::MacroDelimiter::Bracket(_) => "MacroDelimiter.bracket",
        };
        let path = self.path(&m.path);
        let body = self.macro_body(m);
        ctor("Macro.mk", vec![path, Term::atom(delim), body])
    }

    /// Parses a macro invocation's tokens into structured arguments when they
    /// form one of the shapes used by specr-lang: a comma-separated expression
    /// list (`panic!`, `assert!`, `throw_ub!`, `format!`, `list![a, b]`), a
    /// repetition (`list![x; n]`), or `matches!(expr, pat)`. Anything else is
    /// kept verbatim and counted as opaque.
    fn macro_body(&mut self, m: &syn::Macro) -> Term {
        use syn::parse::Parser;
        let name = m.path.segments.last().map(|s| s.ident.to_string()).unwrap_or_default();
        if name == "matches" {
            let parser = |input: syn::parse::ParseStream| -> syn::Result<(syn::Expr, syn::Pat, Option<syn::Expr>)> {
                let e: syn::Expr = input.parse()?;
                let _: syn::Token![,] = input.parse()?;
                let p = syn::Pat::parse_multi_with_leading_vert(input)?;
                let guard = if input.peek(syn::Token![if]) {
                    let _: syn::Token![if] = input.parse()?;
                    Some(input.parse::<syn::Expr>()?)
                } else {
                    None
                };
                let _: Option<syn::Token![,]> = input.parse()?;
                Ok((e, p, guard))
            };
            if let Ok((e, p, g)) = parser.parse2(m.tokens.clone()) {
                self.cov.hit("MacroBody::ExprAndPat");
                let e = self.expr(&e);
                let p = self.pat(&p);
                let g = Term::option(g.map(|g| self.expr(&g)));
                return ctor("MacroBody.exprAndPat", vec![e, p, g]);
            }
        }
        if m.tokens.is_empty() {
            self.cov.hit("MacroBody::Exprs");
            return ctor("MacroBody.exprs", vec![Term::List(vec![]), Term::bool(false)]);
        }
        let comma_list = Punctuated::<syn::Expr, syn::Token![,]>::parse_terminated;
        if let Ok(args) = comma_list.parse2(m.tokens.clone()) {
            self.cov.hit("MacroBody::Exprs");
            let trailing = args.trailing_punct();
            let items: Vec<Term> = args.iter().map(|e| self.expr(e)).collect();
            return ctor("MacroBody.exprs", vec![Term::List(items), Term::bool(trailing)]);
        }
        let repeat = |input: syn::parse::ParseStream| -> syn::Result<(syn::Expr, syn::Expr)> {
            let e: syn::Expr = input.parse()?;
            let _: syn::Token![;] = input.parse()?;
            let n: syn::Expr = input.parse()?;
            Ok((e, n))
        };
        if let Ok((e, n)) = repeat.parse2(m.tokens.clone()) {
            self.cov.hit("MacroBody::RepeatList");
            let e = self.expr(&e);
            let n = self.expr(&n);
            return ctor("MacroBody.repeatList", vec![e, n]);
        }
        self.cov.opaque("MacroBody::Tokens");
        ctor("MacroBody.tokens", vec![Term::str(&m.tokens.to_string())])
    }

    pub fn expr(&mut self, e: &syn::Expr) -> Term {
        use syn::Expr as E;
        match e {
            E::Array(a) => {
                self.cov.hit("Expr::Array");
                let elems: Vec<Term> = a.elems.iter().map(|x| self.expr(x)).collect();
                let t = ctor("Expr.array", vec![Term::List(elems)]);
                self.with_attrs(&a.attrs, t)
            }
            E::Assign(a) => {
                self.cov.hit("Expr::Assign");
                let t = ctor("Expr.assign", vec![self.expr(&a.left), self.expr(&a.right)]);
                self.with_attrs(&a.attrs, t)
            }
            E::Async(a) => {
                self.cov.hit("Expr::Async");
                let b = self.block(&a.block);
                let t = ctor("Expr.asyncBlock", vec![Term::bool(a.capture.is_some()), b]);
                self.with_attrs(&a.attrs, t)
            }
            E::Await(a) => {
                self.cov.hit("Expr::Await");
                let t = ctor("Expr.awaitExpr", vec![self.expr(&a.base)]);
                self.with_attrs(&a.attrs, t)
            }
            E::Binary(b) => {
                self.cov.hit("Expr::Binary");
                let l = self.expr(&b.left);
                let op = self.binop(&b.op);
                let r = self.expr(&b.right);
                let t = ctor("Expr.binary", vec![l, op, r]);
                self.with_attrs(&b.attrs, t)
            }
            E::Block(b) => {
                self.cov.hit("Expr::Block");
                let blk = self.block(&b.block);
                let t = ctor("Expr.block", vec![opt_label(&b.label), blk]);
                self.with_attrs(&b.attrs, t)
            }
            E::Break(b) => {
                self.cov.hit("Expr::Break");
                let v = self.opt_expr(&b.expr);
                let t = ctor("Expr.break", vec![opt_lifetime(&b.label), v]);
                self.with_attrs(&b.attrs, t)
            }
            E::Call(c) => {
                self.cov.hit("Expr::Call");
                let f = self.expr(&c.func);
                let args: Vec<Term> = c.args.iter().map(|x| self.expr(x)).collect();
                let t = ctor("Expr.call", vec![f, Term::List(args)]);
                self.with_attrs(&c.attrs, t)
            }
            E::Cast(c) => {
                self.cov.hit("Expr::Cast");
                let t = ctor("Expr.cast", vec![self.expr(&c.expr), self.ty(&c.ty)]);
                self.with_attrs(&c.attrs, t)
            }
            E::Closure(c) => {
                self.cov.hit("Expr::Closure");
                let inputs: Vec<Term> = c.inputs.iter().map(|p| self.pat(p)).collect();
                let output = match &c.output {
                    syn::ReturnType::Default => None,
                    syn::ReturnType::Type(_, t) => Some(self.ty(t)),
                };
                let body = self.expr(&c.body);
                let t = ctor(
                    "Expr.closure",
                    vec![Term::bool(c.capture.is_some()), Term::List(inputs), Term::option(output), body],
                );
                self.with_attrs(&c.attrs, t)
            }
            E::Const(c) => {
                self.cov.hit("Expr::Const");
                let t = ctor("Expr.constBlock", vec![self.block(&c.block)]);
                self.with_attrs(&c.attrs, t)
            }
            E::Continue(c) => {
                self.cov.hit("Expr::Continue");
                let t = ctor("Expr.continue", vec![opt_lifetime(&c.label)]);
                self.with_attrs(&c.attrs, t)
            }
            E::Field(f) => {
                self.cov.hit("Expr::Field");
                let base = self.expr(&f.base);
                let m = self.member(&f.member);
                let t = ctor("Expr.field", vec![base, m]);
                self.with_attrs(&f.attrs, t)
            }
            E::ForLoop(f) => {
                self.cov.hit("Expr::ForLoop");
                let p = self.pat(&f.pat);
                let x = self.expr(&f.expr);
                let b = self.block(&f.body);
                let t = ctor("Expr.forLoop", vec![opt_label(&f.label), p, x, b]);
                self.with_attrs(&f.attrs, t)
            }
            E::Group(g) => {
                self.cov.hit("Expr::Group");
                let t = ctor("Expr.group", vec![self.expr(&g.expr)]);
                self.with_attrs(&g.attrs, t)
            }
            E::If(i) => {
                self.cov.hit("Expr::If");
                let c = self.expr(&i.cond);
                let th = self.block(&i.then_branch);
                let el = Term::option(i.else_branch.as_ref().map(|(_, e)| self.expr(e)));
                let t = ctor("Expr.ite", vec![c, th, el]);
                self.with_attrs(&i.attrs, t)
            }
            E::Index(i) => {
                self.cov.hit("Expr::Index");
                let t = ctor("Expr.index", vec![self.expr(&i.expr), self.expr(&i.index)]);
                self.with_attrs(&i.attrs, t)
            }
            E::Infer(i) => {
                self.cov.hit("Expr::Infer");
                let t = Term::atom("Expr.infer");
                self.with_attrs(&i.attrs, t)
            }
            E::Let(l) => {
                self.cov.hit("Expr::Let");
                let p = self.pat(&l.pat);
                let x = self.expr(&l.expr);
                let t = ctor("Expr.letCond", vec![p, x]);
                self.with_attrs(&l.attrs, t)
            }
            E::Lit(l) => {
                self.cov.hit("Expr::Lit");
                let t = ctor("Expr.lit", vec![self.lit(&l.lit)]);
                self.with_attrs(&l.attrs, t)
            }
            E::Loop(l) => {
                self.cov.hit("Expr::Loop");
                let b = self.block(&l.body);
                let t = ctor("Expr.loop", vec![opt_label(&l.label), b]);
                self.with_attrs(&l.attrs, t)
            }
            E::Macro(m) => {
                self.cov.hit("Expr::Macro");
                let t = ctor("Expr.macro", vec![self.mac(&m.mac)]);
                self.with_attrs(&m.attrs, t)
            }
            E::Match(m) => {
                self.cov.hit("Expr::Match");
                let x = self.expr(&m.expr);
                let arms: Vec<Term> = m
                    .arms
                    .iter()
                    .map(|a| {
                        self.cov.hit("Arm");
                        let attrs = self.attrs(&a.attrs);
                        let p = self.pat(&a.pat);
                        let g = Term::option(a.guard.as_ref().map(|(_, g)| self.expr(g)));
                        let b = self.expr(&a.body);
                        ctor("Arm.mk", vec![attrs, p, g, b])
                    })
                    .collect();
                let t = ctor("Expr.matchExpr", vec![x, Term::List(arms)]);
                self.with_attrs(&m.attrs, t)
            }
            E::MethodCall(m) => {
                self.cov.hit("Expr::MethodCall");
                let r = self.expr(&m.receiver);
                let tf = Term::option(m.turbofish.as_ref().map(|tf| {
                    let args: Vec<Term> = tf.args.iter().map(|g| self.generic_arg(g)).collect();
                    Term::List(args)
                }));
                let args: Vec<Term> = m.args.iter().map(|x| self.expr(x)).collect();
                let t = ctor("Expr.methodCall", vec![r, ident_term(&m.method), tf, Term::List(args)]);
                self.with_attrs(&m.attrs, t)
            }
            E::Paren(p) => {
                self.cov.hit("Expr::Paren");
                let t = ctor("Expr.paren", vec![self.expr(&p.expr)]);
                self.with_attrs(&p.attrs, t)
            }
            E::Path(p) => {
                self.cov.hit("Expr::Path");
                let q = self.qself(&p.qself);
                let t = ctor("Expr.path", vec![q, self.path(&p.path)]);
                self.with_attrs(&p.attrs, t)
            }
            E::Range(r) => {
                self.cov.hit("Expr::Range");
                let s = self.opt_expr(&r.start);
                let l = self.limits(&r.limits);
                let en = self.opt_expr(&r.end);
                let t = ctor("Expr.range", vec![s, l, en]);
                self.with_attrs(&r.attrs, t)
            }
            E::RawAddr(r) => {
                self.cov.hit("Expr::RawAddr");
                let m = matches!(r.mutability, syn::PointerMutability::Mut(_));
                let t = ctor("Expr.rawAddr", vec![Term::bool(m), self.expr(&r.expr)]);
                self.with_attrs(&r.attrs, t)
            }
            E::Reference(r) => {
                self.cov.hit("Expr::Reference");
                let t = ctor("Expr.reference", vec![Term::bool(r.mutability.is_some()), self.expr(&r.expr)]);
                self.with_attrs(&r.attrs, t)
            }
            E::Repeat(r) => {
                self.cov.hit("Expr::Repeat");
                let t = ctor("Expr.repeatExpr", vec![self.expr(&r.expr), self.expr(&r.len)]);
                self.with_attrs(&r.attrs, t)
            }
            E::Return(r) => {
                self.cov.hit("Expr::Return");
                let v = self.opt_expr(&r.expr);
                let t = ctor("Expr.returnExpr", vec![v]);
                self.with_attrs(&r.attrs, t)
            }
            E::Struct(s) => {
                self.cov.hit("Expr::Struct");
                let q = self.qself(&s.qself);
                let p = self.path(&s.path);
                let fields: Vec<Term> = s
                    .fields
                    .iter()
                    .map(|f| {
                        self.cov.hit("FieldValue");
                        let attrs = self.attrs(&f.attrs);
                        let m = self.member(&f.member);
                        let x = self.expr(&f.expr);
                        ctor("FieldValue.mk", vec![attrs, m, Term::bool(f.colon_token.is_none()), x])
                    })
                    .collect();
                let rest = self.opt_expr(&s.rest);
                let t = ctor(
                    "Expr.struct",
                    vec![q, p, Term::List(fields), Term::bool(s.dot2_token.is_some()), rest],
                );
                self.with_attrs(&s.attrs, t)
            }
            E::Try(t) => {
                self.cov.hit("Expr::Try");
                let x = ctor("Expr.tryExpr", vec![self.expr(&t.expr)]);
                self.with_attrs(&t.attrs, x)
            }
            E::TryBlock(t) => {
                self.cov.hit("Expr::TryBlock");
                let x = ctor("Expr.tryBlock", vec![self.block(&t.block)]);
                self.with_attrs(&t.attrs, x)
            }
            E::Tuple(t) => {
                self.cov.hit("Expr::Tuple");
                let elems: Vec<Term> = t.elems.iter().map(|x| self.expr(x)).collect();
                let x = ctor("Expr.tuple", vec![Term::List(elems)]);
                self.with_attrs(&t.attrs, x)
            }
            E::Unary(u) => {
                self.cov.hit("Expr::Unary");
                let op = self.unop(&u.op);
                let x = ctor("Expr.unary", vec![op, self.expr(&u.expr)]);
                self.with_attrs(&u.attrs, x)
            }
            E::Unsafe(u) => {
                self.cov.hit("Expr::Unsafe");
                let x = ctor("Expr.unsafeBlock", vec![self.block(&u.block)]);
                self.with_attrs(&u.attrs, x)
            }
            E::While(w) => {
                self.cov.hit("Expr::While");
                let c = self.expr(&w.cond);
                let b = self.block(&w.body);
                let x = ctor("Expr.whileLoop", vec![opt_label(&w.label), c, b]);
                self.with_attrs(&w.attrs, x)
            }
            E::Yield(y) => {
                self.cov.hit("Expr::Yield");
                let v = self.opt_expr(&y.expr);
                let x = ctor("Expr.yieldExpr", vec![v]);
                self.with_attrs(&y.attrs, x)
            }
            other => {
                self.cov.opaque("Expr::Other");
                ctor("Expr.verbatim", vec![Term::str(&tokens_of(other))])
            }
        }
    }

    // ----- patterns -------------------------------------------------------

    fn pat_with_attrs(&mut self, attrs: &[syn::Attribute], inner: Term) -> Term {
        if attrs.is_empty() {
            inner
        } else {
            self.cov.hit("Pat::WithAttrs");
            let a = self.attrs(attrs);
            ctor("Pat.withAttrs", vec![a, inner])
        }
    }

    pub fn pat(&mut self, p: &syn::Pat) -> Term {
        use syn::Pat as P;
        match p {
            P::Const(c) => {
                self.cov.hit("Pat::Const");
                let t = ctor("Pat.constBlock", vec![self.block(&c.block)]);
                self.pat_with_attrs(&c.attrs, t)
            }
            P::Ident(i) => {
                self.cov.hit("Pat::Ident");
                let sub = Term::option(i.subpat.as_ref().map(|(_, s)| self.pat(s)));
                let t = ctor(
                    "Pat.ident",
                    vec![Term::bool(i.by_ref.is_some()), Term::bool(i.mutability.is_some()), ident_term(&i.ident), sub],
                );
                self.pat_with_attrs(&i.attrs, t)
            }
            P::Lit(l) => {
                self.cov.hit("Pat::Lit");
                let lit = ctor("Expr.lit", vec![self.lit(&l.lit)]);
                let t = ctor("Pat.lit", vec![lit]);
                self.pat_with_attrs(&l.attrs, t)
            }
            P::Macro(m) => {
                self.cov.hit("Pat::Macro");
                let t = ctor("Pat.macro", vec![self.mac(&m.mac)]);
                self.pat_with_attrs(&m.attrs, t)
            }
            P::Or(o) => {
                self.cov.hit("Pat::Or");
                let cases: Vec<Term> = o.cases.iter().map(|c| self.pat(c)).collect();
                let t = ctor("Pat.or", vec![Term::List(cases)]);
                self.pat_with_attrs(&o.attrs, t)
            }
            P::Paren(x) => {
                self.cov.hit("Pat::Paren");
                let t = ctor("Pat.paren", vec![self.pat(&x.pat)]);
                self.pat_with_attrs(&x.attrs, t)
            }
            P::Path(x) => {
                self.cov.hit("Pat::Path");
                let q = self.qself(&x.qself);
                let t = ctor("Pat.path", vec![q, self.path(&x.path)]);
                self.pat_with_attrs(&x.attrs, t)
            }
            P::Range(r) => {
                self.cov.hit("Pat::Range");
                let s = self.opt_expr(&r.start);
                let l = self.limits(&r.limits);
                let e = self.opt_expr(&r.end);
                let t = ctor("Pat.range", vec![s, l, e]);
                self.pat_with_attrs(&r.attrs, t)
            }
            P::Reference(r) => {
                self.cov.hit("Pat::Reference");
                let t = ctor("Pat.reference", vec![Term::bool(r.mutability.is_some()), self.pat(&r.pat)]);
                self.pat_with_attrs(&r.attrs, t)
            }
            P::Rest(r) => {
                self.cov.hit("Pat::Rest");
                let t = Term::atom("Pat.rest");
                self.pat_with_attrs(&r.attrs, t)
            }
            P::Slice(s) => {
                self.cov.hit("Pat::Slice");
                let elems: Vec<Term> = s.elems.iter().map(|x| self.pat(x)).collect();
                let t = ctor("Pat.slice", vec![Term::List(elems)]);
                self.pat_with_attrs(&s.attrs, t)
            }
            P::Struct(s) => {
                self.cov.hit("Pat::Struct");
                let q = self.qself(&s.qself);
                let path = self.path(&s.path);
                let fields: Vec<Term> = s
                    .fields
                    .iter()
                    .map(|f| {
                        self.cov.hit("FieldPat");
                        let attrs = self.attrs(&f.attrs);
                        let m = self.member(&f.member);
                        let x = self.pat(&f.pat);
                        ctor("FieldPat.mk", vec![attrs, m, Term::bool(f.colon_token.is_none()), x])
                    })
                    .collect();
                let t = ctor("Pat.struct", vec![q, path, Term::List(fields), Term::bool(s.rest.is_some())]);
                self.pat_with_attrs(&s.attrs, t)
            }
            P::Tuple(t) => {
                self.cov.hit("Pat::Tuple");
                let elems: Vec<Term> = t.elems.iter().map(|x| self.pat(x)).collect();
                let x = ctor("Pat.tuple", vec![Term::List(elems)]);
                self.pat_with_attrs(&t.attrs, x)
            }
            P::TupleStruct(t) => {
                self.cov.hit("Pat::TupleStruct");
                let q = self.qself(&t.qself);
                let path = self.path(&t.path);
                let elems: Vec<Term> = t.elems.iter().map(|x| self.pat(x)).collect();
                let x = ctor("Pat.tupleStruct", vec![q, path, Term::List(elems)]);
                self.pat_with_attrs(&t.attrs, x)
            }
            P::Type(t) => {
                self.cov.hit("Pat::Type");
                let x = ctor("Pat.typed", vec![self.pat(&t.pat), self.ty(&t.ty)]);
                self.pat_with_attrs(&t.attrs, x)
            }
            P::Wild(w) => {
                self.cov.hit("Pat::Wild");
                let t = Term::atom("Pat.wild");
                self.pat_with_attrs(&w.attrs, t)
            }
            other => {
                self.cov.opaque("Pat::Other");
                ctor("Pat.verbatim", vec![Term::str(&tokens_of(other))])
            }
        }
    }

    // ----- items ----------------------------------------------------------

    pub fn generics(&mut self, g: &syn::Generics) -> Term {
        self.cov.hit("Generics");
        let params: Vec<Term> = g
            .params
            .iter()
            .map(|p| match p {
                syn::GenericParam::Lifetime(l) => {
                    self.cov.hit("GenericParam::Lifetime");
                    let attrs = self.attrs(&l.attrs);
                    let bounds: Vec<Term> = l.bounds.iter().map(|b| Term::str(&b.ident.to_string())).collect();
                    ctor(
                        "GenericParam.lifetime",
                        vec![attrs, Term::str(&l.lifetime.ident.to_string()), Term::List(bounds)],
                    )
                }
                syn::GenericParam::Type(t) => {
                    self.cov.hit("GenericParam::Type");
                    let attrs = self.attrs(&t.attrs);
                    let bounds = self.bounds(&t.bounds);
                    let default = Term::option(t.default.as_ref().map(|d| self.ty(d)));
                    ctor("GenericParam.type", vec![attrs, ident_term(&t.ident), bounds, default])
                }
                syn::GenericParam::Const(c) => {
                    self.cov.hit("GenericParam::Const");
                    let attrs = self.attrs(&c.attrs);
                    let ty = self.ty(&c.ty);
                    let default = Term::option(c.default.as_ref().map(|d| self.expr(d)));
                    ctor("GenericParam.const", vec![attrs, ident_term(&c.ident), ty, default])
                }
            })
            .collect();
        let preds: Vec<Term> = g
            .where_clause
            .iter()
            .flat_map(|w| w.predicates.iter())
            .map(|p| match p {
                syn::WherePredicate::Lifetime(l) => {
                    self.cov.hit("WherePredicate::Lifetime");
                    let bounds: Vec<Term> = l.bounds.iter().map(|b| Term::str(&b.ident.to_string())).collect();
                    ctor(
                        "WherePredicate.lifetime",
                        vec![Term::str(&l.lifetime.ident.to_string()), Term::List(bounds)],
                    )
                }
                syn::WherePredicate::Type(t) => {
                    self.cov.hit("WherePredicate::Type");
                    let lifetimes: Vec<Term> = t
                        .lifetimes
                        .iter()
                        .flat_map(|bl| bl.lifetimes.iter())
                        .map(|gp| Term::str(&tokens_of(gp)))
                        .collect();
                    let bt = self.ty(&t.bounded_ty);
                    let bounds = self.bounds(&t.bounds);
                    ctor("WherePredicate.type", vec![Term::List(lifetimes), bt, bounds])
                }
                other => panic!("unsupported where predicate {}", tokens_of(other)),
            })
            .collect();
        ctor("Generics.mk", vec![Term::List(params), Term::List(preds)])
    }

    pub fn signature(&mut self, s: &syn::Signature) -> Term {
        self.cov.hit("Signature");
        let generics = self.generics(&s.generics);
        let inputs: Vec<Term> = s
            .inputs
            .iter()
            .map(|a| match a {
                syn::FnArg::Receiver(r) => {
                    self.cov.hit("FnArg::Receiver");
                    let attrs = self.attrs(&r.attrs);
                    let (is_ref, lt) = match &r.reference {
                        None => (false, None),
                        Some((_, lt)) => (true, lt.as_ref().map(|l| Term::str(&l.ident.to_string()))),
                    };
                    let colon_ty = if r.colon_token.is_some() { Some(self.ty(&r.ty)) } else { None };
                    ctor(
                        "FnArg.receiver",
                        vec![
                            attrs,
                            Term::bool(is_ref),
                            Term::option(lt),
                            Term::bool(r.mutability.is_some()),
                            Term::option(colon_ty),
                        ],
                    )
                }
                syn::FnArg::Typed(t) => {
                    self.cov.hit("FnArg::Typed");
                    let attrs = self.attrs(&t.attrs);
                    let p = self.pat(&t.pat);
                    let ty = self.ty(&t.ty);
                    ctor("FnArg.typed", vec![attrs, p, ty])
                }
            })
            .collect();
        let output = match &s.output {
            syn::ReturnType::Default => None,
            syn::ReturnType::Type(_, t) => Some(self.ty(t)),
        };
        let abi = s.abi.as_ref().map(|a| Term::str(&tokens_of(a)));
        ctor(
            "Signature.mk",
            vec![
                Term::bool(s.constness.is_some()),
                Term::bool(s.asyncness.is_some()),
                Term::bool(s.unsafety.is_some()),
                Term::option(abi),
                ident_term(&s.ident),
                generics,
                Term::List(inputs),
                Term::bool(s.variadic.is_some()),
                Term::option(output),
            ],
        )
    }

    fn fields(&mut self, f: &syn::Fields) -> Term {
        let field = |this: &mut Self, f: &syn::Field| {
            this.cov.hit("Field");
            let attrs = this.attrs(&f.attrs);
            let vis = this.vis(&f.vis);
            let ty = this.ty(&f.ty);
            ctor("Field.mk", vec![attrs, vis, opt_ident(f.ident.as_ref()), ty])
        };
        match f {
            syn::Fields::Named(n) => {
                self.cov.hit("Fields::Named");
                let fs: Vec<Term> = n.named.iter().map(|x| field(self, x)).collect();
                ctor("Fields.named", vec![Term::List(fs)])
            }
            syn::Fields::Unnamed(u) => {
                self.cov.hit("Fields::Unnamed");
                let fs: Vec<Term> = u.unnamed.iter().map(|x| field(self, x)).collect();
                ctor("Fields.unnamed", vec![Term::List(fs)])
            }
            syn::Fields::Unit => {
                self.cov.hit("Fields::Unit");
                Term::atom("Fields.unit")
            }
        }
    }

    fn use_tree(&mut self, t: &syn::UseTree) -> Term {
        match t {
            syn::UseTree::Path(p) => {
                self.cov.hit("UseTree::Path");
                ctor("UseTree.path", vec![ident_term(&p.ident), self.use_tree(&p.tree)])
            }
            syn::UseTree::Name(n) => {
                self.cov.hit("UseTree::Name");
                ctor("UseTree.name", vec![ident_term(&n.ident)])
            }
            syn::UseTree::Rename(r) => {
                self.cov.hit("UseTree::Rename");
                ctor("UseTree.rename", vec![ident_term(&r.ident), ident_term(&r.rename)])
            }
            syn::UseTree::Glob(_) => {
                self.cov.hit("UseTree::Glob");
                Term::atom("UseTree.glob")
            }
            syn::UseTree::Group(g) => {
                self.cov.hit("UseTree::Group");
                let items: Vec<Term> = g.items.iter().map(|x| self.use_tree(x)).collect();
                ctor("UseTree.group", vec![Term::List(items)])
            }
        }
    }

    fn defaultness(d: &Option<syn::Token![default]>) -> Term {
        Term::bool(d.is_some())
    }

    pub fn item(&mut self, item: &syn::Item) -> Term {
        use syn::Item as I;
        match item {
            I::Const(c) => {
                self.cov.hit("Item::Const");
                let attrs = self.attrs(&c.attrs);
                let vis = self.vis(&c.vis);
                let g = self.generics(&c.generics);
                let ty = self.ty(&c.ty);
                let e = self.expr(&c.expr);
                ctor("Item.const", vec![attrs, vis, ident_term(&c.ident), g, ty, e])
            }
            I::Enum(e) => {
                self.cov.hit("Item::Enum");
                let attrs = self.attrs(&e.attrs);
                let vis = self.vis(&e.vis);
                let g = self.generics(&e.generics);
                let variants: Vec<Term> = e
                    .variants
                    .iter()
                    .map(|v| {
                        self.cov.hit("Variant");
                        let attrs = self.attrs(&v.attrs);
                        let fields = self.fields(&v.fields);
                        let disc = Term::option(v.discriminant.as_ref().map(|(_, d)| self.expr(d)));
                        ctor("Variant.mk", vec![attrs, ident_term(&v.ident), fields, disc])
                    })
                    .collect();
                ctor("Item.enum", vec![attrs, vis, ident_term(&e.ident), g, Term::List(variants)])
            }
            I::Fn(f) => {
                self.cov.hit("Item::Fn");
                let attrs = self.attrs(&f.attrs);
                let vis = self.vis(&f.vis);
                let sig = self.signature(&f.sig);
                let b = self.block(&f.block);
                ctor("Item.fn", vec![attrs, vis, sig, b])
            }
            I::Impl(i) => {
                self.cov.hit("Item::Impl");
                let attrs = self.attrs(&i.attrs);
                let g = self.generics(&i.generics);
                let (neg, tp) = match &i.trait_ {
                    None => (false, None),
                    Some((bang, p, _)) => (bang.is_some(), Some(self.path(p))),
                };
                let self_ty = self.ty(&i.self_ty);
                let items: Vec<Term> = i.items.iter().map(|x| self.impl_item(x)).collect();
                ctor(
                    "Item.impl",
                    vec![
                        attrs,
                        Self::defaultness(&i.defaultness),
                        Term::bool(i.unsafety.is_some()),
                        g,
                        Term::bool(neg),
                        Term::option(tp),
                        self_ty,
                        Term::List(items),
                    ],
                )
            }
            I::Macro(m) => {
                self.cov.hit("Item::Macro");
                let attrs = self.attrs(&m.attrs);
                let mac = self.mac(&m.mac);
                ctor("Item.macro", vec![attrs, opt_ident(m.ident.as_ref()), mac])
            }
            I::Struct(s) => {
                self.cov.hit("Item::Struct");
                let attrs = self.attrs(&s.attrs);
                let vis = self.vis(&s.vis);
                let g = self.generics(&s.generics);
                let f = self.fields(&s.fields);
                ctor("Item.struct", vec![attrs, vis, ident_term(&s.ident), g, f])
            }
            I::Trait(t) => {
                self.cov.hit("Item::Trait");
                let attrs = self.attrs(&t.attrs);
                let vis = self.vis(&t.vis);
                let g = self.generics(&t.generics);
                let sup = self.bounds(&t.supertraits);
                let items: Vec<Term> = t.items.iter().map(|x| self.trait_item(x)).collect();
                ctor(
                    "Item.trait",
                    vec![
                        attrs,
                        vis,
                        Term::bool(t.unsafety.is_some()),
                        Term::bool(t.auto_token.is_some()),
                        ident_term(&t.ident),
                        g,
                        sup,
                        Term::List(items),
                    ],
                )
            }
            I::Type(t) => {
                self.cov.hit("Item::Type");
                let attrs = self.attrs(&t.attrs);
                let vis = self.vis(&t.vis);
                let g = self.generics(&t.generics);
                let ty = self.ty(&t.ty);
                ctor("Item.type", vec![attrs, vis, ident_term(&t.ident), g, ty])
            }
            I::Use(u) => {
                self.cov.hit("Item::Use");
                let attrs = self.attrs(&u.attrs);
                let vis = self.vis(&u.vis);
                let tree = self.use_tree(&u.tree);
                ctor("Item.use", vec![attrs, vis, Term::bool(u.leading_colon.is_some()), tree])
            }
            I::Static(s) => {
                self.cov.hit("Item::Static");
                let attrs = self.attrs(&s.attrs);
                let vis = self.vis(&s.vis);
                let m = !matches!(s.mutability, syn::StaticMutability::None);
                let ty = self.ty(&s.ty);
                let e = self.expr(&s.expr);
                ctor("Item.static", vec![attrs, vis, Term::bool(m), ident_term(&s.ident), ty, e])
            }
            I::Mod(m) => {
                self.cov.hit("Item::Mod");
                let attrs = self.attrs(&m.attrs);
                let vis = self.vis(&m.vis);
                let content = Term::option(m.content.as_ref().map(|(_, items)| {
                    let v: Vec<Term> = items.iter().map(|x| self.item(x)).collect();
                    Term::List(v)
                }));
                ctor("Item.mod", vec![attrs, vis, ident_term(&m.ident), content])
            }
            I::Union(u) => {
                self.cov.hit("Item::Union");
                let attrs = self.attrs(&u.attrs);
                let vis = self.vis(&u.vis);
                let g = self.generics(&u.generics);
                let f = self.fields(&syn::Fields::Named(u.fields.clone()));
                ctor("Item.union", vec![attrs, vis, ident_term(&u.ident), g, f])
            }
            other => {
                self.cov.opaque("Item::Other");
                ctor("Item.verbatim", vec![Term::str(&tokens_of(other))])
            }
        }
    }

    fn impl_item(&mut self, i: &syn::ImplItem) -> Term {
        match i {
            syn::ImplItem::Const(c) => {
                self.cov.hit("ImplItem::Const");
                let attrs = self.attrs(&c.attrs);
                let vis = self.vis(&c.vis);
                let g = self.generics(&c.generics);
                let ty = self.ty(&c.ty);
                let e = self.expr(&c.expr);
                ctor(
                    "ImplItem.const",
                    vec![attrs, vis, Self::defaultness(&c.defaultness), ident_term(&c.ident), g, ty, e],
                )
            }
            syn::ImplItem::Fn(f) => {
                self.cov.hit("ImplItem::Fn");
                let attrs = self.attrs(&f.attrs);
                let vis = self.vis(&f.vis);
                let sig = self.signature(&f.sig);
                let b = self.block(&f.block);
                ctor("ImplItem.fn", vec![attrs, vis, Self::defaultness(&f.defaultness), sig, b])
            }
            syn::ImplItem::Type(t) => {
                self.cov.hit("ImplItem::Type");
                let attrs = self.attrs(&t.attrs);
                let vis = self.vis(&t.vis);
                let g = self.generics(&t.generics);
                let ty = self.ty(&t.ty);
                ctor(
                    "ImplItem.type",
                    vec![attrs, vis, Self::defaultness(&t.defaultness), ident_term(&t.ident), g, ty],
                )
            }
            syn::ImplItem::Macro(m) => {
                self.cov.hit("ImplItem::Macro");
                let attrs = self.attrs(&m.attrs);
                let mac = self.mac(&m.mac);
                ctor("ImplItem.macro", vec![attrs, mac])
            }
            other => {
                self.cov.opaque("ImplItem::Other");
                ctor("ImplItem.verbatim", vec![Term::str(&tokens_of(other))])
            }
        }
    }

    fn trait_item(&mut self, i: &syn::TraitItem) -> Term {
        match i {
            syn::TraitItem::Const(c) => {
                self.cov.hit("TraitItem::Const");
                let attrs = self.attrs(&c.attrs);
                let g = self.generics(&c.generics);
                let ty = self.ty(&c.ty);
                let d = Term::option(c.default.as_ref().map(|(_, e)| self.expr(e)));
                ctor("TraitItem.const", vec![attrs, ident_term(&c.ident), g, ty, d])
            }
            syn::TraitItem::Fn(f) => {
                self.cov.hit("TraitItem::Fn");
                let attrs = self.attrs(&f.attrs);
                let sig = self.signature(&f.sig);
                let d = Term::option(f.default.as_ref().map(|b| self.block(b)));
                ctor("TraitItem.fn", vec![attrs, sig, d])
            }
            syn::TraitItem::Type(t) => {
                self.cov.hit("TraitItem::Type");
                let attrs = self.attrs(&t.attrs);
                let g = self.generics(&t.generics);
                let bounds = self.bounds(&t.bounds);
                let d = Term::option(t.default.as_ref().map(|(_, ty)| self.ty(ty)));
                ctor("TraitItem.type", vec![attrs, ident_term(&t.ident), g, bounds, d])
            }
            syn::TraitItem::Macro(m) => {
                self.cov.hit("TraitItem::Macro");
                let attrs = self.attrs(&m.attrs);
                let mac = self.mac(&m.mac);
                ctor("TraitItem.macro", vec![attrs, mac])
            }
            other => {
                self.cov.opaque("TraitItem::Other");
                ctor("TraitItem.verbatim", vec![Term::str(&tokens_of(other))])
            }
        }
    }
}
