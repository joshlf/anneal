//! Procedural macros extending `anodized-core` (`v0.7.0`) for Anneal's MIR
//! contract extraction, external sidecar specifications, type invariants, and
//! `unsafe` trait implementation obligations (`#103` §3.2).
//!
//! `anodized-macros` selects its instrumentation mode at macro-compilation time
//! via `cfg!(anodized_embed_specs)`. Because Cargo compiles procedural macro
//! crates for the host target without forwarding target `RUSTFLAGS`, invoking
//! `anodized::spec` directly does not emit companion specification items unless
//! the host procedural macro crate is also compiled with
//! `--cfg anodized_embed_specs`. The macros in this crate pin
//! `anodized_core::instrument::Mode::EmbedSpecs` so that inline contracts,
//! external sidecar contracts, type invariants, `unsafe` trait contracts, and
//! ghost model markers are unconditionally lowered into the target crate's
//! `Runtime(PostCleanup)` MIR.

use anodized_core::{
    FnSpec,
    annotate::Specified as _,
    instrument::{Mode, SpecEmbedding, make_item_error},
    syntax::SpecFields,
};
use proc_macro::TokenStream;
use proc_macro2::{Delimiter, Spacing, TokenStream as TokenStream2, TokenTree};
use quote::{ToTokens, format_ident, quote};
use syn::{
    Attribute, Block, Error, Expr, ExprPath, FnArg, Ident, ImplItem, Item, ItemFn, ItemImpl,
    ItemTrait, Path, ReturnType, Signature, Stmt, Token, TraitItem, TraitItemFn, Type, Visibility,
    parse::{Parse, ParseStream, Result},
    parse_quote,
    punctuated::Punctuated,
    visit_mut::{self, VisitMut},
};

/// Instrumentation mode that unconditionally embeds synthetic `__anodized_fn_*`
/// companion items into the crate without altering runtime function bodies.
const EMBED_MODE: Mode = Mode::EmbedSpecs(SpecEmbedding {
    uses_charon: false,
});

/// Embeds an `anodized` specification contract as synthetic `__anodized_fn_*`
/// companion items alongside the annotated item.
///
/// For an annotated function `<fn>`, this macro emits:
///
/// - `__anodized_fn_qualifiers_<fn>`: a `u32` bitmask encoding function
///   qualifiers such as `pure`, `total`, and `terminating`.
/// - `__anodized_fn_requires_<fn>`: a boolean function with the same parameters
///   as `<fn>` that evaluates all `requires` and entry `maintains` clauses.
/// - `__anodized_fn_ensures_<fn>`: a boolean function taking `<fn>`'s
///   parameters and `__anodized_output` that evaluates all `captures`, exit
///   `maintains`, and `ensures` clauses.
#[proc_macro_attribute]
pub fn embed_spec(args: TokenStream, input: TokenStream) -> TokenStream {
    match expand_embed_spec(args.into(), input.into()) {
        Ok(tokens) => tokens.into(),
        Err(err) => err.to_compile_error().into(),
    }
}

/// Alias for [`embed_spec`] that embeds `anodized` specification contracts as
/// synthetic `__anodized_fn_*` companion items for MIR extraction.
#[proc_macro_attribute]
pub fn spec(args: TokenStream, input: TokenStream) -> TokenStream {
    match expand_embed_spec(args.into(), input.into()) {
        Ok(tokens) => tokens.into(),
        Err(err) => err.to_compile_error().into(),
    }
}

/// Attaches an external specification (`requires`, `maintains`, `captures`,
/// `ensures`, and qualifiers) to an unowned target function via a sidecar
/// declaration (`#103` §3.2).
///
/// The attribute's first argument must identify the target item using
/// `for = <path>` or `target = <path>`, followed by optional `anodized`
/// specification clauses. The annotated sidecar function may end with either a
/// semicolon (`;`) or a block body (`{ ... }`).
///
/// For a sidecar function `<ident>` targeting `<path>`, this macro emits:
///
/// - `__ANNEAL_EXT_SPEC_TARGET_<ident>`: a hidden `&str` constant recording the
///   canonical target path for `anneal-rustc-capture`.
/// - `__anodized_fn_qualifiers_<ident>`, `__anodized_fn_requires_<ident>`, and
///   `__anodized_fn_ensures_<ident>`: synthetic companion items lowered to MIR.
/// - A compile-time signature check inside `<ident>` verifying that `<path>`
///   has the exact parameter and return types declared on `<ident>`.
#[proc_macro_attribute]
pub fn external_spec(args: TokenStream, input: TokenStream) -> TokenStream {
    match expand_external_spec(args.into(), input.into()) {
        Ok(tokens) => tokens.into(),
        Err(err) => err.to_compile_error().into(),
    }
}

/// Marks a specification helper function, type, or constant as a ghost model
/// item.
///
/// For an annotated item `<ident>`, this macro emits a hidden constant
/// `__ANNEAL_MODEL_<ident>: &str = "<ident>"` alongside the item so that
/// `anneal-rustc-capture` classifies it as `CapturedItemKind::Model`.
#[proc_macro_attribute]
pub fn model(args: TokenStream, input: TokenStream) -> TokenStream {
    match expand_model(args.into(), input.into()) {
        Ok(tokens) => tokens.into(),
        Err(err) => err.to_compile_error().into(),
    }
}

/// Attaches a boolean type invariant to a `struct` or `enum` definition.
///
/// The original `struct` or `enum` definition is preserved intact alongside a
/// companion inherent method `__anneal_type_invariant_<TypeSnake>(&self) -> bool`
/// annotated with `#[doc = "\u{200b}anneal::type_invariant=<TypeName>"]`.
/// Inside the invariant expression, `self` refers to `&Self`.
#[proc_macro_attribute]
pub fn invariant(args: TokenStream, input: TokenStream) -> TokenStream {
    match expand_invariant(args.into(), input.into()) {
        Ok(tokens) => tokens.into(),
        Err(err) => err.to_compile_error().into(),
    }
}

/// Marks an `unsafe trait` (or `trait`) declaration with an Anneal safety
/// contract marker (`#[doc = "\u{200b}anneal::unsafe_trait=<TraitName>"]`) and
/// instruments any nested `#[spec]` or `#[embed_spec]` method contracts.
#[proc_macro_attribute]
pub fn unsafe_trait(args: TokenStream, input: TokenStream) -> TokenStream {
    match expand_unsafe_trait(args.into(), input.into()) {
        Ok(tokens) => tokens.into(),
        Err(err) => err.to_compile_error().into(),
    }
}

/// Attaches a verification obligation and optional `requires`/`ensures`
/// contract to an `unsafe impl Trait for Type` block or a safety witness
/// function.
///
/// For an `unsafe impl <Trait> for <Type>` block, this macro preserves the
/// implementation block and emits a companion witness function
/// `__anneal_unsafe_impl_<Trait>_for_<Type>() -> bool` equipped with
/// `#[doc = "\u{200b}anneal::unsafe_impl=<Trait>::<Type>"]` and any specified
/// `anodized` `requires`/`ensures` companion items so `anneal-rustc-capture`
/// extracts a first-class verification target for the `unsafe impl`.
#[proc_macro_attribute]
pub fn unsafe_impl(args: TokenStream, input: TokenStream) -> TokenStream {
    match expand_unsafe_impl(args.into(), input.into()) {
        Ok(tokens) => tokens.into(),
        Err(err) => err.to_compile_error().into(),
    }
}

fn expand_embed_spec(args: TokenStream2, input: TokenStream2) -> Result<TokenStream2> {
    let spec_fields: SpecFields = syn::parse2(args)?;
    let mut item: Item = syn::parse2(input)?;
    normalize_nested_spec_attrs(&mut item);

    let raw_tokens = match item {
        Item::Fn(mut func) => func
            .parse_spec_from_fields(spec_fields)
            .and_then(|spec| EMBED_MODE.instrument_item_fn(spec, func)),
        Item::Trait(mut the_trait) => the_trait
            .parse_spec_from_fields(spec_fields)
            .and_then(|spec| EMBED_MODE.instrument_item_trait(spec, the_trait)),
        Item::Impl(mut the_impl) if the_impl.trait_.is_some() => the_impl
            .parse_spec_from_fields(spec_fields)
            .and_then(|spec| EMBED_MODE.instrument_item_trait_impl(spec, the_impl)),
        Item::Impl(mut the_impl) => the_impl
            .parse_spec_from_fields(spec_fields)
            .and_then(|spec| EMBED_MODE.instrument_item_impl(spec, the_impl)),
        Item::Enum(mut the_enum) => the_enum
            .parse_spec_from_fields(spec_fields)
            .and_then(|spec| EMBED_MODE.instrument_item_enum(spec, the_enum)),
        Item::Struct(mut the_struct) => the_struct
            .parse_spec_from_fields(spec_fields)
            .and_then(|spec| EMBED_MODE.instrument_item_struct(spec, the_struct)),
        Item::Const(_) => Err(make_item_error(&item, "const")),
        Item::ExternCrate(_) => Err(make_item_error(&item, "extern crate")),
        Item::ForeignMod(_) => Err(make_item_error(&item, "extern block")),
        Item::Macro(_) => Err(make_item_error(&item, "macro")),
        Item::Mod(_) => Err(make_item_error(&item, "mod")),
        Item::Static(_) => Err(make_item_error(&item, "static")),
        Item::TraitAlias(_) => Err(make_item_error(&item, "trait alias")),
        Item::Type(_) => Err(make_item_error(&item, "type")),
        Item::Union(_) => Err(make_item_error(&item, "union")),
        Item::Use(_) => Err(make_item_error(&item, "use")),
        Item::Verbatim(ref tokens) => {
            if let Ok(trait_fn) = syn::parse2::<TraitItemFn>(tokens.clone()) {
                Err(Error::new_spanned(
                    &trait_fn,
                    "The enclosing trait must have a `#[spec]` or `#[embed_spec]` annotation.",
                ))
            } else {
                Err(make_item_error(&item, "<unexpected>"))
            }
        }
        _ => Err(make_item_error(&item, "<unknown>")),
    }?;

    rewrite_anodized_root_paths(raw_tokens)
}

/// Parsed arguments to `#[external_spec(for = <path>, ...)]`.
struct ExternalSpecArgs {
    target_path: ExprPath,
    target_path_str: String,
    spec_fields: SpecFields,
}

impl Parse for ExternalSpecArgs {
    fn parse(input: ParseStream<'_>) -> Result<Self> {
        if input.peek(Token![for]) {
            input.parse::<Token![for]>()?;
        } else if input.peek(Ident) {
            let key: Ident = input.parse()?;
            if key != "target" {
                return Err(Error::new_spanned(
                    key,
                    "expected `for = <path>` or `target = <path>` as the first argument to `#[external_spec]`",
                ));
            }
        } else {
            return Err(input.error(
                "expected `for = <path>` or `target = <path>` as the first argument to `#[external_spec]`",
            ));
        }

        if input.peek(Token![=]) {
            input.parse::<Token![=]>()?;
        } else if input.peek(Token![:]) {
            input.parse::<Token![:]>()?;
        } else {
            return Err(input.error("expected `=` after `for` or `target` in `#[external_spec]`"));
        }

        let target_path: ExprPath = input.parse()?;
        let target_path_str = compact_path_string(target_path.to_token_stream());

        let spec_fields = if input.is_empty() {
            SpecFields {
                fields: Punctuated::new(),
            }
        } else {
            input.parse::<Token![,]>()?;
            input.parse::<SpecFields>()?
        };

        Ok(Self {
            target_path,
            target_path_str,
            spec_fields,
        })
    }
}

/// Sidecar function item that accepts either a block body or a terminating
/// semicolon.
struct SidecarFn {
    attrs: Vec<Attribute>,
    vis: Visibility,
    sig: Signature,
    body: Option<Block>,
}

impl Parse for SidecarFn {
    fn parse(input: ParseStream<'_>) -> Result<Self> {
        let attrs = input.call(Attribute::parse_outer)?;
        let vis: Visibility = input.parse()?;
        let sig: Signature = input.parse()?;

        let body = if input.peek(Token![;]) {
            input.parse::<Token![;]>()?;
            None
        } else {
            Some(input.parse::<Block>()?)
        };

        Ok(Self {
            attrs,
            vis,
            sig,
            body,
        })
    }
}

fn expand_external_spec(args: TokenStream2, input: TokenStream2) -> Result<TokenStream2> {
    let ext_args: ExternalSpecArgs = syn::parse2(args)?;
    let sidecar: SidecarFn = syn::parse2(input)?;

    for arg in &sidecar.sig.inputs {
        if let FnArg::Receiver(receiver) = arg {
            return Err(Error::new_spanned(
                receiver,
                "`#[external_spec]` sidecar functions cannot use a `self` receiver; declare the receiver as an explicit typed parameter (for example, `this: &TargetType`)",
            ));
        }
    }

    let mut fallback_body: Block = match sidecar.body {
        Some(block) => block,
        None => parse_quote!({
            ::core::unimplemented!(
                "`#[external_spec]` sidecar functions exist only for verification and cannot be called at runtime"
            )
        }),
    };
    NormalizeEmbedSpecVisitor.visit_block_mut(&mut fallback_body);

    let mut item_fn = ItemFn {
        attrs: sidecar.attrs,
        vis: sidecar.vis,
        sig: sidecar.sig,
        block: Box::new(fallback_body),
    };

    // Parse the `anodized` specification fields against the sidecar signature
    // first so any `Spec!(T)` refinement markers are stripped from parameter
    // and return types before constructing the signature check.
    let spec = FnSpec::from_spec_and_signature(ext_args.spec_fields, &mut item_fn.sig)?;

    let sig_check_stmt = build_signature_check_stmt(&item_fn.sig, &ext_args.target_path)?;
    item_fn.block.stmts.insert(0, sig_check_stmt);

    item_fn.attrs.push(parse_quote!(#[doc(hidden)]));
    item_fn.attrs.push(
        parse_quote!(#[allow(warnings, dead_code, unused_variables, unreachable_code, non_snake_case)]),
    );

    let marker_ident = format_ident!("__ANNEAL_EXT_SPEC_TARGET_{}", item_fn.sig.ident);
    let target_str = &ext_args.target_path_str;

    let instrumented_fn = EMBED_MODE.instrument_item_fn(spec, item_fn)?;
    let instrumented_fn = rewrite_anodized_root_paths(instrumented_fn)?;

    Ok(quote! {
        #[doc(hidden)]
        #[allow(non_upper_case_globals, dead_code)]
        pub const #marker_ident: &str = #target_str;

        #instrumented_fn
    })
}

/// Builds a compile-time statement verifying that `target_path` has the exact
/// function signature declared in `sig`.
fn build_signature_check_stmt(sig: &Signature, target_path: &ExprPath) -> Result<Stmt> {
    let mut input_tys = Vec::with_capacity(sig.inputs.len());
    for arg in &sig.inputs {
        if let FnArg::Typed(pat_type) = arg {
            input_tys.push((*pat_type.ty).clone());
        }
    }

    let uses_impl_trait = input_tys.iter().any(type_contains_impl_trait)
        || match &sig.output {
            ReturnType::Default => false,
            ReturnType::Type(_, ty) => type_contains_impl_trait(ty),
        };

    let unsafety = &sig.unsafety;
    let abi = &sig.abi;
    let output = &sig.output;

    if !uses_impl_trait {
        Ok(parse_quote! {
            let _: #unsafety #abi fn(#(#input_tys),*) #output = #target_path;
        })
    } else {
        // Function pointer types cannot mention `impl Trait`, so fall back to a
        // dead-branch call that forces `rustc` to unify the argument and return
        // types against `target_path`.
        let fake_args = input_tys.iter().map(|ty| -> syn::Expr {
            parse_quote!(::core::todo!() as #ty)
        });
        let call_expr: syn::Expr = if unsafety.is_some() {
            parse_quote!(unsafe { #target_path(#(#fake_args),*) })
        } else {
            parse_quote!(#target_path(#(#fake_args),*))
        };
        Ok(parse_quote! {
            if false {
                return #call_expr;
            }
        })
    }
}

fn expand_model(args: TokenStream2, input: TokenStream2) -> Result<TokenStream2> {
    if !args.is_empty() {
        return Err(Error::new_spanned(
            args,
            "`#[model]` does not take any arguments",
        ));
    }

    let item: Item = syn::parse2(input)?;
    let ident = match &item {
        Item::Fn(item_fn) => &item_fn.sig.ident,
        Item::Struct(item_struct) => &item_struct.ident,
        Item::Enum(item_enum) => &item_enum.ident,
        Item::Type(item_type) => &item_type.ident,
        Item::Const(item_const) => &item_const.ident,
        _ => {
            return Err(Error::new_spanned(
                &item,
                "`#[model]` may only be applied to a `fn`, `struct`, `enum`, `type`, or `const` item",
            ));
        }
    };

    let marker_ident = format_ident!("__ANNEAL_MODEL_{ident}");
    let ident_str = ident.to_string();

    Ok(quote! {
        #[doc(hidden)]
        #[allow(non_upper_case_globals, dead_code)]
        pub const #marker_ident: &str = #ident_str;

        #item
    })
}

fn expand_invariant(args: TokenStream2, input: TokenStream2) -> Result<TokenStream2> {
    let item: Item = syn::parse2(input)?;
    let (type_ident, generics) = match &item {
        Item::Struct(item_struct) => (&item_struct.ident, &item_struct.generics),
        Item::Enum(item_enum) => (&item_enum.ident, &item_enum.generics),
        _ => {
            return Err(Error::new_spanned(
                &item,
                "`#[invariant]` may only be applied to a `struct` or `enum` definition",
            ));
        }
    };

    if args.is_empty() {
        return Err(Error::new_spanned(
            &item,
            "`#[invariant]` requires a boolean invariant expression (for example, `#[invariant(self.0 > 0)]`)",
        ));
    }

    let invariant_expr = parse_conjoined_bool_exprs(args)?;
    let type_name = type_ident.to_string();
    let type_snake = to_snake_case(&type_name);
    let fn_ident = format_ident!("__anneal_type_invariant_{type_snake}");
    let doc_marker = format!("\u{200b}anneal::type_invariant={type_name}");
    let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

    Ok(quote! {
        #item

        #[automatically_derived]
        impl #impl_generics #type_ident #ty_generics #where_clause {
            #[doc(hidden)]
            #[doc = #doc_marker]
            #[allow(warnings, dead_code, unused_variables, non_snake_case)]
            pub fn #fn_ident(&self) -> bool {
                #invariant_expr
            }
        }
    })
}

fn expand_unsafe_trait(args: TokenStream2, input: TokenStream2) -> Result<TokenStream2> {
    let mut item: Item = syn::parse2(input)?;
    normalize_nested_spec_attrs(&mut item);

    let Item::Trait(mut the_trait) = item else {
        return Err(Error::new_spanned(
            &item,
            "`#[unsafe_trait]` may only be applied to a `trait` definition",
        ));
    };

    let trait_name = the_trait.ident.to_string();
    let doc_marker = format!("\u{200b}anneal::unsafe_trait={trait_name}");
    the_trait.attrs.push(parse_quote!(#[doc = #doc_marker]));

    let has_nested_specs = the_trait.items.iter().any(|trait_item| {
        if let TraitItem::Fn(func) = trait_item {
            func.attrs.iter().any(|attr| {
                attr.path()
                    .segments
                    .last()
                    .is_some_and(|seg| seg.ident == "spec")
            })
        } else {
            false
        }
    });

    if args.is_empty() {
        if has_nested_specs {
            let empty_fields = SpecFields {
                fields: Punctuated::new(),
            };
            let instrumented = the_trait
                .parse_spec_from_fields(empty_fields)
                .and_then(|spec| EMBED_MODE.instrument_item_trait(spec, the_trait))?;
            return rewrite_anodized_root_paths(instrumented);
        }
        return Ok(the_trait.into_token_stream());
    }

    if let Ok(spec_fields) = syn::parse2::<SpecFields>(normalize_ensures_closures(args.clone())) {
        if let Ok(spec) = the_trait.parse_spec_from_fields(spec_fields) {
            let instrumented = EMBED_MODE.instrument_item_trait(spec, the_trait)?;
            return rewrite_anodized_root_paths(instrumented);
        }
    }

    let _ = parse_conjoined_bool_exprs(args)?;
    if has_nested_specs {
        let empty_fields = SpecFields {
            fields: Punctuated::new(),
        };
        let instrumented = the_trait
            .parse_spec_from_fields(empty_fields)
            .and_then(|spec| EMBED_MODE.instrument_item_trait(spec, the_trait))?;
        return rewrite_anodized_root_paths(instrumented);
    }

    Ok(the_trait.into_token_stream())
}

fn expand_unsafe_impl(args: TokenStream2, input: TokenStream2) -> Result<TokenStream2> {
    let mut item: Item = syn::parse2(input)?;
    normalize_nested_spec_attrs(&mut item);

    match item {
        Item::Impl(mut the_impl) => expand_unsafe_impl_block(args, &mut the_impl),
        Item::Fn(item_fn) => expand_unsafe_impl_witness_fn(args, item_fn),
        other => Err(Error::new_spanned(
            other,
            "`#[unsafe_impl]` may only be applied to an `unsafe impl Trait for Type` block or a safety witness `fn`",
        )),
    }
}

fn expand_unsafe_impl_block(args: TokenStream2, the_impl: &mut ItemImpl) -> Result<TokenStream2> {
    let Some((_, ref trait_path, _)) = the_impl.trait_ else {
        return Err(Error::new_spanned(
            &*the_impl,
            "`#[unsafe_impl]` on an `impl` block requires a trait implementation (`unsafe impl Trait for Type`)",
        ));
    };

    let trait_name = trait_path
        .segments
        .last()
        .map(|seg| seg.ident.to_string())
        .ok_or_else(|| Error::new_spanned(trait_path, "expected non-empty trait path"))?;
    let type_name = extract_type_ident_name(&the_impl.self_ty);

    let witness_ident = format_ident!("__anneal_unsafe_impl_{trait_name}_for_{type_name}");
    let doc_marker = format!("\u{200b}anneal::unsafe_impl={trait_name}::{type_name}");

    let witness_tokens = build_unsafe_impl_witness_tokens(args, &witness_ident, &doc_marker)?;

    let has_nested_specs = the_impl.items.iter().any(|impl_item| {
        if let ImplItem::Fn(func) = impl_item {
            func.attrs.iter().any(|attr| {
                attr.path()
                    .segments
                    .last()
                    .is_some_and(|seg| seg.ident == "spec")
            })
        } else {
            false
        }
    });

    let impl_tokens = if has_nested_specs {
        let empty_fields = SpecFields {
            fields: Punctuated::new(),
        };
        let mut cloned_impl = the_impl.clone();
        let instrumented = cloned_impl
            .parse_spec_from_fields(empty_fields)
            .and_then(|spec| EMBED_MODE.instrument_item_trait_impl(spec, cloned_impl))?;
        rewrite_anodized_root_paths(instrumented)?
    } else {
        the_impl.to_token_stream()
    };

    Ok(quote! {
        #impl_tokens

        #witness_tokens
    })
}

fn build_unsafe_impl_witness_tokens(
    args: TokenStream2,
    witness_ident: &Ident,
    doc_marker: &str,
) -> Result<TokenStream2> {
    if args.is_empty() {
        return Ok(quote! {
            #[doc(hidden)]
            #[doc = #doc_marker]
            #[allow(warnings, dead_code, unused_variables, non_snake_case)]
            pub fn #witness_ident() -> bool {
                true
            }
        });
    }

    let normalized_args = normalize_ensures_closures(args.clone());
    if looks_like_spec_fields(&normalized_args)
        && let Ok(spec_fields) = syn::parse2::<SpecFields>(normalized_args)
    {
        let mut witness_fn: ItemFn = parse_quote! {
            #[doc(hidden)]
            #[doc = #doc_marker]
            #[allow(warnings, dead_code, unused_variables, non_snake_case)]
            pub fn #witness_ident() -> bool {
                true
            }
        };
        let spec = FnSpec::from_spec_and_signature(spec_fields, &mut witness_fn.sig)?;
        let instrumented = EMBED_MODE.instrument_item_fn(spec, witness_fn)?;
        return rewrite_anodized_root_paths(instrumented);
    }

    let body_expr = parse_conjoined_bool_exprs(args)?;
    Ok(quote! {
        #[doc(hidden)]
        #[doc = #doc_marker]
        #[allow(warnings, dead_code, unused_variables, non_snake_case)]
        pub fn #witness_ident() -> bool {
            #body_expr
        }
    })
}

/// Optional target header (`for = Trait::Type` or `trait = Trait, for = Type`)
/// when `#[unsafe_impl(...)]` is applied directly to a safety witness function.
struct WitnessFnArgs {
    trait_and_type: Option<(String, String)>,
    remaining: TokenStream2,
}

impl Parse for WitnessFnArgs {
    fn parse(input: ParseStream<'_>) -> Result<Self> {
        if input.is_empty() {
            return Ok(Self {
                trait_and_type: None,
                remaining: TokenStream2::new(),
            });
        }

        let fork = input.fork();
        if fork.peek(Token![trait]) {
            let _ = input.parse::<Token![trait]>()?;
            if input.peek(Token![=]) {
                input.parse::<Token![=]>()?;
            } else {
                input.parse::<Token![:]>()?;
            }
            let trait_path: Path = input.parse()?;
            input.parse::<Token![,]>()?;
            if input.peek(Token![for]) {
                input.parse::<Token![for]>()?;
            } else {
                let kw: Ident = input.parse()?;
                if kw != "for_type" && kw != "type" && kw != "target" {
                    return Err(Error::new_spanned(
                        kw,
                        "expected `for = <Type>` after `trait = <Trait>,` in `#[unsafe_impl]`",
                    ));
                }
            }
            if input.peek(Token![=]) {
                input.parse::<Token![=]>()?;
            } else {
                input.parse::<Token![:]>()?;
            }
            let self_ty: Type = input.parse()?;
            if input.peek(Token![,]) {
                input.parse::<Token![,]>()?;
            }
            let trait_name = trait_path
                .segments
                .last()
                .map(|s| s.ident.to_string())
                .unwrap_or_else(|| compact_path_string(trait_path.to_token_stream()));
            let type_name = extract_type_ident_name(&self_ty);
            let remaining: TokenStream2 = input.parse()?;
            return Ok(Self {
                trait_and_type: Some((trait_name, type_name)),
                remaining,
            });
        }

        if fork.peek(Token![for])
            || (fork.peek(Ident) && {
                let id: Ident = fork.parse()?;
                id == "target"
            })
        {
            if input.peek(Token![for]) {
                input.parse::<Token![for]>()?;
            } else {
                input.parse::<Ident>()?;
            }
            if input.peek(Token![=]) {
                input.parse::<Token![=]>()?;
            } else {
                input.parse::<Token![:]>()?;
            }
            let path: Path = input.parse()?;
            if input.peek(Token![,]) {
                input.parse::<Token![,]>()?;
            }
            let segments: Vec<String> = path
                .segments
                .iter()
                .map(|s| s.ident.to_string())
                .collect();
            let pair = if segments.len() >= 2 {
                let ty = segments.last().cloned().unwrap_or_default();
                let tr = segments[segments.len() - 2].clone();
                Some((tr, ty))
            } else {
                None
            };
            let remaining: TokenStream2 = input.parse()?;
            return Ok(Self {
                trait_and_type: pair,
                remaining,
            });
        }

        let remaining: TokenStream2 = input.parse()?;
        Ok(Self {
            trait_and_type: None,
            remaining,
        })
    }
}

fn expand_unsafe_impl_witness_fn(args: TokenStream2, mut item_fn: ItemFn) -> Result<TokenStream2> {
    let parsed_args: WitnessFnArgs = syn::parse2(args)?;
    let fn_name = item_fn.sig.ident.to_string();

    let (trait_name, type_name) = if let Some(pair) = parsed_args.trait_and_type {
        pair
    } else if let Some(rest) = fn_name.strip_prefix("__anneal_unsafe_impl_")
        && let Some((tr, ty)) = rest.split_once("_for_")
        && !tr.is_empty()
        && !ty.is_empty()
    {
        (tr.to_owned(), ty.to_owned())
    } else {
        ("UnsafeTrait".to_owned(), fn_name.clone())
    };

    let doc_marker = format!("\u{200b}anneal::unsafe_impl={trait_name}::{type_name}");
    item_fn.attrs.push(parse_quote!(#[doc = #doc_marker]));

    if parsed_args.remaining.is_empty() {
        return Ok(item_fn.into_token_stream());
    }

    let normalized_rem = normalize_ensures_closures(parsed_args.remaining.clone());
    if looks_like_spec_fields(&normalized_rem) {
        let spec_fields: SpecFields = syn::parse2(normalized_rem)?;
        let spec = FnSpec::from_spec_and_signature(spec_fields, &mut item_fn.sig)?;
        let instrumented = EMBED_MODE.instrument_item_fn(spec, item_fn)?;
        return rewrite_anodized_root_paths(instrumented);
    }

    let extra_expr = parse_conjoined_bool_exprs(parsed_args.remaining)?;
    let orig_block = &item_fn.block;
    item_fn.block = Box::new(parse_quote!({
        (#orig_block) && (#extra_expr)
    }));
    Ok(item_fn.into_token_stream())
}

/// Parses one or more boolean invariant expressions (either `[e1, e2]` or
/// `e1, e2`, optionally preceded by `invariant:` or `requires:`) and conjoins
/// them with `&&`.
fn parse_conjoined_bool_exprs(tokens: TokenStream2) -> Result<Expr> {
    struct ExprList(Vec<Expr>);

    impl Parse for ExprList {
        fn parse(input: ParseStream<'_>) -> Result<Self> {
            let fork = input.fork();
            if fork.peek(Ident) {
                let kw: Ident = fork.parse()?;
                if (kw == "invariant" || kw == "requires") && fork.peek(Token![:]) {
                    let _ = input.parse::<Ident>()?;
                    let _ = input.parse::<Token![:]>()?;
                }
            }

            if input.peek(syn::token::Bracket) {
                let content;
                syn::bracketed!(content in input);
                let elems: Punctuated<Expr, Token![,]> =
                    content.parse_terminated(Expr::parse, Token![,])?;
                if !input.is_empty() {
                    let _ = input.parse::<Option<Token![,]>>()?;
                }
                return Ok(Self(elems.into_iter().collect()));
            }

            let elems: Punctuated<Expr, Token![,]> =
                input.parse_terminated(Expr::parse, Token![,])?;
            Ok(Self(elems.into_iter().collect()))
        }
    }

    let list: ExprList = syn::parse2(tokens)?;
    let mut iter = list.0.into_iter();
    let Some(first) = iter.next() else {
        return Ok(parse_quote!(true));
    };
    let combined = iter.fold(first, |acc, next| parse_quote!((#acc) && (#next)));
    Ok(combined)
}

/// Returns true if `tokens` begins with an `anodized` specification keyword
/// (`requires`, `ensures`, `maintains`, `captures`, `pure`, `total`,
/// `terminating`, or `decreases`).
fn looks_like_spec_fields(tokens: &TokenStream2) -> bool {
    let mut iter = tokens.clone().into_iter();
    let Some(TokenTree::Ident(first)) = iter.next() else {
        return false;
    };
    let kw = first.to_string();
    matches!(
        kw.as_str(),
        "requires"
            | "ensures"
            | "maintains"
            | "captures"
            | "pure"
            | "total"
            | "terminating"
            | "decreases"
    )
}

/// Normalizes bare `ensures: <expr>` clauses (where `<expr>` is not already a
/// closure `|...| ...`) into `ensures: |__anneal_ret| (<expr>)` so that
/// `anodized` accepts both closure and boolean-expression postconditions on
/// `-> bool` witness functions.
fn normalize_ensures_closures(tokens: TokenStream2) -> TokenStream2 {
    struct RawClauseList {
        clauses: Vec<TokenStream2>,
    }

    impl Parse for RawClauseList {
        fn parse(input: ParseStream<'_>) -> Result<Self> {
            let mut clauses = Vec::new();
            while !input.is_empty() {
                let fork = input.fork();
                if fork.peek(Ident) {
                    let kw: Ident = fork.parse()?;
                    if kw == "ensures" && fork.peek(Token![:]) {
                        let ens_ident: Ident = input.parse()?;
                        let colon: Token![:] = input.parse()?;
                        if input.peek(syn::token::Bracket) {
                            let content;
                            syn::bracketed!(content in input);
                            let exprs: Punctuated<Expr, Token![,]> =
                                content.parse_terminated(Expr::parse, Token![,])?;
                            let wrapped: Vec<Expr> = exprs
                                .into_iter()
                                .map(|e| match e {
                                    Expr::Closure(_) => e,
                                    other => parse_quote!(|__anneal_ret: bool| (#other)),
                                })
                                .collect();
                            clauses.push(quote!(#ens_ident #colon [ #(#wrapped),* ]));
                        } else {
                            let expr: Expr = input.parse()?;
                            let wrapped: Expr = match expr {
                                Expr::Closure(_) => expr,
                                other => parse_quote!(|__anneal_ret: bool| (#other)),
                            };
                            clauses.push(quote!(#ens_ident #colon #wrapped));
                        }
                        if input.peek(Token![,]) {
                            let comma: Token![,] = input.parse()?;
                            clauses.push(comma.into_token_stream());
                        }
                        continue;
                    }
                }

                // Consume tokens up to the next top-level comma.
                let mut chunk = TokenStream2::new();
                while !input.is_empty() && !input.peek(Token![,]) {
                    let tt: TokenTree = input.parse()?;
                    chunk.extend(std::iter::once(tt));
                }
                if input.peek(Token![,]) {
                    let comma: Token![,] = input.parse()?;
                    chunk.extend(comma.into_token_stream());
                }
                clauses.push(chunk);
            }
            Ok(Self { clauses })
        }
    }

    match syn::parse2::<RawClauseList>(tokens.clone()) {
        Ok(parsed) => parsed.clauses.into_iter().collect(),
        Err(_) => tokens,
    }
}

/// Converts a `PascalCase` or `camelCase` identifier into `snake_case`
/// (`NonZeroU32` -> `non_zero_u32`, `PositivePair` -> `positive_pair`).
fn to_snake_case(input: &str) -> String {
    let chars: Vec<char> = input.chars().collect();
    let mut out = String::with_capacity(input.len() + 4);
    for (i, &ch) in chars.iter().enumerate() {
        if ch.is_ascii_uppercase() {
            if i > 0 {
                let prev = chars[i - 1];
                let next_is_lower = chars.get(i + 1).is_some_and(|c| c.is_ascii_lowercase());
                if prev != '_'
                    && (prev.is_ascii_lowercase()
                        || prev.is_ascii_digit()
                        || (prev.is_ascii_uppercase() && next_is_lower))
                {
                    out.push('_');
                }
            }
            out.push(ch.to_ascii_lowercase());
        } else {
            out.push(ch);
        }
    }
    out
}

/// Extracts a clean identifier segment from `ty` suitable for constructing
/// `__anneal_unsafe_impl_<Trait>_for_<Type>` and `anneal::unsafe_impl=<Trait>::<Type>`.
fn extract_type_ident_name(ty: &Type) -> String {
    match ty {
        Type::Path(type_path) => type_path
            .path
            .segments
            .last()
            .map(|seg| seg.ident.to_string())
            .unwrap_or_else(|| sanitize_ident_chars(&compact_path_string(ty.to_token_stream()))),
        Type::Group(group) => extract_type_ident_name(&group.elem),
        Type::Paren(paren) => extract_type_ident_name(&paren.elem),
        _ => sanitize_ident_chars(&compact_path_string(ty.to_token_stream())),
    }
}

fn sanitize_ident_chars(raw: &str) -> String {
    let mut out = String::with_capacity(raw.len());
    for ch in raw.chars() {
        if ch.is_ascii_alphanumeric() || ch == '_' {
            out.push(ch);
        } else {
            out.push('_');
        }
    }
    let trimmed = out.trim_matches('_');
    if trimmed.is_empty() {
        "SelfType".to_owned()
    } else {
        trimmed.to_owned()
    }
}

/// Rewrites nested `#[embed_spec(...)]` or qualified
/// `#[anneal_spec::spec(...)]` attributes inside `impl`, `trait`, and loop
/// blocks to `#[spec(...)]` so that `anodized-core`'s
/// `Specified::parse_spec_from_attrs` recognizes them.
fn normalize_nested_spec_attrs(item: &mut Item) {
    match item {
        Item::Fn(func) => NormalizeEmbedSpecVisitor.visit_block_mut(&mut func.block),
        Item::Impl(the_impl) => NormalizeEmbedSpecVisitor.visit_item_impl_mut(the_impl),
        Item::Trait(the_trait) => NormalizeEmbedSpecVisitor.visit_item_trait_mut(the_trait),
        _ => {}
    }
}

struct NormalizeEmbedSpecVisitor;

impl NormalizeEmbedSpecVisitor {
    fn normalize_attrs(attrs: &mut [Attribute]) {
        for attr in attrs {
            let is_spec_alias = match attr.path().segments.last() {
                Some(seg) => {
                    seg.ident == "embed_spec"
                        || (seg.ident == "spec" && attr.path().segments.len() > 1)
                }
                None => false,
            };
            if is_spec_alias {
                let span = attr.path().ident_span().unwrap_or_else(proc_macro2::Span::call_site);
                let spec_path: Path = syn::Ident::new("spec", span).into();
                match &mut attr.meta {
                    syn::Meta::Path(_) => attr.meta = syn::Meta::Path(spec_path),
                    syn::Meta::List(list) => list.path = spec_path,
                    syn::Meta::NameValue(nv) => nv.path = spec_path,
                }
            }
        }
    }
}

trait PathIdentSpan {
    fn ident_span(&self) -> Option<proc_macro2::Span>;
}

impl PathIdentSpan for Path {
    fn ident_span(&self) -> Option<proc_macro2::Span> {
        self.segments.last().map(|seg| seg.ident.span())
    }
}

impl VisitMut for NormalizeEmbedSpecVisitor {
    fn visit_item_impl_mut(&mut self, node: &mut ItemImpl) {
        for item in &mut node.items {
            if let ImplItem::Fn(func) = item {
                Self::normalize_attrs(&mut func.attrs);
                self.visit_block_mut(&mut func.block);
            }
        }
    }

    fn visit_item_trait_mut(&mut self, node: &mut ItemTrait) {
        for item in &mut node.items {
            if let TraitItem::Fn(func) = item {
                Self::normalize_attrs(&mut func.attrs);
                if let Some(body) = &mut func.default {
                    self.visit_block_mut(body);
                }
            }
        }
    }

    fn visit_expr_while_mut(&mut self, node: &mut syn::ExprWhile) {
        Self::normalize_attrs(&mut node.attrs);
        visit_mut::visit_expr_while_mut(self, node);
    }

    fn visit_expr_for_loop_mut(&mut self, node: &mut syn::ExprForLoop) {
        Self::normalize_attrs(&mut node.attrs);
        visit_mut::visit_expr_for_loop_mut(self, node);
    }

    fn visit_item_fn_mut(&mut self, _node: &mut ItemFn) {
        // Nested free functions are expanded independently by the compiler.
    }
}

/// Strips the leading `::` from `::anodized::...` paths emitted by
/// `anodized-core`.
///
/// In Rust 2018 and later editions, a leading `::` restricts path resolution to
/// the extern prelude, which fails when a crate imports `anodized` via
/// `use anneal_spec::*;` rather than declaring a direct `anodized` dependency
/// in `Cargo.toml`. Removing the leading `::` allows `anodized::__::eval` to
/// resolve through either `use anneal_spec::*;` or the extern prelude.
fn rewrite_anodized_root_paths(tokens: TokenStream2) -> Result<TokenStream2> {
    if let Ok(mut file) = syn::parse2::<syn::File>(tokens.clone()) {
        AnodizedPathVisitor.visit_file_mut(&mut file);
        return Ok(file.into_token_stream());
    }
    if let Ok(mut item_impl) = syn::parse2::<ItemImpl>(tokens.clone()) {
        AnodizedPathVisitor.visit_item_impl_mut(&mut item_impl);
        return Ok(item_impl.into_token_stream());
    }
    if let Ok(mut item_trait) = syn::parse2::<ItemTrait>(tokens.clone()) {
        AnodizedPathVisitor.visit_item_trait_mut(&mut item_trait);
        return Ok(item_trait.into_token_stream());
    }
    Ok(tokens)
}

struct AnodizedPathVisitor;

impl VisitMut for AnodizedPathVisitor {
    fn visit_path_mut(&mut self, path: &mut Path) {
        if path.leading_colon.is_some()
            && path
                .segments
                .first()
                .is_some_and(|seg| seg.ident == "anodized")
        {
            path.leading_colon = None;
        }
        visit_mut::visit_path_mut(self, path);
    }
}

/// Detects whether a type syntactically contains `impl Trait`.
fn type_contains_impl_trait(ty: &Type) -> bool {
    struct ImplTraitFinder(bool);

    impl VisitMut for ImplTraitFinder {
        fn visit_type_mut(&mut self, ty: &mut Type) {
            if matches!(ty, Type::ImplTrait(_)) {
                self.0 = true;
            } else {
                visit_mut::visit_type_mut(self, ty);
            }
        }
    }

    let mut cloned = ty.clone();
    let mut finder = ImplTraitFinder(false);
    finder.visit_type_mut(&mut cloned);
    finder.0
}

/// Formats a path token stream without inserting spaces around `::` or angle
/// brackets.
fn compact_path_string(tokens: TokenStream2) -> String {
    let mut out = String::new();
    let mut prev_was_ident = false;

    for tt in tokens {
        match tt {
            TokenTree::Ident(ident) => {
                if prev_was_ident {
                    out.push(' ');
                }
                out.push_str(&ident.to_string());
                prev_was_ident = true;
            }
            TokenTree::Punct(punct) => {
                out.push(punct.as_char());
                if punct.as_char() == ',' && punct.spacing() == Spacing::Alone {
                    out.push(' ');
                }
                prev_was_ident = false;
            }
            TokenTree::Group(group) => {
                let (open, close) = match group.delimiter() {
                    Delimiter::Parenthesis => ("(", ")"),
                    Delimiter::Brace => ("{", "}"),
                    Delimiter::Bracket => ("[", "]"),
                    Delimiter::None => ("", ""),
                };
                out.push_str(open);
                out.push_str(&compact_path_string(group.stream()));
                out.push_str(close);
                prev_was_ident = false;
            }
            TokenTree::Literal(lit) => {
                if prev_was_ident {
                    out.push(' ');
                }
                out.push_str(&lit.to_string());
                prev_was_ident = false;
            }
        }
    }

    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn embed_spec_emits_companion_items_and_strips_leading_colon() {
        let args = quote! {
            pure,
            total,
            requires: x < 100,
            maintains: x > 0,
            captures: old_x = x,
            ensures: |ret| ret == old_x + 1,
        };
        let input = quote! {
            pub fn increment(x: u32) -> u32 {
                x + 1
            }
        };

        let expanded = expand_embed_spec(args, input)
            .expect("expand_embed_spec should succeed")
            .to_string();

        assert!(expanded.contains("__anodized_fn_qualifiers_increment"));
        assert!(expanded.contains("__anodized_fn_requires_increment"));
        assert!(expanded.contains("__anodized_fn_ensures_increment"));
        assert!(!expanded.contains(":: anodized ::"));
        assert!(expanded.contains("anodized :: __ :: eval"));
    }

    #[test]
    fn external_spec_emits_target_marker_sig_check_and_companions() {
        let args = quote! {
            for = core::num::Wrapping,
            requires: x < 100,
            ensures: |ret| ret.0 == x,
        };
        let input = quote! {
            fn spec_wrapping(x: u32) -> core::num::Wrapping<u32>;
        };

        let expanded = expand_external_spec(args, input)
            .expect("expand_external_spec should succeed")
            .to_string();

        assert!(expanded.contains("__ANNEAL_EXT_SPEC_TARGET_spec_wrapping"));
        assert!(expanded.contains("\"core::num::Wrapping\""));
        assert!(expanded.contains("__anodized_fn_qualifiers_spec_wrapping"));
        assert!(expanded.contains("__anodized_fn_requires_spec_wrapping"));
        assert!(expanded.contains("__anodized_fn_ensures_spec_wrapping"));
    }

    #[test]
    fn external_spec_rejects_missing_target_argument() {
        let args = quote! {
            requires: x > 0,
        };
        let input = quote! {
            fn bad_sidecar(x: u32) -> u32;
        };

        let err = expand_external_spec(args, input).expect_err("missing target should fail");
        assert!(
            err.to_string()
                .contains("expected `for = <path>` or `target = <path>`")
        );
    }

    #[test]
    fn model_emits_marker_const_and_rejects_arguments() {
        let input = quote! {
            pub fn ghost_sum(a: u64, b: u64) -> u128 {
                (a as u128) + (b as u128)
            }
        };

        let expanded = expand_model(TokenStream2::new(), input.clone())
            .expect("expand_model should succeed")
            .to_string();
        assert!(expanded.contains("__ANNEAL_MODEL_ghost_sum"));
        assert!(expanded.contains("\"ghost_sum\""));

        let err = expand_model(quote!(unexpected), input)
            .expect_err("non-empty model args should fail");
        assert!(err.to_string().contains("does not take any arguments"));
    }

    #[test]
    fn invariant_emits_companion_method_with_doc_marker() {
        let args = quote! {
            self.0 > 0,
            self.0 <= 1_000
        };
        let input = quote! {
            pub struct NonZeroBounded(pub u32);
        };

        let expanded = expand_invariant(args, input)
            .expect("expand_invariant should succeed")
            .to_string();
        assert!(expanded.contains("pub struct NonZeroBounded"));
        assert!(expanded.contains("__anneal_type_invariant_non_zero_bounded"));
        assert!(expanded.contains("anneal::type_invariant=NonZeroBounded"));
    }

    #[test]
    fn unsafe_trait_and_unsafe_impl_emit_witness_and_contract_companions() {
        let trait_input = quote! {
            pub unsafe trait Zeroable {}
        };
        let trait_expanded = expand_unsafe_trait(TokenStream2::new(), trait_input)
            .expect("expand_unsafe_trait should succeed")
            .to_string();
        assert!(trait_expanded.contains("anneal::unsafe_trait=Zeroable"));

        let impl_args = quote! {
            requires: true,
            ensures: |ok| ok,
        };
        let impl_input = quote! {
            unsafe impl Zeroable for NonZeroBounded {}
        };
        let impl_expanded = expand_unsafe_impl(impl_args, impl_input)
            .expect("expand_unsafe_impl should succeed")
            .to_string();
        assert!(impl_expanded.contains("__anneal_unsafe_impl_Zeroable_for_NonZeroBounded"));
        assert!(impl_expanded.contains("anneal::unsafe_impl=Zeroable::NonZeroBounded"));
        assert!(
            impl_expanded
                .contains("__anodized_fn_requires___anneal_unsafe_impl_Zeroable_for_NonZeroBounded")
        );
        assert!(
            impl_expanded
                .contains("__anodized_fn_ensures___anneal_unsafe_impl_Zeroable_for_NonZeroBounded")
        );
    }
}
