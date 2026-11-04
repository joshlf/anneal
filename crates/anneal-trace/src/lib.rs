// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Procedural attribute macro [`external`] for interposing at external-call
//! boundaries during Anneal ITree differential testing.
//!
//! Annotating an environment or helper function with `#[anneal_trace::external]`
//! expands to two `#[cfg]`-gated versions of the function:
//!
//! 1. Under normal compilation (`#[cfg(not(any(test, anneal_trace_ext)))]`), such
//!    as when `anneal-rustc-capture` runs `cargo check` to extract MIR, the
//!    macro emits the unmodified original function tokens (`#![no_std]`-clean).
//! 2. Under test or trace-collection builds (`#[cfg(any(test, anneal_trace_ext))]`),
//!    the macro wraps the function body in
//!    `::cargo_anneal::trace_observer::observe_boundary_call`, recording live
//!    argument byte slices, return byte slices, and unwinding panics into the
//!    active thread-local `TraceRecorder` when invoked from an unmodified root
//!    function under `TraceRecorder::observe_root`.

extern crate proc_macro;

use proc_macro::{Delimiter, Group, Ident, Punct, Spacing, Span, TokenStream, TokenTree};

/// Marks a function as an observable external or helper call boundary.
#[proc_macro_attribute]
pub fn external(attr: TokenStream, item: TokenStream) -> TokenStream {
    if !attr.is_empty() {
        return compile_error("`#[anneal_trace::external]` does not take arguments");
    }

    let orig_stream = item.clone();
    let tokens: Vec<TokenTree> = item.into_iter().collect();

    let Some(fn_pos) = tokens
        .iter()
        .position(|tt| matches!(tt, TokenTree::Ident(id) if id.to_string() == "fn"))
    else {
        return compile_error("`#[anneal_trace::external]` may only be applied to a function");
    };

    let Some(TokenTree::Ident(fn_ident)) = tokens.get(fn_pos + 1) else {
        return compile_error("expected function identifier after `fn`");
    };
    let fn_name = fn_ident.to_string();

    let Some(rel_params_pos) = tokens[fn_pos + 2..].iter().position(
        |tt| matches!(tt, TokenTree::Group(g) if g.delimiter() == Delimiter::Parenthesis),
    ) else {
        return compile_error("expected parameter list `(...)` in function signature");
    };
    let params_pos = fn_pos + 2 + rel_params_pos;

    let Some(TokenTree::Group(params_group)) = tokens.get(params_pos) else {
        return compile_error("expected parameter group");
    };

    let Some(TokenTree::Group(body_group)) = tokens.last() else {
        return compile_error("expected function body `{ ... }` at end of item");
    };
    if body_group.delimiter() != Delimiter::Brace || params_pos >= tokens.len() - 1 {
        return compile_error("expected function body `{ ... }` after signature");
    }

    let (normalized_params, arg_idents) = match parse_and_normalize_params(params_group.stream()) {
        Ok(pair) => pair,
        Err(err) => return err,
    };

    let mut out = TokenStream::new();

    // 1. Unmodified item for normal (`#![no_std]` / MIR capture) builds:
    //    `#[allow(unexpected_cfgs)] #[cfg(not(any(test, anneal_trace_ext)))] <orig_stream>`
    out.extend(parse_tokens(
        "#[allow(unexpected_cfgs)] #[cfg(not(any(test, anneal_trace_ext)))]",
    ));
    out.extend(orig_stream);

    // 2. Boundary-observing item for test and trace-collection builds:
    //    `#[allow(unexpected_cfgs)] #[cfg(any(test, anneal_trace_ext))] ...`
    out.extend(parse_tokens(
        "#[allow(unexpected_cfgs)] #[cfg(any(test, anneal_trace_ext))]",
    ));
    for tt in &tokens[..params_pos] {
        out.extend(std::iter::once(tt.clone()));
    }
    let mut new_params_group = Group::new(Delimiter::Parenthesis, normalized_params);
    new_params_group.set_span(params_group.span());
    out.extend(std::iter::once(TokenTree::Group(new_params_group)));

    for tt in &tokens[params_pos + 1..tokens.len() - 1] {
        out.extend(std::iter::once(tt.clone()));
    }

    let mut raw_args_elems = String::new();
    for (idx, arg_id) in arg_idents.iter().enumerate() {
        if idx > 0 {
            raw_args_elems.push_str(", ");
        }
        raw_args_elems.push_str(&format!(
            "::cargo_anneal::trace_observer::value_as_raw_bytes(&{arg_id})"
        ));
    }

    let mut wrapper_body = TokenStream::new();
    wrapper_body.extend(parse_tokens(
        "::cargo_anneal::trace_observer::observe_boundary_call",
    ));

    let mut call_args = TokenStream::new();
    call_args.extend(parse_tokens(&format!(
        "module_path!(), {:?}, ::std::vec![{}], move || ",
        fn_name, raw_args_elems
    )));
    call_args.extend(std::iter::once(TokenTree::Group(body_group.clone())));

    wrapper_body.extend(std::iter::once(TokenTree::Group(Group::new(
        Delimiter::Parenthesis,
        call_args,
    ))));

    let mut new_body_group = Group::new(Delimiter::Brace, wrapper_body);
    new_body_group.set_span(body_group.span());
    out.extend(std::iter::once(TokenTree::Group(new_body_group)));

    out
}

fn parse_and_normalize_params(
    params_stream: TokenStream,
) -> Result<(TokenStream, Vec<String>), TokenStream> {
    let all_tts: Vec<TokenTree> = params_stream.into_iter().collect();
    if all_tts.is_empty() {
        return Ok((TokenStream::new(), Vec::new()));
    }

    let mut segments: Vec<Vec<TokenTree>> = Vec::new();
    let mut current: Vec<TokenTree> = Vec::new();
    let mut angle_depth = 0usize;
    for tt in all_tts {
        match &tt {
            TokenTree::Punct(p) if p.as_char() == '<' => {
                angle_depth += 1;
                current.push(tt);
            }
            TokenTree::Punct(p) if p.as_char() == '>' => {
                angle_depth = angle_depth.saturating_sub(1);
                current.push(tt);
            }
            TokenTree::Punct(p) if p.as_char() == ',' && angle_depth == 0 => {
                segments.push(std::mem::take(&mut current));
            }
            _ => current.push(tt),
        }
    }
    if !current.is_empty() {
        segments.push(current);
    }

    let mut normalized = TokenStream::new();
    let mut arg_names = Vec::with_capacity(segments.len());

    for (idx, seg) in segments.into_iter().enumerate() {
        if idx > 0 {
            normalized.extend(std::iter::once(TokenTree::Punct(Punct::new(
                ',',
                Spacing::Alone,
            ))));
        }
        let Some(colon_pos) = seg
            .iter()
            .position(|tt| matches!(tt, TokenTree::Punct(p) if p.as_char() == ':'))
        else {
            return Err(compile_error(
                "`#[anneal_trace::external]` does not support `self` receivers",
            ));
        };

        let pat_slice = &seg[..colon_pos];
        let ty_slice = &seg[colon_pos..];

        let mut found_ident: Option<String> = None;
        for tt in pat_slice {
            if let TokenTree::Ident(id) = tt {
                let s = id.to_string();
                if s != "mut" && s != "ref" && s != "_" {
                    found_ident = Some(s);
                }
            }
        }

        if let Some(name) = found_ident {
            for tt in pat_slice {
                normalized.extend(std::iter::once(tt.clone()));
            }
            for tt in ty_slice {
                normalized.extend(std::iter::once(tt.clone()));
            }
            arg_names.push(name);
        } else {
            let synth_name = format!("__anneal_arg_{idx}");
            normalized.extend(std::iter::once(TokenTree::Ident(Ident::new(
                &synth_name,
                Span::call_site(),
            ))));
            for tt in ty_slice {
                normalized.extend(std::iter::once(tt.clone()));
            }
            arg_names.push(synth_name);
        }
    }

    Ok((normalized, arg_names))
}

fn parse_tokens(src: &str) -> TokenStream {
    src.parse::<TokenStream>()
        .expect("internal token stream literal must parse")
}

fn compile_error(msg: &str) -> TokenStream {
    parse_tokens(&format!("compile_error!({msg:?});"))
}
