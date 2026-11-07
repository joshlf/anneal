// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Procedural attribute macros [`external`] and [`capture`] for Anneal ITree
//! differential testing and runtime trace observation.
//!
//! - `#[anneal_trace::external]` marks an environment or helper function as an
//!   observable call boundary. Under normal compilation and MIR capture
//!   (`#[cfg(not(any(test, anneal_trace_ext)))]`), it expands to the unmodified
//!   function tokens. Under test and trace-collection builds
//!   (`#[cfg(any(test, anneal_trace_ext))]`), it wraps the body in
//!   `::cargo_anneal::trace_observer::observe_boundary_call`.
//! - `#[anneal_trace::capture]` derives safe, layout-aware implementations of
//!   `::cargo_anneal::trace_observer::TraceCapture` (using `core::mem::offset_of!`
//!   so struct padding bytes are never read and are marked as `None`) and
//!   `::cargo_anneal::trace_observer::FromScheduleBytes` (validating byte length
//!   and field validity invariants without `MaybeUninit::assume_init`) under
//!   `#[cfg(any(test, anneal_trace_ext))]`, while expanding to unmodified tokens
//!   during normal compilation and MIR capture.

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

    // 1. Unmodified item for normal (`#![no_std]` / MIR capture) or
    //    MIR-instrumented (`anneal_mir_instrument`) builds:
    out.extend(parse_tokens(
        "#[allow(unexpected_cfgs)] #[cfg(any(anneal_mir_instrument, not(any(test, anneal_trace_ext))))]",
    ));
    out.extend(orig_stream);

    // 2. Boundary-observing item for source-level test and trace-collection builds:
    out.extend(parse_tokens(
        "#[allow(unexpected_cfgs)] #[cfg(all(not(anneal_mir_instrument), any(test, anneal_trace_ext)))]",
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

/// Derives safe, padding-aware `TraceCapture` and `FromScheduleBytes`
/// implementations for a struct or unit enum under
/// `#[cfg(any(test, anneal_trace_ext))]`, while emitting the unmodified item
/// during normal compilation and MIR capture.
#[proc_macro_attribute]
pub fn capture(attr: TokenStream, item: TokenStream) -> TokenStream {
    if !attr.is_empty() {
        return compile_error("`#[anneal_trace::capture]` does not take arguments");
    }

    let orig_stream = item.clone();
    let tokens: Vec<TokenTree> = item.into_iter().collect();

    if let Some(struct_pos) = tokens
        .iter()
        .position(|tt| matches!(tt, TokenTree::Ident(id) if id.to_string() == "struct"))
    {
        return expand_struct_capture(orig_stream, &tokens, struct_pos);
    }

    if let Some(enum_pos) = tokens
        .iter()
        .position(|tt| matches!(tt, TokenTree::Ident(id) if id.to_string() == "enum"))
    {
        return expand_enum_capture(orig_stream, &tokens, enum_pos);
    }

    compile_error("`#[anneal_trace::capture]` may only be applied to a `struct` or `enum`")
}

fn expand_struct_capture(
    orig_stream: TokenStream,
    tokens: &[TokenTree],
    struct_pos: usize,
) -> TokenStream {
    let Some(TokenTree::Ident(struct_ident)) = tokens.get(struct_pos + 1) else {
        return compile_error("expected struct identifier after `struct`");
    };
    let struct_name = struct_ident.to_string();

    let Some(TokenTree::Group(body_group)) = tokens.last() else {
        return compile_error("expected struct body `{ ... }`");
    };
    if body_group.delimiter() != Delimiter::Brace {
        return compile_error(
            "`#[anneal_trace::capture]` on structs requires named fields `{ ... }`",
        );
    }

    let fields = match parse_struct_fields(body_group.stream()) {
        Ok(f) => f,
        Err(err) => return err,
    };

    let mut write_stmts = String::new();
    let mut decode_inits = String::new();
    for (field_name, field_ty) in &fields {
        write_stmts.push_str(&format!(
            "{{ \
                let off = ::core::mem::offset_of!(Self, {field_name}); \
                let len = ::core::mem::size_of_val(&self.{field_name}); \
                ::cargo_anneal::trace_observer::TraceCapture::write_captured_bytes( \
                    &self.{field_name}, \
                    &mut dst[off..off + len], \
                ); \
            }}\n"
        ));
        decode_inits.push_str(&format!(
            "{field_name}: {{ \
                let off = ::core::mem::offset_of!(Self, {field_name}); \
                let len = ::core::mem::size_of::<{field_ty}>(); \
                <{field_ty} as ::cargo_anneal::trace_observer::FromScheduleBytes>::from_schedule_bytes( \
                    &bytes[off..off + len], \
                )? \
            }},\n"
        ));
    }

    let impl_src = format!(
        "#[allow(unexpected_cfgs)]\n\
         const _: () = {{\n\
             #[cfg(any(test, anneal_trace_ext, anneal_mir_instrument))]\n\
             impl ::cargo_anneal::trace_observer::TraceCapture for {struct_name} {{\n\
                 fn write_captured_bytes(&self, dst: &mut [::core::option::Option<u8>]) {{\n\
                     {write_stmts}\
                 }}\n\
             }}\n\
             #[cfg(any(test, anneal_trace_ext, anneal_mir_instrument))]\n\
             impl ::cargo_anneal::trace_observer::FromScheduleBytes for {struct_name} {{\n\
                 fn from_schedule_bytes(\n\
                     bytes: &[u8],\n\
                 ) -> ::core::result::Result<Self, ::cargo_anneal::trace_observer::ScheduleError> {{\n\
                     let expected = ::core::mem::size_of::<Self>();\n\
                     if bytes.len() != expected {{\n\
                         return ::core::result::Result::Err(\n\
                             ::cargo_anneal::trace_observer::ScheduleError::PayloadSizeMismatch {{\n\
                                 context: {struct_name:?}.to_string(),\n\
                                 expected,\n\
                                 actual: bytes.len(),\n\
                             }},\n\
                         );\n\
                     }}\n\
                     ::core::result::Result::Ok(Self {{\n\
                         {decode_inits}\
                     }})\n\
                 }}\n\
             }}\n\
         }};\n"
    );

    let mut out = orig_stream;
    out.extend(parse_tokens(&impl_src));
    out
}

fn expand_enum_capture(
    orig_stream: TokenStream,
    tokens: &[TokenTree],
    enum_pos: usize,
) -> TokenStream {
    let Some(TokenTree::Ident(enum_ident)) = tokens.get(enum_pos + 1) else {
        return compile_error("expected enum identifier after `enum`");
    };
    let enum_name = enum_ident.to_string();

    let Some(TokenTree::Group(body_group)) = tokens.last() else {
        return compile_error("expected enum body `{ ... }`");
    };
    if body_group.delimiter() != Delimiter::Brace {
        return compile_error("expected enum body `{ ... }`");
    }

    let variants = match parse_unit_enum_variants(body_group.stream()) {
        Ok(v) => v,
        Err(err) => return err,
    };

    let mut match_arms = String::new();
    let mut cand_list = String::new();
    for (idx, var_name) in variants.iter().enumerate() {
        match_arms.push_str(&format!(
            "Self::{var_name} => (Self::{var_name} as i128) as u128,\n"
        ));
        if idx > 0 {
            cand_list.push_str(", ");
        }
        cand_list.push_str(&format!("Self::{var_name}"));
    }

    let impl_src = format!(
        "#[allow(unexpected_cfgs)]\n\
         const _: () = {{\n\
             #[cfg(any(test, anneal_trace_ext, anneal_mir_instrument))]\n\
             impl ::cargo_anneal::trace_observer::TraceCapture for {enum_name} {{\n\
                 fn write_captured_bytes(&self, dst: &mut [::core::option::Option<u8>]) {{\n\
                     let disc: u128 = match *self {{\n\
                         {match_arms}\
                     }};\n\
                     let le = disc.to_le_bytes();\n\
                     let n = dst.len().min(16);\n\
                     let mut i = 0usize;\n\
                     while i < n {{\n\
                         dst[i] = ::core::option::Option::Some(le[i]);\n\
                         i += 1;\n\
                     }}\n\
                 }}\n\
                 fn write_niche_none_bytes(dst: &mut [::core::option::Option<u8>]) {{\n\
                     for slot in dst.iter_mut() {{\n\
                         *slot = ::core::option::Option::Some(0xFF);\n\
                     }}\n\
                 }}\n\
             }}\n\
             #[cfg(any(test, anneal_trace_ext, anneal_mir_instrument))]\n\
             impl ::cargo_anneal::trace_observer::FromScheduleBytes for {enum_name} {{\n\
                 fn from_schedule_bytes(\n\
                     bytes: &[u8],\n\
                 ) -> ::core::result::Result<Self, ::cargo_anneal::trace_observer::ScheduleError> {{\n\
                     let expected = ::core::mem::size_of::<Self>();\n\
                     if bytes.len() != expected {{\n\
                         return ::core::result::Result::Err(\n\
                             ::cargo_anneal::trace_observer::ScheduleError::PayloadSizeMismatch {{\n\
                                 context: {enum_name:?}.to_string(),\n\
                                 expected,\n\
                                 actual: bytes.len(),\n\
                             }},\n\
                         );\n\
                     }}\n\
                     for cand in [{cand_list}] {{\n\
                         let raw = ::cargo_anneal::trace_observer::value_as_raw_bytes(&cand);\n\
                         if raw.as_slice() == bytes {{\n\
                             return ::core::result::Result::Ok(cand);\n\
                         }}\n\
                     }}\n\
                     ::core::result::Result::Err(\n\
                         ::cargo_anneal::trace_observer::ScheduleError::InvalidBitPattern {{\n\
                             context: {enum_name:?}.to_string(),\n\
                             reason: ::std::format!(\"invalid enum discriminant bytes {{:?}}\", bytes),\n\
                         }},\n\
                     )\n\
                 }}\n\
                 fn is_niche_none_bytes(bytes: &[u8]) -> bool {{\n\
                     !bytes.is_empty()\n\
                         && bytes.iter().all(|&b| b == 0xFF)\n\
                         && <Self as ::cargo_anneal::trace_observer::FromScheduleBytes>::from_schedule_bytes(bytes).is_err()\n\
                 }}\n\
             }}\n\
         }};\n"
    );

    let mut out = orig_stream;
    out.extend(parse_tokens(&impl_src));
    out
}

fn split_top_level_comma(stream: TokenStream) -> Vec<Vec<TokenTree>> {
    let all_tts: Vec<TokenTree> = stream.into_iter().collect();
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
                if !current.is_empty() {
                    segments.push(std::mem::take(&mut current));
                }
            }
            _ => current.push(tt),
        }
    }
    if !current.is_empty() {
        segments.push(current);
    }
    segments
}

fn parse_struct_fields(body_stream: TokenStream) -> Result<Vec<(String, String)>, TokenStream> {
    let mut fields = Vec::new();
    for seg in split_top_level_comma(body_stream) {
        let Some(colon_pos) = seg
            .iter()
            .position(|tt| matches!(tt, TokenTree::Punct(p) if p.as_char() == ':'))
        else {
            return Err(compile_error("expected `field: Type` in struct definition"));
        };
        let Some(TokenTree::Ident(field_ident)) = seg[..colon_pos].last() else {
            return Err(compile_error("expected field identifier before `:`"));
        };
        let mut ty_stream = TokenStream::new();
        for tt in &seg[colon_pos + 1..] {
            ty_stream.extend(std::iter::once(tt.clone()));
        }
        fields.push((field_ident.to_string(), ty_stream.to_string()));
    }
    Ok(fields)
}

fn parse_unit_enum_variants(body_stream: TokenStream) -> Result<Vec<String>, TokenStream> {
    let mut variants = Vec::new();
    for seg in split_top_level_comma(body_stream) {
        let mut var_ident: Option<String> = None;
        for tt in seg {
            match tt {
                TokenTree::Group(g) if g.delimiter() == Delimiter::Bracket => {
                    // Skip attributes on variants.
                }
                TokenTree::Punct(p) if p.as_char() == '#' => {}
                TokenTree::Ident(id) => {
                    var_ident = Some(id.to_string());
                    break;
                }
                _ => {}
            }
        }
        let Some(name) = var_ident else {
            return Err(compile_error("expected enum variant identifier"));
        };
        variants.push(name);
    }
    Ok(variants)
}

fn parse_and_normalize_params(
    params_stream: TokenStream,
) -> Result<(TokenStream, Vec<String>), TokenStream> {
    let segments = split_top_level_comma(params_stream);
    if segments.is_empty() {
        return Ok((TokenStream::new(), Vec::new()));
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
