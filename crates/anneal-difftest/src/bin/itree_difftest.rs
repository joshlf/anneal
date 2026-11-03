// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! `itree-difftest`: generates safe-Rust ITree candidate programs and checks
//! that they, and their auto-instrumented copies, compile.
//!
//! This binary does not execute the generated programs or their instrumented
//! copies, and it does not run Anneal's Lean model. It therefore reports no
//! traces, parity rates, path counts, or divergences; its JSON output states
//! `"oracle_comparison": "not_performed"`, and the campaign runner
//! (`scripts/run_diff_test_campaign.py`) reports such a run as not evaluated.
//! The `-C opt-level=0` and `-C opt-level=2` checks only compile.

use std::collections::BTreeMap;
use std::env;
use std::fs;
use std::io::Write;
use std::path::PathBuf;
use std::process::{Command, Stdio};
use std::time::Instant;

use anneal_difftest::instrument::instrument_source;
use anneal_difftest::mutators_itree::{
    GeneratedItreeCandidate, contains_unsafe_token, generate_itree_batch,
};

/// Strictly safe seed programs with target function `kernel_step` and external
/// callee `ext_oracle`.
const ITREE_SAFE_SEEDS: &[&str] = &[
    r#"
pub fn ext_oracle(query: u32) -> u32 {
    query.wrapping_mul(1664525).wrapping_add(1013904223)
}

pub fn kernel_step(magic: u32, payload_len: u32) -> u32 {
    if magic == 0x414E_4E4C {
        if payload_len > 1024 {
            ext_oracle(payload_len)
        } else {
            ext_oracle(magic ^ payload_len)
        }
    } else if payload_len == 0x80 {
        ext_oracle(0x80)
    } else {
        magic.wrapping_add(payload_len)
    }
}
"#,
    r#"
pub fn ext_oracle(query: u32) -> u32 {
    query.rotate_left(13) ^ 0x55AA_55AA
}

pub fn kernel_step(magic: u32, payload_len: u32) -> u32 {
    let delta: u32 = magic.wrapping_sub(payload_len);
    if delta < 16 {
        ext_oracle(delta)
    } else if delta == 0xDEAD_BEEF {
        ext_oracle(0xDEAD_BEEF)
    } else {
        delta ^ 0x0F0F_0F0F
    }
}
"#,
];

/// Mutator families whose application counts are always reported, so that a
/// family that never fires shows up as zero rather than disappearing.
const MUTATOR_NAMES: [&str; 4] = [
    "CallBoundaryOutliner",
    "LayoutPaddingPerturber",
    "BranchLoopWeaver",
    "ExtOracleInjector",
];

/// CLI configuration for `itree-difftest`.
#[derive(Debug, Clone)]
struct ItreeDiffTestArgs {
    batches: usize,
    batch_size: usize,
    seed: u64,
    output_json: Option<PathBuf>,
}

impl Default for ItreeDiffTestArgs {
    fn default() -> Self {
        Self {
            batches: 2,
            batch_size: 16,
            seed: 0x5EED_0002,
            output_json: None,
        }
    }
}

fn parse_u64_or_hex(raw: &str) -> Result<u64, String> {
    let clean: String = raw.trim().chars().filter(|&c| c != '_').collect();
    if let Some(hex) = clean
        .strip_prefix("0x")
        .or_else(|| clean.strip_prefix("0X"))
    {
        u64::from_str_radix(hex, 16).map_err(|e| format!("invalid hex seed `{raw}`: {e}"))
    } else {
        clean
            .parse::<u64>()
            .map_err(|e| format!("invalid integer seed `{raw}`: {e}"))
    }
}

fn parse_cli_args() -> Result<ItreeDiffTestArgs, String> {
    let mut cfg = ItreeDiffTestArgs::default();
    let args: Vec<String> = env::args().skip(1).collect();
    let mut i = 0usize;
    while i < args.len() {
        match args[i].as_str() {
            "--batches" => {
                i += 1;
                let val = args.get(i).ok_or("--batches requires a value")?;
                cfg.batches = val
                    .parse::<usize>()
                    .map_err(|e| format!("invalid --batches `{val}`: {e}"))?;
            }
            "--batch-size" => {
                i += 1;
                let val = args.get(i).ok_or("--batch-size requires a value")?;
                cfg.batch_size = val
                    .parse::<usize>()
                    .map_err(|e| format!("invalid --batch-size `{val}`: {e}"))?;
            }
            "--seed" => {
                i += 1;
                let val = args.get(i).ok_or("--seed requires a value")?;
                cfg.seed = parse_u64_or_hex(val)?;
            }
            "--output-json" => {
                i += 1;
                let val = args.get(i).ok_or("--output-json requires a path")?;
                cfg.output_json = Some(PathBuf::from(val));
            }
            "--help" | "-h" => {
                println!(
                    "Usage: itree-difftest [--batches N] [--batch-size B] [--seed S] \
                     [--output-json PATH]\n\
                     Generates and compiles candidates only; executes nothing and runs no \
                     oracle."
                );
                std::process::exit(0);
            }
            other => {
                return Err(format!("unrecognized argument `{other}`"));
            }
        }
        i += 1;
    }
    Ok(cfg)
}

fn resolve_rustc_bin() -> String {
    if let Ok(r) = env::var("RUSTC")
        && !r.is_empty()
    {
        return r;
    }
    if let Ok(home) = env::var("HOME") {
        let candidate = PathBuf::from(home).join(".cargo/bin/rustc");
        if candidate.exists() {
            return candidate.to_string_lossy().into_owned();
        }
    }
    "rustc".to_string()
}

/// Runs `rustc --edition=2024 --crate-type=lib -D warnings` with
/// `-C opt-level=<level>` on `source` and reports whether it compiled.
fn compile_rust_strict_opt(label: &str, opt_level: &str, source: &str) -> bool {
    let rustc_bin = resolve_rustc_bin();
    let tmp_dir = env::temp_dir().join(format!(
        "anneal_itree_difftest_{}_{}_o{}",
        std::process::id(),
        label,
        opt_level
    ));
    let _ = fs::create_dir_all(&tmp_dir);
    let out_path = tmp_dir.join("libitree_check.rlib");
    let opt_flag = format!("opt-level={opt_level}");

    let child_res = Command::new(&rustc_bin)
        .args([
            "--edition=2024",
            "--crate-type=lib",
            "-D",
            "warnings",
            "-C",
            &opt_flag,
            "-o",
        ])
        .arg(&out_path)
        .arg("-")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn();

    let Ok(mut child) = child_res else {
        let _ = fs::remove_dir_all(&tmp_dir);
        return false;
    };

    if let Some(mut stdin) = child.stdin.take() {
        let _ = stdin.write_all(source.as_bytes());
    }
    let ok = child
        .wait_with_output()
        .map(|o| o.status.success())
        .unwrap_or(false);
    let _ = fs::remove_dir_all(&tmp_dir);
    ok
}

/// Per-candidate compile results.
#[derive(Debug, Clone, Copy, Default)]
struct CandidateCompile {
    opt0: bool,
    opt2: bool,
    instrumented: bool,
}

/// Compiles every candidate under `#![forbid(unsafe_code)]` at `-C
/// opt-level=0` and `-C opt-level=2`, and compiles every candidate's
/// instrumented copy at `-C opt-level=0`. Each check first compiles all
/// candidates as one crate and falls back to one candidate at a time only when
/// the combined crate fails, so a failure is always attributed to a candidate.
fn compile_candidates(batches: &[Vec<GeneratedItreeCandidate>]) -> Vec<Vec<CandidateCompile>> {
    let mut results: Vec<Vec<CandidateCompile>> = batches
        .iter()
        .map(|b| vec![CandidateCompile::default(); b.len()])
        .collect();

    let mut combined_safe = String::from("#![forbid(unsafe_code)]\n");
    let mut combined_inst = String::new();
    // `None` records a candidate whose instrumentation failed before compiling.
    let mut inst_sources: Vec<Vec<Option<String>>> = Vec::with_capacity(batches.len());
    for (b_idx, batch) in batches.iter().enumerate() {
        let mut batch_inst = Vec::with_capacity(batch.len());
        for (c_idx, cand) in batch.iter().enumerate() {
            combined_safe.push_str(&format!(
                "pub mod b{b_idx}_c{c_idx} {{\n{}\n}}\n",
                cand.source
            ));
            let inst = instrument_source(&cand.source, "kernel_step", &["ext_oracle"]).ok();
            if let Some(src) = &inst {
                combined_inst.push_str(&format!("pub mod inst_b{b_idx}_c{c_idx} {{\n{src}\n}}\n"));
            }
            batch_inst.push(inst);
        }
        inst_sources.push(batch_inst);
    }
    let any_inst_failed = inst_sources.iter().flatten().any(Option::is_none);

    let (o0_all, o2_all, inst_all) = std::thread::scope(|s| {
        let h0 = s.spawn(|| compile_rust_strict_opt("all_safe", "0", &combined_safe));
        let h2 = s.spawn(|| compile_rust_strict_opt("all_safe", "2", &combined_safe));
        let hi = s.spawn(|| {
            !any_inst_failed
                && !combined_inst.is_empty()
                && compile_rust_strict_opt("all_inst", "0", &combined_inst)
        });
        (
            h0.join().unwrap_or(false),
            h2.join().unwrap_or(false),
            hi.join().unwrap_or(false),
        )
    });

    for (b_idx, batch) in batches.iter().enumerate() {
        for (c_idx, cand) in batch.iter().enumerate() {
            let safe_src = format!("#![forbid(unsafe_code)]\n{}", cand.source);
            let label = format!("b{b_idx}_c{c_idx}");
            let entry = &mut results[b_idx][c_idx];
            entry.opt0 = o0_all || compile_rust_strict_opt(&label, "0", &safe_src);
            entry.opt2 = o2_all || compile_rust_strict_opt(&label, "2", &safe_src);
            entry.instrumented = match &inst_sources[b_idx][c_idx] {
                None => false,
                Some(src) => {
                    inst_all || compile_rust_strict_opt(&format!("{label}_inst"), "0", src)
                }
            };
        }
    }
    results
}

/// Renders a flat JSON object with one `"key": value` line per field. Values
/// are emitted verbatim, so callers pass numbers or already-quoted strings.
/// `mutator_applications` holds per-mutator counts as a nested object.
fn render_json(fields: &[(&str, String)], mutator_counts: &BTreeMap<String, usize>) -> String {
    let mutators = mutator_counts
        .iter()
        .map(|(name, count)| format!("    \"{name}\": {count}"))
        .collect::<Vec<_>>()
        .join(",\n");
    let mut lines: Vec<String> = fields
        .iter()
        .map(|(key, value)| format!("  \"{key}\": {value}"))
        .collect();
    lines.push(format!("  \"mutator_applications\": {{\n{mutators}\n  }}"));
    format!("{{\n{}\n}}\n", lines.join(",\n"))
}

fn main() {
    let args = match parse_cli_args() {
        Ok(a) => a,
        Err(e) => {
            eprintln!("error: {e}");
            std::process::exit(2);
        }
    };

    let start = Instant::now();

    let batches: Vec<Vec<GeneratedItreeCandidate>> = (0..args.batches)
        .map(|b_idx| {
            let batch_seed = args
                .seed
                .wrapping_add((b_idx as u64).wrapping_mul(0x9E37_79B9_7F4A_7C15));
            generate_itree_batch(ITREE_SAFE_SEEDS, args.batch_size, batch_seed)
        })
        .collect();
    let total_candidates: usize = batches.iter().map(Vec::len).sum();

    let unsafe_token_violations = batches
        .iter()
        .flatten()
        .filter(|cand| contains_unsafe_token(&cand.source))
        .count();

    let compile_results = compile_candidates(&batches);
    let flat: Vec<CandidateCompile> = compile_results.into_iter().flatten().collect();
    let o0_compiled = flat.iter().filter(|c| c.opt0).count();
    let o2_compiled = flat.iter().filter(|c| c.opt2).count();
    let both_compiled = flat.iter().filter(|c| c.opt0 && c.opt2).count();
    let instrumented_compiled = flat.iter().filter(|c| c.instrumented).count();

    let mut mutator_counts: BTreeMap<String, usize> =
        MUTATOR_NAMES.iter().map(|m| (m.to_string(), 0)).collect();
    for cand in batches.iter().flatten() {
        for m in &cand.applied_mutators {
            *mutator_counts.entry(m.clone()).or_insert(0) += 1;
        }
    }

    let elapsed_ms = start.elapsed().as_secs_f64() * 1000.0;
    let compile_rate_pct = if total_candidates == 0 {
        0.0
    } else {
        (both_compiled as f64 / total_candidates as f64) * 100.0
    };

    let json_report = render_json(
        &[
            ("harness", "\"itree-difftest\"".to_string()),
            ("oracle_comparison", "\"not_performed\"".to_string()),
            ("seed", format!("\"0x{:08x}\"", args.seed)),
            ("batches", args.batches.to_string()),
            ("batch_size", args.batch_size.to_string()),
            ("total_candidates", total_candidates.to_string()),
            (
                "unsafe_token_violations",
                unsafe_token_violations.to_string(),
            ),
            ("opt_level_0_compiled", o0_compiled.to_string()),
            ("opt_level_2_compiled", o2_compiled.to_string()),
            ("opt_level_0_and_2_compiled", both_compiled.to_string()),
            ("instrumented_compiled", instrumented_compiled.to_string()),
            ("compile_pass_rate_pct", format!("{compile_rate_pct:.2}")),
            ("elapsed_ms", format!("{elapsed_ms:.2}")),
        ],
        &mutator_counts,
    );

    if let Some(ref out_path) = args.output_json {
        if let Some(parent) = out_path.parent()
            && !parent.as_os_str().is_empty()
        {
            let _ = fs::create_dir_all(parent);
        }
        fs::write(out_path, &json_report).expect("failed to write --output-json file");
    }

    println!("# `itree-difftest` candidate generation report\n");
    println!(
        "- **Oracle comparison**: NOT PERFORMED. This binary does not execute the \
         generated programs or their instrumented copies, and does not run \
         Anneal's Lean model."
    );
    println!(
        "- **Seed**: `0x{:08x}` (`{}` batches × `{}` candidates = `{}` generated)",
        args.seed, args.batches, args.batch_size, total_candidates
    );
    println!("- **Candidates containing `unsafe`**: `{unsafe_token_violations}`");
    println!(
        "- **Compiled at both `-C opt-level=0` and `-C opt-level=2` (compile only)**: \
         `{}/{}` ({:.2}%)",
        both_compiled, total_candidates, compile_rate_pct
    );
    println!(
        "- **Instrumented copies compiled (never executed)**: `{}/{}`",
        instrumented_compiled, total_candidates
    );
    println!("- **Wall-clock time**: `{:.2} ms`\n", elapsed_ms);
    println!("| Mutator | Applications |");
    println!("| :--- | ---: |");
    for (name, count) in &mutator_counts {
        println!("| `{name}` | {count} |");
    }
}
