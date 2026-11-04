// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! `itree-difftest`: generates strictly safe-Rust ITree candidate programs,
//! executes them natively with `#[anneal_trace::external]` boundary
//! interposition over generated inputs, deduplicates distinct traces, checks
//! each in batch in the Lean 4 kernel (`TraceCheck`, obs-erased), and reports
//! `TraceReplayDiag` divergences.
//!
//! When invoked with `--compile-only`, it checks candidate compilation at
//! `-C opt-level=0`, `-C opt-level=2`, and `#[anneal_trace::external]`
//! annotation without running native execution or Lean
//! (`"oracle_comparison": "not_performed"`).

use std::collections::BTreeMap;
use std::env;
use std::fs;
use std::path::{Path, PathBuf};
use std::time::Instant;

use anneal_difftest::itree_eval::{
    CandidateCompile, DEFAULT_ITREE_TRIALS_PER_CANDIDATE, ITREE_MUTATOR_NAMES, ITREE_SAFE_SEEDS,
    ItreeEvalOptions, compile_itree_candidates, evaluate_itree_batches_with_options,
    render_itree_eval_report_json, render_itree_eval_report_markdown, reproduce_itree_finding,
};
use anneal_difftest::miri_eval::json_escape;
use anneal_difftest::mutators_itree::{
    GeneratedItreeCandidate, contains_unsafe_token, generate_itree_batch,
    generate_itree_identity_batch,
};

/// CLI configuration for `itree-difftest`.
#[derive(Debug, Clone)]
struct ItreeDiffTestArgs {
    batches: usize,
    batch_size: usize,
    trials: usize,
    seed: u64,
    identity: bool,
    compile_only: bool,
    findings_dir: Option<PathBuf>,
    output_json: Option<PathBuf>,
    reproduce: Option<PathBuf>,
}

impl Default for ItreeDiffTestArgs {
    fn default() -> Self {
        Self {
            batches: 2,
            batch_size: 16,
            trials: DEFAULT_ITREE_TRIALS_PER_CANDIDATE,
            seed: 0x5EED_0002,
            identity: false,
            compile_only: false,
            findings_dir: None,
            output_json: None,
            reproduce: None,
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
            "--trials" => {
                i += 1;
                let val = args.get(i).ok_or("--trials requires a value")?;
                cfg.trials = val
                    .parse::<usize>()
                    .map_err(|e| format!("invalid --trials `{val}`: {e}"))?;
            }
            "--seed" => {
                i += 1;
                let val = args.get(i).ok_or("--seed requires a value")?;
                cfg.seed = parse_u64_or_hex(val)?;
            }
            "--identity" => {
                cfg.identity = true;
            }
            "--compile-only" => {
                cfg.compile_only = true;
            }
            "--findings-dir" => {
                i += 1;
                let val = args.get(i).ok_or("--findings-dir requires a path")?;
                cfg.findings_dir = Some(PathBuf::from(val));
            }
            "--output-json" => {
                i += 1;
                let val = args.get(i).ok_or("--output-json requires a path")?;
                cfg.output_json = Some(PathBuf::from(val));
            }
            "--reproduce" => {
                i += 1;
                let val = args.get(i).ok_or("--reproduce requires a path")?;
                cfg.reproduce = Some(PathBuf::from(val));
            }
            "--help" | "-h" => {
                println!(
                    "Usage: itree-difftest [--batches N] [--batch-size B] [--trials T] \
                     [--seed S] [--identity] [--findings-dir DIR] [--output-json PATH] \
                     [--reproduce PATH] [--compile-only]"
                );
                std::process::exit(0);
            }
            other => {
                return Err(format!("unrecognized argument `{other}`"));
            }
        }
        i += 1;
    }
    if cfg.compile_only && cfg.findings_dir.is_some() {
        return Err("--findings-dir cannot be used with --compile-only".to_string());
    }
    if cfg.compile_only && cfg.reproduce.is_some() {
        return Err("--reproduce cannot be used with --compile-only".to_string());
    }
    if cfg.identity && cfg.reproduce.is_some() {
        return Err("--reproduce cannot be used with --identity".to_string());
    }
    if !cfg.compile_only
        && !cfg.identity
        && cfg.reproduce.is_none()
        && (cfg.batches == 0 || cfg.batch_size == 0 || cfg.trials == 0)
    {
        return Err(
            "--batches, --batch-size, and --trials must be at least 1 when running oracle comparison"
                .to_string(),
        );
    }
    Ok(cfg)
}

fn default_repo_root() -> Option<PathBuf> {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(Path::parent)
        .map(Path::to_path_buf)
}

fn render_compile_only_json(
    fields: &[(&str, String)],
    mutator_counts: &BTreeMap<String, usize>,
) -> String {
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

fn write_json_output(out_path: &Path, contents: &str) {
    if let Some(parent) = out_path.parent()
        && !parent.as_os_str().is_empty()
    {
        let _ = fs::create_dir_all(parent);
    }
    fs::write(out_path, contents).expect("failed to write --output-json file");
}

fn run_compile_only(args: &ItreeDiffTestArgs, batches: &[Vec<GeneratedItreeCandidate>]) {
    let start = Instant::now();
    let total_candidates: usize = batches.iter().map(Vec::len).sum();
    let unsafe_token_violations = batches
        .iter()
        .flatten()
        .filter(|cand| contains_unsafe_token(&cand.source))
        .count();

    let compile_results = compile_itree_candidates(batches);
    let flat: Vec<CandidateCompile> = compile_results.into_iter().flatten().collect();
    let o0_compiled = flat.iter().filter(|c| c.opt0).count();
    let o2_compiled = flat.iter().filter(|c| c.opt2).count();
    let both_compiled = flat.iter().filter(|c| c.opt0 && c.opt2).count();
    let instrumented_compiled = flat.iter().filter(|c| c.instrumented).count();

    let mut mutator_counts: BTreeMap<String, usize> = ITREE_MUTATOR_NAMES
        .iter()
        .map(|m| (m.to_string(), 0))
        .collect();
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

    let json_report = render_compile_only_json(
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
        write_json_output(out_path, &json_report);
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

fn run_reproducer(repro_path: &Path, output_json: Option<&Path>) -> Result<(), String> {
    let repo_root = default_repo_root();
    let rep = reproduce_itree_finding(repro_path, repo_root.as_deref())?;
    let json = format!(
        "{{\n\
         \x20 \"reproducer\": {},\n\
         \x20 \"fn_name\": {},\n\
         \x20 \"verdict\": {},\n\
         \x20 \"diag_tag\": {},\n\
         \x20 \"diag_repr\": {},\n\
         \x20 \"kernel_confirmed\": {}\n\
         }}\n",
        json_escape(&repro_path.to_string_lossy()),
        json_escape(&rep.fn_name),
        json_escape(&rep.verdict),
        json_escape(&rep.diag_tag),
        json_escape(&rep.diag_repr),
        rep.kernel_confirmed,
    );
    if let Some(out) = output_json {
        write_json_output(out, &json);
    }
    print!("{json}");
    Ok(())
}

fn main() {
    let args = match parse_cli_args() {
        Ok(a) => a,
        Err(e) => {
            eprintln!("error: {e}");
            std::process::exit(2);
        }
    };

    if let Some(ref repro_path) = args.reproduce {
        if let Err(e) = run_reproducer(repro_path, args.output_json.as_deref()) {
            eprintln!("error: {e}");
            std::process::exit(1);
        }
        return;
    }

    let (mode, batches, eff_batch_size) = if args.identity {
        let id_batch = generate_itree_identity_batch(ITREE_SAFE_SEEDS);
        let len = id_batch.len();
        ("identity", vec![id_batch], len)
    } else {
        let generated: Vec<Vec<GeneratedItreeCandidate>> = (0..args.batches)
            .map(|b_idx| {
                let batch_seed = args
                    .seed
                    .wrapping_add((b_idx as u64).wrapping_mul(0x9E37_79B9_7F4A_7C15));
                generate_itree_batch(ITREE_SAFE_SEEDS, args.batch_size, batch_seed)
            })
            .collect();
        ("seeded", generated, args.batch_size)
    };

    if args.compile_only {
        run_compile_only(&args, &batches);
        return;
    }

    let options = ItreeEvalOptions {
        trials_per_candidate: args.trials,
        anneal_repo_root: default_repo_root(),
        findings_dir: args.findings_dir.clone(),
        mir_mutations: Vec::new(),
        root_mir_swaps: Vec::new(),
    };
    let eval_report = match evaluate_itree_batches_with_options(
        mode,
        args.seed,
        &batches,
        eff_batch_size,
        &options,
    ) {
        Ok(r) => r,
        Err(e) => {
            eprintln!("error: {e}");
            std::process::exit(1);
        }
    };

    let json_report = render_itree_eval_report_json(&eval_report);
    if let Some(ref out_path) = args.output_json {
        write_json_output(out_path, &json_report);
    }

    let md_report = render_itree_eval_report_markdown(&eval_report);
    print!("{md_report}");
}
