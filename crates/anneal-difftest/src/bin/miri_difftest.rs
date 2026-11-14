// Copyright 2026 The Fuchsia Authors
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0>, the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, or the BSD-2-Clause
// license <LICENSE-BSD or https://opensource.org/license/bsd-2-clause>, at your
// option. This file may not be copied, modified, or distributed except
// according to those terms.

//! `miri-difftest`: generates closed, zero-argument Miri candidates from the
//! `tests/miri-diff/corpus` seed suite, compiles them with `rustc`, evaluates
//! them through the shared Miri + Anneal oracle pipeline
//! (`cargo_anneal::run_difftest_oracle_pipeline`), and emits JSON/Markdown
//! coverage reports plus self-contained divergence finding bundles.

use std::collections::BTreeMap;
use std::env;
use std::fs;
use std::path::{Path, PathBuf};
use std::time::Instant;

use anneal_difftest::miri_eval::{
    MIRI_MUTATOR_NAMES, classify_verdict_witness_polarity, compile_candidates,
    divergence_class_slug, evaluate_miri_batches, json_escape, render_eval_report_json,
    render_eval_report_markdown, reproduce_miri_finding,
};
use anneal_difftest::mutators_miri::{
    GeneratedMiriCandidate, generate_miri_corpus_batch, generate_miri_identity_batch,
};
use cargo_anneal::ComparisonVerdict;

/// CLI configuration for `miri-difftest`.
#[derive(Debug, Clone)]
struct MiriDiffTestArgs {
    batches: usize,
    batch_size: usize,
    seed: u64,
    identity: bool,
    compile_only: bool,
    findings_dir: Option<PathBuf>,
    output_json: Option<PathBuf>,
    reproduce: Option<PathBuf>,
}

impl Default for MiriDiffTestArgs {
    fn default() -> Self {
        Self {
            batches: 2,
            batch_size: 16,
            seed: 0x5EED_0001,
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

fn parse_cli_args() -> Result<MiriDiffTestArgs, String> {
    let mut cfg = MiriDiffTestArgs::default();
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
                let val = args.get(i).ok_or("--reproduce requires a path to repro.rs")?;
                cfg.reproduce = Some(PathBuf::from(val));
            }
            "--help" | "-h" => {
                println!(
                    "Usage: miri-difftest [--batches N] [--batch-size B] [--seed S] \
                     [--identity] [--findings-dir DIR] [--output-json PATH] \
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
        && (cfg.batches == 0 || cfg.batch_size == 0)
    {
        return Err(
            "--batches and --batch-size must be at least 1 when running oracle comparison"
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

fn run_compile_only(args: &MiriDiffTestArgs, batches: &[Vec<GeneratedMiriCandidate>]) {
    let start = Instant::now();
    let total_candidates: usize = batches.iter().map(Vec::len).sum();
    let compile_results = compile_candidates(batches);
    let compiled_count = compile_results.iter().flatten().filter(|&&ok| ok).count();

    let mut mutator_counts: BTreeMap<String, usize> = MIRI_MUTATOR_NAMES
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
        (compiled_count as f64 / total_candidates as f64) * 100.0
    };

    let json_report = render_compile_only_json(
        &[
            ("harness", "\"miri-difftest\"".to_string()),
            ("oracle_comparison", "\"not_performed\"".to_string()),
            ("seed", format!("\"0x{:08x}\"", args.seed)),
            ("batches", args.batches.to_string()),
            ("batch_size", args.batch_size.to_string()),
            ("total_candidates", total_candidates.to_string()),
            ("compiled_candidates", compiled_count.to_string()),
            ("compile_pass_rate_pct", format!("{compile_rate_pct:.2}")),
            ("elapsed_ms", format!("{elapsed_ms:.2}")),
        ],
        &mutator_counts,
    );

    if let Some(ref out_path) = args.output_json {
        write_json_output(out_path, &json_report);
    }

    println!("# `miri-difftest` candidate generation report\n");
    println!(
        "- **Oracle comparison**: NOT PERFORMED. This binary does not run Miri, \
         Anneal's Lean model, or the generated programs."
    );
    println!(
        "- **Seed**: `0x{:08x}` (`{}` batches × `{}` candidates = `{}` generated)",
        args.seed, args.batches, args.batch_size, total_candidates
    );
    println!(
        "- **Compiled with `rustc --edition=2024 --crate-type=lib`**: `{}/{}` ({:.2}%)",
        compiled_count, total_candidates, compile_rate_pct
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
    let item_rep = reproduce_miri_finding(repro_path, repo_root.as_deref())?;
    let (verdict_tag, div_class) = match &item_rep.verdict {
        ComparisonVerdict::Agree => ("agree".to_string(), None),
        ComparisonVerdict::Diverge(kind) => (
            "diverge".to_string(),
            Some(divergence_class_slug(kind).to_string()),
        ),
        ComparisonVerdict::NotCompared(reason) => (format!("not_compared:{reason:?}"), None),
    };
    let witness_polarity =
        classify_verdict_witness_polarity(&item_rep.miri, &item_rep.anneal, &item_rep.verdict)
            .map(|p| p.as_str().to_string());
    let miri_tag = item_rep.miri.summary_tag();
    let anneal_tag = item_rep.anneal.summary_tag();
    let anneal_lean = item_rep
        .anneal
        .to_lean_mir_diff_tag()
        .unwrap_or_else(|| "none".to_string());
    let json = format!(
        "{{\n\
         \x20 \"reproducer\": {},\n\
         \x20 \"fn_name\": {},\n\
         \x20 \"verdict\": {},\n\
         \x20 \"divergence_class\": {},\n\
         \x20 \"witness_polarity\": {},\n\
         \x20 \"miri_outcome\": {},\n\
         \x20 \"anneal_outcome\": {},\n\
         \x20 \"anneal_lean_tag\": {},\n\
         \x20 \"kernel_confirmed\": {}\n\
         }}\n",
        json_escape(&repro_path.to_string_lossy()),
        json_escape(&item_rep.name),
        json_escape(&verdict_tag),
        div_class
            .as_ref()
            .map(|c| json_escape(c))
            .unwrap_or_else(|| "null".to_string()),
        witness_polarity
            .as_ref()
            .map(|p| json_escape(p))
            .unwrap_or_else(|| "null".to_string()),
        json_escape(&miri_tag),
        json_escape(&anneal_tag),
        json_escape(&anneal_lean),
        item_rep.kernel_confirmed,
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
        let id_batch = generate_miri_identity_batch();
        let len = id_batch.len();
        ("identity", vec![id_batch], len)
    } else {
        let generated: Vec<Vec<GeneratedMiriCandidate>> = (0..args.batches)
            .map(|b_idx| {
                let batch_seed = args
                    .seed
                    .wrapping_add((b_idx as u64).wrapping_mul(0x9E37_79B9_7F4A_7C15));
                generate_miri_corpus_batch(args.batch_size, batch_seed, b_idx)
            })
            .collect();
        ("seeded", generated, args.batch_size)
    };

    if args.compile_only {
        run_compile_only(&args, &batches);
        return;
    }

    let repo_root = default_repo_root();
    let eval_report = match evaluate_miri_batches(
        mode,
        args.seed,
        &batches,
        eff_batch_size,
        args.findings_dir.as_deref(),
        repo_root.as_deref(),
    ) {
        Ok(r) => r,
        Err(e) => {
            eprintln!("error: {e}");
            std::process::exit(1);
        }
    };

    let json_report = render_eval_report_json(&eval_report);
    if let Some(ref out_path) = args.output_json {
        write_json_output(out_path, &json_report);
    }

    let md_report = render_eval_report_markdown(&eval_report);
    print!("{md_report}");
}
