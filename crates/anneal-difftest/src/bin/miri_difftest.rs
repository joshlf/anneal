// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! `miri-difftest`: generates Miri-oriented candidate programs and checks that
//! they compile.
//!
//! This binary does not run Miri, Anneal's Lean model, or the generated
//! programs. It therefore reports no verdicts, agreement rates, or divergences;
//! its JSON output states `"oracle_comparison": "not_performed"`, and the
//! campaign runner (`scripts/run_diff_test_campaign.py`) reports such a run as
//! not evaluated. The candidates take arguments and have no driver, so they
//! cannot be run under Miri as generated.

use std::collections::BTreeMap;
use std::env;
use std::fs;
use std::io::Write;
use std::path::PathBuf;
use std::process::{Command, Stdio};
use std::time::Instant;

use anneal_difftest::mutators_miri::{GeneratedMiriCandidate, generate_miri_batch};

/// Seed programs that `generate_miri_batch` mutates.
const MIRI_SEED_CORPUS: &[&str] = &[
    r#"
pub fn seed_arith_checksum(x: u32, y: u32) -> u32 {
    let sum: u32 = x.wrapping_add(y);
    let folded: u32 = (sum ^ 0x55AA_55AA).rotate_left(7);
    if folded == 0xDEAD_BEEF {
        folded.wrapping_sub(1)
    } else {
        folded
    }
}
"#,
    r#"
pub fn seed_signed_clamp(v: i32, bound: i32) -> i32 {
    let delta: i32 = v.wrapping_sub(bound);
    if delta < -1024 {
        -1024
    } else if delta > 1024 {
        1024
    } else {
        delta
    }
}
"#,
    r#"
pub fn seed_bitmask_window(word: u64, mask: u64) -> u64 {
    let masked: u64 = (word & mask) ^ 0x414E_4E4C_0000_0001u64;
    masked.wrapping_mul(3)
}
"#,
    r#"
pub fn seed_stride_index(idx: u32, stride: u32) -> u32 {
    let scaled: u32 = (idx & 0xFF).wrapping_mul(stride & 0x0F);
    scaled.wrapping_add(0x80)
}
"#,
];

/// Mutator families whose application counts are always reported, so that a
/// family that never fires shows up as zero rather than disappearing.
const MUTATOR_NAMES: [&str; 5] = [
    "ArithmeticCastMutator",
    "PlaceProjectionWrapper",
    "RawPtrOffsetMutator",
    "TreeBorrowsRetagInterleaver",
    "BitValidityTransmuteMutator",
];

/// CLI configuration for `miri-difftest`.
#[derive(Debug, Clone)]
struct MiriDiffTestArgs {
    batches: usize,
    batch_size: usize,
    seed: u64,
    output_json: Option<PathBuf>,
}

impl Default for MiriDiffTestArgs {
    fn default() -> Self {
        Self {
            batches: 2,
            batch_size: 16,
            seed: 0x5EED_0001,
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
            "--output-json" => {
                i += 1;
                let val = args.get(i).ok_or("--output-json requires a path")?;
                cfg.output_json = Some(PathBuf::from(val));
            }
            "--help" | "-h" => {
                println!(
                    "Usage: miri-difftest [--batches N] [--batch-size B] [--seed S] \
                     [--output-json PATH]\n\
                     Generates and compiles candidates only; runs no oracle."
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

/// Runs `rustc --edition=2024 --crate-type=lib` on an in-memory Rust source
/// string and reports whether it compiled.
fn compile_rust_snippet(label: &str, source: &str) -> bool {
    let rustc_bin = resolve_rustc_bin();
    let tmp_dir = env::temp_dir().join(format!(
        "anneal_miri_difftest_{}_{}",
        std::process::id(),
        label
    ));
    let _ = fs::create_dir_all(&tmp_dir);
    let out_path = tmp_dir.join("libmiri_check.rlib");

    let child_res = Command::new(&rustc_bin)
        .args(["--edition=2024", "--crate-type=lib", "-A", "warnings", "-o"])
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

/// Compiles every candidate, first as one combined crate and, if that fails,
/// one candidate at a time so that each failure is attributed to its
/// candidate.
fn compile_candidates(batches: &[Vec<GeneratedMiriCandidate>]) -> Vec<Vec<bool>> {
    let mut combined = String::new();
    for (b_idx, batch) in batches.iter().enumerate() {
        for (c_idx, cand) in batch.iter().enumerate() {
            combined.push_str(&format!(
                "#[allow(dead_code, unused_variables, unused_assignments)]\n\
                 pub mod b{b_idx}_c{c_idx} {{\n{}\n}}\n",
                cand.source
            ));
        }
    }
    if !combined.is_empty() && compile_rust_snippet("all_batches", &combined) {
        return batches.iter().map(|b| vec![true; b.len()]).collect();
    }
    batches
        .iter()
        .enumerate()
        .map(|(b_idx, batch)| {
            batch
                .iter()
                .enumerate()
                .map(|(c_idx, cand)| {
                    compile_rust_snippet(&format!("b{b_idx}_c{c_idx}"), &cand.source)
                })
                .collect()
        })
        .collect()
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

    let batches: Vec<Vec<GeneratedMiriCandidate>> = (0..args.batches)
        .map(|b_idx| {
            let batch_seed = args
                .seed
                .wrapping_add((b_idx as u64).wrapping_mul(0x9E37_79B9_7F4A_7C15));
            generate_miri_batch(MIRI_SEED_CORPUS, args.batch_size, batch_seed)
        })
        .collect();
    let total_candidates: usize = batches.iter().map(Vec::len).sum();

    let compile_results = compile_candidates(&batches);
    let compiled_count = compile_results.iter().flatten().filter(|&&ok| ok).count();

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
        (compiled_count as f64 / total_candidates as f64) * 100.0
    };

    let json_report = render_json(
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
        if let Some(parent) = out_path.parent()
            && !parent.as_os_str().is_empty()
        {
            let _ = fs::create_dir_all(parent);
        }
        fs::write(out_path, &json_report).expect("failed to write --output-json file");
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
