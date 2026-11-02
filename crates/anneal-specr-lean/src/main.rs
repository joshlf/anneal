//! CLI entrypoint for `anneal-specr-lean`: generates Lean 4 snapshot modules
//! (`Generated/SpecIndex.lean` + `snapshot-lock.json`), verifies SHA-256 lockfiles,
//! and computes structural declaration-level diffs between upstream MiniRust snapshots.

use std::env;
use std::path::{Path, PathBuf};
use std::process::ExitCode;

use anneal_specr_lean::ast_diff::diff_snapshots;
use anneal_specr_lean::extractor::{
    extract_snapshot, parse_upstream_lock_toml, verify_upstream_lock,
};
use anneal_specr_lean::lean_emit::{emit_snapshot_to_dir, verify_snapshot_lock};
use anneal_specr_lean::type_env::TypeEnvironment;

fn main() -> ExitCode {
    let args: Vec<String> = env::args().skip(1).collect();
    match run(&args) {
        Ok(()) => ExitCode::SUCCESS,
        Err(msg) => {
            eprintln!("error: {msg}");
            ExitCode::FAILURE
        }
    }
}

fn run(args: &[String]) -> Result<(), String> {
    let cmd = args.first().map_or("generate-all", String::as_str);
    match cmd {
        "generate-all" => {
            let repo_root = flag_value(args, "--repo-root")
                .map_or_else(|| PathBuf::from("."), PathBuf::from);
            generate_all_from_lock(&repo_root)
        }
        "verify-lock" => {
            let repo_root = flag_value(args, "--repo-root")
                .map_or_else(|| PathBuf::from("."), PathBuf::from);
            let lock_path = repo_root.join("theory/MiniRust/upstream-minirust.lock.toml");
            let verified = verify_upstream_lock(&lock_path, &repo_root)?;
            for v in &verified {
                println!(
                    "verified upstream lock: {} @ {} ({} files, {} bytes)",
                    v.snapshot_id, v.git_sha, v.verified_file_count, v.total_verified_bytes
                );
            }
            let raw_lock = std::fs::read_to_string(&lock_path)
                .map_err(|e| format!("failed reading {}: {e}", lock_path.display()))?;
            let lock = parse_upstream_lock_toml(&raw_lock)?;
            for snap in &lock.snapshots {
                let snap_dir = repo_root.join(&snap.generated_dir);
                let vendor_dir = repo_root.join(&snap.vendor_dir);
                let sv = verify_snapshot_lock(&snap_dir, &vendor_dir)?;
                println!(
                    "verified snapshot-lock.json: {} ({} inputs, {} outputs, {} declarations)",
                    sv.snapshot_id,
                    sv.verified_input_files,
                    sv.verified_output_files,
                    sv.declaration_count
                );
            }
            Ok(())
        }
        "diff" => {
            let old_dir = flag_value(args, "--old")
                .ok_or_else(|| "missing --old <vendor-dir>".to_string())?;
            let new_dir = flag_value(args, "--new")
                .ok_or_else(|| "missing --new <vendor-dir>".to_string())?;
            let old_id = flag_value(args, "--old-id").unwrap_or_else(|| "old".to_string());
            let new_id = flag_value(args, "--new-id").unwrap_or_else(|| "new".to_string());
            let old_sha = flag_value(args, "--old-sha")
                .unwrap_or_else(|| "0000000000000000000000000000000000000000".to_string());
            let new_sha = flag_value(args, "--new-sha")
                .unwrap_or_else(|| "1111111111111111111111111111111111111111".to_string());

            let old_snap = extract_snapshot(Path::new(&old_dir), &old_id, &old_sha)?;
            let new_snap = extract_snapshot(Path::new(&new_dir), &new_id, &new_sha)?;
            let old_env = TypeEnvironment::build(&old_snap);
            let new_env = TypeEnvironment::build(&new_snap);
            let report = diff_snapshots(&old_env, &new_env);
            print!("{}", report.render_markdown_report());
            Ok(())
        }
        other => Err(format!(
            "unknown subcommand `{other}` (expected `generate-all`, `verify-lock`, or `diff`)"
        )),
    }
}

fn generate_all_from_lock(repo_root: &Path) -> Result<(), String> {
    let lock_path = repo_root.join("theory/MiniRust/upstream-minirust.lock.toml");
    let raw_lock = std::fs::read_to_string(&lock_path)
        .map_err(|e| format!("failed reading {}: {e}", lock_path.display()))?;
    let lock = parse_upstream_lock_toml(&raw_lock)?;

    for snap_cfg in &lock.snapshots {
        let vendor_dir = repo_root.join(&snap_cfg.vendor_dir);
        let gen_dir = repo_root.join(&snap_cfg.generated_dir);
        let extracted = extract_snapshot(&vendor_dir, &snap_cfg.id, &snap_cfg.git_sha)?;
        let env = TypeEnvironment::build(&extracted);
        let emitted = emit_snapshot_to_dir(&extracted, &env, &gen_dir)?;
        let verified = verify_snapshot_lock(&gen_dir, &vendor_dir)?;
        println!(
            "generated {}: {} chapters, {} blocks, {} declarations -> {} (sha256: {}) [verified {} inputs]",
            emitted.snapshot_id,
            emitted.chapter_count,
            emitted.block_count,
            emitted.declaration_count,
            emitted.spec_index_lean_path.display(),
            &emitted.spec_index_sha256[..16],
            verified.verified_input_files
        );
    }

    Ok(())
}

fn flag_value(args: &[String], flag: &str) -> Option<String> {
    let mut iter = args.iter();
    while let Some(a) = iter.next() {
        if a == flag {
            return iter.next().cloned();
        }
        if let Some(rest) = a.strip_prefix(&format!("{flag}=")) {
            return Some(rest.to_string());
        }
    }
    None
}
