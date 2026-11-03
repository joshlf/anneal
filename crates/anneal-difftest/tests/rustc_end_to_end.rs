//! End-to-end live `rustc --edition=2024 --crate-type=lib -D warnings` verification
//! proving that Milestone 1 auto-instrumented modules, Milestone 4 Miri-strength AST
//! mutation candidates, and Milestone 5 `#![forbid(unsafe_code)]` ITree AST mutation
//! candidates all parse, typecheck, borrow-check, and compile with zero warnings.

use std::io::Write;
use std::process::{Command, Stdio};

fn assert_compiles_cleanly_with_rustc(label: &str, rust_source: &str) {
    let rustc_bin = std::env::var("RUSTC").unwrap_or_else(|_| "rustc".to_string());
    let tmp_dir = std::env::temp_dir().join(format!(
        "anneal_difftest_verify_{}_{}",
        std::process::id(),
        label
    ));
    let _ = std::fs::create_dir_all(&tmp_dir);
    let out_path = tmp_dir.join("libcheck.rlib");

    let mut child = Command::new(&rustc_bin)
        .args([
            "--edition=2024",
            "--crate-type=lib",
            "-D",
            "warnings",
            "-o",
        ])
        .arg(&out_path)
        .arg("-")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("failed to spawn rustc");

    if let Some(mut stdin) = child.stdin.take() {
        stdin
            .write_all(rust_source.as_bytes())
            .expect("failed to write source to rustc stdin");
    }

    let output = child.wait_with_output().expect("failed waiting for rustc");
    let _ = std::fs::remove_dir_all(&tmp_dir);

    assert!(
        output.status.success(),
        "`{label}` failed `rustc --edition=2024 -D warnings`:\n--- stderr ---\n{}\n--- source ---\n{}",
        String::from_utf8_lossy(&output.stderr),
        rust_source
    );
}

#[test]
fn milestone_1_4_5_generated_sources_compile_cleanly_under_rustc_with_zero_warnings() {
    let seed_program = r#"
pub fn ext_oracle(x: u32) -> u32 {
    x.wrapping_mul(1664525).wrapping_add(1013904223)
}

pub fn kernel_step(a: u32, b: u32) -> u32 {
    let acc: u32 = a.wrapping_add(b);
    if acc > 100 {
        ext_oracle(acc)
    } else {
        acc ^ 0x55AA_55AA
    }
}
"#;

    // 1. Verify Milestone 1 instrumented module compiles cleanly with `rustc -D warnings`.
    let instrumented =
        anneal_difftest::instrument_source(seed_program, "kernel_step", &["ext_oracle"])
            .expect("instrument_source should succeed");
    assert_compiles_cleanly_with_rustc("milestone_1_instrumented", &instrumented);

    // 2. Verify Milestone 4 Miri batch candidates compile cleanly with `rustc -D warnings`.
    let miri_batch =
        anneal_difftest::generate_miri_batch(&[seed_program], 6, 0x1122_3344_5566_7788);
    assert_eq!(miri_batch.len(), 6);
    for cand in &miri_batch {
        assert_compiles_cleanly_with_rustc(
            &format!("milestone_4_miri_{}", cand.id),
            &cand.source,
        );
    }

    // 3. Verify Milestone 5 ITree batch candidates compile cleanly with `#![forbid(unsafe_code)]`
    // and `rustc -D warnings`.
    let itree_batch =
        anneal_difftest::generate_itree_batch(&[seed_program], 6, 0x8877_6655_4433_2211);
    assert_eq!(itree_batch.len(), 6);
    for cand in &itree_batch {
        assert!(!anneal_difftest::contains_unsafe_token(&cand.source));
        let strict_safe_src = format!("#![forbid(unsafe_code)]\n{}", cand.source);
        assert_compiles_cleanly_with_rustc(
            &format!("milestone_5_itree_{}", cand.id),
            &strict_safe_src,
        );
    }
}
