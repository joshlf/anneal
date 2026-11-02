//! Deterministic byte-prefix, chunk-deletion (ddmin), byte-magnitude, and mutation-chain
//! counterexample minimizer built on `arbitrary::Unstructured` and `arbtest`.

use std::sync::{Arc, Mutex};

use arbitrary::Unstructured;

/// Summary of a deterministic counterexample minimization run.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ShrinkOutcome {
    /// Original failing byte slice passed to the shrinker.
    pub original_bytes: Vec<u8>,
    /// Minimal failing byte slice satisfying the failure predicate.
    pub minimized_bytes: Vec<u8>,
    /// Original byte length before minimization.
    pub original_len: usize,
    /// Final minimized byte length after minimization.
    pub minimized_len: usize,
    /// Total number of predicate evaluations performed during minimization.
    pub predicate_evaluations: usize,
    /// `true` iff `predicate(&minimized_bytes)` held on the initial input and every
    /// accepted reduction step.
    pub succeeded: bool,
}

impl ShrinkOutcome {
    /// Fraction of bytes removed in `[0.0, 1.0]`.
    pub fn reduction_ratio(&self) -> f64 {
        if self.original_len == 0 {
            0.0
        } else {
            1.0 - (self.minimized_len as f64 / self.original_len as f64)
        }
    }
}

/// Deterministically minimizes a raw byte counterexample `initial` while preserving
/// `predicate(&candidate) == true`.
///
/// Executes three complementary deterministic passes tailored to `arbitrary::Unstructured`:
/// 1. Binary search for the shortest failing prefix `initial[..len]`.
/// 2. Delta-debugging (`ddmin`) contiguous chunk deletion (`chunk = len/2, len/4, ..., 1`).
/// 3. Per-byte lexicographic value reduction toward `0` (`0`, `b / 2`, `b - 1`).
pub fn shrink_bytes<F>(initial: &[u8], mut predicate: F) -> ShrinkOutcome
where
    F: FnMut(&[u8]) -> bool,
{
    let mut evals = 1usize;
    if !predicate(initial) {
        return ShrinkOutcome {
            original_bytes: initial.to_vec(),
            minimized_bytes: initial.to_vec(),
            original_len: initial.len(),
            minimized_len: initial.len(),
            predicate_evaluations: evals,
            succeeded: false,
        };
    }

    let mut best = initial.to_vec();

    // Pass 1: Binary search on prefix truncation (matches `Unstructured` front-to-back reads).
    if !best.is_empty() {
        evals += 1;
        if predicate(&[]) {
            best.clear();
        } else {
            let mut lo = 1usize;
            let mut hi = best.len();
            while lo < hi {
                let mid = lo + (hi - lo) / 2;
                evals += 1;
                if predicate(&best[..mid]) {
                    hi = mid;
                } else {
                    lo = mid + 1;
                }
            }
            best.truncate(lo);
        }
    }

    // Pass 2: Exponential-to-single-byte delta-debugging (`ddmin`) chunk deletions.
    let mut chunk_size = best.len() / 2;
    while chunk_size >= 1 {
        let mut idx = 0usize;
        while idx + chunk_size <= best.len() {
            let mut candidate = Vec::with_capacity(best.len() - chunk_size);
            candidate.extend_from_slice(&best[..idx]);
            candidate.extend_from_slice(&best[idx + chunk_size..]);
            evals += 1;
            if predicate(&candidate) {
                best = candidate;
                // Keep `idx` fixed so adjacent chunks at the new offset are also tested.
            } else {
                idx += 1;
            }
        }
        if chunk_size == 1 {
            break;
        }
        chunk_size /= 2;
    }

    // Pass 3: Exact binary-search byte-magnitude simplification toward `0x00` per byte.
    for pos in 0..best.len() {
        let orig_byte = best[pos];
        if orig_byte == 0 {
            continue;
        }
        best[pos] = 0;
        evals += 1;
        if predicate(&best) {
            continue;
        }
        let mut lo = 1u8;
        let mut hi = orig_byte;
        while lo < hi {
            let mid = lo + (hi - lo) / 2;
            best[pos] = mid;
            evals += 1;
            if predicate(&best) {
                hi = mid;
            } else {
                lo = mid + 1;
            }
        }
        best[pos] = lo;
    }

    ShrinkOutcome {
        original_bytes: initial.to_vec(),
        minimized_len: best.len(),
        minimized_bytes: best,
        original_len: initial.len(),
        predicate_evaluations: evals,
        succeeded: true,
    }
}

/// Minimizes an `arbitrary::Unstructured`-backed counterexample given a typed builder
/// closure `build` and a failure oracle `is_failing`.
pub fn shrink_unstructured<T, G, F>(
    initial_bytes: &[u8],
    build: G,
    is_failing: F,
) -> ShrinkOutcome
where
    G: Fn(&mut Unstructured<'_>) -> arbitrary::Result<T>,
    F: Fn(&T) -> bool,
{
    shrink_bytes(initial_bytes, |raw| {
        let mut u = Unstructured::new(raw);
        match build(&mut u) {
            Ok(val) => is_failing(&val),
            Err(_) => false,
        }
    })
}

/// Deterministically delta-debugs a sequence of AST or environment-schedule mutation
/// steps `initial_steps` down to a 1-minimal subsequence that still satisfies `predicate`.
pub fn shrink_mutation_chain<T: Clone, F>(initial_steps: &[T], mut predicate: F) -> Vec<T>
where
    F: FnMut(&[T]) -> bool,
{
    if initial_steps.is_empty() || !predicate(initial_steps) {
        return initial_steps.to_vec();
    }

    if predicate(&[]) {
        return Vec::new();
    }

    let mut best = initial_steps.to_vec();
    let mut chunk_size = best.len().div_ceil(2);
    loop {
        let mut pos = 0usize;
        let mut improved = false;
        while pos < best.len() {
            let end = (pos + chunk_size).min(best.len());
            if end - pos == best.len() {
                break;
            }
            let mut candidate = Vec::with_capacity(best.len() - (end - pos));
            candidate.extend_from_slice(&best[..pos]);
            candidate.extend_from_slice(&best[end..]);
            if predicate(&candidate) {
                best = candidate;
                improved = true;
            } else {
                pos += 1;
            }
        }
        if chunk_size == 1 {
            if !improved {
                break;
            }
        } else {
            chunk_size = chunk_size.div_ceil(2);
        }
    }

    best
}

/// Runs `arbtest` with deterministic `seed` and budget `budget_ms` to search for any raw
/// `Unstructured` input buffer that satisfies `failure_predicate`, and automatically
/// shrinks the discovered counterexample to minimal form via [`shrink_bytes`].
pub fn run_arbtest_and_shrink<F>(
    seed: u64,
    budget_ms: u64,
    failure_predicate: F,
) -> Option<ShrinkOutcome>
where
    F: Fn(&[u8]) -> bool + Send + Sync + std::panic::RefUnwindSafe,
{
    let captured: Arc<Mutex<Option<Vec<u8>>>> = Arc::new(Mutex::new(None));
    let captured_slot = Arc::clone(&captured);

    // In `arbtest`, the low 32 bits of `seed` encode the initial byte-slice length!
    // Normalize the low 32 bits to `64` bytes so arbitrary 64-bit caller seeds never
    // request multi-gigabyte initial allocations.
    let arbtest_seed = (seed & 0xFFFF_FFFF_0000_0000) | 64;

    arbtest::arbtest(|u| {
        if let Ok(guard) = captured_slot.lock()
            && guard.is_some()
        {
            let _ = u.bytes(u.len());
            return Ok(());
        }
        let len = u.len();
        if len == 0 {
            return Ok(());
        }
        let raw = u.bytes(len)?.to_vec();
        if failure_predicate(&raw)
            && let Ok(mut guard) = captured_slot.lock()
            && guard.is_none()
        {
            *guard = Some(raw);
        }
        Ok(())
    })
    .size_min(8)
    .size_max(256)
    .seed(arbtest_seed)
    .budget_ms(budget_ms.clamp(1, 20));

    let found = captured.lock().ok().and_then(|mut g| g.take())?;
    Some(shrink_bytes(&found, &failure_predicate))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn shrink_bytes_finds_exact_minimal_counterexample() {
        let noisy = vec![
            0xFF, 0xEE, 0xDD, 0xAA, 0xBB, 0xCC, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66,
        ];
        // Failure triggers whenever the slice contains at least 3 bytes with sum >= 200.
        let outcome = shrink_bytes(&noisy, |b| {
            b.len() >= 3 && b.iter().map(|&x| x as u32).sum::<u32>() >= 200
        });
        assert!(outcome.succeeded);
        assert_eq!(outcome.minimized_len, 3);
        let sum: u32 = outcome.minimized_bytes.iter().map(|&x| x as u32).sum();
        assert_eq!(sum, 200);
        assert!(outcome.reduction_ratio() >= 0.70);
    }

    #[test]
    fn shrink_mutation_chain_isolates_minimal_faulty_subsequence() {
        let steps = vec![
            "nop_0",
            "nop_1",
            "trigger_part_a",
            "nop_2",
            "nop_3",
            "trigger_part_b",
            "nop_4",
        ];
        let minimal = shrink_mutation_chain(&steps, |subset| {
            subset.contains(&"trigger_part_a") && subset.contains(&"trigger_part_b")
        });
        assert_eq!(minimal, vec!["trigger_part_a", "trigger_part_b"]);
    }

    #[test]
    fn run_arbtest_and_shrink_discovers_and_shrinks_unstructured_bug() {
        let pred = |bytes: &[u8]| {
            let mut u = Unstructured::new(bytes);
            if let Ok(v) = u.arbitrary::<u16>() {
                v >= 1000
            } else {
                false
            }
        };
        let report = run_arbtest_and_shrink(0x1234_5678_9ABC_DEF0, 5, pred)
            .expect("arbtest should find u16 >= 1000 within 5ms");

        assert!(report.succeeded);
        assert!(pred(&report.minimized_bytes));
        assert!(report.minimized_len <= 2);
        // Verify strict 1-coordinate byte minimality: reducing any byte by 1 falsifies `pred`.
        for idx in 0..report.minimized_bytes.len() {
            if report.minimized_bytes[idx] > 0 {
                let mut smaller = report.minimized_bytes.clone();
                smaller[idx] -= 1;
                assert!(
                    !pred(&smaller),
                    "minimized counterexample must be strictly byte-minimal at index {idx}"
                );
            }
        }
    }
}
