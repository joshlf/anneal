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

/// Detailed summary of a deterministic mutator-chain delta-debugging (`ddmin`) run.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MutationChainShrinkOutcome<T> {
    /// Original sequence of mutation steps passed to the shrinker.
    pub original_steps: Vec<T>,
    /// Minimized 1-minimal subsequence satisfying the failure predicate.
    pub minimized_steps: Vec<T>,
    /// Total number of predicate evaluations performed during minimization.
    pub predicate_evaluations: usize,
    /// `true` iff `predicate(&initial_steps)` held on the initial input and every
    /// accepted reduction step.
    pub succeeded: bool,
    /// `true` iff `succeeded` is `true` and deleting any single element from
    /// `minimized_steps` falsifies `predicate`. The shrinker only terminates after a
    /// complete single-deletion sweep over `minimized_steps` in which every deletion was
    /// rejected (the single-element case relies on the initial `predicate(&[])` check),
    /// so this holds for every deterministic `predicate`; with a nondeterministic oracle
    /// it holds relative to the answers the oracle actually gave.
    pub is_one_minimal: bool,
}

impl<T> MutationChainShrinkOutcome<T> {
    /// Fraction of mutation steps removed in `[0.0, 1.0]`.
    pub fn reduction_ratio(&self) -> f64 {
        if self.original_steps.is_empty() {
            0.0
        } else {
            1.0 - (self.minimized_steps.len() as f64 / self.original_steps.len() as f64)
        }
    }
}

/// Deterministically delta-debugs a sequence of AST or environment-schedule mutation
/// steps `initial_steps` down to a 1-minimal subsequence that still satisfies `predicate`,
/// returning full diagnostic metadata ([`MutationChainShrinkOutcome`]).
///
/// The shrinker runs `ddmin` with chunk sizes `len / 2` down to `1`. Whenever a deletion
/// succeeds at `chunk_size == 1` and at least 2 steps remain, `chunk_size` is reset to
/// `best.len().div_ceil(2)` so coupled multi-step dependencies unlocked by an earlier
/// single-step deletion are also eliminated before final 1-minimality verification.
pub fn shrink_mutation_chain_detailed<T: Clone, F>(
    initial_steps: &[T],
    mut predicate: F,
) -> MutationChainShrinkOutcome<T>
where
    F: FnMut(&[T]) -> bool,
{
    let mut evals = 1usize;
    if !predicate(initial_steps) {
        return MutationChainShrinkOutcome {
            original_steps: initial_steps.to_vec(),
            minimized_steps: initial_steps.to_vec(),
            predicate_evaluations: evals,
            succeeded: false,
            is_one_minimal: false,
        };
    }

    if initial_steps.is_empty() {
        return MutationChainShrinkOutcome {
            original_steps: Vec::new(),
            minimized_steps: Vec::new(),
            predicate_evaluations: evals,
            succeeded: true,
            is_one_minimal: true,
        };
    }

    evals += 1;
    if predicate(&[]) {
        return MutationChainShrinkOutcome {
            original_steps: initial_steps.to_vec(),
            minimized_steps: Vec::new(),
            predicate_evaluations: evals,
            succeeded: true,
            is_one_minimal: true,
        };
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
            evals += 1;
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
            if best.len() >= 2 {
                chunk_size = best.len().div_ceil(2);
            }
        } else {
            chunk_size = chunk_size.div_ceil(2).min(best.len().div_ceil(2)).max(1);
        }
    }

    MutationChainShrinkOutcome {
        original_steps: initial_steps.to_vec(),
        minimized_steps: best,
        predicate_evaluations: evals,
        succeeded: true,
        is_one_minimal: true,
    }
}

/// Deterministically delta-debugs a sequence of AST or environment-schedule mutation
/// steps `initial_steps` down to a 1-minimal subsequence that still satisfies `predicate`.
pub fn shrink_mutation_chain<T: Clone, F>(initial_steps: &[T], predicate: F) -> Vec<T>
where
    F: FnMut(&[T]) -> bool,
{
    shrink_mutation_chain_detailed(initial_steps, predicate).minimized_steps
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
        let outcome = shrink_mutation_chain_detailed(&steps, |subset| {
            subset.contains(&"trigger_part_a") && subset.contains(&"trigger_part_b")
        });
        assert!(outcome.succeeded);
        assert!(outcome.is_one_minimal);
        assert_eq!(outcome.minimized_steps, vec!["trigger_part_a", "trigger_part_b"]);
        assert!(outcome.reduction_ratio() >= 0.70);
    }

    #[test]
    fn shrink_mutation_chain_detailed_handles_empty_false_root_and_coupled_steps() {
        // 1. Empty input with true predicate.
        let empty_ok: MutationChainShrinkOutcome<&str> =
            shrink_mutation_chain_detailed(&[], |_| true);
        assert!(empty_ok.succeeded);
        assert!(empty_ok.is_one_minimal);
        assert!(empty_ok.minimized_steps.is_empty());
        assert_eq!(empty_ok.predicate_evaluations, 1);

        // 2. Non-empty input where initial predicate is false.
        let init_false = shrink_mutation_chain_detailed(&["M1", "M2"], |_| false);
        assert!(!init_false.succeeded);
        assert!(!init_false.is_one_minimal);
        assert_eq!(init_false.minimized_steps, vec!["M1", "M2"]);
        assert_eq!(init_false.predicate_evaluations, 1);

        // 3. Non-empty input where unmutated seed `&[]` already satisfies predicate.
        let root_faults = shrink_mutation_chain_detailed(&["M1", "M2", "M3"], |_| true);
        assert!(root_faults.succeeded);
        assert!(root_faults.is_one_minimal);
        assert!(root_faults.minimized_steps.is_empty());
        assert_eq!(root_faults.predicate_evaluations, 2);

        // 4. Single-element chain where `&[]` does not satisfy predicate.
        let single = shrink_mutation_chain_detailed(&["M1"], |s| s == ["M1"]);
        assert!(single.succeeded);
        assert!(single.is_one_minimal);
        assert_eq!(single.minimized_steps, vec!["M1"]);
        assert_eq!(single.predicate_evaluations, 2);

        // 5. Tag-sensitive pair `[M1, M4]`: `[M1]` alone produces `"panic"` instead of
        // `"missed_ub"`, while `[M1, M4]` produces `"missed_ub"`.
        let eval_tag = |s: &[&str]| -> Option<&'static str> {
            if s.contains(&"M1") && s.contains(&"M4") {
                Some("missed_ub")
            } else if s.contains(&"M1") {
                Some("panic")
            } else {
                None
            }
        };
        let tag_outcome = shrink_mutation_chain_detailed(
            &["M0", "M1", "M2", "M3", "M4", "M5"],
            |s| eval_tag(s) == Some("missed_ub"),
        );
        assert!(tag_outcome.succeeded);
        assert!(tag_outcome.is_one_minimal);
        assert_eq!(tag_outcome.minimized_steps, vec!["M1", "M4"]);

        // 6. Coupled AST dependency: `M2` references a binding introduced by `M1`
        // (so `M2` without `M1` fails compilation, and `M1` without `M2` fails a check),
        // while `M4` is the real divergence trigger. Chunk deletion (`chunk_size = 2`)
        // removes the coupled pair `[M1, M2]` together and isolates `["M4"]`.
        let coupled = shrink_mutation_chain_detailed(&["M1", "M2", "M3", "M4"], |s| {
            let has_m1 = s.contains(&"M1");
            let has_m2 = s.contains(&"M2");
            let compiles = has_m1 == has_m2;
            compiles && s.contains(&"M4")
        });
        assert!(coupled.succeeded);
        assert!(coupled.is_one_minimal);
        assert_eq!(coupled.minimized_steps, vec!["M4"]);
    }

    /// Mirrors `ddminReference_globally_minimal_of_monotone`: for monotone "every trigger
    /// step is present" predicates the 1-minimal result is the trigger set itself, i.e.
    /// globally minimal among all subsequences (600 random trigger sets, lengths `0..=10`).
    #[test]
    fn shrink_mutation_chain_detailed_is_globally_minimal_for_monotone_predicates() {
        let mut seed = 0x0DDB_A11u64;
        for trial in 0..600usize {
            seed = splitmix64(seed);
            let n = trial % 11;
            let steps: Vec<usize> = (0..n).collect();
            let required: Vec<usize> =
                steps.iter().copied().filter(|i| (seed >> i) & 1 == 1).collect();
            let out =
                shrink_mutation_chain_detailed(&steps, |s| required.iter().all(|r| s.contains(r)));
            assert!(out.succeeded && out.is_one_minimal, "trial {trial}");
            assert_eq!(out.minimized_steps, required, "trial {trial}: not globally minimal");
        }
    }

    /// Mirrors `coupled_window_one_minimal_not_globally_minimal` and
    /// `coupled_window_ddmin_reaches_smaller_witness`: the predicate holds exactly on
    /// `[1, 2, 3]` and `[3]`, so `[1, 2, 3]` is already 1-minimal, yet the chunk phase
    /// deletes the coupled window `[1, 2]` at `chunk_size == 2` and reaches `[3]`.
    #[test]
    fn ddmin_chunk_phase_reaches_witness_below_single_step_local_minimum() {
        let pred = |s: &[u32]| s == [1, 2, 3] || s == [3];
        for i in 0..3 {
            let mut deleted = vec![1u32, 2, 3];
            deleted.remove(i);
            assert!(!pred(&deleted), "[1, 2, 3] must be 1-minimal");
        }
        let out = shrink_mutation_chain_detailed(&[1u32, 2, 3], pred);
        assert_eq!(out.minimized_steps, vec![3]);
        assert!(out.succeeded && out.is_one_minimal);
    }

    fn splitmix64(mut z: u64) -> u64 {
        z = z.wrapping_add(0x9E37_79B9_7F4A_7C15);
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }

    /// Transliteration of the Lean `windowDelete` (`theory/Anneal/DiffTestShrinkerPrototype.lean`).
    fn lean_window_delete(xs: &[usize], pos: usize, chunk: usize) -> Vec<usize> {
        let stop = (pos + chunk).min(xs.len());
        xs[..pos.min(xs.len())]
            .iter()
            .chain(xs[stop.max(pos.min(xs.len()))..].iter())
            .copied()
            .collect()
    }

    /// Transliteration of the Lean `ddminSweep` (same fuel discipline).
    fn lean_ddmin_sweep(
        pred: &mut dyn FnMut(&[usize]) -> bool,
        chunk: usize,
        fuel: usize,
        best: Vec<usize>,
        pos: usize,
        improved: bool,
    ) -> Option<(Vec<usize>, bool)> {
        if fuel == 0 {
            return None;
        }
        if pos < best.len() {
            if (pos + chunk).min(best.len()) - pos == best.len() {
                Some((best, improved))
            } else {
                let cand = lean_window_delete(&best, pos, chunk);
                if pred(&cand) {
                    lean_ddmin_sweep(pred, chunk, fuel - 1, cand, pos, true)
                } else {
                    lean_ddmin_sweep(pred, chunk, fuel - 1, best, pos + 1, improved)
                }
            }
        } else {
            Some((best, improved))
        }
    }

    /// Transliteration of the Lean `ddminNextChunk`.
    fn lean_ddmin_next_chunk(chunk: usize, best: &[usize]) -> usize {
        if chunk == 1 {
            if 2 <= best.len() { best.len().div_ceil(2) } else { 1 }
        } else {
            1.max(chunk.div_ceil(2).min(best.len().div_ceil(2)))
        }
    }

    /// Transliteration of the Lean `ddminLoop`.
    fn lean_ddmin_loop(
        pred: &mut dyn FnMut(&[usize]) -> bool,
        fuel: usize,
        best: Vec<usize>,
        chunk: usize,
    ) -> Option<Vec<usize>> {
        if fuel == 0 {
            return None;
        }
        let sweep_fuel = 2 * best.len() + 1;
        let (best2, improved) = lean_ddmin_sweep(pred, chunk, sweep_fuel, best, 0, false)?;
        if chunk == 1 && !improved {
            Some(best2)
        } else {
            let next = lean_ddmin_next_chunk(chunk, &best2);
            lean_ddmin_loop(pred, fuel - 1, best2, next)
        }
    }

    /// Transliteration of the Lean `ddminReference`.
    fn lean_ddmin_reference(
        pred: &mut dyn FnMut(&[usize]) -> bool,
        fuel: usize,
        xs: &[usize],
    ) -> Option<Vec<usize>> {
        if pred(xs) {
            if xs.is_empty() {
                Some(Vec::new())
            } else if pred(&[]) {
                Some(Vec::new())
            } else {
                lean_ddmin_loop(pred, fuel, xs.to_vec(), xs.len().div_ceil(2))
            }
        } else {
            None
        }
    }

    /// Ties `shrink_mutation_chain_detailed` to the Lean reference model whose results are
    /// proved 1-minimal (`ddminReference_one_minimal`) and which provably answers with the
    /// fuel used here (`ddminReference_total`): on 1200 arbitrary deterministic predicates
    /// both make exactly the same predicate calls, in the same order, and return the same
    /// chain.
    #[test]
    fn shrink_mutation_chain_detailed_matches_lean_ddmin_reference_call_for_call() {
        let mut seed = 0x1357_9BDF_2468_ACE0u64;
        for trial in 0..1200usize {
            seed = splitmix64(seed);
            let n = trial % 10;
            let steps: Vec<usize> = (0..n).collect();
            let full_mask = (1u64 << n) - 1;
            let salt = seed;
            let modulus = 2 + (seed >> 60) % 4;
            let initial_true = trial % 13 != 0;
            let truth = move |sub: &[usize]| -> bool {
                let mask = sub.iter().fold(0u64, |m, &i| m | (1u64 << i));
                if mask == full_mask {
                    return initial_true;
                }
                splitmix64(mask ^ salt) % modulus == 0
            };

            let mut impl_calls: Vec<Vec<usize>> = Vec::new();
            let outcome = shrink_mutation_chain_detailed(&steps, |s| {
                impl_calls.push(s.to_vec());
                truth(s)
            });

            let mut model_calls: Vec<Vec<usize>> = Vec::new();
            // Fuel strictly above the `ddminReference_total` bound `n * (n + 1) + ⌈n / 2⌉`.
            let fuel = n * (n + 1) + n.div_ceil(2) + 1;
            let mut model_pred = |s: &[usize]| {
                model_calls.push(s.to_vec());
                truth(s)
            };
            let model = lean_ddmin_reference(&mut model_pred, fuel, &steps);

            assert_eq!(impl_calls, model_calls, "trial {trial}: predicate call sequence");
            assert_eq!(outcome.predicate_evaluations, model_calls.len(), "trial {trial}");
            match model {
                None => {
                    assert!(!initial_true, "trial {trial}: model ran out of fuel");
                    assert!(!outcome.succeeded, "trial {trial}");
                }
                Some(chain) => {
                    assert!(outcome.succeeded && outcome.is_one_minimal, "trial {trial}");
                    assert_eq!(outcome.minimized_steps, chain, "trial {trial}: result");
                }
            }
        }
    }

    /// Differential check of `shrink_mutation_chain_detailed` against a brute-force
    /// 1-minimality oracle over 1200 arbitrary (non-monotone) deterministic predicates on
    /// chains of length `0..=9`. Steps are the distinct indices `0..n`, so a result is a
    /// subsequence of the input iff it is strictly increasing.
    #[test]
    fn shrink_mutation_chain_detailed_is_one_minimal_for_arbitrary_deterministic_predicates() {
        let mut seed = 0x243F_6A88_85A3_08D3u64;
        let mut minimized_strictly = 0usize;
        for trial in 0..1200usize {
            seed = splitmix64(seed);
            let n = trial % 10;
            let steps: Vec<usize> = (0..n).collect();
            let full_mask = (1u64 << n) - 1;
            let salt = seed;
            let modulus = 2 + (seed >> 60) % 4;
            let initial_true = trial % 11 != 0;
            // Truth table over the set of kept original indices; arbitrary, so neither
            // monotone nor anti-monotone.
            let truth = |sub: &[usize]| -> bool {
                let mask = sub.iter().fold(0u64, |m, &i| m | (1u64 << i));
                if mask == full_mask {
                    return initial_true;
                }
                splitmix64(mask ^ salt) % modulus == 0
            };

            let mut calls = 0usize;
            let out = shrink_mutation_chain_detailed(&steps, |s| {
                calls += 1;
                truth(s)
            });

            assert_eq!(out.predicate_evaluations, calls, "trial {trial}: evaluation count");
            assert_eq!(out.original_steps, steps, "trial {trial}: original steps");
            if !initial_true {
                assert!(!out.succeeded && !out.is_one_minimal, "trial {trial}");
                assert_eq!(out.minimized_steps, steps, "trial {trial}");
                assert_eq!(calls, 1, "trial {trial}: only the initial check may run");
                continue;
            }
            assert!(out.succeeded && out.is_one_minimal, "trial {trial}");
            assert!(
                out.minimized_steps.windows(2).all(|w| w[0] < w[1])
                    && out.minimized_steps.iter().all(|&i| i < n),
                "trial {trial}: {:?} is not a subsequence of 0..{n}",
                out.minimized_steps
            );
            assert!(truth(&out.minimized_steps), "trial {trial}: predicate not preserved");
            for i in 0..out.minimized_steps.len() {
                let mut deleted = out.minimized_steps.clone();
                deleted.remove(i);
                assert!(
                    !truth(&deleted),
                    "trial {trial}: deleting index {i} of {:?} still satisfies the predicate",
                    out.minimized_steps
                );
            }
            if out.minimized_steps.len() < n {
                minimized_strictly += 1;
            }
            if out.minimized_steps.len() <= 2 {
                // Mirror `ddminLoop_one_eq_some_of_isOneMinimal`: on any 1-minimal chain
                // of length <= 2 (where the initial chunk size is `len.div_ceil(2) == 1`),
                // re-running `shrink_mutation_chain_detailed` is strictly idempotent.
                let rerun = shrink_mutation_chain_detailed(&out.minimized_steps, &truth);
                assert!(rerun.succeeded && rerun.is_one_minimal, "trial {trial}: rerun");
                assert_eq!(
                    rerun.minimized_steps, out.minimized_steps,
                    "trial {trial}: 1-minimal chain of len <= 2 must be a fixed point"
                );
            }
        }
        assert!(minimized_strictly > 500, "only {minimized_strictly} trials shrank");
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
