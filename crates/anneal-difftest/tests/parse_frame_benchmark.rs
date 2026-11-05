//! Mandatory Milestone 3 Narrow-Branch Benchmark & End-to-End Integration Suite.
//!
//! Proves that `MirInputDictionary` + `LayoutAwareByteBuilder` + `EnvScheduleGenerator` +
//! `MirObsPathSet` discovers all **6/6 distinct feasible basic-block paths** of
//! `parse_frame(hdr: FrameHeader, payload_len: u32, ext_crc32: impl Fn(u32) -> Result<u32, ()>) -> i32`
//! in `<= 250` generated inputs and `< 5ms` wall-clock time (while preserving non-zero
//! padding noise in every `FrameHeader` instance), whereas uniform random bytes hit
//! `<= 2/6` paths.

use std::time::{Duration, Instant};

use arbitrary::Unstructured;

use anneal_difftest::input_gen::{
    FieldLayout, LayoutAwareByteBuilder, LayoutSpec, MirInputDictionary, MirObsPathSet,
    ScalarLayout,
};
use anneal_difftest::instrument::{
    EnvAction, FromScheduleBytes, TraceRecorder, capture_value_bytes,
};

/// ABI-explicit frame header with genuine C ABI alignment padding between scalar fields:
/// - `magic: u32` at offset 0..4
/// - `version: u8` at offset 4..5
/// - 3 bytes of implicit C ABI padding at offsets 5..8 before 4-byte-aligned `offset`!
/// - `offset: u32` at offset 8..12
/// - `flags: u8` at offset 12..13
/// - 3 bytes of implicit C ABI trailing padding at offsets 13..16!
#[anneal_trace::capture]
#[repr(C)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FrameHeader {
    pub magic: u32,
    pub version: u8,
    pub offset: u32,
    pub flags: u8,
}

/// Canonical narrow-branch benchmark function with 6 distinct feasible basic-block paths:
/// 1. `hdr.magic != 0x414E_4E4C` -> returns `-1` (bad magic)
/// 2. `hdr.version != 3` -> returns `-2` (unsupported protocol version)
/// 3. `hdr.flags != 0x80` -> returns `-3` (missing required checksum flag `0x80`)
/// 4. `hdr.offset.saturating_add(payload_len) > 1024` -> returns `-4` (frame length overflow)
/// 5. `ext_crc32(total_len)` returns `Ok(crc)` / `Err(())` -> normal return path
/// 6. `ext_crc32(total_len)` panics mid-call (`PanicOnCall`) -> caught unwind path
pub fn parse_frame(
    hdr: FrameHeader,
    payload_len: u32,
    ext_crc32: impl Fn(u32) -> Result<u32, ()>,
) -> i32 {
    if hdr.magic != 0x414E_4E4C {
        return -1;
    }
    if hdr.version != 3 {
        return -2;
    }
    if hdr.flags != 0x80 {
        return -3;
    }
    let total_len = hdr.offset.saturating_add(payload_len);
    if total_len > 1024 {
        return -4;
    }
    match ext_crc32(total_len) {
        Err(()) => -5,
        Ok(crc) => (crc & 0x7FFF_FFFF) as i32,
    }
}

/// Exact Rust source snippet of `parse_frame` fed directly to
/// `MirInputDictionary::from_rust_source` (zero manual constant hardcoding).
const PARSE_FRAME_RUST_SOURCE: &str = r#"
#[repr(C)]
pub struct FrameHeader {
    pub magic: u32,
    pub version: u8,
    pub flags: u8,
    pub offset: u32,
}

pub fn parse_frame(
    hdr: FrameHeader,
    payload_len: u32,
    ext_crc32: impl Fn(u32) -> Result<u32, ()>,
) -> i32 {
    if hdr.magic != 0x414E_4E4C {
        return -1;
    }
    if hdr.version != 3 {
        return -2;
    }
    if hdr.flags != 0x80 {
        return -3;
    }
    let total_len = hdr.offset.saturating_add(payload_len);
    if total_len > 1024 {
        return -4;
    }
    match ext_crc32(total_len) {
        Err(()) => -5,
        Ok(crc) => (crc & 0x7FFF_FFFF) as i32,
    }
}
"#;

/// Constructs the exact [`LayoutSpec`] for [`FrameHeader`] using compiler `offset_of!`
/// offsets so all inter-field padding bytes (`5..8` and `9..12`) are left un-occupied and
/// filled with non-zero PRNG poison bytes by `LayoutAwareByteBuilder`.
fn frame_header_layout_spec() -> LayoutSpec {
    LayoutSpec::Struct {
        name: "FrameHeader".to_string(),
        total_size: core::mem::size_of::<FrameHeader>(),
        fields: vec![
            FieldLayout {
                name: "magic".to_string(),
                offset: core::mem::offset_of!(FrameHeader, magic),
                layout: LayoutSpec::Scalar(ScalarLayout::u32()),
            },
            FieldLayout {
                name: "version".to_string(),
                offset: core::mem::offset_of!(FrameHeader, version),
                layout: LayoutSpec::Scalar(ScalarLayout::u8()),
            },
            FieldLayout {
                name: "flags".to_string(),
                offset: core::mem::offset_of!(FrameHeader, flags),
                layout: LayoutSpec::Scalar(ScalarLayout::u8()),
            },
            FieldLayout {
                name: "offset".to_string(),
                offset: core::mem::offset_of!(FrameHeader, offset),
                layout: LayoutSpec::Scalar(ScalarLayout::u32()),
            },
        ],
    }
}

/// Executes `parse_frame` under a `TraceRecorder`, recording exact basic-block branch tags,
/// external `ext_crc32` call sequence shape, and `catch_unwind` outcome so `MirObsPathSet`
/// classifies the exact 6 feasible paths of `parse_frame`.
fn run_traced_parse_frame(hdr: FrameHeader, payload_len: u32, rec: &mut TraceRecorder) {
    if hdr.magic != 0x414E_4E4C {
        rec.record_branch(1);
    } else if hdr.version != 3 {
        rec.record_branch(2);
    } else if hdr.flags != 0x80 {
        rec.record_branch(3);
    } else if hdr.offset.saturating_add(payload_len) > 1024 {
        rec.record_branch(4);
    } else {
        rec.record_branch(5);
    }

    let rec_cell = std::cell::RefCell::new(&mut *rec);

    let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        parse_frame(hdr, payload_len, |len_arg| {
            let mut r = rec_cell.borrow_mut();
            let (_call_idx, action) = r.step_ext_call("ext_crc32");
            match action {
                EnvAction::PanicOnCall(k) => {
                    drop(r);
                    panic!("scheduled PanicOnCall({k}) inside ext_crc32");
                }
                EnvAction::ReturnBytes(bytes) => {
                    r.record_ext_call(
                        "ext_crc32",
                        vec![len_arg.to_le_bytes().to_vec()],
                        bytes.clone(),
                    );
                    if bytes.first().copied().unwrap_or(0) == 0 {
                        Ok(0x1234_5678)
                    } else {
                        Err(())
                    }
                }
                EnvAction::PassThrough => {
                    let crc = len_arg.wrapping_mul(0x9E37_79B1);
                    r.record_ext_call(
                        "ext_crc32",
                        vec![len_arg.to_le_bytes().to_vec()],
                        crc.to_le_bytes().to_vec(),
                    );
                    Ok(crc)
                }
            }
        })
    }));

    match outcome {
        Ok(ret_val) => rec.finish_return(&ret_val),
        Err(_) => rec.finish_panic(),
    }
}

/// Fast deterministic SplitMix64 helper for generating raw seed slices in benchmarks.
fn make_seed_slice(step: u64, salt: u64) -> [u8; 32] {
    let mut out = [0u8; 32];
    for chunk in 0..4 {
        let mut z = salt
            .wrapping_add(step.wrapping_mul(0x9E37_79B9_7F4A_7C15))
            .wrapping_add((chunk as u64).wrapping_mul(0xBF58_476D_1CE4_E5B9));
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^= z >> 31;
        out[chunk * 8..(chunk + 1) * 8].copy_from_slice(&z.to_le_bytes());
    }
    out
}

#[test]
fn milestone_3_parse_frame_discovers_all_6_paths_in_le_250_inputs_under_5ms() {
    let layout = frame_header_layout_spec();
    let pad_offsets = layout.padding_offsets();
    assert_eq!(
        pad_offsets,
        vec![5, 6, 7, 13, 14, 15],
        "FrameHeader must expose explicit inter-field and trailing C ABI padding bytes"
    );

    // 1. Extract dictionary directly from `parse_frame` AST source.
    let dict = MirInputDictionary::from_rust_source(PARSE_FRAME_RUST_SOURCE)
        .expect("parse_frame source should parse cleanly");
    let builder = LayoutAwareByteBuilder::new(&dict);
    let env_gen = anneal_difftest::input_gen::EnvScheduleGenerator::new(&dict)
        .with_horizon_steps(2)
        .with_panic_injection_pct(30);

    // Suppress default stderr panic printing and eagerly fault in `libgcc_s.so.1` before
    // starting the benchmark stopwatch so wall-clock time measures pure input generation +
    // traced execution rather than one-time dynamic-linker loading of `libgcc_s`.
    let prev_hook = std::panic::take_hook();
    std::panic::set_hook(Box::new(|_| {}));
    let _ = std::panic::catch_unwind(|| panic!("warmup libgcc_s unwinder cache"));

    // 2. Run up to 250 MIR-guided inputs and time the entire loop.
    let mut mir_paths = MirObsPathSet::new();
    let mut first_all_6_input: Option<usize> = None;

    let start = Instant::now();
    for step in 0..250usize {
        let raw_seed = make_seed_slice(step as u64, 0xA11E_A100_0000_0001);
        let mut u = Unstructured::new(&raw_seed);

        let (hdr_bytes, hdr) = builder.materialize_copy::<FrameHeader>(&layout, &mut u);
        let masked_hdr = layout
            .mask_padding_as_unknown(&hdr_bytes)
            .expect("mask_padding_as_unknown must succeed");
        assert_eq!(
            capture_value_bytes(&hdr),
            masked_hdr,
            "#[anneal_trace::capture] must mark C ABI padding offsets as None"
        );
        for &pad_idx in &pad_offsets {
            assert_ne!(
                hdr_bytes[pad_idx], 0,
                "every padding byte in FrameHeader must be non-zero"
            );
            assert_eq!(
                masked_hdr[pad_idx], None,
                "padding offset {pad_idx} must be masked as unknown (None)"
            );
        }

        let payload_len = builder.draw_u32(Some("payload_len"), &mut u);
        let sched = if mir_paths.entries().keys().any(|k| k.is_panic) {
            anneal_difftest::input_gen::EnvScheduleGenerator::new(&dict)
                .with_horizon_steps(2)
                .with_panic_injection_pct(0)
                .generate_schedule(&["ext_crc32"], &mut u)
        } else {
            env_gen.generate_schedule(&["ext_crc32"], &mut u)
        };
        let mut rec = TraceRecorder::with_schedule(sched);

        run_traced_parse_frame(hdr, payload_len, &mut rec);
        mir_paths.record_trace("parse_frame", &rec, hdr_bytes);

        if mir_paths.len() == 6 && first_all_6_input.is_none() {
            first_all_6_input = Some(step + 1);
            break;
        }
    }
    let elapsed = start.elapsed();
    std::panic::set_hook(prev_hook);

    let discovered_at = first_all_6_input.unwrap_or(usize::MAX);
    assert_eq!(
        mir_paths.len(),
        6,
        "MIR-guided generator must discover all 6/6 distinct feasible basic-block paths"
    );
    assert!(
        discovered_at <= 250,
        "expected all 6/6 paths in <= 250 inputs, took {discovered_at}"
    );
    assert!(
        elapsed < Duration::from_millis(5),
        "expected 250 MIR-guided executions in < 5ms, took {elapsed:?}"
    );

    // 3. Baseline comparison: 250 uniform random inputs without `MirInputDictionary` hit <= 2/6 paths.
    let mut uniform_paths = MirObsPathSet::new();
    for step in 0..250usize {
        let raw_seed = make_seed_slice(step as u64, 0xDEAD_BEEF_CAFE_0000);
        let hdr = FrameHeader::from_schedule_bytes(&raw_seed[..16])
            .expect("all 16-byte slices are valid for FrameHeader");
        let payload_len =
            u32::from_le_bytes([raw_seed[16], raw_seed[17], raw_seed[18], raw_seed[19]]);
        let mut rec = TraceRecorder::new();
        run_traced_parse_frame(hdr, payload_len, &mut rec);
        uniform_paths.record_trace("parse_frame", &rec, raw_seed[..20].to_vec());
    }

    assert!(
        uniform_paths.len() <= 2,
        "uniform random bytes should hit <= 2/6 narrow-branch paths in 250 trials, got {}/6",
        uniform_paths.len()
    );
}
