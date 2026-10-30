//! Integration tests for `anneal-spec` and `anneal-spec-macros`.

use anneal_spec::*;

fn local_unowned_clamp(val: u32, lo: u32, hi: u32) -> u32 {
    if val < lo {
        lo
    } else if val > hi {
        hi
    } else {
        val
    }
}

#[model]
fn in_closed_range(x: u32, lo: u32, hi: u32) -> bool {
    lo <= x && x <= hi
}

#[model]
struct GhostPair(u32, u32);

#[embed_spec(
    pure,
    total,
    requires: [a <= 1_000, b <= 1_000],
    maintains: a <= b,
    captures: [orig_a = a, orig_b = b],
    ensures: |mid| [
        in_closed_range(mid, orig_a, orig_b),
        mid - orig_a <= orig_b - mid,
    ],
)]
fn midpoint(a: u32, b: u32) -> u32 {
    a + (b - a) / 2
}

#[external_spec(
    for = local_unowned_clamp,
    pure,
    total,
    requires: lo <= hi,
    captures: [bound_lo = lo, bound_hi = hi],
    ensures: |ret| in_closed_range(ret, bound_lo, bound_hi),
)]
fn spec_local_unowned_clamp(val: u32, lo: u32, hi: u32) -> u32;

#[external_spec(
    for = core::cmp::max,
    pure,
    total,
    ensures: |ret| [ret >= a, ret >= b, ret == a || ret == b],
)]
fn spec_core_cmp_max_u32(a: u32, b: u32) -> u32;

#[external_spec(
    for = <[u32]>::len,
    pure,
    total,
    requires: !slice.is_empty(),
    ensures: |len| len >= 1,
)]
fn spec_slice_u32_len(slice: &[u32]) -> usize;

struct Counter {
    value: u32,
    limit: u32,
}

#[embed_spec]
impl Counter {
    #[embed_spec(
        requires: self.value < self.limit,
        maintains: self.value <= self.limit,
        captures: prev = self.value,
        ensures: |out| out == prev + 1,
    )]
    fn step(&mut self) -> u32 {
        self.value += 1;
        self.value
    }
}

#[test]
fn integration_embed_spec_free_fn_and_impl_method() {
    assert_eq!(midpoint(10, 20), 15);
    assert_eq!(__anodized_fn_qualifiers_midpoint, 15);
    assert!(__anodized_fn_requires_midpoint(10, 20));
    assert!(!__anodized_fn_requires_midpoint(20, 10));
    assert!(__anodized_fn_ensures_midpoint(10, 20, 15));
    assert!(!__anodized_fn_ensures_midpoint(10, 20, 16));

    let mut counter = Counter {
        value: 2,
        limit: 5,
    };
    assert!(counter.__anodized_fn_requires_step());
    assert!(counter.__anodized_fn_ensures_step(3));
    assert!(!counter.__anodized_fn_ensures_step(4));
    assert_eq!(counter.step(), 3);
}

#[test]
fn integration_external_spec_local_and_stdlib_targets() {
    assert_eq!(local_unowned_clamp(50, 10, 30), 30);
    assert_eq!(
        __ANNEAL_EXT_SPEC_TARGET_spec_local_unowned_clamp,
        "local_unowned_clamp"
    );
    assert!(__anodized_fn_requires_spec_local_unowned_clamp(50, 10, 30));
    assert!(!__anodized_fn_requires_spec_local_unowned_clamp(50, 30, 10));
    assert!(__anodized_fn_ensures_spec_local_unowned_clamp(
        50, 10, 30, 30
    ));
    assert!(!__anodized_fn_ensures_spec_local_unowned_clamp(
        50, 10, 30, 35
    ));

    assert_eq!(
        __ANNEAL_EXT_SPEC_TARGET_spec_core_cmp_max_u32,
        "core::cmp::max"
    );
    assert!(__anodized_fn_requires_spec_core_cmp_max_u32(3, 9));
    assert!(__anodized_fn_ensures_spec_core_cmp_max_u32(3, 9, 9));
    assert!(!__anodized_fn_ensures_spec_core_cmp_max_u32(3, 9, 5));

    assert_eq!(
        __ANNEAL_EXT_SPEC_TARGET_spec_slice_u32_len,
        "<[u32]>::len"
    );
    assert!(__anodized_fn_requires_spec_slice_u32_len(&[1, 2, 3]));
    assert!(!__anodized_fn_requires_spec_slice_u32_len(&[]));
    assert!(__anodized_fn_ensures_spec_slice_u32_len(&[1, 2, 3], 3));
    assert!(!__anodized_fn_ensures_spec_slice_u32_len(&[1, 2, 3], 0));
}

#[test]
fn integration_model_markers_on_fn_and_type() {
    let pair = GhostPair(3, 7);
    assert!(in_closed_range(5, pair.0, pair.1));
    assert_eq!(__ANNEAL_MODEL_in_closed_range, "in_closed_range");
    assert_eq!(__ANNEAL_MODEL_GhostPair, "GhostPair");
}

#[invariant(self.0 > 0)]
struct NonZeroCounter(u32);

#[unsafe_trait]
unsafe trait TrustedNonZero {
    fn raw_val(&self) -> u32;
}

#[unsafe_impl(
    requires: core::mem::align_of::<NonZeroCounter>() >= 4,
    ensures: core::mem::size_of::<NonZeroCounter>() == 4,
)]
unsafe impl TrustedNonZero for NonZeroCounter {
    fn raw_val(&self) -> u32 {
        self.0
    }
}

#[test]
fn integration_invariant_and_unsafe_impl_attributes() {
    let good = NonZeroCounter(7);
    let bad = NonZeroCounter(0);
    assert!(good.__anneal_type_invariant_non_zero_counter());
    assert!(!bad.__anneal_type_invariant_non_zero_counter());
    assert_eq!(good.raw_val(), 7);
    assert!(__anneal_unsafe_impl_TrustedNonZero_for_NonZeroCounter());
    assert!(__anodized_fn_requires___anneal_unsafe_impl_TrustedNonZero_for_NonZeroCounter());
    assert!(__anodized_fn_ensures___anneal_unsafe_impl_TrustedNonZero_for_NonZeroCounter(true));
}
