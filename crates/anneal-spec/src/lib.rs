//! User-facing specification annotations for Anneal (`#[spec]`,
//! `#[embed_spec]`, `#[external_spec]`, `#[model]`, `#[invariant]`,
//! `#[unsafe_trait]`, and `#[unsafe_impl]`).
//!
//! This crate re-exports the `anodized` specification runtime and logic modules
//! at the crate root alongside [`anneal_spec_macros`] so that synthetic
//! companion items (`__anodized_fn_requires_*`, `__anodized_fn_ensures_*`,
//! `__anodized_fn_qualifiers_*`, `__anneal_type_invariant_*`, and
//! `__anneal_unsafe_impl_*`) resolve when a crate brings `anneal_spec::*`
//! into scope or links `anodized` directly (`#103` §3.2).

pub use anodized::{self, __, arithmetic, logic, result, types};
pub use anneal_spec_macros::{
    embed_spec, external_spec, invariant, model, spec, unsafe_impl, unsafe_trait,
};

#[cfg(test)]
mod tests {
    use crate::*;

    #[model]
    fn ghost_bounded_inc(x: u32, step: u32) -> u64 {
        (x as u64) + (step as u64)
    }

    #[embed_spec(
        pure,
        total,
        requires: [x < 1_000, step <= 10],
        maintains: x >= 1,
        captures: [old_x = x, old_step = step],
        ensures: |out| [
            out == old_x + old_step,
            (out as u64) == ghost_bounded_inc(old_x, old_step),
        ],
    )]
    fn add_bounded(x: u32, step: u32) -> u32 {
        x + step
    }

    #[spec(
        pure,
        terminating,
        requires: n <= 20,
        ensures: |sum| sum >= n,
    )]
    fn triangle_sum(n: u32) -> u32 {
        let mut i = 0u32;
        let mut acc = 0u32;
        #[embed_spec(maintains: i <= n, decreases: n - i)]
        while i < n {
            i += 1;
            acc += i;
        }
        acc
    }

    #[external_spec(
        for = core::num::Wrapping,
        pure,
        total,
        requires: x < 100,
        ensures: |ret| ret.0 == x,
    )]
    fn spec_wrapping_u32(x: u32) -> core::num::Wrapping<u32>;

    #[external_spec(
        target = u32::wrapping_add,
        pure,
        total,
        requires: [a < 500, b < 500],
        captures: [init_a = a, init_b = b],
        ensures: |ret| ret == init_a + init_b,
    )]
    fn spec_u32_wrapping_add(a: u32, b: u32) -> u32 {
        unreachable!()
    }

    #[test]
    fn embed_spec_companions_evaluate_contracts_and_qualifiers() {
        assert_eq!(add_bounded(10, 5), 15);

        // `pure` (1 | 2 = 3) and `total` (4 | 8 = 12) combine to bitmask 15.
        assert_eq!(__anodized_fn_qualifiers_add_bounded, 15);

        assert!(__anodized_fn_requires_add_bounded(10, 5));
        assert!(!__anodized_fn_requires_add_bounded(0, 5));
        assert!(!__anodized_fn_requires_add_bounded(1_000, 5));
        assert!(!__anodized_fn_requires_add_bounded(10, 11));

        assert!(__anodized_fn_ensures_add_bounded(10, 5, 15));
        assert!(!__anodized_fn_ensures_add_bounded(10, 5, 14));
        assert!(!__anodized_fn_ensures_add_bounded(0, 5, 5));
    }

    #[test]
    fn spec_alias_and_loop_annotations_emit_companions() {
        assert_eq!(triangle_sum(4), 10);
        assert_ne!(__anodized_fn_qualifiers_triangle_sum, 0);
        assert!(__anodized_fn_requires_triangle_sum(4));
        assert!(!__anodized_fn_requires_triangle_sum(21));
        assert!(__anodized_fn_ensures_triangle_sum(4, 10));
        assert!(!__anodized_fn_ensures_triangle_sum(4, 3));
    }

    #[test]
    fn external_spec_emits_target_marker_and_callable_companions() {
        assert_eq!(
            __ANNEAL_EXT_SPEC_TARGET_spec_wrapping_u32,
            "core::num::Wrapping"
        );
        assert_eq!(__anodized_fn_qualifiers_spec_wrapping_u32, 15);
        assert!(__anodized_fn_requires_spec_wrapping_u32(42));
        assert!(!__anodized_fn_requires_spec_wrapping_u32(100));
        assert!(__anodized_fn_ensures_spec_wrapping_u32(
            42,
            core::num::Wrapping(42)
        ));
        assert!(!__anodized_fn_ensures_spec_wrapping_u32(
            42,
            core::num::Wrapping(43)
        ));

        assert_eq!(
            __ANNEAL_EXT_SPEC_TARGET_spec_u32_wrapping_add,
            "u32::wrapping_add"
        );
        assert!(__anodized_fn_requires_spec_u32_wrapping_add(100, 200));
        assert!(!__anodized_fn_requires_spec_u32_wrapping_add(500, 200));
        assert!(__anodized_fn_ensures_spec_u32_wrapping_add(100, 200, 300));
        assert!(!__anodized_fn_ensures_spec_u32_wrapping_add(100, 200, 301));
    }

    #[test]
    fn model_attribute_emits_marker_constant() {
        assert_eq!(__ANNEAL_MODEL_ghost_bounded_inc, "ghost_bounded_inc");
        assert_eq!(ghost_bounded_inc(10, 5), 15);
    }

    #[invariant(self.low <= self.high, self.high < 10_000)]
    struct BoundedRange {
        low: u32,
        high: u32,
    }

    #[invariant(match self { Self::Empty => true, Self::NonEmpty(n) => *n > 0 })]
    enum CountState {
        Empty,
        NonEmpty(u32),
    }

    #[unsafe_trait]
    #[allow(dead_code)]
    pub unsafe trait SafeByteRepr {}

    #[unsafe_impl(
        requires: core::mem::size_of::<BoundedRange>() == 8,
        ensures: |ok| ok,
    )]
    unsafe impl SafeByteRepr for BoundedRange {}

    #[test]
    fn invariant_and_unsafe_impl_companions_evaluate_correctly() {
        let valid_range = BoundedRange { low: 10, high: 20 };
        let invalid_range = BoundedRange { low: 30, high: 20 };
        assert!(valid_range.__anneal_type_invariant_bounded_range());
        assert!(!invalid_range.__anneal_type_invariant_bounded_range());

        let valid_enum = CountState::NonEmpty(5);
        let invalid_enum = CountState::NonEmpty(0);
        assert!(CountState::Empty.__anneal_type_invariant_count_state());
        assert!(valid_enum.__anneal_type_invariant_count_state());
        assert!(!invalid_enum.__anneal_type_invariant_count_state());

        assert!(__anneal_unsafe_impl_SafeByteRepr_for_BoundedRange());
        assert!(__anodized_fn_requires___anneal_unsafe_impl_SafeByteRepr_for_BoundedRange());
        assert!(__anodized_fn_ensures___anneal_unsafe_impl_SafeByteRepr_for_BoundedRange(true));
        assert!(!__anodized_fn_ensures___anneal_unsafe_impl_SafeByteRepr_for_BoundedRange(false));
    }
}
