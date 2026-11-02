#![cfg_attr(not(test), no_std)]
//! Curated 30-function seed corpus for Anneal ITree trace differential testing (`tests/itree-diff/`).
//!
//! Organized into 6 categories (5 functions per category = 30 functions):
//! 1. Multi-argument scalar & bitwise functions (`cat1_*`)
//! 2. Structs, tuples & enums with inter-field padding (`cat2_*`)
//! 3. Branching & loop CFGs (`switchInt` + `mirObsErasedStatefulTree`) (`cat3_*`)
//! 4. Single & multi-step external calls (`MirCallE` continuations) (`cat4_*`)
//! 5. Metamorphic inlining duality (`inlinedCallees` vs. `MirCallE`) (`cat5_*`)
//! 6. References, pointers & `ShadowProvenanceTable` metadata (`cat6_*`)

// ============================================================================
// Shared types & helper / external callees
// ============================================================================

#[repr(C)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PaddedHeader {
    pub tag: u8,
    // 3 bytes of implicit C ABI padding at offsets 1..4 before `len`
    pub len: u32,
}

#[repr(C)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct NestedPair {
    pub flag: u8,
    // 3 bytes padding
    pub left: u32,
    pub right: u32,
}

#[repr(u8)]
#[allow(dead_code)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DispatchMode {
    Add = 0,
    Sub = 1,
    Xor = 2,
    SelectLeft = 3,
}

#[repr(C)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct MaybeU32 {
    pub is_some: bool,
    // 3 bytes padding
    pub val: u32,
}

#[repr(C)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct OutcomeU16 {
    pub is_ok: bool,
    // 1 byte padding
    pub ok_val: u16,
    pub err_code: u16,
}

#[inline(never)]
pub fn ext_transform_u32(v: u32) -> u32 {
    v * 3 + 7
}

#[inline(never)]
pub fn ext_combine_u32(a: u32, b: u32) -> u32 {
    a + (b * 5)
}

#[inline(never)]
pub fn ext_may_panic_u32(trigger: u32, x: u32) -> u32 {
    if trigger == 0xDEAD {
        panic!("simulated external callee panic");
    }
    x + trigger
}

#[inline(never)]
pub fn helper_add_const(x: u32, c: u32) -> u32 {
    x + c
}

#[inline(never)]
pub fn helper_xor_fold(a: u32, b: u32) -> u32 {
    (a ^ b) + (a & 0xFF)
}

#[inline(never)]
pub fn helper_step_counter(cur: u32, delta: u32) -> u32 {
    (cur + delta) * 2
}

#[inline(never)]
pub fn helper_depth_step(n: u32, acc: u32) -> u32 {
    if n == 0 {
        acc
    } else {
        acc + (n * 4)
    }
}

// ============================================================================
// Category 1: Multi-argument scalar & bitwise functions (5 functions)
// ============================================================================

#[inline(never)]
pub fn clamp_u32_range(x: u32, lo: u32, hi: u32) -> u32 {
    if x < lo {
        lo
    } else if x > hi {
        hi
    } else {
        x
    }
}

#[inline(never)]
pub fn rotate_xor_mix(a: u32, b: u32, shift: u32) -> u32 {
    let s = shift & 7;
    let mixed = a ^ b;
    mixed.wrapping_shl(s) | mixed.wrapping_shr(32u32.wrapping_sub(s) & 31)
}

#[inline(never)]
pub fn checked_affine_step(x: u32, scale: u32, bias: u32) -> u32 {
    let prod = x.wrapping_mul(scale);
    if prod > u32::MAX.wrapping_sub(bias) {
        u32::MAX
    } else {
        prod.wrapping_add(bias)
    }
}

#[inline(never)]
pub fn signed_abs_diff(a: i32, b: i32) -> u32 {
    if a >= b {
        (a as u32).wrapping_sub(b as u32)
    } else {
        (b as u32).wrapping_sub(a as u32)
    }
}

#[inline(never)]
pub fn bitfield_extract(word: u32, offset: u32, mask: u32) -> u32 {
    let safe_off = offset & 15;
    (word.wrapping_shr(safe_off)) & mask
}

// ============================================================================
// Category 2: Structs, tuples & enums with inter-field padding (5 functions)
// ============================================================================

#[inline(never)]
pub fn repr_c_padded_header(hdr: PaddedHeader, bonus: u32) -> u32 {
    if hdr.tag == 1 {
        hdr.len + bonus
    } else {
        hdr.len ^ bonus
    }
}

#[inline(never)]
pub fn nested_tuple_struct_sum(pair: NestedPair, scale: u32) -> u32 {
    let base = pair.left.wrapping_add(pair.right);
    if pair.flag != 0 {
        base.wrapping_mul(scale)
    } else {
        base
    }
}

#[inline(never)]
pub fn c_like_enum_dispatch(mode: DispatchMode, x: u32, y: u32) -> u32 {
    match mode {
        DispatchMode::Add => x.wrapping_add(y),
        DispatchMode::Sub => x.wrapping_sub(y),
        DispatchMode::Xor => x ^ y,
        DispatchMode::SelectLeft => x,
    }
}

#[inline(never)]
pub fn option_u32_map_or(opt: MaybeU32, fallback: u32, addend: u32) -> u32 {
    if opt.is_some {
        opt.val.wrapping_add(addend)
    } else {
        fallback
    }
}

#[inline(never)]
pub fn result_u16_unwrap_or(res: OutcomeU16, default_val: u16) -> u16 {
    if res.is_ok {
        res.ok_val
    } else {
        res.err_code.wrapping_add(default_val)
    }
}

// ============================================================================
// Category 3: Branching & loop CFGs (`switchInt` + erased branches) (5 functions)
// ============================================================================

#[inline(never)]
pub fn match_four_way_tag(tag: u32, a: u32, b: u32) -> u32 {
    match tag {
        0 => a.wrapping_add(b),
        1 => a.wrapping_mul(2).wrapping_add(b),
        2 => b.wrapping_sub(a),
        _ => a ^ b ^ 0x55,
    }
}

#[inline(never)]
pub fn short_circuit_guard_chain(a: u32, b: u32, c: u32) -> u32 {
    if a > 0 && b > a && c > b {
        a.wrapping_add(b).wrapping_add(c)
    } else if a == 0 || b == 0 {
        c
    } else {
        b.wrapping_sub(a)
    }
}

#[inline(never)]
pub fn while_loop_accumulate(limit: u32, step: u32) -> u32 {
    let bounded = if limit > 6 { 6 } else { limit };
    let mut i = 0u32;
    let mut acc = 0u32;
    while i < bounded {
        acc = acc.wrapping_add(i.wrapping_mul(step));
        i = i.wrapping_add(1);
    }
    acc
}

#[inline(never)]
pub fn early_return_search_4(k0: u32, k1: u32, k2: u32, k3: u32, needle: u32) -> i32 {
    if k0 == needle {
        return 0;
    }
    if k1 == needle {
        return 1;
    }
    if k2 == needle {
        return 2;
    }
    if k3 == needle {
        return 3;
    }
    -1
}

#[inline(never)]
pub fn nested_if_else_matrix(row: u32, col: u32, val: u32) -> u32 {
    if row < 2 {
        if col < 2 {
            val.wrapping_add(10)
        } else {
            val.wrapping_add(20)
        }
    } else if col < 2 {
        val.wrapping_add(30)
    } else {
        val.wrapping_add(40)
    }
}

// ============================================================================
// Category 4: Single & multi-step external calls (`MirCallE`) (5 functions)
// ============================================================================

#[inline(never)]
pub fn call_once_and_postprocess(x: u32, bias: u32) -> u32 {
    let raw = ext_transform_u32(x);
    raw + bias
}

#[inline(never)]
pub fn call_twice_sequential(x: u32, y: u32) -> u32 {
    let first = ext_transform_u32(x);
    let second = ext_transform_u32(first.wrapping_add(y));
    second
}

#[inline(never)]
pub fn call_in_branch_arms(sel: u32, x: u32, y: u32) -> u32 {
    if sel & 1 == 0 {
        ext_transform_u32(x)
    } else {
        ext_combine_u32(x, y)
    }
}

#[inline(never)]
pub fn call_in_bounded_loop_3x(seed: u32) -> u32 {
    let a = ext_transform_u32(seed);
    let b = ext_transform_u32(a);
    let c = ext_transform_u32(b);
    c
}

#[inline(never)]
pub fn callee_panic_unwind_recovery(trigger: u32, x: u32) -> u32 {
    let out = ext_may_panic_u32(trigger, x);
    out.wrapping_add(1)
}

// ============================================================================
// Category 5: Metamorphic Inlining Duality (`inlinedCallees` vs `MirCallE`) (5)
// ============================================================================

#[inline(never)]
pub fn pipeline_two_helpers(x: u32, y: u32) -> u32 {
    let stepped = helper_add_const(x, 12);
    helper_xor_fold(stepped, y)
}

#[inline(never)]
pub fn diamond_helper_dag(x: u32) -> u32 {
    let left = helper_add_const(x, 5);
    let right = helper_add_const(x, 9);
    helper_xor_fold(left, right)
}

#[inline(never)]
pub fn conditional_helper_dispatch(flag: u32, x: u32, y: u32) -> u32 {
    if flag == 0 {
        helper_add_const(x, y)
    } else {
        helper_xor_fold(x, y)
    }
}

#[inline(never)]
pub fn stateful_counter_pair(start: u32, delta: u32) -> u32 {
    let mid = helper_step_counter(start, delta);
    helper_step_counter(mid, delta.wrapping_add(1))
}

#[inline(never)]
pub fn recursive_depth_2_unroll(n: u32, acc: u32) -> u32 {
    let step1 = helper_depth_step(n, acc);
    let next_n = if n > 0 { n - 1 } else { 0 };
    helper_depth_step(next_n, step1)
}

// ============================================================================
// Category 6: References, slices & `ShadowProvenanceTable` pointers (5 fns)
// ============================================================================

#[inline(never)]
pub fn ref_u32_passthrough(r: &u32, addend: u32) -> u32 {
    (*r).wrapping_add(addend)
}

#[inline(never)]
pub fn pair_of_refs_select(choose_first: bool, a: &u32, b: &u32) -> u32 {
    if choose_first {
        *a
    } else {
        *b
    }
}

#[inline(never)]
pub fn struct_field_ref_project(hdr: &PaddedHeader) -> u32 {
    (hdr.tag as u32).wrapping_add(hdr.len)
}

#[inline(never)]
pub fn raw_const_ptr_identity(ptr: *const u32, _offset_val: u32) -> *const u32 {
    ptr
}

#[inline(never)]
pub fn slice_len_and_ptr_meta(first_elem: &u32, len: usize) -> usize {
    if len == 0 {
        0
    } else {
        (*first_elem as usize).wrapping_add(len)
    }
}

pub mod harvested;
