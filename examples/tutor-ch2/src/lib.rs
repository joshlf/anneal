use anneal_spec::*;

pub const fn magic_version() -> u32 {
    1
}

#[anneal_spec::spec(
    requires: magic == 7,
    ensures: |ref ret| *ret == 7,
)]
pub fn pin_magic(magic: u32) -> u32 {
    magic
}

#[anneal_spec::spec(
    requires: header_len == 1 && payload_len == 2,
    ensures: |ref ret| *ret == 3,
)]
pub fn total_frame_len(header_len: u8, payload_len: u8) -> u8 {
    header_len + payload_len
}

#[anneal_spec::spec(
    requires: offset < 4,
    ensures: |ref ret| *ret == offset + 4,
)]
pub fn advance_offset(offset: u8) -> u8 {
    offset + 4
}

#[anneal_spec::model]
pub const fn is_valid_version(v: u8) -> bool {
    v == 1
}

#[anneal_spec::invariant(self.0 <= 64)]
pub struct FrameLen(pub u8);
