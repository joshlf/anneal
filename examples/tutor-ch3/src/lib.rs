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
