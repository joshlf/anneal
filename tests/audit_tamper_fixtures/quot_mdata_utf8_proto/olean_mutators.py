# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Deterministic Lean 4.34.1 `.olean` / `.ir` compacted-region parser & mutators.

Used by the six-vector tamper test suite (`test_six_vectors.py`) to apply precise,
reproducible binary mutations to real Lean 4.34.1 compiled `.olean` and `.ir` files
for V-Q1, V-M2, V-U3, V-F4, and V-S5.
"""

from __future__ import annotations

from dataclasses import dataclass
import struct
from typing import Iterable


HEADER_SIZE = 88
LEAN_ARRAY_TAG = 246
LEAN_STRING_TAG = 249
LEAN_MPZ_TAG = 250


@dataclass(frozen=True)
class ObjHeader:
    ptr: int
    off: int
    rc: int
    cs_sz: int
    other: int
    tag: int


class OleanImage:
    """Mutable view of a Lean 4.34.1 single-part `.olean` or `.ir` compacted region."""

    def __init__(self, raw: bytes) -> None:
        if len(raw) < 96:
            raise ValueError(f"olean image too small: {len(raw)} bytes")
        if raw[:5] != b"olean" or raw[5] != 2:
            raise ValueError(f"unsupported olean header: {raw[:8]!r}")
        self.buf = bytearray(raw)
        self.base_addr: int = struct.unpack_from("<Q", self.buf, 80)[0]
        self.root_ptr: int = struct.unpack_from("<Q", self.buf, 88)[0]

    def clone(self) -> "OleanImage":
        return OleanImage(bytes(self.buf))

    def to_bytes(self) -> bytes:
        return bytes(self.buf)

    @staticmethod
    def is_scalar(word: int) -> bool:
        return (word & 1) == 1

    def ptr_to_off(self, ptr: int) -> int:
        if self.is_scalar(ptr):
            raise ValueError(f"expected heap pointer, got scalar {hex(ptr)}")
        off = ptr - self.base_addr
        if off < HEADER_SIZE + 8 or off + 8 > len(self.buf):
            raise ValueError(f"pointer {hex(ptr)} out of bounds (off={off}, len={len(self.buf)})")
        return off

    def read_u64(self, off: int) -> int:
        return struct.unpack_from("<Q", self.buf, off)[0]

    def write_u64(self, off: int, val: int) -> None:
        struct.pack_into("<Q", self.buf, off, val & 0xFFFFFFFFFFFFFFFF)

    def read_u32(self, off: int) -> int:
        return struct.unpack_from("<I", self.buf, off)[0]

    def write_u32(self, off: int, val: int) -> None:
        struct.pack_into("<I", self.buf, off, val & 0xFFFFFFFF)

    def read_header(self, ptr: int) -> ObjHeader:
        off = self.ptr_to_off(ptr)
        rc, cs_sz, other, tag = struct.unpack_from("<iHBB", self.buf, off)
        return ObjHeader(ptr=ptr, off=off, rc=rc, cs_sz=cs_sz, other=other, tag=tag)

    def read_field(self, hdr: ObjHeader, idx: int) -> int:
        if idx < 0 or idx >= hdr.other:
            raise IndexError(f"field {idx} out of range for m_other={hdr.other}")
        return self.read_u64(hdr.off + 8 + idx * 8)

    def read_array(self, ptr: int) -> list[int]:
        hdr = self.read_header(ptr)
        if hdr.tag != LEAN_ARRAY_TAG:
            raise ValueError(f"expected LeanArray (246), got tag {hdr.tag}")
        size = self.read_u64(hdr.off + 8)
        return [self.read_u64(hdr.off + 24 + i * 8) for i in range(size)]

    def read_string_raw(self, ptr: int) -> tuple[bytes, int, int, int]:
        """Returns `(payload_without_nul, m_size, m_capacity, m_length)`."""
        hdr = self.read_header(ptr)
        if hdr.tag != LEAN_STRING_TAG:
            raise ValueError(f"expected LeanString (249), got tag {hdr.tag}")
        m_size = self.read_u64(hdr.off + 8)
        m_cap = self.read_u64(hdr.off + 16)
        m_len = self.read_u64(hdr.off + 24)
        payload = bytes(self.buf[hdr.off + 32 : hdr.off + 32 + m_size - 1])
        return payload, m_size, m_cap, m_len

    def read_name(self, word: int) -> str:
        if self.is_scalar(word):
            return ""
        hdr = self.read_header(word)
        pre = self.read_field(hdr, 0)
        arg = self.read_field(hdr, 1)
        pre_s = self.read_name(pre)
        if hdr.tag == 1:
            raw, _, _, _ = self.read_string_raw(arg)
            part = raw.decode("utf-8", errors="replace")
        elif hdr.tag == 2:
            part = str(arg >> 1) if self.is_scalar(arg) else "<mpz>"
        else:
            raise ValueError(f"unexpected Name tag {hdr.tag}")
        return f"{pre_s}.{part}" if pre_s else part

    def module_constants(self) -> dict[str, int]:
        """Map declaration name -> `ConstantInfo` heap pointer from `ModuleData` root."""
        rh = self.read_header(self.root_ptr)
        if rh.tag != 0 or rh.other != 5:
            raise ValueError(f"unexpected ModuleData root header: {rh}")
        cn_arr = self.read_array(self.read_field(rh, 1))
        ci_arr = self.read_array(self.read_field(rh, 2))
        if len(cn_arr) != len(ci_arr):
            raise ValueError("constNames and constants length mismatch")
        return {self.read_name(cn): ci for cn, ci in zip(cn_arr, ci_arr)}

    def constant_type_and_value_ptrs(self, ci_ptr: int) -> tuple[int, int | None]:
        """Return `(type_expr_ptr, value_expr_ptr_or_none)` for a `ConstantInfo`."""
        ci_h = self.read_header(ci_ptr)
        val_ptr = self.read_field(ci_h, 0)
        val_h = self.read_header(val_ptr)
        cv_ptr = self.read_field(val_h, 0)
        cv_h = self.read_header(cv_ptr)
        type_ptr = self.read_field(cv_h, 2)
        value_ptr = self.read_field(val_h, 1) if ci_h.tag in (1, 2, 3) else None
        return type_ptr, value_ptr

    def constant_name_ptr(self, ci_ptr: int) -> int:
        ci_h = self.read_header(ci_ptr)
        val_ptr = self.read_field(ci_h, 0)
        val_h = self.read_header(val_ptr)
        cv_ptr = self.read_field(val_h, 0)
        cv_h = self.read_header(cv_ptr)
        return self.read_field(cv_h, 0)

    def expr_data_off(self, expr_ptr: int) -> int:
        hdr = self.read_header(expr_ptr)
        return hdr.off + 8 + hdr.other * 8

    def level_data_off(self, lvl_ptr: int) -> int:
        hdr = self.read_header(lvl_ptr)
        return hdr.off + 8 + hdr.other * 8

    def name_hash_off(self, name_ptr: int) -> int:
        hdr = self.read_header(name_ptr)
        return hdr.off + 8 + hdr.other * 8

    def walk_expr_graph(self, root_expr_ptr: int) -> list[int]:
        """DFS over reachable `Expr` heap pointers starting at `root_expr_ptr`."""
        seen: set[int] = set()
        order: list[int] = []
        stack = [root_expr_ptr]
        while stack:
            p = stack.pop()
            if self.is_scalar(p) or p in seen:
                continue
            seen.add(p)
            order.append(p)
            hdr = self.read_header(p)
            if hdr.tag == 5:  # app
                stack.append(self.read_field(hdr, 0))
                stack.append(self.read_field(hdr, 1))
            elif hdr.tag in (6, 7):  # lam / forallE
                stack.append(self.read_field(hdr, 1))
                stack.append(self.read_field(hdr, 2))
            elif hdr.tag == 8:  # letE
                stack.append(self.read_field(hdr, 1))
                stack.append(self.read_field(hdr, 2))
                stack.append(self.read_field(hdr, 3))
            elif hdr.tag == 10:  # mdata
                stack.append(self.read_field(hdr, 1))
            elif hdr.tag == 11:  # proj
                stack.append(self.read_field(hdr, 2))
        return order

    def find_string_ptrs(self, needle: bytes) -> list[int]:
        """Find all reachable `LeanString` objects whose raw payload equals `needle`."""
        seen: set[int] = set()
        found: list[int] = []
        stack = [self.root_ptr]
        while stack:
            p = stack.pop()
            if self.is_scalar(p) or p in seen:
                continue
            seen.add(p)
            hdr = self.read_header(p)
            if hdr.tag == LEAN_STRING_TAG:
                raw, _, _, _ = self.read_string_raw(p)
                if raw == needle:
                    found.append(p)
            elif hdr.tag == LEAN_ARRAY_TAG:
                for elem in self.read_array(p):
                    if not self.is_scalar(elem):
                        stack.append(elem)
            elif hdr.tag <= 243:
                for i in range(hdr.other):
                    w = self.read_field(hdr, i)
                    if not self.is_scalar(w):
                        stack.append(w)
        return found

    def patch_string_payload(
        self,
        str_ptr: int,
        new_bytes: bytes,
        *,
        new_m_length: int | None = None,
        write_nul: bool = True,
    ) -> None:
        """Overwrite a `LeanString` payload in-place (preserving `m_capacity`)."""
        hdr = self.read_header(str_ptr)
        if hdr.tag != LEAN_STRING_TAG:
            raise ValueError(f"expected LeanString at {hex(str_ptr)}")
        m_cap = self.read_u64(hdr.off + 16)
        new_size = len(new_bytes) + 1
        if new_size > m_cap:
            raise ValueError(
                f"replacement payload size {new_size} exceeds m_capacity {m_cap}"
            )
        self.write_u64(hdr.off + 8, new_size)
        if new_m_length is not None:
            self.write_u64(hdr.off + 24, new_m_length)
        start = hdr.off + 32
        self.buf[start : start + len(new_bytes)] = new_bytes
        if write_nul:
            self.buf[start + len(new_bytes)] = 0

    def flip_expr_mdata_mask(self, expr_ptr: int, xor_mask: int) -> tuple[int, int]:
        """XOR `Expr.Data` at `expr_ptr` with `xor_mask`. Returns `(old, new)`."""
        doff = self.expr_data_off(expr_ptr)
        old = self.read_u64(doff)
        new = old ^ xor_mask
        self.write_u64(doff, new)
        return old, new

    def clear_expr_closedness_flags(self, expr_ptr: int) -> tuple[int, int]:
        """Clear `hasFVar` (bit 40), `hasExprMVar` (bit 41), `hasLevelMVar` (bit 42),
        and `looseBVarRange` (bits 44..63) on `expr_ptr` so cached `isClosedExpr` returns true."""
        doff = self.expr_data_off(expr_ptr)
        old = self.read_u64(doff)
        # Keep hash (0..31), approxDepth (32..39), and hasLevelParam (43).
        keep_mask = 0x000008FFFFFFFFFF
        new = old & keep_mask
        self.write_u64(doff, new)
        return old, new

    def flip_level_mdata_mask(self, lvl_ptr: int, xor_mask: int) -> tuple[int, int]:
        doff = self.level_data_off(lvl_ptr)
        old = self.read_u64(doff)
        new = old ^ xor_mask
        self.write_u64(doff, new)
        return old, new

    def flip_name_hash_mask(self, name_ptr: int, xor_mask: int) -> tuple[int, int]:
        hoff = self.name_hash_off(name_ptr)
        old = self.read_u64(hoff)
        new = old ^ xor_mask
        self.write_u64(hoff, new)
        return old, new

    def find_first_level_in_expr(self, expr_ptr: int) -> int | None:
        """Return the first heap-allocated `Level` pointer reachable from `expr_ptr`."""
        for ep in self.walk_expr_graph(expr_ptr):
            hdr = self.read_header(ep)
            if hdr.tag == 3:  # sort lvl
                lv = self.read_field(hdr, 0)
                if not self.is_scalar(lv):
                    return lv
            elif hdr.tag == 4:  # const n us
                cur = self.read_field(hdr, 1)
                while not self.is_scalar(cur):
                    lh = self.read_header(cur)
                    hd = self.read_field(lh, 0)
                    if not self.is_scalar(hd):
                        return hd
                    cur = self.read_field(lh, 1)
        return None


def corrupt_olean_with_nonzero_rc(raw: bytes) -> bytes:
    """Set `m_rc = 1` on the root `ModuleData` object (illegal in compacted regions)."""
    img = OleanImage(raw)
    rh = img.read_header(img.root_ptr)
    img.write_u32(rh.off, 1)
    return img.to_bytes()


def corrupt_olean_with_oob_root(raw: bytes) -> bytes:
    """Point root_ptr past EOF to test OOB pointer rejection."""
    img = OleanImage(raw)
    img.write_u64(88, img.base_addr + len(raw) + 4096)
    return img.to_bytes()


def corrupt_olean_with_expr_cycle(raw: bytes, decl_name: str) -> bytes:
    """Rewrite an `Expr.app` inside `decl_name` so its function pointer points to itself."""
    img = OleanImage(raw)
    consts = img.module_constants()
    ci = consts[decl_name]
    ty, val = img.constant_type_and_value_ptrs(ci)
    roots: Iterable[int] = [x for x in (val, ty) if x is not None]
    for r in roots:
        for ep in img.walk_expr_graph(r):
            hdr = img.read_header(ep)
            if hdr.tag == 5:  # Expr.app
                img.write_u64(hdr.off + 8, ep)
                return img.to_bytes()
    raise ValueError(f"no Expr.app found in {decl_name}")
