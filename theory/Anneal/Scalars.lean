namespace Anneal.Scalars

/-!
Toolchain-independent fixed-width scalar bounds, two's-complement range
predicates, endian byte-swapping, and modular arithmetic lemmas for
`theory/Anneal/` (`#100`, `#103`).
-/

/-- Modulus $2^8 = 256$ for 8-bit integers (`u8`, `i8`). -/
def U8Modulus : Nat := 256
/-- Maximum unsigned value $2^8 - 1 = 255$ for `u8`. -/
def U8Max : Nat := 255
/-- Sign-bit threshold $2^7 = 128$ for two's-complement `i8`. -/
def I8SignBit : Nat := 128

/-- Modulus $2^{16} = 65536$ for 16-bit integers (`u16`, `i16`). -/
def U16Modulus : Nat := 65536
/-- Maximum unsigned value $2^{16} - 1 = 65535$ for `u16`. -/
def U16Max : Nat := 65535
/-- Sign-bit threshold $2^{15} = 32768$ for two's-complement `i16`. -/
def I16SignBit : Nat := 32768

/-- Modulus $2^{32} = 4294967296$ for 32-bit integers (`u32`, `i32`). -/
def U32Modulus : Nat := 4294967296
/-- Maximum unsigned value $2^{32} - 1 = 4294967295$ for `u32`. -/
def U32Max : Nat := 4294967295
/-- Sign-bit threshold $2^{31} = 2147483648$ for two's-complement `i32`. -/
def I32SignBit : Nat := 2147483648

/-- Modulus $2^{64}$ for 64-bit integers (`u64`, `i64`, `usize`, `isize`). -/
def U64Modulus : Nat := 18446744073709551616
/-- Maximum unsigned value $2^{64} - 1$ for `u64` / `usize`. -/
def U64Max : Nat := 18446744073709551615
/-- Sign-bit threshold $2^{63}$ for two's-complement `i64` / `isize`. -/
def I64SignBit : Nat := 9223372036854775808

/-- Modulus $2^{8 \cdot \text{sizeBytes}}$ for a scalar of width `sizeBytes`. -/
def widthModulus (sizeBytes : Nat) : Nat :=
  2 ^ (sizeBytes * 8)

/-- Sign-bit threshold $2^{8 \cdot \text{sizeBytes} - 1}$ for width `sizeBytes`. -/
def widthSignBit (sizeBytes : Nat) : Nat :=
  2 ^ (sizeBytes * 8 - 1)

/-- Whether `bits` lies in the unsigned range $[0, 2^{8 \cdot \text{sizeBytes}})$. -/
def inUnsignedRange (bits sizeBytes : Nat) : Prop :=
  bits < widthModulus sizeBytes

/-- Whether `bits` is a non-negative two's-complement integer of width `sizeBytes`. -/
def inSignedNonNegRange (bits sizeBytes : Nat) : Prop :=
  bits < widthSignBit sizeBytes

/-- Whether `bits` is a negative two's-complement integer of width `sizeBytes`. -/
def inSignedNegRange (bits sizeBytes : Nat) : Prop :=
  widthSignBit sizeBytes ≤ bits ∧ bits < widthModulus sizeBytes

@[simp] theorem widthModulus_one : widthModulus 1 = U8Modulus := rfl
@[simp] theorem widthModulus_two : widthModulus 2 = U16Modulus := rfl
@[simp] theorem widthModulus_four : widthModulus 4 = U32Modulus := rfl
@[simp] theorem widthModulus_eight : widthModulus 8 = U64Modulus := rfl

@[simp] theorem widthSignBit_one : widthSignBit 1 = I8SignBit := rfl
@[simp] theorem widthSignBit_two : widthSignBit 2 = I16SignBit := rfl
@[simp] theorem widthSignBit_four : widthSignBit 4 = I32SignBit := rfl
@[simp] theorem widthSignBit_eight : widthSignBit 8 = I64SignBit := rfl

/--
When `x < bound` and `bound < modulus`, incrementing `x` by `1` does not reach
`modulus`.
-/
theorem add_one_no_overflow_of_lt {x bound modulus : Nat}
    (h_lt : x < bound) (h_bound : Nat.ble modulus bound = false) :
    Nat.ble modulus (x + 1) = false := by
  cases hb : Nat.ble modulus (x + 1)
  · rfl
  · have h1 := Nat.le_of_ble_eq_true hb
    have h2 : ¬ modulus ≤ bound := fun hle => by
      rw [Nat.ble_eq_true_of_le hle] at h_bound; nomatch h_bound
    omega

/-- Swap the low and high bytes of a 16-bit unsigned integer (`u16::swap_bytes`). -/
def swapBytes16 (n : Nat) : Nat :=
  ((n % 256) * 256) + ((n / 256) % 256)

/-- `swapBytes16` is an involution on every 16-bit integer `n < 65536`. -/
theorem swapBytes16_involutive {n : Nat} (hn : n < U16Modulus) :
    swapBytes16 (swapBytes16 n) = n := by
  unfold swapBytes16 U16Modulus at *
  have hhi : (n / 256) % 256 = n / 256 := by omega
  rw [hhi]
  have h1 : (n % 256 * 256 + n / 256) % 256 = n / 256 := by omega
  have h2 : (n % 256 * 256 + n / 256) / 256 = n % 256 := by omega
  rw [h1, h2]
  omega

end Anneal.Scalars
