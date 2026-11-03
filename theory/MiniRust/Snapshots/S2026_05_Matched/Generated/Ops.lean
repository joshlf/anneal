import MiniRust.LibSpecr

-- Mechanically generated executable MiniRust operational semantics (`Generated/Ops.lean`).
-- Upstream snapshot: S2026_05_Matched @ 5f78e227bbe30ae9fb5e1286a772d91a92e3622a
-- AST-translated from `env.items` by `crates/anneal-specr-lean/src/ops_emit.rs`.

namespace MiniRust.Snapshots.S2026_05_Matched.Generated.Ops

open MiniRust.LibSpecr

deriving instance DecidableEq for Except

deriving instance Inhabited for Align, Size, Offset, Endianness, SpecrMap, SpecrSet, TerminationInfo

instance {α : Type} : Inhabited (NdComp α) where
  default := .ret (.error .machineStop)

instance : Min Align where
  min a₁ a₂ := ⟨Nat.min a₁.exp a₂.exp⟩

instance : Max Align where
  max a₁ a₂ := ⟨Nat.max a₁.exp a₂.exp⟩

instance : Min Size where
  min s₁ s₂ := ⟨Nat.min s₁.bytes s₂.bytes⟩

instance : Max Size where
  max s₁ s₂ := ⟨Nat.max s₁.bytes s₂.bytes⟩

/-! ## 1. Core Syntax, Type, Memory, Tree Borrows, & Machine Data Types -/

/-- Integer signedness (`libspecr::Signedness`). -/
inductive Signedness : Type where
  | Signed
  | Unsigned
  deriving Inhabited, DecidableEq, Repr

-- @specr-source: spec/lang/syntax.md:52..54 (IntUnOp)
-- @specr-body-sha256: aa4f7357b11e6a9f796c38cdbab23ccff793368d1eec79fc0da280d4f1ae7a5b
inductive IntUnOp : Type where
  | Neg : IntUnOp
  | BitNot : IntUnOp
  | CountOnes : IntUnOp
  deriving Inhabited, DecidableEq, Repr

-- @specr-source: spec/lang/syntax.md:66..81 (IntBinOp)
-- @specr-body-sha256: 3aa04f1af14aa2a333349c529e8092082c987aec0b80115243acc53c0f36bcf4
inductive IntBinOp : Type where
  | Add : IntBinOp
  | AddUnchecked : IntBinOp
  | Sub : IntBinOp
  | SubUnchecked : IntBinOp
  | Mul : IntBinOp
  | MulUnchecked : IntBinOp
  | Div : IntBinOp
  | DivExact : IntBinOp
  | Rem : IntBinOp
  | Shl : IntBinOp
  | ShlUnchecked : IntBinOp
  | Shr : IntBinOp
  | ShrUnchecked : IntBinOp
  | BitAnd : IntBinOp
  | BitOr : IntBinOp
  | BitXor : IntBinOp
  deriving Inhabited, DecidableEq, Repr

-- @specr-source: spec/lang/syntax.md:81..83 (IntBinOpWithOverflow)
-- @specr-body-sha256: 9be481d913beca293c47b53e8c1d7480ac91336fb27eecaf5a1a32bdc1e9fc73
inductive IntBinOpWithOverflow : Type where
  | Add : IntBinOpWithOverflow
  | Sub : IntBinOpWithOverflow
  | Mul : IntBinOpWithOverflow
  deriving Inhabited, DecidableEq, Repr

-- @specr-source: spec/lang/syntax.md:83..87 (RelOp)
-- @specr-body-sha256: bbe3a5979b4a402d23b879a22cdf8a9e945cf0f96ea5e1ef9de9d33003043eec
inductive RelOp : Type where
  | Lt : RelOp
  | Gt : RelOp
  | Le : RelOp
  | Ge : RelOp
  | Eq : RelOp
  | Ne : RelOp
  | Cmp : RelOp
  deriving Inhabited, DecidableEq, Repr

-- @specr-source: spec/lang/types.md:37..38 (IntType)
-- @specr-body-sha256: ae70fd01ca80d340a1e6591740d70f92fae326a09dbd4e368b190533f7efacf8
structure IntType : Type where
  signed : Signedness
  size : Size
  deriving Inhabited, DecidableEq, Repr

-- @specr-source: spec/mem/interface.md:57..58 (AllocationKind)
-- @specr-body-sha256: faa2bb7fd0b663680545639548981af44cabcd5b81e46cfef391e4afe8fd0fc4
inductive AllocationKind : Type where
  | Stack : AllocationKind
  | Heap : AllocationKind
  | Global : AllocationKind
  | Function : AllocationKind
  | VTable : AllocationKind
  deriving Inhabited, DecidableEq, Repr

-- @specr-source: spec/mem/tree_borrows/tree.md:60..63 (AccessKind)
-- @specr-body-sha256: 8103e2aa1b1b8edaea87f0e8a37cd83a8526ff2e474e98e42c92b5cb1eed79a7
inductive AccessKind : Type where
  | Read : AccessKind
  | Write : AccessKind
  deriving Inhabited, DecidableEq, Repr

-- @specr-source: spec/mem/tree_borrows/tree.md:51..54 (NodeRelation)
-- @specr-body-sha256: 36957fdbb78238f841baf7d56498906832c6bd257e4ec4bc4a87c25b3b1cf42c
inductive NodeRelation : Type where
  | Local : NodeRelation
  | Foreign : NodeRelation
  deriving Inhabited, DecidableEq, Repr

-- @specr-source: spec/mem/tree_borrows/tree.md:14..18 (Protected)
-- @specr-body-sha256: 36c5059f309f3091dee1b59e1aa3f2d71abb56c532db2c40e2682624bd57bb1c
inductive Protected : Type where
  | Strong : Protected
  | Weak : Protected
  | No : Protected
  deriving Inhabited, DecidableEq, Repr

-- @specr-source: spec/mem/tree_borrows/tree.md:21..21 (Protected::yes)
-- @specr-body-sha256: 5dd42891e4a07a84cfc449c894f10018c2fd1ea5c49dde5515ce4cf76a3809c4
@[reducible]
def Protected.yes (self : Protected) : Bool :=
  (self != Protected.No)

abbrev Protected_yes := Protected.yes

-- @specr-source: spec/mem/tree_borrows/state_machine_unprotected.md:6..9 (PermissionUnprot)
-- @specr-body-sha256: 3cf33c96e3aad164000cb904ae1ba09a2e622aa758ce915bc3edfac9addd0831
inductive PermissionUnprot : Type where
  | Cell : PermissionUnprot
  | Reserved : PermissionUnprot
  | ReservedIm : PermissionUnprot
  | Unique : PermissionUnprot
  | Frozen : PermissionUnprot
  | Disabled : PermissionUnprot
  deriving Inhabited, DecidableEq, Repr

-- @specr-source: spec/mem/tree_borrows/state_machine_protected.md:7..10 (PermissionProt)
-- @specr-body-sha256: 5dc9372e7d26c7da9c46c0ceedd98147ace076c0b82a4ed45789307d84d650bd
inductive PermissionProt : Type where
  | Cell : PermissionProt
  | Reserved (had_local_read : Bool) (had_foreign_read : Bool) : PermissionProt
  | Unique : PermissionProt
  | Frozen (had_local_read : Bool) : PermissionProt
  | Disabled : PermissionProt
  deriving Inhabited, DecidableEq, Repr

-- @specr-source: spec/mem/tree_borrows/state_machine.md:11..14 (Permission)
-- @specr-body-sha256: b7ffb2f9911409645e2de835da58dc37f9ba85ed8344ce613c7c0feb0f342d97
inductive Permission : Type where
  | Unprot (arg_0 : PermissionUnprot) : Permission
  | Prot (arg_0 : PermissionProt) : Permission
  deriving Inhabited, DecidableEq, Repr

-- @specr-source: spec/lang/machine.md:101-105 @ 5f78e227bbe30ae9fb5e1286a772d91a92e3622a
-- @specr-body-sha256: abb8eafb9b5cf73175ff9af203e6701ee3fe59a0f93df5bb8533708e98aa3b0c
inductive ThreadState : Type where
  | Enabled
  | BlockedOnJoin (tid : Nat)
  | BlockedOnLock (lid : Nat)
  | Terminated
  deriving Inhabited, DecidableEq, Repr

/-! ## 2. L1 Scalar & Arithmetic Semantics (`spec/lang/types.md`, `spec/lang/step/operators.md`) -/

-- @specr-source: spec/lang/types.md:303-305 @ 5f78e227bbe30ae9fb5e1286a772d91a92e3622a
-- @specr-body-sha256: 9d4a04f4b21219c81e9c2b30d8d2772a66d3e459a04719f549cfb3a8d12023e5
@[reducible]
def IntType.can_represent (self : IntType) (i : SpecrInt) : Bool :=
  match self.signed with
  | .Unsigned => SpecrInt.inUnsignedRange i self.size.bits
  | .Signed => SpecrInt.inSignedRange i self.size.bits

-- @specr-source: spec/lang/types.md:307-309 @ 5f78e227bbe30ae9fb5e1286a772d91a92e3622a
-- @specr-body-sha256: aa7e443b6c588a2f67b5ae27de66d01b1cd261c6f06e0bd22b57553bc98ba001
@[reducible]
def IntType.bring_in_bounds (self : IntType) (i : SpecrInt) : SpecrInt :=
  let wrapped := SpecrInt.wrapUnsigned i self.size.bits
  match self.signed with
  | .Unsigned => Int.ofNat wrapped
  | .Signed => SpecrInt.toSigned wrapped self.size.bits

-- @specr-source: spec/lang/step/operators.md:59-64 @ 5f78e227bbe30ae9fb5e1286a772d91a92e3622a
-- @specr-body-sha256: 3bc13a70f55918671f436542e21103836422050868bad80763534121683e51b0
def countOnesBitsAux : Nat → Nat → Nat
  | 0, _ => 0
  | k + 1, rem => (rem % 2) + countOnesBitsAux k (rem / 2)

@[reducible]
def eval_count_ones (operand : SpecrInt) (int_ty : IntType) : SpecrInt :=
  let u := SpecrInt.wrapUnsigned operand int_ty.size.bits
  Int.ofNat (countOnesBitsAux int_ty.size.bits u)

-- @specr-source: spec/lang/step/operators.md:18-24 @ 5f78e227bbe30ae9fb5e1286a772d91a92e3622a
-- @specr-body-sha256: f21bb7b533eb7dacd867915a30481d5ea7a24e4790e2e2dde65dda11babfc8ec
@[reducible]
def eval_int_un_op (op : IntUnOp) (operand : SpecrInt) (operand_ty : IntType) : Except TerminationInfo SpecrInt :=
  match op with
  | .Neg => .ok (operand_ty.bring_in_bounds (-operand))
  | .BitNot => .ok (operand_ty.bring_in_bounds (-operand - 1))
  | .CountOnes => .ok (eval_count_ones operand operand_ty)

def mrBitAnd : Nat → Nat → Nat → Nat
  | 0, _, _ => 0
  | k + 1, a, b =>
    let bit := if (a % 2 == 1) && (b % 2 == 1) then 1 else 0
    bit + 2 * mrBitAnd k (a / 2) (b / 2)

def mrBitOr : Nat → Nat → Nat → Nat
  | 0, _, _ => 0
  | k + 1, a, b =>
    let bit := if (a % 2 == 1) || (b % 2 == 1) then 1 else 0
    bit + 2 * mrBitOr k (a / 2) (b / 2)

def mrBitXor : Nat → Nat → Nat → Nat
  | 0, _, _ => 0
  | k + 1, a, b =>
    let bit := if (a % 2) == (b % 2) then 0 else 1
    bit + 2 * mrBitXor k (a / 2) (b / 2)

-- @specr-source: spec/lang/step/operators.md:187-269 @ 5f78e227bbe30ae9fb5e1286a772d91a92e3622a
-- @specr-body-sha256: 7220b4c4d65ff055cef05ce46f5ff357c689ab422162336c3b072796c7d5c6bd
@[reducible]
def eval_int_bin_op (op : IntBinOp) (left right : SpecrInt) (left_ty : IntType) : Except TerminationInfo SpecrInt :=
  match op with
  | .Add => .ok (left + right)
  | .AddUnchecked =>
    let result := left + right
    if !left_ty.can_represent result then .error (.ub "overflow in unchecked add") else .ok result
  | .Sub => .ok (left - right)
  | .SubUnchecked =>
    let result := left - right
    if !left_ty.can_represent result then .error (.ub "overflow in unchecked sub") else .ok result
  | .Mul => .ok (left * right)
  | .MulUnchecked =>
    let result := left * right
    if !left_ty.can_represent result then .error (.ub "overflow in unchecked mul") else .ok result
  | .Div =>
    if right == 0 then .error (.ub "division by zero")
    else
      let result := Int.tdiv left right
      if !left_ty.can_represent result then .error (.ub "overflow in division") else .ok result
  | .DivExact =>
    if right == 0 then .error (.ub "division by zero")
    else
      let result := Int.tdiv left right
      if !left_ty.can_represent result then .error (.ub "overflow in division")
      else if Int.tmod left right != 0 then .error (.ub "non-zero remainder in exact division")
      else .ok result
  | .Rem =>
    if right == 0 then .error (.ub "modulus of remainder is zero")
    else if !left_ty.can_represent (Int.tdiv left right) then .error (.ub "overflow in remainder")
    else .ok (Int.tmod left right)
  | .Shl =>
    let bits := left_ty.size.bits
    let offset := Int.toNat (right % Int.ofNat bits)
    .ok (left * Int.ofNat (2 ^ offset))
  | .Shr =>
    let bits := left_ty.size.bits
    let offset := Int.toNat (right % Int.ofNat bits)
    .ok (Int.fdiv left (Int.ofNat (2 ^ offset)))
  | .ShlUnchecked =>
    let bits := left_ty.size.bits
    if decide (right < 0) || decide (right ≥ Int.ofNat bits) then .error (.ub "overflow in unchecked shift")
    else .ok (left * Int.ofNat (2 ^ Int.toNat right))
  | .ShrUnchecked =>
    let bits := left_ty.size.bits
    if decide (right < 0) || decide (right ≥ Int.ofNat bits) then .error (.ub "overflow in unchecked shift")
    else .ok (Int.fdiv left (Int.ofNat (2 ^ Int.toNat right)))
  | .BitAnd =>
    let bits := left_ty.size.bits
    let u := mrBitAnd bits (SpecrInt.wrapUnsigned left bits) (SpecrInt.wrapUnsigned right bits)
    .ok (left_ty.bring_in_bounds (Int.ofNat u))
  | .BitOr =>
    let bits := left_ty.size.bits
    let u := mrBitOr bits (SpecrInt.wrapUnsigned left bits) (SpecrInt.wrapUnsigned right bits)
    .ok (left_ty.bring_in_bounds (Int.ofNat u))
  | .BitXor =>
    let bits := left_ty.size.bits
    let u := mrBitXor bits (SpecrInt.wrapUnsigned left bits) (SpecrInt.wrapUnsigned right bits)
    .ok (left_ty.bring_in_bounds (Int.ofNat u))

-- @specr-source: spec/lang/step/operators.md:172-179 @ 5f78e227bbe30ae9fb5e1286a772d91a92e3622a
-- @specr-body-sha256: c82caaad911dd7878c37e76c490f6d83839b7e1e10c7283ce5fb24f0cb6767a0
@[reducible]
def eval_bin_op_int (op : IntBinOp) (left right : SpecrInt) (int_ty : IntType) : Except TerminationInfo SpecrInt :=
  match eval_int_bin_op op left right int_ty with
  | .ok res => .ok (int_ty.bring_in_bounds res)
  | .error e => .error e

@[reducible]
def eval_bin_op_int_with_overflow (op : IntBinOpWithOverflow) (left right : SpecrInt) (int_ty : IntType) : SpecrInt × Bool :=
  let result : SpecrInt :=
    match op with
    | .Add => left + right
    | .Sub => left - right
    | .Mul => left * right
  let overflow := !int_ty.can_represent result
  (int_ty.bring_in_bounds result, overflow)

-- @specr-source: spec/lang/step/operators.md:321-337 @ 5f78e227bbe30ae9fb5e1286a772d91a92e3622a
-- @specr-body-sha256: 52ed9fc906eba5daa59147a6c7fad0726c757aa6097694612920aeb1d3334cbf
@[reducible]
def eval_rel_op_bool (rel : RelOp) (left right : SpecrInt) : Bool :=
  match rel with
  | .Lt => decide (left < right)
  | .Gt => decide (left > right)
  | .Le => decide (left ≤ right)
  | .Ge => decide (left ≥ right)
  | .Eq => decide (left = right)
  | .Ne => decide (left ≠ right)
  | .Cmp => decide (left = right)

@[reducible]
def eval_cmp_int (left right : SpecrInt) : SpecrInt :=
  if decide (left < right) then -1
  else if decide (left = right) then 0
  else 1

-- @specr-source: spec/lang/step/operators.md:187-269 @ 5f78e227bbe30ae9fb5e1286a772d91a92e3622a
-- @specr-body-sha256: 7220b4c4d65ff055cef05ce46f5ff357c689ab422162336c3b072796c7d5c6bd
@[reducible]
def mrWrappingAdd (a b sizeBytes : Nat) : Nat :=
  (a + b) % (256 ^ sizeBytes)

@[reducible]
def mrWrappingSub (a b sizeBytes : Nat) : Nat :=
  let m := 256 ^ sizeBytes
  if b ≤ a then (a - b) % m else (m + (a % m) - (b % m)) % m

@[reducible]
def mrWrappingMul (a b sizeBytes : Nat) : Nat :=
  (a * b) % (256 ^ sizeBytes)

@[reducible]
def mrCheckedAdd (a b sizeBytes : Nat) : Nat × Bool :=
  let m := 256 ^ sizeBytes
  ((a + b) % m, decide (m ≤ a + b))

@[reducible]
def mrCheckedSub (a b sizeBytes : Nat) : Nat × Bool :=
  let m := 256 ^ sizeBytes
  if b ≤ a then ((a - b) % m, false) else ((m + (a % m) - (b % m)) % m, true)

@[reducible]
def mrCheckedMul (a b sizeBytes : Nat) : Nat × Bool :=
  let m := 256 ^ sizeBytes
  ((a * b) % m, decide (m ≤ a * b))

@[reducible]
def mrEvalUnsignedDiv (a b _sizeBytes : Nat) : Except TerminationInfo Nat :=
  if b == 0 then
    .error (.ub "division by zero")
  else
    .ok (a / b)

@[reducible]
def mrEvalUnsignedRem (a b _sizeBytes : Nat) : Except TerminationInfo Nat :=
  if b == 0 then
    .error (.ub "modulus of remainder is zero")
  else
    .ok (a % b)

@[reducible]
def mrEvalSignedDiv (lhs rhs : SpecrInt) (bitWidth : Nat) : Except TerminationInfo SpecrInt :=
  match bitWidth with
  | 0 => .error (.ub "zero-width signed division")
  | k + 1 =>
    let intMin : SpecrInt := -(Int.ofNat (2 ^ k))
    if rhs == 0 || (lhs == intMin && rhs == -1) then
      .error (.ub "division overflow or by zero")
    else
      .ok (Int.tdiv lhs rhs)

@[reducible]
def mrEvalSignedRem (lhs rhs : SpecrInt) (bitWidth : Nat) : Except TerminationInfo SpecrInt :=
  match bitWidth with
  | 0 => .error (.ub "zero-width signed remainder")
  | k + 1 =>
    let intMin : SpecrInt := -(Int.ofNat (2 ^ k))
    if rhs == 0 || (lhs == intMin && rhs == -1) then
      .error (.ub "remainder overflow or by zero")
    else
      .ok (Int.tmod lhs rhs)

@[reducible]
def mrShiftValid (shift sizeBytes : Nat) : Bool :=
  decide (shift < 8 * sizeBytes)

@[reducible]
def mrEncodeBool : Bool → Nat
  | false => 0
  | true => 1

@[reducible]
def mrShl (a b sizeBytes : Nat) : Nat :=
  let numBits := sizeBytes * 8
  let shift := b % numBits
  (a * (2 ^ shift)) % (256 ^ sizeBytes)

@[reducible]
def mrShlUnchecked (a b sizeBytes : Nat) : Except TerminationInfo Nat :=
  let numBits := sizeBytes * 8
  if decide (numBits ≤ b) then
    .error (.ub "overflow in unchecked shift")
  else
    .ok ((a * (2 ^ b)) % (256 ^ sizeBytes))

@[reducible]
def mrShrUnsigned (a b sizeBytes : Nat) : Nat :=
  let numBits := sizeBytes * 8
  let shift := b % numBits
  (a / (2 ^ shift)) % (256 ^ sizeBytes)

@[reducible]
def mrShrUncheckedUnsigned (a b sizeBytes : Nat) : Except TerminationInfo Nat :=
  let numBits := sizeBytes * 8
  if decide (numBits ≤ b) then
    .error (.ub "overflow in unchecked shift")
  else
    .ok ((a / (2 ^ b)) % (256 ^ sizeBytes))

@[reducible]
def mrShrSigned (a b sizeBytes : Nat) : Nat :=
  let modulus := 256 ^ sizeBytes
  let numBits := sizeBytes * 8
  let shift := b % numBits
  let canonical := a % modulus
  let logical := canonical / (2 ^ shift)
  if sizeBytes == 0 || canonical < modulus / 2 then
    logical % modulus
  else
    let highOnes := modulus - (2 ^ (numBits - shift))
    (logical + highOnes) % modulus

@[reducible]
def mrShrUncheckedSigned (a b sizeBytes : Nat) : Except TerminationInfo Nat :=
  let numBits := sizeBytes * 8
  if decide (numBits ≤ b) then
    .error (.ub "overflow in unchecked shift")
  else
    .ok (mrShrSigned a b sizeBytes)

/-! ## 3. L2 Abstract Bytes & Representation Relation (`spec/mem/interface.md`, `spec/lang/representation.md`) -/

-- @specr-source: spec/mem/interface.md:22-25 @ 5f78e227bbe30ae9fb5e1286a772d91a92e3622a
-- @specr-body-sha256: cd1963582f3098c9552dfea9871ca7265aa585835d951ee3b422b550a893b453
inductive MrAbstractByte : Type where
  | uninit
  | init (byte : UInt8) (prov : Option (Nat × Nat))
  deriving DecidableEq, Repr

-- @specr-source: spec/mem/interface.md:29-32 @ 5f78e227bbe30ae9fb5e1286a772d91a92e3622a
-- @specr-body-sha256: 197a2184ee255b3a2a7c8a898969e02c1da31855fbb9de57485b11b93f900e63
@[reducible]
def MrAbstractByte.data : MrAbstractByte → Option UInt8
  | .uninit => none
  | .init b _ => some b

-- @specr-source: spec/mem/interface.md:32-39 @ 5f78e227bbe30ae9fb5e1286a772d91a92e3622a
-- @specr-body-sha256: b1db98de5a4242e65ac8d86bc94a91aeab925b909d4a2c6a0731043430fcba11
@[reducible]
def MrAbstractByte.provenance : MrAbstractByte → Option (Nat × Nat)
  | .uninit => none
  | .init _ p => p

-- @specr-source: spec/lang/representation.md:653-662 @ 5f78e227bbe30ae9fb5e1286a772d91a92e3622a
-- @specr-body-sha256: 1ed3c6bdf99374f315ec847880770bd4fcab1241866d59b031d22d27df104c55
@[reducible]
def MrAbstractByte.le_defined (self other : MrAbstractByte) : Bool :=
  match self, other with
  | .uninit, _ => true
  | .init d1 none, .init d2 _ => d1 == d2
  | .init d1 (some p1), .init d2 (some p2) => d1 == d2 && p1 == p2
  | _, _ => false

-- @specr-source: spec/lang/representation.md:34-37 @ 5f78e227bbe30ae9fb5e1286a772d91a92e3622a
-- @specr-body-sha256: c82caaad911dd7878c37e76c490f6d83839b7e1e10c7283ce5fb24f0cb6767a0
@[reducible]
def mrDecodeBoolByte : MrAbstractByte → Except TerminationInfo Bool
  | .uninit => .error (.ub "uninitialized bool byte")
  | .init b _ =>
    if b == 0 then
      .ok false
    else if b == 1 then
      .ok true
    else
      .error (.ub "invalid bool bit pattern")

@[reducible]
def decode_bool_bytes : List MrAbstractByte → Option Bool
  | [.init 0 _] => some false
  | [.init 1 _] => some true
  | _ => none

-- @specr-source: spec/lang/representation.md:37-39 @ 5f78e227bbe30ae9fb5e1286a772d91a92e3622a
-- @specr-body-sha256: c82caaad911dd7878c37e76c490f6d83839b7e1e10c7283ce5fb24f0cb6767a0
@[reducible]
def encode_bool_bytes (b : Bool) : List MrAbstractByte :=
  [.init (if b then 1 else 0) none]

@[reducible]
def mergeMrProvenance (p₁ p₂ : Option (Nat × Nat)) : Option (Nat × Nat) :=
  match p₂ with
  | none => p₁
  | some _ =>
    match p₁ with
    | some _ => p₁
    | none => p₂

@[reducible]
def encode_int_le (bits : Nat) : Nat → Option (Nat × Nat) → List MrAbstractByte
  | 0, _ => []
  | rem + 1, prov =>
    .init (UInt8.ofNat bits) prov :: encode_int_le (bits / 256) rem prov

@[reducible]
def decode_int_le : List MrAbstractByte → Option (Nat × Option (Nat × Nat))
  | [] => some (0, none)
  | .uninit :: _ => none
  | .init b prov :: rest =>
    match decode_int_le rest with
    | some (highBits, restProv) =>
      some (b.toBitVec.toNat + 256 * highBits, mergeMrProvenance prov restProv)
    | none => none

-- @specr-source: spec/lang/representation.md:34-37 @ 5f78e227bbe30ae9fb5e1286a772d91a92e3622a
-- @specr-body-sha256: c82caaad911dd7878c37e76c490f6d83839b7e1e10c7283ce5fb24f0cb6767a0
@[reducible]
def replicate_uninit_bytes : Nat → List MrAbstractByte
  | 0 => []
  | k + 1 => .uninit :: replicate_uninit_bytes k

@[reducible]
def subslice_with_length (bytes : List MrAbstractByte) (offset len : Nat) : Option (List MrAbstractByte) :=
  if decide (offset + len ≤ bytes.length) then
    some ((bytes.drop offset).take len)
  else
    none

@[reducible]
def write_subslice_at_index : List MrAbstractByte → Nat → List MrAbstractByte → Option (List MrAbstractByte)
  | buf, _, [] => some buf
  | [], _, _ :: _ => none
  | _ :: bufRest, 0, w :: wRest =>
    match write_subslice_at_index bufRest 0 wRest with
    | some tail' => some (w :: tail')
    | none => none
  | b :: bufRest, off + 1, wList =>
    match write_subslice_at_index bufRest off wList with
    | some tail' => some (b :: tail')
    | none => none

@[reducible]
def encode_tuple_fields_aux : List (Nat × List MrAbstractByte) → List MrAbstractByte → Option (List MrAbstractByte)
  | [], buf => some buf
  | (off, fbytes) :: rest, buf =>
    match write_subslice_at_index buf off fbytes with
    | some buf' => encode_tuple_fields_aux rest buf'
    | none => none

@[reducible]
def encode_tuple_fields (total_size : Nat) (fields : List (Nat × List MrAbstractByte)) : Option (List MrAbstractByte) :=
  encode_tuple_fields_aux fields (replicate_uninit_bytes total_size)

@[reducible]
def decode_tuple_fields (bytes : List MrAbstractByte) : List (Nat × Nat) → Option (List (List MrAbstractByte))
  | [] => some []
  | (off, len) :: rest =>
    match subslice_with_length bytes off len, decode_tuple_fields bytes rest with
    | some slice, some restSlices => some (slice :: restSlices)
    | _, _ => none

@[reducible]
def encode_array_elems (elem_size : Nat) : List (List MrAbstractByte) → Option (List MrAbstractByte)
  | [] => some []
  | e :: rest =>
    if e.length == elem_size then
      match encode_array_elems elem_size rest with
      | some tailBytes => some (e ++ tailBytes)
      | none => none
    else
      none

@[reducible]
def decode_array_elems (elem_size : Nat) : Nat → List MrAbstractByte → Option (List (List MrAbstractByte))
  | 0, [] => some []
  | 0, _ :: _ => none
  | k + 1, bytes =>
    if decide (elem_size ≤ bytes.length) then
      let chunk := bytes.take elem_size
      let rest := bytes.drop elem_size
      match decode_array_elems elem_size k rest with
      | some chunks => some (chunk :: chunks)
      | none => none
    else
      none

@[reducible]
def encode_union_chunks (total_size : Nat) (chunks : List (Nat × List MrAbstractByte)) : Option (List MrAbstractByte) :=
  encode_tuple_fields total_size chunks

@[reducible]
def decode_union_chunks (bytes : List MrAbstractByte) (chunks : List (Nat × Nat)) : Option (List (List MrAbstractByte)) :=
  decode_tuple_fields bytes chunks

-- @specr-source: spec/lang/representation.md:353-364 @ 5f78e227bbe30ae9fb5e1286a772d91a92e3622a
-- @specr-body-sha256: 1ac1adafd5f91a0e4d1738420771e7224206e526449306c6f65c221c0384bfe8
@[reducible]
def decode_discriminant_tag (bytes : List MrAbstractByte) (tag_offset tag_size : Nat) : Option Nat :=
  match subslice_with_length bytes tag_offset tag_size with
  | some tagBytes =>
    match decode_int_le tagBytes with
    | some (val, _) => some val
    | none => none
  | none => none

/-! ## 4. L3 Places & `BasicMemory` Semantics (`spec/mem/basic.md`, `spec/lang/step/expressions.md`) -/

-- @specr-source: spec/mem/basic.md:18-18 @ 5f78e227bbe30ae9fb5e1286a772d91a92e3622a
-- @specr-body-sha256: 4623dca6558191a8bcd629626eb9c8c63cd647601ccd4eaa4fbf2a320f8dfbe4
abbrev AllocId : Type := Nat

structure MrPointer : Type where
  allocId : AllocId
  offset : Nat
  tag : Option Nat := none
  deriving DecidableEq, Repr

-- @specr-source: spec/mem/basic.md:26-30 @ 5f78e227bbe30ae9fb5e1286a772d91a92e3622a
-- @specr-body-sha256: 1a1bdea8f5f25023f12b82e075df28f774e0b3f01090009b45911c51dbab4399
structure MrAllocation : Type where
  id : AllocId
  align : Align
  size : Nat
  live : Bool
  bytes : List UInt8
  deriving DecidableEq, Repr

-- @specr-source: spec/mem/basic.md:47-50 @ 5f78e227bbe30ae9fb5e1286a772d91a92e3622a
-- @specr-body-sha256: 787ff35529b445ce3801ea85aea653c9da1b84986437021560bda7e2c66e0eae
structure BasicMemory : Type where
  allocs : List MrAllocation
  nextAllocId : AllocId
  deriving DecidableEq, Repr

@[reducible]
def BasicMemory.findAlloc (mem : BasicMemory) (id : AllocId) : Option MrAllocation :=
  mem.allocs.find? (fun a => a.id == id)

-- @specr-source: spec/mem/basic.md:194-208 @ 5f78e227bbe30ae9fb5e1286a772d91a92e3622a
-- @specr-body-sha256: 89b01a68169c2be5094720e79551e1cadcb0993ad3e71eea9b0099312ff14544
@[reducible]
def basicMemCheckAccess
    (mem : BasicMemory) (ptr : MrPointer) (reqAlign : Align) (len : Nat) :
    Except TerminationInfo MrAllocation :=
  if !Align.isAligned ptr.offset reqAlign then
    .error (.ub "misaligned pointer access")
  else
    match mem.findAlloc ptr.allocId with
    | none => .error (.ub "dangling pointer to nonexistent allocation")
    | some alloc =>
      if !alloc.live then
        .error (.ub "dangling pointer to deallocated memory")
      else if decide (ptr.offset + len ≤ alloc.size) then
        .ok alloc
      else
        .error (.ub "pointer access out of bounds")

-- @specr-source: spec/mem/basic.md:230-248 @ 5f78e227bbe30ae9fb5e1286a772d91a92e3622a
-- @specr-body-sha256: 97be9c897786adf6f8ce43a09b5595ab2cd6546399580c558a58a25fe81f0342
@[reducible]
def basicMemLoad (mem : BasicMemory) (ptr : MrPointer) (reqAlign : Align) (len : Nat) : Except TerminationInfo (List UInt8) :=
  match basicMemCheckAccess mem ptr reqAlign len with
  | .ok alloc => .ok ((alloc.bytes.drop ptr.offset).take len)
  | .error e => .error e

-- @specr-source: spec/mem/basic.md:208-230 @ 5f78e227bbe30ae9fb5e1286a772d91a92e3622a
-- @specr-body-sha256: 66b865f93a9a900cdb1e24796d3cc822efebd96eebf31396426196752d8fa320
@[reducible]
def basicMemStore (mem : BasicMemory) (ptr : MrPointer) (reqAlign : Align) (data : List UInt8) : Except TerminationInfo BasicMemory :=
  match basicMemCheckAccess mem ptr reqAlign data.length with
  | .error e => .error e
  | .ok alloc =>
    let newBytes := (alloc.bytes.take ptr.offset) ++ data ++ (alloc.bytes.drop (ptr.offset + data.length))
    let newAlloc := { alloc with bytes := newBytes }
    let newAllocs := mem.allocs.map (fun a => if a.id == ptr.allocId then newAlloc else a)
    .ok { mem with allocs := newAllocs }

-- @specr-source: spec/mem/basic.md:121-162 @ 5f78e227bbe30ae9fb5e1286a772d91a92e3622a
-- @specr-body-sha256: d45c46bcf4e86f914aad0503b4bf31ff8d78b69e7982b35e4bb059eb11e3bcd0
@[reducible]
def basicMemDeallocate (mem : BasicMemory) (ptr : MrPointer) (reqAlign : Align) (expectedSize : Nat) : Except TerminationInfo BasicMemory :=
  match mem.findAlloc ptr.allocId with
  | none => .error (.ub "deallocating invalid pointer")
  | some alloc =>
    if !alloc.live then
      .error (.ub "double-free")
    else if ptr.offset != 0 then
      .error (.ub "deallocating with pointer not to the beginning of its allocation")
    else if alloc.size != expectedSize then
      .error (.ub "deallocating with incorrect size information")
    else if alloc.align != reqAlign then
      .error (.ub "deallocating with incorrect alignment information")
    else
      let newAlloc := { alloc with live := false }
      let newAllocs := mem.allocs.map (fun a => if a.id == ptr.allocId then newAlloc else a)
      .ok { mem with allocs := newAllocs }

-- @specr-source: spec/lang/step/expressions.md:212-215 @ 5f78e227bbe30ae9fb5e1286a772d91a92e3622a
-- @specr-body-sha256: c82caaad911dd7878c37e76c490f6d83839b7e1e10c7283ce5fb24f0cb6767a0
@[reducible]
def mrProjectFieldOffset (baseOffset : Nat) (fieldOffsets : List Nat) (fieldIdx : Nat) : Except TerminationInfo Nat :=
  match fieldOffsets[fieldIdx]? with
  | some fOff => .ok (baseOffset + fOff)
  | none => .error (.ub "field projection to invalid field")

@[reducible]
def mrProjectIndexOffset (baseOffset elemSize index count : Nat) : Except TerminationInfo Nat :=
  if decide (index < count) then
    .ok (baseOffset + index * elemSize)
  else
    .error (.ub "access to out-of-bounds index")

@[reducible]
def mrProjectSubsliceBounds (len from_ to_ : Nat) (fromEnd : Bool) : Except TerminationInfo (Nat × Nat) :=
  let endIdx := if fromEnd then len - to_ else to_
  if decide (from_ ≤ endIdx ∧ endIdx ≤ len && (!fromEnd || to_ ≤ len)) then
    .ok (from_, endIdx)
  else
    .error (.ub "subslice projection out of bounds")

/-! ## 5. L4 Tree Borrows State Machine & Reborrow Settings (`spec/mem/tree_borrows/*.md`) -/

-- @specr-source: spec/mem/tree_borrows/state_machine_unprotected.md:27-32 @ 5f78e227bbe30ae9fb5e1286a772d91a92e3622a
-- @specr-body-sha256: e2b1137e33c653dfe5492130a92a79b8db1fd2fc3aeb3687e90a41d0083bb185
@[reducible]
def PermissionUnprot.local_read (self : PermissionUnprot) : Except TerminationInfo PermissionUnprot :=
  match self with
  | .Disabled => .error (.ub "Tree Borrows: local read of Disabled reference")
  | perm => .ok perm

-- @specr-source: spec/mem/tree_borrows/state_machine_unprotected.md:32-42 @ 5f78e227bbe30ae9fb5e1286a772d91a92e3622a
-- @specr-body-sha256: 59c9633343ddfc4923f6be30cbcf77e5ec17f9e16ddd45bdfdf973aeeb7a055a
@[reducible]
def PermissionUnprot.local_write (self : PermissionUnprot) : Except TerminationInfo PermissionUnprot :=
  match self with
  | .Frozen => .error (.ub "Tree Borrows: local write of Frozen reference")
  | .Disabled => .error (.ub "Tree Borrows: local write of Disabled reference")
  | .Cell => .ok .Cell
  | _ => .ok .Unique

-- @specr-source: spec/mem/tree_borrows/state_machine_unprotected.md:42-50 @ 5f78e227bbe30ae9fb5e1286a772d91a92e3622a
-- @specr-body-sha256: 010d88f00c4a7b6020f56b4fa3f3b0f73375c3f666c3f7532075c951606b6882
@[reducible]
def PermissionUnprot.foreign_read (self : PermissionUnprot) : Except TerminationInfo PermissionUnprot :=
  match self with
  | .Reserved => .ok .Reserved
  | .Unique => .ok .Frozen
  | perm => .ok perm

-- @specr-source: spec/mem/tree_borrows/state_machine_unprotected.md:50-58 @ 5f78e227bbe30ae9fb5e1286a772d91a92e3622a
-- @specr-body-sha256: 99a633db00c8dc80c05ed107b3a2b3faaf947060f7f6a8113356849684219f92
@[reducible]
def PermissionUnprot.foreign_write (self : PermissionUnprot) : Except TerminationInfo PermissionUnprot :=
  match self with
  | .Cell => .ok .Cell
  | .ReservedIm => .ok .ReservedIm
  | _ => .ok .Disabled

-- @specr-source: spec/mem/tree_borrows/state_machine_unprotected.md:59-72 @ 5f78e227bbe30ae9fb5e1286a772d91a92e3622a
-- @specr-body-sha256: 143c53b1b1643adcd6ac8d9335520bcd29e1121a9b21b1941e15e8749bb45cdc
@[reducible]
def PermissionUnprot.transition (self : PermissionUnprot) (access_kind : AccessKind) (node_relation : NodeRelation) : Except TerminationInfo PermissionUnprot :=
  match node_relation, access_kind with
  | .Local, .Read => self.local_read
  | .Local, .Write => self.local_write
  | .Foreign, .Read => self.foreign_read
  | .Foreign, .Write => self.foreign_write

-- @specr-source: spec/mem/tree_borrows/state_machine_unprotected.md:96-99 @ 5f78e227bbe30ae9fb5e1286a772d91a92e3622a
-- @specr-body-sha256: f26dd209704aed28914e148b9de5b1de7f8e859edebffa24ad02dee00b6047eb
@[reducible]
def PermissionUnprot.init_access (self : PermissionUnprot) : Option AccessKind :=
  match self with
  | .Cell => none
  | _ => some .Read

-- @specr-source: spec/mem/tree_borrows/state_machine_unprotected.md:73-74 @ 5f78e227bbe30ae9fb5e1286a772d91a92e3622a
-- @specr-body-sha256: 08914a24a2356c4b8c6151e17f13e42593f0337f95dc9bf59b0d533dc0f07c56
@[reducible]
def PermissionUnprot.prevents_deallocation (_self : PermissionUnprot) : Bool :=
  false

-- @specr-source: spec/mem/tree_borrows/state_machine_protected.md:29-37 @ 5f78e227bbe30ae9fb5e1286a772d91a92e3622a
-- @specr-body-sha256: 702974d7c426aabd89d93cb1619450003422c64c2356fcda7630256ad79b9b40
@[reducible]
def PermissionProt.local_read (self : PermissionProt) : Except TerminationInfo PermissionProt :=
  match self with
  | .Cell => .ok .Cell
  | .Reserved _ had_foreign_read => .ok (.Reserved true had_foreign_read)
  | .Unique => .ok .Unique
  | .Frozen _ => .ok (.Frozen true)
  | .Disabled => .error (.ub "Tree Borrows: local read of protected Disabled reference")

-- @specr-source: spec/mem/tree_borrows/state_machine_protected.md:39-48 @ 5f78e227bbe30ae9fb5e1286a772d91a92e3622a
-- @specr-body-sha256: 2af1cefd958db10403350fc613af70475c9a83da3898593ee2c6f04005aacb51
@[reducible]
def PermissionProt.local_write (self : PermissionProt) : Except TerminationInfo PermissionProt :=
  match self with
  | .Cell => .ok .Cell
  | .Unique => .ok .Unique
  | .Reserved _ false => .ok .Unique
  | .Reserved _ true => .error (.ub "Tree Borrows: local write to protected Reserved reference that had a foreign read")
  | .Frozen _ => .error (.ub "Tree Borrows: local write to protected Frozen reference")
  | .Disabled => .error (.ub "Tree Borrows: local write to protected Disabled reference")

-- @specr-source: spec/mem/tree_borrows/state_machine_protected.md:48-58 @ 5f78e227bbe30ae9fb5e1286a772d91a92e3622a
-- @specr-body-sha256: ed449bd0653f095abdc3e02bd207cc6927ad212e628de2a1d2c858fe7bbe6939
@[reducible]
def PermissionProt.foreign_read (self : PermissionProt) : Except TerminationInfo PermissionProt :=
  match self with
  | .Cell => .ok .Cell
  | .Unique => .error (.ub "Tree Borrows: foreign read of protected Unique reference")
  | .Reserved had_local_read _ => .ok (.Reserved had_local_read true)
  | .Frozen had_local_read => .ok (.Frozen had_local_read)
  | .Disabled => .ok .Disabled

-- @specr-source: spec/mem/tree_borrows/state_machine_protected.md:58-72 @ 5f78e227bbe30ae9fb5e1286a772d91a92e3622a
-- @specr-body-sha256: b53ea0d6566471120a981e3e0457c5317c8f76041057160e8ea90c6c46cf6060
@[reducible]
def PermissionProt.foreign_write (self : PermissionProt) : Except TerminationInfo PermissionProt :=
  match self with
  | .Cell => .ok .Cell
  | .Frozen true => .error (.ub "Tree Borrows: foreign write of protected Frozen reference which had a local read")
  | .Reserved true _ => .error (.ub "Tree Borrows: foreign write of protected Reserved reference which had a local read")
  | .Unique => .error (.ub "Tree Borrows: foreign read of protected Unique reference")
  | .Frozen false => .ok .Disabled
  | .Reserved false _ => .ok .Disabled
  | .Disabled => .ok .Disabled

-- @specr-source: spec/mem/tree_borrows/state_machine_protected.md:72-85 @ 5f78e227bbe30ae9fb5e1286a772d91a92e3622a
-- @specr-body-sha256: 143c53b1b1643adcd6ac8d9335520bcd29e1121a9b21b1941e15e8749bb45cdc
@[reducible]
def PermissionProt.transition (self : PermissionProt) (access_kind : AccessKind) (node_relation : NodeRelation) : Except TerminationInfo PermissionProt :=
  match node_relation, access_kind with
  | .Local, .Read => self.local_read
  | .Local, .Write => self.local_write
  | .Foreign, .Read => self.foreign_read
  | .Foreign, .Write => self.foreign_write

-- @specr-source: spec/mem/tree_borrows/state_machine_protected.md:85-90 @ 5f78e227bbe30ae9fb5e1286a772d91a92e3622a
-- @specr-body-sha256: d18a9bba40146bdaf1b0192abb5d20b0479e3fbd606167266c5af5857a29581a
@[reducible]
def PermissionProt.init_access (self : PermissionProt) : Option AccessKind :=
  match self with
  | .Cell => none
  | _ => some .Read

-- @specr-source: spec/mem/tree_borrows/state_machine_protected.md:110-119 @ 5f78e227bbe30ae9fb5e1286a772d91a92e3622a
-- @specr-body-sha256: 75cdb2ddadbeb162a8e94be32b915ec089201208a299d34912dc6e15d02e4a2b
@[reducible]
def PermissionProt.unprotect (self : PermissionProt) : PermissionUnprot × Option AccessKind :=
  match self with
  | .Unique => (.Unique, some .Write)
  | .Reserved true _ => (.Reserved, some .Read)
  | .Reserved false _ => (.Reserved, none)
  | .Frozen true => (.Frozen, some .Read)
  | .Frozen false => (.Frozen, none)
  | .Disabled => (.Disabled, none)
  | .Cell => (.Cell, none)

-- @specr-source: spec/mem/tree_borrows/state_machine_protected.md:119-127 @ 5f78e227bbe30ae9fb5e1286a772d91a92e3622a
-- @specr-body-sha256: b7d27cd30003a4d2e514e413adc956098507c93388534393aea0be4265158c00
@[reducible]
def PermissionProt.prevents_deallocation (self : PermissionProt) : Bool :=
  match self with
  | .Unique => true
  | .Reserved had_local_read _ => had_local_read
  | .Frozen had_local_read => had_local_read
  | .Disabled => false
  | .Cell => false

-- @specr-source: spec/mem/tree_borrows/state_machine.md:18-32 @ 5f78e227bbe30ae9fb5e1286a772d91a92e3622a
-- @specr-body-sha256: d5738a0d994c17b6ba744e7e65526b86db56c9da22d7cd3875981cefd441044f
@[reducible]
def Permission.transition (self : Permission) (access_kind : AccessKind) (node_relation : NodeRelation) : Except TerminationInfo Permission :=
  match self with
  | .Unprot p =>
    match p.transition access_kind node_relation with
    | .ok p' => .ok (.Unprot p')
    | .error e => .error e
  | .Prot p =>
    match p.transition access_kind node_relation with
    | .ok p' => .ok (.Prot p')
    | .error e => .error e

-- @specr-source: spec/mem/tree_borrows/state_machine.md:34-39 @ 5f78e227bbe30ae9fb5e1286a772d91a92e3622a
-- @specr-body-sha256: be292303cc97e330319f18c1d3edfac6e9d2f817637e2116a9f7676f20b08fd6
@[reducible]
def Permission.init_access (self : Permission) : Option AccessKind :=
  match self with
  | .Unprot p => p.init_access
  | .Prot p => p.init_access

-- @specr-source: spec/mem/tree_borrows/state_machine.md:41-46 @ 5f78e227bbe30ae9fb5e1286a772d91a92e3622a
-- @specr-body-sha256: d51eac007d7c3cd76ec79d2889c5ab4be836a717955af870877a5b4bf41465d3
@[reducible]
def Permission.unprotect (self : Permission) : Option (Permission × Option AccessKind) :=
  match self with
  | .Unprot _ => none
  | .Prot p =>
    let (new_perm, access) := p.unprotect
    some (.Unprot new_perm, access)

-- @specr-source: spec/mem/tree_borrows/state_machine.md:46-51 @ 5f78e227bbe30ae9fb5e1286a772d91a92e3622a
-- @specr-body-sha256: f16a81bb43b0e99d1167b1630104c8abcfa962418151a4d54e647270fe055e90
@[reducible]
def Permission.prevents_deallocation (self : Permission) : Bool :=
  match self with
  | .Unprot p => p.prevents_deallocation
  | .Prot p => p.prevents_deallocation

-- @specr-source: spec/mem/tree_borrows/reborrow_settings.md:90-130 @ 5f78e227bbe30ae9fb5e1286a772d91a92e3622a
-- @specr-body-sha256: 1471a1a4812e5a9fcd9bba8de31427276619a87f4104c2a35b30df9ec3bc6242
@[reducible]
def reborrow_permission
    (is_mutable : Bool) (prot : Protected) (_inside : Bool) (frozen : Bool) (_implicit_writes : Bool) :
    Permission :=
  let mk_perm (unprot : PermissionUnprot) (p : PermissionProt) : Permission :=
    if prot.yes then .Prot p else .Unprot unprot
  if !is_mutable then
    if frozen then
      mk_perm .Frozen (.Frozen false)
    else
      mk_perm .Cell .Cell
  else if frozen then
    mk_perm .Reserved (.Reserved false false)
  else
    mk_perm .ReservedIm (.Reserved false false)

@[reducible]
def reborrow_init_and_foreign_read
    (is_mutable : Bool) (prot : Protected) (inside : Bool) (frozen : Bool) (implicit_writes : Bool) :
    Except TerminationInfo Permission :=
  let p0 := reborrow_permission is_mutable prot inside frozen implicit_writes
  let pAfterInit : Except TerminationInfo Permission :=
    match p0.init_access with
    | none => .ok p0
    | some acc => p0.transition acc .Local
  match pAfterInit with
  | .ok p1 => p1.transition .Read .Foreign
  | .error e => .error e

-- @specr-source: spec/mem/tree_borrows/state_machine_unprotected.md:59-72 @ 5f78e227bbe30ae9fb5e1286a772d91a92e3622a
-- @specr-body-sha256: 143c53b1b1643adcd6ac8d9335520bcd29e1121a9b21b1941e15e8749bb45cdc
@[reducible]
def mrExpectedWritePerm
    (target_matches : Bool) (writer_tag : Option Nat) (entry_tag : Nat) (perm_unprot : PermissionUnprot) :
    PermissionUnprot :=
  match target_matches with
  | false => perm_unprot
  | true =>
    match writer_tag with
    | none =>
      match perm_unprot with
      | .Unique => .Disabled
      | .Frozen => .Disabled
      | .Reserved => .Reserved
      | .ReservedIm => .ReservedIm
      | .Cell => .Cell
      | .Disabled => .Disabled
    | some tag =>
      match Nat.beq entry_tag tag with
      | true =>
        match perm_unprot with
        | .Reserved => .Unique
        | .ReservedIm => .Unique
        | other => other
      | false =>
        match perm_unprot with
        | .Cell => .Cell
        | .ReservedIm => .ReservedIm
        | _ => .Disabled

/-! ## 6. L5 & L6 Control Flow, Calls, & Machine Step (`spec/lang/step/terminators.md`, `spec/lang/machine.md`) -/

-- @specr-source: spec/lang/machine.md:34-42 @ 5f78e227bbe30ae9fb5e1286a772d91a92e3622a
-- @specr-body-sha256: f473d51dd92f4e6019085762dfc034459772bec162a2040916aaaebe77e2c3f1
inductive StackPopAction : Type where
  | BottomOfStack
  | BackToCaller (next_block : Option Nat) (unwind_block : Option Nat) (ret_val_ptr : MrPointer)
  deriving DecidableEq, Repr

-- @specr-source: spec/lang/machine.md:30-34 @ 5f78e227bbe30ae9fb5e1286a772d91a92e3622a
-- @specr-body-sha256: a409573d7feecf1505090a8f90e1d3634d6d236812b0b65aff3074b255ad87fa
structure MrStackFrame : Type where
  func_id : Nat := 0
  blockIdx : Nat
  stmtIdx : Nat
  stack_pop_action : StackPopAction := .BottomOfStack
  deriving DecidableEq, Repr

-- @specr-source: spec/lang/machine.md:297-299 @ 5f78e227bbe30ae9fb5e1286a772d91a92e3622a
-- @specr-body-sha256: 4ab379d88f0416f637c1e985d5c9ceb2d45302dbba3598d8da14dbe51b7272a1
@[reducible]
def MrStackFrame.jump_to_block (frame : MrStackFrame) (b : Nat) : MrStackFrame :=
  { frame with blockIdx := b, stmtIdx := 0 }

-- @specr-source: spec/lang/machine.md:185-223 @ 5f78e227bbe30ae9fb5e1286a772d91a92e3622a
-- @specr-body-sha256: 32d9fb313193500b87a453e9a585fe65f36385a2ac1ae36e0f470e76db2aea82
@[reducible]
def mrAdvanceStmtPc (stmtIdx : Nat) : Nat :=
  stmtIdx + 1

-- @specr-source: spec/lang/step/terminators.md:9-10 @ 5f78e227bbe30ae9fb5e1286a772d91a92e3622a
-- @specr-body-sha256: c82caaad911dd7878c37e76c490f6d83839b7e1e10c7283ce5fb24f0cb6767a0
@[reducible]
def mrLookupSwitchTarget (val : Nat) : List (Nat × Nat) → Nat → Nat
  | [], fallback => fallback
  | (branchVal, target) :: rest, fallback =>
    match Nat.beq val branchVal with
    | true => target
    | false => mrLookupSwitchTarget val rest fallback

-- @specr-source: spec/lang/machine.md:321-337 @ 5f78e227bbe30ae9fb5e1286a772d91a92e3622a
-- @specr-body-sha256: 6803846d65122ecb429cb2ff3b75899460931e276051e8365b294b8180b70b51
@[reducible]
def mrFindCalleeById {α : Type} : List (String × α) → String → Option α
  | [], _ => none
  | (name, body) :: rest, defPath =>
    if name == defPath then some body else mrFindCalleeById rest defPath

-- @specr-source: spec/lang/step/terminators.md:9-10 @ 5f78e227bbe30ae9fb5e1286a772d91a92e3622a
-- @specr-body-sha256: c82caaad911dd7878c37e76c490f6d83839b7e1e10c7283ce5fb24f0cb6767a0
inductive MrUnwindOutcome : Type where
  | faultUb
  | abort
  | panic
  | cleanup (bb : Nat)
  deriving DecidableEq, Repr

@[reducible]
def mrApplyUnwindAction (unwind_block : Option Nat) (is_terminate is_unreachable : Bool) : MrUnwindOutcome :=
  if is_unreachable then
    .faultUb
  else if is_terminate then
    .abort
  else
    match unwind_block with
    | some bb => .cleanup bb
    | none => .panic

-- @specr-source: spec/lang/machine.md:185-223 @ 5f78e227bbe30ae9fb5e1286a772d91a92e3622a
-- @specr-body-sha256: 32d9fb313193500b87a453e9a585fe65f36385a2ac1ae36e0f470e76db2aea82
@[reducible]
def mrStepDispatchIsTerminator (next_stmt stmt_len : Nat) : Bool :=
  next_stmt == stmt_len

/-! ## 7. General-Purpose AST-Lowered Specr Declarations -/

-- @specr-source: spec/prelude/target.md:32..33 (x86_64)
-- @specr-body-sha256: 8ca910b762f39c45b0853d8853277881cb06841e20093f618151ae44d680c9fd
structure x86_64 : Type where
  mk ::
  deriving Inhabited, DecidableEq, Repr

-- @specr-source: spec/mem/concurrent.md:10..11 (Atomicity)
-- @specr-body-sha256: 33bb11c47d69c866b830d8e542f4db3095d1029361eb78d7b25a930998b7ce61
inductive Atomicity : Type where
  | Atomic : Atomicity
  | None : Atomicity
  deriving Inhabited, DecidableEq, Repr

-- @specr-source: spec/mem/concurrent.md:11..14 (AccessType)
-- @specr-body-sha256: a5152f4e1d67172e6467d7c4a6bd8563f07475dbc53e0265d4a25eb6eabc042e
inductive AccessType : Type where
  | Store : AccessType
  | Load : AccessType
  deriving Inhabited, DecidableEq, Repr

-- @specr-source: spec/mem/concurrent.md:130..130 (ThreadId)
-- @specr-body-sha256: f77e777772cd7c14c6cd18fb5d92f37eb9d6321dc57c2957101b6f9ff9080af7
abbrev ThreadId : Type := SpecrInt

-- @specr-source: spec/mem/pointer.md:22..22 (Address)
-- @specr-body-sha256: 82ead93fe04a74b348e74bd4aeb5876f229a62cb8cdcd42bb259549803b6bd5f
abbrev Address : Type := SpecrInt

-- @specr-source: spec/mem/pointer.md:77..79 (TupleHeadLayout)
-- @specr-body-sha256: 3555aea2a65700687a82383bb771774ca6c715cda940f12878129b7912d1c05e
structure TupleHeadLayout : Type where
  end_ : Offset
  align : Align
  packed_align : Option (Align)
  deriving Inhabited, DecidableEq, Repr

-- @specr-source: spec/mem/tree_borrows/memory.md:36..36 (ChildId)
-- @specr-body-sha256: a090086f1261d3068f02ff44a31171bd6bb6a9aa7927a6674e194918646b7516
abbrev ChildId : Type := SpecrInt

-- @specr-source: spec/mem/tree_borrows/memory.md:36..36 (Path)
-- @specr-body-sha256: fa7d66fde967a8e014942c893e9175e9be508a828a252ad59243ed7ca9e2ea52
abbrev Path : Type := List (ChildId)

-- @specr-source: spec/mem/tree_borrows/memory.md:45..45 (TreeBorrowsProvenance)
-- @specr-body-sha256: 830fb2dd2944e077aa97e3229fae78dd3bbe6d492d3fd46841d6cd094e4c5fce
abbrev TreeBorrowsProvenance : Type := (AllocId × Path)

-- @specr-source: spec/mem/tree_borrows/memory.md:55..56 (TreeBorrowsFrameExtra)
-- @specr-body-sha256: a64379c7a9372b8da072b16422023831d27413d0aa86d6c147300fcc262ed1be
structure TreeBorrowsFrameExtra : Type where
  protectors : List (TreeBorrowsProvenance)
  deriving Inhabited, DecidableEq, Repr

-- @specr-source: spec/mem/tree_borrows/reborrow_settings.md:7..9 (ReborrowSettings)
-- @specr-body-sha256: f4746db5080876704c6c0ed3d91a0dfefe585fc59417c8949f6504832b1458ef
structure ReborrowSettings : Type where
  inside : List (Permission)
  outside : Permission
  protected_ : Protected
  deriving Inhabited, DecidableEq, Repr

-- @specr-source: spec/lang/syntax.md:327..328 (CallingConvention)
-- @specr-body-sha256: 1140472b4b32cdc070f82ed476d82a0195879059f7fde408ad3665f78f6891bd
inductive CallingConvention : Type where
  | Rust : CallingConvention
  | C : CallingConvention
  deriving Inhabited, DecidableEq, Repr

-- @specr-source: spec/lang/syntax.md:328..331 (IntrinsicLockOp)
-- @specr-body-sha256: fb1dd19009806a9b4146c0295a3b810059a5e2e87f432cd974716d954482b5a7
inductive IntrinsicLockOp : Type where
  | Acquire : IntrinsicLockOp
  | Release : IntrinsicLockOp
  | Create : IntrinsicLockOp
  deriving Inhabited, DecidableEq, Repr

-- @specr-source: spec/lang/syntax.md:331..341 (IntrinsicOp)
-- @specr-body-sha256: 4d2a0ede8e4ca5603c04f270ef56aaf4d05d7b6426a52f1fc2d414720672747e
inductive IntrinsicOp : Type where
  | Abort : IntrinsicOp
  | Assume : IntrinsicOp
  | Exit : IntrinsicOp
  | PrintStdout : IntrinsicOp
  | PrintStderr : IntrinsicOp
  | Allocate : IntrinsicOp
  | Deallocate : IntrinsicOp
  | Spawn : IntrinsicOp
  | Join : IntrinsicOp
  | RawEq : IntrinsicOp
  | AtomicStore : IntrinsicOp
  | AtomicLoad : IntrinsicOp
  | AtomicCompareExchange : IntrinsicOp
  | AtomicFetchAndOp (arg_0 : IntBinOp) : IntrinsicOp
  | Lock (arg_0 : IntrinsicLockOp) : IntrinsicOp
  | PointerExposeProvenance : IntrinsicOp
  | PointerWithExposedProvenance : IntrinsicOp
  | GetUnwindPayload : IntrinsicOp
  deriving Inhabited, DecidableEq, Repr

-- @specr-source: spec/lang/syntax.md:468..472 (BbKind)
-- @specr-body-sha256: bd68be1b2a027cd0c5b497de0451e040f88013ae61c42b9148c2c0a4e528b89f
inductive BbKind : Type where
  | Regular : BbKind
  | Cleanup : BbKind
  | Catch : BbKind
  | Terminate : BbKind
  deriving Inhabited, DecidableEq, Repr

-- @specr-source: spec/lang/step/locks.md:9..12 (LockState)
-- @specr-body-sha256: ae0b08d5103ca1683fe1b4ec47309567bc966051148a2d98c1bc47dd9add4efe
inductive LockState : Type where
  | Unlocked : LockState
  | LockedBy (arg_0 : ThreadId) : LockState
  deriving Inhabited, DecidableEq, Repr

-- @specr-source: spec/lang/step/locks.md:14..14 (LockId)
-- @specr-body-sha256: 60772fdf4b522b35b883396b6590965e187498f99da703c5c3567143ea02f733
abbrev LockId : Type := SpecrInt

-- @specr-source: spec/mem/concurrent.md:14..19 (Access)
-- @specr-body-sha256: 2e9662e4a546c7e94381afb6e647dfd8b25bd24fd3828be59648c202047214e0
structure Access : Type where
  ty : AccessType
  atomicity : Atomicity
  addr : Address
  len : Size
  deriving Inhabited, DecidableEq, Repr

-- @specr-source: spec/mem/tree_borrows/state_machine.md:51..58 (Permission::matches_protector)
-- @specr-body-sha256: fa3ea07651236d42fa8c2bd21515148dec745bfe77f5a31986e22400b92ea579
@[reducible]
def Permission_matches_protector (self : Permission) (protected_ : Protected) : Bool :=
  if (protected_.yes) then
    (match self with | (.Prot _) => true | _ => false)
  else
    (match self with | (.Unprot _) => true | _ => false)

abbrev Permission.matches_protector := Permission_matches_protector

-- @specr-source: spec/lang/types.md:201..204 (TupleHeadLayout::capped_tail_align)
-- @specr-body-sha256: ab947fd4debe06d23361cb8acef3b6f13fce02f96d12e404f3f337a059be6430
@[reducible]
def TupleHeadLayout_capped_tail_align (self : TupleHeadLayout) (tail_align : Align) : Align :=
  match self.packed_align with
  | (some packed_align) => (min tail_align packed_align)
  | none => tail_align

abbrev TupleHeadLayout.capped_tail_align := TupleHeadLayout_capped_tail_align

-- @specr-source: spec/lang/representation.md:482..483 (ensure_else_ub)
-- @specr-body-sha256: 0b7249502c88a1d7c26824e01c63bb470925f1e20584de6efbb465ad8477668b
@[reducible]
def ensure_else_ub (b : Bool) (msg : String) : Except TerminationInfo (Unit) :=
  if (!b) then
    (.error (.ub msg))
  else
    (.ok ())

-- @specr-source: spec/lang/well-formed.md:12..15 (ensure_wf)
-- @specr-body-sha256: 0c83b0bdf8cc64db91b333aea611b1ecb303f4160dd85232f540fc6701eac0cb
@[reducible]
def ensure_wf (b : Bool) (msg : String) : Except TerminationInfo (Unit) :=
  if (!b) then
    (.error (.illFormed msg))
  else
    (.ok ())

end MiniRust.Snapshots.S2026_05_Matched.Generated.Ops
