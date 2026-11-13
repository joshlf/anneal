-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

-- anneal-trust-tier: candidate:mvp
prelude
import Init.Data.BitVec.Basic
import Trusted.Mvp.Syntax

namespace Trusted.Mvp

/--
Logical storage words have 64 bits; narrower integers have zero high bits.
Unit is encoded as zero without claiming a physical size for a Rust unit value.
-/
abbrev Word := BitVec 64

/-!
Typed loads enforce primitive validity. The compiler calls loading a place
"a fundamentally *typed* operation" and notes that validity violations can be
UB at `Operand`:
https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/mir/syntax.rs

The integer width and signedness come from capture, not from a proof-supplied
codec. Booleans are 0 or 1; fieldless enum indices must name an existing
variant.
The enum table holds raw 64-bit isize discriminants, including negative values
in two's-complement form. Other enum representations are refused by capture.

For booleans, the pinned `Scalar::to_bool` admits only `0 => interp_ok(false)`
and `1 => interp_ok(true)`:
https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/mir/interpret/value.rs

For enum validity, the pinned validator requires "a valid enum tag" and rejects
"an uninhabited enum variant" at `ValidityVisitor::read_discriminant`:
https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_const_eval/src/interpret/validity.rs

The pinned type syntax calls `Never` "The never type `!`" and `Tuple` "A tuple
type". Only the empty tuple is admitted here, with one logical value:
https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_type_ir/src/ty_kind.rs

The validator rejects "a value of the never type `!`". Thus an unused never
local is admitted, while no initialized word is valid at that type:
https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_const_eval/src/interpret/validity.rs
-/

def Ty.admitted : Ty → Bool
  | .never | .unit => true
  | .bool => true
  | .int bits _ => (bits == 8) || (bits == 16) || (bits == 32) || (bits == 64)
  | .enum _ ds => !ds.isEmpty && decide (ds.length < Nat.pow 2 64) &&
      ds.all (fun d => decide (d < Nat.pow 2 64)) &&
      decide (ds.Pairwise (fun a b => a ≠ b))

def validValue (ty : Ty) (value : Word) : Bool :=
  ty.admitted && match ty with
    | .never => false
    | .unit => value == 0
    | .bool => decide (value.toNat < 2)
    | .int bits _ => if bits == 64 then true else
        decide (value.toNat < Nat.pow 2 bits)
    | .enum _ ds => decide (value.toNat < ds.length)

def rawValid (ty : Ty) (bits : Nat) : Bool :=
  decide (bits < Nat.pow 2 64) && validValue ty (BitVec.ofNat 64 bits)

def operandTy (body : Body) : Operand → Option Ty
  | .copy index | .move index => body.localTys[index]?
  | .constant ty bits => if rawValid ty bits then some ty else none

/-!
The pinned `Rvalue::BinaryOp` requires matching operand types for comparisons
and arithmetic. Comparisons accept booleans or integers in this fragment and
"return a `bool`". Shifts accept integer operands "not necessarily of the same
type" and return the LHS type. Bitwise operations accept matching integer or
Boolean types and "return a value of that type". Addition, subtraction and
multiplication accept matching integers and return that type.

The successful operator cases are named explicitly in typing and evaluation.
Adding a BinOp must expose the missing decisions: a wildcard success could
otherwise assign a new operation an integer result and false comparison value.

This fragment omits the compiler's other operand classes and operators. The
admitted integer widths are checked by `Ty.admitted` above:
https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/mir/syntax.rs#L1412-L1423
-/

def binaryTy (op : BinOp) (left right : Ty) : Option Ty :=
  if !(left.admitted && right.admitted) then none else
  match op, left, right with
  | .shl, .int bits signed, .int _ _
  | .shr, .int bits signed, .int _ _ => some (.int bits signed)
  | .eq, .bool, .bool | .ne, .bool, .bool
  | .lt, .bool, .bool | .le, .bool, .bool
  | .gt, .bool, .bool | .ge, .bool, .bool => some .bool
  | .bitAnd, .bool, .bool | .bitOr, .bool, .bool
  | .bitXor, .bool, .bool => some .bool
  | op, .int bits signed, .int bits' signed' =>
      if (bits == bits') && (signed == signed') then
        match op with
        | .eq | .ne | .lt | .le | .gt | .ge => some .bool
        | .bitAnd | .bitOr | .bitXor | .shl | .shr | .add | .sub | .mul =>
            some (.int bits signed)
      else none
  | _, _, _ => none

/--
MIR `Discriminant` returns "an integer of type" `discriminant_ty`; the enum arm
of that query uses `adt.repr().discr_type().to_ty(tcx)`:
https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/mir/syntax.rs#L1433-L1443
https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/ty/sty.rs#L1682-L1686

Capture admits only `IntegerType::Pointer(true)` enum discriminants. The pinned
mapping is "IntegerType::Pointer(true) => tcx.types.isize":
https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/ty/util.rs#L106-L114

Capture selects only `x86_64-unknown-linux-gnu` and checks its 64-bit compiler
pointer layout. For isize, the compiler selects `ptr_sized_integer()`; this
target's 64-bit pointer index maps to `I64`. Thus this typing rule and
`evalRvalue` use signed 64-bit isize data, not the logical variant index:
https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/ty/layout.rs#L47-L57
https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_abi/src/lib.rs#L316-L321
https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_abi/src/lib.rs#L637-L644
https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_target/src/spec/targets/x86_64_unknown_linux_gnu.rs#L24-L35

This is the discriminant's typeck type. The compiler notes that layout may use
"a smaller type for the tag that stores the discriminant at runtime"; the
owned logical encoding does not substitute that physical tag type:
https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_abi/src/lib.rs#L195-L204
-/
def rvalueTy (body : Body) : Rvalue → Option Ty
  | .unit => some .unit
  | .use operand _ => operandTy body operand
  | .binary op left right =>
      match operandTy body left, operandTy body right with
      | some lt, some rt => binaryTy op lt rt
      | _, _ => none
  | .discriminant index =>
      match body.localTys[index]? with
      | some (.enum _ _) => some (.int 64 true)
      | _ => none

/--
MIR requires "Assignments in which the types of the place and rvalue differ
are not well-formed." The scalar model retains exact captured types, including
integer signedness and enum identity, so a matching word width cannot replace
this assignment-type check:
https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/mir/syntax.rs#L307-L332
-/
def statementWF (body : Body) : Statement → Bool
  | .assign index rhs =>
      match body.localTys[index]?, rvalueTy body rhs with
      | some lt, some rt => lt == rt
      | _, _ => false
  | .storageLive index | .storageDead index => decide (index < body.localTys.length)
  | .nop => true

/--
`SwitchInt` accepts a "signed or unsigned integer, char, or bool" operand, and
"Target values may not appear more than once." This fragment omits chars and
checks the remaining type, target values and block indices before execution;
a logical enum index must first pass through its discriminant operation:
https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/mir/syntax.rs#L695-L707
-/
def switchTy : Ty → Bool
  | .bool | .int _ _ => true
  | _ => false

def terminatorWF (body : Body) : Terminator → Bool
  | .goto target => decide (target < body.blocks.length)
  | .switchInt operand targets otherwise =>
      match operandTy body operand with
      | none => false
      | some ty => switchTy ty &&
          decide (otherwise < body.blocks.length) &&
          targets.all (fun entry => rawValid ty entry.1 &&
            decide (entry.2 < body.blocks.length)) &&
          decide ((targets.map Prod.fst).Pairwise (fun a b => a ≠ b))
  | .ret | .unreachable => true

/--
Static admission is independent of all caller and functional predicates. A
contradictory unsafe caller requirement cannot excuse malformed syntax or
unsupported types. Admission alone establishes no execution safety: an
`unreachable` terminator is well-formed syntax and faults if reached.
-/
def bodyWF (body : Body) : Bool :=
  decide (body.argCount < body.localTys.length) && !body.blocks.isEmpty &&
  body.localTys.all Ty.admitted &&
  body.blocks.all (fun block => block.statements.all (statementWF body) &&
    terminatorWF body block.terminator)

/-!
`StorageLive` allocates fresh uninitialized storage; `StorageDead` frees it.
The compiler specifies "Using a local in any way (not only reading/writing
from it) while it is unallocated is UB" and says unmarked locals are
"implicitly allocated for the full duration of the function":
https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/mir/syntax.rs#L364-L377

For repeated live markers it states: "If the local is already allocated,
calling `StorageLive` again will implicitly free the local and then allocate
fresh uninitialized memory." It also says "calling `StorageDead` again is a
NOP" for an already deallocated local:
https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/mir/syntax.rs#L379-L382

These rules need three states: dead, allocated-uninitialized, and initialized.
They justify `execStatement` resetting a live value to `.uninit`, rather than
keeping its value or assuming the repeated marker cannot execute. Parameters
start initialized even when the body contains a storage marker for them.
-/

inductive Slot where
  | dead
  | uninit
  | value (word : Word)

structure State where
  block : Nat
  statement : Nat
  locals : List Slot

inductive Fault where
  | badBlock
  | badPosition
  | badLocal
  | deadLocal
  | uninitialized
  | invalidValue
  | typeMismatch
  | unreachable

inductive StepResult where
  | next (state : State)
  | ret (word : Word)
  | fault (reason : Fault)

def hasStorageMarker (body : Body) (index : Nat) : Bool :=
  body.blocks.any (fun block => block.statements.any (fun stmt =>
    match stmt with
    | .storageLive l | .storageDead l => l == index
    | _ => false))

/--
Caller-provided arguments occupy MIR locals `1..=argCount`; local zero is the
return place. Install those initialized values before applying storage-marker
policy. The pinned layout and initialization contract is quoted at `argsValid`.
-/
def initialSlot (body : Body) (args : List Word) (index : Nat) : Slot :=
  if (0 < index) && (index ≤ body.argCount) then
    match args[index - 1]? with
    | some value => .value value
    | none => .uninit
  else if hasStorageMarker body index then .dead else .uninit

/--
The pinned compiler declares "const START_BLOCK = 0" and defines a block's
start location with "statement_index: 0". Capture preserves both index orders,
so entry uses these locations instead of a proof-selected starting state:
https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/mir/mod.rs#L1294-L1308
-/
def initial (body : Body) (args : List Word) : State :=
  ⟨0, 0, (List.range body.localTys.length).map (initialSlot body args)⟩

/--
The pinned `Body::arg_count` contract says: "Starting at local 1, `arg_count`
locals will be provided by the caller and can be assumed to be initialized."
The local declaration order puts the return place first, and `Local` declares
"const RETURN_PLACE = 0":
https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/mir/mod.rs#L235-L251
https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/mir/mod.rs#L859-L868

Thus zero-based argument `index` has its captured type at MIR local `index + 1`.
`initialSlot` must use the same offset when installing the caller's values.

The entry domain comes from captured types and argument count. Keeping it
separate from authored predicates prevents a specification from redefining which
safe-function inputs the baseline must cover. A genuinely uninhabited argument
type can still leave this structural domain empty.
-/
def argsValid (body : Body) (args : List Word) : Prop :=
  args.length = body.argCount ∧
  ∀ index value, args[index]? = some value →
    ∃ ty, body.localTys[index + 1]? = some ty ∧ validValue ty value = true

-- The static type table does not establish current allocation or
-- initialization. Storage markers and moves can change those facts. Validate
-- at each load so a stale slot cannot become a usable value merely because its
-- type is admitted.
def readLocal (body : Body) (locals : List Slot) (index : Nat) :
    Except Fault (Ty × Word) :=
  match body.localTys[index]?, locals[index]? with
  | some ty, some (.value value) =>
      if validValue ty value then .ok (ty, value) else .error .invalidValue
  | some _, some .dead => .error .deadLocal
  | some _, some .uninit => .error .uninitialized
  | _, _ => .error .badLocal

/-!
Moves remain distinct from copies. As a conservative admission restriction,
a move invalidates the source slot. The compiler says it "*may* additionally
overwrite the place with `uninit` bytes" and forbids relying on a subsequent
load without reinitialization at `Operand::Move`:
https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/mir/syntax.rs

The pinned interpreter currently copies for regular non-call operands. Thus a
move-related model fault is a refusal, not a claim of actual Rust UB. No calls,
pointers, aliases, or drop glue are admitted in this fragment.

The same `Operand` definition states: "Constants are already semantically
values, and remain unchanged." This fragment admits only captured scalar
constants and checks their type's logical encoding before constructing a Word:
https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/mir/syntax.rs#L1332-L1333
-/

def evalOperand (body : Body) (locals : List Slot) : Operand →
    Except Fault (Ty × Word × List Slot)
  | .copy index =>
      match readLocal body locals index with
      | .ok (ty, value) => .ok (ty, value, locals)
      | .error reason => .error reason
  | .move index =>
      match readLocal body locals index with
      | .ok (ty, value) => .ok (ty, value, locals.set index .uninit)
      | .error reason => .error reason
  | .constant ty bits =>
      if rawValid ty bits then .ok (ty, BitVec.ofNat 64 bits, locals)
      else .error .invalidValue

def truncate (bits : Nat) (value : Word) : Word :=
  if bits == 64 then value
  else BitVec.ofNat 64 (Nat.mod value.toNat (Nat.pow 2 bits))

def signedValue (bits : Nat) (value : Word) : Int :=
  (value.setWidth bits).toInt

/-!
Admitted ordinary addition, subtraction and multiplication wrap; their
distinct `*Unchecked` constructors are UB on overflow and are not admitted.
`BinOp::Shl` states: "The offset is given by
`RHS.rem_euclid(LHS::BITS)`". `Shr` is arithmetic for signed LHS and logical
otherwise. Shift operands may have different widths and signedness:
https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/mir/syntax.rs

The pinned interpreter computes the signed RHS remainder before shifting, and
truncates signed results to the LHS width at `binary_int_op`:
https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_const_eval/src/interpret/operator.rs

The ordinary shift therefore accepts negative and out-of-range RHS values;
it does not confuse them with unchecked-shift UB.

For signed ordered comparisons the interpreter applies the comparison to
`l_signed()` and `r_signed()`. Add, subtract and multiply use overflowing
arithmetic and truncate to the operand layout; the unsigned path says
"Truncate to target type." For these arithmetic operations, only their unchecked
counterparts make overflow UB. The model's zero high bits and the
`signedValue`/`truncate` helpers retain the signed values and bounded results:
https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_const_eval/src/interpret/operator.rs#L174-L237
https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_const_eval/src/interpret/operator.rs#L242-L282
-/

def shiftAmount (lhsBits : Nat) (rhsTy : Ty) (rhs : Word) : Nat :=
  match rhsTy with
  | .int bits true => (Int.emod (signedValue bits rhs) (Int.ofNat lhsBits)).toNat
  | _ => Nat.mod rhs.toNat lhsBits

-- This helper is total and returns false for listed noncomparison operators.
-- evalBinary dispatches only its comparison cases here. Naming the remaining
-- cases preserves that answer while exposing additions to the operator grammar.
def comparison (op : BinOp) (signed : Bool) (bits : Nat)
    (left right : Word) : Bool :=
  match op with
  | .eq => left == right
  | .ne => left != right
  | .lt => if signed then decide (signedValue bits left < signedValue bits right)
      else decide (left.toNat < right.toNat)
  | .le => if signed then decide (signedValue bits left ≤ signedValue bits right)
      else decide (left.toNat ≤ right.toNat)
  | .gt => if signed then decide (signedValue bits right < signedValue bits left)
      else decide (right.toNat < left.toNat)
  | .ge => if signed then decide (signedValue bits right ≤ signedValue bits left)
      else decide (right.toNat ≤ left.toNat)
  | .bitAnd | .bitOr | .bitXor | .shl | .shr | .add | .sub | .mul => false

def boolWord (value : Bool) : Word := if value then 1 else 0

-- Operand typing and result validity are separate checks. Knowing the result
-- type does not prove that the computed 64-bit word encodes a value of that
-- type, especially for narrower integers and booleans.
def evalBinary (op : BinOp) (lt : Ty) (left : Word) (rt : Ty) (right : Word) :
    Except Fault (Ty × Word) :=
  match binaryTy op lt rt with
  | none => .error .typeMismatch
  | some resultTy =>
      let bits := match lt with | .int n _ => n | _ => 1
      let signed := match lt with | .int _ s => s | _ => false
      let result := match op with
        | .bitAnd => BitVec.and left right
        | .bitOr => BitVec.or left right
        | .bitXor => BitVec.xor left right
        | .shl => truncate bits (BitVec.shiftLeft left (shiftAmount bits rt right))
        | .shr => if signed then
            truncate bits (BitVec.ofInt 64
              (Int.shiftRight (signedValue bits left) (shiftAmount bits rt right)))
          else BitVec.ushiftRight left (shiftAmount bits rt right)
        | .add => truncate bits (left + right)
        | .sub => truncate bits (left - right)
        | .mul => truncate bits (BitVec.mul left right)
        | .eq | .ne | .lt | .le | .gt | .ge =>
            boolWord (comparison op signed bits left right)
      if validValue resultTy result then .ok (resultTy, result)
      else .error .invalidValue

/-!
`Use` yields its operand "unchanged, except for a potential retag"; the flag is
preserved in syntax. With no pointers or references, there is no alias
permission for a retag to change. `Discriminant` uses the compiler table rather than the
logical index, as required by `Rvalue::Discriminant`:
https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/mir/syntax.rs

That source calls the discriminant's underlying validity requirements
"undecided". This admitted model conservatively requires an initialized, valid
enum for the operation; failing that check is refusal rather than a claim that
the Rust language has resolved this validity question.

The unit rvalue is exactly `AggregateKind::Tuple` with an empty operand list.
The compiler describes `Aggregate` as creating "a tuple or struct". Capture
admits only the empty tuple constructor, with no operand evaluation or fields:
https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/mir/syntax.rs
-/

/-!
MIR leaves the abstract operand order at "Which order?". The pinned interpreter
evaluates the left operand before the right; codegen likewise generates
"let lhs = self.codegen_operand(bx, lhs);" before the corresponding RHS.
Left-to-right threading here follows these pinned implementations, rather than
claiming the abstract MIR documentation has resolved the order:
https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/mir/syntax.rs#L1359-L1361
https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_const_eval/src/interpret/step.rs#L182-L189
https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_codegen_ssa/src/mir/rvalue.rs#L564-L568

Admitted binary operands are bools and integers, which have primitive `Copy`
implementations. Fieldless enums have no admitted binary operations. Copies
and constants have no storage effects here, but an explicit MIR move still
uses the conservative invalidation rule above. Thread that change through both
operands so evaluating the RHS against old locals cannot erase it:
https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/library/core/src/marker.rs#L466-L477
-/
def evalRvalue (body : Body) (locals : List Slot) : Rvalue →
    Except Fault (Ty × Word × List Slot)
  | .unit => .ok (.unit, 0, locals)
  | .use operand _ => evalOperand body locals operand
  | .binary op left right =>
      match evalOperand body locals left with
      | .error reason => .error reason
      | .ok (lt, lv, locals') =>
          match evalOperand body locals' right with
          | .error reason => .error reason
          | .ok (rt, rv, locals'') =>
              match evalBinary op lt lv rt rv with
              | .ok (ty, value) => .ok (ty, value, locals'')
              | .error reason => .error reason
  | .discriminant index =>
      match readLocal body locals index with
      | .error reason => .error reason
      | .ok (.enum _ ds, value) =>
          match ds[value.toNat]? with
          | some disc => .ok (.int 64 true, BitVec.ofNat 64 disc, locals)
          | none => .error .invalidValue
      | .ok _ => .error .typeMismatch

-- An allocated uninitialized slot can receive its first value. A dead slot
-- still needs allocation even when its old value is irrelevant, so overwriting
-- a local cannot bypass the storage check.
def writeLocal (body : Body) (locals : List Slot) (index : Nat)
    (ty : Ty) (value : Word) : Except Fault (List Slot) :=
  match body.localTys[index]?, locals[index]? with
  | some targetTy, some slot =>
      if targetTy != ty then .error .typeMismatch
      else if !(validValue targetTy value) then .error .invalidValue
      else match slot with
        | .dead => .error .deadLocal
        | _ => .ok (locals.set index (.value value))
  | _, _ => .error .badLocal

/--
The pinned interpreter dispatches assignment to `eval_rvalue_into_place`. The
scalar model evaluates the RHS and writes the matching typed value; calls,
padding, pointers and destruction are outside its admitted representation:
https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_const_eval/src/interpret/step.rs#L75-L94

`Nop` is "Useful for deleting instructions without affecting statement
indices." It preserves storage here while `step` still advances the cursor.
Storage-marker transitions follow the repeated-allocation rules quoted above:
https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/mir/syntax.rs#L442-L443
-/
def execStatement (body : Body) (locals : List Slot) : Statement →
    Except Fault (List Slot)
  | .assign index rhs =>
      match evalRvalue body locals rhs with
      | .error reason => .error reason
      | .ok (ty, value, locals') => writeLocal body locals' index ty value
  | .storageLive index =>
      if (index < body.localTys.length) && (index < locals.length) then
        .ok (locals.set index .uninit)
      else .error .badLocal
  | .storageDead index =>
      if (index < body.localTys.length) && (index < locals.length) then
        .ok (locals.set index .dead)
      else .error .badLocal
  | .nop => .ok locals

/-!
The compiler says `Goto` has "one successor" and `SwitchInt` evaluates its
operand then chooses an equal target, or otherwise the default target.
`Return` transfers the return place `_0`; executing `Unreachable` "is UB":
https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/mir/syntax.rs

Every absent block, invalid position, invalid load, or unsupported type faults.
There is no implicit transition or empty outcome set that could hide a stuck
execution. A fault can also represent conservative refusal, as with moves.
-/

def switchTarget (value : Nat) (targets : List (Nat × Nat))
    (otherwise : Nat) : Nat :=
  match targets.find? (fun entry => value == entry.1) with
  | some entry => entry.2
  | none => otherwise

def execTerminator (body : Body) (state : State) : Terminator → StepResult
  | .goto block => .next ⟨block, 0, state.locals⟩
  | .switchInt operand targets otherwise =>
      match evalOperand body state.locals operand with
      | .error reason => .fault reason
      | .ok (ty, value, locals) =>
          if switchTy ty then
            .next ⟨switchTarget value.toNat targets otherwise, 0, locals⟩
          else .fault .typeMismatch
  | .ret =>
      match readLocal body state.locals 0 with
      | .ok (_, value) => .ret value
      | .error reason => .fault reason
  | .unreachable => .fault .unreachable

/--
The pinned interpreter evaluates the indexed statement and then performs
"statement_index += 1"; once statements are exhausted, it evaluates the block's
terminator. This preserves every statement boundary for prefix safety. Invalid
cursor positions fault under the model's total malformed-state policy:
https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_const_eval/src/interpret/step.rs#L52-L67
-/
def step (body : Body) (state : State) : StepResult :=
  match body.blocks[state.block]? with
  | none => .fault .badBlock
  | some block =>
      match block.statements[state.statement]? with
      | some statement =>
          match execStatement body state.locals statement with
          | .ok locals => .next ⟨state.block, state.statement + 1, locals⟩
          | .error reason => .fault reason
      | none =>
          if state.statement == block.statements.length then
            execTerminator body state block.terminator
          else .fault .badPosition

/--
Reachability includes every finite prefix, whether or not execution returns.
The reflexive case includes the starting state. A faulting endpoint is therefore
reachable; SafeFrom must inspect the step at that endpoint rather than treating
reachability itself as a safety certificate.
-/
inductive Reach (body : Body) (start : State) : State → Prop where
  | refl : Reach body start start
  | next {before after : State} : Reach body start before →
      step body before = .next after → Reach body start after

/--
Every reachable state must have a nonfaulting step. An infinite execution is
safe only when every finite prefix meets this condition; failure to return
cannot hide a faulty prefix. This proposition imposes no termination duty.
-/
def SafeFrom (body : Body) (start : State) : Prop :=
  ∀ state, Reach body start state → ∀ reason, step body state ≠ .fault reason

def Safe (body : Body) (args : List Word) : Prop :=
  SafeFrom body (initial body args)

/--
An actual source return adds completion information beyond prefix safety. The
canonical roots require it only when an authored property asks for completion;
a conditional statement about results of returns need not supply this witness.
-/
def ReturnsFrom (body : Body) (start : State) (value : Word) : Prop :=
  ∃ state, Reach body start state ∧ step body state = .ret value

def Returns (body : Body) (args : List Word) (value : Word) : Prop :=
  ReturnsFrom body (initial body args) value

/--
Capture takes `isUnsafe` from `tcx.fn_sig(def)`'s `safety().is_unsafe()`; the
signature accessor "Returns the safety mode." The compiler's `Safety` type
separates `Unsafe` and `Safe`. This is the function signature's safety flag,
independent of unsafe blocks that may occur inside its implementation:
https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_type_ir/src/ty_kind.rs#L882-L885
https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_type_ir/src/ty_kind.rs#L899-L927
https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_hir/src/hir.rs#L4590-L4619

The pinned keyword documentation says: "`unsafe fn`: calling this function
means abiding by a contract the compiler cannot enforce." An unsafe block
instead records that the operations' contracts have been checked:
https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/library/std/src/keyword_docs.rs#L2085-L2105

Rust's distinction identifies entries with additional caller safety duties;
it does not prescribe this verification predicate or establish that an authored
requirement captures every intended safety duty. Anneal's own policy requires
unconditional static admission and prefix safety, permits reviewed caller
requirements only for unsafe entries, and keeps functional properties separate.
Safe entries cannot be restricted by a developer's functional precondition.
For a safe body the `isUnsafe` premise is impossible, so every valid input must
be safe regardless of `safetyPre`. For an unsafe body, the caller supplies the
reviewed safety requirement before that entry's safety can be used.

Static admission remains unconditional in both cases. Neither branch requires
a normal return; prefix safety remains mandatory when execution diverges.
-/
def BodyVerified (body : Body) (safetyPre : List Word → Prop) : Prop :=
  bodyWF body = true ∧
  ∀ args, argsValid body args → (body.isUnsafe = true → safetyPre args) →
    Safe body args

structure Specs where
  /-- Reviewed unsafe caller requirements, keyed by captured source identity. -/
  safety : String → List Word → Prop
  /--
  Additional reviewed requirements can express result relations or completion.
  Their strength is authored; the independent BodyVerified duties remain even
  when this predicate is trivial or conditional on an empty domain.
  -/
  property : Program → Prop

/--
The authored property adds an obligation; it cannot erase baseline safety.

The numeric index enumerates the complete captured inventory. Caller safety
requirements instead follow each body's authenticated identity: using the list
position for both purposes would let a source reordering change which function
receives a restrictive reviewed predicate. The capture authority establishes
unambiguous identities before it emits the source subject.
-/
def ProgramVerified (program : Program) (specs : Specs) : Prop :=
  (∀ (index : Nat) body, program.bodies[index]? = some body →
    BodyVerified body (specs.safety body.identity)) ∧ specs.property program

/--
The scope is part of the theorem subject. Host capture authentication must also
establish that a crate-scoped program's body census is complete.
-/
def CrateTheorem (program : Program) (specs : Specs) : Prop :=
  program.scope = .crate ∧ ProgramVerified program specs

/-- Unit verification proves the common duties only for the selected scope. -/
def UnitTheorem (program : Program) (specs : Specs) : Prop :=
  program.scope = .unit ∧ ProgramVerified program specs

end Trusted.Mvp
