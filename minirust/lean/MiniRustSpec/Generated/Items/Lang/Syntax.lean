/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.

GENERATED FILE -- DO NOT EDIT. Regenerate with
`cargo run -p anneal-minirust-gen -- generate`.

Deep (syntax) embedding of every top-level item of upstream MiniRust
`spec/lang/syntax.md` (commit `d821c6e3`), one Lean definition per item, in source order.
-/

import MiniRustSpec.Meta.Syntax

set_option maxRecDepth 100000

namespace MiniRustSpec.Gen.Items.Lang.Syntax

open MiniRustSpec.Syntax

/-- Path of the upstream file these items were extracted from. -/
def sourceFile : String := "spec/lang/syntax.md"

/-- SHA-256 of the upstream file. -/
def sourceSha256 : String := "fb52bcf504990477daf6928e95b8ccf90f99700fdf17d6bb031fb590728c0674"

/-- `spec/lang/syntax.md:16` -/
def enum_ValueExpr : Item :=
  (Item.enum
    [(Attr.mk true "doc" (AttrMeta.nameValue " A \"value expression\" evaluates to a `Value`."))]
    Visibility.pub
    "ValueExpr"
    (Generics.mk [] [])
    [
      (Variant.mk
        [(Attr.mk true "doc" (AttrMeta.nameValue " Just return a constant value."))]
        "Constant"
        (Fields.unnamed
          [
            (Field.mk
              []
              Visibility.inherited
              none
              (Ty.path none (Path.mk false [(PathSegment.mk "Constant" PathArguments.none)]))),
            (Field.mk
              []
              Visibility.inherited
              none
              (Ty.path none (Path.mk false [(PathSegment.mk "Type" PathArguments.none)])))])
        none),
      (Variant.mk
        [
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue " An n-tuple, used for arrays, structs, tuples (including unit)."))]
        "Tuple"
        (Fields.unnamed
          [
            (Field.mk
              []
              Visibility.inherited
              none
              (Ty.path
                none
                (Path.mk
                  false
                  [
                    (PathSegment.mk
                      "List"
                      (PathArguments.angleBracketed
                        false
                        [
                          (GenericArgument.type
                            (Ty.path
                              none
                              (Path.mk false [(PathSegment.mk "ValueExpr" PathArguments.none)])))]))]))),
            (Field.mk
              []
              Visibility.inherited
              none
              (Ty.path none (Path.mk false [(PathSegment.mk "Type" PathArguments.none)])))])
        none),
      (Variant.mk
        [(Attr.mk true "doc" (AttrMeta.nameValue " A `Union` value."))]
        "Union"
        (Fields.named
          [
            (Field.mk
              [
                (Attr.mk
                  true
                  "doc"
                  (AttrMeta.nameValue " The union's field which will be initialized."))]
              Visibility.inherited
              (some "field")
              (Ty.path none (Path.mk false [(PathSegment.mk "Int" PathArguments.none)]))),
            (Field.mk
              [
                (Attr.mk true "doc" (AttrMeta.nameValue " The value it will be initialized with.")),
                (Attr.mk true "specr::indirection" AttrMeta.path)]
              Visibility.inherited
              (some "expr")
              (Ty.path none (Path.mk false [(PathSegment.mk "ValueExpr" PathArguments.none)]))),
            (Field.mk
              [
                (Attr.mk
                  true
                  "doc"
                  (AttrMeta.nameValue " The union type, needs to be `Type::Union`"))]
              Visibility.inherited
              (some "union_ty")
              (Ty.path none (Path.mk false [(PathSegment.mk "Type" PathArguments.none)])))])
        none),
      (Variant.mk
        [(Attr.mk true "doc" (AttrMeta.nameValue " A variant of an enum type."))]
        "Variant"
        (Fields.named
          [
            (Field.mk
              [(Attr.mk true "doc" (AttrMeta.nameValue " The discriminant of the variant."))]
              Visibility.inherited
              (some "discriminant")
              (Ty.path none (Path.mk false [(PathSegment.mk "Int" PathArguments.none)]))),
            (Field.mk
              [
                (Attr.mk true "doc" (AttrMeta.nameValue " The `ValueExpr` for the variant.")),
                (Attr.mk true "specr::indirection" AttrMeta.path)]
              Visibility.inherited
              (some "data")
              (Ty.path none (Path.mk false [(PathSegment.mk "ValueExpr" PathArguments.none)]))),
            (Field.mk
              [
                (Attr.mk
                  true
                  "doc"
                  (AttrMeta.nameValue " The enum type, needs to be `Type::Enum`."))]
              Visibility.inherited
              (some "enum_ty")
              (Ty.path none (Path.mk false [(PathSegment.mk "Type" PathArguments.none)])))])
        none),
      (Variant.mk
        [
          (Attr.mk true "doc" (AttrMeta.nameValue " Read the discriminant of an enum type.")),
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue " As we don't need to know the validity of the inner data")),
          (Attr.mk true "doc" (AttrMeta.nameValue " we don't fully load the variant value."))]
        "GetDiscriminant"
        (Fields.named
          [
            (Field.mk
              [
                (Attr.mk true "doc" (AttrMeta.nameValue " The place where the enum is located.")),
                (Attr.mk true "specr::indirection" AttrMeta.path)]
              Visibility.inherited
              (some "place")
              (Ty.path none (Path.mk false [(PathSegment.mk "PlaceExpr" PathArguments.none)])))])
        none),
      (Variant.mk
        [(Attr.mk true "doc" (AttrMeta.nameValue " Load a value from memory."))]
        "Load"
        (Fields.named
          [
            (Field.mk
              [
                (Attr.mk true "doc" (AttrMeta.nameValue " The place to load from.")),
                (Attr.mk true "specr::indirection" AttrMeta.path)]
              Visibility.inherited
              (some "source")
              (Ty.path none (Path.mk false [(PathSegment.mk "PlaceExpr" PathArguments.none)])))])
        none),
      (Variant.mk
        [
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue " Create a pointer (raw pointer or reference) to a place."))]
        "AddrOf"
        (Fields.named
          [
            (Field.mk
              [
                (Attr.mk true "doc" (AttrMeta.nameValue " The place to create a pointer to.")),
                (Attr.mk true "specr::indirection" AttrMeta.path)]
              Visibility.inherited
              (some "target")
              (Ty.path none (Path.mk false [(PathSegment.mk "PlaceExpr" PathArguments.none)]))),
            (Field.mk
              [(Attr.mk true "doc" (AttrMeta.nameValue " The type of the created pointer."))]
              Visibility.inherited
              (some "ptr_ty")
              (Ty.path none (Path.mk false [(PathSegment.mk "PtrType" PathArguments.none)])))])
        none),
      (Variant.mk
        [(Attr.mk true "doc" (AttrMeta.nameValue " Unary operators."))]
        "UnOp"
        (Fields.named
          [
            (Field.mk
              []
              Visibility.inherited
              (some "operator")
              (Ty.path none (Path.mk false [(PathSegment.mk "UnOp" PathArguments.none)]))),
            (Field.mk
              [(Attr.mk true "specr::indirection" AttrMeta.path)]
              Visibility.inherited
              (some "operand")
              (Ty.path none (Path.mk false [(PathSegment.mk "ValueExpr" PathArguments.none)])))])
        none),
      (Variant.mk
        [(Attr.mk true "doc" (AttrMeta.nameValue " Binary operators."))]
        "BinOp"
        (Fields.named
          [
            (Field.mk
              []
              Visibility.inherited
              (some "operator")
              (Ty.path none (Path.mk false [(PathSegment.mk "BinOp" PathArguments.none)]))),
            (Field.mk
              [(Attr.mk true "specr::indirection" AttrMeta.path)]
              Visibility.inherited
              (some "left")
              (Ty.path none (Path.mk false [(PathSegment.mk "ValueExpr" PathArguments.none)]))),
            (Field.mk
              [(Attr.mk true "specr::indirection" AttrMeta.path)]
              Visibility.inherited
              (some "right")
              (Ty.path none (Path.mk false [(PathSegment.mk "ValueExpr" PathArguments.none)])))])
        none)])

/-- `spec/lang/syntax.md:80` -/
def enum_Constant : Item :=
  (Item.enum
    [
      (Attr.mk
        true
        "doc"
        (AttrMeta.nameValue " Constants are basically values, but cannot have explicit provenance.")),
      (Attr.mk
        true
        "doc"
        (AttrMeta.nameValue " Currently we do not support Ptr and Union constants."))]
    Visibility.pub
    "Constant"
    (Generics.mk [] [])
    [
      (Variant.mk
        [
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue " A mathematical integer, used for `i*`/`u*` types."))]
        "Int"
        (Fields.unnamed
          [
            (Field.mk
              []
              Visibility.inherited
              none
              (Ty.path none (Path.mk false [(PathSegment.mk "Int" PathArguments.none)])))])
        none),
      (Variant.mk
        [(Attr.mk true "doc" (AttrMeta.nameValue " A Boolean value, used for `bool`."))]
        "Bool"
        (Fields.unnamed
          [
            (Field.mk
              []
              Visibility.inherited
              none
              (Ty.path none (Path.mk false [(PathSegment.mk "bool" PathArguments.none)])))])
        none),
      (Variant.mk
        [
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue " A pointer pointing into a global allocation with a given offset."))]
        "GlobalPointer"
        (Fields.unnamed
          [
            (Field.mk
              []
              Visibility.inherited
              none
              (Ty.path none (Path.mk false [(PathSegment.mk "Relocation" PathArguments.none)])))])
        none),
      (Variant.mk
        [(Attr.mk true "doc" (AttrMeta.nameValue " A pointer pointing to a function."))]
        "FnPointer"
        (Fields.unnamed
          [
            (Field.mk
              []
              Visibility.inherited
              none
              (Ty.path none (Path.mk false [(PathSegment.mk "FnName" PathArguments.none)])))])
        none),
      (Variant.mk
        [(Attr.mk true "doc" (AttrMeta.nameValue " A pointer pointing to a vtable."))]
        "VTablePointer"
        (Fields.unnamed
          [
            (Field.mk
              []
              Visibility.inherited
              none
              (Ty.path none (Path.mk false [(PathSegment.mk "VTableName" PathArguments.none)])))])
        none),
      (Variant.mk
        [
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue
              " A pointer with constant address, not pointing into any allocation."))]
        "PointerWithoutProvenance"
        (Fields.unnamed
          [
            (Field.mk
              []
              Visibility.inherited
              none
              (Ty.path none (Path.mk false [(PathSegment.mk "Address" PathArguments.none)])))])
        none)])

/-- `spec/lang/syntax.md:97` -/
def enum_IntUnOp : Item :=
  (Item.enum
    []
    Visibility.pub
    "IntUnOp"
    (Generics.mk [] [])
    [
      (Variant.mk
        [
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue " Negate an integer value arithmetically (`x` becomes `-x`)."))]
        "Neg"
        Fields.unit
        none),
      (Variant.mk
        [(Attr.mk true "doc" (AttrMeta.nameValue " Bitwise-invert an integer value"))]
        "BitNot"
        Fields.unit
        none),
      (Variant.mk
        [(Attr.mk true "doc" (AttrMeta.nameValue " Used for the intrinsic ˋctpopˋ."))]
        "CountOnes"
        Fields.unit
        none)])

/-- `spec/lang/syntax.md:105` -/
def enum_CastOp : Item :=
  (Item.enum
    []
    Visibility.pub
    "CastOp"
    (Generics.mk [] [])
    [
      (Variant.mk
        [
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue
              " Argument can be any integer type; returns the given integer type."))]
        "IntToInt"
        (Fields.unnamed
          [
            (Field.mk
              []
              Visibility.inherited
              none
              (Ty.path none (Path.mk false [(PathSegment.mk "IntType" PathArguments.none)])))])
        none),
      (Variant.mk
        [
          (Attr.mk true "doc" (AttrMeta.nameValue " Transmute the value to a different type.")),
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue
              " The program is well-formed even if the output type has a different size than the")),
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue " input type, but the operation is UB in that case."))]
        "Transmute"
        (Fields.unnamed
          [
            (Field.mk
              []
              Visibility.inherited
              none
              (Ty.path none (Path.mk false [(PathSegment.mk "Type" PathArguments.none)])))])
        none)])

/-- `spec/lang/syntax.md:113` -/
def enum_UnOp : Item :=
  (Item.enum
    []
    Visibility.pub
    "UnOp"
    (Generics.mk [] [])
    [
      (Variant.mk
        [
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue " An operation on an integer; returns an integer of the same type."))]
        "Int"
        (Fields.unnamed
          [
            (Field.mk
              []
              Visibility.inherited
              none
              (Ty.path none (Path.mk false [(PathSegment.mk "IntUnOp" PathArguments.none)])))])
        none),
      (Variant.mk
        [
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue
              " A form of cast; the return type is given by the specific cast operation."))]
        "Cast"
        (Fields.unnamed
          [
            (Field.mk
              []
              Visibility.inherited
              none
              (Ty.path none (Path.mk false [(PathSegment.mk "CastOp" PathArguments.none)])))])
        none),
      (Variant.mk
        [
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue
              " Returns a raw pointer with same thin pointer as the operand, but without the metadata."))]
        "GetThinPointer"
        Fields.unit
        none),
      (Variant.mk
        [
          (Attr.mk true "doc" (AttrMeta.nameValue " Returns the metadata of a pointer as a value.")),
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue
              " The return type is given by `PointerMetaKind::ty()`, e.g., for a thin pointer this is `()`."))]
        "GetMetadata"
        Fields.unit
        none),
      (Variant.mk
        [
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue " Returns the dynamic size of the type given the pointer metadata.")),
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue
              " The operand must be a matching metadata for the type. For sized types this is `()`."))]
        "ComputeSize"
        (Fields.unnamed
          [
            (Field.mk
              []
              Visibility.inherited
              none
              (Ty.path none (Path.mk false [(PathSegment.mk "Type" PathArguments.none)])))])
        none),
      (Variant.mk
        [
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue
              " Returns the dynamic alignment of the type given the pointer metadata.")),
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue
              " The operand must be a matching metadata for the type. For sized types this is `()`."))]
        "ComputeAlign"
        (Fields.unnamed
          [
            (Field.mk
              []
              Visibility.inherited
              none
              (Ty.path none (Path.mk false [(PathSegment.mk "Type" PathArguments.none)])))])
        none),
      (Variant.mk
        [
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue " Lookup the function pointer for a trait object method.")),
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue
              " The operand must be a pointer to a vtable as returned by `Constant::VTablePointer`.")),
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue " The parameter specifies which method of the vtable to look up."))]
        "VTableMethodLookup"
        (Fields.unnamed
          [
            (Field.mk
              []
              Visibility.inherited
              none
              (Ty.path none (Path.mk false [(PathSegment.mk "TraitMethodName" PathArguments.none)])))])
        none)])

/-- `spec/lang/syntax.md:136` -/
def enum_IntBinOp : Item :=
  (Item.enum
    []
    Visibility.pub
    "IntBinOp"
    (Generics.mk [] [])
    [
      (Variant.mk
        [(Attr.mk true "doc" (AttrMeta.nameValue " Add two integer values."))]
        "Add"
        Fields.unit
        none),
      (Variant.mk
        [
          (Attr.mk true "doc" (AttrMeta.nameValue " Add two integer values.")),
          (Attr.mk true "doc" (AttrMeta.nameValue " Throws UB on overflow."))]
        "AddUnchecked"
        Fields.unit
        none),
      (Variant.mk
        [(Attr.mk true "doc" (AttrMeta.nameValue " Subtract two integer values."))]
        "Sub"
        Fields.unit
        none),
      (Variant.mk
        [
          (Attr.mk true "doc" (AttrMeta.nameValue " Subtract two integer values.")),
          (Attr.mk true "doc" (AttrMeta.nameValue " Throws UB on overflow."))]
        "SubUnchecked"
        Fields.unit
        none),
      (Variant.mk
        [(Attr.mk true "doc" (AttrMeta.nameValue " Multiply two integer values."))]
        "Mul"
        Fields.unit
        none),
      (Variant.mk
        [
          (Attr.mk true "doc" (AttrMeta.nameValue " Multiply two integer values.")),
          (Attr.mk true "doc" (AttrMeta.nameValue " Throws UB on overflow."))]
        "MulUnchecked"
        Fields.unit
        none),
      (Variant.mk
        [
          (Attr.mk true "doc" (AttrMeta.nameValue " Divide two integer values.")),
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue " UB on division by zero and on `int::MIN / -1`."))]
        "Div"
        Fields.unit
        none),
      (Variant.mk
        [
          (Attr.mk true "doc" (AttrMeta.nameValue " Divide two integer values.")),
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue
              " UB on division by zero, on `int::MIN / -1`, and on a non-zero remainder."))]
        "DivExact"
        Fields.unit
        none),
      (Variant.mk
        [
          (Attr.mk true "doc" (AttrMeta.nameValue " Remainder of a division, the `%` operator.")),
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue
              " UB if the modulos (right operand) is zero and on `int::MIN % -1`."))]
        "Rem"
        Fields.unit
        none),
      (Variant.mk
        [(Attr.mk true "doc" (AttrMeta.nameValue " Shift left `<<`"))]
        "Shl"
        Fields.unit
        none),
      (Variant.mk
        [
          (Attr.mk true "doc" (AttrMeta.nameValue " Shift left `<<`")),
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue " Throws UB if right operand not in range 0..left::BITS."))]
        "ShlUnchecked"
        Fields.unit
        none),
      (Variant.mk
        [
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue
              " Shift right `>>` (logical shift for unsigned integers, arithmetic shift for signed integers)"))]
        "Shr"
        Fields.unit
        none),
      (Variant.mk
        [
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue
              " Shift right `>>` (logical shift for unsigned integers, arithmetic shift for signed integers)")),
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue " Throws UB if right operand not in range 0..left::BITS."))]
        "ShrUnchecked"
        Fields.unit
        none),
      (Variant.mk
        [(Attr.mk true "doc" (AttrMeta.nameValue " Bitwise-and two integer values."))]
        "BitAnd"
        Fields.unit
        none),
      (Variant.mk
        [(Attr.mk true "doc" (AttrMeta.nameValue " Bitwise-or two integer values."))]
        "BitOr"
        Fields.unit
        none),
      (Variant.mk
        [(Attr.mk true "doc" (AttrMeta.nameValue " Bitwise-xor two integer values."))]
        "BitXor"
        Fields.unit
        none)])

/-- `spec/lang/syntax.md:178` -/
def enum_IntBinOpWithOverflow : Item :=
  (Item.enum
    []
    Visibility.pub
    "IntBinOpWithOverflow"
    (Generics.mk [] [])
    [
      (Variant.mk
        [
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue " Add two integer values, returns a tuple of the result integer")),
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue " and a bool indicating whether the calculation overflowed."))]
        "Add"
        Fields.unit
        none),
      (Variant.mk
        [
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue
              " Subtract two integer values, returns a tuple of the result integer")),
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue " and a bool indicating whether the calculation overflowed."))]
        "Sub"
        Fields.unit
        none),
      (Variant.mk
        [
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue " Multiply two integers, returns a tuple of the result integer")),
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue " and a bool indicating whether the calculation overflowed."))]
        "Mul"
        Fields.unit
        none)])

/-- `spec/lang/syntax.md:189` -/
def enum_RelOp : Item :=
  (Item.enum
    [
      (Attr.mk
        true
        "doc"
        (AttrMeta.nameValue " A relational operator indicates how two values are to be compared.")),
      (Attr.mk
        true
        "doc"
        (AttrMeta.nameValue " Unless noted otherwise, these all return a Boolean."))]
    Visibility.pub
    "RelOp"
    (Generics.mk [] [])
    [
      (Variant.mk [(Attr.mk true "doc" (AttrMeta.nameValue " less than"))] "Lt" Fields.unit none),
      (Variant.mk [(Attr.mk true "doc" (AttrMeta.nameValue " greater than"))] "Gt" Fields.unit none),
      (Variant.mk
        [(Attr.mk true "doc" (AttrMeta.nameValue " less than or equal"))]
        "Le"
        Fields.unit
        none),
      (Variant.mk
        [(Attr.mk true "doc" (AttrMeta.nameValue " greater than or equal"))]
        "Ge"
        Fields.unit
        none),
      (Variant.mk [(Attr.mk true "doc" (AttrMeta.nameValue " equal"))] "Eq" Fields.unit none),
      (Variant.mk [(Attr.mk true "doc" (AttrMeta.nameValue " inequal"))] "Ne" Fields.unit none),
      (Variant.mk
        [
          (Attr.mk true "doc" (AttrMeta.nameValue " The three-way comparison; returns an i8:")),
          (Attr.mk true "doc" (AttrMeta.nameValue " * -1 if left <  right")),
          (Attr.mk true "doc" (AttrMeta.nameValue " *  0 if left == right")),
          (Attr.mk true "doc" (AttrMeta.nameValue " * +1 if left >  right"))]
        "Cmp"
        Fields.unit
        none)])

/-- `spec/lang/syntax.md:211` -/
def enum_BinOp : Item :=
  (Item.enum
    []
    Visibility.pub
    "BinOp"
    (Generics.mk [] [])
    [
      (Variant.mk
        [
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue
              " An operation on integers (both must have the same type); returns an integer of the same type."))]
        "Int"
        (Fields.unnamed
          [
            (Field.mk
              []
              Visibility.inherited
              none
              (Ty.path none (Path.mk false [(PathSegment.mk "IntBinOp" PathArguments.none)])))])
        none),
      (Variant.mk
        [
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue
              " An operation on integers (both must have the same type); returns a tuple of integer of the same type")),
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue
              " and a boolean that is true if the result is not equal to the infinite-precision result."))]
        "IntWithOverflow"
        (Fields.unnamed
          [
            (Field.mk
              []
              Visibility.inherited
              none
              (Ty.path
                none
                (Path.mk false [(PathSegment.mk "IntBinOpWithOverflow" PathArguments.none)])))])
        none),
      (Variant.mk
        [
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue
              " Compares two values according to the given relational operator. Both must have the same type,")),
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue " and they must both be integers, Booleans, or pointers."))]
        "Rel"
        (Fields.unnamed
          [
            (Field.mk
              []
              Visibility.inherited
              none
              (Ty.path none (Path.mk false [(PathSegment.mk "RelOp" PathArguments.none)])))])
        none),
      (Variant.mk
        [
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue
              " Add a byte-offset to a pointer (with or without inbounds requirement).")),
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue " Takes a pointer as left operand and an integer as right operand;")),
          (Attr.mk true "doc" (AttrMeta.nameValue " returns a pointer.")),
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue
              " FIXME: should we make this in units of the pointee size? The thing is, for")),
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue " raw pointers we do not have the pointee type..."))]
        "PtrOffset"
        (Fields.named
          [
            (Field.mk
              []
              Visibility.inherited
              (some "inbounds")
              (Ty.path none (Path.mk false [(PathSegment.mk "bool" PathArguments.none)])))])
        none),
      (Variant.mk
        [
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue
              " Compute the distance between two pointers in bytes (with or without inbounds requirement).")),
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue " Takes two pointers; returns a signed pointer-sized integer.")),
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue " If `nonneg` is true, it is UB for the result to be negative."))]
        "PtrOffsetFrom"
        (Fields.named
          [
            (Field.mk
              []
              Visibility.inherited
              (some "inbounds")
              (Ty.path none (Path.mk false [(PathSegment.mk "bool" PathArguments.none)]))),
            (Field.mk
              []
              Visibility.inherited
              (some "nonneg")
              (Ty.path none (Path.mk false [(PathSegment.mk "bool" PathArguments.none)])))])
        none),
      (Variant.mk
        [
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue " This corresponds to `core::ptr::from_raw_parts`")),
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue
              " and takes a thin pointer and matching metadata to construct a pointer of the given type.")),
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue
              " When the target type is a thin pointer and the metadata is `()`, this is just a pointer cast."))]
        "ConstructWidePointer"
        (Fields.unnamed
          [
            (Field.mk
              []
              Visibility.inherited
              none
              (Ty.path none (Path.mk false [(PathSegment.mk "PtrType" PathArguments.none)])))])
        none)])

/-- `spec/lang/syntax.md:241` -/
def enum_PlaceExpr : Item :=
  (Item.enum
    [(Attr.mk true "doc" (AttrMeta.nameValue " A \"place expression\" evaluates to a `Place`."))]
    Visibility.pub
    "PlaceExpr"
    (Generics.mk [] [])
    [
      (Variant.mk
        [(Attr.mk true "doc" (AttrMeta.nameValue " Denotes a local variable."))]
        "Local"
        (Fields.unnamed
          [
            (Field.mk
              []
              Visibility.inherited
              none
              (Ty.path none (Path.mk false [(PathSegment.mk "LocalName" PathArguments.none)])))])
        none),
      (Variant.mk
        [
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue " Dereference a value (of pointer/reference type)."))]
        "Deref"
        (Fields.named
          [
            (Field.mk
              [(Attr.mk true "specr::indirection" AttrMeta.path)]
              Visibility.inherited
              (some "operand")
              (Ty.path none (Path.mk false [(PathSegment.mk "ValueExpr" PathArguments.none)]))),
            (Field.mk
              []
              Visibility.inherited
              (some "ty")
              (Ty.path none (Path.mk false [(PathSegment.mk "Type" PathArguments.none)])))])
        none),
      (Variant.mk
        [(Attr.mk true "doc" (AttrMeta.nameValue " Project to a field."))]
        "Field"
        (Fields.named
          [
            (Field.mk
              [
                (Attr.mk true "doc" (AttrMeta.nameValue " The place to base the projection on.")),
                (Attr.mk true "specr::indirection" AttrMeta.path)]
              Visibility.inherited
              (some "root")
              (Ty.path none (Path.mk false [(PathSegment.mk "PlaceExpr" PathArguments.none)]))),
            (Field.mk
              [(Attr.mk true "doc" (AttrMeta.nameValue " The field to project to."))]
              Visibility.inherited
              (some "field")
              (Ty.path none (Path.mk false [(PathSegment.mk "Int" PathArguments.none)])))])
        none),
      (Variant.mk
        [(Attr.mk true "doc" (AttrMeta.nameValue " Index to an array or slice element."))]
        "Index"
        (Fields.named
          [
            (Field.mk
              [
                (Attr.mk true "doc" (AttrMeta.nameValue " The array or slice to index into.")),
                (Attr.mk true "specr::indirection" AttrMeta.path)]
              Visibility.inherited
              (some "root")
              (Ty.path none (Path.mk false [(PathSegment.mk "PlaceExpr" PathArguments.none)]))),
            (Field.mk
              [
                (Attr.mk true "doc" (AttrMeta.nameValue " The index to project to.")),
                (Attr.mk true "specr::indirection" AttrMeta.path)]
              Visibility.inherited
              (some "index")
              (Ty.path none (Path.mk false [(PathSegment.mk "ValueExpr" PathArguments.none)])))])
        none),
      (Variant.mk
        [(Attr.mk true "doc" (AttrMeta.nameValue " Enum variant downcast."))]
        "Downcast"
        (Fields.named
          [
            (Field.mk
              [
                (Attr.mk
                  true
                  "doc"
                  (AttrMeta.nameValue " The base enum to project to the specific variant.")),
                (Attr.mk true "specr::indirection" AttrMeta.path)]
              Visibility.inherited
              (some "root")
              (Ty.path none (Path.mk false [(PathSegment.mk "PlaceExpr" PathArguments.none)]))),
            (Field.mk
              [
                (Attr.mk
                  true
                  "doc"
                  (AttrMeta.nameValue " The discriminant of the variant to project to."))]
              Visibility.inherited
              (some "discriminant")
              (Ty.path none (Path.mk false [(PathSegment.mk "Int" PathArguments.none)])))])
        none)])

/-- `spec/lang/syntax.md:285` -/
def enum_Statement : Item :=
  (Item.enum
    []
    Visibility.pub
    "Statement"
    (Generics.mk [] [])
    [
      (Variant.mk
        [(Attr.mk true "doc" (AttrMeta.nameValue " Copy value from `source` to `destination`."))]
        "Assign"
        (Fields.named
          [
            (Field.mk
              []
              Visibility.inherited
              (some "destination")
              (Ty.path none (Path.mk false [(PathSegment.mk "PlaceExpr" PathArguments.none)]))),
            (Field.mk
              []
              Visibility.inherited
              (some "source")
              (Ty.path none (Path.mk false [(PathSegment.mk "ValueExpr" PathArguments.none)])))])
        none),
      (Variant.mk
        [
          (Attr.mk true "doc" (AttrMeta.nameValue " Evaluate a place without accessing it.")),
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue " This is the result of translating e.g. `let _ = place;`."))]
        "PlaceMention"
        (Fields.unnamed
          [
            (Field.mk
              []
              Visibility.inherited
              none
              (Ty.path none (Path.mk false [(PathSegment.mk "PlaceExpr" PathArguments.none)])))])
        none),
      (Variant.mk
        [
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue " Set the discriminant of the variant at `destination` to `value`."))]
        "SetDiscriminant"
        (Fields.named
          [
            (Field.mk
              []
              Visibility.inherited
              (some "destination")
              (Ty.path none (Path.mk false [(PathSegment.mk "PlaceExpr" PathArguments.none)]))),
            (Field.mk
              []
              Visibility.inherited
              (some "value")
              (Ty.path none (Path.mk false [(PathSegment.mk "Int" PathArguments.none)])))])
        none),
      (Variant.mk
        [
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue
              " Ensure that `place` contains a valid value of its type (else UB).")),
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue
              " Also perform retagging and ensure safe pointers are dereferenceable.")),
          (Attr.mk true "doc" (AttrMeta.nameValue "")),
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue
              " The frontend is generally expected to generate this for all function argument,")),
          (Attr.mk true "doc" (AttrMeta.nameValue " and possibly in more places."))]
        "Validate"
        (Fields.named
          [
            (Field.mk
              []
              Visibility.inherited
              (some "place")
              (Ty.path none (Path.mk false [(PathSegment.mk "PlaceExpr" PathArguments.none)]))),
            (Field.mk
              [
                (Attr.mk
                  true
                  "doc"
                  (AttrMeta.nameValue
                    " Indicates whether this operation occurs as part of the prelude")),
                (Attr.mk
                  true
                  "doc"
                  (AttrMeta.nameValue
                    " that we have at the top of each function (which affects retagging)."))]
              Visibility.inherited
              (some "fn_entry")
              (Ty.path none (Path.mk false [(PathSegment.mk "bool" PathArguments.none)])))])
        none),
      (Variant.mk
        [(Attr.mk true "doc" (AttrMeta.nameValue " De-initialize a place."))]
        "Deinit"
        (Fields.named
          [
            (Field.mk
              []
              Visibility.inherited
              (some "place")
              (Ty.path none (Path.mk false [(PathSegment.mk "PlaceExpr" PathArguments.none)])))])
        none),
      (Variant.mk
        [(Attr.mk true "doc" (AttrMeta.nameValue " Allocate the backing store for this local."))]
        "StorageLive"
        (Fields.unnamed
          [
            (Field.mk
              []
              Visibility.inherited
              none
              (Ty.path none (Path.mk false [(PathSegment.mk "LocalName" PathArguments.none)])))])
        none),
      (Variant.mk
        [(Attr.mk true "doc" (AttrMeta.nameValue " Deallocate the backing store for this local."))]
        "StorageDead"
        (Fields.unnamed
          [
            (Field.mk
              []
              Visibility.inherited
              none
              (Ty.path none (Path.mk false [(PathSegment.mk "LocalName" PathArguments.none)])))])
        none)])

/-- `spec/lang/syntax.md:320` -/
def enum_Terminator : Item :=
  (Item.enum
    []
    Visibility.pub
    "Terminator"
    (Generics.mk [] [])
    [
      (Variant.mk
        [(Attr.mk true "doc" (AttrMeta.nameValue " Just jump to the next block."))]
        "Goto"
        (Fields.unnamed
          [
            (Field.mk
              []
              Visibility.inherited
              none
              (Ty.path none (Path.mk false [(PathSegment.mk "BbName" PathArguments.none)])))])
        none),
      (Variant.mk
        [
          (Attr.mk true "doc" (AttrMeta.nameValue " `value` needs to evaluate to a `Value::Int`.")),
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue
              " `cases` map those values to blocks to jump to and therefore have to have the equivalent type.")),
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue
              " If no value matches we fall back to the block given in `fallback`."))]
        "Switch"
        (Fields.named
          [
            (Field.mk
              []
              Visibility.inherited
              (some "value")
              (Ty.path none (Path.mk false [(PathSegment.mk "ValueExpr" PathArguments.none)]))),
            (Field.mk
              []
              Visibility.inherited
              (some "cases")
              (Ty.path
                none
                (Path.mk
                  false
                  [
                    (PathSegment.mk
                      "Map"
                      (PathArguments.angleBracketed
                        false
                        [
                          (GenericArgument.type
                            (Ty.path
                              none
                              (Path.mk false [(PathSegment.mk "Int" PathArguments.none)]))),
                          (GenericArgument.type
                            (Ty.path
                              none
                              (Path.mk false [(PathSegment.mk "BbName" PathArguments.none)])))]))]))),
            (Field.mk
              []
              Visibility.inherited
              (some "fallback")
              (Ty.path none (Path.mk false [(PathSegment.mk "BbName" PathArguments.none)])))])
        none),
      (Variant.mk
        [(Attr.mk true "doc" (AttrMeta.nameValue " If this is ever executed, we have UB."))]
        "Unreachable"
        Fields.unit
        none),
      (Variant.mk
        [
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue " Invoke the given intrinsic operation with the given arguments.")),
          (Attr.mk true "doc" (AttrMeta.nameValue "")),
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue
              " Intrinsics are langauge primitives that can have arbitrary side-effects, including divergence."))]
        "Intrinsic"
        (Fields.named
          [
            (Field.mk
              []
              Visibility.inherited
              (some "intrinsic")
              (Ty.path none (Path.mk false [(PathSegment.mk "IntrinsicOp" PathArguments.none)]))),
            (Field.mk
              [(Attr.mk true "doc" (AttrMeta.nameValue " The arguments to pass."))]
              Visibility.inherited
              (some "arguments")
              (Ty.path
                none
                (Path.mk
                  false
                  [
                    (PathSegment.mk
                      "List"
                      (PathArguments.angleBracketed
                        false
                        [
                          (GenericArgument.type
                            (Ty.path
                              none
                              (Path.mk false [(PathSegment.mk "ValueExpr" PathArguments.none)])))]))]))),
            (Field.mk
              [(Attr.mk true "doc" (AttrMeta.nameValue " The place to put the return value into."))]
              Visibility.inherited
              (some "ret")
              (Ty.path none (Path.mk false [(PathSegment.mk "PlaceExpr" PathArguments.none)]))),
            (Field.mk
              [
                (Attr.mk
                  true
                  "doc"
                  (AttrMeta.nameValue " The block to jump to when this call returns.")),
                (Attr.mk
                  true
                  "doc"
                  (AttrMeta.nameValue " If `None`, UB will be raised when the intrinsic returns."))]
              Visibility.inherited
              (some "next_block")
              (Ty.path
                none
                (Path.mk
                  false
                  [
                    (PathSegment.mk
                      "Option"
                      (PathArguments.angleBracketed
                        false
                        [
                          (GenericArgument.type
                            (Ty.path
                              none
                              (Path.mk false [(PathSegment.mk "BbName" PathArguments.none)])))]))])))])
        none),
      (Variant.mk
        [
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue " Call the given function with the given arguments."))]
        "Call"
        (Fields.named
          [
            (Field.mk
              [
                (Attr.mk true "doc" (AttrMeta.nameValue " What function or method to call.")),
                (Attr.mk
                  true
                  "doc"
                  (AttrMeta.nameValue
                    " This must evaluate to a function pointer and for safe behaviour, the functions signature must match the arguments.")),
                (Attr.mk true "doc" (AttrMeta.nameValue "")),
                (Attr.mk
                  true
                  "doc"
                  (AttrMeta.nameValue
                    " Dynamic dispatch is represented with the callee being the result of `VTableMethodLookup(GetMetadata(self))`,")),
                (Attr.mk
                  true
                  "doc"
                  (AttrMeta.nameValue
                    " and the `self` argument appropriately cast to a thin pointer type."))]
              Visibility.inherited
              (some "callee")
              (Ty.path none (Path.mk false [(PathSegment.mk "ValueExpr" PathArguments.none)]))),
            (Field.mk
              [
                (Attr.mk
                  true
                  "doc"
                  (AttrMeta.nameValue " The calling convention to use for this call."))]
              Visibility.inherited
              (some "calling_convention")
              (Ty.path
                none
                (Path.mk false [(PathSegment.mk "CallingConvention" PathArguments.none)]))),
            (Field.mk
              [(Attr.mk true "doc" (AttrMeta.nameValue " The arguments to pass."))]
              Visibility.inherited
              (some "arguments")
              (Ty.path
                none
                (Path.mk
                  false
                  [
                    (PathSegment.mk
                      "List"
                      (PathArguments.angleBracketed
                        false
                        [
                          (GenericArgument.type
                            (Ty.path
                              none
                              (Path.mk false [(PathSegment.mk "ArgumentExpr" PathArguments.none)])))]))]))),
            (Field.mk
              [(Attr.mk true "doc" (AttrMeta.nameValue " The place to put the return value into."))]
              Visibility.inherited
              (some "ret")
              (Ty.path none (Path.mk false [(PathSegment.mk "PlaceExpr" PathArguments.none)]))),
            (Field.mk
              [
                (Attr.mk
                  true
                  "doc"
                  (AttrMeta.nameValue " The block to jump to when this call returns.")),
                (Attr.mk
                  true
                  "doc"
                  (AttrMeta.nameValue " If `None`, UB will be raised when the function returns."))]
              Visibility.inherited
              (some "next_block")
              (Ty.path
                none
                (Path.mk
                  false
                  [
                    (PathSegment.mk
                      "Option"
                      (PathArguments.angleBracketed
                        false
                        [
                          (GenericArgument.type
                            (Ty.path
                              none
                              (Path.mk false [(PathSegment.mk "BbName" PathArguments.none)])))]))]))),
            (Field.mk
              [
                (Attr.mk
                  true
                  "doc"
                  (AttrMeta.nameValue " The block to jump to when this call unwinds.")),
                (Attr.mk
                  true
                  "doc"
                  (AttrMeta.nameValue " If `None`, UB will be raised when the function unwinds.")),
                (Attr.mk
                  true
                  "doc"
                  (AttrMeta.nameValue
                    " This comes with a well-formedness requirement: if the current block is a regular block,")),
                (Attr.mk
                  true
                  "doc"
                  (AttrMeta.nameValue
                    " `unwind_block` must be either a cleanup block or a catch block;")),
                (Attr.mk
                  true
                  "doc"
                  (AttrMeta.nameValue " otherwise, `unwind_block` must be a terminating block."))]
              Visibility.inherited
              (some "unwind_block")
              (Ty.path
                none
                (Path.mk
                  false
                  [
                    (PathSegment.mk
                      "Option"
                      (PathArguments.angleBracketed
                        false
                        [
                          (GenericArgument.type
                            (Ty.path
                              none
                              (Path.mk false [(PathSegment.mk "BbName" PathArguments.none)])))]))])))])
        none),
      (Variant.mk
        [(Attr.mk true "doc" (AttrMeta.nameValue " Return from the current function."))]
        "Return"
        Fields.unit
        none),
      (Variant.mk
        [
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue " Starts unwinding, jump to the indicated cleanup block."))]
        "StartUnwind"
        (Fields.named
          [
            (Field.mk
              [
                (Attr.mk
                  true
                  "doc"
                  (AttrMeta.nameValue
                    " The unwinding payload. This should evaluate to a thin pointer."))]
              Visibility.inherited
              (some "unwind_payload")
              (Ty.path none (Path.mk false [(PathSegment.mk "ValueExpr" PathArguments.none)]))),
            (Field.mk
              [
                (Attr.mk
                  true
                  "doc"
                  (AttrMeta.nameValue " The cleanup or catch block the execution jumps to."))]
              Visibility.inherited
              (some "unwind_block")
              (Ty.path none (Path.mk false [(PathSegment.mk "BbName" PathArguments.none)])))])
        none),
      (Variant.mk
        [
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue " Stops unwinding, jump to the indicated regular block.")),
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue " This also removes the topmost unwinding payload.")),
          (Attr.mk true "doc" (AttrMeta.nameValue " UB if not currently unwinding."))]
        "StopUnwind"
        (Fields.unnamed
          [
            (Field.mk
              []
              Visibility.inherited
              none
              (Ty.path none (Path.mk false [(PathSegment.mk "BbName" PathArguments.none)])))])
        none),
      (Variant.mk
        [
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue
              " Ends this function call. The unwinding should continue at the caller's stack frame."))]
        "ResumeUnwind"
        Fields.unit
        none)])

/-- `spec/lang/syntax.md:387` -/
def enum_ArgumentExpr : Item :=
  (Item.enum
    [
      (Attr.mk
        true
        "doc"
        (AttrMeta.nameValue " Function arguments can be passed by-value or in-place."))]
    Visibility.pub
    "ArgumentExpr"
    (Generics.mk [] [])
    [
      (Variant.mk
        [
          (Attr.mk true "doc" (AttrMeta.nameValue " Pass a copy of this value to the function.")),
          (Attr.mk true "doc" (AttrMeta.nameValue "")),
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue
              " Technically this could be encoded by generating a fresh temporary, copying the value there, and doing in-place passing.")),
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue " FIXME: is it worth providing this mode anyway?"))]
        "ByValue"
        (Fields.unnamed
          [
            (Field.mk
              []
              Visibility.inherited
              none
              (Ty.path none (Path.mk false [(PathSegment.mk "ValueExpr" PathArguments.none)])))])
        none),
      (Variant.mk
        [
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue
              " Pass the argument value in-place; the contents of this place may be altered arbitrarily by the callee."))]
        "InPlace"
        (Fields.unnamed
          [
            (Field.mk
              []
              Visibility.inherited
              none
              (Ty.path none (Path.mk false [(PathSegment.mk "PlaceExpr" PathArguments.none)])))])
        none)])

/-- `spec/lang/syntax.md:398` -/
def enum_CallingConvention : Item :=
  (Item.enum
    [
      (Attr.mk
        true
        "doc"
        (AttrMeta.nameValue
          " The `CallingConvention` defines how function arguments and return values are passed.")),
      (Attr.mk true "doc" (AttrMeta.nameValue "")),
      (Attr.mk
        true
        "doc"
        (AttrMeta.nameValue
          " The assumption is that if caller and callee agree on the calling convention, and all arguments and the return types")),
      (Attr.mk
        true
        "doc"
        (AttrMeta.nameValue
          " pass `check_abi_compatibility`, then this implies they are ABI-compatible on real implementations."))]
    Visibility.pub
    "CallingConvention"
    (Generics.mk [] [])
    [(Variant.mk [] "Rust" Fields.unit none), (Variant.mk [] "C" Fields.unit none)])

/-- `spec/lang/syntax.md:406` -/
def enum_IntrinsicLockOp : Item :=
  (Item.enum
    []
    Visibility.pub
    "IntrinsicLockOp"
    (Generics.mk [] [])
    [
      (Variant.mk [] "Acquire" Fields.unit none),
      (Variant.mk [] "Release" Fields.unit none),
      (Variant.mk [] "Create" Fields.unit none)])

/-- `spec/lang/syntax.md:412` -/
def enum_IntrinsicOp : Item :=
  (Item.enum
    [
      (Attr.mk true "doc" (AttrMeta.nameValue " The intrinsic operations supported by MiniRust.")),
      (Attr.mk
        true
        "doc"
        (AttrMeta.nameValue
          " Generally we only make things intrinsics if they cannot be operands, i.e.")),
      (Attr.mk
        true
        "doc"
        (AttrMeta.nameValue " they are non-deterministic or mutate the global state.")),
      (Attr.mk
        true
        "doc"
        (AttrMeta.nameValue
          " We also make them intrinsic if they return `()`, because an operand that")),
      (Attr.mk true "doc" (AttrMeta.nameValue " does not return anything is kind of odd."))]
    Visibility.pub
    "IntrinsicOp"
    (Generics.mk [] [])
    [
      (Variant.mk [] "Abort" Fields.unit none),
      (Variant.mk [] "Assume" Fields.unit none),
      (Variant.mk [] "Exit" Fields.unit none),
      (Variant.mk [] "PrintStdout" Fields.unit none),
      (Variant.mk [] "PrintStderr" Fields.unit none),
      (Variant.mk [] "Allocate" Fields.unit none),
      (Variant.mk [] "Deallocate" Fields.unit none),
      (Variant.mk [] "Spawn" Fields.unit none),
      (Variant.mk [] "Join" Fields.unit none),
      (Variant.mk
        [
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue
              " Determines whether the raw bytes pointed to by two pointers are equal.")),
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue " (Can't be an operand because it reads from memory.)"))]
        "RawEq"
        Fields.unit
        none),
      (Variant.mk [] "AtomicStore" Fields.unit none),
      (Variant.mk [] "AtomicLoad" Fields.unit none),
      (Variant.mk [] "AtomicCompareExchange" Fields.unit none),
      (Variant.mk
        []
        "AtomicFetchAndOp"
        (Fields.unnamed
          [
            (Field.mk
              []
              Visibility.inherited
              none
              (Ty.path none (Path.mk false [(PathSegment.mk "IntBinOp" PathArguments.none)])))])
        none),
      (Variant.mk
        []
        "Lock"
        (Fields.unnamed
          [
            (Field.mk
              []
              Visibility.inherited
              none
              (Ty.path none (Path.mk false [(PathSegment.mk "IntrinsicLockOp" PathArguments.none)])))])
        none),
      (Variant.mk
        [
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue
              " 'Expose' the provenance a pointer so that it can later be cast to an integer.")),
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue " The address part of the pointer is stored in `destination`."))]
        "PointerExposeProvenance"
        Fields.unit
        none),
      (Variant.mk
        [
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue
              " Create a new pointer from the given address with some previously exposed provenance."))]
        "PointerWithExposedProvenance"
        Fields.unit
        none),
      (Variant.mk
        [
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue
              " Access the current unwinding payload. UB if not currently unwinding."))]
        "GetUnwindPayload"
        Fields.unit
        none)])

/-- `spec/lang/syntax.md:450` -/
def struct_FnName : Item :=
  (Item.struct
    [
      (Attr.mk
        true
        "doc"
        (AttrMeta.nameValue
          " Opaque types of names for functions, vtables, trait methods, and globals.")),
      (Attr.mk
        true
        "doc"
        (AttrMeta.nameValue " The internal representations of these types do not matter."))]
    Visibility.pub
    "FnName"
    (Generics.mk [] [])
    (Fields.unnamed
      [
        (Field.mk
          []
          Visibility.pub
          none
          (Ty.path
            none
            (Path.mk
              false
              [
                (PathSegment.mk "libspecr" PathArguments.none),
                (PathSegment.mk "Name" PathArguments.none)])))]))

/-- `spec/lang/syntax.md:453` -/
def struct_GlobalName : Item :=
  (Item.struct
    []
    Visibility.pub
    "GlobalName"
    (Generics.mk [] [])
    (Fields.unnamed
      [
        (Field.mk
          []
          Visibility.pub
          none
          (Ty.path
            none
            (Path.mk
              false
              [
                (PathSegment.mk "libspecr" PathArguments.none),
                (PathSegment.mk "Name" PathArguments.none)])))]))

/-- `spec/lang/syntax.md:454` -/
def struct_VTableName : Item :=
  (Item.struct
    []
    Visibility.pub
    "VTableName"
    (Generics.mk [] [])
    (Fields.unnamed
      [
        (Field.mk
          []
          Visibility.pub
          none
          (Ty.path
            none
            (Path.mk
              false
              [
                (PathSegment.mk "libspecr" PathArguments.none),
                (PathSegment.mk "Name" PathArguments.none)])))]))

/-- `spec/lang/syntax.md:455` -/
def struct_TraitMethodName : Item :=
  (Item.struct
    []
    Visibility.pub
    "TraitMethodName"
    (Generics.mk [] [])
    (Fields.unnamed
      [
        (Field.mk
          []
          Visibility.pub
          none
          (Ty.path
            none
            (Path.mk
              false
              [
                (PathSegment.mk "libspecr" PathArguments.none),
                (PathSegment.mk "Name" PathArguments.none)])))]))

/-- `spec/lang/syntax.md:457` -/
def struct_Program : Item :=
  (Item.struct
    [(Attr.mk true "doc" (AttrMeta.nameValue " A closed MiniRust program."))]
    Visibility.pub
    "Program"
    (Generics.mk [] [])
    (Fields.named
      [
        (Field.mk
          [
            (Attr.mk
              true
              "doc"
              (AttrMeta.nameValue " Associate a function with each declared function name."))]
          Visibility.pub
          (some "functions")
          (Ty.path
            none
            (Path.mk
              false
              [
                (PathSegment.mk
                  "Map"
                  (PathArguments.angleBracketed
                    false
                    [
                      (GenericArgument.type
                        (Ty.path
                          none
                          (Path.mk false [(PathSegment.mk "FnName" PathArguments.none)]))),
                      (GenericArgument.type
                        (Ty.path
                          none
                          (Path.mk false [(PathSegment.mk "Function" PathArguments.none)])))]))]))),
        (Field.mk
          [(Attr.mk true "doc" (AttrMeta.nameValue " The function where execution starts."))]
          Visibility.pub
          (some "start")
          (Ty.path none (Path.mk false [(PathSegment.mk "FnName" PathArguments.none)]))),
        (Field.mk
          [
            (Attr.mk
              true
              "doc"
              (AttrMeta.nameValue " Associate each global name with the associated global."))]
          Visibility.pub
          (some "globals")
          (Ty.path
            none
            (Path.mk
              false
              [
                (PathSegment.mk
                  "Map"
                  (PathArguments.angleBracketed
                    false
                    [
                      (GenericArgument.type
                        (Ty.path
                          none
                          (Path.mk false [(PathSegment.mk "GlobalName" PathArguments.none)]))),
                      (GenericArgument.type
                        (Ty.path
                          none
                          (Path.mk false [(PathSegment.mk "Global" PathArguments.none)])))]))]))),
        (Field.mk
          [
            (Attr.mk
              true
              "doc"
              (AttrMeta.nameValue
                " Stores all traits and method names which are available for dynamic dispatch."))]
          Visibility.pub
          (some "traits")
          (Ty.path
            none
            (Path.mk
              false
              [
                (PathSegment.mk
                  "Map"
                  (PathArguments.angleBracketed
                    false
                    [
                      (GenericArgument.type
                        (Ty.path
                          none
                          (Path.mk false [(PathSegment.mk "TraitName" PathArguments.none)]))),
                      (GenericArgument.type
                        (Ty.path
                          none
                          (Path.mk
                            false
                            [
                              (PathSegment.mk
                                "Set"
                                (PathArguments.angleBracketed
                                  false
                                  [
                                    (GenericArgument.type
                                      (Ty.path
                                        none
                                        (Path.mk
                                          false
                                          [(PathSegment.mk "TraitMethodName" PathArguments.none)])))]))])))]))]))),
        (Field.mk
          [
            (Attr.mk
              true
              "doc"
              (AttrMeta.nameValue " Store the vtables with method tables and layout information."))]
          Visibility.pub
          (some "vtables")
          (Ty.path
            none
            (Path.mk
              false
              [
                (PathSegment.mk
                  "Map"
                  (PathArguments.angleBracketed
                    false
                    [
                      (GenericArgument.type
                        (Ty.path
                          none
                          (Path.mk false [(PathSegment.mk "VTableName" PathArguments.none)]))),
                      (GenericArgument.type
                        (Ty.path
                          none
                          (Path.mk false [(PathSegment.mk "VTable" PathArguments.none)])))]))])))]))

/-- `spec/lang/syntax.md:471` -/
def struct_LocalName : Item :=
  (Item.struct
    [
      (Attr.mk
        true
        "doc"
        (AttrMeta.nameValue " Opaque types of names for local variables and basic blocks."))]
    Visibility.pub
    "LocalName"
    (Generics.mk [] [])
    (Fields.unnamed
      [
        (Field.mk
          []
          Visibility.pub
          none
          (Ty.path
            none
            (Path.mk
              false
              [
                (PathSegment.mk "libspecr" PathArguments.none),
                (PathSegment.mk "Name" PathArguments.none)])))]))

/-- `spec/lang/syntax.md:473` -/
def struct_BbName : Item :=
  (Item.struct
    []
    Visibility.pub
    "BbName"
    (Generics.mk [] [])
    (Fields.unnamed
      [
        (Field.mk
          []
          Visibility.pub
          none
          (Ty.path
            none
            (Path.mk
              false
              [
                (PathSegment.mk "libspecr" PathArguments.none),
                (PathSegment.mk "Name" PathArguments.none)])))]))

/-- `spec/lang/syntax.md:475` -/
def struct_Function : Item :=
  (Item.struct
    [(Attr.mk true "doc" (AttrMeta.nameValue " A MiniRust function."))]
    Visibility.pub
    "Function"
    (Generics.mk [] [])
    (Fields.named
      [
        (Field.mk
          [
            (Attr.mk
              true
              "doc"
              (AttrMeta.nameValue " The locals of this function, and their type."))]
          Visibility.pub
          (some "locals")
          (Ty.path
            none
            (Path.mk
              false
              [
                (PathSegment.mk
                  "Map"
                  (PathArguments.angleBracketed
                    false
                    [
                      (GenericArgument.type
                        (Ty.path
                          none
                          (Path.mk false [(PathSegment.mk "LocalName" PathArguments.none)]))),
                      (GenericArgument.type
                        (Ty.path none (Path.mk false [(PathSegment.mk "Type" PathArguments.none)])))]))]))),
        (Field.mk
          [
            (Attr.mk
              true
              "doc"
              (AttrMeta.nameValue
                " A list of locals that are initially filled with the function arguments."))]
          Visibility.pub
          (some "args")
          (Ty.path
            none
            (Path.mk
              false
              [
                (PathSegment.mk
                  "List"
                  (PathArguments.angleBracketed
                    false
                    [
                      (GenericArgument.type
                        (Ty.path
                          none
                          (Path.mk false [(PathSegment.mk "LocalName" PathArguments.none)])))]))]))),
        (Field.mk
          [
            (Attr.mk
              true
              "doc"
              (AttrMeta.nameValue
                " The name of a local that holds the return value when the function returns."))]
          Visibility.pub
          (some "ret")
          (Ty.path none (Path.mk false [(PathSegment.mk "LocalName" PathArguments.none)]))),
        (Field.mk
          [
            (Attr.mk
              true
              "doc"
              (AttrMeta.nameValue " The call calling convention of this function."))]
          Visibility.pub
          (some "calling_convention")
          (Ty.path none (Path.mk false [(PathSegment.mk "CallingConvention" PathArguments.none)]))),
        (Field.mk
          [
            (Attr.mk
              true
              "doc"
              (AttrMeta.nameValue " Associate each basic block name with the associated block."))]
          Visibility.pub
          (some "blocks")
          (Ty.path
            none
            (Path.mk
              false
              [
                (PathSegment.mk
                  "Map"
                  (PathArguments.angleBracketed
                    false
                    [
                      (GenericArgument.type
                        (Ty.path
                          none
                          (Path.mk false [(PathSegment.mk "BbName" PathArguments.none)]))),
                      (GenericArgument.type
                        (Ty.path
                          none
                          (Path.mk false [(PathSegment.mk "BasicBlock" PathArguments.none)])))]))]))),
        (Field.mk
          [(Attr.mk true "doc" (AttrMeta.nameValue " The basic block where execution starts."))]
          Visibility.pub
          (some "start")
          (Ty.path none (Path.mk false [(PathSegment.mk "BbName" PathArguments.none)]))),
        (Field.mk
          [
            (Attr.mk
              true
              "doc"
              (AttrMeta.nameValue " Whether implicit writes are enabled for this function."))]
          Visibility.pub
          (some "implicit_writes")
          (Ty.path none (Path.mk false [(PathSegment.mk "bool" PathArguments.none)])))]))

/-- `spec/lang/syntax.md:495` -/
def struct_BasicBlock : Item :=
  (Item.struct
    [
      (Attr.mk
        true
        "doc"
        (AttrMeta.nameValue " A basic block is a sequence of statements followed by a terminator."))]
    Visibility.pub
    "BasicBlock"
    (Generics.mk [] [])
    (Fields.named
      [
        (Field.mk
          []
          Visibility.pub
          (some "statements")
          (Ty.path
            none
            (Path.mk
              false
              [
                (PathSegment.mk
                  "List"
                  (PathArguments.angleBracketed
                    false
                    [
                      (GenericArgument.type
                        (Ty.path
                          none
                          (Path.mk false [(PathSegment.mk "Statement" PathArguments.none)])))]))]))),
        (Field.mk
          []
          Visibility.pub
          (some "terminator")
          (Ty.path none (Path.mk false [(PathSegment.mk "Terminator" PathArguments.none)]))),
        (Field.mk
          []
          Visibility.pub
          (some "kind")
          (Ty.path none (Path.mk false [(PathSegment.mk "BbKind" PathArguments.none)])))]))

/-- `spec/lang/syntax.md:502` -/
def enum_BbKind : Item :=
  (Item.enum
    [(Attr.mk true "doc" (AttrMeta.nameValue " The kind of a basic block in the CFG."))]
    Visibility.pub
    "BbKind"
    (Generics.mk [] [])
    [
      (Variant.mk
        [
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue
              " Regular blocks may use `Return` and `StartUnwind` but not `ResumeUnwind`."))]
        "Regular"
        Fields.unit
        none),
      (Variant.mk
        [
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue
              " Cleanup blocks may use `ResumeUnwind` but not `Return` or `StartUnwind`."))]
        "Cleanup"
        Fields.unit
        none),
      (Variant.mk
        [
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue
              " Catch blocks may use neither `Return` nor `ResumeUnwind` nor `StartUnwind`. ")),
          (Attr.mk true "doc" (AttrMeta.nameValue " Catch blocks may branch to regular blocks."))]
        "Catch"
        Fields.unit
        none),
      (Variant.mk
        [
          (Attr.mk
            true
            "doc"
            (AttrMeta.nameValue
              " `Terminate` blocks may use neither `Return` nor `ResumeUnwind` nor `StartUnwind`."))]
        "Terminate"
        Fields.unit
        none)])

/-- `spec/lang/syntax.md:515` -/
def struct_Global : Item :=
  (Item.struct
    [(Attr.mk true "doc" (AttrMeta.nameValue " A global allocation."))]
    Visibility.pub
    "Global"
    (Generics.mk [] [])
    (Fields.named
      [
        (Field.mk
          [
            (Attr.mk
              true
              "doc"
              (AttrMeta.nameValue
                " The raw bytes of the allocation. `None` represents uninitialized bytes."))]
          Visibility.pub
          (some "bytes")
          (Ty.path
            none
            (Path.mk
              false
              [
                (PathSegment.mk
                  "List"
                  (PathArguments.angleBracketed
                    false
                    [
                      (GenericArgument.type
                        (Ty.path
                          none
                          (Path.mk
                            false
                            [
                              (PathSegment.mk
                                "Option"
                                (PathArguments.angleBracketed
                                  false
                                  [
                                    (GenericArgument.type
                                      (Ty.path
                                        none
                                        (Path.mk false [(PathSegment.mk "u8" PathArguments.none)])))]))])))]))]))),
        (Field.mk
          [
            (Attr.mk
              true
              "doc"
              (AttrMeta.nameValue " Cross-references pointing to other global allocations,")),
            (Attr.mk
              true
              "doc"
              (AttrMeta.nameValue
                " together with an offset, expressing where this allocation should put the pointer.")),
            (Attr.mk
              true
              "doc"
              (AttrMeta.nameValue
                " Note that the pointers created due to relocations overwrite the data given by `bytes`."))]
          Visibility.pub
          (some "relocations")
          (Ty.path
            none
            (Path.mk
              false
              [
                (PathSegment.mk
                  "List"
                  (PathArguments.angleBracketed
                    false
                    [
                      (GenericArgument.type
                        (Ty.tuple
                          [
                            (Ty.path
                              none
                              (Path.mk false [(PathSegment.mk "Offset" PathArguments.none)])),
                            (Ty.path
                              none
                              (Path.mk false [(PathSegment.mk "Relocation" PathArguments.none)]))]))]))]))),
        (Field.mk
          [
            (Attr.mk
              true
              "doc"
              (AttrMeta.nameValue " The alignment with which this global shall be allocated."))]
          Visibility.pub
          (some "align")
          (Ty.path none (Path.mk false [(PathSegment.mk "Align" PathArguments.none)])))]))

/-- `spec/lang/syntax.md:527` -/
def struct_Relocation : Item :=
  (Item.struct
    [(Attr.mk true "doc" (AttrMeta.nameValue " A pointer into a global allocation."))]
    Visibility.pub
    "Relocation"
    (Generics.mk [] [])
    (Fields.named
      [
        (Field.mk
          [
            (Attr.mk
              true
              "doc"
              (AttrMeta.nameValue " The name of the global allocation we are pointing into."))]
          Visibility.pub
          (some "name")
          (Ty.path none (Path.mk false [(PathSegment.mk "GlobalName" PathArguments.none)]))),
        (Field.mk
          [(Attr.mk true "doc" (AttrMeta.nameValue " The offset within that allocation."))]
          Visibility.pub
          (some "offset")
          (Ty.path none (Path.mk false [(PathSegment.mk "Offset" PathArguments.none)])))]))

/-- `spec/lang/syntax.md:535` -/
def struct_VTable : Item :=
  (Item.struct
    [
      (Attr.mk true "doc" (AttrMeta.nameValue " A vtable for a trait-type pair.")),
      (Attr.mk true "doc" (AttrMeta.nameValue " This is pointed to by the trait object metadata."))]
    Visibility.pub
    "VTable"
    (Generics.mk [] [])
    (Fields.named
      [
        (Field.mk
          [
            (Attr.mk true "doc" (AttrMeta.nameValue " What trait this vtable is for.")),
            (Attr.mk
              true
              "doc"
              (AttrMeta.nameValue
                " All vtables for this trait name have implementation for same set of methods."))]
          Visibility.pub
          (some "trait_name")
          (Ty.path none (Path.mk false [(PathSegment.mk "TraitName" PathArguments.none)]))),
        (Field.mk
          [(Attr.mk true "doc" (AttrMeta.nameValue " The size of the type."))]
          Visibility.pub
          (some "size")
          (Ty.path none (Path.mk false [(PathSegment.mk "Size" PathArguments.none)]))),
        (Field.mk
          [(Attr.mk true "doc" (AttrMeta.nameValue " The alignment of the type."))]
          Visibility.pub
          (some "align")
          (Ty.path none (Path.mk false [(PathSegment.mk "Align" PathArguments.none)]))),
        (Field.mk
          [
            (Attr.mk
              true
              "doc"
              (AttrMeta.nameValue " Offset and sizes of `UnsafeCell` in this vtable."))]
          Visibility.pub
          (some "cells")
          (Ty.path
            none
            (Path.mk
              false
              [
                (PathSegment.mk
                  "List"
                  (PathArguments.angleBracketed
                    false
                    [
                      (GenericArgument.type
                        (Ty.tuple
                          [
                            (Ty.path
                              none
                              (Path.mk false [(PathSegment.mk "Offset" PathArguments.none)])),
                            (Ty.path
                              none
                              (Path.mk false [(PathSegment.mk "Size" PathArguments.none)]))]))]))]))),
        (Field.mk
          [(Attr.mk true "doc" (AttrMeta.nameValue " The implementations of trait methods."))]
          Visibility.pub
          (some "methods")
          (Ty.path
            none
            (Path.mk
              false
              [
                (PathSegment.mk
                  "Map"
                  (PathArguments.angleBracketed
                    false
                    [
                      (GenericArgument.type
                        (Ty.path
                          none
                          (Path.mk false [(PathSegment.mk "TraitMethodName" PathArguments.none)]))),
                      (GenericArgument.type
                        (Ty.path
                          none
                          (Path.mk false [(PathSegment.mk "FnName" PathArguments.none)])))]))])))]))

/-- All items of `spec/lang/syntax.md`, in source order, with provenance. -/
def items : List SourceItem :=
  [
    (SourceItem.mk
      "enum_ValueExpr"
      16
      "c3b9c0caf6c3395f93b9a5bd8b38a49132bc9733610b433b6bcef54230bef621"
      enum_ValueExpr),
    (SourceItem.mk
      "enum_Constant"
      80
      "40401114559ad6688a9150fb9ac898ce6ca0c33c394a2c171b42066c4a23ffc1"
      enum_Constant),
    (SourceItem.mk
      "enum_IntUnOp"
      97
      "b62314e500c8d64872e3c0c8aa5fbdde76b03dee657d570e1ca25ec4148b5a08"
      enum_IntUnOp),
    (SourceItem.mk
      "enum_CastOp"
      105
      "3b1f9882b40dcfadf561816b2d161016ac1a269a264a466af1bb01c74ca06290"
      enum_CastOp),
    (SourceItem.mk
      "enum_UnOp"
      113
      "804c5f8da73170c11031272ba78238d78cd2e6a16c6241da560dfa5a711bd737"
      enum_UnOp),
    (SourceItem.mk
      "enum_IntBinOp"
      136
      "619ffaf3682daa7a3086a6a0339a6c0a2a3e11092f9144f116e65aeb518c945e"
      enum_IntBinOp),
    (SourceItem.mk
      "enum_IntBinOpWithOverflow"
      178
      "f001bee8536e66eb0eedae195e3fec8e7f20624be166444feb4d1c015e19f648"
      enum_IntBinOpWithOverflow),
    (SourceItem.mk
      "enum_RelOp"
      189
      "3fb7c52cf5caf96b44cba3639efb55a6506c10fdae10ddd6ff61dd33d617c266"
      enum_RelOp),
    (SourceItem.mk
      "enum_BinOp"
      211
      "f3ec4e6c3401f7b88a41e5965497e75cc152f8697a28125af76f9a7365a4ac63"
      enum_BinOp),
    (SourceItem.mk
      "enum_PlaceExpr"
      241
      "815c49b1eb5b098d59995810c00cce6e37dedc0163eb9b96a6c773bb396d8864"
      enum_PlaceExpr),
    (SourceItem.mk
      "enum_Statement"
      285
      "664899bb9876acd105896f7f76fecd40049f7921e834f9e9eb08ce1b6ef3e710"
      enum_Statement),
    (SourceItem.mk
      "enum_Terminator"
      320
      "a95fe9e3a6c0d5d4a2b001478fb3680396896177264c817e18ac3d5f9f60d485"
      enum_Terminator),
    (SourceItem.mk
      "enum_ArgumentExpr"
      387
      "624e1adbffc49d48227534e98e79a29a57832be6bb0fdd339143791625087204"
      enum_ArgumentExpr),
    (SourceItem.mk
      "enum_CallingConvention"
      398
      "2bef60f954bc40eeef2421b6b750b1aad8d2e44c7912f3dacd987b8d8e88b48d"
      enum_CallingConvention),
    (SourceItem.mk
      "enum_IntrinsicLockOp"
      406
      "e9d200a5b782b0c3ac6e1aa3e8fd87cde976a060d7f5f09506637f58dc7dac9d"
      enum_IntrinsicLockOp),
    (SourceItem.mk
      "enum_IntrinsicOp"
      412
      "4c29473feb47a729547f1d8282b41231958c91ad82b507faafefbbd65d190746"
      enum_IntrinsicOp),
    (SourceItem.mk
      "struct_FnName"
      450
      "95910adc1435c7ccebdd7549a34d2b0e68bf32815c34f2b68f723f3379cf6747"
      struct_FnName),
    (SourceItem.mk
      "struct_GlobalName"
      453
      "efef6220b21a53c9f95a29b09100dcf2e7640999ef1fc5dbe15d66097a1fef70"
      struct_GlobalName),
    (SourceItem.mk
      "struct_VTableName"
      454
      "c5a12ff0a37067a83e534624043fe948f84b6bfdfa64f176eafd0cee4598773e"
      struct_VTableName),
    (SourceItem.mk
      "struct_TraitMethodName"
      455
      "04919bb575ec5578754542446e5876d4f816a4a1af3b383a068ca88b05bad06e"
      struct_TraitMethodName),
    (SourceItem.mk
      "struct_Program"
      457
      "2dfa1bdf3d785a092d0f6553ec33161b37dd2a9f8f478a7e1c8242f65e5640b1"
      struct_Program),
    (SourceItem.mk
      "struct_LocalName"
      471
      "87edfd919ab565e2413738dcddc7705ed734602b782dca1511083359f5820cec"
      struct_LocalName),
    (SourceItem.mk
      "struct_BbName"
      473
      "99405ce076b3285b9609f802ad89ebdb98c48412a14dd8a056cb3d4a01fe3346"
      struct_BbName),
    (SourceItem.mk
      "struct_Function"
      475
      "8db9904e725fb3c9cc1a66dcb8e1ea89380dd21681e1851d6797836e5937ff9a"
      struct_Function),
    (SourceItem.mk
      "struct_BasicBlock"
      495
      "5ca2760f56dd4c365c70d7cdd38899e865711f5ddc59b4ee52bc94bef1b8f87e"
      struct_BasicBlock),
    (SourceItem.mk
      "enum_BbKind"
      502
      "596f76326a8206c650cbf81f5eb642871937d2bafdfb8e81b115f9dfd21f1bff"
      enum_BbKind),
    (SourceItem.mk
      "struct_Global"
      515
      "9bf850811ebcb18134a526a741f082566cea7c31000565b5a1740520bb4b422c"
      struct_Global),
    (SourceItem.mk
      "struct_Relocation"
      527
      "4d1b1780d99b836500640e8e4809ef4dbf2ca55ef5cc11a7154aec19d1503856"
      struct_Relocation),
    (SourceItem.mk
      "struct_VTable"
      535
      "d0d077d93f89bdc188d67a124327e832a14dcc1898107081e53c3f4d57c9721e"
      struct_VTable)]

end MiniRustSpec.Gen.Items.Lang.Syntax
