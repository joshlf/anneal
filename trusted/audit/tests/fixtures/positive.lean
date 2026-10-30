-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.NotationExtra

namespace Trusted

@[macro Lean.Parser.Command.declaration, macro Lean.Parser.Command.mutual]
def expandTrustDeclaration : Lean.Macro := fun stx =>
  let emptyArr : Array Lean.Syntax := Array.mk List.nil
  let setArg (s : Lean.Syntax) (i : Nat) (v : Lean.Syntax) : Lean.Syntax :=
    match s, i with
    | .node info k (.mk (_ :: r)), 0 => .node info k (.mk (v :: r))
    | .node info k (.mk (a :: _ :: r)), 1 => .node info k (.mk (a :: v :: r))
    | .node info k (.mk (a :: b :: _ :: r)), 2 => .node info k (.mk (a :: b :: v :: r))
    | .node info k (.mk (a :: b :: c :: d :: _ :: r)), 4 => .node info k (.mk (a :: b :: c :: d :: v :: r))
    | other, _ => other
  let stripAttrs (mods : Lean.Syntax) : Bool × Lean.Syntax :=
    let attrsNode := mods.getArg 1
    match attrsNode.getArgs.toList with
    | .nil => (false, mods)
    | inner :: _ =>
      let (changed, kept) := List.foldl (fun (chg, acc) elem =>
        if elem.getKind == `Lean.Parser.Term.attrInstance then
          let attr := elem.getArg 1
          if attr.getKind == `Lean.Parser.Attr.simple &&
              ((attr.getArg 0).getId == `vetted || (attr.getArg 0).getId == `candidate) then
            (true, acc)
          else (chg, acc.push elem)
        else (chg, acc)) (false, emptyArr) (inner.getArg 1).getArgs.toList
      if !changed then (false, mods) else
        match kept.toList with
        | .nil => (true, setArg mods 1 (.node .none `null emptyArr))
        | first :: rest =>
          let sep := List.foldl (fun acc e => (acc.push (.atom .none ",")).push e) (emptyArr.push first) rest
          (true, setArg mods 1 (setArg attrsNode 0 (setArg inner 1 (.node .none `null sep))))
  let stripDecl (s : Lean.Syntax) : Bool × Lean.Syntax :=
    if s.getKind != `Lean.Parser.Command.declaration then (false, s) else
      let (mc, mods') := stripAttrs (s.getArg 0)
      let decl := s.getArg 1
      let (dc, decl') :=
        if decl.getKind != `Lean.Parser.Command.inductive then (false, decl) else
          let (cc, ctors') := List.foldl (fun (c, acc) ctor =>
            let (kc, m') := stripAttrs (ctor.getArg 2)
            (c || kc, acc.push (if kc then setArg ctor 2 m' else ctor))) (false, emptyArr) (decl.getArg 4).getArgs.toList
          (cc, if cc then setArg decl 4 (.node .none `null ctors') else decl)
      (mc || dc, if mc || dc then setArg (setArg s 0 mods') 1 decl' else s)
  if stx.getKind == `Lean.Parser.Command.mutual then
    let (mc, items') := List.foldl (fun (c, acc) item =>
      let (ic, item') := stripDecl item
      (c || ic, acc.push item')) (false, emptyArr) (stx.getArg 1).getArgs.toList
    if mc then pure (setArg stx 1 (.node .none `null items')) else Lean.Macro.throwUnsupported
  else
    let (c, stx') := stripDecl stx
    if c then pure stx' else Lean.Macro.throwUnsupported

end Trusted

namespace Outside

@[vetted]
private def helper (n : Nat) : Nat := n

@[vetted]
structure Box where
  value : Nat

@[vetted]
opaque sealed : Box := Box.mk (helper 7)

@[vetted, simp] theorem helper_eq (n : Nat) : Eq (helper n) n := by rfl

@[vetted]
noncomputable def chosen : Nat := Classical.choice ⟨0⟩
@[vetted]
theorem extensionality (p q : Prop) (h : p ↔ q) : Eq p q := propext h
@[vetted]
theorem quotient_sound (r : Nat → Nat → Prop) (a b : Nat) (h : r a b) :
    Eq (Quot.mk r a) (Quot.mk r b) := Quot.sound h

@[vetted]
class Wrap (α : Type) where
  wrap : α → Nat

@[vetted]
instance instWrapNat : Wrap Nat := ⟨helper⟩
@[vetted]
def inferred : Nat := Wrap.wrap (α := Nat) 3

@[vetted]
instance instCoeBoxNat : Coe Box Nat := ⟨Box.value⟩
@[vetted]
def coerced (b : Box) : Nat := b

@[vetted]
inductive Indexed : Nat → Type where
  | zero : Indexed 0
  | succ {n : Nat} : Indexed n → Indexed (n + 1)

mutual
  @[vetted]
  inductive Left where
    | mk : Right → Left
  @[vetted]
  inductive Right where
    | mk : Left → Right
end

@[vetted]
inductive Tree where
  | node : List Tree → Tree

@[vetted]
def matched (n : Nat) : Nat :=
  match n with
  | 0 => helper 0
  | k + 1 => helper k

@[vetted]
def sampleList : List Nat := [1, 2, 3]
@[vetted]
def sampleExists : Prop := ∃ n : Nat, sampleList[0]? = some n

end Outside

open Outside in
@[vetted]
def wrapped : Box := Box.mk 4
