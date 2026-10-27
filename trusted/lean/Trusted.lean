-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.Core

namespace Trusted

/-- Declaration macro that strips Anneal's in-place trust-tier attributes
    (`@[vetted]` and `@[candidate <feature>]`) from top-level declarations and
    `inductive` constructors after `trusted/audit/TrustedBoundary.lean`
    validates and records them during `preflight`. -/
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

@[candidate refinement]
def BoundaryMarker : Prop := True

end Trusted
