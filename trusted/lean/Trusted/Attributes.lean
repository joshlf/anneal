-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.NotationExtra

/-!
# Trust-Tier Declaration Attributes and Guards (`Trusted/Attributes.lean`)

This module provides the in-module syntax macro
(`Trusted.expandTrustDeclaration`) and kernel expression marker
(`Trusted.candidate`) that pair with the external boundary auditor in
`trusted/audit/TrustedBoundary.lean`.

## Why These Definitions Live in `trusted/lean/`

`TrustedBoundary.lean` imports Lean's compiler and metaprogramming libraries and
executes out-of-process via `lean --run`. By contrast, `Trusted.*` modules are
compiled with `prelude` on top of the locked `Init.*` foundation
(`trusted/lean/foundation-lock.json`), which does not define `@[vetted]` or
`@[candidate <feature>]` attributes.

To attach trust-tier metadata directly to `Trusted.*` declarations without
importing metaprogramming libraries into the TCB foundation, attribute
handling splits across two stages:

1. **Source preflight (`TrustedBoundary.lean` `"preflight"` mode):** Before any
   file is compiled, `TrustedBoundary.lean` parses the raw source syntax of each
   `Trusted.*` module, validates that every declaration carries `@[vetted]` or
   `@[candidate <feature>]`, and records the resulting declaration table.
2. **Compilation and `.olean` audit (`Trusted.expandTrustDeclaration` and
   `Trusted.candidate`):**
   - During `lean --setup` compilation, `Trusted.expandTrustDeclaration` strips
     `@[vetted]` and `@[candidate <feature>]` from top-level declarations and
     `inductive` constructors before Lean's command elaborator checks attribute
     names.
   - Inside a `@[vetted]` function body that pattern-matches on a `@[vetted]`
     inductive with `@[candidate <feature>]` constructors, wrapping a candidate
     constructor's match arm in `Trusted.candidate "<feature>" (...)` preserves
     an explicit constant application in the compiled `.olean` kernel `Expr`
     tree. Phase 2 (`"audit"` mode) of `TrustedBoundary.lean` recognizes
     `Trusted.candidate` applications to verify non-contamination and track
     which candidate features a crate actually reaches.
-/

namespace Trusted

/-- Command macro that strips Anneal's in-place trust-tier attributes
    (`@[vetted]` and `@[candidate <feature>]`) from top-level declarations and
    `inductive` constructors after `trusted/audit/TrustedBoundary.lean` has
    validated and recorded them during `"preflight"`.

    `TrustedBoundary.lean` specifically permits `@[macro ...]` only on the
    declaration named `Trusted.expandTrustDeclaration`. When a declaration
    contains neither `@[vetted]` nor `@[candidate ...]`, this macro throws
    `Lean.Macro.throwUnsupported` so Lean's built-in declaration elaborator
    processes the stripped declaration without re-invoking this macro. -/
@[macro Lean.Parser.Command.declaration, macro Lean.Parser.Command.mutual]
def expandTrustDeclaration : Lean.Macro := fun stx =>
  -- Remove `@[vetted]` and `@[candidate ...]` entries from a
  -- `Lean.Parser.Command.declModifiers` node `mods`.
  --
  -- In Lean's command grammar, `mods.getArg 1` is the optional
  -- `Lean.Parser.Term.attributes` wrapper `@[...]`, whose first child `inner`
  -- holds the comma-separated `sepBy1` array of `attrInstance` nodes at
  -- `inner.getArg 1`.
  let stripAttrs (mods : Lean.Syntax) : Bool × Lean.Syntax :=
    let attrsNode := mods.getArg 1
    match attrsNode.getArgs[0]? with
    | none => (false, mods)
    | some inner =>
      let (changed, kept) := (inner.getArg 1).getArgs.foldl (init := (false, #[])) fun (chg, acc) elem =>
        if elem.getKind == `Lean.Parser.Term.attrInstance then
          let attr := elem.getArg 1
          if attr.getKind == `Lean.Parser.Attr.simple &&
              ((attr.getArg 0).getId == `vetted || (attr.getArg 0).getId == `candidate) then
            (true, acc)
          else (chg, acc.push elem)
        else (chg, acc)
      if !changed then (false, mods) else
        -- If every attribute on `mods` was a trust-tier attribute, replace the
        -- optional `attributes` node with an empty null node; otherwise rebuild
        -- the comma-separated attribute list with the remaining attributes.
        if kept.isEmpty then
          (true, mods.setArg 1 (Lean.mkNullNode))
        else
          let sep := Lean.Syntax.mkSep kept (.atom .none ",")
          (true, mods.setArg 1 (attrsNode.setArg 0 (inner.setArg 1 sep)))
  -- Strip trust-tier attributes from a single `Lean.Parser.Command.declaration`
  -- node `s`: both its outer `declModifiers` (`s.getArg 0`) and, when the
  -- inner declaration (`s.getArg 1`) is `Lean.Parser.Command.inductive`, each
  -- constructor's `declModifiers` (`ctor.getArg 2` inside `decl.getArg 4`).
  let stripDecl (s : Lean.Syntax) : Bool × Lean.Syntax :=
    if s.getKind != `Lean.Parser.Command.declaration then (false, s) else
      let (mc, mods') := stripAttrs (s.getArg 0)
      let decl := s.getArg 1
      let (dc, decl') :=
        if decl.getKind != `Lean.Parser.Command.inductive then (false, decl) else
          let (cc, ctors') := (decl.getArg 4).getArgs.foldl (init := (false, #[])) fun (c, acc) ctor =>
            let (kc, m') := stripAttrs (ctor.getArg 2)
            (c || kc, acc.push (if kc then ctor.setArg 2 m' else ctor))
          (cc, if cc then decl.setArg 4 (Lean.mkNullNode ctors') else decl)
      (mc || dc, if mc || dc then (s.setArg 0 mods').setArg 1 decl' else s)
  -- For `mutual ... end` blocks, strip every member declaration in
  -- `stx.getArg 1`. Once all trust attributes are removed, throw
  -- `throwUnsupported` so macro expansion terminates and hands the cleaned
  -- syntax to Lean's built-in command elaborator.
  if stx.getKind == `Lean.Parser.Command.mutual then
    let (mc, items') := (stx.getArg 1).getArgs.foldl (init := (false, #[])) fun (c, acc) item =>
      let (ic, item') := stripDecl item
      (c || ic, acc.push item')
    if mc then pure (stx.setArg 1 (Lean.mkNullNode items')) else Lean.Macro.throwUnsupported
  else
    let (c, stx') := stripDecl stx
    if c then pure stx' else Lean.Macro.throwUnsupported

/-- Identity marker used inside a `@[vetted]` declaration's body to guard a
    match arm that handles a `@[candidate <feature>]` constructor.

    In `"audit"` mode, `trusted/audit/TrustedBoundary.lean` (`exprEdges`)
    recognizes `@Trusted.candidate "<feat>" α body` applications in the compiled
    `.olean` expression tree:
    1. It checks that every `Trusted.candidate "<feat>"` guard in a `@[vetted]`
       body is paired one-to-one with pattern-matching on a `@[vetted]`
       inductive's `@[candidate <feat>]` constructors, and that the guarded
       subexpression `body` references only `@[vetted]` and
       `@[candidate <feat>]` constants.
    2. When computing the active candidate features of a verified crate, it
       defers traversing `body` unless `candidate:<feat>` is actually reached by
       the crate, so an unused candidate constructor arm in a `@[vetted]`
       definition does not contaminate crates that do not use `<feat>`. -/
@[vetted, reducible]
def candidate (_feat : String) {α : Sort u} (x : α) : α := x

end Trusted
