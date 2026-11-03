/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

/-!
# Syntax schema for specr-lang (deep embedding target)

MiniRust's specification is written in *specr-lang*, a Rust-like meta language
(see the "specr lang" section of the vendored upstream `README.md`). Upstream
tooling parses it with the Rust `syn` crate; so does our translator
(`crates/anneal-minirust-gen`). This module defines Lean inductive types that
mirror `syn`'s syntax categories one-to-one, so that every top-level specr-lang
item of the pinned MiniRust snapshot can be emitted as a Lean term
(`MiniRustSpec.Gen.Items.*`).

The schema is *syntax only*: nothing here assigns meaning to specr-lang. The
correspondence is constructor-for-variant with `syn` (2.x):

* `Expr.call` is `syn::Expr::Call`, `Expr.methodCall` is `syn::Expr::MethodCall`,
  and so on. Constructors whose `syn` names collide with Lean keywords are
  renamed (`Expr.ite` for `syn::Expr::If`, `Expr.matchExpr` for
  `syn::Expr::Match`, `Expr.letCond` for `syn::Expr::Let`, ...).
* Spans, punctuation tokens, and `//` comments are not represented. `///` doc
  comments appear as `#[doc = ...]` attributes, as in `syn`.
* `verbatim` constructors (and `MacroBody.tokens`, `AttrMeta.list`) carry the
  source tokens of a node the translator did not decompose. The translator
  counts every such node as *opaque* in `minirust/coverage.json`; there is no
  other lossy path.
-/

namespace MiniRustSpec.Syntax

/-- An identifier (`syn::Ident`). -/
abbrev Ident := String

/-- A literal (`syn::Lit`). Integer literals keep their suffix (`1u8`). -/
inductive Lit : Type where
  | str (value : String)
  | byteStr (value : List UInt8)
  | byte (value : UInt8)
  | char (value : Char)
  | int (value : Nat) (suffix : String)
  | float (digits : String) (suffix : String)
  | bool (value : Bool)
  | verbatim (src : String)
  deriving DecidableEq

/-- Binary operators (`syn::BinOp`), including compound assignment. -/
inductive BinOp : Type where
  | add | sub | mul | div | rem | and | or | bitXor | bitAnd | bitOr | shl | shr
  | eq | lt | le | ne | ge | gt
  | addAssign | subAssign | mulAssign | divAssign | remAssign | bitXorAssign
  | bitAndAssign | bitOrAssign | shlAssign | shrAssign
  deriving DecidableEq

/-- Unary operators (`syn::UnOp`). -/
inductive UnOp : Type where
  | deref | not | neg
  deriving DecidableEq

/-- `..` versus `..=` (`syn::RangeLimits`). -/
inductive RangeLimits : Type where
  | halfOpen | closed
  deriving DecidableEq

/-- A field selector (`syn::Member`): `x.name` or `x.0`. -/
inductive Member : Type where
  | named (ident : Ident)
  | unnamed (index : Nat)
  deriving DecidableEq

/-- Item visibility (`syn::Visibility`). -/
inductive Visibility : Type where
  | pub
  | restricted (path : String)
  | inherited
  deriving DecidableEq

/-- Attribute arguments (`syn::Meta`). `list` keeps tool-directive tokens such
as `specr::argmatch(statement)` verbatim (counted as opaque). -/
inductive AttrMeta : Type where
  | path
  | list (tokens : String)
  | nameValue (value : String)
  deriving DecidableEq

/-- An attribute (`syn::Attribute`); `outer` is `#[..]` versus `#![..]`. -/
structure Attr : Type where
  outer : Bool
  path : String
  args : AttrMeta
  deriving DecidableEq

/-- Macro delimiters (`syn::MacroDelimiter`). -/
inductive MacroDelimiter : Type where
  | paren | brace | bracket
  deriving DecidableEq

/-- `use` trees (`syn::UseTree`). -/
inductive UseTree : Type where
  | path (ident : Ident) (tree : UseTree)
  | name (ident : Ident)
  | rename (ident : Ident) (rename : Ident)
  | glob
  | group (items : List UseTree)

mutual
/-- `syn::Path`. -/
inductive Path : Type where
  | mk (leadingColon : Bool) (segments : List PathSegment)
/-- `syn::PathSegment`. -/
inductive PathSegment : Type where
  | mk (ident : Ident) (arguments : PathArguments)
/-- `syn::PathArguments`; `turbofish` records `::<..>`. -/
inductive PathArguments : Type where
  | none
  | angleBracketed (turbofish : Bool) (args : List GenericArgument)
  | parenthesized (inputs : List Ty) (output : Option Ty)
/-- `syn::GenericArgument`. -/
inductive GenericArgument : Type where
  | lifetime (name : Ident)
  | type (ty : Ty)
  | const (expr : Expr)
  | assocType (ident : Ident) (generics : PathArguments) (ty : Ty)
  | assocConst (ident : Ident) (generics : PathArguments) (expr : Expr)
  | constraint (ident : Ident) (generics : PathArguments) (bounds : List TypeParamBound)
/-- `syn::QSelf`: the `<T as Trait>` part of a qualified path. -/
inductive QSelf : Type where
  | mk (ty : Ty) (position : Nat) (asTrait : Bool)
/-- Types (`syn::Type`). -/
inductive Ty : Type where
  | array (elem : Ty) (len : Expr)
  | bareFn (lifetimes : List Ident) (unsafety : Bool) (inputs : List Ty) (variadic : Bool)
      (output : Option Ty)
  | implTrait (bounds : List TypeParamBound)
  | traitObject (dyn : Bool) (bounds : List TypeParamBound)
  | infer
  | never
  | paren (elem : Ty)
  | group (elem : Ty)
  | path (qself : Option QSelf) (path : Path)
  | ptr (mutable : Bool) (elem : Ty)
  | reference (lifetime : Option Ident) (mutable : Bool) (elem : Ty)
  | slice (elem : Ty)
  | tuple (elems : List Ty)
  | macro (mac : Macro)
  | verbatim (src : String)
/-- `syn::TypeParamBound`; `maybe` is `?Sized`-style. -/
inductive TypeParamBound : Type where
  | trait (paren : Bool) (maybe : Bool) (lifetimes : List Ident) (path : Path)
  | lifetime (name : Ident)
  | verbatim (src : String)
/-- Expressions (`syn::Expr`). -/
inductive Expr : Type where
  | withAttrs (attrs : List Attr) (expr : Expr)
  | array (elems : List Expr)
  | assign (left : Expr) (right : Expr)
  | binary (left : Expr) (op : BinOp) (right : Expr)
  | block (label : Option Ident) (block : Block)
  | break (label : Option Ident) (expr : Option Expr)
  | call (func : Expr) (args : List Expr)
  | cast (expr : Expr) (ty : Ty)
  | closure (isMove : Bool) (inputs : List Pat) (output : Option Ty) (body : Expr)
  | constBlock (block : Block)
  | continue (label : Option Ident)
  | field (base : Expr) (member : Member)
  | forLoop (label : Option Ident) (pat : Pat) (expr : Expr) (body : Block)
  | group (expr : Expr)
  | ite (cond : Expr) (thenBranch : Block) (elseBranch : Option Expr)
  | index (expr : Expr) (index : Expr)
  | infer
  | letCond (pat : Pat) (expr : Expr)
  | lit (lit : Lit)
  | loop (label : Option Ident) (body : Block)
  | macro (mac : Macro)
  | matchExpr (expr : Expr) (arms : List Arm)
  | methodCall (receiver : Expr) (method : Ident) (turbofish : Option (List GenericArgument))
      (args : List Expr)
  | paren (expr : Expr)
  | path (qself : Option QSelf) (path : Path)
  | range (start : Option Expr) (limits : RangeLimits) (stop : Option Expr)
  | rawAddr (mutable : Bool) (expr : Expr)
  | reference (mutable : Bool) (expr : Expr)
  | repeatExpr (expr : Expr) (len : Expr)
  | returnExpr (expr : Option Expr)
  | struct (qself : Option QSelf) (path : Path) (fields : List FieldValue) (dot2 : Bool)
      (rest : Option Expr)
  | tryExpr (expr : Expr)
  | tryBlock (block : Block)
  | tuple (elems : List Expr)
  | unary (op : UnOp) (expr : Expr)
  | unsafeBlock (block : Block)
  | whileLoop (label : Option Ident) (cond : Expr) (body : Block)
  | yieldExpr (expr : Option Expr)
  | awaitExpr (base : Expr)
  | asyncBlock (isMove : Bool) (block : Block)
  | verbatim (src : String)
/-- A `match` arm (`syn::Arm`). -/
inductive Arm : Type where
  | mk (attrs : List Attr) (pat : Pat) (guard : Option Expr) (body : Expr)
/-- A struct-literal field (`syn::FieldValue`); `shorthand` is `S { x }`. -/
inductive FieldValue : Type where
  | mk (attrs : List Attr) (member : Member) (shorthand : Bool) (expr : Expr)
/-- Patterns (`syn::Pat`). -/
inductive Pat : Type where
  | withAttrs (attrs : List Attr) (pat : Pat)
  | constBlock (block : Block)
  | ident (byRef : Bool) (mutable : Bool) (ident : Ident) (subpat : Option Pat)
  | lit (expr : Expr)
  | macro (mac : Macro)
  | or (cases : List Pat)
  | paren (pat : Pat)
  | path (qself : Option QSelf) (path : Path)
  | range (start : Option Expr) (limits : RangeLimits) (stop : Option Expr)
  | reference (mutable : Bool) (pat : Pat)
  | rest
  | slice (elems : List Pat)
  | struct (qself : Option QSelf) (path : Path) (fields : List FieldPat) (rest : Bool)
  | tuple (elems : List Pat)
  | tupleStruct (qself : Option QSelf) (path : Path) (elems : List Pat)
  | typed (pat : Pat) (ty : Ty)
  | wild
  | verbatim (src : String)
/-- A struct-pattern field (`syn::FieldPat`). -/
inductive FieldPat : Type where
  | mk (attrs : List Attr) (member : Member) (shorthand : Bool) (pat : Pat)
/-- Statements (`syn::Stmt`); `letStmt` carries the `let ... else` branch. -/
inductive Stmt : Type where
  | letStmt (attrs : List Attr) (pat : Pat) (init : Option Expr) (diverge : Option Expr)
  | item (item : Item)
  | expr (expr : Expr) (semi : Bool)
  | macro (attrs : List Attr) (mac : Macro) (semi : Bool)
/-- A block (`syn::Block`). -/
inductive Block : Type where
  | mk (stmts : List Stmt)
/-- A macro invocation (`syn::Macro`). -/
inductive Macro : Type where
  | mk (path : Path) (delimiter : MacroDelimiter) (body : MacroBody)
/-- Macro arguments: decomposed when they are an expression list
(`panic!`, `throw_ub!`, `list![a, b]`), a repetition (`list![x; n]`), or
`matches!(e, pat)`; otherwise kept as `tokens` (opaque). -/
inductive MacroBody : Type where
  | exprs (args : List Expr) (trailingComma : Bool)
  | repeatList (elem : Expr) (len : Expr)
  | exprAndPat (expr : Expr) (pat : Pat) (guard : Option Expr)
  | tokens (src : String)
/-- `syn::GenericParam`. -/
inductive GenericParam : Type where
  | lifetime (attrs : List Attr) (name : Ident) (bounds : List Ident)
  | type (attrs : List Attr) (ident : Ident) (bounds : List TypeParamBound) (default : Option Ty)
  | const (attrs : List Attr) (ident : Ident) (ty : Ty) (default : Option Expr)
/-- `syn::WherePredicate`. -/
inductive WherePredicate : Type where
  | lifetime (name : Ident) (bounds : List Ident)
  | type (lifetimes : List Ident) (boundedTy : Ty) (bounds : List TypeParamBound)
/-- `syn::Generics`. -/
inductive Generics : Type where
  | mk (params : List GenericParam) (wherePredicates : List WherePredicate)
/-- `syn::FnArg`: a `self` receiver or a typed pattern argument. -/
inductive FnArg : Type where
  | receiver (attrs : List Attr) (reference : Bool) (lifetime : Option Ident) (mutable : Bool)
      (colonTy : Option Ty)
  | typed (attrs : List Attr) (pat : Pat) (ty : Ty)
/-- `syn::Signature`. -/
inductive Signature : Type where
  | mk (constness : Bool) (asyncness : Bool) (unsafety : Bool) (abi : Option String)
      (ident : Ident) (generics : Generics) (inputs : List FnArg) (variadic : Bool)
      (output : Option Ty)
/-- `syn::Field`. -/
inductive Field : Type where
  | mk (attrs : List Attr) (vis : Visibility) (ident : Option Ident) (ty : Ty)
/-- `syn::Fields`. -/
inductive Fields : Type where
  | named (fields : List Field)
  | unnamed (fields : List Field)
  | unit
/-- An enum variant (`syn::Variant`). -/
inductive Variant : Type where
  | mk (attrs : List Attr) (ident : Ident) (fields : Fields) (discriminant : Option Expr)
/-- `syn::ImplItem`. -/
inductive ImplItem : Type where
  | const (attrs : List Attr) (vis : Visibility) (defaultness : Bool) (ident : Ident)
      (generics : Generics) (ty : Ty) (expr : Expr)
  | fn (attrs : List Attr) (vis : Visibility) (defaultness : Bool) (sig : Signature) (block : Block)
  | type (attrs : List Attr) (vis : Visibility) (defaultness : Bool) (ident : Ident)
      (generics : Generics) (ty : Ty)
  | macro (attrs : List Attr) (mac : Macro)
  | verbatim (src : String)
/-- `syn::TraitItem`. -/
inductive TraitItem : Type where
  | const (attrs : List Attr) (ident : Ident) (generics : Generics) (ty : Ty) (default : Option Expr)
  | fn (attrs : List Attr) (sig : Signature) (default : Option Block)
  | type (attrs : List Attr) (ident : Ident) (generics : Generics) (bounds : List TypeParamBound)
      (default : Option Ty)
  | macro (attrs : List Attr) (mac : Macro)
  | verbatim (src : String)
/-- Top-level items (`syn::Item`). -/
inductive Item : Type where
  | const (attrs : List Attr) (vis : Visibility) (ident : Ident) (generics : Generics) (ty : Ty)
      (expr : Expr)
  | enum (attrs : List Attr) (vis : Visibility) (ident : Ident) (generics : Generics)
      (variants : List Variant)
  | fn (attrs : List Attr) (vis : Visibility) (sig : Signature) (block : Block)
  | impl (attrs : List Attr) (defaultness : Bool) (unsafety : Bool) (generics : Generics)
      (traitNeg : Bool) (traitPath : Option Path) (selfTy : Ty) (items : List ImplItem)
  | macro (attrs : List Attr) (ident : Option Ident) (mac : Macro)
  | struct (attrs : List Attr) (vis : Visibility) (ident : Ident) (generics : Generics)
      (fields : Fields)
  | trait (attrs : List Attr) (vis : Visibility) (unsafety : Bool) (auto : Bool) (ident : Ident)
      (generics : Generics) (supertraits : List TypeParamBound) (items : List TraitItem)
  | type (attrs : List Attr) (vis : Visibility) (ident : Ident) (generics : Generics) (ty : Ty)
  | use (attrs : List Attr) (vis : Visibility) (leadingColon : Bool) (tree : UseTree)
  | static (attrs : List Attr) (vis : Visibility) (mutable : Bool) (ident : Ident) (ty : Ty)
      (expr : Expr)
  | mod (attrs : List Attr) (vis : Visibility) (ident : Ident) (content : Option (List Item))
  | union (attrs : List Attr) (vis : Visibility) (ident : Ident) (generics : Generics)
      (fields : Fields)
  | verbatim (src : String)
end

/-- A generated item with its provenance: the stable per-file name, the line
in the upstream Markdown file, and the SHA-256 of the item's token stream
(insensitive to whitespace and `//` comments). -/
structure SourceItem : Type where
  name : String
  line : Nat
  tokenSha256 : String
  item : Item

end MiniRustSpec.Syntax
