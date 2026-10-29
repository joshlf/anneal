namespace Trusted.Sequence

/-!
0-based dense-index helpers (`get?`, `set?`, `length`) used by captured MIR
AST tables (`Local`, `BasicBlockIdx`, `FieldIdx`, `VariantIdx`, `LayoutIdx`,
`AllocId`), backed directly by Lean's standard `List` operations (`xs[idx]?`,
`List.set`, `List.length`).

Reference (`compiler/rustc_index/src/slice.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_index/src/slice.rs#L17-L23>

> "A view into contiguous `I`-indexed values (e.g. `&[T]` for `I = usize`)."

Reference (`compiler/rustc_index/src/slice.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_index/src/slice.rs#L103-L106>

> "pub fn get(&self, index: I) -> Option<&T> {
>     self.raw.get(index.index())
> }"
-/

/-- Look up the element at 0-based `idx`, returning `none` if out of bounds. -/
@[inline]
def get? {α : Type u} (xs : List α) (idx : Nat) : Option α :=
  xs[idx]?

/--
Functional point update at 0-based `idx`, returning `none` if `idx` is out of
bounds.
-/
@[inline]
def set? {α : Type u} (xs : List α) (idx : Nat) (val : α) : Option (List α) :=
  if idx < xs.length then some (xs.set idx val) else none

/-- Length of `xs` (`List.length`). -/
@[inline]
def length {α : Type u} (xs : List α) : Nat :=
  xs.length

end Trusted.Sequence
