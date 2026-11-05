import MiniRustSpec.Interp

open MiniRustSpec.Interp

mutual

partial def decodeDisc {m' : Type → Type} [Monad m'] [MonadLift Interp m']
    (accessor : Offset → LibSpecr.Size → m' (List Byte)) : Discriminator → m' (Option Int)
  | .Known val => pure (some val)
  | _ => pure none

def decodeEnum : List Byte → Interp (Option Val) := fun bytes => do
  let accessor (offset : Offset) (sz : LibSpecr.Size) : Interp (List Byte) := pure []
  let x ← decodeDisc accessor .Invalid
  pure none

end
