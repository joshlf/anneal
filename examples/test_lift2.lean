import MiniRustSpec.Interp

open MiniRustSpec.Interp

mutual

def decodeDisc {m' : Type → Type} [Monad m'] [MonadLiftT Interp m']
    (accessor : Offset → Size → m' (List Byte)) : Discriminator → m' (Option Int)
  | .Known val => pure (some val)
  | .Invalid => pure none
  | .Branch offset value_type fallback children => do
    let bytes ← accessor offset value_type.size
    let decoded ← liftM (Type.decode (.Int value_type) bytes)
    match decoded with
    | some (.Int val) =>
      let rec loop (entries : List ((Int × Int) × Discriminator)) : m' (Option Int) := do
        match entries with
        | [] => decodeDisc accessor fallback
        | ((start, end_), child) :: rest =>
          if start ≤ val ∧ val < end_ then
            decodeDisc accessor child
          else
            loop rest
      loop children.entries
    | _ => pure none

def decodeEnum : List Byte → Interp (Option Val) := fun bytes => do
  let accessor (offset : Offset) (sz : Size) : Interp (List Byte) := pure []
  let x ← decodeDisc accessor .Invalid
  pure none

end
