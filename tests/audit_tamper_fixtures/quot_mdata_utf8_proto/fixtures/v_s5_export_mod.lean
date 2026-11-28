-- V-S5 Fixture (module): public and private `@[export]` functions in a
-- module-system file, demonstrating `.olean` / `.olean.private` vs `.ir` storage.
module
prelude
public import Init.Core

@[export proto_s5_mod_pub_sym]
public def s5ModPubExported (n : Nat) : Nat := n

@[export proto_s5_mod_priv_sym]
def s5ModPrivExported (n : Nat) : Nat := n
