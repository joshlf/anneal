-- V-S5 Fixture (non-module): safe, non-@[extern] Lean function with
-- `@[export]` C-symbol binding into `ir_interpreter::lookup_symbol`.
prelude
import Init.Core

@[export proto_s5_nonmod_sym]
def s5NonModExported (n : Nat) : Nat := n
