-- V-F4 Fixture: compiled `.olean` containing `_kernel_fresh` declaration and
-- binder identifiers (accepted by current `OleanEnvAuditor.lean`, rejected with
-- `kernelFreshCollision` by the prototype validator).
prelude
import Init.Core

def _kernel_fresh : Nat := 0
def nested._kernel_fresh_decl (x : Nat) : Nat := x
def usesKernelFreshBinder (_kernel_fresh : Nat) : Nat := _kernel_fresh
