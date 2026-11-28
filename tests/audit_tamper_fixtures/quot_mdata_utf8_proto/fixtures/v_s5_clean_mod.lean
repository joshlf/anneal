-- V-S5 Fixture (clean module): honest module-system file whose `.ir` companion
-- is subsequently injected with a forged `Lean.exportAttr` entry to test
-- `OleanEnvAuditor.lean:1649`'s `getModuleEntries`-only blind spot.
module
prelude
public import Init.Core

public def s5CleanFn (n : Nat) : Nat := n
