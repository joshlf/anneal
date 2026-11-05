with open("theory/Anneal/Rustc/V2026_06_01/SymbolicEval.lean", "r") as f:
    content = f.read()

content = content.replace(
    'theorem ActiveCalleeCtx.initMem {body args mem callees} :\n  ActiveCalleeCtx (initMachineStateWithMemoryAndCallees body args mem callees) body body := by unfold ActiveCalleeCtx; cases callees <;> rfl',
    'theorem ActiveCalleeCtx.initMem {body args mem callees} :\n  ActiveCalleeCtx (initMachineStateWithMemoryAndCallees body args mem callees) body (mem.activeCallee.getD body) := by unfold ActiveCalleeCtx; cases callees <;> rfl'
)

# And replace verifyPolyUbExceptionMirSym to use mem.activeCallee.getD body in the signature
content = content.replace(
    'ActiveCalleeCtx s (ubExceptionClaimFor typeArgs).body (ubExceptionClaimFor typeArgs).body',
    'ActiveCalleeCtx s (ubExceptionClaimFor typeArgs).body (mem.activeCallee.getD (ubExceptionClaimFor typeArgs).body)'
)

# Also check if there are other verifyPoly* theorems that use ActiveCalleeCtx.initMem and have `body body`.
import re
content = re.sub(
    r'ActiveCalleeCtx s \(([^)]+)\)\.body \(\1\.body\)',
    r'ActiveCalleeCtx s (\1).body (mem.activeCallee.getD (\1).body)',
    content
)

with open("theory/Anneal/Rustc/V2026_06_01/SymbolicEval.lean", "w") as f:
    f.write(content)
