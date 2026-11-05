import re

with open("theory/Anneal/Rustc/V2026_06_01/SymbolicEval.lean", "r") as f:
    content = f.read()

content = content.replace(
    'ActiveCalleeCtx s (claimFor typeArgs).body (mem.activeCallee.getD (claimFor typeArgs).body)',
    'ActiveCalleeCtx s (claimFor typeArgs).body (claimFor typeArgs).body'
)

with open("theory/Anneal/Rustc/V2026_06_01/SymbolicEval.lean", "w") as f:
    f.write(content)
