import re

with open("theory/Anneal/Rustc/V2026_06_01/SymbolicEval.lean", "r") as f:
    content = f.read()

# Fix duplicate docstring
content = content.replace(
"""/--
`O(1)` basic-block lookup context hypothesis (`BlockCtx body idx bb`): records
that basic block `idx` in `body.basicBlocks` is `bb`, avoiding repeated linear
list traversal of `body.basicBlocks` during symbolic execution.
-/
/--
`O(1)` basic-block lookup context hypothesis (`BlockCtx body idx bb`): records
that basic block `idx` in `body.basicBlocks` is `bb`, avoiding repeated linear
list traversal of `body.basicBlocks` during symbolic execution.
-/
def BlockCtx""",
"""/--
`O(1)` basic-block lookup context hypothesis (`BlockCtx body idx bb`): records
that basic block `idx` in `body.basicBlocks` is `bb`, avoiding repeated linear
list traversal of `body.basicBlocks` during symbolic execution.
-/
def BlockCtx""")

# Fix all ActiveCalleeCtx signatures in verifyPoly*Sym theorems.
# We are looking for: ActiveCalleeCtx s (X).body (X).body
# We want to replace it with: ActiveCalleeCtx s (X).body (mem.activeCallee.getD (X).body)

def replacer(match):
    x = match.group(1)
    return f"ActiveCalleeCtx s ({x}).body (mem.activeCallee.getD ({x}).body)"

content = re.sub(r'ActiveCalleeCtx s \(([^)]+)\)\.body \(\1\)\.body', replacer, content)

with open("theory/Anneal/Rustc/V2026_06_01/SymbolicEval.lean", "w") as f:
    f.write(content)
