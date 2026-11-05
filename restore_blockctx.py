with open("theory/Anneal/Rustc/V2026_06_01/SymbolicEval.lean", "r") as f:
    content = f.read()

content = content.replace(
    'def BlockCtx (body : CapturedMir) (idx : BasicBlockIdx) (bb : BasicBlockData) : Prop :=',
    '/--\n`O(1)` basic-block lookup context hypothesis (`BlockCtx body idx bb`): records\nthat basic block `idx` in `body.basicBlocks` is `bb`, avoiding repeated linear\nlist traversal of `body.basicBlocks` during symbolic execution.\n-/\ndef BlockCtx (body : CapturedMir) (idx : BasicBlockIdx) (bb : BasicBlockData) : Prop :='
)

with open("theory/Anneal/Rustc/V2026_06_01/SymbolicEval.lean", "w") as f:
    f.write(content)
