import re

with open("theory/Anneal/Rustc/V2026_06_01/SymbolicEval.lean", "r") as f:
    content = f.read()

content = content.replace(
"""/-! ## 15. `O(1)` Block & Callee Lookup Context Lemmas, Indirect `FnPtr` & Diverging Call Stepping, and Polymorphic Claim Combinators -/

/--
`O(1)` basic-block lookup context hypothesis (`BlockCtx body idx bb`): records
that basic block `idx` in `body.basicBlocks` is `bb`, avoiding repeated linear
list traversal of `body.basicBlocks` during symbolic execution.
-/

/--
`O(1)` active callee normalization hypothesis (`ActiveCalleeCtx s body instBody`):
records that `s.memory.activeCallee.getD body = instBody`, avoiding repeated
evaluation and WHNF unrolling of `.getD` and `CapturedMir.instantiate` across steps.
-/
def ActiveCalleeCtx""",
"""/-! ## 15. `O(1)` Block & Callee Lookup Context Lemmas, Indirect `FnPtr` & Diverging Call Stepping, and Polymorphic Claim Combinators -/

/--
`O(1)` active callee normalization hypothesis (`ActiveCalleeCtx s body instBody`):
records that `s.memory.activeCallee.getD body = instBody`, avoiding repeated
evaluation and WHNF unrolling of `.getD` and `CapturedMir.instantiate` across steps.
-/
def ActiveCalleeCtx"""
)

# Unfold ActiveCalleeCtx
content = content.replace(
    'theorem ActiveCalleeCtx.init {body args callees} :\n  ActiveCalleeCtx (initMachineStateWithCallees body args callees) body body := by cases callees <;> rfl',
    'theorem ActiveCalleeCtx.init {body args callees} :\n  ActiveCalleeCtx (initMachineStateWithCallees body args callees) body body := by unfold ActiveCalleeCtx; cases callees <;> rfl'
)

content = content.replace(
    'theorem ActiveCalleeCtx.initMem {body args mem callees} :\n  ActiveCalleeCtx (initMachineStateWithMemoryAndCallees body args mem callees) body body := by cases callees <;> rfl',
    'theorem ActiveCalleeCtx.initMem {body args mem callees} :\n  ActiveCalleeCtx (initMachineStateWithMemoryAndCallees body args mem callees) body body := by unfold ActiveCalleeCtx; cases callees <;> rfl'
)

with open("theory/Anneal/Rustc/V2026_06_01/SymbolicEval.lean", "w") as f:
    f.write(content)
