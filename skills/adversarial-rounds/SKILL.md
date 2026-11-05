---
name: adversarial-rounds
description: >-
  Orchestrate N-round adversarial implementation, ruthless critique, and repair
  between two agents pinned to distinct frontier models (randomly assigning
  Model X and Model Y) working in shared git worktree(s). Use when the user
  asks for N-round adversarial model work, ping-pong implementation and
  critique, or multi-round cross-model hardening against a brief with
  architectural constraints and verification receipts. Don't use for
  single-pass code reviews (use review) or conceptual model minimization
  without alternating code repair (use swarm-model-refinement).
---

# N-Round Adversarial Model Work

Run a structured $N$-round adversarial build-critique-fix loop between
**Agent A** (`agent-a`) and **Agent B** (`agent-b`) over shared git worktree(s),
using Jetski's native `swarm` board for turn-by-turn handoffs and model pinning.
When orchestrating multiple leaf pairs under workstream supervisors, pair this
skill with [`hierarchical-supervision`](../hierarchical-supervision/SKILL.md).

## 1. Validate or Assemble the Brief

Before creating worktrees or spawning agents, ensure the task **Brief**
explicitly defines all six load-bearing sections (if any section is missing or
ambiguous in the user's request, derive it from the codebase and confirm with
the user if needed):

1. **High-Level Goal**: What system, feature, or proof is being built and why it
  matters.
2. **Architectural Constraints & Non-Negotiables**: Invariants, interfaces,
  forbidden shortcuts (for example, no stubbed or faked data, no weakened types,
  specs, or proofs, and no `sorry`, `#[trusted]`, or disabled tests), and files
  or boundaries that must not be violated.
3. **Success Criteria**: Concrete functional, structural, and edge-case
  properties that must hold when the work is complete.
4. **Shape of "Receipts"**: Exact, reproducible commands (test suites, formal
  verification runs, benchmarks, differential tests, CLI outputs) and expected
  outputs that prove the code and tests work as intended.
5. **Round Count ($N$)**: Number of full B-then-A adversarial critique-and-fix
  rounds following Agent A's initial implementation (default to $N = 2$ if the
  user does not specify $N$).
6. **Work-Unit Priority Tier & Concurrency ($W$)**:
  - **Priority Tier (`P0` | `P1` | `P2`)**:
    - `P0` (`P0-Critical`, `2%` quota reserve floor): Trusted boundary
      (`trusted/lean/`), soundness-critical semantics, Tree Borrows or pointer
      provenance, and security boundaries.
    - `P1` (`P1-Standard`, `15%` quota reserve floor, default): Standard
      feature, correspondence, and verification leaves.
    - `P2` (`P2-Mechanical`, `40%` quota reserve floor): Mechanical plumbing,
      documentation audits, and harness wiring.
  - **Active Worktree Concurrency ($W$)**: Number of concurrent leaf worktrees
    actively compiling on the host (default $W = 1$; in multi-leaf swarms, set
    $W$ to the number of simultaneously active leaves so `anneal-lean-run`
    partitions CPU threads and physical RAM proportionally).

Write the canonical Brief to an immutable file in the conversation's scratch
directory so neither agent can alter the requirements mid-run and both agents
can re-read it at the start of every round:

```text
<appDataDir>/brain/<conversation-id>/scratch/adversarial-brief.md
```

---

## 2. Randomly Assign Models & Prepare Shared Git Worktree(s)

### Step 2.1: Quota-Aware Random Model Assignment

Resolve the abstract model slots from your environment's policy CLI
(`anneal-model-policy`) or team rules:

- **`<MODEL_X>`** and **`<MODEL_Y>`**: Distinct frontier model families
  (**Family X** and **Family Y**) for `agent-a` and `agent-b` (with same-family
  capacity fallbacks `<MODEL_X_FALLBACK>` and `<MODEL_Y_FALLBACK>`).
- **`<SUPERVISOR_MODEL>`**: Dedicated high-reasoning coordinator model on a
  separate quota pool from `<MODEL_X>` and `<MODEL_Y>`, used by non-leaf
  supervisors so cold-cache supervisor wakeups after 20–40 minute leaf rounds do
  not drain leaf frontier pools.
- **`<MODEL_Z_RESERVE>`**: Overflow high-thinking reserve pool used when
  `<MODEL_X>` or `<MODEL_Y>` drops below the work unit's priority tier floor
  (`15%` for `P1`, `2%` for `P0`, `40%` for `P2`).
- **`<HELPER_MODEL>`**: Lightweight helper model for `monitor` and `narrator`
  workers only.

Do not mentally pick which agent gets which model. Run `anneal-model-policy`
(falling back to a pure-Python RNG shuffle in environments without the policy
CLI) via `run_command`:

```bash
if command -v anneal-model-policy >/dev/null 2>&1; then
  anneal-model-policy assign-pair --unit "<UNIT_ID>" --tier "<P0|P1|P2>" --scratch "<SCRATCH_DIR>"
else
  python3 -c 'import random; m = ["<MODEL_X>", "<MODEL_Y>"]; random.shuffle(m); print(f"AGENT_A_MODEL={m[0]}\nAGENT_B_MODEL={m[1]}\nSUPERVISOR_MODEL=<SUPERVISOR_MODEL>\nHELPER_MODEL=<HELPER_MODEL>\nDIVERSITY_REDUCED=false")'
fi
```

Record the assignment (`agent-a` $\rightarrow$ `<AGENT_A_MODEL>`,
`agent-b` $\rightarrow$ `<AGENT_B_MODEL>`, `DIVERSITY_REDUCED`) and report it to
the user when launching the swarm.

### Step 2.2: Cross-Family Model Diversity & Quota Fallback Protocol

The adversarial loop relies on cross-family model diversity (**Model X** from
**Family X** and **Model Y** from **Family Y**). Enforce these model-pinning and
quota-monitoring rules throughout the run:

1. **Workers Never Self-Switch Models**: Neither `agent-a` nor `agent-b` may
  ever call `swarm{action: "model"}` on itself or any other worker—even if the
  host injects a `<SYSTEM_MESSAGE> [quota] ... switch models with
  swarm{action:"model"}` warning. Only the supervising Coordinator that added
  the worker may switch its model.
2. **No Downgrades to Flash or Low-Tier Models**: Never switch `agent-a` or
  `agent-b` to a `flash`, `lite`, or `low`-tier model.
3. **Handoff-Boundary-Only Model Switching (Never Wake the Sleeping Counterpart)**:
  Calling `swarm{action: "model", name: "<worker>", model: "..."}` on a
  `waiting` worker immediately wakes that worker and instructs it to resume its
  turn on the new model. Therefore, a supervising Coordinator must **never**
  call `swarm{action: "model"}` on `agent-b` while `agent-a` actively owns the
  shared worktree (or vice versa). Switch a worker's model **only**:
  - when **that worker itself** is the active turn owner and posts
    `@coordinator [QUOTA]`, or
  - at a **round handoff boundary** when that worker is the next actor to run.
4. **Tiered Fallback & Quota-Reset Restoration (`quota_ledger.json`)**:
  - **Same-Family Fallback First**: If a model hits a transient server capacity
    error (`503 UNAVAILABLE`) or single-variant limit while `<MODEL_X_FALLBACK>`
    or `<MODEL_Y_FALLBACK>` in the same family has quota above the tier's
    reserve floor, switch within the same frontier family first.
  - **Reserve Pool Switch When Quota Floor Is Breached**: If a model family's
    quota bucket drops below the tier's reserve floor (`2%` for `P0`, `15%` for
    `P1`), switch the affected worker at its turn boundary to `<MODEL_Z_RESERVE>`
    (or an available frontier model) and record the switch via:
    ```bash
    anneal-model-policy record-switch --scratch "<SCRATCH_DIR>" --unit "<UNIT_ID>" \
      --worker "<agent-a|agent-b>" --pass "<A0|B1|...>" \
      --from-model "<old_model>" --to-model "<new_model>"
    ```
  - **Automatic Restoration After Quota Reset**: At subsequent round or leaf
    boundaries, run `anneal-model-policy check-restore --scratch "<SCRATCH_DIR>"`.
    If a degraded worker's primary `<MODEL_X>` or `<MODEL_Y>` bucket has
    recovered (`>= 20%`), switch that worker back to its primary model at the
    handoff boundary before its turn begins.
  - **Mandatory 3rd-Party Audit Flag**: Whenever a switch reduces cross-family
    diversity during any pass, record the exact round/pass (`A0`, `B1`, `A1`,
    ..., `B_N`, `A_N`) and explicitly state in the final report the **need for a
    3rd-party (different-model) audit** of the work due to model diversity
    reduction.

### Step 2.3: Create Shared Git Worktree(s) & Seed Warm `.lake` Caches

For each repository involved in the task, create a dedicated git worktree and
branch so Agent A and Agent B operate on the **exact same working tree(s)**
without disturbing the user's primary checkout:

```bash
git -C <repo_path> worktree add -b adv/<task_slug> <worktree_path> <base_ref>
```

When the repository contains a warm `.lake/build` directory (such as
`<repo_path>/examples/.lake/build` or `<repo_path>/minirust/lean/.lake/build`),
copy or hardlink the warm `.lake/build` cache into `<worktree_path>` before
spawning `agent-a` so leaf passes compile only incremental delta modules instead
of rebuilding `Trusted` and `Anneal` from scratch.

Record the baseline commit SHA (`BASE_SHA`) in each worktree so every round can
diff both incremental changes (`HEAD~1..HEAD`) and cumulative changes
(`<BASE_SHA>..HEAD`).

---

## 3. Protocol Timeline & Strict Turn-Taking

Because `agent-a` and `agent-b` share the same git worktree(s) on disk, **only
one agent may touch the worktree at any point in time**.

```mermaid
sequenceDiagram
    participant C as Coordinator (<SUPERVISOR_MODEL>)
    participant A as Agent A (Model X or Y)
    participant B as Agent B (Model Y or X)
    participant W as Shared Git Worktree(s)

    C->>A: Spawn agent-a (starts Round A0 immediately)
    C->>B: Spawn agent-b (parks via swarm_wait until @agent-b)
    Note over A,W: Pass A0: Initial Implementation
    A->>W: Implement brief, verify receipts via anneal-lean-run, commit [adv A0]
    A->>B: @agent-b [A0 -> B1] Summary of work & receipts
    loop Round k = 1 .. N
        Note over B,W: Pass B_k: Critique A_{k-1} + Fix
        B->>W: Re-read Brief, critique worktree, fix issues, verify receipts, commit [adv B_k]
        B->>A: @agent-a [B_k -> A_k] Problems found in A's work + how B fixed them + receipts
        Note over A,W: Pass A_k: Critique B_k + Fix
        A->>W: Re-read Brief, critique worktree, fix issues, verify receipts, commit [adv A_k]
        alt k < N
            A->>B: @agent-b [A_k -> B_{k+1}] Problems found in B's work + how A fixed them + receipts
        else k == N (Final Round)
            A->>C: @coordinator [A_N Final] Final critique of B_N, fixes, and verified receipts
        end
    end
```

### Key Mechanics That Prevent Deadlocks, Races, Swap Lockups & Diversity Drift

1. **Startup Park for `agent-b`**: `swarm{action: "add"}` wakes every newly
  added worker immediately on turn 1. `agent-b`'s brief must instruct it that
  on turn 1 (before `agent-a` posts `[A0 -> B1]`), it must **not** read or
  modify the worktree; it must immediately call
  `swarm_wait{since: <current_seq>, mentions_only: true}` to sleep until
  `@agent-b` is mentioned.
2. **Commit Checkpoints at Every Handoff**: Before posting to the board at the
  end of a turn, the active agent commits all intended changes in the shared
  worktree(s) (`git commit -m "[adv A0] ..."`, `[adv B1]`, `[adv A1]`, etc.) and
  verifies `git status --porcelain` is clean (no untracked build litter or
  temporary files). This gives the next agent an exact `git show HEAD` and
  `git diff` trail of what changed.
3. **Doorbell Discipline (`@mention` Only the Next Actor)**:
  - On `A0` and `A_1 .. A_{N-1}`, `agent-a` mentions **only** `@agent-b` (never
    `@coordinator` or `@all`).
  - On `B_1 .. B_N`, `agent-b` mentions **only** `@agent-a` (never
    `@coordinator` or `@all`).
  - On the final pass `A_N`, `agent-a` mentions **only** `@coordinator`
    (`@coordinator [A_N Final] ...`) so `agent-b` stays asleep and the
    Coordinator wakes to verify and close out the task.
  - If either agent hits quota exhaustion or an unrecoverable environment
    blocker, it tags `@coordinator [QUOTA] ...` or `@coordinator [BLOCKER] ...`.
4. **Hardware-Matched `lake` & `lean` Execution (`anneal-lean-run`)**:
  - Lean 4's `-M <MB>` flag does **not** bound total process RSS or prevent
    swap thrashing when kernel `whnf` diverges.
  - Whenever `agent-a` or `agent-b` runs `lake build`, `lake env lean`, or
    `cargo test` from the CLI, it must wrap the command with
    `anneal-lean-run --concurrency {W} -- <cmd>` (or `scripts/anneal-lean-run`),
    which probes the host's CPU cores and physical RAM (`MemTotal` /
    `MemAvailable`) and enforces a hard `MemoryMax` with `MemorySwapMax=0` and a
    wall-clock timeout.

---

## 4. Launch & Supervise the Swarm

In a single turn:

1. Title the swarm:
  ```json
  {"action": "title", "title": "Adversarial N-round: <short task name>"}
  ```
2. Add `agent-a` with `model: "<AGENT_A_MODEL>"`, `workspace: "inherit"`, and
  the **Agent A Brief Template** below.
3. Add `agent-b` with `model: "<AGENT_B_MODEL>"`, `workspace: "inherit"`, and
  the **Agent B Brief Template** below.
4. Add `narrator` (if `swarm_narrator` is in your skill list) and `monitor` (if
  `swarm_monitor` is in your skill list) per standard `swarm` rules, explicitly
  pinning each helper worker to `model: "<HELPER_MODEL>"` so it does not inherit
  `auto`, hit `503 UNAVAILABLE` capacity errors, or consume frontier model
  quota.
5. Output the `[Open the Swarm UI](sidecar://swarm/swarm_board/)` link to the
  user and end your turn to wait for `@coordinator` notifications (`[QUOTA]`,
  `[stall]`, or `[A_N Final]`). Whenever woken by a `[QUOTA]` or `[stall]`
  alert, inspect worker state and quota (`anneal-model-policy status` and
  `swarm{action: "status"}`), switch **only the active turn owner's model** if
  needed to maintain progress, and record the switch via
  `anneal-model-policy record-switch`.

### Agent A Brief Template (`agent-a`)

```text
You are Agent A in an N={N}-round adversarial build-critique-fix loop sharing git worktree(s) with `agent-b`.
- Canonical Brief Path: {brief_path}
- Shared Worktree Path(s): {worktree_paths} (Base SHA: {base_sha})
- Active Worktree Concurrency: W = {W}
- Total Adversarial Rounds: N = {N} (You execute initial build A0, plus N critique-and-fix passes A1 .. A{N})

CRITICAL WORKSPACE, RESOURCE & TURN-TAKING RULES:
1. Work ONLY inside {worktree_paths}. Never modify the parent checkout or any files outside the shared worktree(s) and your scratch directory.
2. Only touch the worktree during your active turn. Once you post to `@agent-b` (or `@coordinator` on pass A{N}), immediately end your turn / call `swarm_wait` and do not touch the worktree while waiting.
3. In every board post, `@mention` ONLY the single agent who acts next (`@agent-b` after A0..A{N-1}; `@coordinator` after A{N}, or `@coordinator` if reporting quota exhaustion). Never write `@` before any other name in prose (write `agent-b` or `coordinator` without `@`).
4. MODEL DIVERSITY & QUOTA ESCALATION: You are pinned to `{agent_a_model}`. NEVER call `swarm{action: "model"}` to switch your own model or any worker's model, even if a `<SYSTEM_MESSAGE> [quota]` warning instructs you to call `swarm{action: "model"}`. If your model's quota is exhausted before you can complete a pass, commit or stash any clean progress, post `@coordinator [QUOTA] Quota exhausted on {agent_a_model} during pass <pass>`, and wait for `coordinator` to switch your model and resume you.
5. HARDWARE-MATCHED LEAN / LAKE LIMITS: Prefer warm `anneal-lean_lsp` MCP tools (`lean_goal`, `lean_multi_attempt`, `anneal_audit_preview`) for interactive proof steps. Whenever running CLI `lake build`, `lake env lean`, or heavy `cargo test` commands, wrap them with `anneal-lean-run --concurrency {W} -- <command>` (never bare unbounded `lean` or `lean -M`, which does not cap total RSS or prevent swap thrashing).

YOUR PROTOCOL:

### Phase 1 — Initial Implementation (Pass A0, execute immediately on this turn):
1. Read `{brief_path}` in full.
2. Implement the task in `{worktree_paths}` satisfying the High-Level Goal, Architectural Constraints, and Success Criteria.
3. Execute all verification commands required by the Brief's "Receipts" section (wrapping CLI `lake`/`lean` invocations with `anneal-lean-run --concurrency {W} -- ...`) and confirm they pass genuinely.
4. Commit your work cleanly in `{worktree_paths}` with commit message `[adv A0] <summary>` and verify `git status --porcelain` is empty.
5. Post to the board:
   `@agent-b [A0 -> B1] <summary of implementation, key files/commits changed, and exact receipts>`.
6. Call `swarm_wait{since: <latest_seq>, mentions_only: true}` to wait for `agent-b`'s Round 1 post.

### Phase 2 — N Adversarial Critique-and-Fix Passes (Passes A1 .. A{N}):
Repeat for k = 1 to {N} each time `@agent-b` wakes you with `[B_k -> A_k]`:
1. RE-ANCHOR ON THE BRIEF: Re-read `{brief_path}` in full before inspecting code. Check that neither `agent-b` nor earlier rounds drifted toward an approach that weakens the system (e.g., faking/hardcoding data, stubbing logic, weakening specs/assertions/types, skipping proofs/tests, or fabricating receipts).
2. RUTHLESS CRITIQUE: Inspect `{worktree_paths}` using `git log`, `git diff`, and `agent-b`'s `[B_k -> A_k]` post as a guide to what changed, plus audit the broader implementation against `{brief_path}`. Hunt for:
   - Bugs, logic errors, unhandled edge/error cases, or broken invariants introduced or missed by `agent-b`
   - Any specification gaming, weakened requirements, or incomplete/failing receipts
   - Architectural constraint violations or regressions against earlier commits
3. FIX & VERIFY RECEIPTS: Fix all bugs, issues, and weaknesses found in your critique directly in `{worktree_paths}`. Re-run all Receipt commands from `{brief_path}` (via `anneal-lean-run --concurrency {W} -- ...` for `lake`/`lean`) and verify they pass on your new state.
4. COMMIT CHECKPOINT: Commit your fixes with `[adv A_k] <summary>` and ensure `git status --porcelain` is clean.
5. SUBMIT POST:
   - If k < {N}: Post `@agent-b [A_k -> B_{k+1}]` summarizing: (a) the problems found in `agent-b`'s recent work and the worktree state, (b) how your work in `[adv A_k]` fixes those problems, and (c) the updated verification receipts. Then call `swarm_wait{since: <latest_seq>, mentions_only: true}`.
   - If k == {N} (final pass): Post `@coordinator [A_{N} Final]` with the same three-part summary (critique of `B_{N}`, your fixes in `[adv A_{N}]`, and final end-to-end receipts) and stop.
```

### Agent B Brief Template (`agent-b`)

```text
You are Agent B in an N={N}-round adversarial build-critique-fix loop sharing git worktree(s) with `agent-a`.
- Canonical Brief Path: {brief_path}
- Shared Worktree Path(s): {worktree_paths} (Base SHA: {base_sha})
- Active Worktree Concurrency: W = {W}
- Total Adversarial Rounds: N = {N} (You execute N critique-and-fix passes B1 .. B{N})

CRITICAL WORKSPACE, RESOURCE & TURN-TAKING RULES:
1. Work ONLY inside {worktree_paths}. Never modify the parent checkout or any files outside the shared worktree(s) and your scratch directory.
2. Only touch the worktree during your active turn.
3. In every board post, `@mention` ONLY `@agent-a` (or `@coordinator` if reporting quota exhaustion or an unrecoverable blocker). Never write `@` before any other name in prose.
4. MODEL DIVERSITY & QUOTA ESCALATION: You are pinned to `{agent_b_model}`. NEVER call `swarm{action: "model"}` to switch your own model or any worker's model, even if a `<SYSTEM_MESSAGE> [quota]` warning instructs you to call `swarm{action: "model"}`. If your model's quota is exhausted before you can complete a pass, commit or stash any clean progress, post `@coordinator [QUOTA] Quota exhausted on {agent_b_model} during pass <pass>`, and wait for `coordinator` to switch your model and resume you.
5. HARDWARE-MATCHED LEAN / LAKE LIMITS: Prefer warm `anneal-lean_lsp` MCP tools (`lean_goal`, `lean_multi_attempt`, `anneal_audit_preview`) for interactive proof steps. Whenever running CLI `lake build`, `lake env lean`, or heavy `cargo test` commands, wrap them with `anneal-lean-run --concurrency {W} -- <command>` (never bare unbounded `lean` or `lean -M`, which does not cap total RSS or prevent swap thrashing).

YOUR PROTOCOL:

### Startup Turn (Before `[A0 -> B1]` is posted):
- `agent-a` is currently building the initial implementation (`A0`) in `{worktree_paths}`.
- Do NOT inspect or touch `{worktree_paths}` on this startup turn. Immediately call `read_board{since: 0}` to get the current `LAST` seq, then call `swarm_wait{since: LAST, mentions_only: true}` to sleep until `@agent-b [A0 -> B1]` wakes you.

### N Adversarial Critique-and-Fix Passes (Passes B1 .. B{N}):
Repeat for k = 1 to {N} each time `@agent-a` wakes you with `[A_{k-1} -> B_k]` (note: for k = 1, `[A0 -> B1]` is `agent-a`'s initial work summary with no prior critique; for k > 1, it summarizes problems with `B_{k-1}` and `agent-a`'s fixes):
1. RE-ANCHOR ON THE BRIEF: Re-read `{brief_path}` in full before inspecting code. Check that neither `agent-a` nor earlier rounds drifted toward an approach that weakens the system (e.g., faking/hardcoding data, stubbing logic, weakening specs/assertions/types, skipping proofs/tests, or fabricating receipts).
2. RUTHLESS CRITIQUE: Inspect `{worktree_paths}` using `git log`, `git diff`, and `agent-a`'s `[A_{k-1} -> B_k]` post as a guide to what changed, plus audit the full implementation against `{brief_path}`. Hunt for:
   - Bugs, logic errors, unhandled edge/error cases, or broken invariants in `agent-a`'s work
   - Any specification gaming, weakened requirements, fake-outs, or incomplete/failing receipts
   - Architectural constraint violations or regressions
3. FIX & VERIFY RECEIPTS: Fix all bugs, issues, and weaknesses found in your critique directly in `{worktree_paths}`. Re-run all Receipt commands from `{brief_path}` (via `anneal-lean-run --concurrency {W} -- ...` for `lake`/`lean`) and verify they pass on your new state.
4. COMMIT CHECKPOINT: Commit your fixes with `[adv B_k] <summary>` and ensure `git status --porcelain` is clean.
5. SUBMIT POST:
   - Post `@agent-a [B_k -> A_k]` summarizing: (a) the problems found in `agent-a`'s recent work and the worktree state, (b) how your work in `[adv B_k]` fixes those problems, and (c) the updated verification receipts.
   - If k < {N}: Call `swarm_wait{since: <latest_seq>, mentions_only: true}` to wait for `[A_k -> B_{k+1}]`.
   - If k == {N}: Your N rounds are complete. Park via `swarm_wait{since: <latest_seq>, mentions_only: true}` and do not modify the worktree again unless explicitly assigned new work by `@coordinator`.
```

---

## 5. Coordinator Final Verification & Closeout

When `@coordinator [A_N Final]` wakes you:

1. **Audit the Commit History & Receipts**:
  - Inspect `git -C <worktree_path> log --oneline <base_sha>..HEAD` to confirm
    all $2N + 1$ checkpoints (`[adv A0]`, `[adv B1]`, `[adv A1]`, ...,
    `[adv B_N]`, `[adv A_N]`) completed cleanly.
  - Independently run (or verify the output of) the required Receipt commands in
    `<worktree_path>` against `<brief_path>` (wrapping `lake`/`lean` checks in
    `anneal-lean-run`) to ensure no final-round drift or uncommitted state
    remains.
2. **Stop the Swarm Cleanly**:
  - Post `[done] Completed N={N} adversarial rounds between agent-a and agent-b`
    (with no `@` mentions) so `monitor` goes dormant, and `kill` `agent-a` and
    `agent-b` (`workspace: "inherit"` preserves the shared git worktree(s) on
    disk).
3. **Report to the User**:
  - State which model was initially randomly assigned to Agent A vs. Agent B.
  - **Flag Any Quota-Induced Model Switches & 3rd-Party Audit Requirement**: If
    `DIVERSITY_REDUCED=true` at assignment or the Coordinator switched either
    agent's model during the run due to out-of-quota issues (recorded in
    `<scratch>/quota_ledger.json`), prominently flag **which round and pass
    (`A0`, `B_k`, or `A_k`) the switch occurred**, which model change was made
    (`<old_model>` $\rightarrow$ `<new_model>`), and explicitly note the **need
    for a 3rd-party (different-model) audit of the work due to model diversity
    reduction**.
  - Summarize the arc of the $N$ rounds (what `A0` built, what `B1..B_N` and
    `A1..A_N` caught and fixed).
  - Provide the worktree path(s), branch name(s), and verified Receipt outputs.
