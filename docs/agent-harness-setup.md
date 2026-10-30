# Agent harness setup and anti-cheating configuration

This guide explains how to configure AI coding agents (Claude Code, Gemini CLI,
Jetski, and Codex) to discharge Anneal verification obligations rapidly using
the warm Lean 4 LSP server (`tools/anneal-lsp/`) while enforcing strict
anti-cheating boundaries so agents can only succeed by writing valid proofs in
`anneal/proofs/Proof/<Crate>/<Item>.lean`.

For the underlying four-layer threat model, see
[**Agentic proof construction workflow and anti-cheating safeguards**](agent-proof-workflow.md).
For Rust maintainers adopting Anneal in a project, see the
[**Project owner guide**](project-owner-guide.md).

---

## 1. Architecture of the Anneal agent harness

An effective Anneal agent harness combines three components:

1. **Warm Lean 4 & Rust LSP MCP server (`tools/anneal-lsp/mcp_server.py`):**
   Maintains a background `lake serve` process per `.anneal/` workspace so agents
   can query proof states (`lean_goal`), test candidate tactics in memory without
   disk writes (`lean_multi_attempt`), inspect types (`lean_hover`), and run
   pre-flight `TrustedBoundary` checks (`anneal_audit_preview`) in **12–50 ms**
   instead of spawning cold `lake env lean` processes (2–10 s per invocation).
2. **Pre-tool and post-tool enforcement hooks (`tools/anneal-lsp/hooks/`):**
   - `pre_tool_use.py` (`PreToolUse`) intercepts file-write and edit tool calls
     when `.anneal/spec-lock.json` is active and blocks edits to any file outside
     `anneal/proofs/Proof/<Crate>/<Item>.lean` (plus designated mutable Rust
     source files when `--allow-impl-edit <item>` was used during `lock-specs`).
   - `post_tool_use.py` (`PostToolUse`) automatically runs `lean_diagnostics` on
     any edited `.lean` file and appends compiler errors, warnings, and open
     `sorry` goals directly to the tool output in the same turn.
3. **Outer cryptographic lock and OS sandbox (`cargo anneal agent-verify` &
   `cargo anneal agent-sandbox`):**
   Even if an agent has unconstrained shell access, `cargo anneal agent-verify`
    supports out-of-tree lockfiles (`--lock-file <PATH>`), git-committed lock
   references (`--lock-git-ref <REV>`), semantic vacuity checks, and bubblewrap
   read-only bind mounts (`cargo anneal agent-sandbox`) so the agent cannot
   modify `.anneal/spec-lock.json` or `anneal/proofs/Specs/**`.

---

## 2. Configuring MCP and hooks across agent hosts

The repository ships a self-contained Python 3 MCP server and hook suite in
`tools/anneal-lsp/` (requiring only Python $\ge 3.10$ and the Lean toolchain
installed by `cargo anneal setup` or `elan`) together with portable agent skills
in `skills/anneal-prove/SKILL.md` and `skills/anneal-lsp/SKILL.md`.

### Claude Code (`.claude/settings.json` and `.mcp.json`)

Add the `anneal-lean_lsp` MCP server to `.mcp.json` at the root of your
workspace:

```json
{
  "mcpServers": {
    "anneal-lean_lsp": {
      "command": "python3",
      "args": ["/absolute/path/to/anneal/tools/anneal-lsp/mcp_server.py"],
      "env": {
        "PYTHONUNBUFFERED": "1"
      }
    }
  }
}
```

Configure `PreToolUse` and `PostToolUse` hooks in `.claude/settings.json`:

```json
{
  "hooks": {
    "PreToolUse": [
      {
        "matcher": "Edit|MultiEdit|Write|NotebookEdit",
        "hooks": [
          {
            "type": "command",
            "command": "python3 /absolute/path/to/anneal/tools/anneal-lsp/hooks/pre_tool_use.py"
          }
        ]
      }
    ],
    "PostToolUse": [
      {
        "matcher": "Edit|MultiEdit|Write",
        "hooks": [
          {
            "type": "command",
            "command": "python3 /absolute/path/to/anneal/tools/anneal-lsp/hooks/post_tool_use.py"
          }
        ]
      }
    ]
  }
}
```

### Gemini CLI / Jetski (`~/.gemini/config/plugins/anneal-lean/`)

In Gemini CLI or Jetski environments, `tools/anneal-lsp/` can be installed
directly as a plugin bundle or registered in `settings.json` using the exact same
`mcp_server.py`, `hooks/pre_tool_use.py`, and `hooks/post_tool_use.py` scripts
(both hook scripts accept both Claude Code `tool_name`/`tool_input` and
Jetski/Gemini `toolName`/`toolInput` JSON payloads).

---

## 3. Locking specifications and preventing lockfile tampering

Before starting an autonomous proof session, the human maintainer or outer
orchestrator script locks the workspace specifications:

```bash
cargo anneal lock-specs
```

### Closing the shell-overwrite vector (`--lock-file` and `--lock-git-ref`)

If an agent can execute arbitrary shell commands inside the workspace, it could
attempt to re-run `cargo anneal lock-specs` after weakening a Rust attribute or
editing `anneal/proofs/Specs/<Crate>/<Item>.lean`. Use one or more of the
following three defenses to close this vector completely:

1. **Verify against a Git-committed lockfile (`--lock-git-ref`):**
   Commit `.anneal/spec-lock.json` before launching the agent, then gate
   acceptance with:
   ```bash
   cargo anneal agent-verify --lock-git-ref HEAD
   ```
   `agent-verify` reads `HEAD:.anneal/spec-lock.json` from the Git object
   database and rejects the run if `.anneal/spec-lock.json` on disk was modified.
2. **Write the lockfile outside the agent's writable workspace (`--lock-file`):**
   In an outer orchestrator script, store the lockfile in a protected directory
   outside the repository:
   ```bash
   cargo anneal lock-specs --lock-file /var/run/anneal-locks/spec-lock.json
   # ... run agent ...
   cargo anneal agent-verify --lock-file /var/run/anneal-locks/spec-lock.json
   ```
3. **Run the agent inside an OS-level read-only bind-mount sandbox (`agent-sandbox`):**
   On Linux hosts with `bwrap` (`bubblewrap`), invoke the agent inside
   `cargo anneal agent-sandbox`:
   ```bash
   cargo anneal agent-sandbox -- claude -p "Prove all open obligations in anneal/proofs/Proof/"
   ```
   `agent-sandbox` mounts `.anneal/spec-lock.json`, `anneal/proofs/Specs/`,
   `anneal/proofs/Assumptions/`, `Cargo.toml`, and `src/` (unless
   `--allow-impl-edit` is active in the lockfile) as kernel-enforced read-only
   bind mounts (`--ro-bind`), while keeping `anneal/proofs/Proof/` and build
   caches writable.

### Safe-to-unsafe optimization workflows (`--allow-impl-edit`)

When an agent is tasked with optimizing a Rust function's body (for example,
replacing a safe loop with an `unsafe` fast path proved equivalent via
`#[anneal_spec::spec(equivalent_to: ...)]`) while keeping the specification
locked, lock the workspace with `--allow-impl-edit`:

```bash
cargo anneal lock-specs --allow-impl-edit checksum_frame_fast
```

This records `checksum_frame_fast` in `mutable_subjects` inside
`.anneal/spec-lock.json`. During `agent-verify`:
- the agent may modify the body of `checksum_frame_fast` in `src/` and its proof
  in `anneal/proofs/Proof/**/checksum_frame_fast.lean`, and
- every other Rust item, every `#[spec]` companion (`__anodized_fn_requires_*`,
  `__anodized_fn_ensures_*`), and all `Specs/**` and `Assumptions/**` files
  remain cryptographically locked to their baseline SHA-256 digests.

---

## 4. Two-regime proof workflow: Fast edits vs. precision LSP tools

Agents equipped with `skills/anneal-prove/SKILL.md` and
`skills/anneal-lsp/SKILL.md` should follow the **Threshold Heuristic** to balance
LLM turn latency against Lean kernel elaboration time:

- **Below the threshold (routine arithmetic, straight-line `verifyMirNoPanicSym`
  templates, standard `omega`/`simp`/`rfl` steps):**
  Write the complete proof directly to `anneal/proofs/Proof/<Crate>/<Item>.lean`
  using `edit_file` / `Write`. Do not spend extra tool turns calling
  `lean_multi_attempt` beforehand—the `PostToolUse` hook automatically runs warm
  LSP diagnostics in ~15–300 ms and returns any remaining goals in the same turn.
- **Above the threshold (symbolic evaluator stalls, multi-block CFGs, bitwise
  operations, or loops):**
  Switch immediately to precision LSP tools:
  1. Write a wildcard `change match _ with | true => _ | false => _` + `sorry`
     with tight `fuel` (`#statements + 2`) and call `lean_goal` (~15 ms) to
     inspect the exact kernel WHNF terms.
  2. Never include `wpMirExecSym`, `Trusted.Sequence.length`, or
     `Mir.<Crate>.<Item>.body` (for multi-block CFGs) inside `dsimp`.
  3. Use `lean_multi_attempt` (capped at 1–2 probes per subgoal) to compare
     candidate tactics in memory without touching disk.
  4. Run `anneal_audit_preview` on `Proof/<Crate>/<Item>.lean` to verify zero
     compiler errors, zero `sorry` tokens, `Anneal.*` statement-origin
     isolation, and clean `#print axioms` before running final end-to-end
     `cargo anneal agent-verify`.

---

## 5. Phase 1 provisional verification (`--provisional`)

When onboarding a large crate or triaging whether a new specification is
satisfiable on concrete execution traces before investing in a full symbolic
proof, run `agent-verify` with `--provisional`:

```bash
cargo anneal agent-verify --provisional --item <item>
```

Under `--provisional` (or `cargo anneal verify --allow-provisional-native`),
`TrustedBoundary` permits `native_decide` (`Lean.ofReduceBool` /
`Lean.trustCompiler`) inside `Proof.*` modules (never in `Specs.*` or
`Obligations.*`) and marks the item distinctly as `PROVISIONAL_NATIVE` in the
verification report. A `PROVISIONAL_NATIVE` result is never reported as
`UNCONDITIONAL`; once the specification and boundary invariants are validated,
replace `native_decide` with a symbolic kernel proof (`verifyMirNoPanicSym`,
`verifyStatefulMirNoPanicSym`, or `FunctionalTranslation`) so `cargo anneal
agent-verify` (without `--provisional`) reports `UNCONDITIONAL`.

---

## 6. Parallel multi-agent sharding (`--item`)

Because each subject item compiles to an independent verification module
`Verify.<Crate>.<Item>` and proof file `anneal/proofs/Proof/<Crate>/<Item>.lean`,
an orchestrator can fan out proof construction across multiple parallel agents:

1. Run `cargo anneal lock-specs` once in the parent workspace.
2. Assign each worker agent a disjoint `<item>` slice:
   - Each worker runs `cargo anneal agent-context --item <item>`.
   - Each worker edits only `anneal/proofs/Proof/<Crate>/<Item>.lean` and checks
     its slice with `anneal_audit_preview` or
     `cargo anneal agent-verify --item <item>`.
3. After all workers finish, run full crate verification once:
   ```bash
   cargo anneal agent-verify --lock-git-ref HEAD
   ```
