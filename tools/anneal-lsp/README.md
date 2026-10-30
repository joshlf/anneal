# Anneal Lean 4 & Rust LSP Harness (`tools/anneal-lsp`)

Portable MCP server, warm `lake serve` worker pool daemon, lifecycle hooks, and
live InfoView sidecar for interactive Lean 4 (`v4.34.1` `lake serve`) and Rust
verification development across Claude Code, Gemini CLI, Jetski, and Codex.

See [`../../docs/agent-harness-setup.md`](../../docs/agent-harness-setup.md) for
complete step-by-step installation and configuration instructions.

## Bundled Components

1. **MCP Server (`anneal-lean_lsp` in `mcp_config.json`)**:
   - Thin `stdio` JSON-RPC bridge (`server/anneal_lsp_mcp.py`) connected to a
     singleton warm worker pool daemon (`server/anneal_lsp_daemon.py` on
     `/tmp/anneal-lean-lsp.sock`).
   - Lazily pools up to 4 `lake serve --` workers across Anneal verification crates,
     sandboxed under `bwrap` (`--ro-bind / /`, writable `.lake/`, `--tmpfs /tmp`,
     `--unshare-net`) when `bwrap` is installed, with automatic worker restart
     whenever `cargo anneal` regenerates `.anneal/lakefile.toml`.
   - 13 MCP tools (`<4 KiB` inline-compacted outputs):
     - **Lean 4 Proving & Navigation**: `lean_goal`, `lean_multi_attempt`,
       `lean_diagnostics`, `lean_hover`, `lean_definition`, `lean_completions`,
       `lean_outline`, `lean_local_search`, `lean_restart_workspace`.
     - **Anneal & Rust Verification**: `anneal_audit_preview`,
       `anneal_item_bridge`, `rust_diagnostics`, `rust_symbols_and_def`.

2. **Lifecycle Hooks (`hooks.json`)**:
   - `PreToolUse` (`hooks/pre_tool_use.py`): `<5 ms` guard blocking edits
     outside `anneal/proofs/Proof/**` (and designated `mutable_subjects` under
     `src/**/*.rs` when `--allow-impl-edit` is active) whenever
     `.anneal/spec-lock.json` is present.
   - `PostToolUse` (`hooks/post_tool_use.py`): Appends live Lean 4 diagnostics and
     open `sorry` goals directly to `edit_file` / `write_file` / `Edit` / `Write`
     tool results on `*.lean` files.

3. **Jetski Web AuxPane UI (`sidecars/infoview/`)**:
   - **Anneal Lean 4 InfoView** panel in the conversation's right-hand Auxiliary Pane:
     live proof goals, compiler diagnostics, interactive zero-disk Multi-Attempt
     tactic sandbox, Anneal crate obligation scoreboard, and LSP worker pool monitor.

4. **Skill (`../../skills/anneal-lsp/SKILL.md`) & Rule (`rules/AGENTS.md`)**:
   - Guides agents to use ~12 ms in-memory tactic checks (`lean_goal` +
     `lean_multi_attempt` + `anneal_audit_preview`) and the two-regime threshold
     heuristic instead of cold `lake env lean` loops.
