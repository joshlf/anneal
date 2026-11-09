# Reproduction Instructions — `BRIEF-1.4`

Slice Unsizing (`CastKind.pointerCoercion "Unsize"` `[T; N]` $\rightarrow$ `[T]`), `Rvalue.len` on Slices, Non-Scalar `ConstValue` / Global Reads, Signed & Element-Scaled `BinOp.offset`, and Structural Completeness (`N = 4` Adversarial Rounds: `A0 -> B1 -> A1 -> B2 -> A2 -> B3 -> A3 -> B4 -> A4`).

## 1. Environment & Worktree Setup

```bash
cd <path/to/anneal>
export PATH="$HOME/.local/bin:$HOME/.cargo/bin:$HOME/.elan/bin:$PATH"
git status --porcelain
```

## 2. Single-File Correspondence Verification (Both Dialects)

Verify `L3_PlacesAndBasicMem.lean` (including Theorems `L3.17`–`L3.29`) in both `V2026_06_01` and `V2026_08_01`:

```bash
cd <path/to/anneal>/examples
anneal-lean-run --mode file --concurrency 3 -- lake env lean ../theory/Correspondence/V2026_06_01/L3_PlacesAndBasicMem.lean
anneal-lean-run --mode file --concurrency 3 -- lake env lean ../theory/Correspondence/V2026_08_01/L3_PlacesAndBasicMem.lean
```

## 3. Full Multi-Target Lake Build

Build `Trusted`, `Anneal`, `MiniRust`, `Correspondence`, `MirVerification`, and all `examples/` targets under `anneal-lean-run`:

```bash
cd <path/to/anneal>/examples
anneal-lean-run --mode build --concurrency 3 -- lake build Trusted Anneal MiniRust Correspondence MirVerification
anneal-lean-run --mode build --concurrency 3 -- lake build
```

## 4. Trusted Computing Base Audit & Zero-Sorry Gate

Verify kernel dependency closure, statement-origin separation, Cargo DAG boundary, and zero `sorry`/`admit`/`axiom`:

```bash
cd <path/to/anneal>
python3 trusted/audit/check_trusted.py --fast
./ci/check_todo.sh
```
