# Reproduction Instructions for BRIEF-2.1

## Environment & Worktree
- **Worktree Path**: `/home/groupagent-anneal-bot/Projects/markdittmer/anneal-wt-brief-2-1`
- **Branch**: `adv/brief-2-1`
- **Base Commit**: `d2851b0d778b90c2cb134350b3d7466361bcb3d1`

## Step-by-Step Verification Commands

1. Enter the worktree and verify the branch:
   ```bash
   cd /home/groupagent-anneal-bot/Projects/markdittmer/anneal-wt-brief-2-1
   git status --short --branch
   ```

2. Build the Lean targets (`Trusted`, `Anneal`, and `MirVerification` including polymorphic `CapturedMir.instantiate` tests) via Lake:
   ```bash
   export PATH="$HOME/.elan/bin:$PATH"
   cd /home/groupagent-anneal-bot/Projects/markdittmer/anneal-wt-brief-2-1/examples
   lake build Trusted Anneal MirVerification
   ```
   Expected output: Exit code `0` (`Build completed successfully`).

3. Run the TrustedBoundary & downstream kernel replay audit:
   ```bash
   cd /home/groupagent-anneal-bot/Projects/markdittmer/anneal-wt-brief-2-1
   python3 trusted/audit/check_trusted.py --fast
   ```
   Expected output:
   ```text
   PASS: kernel dependency closure, statement-origin separation, and Cargo DAG boundary
   40 Trusted modules; ...
   ```
   with exit code `0` and `axioms=['propext', 'Classical.choice', 'Quot.sound']`.
