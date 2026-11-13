## Landing (direct to main, no PRs)
- Work in a worktree off a fresh origin/main. Diff ≤150 production lines, ≤45 min without a passing build; over either, stop and write a decomposition plan.
- Commit locally with Conventional Commits. Land only with `.land/land-direct`; never push main yourself, never force-push it, never open a PR.
- New behaviour lands behind a flag that defaults OFF. Interface changes: add beside the old, migrate callers, delete at zero references.
- Everything runs before the push, once (Tier 1 on the rebased tree); nothing runs after it. If main is ever red, whoever sees it reverts the offending commit with `git revert` and lands the revert; the author fixes forward in a new worktree. A landing must not add a failure.
- `.land/tool/` is a pinned copy of vbm-land: never edit it (`.land/tool/bin/land-check` fails the gate). Change the tool upstream, then `.land/tool/bin/land-update <tag>`.
- Decide anything reversible and log it. Escalate only money, data loss, secrets, publishing, or harm to a third party; say so in one line and stop.

## Principles (the VBM + HVTBD family)
- Everything runs before the push, once, on the commit rebased onto main. Nothing runs after the push.
- Proofs, not tests. A test exists only for what the proofs do not cover (the boundary), never for the development tooling.
- A failure is a root-cause question, never a reason to add a check, gate, script or document. Nothing is added to the process without deleting something.
- The worker owns its change: when the lander refuses it, the worker fixes it and lands again until it converges.

## Landing (direct to main, no PRs)
- Work in a worktree off a fresh origin/main. Diff ≤150 production lines, ≤45 min without a passing build; over either, stop and write a decomposition plan.
- Commit locally with Conventional Commits. Land only with `.land/land-direct`; never push main yourself, never force-push it, never open a PR.
- New behaviour lands behind a flag that defaults OFF. Interface changes: add beside the old, migrate callers, delete at zero references.
- Everything runs before the push, once (Tier 1 on the rebased tree); nothing runs after it. If main is ever red, whoever sees it reverts the offending commit with `git revert` and lands the revert; the author fixes forward in a new worktree. A landing must not add a failure.
- `.land/tool/` and `.land/land-direct` are a pinned copy of vbm-land: never edit them (`.land/tool/bin/land-check` fails the gate). Change the tool upstream, then `.land/tool/bin/land-update <tag>`.
- Decide anything reversible and log it. Escalate only money, data loss, secrets, publishing, or harm to a third party; say so in one line and stop.

## Principles (the VBM + HVTBD family)
- Everything runs before the push, once, on the commit rebased onto main. Nothing runs after the push.
- Proofs, not tests. A test exists only for what the proofs do not cover (the boundary), never for the development tooling.
- A failure is a root-cause question, never a reason to add a check, gate, script or document. Nothing is added to the process without deleting something.
- The worker owns its change: when the lander refuses it, the worker fixes it and lands again until it converges.

# AGENTS.md: vbm-orchestrator

The task cycle as a pure state machine, written once in Lean 4 and machine-checked: prepare a workspace, run a worker agent, validate with the lander's checks, review, land, clean up; criticism returns whole to the same worker session after a decision model has judged the task still converging; the money ceiling and a wall deadline are the only hard stops.

**Scope.** Pure data and total functions over `Init` and the vocabulary package `VbmWork`. No input or output, no clock, no model call, no network, no storage. What is proved is what any interpreter that meets the ports' laws may rely on; the ports' implementations are the application's.

## Status
Slices (docs/decisions/0001-vbm-orchestrator.md): S1: the data, the machine and its proofs (reports once, cleans once, lands only done, the worker runs at most `fuse` times). S2: non-interference (control never reads prose). S3: the reference model and the conformance vectors (`docs/vectors.md`): the specification is complete. Next is the interpreter, in the application that binds it.

## Hard rules
- **Forbidden anywhere in Lean:** `sorry`, `admit`, `axiom`, `unsafe`, `implemented_by`, `csimp` (Tier 1 scans for them; a comment may mention one only on a line marked `tier1-allow`). A proof is hard? Decompose it; never weaken the statement.
- **Spec first.** Behaviour lands as a specification and its proofs. A theorem with a hypothesis carries a witness that the hypothesis can hold (a theorem whose hypothesis cannot be met is not a theorem).
- **Ran-evidence.** A gate or test that runs zero cases fails: every test script ends with `ran: NAME: N cases` (N > 0) and every concurrent gate reports its own count (`scripts/ran-gates.txt`). A refused tool, a `SKIPPED` line or an early exit is never a pass. Every gate has a negative self-test that must be shown able to fail in the same run.
- **Nothing runs after the push.** Everything runs before it, once, in Tier 1 on the rebased tree; there is no workflow and no runner in this repository, and none is registered for it.
- **Public-ready, always.** No private name, no path of ours, no number of ours, no e-mail anywhere; write generic ("a verified agent harness"). Names are kept as hashes (`scripts/public-banned-hashes.txt`).
- **Small diffs** and Conventional Commits; TTL 45 minutes without a passing build: abort and decompose.
- **Land with `.land/land-direct`**, never a PR, never push or force-push `main`. Any file of the repository, spec and scripts and docs and this file included, lands like any change when Tier 1 passes; no approval is needed. Only the lander's own files (`.land/tool/`) and the signing keys are read-only.
- **No secrets in the repository.** No paid model call and no network call from a test or a gate.

## Library rules
- **Module roots:** `VbmOrchestrator` imports `Init`, the pinned `VbmWork` and itself only (Tier 1 scans the imports); `VbmOrchestratorProofs` may import `Std` and `Lean` and is never linked, and nothing in `VbmOrchestrator` may import it.
- **No cap, no heuristic.** A number that stands in for understanding does not belong in the machine: progress is the Judge's, the fuse is the money's, the deadline is time's. Nothing in it reads prose: control depends on typed data only (a theorem says so).
- **A vendored library is never patched** (`land-pin verify`); change `vbm-work` upstream, then bump the pin.

## Gates
**Tier 1** (`scripts/tier1.sh`): forbidden-constructs scan, import scan, pipefail lint, the vendored lander's drift check, zero-warning build, axiom gate, public-readiness lint, ran-evidence self-tests. It runs before every landing, on the commit rebased onto main; nothing runs after the push. If main is ever red, whoever sees it reverts the offending commit with `git revert` and lands the revert; the author fixes forward in a new worktree.

## Layout
`VbmOrchestrator/` spec and code · `VbmOrchestratorProofs/` proofs and the obligation ledger (never linked) · `docs/decisions/` design · `scripts/` gates, lints and their self-tests, `.land/land.d/` the lander's hooks, the pinned lander.
