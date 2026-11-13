# Contributing

vbm-orchestrator is built by agents under mechanical gates, and it lands directly on `main` with `.land/land-direct` (no pull requests: the maintainers' agents use the pinned [vbm-land](https://github.com/witt3rd/vbm-land) lander). Outside contributions are welcome as an **issue** first: a counterexample to a claim, a missing guarantee you need, a gate that can be fooled. Pull requests from forks are not merged as such; a maintainer may land an equivalent change.

## Rules a change must meet

- `mise exec -- scripts/tier1.sh` passes (Lean 4.35.0, pinned in `mise.toml`). It runs offline after the first toolchain fetch.
- No `sorry`, `admit`, `axiom`, `unsafe`, `implemented_by` or `csimp` in Lean; `VbmOrchestrator/` imports `Init` and itself only. A proof is hard? Decompose it; never weaken the statement.
- Every gate has a negative self-test and prints ran-evidence (`ran: NAME: N cases`, N > 0); a gate that ran nothing fails.
- Small diffs: at most 150 production lines under `VbmOrchestrator/` per change. Conventional Commits (`type(scope): summary`).
- No private name, no personal path, no secret, no network call from a test. Nothing runs after the push: there is no workflow and no runner in this repository.
- `.land/tool/` is a pinned copy of vbm-land: never edit it.

By contributing you agree your contribution is licensed under Apache-2.0.
