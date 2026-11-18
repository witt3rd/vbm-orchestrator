# Scorecard

Status: draft by a worker, 2026-11-18; goals and targets are the owner's to set.

Measured on release 0.10.0 (`VERSION`), commit 95dfe90, with Lean 4.35.0 run through `lake` directly (`mise exec` could not fetch its toolchain offline; the `lake` on the path is the pinned 4.35.0). Every command runs from the repository root.

## Goals as the repository states them

- **G1. The task cycle is a pure, total state machine written once in Lean 4 and machine-checked, with no input or output, clock, model call, network or storage.** README.md:3, README.md:9, AGENTS.md:31, AGENTS.md:33.
- **G2. The stated guarantees are proved:** the worker runs at most as often as the money allows, a task reports at most once, lands only a done outcome after validation and review, never approves through an unreachable reviewer, and cleans up exactly once on every path. README.md:3, docs/decisions/0001-vbm-orchestrator.md:19-31.
- **G3. Control never depends on prose (non-interference):** two runs over events that differ only in their words ask for the same actions and end in the same phase. README.md:3, docs/decisions/0001-vbm-orchestrator.md:33, AGENTS.md:50.
- **G4. Money and time are the only hard stops:** the fuse (a money ceiling) and the wall deadline; no cap on rounds, no heuristic number standing in for understanding. docs/decisions/0001-vbm-orchestrator.md:10, AGENTS.md:50.
- **G5. What is not proved is covered by conformance vectors,** language-neutral scenarios generated from the machine, that any interpreter runs, and they cannot drift from it. README.md:9, docs/vectors.md:3, docs/vectors.md:49, docs/decisions/0001-vbm-orchestrator.md:38.
- **G6. Only `proved` claims may be called verified; what rests on no proof is declared** (the proof ledger, with its one `limit`, and the trust ledger). docs/proof-ledger.md:5, docs/trust-ledger.md:3, AGENTS.md:40.
- **G7. The verified core stays small and its imports stay narrow:** `VbmOrchestrator` imports `Init`, the pinned `VbmWork` and itself only; diffs of at most 150 production lines. AGENTS.md:49, CONTRIBUTING.md:8, CONTRIBUTING.md:10.
- **G8. Nothing unsound or unfinished enters:** no `sorry`, `admit`, `axiom`, `unsafe`, `implemented_by`, `csimp`; zero build warnings; only the three standard axioms. AGENTS.md:39, CONTRIBUTING.md:8, scripts/tier1.sh:47.
- **G9. Every gate is trustworthy:** it prints ran-evidence (N > 0 cases) and has a negative self-test that can fail. AGENTS.md:41, CONTRIBUTING.md:9.
- **G10. The repository is public-ready:** no private name, path, number or e-mail. AGENTS.md:43, CONTRIBUTING.md:11.
- **G11. The vendored lander and library are exactly their pins** (never patched). AGENTS.md:51, CONTRIBUTING.md:12, docs/trust-ledger.md:28.
- **G12. Everything runs before the push, once, in Tier 1, and the gate stays practical to run** (the 45-minute TTL, a landing must not add a failure). AGENTS.md:5, AGENTS.md:44, scripts/tier1.sh:1-4.
- **G13. Next, the interpreter in the application that binds the machine;** the repository is pre-release and publishes nothing yet. AGENTS.md:36, README.md:5.

## Metrics

All are integers. `now` was measured on 2026-11-18 unless it says `unmeasured`. `floor` starts equal to `now` and only moves toward better. The target column is for the owner.

| metric | direction | goal it serves | how to measure (from the repository root) | now | floor (= now) | target |
|---|---|---|---|---|---|---|
| `proof-ledger-gaps` (claims `partial` or `open`, count) | lower | G2, G6 | `.land/tool/bin/land-lean ledger \| sed -nE 's/.* ([0-9]+) partial, ([0-9]+) open.*/\1 \2/p' \| awk '{print $1+$2}'` | 0 (2026-11-18) | 0 | |
| `proved-claims-share-hundredths-percent` (proved claims of all ledger claims) | higher | G2, G6 | `.land/tool/bin/land-lean ledger \| sed -nE 's/^ledger: ([0-9]+) proved.* of ([0-9]+)$/\1 \2/p' \| awk '{print int($1*10000/$2)}'` | 9230 (2026-11-18; 12 of 13) | 9230 | |
| `limit-claims` (claims no machine decides; the ports' laws) | lower | G5, G6 | `.land/tool/bin/land-lean ledger \| sed -nE 's/.* ([0-9]+) limit.*/\1/p'` | 1 (2026-11-18) | 1 | |
| `proved-theorems` (theorem and lemma declarations under `VbmOrchestratorProofs/`) | higher | G2, G3 | `cat VbmOrchestratorProofs/*.lean \| grep -cE '^[[:space:]]*(@\[[^]]*\][[:space:]]*)?(private[[:space:]]+)?(theorem\|lemma)\b'` | 110 (2026-11-18) | 110 | |
| `witness-examples` (`example` declarations, the non-vacuity witnesses, in the proofs) | higher | G2 | `cat VbmOrchestratorProofs/*.lean \| grep -cE '^[[:space:]]*example\b'` | 10 (2026-11-18) | 10 | |
| `axiom-offending-constants` (constants depending on a non-standard axiom) | lower | G8 | `.land/tool/bin/land-lean axiom \| sed -nE 's/.* ([0-9]+) offending.*/\1/p'` | 0 (2026-11-18; 1582 constants checked) | 0 | |
| `forbidden-construct-hits` (the Tier 1 scan of `sorry`, `admit`, `axiom`, `unsafe`, `implemented_by`, `csimp`) | lower | G8 | `grep -rHnE '\b(sorry\|admit\|axiom\|unsafe\|implemented_by\|csimp)\b' VbmOrchestrator VbmOrchestratorProofs VbmOrchestratorWire.lean VbmOrchestrator.lean VbmOrchestratorProofs.lean vectors --include=*.lean \| grep -v tier1-allow \| wc -l` | 0 (2026-11-18) | 0 | |
| `warnings` (build warnings; the build also fails on any, `warningAsError`) | lower | G8 | `rm -rf .lake/build; lake build VbmOrchestrator VbmOrchestratorProofs VbmOrchestratorWire LandLedger vbm-orchestrator-vectors 2>&1 \| grep -c 'warning:'` | 0 (2026-11-18) | 0 | |
| `vectors` (conformance scenarios in the checked-in file) | higher | G5 | `grep -c . vectors/vbm-orchestrator-vectors-1.jsonl` | 30 (2026-11-18) | 30 | |
| `vector-check-failures` (scenarios that fail the generator's `--check`, `--roundtrip` or byte comparison) | lower | G5 | `scripts/test_vectors.sh >/dev/null 2>&1; echo $?` (0 = none; its output ends `ran: test_vectors: N cases`) | 0 (2026-11-18; 11 cases ran) | 0 | |
| `stale-scenario-count-statements` (statements of a scenario count in README.md or docs/ that differ from the file) | lower | G5 | `n=$(grep -c . vectors/vbm-orchestrator-vectors-1.jsonl); grep -rhoE '[0-9]+ scenarios' README.md docs \| grep -vc "^$n scenarios"` | 1 (2026-11-18; docs/decisions/0001-vbm-orchestrator.md:38 says 28) | 1 | |
| `trust-ledger-gaps` (trust entries with no written contract or no test) | lower | G6 | `.land/tool/bin/land-lean trust \| sed -nE 's/.*; ([0-9]+) with no written.*/\1/p'` | 3 (2026-11-18; of 3 entries) | 3 | |
| `core-lines` (non-blank lines not starting with `--` in `VbmOrchestrator/` and `VbmOrchestrator.lean`; the verified core's size) | lower | G7 | `cat VbmOrchestrator/*.lean VbmOrchestrator.lean \| grep -vE '^[[:space:]]*(--\|$)' \| wc -l` | 320 (2026-11-18) | 320 | |
| `core-import-violations` (imports in the core outside `VbmOrchestrator` and `VbmWork`) | lower | G7 | `grep -rHnE '^[[:space:]]*((public\|meta\|private)[[:space:]]+)*(import\|prelude)\b' VbmOrchestrator VbmOrchestrator.lean \| grep -vcE ':[0-9]+:import (VbmOrchestrator\|VbmWork)(\.[A-Za-z0-9_]+)*[[:space:]]*$'` | 0 (2026-11-18) | 0 | |
| `tier1-test-cases` (cases the Tier 1 test scripts ran, from `ran: tests: N cases`) | higher | G9 | `scripts/tier1.sh 2>&1 \| grep -E '^ran: tests:'` | 19 (2026-11-18; plus `axiom-gate` 1582 and `zero-warning` 3) | 19 | |
| `public-lint-violations` (findings of the public-readiness lint) | lower | G10 | `scripts/lint-public \| wc -l` | 0 (2026-11-18) | 0 | |
| `pin-verify-failures` (vendored libraries and lander not equal to their pins; 1 = fail) | lower | G11 | `.land/tool/bin/land-pin verify >/dev/null 2>&1; echo $?` and `.land/tool/bin/land-check >/dev/null 2>&1; echo $?` (sum) | 0 (2026-11-18; vbm-work v0.3.0, vbm-land v0.21.0) | 0 | |
| `tier1-seconds` (wall time of the whole gate, warm cache) | lower | G12 | `( time scripts/tier1.sh ) 2>&1 \| tail -4` | 126 (2026-11-18; `land-lean recheck` alone takes 65) | 126 | |
| `unreleased-commits` (commits on the branch since the tag of `VERSION`) | lower | G13 | `git rev-list "v$(cat VERSION)"..HEAD --count` | 0 (2026-11-18; v0.10.0) | 0 | |
| `interpreter-vectors-failing` (scenarios the application's interpreter fails) | lower | G5, G13 | the interpreter lives in the application, not here; its own tests run `vectors/vbm-orchestrator-vectors-1.jsonl` | unmeasured: needs the application's repository and its test command | unmeasured | |
| `gate-mutants-escaped` (seeded faults in the machine that the proofs and vectors do not catch) | lower | G2, G5, G9 | none in this repository; needs a mutation run over `VbmOrchestrator/Step.lean` | unmeasured: no mutant suite exists here | unmeasured | |
| `vendored-proof-modules-unchecked` (proof modules of the pinned `vbm-work` this repository has not re-checked) | lower | G6 | none; `docs/trust-ledger.md:31` plans the re-check but `.land/lean.conf` does not list `VbmWork` modules | unmeasured: needs a decision on whether `land-lean recheck` already replays the imports | unmeasured | |

## Health today

- **Regressed:** nothing can be called regressed; every floor equals the first measurement, so there is no history yet.
- **Clean on every measure the gate enforces:** no ledger gaps, no offending axiom, no forbidden construct, no warning, no import violation, no lint finding, pins intact, vectors consistent, Tier 1 passes.
- **Stale:** `stale-scenario-count-statements` is 1: docs/decisions/0001-vbm-orchestrator.md:38 says 28 scenarios, and the file has 30.
- **Unmeasured:** `interpreter-vectors-failing`, `gate-mutants-escaped` and `vendored-proof-modules-unchecked`. The first is the one that matters most for what the repository says comes next (AGENTS.md:36): the interpreter is the part that is not proved, and nothing here counts its failures.
- **Furthest from where the goals point:** `limit-claims` (1: the ports' laws, carried only by vectors and the application's tests, docs/proof-ledger.md:21), `trust-ledger-gaps` (3 of 3 entries have no written contract or no test), and `proved-claims-share-hundredths-percent` at 9230, short of 10000 only because of that one limit.
- **Not a goal-gap:** the gate takes 126 seconds, far inside the 45-minute TTL.

## What a steward would do first

1. Bring the conformance vectors to the interpreter: measure `interpreter-vectors-failing` by naming the application's test command, because the `limit` claim (`limit-claims`) and goal G5 rest entirely on it.
2. Close the trust-ledger gaps, T1 to T3 (`trust-ledger-gaps`), by writing each contract and adding a test, and decide whether the pinned `vbm-work` proofs are re-checked here (`vendored-proof-modules-unchecked`, docs/trust-ledger.md:31).
3. Fix the stale count in docs/decisions/0001-vbm-orchestrator.md (`stale-scenario-count-statements`), then raise `vectors` where the vectors' list (docs/vectors.md:41) shows a behaviour with no scenario.

## Questions for the owner

- What are the targets? The repository gives none, and the table leaves every target blank. In particular: is `limit-claims` = 1 permanent (the ports are the application's, docs/proof-ledger.md:21), or is there a target of 0?
- Should `vectors` have a target, or is it only "every behaviour in docs/vectors.md:41 has a scenario"? The repository states no count.
- Is `core-lines` a goal to keep small, or only to keep each diff within 150 lines (CONTRIBUTING.md:10)? I took the first reading; the repository states the second.
- Which application binds the machine, and what is its test command? Without it `interpreter-vectors-failing` stays unmeasured.
- What is a release for this repository? README.md:5 says pre-release and nothing is published, yet there are tags v0.7.0 to v0.10.0; should `unreleased-commits` have a target above 0?
- Is a mutation suite wanted (`gate-mutants-escaped`)? AGENTS.md:41 requires negative self-tests of the gates, but nothing seeds faults in the machine.
- Which goal does the owner want added that the repository does not state (for example, interpreter latency or the cost of a task)?
