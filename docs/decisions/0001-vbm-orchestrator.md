# 0001: vbm-orchestrator: the task cycle as a pure state machine

Status: accepted 2026-11-12. The machine and its first proofs (S1); the reference model and the conformance vectors follow (S2).

## What it is

`step : Config → State → Event → State × List Action`, total and pure. A run starts in `preparing` (asking for the workspace) and every way it can end passes through
`closing` (which asks for `cleanup`) and then `closed` (which reports once, unless the run was abandoned). An event that does not fit the phase changes nothing.

- **Config**: `fuse`, an absolute money ceiling for the task summed over every round (a money-safety limit: it protects against a runaway spend, and nothing extends it), and `reviewers`, the names of the reviewer definitions the lander supplies. **There is no cap on rounds and none on revalidations**: whether a failing task is still converging is a judgment (a decision model's), and the fuse and a wall deadline are the only hard stops.
- **Phases**: `preparing`, `working r`, `validating r d`, `judging r feedback`, `reviewing r d commit`, `pushing r d commit`, `closing outcome? landed?`, `closed`. A `Delivery` (the worker's commit and its typed outcome) rides along from the moment the worker finishes, so there is no state in which the outcome is missing when it is time to land.
- **Events**: `preparedOk`, `preparedFailed`, `agentFinished outcome commit cost`, `validated`, `reviewed`, `judged`, `pushed`, `cleaned`, `leaseLost`, `deadline`. All typed.
- **Actions**: `prepare`, `runAgent round (first | resume feedback)`, `askJudge`, `validate`, `review`, `push`, `cleanup`, `report`.

The words are those of `vbm-work`: the worker's outcome is its typed `Outcome`; a failure the task cannot recover from closes as a block of the kind of its last failure
(`checksFailed`, `conflictUnresolved`, `reviewFindings`), a reviewer that could not be reached as `unableToReview`, a refusal of a protected path as `protectedPath`, the money ceiling as `fuse`,
the wall deadline as `timeout`.

## What is proved (`VbmOrchestratorProofs`; one row per claim in `docs/proof-ledger.md`)

1. Closed is absorbing: nothing is done after it.
2. A report is asked for only when closing finishes, and the abandoned run reports nothing.
3. Cleanup is asked for exactly when a task enters closing, and a task enters it once.
4. A push is asked for only after the lander validated the commit, and after every reviewer answered and none found a defect.
5. The worker is asked to run again, in the same session, with the whole feedback, only after the Judge said `progressing` and while the money is below the fuse; its first run is round 1.
6. A reviewer that could not be reached never lets the task land or repair.
7. Control never depends on prose: erasing every text of an event changes neither the next phase nor the kinds of the actions.

Each conditional theorem has a witness that its hypothesis can hold.

## What is not decided here

The ports' contracts (the workspace, the agent, the lander's two steps, the reviewers, the judge) are stated as the laws the machine relies on; their implementations are bindings of the application. What the Judge is shown and how its question is worded is the Judge port's contract, calibrated on the application's own history.

## Rules

`VbmOrchestrator` imports `Init`, itself and `VbmWork` only. `VbmOrchestratorProofs` may import `Std` and `Lean` and is never linked, and nothing in `VbmOrchestrator` may import it. No `sorry`, `admit`, `axiom`, `unsafe`, `implemented_by` or `csimp`. Gates and landing are those of the VBM family (`AGENTS.md`).
