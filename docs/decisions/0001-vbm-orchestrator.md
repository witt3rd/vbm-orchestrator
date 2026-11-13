# 0001: vbm-orchestrator: the task cycle as a pure state machine

Status: accepted 2026-11-12. The machine and its proofs (S1); non-interference (S2); the reference model and the conformance vectors (S3). Complete as a specification.

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
2. A task reports at most once, only when its closing finishes; an abandoned task (a lost lease) reports nothing.
3. A task asks for its cleanup exactly once on every path (including a failed preparation and an abandoned run), and when it finishes it has asked.
4. A push is asked for only after the lander validated the commit, and after every reviewer answered and none found a defect (or there are no reviewers).
5. A task lands only a done-type outcome: the worker said it was done.
6. The worker's first run is round 1; it runs again, in the same session with the whole feedback, only after the Judge said `progressing` and while the money is below the fuse.
7. A reviewer that could not be reached never lets the task land or repair: it closes as `unableToReview`.
8. The deadline and a lost lease always close a task that had not finished, asking for the cleanup.
9. **The worker runs at most `fuse` times, whatever the Judge answers**, given every round costs at least a picodollar: no count of rounds ends a task, the money does.

The witnesses (`VbmOrchestratorProofs/Witnesses.lean`, and the last example of `Shape.lean`: two runs whose events differ in every text) are whole runs, computed: a full success, a repair the Judge allows, a task it stops, an unreachable judge read as `stuck`, the money ceiling, an unreachable reviewer, a lost lease, a moved base re-validated. They show each hypothesis can hold.

10. **Control never depends on prose (non-interference)**: two states and two events with the same typed shape (the same constructors, kinds of block, counts and numbers, whatever their texts) give results of the same shape; so two runs over events of the same shape ask for the same actions, up to their texts, and end in the same phase. The machine copies text, it never reads it.

11. **The reference model is the machine under the port discipline**: `drive` computes exactly what `run` computes, and refuses a sequence of events that answers no pending action or that the machine would ignore.
12. **Every conformance scenario obeys that discipline**, so each vector is a run a correct interpreter can meet.

**The conformance vectors** (`vectors/vbm-orchestrator-vectors-1.jsonl`, 28 scenarios, format in `docs/vectors.md`) are generated from the machine and checked in; they are the checklist for the interpreter, the part that is not proved.

## What is not decided here

The ports' contracts (the workspace, the agent, the lander's two steps, the reviewers, the judge) are stated as the laws the machine relies on; their implementations are bindings of the application. What the Judge is shown and how its question is worded is the Judge port's contract, calibrated on the application's own history.

## Rules

`VbmOrchestrator` imports `Init`, itself and `VbmWork` only. `VbmOrchestratorProofs` may import `Std` and `Lean` and is never linked, and nothing in `VbmOrchestrator` may import it. No `sorry`, `admit`, `axiom`, `unsafe`, `implemented_by` or `csimp`. Gates and landing are those of the VBM family (`AGENTS.md`).
