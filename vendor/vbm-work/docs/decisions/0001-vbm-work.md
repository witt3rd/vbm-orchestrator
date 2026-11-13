# 0001: vbm-work: the vocabulary of work

Status: accepted 2026-11-12. S1 (the outcome and the review words) in v0.1.0; S2 (the task, the change class, the cycle's closing kinds) in v0.2.0; S3 adds `timeout` in v0.3.0.

## What it is

The words two machines share. A **task** goes in; a **typed outcome** comes out; between them a **review** returns typed findings. `vbm-work` is that vocabulary
and the small decision tables over it, in Lean 4, machine-checked. It is pure data and total functions over `Init`: no input or output, no wire format, no model
call, no storage, no dependency. A machine that schedules work (a dispatcher) and a machine that carries one task through its cycle (an orchestrator) both
depend on it and on nothing of each other's.

It decides nothing about what to do next. It says what a run's end can be, what makes one well formed, what a reviewer may return and what a round's
review comes to. Reading a reply into findings, encoding an outcome as JSON, storing either: those are bindings, and live with the application.

## The slice (S1)

1. **The outcome** (`VbmWork.Outcome`): four tags (`done`, `doneWithAssumptions`, `blocked`, `needsClarification`), nineteen kinds of block, each with one wire
   word; the citation of a tool result; the outcome; and `Outcome.ok`, what makes one well formed.
2. **The review words** (`VbmWork.Review`): `Severity` (`fix`, `note`), `Finding`, `Review`, `Verdict` (`clean`, `notes`, `blocked`, `unreviewed`), and the
   verdict of a review and of a reply that may not have decoded.

3. **The task** (`VbmWork.Task`, S2): what is asked of one orchestrator run: an id, the project, the intent, how it is checked, file hints and the `ChangeClass` (docs, impl, spec, tightening, loosening, trustedC, infra, scout: how far the change may reach, which decides the checks it must pass), with what makes a task well formed. Scheduling facts (priority, keys, dependencies, needs) are NOT the task: they belong to the machine that schedules.
4. **Five kinds of block the orchestrator's cycle closes in** (S2, S3): `checksFailed`, `reviewFindings`, `unableToReview`, `conflictUnresolved`, and `timeout` (the wall deadline): new words, the harness's own, never claimed by a model. Running out of rounds is not a kind: a task that exhausts its rounds closes as the kind of its last failure.

## What is proved (`VbmWorkProofs`, one row per claim in `docs/proof-ledger.md`)

- The alphabets are closed; each word names one tag or kind, a word names at most one, and a word that names none is refused: nothing is guessed, there is no default.
- The model may claim exactly six of the nineteen kinds; the other eight are the harness's own.
- An outcome is well formed exactly when its text says something: a block says why, an assumption is stated, a question has a default, a citation names its call.
- A review blocks exactly when it has a `fix`; notes alone never block; the empty review is clean.
- A reply that could not be decoded is `unreviewed`, no review has that verdict, and it is never an approval.

Each conditional theorem has a witness that its hypothesis can hold.

## What is not proved, and why it is honest

The wire words are the words an existing journal already holds, kept exactly. That a given journal still decodes is a property of the consumer's codec, not of this
vocabulary (a `limit` in the ledger: carried by the consumer's own tests). Fidelity of the wording to the way a requester reads it is review, not proof.

## What comes next (each its own slice, each with a consumer)

- The task: what is asked (class, priority, serialisation keys, dependencies, needs), when the orchestrator's input contract is specified.
- One list of the kinds of block: the harness-side kinds an application keeps elsewhere join the nineteen by expand-and-contract; the wire words do not change.

## Rules

`VbmWork` imports `Init` and itself only. `VbmWorkProofs` may import `Std` and `Lean` and is never linked. No `sorry`, `admit`, `axiom`, `unsafe`, `implemented_by`
or `csimp` (Tier 1 scans for them). Gates and landing are those of the VBM family (`AGENTS.md`).
