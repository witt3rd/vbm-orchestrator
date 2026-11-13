# The conformance vectors (`vbm-orchestrator-vectors-1`)

`vectors/vbm-orchestrator-vectors-1.jsonl`: one JSON object per line, one scenario per line, generated from the Lean machine itself (`scripts/test_vectors.sh --write`), so they cannot drift from it. Any language can read them. They are the checklist for the part of a system that is NOT proved: the interpreter that turns the machine's actions into calls of real ports and the ports' answers into events.

## A scenario

```
{"name": "repair-after-red-checks",
 "config": {"fuse": 10, "reviewers": []},
 "start": [ {"action": "prepare"} ],
 "steps": [ {"event": {"event": "preparedOk"}, "asks": [ {"action": "runAgent", "round": 1, "session": {"mode": "first"}} ]}, ... ],
 "final": {"phase": {"phase": "closed"}, "spent": 5}}
```

- `config`: the run's configuration: `fuse` (the money ceiling in picodollars, summed over every round) and `reviewers` (the names of the reviewer definitions the lander supplies).
- `start`: what the machine asks for before any event (always `prepare`).
- `steps`: in order, an `event` the world raises and `asks`, what the machine then asks for (zero or one action).
- `final`: the phase the run ends in and the money spent.

## The port discipline: what an interpreter must do to conform

Every action asks one port; the event that follows answers it:

| the machine asks | the port | the answering event |
|---|---|---|
| `prepare` | the workspace | `preparedOk` or `preparedFailed` |
| `runAgent` (round, `first` or `resume` with the whole feedback) | the worker agent | `agentFinished` (its typed outcome, the commit it made or null, the cost) |
| `askJudge` | the decision model | `judged` (`progressing`, `stuck` or `unavailable`) |
| `validate` | the lander's validate step | `validated` (`passed` with the rebased commit, `failed`, `conflict`, `refused`, or `unavailable` with the reason: the lander could not validate for a reason that is not the task's) |
| `review` | the reviewers (read-only, given the diff up front) | `reviewed` (one answer per reviewer: its findings, or undecodable) |
| `push` | the lander's push step | `pushed` (`landed` with the sha, `baseMoved`, `refused`) |
| `cleanup` | the workspace | `cleaned` |
| `report` | the requester | none: the run is over |

Two events are not answers: `leaseLost` (the task now belongs to another host) and `deadline` (the wall clock): the world raises them at any point. After one of them the machine asks for `cleanup`.

**An interpreter conforms to a scenario when, with its ports scripted to answer the events in order (an answering event when the call returns, an external event at its place), it makes exactly the calls `asks` lists, in order, and reports what `report` says.** Its decisions are not its own: it never chooses to repair, to give up, to review or to push; it performs what the machine asks and reports what the port answered. That it reads no text to decide is the machine's theorem; that its own translation of a port's answer into an event is exact is what these vectors test.

## What each scenario shows

Success with and without reviewers; a repair after red checks, after a conflict and after a reviewer's finding (the SAME session continues with the whole feedback, round 2); two repairs; the Judge stopping a task (it closes as the kind of its last failure, with the failure whole) and an unreachable Judge read as stuck; an unreachable reviewer (nothing lands, nothing is repaired); the worker's own `blocked` and `needsClarification` passed through; a worker that says done and changed nothing; a refused protected path; a lander that could not validate at all (held, the base kept moving, a fetch failed); the money ceiling at the first round and inside a repair; the deadline; a lost lease (it cleans up and reports nothing); a workspace that could not be prepared; a push the remote refuses; a moved base re-validated twice, and a moved base whose re-validation fails and is repaired.

## Reading and writing them

The wire library (`VbmOrchestratorWire`, a binding that may import `Lean`) encodes and decodes every event and action; a decoder never repairs or guesses (a word that names no event, no kind, no severity is an error). The vectors are its conformance test: `vbm-orchestrator-vectors --roundtrip FILE` decodes every line and encodes it back, and it must equal the line.

## Stability

The `-1` names this format. A change to the machine or to a scenario changes the file, `scripts/test_vectors.sh` fails until the file is regenerated with `--write`, and the diff is the review. A change that alters the meaning of an existing line is a new format version, not an edit.
