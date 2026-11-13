import VbmWork.Outcome
import VbmWork.Review
/-! # The orchestrator's data

What a run is configured with, what its ports answer (the events), what it asks of them (the actions), and the phases between. Pure data over `Init` and the
vocabulary package (`VbmWork`): no input or output, no clock, no model. `VbmOrchestrator.Step` is the machine and `VbmOrchestratorProofs` what is proved of it. -/
namespace VbmOrchestrator
open VbmWork

/-- What a run is configured with, constant for the run. `fuse` is an absolute ceiling on the money one task may cost, summed over every round, in picodollars (exact
arithmetic): a money-safety limit that protects against a runaway spend, which nothing extends. There is no cap on rounds and none on revalidations: whether a
failing task is still converging is a judgment, a decision model's, and the fuse and a wall deadline are the only hard stops. `reviewers` names the reviewer
definitions the lander supplies (possibly none). -/
structure Config where
  fuse : Nat
  reviewers : List String
  deriving DecidableEq, Repr

/-- A configuration with a fuse that allows at least one picodollar. -/
def Config.ok (c : Config) : Bool := decide (0 < c.fuse)

/-- Why a repair round is wanted, always WHOLE (never a digest): the checks' report, the conflict's report, or every `fix` finding of every reviewer. -/
inductive Feedback where
  | checks (report : String)
  | conflict (report : String)
  | findings (fixes : List Finding)
  deriving DecidableEq, Repr

/-- The kind of block a failure closes the task in when it cannot be repaired: what the requester can act on. -/
def Feedback.kind : Feedback → Kind
  | .checks _ => .checksFailed
  | .conflict _ => .conflictUnresolved
  | .findings _ => .reviewFindings

/-- The findings as text, one per line. -/
def renderFindings : List Finding → String
  | [] => ""
  | f :: fs => f.declaration ++ ": " ++ f.why ++ (match fs with | [] => "" | _ => "\n" ++ renderFindings fs)

/-- The text itself, or the stated default when it says nothing: a block always says why (`Outcome.ok`). -/
def orElse (s d : String) : String := if fullOk s then s else d

/-- The words that close a task for a failure: the failure's own text, whole. -/
def Feedback.text : Feedback → String
  | .checks r => orElse r "the checks failed"
  | .conflict r => orElse r "the change conflicts with the base"
  | .findings fs => orElse (renderFindings fs) "a reviewer found a defect"

/-- What the lander's `validate` answers: the rebased commit it tested and found good, red checks, a conflict, or a refusal (a protected path: never repairable). -/
inductive ValidateResult where
  | passed (commit : String)
  | failed (report : String)
  | conflict (report : String)
  | refused
  deriving DecidableEq, Repr

/-- What the lander's `push` of exactly the validated commit answers. A moved base is not a failure: someone else landed, the system advanced. -/
inductive PushResult where
  | landed (sha : String)
  | baseMoved
  | refused (words : String)
  deriving DecidableEq, Repr

/-- What the Judge answers to "is this task converging?". An unreachable judge, or a reply that did not decode, is `unavailable`, which the machine reads as `stuck`:
the decision fails closed. -/
inductive JudgeAnswer where
  | progressing
  | stuck
  | unavailable
  deriving DecidableEq, Repr

/-- One reviewer's answer: its findings, or that its reply could not be decoded. -/
abbrev ReviewAnswer := Except DecodeError Review

/-- Could not be decoded. -/
def answerFailed : ReviewAnswer → Bool
  | .error _ => true
  | .ok _ => false

/-- The findings a reviewer rated `fix`. -/
def answerFixes : ReviewAnswer → List Finding
  | .error _ => []
  | .ok r => r.filter fun f => f.severity == .fix

/-- What the worker delivered: the commit its harness made, and its typed outcome (`done` or `doneWithAssumptions`). -/
structure Delivery where
  commit : String
  outcome : Outcome
  deriving DecidableEq, Repr

/-- The events: typed data only, never a log line. -/
inductive Event where
  | preparedOk
  | preparedFailed (words : String)
  | agentFinished (outcome : Outcome) (commit : Option String) (cost : Nat)
  | validated (r : ValidateResult)
  | reviewed (answers : List ReviewAnswer)
  | judged (a : JudgeAnswer)
  | pushed (r : PushResult)
  | cleaned
  | leaseLost
  | deadline
  deriving Repr

inductive Phase where
  | preparing
  | working (round : Nat)
  | validating (round : Nat) (d : Delivery)
  | judging (round : Nat) (fb : Feedback)
  | reviewing (round : Nat) (d : Delivery) (validated : String)
  | pushing (round : Nat) (d : Delivery) (validated : String)
  /-- Closing: `cleanup` has been asked. The outcome is `none` when the run was ABANDONED (the lease was lost: another host owns the task, so this machine cleans up and reports nothing). -/
  | closing (outcome : Option Outcome) (landed : Option String)
  | closed
  deriving DecidableEq, Repr

/-- The state: the phase and `spent`, the sum of what every round reported it cost. -/
structure State where
  phase : Phase
  spent : Nat
  deriving DecidableEq, Repr

/-- How the worker is asked to run: its first session, or the SAME session continued with the whole feedback. -/
inductive AgentMode where
  | first
  | resume (fb : Feedback)
  deriving DecidableEq, Repr

/-- The actions: what the interpreter performs through a port. -/
inductive Action where
  | prepare
  | runAgent (round : Nat) (mode : AgentMode)
  | askJudge (round : Nat) (fb : Feedback) (spent : Nat)
  | validate (commit : String)
  | review (commit : String)
  | push (commit : String)
  | cleanup
  | report (outcome : Outcome) (landed : Option String)
  deriving DecidableEq, Repr

end VbmOrchestrator
