import VbmOrchestrator.Data
/-! # The machine

`step cfg s e` is total and pure: the next state and the actions it asks for. An event that does not fit the phase changes nothing and asks for nothing. Every
way a task ends goes through `closing` (which asks for `cleanup` exactly once) and then `closed` (which reports, once, unless the run was abandoned). -/
namespace VbmOrchestrator
open VbmWork

/-- A block the machine itself authors: a harness kind and the words that say why, no citations. -/
def blockedOut (k : Kind) (reason : String) : Outcome := .blocked k reason []

/-- Enter `closing`: ask for the cleanup and wait for it. -/
def close (s : State) (o : Option Outcome) (landed : Option String := none) : State × List Action :=
  ({ s with phase := .closing o landed }, [.cleanup])

/-- The worker runs again, in the SAME session, with the whole feedback; or the money is spent. -/
def resumeOrFuse (cfg : Config) (s : State) (r : Nat) (fb : Feedback) : State × List Action :=
  if cfg.fuse ≤ s.spent then close s (some (blockedOut .fuse "the task reached its money ceiling"))
  else ({ s with phase := .working (r + 1) }, [.runAgent (r + 1) (.resume fb)])

/-- Ask the Judge whether the task is converging, with the typed facts. -/
def ask (s : State) (r : Nat) (fb : Feedback) : State × List Action :=
  ({ s with phase := .judging r fb }, [.askJudge r fb s.spent])

/-- The workspace answered: start the worker, unless there is no money at all. -/
def onPrepared (cfg : Config) (s : State) : State × List Action :=
  match decide (cfg.fuse ≤ s.spent) with
  | true => close s (some (blockedOut .fuse "the task reached its money ceiling"))
  | false => ({ s with phase := .working 1 }, [.runAgent 1 .first])

/-- The worker finished round `r` at `cost`: the money first (the sum across rounds against the fuse), then what the worker said. -/
def onWork (cfg : Config) (s : State) (r : Nat) (o : Outcome) (commit : Option String) (cost : Nat) : State × List Action :=
  let s' : State := { s with spent := s.spent + cost }
  match decide (cfg.fuse ≤ s'.spent), o, commit with
  | true, _, _ => close s' (some (blockedOut .fuse "the task reached its money ceiling"))
  | false, .done cs, some c => ({ s' with phase := .validating r ⟨c, .done cs⟩ }, [.validate c])
  | false, .doneWithAssumptions as cs, some c => ({ s' with phase := .validating r ⟨c, .doneWithAssumptions as cs⟩ }, [.validate c])
  | false, .done _, none => close s' (some (blockedOut .noProgress "the work was reported done, but nothing changed"))
  | false, .doneWithAssumptions _ _, none => close s' (some (blockedOut .noProgress "the work was reported done, but nothing changed"))
  | false, .blocked k w cs, _ => close s' (some (.blocked k w cs))
  | false, .needsClarification q d cs, _ => close s' (some (.needsClarification q d cs))

/-- The lander's `validate` answered. -/
def onValidated (cfg : Config) (s : State) (r : Nat) (d : Delivery) (v : ValidateResult) : State × List Action :=
  match v, cfg.reviewers.isEmpty with
  | .passed c, true => ({ s with phase := .pushing r d c }, [.push c])
  | .passed c, false => ({ s with phase := .reviewing r d c }, [.review c])
  | .failed rep, _ => ask s r (.checks rep)
  | .conflict rep, _ => ask s r (.conflict rep)
  | .moved, _ => ({ s with phase := .validating r d }, [.validate d.commit])
  | .refused, _ => close s (some (blockedOut .protectedPath "the change touches a path the lander protects"))
  | .unavailable why, _ => close s (some (blockedOut .runFailed (orElse why "the lander could not validate")))

/-- Every reviewer answered. -/
def onReviewed (s : State) (r : Nat) (d : Delivery) (c : String) (answers : List ReviewAnswer) : State × List Action :=
  match answers.any answerFailed, answers.flatMap answerFixes with
  | true, _ => close s (some (blockedOut .unableToReview "a reviewer could not be reached or its reply did not decode"))
  | false, [] => ({ s with phase := .pushing r d c }, [.push c])
  | false, fixes => ask s r (.findings fixes)

/-- The Judge answered whether the task is converging. -/
def onJudged (cfg : Config) (s : State) (r : Nat) (fb : Feedback) (a : JudgeAnswer) : State × List Action :=
  match a with
  | .progressing => resumeOrFuse cfg s r fb
  | .stuck => close s (some (blockedOut fb.kind fb.text))
  | .unavailable => close s (some (blockedOut fb.kind fb.text))

/-- The lander's `push` answered. -/
def onPushed (s : State) (r : Nat) (d : Delivery) (p : PushResult) : State × List Action :=
  match p with
  | .landed sha => close s (some d.outcome) (some sha)
  | .baseMoved => ({ s with phase := .validating r d }, [.validate d.commit])
  | .refused w => close s (some (blockedOut .runFailed (orElse w "the push was refused")))

def step (cfg : Config) (s : State) (e : Event) : State × List Action :=
  match s.phase, e with
  | .closed, _ => (s, [])
  | .closing o l, .cleaned =>
      ({ s with phase := .closed }, match o with | some o => [.report o l] | none => [])
  | .closing _ _, _ => (s, [])
  | _, .leaseLost => close s none
  | _, .deadline => close s (some (blockedOut .timeout "the wall deadline was reached"))
  | .preparing, .preparedOk => onPrepared cfg s
  | .preparing, .preparedFailed w =>
      close s (some (blockedOut .runFailed (orElse w "the workspace could not be prepared")))
  | .working r, .agentFinished o commit cost => onWork cfg s r o commit cost
  | .validating r d, .validated v => onValidated cfg s r d v
  | .reviewing r d c, .reviewed answers => onReviewed s r d c answers
  | .judging r fb, .judged a => onJudged cfg s r fb a
  | .pushing r d _, .pushed p => onPushed s r d p
  | _, _ => (s, [])

/-- The machine before its first event: preparing, and the workspace is asked for. -/
def start : State × List Action := ({ phase := .preparing, spent := 0 }, [.prepare])

/-- Feed events in order; the actions in the order they were asked. -/
def run (cfg : Config) : State → List Event → State × List Action
  | s, [] => (s, [])
  | s, e :: es =>
      let r := step cfg s e
      let t := run cfg r.1 es
      (t.1, r.2 ++ t.2)

end VbmOrchestrator
