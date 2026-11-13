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

def step (cfg : Config) (s : State) (e : Event) : State × List Action :=
  match s.phase, e with
  | .closed, _ => (s, [])
  | .closing o l, .cleaned =>
      ({ s with phase := .closed }, match o with | some o => [.report o l] | none => [])
  | .closing _ _, _ => (s, [])
  | _, .leaseLost => close s none
  | _, .deadline => close s (some (blockedOut .timeout "the wall deadline was reached"))
  | .preparing, .preparedOk =>
      if cfg.fuse ≤ s.spent then close s (some (blockedOut .fuse "the task reached its money ceiling"))
      else ({ s with phase := .working 1 }, [.runAgent 1 .first])
  | .preparing, .preparedFailed w =>
      close s (some (blockedOut .runFailed (orElse w "the workspace could not be prepared")))
  | .working r, .agentFinished o commit cost =>
      let s' : State := { s with spent := s.spent + cost }
      if cfg.fuse ≤ s'.spent then close s' (some (blockedOut .fuse "the task reached its money ceiling"))
      else match o with
        | .done _ | .doneWithAssumptions _ _ =>
            match commit with
            | some c => ({ s' with phase := .validating r ⟨c, o⟩ }, [.validate c])
            | none => close s' (some (blockedOut .noProgress "the work was reported done, but nothing changed"))
        | .blocked _ _ _ | .needsClarification _ _ _ => close s' (some o)
  | .validating r d, .validated (.passed c) =>
      if cfg.reviewers.isEmpty then ({ s with phase := .pushing r d c }, [.push c])
      else ({ s with phase := .reviewing r d c }, [.review c])
  | .validating r _, .validated (.failed rep) => ask s r (.checks rep)
  | .validating r _, .validated (.conflict rep) => ask s r (.conflict rep)
  | .validating _ _, .validated .refused =>
      close s (some (blockedOut .protectedPath "the change touches a path the lander protects"))
  | .reviewing r d c, .reviewed answers =>
      if answers.any answerFailed then
        close s (some (blockedOut .unableToReview "a reviewer could not be reached or its reply did not decode"))
      else
        match answers.flatMap answerFixes with
        | [] => ({ s with phase := .pushing r d c }, [.push c])
        | fixes => ask s r (.findings fixes)
  | .judging r fb, .judged .progressing => resumeOrFuse cfg s r fb
  | .judging _ fb, .judged _ => close s (some (blockedOut fb.kind fb.text))
  | .pushing _ d _, .pushed (.landed sha) => close s (some d.outcome) (some sha)
  | .pushing r d _, .pushed .baseMoved => ({ s with phase := .validating r d }, [.validate d.commit])
  | .pushing _ _ _, .pushed (.refused w) =>
      close s (some (blockedOut .runFailed (orElse w "the push was refused")))
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
