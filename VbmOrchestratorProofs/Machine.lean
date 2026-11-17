import VbmOrchestrator
/-! # The machine: step-level proofs

What each action can come from, stated of one step (`step cfg s e = (s', acts)`). The run-level facts (exactly one report, cleanup exactly once, the bound from the
fuse) follow from these. -/
namespace VbmOrchestrator
open VbmWork

/-- Has the task finished (closing or closed)? -/
def Phase.finished : Phase → Bool
  | .closing _ _ => true
  | .closed => true
  | _ => false

def Phase.isClosing : Phase → Bool
  | .closing _ _ => true
  | _ => false

/-- A phase that is neither `closed` nor `closing` has not finished. -/
theorem Phase.finished_eq_false {p : Phase} (h1 : p ≠ .closed) (h2 : ∀ o l, p ≠ .closing o l) : p.finished = false := by
  cases p <;> simp_all [Phase.finished]

/-- Case-split the machine's equation `hs : step cfg s e = (s', acts)` arm by arm (the match, then the `if`s and matches inside an arm), unfold the helpers, and
substitute the result. -/
macro "step_split " hs:ident : tactic =>
  `(tactic| (unfold step at $hs:ident
             split at $hs:ident
             all_goals (try simp only [onPrepared, onWork, onValidated, onReviewed, onJudged, onPushed, close, ask, resumeOrFuse, feedback] at $hs:ident)
             all_goals (repeat' (split at $hs:ident))
             all_goals (try simp only [Prod.mk.injEq] at $hs:ident)
             all_goals (try (obtain ⟨hs1, hs2⟩ := $hs:ident; subst hs1; subst hs2))))

/-- `step_split`, then close each arm with the facts about phases. -/
macro "step_cases " hs:ident : tactic =>
  `(tactic| (step_split $hs:ident
             all_goals simp_all [Phase.finished_eq_false, Phase.isClosing, Phase.finished]))

/-- **Closed is absorbing**: nothing is asked for and nothing changes. -/
theorem step_closed (cfg : Config) (s : State) (e : Event) (h : s.phase = .closed) : step cfg s e = (s, []) := by
  simp [step, h]

/-- **An abandoned run reports nothing.** -/
theorem abandoned_reports_nothing (cfg : Config) (s : State) (l : Option String) (h : s.phase = .closing none l) :
    (step cfg s .cleaned).2 = [] := by
  simp [step, h]

/-- **A report comes only from finishing the close**: the phase was `closing (some o) l` and the event `cleaned`. -/
theorem report_origin (cfg : Config) (s s' : State) (e : Event) (acts : List Action) (o : Outcome) (l : Option String)
    (hs : step cfg s e = (s', acts)) (h : Action.report o l ∈ acts) : s.phase = .closing (some o) l ∧ e = .cleaned := by
  step_cases hs

/-- **Cleanup is asked for only when a task enters closing**, never when it was already finishing. -/
theorem cleanup_origin (cfg : Config) (s s' : State) (e : Event) (acts : List Action)
    (hs : step cfg s e = (s', acts)) (h : Action.cleanup ∈ acts) :
    s.phase.finished = false ∧ s'.phase.isClosing = true := by
  step_cases hs

/-- **Entering closing asks for the cleanup, once** (and only that). -/
theorem entering_closing_cleans (cfg : Config) (s s' : State) (e : Event) (acts : List Action)
    (hs : step cfg s e = (s', acts)) (hf : s.phase.finished = false) (h : s'.phase.isClosing = true) : acts = [.cleanup] := by
  step_cases hs

/-- **A push is asked for only after the lander validated the commit, and the reviewers cleared it**: either there are no reviewers and the validation just passed, or
every reviewer answered, none could not be decoded, and none found a `fix`. -/
theorem push_origin (cfg : Config) (s s' : State) (e : Event) (acts : List Action) (c : String)
    (hs : step cfg s e = (s', acts)) (h : Action.push c ∈ acts) :
    (∃ r d, s.phase = .validating r d ∧ e = .validated (.passed c) ∧ cfg.reviewers = []) ∨
    (∃ r d answers, s.phase = .reviewing r d c ∧ e = .reviewed answers ∧
        answers.any answerFailed = false ∧ answers.flatMap answerFixes = []) := by
  step_cases hs

/-- **The worker's first run is round 1**, asked for only by a preparation that succeeded, while the money is below the fuse. -/
theorem first_run_origin (cfg : Config) (s s' : State) (e : Event) (acts : List Action) (r : Nat)
    (hs : step cfg s e = (s', acts)) (h : Action.runAgent r .first ∈ acts) :
    r = 1 ∧ s.phase = .preparing ∧ e = .preparedOk ∧ s.spent < cfg.fuse := by
  step_cases hs
  all_goals (try omega)

/-- **A failure of the FIRST round**: the phase is the first round's validation or review, and the event is the failure that phase can answer with, whose feedback is `fb`. -/
def FirstFailure (p : Phase) (e : Event) (fb : Feedback) : Prop :=
  (∃ d rep, p = .validating 1 d ∧ ((e = .validated (.failed rep) ∧ fb = .checks rep) ∨ (e = .validated (.conflict rep) ∧ fb = .conflict rep))) ∨
  (∃ d c answers, p = .reviewing 1 d c ∧ e = .reviewed answers ∧ answers.any answerFailed = false ∧ answers.flatMap answerFixes ≠ [] ∧ fb = .findings (answers.flatMap answerFixes))

/-- **The worker runs again, in the same session, with the whole feedback, only after the Judge said `progressing`, or on the failure of the first round (feedback, not a verdict:
one failed attempt cannot show the rounds are not converging), and in both cases only while the money is below the fuse.** The round is the failed round plus one. -/
theorem resume_origin (cfg : Config) (s s' : State) (e : Event) (acts : List Action) (r : Nat) (fb : Feedback)
    (hs : step cfg s e = (s', acts)) (h : Action.runAgent r (.resume fb) ∈ acts) :
    ∃ q, r = q + 1 ∧ ((s.phase = .judging q fb ∧ e = .judged .progressing) ∨ (q = 1 ∧ FirstFailure s.phase e fb)) ∧ s.spent < cfg.fuse := by
  step_cases hs
  all_goals (try omega)
  all_goals (try (simp [FirstFailure]; done))
  all_goals (try (unfold FirstFailure; refine Or.inr ⟨_, _, _, rfl, rfl, ?_, ?_, rfl⟩ <;> simp_all [List.flatMap_eq_nil_iff]; done))

/-- **The FIRST round's failed checks resume the worker at once**, with no Judge: the same session, round 2, the whole report, while the money is below the fuse. -/
theorem first_failure_resumes (cfg : Config) (s : State) (d : Delivery) (rep : String) (hp : s.phase = .validating 1 d) (hm : s.spent < cfg.fuse) :
    step cfg s (.validated (.failed rep)) = ({ s with phase := .working 2 }, [.runAgent 2 (.resume (.checks rep))]) := by
  simp [step, hp, onValidated, feedback, resumeOrFuse, Nat.not_le.mpr hm]

/-- **A failure after the first round asks the Judge** (the facts the Judge reads are the failure, the round and the money so far). -/
theorem later_failure_asks (cfg : Config) (s : State) (r : Nat) (d : Delivery) (rep : String) (hp : s.phase = .validating r d) (hr : r ≠ 1) :
    step cfg s (.validated (.failed rep)) = ({ s with phase := .judging r (.checks rep) }, [.askJudge r (.checks rep) s.spent]) := by
  simp [step, hp, onValidated, feedback, hr, ask]

/-- **An unreachable reviewer never lets the task land or repair**: the task closes as `unableToReview` and asks for nothing but the cleanup. -/
theorem unreviewed_closes (cfg : Config) (s : State) (r : Nat) (d : Delivery) (c : String) (answers : List ReviewAnswer)
    (hp : s.phase = .reviewing r d c) (hf : answers.any answerFailed = true) :
    step cfg s (.reviewed answers) =
      ({ s with phase := .closing (some (blockedOut .unableToReview "a reviewer could not be reached or its reply did not decode")) none }, [.cleanup]) := by
  simp [step, hp, hf, onReviewed, close]

end VbmOrchestrator
