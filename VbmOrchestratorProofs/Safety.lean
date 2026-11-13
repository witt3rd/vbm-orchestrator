import VbmOrchestratorProofs.Run
/-! # The machine: what it never does

A task lands only a `done`-type outcome; the deadline and a lost lease always close it; and the worker runs at most `fuse` times, because every round costs at least
a picodollar and the machine asks for a run only while the sum is below the fuse. There is no count of rounds anywhere in the machine: money ends it. -/
namespace VbmOrchestrator
open VbmWork

/-- The outcomes a task may land: the worker said it was done. -/
def outcomeIsDone : Outcome → Bool
  | .done _ => true
  | .doneWithAssumptions _ _ => true
  | _ => false

/-- Well formed: the delivery a phase carries past the worker is a done-type outcome, and so is the outcome of a task closing with a landed commit. -/
def Phase.wf : Phase → Prop
  | .validating _ d => outcomeIsDone d.outcome = true
  | .reviewing _ d _ => outcomeIsDone d.outcome = true
  | .pushing _ d _ => outcomeIsDone d.outcome = true
  | .closing (some o) (some _) => outcomeIsDone o = true
  | _ => True

theorem step_wf (cfg : Config) (s : State) (e : Event) (h : s.phase.wf) : (step cfg s e).1.phase.wf := by
  obtain ⟨s', acts, hs⟩ : ∃ s' acts, step cfg s e = (s', acts) := ⟨_, _, rfl⟩
  rw [hs]
  step_split hs
  all_goals simp_all [Phase.wf, outcomeIsDone]

theorem start_wf : start.1.phase.wf := by simp [start, Phase.wf]

/-- **A task reports a landed commit only with a done-type outcome**: the worker said it was done, the lander validated, the reviewers cleared it. -/
theorem landed_report_is_done (cfg : Config) (s s' : State) (e : Event) (acts : List Action) (o : Outcome) (sha : String)
    (hw : s.phase.wf) (hs : step cfg s e = (s', acts)) (h : Action.report o (some sha) ∈ acts) : outcomeIsDone o = true := by
  have := report_origin cfg s s' e acts o (some sha) hs h
  rw [this.1] at hw
  simpa [Phase.wf] using hw

/-- **The deadline always closes a task that had not finished**, asking for the cleanup. -/
theorem deadline_closes (cfg : Config) (s : State) (h : s.phase.finished = false) :
    (step cfg s .deadline).1.phase.isClosing = true ∧ (step cfg s .deadline).2 = [.cleanup] := by
  obtain ⟨s', acts, hs⟩ : ∃ s' acts, step cfg s .deadline = (s', acts) := ⟨_, _, rfl⟩
  rw [hs]
  step_cases hs

/-- **A lost lease always closes a task that had not finished**, asking for the cleanup and reporting nothing (the task belongs to another host now). -/
theorem lease_lost_closes (cfg : Config) (s : State) (h : s.phase.finished = false) :
    (step cfg s .leaseLost).1.phase = .closing none none ∧ (step cfg s .leaseLost).2 = [.cleanup] := by
  obtain ⟨s', acts, hs⟩ : ∃ s' acts, step cfg s .leaseLost = (s', acts) := ⟨_, _, rfl⟩
  rw [hs]
  step_cases hs

/-! ## The bound from the money -/

/-- A round costs at least one picodollar (a law of the agent port: an unpriceable call stops the run). -/
def Event.costOk : Event → Prop
  | .agentFinished _ _ c => 1 ≤ c
  | _ => True

/-- `k` worker runs have been asked for. -/
def Inv (cfg : Config) (s : State) (k : Nat) : Prop :=
  k ≤ cfg.fuse ∧ (match s.phase with
    | .preparing => k = 0
    | .working _ => k ≤ s.spent + 1
    | .validating _ _ => k ≤ s.spent
    | .reviewing _ _ _ => k ≤ s.spent
    | .pushing _ _ _ => k ≤ s.spent
    | .judging _ _ => k ≤ s.spent
    | .closing _ _ => True
    | .closed => True)

theorem step_inv (cfg : Config) (s : State) (e : Event) (k : Nat) (hi : Inv cfg s k) (he : e.costOk) :
    Inv cfg (step cfg s e).1 (k + count Action.isRun (step cfg s e).2) := by
  obtain ⟨s', acts, hs⟩ : ∃ s' acts, step cfg s e = (s', acts) := ⟨_, _, rfl⟩
  rw [hs]
  step_split hs
  all_goals simp_all [Inv, Event.costOk, count, Action.isRun]
  all_goals omega

/-- **The worker runs at most `fuse` times, whatever the Judge answers**: no count of rounds ends a task, the money does. -/
theorem runs_le_fuse (cfg : Config) (es : List Event) :
    ∀ (s : State) (k : Nat), Inv cfg s k → (∀ e ∈ es, e.costOk) → k + count Action.isRun (run cfg s es).2 ≤ cfg.fuse := by
  induction es with
  | nil => intro s k hi _; simp [run, count]; exact hi.1
  | cons e es ih =>
    intro s k hi hall
    rw [run_cons, count_append]
    have h1 := step_inv cfg s e k hi (hall e (by simp))
    have h2 := ih (step cfg s e).1 (k + count Action.isRun (step cfg s e).2) h1 (fun e' he' => hall e' (by simp [he']))
    omega

theorem start_inv (cfg : Config) : Inv cfg start.1 0 := by
  simp [Inv, start]

/-- **From the start, the worker is asked to run at most `fuse` times** (given every round costs at least a picodollar). -/
theorem rounds_le_fuse (cfg : Config) (es : List Event) (hall : ∀ e ∈ es, e.costOk) :
    count Action.isRun (run cfg start.1 es).2 ≤ cfg.fuse := by
  have := runs_le_fuse cfg es start.1 0 (start_inv cfg) hall
  omega

end VbmOrchestrator
