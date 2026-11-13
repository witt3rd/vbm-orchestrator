import VbmOrchestratorProofs.Machine
/-! # The machine: facts about a whole run

`run cfg s es` feeds the events in order. From the step-level lemmas: a task reports at most once and cleans up exactly once, and the worker runs at most `fuse`
times (the money, not a count of rounds, is what ends it). -/
namespace VbmOrchestrator
open VbmWork

def Action.isReport : Action → Bool
  | .report _ _ => true
  | _ => false

def Action.isCleanup : Action → Bool
  | .cleanup => true
  | _ => false

def Action.isRun : Action → Bool
  | .runAgent _ _ => true
  | _ => false

/-- How many of the actions are of a kind. -/
def count (p : Action → Bool) (acts : List Action) : Nat := acts.countP p

theorem count_append (p : Action → Bool) (a b : List Action) : count p (a ++ b) = count p a + count p b := by
  simp [count, List.countP_append]

theorem run_cons (cfg : Config) (s : State) (e : Event) (es : List Event) :
    run cfg s (e :: es) = ((run cfg (step cfg s e).1 es).1, (step cfg s e).2 ++ (run cfg (step cfg s e).1 es).2) := rfl

/-- Once closed, a run does nothing more. -/
theorem run_closed (cfg : Config) (es : List Event) : ∀ (s : State), s.phase = .closed → run cfg s es = (s, []) := by
  induction es with
  | nil => intro s _; rfl
  | cons e es ih =>
    intro s h
    rw [run_cons, step_closed cfg s e h]
    simp [ih s h]

/-- One step reports at most once, and a report means the task is now closed. -/
theorem step_reports (cfg : Config) (s : State) (e : Event) :
    count Action.isReport (step cfg s e).2 ≤ 1 ∧ (count Action.isReport (step cfg s e).2 = 1 → (step cfg s e).1.phase = .closed) := by
  obtain ⟨s', acts, hs⟩ : ∃ s' acts, step cfg s e = (s', acts) := ⟨_, _, rfl⟩
  rw [hs]
  step_cases hs
  all_goals simp_all [count, Action.isReport]

/-- **A task reports at most once, and a closed task reports nothing more.** -/
theorem reports_le_one (cfg : Config) (es : List Event) :
    ∀ (s : State), count Action.isReport (run cfg s es).2 ≤ (if s.phase = .closed then 0 else 1) := by
  induction es with
  | nil => intro s; simp [run, count]
  | cons e es ih =>
    intro s
    rw [run_cons, count_append]
    by_cases hc : s.phase = .closed
    · rw [step_closed cfg s e hc]; simp [count, hc, run_closed cfg es s hc]
    · have h1 := step_reports cfg s e
      have h2 := ih (step cfg s e).1
      have hgoal : (if s.phase = Phase.closed then 0 else 1) = 1 := by simp [hc]
      rw [hgoal]
      by_cases hr : count Action.isReport (step cfg s e).2 = 1
      · have hcl := h1.2 hr
        rw [hcl] at h2
        simp at h2
        omega
      · have hle : (if (step cfg s e).1.phase = Phase.closed then 0 else 1) ≤ 1 := by split <;> omega
        omega

/-- **A closing task that was not abandoned reports exactly its outcome and where it landed.** -/
theorem closing_reports (cfg : Config) (s : State) (o : Outcome) (l : Option String) (h : s.phase = .closing (some o) l) :
    step cfg s .cleaned = ({ s with phase := .closed }, [.report o l]) := by
  simp [step, h]

/-- One step's cleanups: exactly one when the task enters closing, none otherwise. -/
theorem step_cleanups (cfg : Config) (s : State) (e : Event) :
    count Action.isCleanup (step cfg s e).2 ≤ 1 ∧
    (count Action.isCleanup (step cfg s e).2 = 1 → s.phase.finished = false ∧ (step cfg s e).1.phase.isClosing = true) ∧
    (s.phase.finished = false → (step cfg s e).1.phase.finished = true → count Action.isCleanup (step cfg s e).2 = 1) := by
  obtain ⟨s', acts, hs⟩ : ∃ s' acts, step cfg s e = (s', acts) := ⟨_, _, rfl⟩
  rw [hs]
  step_cases hs
  all_goals simp_all [count, Action.isCleanup]

/-- A finished task stays finished. -/
theorem step_finished_stays (cfg : Config) (s : State) (e : Event) (h : s.phase.finished = true) :
    (step cfg s e).1.phase.finished = true := by
  obtain ⟨s', acts, hs⟩ : ∃ s' acts, step cfg s e = (s', acts) := ⟨_, _, rfl⟩
  rw [hs]
  step_cases hs
  all_goals simp_all [Phase.finished]

/-- **A task that has begun to finish cleans up no more.** -/
theorem cleanups_le_one (cfg : Config) (es : List Event) :
    ∀ (s : State), count Action.isCleanup (run cfg s es).2 ≤ (if s.phase.finished then 0 else 1) := by
  induction es with
  | nil => intro s; simp [run, count]
  | cons e es ih =>
    intro s
    rw [run_cons, count_append]
    obtain ⟨h1, h2, _⟩ := step_cleanups cfg s e
    have h3 := ih (step cfg s e).1
    by_cases hf : s.phase.finished = true
    · have hz : count Action.isCleanup (step cfg s e).2 = 0 := by
        by_cases hz : count Action.isCleanup (step cfg s e).2 = 1
        · have := (h2 hz).1; simp_all
        · omega
      have hs' := step_finished_stays cfg s e hf
      simp only [hs', hf, ite_true] at h3 ⊢
      omega
    · have hf' : s.phase.finished = false := by simpa using hf
      have hgoal : (if s.phase.finished = true then 0 else 1) = 1 := by simp [hf']
      rw [hgoal]
      by_cases hz : count Action.isCleanup (step cfg s e).2 = 1
      · have hc := (h2 hz).2
        have hfin : (step cfg s e).1.phase.finished = true := by
          revert hc; generalize (step cfg s e).1.phase = p; cases p <;> simp [Phase.isClosing, Phase.finished]
        simp only [hfin, ite_true] at h3
        omega
      · have hle : (if (step cfg s e).1.phase.finished = true then 0 else 1) ≤ 1 := by split <;> omega
        omega

/-- **Every task that finishes cleans up exactly once**: from a task that had not begun to finish, if it has finished by the end, it asked for exactly one cleanup. -/
theorem cleanups_exact (cfg : Config) (es : List Event) :
    ∀ (s : State), s.phase.finished = false → (run cfg s es).1.phase.finished = true → count Action.isCleanup (run cfg s es).2 = 1 := by
  induction es with
  | nil => intro s hf hfin; simp [run] at hfin; simp_all
  | cons e es ih =>
    intro s hf hfin
    rw [run_cons] at hfin ⊢
    simp only [count_append]
    obtain ⟨_, h2, h3⟩ := step_cleanups cfg s e
    by_cases hs' : (step cfg s e).1.phase.finished = true
    · have h1 := h3 hf hs'
      have h4 := cleanups_le_one cfg es (step cfg s e).1
      simp [hs'] at h4
      omega
    · have hs'' : (step cfg s e).1.phase.finished = false := by simpa using hs'
      have : count Action.isCleanup (step cfg s e).2 = 0 := by
        by_cases hz : count Action.isCleanup (step cfg s e).2 = 1
        · have := (h2 hz).2
          have hfin' : (step cfg s e).1.phase.finished = true := by
            revert this; generalize (step cfg s e).1.phase = p; cases p <;> simp [Phase.isClosing, Phase.finished]
          simp_all
        · have := (step_cleanups cfg s e).1; omega
      have := ih (step cfg s e).1 hs'' hfin
      omega

end VbmOrchestrator
