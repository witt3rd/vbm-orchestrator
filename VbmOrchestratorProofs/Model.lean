import VbmOrchestratorProofs.Run
/-! # The reference model: proofs

The model is the machine under the port discipline and adds nothing: what it computes is what `run` computes. And every conformance scenario obeys the discipline, so a vector is
a run a correct interpreter can meet. -/
namespace VbmOrchestrator

/-- **The model computes exactly what the machine does**: when `drive` accepts a sequence of events, the state it ends in and the actions of its steps, in order, are `run`'s. -/
theorem drive_run (cfg : Config) (es : List Event) :
    ∀ (s : State) (pending : List Action) (steps : List Step) (s' : State),
      drive cfg s pending es = .ok (steps, s') → s' = (run cfg s es).1 ∧ steps.flatMap Step.actions = (run cfg s es).2 := by
  induction es with
  | nil =>
    intro s pending steps s' h
    simp [drive] at h
    obtain ⟨h1, h2⟩ := h
    subst h1 h2
    simp [run]
  | cons e es ih =>
    intro s pending steps s' h
    unfold drive at h
    by_cases h1 : (!(e.external || pending.any e.answers)) = true
    · simp [h1] at h
    · by_cases h2 : (decide ((step cfg s e).1 = s) && (step cfg s e).2.isEmpty) = true
      · simp [h1, h2] at h
      · simp only [h1, h2, Bool.false_eq_true, ↓reduceIte] at h
        cases hd : drive cfg (step cfg s e).1 (step cfg s e).2 es with
        | error m => simp [hd] at h
        | ok p =>
          obtain ⟨st, s2⟩ := p
          simp only [hd, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨hst, hs2⟩ := h
          have := ih _ _ st s2 hd
          subst hst hs2
          rw [run_cons]
          simp [this.1, this.2]

/-- **Every conformance scenario obeys the port discipline**: each event answers the action pending or is the world's own, and the machine ignores none, so each vector is a run a
correct interpreter can meet. -/
theorem scenarios_obey_the_discipline : scenarios.all (fun sc => (runModel sc.cfg sc.events).toBool) = true := by
  decide

end VbmOrchestrator
