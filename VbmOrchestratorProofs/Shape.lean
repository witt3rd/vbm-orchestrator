import VbmOrchestratorProofs.Safety
/-! # Control never depends on prose (non-interference)

Two things have the same TYPED SHAPE when they differ only in their texts: the same constructors, the same kinds of block, the same numbers, whatever the words of a
report, a reason, a finding or a commit. `step` maps inputs of the same shape to results of the same shape: it copies text, it never reads it. A run from `start` over two
event sequences of the same shape therefore asks for the same actions (up to their texts) and ends in the same phase. -/
namespace VbmOrchestrator
open VbmWork

/-- A relation lifted over two lists of equal length. -/
inductive Lrel {α β : Type} (R : α → β → Prop) : List α → List β → Prop
  | nil : Lrel R [] []
  | cons {a b as bs} : R a b → Lrel R as bs → Lrel R (a :: as) (b :: bs)

theorem Lrel.append {α β : Type} {R : α → β → Prop} {as as' : List α} {bs bs' : List β}
    (h1 : Lrel R as bs) (h2 : Lrel R as' bs') : Lrel R (as ++ as') (bs ++ bs') := by
  induction h1 with
  | nil => simpa using h2
  | cons hab _ ih => exact Lrel.cons hab ih

/-- Same outcome up to its texts and citations: the same constructor and, for a block, the same kind. -/
inductive OutRel : Outcome → Outcome → Prop
  | done (a b : List Citation) : OutRel (.done a) (.done b)
  | doneWithAssumptions (a b : List String) (c d : List Citation) : OutRel (.doneWithAssumptions a c) (.doneWithAssumptions b d)
  | blocked (k : Kind) (w w' : String) (c c' : List Citation) : OutRel (.blocked k w c) (.blocked k w' c')
  | needsClarification (q q' d d' : String) (c c' : List Citation) : OutRel (.needsClarification q d c) (.needsClarification q' d' c')

inductive OptRel : Option Outcome → Option Outcome → Prop
  | none : OptRel none none
  | some {o o'} : OutRel o o' → OptRel (some o) (some o')

inductive FbRel : Feedback → Feedback → Prop
  | checks (r r' : String) : FbRel (.checks r) (.checks r')
  | conflict (r r' : String) : FbRel (.conflict r) (.conflict r')
  | findings (fs fs' : List Finding) : FbRel (.findings fs) (.findings fs')

structure DelRel (d d' : Delivery) : Prop where
  out : OutRel d.outcome d'.outcome

inductive PhaseRel : Phase → Phase → Prop
  | preparing : PhaseRel .preparing .preparing
  | working (r : Nat) : PhaseRel (.working r) (.working r)
  | validating (r : Nat) {d d'} : DelRel d d' → PhaseRel (.validating r d) (.validating r d')
  | judging (r : Nat) {fb fb'} : FbRel fb fb' → fb.kind = fb'.kind → PhaseRel (.judging r fb) (.judging r fb')
  | reviewing (r : Nat) {d d'} (c c' : String) : DelRel d d' → PhaseRel (.reviewing r d c) (.reviewing r d' c')
  | pushing (r : Nat) {d d'} (c c' : String) : DelRel d d' → PhaseRel (.pushing r d c) (.pushing r d' c')
  | closing {o o'} {l l'} : OptRel o o' → l.isSome = l'.isSome → PhaseRel (.closing o l) (.closing o' l')
  | closed : PhaseRel .closed .closed

structure StateRel (s t : State) : Prop where
  phase : PhaseRel s.phase t.phase
  spent : s.spent = t.spent

inductive ModeRel : AgentMode → AgentMode → Prop
  | first : ModeRel .first .first
  | resume {fb fb'} : FbRel fb fb' → ModeRel (.resume fb) (.resume fb')

inductive ActionRel : Action → Action → Prop
  | prepare : ActionRel .prepare .prepare
  | runAgent (r : Nat) {m m'} : ModeRel m m' → ActionRel (.runAgent r m) (.runAgent r m')
  | askJudge (r : Nat) {fb fb'} (n : Nat) : FbRel fb fb' → ActionRel (.askJudge r fb n) (.askJudge r fb' n)
  | validate (c c' : String) : ActionRel (.validate c) (.validate c')
  | review (c c' : String) : ActionRel (.review c) (.review c')
  | push (c c' : String) : ActionRel (.push c) (.push c')
  | cleanup : ActionRel .cleanup .cleanup
  | report {o o'} {l l'} : OutRel o o' → l.isSome = l'.isSome → ActionRel (.report o l) (.report o' l')

inductive VRel : ValidateResult → ValidateResult → Prop
  | passed (c c' : String) : VRel (.passed c) (.passed c')
  | failed (r r' : String) : VRel (.failed r) (.failed r')
  | conflict (r r' : String) : VRel (.conflict r) (.conflict r')
  | refused : VRel .refused .refused

inductive PRel : PushResult → PushResult → Prop
  | landed (s s' : String) : PRel (.landed s) (.landed s')
  | baseMoved : PRel .baseMoved .baseMoved
  | refused (w w' : String) : PRel (.refused w) (.refused w')

/-- Two reviewer answers: both undecodable, or both findings with the same severities (their words may differ). -/
inductive ARel : ReviewAnswer → ReviewAnswer → Prop
  | ok {a b : Review} : Lrel (fun f g => f.severity = g.severity) a b → ARel (.ok a) (.ok b)
  | error (d d' : DecodeError) : ARel (.error d) (.error d')

inductive EventRel : Event → Event → Prop
  | preparedOk : EventRel .preparedOk .preparedOk
  | preparedFailed (w w' : String) : EventRel (.preparedFailed w) (.preparedFailed w')
  | agentFinished {o o'} {commit commit' : Option String} (cost : Nat) :
      OutRel o o' → commit.isSome = commit'.isSome → EventRel (.agentFinished o commit cost) (.agentFinished o' commit' cost)
  | validated {v v'} : VRel v v' → EventRel (.validated v) (.validated v')
  | reviewed {as bs} : Lrel ARel as bs → EventRel (.reviewed as) (.reviewed bs)
  | judged (a : JudgeAnswer) : EventRel (.judged a) (.judged a)
  | pushed {p p'} : PRel p p' → EventRel (.pushed p) (.pushed p')
  | cleaned : EventRel .cleaned .cleaned
  | leaseLost : EventRel .leaseLost .leaseLost
  | deadline : EventRel .deadline .deadline

end VbmOrchestrator

namespace VbmOrchestrator
open VbmWork

theorem lrel_cons_iff {α β : Type} {R : α → β → Prop} {a : α} {b : β} {as : List α} {bs : List β} :
    Lrel R (a :: as) (b :: bs) ↔ R a b ∧ Lrel R as bs :=
  ⟨fun h => by cases h with | cons h1 h2 => exact ⟨h1, h2⟩, fun ⟨h1, h2⟩ => Lrel.cons h1 h2⟩

theorem lrel_nil {α β : Type} {R : α → β → Prop} : Lrel R ([] : List α) ([] : List β) := Lrel.nil

theorem stateRel_iff {s t : State} : StateRel s t ↔ PhaseRel s.phase t.phase ∧ s.spent = t.spent :=
  ⟨fun h => ⟨h.phase, h.spent⟩, fun h => ⟨h.1, h.2⟩⟩

@[simp] theorem fbRel_kind {a b : Feedback} (h : FbRel a b) : a.kind = b.kind := by cases h <;> rfl

/-- Closing for a failure: related feedbacks close in blocks of the same kind, whatever their words. -/
@[simp] theorem outRel_of_fb {a b : Feedback} (h : FbRel a b) (w w' : String) :
    OutRel (Outcome.blocked a.kind w []) (Outcome.blocked b.kind w' []) := by
  rw [fbRel_kind h]; exact OutRel.blocked _ _ _ _ _

/-- Whether a reviewer's reply could not be decoded depends only on the typed shape of the answers. -/
theorem any_failed_rel {as bs : List ReviewAnswer} (h : Lrel ARel as bs) : as.any answerFailed = bs.any answerFailed := by
  induction h with
  | nil => rfl
  | cons hab _ ih => cases hab <;> simp_all [answerFailed]

theorem filter_length_rel {a b : List Finding} (h : Lrel (fun f g => f.severity = g.severity) a b) :
    (a.filter fun f => f.severity == .fix).length = (b.filter fun f => f.severity == .fix).length := by
  induction h with
  | nil => rfl
  | @cons f g _ _ hab _ ih =>
    by_cases hf : g.severity = .fix
    · have hf' : f.severity = .fix := hab.trans hf
      simp [hf, hf', ih]
    · have hf' : ¬ f.severity = .fix := fun h => hf (hab.symm.trans h)
      simp [hf, hf', ih]

theorem fixes_length_rel {as bs : List ReviewAnswer} (h : Lrel ARel as bs) :
    (as.flatMap answerFixes).length = (bs.flatMap answerFixes).length := by
  induction h with
  | nil => rfl
  | cons hab _ ih =>
    cases hab with
    | ok hl => simp [answerFixes, List.flatMap_cons, filter_length_rel hl, ih]
    | error => simp [answerFixes, List.flatMap_cons, ih]

/-- Whether any reviewer found a `fix` depends only on the typed shape of the answers. -/
theorem fixes_empty_rel {as bs : List ReviewAnswer} (h : Lrel ARel as bs) :
    (as.flatMap answerFixes = []) ↔ (bs.flatMap answerFixes = []) := by
  rw [← List.length_eq_zero_iff, ← List.length_eq_zero_iff, fixes_length_rel h]

theorem delRel_mk {c c' : String} {o o' : Outcome} : DelRel ⟨c, o⟩ ⟨c', o'⟩ ↔ OutRel o o' :=
  ⟨fun h => h.out, fun h => ⟨h⟩⟩

/-! Outcomes of different constructors are never related. -/
@[simp] theorem outRel_done_doneW (xa : List Citation) (ya : List String) (yc : List Citation) : ¬ OutRel (Outcome.done xa) (Outcome.doneWithAssumptions ya yc) := by intro h; cases h
@[simp] theorem outRel_done_blocked (xa : List Citation) (yk : Kind) (yw : String) (yc : List Citation) : ¬ OutRel (Outcome.done xa) (Outcome.blocked yk yw yc) := by intro h; cases h
@[simp] theorem outRel_done_needs (xa : List Citation) (yq yd : String) (yc : List Citation) : ¬ OutRel (Outcome.done xa) (Outcome.needsClarification yq yd yc) := by intro h; cases h
@[simp] theorem outRel_doneW_done (xa : List String) (xc : List Citation) (ya : List Citation) : ¬ OutRel (Outcome.doneWithAssumptions xa xc) (Outcome.done ya) := by intro h; cases h
@[simp] theorem outRel_doneW_blocked (xa : List String) (xc : List Citation) (yk : Kind) (yw : String) (yc : List Citation) : ¬ OutRel (Outcome.doneWithAssumptions xa xc) (Outcome.blocked yk yw yc) := by intro h; cases h
@[simp] theorem outRel_doneW_needs (xa : List String) (xc : List Citation) (yq yd : String) (yc : List Citation) : ¬ OutRel (Outcome.doneWithAssumptions xa xc) (Outcome.needsClarification yq yd yc) := by intro h; cases h
@[simp] theorem outRel_blocked_done (xk : Kind) (xw : String) (xc : List Citation) (ya : List Citation) : ¬ OutRel (Outcome.blocked xk xw xc) (Outcome.done ya) := by intro h; cases h
@[simp] theorem outRel_blocked_doneW (xk : Kind) (xw : String) (xc : List Citation) (ya : List String) (yc : List Citation) : ¬ OutRel (Outcome.blocked xk xw xc) (Outcome.doneWithAssumptions ya yc) := by intro h; cases h
@[simp] theorem outRel_blocked_needs (xk : Kind) (xw : String) (xc : List Citation) (yq yd : String) (yc : List Citation) : ¬ OutRel (Outcome.blocked xk xw xc) (Outcome.needsClarification yq yd yc) := by intro h; cases h
@[simp] theorem outRel_needs_done (xq xd : String) (xc : List Citation) (ya : List Citation) : ¬ OutRel (Outcome.needsClarification xq xd xc) (Outcome.done ya) := by intro h; cases h
@[simp] theorem outRel_needs_doneW (xq xd : String) (xc : List Citation) (ya : List String) (yc : List Citation) : ¬ OutRel (Outcome.needsClarification xq xd xc) (Outcome.doneWithAssumptions ya yc) := by intro h; cases h
@[simp] theorem outRel_needs_blocked (xq xd : String) (xc : List Citation) (yk : Kind) (yw : String) (yc : List Citation) : ¬ OutRel (Outcome.needsClarification xq xd xc) (Outcome.blocked yk yw yc) := by intro h; cases h

/-! The other relations: different constructors are never related. -/
@[simp] theorem vRel_passed_failed (xs : String) (ys : String) : ¬ VRel (ValidateResult.passed xs) (ValidateResult.failed ys) := by intro h; cases h
@[simp] theorem vRel_passed_conflict (xs : String) (ys : String) : ¬ VRel (ValidateResult.passed xs) (ValidateResult.conflict ys) := by intro h; cases h
@[simp] theorem vRel_passed_refused (xs : String)  : ¬ VRel (ValidateResult.passed xs) ValidateResult.refused := by intro h; cases h
@[simp] theorem vRel_failed_passed (xs : String) (ys : String) : ¬ VRel (ValidateResult.failed xs) (ValidateResult.passed ys) := by intro h; cases h
@[simp] theorem vRel_failed_conflict (xs : String) (ys : String) : ¬ VRel (ValidateResult.failed xs) (ValidateResult.conflict ys) := by intro h; cases h
@[simp] theorem vRel_failed_refused (xs : String)  : ¬ VRel (ValidateResult.failed xs) ValidateResult.refused := by intro h; cases h
@[simp] theorem vRel_conflict_passed (xs : String) (ys : String) : ¬ VRel (ValidateResult.conflict xs) (ValidateResult.passed ys) := by intro h; cases h
@[simp] theorem vRel_conflict_failed (xs : String) (ys : String) : ¬ VRel (ValidateResult.conflict xs) (ValidateResult.failed ys) := by intro h; cases h
@[simp] theorem vRel_conflict_refused (xs : String)  : ¬ VRel (ValidateResult.conflict xs) ValidateResult.refused := by intro h; cases h
@[simp] theorem vRel_refused_passed  (ys : String) : ¬ VRel ValidateResult.refused (ValidateResult.passed ys) := by intro h; cases h
@[simp] theorem vRel_refused_failed  (ys : String) : ¬ VRel ValidateResult.refused (ValidateResult.failed ys) := by intro h; cases h
@[simp] theorem vRel_refused_conflict  (ys : String) : ¬ VRel ValidateResult.refused (ValidateResult.conflict ys) := by intro h; cases h
@[simp] theorem pRel_landed_baseMoved (xs : String)  : ¬ PRel (PushResult.landed xs) PushResult.baseMoved := by intro h; cases h
@[simp] theorem pRel_landed_refused (xs : String) (ys : String) : ¬ PRel (PushResult.landed xs) (PushResult.refused ys) := by intro h; cases h
@[simp] theorem pRel_baseMoved_landed  (ys : String) : ¬ PRel PushResult.baseMoved (PushResult.landed ys) := by intro h; cases h
@[simp] theorem pRel_baseMoved_refused  (ys : String) : ¬ PRel PushResult.baseMoved (PushResult.refused ys) := by intro h; cases h
@[simp] theorem pRel_refused_landed (xs : String) (ys : String) : ¬ PRel (PushResult.refused xs) (PushResult.landed ys) := by intro h; cases h
@[simp] theorem pRel_refused_baseMoved (xs : String)  : ¬ PRel (PushResult.refused xs) PushResult.baseMoved := by intro h; cases h
@[simp] theorem optRel_none_some  (yo : Outcome) : ¬ OptRel (none : Option Outcome) (some yo) := by intro h; cases h
@[simp] theorem optRel_some_none (xo : Outcome)  : ¬ OptRel (some xo) (none : Option Outcome) := by intro h; cases h
@[simp] theorem aRel_ok_error (xa : Review) (yd : DecodeError) : ¬ ARel (Except.ok xa : ReviewAnswer) (Except.error yd : ReviewAnswer) := by intro h; cases h
@[simp] theorem aRel_error_ok (xd : DecodeError) (ya : Review) : ¬ ARel (Except.error xd : ReviewAnswer) (Except.ok ya : ReviewAnswer) := by intro h; cases h
@[simp] theorem fbRel_ne_checks_conflict (xs : String) (ys : String) : ¬ FbRel (Feedback.checks xs) (Feedback.conflict ys) := by intro h; cases h
@[simp] theorem fbRel_ne_checks_findings (xs : String) (yf : List Finding) : ¬ FbRel (Feedback.checks xs) (Feedback.findings yf) := by intro h; cases h
@[simp] theorem fbRel_ne_conflict_checks (xs : String) (ys : String) : ¬ FbRel (Feedback.conflict xs) (Feedback.checks ys) := by intro h; cases h
@[simp] theorem fbRel_ne_conflict_findings (xs : String) (yf : List Finding) : ¬ FbRel (Feedback.conflict xs) (Feedback.findings yf) := by intro h; cases h
@[simp] theorem fbRel_ne_findings_checks (xf : List Finding) (ys : String) : ¬ FbRel (Feedback.findings xf) (Feedback.checks ys) := by intro h; cases h
@[simp] theorem fbRel_ne_findings_conflict (xf : List Finding) (ys : String) : ¬ FbRel (Feedback.findings xf) (Feedback.conflict ys) := by intro h; cases h

@[simp] theorem phaseRel_judging {r : Nat} {a b : Feedback} (h : FbRel a b) : PhaseRel (.judging r a) (.judging r b) :=
  PhaseRel.judging r h (fbRel_kind h)

@[simp] theorem outRel_of_del {d d' : Delivery} (h : DelRel d d') : OutRel d.outcome d'.outcome := h.out

/-- A landed task closes, in related phases, with related outcomes (the worker's) and a landed commit on each side. -/
@[simp] theorem phaseRel_closing_landed {d d' : Delivery} (h : DelRel d d') (s s' : String) :
    PhaseRel (.closing (some d.outcome) (some s)) (.closing (some d'.outcome) (some s')) :=
  PhaseRel.closing (OptRel.some h.out) rfl

/-- Finishing a close reports related outcomes. -/
@[simp] theorem actionRel_report_of_opt {o o' : Outcome} {l l' : Option String} (h : OptRel (some o) (some o')) (hl : l.isSome = l'.isSome) :
    ActionRel (.report o l) (.report o' l') := by
  cases h with
  | some ho => exact ActionRel.report ho hl

attribute [simp] PhaseRel.preparing PhaseRel.working PhaseRel.validating PhaseRel.judging PhaseRel.reviewing PhaseRel.pushing
  PhaseRel.closing PhaseRel.closed OutRel.done OutRel.doneWithAssumptions OutRel.blocked OutRel.needsClarification
  OptRel.none OptRel.some FbRel.checks FbRel.conflict FbRel.findings ModeRel.first ModeRel.resume
  ActionRel.prepare ActionRel.runAgent ActionRel.askJudge ActionRel.validate ActionRel.review ActionRel.push ActionRel.cleanup ActionRel.report
  lrel_cons_iff lrel_nil stateRel_iff delRel_mk

theorem step_rel (cfg : Config) (s t : State) (e e' : Event) (hs : StateRel s t) (he : EventRel e e') :
    StateRel (step cfg s e).1 (step cfg t e').1 ∧ Lrel ActionRel (step cfg s e).2 (step cfg t e').2 := by
  obtain ⟨p, n⟩ := s
  obtain ⟨q, m⟩ := t
  have hp := hs.phase
  have hn := hs.spent
  simp only at hp hn
  subst hn
  have hp0 := hp
  cases hp <;> cases he <;>
    (try (have h1 := any_failed_rel ‹Lrel ARel _ _›; have h2 := fixes_empty_rel ‹Lrel ARel _ _›)) <;>
    simp_all [step, onPrepared, onWork, onValidated, onReviewed, onJudged, onPushed, close, ask, resumeOrFuse, blockedOut, Feedback.kind] <;>
    (repeat' split) <;> (try simp_all) <;> (try grind)

end VbmOrchestrator

namespace VbmOrchestrator
open VbmWork

/-- **Control never depends on prose, step by step to the end**: feed two event sequences of the same typed shape (they may differ in every text: reports, reasons,
findings, commits, shas) into two states of the same shape, and the runs end in states of the same shape and ask for actions of the same shape. -/
theorem run_rel (cfg : Config) {es es' : List Event} (h : Lrel EventRel es es') :
    ∀ (s t : State), StateRel s t → StateRel (run cfg s es).1 (run cfg t es').1 ∧ Lrel ActionRel (run cfg s es).2 (run cfg t es').2 := by
  induction h with
  | nil => intro s t hs; exact ⟨by simpa [run] using hs, by simp [run]⟩
  | cons he _ ih =>
    intro s t hs
    rw [run_cons, run_cons]
    obtain ⟨h1, h2⟩ := step_rel cfg s t _ _ hs he
    obtain ⟨h3, h4⟩ := ih _ _ h1
    exact ⟨h3, Lrel.append h2 h4⟩

theorem start_rel : StateRel start.1 start.1 := ⟨PhaseRel.preparing, rfl⟩

/-- **From the start**: two runs whose events have the same typed shape ask for the same actions (up to their texts) and end in the same phase and the same spend. -/
theorem no_prose (cfg : Config) {es es' : List Event} (h : Lrel EventRel es es') :
    StateRel (run cfg start.1 es).1 (run cfg start.1 es').1 ∧ Lrel ActionRel (run cfg start.1 es).2 (run cfg start.1 es').2 :=
  run_rel cfg h start.1 start.1 start_rel

/-! ## The witness: the hypothesis can hold. Two runs whose events differ in every text. -/

example : Lrel EventRel
    [.preparedOk, .agentFinished (.done []) (some "c1") 3, .validated (.failed "red: 2 tests failed"), .judged .progressing]
    [.preparedOk, .agentFinished (.done [⟨"call-9", "a span"⟩]) (some "another commit") 3, .validated (.failed "completely different words"), .judged .progressing] := by
  repeat' constructor

end VbmOrchestrator
