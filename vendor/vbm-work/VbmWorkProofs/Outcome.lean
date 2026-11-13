import VbmWork
/-! # The typed outcome: proofs

The alphabet is closed (every tag and kind is in its list), each has one word and a word names at most one (`ofName_name`, `name_injective`), a word that names
none is refused (`ofName_eq_none`: there is no default), the model may claim exactly six of the nineteen kinds, and an outcome is well formed exactly when its text
says something. Each conditional statement has a witness that its hypothesis can hold. -/
namespace VbmWork

theorem Tag.mem_all (t : Tag) : t ∈ Tag.all := by cases t <;> simp [Tag.all]

theorem Tag.ofName_name (t : Tag) : Tag.ofName t.name = some t := by cases t <;> decide

theorem Tag.name_ofName {n : String} {t : Tag} (h : Tag.ofName n = some t) : t.name = n := by
  have := List.find?_some h
  simpa using this

/-- **A word names at most one tag.** -/
theorem Tag.name_injective {a b : Tag} (h : a.name = b.name) : a = b := by
  have h1 := Tag.ofName_name a
  have h2 := Tag.ofName_name b
  rw [h] at h1
  rw [h1] at h2
  exact Option.some.inj h2

/-- **A word that is no tag's word names no tag**: nothing is guessed. -/
theorem Tag.ofName_eq_none {n : String} : Tag.ofName n = none ↔ ∀ t : Tag, t.name ≠ n := by
  unfold Tag.ofName
  rw [List.find?_eq_none]
  constructor
  · intro h t ht
    exact h t (Tag.mem_all t) (by simp [ht])
  · intro h t _ hb
    exact h t (by simpa using hb)

theorem Kind.mem_all (k : Kind) : k ∈ Kind.all := by cases k <;> simp [Kind.all]

theorem Kind.ofName_name (k : Kind) : Kind.ofName k.name = some k := by cases k <;> decide

theorem Kind.name_ofName {n : String} {k : Kind} (h : Kind.ofName n = some k) : k.name = n := by
  have := List.find?_some h
  simpa using this

/-- **A word names at most one kind.** -/
theorem Kind.name_injective {a b : Kind} (h : a.name = b.name) : a = b := by
  have h1 := Kind.ofName_name a
  have h2 := Kind.ofName_name b
  rw [h] at h1
  rw [h1] at h2
  exact Option.some.inj h2

/-- **A word that is no kind's word names no kind**: there is no default kind. -/
theorem Kind.ofName_eq_none {n : String} : Kind.ofName n = none ↔ ∀ k : Kind, k.name ≠ n := by
  unfold Kind.ofName
  rw [List.find?_eq_none]
  constructor
  · intro h k hk
    exact h k (Kind.mem_all k) (by simp [hk])
  · intro h k _ hb
    exact h k (by simpa using hb)

/-- **Which kinds the model may claim**: exactly these six (what it can see and a requester acts on differently). -/
theorem Kind.byModel_iff (k : Kind) :
    k.byModel = true ↔ (k = .readOnlyPath ∨ k = .protectedPath ∨ k = .redBase ∨ k = .missingInput ∨ k = .noAccess ∨ k = .contradiction) := by
  cases k <;> simp [Kind.byModel]

/-- **Six of the nineteen**: the other thirteen are the harness's own, never produced from a model's words. -/
theorem Kind.byModel_count : (Kind.all.filter Kind.byModel).length = 6 := by decide

/-- **The cycle's closing kinds are the harness's own**: a model may never claim one of them (they are what the orchestrator closes a task with). -/
theorem Kind.cycle_kinds_not_by_model :
    Kind.byModel .checksFailed = false ∧ Kind.byModel .reviewFindings = false ∧ Kind.byModel .unableToReview = false ∧
      Kind.byModel .conflictUnresolved = false ∧ Kind.byModel .timeout = false :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- A `done` outcome is well formed exactly when its citations name their calls. -/
theorem Outcome.done_ok_iff (cs : List Citation) : (Outcome.done cs).ok = true ↔ citationsOk cs = true := Iff.rfl

/-- **A block says why**: a `blocked` outcome is well formed exactly when it has a reason and its citations name their calls. -/
theorem Outcome.blocked_ok_iff (k : Kind) (r : String) (cs : List Citation) :
    (Outcome.blocked k r cs).ok = true ↔ 0 < r.length ∧ citationsOk cs = true := by
  simp [Outcome.ok, fullOk]

/-- **An assumption is stated**: `doneWithAssumptions` is well formed exactly when something is assumed, each assumption says something, and the citations name their calls (with nothing assumed it is `done`). -/
theorem Outcome.assumptions_ok_iff (as : List String) (cs : List Citation) :
    (Outcome.doneWithAssumptions as cs).ok = true ↔ as ≠ [] ∧ (∀ a ∈ as, 0 < a.length) ∧ citationsOk cs = true := by
  simp [Outcome.ok, fullOk, and_assoc]

/-- **A question has a default**: `needsClarification` is well formed exactly when it asks, has a default, and its citations name their calls (a question with no default is a stall). -/
theorem Outcome.clarification_ok_iff (q d : String) (cs : List Citation) :
    (Outcome.needsClarification q d cs).ok = true ↔ 0 < q.length ∧ 0 < d.length ∧ citationsOk cs = true := by
  simp [Outcome.ok, fullOk, and_assoc]

/-- A block with no reason is not well formed. -/
theorem Outcome.blocked_without_reason (k : Kind) (cs : List Citation) : (Outcome.blocked k "" cs).ok = false := by
  simp [Outcome.ok, fullOk]

/-- Assuming nothing is not well formed (it is `done`). -/
theorem Outcome.assumptions_none (cs : List Citation) : (Outcome.doneWithAssumptions [] cs).ok = false := by
  simp [Outcome.ok]

/-! ## The witnesses: each hypothesis can be met, and both sides of each test are inhabited -/

example : (Outcome.done []).ok = true := by decide
example : (Outcome.doneWithAssumptions ["the base is green"] []).ok = true := by decide
example : (Outcome.blocked .budget "the allowance is spent" [⟨"call-1", ""⟩]).ok = true := by decide
example : (Outcome.needsClarification "which file?" "the first" []).ok = true := by decide
example : (Outcome.done [⟨"", "x"⟩]).ok = false := by decide   -- a citation that names no call
example : Kind.byModel .redBase = true := rfl
example : Kind.byModel .budget = false := rfl

end VbmWork
