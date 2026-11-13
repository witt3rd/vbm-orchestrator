import VbmWork
/-! # The task: proofs

The change classes are closed, each has one word and a word names at most one, a word that names none is refused (there is no default class); a task is well
formed exactly when its four texts say something. Each conditional statement has a witness that its hypothesis can hold. -/
namespace VbmWork

theorem ChangeClass.mem_all (c : ChangeClass) : c ∈ ChangeClass.all := by cases c <;> simp [ChangeClass.all]

theorem ChangeClass.ofName_name (c : ChangeClass) : ChangeClass.ofName c.name = some c := by cases c <;> decide

theorem ChangeClass.name_ofName {n : String} {c : ChangeClass} (h : ChangeClass.ofName n = some c) : c.name = n := by
  have := List.find?_some h
  simpa using this

/-- **A word names at most one class.** -/
theorem ChangeClass.name_injective {a b : ChangeClass} (h : a.name = b.name) : a = b := by
  have h1 := ChangeClass.ofName_name a
  have h2 := ChangeClass.ofName_name b
  rw [h] at h1
  rw [h1] at h2
  exact Option.some.inj h2

/-- **A word that is no class's word names no class**: there is no default class. -/
theorem ChangeClass.ofName_eq_none {n : String} : ChangeClass.ofName n = none ↔ ∀ c : ChangeClass, c.name ≠ n := by
  unfold ChangeClass.ofName
  rw [List.find?_eq_none]
  constructor
  · intro h c hc
    exact h c (ChangeClass.mem_all c) (by simp [hc])
  · intro h c _ hb
    exact h c (by simpa using hb)

/-- **A task says what is asked**: well formed exactly when it names itself, its project, what is wanted and how it is checked. -/
theorem Task.ok_iff (t : Task) :
    t.ok = true ↔ 0 < t.id.length ∧ 0 < t.project.length ∧ 0 < t.intent.length ∧ 0 < t.doneWhen.length := by
  simp [Task.ok, fullOk, and_assoc]

/-- A task with no intent is not well formed, whatever else it says. -/
theorem Task.no_intent (t : Task) (h : t.intent = "") : t.ok = false := by
  simp [Task.ok, fullOk, h]

/-- A task with no way to check it is not well formed. -/
theorem Task.no_done_when (t : Task) (h : t.doneWhen = "") : t.ok = false := by
  simp [Task.ok, fullOk, h]

/-! ## The witnesses -/

example : (Task.mk "docs-fix-1" "a-project" "fix the readme" "the readme builds" [] .docs).ok = true := by decide
example : (Task.mk "docs-fix-1" "a-project" "" "the readme builds" [] .docs).ok = false := by decide
example : ChangeClass.ofName "impl" = some .impl := by decide

end VbmWork
