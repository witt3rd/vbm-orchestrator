import VbmWork
/-! # The review words: proofs

A review has a `fix` exactly when one of its findings is a `fix`; the verdict is `blocked` exactly then, `notes` for findings none of which is a `fix`, `clean` for none;
a reply that could not be decoded is `unreviewed`, which no review has and which is never an approval. Each conditional statement has a witness that its hypothesis can hold. -/
namespace VbmWork

/-- **Names and severities are one to one**: a name is read back as the severity that spells it. -/
theorem Severity.ofName?_name (s : Severity) : Severity.ofName? s.name = some s := by cases s <;> rfl

/-- **Only the two names are severities**: any other text is `none`, never a guess. -/
theorem Severity.ofName?_eq_none {t : String} (h : t ≠ "fix") (h' : t ≠ "note") : Severity.ofName? t = none := by
  unfold Severity.ofName?; split <;> simp_all

/-- **A review has a `fix` exactly when one of its findings is a `fix`**. -/
theorem hasFix_iff {r : Review} : hasFix r = true ↔ ∃ f ∈ r, f.severity = .fix := by
  unfold hasFix
  rw [List.any_eq_true]
  refine ⟨fun ⟨f, hf, hfx⟩ => ⟨f, hf, ?_⟩, fun ⟨f, hf, hfx⟩ => ⟨f, hf, by rw [hfx]; rfl⟩⟩
  cases hs : f.severity <;> simp_all

/-- **`clean` is the least verdict**: it is `clean ≤` every verdict. -/
theorem Verdict.clean_le (v : Verdict) : Verdict.clean ≤ v := by cases v <;> exact Nat.zero_le _

/-- **The two questions the table asks always have an answer**. -/
theorem verdict_cases (r : Review) :
    (hasFix r = true ∨ hasFix r = false) ∧ (r.isEmpty = true ∨ r.isEmpty = false) :=
  ⟨by cases hasFix r <;> simp, by cases r.isEmpty <;> simp⟩

/-- **A review with a `fix` is `blocked`**. -/
theorem verdict_fix {r : Review} {f : Finding} (h : f ∈ r) (hs : f.severity = .fix) : verdict r = .blocked := by
  unfold verdict
  rw [show hasFix r = true from hasFix_iff.mpr ⟨f, h, hs⟩]
  rfl

/-- **`blocked` exactly when a `fix`**: no other case of the table is ever `blocked`. -/
theorem blocked_iff {r : Review} : verdict r = .blocked ↔ ∃ f ∈ r, f.severity = .fix := by
  by_cases hx : hasFix r = true
  · have hv : verdict r = .blocked := by unfold verdict; rw [ite_eq_left hx]
    exact ⟨fun _ => hasFix_iff.mp hx, fun _ => hv⟩
  · have hfx : ¬ hasFix r = true := hx
    rw [show verdict r = (if r.isEmpty then (Verdict.clean : Verdict) else .notes) from by
      unfold verdict; rw [ite_eq_right hfx]]
    by_cases he : r.isEmpty = true
    · rw [ite_eq_left he]
      refine ⟨fun hb => absurd hb (by decide), ?_⟩
      rintro ⟨g, hg, _⟩
      rw [List.isEmpty_iff] at he
      subst he
      exact absurd hg (by simp)
    · rw [ite_eq_right he]
      exact ⟨fun hb => absurd hb (by decide), fun ⟨g, hg, hfs⟩ => absurd (hasFix_iff.mpr ⟨g, hg, hfs⟩) hx⟩

/-- **Notes only never blocks**: a review with no `fix` has a verdict that is not `blocked`. -/
theorem notes_not_blocked {r : Review} (hfix : ∀ f ∈ r, f.severity ≠ .fix) : verdict r ≠ .blocked := by
  intro hb
  obtain ⟨f, hf, hfs⟩ := blocked_iff.mp hb
  exact hfix f hf hfs

/-- **Notes only is `notes`**: findings and not one `fix` is `notes`. -/
theorem verdict_notes {r : Review} (hne : r ≠ [])
    (hfix : ∀ f ∈ r, f.severity ≠ .fix) : verdict r = .notes := by
  unfold verdict
  have hx : ¬ hasFix r = true := by
    intro hb
    obtain ⟨f, hf, hfs⟩ := hasFix_iff.mp hb
    exact hfix f hf hfs
  rw [ite_eq_right hx]
  have he : ¬ r.isEmpty = true := by
    intro hb
    exact hne (List.isEmpty_iff.mp hb)
  rw [ite_eq_right he]

/-- **The empty review is `clean`**. -/
theorem verdict_nil : verdict ([] : Review) = .clean := by
  unfold verdict
  rfl

/-- **A reply that could not be decoded is `unreviewed`**, whatever the error. -/
theorem verdictOf_error (e : DecodeError) : verdictOf (.error e) = .unreviewed := rfl

/-- **A decoded reply is its review's verdict**. -/
theorem verdictOf_ok (r : Review) : verdictOf (Except.ok r : Except DecodeError Review) = verdict r := rfl

/-- **`unreviewed` is never `clean`**: a reviewer that did not answer is an error, never an approval. -/
theorem unreviewed_not_clean (e : Except DecodeError Review) (h : verdictOf e = .unreviewed) :
    verdictOf e ≠ .clean := by
  rw [h]; decide

/-- **A reply that could not be decoded is never `clean`**, whatever `DecodeError` it failed with. -/
theorem error_not_clean (d : DecodeError) : verdictOf (.error d) ≠ .clean := by
  rw [verdictOf_error]; decide

/-- **No review has the verdict `unreviewed`**: the table's three answers are its only ones. -/
theorem verdict_of_review_ne_unreviewed (r : Review) : verdict r ≠ .unreviewed := by
  unfold verdict
  cases h : hasFix r
  · cases e : r.isEmpty <;> simp
  · simp

/-! ## The witnesses: each hypothesis can be met -/

example : verdict [⟨"VbmWork.verdict", .fix, "a proof is missing"⟩] = .blocked := by decide
example : verdict [⟨"VbmWork.hasFix", .note, "a name could be clearer"⟩] = .notes := by decide
example : verdict ([] : Review) = .clean := by decide
example : (∀ f ∈ ([⟨"x", .note, "y"⟩] : Review), f.severity ≠ .fix) := by decide
example : ([⟨"x", .note, "y"⟩] : Review) ≠ [] := by decide
example : verdictOf (.error ⟨"not json"⟩) = .unreviewed := rfl

end VbmWork
