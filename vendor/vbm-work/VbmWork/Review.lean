/-! # The review words: what a reviewer returns, and what a round's review comes to

A reviewer returns **typed findings**: the declaration each is about, how the reviewer rated it (`fix` or `note`) and why. Only a `fix` blocks. The verdict of a
round is a function of the findings alone (`clean`, `notes`, `blocked`), and a reply that could not be decoded is `unreviewed`: an error, never an approval.
Vocabulary and the decision table only: reading a reply into findings is a binding's. The proofs are in `VbmWorkProofs`. -/
namespace VbmWork

inductive Severity where
  | fix
  | note
  deriving Repr, DecidableEq

/-- The severity's wire name: exactly what a reviewer writes. -/
def Severity.name : Severity → String
  | .fix => "fix"
  | .note => "note"

/-- The severity of a wire name: exactly `"fix"` or `"note"`; any other text names no severity. -/
def Severity.ofName? : String → Option Severity
  | "fix" => some .fix
  | "note" => some .note
  | _ => none

/-- One finding of one reviewer: the `declaration` it is about, the `severity` the reviewer rated it, and `why`. -/
structure Finding where
  declaration : String
  severity : Severity
  why : String
  deriving Repr, DecidableEq

/-- The findings of one reviewer in one round. `[]` is a reviewer that looked and found nothing. -/
abbrev Review := List Finding

/-- Has this review a `fix`? The one question the verdict asks of a review. -/
def hasFix (r : Review) : Bool := r.any fun f => f.severity == .fix

/-- What a round's review comes to: `clean`, no finding at all; `notes`, findings and none of them a `fix`; `blocked`, some finding is a `fix`; `unreviewed`, a reply that could not be decoded: an error, never an approval. -/
inductive Verdict where
  | clean
  | notes
  | blocked
  | unreviewed
  deriving Repr, DecidableEq

/-- The order as a number: `clean` 0, `notes` 1, `blocked` 2, and `unreviewed` 3, which is in no review's order because no review produces it. -/
def Verdict.rank : Verdict → Nat
  | .clean => 0
  | .notes => 1
  | .blocked => 2
  | .unreviewed => 3

instance : LE Verdict := ⟨fun a b => a.rank ≤ b.rank⟩
instance : LT Verdict := ⟨fun a b => a.rank < b.rank⟩

/-- Why a reply is not a review. `detail` is the whole text; **nothing is ever repaired, defaulted or guessed**. -/
structure DecodeError where
  detail : String
  deriving Repr, DecidableEq

/-- **The verdict of a review**: `blocked` if any finding is a `fix`, else `notes` if there is any finding, else `clean`. -/
def verdict (r : Review) : Verdict :=
  if hasFix r then .blocked else if r.isEmpty then .clean else .notes

/-- A reply that could not be decoded is `unreviewed`. -/
def verdictOf : Except DecodeError Review → Verdict
  | .ok r => verdict r
  | .error _ => .unreviewed

end VbmWork
