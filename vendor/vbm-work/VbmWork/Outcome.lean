/-! # The typed outcome: how a run ends

Every run ends in **exactly one typed outcome**, a closed sum of four: `done`, `doneWithAssumptions`, `blocked (kind, reason)`, `needsClarification (question, default)`.
The harness reads the constructor and its closed `Kind`, never words: a requester learns *done or not, and why* from the type.

This module is the vocabulary only: the alphabet (four tags, nineteen kinds, one word each), the citation of a tool result, the outcome and what makes one
well formed. Nothing here reads or writes any wire format (that is a binding's), and nothing decides what a run does next. The proofs are in `VbmWorkProofs`.
The words are the words an existing journal already holds; they are kept exactly, and a change to one is a change to that journal. -/
namespace VbmWork

/-- The four ways a run ends. -/
inductive Tag where
  | done | doneWithAssumptions | blocked | needsClarification
  deriving DecidableEq, Repr

def Tag.all : List Tag := [.done, .doneWithAssumptions, .blocked, .needsClarification]

def Tag.name : Tag → String
  | .done => "done" | .doneWithAssumptions => "done_with_assumptions" | .blocked => "blocked" | .needsClarification => "needs_clarification"

/-- The tag a word stands for; `none` for a word that names none (there is no default tag). -/
def Tag.ofName (n : String) : Option Tag := Tag.all.find? (·.name == n)

/-- Why a run could not be done, as something a requester acts on differently: re-route to a lane that may write there, hold until the base is green, resize or split, ask for access, fix the request. -/
inductive Kind where
  | readOnlyPath | protectedPath | badPath | redBase | missingInput | noAccess | contradiction
  | budget | runFailed | noFinish | providerStall
  | fuse | noProgress | unpriced
  -- how the orchestrator's cycle closes (decision 0039 of the first application): the harness's own, never claimed by a model; `timeout` is the wall deadline
  | checksFailed | reviewFindings | unableToReview | conflictUnresolved | timeout
  deriving DecidableEq, Repr

def Kind.all : List Kind :=
  [.readOnlyPath, .protectedPath, .badPath, .redBase, .missingInput, .noAccess, .contradiction, .budget, .runFailed, .noFinish, .providerStall,
   .fuse, .noProgress, .unpriced, .checksFailed, .reviewFindings, .unableToReview, .conflictUnresolved, .timeout]

def Kind.name : Kind → String
  | .readOnlyPath => "readOnlyPath" | .protectedPath => "protectedPath" | .badPath => "badPath" | .redBase => "redBase" | .missingInput => "missingInput"
  | .noAccess => "noAccess" | .contradiction => "contradiction" | .budget => "budget" | .runFailed => "runFailed" | .noFinish => "noFinish" | .providerStall => "providerStall"
  | .fuse => "fuse" | .noProgress => "noProgress" | .unpriced => "unpriced"
  | .checksFailed => "checksFailed" | .reviewFindings => "reviewFindings" | .unableToReview => "unableToReview" | .conflictUnresolved => "conflictUnresolved" | .timeout => "timeout"

/-- The kind a word stands for; `none` for a word that names none (there is no default kind). -/
def Kind.ofName (n : String) : Option Kind := Kind.all.find? (·.name == n)

/-- The kinds a model may claim in its `finish`: what it can see and a requester can act on. The rest are the harness's (a path it refused, a spent allowance, a failed run, a run that did not finish). -/
def Kind.byModel : Kind → Bool
  | .readOnlyPath | .protectedPath | .redBase | .missingInput | .noAccess | .contradiction => true
  | .badPath | .budget | .runFailed | .noFinish | .providerStall => false
  | .fuse | .noProgress | .unpriced => false
  | .checksFailed | .reviewFindings | .unableToReview | .conflictUnresolved | .timeout => false

/-! ## The outcome -/

/-- A cited tool result: the provider's id of the call, and a quoted span of its result (`""`: the whole result). -/
structure Citation where
  call : String
  span : String
  deriving DecidableEq, Repr

inductive Outcome where
  | done (citations : List Citation)
  | doneWithAssumptions (assumptions : List String) (citations : List Citation)
  | blocked (kind : Kind) (reason : String) (citations : List Citation)
  | needsClarification (question default : String) (citations : List Citation)
  deriving DecidableEq, Repr

def Outcome.tag : Outcome → Tag
  | .done _ => .done | .doneWithAssumptions _ _ => .doneWithAssumptions | .blocked _ _ _ => .blocked | .needsClarification _ _ _ => .needsClarification

/-- The tool results an outcome cites. -/
def Outcome.citations : Outcome → List Citation
  | .done cs | .doneWithAssumptions _ cs | .blocked _ _ cs | .needsClarification _ _ cs => cs

/-- Text that must say something does. -/
def fullOk (s : String) : Bool := decide (0 < s.length)

/-- Every citation names its call. -/
def citationsOk (cs : List Citation) : Bool := cs.all fun c => fullOk c.call

/-- **Well formed**: the text that must say something does (`doneWithAssumptions` assumes something, `blocked` says why, `needsClarification` asks and has a default), and every citation names its call. -/
def Outcome.ok : Outcome → Bool
  | .done cs => citationsOk cs
  | .doneWithAssumptions as cs => !as.isEmpty && as.all fullOk && citationsOk cs
  | .blocked _ r cs => fullOk r && citationsOk cs
  | .needsClarification q d cs => fullOk q && fullOk d && citationsOk cs

end VbmWork
