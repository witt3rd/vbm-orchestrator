import VbmWork.Outcome
/-! # The task: what is asked

What the orchestrator is given and nothing about how it was scheduled: an `id`, the `project` it is for, the `intent` (the brief), `doneWhen` (how it is
checked), `files` (hints) and the `ChangeClass` (an upper bound the change must stay under, which decides which checks it must pass). Priority, serialisation keys,
dependencies, the labels a host must have and the enqueue tick are the dispatcher's entry AROUND a task; the model class and the reasoning level are a worker's
profile. Vocabulary and what makes a task well formed only; the proofs are in `VbmWorkProofs`. -/
namespace VbmWork

/-- How far a change may reach; it decides which checks it must pass. The words are the constructor names (`impl` is the default an existing queue stores). -/
inductive ChangeClass where
  | docs | impl | spec | tightening | loosening | trustedC | infra | scout
  deriving DecidableEq, Repr

def ChangeClass.all : List ChangeClass := [.docs, .impl, .spec, .tightening, .loosening, .trustedC, .infra, .scout]

def ChangeClass.name : ChangeClass → String
  | .docs => "docs" | .impl => "impl" | .spec => "spec" | .tightening => "tightening"
  | .loosening => "loosening" | .trustedC => "trustedC" | .infra => "infra" | .scout => "scout"

/-- The class a word stands for; `none` for a word that names none (there is no default class). -/
def ChangeClass.ofName (n : String) : Option ChangeClass := ChangeClass.all.find? (·.name == n)

/-- What is asked of one orchestrator run. -/
structure Task where
  id : String
  project : String
  intent : String
  doneWhen : String
  files : List String
  changeClass : ChangeClass
  deriving DecidableEq, Repr

/-- **Well formed**: the text that must say something does: which task, for which project, what is wanted and how it is checked. -/
def Task.ok (t : Task) : Bool := fullOk t.id && fullOk t.project && fullOk t.intent && fullOk t.doneWhen

end VbmWork
