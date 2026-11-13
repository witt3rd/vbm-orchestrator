import VbmOrchestrator.Step
/-! # The reference model

The machine driven under the PORT DISCIPLINE, which is what an interpreter must keep: every action asks one port, and the event that follows answers it (a task is prepared, the
worker finishes, the lander validates, the reviewers answer, the Judge answers, the push lands, the cleanup is done); only the world's own interventions, a lost lease and the
deadline, arrive without having been asked for. `drive` refuses a sequence of events that breaks the discipline (an event that answers nothing pending) or that the machine would
silently ignore: a scenario that passes is one a correct interpreter can meet. The conformance vectors (`VbmOrchestrator.Vectors`) are such scenarios. -/
namespace VbmOrchestrator

/-- An event the world raises on its own, not in answer to an action. -/
def Event.external : Event → Bool
  | .leaseLost => true
  | .deadline => true
  | _ => false

/-- Does this event answer that action? -/
def Event.answers : Event → Action → Bool
  | .preparedOk, .prepare => true
  | .preparedFailed _, .prepare => true
  | .agentFinished _ _ _, .runAgent _ _ => true
  | .judged _, .askJudge _ _ _ => true
  | .validated _, .validate _ => true
  | .reviewed _, .review _ => true
  | .pushed _, .push _ => true
  | .cleaned, .cleanup => true
  | _, _ => false

/-- One step of a run: the event, and what the machine asked for in answer. -/
structure Step where
  event : Event
  actions : List Action
  deriving Repr

/-- Drive the machine through the events, keeping the port discipline. The result is the steps and the state it ends in, or why the sequence is not one a correct
interpreter could produce. -/
def drive (cfg : Config) : State → List Action → List Event → Except String (List Step × State)
  | s, _, [] => .ok ([], s)
  | s, pending, e :: es =>
    if !(e.external || pending.any e.answers) then .error "an event that answers no pending action, and is not the world's own"
    else
      let r := step cfg s e
      if decide (r.1 = s) && r.2.isEmpty then .error "an event the machine ignores (it changed nothing and asked for nothing)"
      else match drive cfg r.1 r.2 es with
        | .ok (steps, s') => .ok (⟨e, r.2⟩ :: steps, s')
        | .error m => .error m

/-- A run of the model from the start: the actions the machine asks before its first event are `prepare`. -/
def runModel (cfg : Config) (events : List Event) : Except String (List Step × State) :=
  drive cfg start.1 start.2 events

end VbmOrchestrator
