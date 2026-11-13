import Lean.Data.Json
import VbmOrchestrator
/-! # The wire: JSON for the machine's data, both ways

A BINDING, not the specification: it only moves the machine's data to and from JSON (the conformance vectors, and an interpreter's own records), and it decides nothing. Words are those of
`vbm-work` (`Tag`, `Kind`, `Severity`): a word that names none is an error, never a default. The conformance vectors are its test: every event and action of every vector decodes and
encodes back to exactly the line it came from (`vbm-orchestrator-vectors --roundtrip`). -/
namespace VbmOrchestrator.Wire
open Lean VbmWork

def arr (xs : List Json) : Json := Json.arr xs.toArray
def optS : Option String → Json | some s => Json.str s | none => Json.null

/-! ## Encoding -/

def citationJ (c : Citation) : Json := Json.mkObj [("call", c.call), ("span", c.span)]
def outcomeJ : Outcome → Json
  | .done cs => Json.mkObj [("outcome", "done"), ("citations", arr (cs.map citationJ))]
  | .doneWithAssumptions as cs => Json.mkObj [("outcome", "done_with_assumptions"), ("assumptions", arr (as.map Json.str)), ("citations", arr (cs.map citationJ))]
  | .blocked k r cs => Json.mkObj [("outcome", "blocked"), ("kind", k.name), ("reason", r), ("citations", arr (cs.map citationJ))]
  | .needsClarification q d cs => Json.mkObj [("outcome", "needs_clarification"), ("question", q), ("default", d), ("citations", arr (cs.map citationJ))]
def findingJ (f : Finding) : Json := Json.mkObj [("declaration", f.declaration), ("severity", f.severity.name), ("why", f.why)]
def feedbackJ : Feedback → Json
  | .checks r => Json.mkObj [("feedback", "checks"), ("report", r)]
  | .conflict r => Json.mkObj [("feedback", "conflict"), ("report", r)]
  | .findings fs => Json.mkObj [("feedback", "findings"), ("findings", arr (fs.map findingJ))]
def validateJ : ValidateResult → Json
  | .passed c => Json.mkObj [("result", "passed"), ("commit", c)]
  | .failed r => Json.mkObj [("result", "failed"), ("report", r)]
  | .conflict r => Json.mkObj [("result", "conflict"), ("report", r)]
  | .refused => Json.mkObj [("result", "refused")]
  | .unavailable w => Json.mkObj [("result", "unavailable"), ("why", w)]
def pushJ : PushResult → Json
  | .landed s => Json.mkObj [("result", "landed"), ("sha", s)]
  | .baseMoved => Json.mkObj [("result", "baseMoved")]
  | .refused w => Json.mkObj [("result", "refused"), ("words", w)]
def answerJ : ReviewAnswer → Json
  | .ok r => Json.mkObj [("findings", arr (r.map findingJ))]
  | .error e => Json.mkObj [("undecodable", e.detail)]
def judgeS : JudgeAnswer → String
  | .progressing => "progressing"
  | .stuck => "stuck"
  | .unavailable => "unavailable"
def eventJ : Event → Json
  | .preparedOk => Json.mkObj [("event", "preparedOk")]
  | .preparedFailed w => Json.mkObj [("event", "preparedFailed"), ("words", w)]
  | .agentFinished o c n => Json.mkObj [("event", "agentFinished"), ("outcome", outcomeJ o), ("commit", optS c), ("cost", toJson n)]
  | .validated v => Json.mkObj [("event", "validated"), ("answer", validateJ v)]
  | .reviewed as => Json.mkObj [("event", "reviewed"), ("answers", arr (as.map answerJ))]
  | .judged a => Json.mkObj [("event", "judged"), ("answer", judgeS a)]
  | .pushed p => Json.mkObj [("event", "pushed"), ("answer", pushJ p)]
  | .cleaned => Json.mkObj [("event", "cleaned")]
  | .leaseLost => Json.mkObj [("event", "leaseLost")]
  | .deadline => Json.mkObj [("event", "deadline")]
def modeJ : AgentMode → Json
  | .first => Json.mkObj [("mode", "first")]
  | .resume fb => Json.mkObj [("mode", "resume"), ("feedback", feedbackJ fb)]
def actionJ : Action → Json
  | .prepare => Json.mkObj [("action", "prepare")]
  | .runAgent r m => Json.mkObj [("action", "runAgent"), ("round", toJson r), ("session", modeJ m)]
  | .askJudge r fb n => Json.mkObj [("action", "askJudge"), ("round", toJson r), ("feedback", feedbackJ fb), ("spent", toJson n)]
  | .validate c => Json.mkObj [("action", "validate"), ("commit", c)]
  | .review c => Json.mkObj [("action", "review"), ("commit", c)]
  | .push c => Json.mkObj [("action", "push"), ("commit", c)]
  | .cleanup => Json.mkObj [("action", "cleanup")]
  | .report o l => Json.mkObj [("action", "report"), ("outcome", outcomeJ o), ("landed", optS l)]
def phaseJ : Phase → Json
  | .preparing => Json.mkObj [("phase", "preparing")]
  | .working r => Json.mkObj [("phase", "working"), ("round", toJson r)]
  | .validating r _ => Json.mkObj [("phase", "validating"), ("round", toJson r)]
  | .judging r fb => Json.mkObj [("phase", "judging"), ("round", toJson r), ("feedback", feedbackJ fb)]
  | .reviewing r _ _ => Json.mkObj [("phase", "reviewing"), ("round", toJson r)]
  | .pushing r _ _ => Json.mkObj [("phase", "pushing"), ("round", toJson r)]
  | .closing o l => Json.mkObj [("phase", "closing"), ("outcome", match o with | some o => outcomeJ o | none => Json.null), ("landed", optS l)]
  | .closed => Json.mkObj [("phase", "closed")]
def configJ (c : Config) : Json := Json.mkObj [("fuse", toJson c.fuse), ("reviewers", arr (c.reviewers.map Json.str))]

/-! ## Decoding: nothing is repaired, defaulted or guessed -/

def getStr (j : Json) (k : String) : Except String String := do (← j.getObjVal? k).getStr?
def getNat (j : Json) (k : String) : Except String Nat := do (← j.getObjVal? k).getNat?
def getList (j : Json) (k : String) : Except String (List Json) := do pure (← (← j.getObjVal? k).getArr?).toList
def getOptStr (j : Json) (k : String) : Except String (Option String) := do
  match ← j.getObjVal? k with
  | .null => pure none
  | .str s => pure (some s)
  | _ => throw s!"{k} must be a string or null"
def strs (xs : List Json) : Except String (List String) := xs.mapM fun x => x.getStr?

def citationOf (j : Json) : Except String Citation := do pure ⟨← getStr j "call", ← getStr j "span"⟩
def outcomeOf (j : Json) : Except String Outcome := do
  let cs ← (← getList j "citations").mapM citationOf
  match ← getStr j "outcome" with
  | "done" => pure (.done cs)
  | "done_with_assumptions" => pure (.doneWithAssumptions (← strs (← getList j "assumptions")) cs)
  | "blocked" =>
    let kn ← getStr j "kind"
    match Kind.ofName kn with
    | some k => pure (.blocked k (← getStr j "reason") cs)
    | none => throw s!"{kn} names no kind"
  | "needs_clarification" => pure (.needsClarification (← getStr j "question") (← getStr j "default") cs)
  | w => throw s!"{w} names no outcome"
def findingOf (j : Json) : Except String Finding := do
  let sn ← getStr j "severity"
  match Severity.ofName? sn with
  | some s => pure ⟨← getStr j "declaration", s, ← getStr j "why"⟩
  | none => throw s!"{sn} names no severity"
def feedbackOf (j : Json) : Except String Feedback := do
  match ← getStr j "feedback" with
  | "checks" => pure (.checks (← getStr j "report"))
  | "conflict" => pure (.conflict (← getStr j "report"))
  | "findings" => pure (.findings (← (← getList j "findings").mapM findingOf))
  | w => throw s!"{w} names no feedback"
def validateOf (j : Json) : Except String ValidateResult := do
  match ← getStr j "result" with
  | "passed" => pure (.passed (← getStr j "commit"))
  | "failed" => pure (.failed (← getStr j "report"))
  | "conflict" => pure (.conflict (← getStr j "report"))
  | "refused" => pure .refused
  | "unavailable" => pure (.unavailable (← getStr j "why"))
  | w => throw s!"{w} names no validation result"
def pushOf (j : Json) : Except String PushResult := do
  match ← getStr j "result" with
  | "landed" => pure (.landed (← getStr j "sha"))
  | "baseMoved" => pure .baseMoved
  | "refused" => pure (.refused (← getStr j "words"))
  | w => throw s!"{w} names no push result"
def answerOf (j : Json) : Except String ReviewAnswer :=
  match j.getObjVal? "undecodable" with
  | .ok d => do pure (.error ⟨← d.getStr?⟩)
  | .error _ => do pure (.ok (← (← getList j "findings").mapM findingOf))
def judgeOf (s : String) : Except String JudgeAnswer :=
  match s with
  | "progressing" => pure .progressing
  | "stuck" => pure .stuck
  | "unavailable" => pure .unavailable
  | w => throw s!"{w} names no judge answer"
def eventOf (j : Json) : Except String Event := do
  match ← getStr j "event" with
  | "preparedOk" => pure .preparedOk
  | "preparedFailed" => pure (.preparedFailed (← getStr j "words"))
  | "agentFinished" => pure (.agentFinished (← outcomeOf (← j.getObjVal? "outcome")) (← getOptStr j "commit") (← getNat j "cost"))
  | "validated" => pure (.validated (← validateOf (← j.getObjVal? "answer")))
  | "reviewed" => pure (.reviewed (← (← getList j "answers").mapM answerOf))
  | "judged" => pure (.judged (← judgeOf (← getStr j "answer")))
  | "pushed" => pure (.pushed (← pushOf (← j.getObjVal? "answer")))
  | "cleaned" => pure .cleaned
  | "leaseLost" => pure .leaseLost
  | "deadline" => pure .deadline
  | w => throw s!"{w} names no event"
def modeOf (j : Json) : Except String AgentMode := do
  match ← getStr j "mode" with
  | "first" => pure .first
  | "resume" => pure (.resume (← feedbackOf (← j.getObjVal? "feedback")))
  | w => throw s!"{w} names no mode"
def actionOf (j : Json) : Except String Action := do
  match ← getStr j "action" with
  | "prepare" => pure .prepare
  | "runAgent" => pure (.runAgent (← getNat j "round") (← modeOf (← j.getObjVal? "session")))
  | "askJudge" => pure (.askJudge (← getNat j "round") (← feedbackOf (← j.getObjVal? "feedback")) (← getNat j "spent"))
  | "validate" => pure (.validate (← getStr j "commit"))
  | "review" => pure (.review (← getStr j "commit"))
  | "push" => pure (.push (← getStr j "commit"))
  | "cleanup" => pure .cleanup
  | "report" => pure (.report (← outcomeOf (← j.getObjVal? "outcome")) (← getOptStr j "landed"))
  | w => throw s!"{w} names no action"
def configOf (j : Json) : Except String Config := do pure ⟨← getNat j "fuse", ← strs (← getList j "reviewers")⟩

/-- One scenario of the vectors, decoded: its name, configuration, the events in order with the actions the machine asks in answer, and what it asks first. -/
structure Vector where
  name : String
  cfg : Config
  start : List Action
  steps : List (Event × List Action)
  final : Json

def vectorOf (j : Json) : Except String Vector := do
  let steps ← (← getList j "steps").mapM fun s => do
    pure (← eventOf (← s.getObjVal? "event"), ← (← getList s "asks").mapM actionOf)
  pure ⟨← getStr j "name", ← configOf (← j.getObjVal? "config"), ← (← getList j "start").mapM actionOf, steps, ← j.getObjVal? "final"⟩

/-- The scenario as the line it came from: the decoded data encoded again. -/
def Vector.toJson (v : Vector) : Json :=
  Json.mkObj [("name", v.name), ("config", configJ v.cfg), ("start", arr (v.start.map actionJ)),
    ("steps", arr (v.steps.map fun (e, as) => Json.mkObj [("event", eventJ e), ("asks", arr (as.map actionJ))])), ("final", v.final)]

end VbmOrchestrator.Wire
