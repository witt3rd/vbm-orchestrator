import Lean.Data.Json
import VbmOrchestrator
/-! The vector generator `vbm-orchestrator-vectors-1`. The scenarios and the machine's answers come from the Lean reference (`VbmOrchestrator.Vectors`, `VbmOrchestrator.step`);
this executable only writes them, one JSON object per line.
  vbm-orchestrator-vectors [--out FILE]   write the scenarios to FILE or stdout, each run under the port discipline (a scenario the discipline refuses stops the generation)
  vbm-orchestrator-vectors --check FILE   the file's lines are exactly what the reference gives (a tampered, dropped or added line fails)
  vbm-orchestrator-vectors --selftest     the discipline can refuse: an event that answers nothing pending, an event after closed -/
open Lean VbmOrchestrator VbmWork

def argOf (args : List String) (k : String) : Option String :=
  match args.dropWhile (· != k) with | _ :: v :: _ => some v | _ => none

def arr (xs : List Json) : Json := Json.arr xs.toArray
def optS : Option String → Json | some s => Json.str s | none => Json.null

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
def pushJ : PushResult → Json
  | .landed s => Json.mkObj [("result", "landed"), ("sha", s)]
  | .baseMoved => Json.mkObj [("result", "baseMoved")]
  | .refused w => Json.mkObj [("result", "refused"), ("words", w)]
def answerJ : ReviewAnswer → Json
  | .ok r => Json.mkObj [("findings", arr (r.map findingJ))]
  | .error e => Json.mkObj [("undecodable", e.detail)]
def judgeJ : JudgeAnswer → String
  | .progressing => "progressing"
  | .stuck => "stuck"
  | .unavailable => "unavailable"
def eventJ : Event → Json
  | .preparedOk => Json.mkObj [("event", "preparedOk")]
  | .preparedFailed w => Json.mkObj [("event", "preparedFailed"), ("words", w)]
  | .agentFinished o c n => Json.mkObj [("event", "agentFinished"), ("outcome", outcomeJ o), ("commit", optS c), ("cost", toJson n)]
  | .validated v => Json.mkObj [("event", "validated"), ("answer", validateJ v)]
  | .reviewed as => Json.mkObj [("event", "reviewed"), ("answers", arr (as.map answerJ))]
  | .judged a => Json.mkObj [("event", "judged"), ("answer", judgeJ a)]
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

/-- One scenario as one line: the configuration, what the machine asks before any event, each event with what the machine asks in answer, and where it ends. -/
def lineOf (sc : Scenario) : Except String String := do
  let (steps, s) ← runModel sc.cfg sc.events
  let stepJ (st : Step) : Json := Json.mkObj [("event", eventJ st.event), ("asks", arr (st.actions.map actionJ))]
  pure (Json.compress (Json.mkObj [("name", sc.name), ("config", configJ sc.cfg), ("start", arr (start.2.map actionJ)),
    ("steps", arr (steps.map stepJ)), ("final", Json.mkObj [("phase", phaseJ s.phase), ("spent", toJson s.spent)])]))

def generate : Except String (List String) := scenarios.mapM fun sc => (lineOf sc).mapError fun m => s!"scenario {sc.name}: {m}"

/-- Scenarios the discipline must refuse: the vector check could not catch a bad scenario if these passed. -/
def badScenarios : List Scenario := [
  ⟨"answers-nothing-pending", ⟨10, []⟩, [.preparedOk, .cleaned]⟩,
  ⟨"event-after-closed", ⟨10, []⟩, [.preparedFailed "x", .cleaned, .preparedOk]⟩,
  ⟨"wrong-answer-for-the-action", ⟨10, []⟩, [.preparedOk, .validated (.passed "r")]⟩]

def main (args : List String) : IO UInt32 := do
  if args.contains "--selftest" then
    for sc in badScenarios do
      match lineOf sc with
      | .ok _ => IO.eprintln s!"selftest: the discipline accepted the bad scenario {sc.name}"; return 1
      | .error _ => pure ()
    match generate with
    | .ok ls => if ls.isEmpty then IO.eprintln "selftest: no scenarios"; return 1
    | .error m => IO.eprintln s!"selftest: {m}"; return 1
    IO.println "selftest ok (the discipline refuses an event that answers nothing pending, an event after closed and a wrong answer)"
    return 0
  match generate with
  | .error m => IO.eprintln m; return 1
  | .ok ls =>
    let text := "\n".intercalate ls ++ "\n"
    if let some f := argOf args "--check" then
      let got ← IO.FS.readFile f
      if got == text then IO.println s!"ok: {ls.length} scenarios"; return 0
      else IO.eprintln s!"{f} is not what the reference gives (a tampered, dropped or added line)"; return 1
    match argOf args "--out" with
    | some f => IO.FS.writeFile f text
    | none => IO.print text
    return 0
