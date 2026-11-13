import Lean.Data.Json
import VbmOrchestratorWire
/-! The vector generator `vbm-orchestrator-vectors-1`. The scenarios and the machine's answers come from the Lean reference (`VbmOrchestrator.Vectors`, `VbmOrchestrator.step`);
this executable only writes them, one JSON object per line, with the wire library (`VbmOrchestratorWire`).
  vbm-orchestrator-vectors [--out FILE]   write the scenarios to FILE or stdout, each run under the port discipline (a scenario the discipline refuses stops the generation)
  vbm-orchestrator-vectors --check FILE   the file's lines are exactly what the reference gives (a tampered, dropped or added line fails)
  vbm-orchestrator-vectors --roundtrip FILE   every line decodes and encodes back to exactly itself (the wire's conformance test)
  vbm-orchestrator-vectors --selftest     the discipline can refuse: an event that answers nothing pending, an event after closed -/
open Lean VbmOrchestrator VbmOrchestrator.Wire VbmWork

def argOf (args : List String) (k : String) : Option String :=
  match args.dropWhile (· != k) with | _ :: v :: _ => some v | _ => none

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

def roundtrip (f : String) : IO UInt32 := do
  let text ← IO.FS.readFile f
  let mut n := 0
  for l in text.splitOn "\n" do
    if l.isEmpty then continue
    match Json.parse l with
    | .error e => IO.eprintln s!"{f}: line {n + 1} is not JSON: {e}"; return 1
    | .ok j =>
      match vectorOf j with
      | .error e => IO.eprintln s!"{f}: line {n + 1} does not decode: {e}"; return 1
      | .ok v =>
        if Json.compress v.toJson != Json.compress j then IO.eprintln s!"{f}: line {n + 1} ({v.name}) does not encode back to itself"; return 1
    n := n + 1
  IO.println s!"ok: {n} scenarios decode and encode back to themselves"
  return 0

def main (args : List String) : IO UInt32 := do
  if let some f := argOf args "--roundtrip" then return (← roundtrip f)
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
