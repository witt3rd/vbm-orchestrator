import VbmOrchestrator.Model
/-! # The conformance scenarios

Each is a configuration and the events a port-disciplined run raises. The machine's answers (the actions) are NOT written here: they are computed by the machine, and the
vector generator writes both. An interpreter conforms when, with its ports answering the events in order (an answering event when the call returns, an external event at its
place), it makes exactly the calls the vector lists. -/
namespace VbmOrchestrator
open VbmWork

structure Scenario where
  name : String
  cfg : Config
  events : List Event

private def cfg0 : Config := ⟨10, []⟩
private def cfgR : Config := ⟨10, ["correctness"]⟩
private def cfgRR : Config := ⟨10, ["correctness", "rules"]⟩
private def done : Outcome := .done []
private def fix1 : Finding := ⟨"VbmWork.verdict", .fix, "a proof is missing"⟩
private def note1 : Finding := ⟨"VbmWork.hasFix", .note, "a name could be clearer"⟩
private def okR (r : Review) : ReviewAnswer := .ok r
private def noReply : ReviewAnswer := .error ⟨"no reply"⟩
private def work (commit : String) (cost : Nat) : Event := .agentFinished done (some commit) cost

def scenarios : List Scenario := [
  ⟨"success-no-reviewers", cfg0, [.preparedOk, work "c1" 3, .validated (.passed "r1"), .pushed (.landed "sha1"), .cleaned]⟩,
  ⟨"success-one-reviewer-clean", cfgR, [.preparedOk, work "c1" 3, .validated (.passed "r1"), .reviewed [okR []], .pushed (.landed "sha1"), .cleaned]⟩,
  ⟨"success-two-reviewers-notes-only", cfgRR, [.preparedOk, work "c1" 3, .validated (.passed "r1"), .reviewed [okR [note1], okR []], .pushed (.landed "sha1"), .cleaned]⟩,
  ⟨"success-done-with-assumptions", cfg0, [.preparedOk, .agentFinished (.doneWithAssumptions ["the base is green"] []) (some "c1") 3, .validated (.passed "r1"), .pushed (.landed "sha1"), .cleaned]⟩,
  ⟨"repair-after-red-checks", cfg0, [.preparedOk, work "c1" 3, .validated (.failed "red: 2 tests failed"), .judged .progressing, work "c2" 2, .validated (.passed "r2"), .pushed (.landed "sha2"), .cleaned]⟩,
  ⟨"repair-after-conflict", cfg0, [.preparedOk, work "c1" 3, .validated (.conflict "x.txt conflicts with main"), .judged .progressing, work "c2" 2, .validated (.passed "r2"), .pushed (.landed "sha2"), .cleaned]⟩,
  ⟨"repair-after-reviewer-fix", cfgR, [.preparedOk, work "c1" 3, .validated (.passed "r1"), .reviewed [okR [fix1]], .judged .progressing, work "c2" 2, .validated (.passed "r2"), .reviewed [okR []], .pushed (.landed "sha2"), .cleaned]⟩,
  ⟨"two-repairs-then-lands", cfg0, [.preparedOk, work "c1" 2, .validated (.failed "red one"), .judged .progressing, work "c2" 2, .validated (.failed "red two"), .judged .progressing, work "c3" 2, .validated (.passed "r3"), .pushed (.landed "sha3"), .cleaned]⟩,
  ⟨"judge-stuck-closes-as-checks-failed", cfg0, [.preparedOk, work "c1" 3, .validated (.failed "red: 2 tests failed"), .judged .stuck, .cleaned]⟩,
  ⟨"judge-unavailable-fails-closed", cfg0, [.preparedOk, work "c1" 3, .validated (.failed "red: 2 tests failed"), .judged .unavailable, .cleaned]⟩,
  ⟨"judge-stuck-on-conflict", cfg0, [.preparedOk, work "c1" 3, .validated (.conflict "x.txt"), .judged .stuck, .cleaned]⟩,
  ⟨"judge-stuck-on-findings", cfgR, [.preparedOk, work "c1" 3, .validated (.passed "r1"), .reviewed [okR [fix1]], .judged .stuck, .cleaned]⟩,
  ⟨"unreachable-reviewer", cfgR, [.preparedOk, work "c1" 3, .validated (.passed "r1"), .reviewed [noReply], .cleaned]⟩,
  ⟨"one-reviewer-unreachable-other-found-a-fix", cfgRR, [.preparedOk, work "c1" 3, .validated (.passed "r1"), .reviewed [okR [fix1], noReply], .cleaned]⟩,
  ⟨"worker-blocked-passes-through", cfg0, [.preparedOk, .agentFinished (.blocked .readOnlyPath "the path is read-only" []) none 2, .cleaned]⟩,
  ⟨"worker-needs-clarification-passes-through", cfg0, [.preparedOk, .agentFinished (.needsClarification "which file?" "the first" []) none 1, .cleaned]⟩,
  ⟨"worker-done-but-nothing-changed", cfg0, [.preparedOk, .agentFinished done none 2, .cleaned]⟩,
  ⟨"validation-refused-protected-path", cfg0, [.preparedOk, work "c1" 3, .validated .refused, .cleaned]⟩,
  ⟨"fuse-at-the-first-round", ⟨5, []⟩, [.preparedOk, work "c1" 7, .cleaned]⟩,
  ⟨"fuse-inside-a-repair", cfg0, [.preparedOk, work "c1" 6, .validated (.failed "red"), .judged .progressing, work "c2" 5, .cleaned]⟩,
  ⟨"deadline-while-working", cfg0, [.preparedOk, .deadline, .cleaned]⟩,
  ⟨"deadline-while-reviewing", cfgR, [.preparedOk, work "c1" 3, .validated (.passed "r1"), .deadline, .cleaned]⟩,
  ⟨"lease-lost-while-reviewing-reports-nothing", cfgR, [.preparedOk, work "c1" 3, .validated (.passed "r1"), .leaseLost, .cleaned]⟩,
  ⟨"lease-lost-before-the-worker-answers", cfg0, [.preparedOk, .leaseLost, .cleaned]⟩,
  ⟨"workspace-could-not-be-prepared", cfg0, [.preparedFailed "disk full", .cleaned]⟩,
  ⟨"push-refused-by-the-remote", cfg0, [.preparedOk, work "c1" 3, .validated (.passed "r1"), .pushed (.refused "protected branch"), .cleaned]⟩,
  ⟨"base-moved-twice-then-lands", cfg0, [.preparedOk, work "c1" 3, .validated (.passed "r1"), .pushed .baseMoved, .validated (.passed "r2"), .pushed .baseMoved, .validated (.passed "r3"), .pushed (.landed "sha3"), .cleaned]⟩,
  ⟨"base-moved-then-the-checks-fail-and-are-repaired", cfg0, [.preparedOk, work "c1" 3, .validated (.passed "r1"), .pushed .baseMoved, .validated (.failed "red on the new base"), .judged .progressing, work "c2" 2, .validated (.passed "r2"), .pushed (.landed "sha2"), .cleaned]⟩
]

end VbmOrchestrator
