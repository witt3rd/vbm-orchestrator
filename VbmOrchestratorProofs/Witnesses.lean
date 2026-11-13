import VbmOrchestratorProofs.Safety
/-! # Witnesses: concrete runs

Each is a whole run, computed. They show that the hypotheses of the theorems can hold (a full success, a repair the Judge allows, a task the Judge stops, the money
ceiling, an unreachable reviewer, a lost lease), and they are the first conformance scenarios. -/
namespace VbmOrchestrator
open VbmWork

def noReviewers : Config := ⟨10, []⟩
def oneReviewer : Config := ⟨10, ["correctness"]⟩

/-- A full success: prepared, the worker is done, the lander validated and pushed, cleaned up, reported once. -/
example : run noReviewers start.1
    [.preparedOk, .agentFinished (.done []) (some "c1") 3, .validated (.passed "r1"), .pushed (.landed "sha"), .cleaned] =
    ({ phase := .closed, spent := 3 },
     [.runAgent 1 .first, .validate "c1", .push "r1", .cleanup, .report (.done []) (some "sha")]) := by decide

/-- A failed check, the Judge says `progressing`: the same session continues, in round 2, with the whole report. -/
example : (run noReviewers start.1
    [.preparedOk, .agentFinished (.done []) (some "c1") 3, .validated (.failed "red: 2 tests"), .judged .progressing]).2 =
    [.runAgent 1 .first, .validate "c1", .askJudge 1 (.checks "red: 2 tests") 3, .runAgent 2 (.resume (.checks "red: 2 tests"))] := by decide

/-- The Judge says `stuck`: the task closes as the kind of its last failure, with the failure whole. -/
example : (run noReviewers start.1
    [.preparedOk, .agentFinished (.done []) (some "c1") 3, .validated (.failed "red: 2 tests"), .judged .stuck, .cleaned]).2 =
    [.runAgent 1 .first, .validate "c1", .askJudge 1 (.checks "red: 2 tests") 3, .cleanup,
     .report (.blocked .checksFailed "red: 2 tests" []) none] := by decide

/-- A judge that cannot be reached is read as `stuck`: the decision fails closed. -/
example : (step noReviewers { phase := .judging 1 (.checks "red"), spent := 3 } (.judged .unavailable)).1.phase =
    .closing (some (.blocked .checksFailed "red" [])) none := by decide

/-- The money ceiling: a round that reaches the fuse closes the task, whatever the worker said. -/
example : (run noReviewers start.1 [.preparedOk, .agentFinished (.done []) (some "c1") 10]).1.phase =
    .closing (some (.blocked .fuse "the task reached its money ceiling" [])) none := by decide

/-- An unreachable reviewer: the task closes as `unableToReview` and nothing lands. -/
example : (run oneReviewer start.1
    [.preparedOk, .agentFinished (.done []) (some "c1") 3, .validated (.passed "r1"), .reviewed [.error ⟨"no reply"⟩]]).2 =
    [.runAgent 1 .first, .validate "c1", .review "r1", .cleanup] := by decide

/-- A lost lease: the task cleans up and reports nothing. -/
example : run noReviewers start.1 [.preparedOk, .leaseLost, .cleaned] =
    ({ phase := .closed, spent := 0 }, [.runAgent 1 .first, .cleanup]) := by decide

/-- A moved base is re-validated without costing a round. -/
example : (run noReviewers start.1
    [.preparedOk, .agentFinished (.done []) (some "c1") 3, .validated (.passed "r1"), .pushed .baseMoved]).2 =
    [.runAgent 1 .first, .validate "c1", .push "r1", .validate "c1"] := by decide

end VbmOrchestrator
