import VbmOrchestratorProofs.Safety
import VbmOrchestratorProofs.Shape
import VbmOrchestratorProofs.Model
import VbmOrchestratorProofs.Model
import VbmOrchestratorProofs.Witnesses
import LandLedger
/-! # The obligation ledger

Every claim the library makes, keyed by a slug and checked by `land-lean ledger`: a claim is `proved` only by naming theorems (double-backtick names are checked at
elaboration), `open_` while nothing is proved, or a `limit` no machine decides. -/
open Land.Ledger

def ledger : List Obligation := [
  O "closed-is-absorbing" (.proved [``VbmOrchestrator.step_closed, ``VbmOrchestrator.run_closed]),
  O "a-task-reports-at-most-once-and-an-abandoned-one-reports-nothing" (.proved [``VbmOrchestrator.report_origin, ``VbmOrchestrator.abandoned_reports_nothing,
    ``VbmOrchestrator.closing_reports, ``VbmOrchestrator.step_reports, ``VbmOrchestrator.reports_le_one]),
  O "a-task-cleans-up-exactly-once-on-every-path" (.proved [``VbmOrchestrator.cleanup_origin, ``VbmOrchestrator.entering_closing_cleans,
    ``VbmOrchestrator.step_cleanups, ``VbmOrchestrator.step_finished_stays, ``VbmOrchestrator.cleanups_le_one, ``VbmOrchestrator.cleanups_exact]),
  O "a-push-needs-a-validated-commit-and-reviews-that-cleared-it" (.proved [``VbmOrchestrator.push_origin]),
  O "a-task-lands-only-a-done-type-outcome" (.proved [``VbmOrchestrator.step_wf, ``VbmOrchestrator.start_wf, ``VbmOrchestrator.landed_report_is_done]),
  O "the-worker-runs-again-only-after-the-judge-says-progressing" (.proved [``VbmOrchestrator.first_run_origin, ``VbmOrchestrator.resume_origin]),
  O "an-unreachable-reviewer-never-lets-a-task-land-or-repair" (.proved [``VbmOrchestrator.unreviewed_closes]),
  O "the-deadline-and-a-lost-lease-always-close-a-task" (.proved [``VbmOrchestrator.deadline_closes, ``VbmOrchestrator.lease_lost_closes]),
  O "the-worker-runs-at-most-fuse-times" (.proved [``VbmOrchestrator.start_inv, ``VbmOrchestrator.step_inv, ``VbmOrchestrator.runs_le_fuse,
    ``VbmOrchestrator.rounds_le_fuse]),
  O "control-never-depends-on-prose" (.proved [``VbmOrchestrator.step_rel, ``VbmOrchestrator.run_rel, ``VbmOrchestrator.start_rel, ``VbmOrchestrator.no_prose]),
  O "the-reference-model-is-the-machine-under-the-port-discipline" (.proved [``VbmOrchestrator.drive_run]),
  O "every-conformance-scenario-obeys-the-port-discipline" (.proved [``VbmOrchestrator.scenarios_obey_the_discipline]),
  O "the-ports-meet-their-laws" (.limit "the workspace, the agent, the lander's two steps, the reviewers and the judge are bindings of the application; that they meet the laws the machine relies on (a round costs at least a picodollar, a push takes only a validated commit, an undecodable reviewer reply is reported as such) is carried by the conformance vectors (vectors/vbm-orchestrator-vectors-1.jsonl, which an interpreter's own tests run) and the application's own tests, not provable here")]
