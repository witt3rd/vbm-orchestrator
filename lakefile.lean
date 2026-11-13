import Lake
open System Lake DSL

package «vbm-orchestrator» where
  leanOptions := #[⟨`warningAsError, true⟩, ⟨`autoImplicit, false⟩]

/-- The vocabulary of work (the typed outcome, the review words, the task): the one dependency, vendored at a signed release. -/
require «vbm-work» from "vendor/vbm-work"

/-- The library: specification and code, one Lean core. Imports `Init` and itself only (checked by Tier 1). No dependency. -/
@[default_target]
lean_lib VbmOrchestrator where
  globs := #[.andSubmodules `VbmOrchestrator]

/-- The proofs: may import `Std` and `Lean`; NEVER linked (nothing in `VbmOrchestrator` may import it). -/
lean_lib VbmOrchestratorProofs where
  globs := #[.andSubmodules `VbmOrchestratorProofs]

/-- The landing tool's Lean modules (the obligation-ledger vocabulary and the reach walk, `land-lean ledger`), a small package it ships; required, never declared here, so a repository that vendors this library and requires it too shares one copy. -/
require «land-ledger» from ".land/tool/lean"

/-- The wire: JSON for the machine's data, both ways. A BINDING (it may import `Lean`; nothing in `VbmOrchestrator` imports it): the vectors and an interpreter's own records use it. -/
lean_lib VbmOrchestratorWire where
  globs := #[.one `VbmOrchestratorWire]

/-- The vector generator (`vbm-orchestrator-vectors-1`): the scenarios and the machine's answers come from the Lean reference only; this executable only writes them. Not part of the library. -/
lean_exe «vbm-orchestrator-vectors» where
  srcDir := "vectors"
  root := `Main
