# The trust ledger

What vbm-orchestrator relies on without proof: the facilities outside this repository that every proof and every run assumes. vbm-orchestrator is pure Lean (specifications, proofs, a reference model): it has no C, no foreign function and no vendored dependency, so nothing in its own tree is trusted code; its trusted base is the toolchain that checks and compiles it and the tools its scripts run.

Entry format: **What** it is; **Enters** where it enters; **Assumes** what we assume of it (the contract); **Test** the test that can fail; **Owner**; **Plan** (verify, replace, sandbox or accept, with a reason); **Covers** the keys it accounts for. `land-lean trust` derives what must be covered from the tree and `.land/lean.conf`, so a trusted thing cannot be left out unseen (vbm-land `docs/lean-gates.md`, guideline `mark-what-is-trusted.md` of the hub).

### T1. The Lean toolchain and the build pins
- **What:** the Lean compiler and kernel, the runtime (`lean.h`, `libleanrt`) and the bundled clang and ld.lld, pinned by `lean-toolchain` and `mise.toml`; `lakefile.lean` drives the build.
- **Enters:** `lean-toolchain`, `mise.toml`, `lakefile.lean`; the kernel checks every proof and the compiler produces every artifact built from this library.
- **Assumes:** the kernel is sound and the compiler is faithful (a miscompile would void what the proofs say about the compiled code): no written contract beyond the Lean project's own documentation.
- **Test:** the axiom gate (`.land/tool/bin/land-lean axiom`, configured by `.land/lean.conf`) fails when any constant depends on an axiom beyond the three standard ones; `lake build` re-checks every proof.
- **Owner:** the owner
- **Plan:** accept because the kernel and the compiler are outside this repository and every claim in it assumes them.
- **Covers:** `file:lean-toolchain` `file:mise.toml` `file:lakefile.lean` `lean-compiler` `lean-runtime` `clang-lld`

### T2. The tools the scripts run
- **What:** `lake` builds the library and its proofs; `mise` provides the pinned toolchain; `git` lists the files the checks read; `python3` runs the trust-ledger checker of the landing tool.
- **Enters:** `scripts/tier1.sh`, `lakefile.lean`.
- **Assumes:** each behaves as documented (a wrong build would be caught by the proofs, a wrong checker by its own negative self-tests): no written contract.
- **Test:** none beyond the tools' own; a wrong build fails the proofs.
- **Owner:** the owner
- **Plan:** accept because they are the host's own tools and nothing from them executes in an artifact.
- **Covers:** `tool:git` `tool:lake` `tool:mise` `tool:python3`

### T3. vbm-work: the vocabulary of work, a pinned library
- **What:** the library `vbm-work` (https://github.com/witt3rd/vbm-work), vendored at a signed release (`vendor/vbm-work/`, locked in `.land/pins.lock`): the typed outcome, the review words and the task this machine's data is built from. No C.
- **Enters:** `.land/pins.lock`, `lakefile.lean` (the `require`), `vendor/vbm-work/`; `VbmOrchestrator/Data.lean` imports it.
- **Assumes:** the library's own proofs and independent re-check; this repository does **not** re-prove them: the gate checks that the bytes are the bytes of the signed release (`land-pin verify`: the tree hash), never that they were proved; no written contract beyond the library's own ledger.
- **Test:** `scripts/tier1.sh` runs `land-pin verify` first (an edited, added or deleted file, an unlocked library or a second copy of one fails it).
- **Owner:** the owner (the lock is `.land/pins.lock`); upstream vbm-work is the same owner's.
- **Plan:** verify. Re-check the library's proof modules here so the recheck is ours rather than the library's; until then the pin is a trusted-by-hash claim and says so.
- **Covers:** `pin:vbm-work`

