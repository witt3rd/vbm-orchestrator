#!/usr/bin/env bash
# Tier 1 (pre-landing gate): forbidden constructs, the import rule, the vendored lander's drift check, zero-warning build, the axiom gate, the public-readiness lint,
# and the offline self-tests of the process scripts. Every gate has a negative self-test and runs it here; every gate and test prints ran-evidence (a gate that ran zero cases FAILS).
# Run from the repo root: mise exec -- scripts/tier1.sh.
set -euo pipefail
cd "$(dirname "$0")/.."
# RAN-EVIDENCE (.land/tool/docs/ran-evidence.md): every test script and every concurrent gate ends with `ran: NAME: N cases` (N > 0, or the gate's own count line named in scripts/ran-gates.txt);
# .land/tool/bin/run-tests-parallel and the check below FAIL a job without it, and a refused tool, a SKIPPED check or a stop by a guard is a failure, never a pass. The tools are the vendored ones: land-check refuses an edited copy.
# The vendored libraries are exactly their pins (vbm-land docs/pin.md): the same first step in every repository (this one vendors none today).
.land/tool/bin/land-pin verify

tests=(); par() { tests+=("$@"); }   # independent test scripts, run in parallel at the end; every scripts/test_*.sh must be declared
bgdir=$(mktemp -d); bgnames=()
bg() { local n=$1; shift; bgnames+=("$n"); ( "$@" ) > "$bgdir/$n.log" 2>&1 & echo $! > "$bgdir/$n.pid"; }
bgwait() { local bad=0 n; for n in "${bgnames[@]}"; do if wait "$(cat "$bgdir/$n.pid")"; then cat "$bgdir/$n.log"; else echo "tier1: FAILED: $n" >&2; cat "$bgdir/$n.log" >&2; bad=1; fi; done; [ $bad = 0 ] || exit 1; }
lean_sources() { find VbmWork VbmWorkProofs vectors -name '*.lean' 2>/dev/null; ls VbmWork.lean VbmWorkProofs.lean 2>/dev/null; }

# 1. Forbidden constructs anywhere in Lean sources (AGENTS.md). A comment may mention one only on a line marked `-- tier1-allow`.
forbidden() { grep -HnE '\b(sorry|admit|axiom|unsafe|implemented_by|csimp)\b' "$@" | grep -v 'tier1-allow' || true; }
bad=$(forbidden $(lean_sources))
if [ -n "$bad" ]; then echo "tier1: forbidden construct(s):" >&2; echo "$bad" >&2; exit 1; fi
st=$(mktemp); trap 'rm -f "$st"; rm -rf "$bgdir"' EXIT
for w in sorry admit axiom unsafe implemented_by csimp; do
  echo "theorem t : True := by $w" > "$st"; [ -n "$(forbidden "$st")" ] || { echo "tier1: the forbidden-constructs scan does not flag '$w'" >&2; exit 1; }
done
echo "-- a comment that says sorry -- tier1-allow" > "$st"; [ -z "$(forbidden "$st")" ] || { echo "tier1: the tier1-allow marker is not honoured" >&2; exit 1; }
echo "-- a comment that says sorry" > "$st"; [ -n "$(forbidden "$st")" ] || { echo "tier1: an unmarked comment is not flagged" >&2; exit 1; }
echo "tier1: forbidden-constructs scan: negative self-tests ok (each forbidden word is flagged, the tier1-allow marker is honoured)"

# 1a. VbmWork/ imports Init (implicitly) and other VbmWork modules only: no Std, no Lean, no VbmWorkProofs, no `prelude`.
bad_imports() { grep -HnE '^[[:space:]]*((public|meta|private)[[:space:]]+)*(import|prelude)\b' "$@" | grep -vE ':[0-9]+:import VbmWork(\.[A-Za-z0-9_]+)*[[:space:]]*$' || true; }
bad=$(bad_imports $(find VbmWork -name '*.lean') VbmWork.lean)
if [ -n "$bad" ]; then echo "tier1: VbmWork may import only VbmWork modules (Init is implicit):" >&2; echo "$bad" >&2; exit 1; fi
for imp in 'import Lean' 'import Std.Data.HashMap' 'import VbmWorkProofs.State' 'prelude' 'public import Lean.Data.Json' 'import VbmWorkX'; do
  printf '%s\n' "$imp" > "$st"; [ -n "$(bad_imports "$st")" ] || { echo "tier1: the import scan does not flag: $imp" >&2; exit 1; }
done
printf 'import VbmWork.State\n' > "$st"; [ -z "$(bad_imports "$st")" ] || { echo "tier1: the import scan flags an allowed import" >&2; exit 1; }
echo "tier1: import scan: negative self-tests ok (each import outside Init and VbmWork is flagged)"

scripts/lint-pipefail.sh   # a producer piped into an early-exiting consumer is flaky by construction; the lint has a negative self-test
.land/tool/bin/land-check   # the vendored lander is the pinned copy (no local patch), offline

# 2. Build, zero warnings (scripts/check-zero-warning.sh: the warning's own diagnostic is required, a clean file must pass; prints `ran: zero-warning: 3 cases`).
scripts/check-zero-warning.sh
lake build VbmWork VbmWorkProofs LandLedger   # once, for the gates and every test (they build nothing more)

# 2a. The axiom gate: every constant of ours depends only on propext, Classical.choice, Quot.sound (--selftest: a non-standard axiom is rejected).
bg axiom-gate .land/tool/bin/land-lean axiom --selftest
.land/tool/bin/land-lean trust   # the trust ledger (docs/trust-ledger.md): what cannot be proven is marked as trusted, and what must be marked is derived from the tree (vbm-land docs/lean-gates.md)
.land/tool/bin/land-lean recheck --selftest   # every proof replayed by Lean's own checker in a fresh process (vbm-land docs/lean-gates.md)
.land/tool/bin/land-lean ledger --selftest   # the obligation ledger: docs/proof-ledger.md rendered, every theorem checked, the ratchet (vbm-land docs/lean-gates.md)
# 2d. The public-readiness lint: no private name, no path of ours, anywhere in the tree; it is shown able to fail.
par scripts/test_lint_public.sh
# 2e. The test-running runtime (ran-evidence, the parallel runner) is the vendored tool's and is tested in vbm-land. Every concurrent gate must say how its count is read: a `bg NAME` of this script has a line in
# scripts/ran-gates.txt, or prints its own `ran: NAME: N cases` (the tests job does).
for g in $(sed -nE 's/^bg ([A-Za-z0-9_-]+) .*/\1/p' scripts/tier1.sh); do
  [ "$g" = tests ] && continue
  grep -qE "^$g " scripts/ran-gates.txt || { echo "tier1: the concurrent gate $g has no line in scripts/ran-gates.txt: its count is not required" >&2; exit 1; }
done

for f in scripts/test_*.sh; do case " ${tests[*]} " in *" $f "*) ;; *) echo "tier1: $f is not declared with par" >&2; exit 1;; esac; done
echo "tier1: ${#tests[@]} test scripts: ${tests[*]}"
bg tests .land/tool/bin/run-tests-parallel "${tests[@]}"
bgwait
.land/tool/bin/ran-evidence check-dir "$bgdir" scripts/ran-gates.txt   # every concurrent gate and the tests job ran something
echo "tier1: ok"
