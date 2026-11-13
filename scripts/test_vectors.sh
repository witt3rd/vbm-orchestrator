#!/usr/bin/env bash
# Tier 1: the conformance vectors (vbm-orchestrator-vectors-1). The scenarios and the machine's answers come from the Lean reference (VbmOrchestrator.Vectors, VbmOrchestrator.step); the generator
# only writes them, one JSON line per scenario, each run under the port discipline (an event must answer the pending action or be the world's own, and the machine must not ignore it). The checked-in
# file (vectors/vbm-orchestrator-vectors-1.jsonl) must be exactly what the reference gives now, so a change of the machine or of a scenario is visible and a regeneration is a decision
# (`scripts/test_vectors.sh --write`); the check can fail (a tampered action, a dropped scenario and an added one are each rejected, and so are bad scenarios).
# Run from the repo root as `mise exec -- scripts/test_vectors.sh`. It builds nothing but the generator (tier1.sh has built the library).
set -euo pipefail
cd "$(dirname "$0")/.."
. .land/tool/lib/ran.sh   # ran_case counts each executed check, ran_done prints the evidence line `ran: NAME: N cases` (.land/tool/docs/ran-evidence.md)
f=vectors/vbm-orchestrator-vectors-1.jsonl
fail() { echo "test_vectors: $*" >&2; exit 1; }
T=$(mktemp -d); trap 'rm -rf "$T"' EXIT
lake build vbm-orchestrator-vectors >/dev/null
gen() { lake exe vbm-orchestrator-vectors "$@"; }
gen --out "$T/gen.jsonl" 2>"$T/err" || { cat "$T/err" >&2; fail "the generator failed (a scenario breaks the port discipline, or the build is broken)"; }
if [ "${1:-}" = --write ]; then cp "$T/gen.jsonl" "$f"; echo "test_vectors: wrote $f ($(wc -l < "$f") scenarios)"; exit 0; fi
[ -f "$f" ] && ran_case || fail "$f is missing"
cmp -s "$f" "$T/gen.jsonl" && ran_case || fail "$f is not what the reference gives now (the machine or a scenario changed); regenerate with scripts/test_vectors.sh --write and review the diff"
gen --check "$f" >/dev/null && ran_case || fail "the checked-in file does not pass its own check"
gen --selftest >/dev/null && ran_case || fail "the generator's own check cannot refuse a bad scenario"
gen --roundtrip "$f" >/dev/null && ran_case || fail "a line of the vectors does not decode and encode back to itself (the wire)"
n=$(wc -l < "$f"); [ "$n" -ge 20 ] && ran_case || fail "only $n scenarios"
# negative: an action tampered, a scenario dropped, a scenario added are each rejected, for the reason the check gives
sed '3s/"action":"validate"/"action":"push"/' "$f" > "$T/bad1.jsonl"; cmp -s "$f" "$T/bad1.jsonl" && fail "the tamper did not change the file"
must_fail "--check rejects a tampered action" gen --check "$T/bad1.jsonl"
sed '5d' "$f" > "$T/bad2.jsonl"; must_fail "--check rejects a dropped scenario" gen --check "$T/bad2.jsonl"
cp "$f" "$T/bad3.jsonl"; sed -n 1p "$f" >> "$T/bad3.jsonl"; must_fail "--check rejects an added scenario" gen --check "$T/bad3.jsonl"
sed '3s/"event":"preparedOk"/"event":"preparedMaybe"/' "$f" > "$T/bad4.jsonl"; cmp -s "$f" "$T/bad4.jsonl" && fail "the word tamper did not change the file"
must_fail "--roundtrip rejects an event word that names no event" gen --roundtrip "$T/bad4.jsonl"
python3 - "$f" "$T/bad5.jsonl" <<'PY'
import json,sys
out=[]
for l in open(sys.argv[1]):
    d=json.loads(l)
    for st in d["steps"]:
        if st["event"]["event"]=="agentFinished": st["event"].pop("cost"); break
    out.append(json.dumps(d,separators=(",",":")))
    break
open(sys.argv[2],"w").write("\n".join(out)+"\n")
PY
must_fail "--roundtrip rejects an event with a missing field" gen --roundtrip "$T/bad5.jsonl"
ran_done test_vectors
echo "test_vectors: ok ($n scenarios; every one runs under the port discipline; tampered, dropped and added lines are rejected)"
