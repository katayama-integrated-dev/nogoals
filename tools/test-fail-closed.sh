#!/usr/bin/env bash
# Negative controls for the transactional build:
#   1. a green build promotes the candidate to the output directory;
#   2. a red gate leaves the previous (green) output byte-for-byte untouched,
#      quarantines the candidate in <out>.failed/, and exits nonzero;
#   3. the quarantined candidate's receipt records the failed gate — and a
#      normal (non-audit) build's receipt records audit gates as "skipped",
#      never "checked", with an empty required list;
#   4. under --audit a MISSING permalink baseline is a red gate, not a skip;
#   6. a report tree that is not well-formed is rejected after the gates
#      (--force-late-failure), leaving the previous output untouched;
#   5. --update-baseline with an existing baseline is ignored (the baseline is
#      a record of production, written by deploy.sh).
# Run from the SITE root (the wrapper in scripts/ does): lake exe build-site must work there.
set -euo pipefail

workdir=$(mktemp -d)
out="$workdir/site"
trap 'rm -rf "$workdir"; [[ -f deploy/permalink-baseline.txt.bak ]] && mv deploy/permalink-baseline.txt.bak deploy/permalink-baseline.txt || true' EXIT

fail() { echo "✗ FAIL-CLOSED TEST: $1" >&2; exit 1; }

echo "── fail-closed test: green build ──"
lake exe build-site "$out" >/dev/null || fail "green build should succeed"
[ -f "$out/index.html" ] || fail "green build produced no index.html"
[ -f "$out/verification/receipt.json" ] || fail "green build produced no receipt"
[ -f "$out/_redirects" ] || fail "green build produced no _redirects"

# 3a. Non-audit receipt: profile 'build', nothing required, no gate claimed.
[ "$(jq -r '.profile.name' "$out/verification/receipt.json")" = "build" ] || fail "non-audit receipt does not say profile build"
[ "$(jq -r '.profile.required | length' "$out/verification/receipt.json")" = "0" ] || fail "non-audit receipt requires gates"
if [ "$(jq -r '[.guarantees[] | select(.id | startswith("gate.")) | select(.tier == "checked")] | length' "$out/verification/receipt.json")" != "0" ]; then
  fail "non-audit receipt claims a gate ran"
fi
[ "$(jq -r '[.guarantees[] | select(.tier == "skipped")] | length' "$out/verification/receipt.json")" -gt 0 ] \
  || fail "non-audit receipt records no skipped checks"

# Sentinel: any change to the last green build must be detectable.
touch "$out/SENTINEL"
sum_before=$(find "$out" -type f | sort | xargs shasum | shasum)

echo "── fail-closed test: forced red gate ──"
if lake exe build-site "$out" --force-gate-failure >/dev/null; then
  fail "red build exited 0"
fi
[ -f "$out/SENTINEL" ] || fail "red build touched the last green output"
sum_after=$(find "$out" -type f | sort | xargs shasum | shasum)
[ "$sum_before" = "$sum_after" ] || fail "red build modified the last green output"
[ -d "$out.failed" ] || fail "red build left no quarantined candidate"
[ ! -d "$out.staging" ] || fail "red build left a staging directory behind"
grep -q '"id":"gate.negative-control"' "$out.failed/verification/receipt.json" \
  || fail "quarantined receipt does not record the failed gate"
grep -q '"tier":"failed"' "$out.failed/verification/receipt.json" \
  || fail "quarantined receipt reports no failure"

echo "── fail-closed test: a report tree that is not well-formed is rejected after the gates ──"
rm -rf "$out.failed"
if lake exe build-site "$out" --force-late-failure >"$workdir/late.log" 2>&1; then
  fail "late-failure build exited 0"
fi
grep -q 'report tree is not well-formed' "$workdir/late.log" || fail "late failure was not the report well-formedness check"
[ -f "$out/SENTINEL" ] || fail "late failure touched the last green output"
sum_after=$(find "$out" -type f | sort | xargs shasum | shasum)
[ "$sum_before" = "$sum_after" ] || fail "late failure modified the last green output"
[ -d "$out.failed" ] || fail "late failure left no quarantined candidate"
[ ! -d "$out.staging" ] || fail "late failure left a staging directory behind"

echo "── fail-closed test: missing baseline under --audit is red ──"
mv deploy/permalink-baseline.txt deploy/permalink-baseline.txt.bak
if lake exe build-site "$out" --audit --offline >/dev/null 2>&1; then
  mv deploy/permalink-baseline.txt.bak deploy/permalink-baseline.txt
  fail "audit with no baseline exited 0"
fi
[ -f "$out/SENTINEL" ] || fail "red audit touched the last green output"
jq -e '.guarantees[] | select(.id == "gate.permalinks") | select(.tier == "failed")' "$out.failed/verification/receipt.json" >/dev/null \
  || fail "quarantined receipt does not record gate.permalinks as failed"
mv deploy/permalink-baseline.txt.bak deploy/permalink-baseline.txt

echo "── fail-closed test: --update-baseline leaves an existing baseline alone ──"
before=$(shasum deploy/permalink-baseline.txt)
lake exe build-site "$out" --update-baseline 2>&1 | grep -q 'update-baseline ignored' \
  || fail "existing baseline was not protected from --update-baseline"
[ "$before" = "$(shasum deploy/permalink-baseline.txt)" ] || fail "--update-baseline rewrote an existing baseline"

echo "── fail-closed test: green build after red ──"
lake exe build-site "$out" >/dev/null || fail "green rebuild should succeed"
[ ! -f "$out/SENTINEL" ] || fail "green promote did not replace the output"
[ ! -d "$out.previous" ] || fail "green promote left the previous output behind"

echo "✓ fail-closed: red gates never touch the output; green promotes cleanly; baselines are protected"
