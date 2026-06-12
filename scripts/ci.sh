#!/usr/bin/env bash
# JSCore₀ CI gate — RESEARCH.md Phase 0.5.
#
# Enforces:
#   1. Lean library builds (includes #guard semantics regression tests in JSCore/Tests.lean)
#   2. Examples build (all checked-in proofs verify)
#   3. No `sorry` outside the allowlist (TaintSoundness — tracked debt, RESEARCH.md Phase 2)
#   4. No `native_decide` in the trusted library (kernel-only; examples tracked as P1)
#   5. Extractor round-trip: re-extracting examples/*.ts is a no-op
#      (idempotence + proof-preserving merge)
set -euo pipefail
cd "$(dirname "$0")/.."
export PATH="$HOME/.elan/bin:$PATH"

echo "== 1/5 build Lean library (jscore/) =="
(cd jscore && lake build JSCore)

echo "== 2/5 build examples =="
(cd examples && lake build)

echo "== 3/5 sorry audit =="
SORRYS=$(grep -rn --include="*.lean" -w "sorry" jscore/JSCore examples \
  | grep -v "Metatheory/TaintSoundness.lean" || true)
if [ -n "$SORRYS" ]; then
  echo "FAIL: unexpected sorry:"
  echo "$SORRYS"
  exit 1
fi
echo "ok (only the tracked TaintSoundness sorry remains)"

echo "== 4/5 native_decide audit (trusted library must be kernel-only) =="
ND=$(grep -rn --include="*.lean" "native_decide" jscore/JSCore || true)
if [ -n "$ND" ]; then
  echo "FAIL: native_decide in the trusted library:"
  echo "$ND"
  exit 1
fi
echo "ok (library is native_decide-free; example usage is tracked P1 work)"

echo "== 5/5 extractor round-trip =="
before=$(shasum examples/*_jscore.lean | shasum | cut -d' ' -f1)
(cd extractor && npx tsx src/index.ts extract --out-dir ../examples ../examples/*.ts > /dev/null)
after=$(shasum examples/*_jscore.lean | shasum | cut -d' ' -f1)
if [ "$before" != "$after" ]; then
  echo "FAIL: extractor not idempotent over examples/ (or merge dropped proofs):"
  git --no-pager diff --stat examples/
  exit 1
fi
echo "ok (re-extraction is a no-op)"

echo
echo "CI gate passed."
