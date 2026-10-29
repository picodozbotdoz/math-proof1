#!/bin/bash
# Staged build of the heavy MaedaGalois5 chain, one `lean_check` run per
# module, stopping at the first failing stage.  lean_check.py saves its
# rolling build cache after every run, so a rerun resumes where it failed:
#
#   tools/stage_chain.sh                       # whole chain
#   tools/stage_chain.sh MaedaGalois5IdE6      # resume from this stage
#
# Never run two heavy stages concurrently: both restore the same cache
# tarball and the later save replaces the earlier one.
#
# Memory requests (MiB).  Modal's limit is soft.  Since the recurrence +
# checkpoint rewrite of tools/gen_poly5.py (research/poly5-memory-study) every
# kernel `decide` in the chain is budgeted to ≈ 0.5–0.9 M modelled list
# operations (≈ 15–25 GiB at the measured ≈ 27 GiB per M ops); before it the
# peaks were IdE4 202 GiB, IdE5 137 GiB, IdE6 172 GiB.  Measured after it
# (2026-10-29): IdBase 8.1, IdE4 13.5, IdE5 22.0, IdE6 34.7, Identities
# 17.6, MaedaGalois5 6.6, Weights 6.3 GiB; ≈ 33 min for the whole chain.
# LEAN_CHECK_MEMORY_MIB overrides every stage; logs go to $STAGE_LOG_DIR.
STAGES=(
  "MaedaGalois5Defs 32768"
  "MaedaGalois5IdBase 49152"
  "MaedaGalois5IdE4 49152"
  "MaedaGalois5IdE5 49152"
  "MaedaGalois5IdE6 49152"
  "MaedaGalois5Identities 32768"
  "MaedaGalois5 32768"
  "MaedaGalois5Weights 32768"
)
RUN=$(dirname "$0")/modal_run.sh
LOG_DIR=${STAGE_LOG_DIR:-${TMPDIR:-/tmp}/mathproof-stages}
mkdir -p "$LOG_DIR"

start=${1:-}
started=$([ -z "$start" ] && echo 1 || echo 0)
for entry in "${STAGES[@]}"; do
  read -r t mem <<<"$entry"
  [ "$t" = "$start" ] && started=1
  [ "$started" = 1 ] || continue
  log=$LOG_DIR/stage_$t.log
  LEAN_CHECK_MEMORY_MIB=${LEAN_CHECK_MEMORY_MIB:-$mem} \
    "$RUN" --target "MathProof.ModularForms.$t" >"$log" 2>&1
  rc=$?
  echo "== $t rc=$rc $(grep -E '\[telemetry\] wall=' "$log" | tail -1)"
  grep -E '\[cache\]' "$log"
  grep -E '^(✔|⚠|✖).*MaedaGalois5|^error' "$log" | cut -c1-220 | head -25
  [ $rc -ne 0 ] && exit $rc
done
[ "$started" = 1 ] || { echo "unknown stage: $start" >&2; exit 2; }
echo ALL_OK
