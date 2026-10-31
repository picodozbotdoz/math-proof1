#!/bin/bash
# Run lean_check.py on the canonical Modal account (Linux user `xyz` since
# 2026-10-29; the doz workspace is invalid error).  All arguments pass
# through to lean_check.py, e.g.
#
#   tools/modal_run.sh --target MathProof.ModularForms.Poly5
#   LEAN_CHECK_MEMORY_MIB=131072 tools/modal_run.sh --file MathProof/Foo.lean
#
# The Modal user cannot read the caller's home, so the working tree (with
# .git, which lean_check.py's overlay detection needs; without .lake) is
# mirrored into that user's home first and `modal run` is started as that
# user via passwordless sudo.  When the caller *is* the Modal user, the
# script runs in place.
#
# Overrides: MODAL_USER (default xyz), MODAL_BIN (default
# ~$MODAL_USER/xyzenv/bin/modal), MODAL_MIRROR (default
# ~$MODAL_USER/math-proof1), MODAL_RUN_LOG_DIR; passed through to lean_check.py:
# LEAN_CHECK_MEMORY_MIB, LEAN_CHECK_NO_CACHE, LEAN_CHECK_PROFILE,
# LEAN_CHECK_MEM_ALERT_GIB.
set -euo pipefail

MODAL_USER=${MODAL_USER:-xyz}
USER_HOME=$(getent passwd "$MODAL_USER" | cut -d: -f6)
MODAL_BIN=${MODAL_BIN:-$USER_HOME/xyzenv/bin/modal}
MODAL_MIRROR=${MODAL_MIRROR:-$USER_HOME/math-proof1}
SRC=$(git -C "$(dirname "$0")/.." rev-parse --show-toplevel)

ARGS=""
if [ $# -gt 0 ]; then ARGS=$(printf '%q ' "$@"); fi
# Memory request ladder (research/iteration21/MEMORY-RIGHTSIZING.md): start at
# 8192 MiB (covers every light/CI module measured), auto-escalate on OOM
# (lean_check exits 42 with an `[memory] OOM likely` marker) to 16384 / 32768;
# heavier targets need an explicit LEAN_CHECK_MEMORY_MIB (e.g. 98304).
MIB=${LEAN_CHECK_MEMORY_MIB:-8192}
ENVS=""
for v in LEAN_CHECK_NO_CACHE LEAN_CHECK_PROFILE LEAN_CHECK_MEM_ALERT_GIB; do
  if [ -n "${!v:-}" ]; then ENVS="$ENVS $v=${!v}"; fi
done

# Every run's output is kept; a `[memory-alert]` (lake tree >= 16 GiB) is
# appended to research/memory-alerts.md as an OPEN entry to investigate
# (AGENTS.md, "Memory alerts").  Profile runs are the investigation itself and
# are not recorded again.
# Persistent default (survives reboots; /tmp is wiped on this machine):
# /home/doz/tmp/math-proof1-temp/mathproof-runs, overridable via
# MODAL_RUN_LOG_DIR / MATHPROOF_TMP_DIR; falls back to /tmp when the
# persistent root is not writable (e.g. in-place runs as the Modal user).
LOG_DIR=${MODAL_RUN_LOG_DIR:-${MATHPROOF_TMP_DIR:-/home/doz/tmp/math-proof1-temp}/mathproof-runs}
mkdir -p "$LOG_DIR" 2>/dev/null || true
if [ ! -w "$LOG_DIR" ]; then LOG_DIR=${TMPDIR:-/tmp}/mathproof-runs; mkdir -p "$LOG_DIR"; fi
LOG=$LOG_DIR/run-$(date +%Y%m%d-%H%M%S)-$$.log

run() {
  local envs="LEAN_CHECK_MEMORY_MIB=${MIB}${ENVS:+ $ENVS}"
  if [ "$(id -un)" = "$MODAL_USER" ]; then
    (cd "$SRC" && env $envs "$MODAL_BIN" run lean_check.py "$@")
  else
    sudo -n rsync -a --delete --exclude .lake "$SRC/" "$MODAL_MIRROR/"
    sudo -n chown -R "$MODAL_USER:$MODAL_USER" "$MODAL_MIRROR"
    sudo -n -u "$MODAL_USER" env $envs \
      bash -lc "cd $(printf '%q' "$MODAL_MIRROR") && $(printf '%q' "$MODAL_BIN") run lean_check.py $ARGS"
  fi
}

set +e
while :; do
  LOG=$LOG_DIR/run-$(date +%Y%m%d-%H%M%S)-$$-m${MIB}.log
  run "$@" 2>&1 | tee "$LOG"
  rc=${PIPESTATUS[0]}
  if [ "$rc" = 42 ] || grep -q '^\[memory\] OOM likely' "$LOG"; then
    case $MIB in
      8192)  MIB=16384; echo "[memory] OOM: escalating request to ${MIB} MiB, retrying"; continue;;
      16384) MIB=32768; echo "[memory] OOM: escalating request to ${MIB} MiB, retrying"; continue;;
      *) echo "[memory] OOM even at ${MIB} MiB: pass an explicit LEAN_CHECK_MEMORY_MIB" \
         "(e.g. 98304 for LehmerPacked-class targets)";;
    esac
  fi
  break
done
set -e

if [ -z "${LEAN_CHECK_PROFILE:-}" ] && grep -q '^\[memory-alert\]' "$LOG"; then
  ALERTS=$SRC/research/memory-alerts.md
  {
    echo "## $(date -u +%Y-%m-%dT%H:%MZ) — OPEN"
    echo
    echo "- command: \`tools/modal_run.sh $*\` (rc=$rc)"
    echo "- log: \`$LOG\`"
    echo "- alert:"
    echo
    echo '  ```'
    grep -E '^\[(memory-alert|memory)\]' "$LOG" | sed 's/^/  /'
    echo '  ```'
    echo
    echo "- investigation: _pending — run the LEAN_CHECK_PROFILE command above, record the"
    echo "  top declarations and the cause, then mark this entry CLOSED._"
    echo
  } >> "$ALERTS"
  echo "[memory-alert] recorded as OPEN in research/memory-alerts.md" >&2
fi
exit "$rc"
