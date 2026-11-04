#!/bin/bash
# Wave-worker liveness report — the artifact side of the §6 stuck-worker
# protocol (external-doc/RESEARCH-WORKFLOW.md).  One row per worker
# worktree: heartbeat ages + a LIVE/STALLED/IDLE flag.  The orchestrator
# combines this with its background-task polls (DEAD/HUNG/LOOPING/OVERDUE
# classification) — the script never kills anything.
#
#   tools/wave_watchdog.sh                 # survey: every worktree (stale = IDLE)
#   tools/wave_watchdog.sh hecke-tm hecke-field   # active set: stale = STALLED
#
# Ages reported (minutes): tip = last commit, dirty = uncommitted files,
# wl = WORKLOG mtime (+ last dated entry), art = newest worktree file
# (excl. .git/.lake), run = newest mirror run log (LOGDIR parsed from the
# worktree's mrun.sh; logs stream live, so an in-flight Modal run is fresh),
# modal = live modal-client processes matching the worktree's mirror path
# (only ever this worker's — never a sibling's).
#
# Flags: LIVE (any signal younger than the stall threshold, or a modal
# client alive); STALLED (every signal older, and the slug was named
# explicitly = the wave expects it running); IDLE (same staleness, survey
# mode).  Exit: 0 nothing stalled, 3 >= 1 stalled, 1 setup error.
#
# Overrides: WAVE_WT_ROOT (default /home/doz/claude-workdir/worktree/mp1),
# WAVE_WATCHDOG_STALL_MIN (default 60 — §6 HUNG threshold).
set -euo pipefail

WT_ROOT=${WAVE_WT_ROOT:-/home/doz/claude-workdir/worktree/mp1}
STALL_MIN=${WAVE_WATCHDOG_STALL_MIN:-60}
NOW=$(date +%s)

if [ ! -d "$WT_ROOT" ]; then
  echo "[watchdog] no worktree root at $WT_ROOT (nothing to watch)" >&2
  exit 1
fi

# Explicit slugs = the wave's active set (their staleness is STALLED);
# no args = cold survey of every worktree (staleness is only IDLE).
EXPLICIT=0
if [ $# -gt 0 ]; then EXPLICIT=1; fi

slug_list() {
  if [ $# -gt 0 ]; then printf '%s\n' "$@"; else ls -1 "$WT_ROOT"; fi
}

age_min() { # epoch -> minutes, or "-" for empty/0
  [ -n "${1:-}" ] && [ "$1" != 0 ] || { echo -; return; }
  echo $(( (NOW - $1) / 60 ))
}

trimmed() { printf '%s' "$1" | cut -c1-38 | tr '\n' ' '; }

rows_stalled=0
printf '%-14s %-8s %-32s %-8s %6s %5s %6s %-38s %6s %6s %s\n' \
  slug flag branch tip tipAge dirty wlAge lastWorklogEntry artAge runAge modal
printf '%.0s-' $(seq 1 132); echo

for slug in $(slug_list "$@"); do
  wt=$WT_ROOT/$slug
  if [ ! -d "$wt" ]; then
    printf '%-14s %-8s %s\n' "$slug" MISSING "no worktree at $wt"
    rows_stalled=$((rows_stalled + 1))
    continue
  fi

  branch=$(git -C "$wt" rev-parse --abbrev-ref HEAD 2>/dev/null || echo '?')
  tip=$(git -C "$wt" rev-parse --short HEAD 2>/dev/null || echo '?')
  tip_ct=$(git -C "$wt" log -1 --format=%ct HEAD 2>/dev/null || echo 0)
  dirty=$(git -C "$wt" status --porcelain 2>/dev/null | wc -l || true)

  # heartbeat: newest WORKLOG under blueprint/*/ (missing WORKLOG is itself
  # a signal — the hecke-tm lesson: a worker that never wrote one)
  wl_file=$(ls -1 "$wt"/blueprint/*/WORKLOG.md 2>/dev/null | head -1 || true)
  wl_ct=0; wl_entry="-"
  if [ -n "$wl_file" ]; then
    wl_ct=$(stat -c %Y "$wl_file" 2>/dev/null || echo 0)
    wl_entry=$(trimmed "$(grep '^### ' "$wl_file" 2>/dev/null | tail -1 || true)")
  fi

  # any writing at all in the worktree (excluding .git/.lake); `|| true`
  # because head's early exit trips pipefail on an empty tree
  art_ct=$(find "$wt" \( -name .git -o -name .lake \) -prune -o \
    -type f -printf '%T@\n' 2>/dev/null | sort -rn | head -1 | cut -d. -f1 || true)
  art_ct=${art_ct:-0}

  # newest run log: LOGDIR from the worktree's mrun.sh, else the default
  # agent-work layout; logs stream (tee) so in-flight runs stay fresh
  rundir=""
  if [ -f "$wt/mrun.sh" ]; then
    rundir=$(sed -n 's/^LOGDIR=//p' "$wt/mrun.sh" | head -1)
  fi
  [ -n "$rundir" ] || rundir=/home/doz/tmp/math-proof1-temp/agent-work/$slug/runs
  run_ct=0
  if [ -d "$rundir" ]; then
    newest=$(ls -1t "$rundir" 2>/dev/null | head -1 || true)
    if [ -n "$newest" ]; then
      run_ct=$(stat -c %Y "$rundir/$newest" 2>/dev/null || echo 0)
    fi
  fi

  # live modal client for THIS worker only: its mirror path from mrun.sh
  mirror=""
  if [ -f "$wt/mrun.sh" ]; then
    mirror=$(sed -n 's/^MIRROR=//p' "$wt/mrun.sh" | head -1)
  fi
  nproc_alive=0
  if [ -n "$mirror" ]; then
    nproc_alive=$(pgrep -f -- "$mirror" 2>/dev/null | wc -l || true)
  fi

  # freshest artifact signal (0 = none known)
  freshest=0
  for ct in "$wl_ct" "$art_ct" "$run_ct"; do
    if [ "$ct" -gt "$freshest" ]; then freshest=$ct; fi
  done
  fresh_min=$(( (NOW - freshest) / 60 ))

  if [ "$nproc_alive" -gt 0 ]; then
    flag=LIVE; note="modal($nproc_alive)"
  elif [ "$freshest" -gt 0 ] && [ "$fresh_min" -le "$STALL_MIN" ]; then
    flag=LIVE; note=no
  elif [ "$EXPLICIT" -eq 1 ]; then
    flag=STALLED; rows_stalled=$((rows_stalled + 1)); note=no
  else
    flag=IDLE; note=no
  fi

  printf '%-14s %-8s %-32s %-8s %6s %5s %6s %-38s %6s %6s %s\n' \
    "$slug" "$flag" "$branch" "$tip" "$(age_min "$tip_ct")" "$dirty" \
    "$(age_min "$wl_ct")" "$wl_entry" "$(age_min "$art_ct")" \
    "$(age_min "$run_ct")" "$note"
done

echo
if [ "$rows_stalled" -gt 0 ]; then
  echo "[watchdog] $rows_stalled stalled (explicit slug; §6: classify with the task poll)"
  exit 3
fi
echo "[watchdog] no stalled workers (survey mode flags stale rows IDLE)"
exit 0
