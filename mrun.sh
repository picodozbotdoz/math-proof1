#!/bin/bash
# Modal runner for the maeda-galois-full WORKTREE.  The worktree's .git is a
# dangling pointer for user xyz, so instead of tools/modal_run.sh we maintain
# a standalone git mirror at ~xyz/t3-galois-small whose refs/remotes/
# origin/master is the EMPTY TREE; `git diff --name-only origin/master` then
# lists EVERY file and lean_check.py overlays the complete worktree state
# (needed because GitHub master is behind this branch).
#
# Usage: mrun.sh [--file F | --target M | --target '' ] (lean_check.py args)
# Env passthrough: LEAN_CHECK_MEMORY_MIB LEAN_CHECK_NO_CACHE LEAN_CHECK_PROFILE
#                  LEAN_CHECK_MEM_ALERT_GIB
set -euo pipefail

WT=/home/doz/claude-workdir/worktree/mp1/t3-galois-small
MIRROR=/home/xyz/t3-galois-small
LOGDIR=/home/doz/tmp/math-proof1-temp/agent-work/t3-galois-small/runs
EMPTY_TREE=4b825dc642cb6eb9a060e54bf8d69288fbee4904
mkdir -p "$LOGDIR"

# 1. mirror the worktree (no .git, no .lake)
sudo -n rsync -a --delete --exclude .git --exclude .lake "$WT/" "$MIRROR/"
sudo -n chown -R xyz:xyz "$MIRROR"

# 2. standalone git repo with origin/master := empty tree
sudo -n -u xyz bash -lc "cd ~/t3-galois-small && \
  { [ -d .git ] || { git init -q && git config user.email agent@local && git config user.name agent && git update-ref refs/remotes/origin/master $EMPTY_TREE; }; } && \
  git add -A && git commit -q -m 'sync from worktree' --allow-empty"

# 3. run lean_check.py as xyz
ARGS=""
if [ $# -gt 0 ]; then ARGS=$(printf '%q ' "$@"); fi
ENVS="LEAN_CHECK_MEMORY_MIB=${LEAN_CHECK_MEMORY_MIB:-8192}"
for v in LEAN_CHECK_NO_CACHE LEAN_CHECK_PROFILE LEAN_CHECK_MEM_ALERT_GIB; do
  if [ -n "${!v:-}" ]; then ENVS="$ENVS $v=${!v}"; fi
done

LOG=$LOGDIR/run-$(date +%Y%m%d-%H%M%S)-$$.log
set +e
sudo -n -u xyz env $ENVS \
  bash -lc "cd ~/t3-galois-small && ~/xyzenv/bin/modal run lean_check.py $ARGS" 2>&1 | tee "$LOG"
rc=${PIPESTATUS[0]}
set -e

# 4. memory alerts -> research/memory-alerts.md in the worktree (AGENTS policy)
if [ -z "${LEAN_CHECK_PROFILE:-}" ] && [ -f "$LOG" ] && grep -q '^\[memory-alert\]' "$LOG"; then
  {
    echo "## $(date -u +%Y-%m-%dT%H:%MZ) — OPEN (maeda-galois-full mirror run)"
    echo
    echo "- command: \`mrun.sh $*\` (rc=$rc)"
    echo "- log: \`$LOG\`"
    echo "- alert:"
    echo
    echo '  ```'
    grep -E '^\[(memory-alert|memory)\]' "$LOG" | sed 's/^/  /'
    echo '  ```'
    echo "- investigation: _pending_"
    echo
  } >> "$WT/research/memory-alerts.md"
fi
exit "$rc"
