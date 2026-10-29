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
# ~$MODAL_USER/math-proof1), LEAN_CHECK_MEMORY_MIB, LEAN_CHECK_NO_CACHE.
set -euo pipefail

MODAL_USER=${MODAL_USER:-xyz}
USER_HOME=$(getent passwd "$MODAL_USER" | cut -d: -f6)
MODAL_BIN=${MODAL_BIN:-$USER_HOME/xyzenv/bin/modal}
MODAL_MIRROR=${MODAL_MIRROR:-$USER_HOME/math-proof1}
SRC=$(git -C "$(dirname "$0")/.." rev-parse --show-toplevel)

ARGS=$(printf '%q ' "$@")
ENVS="LEAN_CHECK_MEMORY_MIB=${LEAN_CHECK_MEMORY_MIB:-32768}"
if [ -n "${LEAN_CHECK_NO_CACHE:-}" ]; then
  ENVS="$ENVS LEAN_CHECK_NO_CACHE=$LEAN_CHECK_NO_CACHE"
fi

if [ "$(id -un)" = "$MODAL_USER" ]; then
  cd "$SRC"
  exec env $ENVS "$MODAL_BIN" run lean_check.py "$@"
fi

sudo -n rsync -a --delete --exclude .lake "$SRC/" "$MODAL_MIRROR/"
sudo -n chown -R "$MODAL_USER:$MODAL_USER" "$MODAL_MIRROR"
exec sudo -n -u "$MODAL_USER" env $ENVS \
  bash -lc "cd $(printf '%q' "$MODAL_MIRROR") && $(printf '%q' "$MODAL_BIN") run lean_check.py $ARGS"
