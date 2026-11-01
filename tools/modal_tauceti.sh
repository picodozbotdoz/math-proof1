#!/bin/bash
# Check a TauCeti port branch on Modal (lean_tauceti.py, app `tauceti-check`).
#
#   tools/modal_tauceti.sh [<branch> ...]      # default: every pr* branch, in order
#
# For each branch the .lean files it adds/changes relative to `main` of the
# local TauCeti clone ($TAUCETI_CLONE, default ~/zcode-workdir/tauceti) are
# staged into a world-readable temp dir (the Modal user `xyz` cannot read
# /home/doz), then `modal run lean_tauceti.py` runs as xyz.  Branches are
# cumulative (prNN contains pr01..prNN-1), so only files new in each branch
# vs its predecessor are checked; earlier ones are overlaid too (needed as
# imports) but not rebuilt-and-audited again.
set -euo pipefail

CLONE=${TAUCETI_CLONE:-$HOME/zcode-workdir/tauceti}
MODAL_USER=${MODAL_USER:-xyz}
USER_HOME=$(getent passwd "$MODAL_USER" | cut -d: -f6)
MODAL_BIN=${MODAL_BIN:-$USER_HOME/xyzenv/bin/modal}
MODAL_MIRROR=${MODAL_MIRROR:-$USER_HOME/math-proof1}
SRC=$(git -C "$(dirname "$0")/.." rev-parse --show-toplevel)
# Persistent default (survives reboots; /tmp is wiped on this machine).
STAGE=${TAUCETI_STAGE:-/home/doz/tmp/math-proof1-temp/tauceti-stage}

if [ $# -eq 0 ]; then
  mapfile -t BRANCHES < <(git -C "$CLONE" for-each-ref --format='%(refname:short)' --sort=refname 'refs/heads/pr*')
else
  BRANCHES=("$@")
fi

sudo -n rsync -a --delete --exclude .lake --exclude .git "$SRC/lean_tauceti.py" "$MODAL_MIRROR/"
rc_all=0
prev=main
for b in "${BRANCHES[@]}"; do
  d=$STAGE/$b
  rm -rf "$d"; mkdir -p "$d"
  mapfile -t NEW < <(git -C "$CLONE" diff --name-only --diff-filter=AM "$prev" "$b" -- '*.lean')
  mapfile -t ALL < <(git -C "$CLONE" diff --name-only --diff-filter=AM main "$b" -- '*.lean')
  for f in "${ALL[@]}"; do
    mkdir -p "$d/$(dirname "$f")"
    git -C "$CLONE" show "$b:$f" > "$d/$f"
  done
  # check the new files, but ship all files up to this branch
  printf '%s\n' "${NEW[@]}" > "$d/ORDER"
  for f in "${ALL[@]}"; do echo "$f" >> "$d/ORDER.all"; done
  chmod -R a+rX "$d"
  echo "##### $b: ${NEW[*]}"
  set +e
  sudo -n -u "$MODAL_USER" bash -lc "cd $(printf '%q' "$MODAL_MIRROR") && $(printf '%q' "$MODAL_BIN") run lean_tauceti.py --dir $(printf '%q' "$d")"
  rc=$?
  set -e
  [ $rc -ne 0 ] && rc_all=$rc && echo "##### $b FAILED (rc=$rc)" && break
  prev=$b
done
exit $rc_all
