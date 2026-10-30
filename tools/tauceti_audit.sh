#!/usr/bin/env bash
# Static TauCeti-compliance audit of MathProof/**.lean (no build needed).
# Usage: tools/tauceti_audit.sh [file ...]   (default: every MathProof module)
# Prints: file  lines  set_option  #eval  native_decide  sorry  non-Mathlib-imports
cd "$(dirname "$0")/.." || exit 1
files=("$@"); [ ${#files[@]} -eq 0 ] && mapfile -t files < <(find MathProof -name '*.lean' | sort)
printf '%-52s %6s %4s %5s %4s %5s %s\n' file lines sopt eval nat sorry bad-imports
# Strip Lean comments (/- -/ blocks and -- to end of line) before matching, so
# mentions inside docstrings/comments (e.g. "no `native_decide`") do not count.
strip_comments() { python3 - "$1" <<'PY'
import re, sys
src = open(sys.argv[1]).read()
src = re.sub(r'/-!.*?-/|/-.*?-/|/-.*\Z', '', src, flags=re.S)
src = re.sub(r'--.*', '', src)
sys.stdout.write(src)
PY
}
for f in "${files[@]}"; do
  c() { strip_comments "$f" | grep -cE "$1" | tr -d '\n'; }
  bad=$(grep -E '^import (Lean|Lake|Std)(\.|$)' "$f" | sed 's/import //' | tr '\n' ',')
  printf '%-52s %6s %4s %5s %4s %5s %s\n' "$f" "$(wc -l <"$f")" "$(c 'set_option')" \
    "$(c '#eval')" "$(c 'native_decide')" "$(c '\bsorry\b')" "${bad%,}"
done
