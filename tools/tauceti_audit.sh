#!/usr/bin/env bash
# Static TauCeti-compliance audit of MathProof/**.lean (no build needed).
# Usage: tools/tauceti_audit.sh [file ...]   (default: every MathProof module)
# Prints: file  lines  set_option  #eval  native_decide  sorry  non-Mathlib-imports
cd "$(dirname "$0")/.." || exit 1
files=("$@"); [ ${#files[@]} -eq 0 ] && mapfile -t files < <(find MathProof -name '*.lean' | sort)
printf '%-52s %6s %4s %5s %4s %5s %s\n' file lines sopt eval nat sorry bad-imports
for f in "${files[@]}"; do
  c() { grep -cE "$1" "$f" | tr -d '\n'; }
  bad=$(grep -E '^import (Lean|Lake|Std)(\.|$)' "$f" | sed 's/import //' | tr '\n' ',')
  printf '%-52s %6s %4s %5s %4s %5s %s\n' "$f" "$(wc -l <"$f")" "$(c '^\s*(set_option|open .* in set_option)|set_option')" \
    "$(c '#eval')" "$(c 'native_decide')" "$(c '\bsorry\b')" "${bad%,}"
done
