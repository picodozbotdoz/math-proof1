import MathProof

/-!
# Axiom audit of every `decide` certificate in the light library

The proof standard (CLAUDE.md) asks computational facts to depend on
`propext` only.  `#audit_decide_certs` walks every theorem defined in a
`MathProof.*` module whose proof is a `decide` / `decide +kernel` certificate
(the proof term is `of_decide_eq_true …`, directly or through the auxiliary
lemma `decide +kernel` creates) and reports each one whose axioms go beyond
`propext`.  Opt-in like `MathProof.AxCheck` (not in `defaultTargets`/CI):

    tools/modal_run.sh --target MathProof.AxCheckDecide

Heavy modules are not imported here; they audit themselves
(`MaedaGalois5AxCheck`, in-file `#print axioms`).
-/

open Lean Elab Command

namespace AxCheckDecide

/-- Strip leading `fun` binders. -/
partial def peelLams : Expr → Expr
  | .lam _ _ b _ => peelLams b
  | e => e

/-- The proof term is a `decide` certificate: `of_decide_eq_true …`, possibly
behind one auxiliary lemma. -/
def isDecideProof (env : Environment) (v : Expr) : Bool :=
  match (peelLams v).getAppFn with
  | .const n _ =>
    n == ``of_decide_eq_true ||
      match env.find? n with
      | some (.thmInfo t) => (peelLams t.value).getAppFn.isConstOf ``of_decide_eq_true
      | _ => false
  | _ => false

/-- Audit the `decide` certificates among top-level theorems (`internal := false`)
or among the internal auxiliary lemmas (`internal := true`): a `decide +kernel`
inside a tactic proof (`ext i j; fin_cases i <;> … <;> decide +kernel`) becomes
an internal auxiliary lemma of the enclosing theorem, invisible to the
top-level pass. -/
def auditDecideCerts (internal : Bool) : CommandElabM Unit := do
  let env ← getEnv
  let mut found : Array (Name × Name × Array Name) := #[]
  for (n, ci) in env.constants.map₁.toList do
    let .thmInfo t := ci | continue
    if n.isInternal != internal then continue
    let some idx := env.getModuleIdxFor? n | continue
    let modName := env.header.moduleNames[idx.toNat]!
    unless (`MathProof).isPrefixOf modName do continue
    unless isDecideProof env t.value do continue
    let axs ← collectAxioms n
    found := found.push (modName, n, axs)
  let sorted := found.qsort fun a b =>
    a.1.toString < b.1.toString || (a.1 == b.1 && a.2.1.toString < b.2.1.toString)
  let bad := sorted.filter fun (_, _, axs) => axs.any (· != ``propext)
  for (m, n, axs) in bad do
    logInfo m!"VIOLATION {m} {n}: {axs.toList}"
  let kind := if internal then "nested decide certificates" else "decide certificates"
  logInfo m!"{kind}: {sorted.size} audited, {bad.size} depend on more than propext"

elab "#audit_decide_certs" : command => auditDecideCerts false

/-- The nested pass: entrywise certificates under `ext`/`fin_cases`. -/
elab "#audit_decide_certs_nested" : command => auditDecideCerts true

/-- A dependency path from `n` to the axiom `ax`: at each step, the first
referenced constant that still depends on `ax`.  Shows *which* definition
pulls an axiom into a certificate. -/
partial def axiomPath (ax n : Name) (fuel : Nat := 60) : CommandElabM (List Name) := do
  if n == ax || fuel == 0 then return [n]
  let env ← getEnv
  let some ci := env.find? n | return [n]
  let used := ci.type.getUsedConstants ++
    ((ci.value? (allowOpaque := true)).map (·.getUsedConstants)).getD #[]
  for c in used do
    if c == n then continue
    if (← collectAxioms c).contains ax then
      return n :: (← axiomPath ax c (fuel - 1))
  return [n]

/-- `#axiom_path ax n`: print the path from `n` to the axiom `ax`. -/
elab "#axiom_path " ax:ident n:ident : command => do
  let some c := (← getEnv).find? n.getId |>.map (·.name)
    | throwError "unknown constant {n.getId}"
  let path ← axiomPath ax.getId c
  logInfo m!"{" → ".intercalate (path.map toString)}"

end AxCheckDecide

#audit_decide_certs
#audit_decide_certs_nested
