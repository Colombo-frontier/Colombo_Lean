import LeanArticleAudit
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Audit the transitive axiom dependencies of every theorem whose namespace
root is LeanArticleAudit, including imported project helper theorems.
The preserved upstream RateForge/AxiomAudit.lean has a narrower, explicit
scope: the 25 mapped article declarations plus its listed auxiliaries. -/

set_option maxHeartbeats 0
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  for (name, info) in env.constants.toList do
    if name.getRoot == `LeanArticleAudit then
      match info with
      | .thmInfo _ => names := names.push name
      | _ => pure ()
  names := names.qsort (fun a b => a.toString < b.toString)
  if names.isEmpty then throwError "No project theorems found."
  for name in names do
    let axioms ← Lean.collectAxioms name
    let unexpected := axioms.filter (fun a =>
      a != `propext && a != `Classical.choice && a != `Quot.sound)
    unless unexpected.isEmpty do
      throwError "{name}: unexpected axiom dependencies {unexpected}"
    logInfo m!"PASS {name}: transitive dependency axioms {axioms}"
  logInfo m!"AUDIT PASSED: {names.size} project theorems; standard axioms only."
