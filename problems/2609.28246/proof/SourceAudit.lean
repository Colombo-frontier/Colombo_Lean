import LeanArticleAudit
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Inspect compiled kernel declarations. This command produces no mathematical
proofs and changes no axiom policy; it is adapted from the reference proof/Audit.lean.
It lives outside the proof project, keeping introspection separate from proof sources. -/
set_option maxHeartbeats 0
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut own : Array Name := #[]
  let mut reused : Array Name := #[]
  for (name, info) in env.constants.toList do
    match info with
    | .thmInfo _ =>
      if name.getRoot == `MinimaxAudit then own := own.push name
      if name.getRoot == `VIReference then reused := reused.push name
    | _ => pure ()
  unless !own.isEmpty do throwError "No MinimaxAudit theorems found."
  let names := (own ++ reused).qsort (fun a b => a.toString < b.toString)
  for name in names do
    let axioms ← Lean.collectAxioms name
    let unexpected := axioms.filter (fun a =>
      a != `propext && a != `Classical.choice && a != `Quot.sound)
    unless unexpected.isEmpty do
      throwError "{name}: unexpected transitive axiom dependencies {unexpected}"
    logInfo m!"PASS {name}: {axioms}"
  logInfo m!"ALL_THEOREMS_AUDIT own={own.size} reused={reused.size} total={names.size} PASS"
