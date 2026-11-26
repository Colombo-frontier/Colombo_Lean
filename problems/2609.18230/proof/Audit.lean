import ExactValue
import Lean.Util.CollectAxioms

/-! Reject any theorem in this project whose transitive axiom dependencies
include anything beyond Lean's standard classical foundations. -/

set_option maxHeartbeats 0
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  for (name, info) in env.constants.toList do
    if name.getRoot == `ExactValue then
      match info with
      | .thmInfo _ => names := names.push name
      | _ => pure ()
  names := names.qsort (fun a b => a.toString < b.toString)
  if names.isEmpty then throwError "No project theorems found."
  -- Reuse the visited dependency closure; every visited dependency was already checked.
  let mut closure : Lean.CollectAxioms.State := {}
  for name in names do
    let (_, next) := ((Lean.CollectAxioms.collect name).run env).run closure
    closure := next
    let unexpected := closure.axioms.filter (fun a =>
      a != `propext && a != `Classical.choice && a != `Quot.sound)
    unless unexpected.isEmpty do
      throwError "{name}: unexpected axiom dependencies {unexpected}"
    logInfo m!"PASS {name}: cumulative dependency axioms {closure.axioms}"
  logInfo m!"AUDIT PASSED: {names.size} project theorems; standard axioms only."
