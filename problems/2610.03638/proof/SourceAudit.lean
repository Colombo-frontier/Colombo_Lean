import Smoothness2601
import Lean.Util.CollectAxioms

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  for (name, info) in env.constants.toList do
    if name.getRoot == `Smoothness2601 || name.getRoot == `Bilevel then
      match info with
      | .thmInfo _ => names := names.push name
      | _ => pure ()
  names := names.qsort (fun a b => a.toString < b.toString)
  if names.isEmpty then throwError "No project theorems found."
  -- One shared traversal checks the union of every theorem's dependency graph.
  -- This is the same collector as #print axioms, preserving its visited set
  -- between roots instead of traversing shared mathlib proofs repeatedly.
  let (_, state) := ((names.forM Lean.CollectAxioms.collect).run env).run {}
  let unexpected := state.axioms.filter (fun a =>
    a != `propext && a != `Classical.choice && a != `Quot.sound)
  unless unexpected.isEmpty do
    throwError "Unexpected transitive axiom dependencies: {unexpected}"
  for name in names do
    logInfo m!"PASS {name}: covered by the checked dependency union"
  logInfo m!"AUDIT PASSED: {names.size} theorems; dependency union {state.axioms}."
