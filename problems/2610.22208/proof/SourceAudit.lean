import GradientHessian
import Lean.Util.CollectAxioms

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  for (name, info) in env.constants.toList do
    if name.getRoot == `GradientHessian then
      match info with
      | .thmInfo _ => names := names.push name
      | _ => pure ()
  names := names.qsort (fun a b => a.toString < b.toString)
  if names.isEmpty then throwError "No GradientHessian theorems found."
  for name in names do
    unless (env.checked.get.find? name).isSome do
      throwError "{name}: theorem is absent from the kernel-checked environment"
  -- Sharing the visited set preserves the full union of transitive dependencies
  -- while avoiding repeated traversal of Mathlib and the LowRank proof chain.
  let collectAll : Lean.CollectAxioms.M Unit := names.forM Lean.CollectAxioms.collect
  let (_, dependencies) := (collectAll.run env).run {}
  let unexpected := dependencies.axioms.filter (fun a =>
    a != `propext && a != `Classical.choice && a != `Quot.sound)
  unless unexpected.isEmpty do
    throwError "Unexpected transitive dependencies: {unexpected}"
  for name in names do
    logInfo m!"PASS {name}: common transitive closure audited"
  logInfo m!"FOUNDATIONS: {dependencies.axioms}"
  logInfo m!"AUDIT PASSED: {names.size} theorem constants; standard foundations only."
