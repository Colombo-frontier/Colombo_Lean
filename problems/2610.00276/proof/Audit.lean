import NoisyZO
import Lean.Util.CollectAxioms

/-! Check every safe declaration defined in a project module, including private
declarations and generated helpers. Lean 4.34 uses the public collectAxioms API
with imported precomputed dependency data; the union is accumulated across all
checked declarations. Compiler-only unsafe artifacts are counted
separately and cannot serve as kernel proofs. -/
set_option maxHeartbeats 0
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  let mut theoremCount := 0
  let mut compilerCount := 0
  for (name, info) in env.constants.toList do
    let moduleName := (env.getModuleIdxFor? name |>.map (fun i => env.header.moduleNames[i.toNat]!)).getD Name.anonymous
    if moduleName.getRoot == `NoisyZO then
      if info.isUnsafe then
        compilerCount := compilerCount + 1
      else
        names := names.push name
        match info with
        | .thmInfo _ => theoremCount := theoremCount + 1
        | .axiomInfo _ => throwError "Custom unproved axiom: {name}"
        | _ => pure ()
  if names.isEmpty || theoremCount == 0 then throwError "No project theorems found."
  names := names.qsort (fun a b => a.toString < b.toString)
  let mut axiomUnion : Array Name := #[]
  for name in names do
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      unless axiomUnion.contains axiomName do
        axiomUnion := axiomUnion.push axiomName
    let unexpected := axioms.filter (fun a =>
      a != `propext && a != `Classical.choice && a != `Quot.sound)
    unless unexpected.isEmpty do
      throwError "{name}: unexpected transitive axioms {unexpected}"
    logInfo m!"PASS {name}: transitive dependencies checked"
  logInfo m!"AXIOM UNION: {axiomUnion}"
  logInfo m!"AUDIT PASSED: {names.size} declarations; {theoremCount} theorems; standard axioms only."
  logInfo m!"COMPILER ARTIFACTS: {compilerCount} unsafe declarations, unavailable to kernel proofs."
