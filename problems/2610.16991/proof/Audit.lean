import NCConcave16991
import Lean.Util.CollectAxioms

/-! Audit every safe declaration whose defining module belongs to this project,
including private declarations and generated helpers. Namespace-only selection
is insufficient for private names. Compiler-only unsafe artifacts are counted
separately and cannot serve as kernel proofs. Lean 4.34's public collectAxioms
uses precomputed imported axiom data; its internal collector is private. -/
set_option maxHeartbeats 0
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  let mut theoremCount : Nat := 0
  let mut compilerCount : Nat := 0
  for (name, info) in env.constants.toList do
    let moduleName := (env.getModuleIdxFor? name |>.map (fun i => env.header.moduleNames[i.toNat]!)).getD Name.anonymous
    if moduleName.getRoot == `NCConcave16991 then
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
  for name in names do
    let axioms ← collectAxioms name
    for ax in axioms do
      unless ax == `propext || ax == `Classical.choice || ax == `Quot.sound do
        throwError "{name}: unexpected transitive axiom {ax}"
    logInfo m!"PASS {name}: transitive closure checked"
  logInfo m!"AUDIT PASSED: {names.size} declarations; {theoremCount} theorems; standard axioms only."
  logInfo m!"COMPILER ARTIFACTS: {compilerCount} unsafe declarations, unavailable to kernel proofs."
