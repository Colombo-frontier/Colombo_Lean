import RandomizedFO2003
import Lean.Util.CollectAxioms

/-! Inspect every project theorem and each public project declaration, including
the model definitions. Compiler-generated internal runtime definitions are not
logical claims and are excluded. Transitive theorem dependencies are all checked. -/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  let mut theoremCount := 0
  for (name, info) in env.constants.toList do
    if name.getRoot == `RandomizedFO2003 then
      let internalName := (name.toString.splitOn ".").any (fun s => s.startsWith "_")
      match info with
      | .thmInfo _ => names := names.push name
      | .axiomInfo _ =>
        -- Lean's code generator emits unsafe internal lambda-lifting
        -- stubs as axiomInfo. They are runtime-only, not kernel axioms.
        -- Every safe axiom (even a private one) remains an audit root;
        -- any dependency of a theorem/public definition is still traversed.
        if internalName && info.isUnsafe then
          logInfo m!"RUNTIME ROOT EXCLUDED (unsafe compiler stub): {name}"
        else names := names.push name
      | _ => if !internalName then names := names.push name
  names := names.qsort (fun a b => a.toString < b.toString)
  if names.isEmpty then throwError "No project declarations found."
  -- Traverse the union of dependency graphs once. This checks the same
  -- transitive closure as separate traversals, while sharing visited nodes.
  let (_, auditState) := ((names.forM Lean.CollectAxioms.collect).run env).run {}
  let unexpected := auditState.axioms.filter (fun a =>
    a != `propext && a != `Classical.choice && a != `Quot.sound)
  unless unexpected.isEmpty do
    throwError "Unexpected transitive axiom dependencies: {unexpected}"
  for name in names do
    if let some (.thmInfo _) := env.find? name then
      theoremCount := theoremCount + 1
      logInfo m!"PASS {name}"
  logInfo m!"TRANSITIVE AXIOMS: {auditState.axioms}"
  match env.find? `RandomizedFO2003.Model.MainLowerBound with
  | some (.defnInfo _) => pure ()
  | _ => throwError "Unexpected representation of MainLowerBound."
  match env.find? `RandomizedFO2003.Model.main_lower_bound with
  | some (.thmInfo info) =>
    unless info.type == mkConst `RandomizedFO2003.Model.MainLowerBound do
      throwError "Main theorem does not have the exact MainLowerBound target type."
    logInfo "MAIN STATUS: PROVED RandomizedFO2003.Model.main_lower_bound : RandomizedFO2003.Model.MainLowerBound"
  | _ => throwError "The main lower-bound proof is missing."
  for (proofName, targetName, label) in #[
      (`RandomizedFO2003.Model.main_upper_bound, `RandomizedFO2003.Model.MainUpperBound, "UPPER"),
      (`RandomizedFO2003.Model.main_theta_bound, `RandomizedFO2003.Model.MainThetaBound, "THETA"),
      (`RandomizedFO2003.Model.main_minimax_theta_bound, `RandomizedFO2003.Model.MinimaxThetaBound, "MINIMAX")] do
    match env.find? targetName with
    | some (.defnInfo _) => pure ()
    | _ => throwError "Missing precise target definition: {targetName}"
    match env.find? proofName with
    | some (.thmInfo info) =>
      unless info.type == mkConst targetName do
        throwError "Proof {proofName} does not have the exact target type {targetName}."
      logInfo m!"{label} STATUS: PROVED {proofName} : {targetName}"
    | _ => throwError "Missing theorem proof: {proofName}"
  for proofName in #[
      `RandomizedFO2003.FiniteSpectralDesign.distributional_lower_bound,
      `RandomizedFO2003.FiniteSpectralDesign.chosen_cascade_inFunctionClass,
      `RandomizedFO2003.Model.inFunctionClass_iff_infimum,
      `RandomizedFO2003.Accelerated.accelerated_algorithm_correct,
      `RandomizedFO2003.Accelerated.accelerated_success_probability,
      `RandomizedFO2003.Accelerated.accelerated_budget_le_rate] do
    match env.find? proofName with
    | some (.thmInfo _) => logInfo m!"MAJOR SUPPORT: PROVED {proofName}"
    | _ => throwError "Missing supporting main result: {proofName}"
  logInfo "SCOPE: Main randomized lower bound, implemented accelerated upper bound, and numerical minimax Theta bound proved. Auxiliary literal refinements and repaired source errors are documented separately."
  logInfo m!"AUDIT PASSED: {names.size} declarations, {theoremCount} theorems; standard axioms only."
