import MatchingBounds1005
import Lean.Util.CollectAxioms

/-! Kernel-dependency audit. Passing this file only verifies implemented
declarations; the separate main-status lines prevent conflating partial proofs
with completion of the manuscript. -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  let mut theoremCount := 0
  for (name, info) in env.constants.toList do
    if name.getRoot == `MatchingBounds1005 then
      let internalName := (name.toString.splitOn ".").any (fun s => s.startsWith "_")
      match info with
      | .thmInfo _ => names := names.push name
      | .axiomInfo _ =>
        unless internalName && info.isUnsafe do names := names.push name
      | _ => unless internalName do names := names.push name
  unless !names.isEmpty do throwError "No project declarations were found."
  let (_, state) := ((names.forM Lean.CollectAxioms.collect).run env).run {}
  let unexpected := state.axioms.filter (fun a =>
    a != `propext && a != `Classical.choice && a != `Quot.sound)
  unless unexpected.isEmpty do
    throwError "Unexpected transitive axioms: {unexpected}"
  for name in names.qsort (fun a b => a.toString < b.toString) do
    if let some (.thmInfo _) := env.find? name then
      theoremCount := theoremCount + 1
      logInfo m!"PASS {name}"
  for (proofName, targetName) in #[
      (`MatchingBounds1005.Model.main_lower_bound, `MatchingBounds1005.Model.MainLowerBound),
      (`MatchingBounds1005.Model.main_upper_bound, `MatchingBounds1005.Model.MainUpperBound),
      (`MatchingBounds1005.Model.main_theorem, `MatchingBounds1005.Model.MainTheorem)] do
    match env.find? proofName with
    | some (.thmInfo info) =>
      unless info.type == mkConst targetName do
        throwError "Main proof has additional hypotheses or the wrong target: {proofName}"
      logInfo m!"MAIN PROVED: {proofName}"
    | _ => logInfo m!"MAIN UNPROVED: {proofName}"
  logInfo m!"TRANSITIVE AXIOMS: {state.axioms}"
  logInfo m!"AUDIT PASSED: {names.size} declarations; {theoremCount} theorems."
