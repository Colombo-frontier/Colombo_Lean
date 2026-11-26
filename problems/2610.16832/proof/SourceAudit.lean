import SampleReuse
import Lean.Util.CollectAxioms

set_option maxHeartbeats 0
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  let mut theoremCount := 0
  for (name, info) in env.constants.toList do
    let moduleName := (env.getModuleIdxFor? name |>.map
      (fun i => env.header.moduleNames[i.toNat]!)).getD Name.anonymous
    if moduleName.getRoot == `SampleReuse then
      unless info.isUnsafe do
        names := names.push name
        match info with
        | .thmInfo _ => theoremCount := theoremCount + 1
        | .axiomInfo _ => throwError "Custom unproved axiom: {name}"
        | _ => pure ()
  if names.isEmpty || theoremCount == 0 then throwError "No project theorems found"
  names := names.qsort (fun a b => a.toString < b.toString)
  let mut closure : Lean.CollectAxioms.State := {}
  for name in names do
    let (_, next) := ((Lean.CollectAxioms.collect name).run env).run closure
    closure := next
    let unexpected := closure.axioms.filter (fun a =>
      a != `propext && a != `Classical.choice && a != `Quot.sound)
    unless unexpected.isEmpty do
      throwError "{name}: unexpected transitive axioms {unexpected}"
    logInfo m!"PASS {name}"
  logInfo m!"AXIOM UNION: {closure.axioms}"
  logInfo m!"AUDIT PASSED: {names.size} declarations; {theoremCount} theorems; standard axioms only"
