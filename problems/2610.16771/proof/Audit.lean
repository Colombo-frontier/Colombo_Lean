import PaperAudit
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Check the ownership and axiom dependencies of the imported project.
Declaration ownership is determined by Lean's module table, so helper theorems
outside the manuscript's namespaces are included. Imported Mathlib theorems are
checked transitively when they are dependencies of a project theorem. -/

set_option maxHeartbeats 0

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner (name : Name) : Option Name := do
    let idx ← env.getModuleIdxFor? name
    env.header.moduleNames[idx.toNat]?
  let isProjectModule (name : Name) : Bool :=
    name == `PaperAudit || (`PaperAudit).isPrefixOf name
  let mut names : Array Name := #[]
  let mut unexpectedAxioms : Array (Name × Array Name) := #[]
  let mut moduleCounts : Std.HashMap Name Nat := {}
  for (name, info) in env.constants.toList do
    if let some moduleName := owner name then
      if isProjectModule moduleName then
        match info with
        | .axiomInfo _ => throwError "Project declares a custom axiom: {name}"
        | .thmInfo _ =>
          names := names.push name
          moduleCounts := moduleCounts.insert moduleName
            (moduleCounts.getD moduleName 0 + 1)
        | _ => pure ()
  unless !names.isEmpty do
    throwError "No project theorems found."
  for name in names do
    let axioms ← Lean.collectAxioms name
    let unexpected := axioms.filter fun a =>
      a != `propext && a != `Classical.choice && a != `Quot.sound
    unless unexpected.isEmpty do
      unexpectedAxioms := unexpectedAxioms.push (name, unexpected)
  unless unexpectedAxioms.isEmpty do
    for (name, axioms) in unexpectedAxioms[:40] do
      logError m!"{name}: unexpected transitive axioms {axioms}"
    throwError "Axiom audit failed for {unexpectedAxioms.size} project theorems."

  let text ← IO.FS.readFile "proof/declarations.json"
  let manifest ← match Json.parse text with
    | .ok value => pure value
    | .error error => throwError "Invalid declaration manifest: {error}"
  let targets ← match manifest.getObjValAs? (Array Json) "targets" with
    | .ok value => pure value
    | .error error => throwError "Missing manifest targets: {error}"
  unless targets.size == 36 do
    throwError "Expected 36 declared audit targets, found {targets.size}."
  for target in targets do
    let principal ← match target.getObjValAs? String "principal" with
      | .ok value => pure value.toName
      | .error error => throwError "Invalid target principal: {error}"
    let moduleName ← match target.getObjValAs? String "module" with
      | .ok value => pure value.toName
      | .error error => throwError "Invalid target module: {error}"
    unless isProjectModule moduleName && owner principal == some moduleName do
      throwError "Target {principal} does not belong to declared module {moduleName}."
    match env.find? principal with
    | some (.thmInfo _) => pure ()
    | _ => throwError "Target {principal} is not an imported theorem."
  for (moduleName, count) in moduleCounts.toArray.qsort (fun a b => a.1.toString < b.1.toString) do
    logInfo m!"MODULE {moduleName}: {count} project theorems audited"
  logInfo m!"AUDIT PASSED: {names.size} project theorems, {targets.size} mapped targets; standard axioms only."
