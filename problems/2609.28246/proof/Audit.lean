import LeanArticleAudit
import LeanArticleAudit.Claims
import Lean.Util.CollectAxioms

/-! Audit every safe declaration originating in a project source module, including
private declarations and generated helpers. Compiler-only unsafe artifacts
cannot serve as kernel proofs and are reported separately. Lean 4.32.1's public collector uses precomputed axiom data for imported modules. -/

set_option maxHeartbeats 0
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  let mut theoremCount := 0
  let mut compilerCount := 0
  for (name, info) in env.constants.toList do
    let moduleName := (env.getModuleIdxFor? name |>.map
      (fun i => env.header.moduleNames[i.toNat]!)).getD Name.anonymous
    if #[`LeanArticleAudit, `MinimaxAudit, `VIReference].contains moduleName.getRoot then
      if info.isUnsafe then
        compilerCount := compilerCount + 1
      else
        names := names.push name
        match info with
        | .thmInfo _ =>
          theoremCount := theoremCount + 1
          unless (env.checked.get.find? name).isSome do
            throwError "Theorem absent from the kernel-checked environment: {name}"
        | .axiomInfo _ => throwError "Custom unproved project axiom: {name}"
        | _ => pure ()
  if names.isEmpty || theoremCount == 0 then throwError "No project theorems found."
  names := names.qsort (fun a b => a.toString < b.toString)
  let mut axiomUnion : Array Name := #[]
  for name in names do
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      unless axiomUnion.contains axiomName do axiomUnion := axiomUnion.push axiomName
    let unexpected := axioms.filter (fun a =>
      a != `propext && a != `Classical.choice && a != `Quot.sound)
    unless unexpected.isEmpty do
      throwError "{name}: unexpected transitive axiom dependencies {unexpected}"
    match env.find? name with
    | some (.thmInfo _) => logInfo m!"THEOREM AUDITED: {name}"
    | _ => pure ()
  logInfo m!"AXIOM UNION: {axiomUnion}"
  logInfo m!"AUDIT PASSED: {names.size} declarations; {theoremCount} theorems; standard axioms only."
  logInfo m!"COMPILER ARTIFACTS: {compilerCount} unsafe declarations, unavailable to kernel proofs."
