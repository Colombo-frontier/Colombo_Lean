import Main
import Lean.Util.CollectAxioms

example : Task003.OracleModel.FullJointProfile (1 / 8) :=
  Task003.UnconditionalMain.paper_main_unconditional
example : Task003.LiteratureMain.ZhangLiteratureInput :=
  Task003Integration.zhangLiteratureInput_proved
example : Task003.LiteratureMain.ProtasovLiteratureInput :=
  Task003Integration.protasovLiteratureInput_proved

namespace AuditInfrastructure
open Lean
structure BodyState where
  seen : NameSet := {}
  axioms : NameSet := {}
  missing : NameSet := {}

/-- Independent body traversal, without using Lean's exported axiom cache. -/
partial def visit (env : Environment) (name : Name) : StateM BodyState Unit := do
  if (← get).seen.contains name then return
  modify fun s => { s with seen := s.seen.insert name }
  let some info := env.checked.get.find? name |
    modify fun s => { s with missing := s.missing.insert name }
  let visitExpr (e : Expr) := e.getUsedConstants.forM (visit env)
  match info with
  | .axiomInfo v =>
      modify fun s => { s with axioms := s.axioms.insert name }
      visitExpr v.type
  | .defnInfo v => visitExpr v.type *> visitExpr v.value
  | .thmInfo v => visitExpr v.type *> visitExpr v.value
  | .opaqueInfo v => visitExpr v.type *> visitExpr v.value
  | .quotInfo _ => pure ()
  | .ctorInfo v => visitExpr v.type
  | .recInfo v => visitExpr v.type
  | .inductInfo v => visitExpr v.type *> v.ctors.forM (visit env)
end AuditInfrastructure

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  let mut theoremCount := 0
  let mut excludedUnsafe := 0
  let mut rows : Array Json := #[]
  for (name, info) in env.constants.toList do
    let moduleName := (env.getModuleIdxFor? name |>.map
      (fun i => env.header.moduleNames[i.toNat]!)).getD Name.anonymous
    if moduleName == `Task003Base || moduleName.getRoot == `Nonsmooth ||
        moduleName.getRoot == `Task003Integration then
      if info.isUnsafe then
        excludedUnsafe := excludedUnsafe + 1
      else
        match info with
        | .axiomInfo _ => throwError "Custom unproved project axiom: {name}"
        | .thmInfo _ => theoremCount := theoremCount + 1
        | _ => pure ()
        if info.type.hasExprMVar || info.type.hasFVar then
          throwError "Open declaration type: {name}"
        names := names.push name
        rows := rows.push (Json.mkObj [
          ("name", toJson name.toString),
          ("module", toJson moduleName.toString),
          ("is_theorem", toJson (match info with | .thmInfo _ => true | _ => false))])
  if names.isEmpty then throwError "No mathematical project declarations were loaded"
  names := names.qsort (fun a b => a.toString < b.toString)
  let mut closure : NameSet := {}
  let mut axiomRows : Array Json := #[]
  for name in names do
    let axioms ← Lean.collectAxioms name
    axiomRows := axiomRows.push (Json.mkObj [
      ("name", toJson name.toString), ("axioms", toJson (axioms.map Name.toString))])
    for ax in axioms do closure := closure.insert ax
    let unexpected := axioms.filter (fun a =>
      a != `propext && a != `Classical.choice && a != `Quot.sound)
    unless unexpected.isEmpty do
      throwError "Unexpected transitive axiom at {name}: {unexpected}"
  let (_, bodyState) := (names.forM (AuditInfrastructure.visit env)).run {}
  unless bodyState.missing.isEmpty do
    throwError "Independent body traversal encountered missing constants: {bodyState.missing.toArray}"
  let bodyAxioms := bodyState.axioms.toArray
  unless bodyAxioms.all (fun a => a == `propext || a == `Classical.choice || a == `Quot.sound) do
    throwError "Independent body traversal found unexpected axioms: {bodyAxioms}"
  unless closure.toArray.all (fun a => bodyState.axioms.contains a) &&
      bodyAxioms.all (fun a => closure.contains a) do
    throwError "Upstream collector and independent body traversal disagree"
  let mut endpoints : Array Json := #[]
  let endpointNames : Array Name := #[`Nonsmooth.general_body_protasov,
    `Nonsmooth.gaussianAdaptiveHardness_proved,
    `Nonsmooth.gaussianPosteriorLogEnergyEstimate_proved,
    `Task003Integration.halfRows_map_law,
    `Task003Integration.protasovLiteratureInput_proved,
    `Task003Integration.zhangLiteratureInput_proved,
    `Task003Integration.protasovOpenPrinciple_proved,
    `Task003Integration.zhang_fixed_prior_hardness,
    `Task003.UnconditionalMain.normalized_main_unconditional,
    `Task003.UnconditionalMain.scaled_main_unconditional,
    `Task003.UnconditionalMain.paper_main_unconditional]
  for name in endpointNames do
    let some info := env.find? name | throwError "Missing endpoint: {name}"
    match info with
    | .thmInfo _ => pure ()
    | _ => throwError "Endpoint is not a theorem: {name}"
    let axioms ← Lean.collectAxioms name
    unless axioms.all (fun a => a == `propext || a == `Classical.choice || a == `Quot.sound) do
      throwError "Fresh endpoint axiom check failed: {name}: {axioms}"
    let typeText ← liftTermElabM do
      return (← Meta.ppExpr info.type).pretty
    endpoints := endpoints.push (Json.mkObj [
      ("name", toJson name.toString),
      ("type", toJson typeText),
      ("axioms", toJson (axioms.map Name.toString))])
  let report := Json.mkObj [
    ("status", toJson "passed"),
    ("declaration_count", toJson names.size),
    ("theorem_count", toJson theoremCount),
    ("unsafe_compiler_artifacts_excluded", toJson excludedUnsafe),
    ("transitive_axioms", toJson (closure.toArray.map Name.toString)),
    ("independent_body_axioms", toJson (bodyAxioms.map Name.toString)),
    ("independent_body_visited", toJson bodyState.seen.size),
    ("declarations", Json.arr rows),
    ("per_declaration_axioms", Json.arr axiomRows),
    ("independent_endpoints", Json.arr endpoints)]
  liftIO (IO.println ("KERNEL_AUDIT_JSON:" ++ report.compress))
  logInfo m!"KERNEL AUDIT PASSED: {names.size} safe project declarations, {theoremCount} theorems"
