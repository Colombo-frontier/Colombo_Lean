import Main
import Lean

/-! Reproduce the preserved Task006-prefix baseline. This is deliberately a
prefix audit, distinct from the complete module-origin audit in Audit.lean. -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let text ← liftIO (IO.FS.readFile "../proof/declarations.json")
  let json ← match Json.parse text with
    | .ok value => pure value
    | .error message => throwError "Invalid coverage inventory JSON: {message}"
  let array ← match json.getObjVal? "declarations" with
    | .ok value => pure value
    | .error message => throwError "Missing coverage declarations: {message}"
  let coverageNames ← match (fromJson? array : Except String (Array String)) with
    | .ok value => pure value
    | .error message => throwError "Invalid coverage inventory: {message}"
  unless coverageNames.size == 217 do throwError "Expected 217 coverage declarations"
  let mut coverageSet : NameSet := {}
  for entry in coverageNames do
    let name := entry.toName
    if coverageSet.contains name then throwError "Duplicate coverage declaration: {name}"
    coverageSet := coverageSet.insert name
    let some info := env.checked.get.find? name |
      throwError "Coverage declaration is not kernel checked: {name}"
    if info.type.hasExprMVar || info.type.hasFVar then
      throwError "Open coverage declaration type: {name}"
  let names ← env.constants.foldM (init := (#[] : Array Name)) fun acc name _ =>
    pure (if name.toString.startsWith "Task006" then acc.push name else acc)
  unless names.size == 2252 do
    throwError "Preserved Task006-prefix baseline changed: expected 2252, got {names.size}"
  let mut closure : NameSet := {}
  let mut theoremCount := 0
  let mut axiomRows : Array Json := #[]
  for name in names do
    let some info := env.checked.get.find? name |
      throwError "Task006 declaration is not kernel checked: {name}"
    if info.type.hasExprMVar || info.type.hasFVar then
      throwError "Open Task006 declaration type: {name}"
    match info with
    | .thmInfo _ => theoremCount := theoremCount + 1
    | _ => pure ()
    let axioms ← collectAxioms name
    unless axioms.all (fun a => a == `propext || a == `Classical.choice || a == `Quot.sound) do
      throwError "Unexpected Task006 transitive axiom: {name} -> {axioms}"
    for axiomName in axioms do closure := closure.insert axiomName
    axiomRows := axiomRows.push (Json.mkObj [
      ("name",toJson name.toString), ("axioms",toJson (axioms.map Name.toString))])
  let targets : Array Name := #[
    ``Task006.Full.main_theorem,
    ``Task006.Full.common_polynomial_envelope,
    ``Task006.Full.diagonal_dimension_four,
    ``Task006.Full.SampleInstance.source_upper_actual_error_lt,
    ``Task006.SphereSmoothing.ballSmoothGradient_eq_haar,
    ``Task006.Full.SampleInstance.ballSmooth_samplewise_hasGradient_haar,
    ``Task006.SphereConcentration.median_bound_spherical_scale,
    ``Task006.AdaptiveSphereOriginalEnergy.original_sphere_fiber_energy,
    ``Task006.AdaptiveSphereKernel.original_condDistrib_eq_sphere_fiber,
    ``Task006.AdaptiveSphereSourceEvent.sourceHandleEvent_half_mass,
    ``Task006.AdaptiveSphereSourceEvent.source_event_original_center_energy_le_ratio,
    ``Task006.AdaptiveSphereSourceEvent.source_large_dimension_bayes_risk_gt_146,
    ``Task006.AdaptiveSphereSourceEvent.source_small_dimension_bayes_risk_ge,
    ``Task006.Full.OracleAlgorithm.expected_informativeHandles_prior_eq]
  let mut targetRows : Array Json := #[]
  for name in targets do
    let some (.thmInfo value) := env.checked.get.find? name |
      throwError "Named result lacks a kernel-checked theorem proof: {name}"
    if value.type.hasExprMVar || value.type.hasFVar || value.value.hasExprMVar || value.value.hasFVar then
      throwError "Named theorem has an open type or proof: {name}"
    let axioms ← collectAxioms name
    unless axioms.all (fun a => a == `propext || a == `Classical.choice || a == `Quot.sound) do
      throwError "Named theorem has unexpected transitive axioms: {name} -> {axioms}"
    targetRows := targetRows.push (Json.mkObj [
      ("name",toJson name.toString), ("has_kernel_checked_proof",toJson true),
      ("axioms",toJson (axioms.map Name.toString))])
  let report := Json.mkObj [
    ("status",toJson "passed"), ("audit_kind",toJson "preserved_Task006_prefix_baseline"),
    ("prefix",toJson "Task006"), ("expected_declaration_count",toJson 2252),
    ("declaration_count",toJson names.size), ("theorem_count",toJson theoremCount),
    ("coverage_declaration_count",toJson coverageSet.size),
    ("kernel_checked_named_target_count",toJson targets.size),
    ("transitive_axioms",toJson (closure.toArray.map Name.toString)),
    ("targets",Json.arr targetRows), ("per_declaration_axioms",Json.arr axiomRows)]
  liftIO (IO.println ("SOURCE_AUDIT_JSON:" ++ report.compress))
  logInfo m!"SOURCE AUDIT PASSED: {names.size} Task006-prefix declarations, {targets.size} kernel theorem targets"
