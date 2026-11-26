import Geode
import Lean.Util.CollectAxioms

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let required : Array Name := #[
    `Geode.Lorentz.matching_complexity,
    `Geode.Lorentz.matchingComplexityStatement_verified,
    `Geode.Lorentz.main_precise_lower,
    `Geode.Lorentz.strict_localization,
    `Geode.Lorentz.projectedAlgorithm_guarantees,
    `Geode.Lorentz.precise_failure_witness,
    `Geode.Lorentz.partial_matching_complexity,
    `Geode.Lorentz.precise_failure_witness_partial,
    `Geode.Lorentz.partialUniformComplexity_eq,
    `Geode.Lorentz.partial_strict_localization,
    `Geode.Lorentz.joint_distance_convex_lines,
    `Geode.Lorentz.logMap_contraction,
    `Geode.Lorentz.subgradient_selection,
    `Geode.Lorentz.admissible_has_legal_oracle,
    `Geode.Lorentz.canonicalOracle_minimum_norm,
    `Geode.Lorentz.ArchiveValid.complete_canonical,
    `Geode.Lorentz.metric_carrier,
    `Geode.Lorentz.contact_realization,
    `Geode.Lorentz.section_ball_subset_halfspace_iff,
    `Geode.perfect_square,
    `Geode.right_branch_persistence,
    `Geode.Lorentz.intrinsic_normal_reserve,
    `Geode.Lorentz.exterior_routing_exists,
    `Geode.Lorentz.on_domain_routing_exists,
    `Geode.Lorentz.RoutingData.scalar_persistence,
    `Geode.Lorentz.candidateSet_latitude_nonempty,
    `Geode.Lorentz.RoutingData.future_ball,
    `Geode.Lorentz.archive_failure_completion,
    `Geode.Rescaled.uniformComplexity_eq,
    `Geode.Rescaled.matching_complexity,
    `Geode.Rescaled.strict_localization,
    `Geode.Rescaled.precise_failure_witness,
    `Geode.Lorentz.uniformComplexity_L_normalization,
    `Geode.curvatureFactor_right_zero,
    `Geode.curvatureFactor_ratio_atTop]
  for name in required do
    match env.find? name with
    | some (.thmInfo _) => logInfo m!"REQUIRED THEOREM PRESENT: {name}"
    | _ => throwError "Required main theorem missing: {name}"
  let mut names : Array Name := #[]
  for (name, info) in env.constants.toList do
    if name.getRoot == `Geode then
      match info with
      | .thmInfo _ => names := names.push name
      | _ => pure ()
  names := names.qsort (fun a b => a.toString < b.toString)
  if names.isEmpty then throwError "No Geode theorems found."
  -- Reuse the visited dependency closure across roots. Every reachable
  -- declaration is checked by Lean's standard collector, exactly once.
  let mut dependencyState : Lean.CollectAxioms.State := {}
  for name in names do
    let (_, nextState) := ((Lean.CollectAxioms.collect name).run env).run dependencyState
    dependencyState := nextState
    let unexpected := dependencyState.axioms.filter (fun a =>
      a != `propext && a != `Classical.choice && a != `Quot.sound)
    unless unexpected.isEmpty do
      throwError "{name}: unexpected axiom dependencies {unexpected}"
    logInfo m!"PASS {name}: standard-only transitive dependency closure"
  logInfo m!"UNION OF AXIOM DEPENDENCIES: {dependencyState.axioms}"
  logInfo m!"AUDIT PASSED: {names.size} Geode theorems; standard axioms only."
