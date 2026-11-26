import HeavyTail
import Lean.Util.CollectAxioms

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let required : Array Name := #[
    `HeavyTail.mixed_scalar_256,
    `HeavyTail.envelope_variational,
    `HeavyTail.manuscript_loss_hamming,
    `HeavyTail.dyadic_confidence_uniform,
    `HeavyTail.accepted_directional_bias,
    `HeavyTail.norm_rejection_probability,
    `HeavyTail.norm_rejection_probability_sixteenth,
    `HeavyTail.accepted_vector_bias,
    `HeavyTail.accepted_second_moment_bound,
    `HeavyTail.accepted_weak_centering,
    `HeavyTail.conditional_truncated_second_moment,
    `HeavyTail.conditional_vector_weak_moment,
    `HeavyTail.proximal_transfer,
    `HeavyTail.rounded_raw_stage_budget_bound,
    `HeavyTail.physical_raw_stage_budget_bound,
    `HeavyTail.erasure_centered_moment,
    `HeavyTail.erasure_testing_probability,
    `HeavyTail.rejection_lemma,
    `HeavyTail.rejectionConstant_pos,
    `HeavyTail.strongConvex_minimum_growth,
    `HeavyTail.envelope_right_inverse,
    `HeavyTail.envelope_inverse_order,
    `HeavyTail.conditional_log_sum_tail_of_bounded,
    `HeavyTail.entropy_variational_withDensity,
    `HeavyTail.mirror_update_inequality,
    `HeavyTail.mirror_descent_regret,
    `HeavyTail.adaptive_erasure_testing_lower,
    `HeavyTail.hardLoss_subgradient,
    `HeavyTail.hardLoss_lipschitz,
    `HeavyTail.hardLoss_convex,
    `HeavyTail.hardComposite_loss_hamming,
    `HeavyTail.GaussianEstimates.gaussian_inner_second_fourth,
    `HeavyTail.GaussianEstimates.gaussian_noise_weighted_bound,
    `HeavyTail.GaussianEstimates.gaussian_shifted_tail_bound,
    `HeavyTail.GaussianEstimates.integrated_mixed_scalar,
    `HeavyTail.no_uniform_negative_eta_constant,
    `HeavyTail.GaussianEstimates.gaussian_ball_mixture_exp_bound,
    `HeavyTail.GaussianEstimates.gaussian_conditional_mixture_exp_bound,
    `HeavyTail.mixtureEntropy_hasFDerivWithinAt,
    `HeavyTail.mixtureEntropy_bregman_eq_KL,
    `HeavyTail.meanRegularizedEntropy_bregman_eq_KL,
    `HeavyTail.exists_mixtureEntropy_mirror_minimizer,
    `HeavyTail.confidence_objective_probability_lower,
    `HeavyTail.confidenceOracle_two_moment_admissible,
    `HeavyTail.confidenceAmplitude_moment,
    `HeavyTail.confidenceAmplitude_envelope,
    `HeavyTail.confidence_erasure_probability,
    `HeavyTail.minimaxErrorQuantile_lower,
    `HeavyTail.confidenceFamilyQuantile_lower,
    `HeavyTail.tunedConfidenceOracle_two_moment_admissible,
    `HeavyTail.confidence_zero_query_quantile_lower,
    `HeavyTail.proximalOracle_growth,
    `HeavyTail.proximalOracle_subgradient,
    `HeavyTail.proximalOracle_displacement_mono,
    `HeavyTail.proximal_halving_search,
    `HeavyTail.zero_query_envelope_cap,
    `HeavyTail.finite_proximal_warm_start,
    `HeavyTail.phase_sum_after_proximal_warm_start,
    `HeavyTail.rejection_budget_tail,
    `HeavyTail.accepted_budget_failure_tail,
    `HeavyTail.capped_accepted_prefix_eq,
    `HeavyTail.capped_ideal_output_disagreement_bound,
    `HeavyTail.gaussianTraceOracle_unbiased,
    `HeavyTail.gaussianTraceOracle_moment_admissible,
    `HeavyTail.gaussian_neighbor_gradient_square,
    `HeavyTail.gaussian_neighbor_normalized_signal,
    `HeavyTail.GaussianLower.gaussian_two_moment_admissible,
    `HeavyTail.GaussianLower.scalar_gaussian_change_of_measure,
    `HeavyTail.GaussianLower.coordinateGaussian_change_of_measure,
    `HeavyTail.GaussianLower.coordinateRatio_second,
    `HeavyTail.GaussianLower.euclideanGaussian_translation,
    `HeavyTail.GaussianLower.likelihoodStep_mean,
    `HeavyTail.GaussianLower.likelihoodStep_second_le,
    `HeavyTail.GaussianEntropy.gaussian_mixture_entropy_derivative,
    `HeavyTail.GaussianEntropy.gaussian_comparator_KL,
    `HeavyTail.GaussianEntropy.gaussianExponentialDensity_measure,
    `HeavyTail.GaussianEntropy.gaussian_mixture_generator_bregman,
    `HeavyTail.GaussianEntropy.gaussian_mixture_quadratic_optimizer_exists,
    `HeavyTail.GaussianEntropy.gaussian_mixture_pathwise_regret,
    `HeavyTail.finite_ball_comparator_net,
    `HeavyTail.finite_net_average_regret_comparison,
    `HeavyTail.iid_eventually_accepts,
    `HeavyTail.rejectionSample_map,
    `HeavyTail.rejectionSample_measurable,
    `HeavyTail.rejectionSamplerKernel_eq_cond,
    `HeavyTail.sampled_rejection_lemma,
    `HeavyTail.PrivateInstance.correctedMean_bound_transfer,
    `HeavyTail.PrivateInstance.acceptedRawLaw_bounds,
    `HeavyTail.PrivateInstance.acceptedMean_measurable,
    `HeavyTail.PrivateInstance.acceptedNoise_square_integrable,
    `HeavyTail.PrivateInstance.model_warm_start,
    `HeavyTail.AdaptiveKernel.historyProduct_integral_le,
    `HeavyTail.AdaptiveKernel.history_log_sum_tail,
    `HeavyTail.CappedRaw.Rule.failure_probability,
    `HeavyTail.rawAcceptanceFactor_bound,
    `HeavyTail.rawBudgetTail_le_confidence,
    `HeavyTail.PrivateInstance.cappedStage_failure_probability,
    `HeavyTail.PublicProblem.stage_output_eq_average,
    `HeavyTail.PublicProblem.stage_output_eq_fallback,
    `HeavyTail.PrivateInstance.stage_online_to_batch,
    `HeavyTail.GaussianLower.gaussian_fixedCallMinimax_lower_of_dimension,
    `HeavyTail.GaussianEntropy.gaussian_online_stability_bound,
    `HeavyTail.GaussianEntropy.gaussian_online_masked_master,
    `HeavyTail.GaussianEntropy.onlineMixtureW_moment,
    `HeavyTail.GaussianEntropy.comparator_exp_error_moment,
    `HeavyTail.AdaptiveKernel.Policy.outputLaw_eq_outputKernel,
    `HeavyTail.AdaptiveKernel.Policy.outputKernel_apply,
    `HeavyTail.kernel_failure_propagation,
    `HeavyTail.stageKernelLaw_failure,
    `HeavyTail.zero_query_fixedCallMinimax_cap,
    `HeavyTail.confidence_zero_query_fixedCallMinimax_lower,
    `HeavyTail.confidence_fixedCallMinimax_lower,
    `HeavyTail.MaskedLower.tuned_maskedKernel_two_moment,
    `HeavyTail.MaskedLower.maskedPrivateInstance_loss,
    `HeavyTail.PrivateInstance.acceptedGaussianW_moment,
    `HeavyTail.PrivateInstance.acceptedGaussianComparatorFactor_moment,
    `HeavyTail.atMostCallMinimax_eq_fixedCallMinimax,
    `HeavyTail.AdaptiveKernel.Policy.chain_outputLaw_kernel,
    `HeavyTail.unified_all_budget_constants,
    `HeavyTail.sharp_convex_heavy_rate,
    `HeavyTail.sharp_strongly_convex_heavy_rate,
    `HeavyTail.matching_statistical_minimax,
    `HeavyTail.full_quadratic_statistical_rate,
    `HeavyTail.expanded_strongly_convex_upper,
    `HeavyTail.fixedThreshold_atMostCallMinimax_upper,
    `HeavyTail.PublicProblem.public_gaussian_primitive,
    `HeavyTail.GaussianEntropy.conditional_mixed_moment_online_rate,
    `HeavyTail.GaussianEntropy.gaussian_clipped_observation_exact_KL_optimizer_exists,
    `HeavyTail.PrivateInstance.stageIdealCappedCoupling_disagreement,
    `HeavyTail.sample_complexity_bounds,
    `HeavyTail.benchmark_convex_minimax_bounds,
    `HeavyTail.benchmark_strong_minimax_bounds,
    `HeavyTail.benchmark_convex_sample_complexity,
    `HeavyTail.benchmark_strong_sample_complexity,
    `HeavyTail.IndependentMoments.independent_centered_sum_moment_of_rpow,
    `HeavyTail.IndependentBernoulli.source_oracle_two_moment_raw_budget,
    `HeavyTail.GaussianEntropy.conditional_mixed_moment_online_rate_ae,
    `HeavyTail.GaussianEntropy.gaussian_clipped_objective_strict_density,
    `HeavyTail.GaussianEntropy.gaussian_clipped_unique_minimizing_density_exists]
  for name in required do
    match env.find? name with
    | some (.thmInfo _) => logInfo m!"REQUIRED THEOREM PRESENT: {name}"
    | _ => throwError "Required theorem missing: {name}"
  let mut names : Array Name := #[]
  let mut definitions : Array Name := #[]
  let mut compilerArtifacts : Array Name := #[]
  for (name, info) in env.constants.toList do
    if name.getRoot == `HeavyTail then
      match info with
      | .thmInfo _ => names := names.push name
      | .defnInfo _ =>
          if info.isUnsafe then compilerArtifacts := compilerArtifacts.push name
          else definitions := definitions.push name
      | .opaqueInfo _ =>
          if info.isUnsafe then compilerArtifacts := compilerArtifacts.push name
          else definitions := definitions.push name
      | _ => pure ()
  names := names.qsort (fun a b => a.toString < b.toString)
  if names.isEmpty then throwError "No HeavyTail theorems found."
  let mut dependencyState : Lean.CollectAxioms.State := {}
  for name in names do
    let (_, nextState) := ((Lean.CollectAxioms.collect name).run env).run dependencyState
    dependencyState := nextState
    let unexpected := dependencyState.axioms.filter (fun a =>
      a != `propext && a != `Classical.choice && a != `Quot.sound)
    unless unexpected.isEmpty do
      throwError "{name}: unexpected axiom dependencies {unexpected}"
    logInfo m!"PASS {name}: standard-only transitive dependency closure"
  for name in definitions do
    let (_, nextState) := ((Lean.CollectAxioms.collect name).run env).run dependencyState
    dependencyState := nextState
    let unexpected := dependencyState.axioms.filter (fun a =>
      a != `propext && a != `Classical.choice && a != `Quot.sound)
    unless unexpected.isEmpty do
      throwError "Definition {name}: unexpected axiom dependencies {unexpected}"
  logInfo m!"DEFINITION AUDIT PASSED: {definitions.size} HeavyTail definitions; standard axioms only."
  -- Lean's compiler emits unsafe runtime copies (e.g. _cstage1) with erased
  -- proof terms using lcProof. They are not logical definitions. The source
  -- scanner rejects authored unsafe code; transitive collection above still
  -- rejects lcProof if any checked theorem or logical definition reaches it.
  logInfo m!"EXCLUDED UNSAFE RUNTIME ARTIFACTS: {compilerArtifacts}"
  logInfo m!"UNION OF AXIOM DEPENDENCIES: {dependencyState.axioms}"
  logInfo m!"AUDIT PASSED: {names.size} HeavyTail theorems; standard axioms only."
