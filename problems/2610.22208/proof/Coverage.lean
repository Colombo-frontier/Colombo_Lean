import GradientHessian

/-! Explicit headline type contracts and every mapped source-claim anchor. -/
example : GradientHessian.Model.MainLowerBound :=
  GradientHessian.PresampledConstruction.source_main_lower

example : GradientHessian.Model.UniformParameterLowerBound :=
  GradientHessian.PresampledConstruction.source_uniform_parameter_lower

example (d : ℕ) {T : ℝ} {h : ℕ}
    (hT : 1 ≤ T) (hh : 1 ≤ h) (hhT : (h : ℝ) ≤ T) :
    ∃ (A : GradientHessian.Model.Algorithm d) (G : ℕ),
      A.Guarantees T G h ∧
      (G : ℝ) ≤ 14740 * T ^ ((3 : ℝ) / 2) / Real.sqrt (h : ℝ) :=
  GradientHessian.NalenPolicy.source_rich_upper d hT hh hhT

example (d : ℕ) {T : ℝ} (hT : 1 ≤ T) :
    ∃ (A : GradientHessian.Model.Algorithm d) (G : ℕ),
      A.Guarantees T G 0 ∧
      (G : ℝ) ≤ 4096 * ((d : ℝ) + T * (d : ℝ) ^ ((1 : ℝ) / 3)) :=
  GradientHessian.NalenPolicy.source_ordinary_upper_all_dimensions d hT

#check GradientHessian.AmbientOrthonormal.ambient_deferred_factorization
#check GradientHessian.AmbientOrthonormal.compile_simulates_ae
#check GradientHessian.AugmentedDirectionFamilies.inner_action_probability
#check GradientHessian.AugmentedDirectionFamilies.localized_action_probability
#check GradientHessian.AugmentedDirectionFamilies.mark_action_probability
#check GradientHessian.AugmentedDirectionFamilies.old_action_probability
#check GradientHessian.AugmentedNumericalEarlyContainment.early_mem_rawEvent
#check GradientHessian.AugmentedNumericalProbability.raw_probability
#check GradientHessian.AugmentedPolicy.prefix_true_replies
#check GradientHessian.AugmentedRepairCost.expected_repair_cost
#check GradientHessian.CensoredOracle.serve_ordinary_decoder
#check GradientHessian.CensoredOriginalExecution.true_jet_policy_execution
#check GradientHessian.CensoredPolicy.serve_completedOrdinary
#check GradientHessian.CensoredPolicy.serve_completedRich
#check GradientHessian.CommonBaseline.diagonal_identification_has_uncertified_stationary
#check GradientHessian.CommonBaseline.diagonal_identification_transport
#check GradientHessian.ControllerCensor.serve_richJet
#check GradientHessian.DeferredGaussian.source_dimensions
#check GradientHessian.DeferredGaussian.source_variance_ne_zero
#check GradientHessian.FirstHeight.firstAmplitude_linear
#check GradientHessian.FirstHeight.first_height_lemma
#check GradientHessian.ForkLifetime.lifetimeFraction_pos
#check GradientHessian.ForkLifetime.lifetime_bounds
#check GradientHessian.GaussianConcentration.gaussian_extreme_singular_values
#check GradientHessian.GaussianConcentration.gaussian_largestExpansion_mean
#check GradientHessian.GaussianConcentration.gaussian_leastExpansion_mean
#check GradientHessian.GaussianConcentration.gaussian_lipschitz_concentration
#check GradientHessian.GaussianConcentration.gaussian_poincare
#check GradientHessian.GaussianConcentration.mean_norm_bounds
#check GradientHessian.GaussianHilbert.norm_square_two_sided
#check GradientHessian.GaussianPosterior.wishart_kernel_projector_spec
#check GradientHessian.HigherHierarchy.activation
#check GradientHessian.HigherHierarchy.incomingCouplingTerm_scaledJets
#check GradientHessian.HigherHierarchy.incomingCoupling_first_source_bound
#check GradientHessian.HigherHierarchy.incomingCoupling_higher_source_bound
#check GradientHessian.HigherHierarchy.nodePerturbation_source_bound
#check GradientHessian.HigherHierarchy.normalizedScalar_hessian_lipschitz
#check GradientHessian.HigherHierarchy.residual_bounded
#check GradientHessian.HigherHierarchy.residual_global_bounds
#check GradientHessian.HigherHierarchy.scalar_coercive
#check GradientHessian.HigherHierarchy.scalar_energy
#check GradientHessian.HigherHierarchy.scalar_gap_source_height
#check GradientHessian.HigherHierarchy.scalar_hessian_lipschitz
#check GradientHessian.HigherHierarchy.selectedChildren_derivative_bound
#check GradientHessian.HigherHierarchy.source_regularity
#check GradientHessian.Inner.inner_bounds
#check GradientHessian.Inner.inner_lemma
#check GradientHessian.InverseGate.source_numerical_activation
#check GradientHessian.LatchLemma.latch_bounds
#check GradientHessian.Leaf.leaf_lemma
#check GradientHessian.Leaf.mixture_localization
#check GradientHessian.Leaf.numerical_gradient_one_product
#check GradientHessian.Leaf.numerical_hessian_from_matrix
#check GradientHessian.Leaf.objective_one_product
#check GradientHessian.Leaf.ordinaryDecoder_borel
#check GradientHessian.Leaf.ordinaryJet_one_product
#check GradientHessian.Leaf.richJet_known_matrix
#check GradientHessian.Leaf.source_leaf_lemma
#check GradientHessian.Localized.localized_robustness
#check GradientHessian.Localized.localized_transition_excludes_small_gradient
#check GradientHessian.Localized.one_lt_sixteen_div_sqrt_two
#check GradientHessian.Localized.small_gradient_distance
#check GradientHessian.Localized.small_gradient_opens_port
#check GradientHessian.LocalizedProductDerivatives.localized_bounds
#check GradientHessian.MachinePosterior.manuscript_machine_overlap
#check GradientHessian.MatrixGoodAnalytic.positive_probability_source_and_compressed_kernel
#check GradientHessian.MatrixGoodAnalytic.sourceGoodEvent_compressed_spectrum
#check GradientHessian.MatrixGoodUpper.exists_quarter_sphere_net
#check GradientHessian.MatrixKernelConcentration.opNorm_le_twice_quadratic_net
#check GradientHessian.NalenPolicy.source_ordinary_complexity_upper_all_dimensions
#check GradientHessian.NalenPolicy.source_ordinary_upper_all_dimensions
#check GradientHessian.NalenPolicy.source_rich_complexity_upper
#check GradientHessian.NalenPolicy.source_rich_upper
#check GradientHessian.PresampledConstruction.augmented_replies_true_ae
#check GradientHessian.PresampledConstruction.expected_augmented_early_cost
#check GradientHessian.PresampledConstruction.expected_augmented_repair_cost
#check GradientHessian.PresampledConstruction.expected_early_cost
#check GradientHessian.PresampledConstruction.source_augmented_success_probability_full
#check GradientHessian.PresampledConstruction.source_main_lower
#check GradientHessian.PresampledConstruction.source_success_probability_full
#check GradientHessian.PresampledConstruction.source_uniform_parameter_lower
#check GradientHessian.RadialHigherDerivatives.radial_squash_bounds
#check GradientHessian.ReadoutCertificate.source_readout_certificate
#check GradientHessian.ReadoutCertificate.source_readout_synthesis
#check GradientHessian.ReadoutFilter.degree_linear_bound
#check GradientHessian.ReadoutOracle.readoutPolicy_exact
#check GradientHessian.SelectingFork.arbitrary_selection_fork_bound
#check GradientHessian.SelectingFork.arbitrary_selection_lifetime
#check GradientHessian.SelectorPayloadBounds.finite_weight_nonneg
#check GradientHessian.SelectorPayloadBounds.finite_weight_partition
#check GradientHessian.SelectorPayloadBounds.manuscript_selector_bound
#check GradientHessian.SelectorPayloadBounds.weightedScalar_derivative_bound
#check GradientHessian.SharpSphereTail.sphereLaw_sharp_tail
#check GradientHessian.SourceOperator.source_inner_activation
#check GradientHessian.SourceOperator.source_inner_bounds
#check GradientHessian.SphereColumnNorm.manuscript_column_sphere_tail
#check GradientHessian.SphereSmallBall.manuscript_small_ball
#check GradientHessian.TestSelectionMachine.Program.record_calls
#check GradientHessian.TestSelectionMachine.Program.recorded_ever_iff
#check GradientHessian.UnmarkedReadout.source_unmarked_test
#check GradientHessian.UnmarkedReadout.source_unmarked_test_of_earlier_data
#check GradientHessian.VisibilityWindow.leaf_visibility_window_bound
#check GradientHessian.VisibilityWindow.visibility_window_bound
