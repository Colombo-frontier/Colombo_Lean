import GradientHessian.DeferredGaussianQueryBasis

/-! Deferred factorization of the original Gaussian input, including exact
transcript functions, complete orthogonal gauges, query columns, invertible
exposed block, and the explicitly enlarged conditional Gaussian law. -/

noncomputable section
namespace GradientHessian.DeferredGaussian
open Classical Matrix MeasureTheory ProbabilityTheory LowRank

theorem deferred_factorization (r s n : ℕ) {Seed : Type*} [MeasurableSpace Seed]
    (policy : VisibleOraclePolicy (r+n) r n 0 Seed)
    (ν : Measure Seed) [IsProbabilityMeasure ν]
    (hunit : VisibleOraclePolicy.IsUnit (r+n) r n 0 policy) {v : NNReal} (hv : v≠0) :
    let μ := ν.prod (iidMatrixLaw (r+n) (s+n) v)
    let st := factors r s n policy
    let G := gramOracleResidual r s n policy
    transcriptField r s n policy≤enlargedField r s n policy ∧
    Measurable[transcriptField r s n policy] (fun w => (st w).1) ∧
    Measurable[transcriptField r s n policy] (fun w => (st w).2.1) ∧
    Measurable[enlargedField r s n policy] (fun w => (st w).2.2) ∧
    (∀ᵐ w ∂μ, (st w).Orthogonal ∧ IsUnit (st w).1.1 ∧
      (st w).2.1ᵀ*w.2*(st w).2.2=fromBlocks (st w).1.1 0 (st w).1.2 (G w)) ∧
    (∀ w,queryColumns (visibleFactorData (st w)) =
      (queryLog (r+n) r n 0 policy (w.2*w.2ᵀ)
        (w.1,visibleFactorData (initialFactorData (r+n) (s+n)))).reverse) ∧
    IndepFun (enlargement r s n policy) G μ ∧
    (∀ (φ : Matrix (Fin r) (Fin s) ℝ → ℝ),Measurable φ → ∀ C : ℝ,(∀ D,‖φ D‖≤C) →
      μ[φ ∘ G | enlargedField r s n policy] =ᵐ[μ] (fun _ => ∫ D,φ D ∂iidMatrixLaw r s v)) := by
  refine ⟨transcriptField_le_enlarged r s n policy,exposed_measurable_transcript r s n policy,
    rowBasis_measurable_transcript r s n policy,columnBasis_measurable_enlarged r s n policy,
    ?_,leading_columns_are_queries r s n policy hunit,
    residual_independent_enlargement r s n policy ν hunit hv,?_⟩
  · filter_upwards [factorization_ae r s n policy ν hunit hv,
      block_form_ae r s n policy ν hunit hv] with w hw hb
    exact ⟨hw.2.1,hw.2.2,hb⟩
  · exact fun φ hφ C hC => residual_conditional_bounded r s n policy ν hunit hv φ hφ C hC

theorem source_dimensions (D k q : ℕ) (hk : k≤D) (hq : q≤D-k) :
    (D-q)+q=D ∧ (D-k-q)+q=D-k ∧ (D-q)-(D-k-q)=k := by omega

theorem source_variance_ne_zero (D : ℕ) (hD : 0<D) : (D:NNReal)⁻¹≠0 := by
  exact inv_ne_zero (by exact_mod_cast Nat.ne_of_gt hD)

end GradientHessian.DeferredGaussian
