import LowRank.GaussianFactorMassProcess

/-! The cumulative query-mass bound for the actual iid input and actual
visible-policy run. The entire Gaussian factor process is integrated;
no separate conditional-increment premise is supplied by the caller. -/

namespace LowRank
open Matrix MeasureTheory
open scoped Matrix BigOperators
noncomputable section

theorem gramOracleQueryMass_mean_sum_le (r s n : ℕ) {S : Type*} [MeasurableSpace S]
    (ν : Measure S) [IsProbabilityMeasure ν] (policy : VisibleOraclePolicy (r + n) r n 0 S)
    (hunit : VisibleOraclePolicy.IsUnit (r + n) r n 0 policy) (hs : s ≤ r)
    {v : NNReal} (hv : v ≠ 0) :
    (∫ p, gramOracleQueryMass r s n policy p ∂ν.prod (iidMatrixLaw (r + n) (s + n) v)) ≤
      ∑ j ∈ Finset.range n, ((r : ℝ) - s) / (r + j + 1) := by
  have h := gaussianFactor_run_mass_mean_le (r + n) (s + n) r s n 0 ν
    (compileGramOracle r s n policy) (compileGramOracle_unit r s n policy hunit)
    (fun _ : S => initialFactorData (r + n) (s + n)) measurable_const
    (fun _ => initialFactorData_orthogonal _ _)
    (Filter.Eventually.of_forall (fun _ => initialFactorData_A_injective _ _)) hs hv
  have hz : ∀ D : Matrix (Fin (r + n)) (Fin (s + n)) ℝ,
      factorKernelMass (initialFactorData (r + n) (s + n)) D = 0 := by
    intro D
    simp [factorKernelMass, Matrix.trace]
  have he : ∀ p : S × Matrix (Fin (r + n)) (Fin (s + n)) ℝ,
      factorKernelMass (gramOracleFactors r s n policy p) (gramOracleResidual r s n policy p) =
        gramOracleQueryMass r s n policy p := by
    intro p
    have hr := initialFactorData_final_reconstruct r s n (compileGramOracle r s n policy) p
    change representedMatrix (gramOracleFactors r s n policy p) (gramOracleResidual r s n policy p) = p.2 at hr
    simp only [factorKernelMass, factorKernelProjector, hr, gramOracleQueryMass, gramOracleKernelCoordinates]
  change (∫ p, factorKernelMass (gramOracleFactors r s n policy p) (gramOracleResidual r s n policy p)
    ∂ν.prod (iidMatrixLaw (r + n) (s + n) v)) ≤
      (∫ p : S × Matrix (Fin (r + n)) (Fin (s + n)) ℝ,
        factorKernelMass (initialFactorData (r + n) (s + n)) p.2
          ∂ν.prod (iidMatrixLaw (r + n) (s + n) v)) + _ at h
  simpa only [hz, integral_zero, zero_add, he] using h

theorem remaining_dimension_sum_bound (r n : ℕ) {k : ℝ} (hk : 0 ≤ k) (hr : 0 < r) :
    (∑ j ∈ Finset.range n, k / (r + j + 1 : ℝ)) ≤ k * n / r := by
  have hr' : 0 < (r : ℝ) := by exact_mod_cast hr
  calc
    _ ≤ ∑ _j ∈ Finset.range n, k / (r : ℝ) := by
      apply Finset.sum_le_sum
      intro j _
      exact div_le_div_of_nonneg_left hk hr' (by linarith [show (0 : ℝ) ≤ (j : ℝ) from Nat.cast_nonneg j])
    _ = _ := by simp; ring

theorem gramOracleQueryMass_mean_le (r s n : ℕ) {S : Type*} [MeasurableSpace S]
    (ν : Measure S) [IsProbabilityMeasure ν] (policy : VisibleOraclePolicy (r + n) r n 0 S)
    (hunit : VisibleOraclePolicy.IsUnit (r + n) r n 0 policy) (hs : s ≤ r) (hr : 0 < r)
    {v : NNReal} (hv : v ≠ 0) :
    (∫ p, gramOracleQueryMass r s n policy p ∂ν.prod (iidMatrixLaw (r + n) (s + n) v)) ≤
      ((r : ℝ) - s) * n / r :=
  (gramOracleQueryMass_mean_sum_le r s n ν policy hunit hs hv).trans
    (remaining_dimension_sum_bound r n (sub_nonneg.mpr (by exact_mod_cast hs)) hr)

theorem ambientOracleQueryMass_mean_le (r s n : ℕ) {S : Type*} [MeasurableSpace S]
    (ν : Measure S) [IsProbabilityMeasure ν] (policy : AmbientOraclePolicy (r + n) n S)
    (hs : s ≤ r) (hr : 0 < r) {v : NNReal} (hv : v ≠ 0) :
    (∫ p, gramOracleQueryMass r s n (normalizedAmbientPolicy r s n policy) p
      ∂ν.prod (iidMatrixLaw (r + n) (s + n) v)) ≤ ((r : ℝ) - s) * n / r :=
  gramOracleQueryMass_mean_le r s n ν (normalizedAmbientPolicy r s n policy)
    (normalizedAmbientPolicy_unit r s n policy) hs hr hv

end
end LowRank
