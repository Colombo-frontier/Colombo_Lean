import NCConcave16991.ConeRandomizedLower
import NCConcave16991.ConeCalibrationAssembly

/-! # The cone contribution at the original public parameters -/

noncomputable section

namespace NCConcave16991.ConeCalibration

theorem normalized_cone_lower (p : ProblemParameters) (hn : 65536 ≤ (p.n : ℝ))
    (hB : diameterThreshold ≤ dimensionlessB p) :
    LowerBudgetBound (normalizedParameters p hn hB) .individual
      ((p.n : ℝ) * (publicStageIndex p + 1 : ℕ) / 4096) := by
  have hr := publicRadius_bounds p hn hB
  have hq := publicRatio_bounds p hn hB
  exact ConeLower.normalized_randomized_lower p.n p.n_pos (publicStageIndex p)
    (publicRadius p) (publicRatio p) hr.1 hq.1 hq.2.2 hq.2.1

theorem cone_regime_randomized_lower (p : ProblemParameters) (hn : 65536 ≤ (p.n : ℝ))
    (hB : diameterThreshold ≤ dimensionlessB p) (hA : 2 ≤ dimensionlessA p) :
    LowerBudgetBound p .individual
      (((p.n : ℝ) + dimensionlessA p * optimizationLower (p.n : ℝ) (dimensionlessB p)) /
        regimeDenominator) :=
  cone_regime_lower p hn hB hA (normalized_cone_lower p hn hB)

/-- The sole remaining input here is the independently constructed smooth
finite-sum baseline. The normalized cone lower theorem is fully discharged. -/
theorem optimization_lower_of_smooth_baseline (p : ProblemParameters) (hA : 2 ≤ dimensionlessA p)
    {S : ℝ} (hS : 0 < S)
    (hSmooth : LowerBudgetBound p .individual
      (((p.n : ℝ) + dimensionlessA p * Real.sqrt (p.n : ℝ)) / S)) :
    LowerBudgetBound p .individual
      (((p.n : ℝ) + dimensionlessA p * optimizationLower (p.n : ℝ) (dimensionlessB p)) /
        globalDenominator S) :=
  optimization_lower_from_sources p hA hS hSmooth (normalized_cone_lower p)

end NCConcave16991.ConeCalibration
