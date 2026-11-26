import NCConcave16991.DenseSmoothRandomizedLower
import NCConcave16991.DenseSmoothCompletionProbability
import NCConcave16991.DenseSmoothCalibration
import NCConcave16991.ConeOptimizationLower

/-! # The complete actual smooth baseline and optimization lower envelope -/

noncomputable section

namespace NCConcave16991.DenseSmooth

open DenseWeakHiding Revelation

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

theorem grid_protocol_randomized_lower {n m r : ℕ} (hn : 0 < n)
    (hm : m ≤ n) (hp : m % 2 = n % 2) (hρ : 0 < (m : ℝ) / n)
    (hρ1 : (m : ℝ) / n ≤ 1) (hr : 0 < r) (hrn : r < n)
    (hbudget : 8 * m + 9 * r ≤ n)
    (hcoef : (32 / 63 : ℝ) * r * ((m : ℝ) / ((n : ℝ) - r)) ^ 2 ≤ 1 / 8000)
    (T : ℕ) (hT : 0 < T) :
    LowerBudgetBound (parameters hn hρ T) .individual ((r : ℝ) * T / 2) := by
  intro N hvalid
  by_contra hN
  have hworkR : (2 : ℝ) * N ≤ (r : ℝ) * T := by linarith [lt_of_not_ge hN]
  have hwork : 2 * N ≤ r * T := by exact_mod_cast hworkR
  let D := alignmentDimension (N + 2) (T + 1)
  have hD : 0 < D := alignmentDimension_pos _ _
  apply invalid_budget_of_static_bank_bound hn hD hm hp hρ hρ1 N (33 / 128) (by norm_num) ?_ hvalid
  intro Ω _ P seed
  have hs := stationary_success_probability_additive n m T D hn hD hm hp hρ P hρ1 seed N r
    hT hr hwork hrn hbudget hcoef (alignmentDimension_information (N + 2) (T + 1))
  have hf := future_alignment_probability_small hn hD hm hp hρ P seed N rfl
  change (stageBankLaw n m D (T + 1) hm).eventMass
    (ActualSuccessEvent n m T D hn hD hm hp hρ P hρ1 seed N) ≤ 33 / 128
  change (stageBankLaw n m D (T + 1) hm).eventMass
    (FutureBadEvent n m T D hn hD hm hp hρ P seed N) ≤ 1 / 128 at hf
  linarith

theorem parity_grid_randomized_lower (n : ℕ) (hn : 65536 ≤ n) (T : ℕ) (hT : 0 < T) :
    LowerBudgetBound (parameters (show 0 < n by omega)
      (DenseSmoothCalibration.gridBias_pos (show 0 < n by omega)) T) .individual
      ((rowCost n (DenseSmoothCalibration.gridBias n) : ℝ) * T / 2) := by
  have hn0 : 0 < n := by omega
  have hb : 8 * parityRoundedSqrt n + 9 * rowCost n ((parityRoundedSqrt n : ℝ) / n) ≤ n := by
    exact_mod_cast parityGrid_row_information_interior hn
  have hr := (parityGrid_rowCost_linear hn).2
  have hm : parityRoundedSqrt n ≤ n := by omega
  have hρ1 : (parityRoundedSqrt n : ℝ) / n ≤ 1 :=
    (div_le_one (show (0 : ℝ) < n by exact_mod_cast hn0)).mpr (by exact_mod_cast hm)
  exact grid_protocol_randomized_lower hn0 hm (parityRoundedSqrt_mod_two n)
    (DenseSmoothCalibration.gridBias_pos hn0) hρ1 (by omega) (by omega) hb
    (parityGrid_information_budget (show 256 ≤ n by omega)) T hT

end DenseSmooth

namespace DenseSmoothCalibration

theorem smooth_baseline_lower (p : ProblemParameters) (hA : 2 ≤ dimensionlessA p) :
    LowerBudgetBound p .individual
      (((p.n : ℝ) + dimensionlessA p * Real.sqrt (p.n : ℝ)) / baselineDenominator) :=
  baseline_lower_from_normalized_sources DenseSmooth.parity_grid_randomized_lower
    (fun n hn T _ ↦ DenseSmooth.one_randomized_lower n hn T) p hA

end DenseSmoothCalibration

namespace ConeCalibration

theorem optimization_randomized_lower (p : ProblemParameters) (hA : 2 ≤ dimensionlessA p) :
    LowerBudgetBound p .individual
      (((p.n : ℝ) + dimensionlessA p * optimizationLower (p.n : ℝ) (dimensionlessB p)) /
        globalDenominator DenseSmoothCalibration.baselineDenominator) :=
  optimization_lower_of_smooth_baseline p hA DenseSmoothCalibration.baselineDenominator_pos
    (DenseSmoothCalibration.smooth_baseline_lower p hA)

end ConeCalibration
end NCConcave16991
