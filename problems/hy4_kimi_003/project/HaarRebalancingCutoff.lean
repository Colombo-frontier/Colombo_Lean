import HaarRebalancingMarkov

/-!
The exact Markov-cutoff normalization and inverse-power event equivalence.
Global rebalancing constants are supplied separately by RebalancingArithmetic.
-/

open Set MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal

namespace Task006.HaarRebalancing
noncomputable section

/-- The Markov root cutoff is exactly K0 L/sqrt(d), not an additional
unproved threshold comparison. -/
theorem thirdHalf_markov_cutoff {C L d : ℝ} (hC : 0 ≤ C) (hL : 0 < L) (hd : 0 < d) :
    (2 * (C * L ^ (3 / 2 : ℝ) / d ^ (3 / 4 : ℝ))) ^ (2 / 3 : ℝ) =
      (2 * C) ^ (2 / 3 : ℝ) * L / Real.sqrt d := by
  have h2C : 0 ≤ 2 * C := mul_nonneg (by norm_num) hC
  have hLp : 0 ≤ L ^ (3 / 2 : ℝ) := Real.rpow_nonneg hL.le _
  have hdp : 0 ≤ d ^ (3 / 4 : ℝ) := Real.rpow_nonneg hd.le _
  rw [show 2 * (C * L ^ (3 / 2 : ℝ) / d ^ (3 / 4 : ℝ)) =
    (2 * C) * L ^ (3 / 2 : ℝ) / d ^ (3 / 4 : ℝ) by ring]
  rw [Real.div_rpow (mul_nonneg h2C hLp) hdp, Real.mul_rpow h2C hLp,
    ← Real.rpow_mul hL.le, ← Real.rpow_mul hd.le]
  norm_num [Real.sqrt_eq_rpow]

/-- Increasing the actual nonnegative sample moment is equivalent to
increasing its actual two-thirds root. -/
theorem directionalMoment_ge_iff_root_ge {Sample E : Type*} [MeasurableSpace Sample]
    (σ : Measure Sample) (D : Sample → E → ℝ) (q : E) {M : ℝ} (hM : 0 ≤ M) :
    M ≤ directionalMoment σ D q ↔ M ^ (2 / 3 : ℝ) ≤ directionalRootMoment σ D q := by
  unfold directionalRootMoment
  exact (Real.rpow_le_rpow_iff hM (directionalMoment_nonneg σ D q) (by norm_num)).symm

end
end Task006.HaarRebalancing
