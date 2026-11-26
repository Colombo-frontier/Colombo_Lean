import NoisyZO.LowerConstants
import NoisyZO.RateArithmetic

/-!
# Saturated lower-bound bandwidth and rate

This file verifies the last real-power calculation in the lower bound: the
manuscript's saturated bandwidth satisfies the KL budget and its induced
strong-convexity loss dominates the saturated minimax rate.
-/

namespace NoisyZO

noncomputable section

/-- The bandwidth used by the adaptive Gaussian lower bound. -/
def lowerBandwidth (a d T β : ℝ) : ℝ :=
  min 1 ((d ^ 2 / (16 * a ^ 2 * T)) ^ (1 / (2 * β) : ℝ))

theorem lowerBandwidth_pos {a d T β : ℝ}
    (ha : 0 < a) (hd : 0 < d) (hT : 0 < T) (hβ : 0 < β) :
    0 < lowerBandwidth a d T β := by
  apply lt_min (by norm_num)
  exact Real.rpow_pos_of_pos (by positivity) _

theorem lowerBandwidth_le_one (a d T β : ℝ) :
    lowerBandwidth a d T β ≤ 1 :=
  min_le_left _ _

/-- Raising the saturated bandwidth to `2β` stays below its unsaturated
information budget. -/
theorem lowerBandwidth_two_beta_le {a d T β : ℝ}
    (ha : 0 < a) (hd : 0 < d) (hT : 0 < T) (hβ : 0 < β) :
    lowerBandwidth a d T β ^ (2 * β) ≤
      d ^ 2 / (16 * a ^ 2 * T) := by
  let base : ℝ := d ^ 2 / (16 * a ^ 2 * T)
  have hbase : 0 < base := by dsimp [base]; positivity
  have hbw : lowerBandwidth a d T β ≤ base ^ (1 / (2 * β) : ℝ) := by
    exact min_le_right _ _
  calc
    lowerBandwidth a d T β ^ (2 * β) ≤
        (base ^ (1 / (2 * β) : ℝ)) ^ (2 * β) :=
      Real.rpow_le_rpow (le_of_lt (lowerBandwidth_pos ha hd hT hβ)) hbw (by positivity)
    _ = base := by
      rw [← Real.rpow_mul (le_of_lt hbase)]
      convert Real.rpow_one base using 2
      field_simp [ne_of_gt hβ]
    _ = d ^ 2 / (16 * a ^ 2 * T) := by rfl

/-- The chosen bandwidth enforces the manuscript's `1/8` average-KL
threshold. -/
theorem lowerBandwidth_KL_budget {a d T β : ℝ}
    (ha : 0 < a) (hd : 0 < d) (hT : 0 < T) (hβ : 0 < β) :
    2 * a ^ 2 * T * lowerBandwidth a d T β ^ (2 * β) / d ^ 2 ≤
      (1 / 8 : ℝ) :=
  KL_budget_le_one_eighth ha hT hd
    (lowerBandwidth_two_beta_le ha hd hT hβ)

/-- For the normalized amplitude `a ≤ 1/4`, saturation loses no rate:
`h^(2β-2)` dominates `min {1, (d²/T)^((β-1)/β)}`. -/
theorem min_rate_le_lowerBandwidth_power {a d T β : ℝ}
    (ha : 0 < a) (ha4 : a ≤ 1 / 4)
    (hd : 0 < d) (hT : 0 < T) (hβ : 2 < β) :
    min 1 ((d ^ 2 / T) ^ rateExponent β) ≤
      lowerBandwidth a d T β ^ (2 * β - 2) := by
  let raw : ℝ := d ^ 2 / T
  let base : ℝ := d ^ 2 / (16 * a ^ 2 * T)
  have hβ0 : 0 < β := lt_trans (by norm_num) hβ
  have hp : 0 < rateExponent β := by
    unfold rateExponent
    exact div_pos (by linarith) hβ0
  have hraw : 0 < raw := by dsimp [raw]; positivity
  have hbase : 0 < base := by dsimp [base]; positivity
  have haSq : 16 * a ^ 2 ≤ 1 := by nlinarith [sq_nonneg (a - 1 / 4)]
  have hrawBase : raw ≤ base := by
    dsimp [raw, base]
    have hden : 0 < 16 * a ^ 2 * T := by positivity
    apply (div_le_div_iff₀ hT hden).2
    have hdSq : 0 ≤ d ^ 2 := sq_nonneg d
    apply mul_le_mul_of_nonneg_left _ hdSq
    calc
      16 * a ^ 2 * T ≤ 1 * T := mul_le_mul_of_nonneg_right haSq hT.le
      _ = T := one_mul T
  by_cases hlarge : 1 ≤ base
  · have hq : 1 ≤ base ^ (1 / (2 * β) : ℝ) := by
      simpa only [Real.one_rpow] using
        Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hlarge (by positivity)
    rw [lowerBandwidth, show d ^ 2 / (16 * a ^ 2 * T) = base by rfl,
      min_eq_left hq, Real.one_rpow]
    exact min_le_left _ _
  · have hbaseOne : base ≤ 1 := le_of_not_ge hlarge
    have hq : base ^ (1 / (2 * β) : ℝ) ≤ 1 := by
      simpa only [Real.one_rpow] using
        Real.rpow_le_rpow (le_of_lt hbase) hbaseOne (by positivity)
    rw [lowerBandwidth, show d ^ 2 / (16 * a ^ 2 * T) = base by rfl,
      min_eq_right hq, balanced_bias_exponent (le_of_lt hbase) hβ0]
    exact (min_le_right _ _).trans
      (Real.rpow_le_rpow (le_of_lt hraw) hrawBase (le_of_lt hp))

/-- The exact `3a²/64` loss constant therefore multiplies the desired
saturated rate. -/
theorem lower_loss_rate
    {a d T β : ℝ} (ha : 0 < a) (ha4 : a ≤ 1 / 4)
    (hd : 0 < d) (hT : 0 < T) (hβ : 2 < β) :
    (3 * a ^ 2 / 64) * min 1 ((d ^ 2 / T) ^ rateExponent β) ≤
      (3 * a ^ 2 / 64) * lowerBandwidth a d T β ^ (2 * β - 2) := by
  exact mul_le_mul_of_nonneg_left
    (min_rate_le_lowerBandwidth_power ha ha4 hd hT hβ) (by positivity)

end

end NoisyZO
