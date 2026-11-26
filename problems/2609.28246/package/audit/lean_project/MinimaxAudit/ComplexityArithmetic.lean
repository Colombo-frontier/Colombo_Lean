import MinimaxAudit.LowerScaling

/-! Accuracy-exponent inversion and absorption of the additive upper-budget
constant. This module does not assert inclusion of arbitrary deterministic
policies into the jointly Borel randomized policy class. -/
namespace MinimaxAudit

theorem rate_budget_inverse {beta a Q B : ℝ}
    (hbeta : 0 < beta) (ha : 0 < a) (hQ : 0 < Q) (hB : 0 ≤ B)
    (hbudget : a * Q / (B+1) ^ beta ≤ 1) :
    (a * Q) ^ (1 / beta) ≤ B+1 := by
  have hb : 0 < B+1 := by linarith
  have hpow : 0 < (B+1) ^ beta := Real.rpow_pos_of_pos hb _
  have h := (div_le_iff₀ hpow).1 hbudget
  have hmono := Real.rpow_le_rpow (mul_pos ha hQ).le (by simpa using h) (by positivity : 0 ≤ 1 / beta)
  rw [← Real.rpow_mul hb.le, mul_one_div_cancel hbeta.ne', Real.rpow_one] at hmono
  exact hmono

theorem rate_budget_asymptotic {beta a Q B : ℝ}
    (hbeta : 0 < beta) (ha : 0 < a) (hB : 0 ≤ B)
    (hQ : (2 : ℝ) ^ beta / a ≤ Q)
    (hbudget : a * Q / (B+1) ^ beta ≤ 1) :
    a ^ (1 / beta) / 2 * Q ^ (1 / beta) ≤ B := by
  have hQ0 : 0 < Q := (div_pos (Real.rpow_pos_of_pos (by norm_num) _) ha).trans_le hQ
  have hbase : (2 : ℝ) ^ beta ≤ a * Q := by
    have h := (div_le_iff₀ ha).1 hQ
    simpa [mul_comm] using h
  have htwo : 2 ≤ (a * Q) ^ (1 / beta) := by
    have h := Real.rpow_le_rpow (Real.rpow_nonneg (by norm_num) _) hbase
      (by positivity : 0 ≤ 1 / beta)
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), mul_one_div_cancel hbeta.ne', Real.rpow_one] at h
    exact h
  have hB1 := rate_budget_inverse hbeta ha hQ0 hB hbudget
  rw [Real.mul_rpow ha.le hQ0.le] at htwo hB1
  nlinarith only [htwo, hB1]

theorem upper_budget_additive_absorption {alpha Q C ell : ℝ}
    (halpha : 0 ≤ alpha) (hQ : 1 ≤ Q) (hC : 0 ≤ C) (hell : 0 ≤ ell) :
    C * (1 + Q ^ alpha) * ell ≤ (2 * C) * Q ^ alpha * ell := by
  have hpow : 1 ≤ Q ^ alpha := Real.one_le_rpow hQ halpha
  have h := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (show 1 + Q ^ alpha ≤ 2 * Q ^ alpha by linarith) hC) hell
  calc
    _ ≤ C * (2 * Q ^ alpha) * ell := h
    _ = _ := by ring
end MinimaxAudit
