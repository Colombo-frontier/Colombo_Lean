import LowerRisk

namespace Task006.LowerRisk

theorem square_root_risk_constant :
    (146/100:ℝ) < 8*(1-Real.sqrt (2/3:ℝ)) := by
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2/3)
  have hn := Real.sqrt_nonneg (2/3:ℝ)
  nlinarith

/-- The manuscript's displayed 1.46 epsilon contradiction follows from the
same unnormalized event moments used by the complete main lower proof. -/
theorem large_dimension_risk_gt_146 (eps risk a n e : ℝ)
    (heps : 0 < eps) (ha : 1/2 ≤ a) (hn : 0 ≤ n)
    (he : e ≤ 1/3) (hCS : n^2 ≤ a*e)
    (hrisk : 16*eps*(a-n) ≤ risk) : (146/100)*eps < risk := by
  have ha0 : 0 ≤ a := by linarith
  have hs0 := Real.sqrt_nonneg (2/3:ℝ)
  have hs2 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2/3)
  have hs1 : Real.sqrt (2/3:ℝ) ≤ 1 := by nlinarith
  have hnn : n ≤ a*Real.sqrt (2/3:ℝ) := by
    have hb : n^2 ≤ a/3 := hCS.trans (by nlinarith)
    have haa := mul_nonneg ha0 (show 0 ≤ a-1/2 by linarith)
    have hsquare : (a*Real.sqrt (2/3:ℝ))^2 = a^2*(2/3) := by
      rw [mul_pow,hs2]
    have hr0 : 0 ≤ a*Real.sqrt (2/3:ℝ) := mul_nonneg ha0 hs0
    nlinarith
  have hagap : (1-Real.sqrt (2/3:ℝ))/2 ≤ a-n := by
    have hh := mul_nonneg (show 0 ≤ a-1/2 by linarith) (show 0 ≤ 1-Real.sqrt (2/3:ℝ) by linarith)
    nlinarith
  have h1 : 8*eps*(1-Real.sqrt (2/3:ℝ)) ≤ risk := by
    have hp := mul_le_mul_of_nonneg_left hagap (show 0 ≤ 16*eps by positivity)
    nlinarith
  have h2 := mul_lt_mul_of_pos_right square_root_risk_constant heps
  nlinarith

#print axioms square_root_risk_constant
#print axioms large_dimension_risk_gt_146
end Task006.LowerRisk
