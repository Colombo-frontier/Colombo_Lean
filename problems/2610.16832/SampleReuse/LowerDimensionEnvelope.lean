import SampleReuse.SlowDimension
import SampleReuse.ComplexityLogarithms

open SecondOrder

namespace SampleReuse
noncomputable section

def lowerDimensionThreshold (P : Parameters) (C ε γ : ℝ) : ℕ :=
  max (FirstOrderDimension (slowBlockSize P ε) (slowLinks P ε))
    ⌈C*(1+Real.log (2/γ)/γ^4+1/γ^3)⌉₊

/-- The concrete maximum of the two hard-family dimensions satisfies the
dimension envelope stated in the manuscript, with every rounding included. -/
theorem lowerDimensionThreshold_source_bound (P : Parameters) {C ε γ : ℝ}
    (hC : 0 ≤ C) (hc : SlowCalibratedConditions P ε) (hγ : 0 < γ) (hg : γ ≤ 1) :
    (lowerDimensionThreshold P C ε γ : ℝ) ≤
      (C+1)*(1+P.gap*(slowBlockSize P ε : ℝ)^(3/4 : ℝ)/ε+
        Real.log (2/γ)/γ^4+1/γ^3) := by
  have hl : 0 ≤ Real.log (2/γ) := Real.log_nonneg
    ((le_div_iff₀ hγ).mpr (by linarith))
  have ha : 0 ≤ P.gap*(slowBlockSize P ε : ℝ)^(3/4 : ℝ)/ε := by
    have := P.gap_pos
    have := hc.tolerance_pos
    positivity
  have hb : 0 ≤ Real.log (2/γ)/γ^4+1/γ^3 := by positivity
  have hd := slow_calibrated_dimension P hc
  have hr := (Nat.ceil_lt_add_one
    (mul_nonneg hC (by positivity : 0 ≤ 1+Real.log (2/γ)/γ^4+1/γ^3))).le
  unfold lowerDimensionThreshold
  rw [Nat.cast_max]
  apply max_le
  · nlinarith [mul_nonneg hC ha,mul_nonneg hC hb]
  · nlinarith [mul_nonneg hC ha]

/-- For fixed model parameters the first-order dimension contribution is
epsilon inverse times the three-quarter power of a logarithm. -/
theorem slow_calibrated_dimension_log_bound (P : Parameters) {ε : ℝ}
    (hc : SlowCalibratedConditions P ε) (he : ε ≤ 1) :
    (FirstOrderDimension (slowBlockSize P ε) (slowLinks P ε) : ℝ) ≤
      P.gap*(slowLogConstant P*(1+Real.log (1/ε)))^(3/4 : ℝ)/ε := by
  apply (slow_calibrated_dimension P hc).trans
  apply div_le_div_of_nonneg_right _ hc.tolerance_pos.le
  apply mul_le_mul_of_nonneg_left _ P.gap_pos.le
  exact Real.rpow_le_rpow (Nat.cast_nonneg _) (slowBlockSize_log_bound P hc.tolerance_pos he)
    (by norm_num)

theorem lowerDimensionThreshold_log_bound (P : Parameters) {C ε γ : ℝ}
    (hC : 0 ≤ C) (hc : SlowCalibratedConditions P ε) (he : ε ≤ 1)
    (hγ : 0 < γ) (hg : γ ≤ 1) :
    (lowerDimensionThreshold P C ε γ : ℝ) ≤
      (C+1)*(1+P.gap*(slowLogConstant P*(1+Real.log (1/ε)))^(3/4 : ℝ)/ε+
        Real.log (2/γ)/γ^4+1/γ^3) := by
  apply (lowerDimensionThreshold_source_bound P hC hc hγ hg).trans
  have hp := Real.rpow_le_rpow (Nat.cast_nonneg (slowBlockSize P ε) : (0 : ℝ) ≤ _)
    (slowBlockSize_log_bound P hc.tolerance_pos he) (by norm_num : (0 : ℝ) ≤ 3/4)
  gcongr
  · exact hc.tolerance_pos.le
  · exact P.gap_pos.le

end
end SampleReuse
