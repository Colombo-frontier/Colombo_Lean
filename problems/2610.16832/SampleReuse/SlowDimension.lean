import SampleReuse.SlowCalibratedRates
import SecondOrder.FirstOrderHorizonConstants

open SecondOrder

namespace SampleReuse
noncomputable section

theorem slowAlpha_cube_rpow (d : ℕ) : slowAlpha d^3 = (d:ℝ)^(3/4:ℝ) := by
  rw [slowAlpha_rpow,← Real.rpow_natCast,← Real.rpow_mul (Nat.cast_nonneg d)]
  norm_num

/-- The actual slow-family ambient dimension has the manuscript's D^(3/4)/epsilon
bound, including the floor in the chain length. -/
theorem slow_calibrated_dimension (P : Parameters) {ε : ℝ} (hc : SlowCalibratedConditions P ε) :
    (FirstOrderDimension (slowBlockSize P ε) (slowLinks P ε):ℝ) ≤
      P.gap*(slowBlockSize P ε:ℝ)^(3/4:ℝ)/ε := by
  let d := slowBlockSize P ε
  let n := slowLinks P ε+1
  have hd : 0 < d := slowBlockSize_pos P hc.tolerance_pos
  have hα := slowAlpha_pos hd
  have hA : ε*slowAlpha d ≤ slowAmplitude d ε := by
    unfold slowAmplitude
    apply (le_div_iff₀ firstOrderGradientConstant_pos).mpr
    have hh := mul_le_mul_of_nonneg_left firstOrderGradientConstant_le_one
      (mul_nonneg hc.tolerance_pos.le hα.le)
    nlinarith only [hh,mul_pos hc.tolerance_pos hα]
  have hm := mul_le_mul_of_nonneg_right hA (Nat.cast_nonneg (α := ℝ) n)
  have hchain : ε*slowAlpha d*n ≤ P.gap/40 := hm.trans hc.chain_budget
  have hp := mul_le_mul_of_nonneg_right hchain (pow_nonneg hα.le 3)
  have he : ε*slowAlpha d*n*slowAlpha d^3 = ε*((n:ℝ)*d) := by
    rw [← slowAlpha_fourth d]
    ring
  rw [he] at hp
  have hnon : 0 ≤ P.gap*slowAlpha d^3 := mul_nonneg P.gap_pos.le (pow_nonneg hα.le 3)
  apply (le_div_iff₀ hc.tolerance_pos).mpr
  change ((n*d:ℕ):ℝ)*ε ≤ P.gap*(d:ℝ)^(3/4:ℝ)
  rw [Nat.cast_mul,← slowAlpha_cube_rpow]
  nlinarith only [hp,hnon]

theorem slow_calibrated_stage_scalars (P : Parameters) {ε : ℝ}
    (hc : SlowCalibratedConditions P ε) (N : ℕ)
    (hN : (N:ℝ) ≤ slowQueryThreshold P ε) :
    0 < (slowBlockSize P ε:ℝ)/256 ∧
    (slowBlockSize P ε:ℝ)/256 ≤ Real.log (1/((N+1:ℕ)*
      (2*Real.exp (-(slowBlockSize P ε:ℝ)/128)))) ∧
    32*((firstOrderResponseCap (slowCoefficientRadius P ε):ℝ)*
      ((slowBlockSize P ε:ℝ)/(slowCoefficientRadius P ε)^2)+Real.log 2) ≤
      (slowBlockSize P ε:ℝ)/256 := by
  have hhor := slow_calibrated_horizon P hc N hN
  have hd := slowBlockSize_pos P hc.tolerance_pos
  have hR : 2 ≤ slowCoefficientRadius P ε := by linarith [hc.radius_large]
  have hi := firstOrderResponseCap_information (slowBlockSize P ε) hR
  rw [firstOrderArrayInformation_eq] at hi
  refine ⟨div_pos (Nat.cast_pos.mpr hd) (by norm_num),?_,?_⟩
  · rw [Real.log_div one_ne_zero (by positivity),Real.log_one]
    have he : Real.log ((N+1:ℕ)*(2*Real.exp (-(slowBlockSize P ε:ℝ)/128))) =
        Real.log (2*(N+1:ℕ))-(slowBlockSize P ε:ℝ)/128 := by
      rw [show (N+1:ℕ)*(2*Real.exp (-(slowBlockSize P ε:ℝ)/128)) =
        (2*(N+1:ℕ))*Real.exp (-(slowBlockSize P ε:ℝ)/128) by ring,
        Real.log_mul (by positivity) (Real.exp_pos _).ne',Real.log_exp]
      ring
    rw [he]
    linarith [hhor.1]
  · nlinarith only [hi,hhor.2.1]

end
end SampleReuse
