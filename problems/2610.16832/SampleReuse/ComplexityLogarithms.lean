import SampleReuse.ComplexityRates
import SampleReuse.SlowCalibratedRates

open SecondOrder

namespace SampleReuse
noncomputable section

def slowLogConstant (P : Parameters) : ℝ :=
  16384*Real.log (firstOrderEndpointEnvelopeConstant P.gap (slowModelScale P))+49153

theorem slowEnvelopeConstant_ge_one (P : Parameters) :
    1 ≤ firstOrderEndpointEnvelopeConstant P.gap (slowModelScale P) := by
  unfold firstOrderEndpointEnvelopeConstant
  have := mul_nonneg P.gap_pos.le (sq_nonneg (slowModelScale P))
  linarith [P.gap_pos]

theorem slowLogConstant_ge_one (P : Parameters) : 1 ≤ slowLogConstant P := by
  have := Real.log_nonneg (slowEnvelopeConstant_ge_one P)
  unfold slowLogConstant
  linarith

theorem tolerance_log_nonneg {ε : ℝ} (hε : 0 < ε) (he : ε ≤ 1) :
    0 ≤ Real.log (1/ε) :=
  Real.log_nonneg ((le_div_iff₀ hε).mpr (by simpa using he))

/-- The exact rounded block size is at most a parameter-only constant times
one logarithm of the inverse tolerance. -/
theorem slowBlockSize_log_bound (P : Parameters) {ε : ℝ} (hε : 0 < ε) (he : ε ≤ 1) :
    (slowBlockSize P ε:ℝ) ≤ slowLogConstant P*(1+Real.log (1/ε)) := by
  have hh := firstOrderEndpointBlockSize_log_bound (s := slowModelScale P) P.gap_pos.le hε he
  have hL := tolerance_log_nonneg hε he
  have hC := Real.log_nonneg (slowEnvelopeConstant_ge_one P)
  have hm := mul_nonneg (by linarith :
      0 ≤ 16384*Real.log (firstOrderEndpointEnvelopeConstant P.gap (slowModelScale P))+1) hL
  rw [one_div,Real.log_inv] at hL hm ⊢
  unfold slowBlockSize slowLogConstant
  nlinarith

theorem slowAlpha_log_bound (P : Parameters) {ε : ℝ} (hε : 0 < ε) (he : ε ≤ 1) :
    slowAlpha (slowBlockSize P ε) ≤ slowLogConstant P*(1+Real.log (1/ε)) :=
  (slowAlpha_le_dimension (slowBlockSize_pos P hε)).trans (slowBlockSize_log_bound P hε he)

def sourceLowerEnvelope (P : Parameters) (ε γ : ℝ) : ℝ :=
  max (P.gap*slowModelScale P^2/(ε^3*slowAlpha (slowBlockSize P ε))) (1/γ^3)

theorem max_scaled_sum_lower {a b c d t : ℝ} (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hd : 0 < d) (ht : 1 ≤ t) (hdt : d ≤ t) :
    min a 1*(b+c)/(2*t) ≤ max (a*b/d) c := by
  let M := max (a*b/d) c
  have hM : 0 ≤ M := hc.trans (le_max_right _ _)
  have haM : a*b ≤ M*d := (div_le_iff₀ hd).mp (le_max_left _ _)
  have hdM := mul_le_mul_of_nonneg_left hdt hM
  have hab := mul_le_mul_of_nonneg_right (min_le_left a 1) hb
  have htc := mul_le_mul_of_nonneg_right ((min_le_right a 1).trans ht) hc
  have hcM := mul_le_mul_of_nonneg_left (le_max_right (a*b/d) c) (by linarith : 0 ≤ t)
  apply (div_le_iff₀ (by linarith : 0 < 2*t)).mpr
  change min a 1*(b+c) ≤ M*(2*t)
  nlinarith

/-- The exact lower envelope dominates the sum of the inverse cubes divided
by one logarithmic factor. Its positive coefficient depends only on P. -/
theorem sourceLowerEnvelope_log_rate (P : Parameters) {ε γ : ℝ}
    (hε : 0 < ε) (he : ε ≤ 1) (hγ : 0 < γ) :
    min (P.gap*slowModelScale P^2) 1*(1/ε^3+1/γ^3)/
      (2*slowLogConstant P*(1+Real.log (1/ε))) ≤ sourceLowerEnvelope P ε γ := by
  have hL := tolerance_log_nonneg hε he
  have hC := slowLogConstant_ge_one P
  have ht : 1 ≤ slowLogConstant P*(1+Real.log (1/ε)) := by nlinarith
  have hh := max_scaled_sum_lower (a := P.gap*slowModelScale P^2)
    (b := 1/ε^3) (c := 1/γ^3) (d := slowAlpha (slowBlockSize P ε))
    (t := slowLogConstant P*(1+Real.log (1/ε))) (by positivity) (by positivity)
    (slowAlpha_pos (slowBlockSize_pos P hε)) ht (slowAlpha_log_bound P hε he)
  simpa only [sourceLowerEnvelope,div_eq_mul_inv,mul_inv_rev,one_mul,mul_assoc,mul_left_comm,mul_comm] using hh

theorem sourceLowerEnvelope_log_coefficient_pos (P : Parameters) :
    0 < min (P.gap*slowModelScale P^2) 1/(2*slowLogConstant P) := by
  have hs := slowModelScale_pos P
  have hC := slowLogConstant_ge_one P
  exact div_pos (lt_min (mul_pos P.gap_pos (sq_pos_of_pos hs)) (by norm_num)) (by linarith)

end
end SampleReuse
