import MatchingBounds1005.AnalyticFamily
import MatchingBounds1005.MaskNormEvent

/-! Actual signal weights and physical Gaussian variances in the t³=ε
calibration. These bounds retain all powers used by the source KL estimate. -/
noncomputable section

namespace MatchingBounds1005.EpsilonCalibration
open PathGreen
variable (a L t : ℝ) (ha : 0 < a) (hL : 0 < L) (ht : 0 < t)
  (hhsmall : pathScale a L t ≤ 1 / 4)
local notation "G" => geometry a L t ha hL ht hhsmall

theorem calibrated_cubic_weight :
    |-120 * (G).tau * amplitude a t ^ 3| ≤ (120 * 18 * 8192 * a ^ 2) * t := by
  have hb := calibrated_nonlinear_budget a L t ha hL ht hhsmall
  have hm := mul_le_mul_of_nonneg_right hb (show 0 ≤ t / a by positivity)
  have he : (G).tau * amplitude a t ^ 4 * (t / a) = (G).tau * amplitude a t ^ 3 := by
    unfold amplitude
    field_simp [ha.ne', ht.ne']
    ring
  rw [he] at hm
  have hp : 0 ≤ 120 * (G).tau * amplitude a t ^ 3 := by
    have hτ := (G).tau_nonneg
    have hA := amplitude_pos a t ha ht
    positivity
  rw [show -120 * (G).tau * amplitude a t ^ 3 = -(120 * (G).tau * amplitude a t ^ 3) by ring,
    abs_neg, abs_of_nonneg hp]
  calc
    _ ≤ 120 * ((18 * 8192 * a ^ 3) * (t / a)) := by nlinarith only [hm]
    _ = _ := by field_simp [ha.ne']; ring

theorem calibrated_quartic_weight :
    |120 * (G).tau * amplitude a t ^ 4| ≤ 120 * 18 * 8192 * a ^ 3 := by
  have hτ := (G).tau_nonneg
  rw [abs_of_nonneg (by positivity : 0 ≤ 120 * (G).tau * amplitude a t ^ 4)]
  nlinarith only [calibrated_nonlinear_budget a L t ha hL ht hhsmall]

end MatchingBounds1005.EpsilonCalibration

namespace MatchingBounds1005.TensorGeometry

theorem source_maskSigma_pos {d k : ℕ} (hd : 0 < d) (hk : 1 ≤ k) {δ : ℝ} (hδ : 0 < δ) :
    0 < maskSigma d k δ := by
  unfold maskSigma
  have hc := sourceGaussianConstant_pos hk
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  positivity

theorem source_maskSigma_inv_sq {d k : ℕ} (hd : 0 < d) (hk : 1 ≤ k) {δ : ℝ} (hδ : 0 < δ) :
    1 / maskSigma d k δ ^ 2 = sourceGaussianConstant k ^ 2 * d / δ ^ 2 := by
  have hc := sourceGaussianConstant_pos hk
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hs := Real.sqrt_pos.mpr hd'
  unfold maskSigma
  rw [div_pow, one_div_div, mul_pow, Real.sq_sqrt hd'.le]

theorem source_cubic_sigma_inv_sq {d : ℕ} (hd : 0 < d) {t : ℝ} (ht : 0 < t) :
    1 / maskSigma d 3 ((t ^ 3) ^ 3 / 8) ^ 2 =
      64 * sourceGaussianConstant 3 ^ 2 * d / t ^ 18 := by
  rw [source_maskSigma_inv_sq hd (by norm_num : 1 ≤ 3) (by positivity)]
  field_simp [ht.ne']
  ring

theorem source_quartic_sigma_inv_sq {d : ℕ} (hd : 0 < d) {t : ℝ} (ht : 0 < t) :
    1 / maskSigma d 4 ((t ^ 3) ^ 4 / 8) ^ 2 =
      64 * sourceGaussianConstant 4 ^ 2 * d / t ^ 24 := by
  rw [source_maskSigma_inv_sq hd (by norm_num : 1 ≤ 4) (by positivity)]
  field_simp [ht.ne']
  ring

end MatchingBounds1005.TensorGeometry

namespace MatchingBounds1005.AnalyticFamily
open EpsilonCalibration

def phaseConstant (p : ℕ) : ℝ := amplitudeConstant p / (1440 * 8192)
def cubicWeightConstant (p : ℕ) : ℝ := 120 * 18 * 8192 * amplitudeConstant p ^ 2
def quarticWeightConstant (p : ℕ) : ℝ := 120 * 18 * 8192 * amplitudeConstant p ^ 3

theorem phaseConstant_pos (p : ℕ) : 0 < phaseConstant p := by
  unfold phaseConstant
  exact div_pos (amplitudeConstant_pos p) (by norm_num)

theorem phaseCount_upper (p : ℕ) (t : ℝ) (ht : 0 < t) :
    (phaseCount (amplitudeConstant p) t : ℝ) ≤ phaseConstant p / t ^ 4 :=
  (le_div_iff₀ (pow_pos ht 4)).mpr (phaseCount_power_upper _ _ (amplitudeConstant_pos p) ht)

theorem cubicWeightConstant_pos (p : ℕ) : 0 < cubicWeightConstant p := by
  have ha := amplitudeConstant_pos p
  unfold cubicWeightConstant
  positivity

theorem quarticWeightConstant_pos (p : ℕ) : 0 < quarticWeightConstant p := by
  have ha := amplitudeConstant_pos p
  unfold quarticWeightConstant
  positivity

end MatchingBounds1005.AnalyticFamily
