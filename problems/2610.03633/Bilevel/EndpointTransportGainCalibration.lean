import Bilevel.EndpointTransportNormalization
import Bilevel.ChiUniformWidthCalibration

/-! Exact transfer of the existing width calibration to the actual
transport gain. Kappa and the condition theta <= kappa^2 are kept unchanged;
only the accuracy parameter in the numerical certificate is rescaled. -/
noncomputable section
namespace Bilevel.EndpointTransportNormalization
open ChiIndependentWidths

def calibrationAccuracy (κ ε : ℝ) : ℝ := ((κ/6)/gain κ)*ε

theorem calibration_factor_bounds {κ : ℝ} (hκ : 3200≤κ) :
    8≤(κ/6)/gain κ ∧ (κ/6)/gain κ≤32 := by
  have hg := gain_pos hκ
  have hb := gain_bounds hκ
  constructor
  · apply (le_div_iff₀ hg).mpr
    linarith only [hb.2]
  · apply (div_le_iff₀ hg).mpr
    linarith only [hb.1]

theorem calibrationAccuracy_bounds {κ ε : ℝ} (hκ : 3200≤κ) (hε : 0≤ε) :
    8*ε≤calibrationAccuracy κ ε ∧ calibrationAccuracy κ ε≤32*ε := by
  exact ⟨mul_le_mul_of_nonneg_right (calibration_factor_bounds hκ).1 hε,
    mul_le_mul_of_nonneg_right (calibration_factor_bounds hκ).2 hε⟩

theorem calibrationAccuracy_pos {κ ε : ℝ} (hκ : 3200≤κ) (hε : 0<ε) :
    0<calibrationAccuracy κ ε :=
  (mul_pos (by norm_num : (0:ℝ)<8) hε).trans_le (calibrationAccuracy_bounds hκ hε.le).1

theorem calibration_middleWidth {κ : ℝ} (hκ : 3200≤κ) (Cb ε L₀ ω : ℝ) (J : ℕ) :
    middleWidth Cb (calibrationAccuracy κ ε) (κ/6) L₀ ω J=
      middleWidth Cb ε (gain κ) L₀ ω J := by
  have hk : κ≠0 := ne_of_gt (by linarith : 0<κ)
  have hg := (gain_pos hκ).ne'
  by_cases hL : L₀=0
  · simp only [middleWidth,hL,mul_zero,zero_mul,div_zero]
  by_cases hw : ω^J=0
  · simp only [middleWidth,hw,mul_zero,div_zero]
  unfold middleWidth calibrationAccuracy
  field_simp [hk,hg,hL,hw]
  ring

theorem calibration_accuracy_window {κ ε c L Δ : ℝ} (hκ : 3200≤κ) (hε : 0≤ε)
    (hacc : ε≤(c/32)*min L (Real.sqrt (L*Δ))) :
    calibrationAccuracy κ ε≤c*min L (Real.sqrt (L*Δ)) := by
  have h := mul_le_mul_of_nonneg_left hacc (by norm_num : (0:ℝ)≤32)
  have hb := (calibrationAccuracy_bounds hκ hε).2
  nlinarith only [h,hb]

theorem calibration_gradient_scale {κ : ℝ} (hκ : 3200≤κ) (ε : ℝ) :
    (gain κ/(κ/6))*calibrationAccuracy κ ε=ε := by
  have hk : κ≠0 := ne_of_gt (by linarith : 0<κ)
  have hg := (gain_pos hκ).ne'
  unfold calibrationAccuracy
  field_simp
  ring

end Bilevel.EndpointTransportNormalization
