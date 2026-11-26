import FreshGradientMinimax.SmoothMaximum

/-! Global Lipschitz control of the actual derivative of the smooth maximum,
proved directly across the interfaces without a twice-differentiability premise. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace FreshGradientMinimax

def smoothMaximumCoefficient (η : ℝ) (z : ℝ × ℝ) : ℝ := smoothRampSlope η (z.2 - z.1)

def smoothMaximumDerivative (η : ℝ) (z : ℝ × ℝ) : (ℝ × ℝ) →L[ℝ] ℝ :=
  (1 - smoothMaximumCoefficient η z) • ContinuousLinearMap.fst ℝ ℝ ℝ +
    smoothMaximumCoefficient η z • ContinuousLinearMap.snd ℝ ℝ ℝ

theorem smoothMaximum_coefficient_lipschitz {η : ℝ} (hη : 0 < η) :
    LipschitzWith ⟨2 / η, by positivity⟩ (smoothMaximumCoefficient η) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  have hin : ‖(z.2 - z.1) - (w.2 - w.1)‖ ≤ 2 * ‖z - w‖ := by
    have he : (z.2 - z.1) - (w.2 - w.1) = (z.2 - w.2) - (z.1 - w.1) := by ring
    rw [he]
    have h := norm_sub_le (z.2 - w.2) (z.1 - w.1)
    have h1 := norm_fst_le (z - w)
    have h2 := norm_snd_le (z - w)
    change ‖z.1 - w.1‖ ≤ ‖z - w‖ at h1
    change ‖z.2 - w.2‖ ≤ ‖z - w‖ at h2
    linarith
  have hs := (smoothRampSlope_lipschitz hη).dist_le_mul (z.2 - z.1) (w.2 - w.1)
  simp only [dist_eq_norm, NNReal.coe_mk] at hs ⊢
  change ‖smoothRampSlope η (z.2 - z.1) - smoothRampSlope η (w.2 - w.1)‖ ≤ _
  calc
    _ ≤ (1 / η) * ‖(z.2 - z.1) - (w.2 - w.1)‖ := hs
    _ ≤ (1 / η) * (2 * ‖z - w‖) := mul_le_mul_of_nonneg_left hin (by positivity)
    _ = (2 / η) * ‖z - w‖ := by ring

theorem smoothMaximum_hasFDerivAt {η : ℝ} (hη : 0 < η) (z : ℝ × ℝ) :
    HasFDerivAt (fun w : ℝ × ℝ => smoothMaximum η w.1 w.2) (smoothMaximumDerivative η z) z :=
  smoothMaximum_comp_hasFDerivAt hη hasFDerivAt_fst hasFDerivAt_snd

theorem smoothMaximum_derivative_lipschitz {η : ℝ} (hη : 0 < η) :
    LipschitzWith ⟨4 / η, by positivity⟩ (smoothMaximumDerivative η) := by
  have hn : ‖ContinuousLinearMap.snd ℝ ℝ ℝ - ContinuousLinearMap.fst ℝ ℝ ℝ‖ ≤ (2 : ℝ) := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro z
    change ‖z.2 - z.1‖ ≤ 2 * ‖z‖
    have h := norm_sub_le z.2 z.1
    linarith [norm_fst_le z, norm_snd_le z]
  apply LipschitzWith.of_dist_le_mul
  intro z w
  have he : smoothMaximumDerivative η z - smoothMaximumDerivative η w =
      (smoothMaximumCoefficient η z - smoothMaximumCoefficient η w) •
        (ContinuousLinearMap.snd ℝ ℝ ℝ - ContinuousLinearMap.fst ℝ ℝ ℝ) := by
    apply ContinuousLinearMap.ext
    intro v
    simp only [smoothMaximumDerivative, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  have hc := (smoothMaximum_coefficient_lipschitz hη).dist_le_mul z w
  simp only [dist_eq_norm, NNReal.coe_mk] at hc ⊢
  rw [he]
  calc
    _ ≤ ‖smoothMaximumCoefficient η z - smoothMaximumCoefficient η w‖ *
        ‖ContinuousLinearMap.snd ℝ ℝ ℝ - ContinuousLinearMap.fst ℝ ℝ ℝ‖ := norm_smul_le _ _
    _ ≤ ‖smoothMaximumCoefficient η z - smoothMaximumCoefficient η w‖ * 2 :=
      mul_le_mul_of_nonneg_left hn (norm_nonneg _)
    _ ≤ ((2 / η) * ‖z - w‖) * 2 := mul_le_mul_of_nonneg_right hc (by norm_num)
    _ = (4 / η) * ‖z - w‖ := by ring

theorem smoothMaximum_fderiv_lipschitz {η : ℝ} (hη : 0 < η) :
    LipschitzWith ⟨4 / η, by positivity⟩
      (fderiv ℝ (fun z : ℝ × ℝ => smoothMaximum η z.1 z.2)) := by
  have he : fderiv ℝ (fun z : ℝ × ℝ => smoothMaximum η z.1 z.2) =
      smoothMaximumDerivative η := funext (fun z => (smoothMaximum_hasFDerivAt hη z).fderiv)
  rw [he]
  exact smoothMaximum_derivative_lipschitz hη

end FreshGradientMinimax

