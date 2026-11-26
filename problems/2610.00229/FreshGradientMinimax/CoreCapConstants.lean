import FreshGradientMinimax.CoreWeightControl

/-! Numerical constants for the three cap correction blocks. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax

theorem sqrt_dimension_product (n : ℕ) (a b : ℝ) :
    (a * Real.sqrt (n + 1 : ℝ)) * (b * Real.sqrt (n + 1 : ℝ)) = a * b * (n + 1 : ℝ) := by
  calc
    _ = (a * b) * Real.sqrt (n + 1 : ℝ) ^ 2 := by ring
    _ = _ := by rw [Real.sq_sqrt (by positivity : 0 ≤ (n + 1 : ℝ))]

theorem coreCap_correction_uu (n : ℕ) {μ t : ℝ} (hμ : 0 < μ) (ht : 0 < t) :
    (7800 * (μ * t ^ 2) * Real.sqrt (n + 1 : ℝ) / coreCapHeight n μ t) *
      (7800 * (μ * t ^ 2) * Real.sqrt (n + 1 : ℝ)) ≤ 80000 * (μ * t ^ 2) := by
  rw [div_mul_eq_mul_div, sqrt_dimension_product]
  apply (div_le_iff₀ (coreCapHeight_pos n hμ ht)).mpr
  unfold coreCapHeight
  nlinarith only [mul_nonneg (sq_nonneg (μ * t ^ 2)) (show 0 ≤ (n + 1 : ℝ) by positivity)]

theorem coreCap_correction_uy (n : ℕ) {μ t : ℝ} (hμ : 0 < μ) (ht : 0 < t) :
    (7800 * (μ * t ^ 2) * Real.sqrt (n + 1 : ℝ) / coreCapHeight n μ t) *
      (180 * μ * t * Real.sqrt (n + 1 : ℝ)) ≤ 1850 * μ * t := by
  rw [div_mul_eq_mul_div, sqrt_dimension_product]
  apply (div_le_iff₀ (coreCapHeight_pos n hμ ht)).mpr
  unfold coreCapHeight
  nlinarith only [show 0 ≤ μ ^ 2 * t ^ 3 * (n + 1 : ℝ) by positivity]

theorem coreCap_correction_yu (n : ℕ) {μ t : ℝ} (hμ : 0 < μ) (ht : 0 < t) :
    (180 * μ * t * Real.sqrt (n + 1 : ℝ) / coreCapHeight n μ t) *
      (7800 * (μ * t ^ 2) * Real.sqrt (n + 1 : ℝ)) ≤ 1850 * μ * t := by
  have he : (180 * μ * t * Real.sqrt (n + 1 : ℝ) / coreCapHeight n μ t) *
      (7800 * (μ * t ^ 2) * Real.sqrt (n + 1 : ℝ)) =
      (7800 * (μ * t ^ 2) * Real.sqrt (n + 1 : ℝ) / coreCapHeight n μ t) *
        (180 * μ * t * Real.sqrt (n + 1 : ℝ)) := by ring
  rw [he]
  exact coreCap_correction_uy n hμ ht

theorem coreCap_correction_yy (n : ℕ) {μ t : ℝ} (hμ : 0 < μ) (ht : 0 < t) :
    (180 * μ * t * Real.sqrt (n + 1 : ℝ) / coreCapHeight n μ t) *
      (180 * μ * t * Real.sqrt (n + 1 : ℝ)) ≤ 43 * μ := by
  rw [div_mul_eq_mul_div, sqrt_dimension_product]
  apply (div_le_iff₀ (coreCapHeight_pos n hμ ht)).mpr
  unfold coreCapHeight
  nlinarith only [show 0 ≤ μ ^ 2 * t ^ 2 * (n + 1 : ℝ) by positivity]

end FreshGradientMinimax
