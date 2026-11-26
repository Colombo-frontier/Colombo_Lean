import FreshGradientMinimax.MaskedCore

/-! The original global constants in C.2, simultaneously for all bounded
seed and link masks. Bounds are on actual first derivatives and their global
differences, so the cap interfaces are included. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax

theorem sub_fields_norm_le {E : Type*} [NormedAddCommGroup E] (a b c d : E) :
    ‖(a - b) - (c - d)‖ ≤ ‖a - c‖ + ‖b - d‖ := by
  rw [show (a - b) - (c - d) = (a - c) - (b - d) by abel]
  exact norm_sub_le _ _

theorem maskedCoreGradU_norm {n dy : ℕ} (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy)
    {μ t : ℝ} (hμ : 0 < μ) (ht : 0 < t) (w : Euclid n) (hw : ∀ e, |w e| ≤ 1)
    (mask : Fin (n + n) → ℝ) (hm : ∀ i, |mask i| ≤ 1) (u : Euclid (n + 1)) (y : Euclid dy) :
    ‖maskedCoreGradU V μ t w mask u y‖ ≤ 8000 * (μ * t ^ 2) * Real.sqrt (n + 1 : ℝ) := by
  have hs := mul_le_mul_of_nonneg_left (weightedCoreSeedGradient_norm w hw u)
    (by positivity : 0 ≤ μ * t ^ 2)
  have hcap := coreProtectedCapGradU_norm V hμ ht mask hm u y
  have h := norm_sub_le ((μ * t ^ 2) • weightedCoreSeedGradient w u) (coreProtectedCapGradU V μ t mask u y)
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ μ * t ^ 2)] at h
  unfold maskedCoreGradU
  nlinarith only [h, hs, hcap, show 0 ≤ μ * t ^ 2 * Real.sqrt (n + 1 : ℝ) by positivity]

theorem maskedCoreGradU_sub_u {n dy : ℕ} (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy)
    {μ t : ℝ} (hμ : 0 < μ) (ht : 0 < t) (w : Euclid n) (hw : ∀ e, |w e| ≤ 1)
    (mask : Fin (n + n) → ℝ) (hm : ∀ i, |mask i| ≤ 1) (u v : Euclid (n + 1)) (y : Euclid dy) :
    ‖maskedCoreGradU V μ t w mask u y - maskedCoreGradU V μ t w mask v y‖ ≤
      10 ^ 6 * (μ * t ^ 2) * ‖u - v‖ := by
  have hs := mul_le_mul_of_nonneg_left (weightedCoreSeedGradient_sub_norm w hw u v)
    (by positivity : 0 ≤ μ * t ^ 2)
  have hcap := coreProtectedCapGradU_sub_u V hμ ht mask hm u v y
  have h := sub_fields_norm_le ((μ * t ^ 2) • weightedCoreSeedGradient w u) (coreProtectedCapGradU V μ t mask u y)
    ((μ * t ^ 2) • weightedCoreSeedGradient w v) (coreProtectedCapGradU V μ t mask v y)
  rw [nonnegative_smul_difference (by positivity : 0 ≤ μ * t ^ 2)] at h
  unfold maskedCoreGradU
  nlinarith only [h, hs, hcap, show 0 ≤ μ * t ^ 2 * ‖u - v‖ by positivity]

theorem maskedCoreGradU_sub_y {n dy : ℕ} (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy)
    {μ t : ℝ} (hμ : 0 < μ) (ht : 0 < t) (w : Euclid n)
    (mask : Fin (n + n) → ℝ) (hm : ∀ i, |mask i| ≤ 1) (u : Euclid (n + 1)) (y z : Euclid dy) :
    ‖maskedCoreGradU V μ t w mask u y - maskedCoreGradU V μ t w mask u z‖ ≤
      2000 * μ * t * ‖y - z‖ := by
  rw [maskedCoreGradU, maskedCoreGradU, sub_sub_sub_cancel_left, norm_sub_rev]
  have h := coreProtectedCapGradU_sub_y V hμ ht mask hm u y z
  nlinarith only [h, show 0 ≤ μ * t * ‖y - z‖ by positivity]

theorem maskedCoreGradY_sub_u {n dy : ℕ} (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy)
    {μ t : ℝ} (hμ : 0 < μ) (ht : 0 < t)
    (mask : Fin (n + n) → ℝ) (hm : ∀ i, |mask i| ≤ 1) (u v : Euclid (n + 1)) (y : Euclid dy) :
    ‖maskedCoreGradY V μ t mask u y - maskedCoreGradY V μ t mask v y‖ ≤
      2000 * μ * t * ‖u - v‖ := by
  rw [maskedCoreGradY, maskedCoreGradY, sub_sub_sub_cancel_left, norm_sub_rev]
  have h := coreProtectedCapGradY_sub_u V hμ ht mask hm u v y
  nlinarith only [h, show 0 ≤ μ * t * ‖u - v‖ by positivity]

theorem maskedCoreGradY_sub_y {n dy : ℕ} (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy)
    {μ t : ℝ} (hμ : 0 < μ) (ht : 0 < t)
    (mask : Fin (n + n) → ℝ) (hm : ∀ i, |mask i| ≤ 1) (u : Euclid (n + 1)) (y z : Euclid dy) :
    ‖maskedCoreGradY V μ t mask u y - maskedCoreGradY V μ t mask u z‖ ≤
      50 * μ * ‖y - z‖ := by
  have hcap := coreProtectedCapGradY_sub_y V hμ ht mask hm u y z
  have h := sub_fields_norm_le (-μ • y) (coreProtectedCapGradY V μ t mask u y)
    (-μ • z) (coreProtectedCapGradY V μ t mask u z)
  rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos hμ] at h
  unfold maskedCoreGradY
  nlinarith only [h, hcap, mul_nonneg hμ.le (norm_nonneg (y - z))]

end FreshGradientMinimax
