import FreshGradientMinimax.CoreInteractionBounds
import FreshGradientMinimax.CoreMaximization

/-! Dimension-uniform interaction constants at the parameters of C.2. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax

theorem double_dimension_sqrt_le (n : ℕ) :
    Real.sqrt (n + n : ℝ) ≤ (17 / 12 : ℝ) * Real.sqrt (n + 1 : ℝ) := by
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
  have h1 := Real.sq_sqrt (show 0 ≤ (n + n : ℝ) by positivity)
  have h2 := Real.sq_sqrt (show 0 ≤ (n + 1 : ℝ) by positivity)
  nlinarith only [h1, h2, Nat.cast_nonneg (α := ℝ) n]

theorem scaledInteractionGradU_norm {n dy : ℕ} (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy)
    {μ t : ℝ} (hμ : 0 < μ) (ht : 0 < t) (mask : Fin (n + n) → ℝ)
    (hm : ∀ i, |mask i| ≤ 1) (u : Euclid (n + 1)) (y : Euclid dy) :
    ‖coreInteractionGradU V (2 * μ * t) (32 * t) mask u y‖ ≤
      7800 * (μ * t ^ 2) * Real.sqrt (n + 1 : ℝ) := by
  have h := coreInteractionGradU_norm V (by positivity : 0 ≤ 2 * μ * t)
    (by positivity : 0 < 32 * t) mask hm u y
  have hs := mul_le_mul_of_nonneg_left (double_dimension_sqrt_le n)
    (by positivity : 0 ≤ 5472 * μ * t ^ 2)
  have hn : 0 ≤ μ * t ^ 2 * Real.sqrt (n + 1 : ℝ) := by positivity
  nlinarith only [h, hs, hn]

theorem scaledInteractionGradY_norm {n dy : ℕ} (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy)
    {μ t : ℝ} (hμ : 0 < μ) (ht : 0 < t) (mask : Fin (n + n) → ℝ)
    (hm : ∀ i, |mask i| ≤ 1) (u : Euclid (n + 1)) (y : Euclid dy) :
    ‖coreInteractionGradY V (2 * μ * t) (32 * t) mask u y‖ ≤
      12 * μ * t * Real.sqrt (n + 1 : ℝ) := by
  have hc := euclid_norm_le_of_coordinate_bound (coreLinks u) (by norm_num : (0 : ℝ) ≤ 4)
    (coreLinks_coordinate_bound u)
  have h := (coreInteractionGradY_norm V (by positivity : 0 ≤ 2 * μ * t) (32 * t) mask hm u y).trans
    (mul_le_mul_of_nonneg_left hc (by positivity : 0 ≤ 2 * μ * t))
  push_cast at h
  have hs := mul_le_mul_of_nonneg_left (double_dimension_sqrt_le n) (by positivity : 0 ≤ 8 * μ * t)
  have hn : 0 ≤ μ * t * Real.sqrt (n + 1 : ℝ) := by positivity
  nlinarith only [h, hs, hn]

theorem scaledInteractionGradU_sub_u {n dy : ℕ} (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy)
    {μ t : ℝ} (hμ : 0 < μ) (ht : 0 < t) (mask : Fin (n + n) → ℝ)
    (hm : ∀ i, |mask i| ≤ 1) (u v : Euclid (n + 1)) (y : Euclid dy) :
    ‖coreInteractionGradU V (2 * μ * t) (32 * t) mask u y -
      coreInteractionGradU V (2 * μ * t) (32 * t) mask v y‖ ≤ 768000 * (μ * t ^ 2) * ‖u - v‖ := by
  convert coreInteractionGradU_sub_u V (by positivity : 0 ≤ 2 * μ * t)
    (by positivity : 0 < 32 * t) mask hm u v y using 1
  ring

theorem scaledInteractionGradU_sub_y {n dy : ℕ} (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy)
    {μ t : ℝ} (hμ : 0 < μ) (ht : 0 < t) (mask : Fin (n + n) → ℝ)
    (hm : ∀ i, |mask i| ≤ 1) (u : Euclid (n + 1)) (y z : Euclid dy) :
    ‖coreInteractionGradU V (2 * μ * t) (32 * t) mask u y -
      coreInteractionGradU V (2 * μ * t) (32 * t) mask u z‖ ≤ (114 * μ * t) * ‖y - z‖ := by
  convert coreInteractionGradU_sub_y V (by positivity : 0 ≤ 2 * μ * t)
    (by positivity : 0 < 32 * t) mask hm u y z using 1
  ring

theorem scaledInteractionGradY_sub_u {n dy : ℕ} (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy)
    {μ t : ℝ} (hμ : 0 < μ) (ht : 0 < t) (mask : Fin (n + n) → ℝ)
    (hm : ∀ i, |mask i| ≤ 1) (u v : Euclid (n + 1)) (y : Euclid dy) :
    ‖coreInteractionGradY V (2 * μ * t) (32 * t) mask u y -
      coreInteractionGradY V (2 * μ * t) (32 * t) mask v y‖ ≤ (114 * μ * t) * ‖u - v‖ := by
  convert coreInteractionGradY_sub_u V (by positivity : 0 ≤ 2 * μ * t)
    (32 * t) mask hm u v y using 1
  ring

theorem scaledInteractionGradY_sub_y {n dy : ℕ} (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy)
    {μ t : ℝ} (hμ : 0 < μ) (ht : 0 < t) (mask : Fin (n + n) → ℝ)
    (hm : ∀ i, |mask i| ≤ 1) (u : Euclid (n + 1)) (y z : Euclid dy) :
    ‖coreInteractionGradY V (2 * μ * t) (32 * t) mask u y -
      coreInteractionGradY V (2 * μ * t) (32 * t) mask u z‖ ≤ (3 * μ / 8) * ‖y - z‖ := by
  have he : 6 * (2 * μ * t) / (32 * t) = 3 * μ / 8 := by field_simp; ring
  simpa only [he] using coreInteractionGradY_sub_y V (by positivity : 0 ≤ 2 * μ * t)
    (by positivity : 0 < 32 * t) mask hm u y z

end FreshGradientMinimax
