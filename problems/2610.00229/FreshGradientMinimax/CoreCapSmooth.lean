import FreshGradientMinimax.CoreCapConstants
import FreshGradientMinimax.BlendDifference

/-! Global Lipschitz bounds for the true partial gradients of every masked cap. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open scoped InnerProductSpace

theorem coreProtectedCapGradU_norm {n dy : ℕ} (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy)
    {μ t : ℝ} (hμ : 0 < μ) (ht : 0 < t) (mask : Fin (n + n) → ℝ)
    (hm : ∀ i, |mask i| ≤ 1) (u : Euclid (n + 1)) (y : Euclid dy) :
    ‖coreProtectedCapGradU V μ t mask u y‖ ≤ 7800 * (μ * t ^ 2) * Real.sqrt (n + 1 : ℝ) := by
  have hb := coreProtectedWeight_bounds V hμ ht mask u y
  unfold coreProtectedCapGradU
  rw [norm_smul, norm_neg, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hb.2)]
  exact (mul_le_of_le_one_left (norm_nonneg _) (by linarith only [hb.1])).trans
    (scaledInteractionGradU_norm V hμ ht mask hm u y)

theorem coreProtectedCapGradU_sub_u {n dy : ℕ} (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy)
    {μ t : ℝ} (hμ : 0 < μ) (ht : 0 < t) (mask : Fin (n + n) → ℝ)
    (hm : ∀ i, |mask i| ≤ 1) (u v : Euclid (n + 1)) (y : Euclid dy) :
    ‖coreProtectedCapGradU V μ t mask u y - coreProtectedCapGradU V μ t mask v y‖ ≤
      848000 * (μ * t ^ 2) * ‖u - v‖ := by
  have hn : ‖-coreInteractionGradU V (2 * μ * t) (32 * t) mask u y‖ ≤
      7800 * (μ * t ^ 2) * Real.sqrt (n + 1 : ℝ) := by
    simpa only [norm_neg] using scaledInteractionGradU_norm V hμ ht mask hm u y
  have hd : ‖-coreInteractionGradU V (2 * μ * t) (32 * t) mask u y -
      -coreInteractionGradU V (2 * μ * t) (32 * t) mask v y‖ ≤ 768000 * (μ * t ^ 2) * ‖u - v‖ := by
    simpa only [neg_sub_neg, norm_sub_rev] using scaledInteractionGradU_sub_u V hμ ht mask hm u v y
  have h := weighted_vector_difference_bound _ _ _ _ (coreProtectedWeight_bounds V hμ ht mask v y)
    (norm_nonneg (u - v)) hn hd (coreProtectedWeight_sub_u V hμ ht mask hm u v y)
    (coreCap_correction_uu n hμ ht)
  unfold coreProtectedCapGradU
  convert h using 1
  ring

theorem coreProtectedCapGradU_sub_y {n dy : ℕ} (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy)
    {μ t : ℝ} (hμ : 0 < μ) (ht : 0 < t) (mask : Fin (n + n) → ℝ)
    (hm : ∀ i, |mask i| ≤ 1) (u : Euclid (n + 1)) (y z : Euclid dy) :
    ‖coreProtectedCapGradU V μ t mask u y - coreProtectedCapGradU V μ t mask u z‖ ≤
      1964 * μ * t * ‖y - z‖ := by
  have hn : ‖-coreInteractionGradU V (2 * μ * t) (32 * t) mask u y‖ ≤
      7800 * (μ * t ^ 2) * Real.sqrt (n + 1 : ℝ) := by
    simpa only [norm_neg] using scaledInteractionGradU_norm V hμ ht mask hm u y
  have hd : ‖-coreInteractionGradU V (2 * μ * t) (32 * t) mask u y -
      -coreInteractionGradU V (2 * μ * t) (32 * t) mask u z‖ ≤ 114 * μ * t * ‖y - z‖ := by
    simpa only [neg_sub_neg, norm_sub_rev] using scaledInteractionGradU_sub_y V hμ ht mask hm u y z
  have h := weighted_vector_difference_bound _ _ _ _ (coreProtectedWeight_bounds V hμ ht mask u z)
    (norm_nonneg (y - z)) hn hd (coreProtectedWeight_sub_y V hμ ht mask hm u y z)
    (coreCap_correction_yu n hμ ht)
  unfold coreProtectedCapGradU
  convert h using 1
  ring

theorem coreProtectedCapGradY_gap_form {n dy : ℕ} (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy)
    (μ t : ℝ) (mask : Fin (n + n) → ℝ) (u : Euclid (n + 1)) (y : Euclid dy) :
    coreProtectedCapGradY V μ t mask u y =
      (4 * μ) • y - (1 - coreProtectedWeight V μ t mask u y) • coreGapGradY V μ t mask u y := by
  unfold coreProtectedCapGradY coreProtectedQGradY coreGapGradY
  module

theorem coreProtectedCapGradY_outside {n dy : ℕ} (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy)
    {μ t : ℝ} (hμ : 0 < μ) (ht : 0 < t) (mask : Fin (n + n) → ℝ)
    (hm : ∀ i, |mask i| ≤ 1) (u : Euclid (n + 1)) (y : Euclid dy)
    (hy : coreControlRadius n t ≤ ‖y‖) : coreProtectedCapGradY V μ t mask u y = (4 * μ) • y := by
  simp only [coreProtectedCapGradY, coreProtectedWeight_outside V hμ ht mask hm u y hy,
    sub_self, zero_smul, one_smul, zero_add]

theorem coreProtectedCapGradY_sub_u {n dy : ℕ} (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy)
    {μ t : ℝ} (hμ : 0 < μ) (ht : 0 < t) (mask : Fin (n + n) → ℝ)
    (hm : ∀ i, |mask i| ≤ 1) (u v : Euclid (n + 1)) (y : Euclid dy) :
    ‖coreProtectedCapGradY V μ t mask u y - coreProtectedCapGradY V μ t mask v y‖ ≤
      1964 * μ * t * ‖u - v‖ := by
  by_cases hy : coreControlRadius n t ≤ ‖y‖
  · rw [coreProtectedCapGradY_outside V hμ ht mask hm u y hy,
      coreProtectedCapGradY_outside V hμ ht mask hm v y hy, sub_self, norm_zero]
    positivity
  · have hn := coreGapGradY_norm_on_ball V hμ ht mask hm u y (le_of_not_ge hy)
    have hd : ‖coreGapGradY V μ t mask u y - coreGapGradY V μ t mask v y‖ ≤ 114 * μ * t * ‖u - v‖ := by
      simpa only [coreGapGradY, add_sub_add_left_eq_sub] using scaledInteractionGradY_sub_u V hμ ht mask hm u v y
    have h := weighted_vector_difference_bound _ _ _ _ (coreProtectedWeight_bounds V hμ ht mask v y)
      (norm_nonneg (u - v)) hn hd (coreProtectedWeight_sub_u V hμ ht mask hm u v y)
      (coreCap_correction_uy n hμ ht)
    rw [coreProtectedCapGradY_gap_form, coreProtectedCapGradY_gap_form, sub_sub_sub_cancel_left, norm_sub_rev]
    convert h using 1
    ring

theorem coreProtectedQGradY_sub_y {n dy : ℕ} (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy)
    {μ t : ℝ} (hμ : 0 < μ) (ht : 0 < t) (mask : Fin (n + n) → ℝ)
    (hm : ∀ i, |mask i| ≤ 1) (u : Euclid (n + 1)) (y z : Euclid dy) :
    ‖coreProtectedQGradY V μ t mask u y - coreProtectedQGradY V μ t mask u z‖ ≤ 4 * μ * ‖y - z‖ := by
  have he : coreProtectedQGradY V μ t mask u y - coreProtectedQGradY V μ t mask u z =
      (μ • y - μ • z) - (coreInteractionGradY V (2 * μ * t) (32 * t) mask u y -
        coreInteractionGradY V (2 * μ * t) (32 * t) mask u z) := by unfold coreProtectedQGradY; abel
  rw [he]
  have h := norm_sub_le (μ • y - μ • z)
    (coreInteractionGradY V (2 * μ * t) (32 * t) mask u y - coreInteractionGradY V (2 * μ * t) (32 * t) mask u z)
  rw [nonnegative_smul_difference hμ.le] at h
  have hΓ := scaledInteractionGradY_sub_y V hμ ht mask hm u y z
  nlinarith only [h, hΓ, mul_nonneg hμ.le (norm_nonneg (y - z))]

theorem coreProtectedCapGradY_sub_y_from_ball {n dy : ℕ} (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy)
    {μ t : ℝ} (hμ : 0 < μ) (ht : 0 < t) (mask : Fin (n + n) → ℝ)
    (hm : ∀ i, |mask i| ≤ 1) (u : Euclid (n + 1)) (y z : Euclid dy)
    (hy : ‖y‖ ≤ coreControlRadius n t) :
    ‖coreProtectedCapGradY V μ t mask u y - coreProtectedCapGradY V μ t mask u z‖ ≤
      47 * μ * ‖y - z‖ := by
  have he : (4 * μ) • y - coreProtectedQGradY V μ t mask u y = coreGapGradY V μ t mask u y := by
    unfold coreProtectedQGradY coreGapGradY
    module
  have hg : ‖(4 * μ) • y - coreProtectedQGradY V μ t mask u y‖ ≤
      180 * μ * t * Real.sqrt (n + 1 : ℝ) := by
    rw [he]
    exact coreGapGradY_norm_on_ball V hμ ht mask hm u y hy
  have hw : ‖(4 * μ) • y - (4 * μ) • z‖ ≤ 4 * μ * ‖y - z‖ :=
    (nonnegative_smul_difference (by positivity : 0 ≤ 4 * μ) y z).le
  have h := convex_blend_difference_bound _ _ _ _ _ _ (coreProtectedWeight_bounds V hμ ht mask u z)
    (norm_nonneg (y - z)) (coreProtectedQGradY_sub_y V hμ ht mask hm u y z) hw hg
    (coreProtectedWeight_sub_y V hμ ht mask hm u y z) (coreCap_correction_yy n hμ ht)
  unfold coreProtectedCapGradY
  convert h using 1
  ring

theorem coreProtectedCapGradY_sub_y {n dy : ℕ} (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy)
    {μ t : ℝ} (hμ : 0 < μ) (ht : 0 < t) (mask : Fin (n + n) → ℝ)
    (hm : ∀ i, |mask i| ≤ 1) (u : Euclid (n + 1)) (y z : Euclid dy) :
    ‖coreProtectedCapGradY V μ t mask u y - coreProtectedCapGradY V μ t mask u z‖ ≤
      47 * μ * ‖y - z‖ := by
  by_cases hy : coreControlRadius n t ≤ ‖y‖
  · by_cases hz : coreControlRadius n t ≤ ‖z‖
    · rw [coreProtectedCapGradY_outside V hμ ht mask hm u y hy,
        coreProtectedCapGradY_outside V hμ ht mask hm u z hz,
        nonnegative_smul_difference (by positivity : 0 ≤ 4 * μ)]
      nlinarith only [mul_nonneg hμ.le (norm_nonneg (y - z))]
    · simpa only [norm_sub_rev] using coreProtectedCapGradY_sub_y_from_ball V hμ ht mask hm u z y
        (le_of_not_ge hz)
  · exact coreProtectedCapGradY_sub_y_from_ball V hμ ht mask hm u y z (le_of_not_ge hy)

end FreshGradientMinimax
