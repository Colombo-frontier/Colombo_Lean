import FreshGradientMinimax.CoreStrongConcavity
import FreshGradientMinimax.BallLipschitz

/-! Global variation of the cap's blending coefficient. The auxiliary radius
56*t*sqrt(T) is slightly larger than the exact protection radius. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open scoped InnerProductSpace

def coreControlRadius (n : ℕ) (t : ℝ) : ℝ := 56 * t * Real.sqrt (n + 1 : ℝ)

def coreGapGradY {n dy : ℕ} (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy) (μ t : ℝ)
    (mask : Fin (n + n) → ℝ) (u : Euclid (n + 1)) (y : Euclid dy) : Euclid dy :=
  (3 * μ) • y + coreInteractionGradY V (2 * μ * t) (32 * t) mask u y

theorem coreControlRadius_sq (n : ℕ) (t : ℝ) :
    coreControlRadius n t ^ 2 = 3136 * t ^ 2 * (n + 1 : ℝ) := by
  unfold coreControlRadius
  rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity : 0 ≤ (n + 1 : ℝ))]
  ring

theorem coreProtectedWeight_outside {n dy : ℕ} (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy)
    {μ t : ℝ} (hμ : 0 < μ) (ht : 0 < t) (mask : Fin (n + n) → ℝ)
    (hm : ∀ i, |mask i| ≤ 1) (u : Euclid (n + 1)) (y : Euclid dy)
    (hy : coreControlRadius n t ≤ ‖y‖) : coreProtectedWeight V μ t mask u y = 1 := by
  have hs := pow_le_pow_left₀ (by unfold coreControlRadius; positivity : 0 ≤ coreControlRadius n t) hy 2
  rw [coreControlRadius_sq] at hs
  have hμs := mul_le_mul_of_nonneg_left hs hμ.le
  have hΓ := (abs_le.mp (coreInteraction_height_bound V hμ ht mask hm u y)).1
  have hgap : coreCapHeight n μ t ≤ coreProtectedWall n μ t y - coreProtectedQ V μ t mask u y := by
    unfold coreProtectedWall coreProtectedQ coreCapHeight at *
    nlinarith only [hμs, hΓ, mul_nonneg (mul_nonneg hμ.le (sq_nonneg t))
      (show 0 ≤ (n + 1 : ℝ) by positivity)]
  unfold coreProtectedWeight
  rw [smoothRampSlope_clamp (coreCapHeight_pos n hμ ht)]
  exact min_eq_left (((one_le_div (coreCapHeight_pos n hμ ht)).mpr hgap).trans (le_max_right _ _))

theorem coreGap_hasFDerivAt_y {n dy : ℕ} (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy)
    (μ : ℝ) {t : ℝ} (ht : 0 < t) (mask : Fin (n + n) → ℝ)
    (u : Euclid (n + 1)) (y : Euclid dy) :
    HasFDerivAt (fun z => coreProtectedWall n μ t z - coreProtectedQ V μ t mask u z)
      (innerSL ℝ (coreGapGradY V μ t mask u y)) y := by
  have h := (coreProtectedWall_hasFDerivAt n μ t y).sub (coreProtectedQ_hasFDerivAt_y V μ ht mask u y)
  have he : (4 * μ) • y - coreProtectedQGradY V μ t mask u y = coreGapGradY V μ t mask u y := by
    unfold coreProtectedQGradY coreGapGradY
    module
  simpa only [← map_sub, he] using h

theorem coreGapGradY_norm_on_ball {n dy : ℕ} (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy)
    {μ t : ℝ} (hμ : 0 < μ) (ht : 0 < t) (mask : Fin (n + n) → ℝ)
    (hm : ∀ i, |mask i| ≤ 1) (u : Euclid (n + 1)) (y : Euclid dy)
    (hy : ‖y‖ ≤ coreControlRadius n t) :
    ‖coreGapGradY V μ t mask u y‖ ≤ 180 * μ * t * Real.sqrt (n + 1 : ℝ) := by
  have h := norm_add_le ((3 * μ) • y) (coreInteractionGradY V (2 * μ * t) (32 * t) mask u y)
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 3 * μ)] at h
  have hr := mul_le_mul_of_nonneg_left hy (by positivity : 0 ≤ 3 * μ)
  have hΓ := scaledInteractionGradY_norm V hμ ht mask hm u y
  unfold coreGapGradY coreControlRadius at *
  nlinarith only [h, hr, hΓ]

theorem smoothRampSlope_comp_bound {H C δ a b : ℝ} (hH : 0 < H)
    (h : |a - b| ≤ C * δ) : |smoothRampSlope H a - smoothRampSlope H b| ≤ (C / H) * δ := by
  have hw := (smoothRampSlope_lipschitz hH).dist_le_mul a b
  simp only [Real.dist_eq, NNReal.coe_mk] at hw
  calc
    _ ≤ (1 / H) * |a - b| := hw
    _ ≤ (1 / H) * (C * δ) := mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by ring

theorem coreProtectedWeight_sub_u {n dy : ℕ} (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy)
    {μ t : ℝ} (hμ : 0 < μ) (ht : 0 < t) (mask : Fin (n + n) → ℝ)
    (hm : ∀ i, |mask i| ≤ 1) (u v : Euclid (n + 1)) (y : Euclid dy) :
    |coreProtectedWeight V μ t mask u y - coreProtectedWeight V μ t mask v y| ≤
      (7800 * (μ * t ^ 2) * Real.sqrt (n + 1 : ℝ) / coreCapHeight n μ t) * ‖u - v‖ := by
  apply smoothRampSlope_comp_bound (coreCapHeight_pos n hμ ht)
  have h := scalar_gradient_bound_global
    (fun w => coreInteraction_hasFDerivAt_u V (2 * μ * t) (32 * t) mask w y)
    (fun w => scaledInteractionGradU_norm V hμ ht mask hm w y) u v
  convert h using 1
  congr 1
  unfold coreProtectedQ
  ring

theorem coreProtectedWeight_sub_y {n dy : ℕ} (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy)
    {μ t : ℝ} (hμ : 0 < μ) (ht : 0 < t) (mask : Fin (n + n) → ℝ)
    (hm : ∀ i, |mask i| ≤ 1) (u : Euclid (n + 1)) (y z : Euclid dy) :
    |coreProtectedWeight V μ t mask u y - coreProtectedWeight V μ t mask u z| ≤
      (180 * μ * t * Real.sqrt (n + 1 : ℝ) / coreCapHeight n μ t) * ‖y - z‖ := by
  have hH := coreCapHeight_pos n hμ ht
  apply ball_bound_constant_outside (by positivity :
    0 ≤ 180 * μ * t * Real.sqrt (n + 1 : ℝ) / coreCapHeight n μ t) (1 : ℝ)
      (R := coreControlRadius n t)
  · intro a b ha hb
    rw [Real.norm_eq_abs]
    exact smoothRampSlope_comp_bound (coreCapHeight_pos n hμ ht)
      (scalar_gradient_bound_on_ball (coreGap_hasFDerivAt_y V μ ht mask u)
        (coreGapGradY_norm_on_ball V hμ ht mask hm u) ha hb)
  · exact coreProtectedWeight_outside V hμ ht mask hm u

end FreshGradientMinimax
