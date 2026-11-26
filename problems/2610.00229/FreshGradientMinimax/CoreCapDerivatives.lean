import FreshGradientMinimax.CoreInteractionScale
import FreshGradientMinimax.QuadraticConvexity

/-! Actual first derivatives of the protected core, including the interfaces of
the smooth maximum. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open scoped InnerProductSpace

def coreProtectedWeight {n dy : ℕ} (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy) (μ t : ℝ)
    (mask : Fin (n + n) → ℝ) (u : Euclid (n + 1)) (y : Euclid dy) : ℝ :=
  smoothRampSlope (coreCapHeight n μ t) (coreProtectedWall n μ t y - coreProtectedQ V μ t mask u y)

def coreProtectedQGradY {n dy : ℕ} (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy) (μ t : ℝ)
    (mask : Fin (n + n) → ℝ) (u : Euclid (n + 1)) (y : Euclid dy) : Euclid dy :=
  μ • y - coreInteractionGradY V (2 * μ * t) (32 * t) mask u y

def coreProtectedCapGradY {n dy : ℕ} (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy) (μ t : ℝ)
    (mask : Fin (n + n) → ℝ) (u : Euclid (n + 1)) (y : Euclid dy) : Euclid dy :=
  (1 - coreProtectedWeight V μ t mask u y) • coreProtectedQGradY V μ t mask u y +
    coreProtectedWeight V μ t mask u y • ((4 * μ) • y)

def coreProtectedCapGradU {n dy : ℕ} (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy) (μ t : ℝ)
    (mask : Fin (n + n) → ℝ) (u : Euclid (n + 1)) (y : Euclid dy) : Euclid (n + 1) :=
  (1 - coreProtectedWeight V μ t mask u y) •
    (-coreInteractionGradU V (2 * μ * t) (32 * t) mask u y)

def coreProtectedGradU {n dy : ℕ} (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy) (μ t : ℝ)
    (u : Euclid (n + 1)) (y : Euclid dy) : Euclid (n + 1) :=
  (μ * t ^ 2) • coreSeedGradient u - coreProtectedCapGradU V μ t (fun _ => 1) u y

def coreProtectedGradY {n dy : ℕ} (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy) (μ t : ℝ)
    (u : Euclid (n + 1)) (y : Euclid dy) : Euclid dy :=
  -μ • y - coreProtectedCapGradY V μ t (fun _ => 1) u y

theorem coreProtectedWeight_bounds {n dy : ℕ} (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy)
    {μ t : ℝ} (hμ : 0 < μ) (ht : 0 < t) (mask : Fin (n + n) → ℝ)
    (u : Euclid (n + 1)) (y : Euclid dy) :
    0 ≤ coreProtectedWeight V μ t mask u y ∧ coreProtectedWeight V μ t mask u y ≤ 1 :=
  smoothRampSlope_bounds (coreCapHeight_pos n hμ ht) _

theorem coreProtectedQ_hasFDerivAt_y {n dy : ℕ} (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy)
    (μ : ℝ) {t : ℝ} (ht : 0 < t) (mask : Fin (n + n) → ℝ)
    (u : Euclid (n + 1)) (y : Euclid dy) :
    HasFDerivAt (coreProtectedQ V μ t mask u) (innerSL ℝ (coreProtectedQGradY V μ t mask u y)) y := by
  simpa only [coreProtectedQ, coreProtectedQGradY, map_sub] using
    (half_quadratic_hasFDerivAt μ y).sub
      (coreInteraction_hasFDerivAt_y V (2 * μ * t) (by positivity : 0 < 32 * t) mask u y)

theorem coreProtectedWall_hasFDerivAt (n : ℕ) {dy : ℕ} (μ t : ℝ) (y : Euclid dy) :
    HasFDerivAt (coreProtectedWall n μ t) (innerSL ℝ ((4 * μ) • y)) y := by
  convert (half_quadratic_hasFDerivAt (4 * μ) y).sub_const (4 * coreCapHeight n μ t) using 1
  funext z
  unfold coreProtectedWall
  ring

theorem coreProtectedCap_hasFDerivAt_y {n dy : ℕ} (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy)
    {μ t : ℝ} (hμ : 0 < μ) (ht : 0 < t) (mask : Fin (n + n) → ℝ)
    (u : Euclid (n + 1)) (y : Euclid dy) :
    HasFDerivAt (coreProtectedCap V μ t mask u)
      (innerSL ℝ (coreProtectedCapGradY V μ t mask u y)) y := by
  simpa only [coreProtectedCap, coreProtectedCapGradY, coreProtectedWeight, map_add, map_smul]
    using smoothMaximum_comp_hasFDerivAt (coreCapHeight_pos n hμ ht)
      (coreProtectedQ_hasFDerivAt_y V μ ht mask u y) (coreProtectedWall_hasFDerivAt n μ t y)

theorem coreProtectedCap_hasFDerivAt_u {n dy : ℕ} (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy)
    {μ t : ℝ} (hμ : 0 < μ) (ht : 0 < t) (mask : Fin (n + n) → ℝ)
    (u : Euclid (n + 1)) (y : Euclid dy) :
    HasFDerivAt (fun v => coreProtectedCap V μ t mask v y)
      (innerSL ℝ (coreProtectedCapGradU V μ t mask u y)) u := by
  have hq := (hasFDerivAt_const (𝕜 := ℝ) (μ / 2 * ‖y‖ ^ 2) u).sub
    (coreInteraction_hasFDerivAt_u V (2 * μ * t) (32 * t) mask u y)
  simpa only [coreProtectedCap, coreProtectedCapGradU, coreProtectedWeight, coreProtectedQ,
    zero_sub, smul_zero, add_zero, map_smul, map_neg] using
    smoothMaximum_comp_hasFDerivAt (coreCapHeight_pos n hμ ht) hq
      (hasFDerivAt_const (coreProtectedWall n μ t y) u)

theorem coreProtectedObjective_hasFDerivAt_u {n dy : ℕ} (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy)
    {μ t : ℝ} (hμ : 0 < μ) (ht : 0 < t) (u : Euclid (n + 1)) (y : Euclid dy) :
    HasFDerivAt (fun v => coreProtectedObjective V μ t v y)
      (innerSL ℝ (coreProtectedGradU V μ t u y)) u := by
  have hs := coreSeed_hasFDerivAt u
  rw [coreSeedDerivative_eq_inner] at hs
  simpa only [coreProtectedObjective, coreProtectedGradU, map_sub, map_smul] using
    ((hs.const_mul (μ * t ^ 2)).sub_const (μ / 2 * ‖y‖ ^ 2)).sub
      (coreProtectedCap_hasFDerivAt_u V hμ ht (fun _ => 1) u y)

theorem coreProtectedObjective_hasFDerivAt_y {n dy : ℕ} (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy)
    {μ t : ℝ} (hμ : 0 < μ) (ht : 0 < t) (u : Euclid (n + 1)) (y : Euclid dy) :
    HasFDerivAt (coreProtectedObjective V μ t u) (innerSL ℝ (coreProtectedGradY V μ t u y)) y := by
  simpa only [coreProtectedObjective, coreProtectedGradY, map_sub, neg_smul, map_neg, zero_sub] using
    ((hasFDerivAt_const ((μ * t ^ 2) * coreSeed u) y).sub (half_quadratic_hasFDerivAt μ y)).sub
      (coreProtectedCap_hasFDerivAt_y V hμ ht (fun _ => 1) u y)

theorem coreProtectedObjective_gradient_y {n dy : ℕ} (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy)
    {μ t : ℝ} (hμ : 0 < μ) (ht : 0 < t) (u : Euclid (n + 1)) (y : Euclid dy) :
    gradient (coreProtectedObjective V μ t u) y = coreProtectedGradY V μ t u y :=
  (hasGradientAt_iff_hasFDerivAt.mpr (coreProtectedObjective_hasFDerivAt_y V hμ ht u y)).gradient

end FreshGradientMinimax
