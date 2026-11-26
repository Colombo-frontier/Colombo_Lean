import FreshGradientMinimax.WeightedCoreSeed
import FreshGradientMinimax.CoreCapSmooth

/-! The protected core with independently truncated seeds and links. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open scoped InnerProductSpace

def maskedCoreObjective {n dy : ℕ} (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy) (μ t : ℝ)
    (w : Euclid n) (mask : Fin (n + n) → ℝ) (u : Euclid (n + 1)) (y : Euclid dy) : ℝ :=
  (μ * t ^ 2) * weightedCoreSeed w u - μ / 2 * ‖y‖ ^ 2 - coreProtectedCap V μ t mask u y

def maskedCoreGradU {n dy : ℕ} (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy) (μ t : ℝ)
    (w : Euclid n) (mask : Fin (n + n) → ℝ) (u : Euclid (n + 1)) (y : Euclid dy) : Euclid (n + 1) :=
  (μ * t ^ 2) • weightedCoreSeedGradient w u - coreProtectedCapGradU V μ t mask u y

def maskedCoreGradY {n dy : ℕ} (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy) (μ t : ℝ)
    (mask : Fin (n + n) → ℝ) (u : Euclid (n + 1)) (y : Euclid dy) : Euclid dy :=
  -μ • y - coreProtectedCapGradY V μ t mask u y

theorem maskedCore_hasFDerivAt_u {n dy : ℕ} (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy)
    {μ t : ℝ} (hμ : 0 < μ) (ht : 0 < t) (w : Euclid n) (mask : Fin (n + n) → ℝ)
    (u : Euclid (n + 1)) (y : Euclid dy) :
    HasFDerivAt (fun v => maskedCoreObjective V μ t w mask v y) (innerSL ℝ (maskedCoreGradU V μ t w mask u y)) u := by
  have hs := weightedCoreSeed_hasFDerivAt w u
  rw [weightedCoreSeedDerivative_eq_inner] at hs
  simpa only [maskedCoreObjective, maskedCoreGradU, map_sub, map_smul] using
    ((hs.const_mul (μ * t ^ 2)).sub_const (μ / 2 * ‖y‖ ^ 2)).sub
      (coreProtectedCap_hasFDerivAt_u V hμ ht mask u y)

theorem maskedCore_hasFDerivAt_y {n dy : ℕ} (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy)
    {μ t : ℝ} (hμ : 0 < μ) (ht : 0 < t) (w : Euclid n) (mask : Fin (n + n) → ℝ)
    (u : Euclid (n + 1)) (y : Euclid dy) :
    HasFDerivAt (maskedCoreObjective V μ t w mask u) (innerSL ℝ (maskedCoreGradY V μ t mask u y)) y := by
  simpa only [maskedCoreObjective, maskedCoreGradY, map_sub, neg_smul, map_neg, zero_sub] using
    ((hasFDerivAt_const ((μ * t ^ 2) * weightedCoreSeed w u) y).sub (half_quadratic_hasFDerivAt μ y)).sub
      (coreProtectedCap_hasFDerivAt_y V hμ ht mask u y)

theorem maskedCore_gradient_u {n dy : ℕ} (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy)
    {μ t : ℝ} (hμ : 0 < μ) (ht : 0 < t) (w : Euclid n) (mask : Fin (n + n) → ℝ)
    (u : Euclid (n + 1)) (y : Euclid dy) :
    gradient (fun v => maskedCoreObjective V μ t w mask v y) u = maskedCoreGradU V μ t w mask u y :=
  (hasGradientAt_iff_hasFDerivAt.mpr (maskedCore_hasFDerivAt_u V hμ ht w mask u y)).gradient

theorem maskedCore_gradient_y {n dy : ℕ} (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy)
    {μ t : ℝ} (hμ : 0 < μ) (ht : 0 < t) (w : Euclid n) (mask : Fin (n + n) → ℝ)
    (u : Euclid (n + 1)) (y : Euclid dy) :
    gradient (maskedCoreObjective V μ t w mask u) y = maskedCoreGradY V μ t mask u y :=
  (hasGradientAt_iff_hasFDerivAt.mpr (maskedCore_hasFDerivAt_y V hμ ht w mask u y)).gradient

theorem maskedCore_strongConcave {n dy : ℕ} (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy)
    {μ t : ℝ} (hμ : 0 < μ) (ht : 0 < t) (w : Euclid n) (mask : Fin (n + n) → ℝ)
    (hm : ∀ i, |mask i| ≤ 1) (u : Euclid (n + 1)) :
    StrongConcaveGradient (maskedCoreObjective V μ t w mask u) (maskedCoreGradY V μ t mask u) μ := by
  have h := convex_penalty_strongConcave (coreProtectedCap_convex V hμ ht mask hm u)
    (coreProtectedCap_hasFDerivAt_y V hμ ht mask u) μ ((μ * t ^ 2) * weightedCoreSeed w u) 0
  unfold maskedCoreObjective maskedCoreGradY
  simpa only [inner_zero_left, add_zero, zero_sub, neg_smul] using h

theorem maskedCore_full {n dy : ℕ} (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy) (μ t : ℝ) :
    maskedCoreObjective V μ t ((WithLp.equiv 2 _).symm (fun _ : Fin n => (1 : ℝ))) (fun _ => 1) =
      coreProtectedObjective V μ t := by
  funext u y
  simp only [maskedCoreObjective, weightedCoreSeed_full, coreProtectedObjective]

end FreshGradientMinimax
