import FreshGradientMinimax.FramedAcceleratedProtected

/-! Exact ambient value identification and the true value-gradient
comparison. The maximization ranges over the entire ambient dual space. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open scoped InnerProductSpace InnerProduct
variable {n k dy : ℕ} (V : Euclid (k * (n + 2)) →ₗᵢ[ℝ] Euclid dy)

theorem framedAcceleratedProtected_maximizer (hn : 10 ≤ n + 2) (hk : 0 < k)
    (u : Euclid (k * 2 + 1)) (y : Euclid dy) :
    framedAcceleratedProtected V (acceleratedThreshold n k) u y ≤
      framedAcceleratedProtected V (acceleratedThreshold n k) u
        (framedAcceleratedMaximizer V (acceleratedThreshold n k) u (acceleratedThreshold_pos n hk).le) := by
  rw [framedAcceleratedMaximizer, framedAcceleratedProtected_frame, acceleratedProtected_at_maximizer hn hk]
  exact (framedAcceleratedProtected_le_uncapped V _ u y).trans
    ((framedAcceleratedUncapped_le_projected V _ u y).trans
      (acceleratedHuberMaximizer_max n k (acceleratedThreshold_pos n hk).le u (frameCoordinates V y)))

def framedAcceleratedValue (δ : ℝ) (u : Euclid (k * 2 + 1)) : ℝ :=
  sSup (Set.range (framedAcceleratedProtected V δ u))

theorem framedAcceleratedValue_eq_max (hn : 10 ≤ n + 2) (hk : 0 < k) (u : Euclid (k * 2 + 1)) :
    framedAcceleratedValue V (acceleratedThreshold n k) u =
      framedAcceleratedProtected V (acceleratedThreshold n k) u
        (framedAcceleratedMaximizer V (acceleratedThreshold n k) u (acceleratedThreshold_pos n hk).le) := by
  apply IsGreatest.csSup_eq
  refine ⟨⟨_, rfl⟩, ?_⟩
  rintro _ ⟨y, rfl⟩
  exact framedAcceleratedProtected_maximizer V hn hk u y

theorem framedAcceleratedValue_eq_intrinsic (hn : 10 ≤ n + 2) (hk : 0 < k) :
    framedAcceleratedValue V (acceleratedThreshold n k) = acceleratedProtectedValue n k (acceleratedThreshold n k) := by
  funext u
  rw [framedAcceleratedValue_eq_max V hn hk, framedAcceleratedMaximizer, framedAcceleratedProtected_frame,
    acceleratedProtectedValue_eq_max hn hk]

theorem framedAcceleratedValue_hasFDerivAt (hn : 10 ≤ n + 2) (hk : 0 < k) (u : Euclid (k * 2 + 1)) :
    HasFDerivAt (framedAcceleratedValue V (acceleratedThreshold n k))
      (innerSL ℝ (acceleratedUncappedGradientU n k (acceleratedThreshold n k) u
        (acceleratedHuberMaximizer n k (acceleratedThreshold n k) u (acceleratedThreshold_pos n hk).le))) u := by
  rw [framedAcceleratedValue_eq_intrinsic V hn hk]
  exact acceleratedProtectedValue_hasFDerivAt hn hk u

theorem framedAcceleratedValue_gradient_comparison (hn : 10 ≤ n + 2) (hk : 0 < k) (u : Euclid (k * 2 + 1)) :
    ‖gradient (framedAcceleratedValue V (acceleratedThreshold n k)) u - gradient acceleratedIdealValue u‖ ≤
      primalRidgeConstant / 100 := by
  rw [framedAcceleratedValue_eq_intrinsic V hn hk]
  exact acceleratedProtectedValue_gradient_comparison hn hk u

theorem framedAcceleratedValue_lower (hn : 10 ≤ n + 2) (hk : 0 < k) (u : Euclid (k * 2 + 1)) :
    -1000 * (k + 1 : ℕ) ≤ framedAcceleratedValue V (acceleratedThreshold n k) u := by
  rw [framedAcceleratedValue_eq_intrinsic V hn hk]
  exact acceleratedProtectedValue_lower hn hk u

theorem framedAcceleratedValue_origin (hn : 10 ≤ n + 2) {δ : ℝ} (hδ : 0 ≤ δ) :
    framedAcceleratedValue V δ 0 = -coreTheta 0 := by
  apply IsGreatest.csSup_eq
  refine ⟨⟨0, framedAcceleratedProtected_origin V hn hδ⟩, ?_⟩
  rintro _ ⟨y, rfl⟩
  exact framedAcceleratedProtected_origin_max V hn hδ y

theorem framedAcceleratedCap_exterior_independent
    (W : Euclid (k * (n + 2)) →ₗᵢ[ℝ] Euclid dy) (hn : 10 ≤ n + 2) {δ : ℝ} (hδ : 0 ≤ δ)
    (u v : Euclid (k * 2 + 1)) (y : Euclid dy) (hy : 2 * acceleratedDualRadius n k ≤ ‖y‖) :
    framedAcceleratedCap V δ u y = framedAcceleratedCap W δ v y := by
  rw [framedAcceleratedCap_exterior V hn hδ u hy, framedAcceleratedCap_exterior W hn hδ v hy]

end FreshGradientMinimax
