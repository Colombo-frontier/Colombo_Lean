import FreshGradientMinimax.FramedAcceleratedModel

/-! The complete original Lemma E.1, for arbitrary ambient dual dimension
and orthonormal frame, retaining the original parameters and full norms. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open scoped InnerProductSpace InnerProduct

theorem lemma_E1 {n k dy : ℕ} (V : Euclid (k * (n + 2)) →ₗᵢ[ℝ] Euclid dy)
    (hn : 10 ≤ n + 2) (hk : 0 < k) :
    let δ := acceleratedThreshold n k
    let O := framedAcceleratedModel V hn (acceleratedThreshold_pos n hk).le
    (∀ u, StrongConcaveGradient (O.f u) (O.gradY u) (robinStep (n + 2) ^ 2)) ∧
    (∀ u y v z, ‖O.gradX u y - O.gradX v z‖ ^ 2 + ‖O.gradY u y - O.gradY v z‖ ^ 2 ≤
      (10 ^ 8 : ℝ) ^ 2 * (‖u - v‖ ^ 2 + ‖y - z‖ ^ 2)) ∧
    (∀ u y, ‖O.gradX u y‖ ≤ 10 ^ 8 * Real.sqrt (k + 1 : ℕ)) ∧
    (∀ u, ‖gradient O.value u - gradient acceleratedIdealValue u‖ ≤ primalRidgeConstant / 100) ∧
    (∀ u, -1000 * (k + 1 : ℕ) ≤ O.value u) ∧
    O.value 0 = -coreTheta 0 ∧ O.dualMax 0 = 0 ∧
    (∀ u y, 2 * acceleratedDualRadius n k ≤ ‖y‖ →
      framedAcceleratedCap V δ u y = ambientAcceleratedWall n k y - acceleratedDualRadius n k ^ 2 / 2) := by
  dsimp only
  refine ⟨(framedAcceleratedModel V hn (acceleratedThreshold_pos n hk).le).dual_strong,
    (framedAcceleratedModel V hn (acceleratedThreshold_pos n hk).le).joint_smooth,
    framedAcceleratedModel_gradient_bound V hn (acceleratedThreshold_pos n hk).le, ?_, ?_, ?_,
    framedAcceleratedModel_origin_dual V hn (acceleratedThreshold_pos n hk).le, ?_⟩
  · exact framedAcceleratedValue_gradient_comparison V hn hk
  · exact framedAcceleratedValue_lower V hn hk
  · exact framedAcceleratedValue_origin V hn (acceleratedThreshold_pos n hk).le
  · intro u y hy
    exact framedAcceleratedCap_exterior V hn (acceleratedThreshold_pos n hk).le u hy

theorem lemma_E1_frame_independence {n k dy : ℕ}
    (V W : Euclid (k * (n + 2)) →ₗᵢ[ℝ] Euclid dy) (hn : 10 ≤ n + 2) (hk : 0 < k)
    (u v : Euclid (k * 2 + 1)) (y : Euclid dy) (hy : 2 * acceleratedDualRadius n k ≤ ‖y‖) :
    framedAcceleratedCap V (acceleratedThreshold n k) u y =
      framedAcceleratedCap W (acceleratedThreshold n k) v y :=
  framedAcceleratedCap_exterior_independent V W hn (acceleratedThreshold_pos n hk).le u v y hy

end FreshGradientMinimax
