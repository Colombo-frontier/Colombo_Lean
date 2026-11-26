import FreshGradientMinimax.AcceleratedProtectedModel

/-! E.1 with the identity dual frame, in the construction's intrinsic
Euclidean spaces. Arbitrary ambient frames are a separate remaining step. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open scoped InnerProductSpace InnerProduct

theorem lemma_E1_intrinsic {n k : ℕ} (hn : 10 ≤ n + 2) (hk : 0 < k) :
    let δ := acceleratedThreshold n k
    let O := acceleratedProtectedModel n k hn (acceleratedThreshold_pos n hk).le
    (∀ u, StrongConcaveGradient (O.f u) (O.gradY u) (robinStep (n + 2) ^ 2)) ∧
    (∀ u y v z, ‖O.gradX u y - O.gradX v z‖ ^ 2 + ‖O.gradY u y - O.gradY v z‖ ^ 2 ≤
      (10 ^ 8 : ℝ) ^ 2 * (‖u - v‖ ^ 2 + ‖y - z‖ ^ 2)) ∧
    (∀ u y, ‖O.gradX u y‖ ≤ 10 ^ 8 * Real.sqrt (k + 1 : ℕ)) ∧
    (∀ u, ‖gradient O.value u - gradient acceleratedIdealValue u‖ ≤ primalRidgeConstant / 100) ∧
    (∀ u, -1000 * (k + 1 : ℕ) ≤ O.value u) ∧
    O.value 0 = -coreTheta 0 ∧ O.dualMax 0 = 0 ∧
    (∀ u y, 2 * acceleratedDualRadius n k ≤ ‖y‖ →
      acceleratedCap n k δ u y = acceleratedWall n k y - acceleratedDualRadius n k ^ 2 / 2) := by
  dsimp only
  refine ⟨(acceleratedProtectedModel n k hn (acceleratedThreshold_pos n hk).le).dual_strong,
    (acceleratedProtectedModel n k hn (acceleratedThreshold_pos n hk).le).joint_smooth,
    acceleratedProtectedModel_gradient_bound hn (acceleratedThreshold_pos n hk).le, ?_, ?_, ?_,
    acceleratedProtectedModel_origin_dual hn (acceleratedThreshold_pos n hk).le, ?_⟩
  · exact acceleratedProtectedValue_gradient_comparison hn hk
  · exact acceleratedProtectedValue_lower hn hk
  · exact acceleratedProtectedValue_origin hn (acceleratedThreshold_pos n hk).le
  · intro u y hy
    exact acceleratedCap_exterior hn (acceleratedThreshold_pos n hk).le u hy

end FreshGradientMinimax
