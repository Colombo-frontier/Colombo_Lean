import FreshGradientMinimax.AcceleratedPrimal
import FreshGradientMinimax.RobinHuberMaximizer

/-! The complete uncapped formula D_delta−r²‖y‖²/2−Q_delta. Its actual
maximizer is assembled from the proved subchain maximizers. -/

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace FreshGradientMinimax
open scoped BigOperators InnerProductSpace InnerProduct

def acceleratedUncapped (n k : ℕ) (δ : ℝ) (u : Euclid (k * 2 + 1)) (y : Euclid (k * (n + 2))) : ℝ :=
  acceleratedPrimal n k δ u - robinStep (n + 2) ^ 2 / 2 * ‖y‖ ^ 2 - robinMultiEnergy n k δ u y

def acceleratedDualGradient (n k : ℕ) (δ : ℝ) (u : Euclid (k * 2 + 1)) (y : Euclid (k * (n + 2))) : Euclid (k * (n + 2)) :=
  -(robinStep (n + 2) ^ 2 • y) - robinMultiGradientY n k δ u y

def acceleratedQuadraticMaximizer (n k : ℕ) (u : Euclid (k * 2 + 1)) : Euclid (k * (n + 2)) :=
  euclidJoin (fun i => robinQuadraticOptimizer n (clipVector 2 u (interleavedX i)) (clipVector 2 u (interleavedZ i) / 2))

def acceleratedHuberMaximizer (n k : ℕ) (δ : ℝ) (u : Euclid (k * 2 + 1)) (hδ : 0 ≤ δ) : Euclid (k * (n + 2)) :=
  euclidJoin (fun i => robinHuberMaximizer n δ (clipVector 2 u (interleavedX i)) (clipVector 2 u (interleavedZ i) / 2) hδ)

theorem clip_two_half_coordinate {m : ℕ} (u : Euclid m) (i : Fin m) :
    |clipVector 2 u i / 2| ≤ 3 / 2 := by
  rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  exact div_le_div_of_nonneg_right (clip_two_coordinate u i) (by norm_num)

theorem acceleratedUncapped_hasFDerivAt_y (n k : ℕ) {δ : ℝ} (hδ : 0 ≤ δ)
    (u : Euclid (k * 2 + 1)) (y : Euclid (k * (n + 2))) :
    HasFDerivAt (acceleratedUncapped n k δ u) (innerSL ℝ (acceleratedDualGradient n k δ u y)) y := by
  have hn := (hasStrictFDerivAt_norm_sq y).hasFDerivAt.const_mul (robinStep (n + 2) ^ 2 / 2)
  have hd := ((hasFDerivAt_const (acceleratedPrimal n k δ u) y).sub hn).sub
    (robinMultiEnergy_hasFDerivAt_y n k hδ u y)
  apply hd.congr_fderiv
  apply ContinuousLinearMap.ext
  intro v
  simp [acceleratedDualGradient, innerSL_apply, inner_sub_left, inner_neg_left, real_inner_smul_left]
  ring

theorem acceleratedUncapped_strongConcave (n k : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) (u : Euclid (k * 2 + 1)) :
    StrongConcaveGradient (acceleratedUncapped n k δ u) (acceleratedDualGradient n k δ u) (robinStep (n + 2) ^ 2) := by
  simpa only [acceleratedUncapped, acceleratedDualGradient, inner_zero_left, add_zero, zero_sub] using
    convex_penalty_strongConcave (robinMultiEnergy_convex_y n k hδ u)
      (robinMultiEnergy_hasFDerivAt_y n k hδ u) (robinStep (n + 2) ^ 2)
      (acceleratedPrimal n k δ u) (0 : Euclid (k * (n + 2)))

theorem acceleratedUncapped_joint_contDiff (n k : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) :
    ContDiff ℝ 1 (fun z : Euclid (k * 2 + 1) × Euclid (k * (n + 2)) => acceleratedUncapped n k δ z.1 z.2) := by
  exact (((acceleratedPrimal_contDiff n k hδ).comp contDiff_fst).sub
    (contDiff_const.mul ((contDiff_norm_sq ℝ).comp contDiff_snd))).sub
      (robinMultiEnergy_joint_contDiff n k hδ)

theorem acceleratedUncapped_blocks (n k : ℕ) (δ : ℝ) (u : Euclid (k * 2 + 1)) (y : Euclid (k * (n + 2))) :
    acceleratedUncapped n k δ u y = acceleratedPrimal n k δ u - robinSmallC (n + 2) *
      (∑ i : Fin k, (clipVector 2 u (interleavedX i) ^ 2 + (clipVector 2 u (interleavedZ i) / 2) ^ 2)) +
      ∑ i : Fin k, robinHuberPotential n δ (clipVector 2 u (interleavedX i)) (clipVector 2 u (interleavedZ i) / 2) (euclidBlock i y) := by
  unfold acceleratedUncapped
  rw [robinMultiEnergy_blocks, euclid_norm_sq_blocks]
  simp only [robinHuberPotential, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

theorem acceleratedHuberMaximizer_max (n k : ℕ) {δ : ℝ} (hδ : 0 ≤ δ)
    (u : Euclid (k * 2 + 1)) (y : Euclid (k * (n + 2))) :
    acceleratedUncapped n k δ u y ≤ acceleratedUncapped n k δ u (acceleratedHuberMaximizer n k δ u hδ) := by
  rw [acceleratedUncapped_blocks, acceleratedUncapped_blocks]
  apply add_le_add_left
  apply Finset.sum_le_sum
  intro i _
  rw [acceleratedHuberMaximizer, euclidBlock_join]
  exact robinHuberMaximizer_max n hδ _ _ _

theorem acceleratedHuberMaximizer_gradient_zero (n k : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) (u : Euclid (k * 2 + 1)) :
    acceleratedDualGradient n k δ u (acceleratedHuberMaximizer n k δ u hδ) = 0 :=
  gradient_zero_at_global_max _ (acceleratedUncapped_hasFDerivAt_y n k hδ u _)
    (acceleratedHuberMaximizer_max n k hδ u)

theorem acceleratedHuberMaximizer_unique (n k : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) (u : Euclid (k * 2 + 1))
    (y : Euclid (k * (n + 2)))
    (hy : ∀ z, acceleratedUncapped n k δ u z ≤ acceleratedUncapped n k δ u y) :
    acceleratedHuberMaximizer n k δ u hδ = y :=
  strong_concave_maximum_unique (sq_pos_of_pos (robinStep_pos (show 0 < n + 2 by omega)))
    (acceleratedUncapped_strongConcave n k hδ u) (acceleratedUncapped_hasFDerivAt_y n k hδ u)
    _ y (acceleratedHuberMaximizer_max n k hδ u) hy

theorem acceleratedHuberMaximizer_zero {n k : ℕ} (hn : 10 ≤ n + 2) (u : Euclid (k * 2 + 1)) :
    acceleratedHuberMaximizer n k 0 u (le_refl 0) = acceleratedQuadraticMaximizer n k u := by
  apply euclid_ext_blocks
  intro i
  rw [acceleratedHuberMaximizer, acceleratedQuadraticMaximizer, euclidBlock_join, euclidBlock_join]
  exact robinHuberMaximizer_zero hn (clip_two_coordinate _ _) (clip_two_half_coordinate _ _)

theorem accelerated_zero_elimination {n k : ℕ} (hn : 10 ≤ n + 2) (u : Euclid (k * 2 + 1)) :
    acceleratedUncapped n k 0 u (acceleratedQuadraticMaximizer n k u) = acceleratedIdealValue u := by
  rw [acceleratedUncapped_blocks, acceleratedPrimal_zero]
  simp only [acceleratedQuadraticMaximizer, euclidBlock_join]
  have hsum : (∑ i : Fin k, robinHuberPotential n 0 (clipVector 2 u (interleavedX i))
      (clipVector 2 u (interleavedZ i) / 2)
      (robinQuadraticOptimizer n (clipVector 2 u (interleavedX i)) (clipVector 2 u (interleavedZ i) / 2))) =
      6 * ∑ i : Fin k, (clipVector 2 u (interleavedX i) - clipVector 2 u (interleavedZ i) / 2) ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => robin_huber_zero_value hn (clip_two_coordinate _ _) (clip_two_half_coordinate _ _))
  rw [hsum]
  unfold acceleratedIdealValue
  ring

theorem accelerated_zero_max {n k : ℕ} (hn : 10 ≤ n + 2) (u : Euclid (k * 2 + 1)) (y : Euclid (k * (n + 2))) :
    acceleratedUncapped n k 0 u y ≤ acceleratedIdealValue u := by
  have h := acceleratedHuberMaximizer_max n k (le_refl 0) u y
  rwa [acceleratedHuberMaximizer_zero hn, accelerated_zero_elimination hn] at h

end FreshGradientMinimax
